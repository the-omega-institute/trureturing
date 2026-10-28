/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite scalar common numerators for actual canonical lattice channels. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
import D5.S3.VertexAlgebra.FormalSeries.UngradedLocalWordSeries
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
The factorial pairing tests the common vector series against an arbitrary
finite oscillator polynomial. Actual mode grading bounds the resulting total
degree, without positivity or a vacuum assumption.

proof_shape: content
admission_basis: escape-witness
escape_witness: finite multilinear expansion and actual mode grading force a
charge-energy lower bound on every nonzero double canonical coefficient.
This bound makes the scalar common series an exact polynomial truncation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorScalarNumerator
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticePositiveEnergy LatticeSugawaraCurrents SupportedChannelSeries MvPolynomial
open FieldNormalProductLocality
open scoped BigOperators VertexOperator
noncomputable section

open private map_extend from D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
open private powerIndex_ext from D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries
open private inner_coefficient_expansion from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation

private theorem inclusion_monomial_grade (D : LatticeData) (α : Charge D)
    (U : Exponent D) (c : ℂ) :
    inclusion D α (monomial U c) ∈ grade D (chargeEnergy D α + oscillatorEnergy U) := by
  classical
  rw [mem_grade_iff]
  rintro ⟨β, T⟩ h
  by_cases hα : α = β
  · subst β
    by_cases hT : U = T
    · subst T
      exact (h rfl).elim
    · simp [inclusion, coeff_monomial, hT]
  · simp [inclusion, hα]

private theorem double_coefficient_zero_below_charge (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (m n : ℤ) (T : Exponent D)
    (low : chargeEnergy D (α + (β + γ)) + oscillatorEnergy T <
      chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2) :
    (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T = 0 := by
  classical
  induction u using MvPolynomial.induction_on' with
  | add u₁ u₂ ih₁ ih₂ =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih₁, ih₂, add_zero]
  | monomial U a =>
    induction v using MvPolynomial.induction_on' with
    | add v₁ v₂ ih₁ ih₂ =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih₁, ih₂, add_zero]
    | monomial V b =>
      induction w using MvPolynomial.induction_on' with
      | add w₁ w₂ ih₁ ih₂ =>
        simp only [map_add, Pi.add_apply, LinearMap.add_apply,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih₁, ih₂, add_zero]
      | monomial W c =>
        have hi := actual_mode_grade D J hJG hGJ _ _ n _ _
          (inclusion_monomial_grade D β V b) (inclusion_monomial_grade D γ W c)
        rw [← inclusion_canonical] at hi
        have ho := actual_mode_grade D J hJG hGJ _ _ m _ _
          (inclusion_monomial_grade D α U a) hi
        rw [← inclusion_canonical] at ho
        have hz := (mem_grade_iff D _ _).mp ho (α + (β + γ), T) (by
          simp only [energy]
          omega)
        simpa only [inclusion, Finsupp.lsingle_apply, Finsupp.single_eq_same] using hz

/-- Every nonzero double actual coefficient has at least the sum of the three
charge energies minus the two signed mode shifts. Inputs may mix energies. -/
theorem actual_product_coefficient_energy_le (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (m n : ℤ) (T : Exponent D)
    (hne : (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T ≠ 0) :
    chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2 ≤
      chargeEnergy D (α + (β + γ)) + oscillatorEnergy T := by
  by_contra h
  exact hne (double_coefficient_zero_below_charge D J hJG hGJ α β γ u v w m n T
    (lt_of_not_ge h))

private theorem energy_le_of_mem_stateEnergies (D : LatticeData) (v : Carrier D)
    (B : ℤ) (hv : ∀ t, carrierCoeffEquiv D v t ≠ 0 → B ≤ energy D t)
    (m : ℤ) (hm : m ∈ stateEnergies D v) : B ≤ m := by
  classical
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
  exact hv t (Finsupp.mem_support_iff.mp ht)

private theorem inclusion_energy_lower (D : LatticeData) (δ : Charge D)
    (w : Oscillator D) (t : Label D)
    (ht : carrierCoeffEquiv D (inclusion D δ w) t ≠ 0) :
    chargeEnergy D δ ≤ energy D t := by
  have hδ : δ = t.1 := by
    by_contra h
    apply ht
    change ((inclusion D δ w) t.1).coeff t.2 = 0
    simp [inclusion, h]
  simp only [energy, ← hδ]
  omega

private theorem mode_energy_lower (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (a b : Carrier D) (B C q : ℤ)
    (ha : ∀ t, carrierCoeffEquiv D a t ≠ 0 → B ≤ energy D t)
    (hb : ∀ t, carrierCoeffEquiv D b t ≠ 0 → C ≤ energy D t)
    (t : Label D) (ht : carrierCoeffEquiv D (((LatticeAllStateField.Y D a)[[q]]) b) t ≠ 0) :
    B + C - q - 1 ≤ energy D t := by
  classical
  by_contra low
  apply ht
  have vanish (m : ℤ) (hm : m ∈ stateEnergies D a)
      (n : ℤ) (hn : n ∈ stateEnergies D b) :
      carrierCoeffEquiv D
        (((LatticeAllStateField.Y D (gradeProjection D m a))[[q]])
          (gradeProjection D n b)) t = 0 := by
    have hB := energy_le_of_mem_stateEnergies D a B ha m hm
    have hC := energy_le_of_mem_stateEnergies D b C hb n hn
    have hg := actual_mode_grade D J hJG hGJ m n q _ _
      (gradeProjection_mem D m a) (gradeProjection_mem D n b)
    exact (mem_grade_iff D _ _).mp hg t (by omega)
  have expand := congrArg
    (fun x => carrierCoeffEquiv D (((LatticeAllStateField.Y D x)[[q]]) b) t)
    (sum_gradeProjections D a)
  rw [← expand]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply,
    Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro m hm
  have expandB := congrArg
    (fun x => carrierCoeffEquiv D
      (((LatticeAllStateField.Y D (gradeProjection D m a))[[q]]) x) t)
    (sum_gradeProjections D b)
  rw [← expandB]
  simp only [map_sum, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero (fun n hn => vanish m hm n hn)

/-- Every surviving coefficient of an arbitrary actual lattice word retains
all signed mode and charge energies of its entire suffix. -/
theorem actual_word_coefficient_energy_le (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D)
    (δ : Charge D) (w : Sector D δ) (l : List (Fin n)) (e : Fin n → ℤ)
    (ρ : Charge D) (T : Exponent D)
    (hne : carrierCoeffEquiv D
      (UniformGradedLocalCorrelator.word
        (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))) l e
        (inclusion D δ w)) (ρ, T) ≠ 0) :
    chargeEnergy D δ + (l.map (fun i => chargeEnergy D (c i) + e i)).sum ≤
      chargeEnergy D ρ + oscillatorEnergy T := by
  induction l generalizing ρ T with
  | nil => exact inclusion_energy_lower D δ w (ρ, T) hne
  | cons i l ih =>
    have bound := mode_energy_lower D J hJG hGJ
      (inclusion D (c i) (s i))
      (UniformGradedLocalCorrelator.word
        (fun j => LatticeAllStateField.Y D (inclusion D (c j) (s j))) l e
        (inclusion D δ w))
      (chargeEnergy D (c i))
      (chargeEnergy D δ + (l.map (fun j => chargeEnergy D (c j) + e j)).sum)
      (-e i - 1) (inclusion_energy_lower D (c i) (s i))
      (fun t ht => ih t.1 t.2 ht) (ρ, T) hne
    simp only [List.map_cons, List.sum_cons, energy] at bound ⊢
    omega

/-- The actual factorial test functional, complex-linear in the tested state. -/
def readout (D : LatticeData) (p : Oscillator D) : Oscillator D →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ (FactorialFockMetric.embedding (Index D) p)).comp
    (FactorialFockMetric.embedding (Index D))

/-- Maximum oscillator energy in the finite test state; the empty maximum is zero. -/
def testEnergy (D : LatticeData) (p : Oscillator D) : ℕ := by
  classical
  exact p.support.sup oscillatorEnergy

/-- The exact integer cutoff, including all three clearing shifts. -/
def degreeBound (D : LatticeData) (α β γ : Charge D)
    (A B N : ℕ) (p : Oscillator D) : ℤ :=
  (A + B + N + testEnergy D p : ℕ) + chargeEnergy D (α + (β + γ)) -
    chargeEnergy D α - chargeEnergy D β - chargeEnergy D γ

private theorem readout_zero_of_above (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w p : Oscillator D) (m n : ℤ)
    (low : chargeEnergy D (α + (β + γ)) + testEnergy D p <
      chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2) :
    readout D p (canonical D α (β + γ) u m (canonical D β γ v n w)) = 0 := by
  classical
  change CanonicalOccupationSewing.H D p _ = 0
  rw [inner_coefficient_expansion]
  apply Finset.sum_eq_zero
  intro T hT
  have hE : oscillatorEnergy T ≤ testEnergy D p := Finset.le_sup hT
  have hz : (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T = 0 := by
    by_contra hn
    have := actual_product_coefficient_energy_le D J hJG hGJ α β γ u v w m n T hn
    omega
  rw [hz, mul_zero]

/-- A common actual vector numerator has no tested coefficient above the
explicit energy cutoff. The clearing summation index cancels from the bound. -/
theorem scalar_numerator_support (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (N A B : ℕ)
    (P : MvPowerSeries (Fin 2) (Oscillator D))
    (common : ∀ a b : ℤ,
      clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b)
    (p : Oscillator D) (d : Fin 2 →₀ ℕ)
    (hne : MvPowerSeries.coeff d (mapSeries (readout D p) P) ≠ 0) :
    (d.degree : ℤ) ≤ degreeBound D α β γ A B N p := by
  classical
  by_contra h
  have hd := powerIndex_ext d
  have hdeg : d.degree = d 0 + d 1 := by
    rw [Finsupp.degree_eq_sum]
    exact Fin.sum_univ_two _
  have hc := common (d 0) (d 1)
  rw [extend, ite_eq_left (by constructor <;> positivity)] at hc
  simp only [Int.toNat_natCast, ← hd] at hc
  apply hne
  change readout D p (MvPowerSeries.coeff d P) = 0
  rw [← hc]
  simp only [clear, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k hk
  rw [product, readout_zero_of_above D J hJG hGJ α β γ u v w p _ _ (by
    unfold degreeBound at h
    rw [hdeg] at h
    push_cast at h
    omega), smul_zero]

private theorem polynomial_of_degree_support {n : ℕ} (Q : MvPowerSeries (Fin n) ℂ) (K : ℤ)
    (support : ∀ d, MvPowerSeries.coeff d Q ≠ 0 → (d.degree : ℤ) ≤ K) :
    ∃ R : MvPolynomial (Fin n) ℂ,
      (R : MvPowerSeries (Fin n) ℂ) = Q ∧ R.totalDegree ≤ K.toNat ∧
      (K < 0 → Q = 0 ∧ R = 0) := by
  let R := MvPowerSeries.truncTotal (K.toNat + 1) Q
  have heq : (R : MvPowerSeries (Fin n) ℂ) = Q := by
    apply MvPowerSeries.ext
    intro d
    rw [MvPolynomial.coeff_coe]
    change (MvPowerSeries.truncTotal (K.toNat + 1) Q).coeff d = _
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with hd
    · rfl
    · symm
      by_contra hn
      have := support d hn
      omega
  refine ⟨R, heq, ?_, ?_⟩
  · exact Nat.le_of_lt_succ
      (MvPowerSeries.totalDegree_truncTotal_lt Q (by omega : K.toNat + 1 ≠ 0))
  · intro hK
    have hQ : Q = 0 := by
      apply MvPowerSeries.ext
      intro d
      change MvPowerSeries.coeff d Q = 0
      by_contra hn
      have := support d hn
      omega
    refine ⟨hQ, ?_⟩
    apply MvPolynomial.coe_injective (Fin n) ℂ
    rw [heq, hQ, MvPolynomial.coe_zero]

/-- One finite scalar polynomial gives the original three cleared channels.
N precedes the third state, and A,B,P precede the arbitrary test polynomial p.
Both inverse-Gram equations are explicit; no definiteness is assumed. -/
theorem ordinary_actual_finite_scalar_numerator
    (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β : Charge D) (u : Sector D α) (v : Sector D β) :
    ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator
        (LatticeAllStateField.Y D (inclusion D α u))
        (LatticeAllStateField.Y D (inclusion D β v))) = 0 ∧
      (∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0) ∧
      ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
        ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
        (∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0) ∧
        (∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0) ∧
        (∀ a b : ℤ,
          clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clear N (reverseProduct D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clearIterate N A B (iterate D α β γ u v w) a b = extend (collision P) a b) ∧
        ∀ p : Oscillator D, ∃! R : MvPolynomial (Fin 2) ℂ,
          (R : MvPowerSeries (Fin 2) ℂ) = mapSeries (readout D p) P ∧
          R.totalDegree ≤ (degreeBound D α β γ A B N p).toNat ∧
          (degreeBound D α β γ A B N p < 0 →
            mapSeries (readout D p) P = 0 ∧ R = 0) ∧
          ∀ a b : ℤ,
            clear N (fun x y => readout D p (product D α β γ u v w x y))
                (a - A) (b - B) = extend (R : MvPowerSeries (Fin 2) ℂ) a b ∧
            clear N (fun x y => readout D p (reverseProduct D α β γ u v w x y))
                (a - A) (b - B) = extend (R : MvPowerSeries (Fin 2) ℂ) a b ∧
            clearIterate N A B (fun x y => readout D p (iterate D α β γ u v w x y))
                a b = extend (collision (R : MvPowerSeries (Fin 2) ℂ)) a b := by
  obtain ⟨N, hN, huv, rest⟩ := ordinary_actual_cleared_channel_transport D α β u v
  refine ⟨N, hN, huv, ?_⟩
  intro γ w
  obtain ⟨A, B, P, hA, hB, common, _inverse, _inverseI⟩ := rest γ w
  refine ⟨A, B, P, hA, hB, common, ?_⟩
  intro p
  obtain ⟨R, heq, hdeg, hneg⟩ := polynomial_of_degree_support (mapSeries (readout D p) P)
    (degreeBound D α β γ A B N p)
    (scalar_numerator_support D J hJG hGJ α β γ u v w N A B P (fun a b => (common a b).1) p)
  refine ⟨R, ⟨heq, hdeg, hneg, ?_⟩, ?_⟩
  · intro a b
    have first := congrArg (readout D p) (common a b).1
    have second := congrArg (readout D p) (common a b).2.1
    have third := congrArg (readout D p) (common a b).2.2
    simp only [clear, map_sum, map_smul, map_extend, ← heq] at first second
    simp only [clearIterate, map_sum, map_smul, map_extend, ← collision_map, ← heq] at third
    exact ⟨first, second, third⟩
  · intro R' hR'
    exact MvPolynomial.coe_injective (Fin 2) ℂ (hR'.1.trans heq.symm)

open UniformGradedLocalCorrelator (word coefficientDistribution clearingPolynomial
  totalExponent labelledPairs polynomialAction difference)
open UngradedLocalWordSeries
open private total_shift from D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

/-- Integer cutoff for the same cleared n-word vector series, before any
polynomial extraction. Every labelled pair contributes k to the clearing degree. -/
def wordDegreeBound (D : LatticeData) {n : ℕ} (c : Fin n → Charge D)
    (δ : Charge D) (k : ℕ) (a : Fin n → ℕ) (p : Oscillator D) : ℤ :=
  (∑ i, (a i : ℤ)) + ((k * (labelledPairs n).card : ℕ) : ℤ) +
    (testEnergy D p : ℤ) + chargeEnergy D ((∑ i, c i) + δ) -
    chargeEnergy D δ - ∑ i, chargeEnergy D (c i)

private theorem word_readout_zero_above (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D)
    (δ : Charge D) (w p : Oscillator D) (e : Fin n → ℤ)
    (low : (testEnergy D p : ℤ) + chargeEnergy D ((∑ i, c i) + δ) -
      chargeEnergy D δ - (∑ i, chargeEnergy D (c i)) < totalExponent e) :
    ((readout D p).comp (projection D ((∑ i, c i) + δ)))
      (coefficientDistribution
        (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i)))
        (inclusion D δ w) 1 (List.ofFn (fun i : Fin n => i)) e) = 0 := by
  classical
  change CanonicalOccupationSewing.H D p _ = 0
  rw [inner_coefficient_expansion]
  apply Finset.sum_eq_zero
  intro T hT
  have hE : oscillatorEnergy T ≤ testEnergy D p := Finset.le_sup hT
  have hz : (projection D ((∑ i, c i) + δ)
      (word (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i)))
        (List.ofFn (fun i : Fin n => i)) e (inclusion D δ w))).coeff T = 0 := by
    by_contra hn
    have bound := actual_word_coefficient_energy_le D J hJG hGJ n c s δ w
      (List.ofFn (fun i : Fin n => i)) e ((∑ i, c i) + δ) T hn
    simp only [List.map_ofFn, List.sum_ofFn, Finset.sum_add_distrib] at bound
    unfold totalExponent at low
    omega
  change _ * (projection D ((∑ i, c i) + δ)
    (word _ _ e (inclusion D δ w))).coeff T = 0
  rw [hz, mul_zero]

private theorem clearing_zero_above {n : ℕ}
    (F : UniformGradedLocalCorrelator.Distribution n ℂ) (B : ℤ) (k : ℕ)
    (hF : ∀ e, B < totalExponent e → F e = 0) :
    ∀ e, B + ((k * (labelledPairs n).card : ℕ) : ℤ) < totalExponent e →
      polynomialAction (clearingPolynomial n k) F e = 0 := by
  have step (G : UniformGradedLocalCorrelator.Distribution n ℂ) (C : ℤ)
      (i j : Fin n) (hG : ∀ e, C < totalExponent e → G e = 0) :
      ∀ e, C + 1 < totalExponent e → difference i j G e = 0 := by
    intro e he
    change G (e - Pi.single i 1) - G (e - Pi.single j 1) = 0
    rw [hG _ (by rw [total_shift]; omega), hG _ (by rw [total_shift]; omega), sub_self]
  have power (G : UniformGradedLocalCorrelator.Distribution n ℂ) (C : ℤ)
      (i j : Fin n) (hG : ∀ e, C < totalExponent e → G e = 0) (r : ℕ) :
      ∀ e, C + r < totalExponent e → (difference i j ^ r) G e = 0 := by
    induction r with
    | zero => simpa using hG
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply]
      simpa [Nat.cast_add, add_assoc] using step _ (C + r) i j ih
  have general (pairs : Finset (Fin n × Fin n)) :
      ∀ e, B + ((k * pairs.card : ℕ) : ℤ) < totalExponent e →
        polynomialAction (∏ p ∈ pairs,
          UniformGradedLocalCorrelator.pairPolynomial p.1 p.2 ^ k) F e = 0 := by
    induction pairs using Finset.induction_on with
    | empty => simpa using hF
    | @insert p pairs hp ih =>
      rw [Finset.prod_insert hp, map_mul, map_pow,
        UniformGradedLocalCorrelator.action_pair, Module.End.mul_apply]
      simpa [Finset.card_insert_of_notMem hp, Nat.mul_add, Nat.cast_add, add_assoc]
        using power _ (B + (k * pairs.card : ℕ)) p.1 p.2 ih k
  exact general (labelledPairs n)

/-- Testing the supplied actual n-word common series gives an explicit total
degree bound. The vector series and all its clearing witnesses stay fixed. -/
theorem actual_word_scalar_numerator_support (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D)
    (δ : Charge D) (w : Sector D δ) (k : ℕ) (a : Fin n → ℕ)
    (P : MvPowerSeries (Fin n) (Carrier D))
    (common : ∀ e : Fin n → ℤ,
      polynomialAction (clearingPolynomial n k)
        (coefficientDistribution
          (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i)))
          (inclusion D δ w) 1 (List.ofFn (fun i : Fin n => i)))
        (fun i => e i - (a i : ℤ)) = signedExtend P e)
    (p : Oscillator D) (d : Fin n →₀ ℕ)
    (hne : ((readout D p).comp (projection D ((∑ i, c i) + δ))) (P d) ≠ 0) :
    (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p := by
  classical
  by_contra low
  let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
  have hc := congrArg φ (common (fun i => (d i : ℤ)))
  have hind : signedIndex (fun i => (d i : ℤ)) = d := by
    ext i
    simp [signedIndex]
  rw [signedExtend, if_pos (fun i => Int.natCast_nonneg (d i)), hind] at hc
  apply hne
  rw [← hc, polynomialAction_map]
  apply clearing_zero_above _ _ k (word_readout_zero_above D J hJG hGJ n c s δ w p)
  have total : totalExponent (fun i => (d i : ℤ) - (a i : ℤ)) =
      (d.degree : ℤ) - ∑ i, (a i : ℤ) := by
    simp [totalExponent, Finset.sum_sub_distrib, Finsupp.degree_eq_sum, Nat.cast_sum]
  rw [total]
  unfold wordDegreeBound at low
  omega

/-- Every finite actual lattice word has a unique finite scalar common
numerator. k depends only on the fields; a and the same vector P precede p.
All signed permutation identities and original truncations are retained. -/
theorem ordinary_actual_word_finite_scalar_numerator
    (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D) :
    let A := fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))
    let order := List.ofFn (fun i : Fin n => i)
    ∃ k : ℕ,
      (∀ i j : Fin n, i < j → (deltaEnd ^ k) (commutator (A i) (A j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin n → ℕ,
        ∃ P : MvPowerSeries (Fin n) (Carrier D),
        (∀ (i : Fin n) (m : ℤ), (a i : ℤ) ≤ m → (A i [[m]]) (inclusion D δ w) = 0) ∧
        (∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
          polynomialAction (clearingPolynomial n k)
            (coefficientDistribution A (inclusion D δ w) 1 other)
            (fun i => e i - (a i : ℤ)) = signedExtend P e) ∧
        ∀ p : Oscillator D,
          let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
          let S : MvPowerSeries (Fin n) ℂ := fun d => φ (P d)
          (∀ d, S d ≠ 0 → (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p) ∧
          ∃! R : MvPolynomial (Fin n) ℂ,
            (R : MvPowerSeries (Fin n) ℂ) = S ∧
            R.totalDegree ≤ (wordDegreeBound D c δ k a p).toNat ∧
            (wordDegreeBound D c δ k a p < 0 → S = 0 ∧ R = 0) ∧
            ∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
              polynomialAction (clearingPolynomial n k)
                (fun b => φ (coefficientDistribution A (inclusion D δ w) 1 other b))
                (fun i => e i - (a i : ℤ)) = signedExtend (R : MvPowerSeries (Fin n) ℂ) e := by
  classical
  dsimp only
  let A := fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))
  let order := List.ofFn (fun i : Fin n => i)
  have localFields : ∀ i j : Fin n, i < j →
      ∃ r : ℕ, (deltaEnd ^ r) (commutator (A i) (A j)) = 0 := by
    intro i j _
    obtain ⟨r, hr⟩ := LatticeAllStateLocality.stateField_locality D
      (inclusion D (c i) (s i)) (inclusion D (c j) (s j))
    refine ⟨r, ?_⟩
    rw [Module.End.pow_apply]
    exact hr
  obtain ⟨k, hk, rest⟩ := ungraded_local_word_common_series A order
    (by simp [order, List.nodup_ofFn]) (by intro i; simp [order]) localFields
  refine ⟨k, hk, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, common⟩ := rest (inclusion D δ w)
  refine ⟨a, P, truncation, common, ?_⟩
  intro p
  let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
  let S : MvPowerSeries (Fin n) ℂ := fun d => φ (P d)
  have support : ∀ d, S d ≠ 0 → (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p :=
    actual_word_scalar_numerator_support D J hJG hGJ n c s δ w k a P
      (common order (List.Perm.refl _)) p
  obtain ⟨R, heq, hdeg, hneg⟩ := polynomial_of_degree_support S
    (wordDegreeBound D c δ k a p) support
  refine ⟨support, R, ⟨heq, hdeg, hneg, ?_⟩, ?_⟩
  · intro other hp e
    have h := congrArg φ (common other hp e)
    rw [polynomialAction_map, signedExtend_map] at h
    rw [heq]
    exact h
  · intro R' hR'
    exact MvPolynomial.coe_injective (Fin n) ℂ (hR'.1.trans heq.symm)

end
end D5.S3.VertexAlgebra.LatticeSectorScalarNumerator
