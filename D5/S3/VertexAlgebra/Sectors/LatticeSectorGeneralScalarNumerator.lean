/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorGeneralScalarNumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorGeneralScalarNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite scalar common numerators for all original lattice data. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy

/-!
Every finite word in the original lattice fields has a finite scalar common
numerator, including singular and indefinite lattice data. Finite grade
projections preserve a lower-energy bound through each entire word suffix.

proof_shape: ordinary_actual_word_finite_scalar_numerator: content
admission_basis: escape-witness
escape_witness: The inverse-free mode lower bound and list induction retain all
signed exponent and charge energies in every suffix. This new support invariant
is consumed by the factorial readout, the original clearing action, and exact
finite polynomial extraction of the supplied common vector series.
utility is none: these are unrestricted algebraic support and existence results,
not certified instances, bounded enumeration, checkers or numerical reductions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorGeneralScalarNumerator
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticePositiveEnergy SupportedChannelSeries MvPolynomial
open FieldNormalProductLocality LatticeSectorScalarNumerator
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open scoped BigOperators VertexOperator
noncomputable section

open private energy_le_of_mem_stateEnergies inclusion_energy_lower
  word_polynomial_of_degree_support clearing_zero_above
  from D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
open private inner_coefficient_expansion from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation

private theorem mode_energy_lower (D : LatticeData)
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
    have hg := LatticeCoefficientEnergy.actual_mode_grade D m n q _ _
      (gradeProjection_mem D m a) (gradeProjection_mem D n b)
    exact (mem_grade_iff D _ _).mp hg t (by omega)
  have expand := congrArg
    (fun x => carrierCoeffEquiv D (((LatticeAllStateField.Y D x)[[q]]) b) t)
    (sum_gradeProjections D a)
  rw [← expand]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply,
    Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro m hm
  have expandB := congrArg
    (fun x => carrierCoeffEquiv D
      (((LatticeAllStateField.Y D (gradeProjection D m a))[[q]]) x) t)
    (sum_gradeProjections D b)
  rw [← expandB]
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun n hn => vanish m hm n hn)

/-- Every surviving coefficient of an arbitrary actual lattice word retains
all signed mode and charge energies of its entire suffix. -/
private theorem actual_word_coefficient_energy_le (D : LatticeData)
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
  | nil => simpa [energy] using inclusion_energy_lower D δ w (ρ, T) hne
  | cons i l ih =>
    have bound := mode_energy_lower D
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

private theorem word_readout_zero_above (D : LatticeData)
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
    have bound := actual_word_coefficient_energy_le D n c s δ w
      (List.ofFn (fun i : Fin n => i)) e ((∑ i, c i) + δ) T hn
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Finset.sum_add_distrib] at bound
    unfold totalExponent at low
    omega
  change _ * (projection D ((∑ i, c i) + δ)
    (word _ _ e (inclusion D δ w))).coeff T = 0
  rw [hz, mul_zero]

/-- Testing the supplied actual n-word common series gives an explicit total
degree bound. The vector series and all its clearing witnesses stay fixed. -/
private theorem actual_word_scalar_numerator_support (D : LatticeData)
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
  rw [signedExtend, ite_eq_left (fun i => Int.natCast_nonneg (d i)), hind] at hc
  apply hne
  rw [← hc, polynomialAction_map]
  apply clearing_zero_above _ _ k (word_readout_zero_above D n c s δ w p)
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
    (D : LatticeData)
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
    (by
      change (List.ofFn (fun i : Fin n => i)).Nodup
      rw [List.nodup_ofFn]
      intro i j h
      exact h) (by intro i; simp [order]) localFields
  refine ⟨k, hk, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, common⟩ := rest (inclusion D δ w)
  refine ⟨a, P, truncation, common, ?_⟩
  intro p
  let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
  let S : MvPowerSeries (Fin n) ℂ := fun d => φ (P d)
  have support : ∀ d, S d ≠ 0 → (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p :=
    actual_word_scalar_numerator_support D n c s δ w k a P
      (common order (List.Perm.refl _)) p
  obtain ⟨R, heq, hdeg, hneg⟩ := word_polynomial_of_degree_support S
    (wordDegreeBound D c δ k a p) support
  refine ⟨support, R, ⟨heq, hdeg, hneg, ?_⟩, ?_⟩
  · intro other hp e
    have h := congrArg φ (common other hp e)
    rw [polynomialAction_map, signedExtend_map] at h
    rw [heq]
    exact h
  · intro R' hR'
    exact MvPolynomial.coe_injective (Fin n) ℂ (hR'.1.trans heq.symm)


#print axioms ordinary_actual_word_finite_scalar_numerator

end
end D5.S3.VertexAlgebra.LatticeSectorGeneralScalarNumerator
