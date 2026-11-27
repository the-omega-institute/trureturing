/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedStateEnergy
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The total oscillator and momentum energy on the order-three state carrier. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificateDraft
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The total energy on the constructed P48q order-three state carrier. Identifying
this operator with the zero mode of a full twisted conformal field is a subsequent step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

open LatticeGeneratingFieldLocality (bilinear)
open P48qTwistedChargeAction (Ground Momentum lattice)
open P48qThirdTwistedField (Fock Mode State frequency)
open P48qMomentumEnergy (fixedBasis momentumCasimir momentumCasimir_single
  momentumCasimir_ker_fixedBasis)
open P48qGramCertificateDraft (nebeGram)
open ThirdCoverSixteenPairSpectrum (MovingFock MovingVariable fractionalLZero
  fractionalLZero_monomial totalOccupationEnergy)
open Module.End MvPolynomial
open scoped BigOperators Matrix TensorProduct

noncomputable section

abbrev Occupation := Mode →₀ ℕ

/-- The normalized creation-annihilation number term at cover frequency `frequency j`. -/
def numberTerm (j : Mode) : Module.End ℂ Fock :=
  ((frequency j : ℂ) / 3) •
    (LinearMap.mulLeft ℂ (X j : Fock)).comp (pderiv j).toLinearMap

theorem numberTerm_apply (j : Mode) (P : Fock) :
    numberTerm j P = ((frequency j : ℂ) / 3) • (X j * pderiv j P) := rfl

private theorem numberTerm_support (P : Fock) :
    Function.support (fun j => numberTerm j P) ⊆ (P.vars : Set Mode) := by
  intro j hj
  change j ∈ P.vars
  by_contra h
  refine hj ?_
  change numberTerm j P = 0
  rw [numberTerm_apply, pderiv_eq_zero_of_notMem_vars h, mul_zero, smul_zero]

private theorem numberTerm_finite (P : Fock) :
    Function.HasFiniteSupport (fun j => numberTerm j P) :=
  P.vars.finite_toSet.subset (numberTerm_support P)

/-- The weighted Euler endomorphism, defined by the pointwise finite sum of
the actual partial-derivative operators. -/
def oscillator : Module.End ℂ Fock where
  toFun P := ∑ᶠ j, numberTerm j P
  map_add' P Q := by
    simp only [map_add]
    exact finsum_add_distrib (numberTerm_finite P) (numberTerm_finite Q)
  map_smul' c P := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (numberTerm_finite P)).symm

theorem oscillator_eq_sum (P : Fock) :
    oscillator P = ∑ j ∈ P.vars, ((frequency j : ℂ) / 3) • (X j * pderiv j P) := by
  calc
    oscillator P = ∑ j ∈ P.vars, numberTerm j P :=
      finsum_eq_sum_of_support_subset _ (numberTerm_support P)
    _ = _ := by simp only [numberTerm_apply]

/-- The integral sum of cover frequencies with multiplicity. -/
def occupationFrequency (d : Occupation) : ℕ := d.sum fun j e => frequency j * e

@[simp] theorem occupationFrequency_eq_zero_iff (d : Occupation) :
    occupationFrequency d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    apply Finsupp.ext
    intro j
    change d j = 0
    by_contra hj
    have hle : frequency j * d j ≤ occupationFrequency d :=
      Finset.single_le_sum (f := fun k : Mode => frequency k * d k)
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj)
    have hpos : 0 < frequency j * d j :=
      Nat.mul_pos (Nat.succ_pos j.2) (Nat.pos_of_ne_zero hj)
    rw [hd] at hle
    exact Nat.not_lt_of_ge hle hpos
  · rintro rfl
    simp [occupationFrequency]

theorem oscillator_monomial (d : Occupation) (a : ℂ) :
    oscillator (monomial d a) = ((occupationFrequency d : ℂ) / 3) • monomial d a := by
  have hterm (j : Mode) : numberTerm j (monomial d a) =
      (((frequency j * d j : ℕ) : ℂ) / 3) • monomial d a := by
    rw [numberTerm_apply, X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, Nat.cast_mul, div_mul_eq_mul_div₀]
  have hs : Function.support (fun j => numberTerm j (monomial d a)) ⊆
      (d.support : Set Mode) := by
    intro j hj
    change j ∈ d.support
    by_contra h
    refine hj ?_
    change numberTerm j (monomial d a) = 0
    rw [hterm, Finsupp.notMem_support_iff.mp h, mul_zero, Nat.cast_zero,
      zero_div, zero_smul]
  change (∑ᶠ j, numberTerm j (monomial d a)) =
    (((∑ j ∈ d.support, frequency j * d j : ℕ) : ℂ) / 3) • monomial d a
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp_rw [hterm]
  rw [← Finset.sum_smul, ← Finset.sum_div, ← Nat.cast_sum]

theorem oscillator_coeff (P : Fock) (d : Occupation) :
    (oscillator P).coeff d = ((occupationFrequency d : ℂ) / 3) * P.coeff d := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, coeff_sum, oscillator_monomial, coeff_smul, smul_eq_mul,
    coeff_monomial, mul_ite, mul_zero, Finset.sum_ite_eq']
  by_cases hd : d ∈ P.support
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd, notMem_support_iff.mp hd, mul_zero]

/-- Inclusion of the two nonzero residue classes in the full mode set. -/
def movingMode (j : MovingVariable) : Mode := (j.1, j.2.val)

private theorem occupationFrequency_moving (d : MovingVariable →₀ ℕ) :
    occupationFrequency (d.mapDomain movingMode) = totalOccupationEnergy d := by
  unfold occupationFrequency totalOccupationEnergy
  exact Finsupp.sum_mapDomain_index (fun j => mul_zero (frequency j))
    (fun j a b => mul_add (frequency j) a b)

/-- On the moving variables, the Euler operator plus its vacuum shift is the
actual sum of the sixteen lifted fractional zero modes. -/
theorem oscillator_add_shift_rename_moving (Q : MovingFock) :
    oscillator (rename movingMode Q) + (16 / 9 : ℂ) • rename movingMode Q =
      rename movingMode (fractionalLZero Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [rename_monomial, oscillator_monomial, occupationFrequency_moving,
      fractionalLZero_monomial, map_smul, rename_monomial, ← add_smul, add_comm]
  | add P Q hP hQ =>
    simp only [map_add, smul_add]
    rw [add_add_add_comm, hP, hQ]

/-- Half the squared physical momentum. The norm-image index is three times
the physical momentum. -/
def momentumWeight (p : Momentum) : ℝ := (bilinear lattice p.1 p.1 : ℝ) / 18

private theorem complex_momentumWeight (p : Momentum) :
    (momentumWeight p : ℂ) = (bilinear lattice p.1 p.1 : ℂ) / 18 := by
  simp only [momentumWeight, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]

theorem momentumWeight_nonneg (p : Momentum) : 0 ≤ momentumWeight p := by
  let x : Fin 48 → ℝ := fun i => (p.1 i : ℝ)
  let G : Matrix (Fin 48) (Fin 48) ℝ := nebeGram.map (Int.cast : ℤ → ℝ)
  have hquad : 0 ≤ G.toBilin' x x := by
    rw [Matrix.toBilin'_apply']
    have hPos := P48qMomentumEnergy.nebeGram_posDef.posSemidef.dotProduct_mulVec_nonneg x
    rw [star_trivial] at hPos
    exact hPos
  have hnorm : G.toBilin' x x = (bilinear lattice p.1 p.1 : ℝ) := by
    change (lattice.G.map (Int.cast : ℤ → ℝ)).toBilin'
      (fun i => (p.1 i : ℝ)) (fun i => (p.1 i : ℝ)) = _
    simp only [Matrix.toBilin'_apply, Matrix.map_apply, bilinear, Int.cast_sum, Int.cast_mul]
  rw [hnorm] at hquad
  exact div_nonneg hquad (by norm_num)

@[simp] theorem momentumWeight_zero : momentumWeight 0 = 0 := by
  simp [momentumWeight, bilinear]

theorem momentumWeight_eq_zero_iff (p : Momentum) : momentumWeight p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hcast : (momentumWeight p : ℂ) = 0 := by simp [h]
    have hk : Finsupp.single p (1 : ℂ) ∈ (momentumCasimir fixedBasis).ker := by
      rw [LinearMap.mem_ker, momentumCasimir_single, ← complex_momentumWeight p, hcast, zero_smul]
    rw [momentumCasimir_ker_fixedBasis, Submodule.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    by_contra hp
    have hcoord := congrArg (fun v : Ground => v p) hc
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (by
      simpa only [Finsupp.smul_apply, Finsupp.single_eq_of_ne hp, smul_zero,
        Finsupp.single_eq_same] using hcoord)
  · rintro rfl
    exact momentumWeight_zero

private def stateTensor : Ground ⊗[ℂ] Fock ≃ₗ[ℂ] State :=
  TensorProduct.finsuppScalarLeft ℂ Fock Momentum

/-- The fixed Cartan Casimir extended by the identity on the oscillator factor. -/
def momentumEnergy : Module.End ℂ State :=
  stateTensor.conj ((momentumCasimir fixedBasis).rTensor Fock)

theorem momentumEnergy_single (p : Momentum) (P : Fock) :
    momentumEnergy (Finsupp.single p P) = (momentumWeight p : ℂ) • Finsupp.single p P := by
  have hs : stateTensor.symm (Finsupp.single p P) = Finsupp.single p (1 : ℂ) ⊗ₜ[ℂ] P :=
    TensorProduct.finsuppScalarLeft_symm_apply_single p P
  rw [momentumEnergy, LinearEquiv.conj_apply_apply, hs, LinearMap.rTensor_tmul,
    momentumCasimir_single, ← complex_momentumWeight p, ← TensorProduct.smul_tmul', map_smul,
    ← hs, LinearEquiv.apply_symm_apply]

theorem momentumEnergy_apply (v : State) (p : Momentum) :
    momentumEnergy v p = (momentumWeight p : ℂ) • v p := by
  have h : (Finsupp.lapply p : State →ₗ[ℂ] Fock).comp momentumEnergy =
      (momentumWeight p : ℂ) • (Finsupp.lapply p : State →ₗ[ℂ] Fock) := by
    apply Finsupp.lhom_ext
    intro q P
    simp only [LinearMap.comp_apply, momentumEnergy_single, LinearMap.smul_apply,
      Finsupp.lapply_apply, Finsupp.smul_apply]
    by_cases hp : p = q
    · subst q
      rfl
    · simp only [Finsupp.single_eq_of_ne hp, smul_zero]
  exact DFunLike.congr_fun h v

/-- The oscillator zero mode, the Cartan Casimir and the sixteen-pair shift. -/
def totalLZero : Module.End ℂ State :=
  Finsupp.mapRange.linearMap oscillator + momentumEnergy + (16 / 9 : ℂ) • LinearMap.id

theorem totalLZero_apply (v : State) (p : Momentum) :
    totalLZero v p = oscillator (v p) + (momentumWeight p : ℂ) • v p +
      (16 / 9 : ℂ) • v p := by
  simp only [totalLZero, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, momentumEnergy_apply]

/-- The joint weight of an occupation monomial in a fixed momentum sector. -/
def totalWeight (p : Momentum) (d : Occupation) : ℝ :=
  16 / 9 + (occupationFrequency d : ℝ) / 3 + momentumWeight p

private theorem complex_totalWeight (p : Momentum) (d : Occupation) :
    (totalWeight p d : ℂ) = (16 / 9 : ℂ) + (occupationFrequency d : ℂ) / 3 +
      (momentumWeight p : ℂ) := by
  simp only [totalWeight, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast]

theorem totalLZero_single_monomial (p : Momentum) (d : Occupation) (a : ℂ) :
    totalLZero (Finsupp.single p (monomial d a)) =
      (totalWeight p d : ℂ) • Finsupp.single p (monomial d a) := by
  simp only [totalLZero, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, oscillator_monomial,
    momentumEnergy_single, ← Finsupp.smul_single, ← add_smul, complex_totalWeight]
  congr 1
  ring

/-- Every momentum and occupation coefficient of the constructed operator,
on an arbitrary state. -/
theorem totalLZero_coeff (v : State) (p : Momentum) (d : Occupation) :
    (totalLZero v p).coeff d = (totalWeight p d : ℂ) * (v p).coeff d := by
  rw [totalLZero_apply]
  change lcoeff ℂ d (oscillator (v p) + (momentumWeight p : ℂ) • v p +
    (16 / 9 : ℂ) • v p) = _
  simp only [map_add, lcoeff_apply, oscillator_coeff, coeff_smul, smul_eq_mul, complex_totalWeight]
  ring

private theorem weight_eq_of_coeff_ne_zero {v : State} {a : ℂ} {p : Momentum} {d : Occupation}
    (heig : totalLZero v = a • v) (hd : (v p).coeff d ≠ 0) : (totalWeight p d : ℂ) = a := by
  have h := congrArg (fun w : State => (w p).coeff d) heig
  change (totalLZero v p).coeff d = ((a • v) p).coeff d at h
  rw [totalLZero_coeff, Finsupp.smul_apply, coeff_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ hd h

/-- The algebraic point spectrum over `ℂ`, expressed by real joint weights. -/
theorem totalLZero_eigenvalues (a : ℂ) :
    (∃ v : State, v ≠ 0 ∧ totalLZero v = a • v) ↔
      ∃ (p : Momentum) (d : Occupation), a = (totalWeight p d : ℂ) := by
  constructor
  · rintro ⟨v, hv, heig⟩
    obtain ⟨p, d, hd⟩ : ∃ (p : Momentum) (d : Occupation), (v p).coeff d ≠ 0 := by
      by_contra! h
      apply hv
      apply Finsupp.ext
      intro p
      apply MvPolynomial.ext
      intro d
      simpa using h p d
    exact ⟨p, d, (weight_eq_of_coeff_ne_zero heig hd).symm⟩
  · rintro ⟨p, d, rfl⟩
    refine ⟨Finsupp.single p (monomial d (1 : ℂ)), Finsupp.single_ne_zero.mpr ?_,
      totalLZero_single_monomial p d 1⟩
    classical
    intro h
    have hcoeff := congrArg (fun P : Fock => P.coeff d) h
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using hcoeff)

theorem totalWeight_lower_bound (p : Momentum) (d : Occupation) : 16 / 9 ≤ totalWeight p d := by
  have hp := momentumWeight_nonneg p
  have hd : 0 ≤ (occupationFrequency d : ℝ) := Nat.cast_nonneg _
  unfold totalWeight
  linarith

theorem totalWeight_eq_vacuum_iff (p : Momentum) (d : Occupation) :
    totalWeight p d = 16 / 9 ↔ p = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hp := momentumWeight_nonneg p
    have hd : 0 ≤ (occupationFrequency d : ℝ) := Nat.cast_nonneg _
    unfold totalWeight at h
    have hmomentum : momentumWeight p = 0 := by linarith
    have hfrequency : (occupationFrequency d : ℝ) = 0 := by linarith
    exact ⟨(momentumWeight_eq_zero_iff p).mp hmomentum,
      (occupationFrequency_eq_zero_iff d).mp (by exact_mod_cast hfrequency)⟩
  · rintro ⟨rfl, rfl⟩
    simp [totalWeight, occupationFrequency]

/-- The constant polynomial on the zero momentum line. -/
def vacuum : State := Finsupp.single 0 1

theorem vacuum_ne_zero : vacuum ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero

theorem totalLZero_vacuum : totalLZero vacuum = (16 / 9 : ℂ) • vacuum := by
  have hweight := (totalWeight_eq_vacuum_iff 0 0).mpr ⟨rfl, rfl⟩
  simpa only [vacuum, monomial_zero', map_one, hweight, Complex.ofReal_div, Complex.ofReal_ofNat]
    using totalLZero_single_monomial (0 : Momentum) (0 : Occupation) (1 : ℂ)

theorem totalLZero_minimum :
    IsLeast {x : ℝ | ∃ v : State, v ≠ 0 ∧ totalLZero v = (x : ℂ) • v} (16 / 9) := by
  refine ⟨⟨vacuum, vacuum_ne_zero, ?_⟩, ?_⟩
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using totalLZero_vacuum
  · rintro x ⟨v, hv, heig⟩
    obtain ⟨p, d, h⟩ := (totalLZero_eigenvalues (x : ℂ)).mp ⟨v, hv, heig⟩
    change (16 / 9 : ℝ) ≤ x
    rw [Complex.ofReal_injective h]
    exact totalWeight_lower_bound p d

theorem totalLZero_ground_eigenspace :
    totalLZero.eigenspace (16 / 9 : ℂ) = Submodule.span ℂ ({vacuum} : Set State) := by
  apply le_antisymm
  · intro v hv
    have heig := mem_eigenspace_iff.mp hv
    have hindices (p : Momentum) (d : Occupation) (hd : (v p).coeff d ≠ 0) :
        p = 0 ∧ d = 0 := by
      apply (totalWeight_eq_vacuum_iff p d).mp
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
        weight_eq_of_coeff_ne_zero heig hd
    have hconstant : v 0 = monomial 0 ((v 0).coeff 0) := by
      apply eq_monomial_of_support_subset_singleton
      intro d hd
      exact (hindices 0 d (mem_support_iff.mp hd)).2
    refine Submodule.mem_span_singleton.mpr ⟨(v 0).coeff 0, ?_⟩
    apply Finsupp.ext
    intro p
    by_cases hp : p = 0
    · subst p
      simpa only [vacuum, Finsupp.smul_apply, Finsupp.single_eq_same, monomial_zero',
        C_eq_smul_one] using hconstant.symm
    · have hsector : v p = 0 := by
        apply MvPolynomial.ext
        intro d
        have hcoeff : (v p).coeff d = 0 := by
          by_contra hd
          exact hp (hindices p d hd).1
        simpa using hcoeff
      simp only [vacuum, Finsupp.smul_apply, Finsupp.single_eq_of_ne hp, smul_zero, hsector]
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (mem_eigenspace_iff.mpr totalLZero_vacuum)

/-- The constructed total zero mode has lowest eigenvalue `16 / 9` and a
one-dimensional vacuum eigenspace generated by `e₀ ⊗ 1`. -/
theorem totalLZero_vacuum_spectrum :
    IsLeast {x : ℝ | ∃ v : State, v ≠ 0 ∧ totalLZero v = (x : ℂ) • v} (16 / 9) ∧
    totalLZero.eigenspace (16 / 9 : ℂ) = Submodule.span ℂ ({vacuum} : Set State) ∧
    Module.finrank ℂ (totalLZero.eigenspace (16 / 9 : ℂ)) = 1 := by
  refine ⟨totalLZero_minimum, totalLZero_ground_eigenspace, ?_⟩
  rw [totalLZero_ground_eigenspace]
  exact finrank_span_singleton vacuum_ne_zero

#print axioms oscillator_eq_sum
#print axioms oscillator_add_shift_rename_moving
#print axioms totalLZero_eigenvalues
#print axioms totalLZero_vacuum_spectrum

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
