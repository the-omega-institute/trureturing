/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedCurrentCasimir
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-current Casimir decomposition of the actual P48q twisted energy operator. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! The fixed block in `P48qConformalVectorDecomposition.omega_decomposition`
on the full twisted State, using the primary modes of `P48qFixedCurrentIterate`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentCasimir

open LatticeGeneratingFieldLocality (bilinear)
open P48qTwistedChargeAction (Ground Momentum lattice)
open P48qThirdTwistedField (Fock Mode State frequency)
open P48qMomentumEnergy (fixedBasis fixedGram fixedGramDual fixedGram_pair_dual
  fixedGram_symm physicalMomentum cartanZeroMode cartanZeroMode_single
  momentumCasimir momentumCasimir_coeff)
open P48qFixedCurrentIterate (fixedVariable frequency_fixedVariable
  creationPolynomial annihilationMode_apply zeroTerm zeroTerm_positive
  zeroTerm_basis_dual_negative zeroTerm_zero_apply coverBound zeroTermIndices
  normalOrderedZero normalOrderedZero_apply)
open P48qTwistedStateEnergy (numberTerm numberTerm_apply oscillator_eq_sum
  momentumEnergy momentumEnergy_apply momentumWeight totalLZero totalLZero_apply)
open MvPolynomial
open scoped BigOperators

noncomputable section

private theorem sum_creationPolynomial_dual (j : Fin 16) (n : ℕ) :
    (∑ i : Fin 16, fixedGram (fixedBasis i) (fixedBasis j) •
      creationPolynomial (fixedGramDual fixedBasis i) n) = X (fixedVariable j n) := by
  classical
  have hComplete :
      (∑ i : Fin 16, fixedGram (fixedBasis i) (fixedBasis j) •
        fixedGramDual fixedBasis i) = fixedBasis j := by
    simpa only [fixedGramDual, LinearMap.BilinForm.dualBasis_repr_apply,
      fixedGram_symm.eq (fixedBasis j)] using
      (fixedGramDual fixedBasis).sum_repr (fixedBasis j)
  calc
    _ = creationPolynomial (∑ i : Fin 16, fixedGram (fixedBasis i) (fixedBasis j) •
          fixedGramDual fixedBasis i) n := by
      simp only [creationPolynomial, Finset.smul_sum, LinearMap.BilinForm.sum_left,
        LinearMap.BilinForm.smul_left, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    _ = X (fixedVariable j n) := by
      rw [hComplete]
      simp only [creationPolynomial, fixedGram_pair_dual, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- At positive physical index the dual basis supplies the creation operator.
Dual completeness makes the resulting sum the same Euler summand as at the
opposite index. -/
theorem sum_zeroTerm_basis_dual_positive (n : ℕ) (w : State) (p : Momentum) :
    (∑ i : Fin 16, zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i)
      (Int.ofNat (n + 1)) w p) = ∑ j : Fin 16, numberTerm (fixedVariable j n) (w p) := by
  classical
  simp only [zeroTerm_positive, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, annihilationMode_apply, Finset.mul_sum,
    mul_smul_comm, numberTerm_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_creationPolynomial_dual j n, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, smul_smul]

private def integerNumberTerm (j : Mode) : Module.End ℂ Fock :=
  if 3 ∣ frequency j then numberTerm j else 0

private theorem integerNumberTerm_support (P : Fock) :
    Function.support (fun j => integerNumberTerm j P) ⊆
      ((P.vars.filter fun j => 3 ∣ frequency j) : Set Mode) := by
  intro j hj
  change integerNumberTerm j P ≠ 0 at hj
  change j ∈ P.vars.filter (fun j => 3 ∣ frequency j)
  rw [Finset.mem_filter]
  by_cases hd : 3 ∣ frequency j
  · refine ⟨?_, hd⟩
    by_contra hv
    exact hj (by rw [integerNumberTerm, if_pos hd, numberTerm_apply,
      pderiv_eq_zero_of_notMem_vars hv, mul_zero, smul_zero])
  · exact (hj (by simp only [integerNumberTerm, if_neg hd, LinearMap.zero_apply])).elim

private theorem integerNumberTerm_finite (P : Fock) :
    Function.HasFiniteSupport (fun j => integerNumberTerm j P) :=
  (P.vars.filter fun j => 3 ∣ frequency j).finite_toSet.subset (integerNumberTerm_support P)

/-- The part of the native weighted Euler endomorphism at integer physical frequencies. -/
def integerOscillator : Module.End ℂ Fock where
  toFun P := ∑ᶠ j : Mode, integerNumberTerm j P
  map_add' P Q := by
    simp only [map_add]
    exact finsum_add_distrib (integerNumberTerm_finite P) (integerNumberTerm_finite Q)
  map_smul' c P := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (integerNumberTerm_finite P)).symm

theorem integerOscillator_eq_sum (P : Fock) :
    integerOscillator P =
      ∑ j ∈ P.vars.filter (fun j => 3 ∣ frequency j), numberTerm j P := by
  change (∑ᶠ j : Mode, integerNumberTerm j P) = _
  rw [finsum_eq_sum_of_support_subset _ (integerNumberTerm_support P)]
  exact Finset.sum_congr rfl fun j hj => by
    rw [integerNumberTerm, if_pos (Finset.mem_filter.mp hj).2]

private def fixedVariableEmbedding : Mode ↪ Mode where
  toFun j := fixedVariable j.1 j.2
  inj' := by
    rintro ⟨i, n⟩ ⟨j, m⟩ h
    change (i, 3 * n + 2) = (j, 3 * m + 2) at h
    have hrow : i = j := congrArg Prod.fst h
    have hfreq : 3 * n + 2 = 3 * m + 2 := congrArg Prod.snd h
    exact Prod.ext hrow (by omega)

private theorem integerOscillator_eq_sum_range (w : State) (p : Momentum) :
    integerOscillator (w p) =
      ∑ n ∈ Finset.range (coverBound w / 3), ∑ i : Fin 16,
        numberTerm (fixedVariable i n) (w p) := by
  classical
  let s : Finset Mode := (Finset.univ : Finset (Fin 16)) ×ˢ Finset.range (coverBound w / 3)
  have hs : Function.support (fun j => integerNumberTerm j (w p)) ⊆
      (s.map fixedVariableEmbedding : Set Mode) := by
    intro j hj
    have hj' : j ∈ (w p).vars.filter (fun j => 3 ∣ frequency j) :=
      integerNumberTerm_support (w p) hj
    obtain ⟨hv, hd⟩ := Finset.mem_filter.mp hj'
    have hp : p ∈ w.support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      simpa [hz] using hv
    have hlocal : frequency j ≤ (w p).vars.sup frequency := Finset.le_sup hv
    have hglobal : (w p).vars.sup frequency ≤ coverBound w :=
      Finset.le_sup (f := fun q => (w q).vars.sup frequency) hp
    have hfreq := hlocal.trans hglobal
    rcases j with ⟨i, r⟩
    obtain ⟨t, ht⟩ := hd
    change r + 1 = 3 * t at ht
    change r + 1 ≤ coverBound w at hfreq
    have hlt : t - 1 < coverBound w / 3 := by omega
    change (i, r) ∈ s.map fixedVariableEmbedding
    refine Finset.mem_map.mpr ⟨(i, t - 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlt⟩
    · change (i, 3 * (t - 1) + 2) = (i, r)
      exact Prod.ext rfl (by omega)
  change (∑ᶠ j : Mode, integerNumberTerm j (w p)) = _
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_map]
  change (∑ j ∈ (Finset.univ : Finset (Fin 16)) ×ˢ Finset.range (coverBound w / 3),
    integerNumberTerm (fixedVariable j.1 j.2) (w p)) = _
  rw [Finset.sum_product_right (Finset.univ : Finset (Fin 16))
    (Finset.range (coverBound w / 3)) (fun j => integerNumberTerm (fixedVariable j.1 j.2) (w p))]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => ?_
  have hd : 3 ∣ frequency (fixedVariable i n) := ⟨n + 1, frequency_fixedVariable i n⟩
  rw [integerNumberTerm, if_pos hd]

private def negativeIndex : ℕ ↪ ℤ :=
  ⟨Int.negSucc, fun _ _ h => Int.negSucc.inj h⟩

private def positiveIndex : ℕ ↪ ℤ :=
  ⟨fun n => Int.ofNat (n + 1), fun _ _ h => Nat.succ.inj (Int.ofNat.inj h)⟩

private theorem sum_nonzero_indices (w : State) (f : ℤ → Fock) :
    (∑ k ∈ (zeroTermIndices w).erase 0, f k) =
      (∑ n ∈ Finset.range (coverBound w / 3), f (Int.negSucc n)) +
      ∑ n ∈ Finset.range (coverBound w / 3), f (Int.ofNat (n + 1)) := by
  classical
  let b := coverBound w / 3
  have hneg (n : ℕ) : Int.negSucc n ∈ (zeroTermIndices w).erase 0 ↔ n < b := by
    simp only [Finset.mem_erase, zeroTermIndices, Finset.mem_Icc, Int.negSucc_eq]
    change _ ↔ n < coverBound w / 3
    omega
  have hpos (n : ℕ) : Int.ofNat (n + 1) ∈ (zeroTermIndices w).erase 0 ↔ n < b := by
    simp only [Finset.mem_erase, zeroTermIndices, Finset.mem_Icc, Int.ofNat_eq_natCast]
    change _ ↔ n < coverBound w / 3
    omega
  have hindices : (zeroTermIndices w).erase 0 =
      ((Finset.range b).map negativeIndex) ∪ ((Finset.range b).map positiveIndex) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_range]
    change k ∈ (zeroTermIndices w).erase 0 ↔
      (∃ n : ℕ, n < b ∧ Int.negSucc n = k) ∨ (∃ n : ℕ, n < b ∧ Int.ofNat (n + 1) = k)
    constructor
    · intro hk
      cases k with
      | negSucc n => exact Or.inl ⟨n, (hneg n).mp hk, rfl⟩
      | ofNat n =>
        cases n with
        | zero => exact ((Finset.mem_erase.mp hk).1 rfl).elim
        | succ n => exact Or.inr ⟨n, (hpos n).mp hk, rfl⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
      · exact (hneg n).mpr hn
      · exact (hpos n).mpr hn
  have hdisjoint : Disjoint ((Finset.range b).map negativeIndex)
      ((Finset.range b).map positiveIndex) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    obtain ⟨n, _, hn⟩ := Finset.mem_map.mp hk
    obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hl
    change Int.negSucc n = k at hn
    change Int.ofNat (m + 1) = k at hm
    have hlt := Int.negSucc_lt_zero n
    rw [hn, ← hm] at hlt
    exact (not_lt_of_ge (Int.ofNat_nonneg (m + 1))) hlt
  rw [hindices, Finset.sum_union hdisjoint]
  simp only [Finset.sum_map, negativeIndex, positiveIndex, Function.Embedding.coeFn_mk, b]

private theorem half_sum_zeroTerm_zero (w : State) (p : Momentum) :
    (2 : ℂ)⁻¹ • (∑ i : Fin 16, zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i) 0 w p) =
      momentumEnergy w p := by
  let x := physicalMomentum p
  let e : Ground := Finsupp.single p 1
  have hground : momentumCasimir fixedBasis e p =
      (2 : ℂ)⁻¹ * ∑ i : Fin 16, fixedGram (fixedGramDual fixedBasis i) x *
        fixedGram (fixedBasis i) x := by
    rw [momentumCasimir, LinearMap.smul_apply, Finsupp.smul_apply]
    change (2 : ℂ)⁻¹ * (Finsupp.lapply p : Ground →ₗ[ℂ] ℂ)
      ((∑ i : Fin 16, (cartanZeroMode (fixedGramDual fixedBasis i)).comp
        (cartanZeroMode (fixedBasis i))) (Finsupp.single p 1)) = _
    rw [LinearMap.sum_apply, map_sum]
    simp only [LinearMap.comp_apply, cartanZeroMode_single,
      map_smul, Finsupp.lapply_apply, Finsupp.single_eq_same, smul_eq_mul, one_mul, mul_comm, x]
  have hnorm : (2 : ℂ)⁻¹ * (∑ i : Fin 16, fixedGram (fixedGramDual fixedBasis i) x *
        fixedGram (fixedBasis i) x) = (bilinear lattice p.1 p.1 : ℂ) / 18 := by
    have h := momentumCasimir_coeff fixedBasis e p
    rw [hground] at h
    simpa only [e, Finsupp.single_eq_same, mul_one] using h
  rw [momentumEnergy_apply]
  simp only [zeroTerm_zero_apply, ← Finset.sum_smul, smul_smul]
  change ((2 : ℂ)⁻¹ * ∑ i : Fin 16, fixedGram (fixedGramDual fixedBasis i) x *
    fixedGram (fixedBasis i) x) • w p = _
  rw [hnorm]
  simp only [momentumWeight, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]

/-- The half-weighted fixed block of the P48q conformal vector contributes the
integer-frequency oscillator energy and the Cartan momentum energy on State. -/
theorem half_sum_normalOrderedZero :
    (2 : ℂ)⁻¹ • (∑ i : Fin 16, normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i)) =
      Finsupp.mapRange.linearMap integerOscillator + momentumEnergy := by
  classical
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  have hnonzero :
      (∑ i : Fin 16, ∑ k ∈ (zeroTermIndices w).erase 0,
        zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i) k w p) =
        integerOscillator (w p) + integerOscillator (w p) := by
    rw [Finset.sum_comm, sum_nonzero_indices w, integerOscillator_eq_sum_range w p]
    simp only [zeroTerm_basis_dual_negative, sum_zeroTerm_basis_dual_positive]
  have hsplit (i : Fin 16) :
      normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i) w p =
        zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i) 0 w p +
          ∑ k ∈ (zeroTermIndices w).erase 0,
            zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i) k w p := by
    rw [normalOrderedZero_apply, zeroTerm_zero_apply]
  have hhalf (P : Fock) : (2 : ℂ)⁻¹ • (P + P) = P := by
    rw [← two_smul ℂ P, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, LinearMap.sum_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply]
  change (2 : ℂ)⁻¹ • (Finsupp.lapply p : State →ₗ[ℂ] Fock)
    (∑ i : Fin 16, normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i) w) =
      integerOscillator (w p) + momentumEnergy w p
  rw [map_sum]
  simp only [Finsupp.lapply_apply, hsplit, Finset.sum_add_distrib]
  rw [hnonzero, smul_add, half_sum_zeroTerm_zero, hhalf, add_comm]

/-- In the native total energy formula, the remaining Euler terms have
noninteger physical frequency. -/
theorem totalLZero_apply_fixedCurrent (w : State) (p : Momentum) :
    totalLZero w p =
      ((2 : ℂ)⁻¹ • (∑ i : Fin 16,
        normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i))) w p +
        (∑ j ∈ (w p).vars.filter (fun j => ¬ 3 ∣ frequency j), numberTerm j (w p)) +
        (16 / 9 : ℂ) • w p := by
  rw [totalLZero_apply, half_sum_normalOrderedZero, oscillator_eq_sum]
  simp only [LinearMap.add_apply, Finsupp.add_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, momentumEnergy_apply, integerOscillator_eq_sum, ← numberTerm_apply]
  rw [← Finset.sum_filter_add_sum_filter_not (w p).vars
    (fun j => 3 ∣ frequency j) (fun j => numberTerm j (w p))]
  ac_rfl

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentCasimir
