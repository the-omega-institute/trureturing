/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedCurrentIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native minus-one iterate for two fixed currents at integral mode indices. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingPairIterate
import Mathlib.RingTheory.Binomial

/-!
Bakalov–Kac, arXiv:math/0402315v3, (3.13) at product index `-1` for
two fixed currents. The physical current indices are integers. An input
index `k` for the state field denotes the power `z^(-k/3-1)`, as in
`ThirdTwistedIterate`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate

open LatticeGeneratingFieldLocality (Carrier)
open LatticeAllStateReconstruction (mu)
open P48qTwistedChargeAction (lattice Ground Momentum)
open P48qThirdTwistedField (Fock Mode State frequency)
open P48qMomentumEnergy (Fixed fixedBasis fixedGram fixedGramDual fixedGram_pair_dual
  fixedGram_symm physicalMomentum cartanZeroMode cartanZeroMode_single)
open P48qTwistedStateEnergy (numberTerm numberTerm_apply)
open ThirdTwistedIterate (currentAlong)
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

/-- The variable with cover frequency `3 * (n + 1)` in row `i`. -/
def fixedVariable (i : Fin 16) (n : ℕ) : Mode := (i, 3 * n + 2)

theorem frequency_fixedVariable (i : Fin 16) (n : ℕ) :
    frequency (fixedVariable i n) = 3 * (n + 1) := by
  change 3 * n + 2 + 1 = 3 * (n + 1)
  omega

/-- Multiplication by the creation vector written in the native Fock variables. -/
def creationPolynomial (u : Fixed) (n : ℕ) : Fock :=
  ∑ i : Fin 16, fixedGram u (fixedGramDual fixedBasis i) • X (fixedVariable i n)

/-- The positive current mode at physical frequency `n + 1`. -/
def annihilationMode (u : Fixed) (n : ℕ) : Module.End ℂ Fock :=
  ∑ i : Fin 16,
    (((frequency (fixedVariable i n) : ℂ) / 3) * fixedGram u (fixedBasis i)) •
      (pderiv (fixedVariable i n)).toLinearMap

theorem annihilationMode_apply (u : Fixed) (n : ℕ) (P : Fock) :
    annihilationMode u n P =
      ∑ i : Fin 16, (((frequency (fixedVariable i n) : ℂ) / 3) *
        fixedGram u (fixedBasis i)) • pderiv (fixedVariable i n) P := by
  simp only [annihilationMode, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]

private def stateTensor : Ground ⊗[ℂ] Fock ≃ₗ[ℂ] State :=
  TensorProduct.finsuppScalarLeft ℂ Fock Momentum

/-- The native Cartan zero mode extended by the identity on the Fock factor. -/
def zeroMode (u : Fixed) : Module.End ℂ State :=
  stateTensor.conj ((cartanZeroMode u).rTensor Fock)

theorem zeroMode_single (u : Fixed) (p : Momentum) (P : Fock) :
    zeroMode u (Finsupp.single p P) =
      fixedGram u (physicalMomentum p) • Finsupp.single p P := by
  have hs : stateTensor.symm (Finsupp.single p P) = Finsupp.single p (1 : ℂ) ⊗ₜ[ℂ] P :=
    TensorProduct.finsuppScalarLeft_symm_apply_single p P
  rw [zeroMode, LinearEquiv.conj_apply_apply, hs, LinearMap.rTensor_tmul,
    cartanZeroMode_single, ← TensorProduct.smul_tmul', map_smul,
    ← hs, LinearEquiv.apply_symm_apply]

theorem zeroMode_apply (u : Fixed) (w : State) (p : Momentum) :
    zeroMode u w p = fixedGram u (physicalMomentum p) • w p := by
  have h : (Finsupp.lapply p : State →ₗ[ℂ] Fock).comp (zeroMode u) =
      fixedGram u (physicalMomentum p) • (Finsupp.lapply p : State →ₗ[ℂ] Fock) := by
    apply Finsupp.lhom_ext
    intro q P
    simp only [LinearMap.comp_apply, zeroMode_single, LinearMap.smul_apply,
      Finsupp.lapply_apply, Finsupp.smul_apply]
    by_cases hpq : p = q
    · subst q
      rfl
    · simp only [Finsupp.single_eq_of_ne hpq, smul_zero]
  exact DFunLike.congr_fun h w

/-- The fixed current on State, indexed by physical frequency. -/
def currentMode (u : Fixed) : ℤ → Module.End ℂ State
  | .negSucc n => Finsupp.mapRange.linearMap (LinearMap.mulLeft ℂ (creationPolynomial u n))
  | .ofNat (n + 1) => Finsupp.mapRange.linearMap (annihilationMode u n)
  | .ofNat 0 => zeroMode u

/-- The summand with first-current index `k` in the coefficient of `z^(-m-2)`. -/
def normalOrderedTerm (U V : ℤ → Module.End ℂ State) (m k : ℤ) : Module.End ℂ State :=
  if k < 0 then U k * V (m - k) else V (m - k) * U k

/-- The actual fixed-current summands in the coefficient of `z^(-2)`. -/
def zeroTerm (u v : Fixed) (k : ℤ) : Module.End ℂ State :=
  normalOrderedTerm (currentMode u) (currentMode v) 0 k

theorem zeroTerm_zero (u v : Fixed) :
    zeroTerm u v 0 = zeroMode v * zeroMode u := by
  simp only [zeroTerm, normalOrderedTerm, lt_irrefl, if_false, sub_self, currentMode]

theorem zeroTerm_zero_apply (u v : Fixed) (w : State) (p : Momentum) :
    zeroTerm u v 0 w p =
      (fixedGram v (physicalMomentum p) * fixedGram u (physicalMomentum p)) • w p := by
  rw [zeroTerm_zero, Module.End.mul_apply, zeroMode_apply, zeroMode_apply, smul_smul]

theorem zeroTerm_negative (u v : Fixed) (n : ℕ) :
    zeroTerm u v (Int.negSucc n) =
      Finsupp.mapRange.linearMap
        ((LinearMap.mulLeft ℂ (creationPolynomial u n)).comp (annihilationMode v n)) := by
  simp only [zeroTerm, normalOrderedTerm, Int.negSucc_lt_zero, if_true,
    zero_sub, Int.neg_negSucc]
  exact (Finsupp.mapRange.linearMap_comp
    (LinearMap.mulLeft ℂ (creationPolynomial u n)) (annihilationMode v n)).symm

theorem zeroTerm_positive (u v : Fixed) (n : ℕ) :
    zeroTerm u v (Int.ofNat (n + 1)) =
      Finsupp.mapRange.linearMap
        ((LinearMap.mulLeft ℂ (creationPolynomial v n)).comp (annihilationMode u n)) := by
  have hk : ¬ Int.ofNat (n + 1) < 0 := not_lt_of_ge (Int.ofNat_nonneg (n + 1))
  simp only [zeroTerm, normalOrderedTerm, if_neg hk, zero_sub, Int.neg_ofNat_succ]
  exact (Finsupp.mapRange.linearMap_comp
    (LinearMap.mulLeft ℂ (creationPolynomial v n)) (annihilationMode u n)).symm

/-- The negative-index summand for a fixed basis vector and its Gram dual is
the corresponding term of the native weighted Euler operator. -/
theorem zeroTerm_basis_dual_negative (i : Fin 16) (n : ℕ) (w : State) (p : Momentum) :
    zeroTerm (fixedBasis i) (fixedGramDual fixedBasis i) (Int.negSucc n) w p =
      numberTerm (fixedVariable i n) (w p) := by
  classical
  have hcreate : creationPolynomial (fixedBasis i) n = X (fixedVariable i n) := by
    simp only [creationPolynomial, fixedGram_pair_dual, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hann : annihilationMode (fixedGramDual fixedBasis i) n (w p) =
      ((frequency (fixedVariable i n) : ℂ) / 3) • pderiv (fixedVariable i n) (w p) := by
    rw [annihilationMode_apply]
    simp only [fixedGram_symm.eq (fixedGramDual fixedBasis i), fixedGram_pair_dual,
      mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [zeroTerm_negative, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, hcreate, hann, numberTerm_apply,
    mul_smul_comm]

/-- Maximum cover frequency of a variable used in any occupied momentum sector. -/
def coverBound (w : State) : ℕ :=
  w.support.sup fun p => (w p).vars.sup frequency

/-- Possible indices of a nonzero summand, including the Cartan term at zero. -/
def zeroTermIndices (w : State) : Finset ℤ :=
  Finset.Icc (-((coverBound w / 3 : ℕ) : ℤ)) ((coverBound w / 3 : ℕ) : ℤ)

private theorem annihilationMode_eq_zero_of_bound (u : Fixed) (w : State) (p : Momentum)
    (n : ℕ) (hn : coverBound w < 3 * (n + 1)) :
    annihilationMode u n (w p) = 0 := by
  rw [annihilationMode_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : fixedVariable i n ∉ (w p).vars := by
    intro hj
    have hp : p ∈ w.support := by
      apply Finsupp.mem_support_iff.mpr
      intro hp
      simpa [hp] using hj
    have hlocal : frequency (fixedVariable i n) ≤ (w p).vars.sup frequency :=
      Finset.le_sup hj
    have hglobal : (w p).vars.sup frequency ≤ coverBound w :=
      Finset.le_sup (f := fun q => (w q).vars.sup frequency) hp
    rw [frequency_fixedVariable] at hlocal
    omega
  rw [pderiv_eq_zero_of_notMem_vars hi, smul_zero]

/-- An explicit finite interval containing the support of the normal-ordered
zero coefficient on every State. The index of the Cartan term is zero. -/
theorem zeroTerm_support (u v : Fixed) (w : State) :
    Function.support (fun k => zeroTerm u v k w) ⊆
      (zeroTermIndices w : Set ℤ) := by
  intro k hk
  change k ∈ zeroTermIndices w
  rw [zeroTermIndices, Finset.mem_Icc]
  by_contra hout
  change zeroTerm u v k w ≠ 0 at hk
  apply hk
  apply Finsupp.ext
  intro p
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hout
    cases n with
    | zero =>
      exfalso
      omega
    | succ n =>
      have hn : coverBound w < 3 * (n + 1) := by omega
      rw [zeroTerm_positive, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
        LinearMap.comp_apply, annihilationMode_eq_zero_of_bound u w p n hn, map_zero,
        Finsupp.zero_apply]
  | negSucc n =>
    have hn : coverBound w < 3 * (n + 1) := by omega
    rw [zeroTerm_negative, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      LinearMap.comp_apply, annihilationMode_eq_zero_of_bound v w p n hn, map_zero,
      Finsupp.zero_apply]

private theorem zeroTerm_finite (u v : Fixed) (w : State) :
    Function.HasFiniteSupport (fun k => zeroTerm u v k w) :=
  (zeroTermIndices w).finite_toSet.subset (zeroTerm_support u v w)

/-- The normal-ordered zero coefficient obtained from the actual current modes. -/
def normalOrderedZero (u v : Fixed) : Module.End ℂ State where
  toFun w := ∑ᶠ k : ℤ, zeroTerm u v k w
  map_add' w x := by
    simp only [map_add]
    exact finsum_add_distrib (zeroTerm_finite u v w) (zeroTerm_finite u v x)
  map_smul' a w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' a (zeroTerm_finite u v w)).symm

/-- A finite formula with the momentum term displayed separately. Each nonzero
summand is explicitly a creation operator after an annihilation operator. -/
theorem normalOrderedZero_apply (u v : Fixed) (w : State) (p : Momentum) :
    normalOrderedZero u v w p =
      (fixedGram v (physicalMomentum p) * fixedGram u (physicalMomentum p)) • w p +
      ∑ k ∈ (zeroTermIndices w).erase 0, zeroTerm u v k w p := by
  classical
  let S := zeroTermIndices w
  have h0 : (0 : ℤ) ∈ S := by
    change (0 : ℤ) ∈ zeroTermIndices w
    rw [zeroTermIndices, Finset.mem_Icc]
    omega
  have hSum : (∑ k ∈ S.erase 0, zeroTerm u v k w) p =
      ∑ k ∈ S.erase 0, zeroTerm u v k w p :=
    map_sum (Finsupp.lapply p : State →ₗ[ℂ] Fock) (fun k => zeroTerm u v k w) (S.erase 0)
  change (∑ᶠ k : ℤ, zeroTerm u v k w) p = _
  rw [finsum_eq_sum_of_support_subset _ (zeroTerm_support u v w)]
  change (∑ k ∈ S, zeroTerm u v k w) p = _
  rw [← Finset.add_sum_erase S (fun k => zeroTerm u v k w) h0, Finsupp.add_apply,
    zeroTerm_zero_apply, hSum]

/-- The cover-index state field on the native twisted State. -/
abbrev TwistedStateField := Carrier lattice →ₗ[ℂ] ℤ → Module.End ℂ State

/-- The residue-zero version of the full coefficientwise pair iterate at
product index `-1`. The normal-ordering sum uses physical integer indices
and the state field uses their cover indices. -/
def FixedPairIterate (a b : Carrier lattice) (Ytw : TwistedStateField) : Prop :=
  ∀ (m : ℤ) (w : State),
    (∑ᶠ k : ℤ, normalOrderedTerm (fun n => Ytw a (3 * n))
      (fun n => Ytw b (3 * n)) m k w) =
      ∑ᶠ j : ℕ, Ring.choose (0 : ℂ) j •
        Ytw (mu lattice a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) w

/-- At residue zero all positive generalized binomials in (3.13) vanish. -/
theorem fixedPairIterate_mode (a b : Carrier lattice) (Ytw : TwistedStateField)
    (hIterate : FixedPairIterate a b Ytw) (m : ℤ) (w : State) :
    Ytw (mu lattice a (-1) b) (3 * (m + 1)) w =
      ∑ᶠ k : ℤ, normalOrderedTerm (fun n => Ytw a (3 * n))
        (fun n => Ytw b (3 * n)) m k w := by
  let term (j : ℕ) : State := Ring.choose (0 : ℂ) j •
    Ytw (mu lattice a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) w
  have h := hIterate m w
  change _ = ∑ᶠ j : ℕ, term j at h
  have hz : ∀ j : ℕ, j ≠ 0 → term j = 0 := by
    intro j hj
    simp only [term, Ring.choose_zero_ite, if_neg hj, zero_smul]
  rw [finsum_eq_single term 0 hz] at h
  simpa [term, Ring.choose_zero_right] using h.symm

/-- The cover index `3` of the actual untwisted current pair state acts
by the proven, pointwise finite normally ordered zero coefficient. -/
theorem currentMinusOne_zero_of_fixedPairIterate (u v : Fixed) (Ytw : TwistedStateField)
    (hU : ∀ n : ℤ, Ytw (currentAlong lattice u.val) (3 * n) = currentMode u n)
    (hV : ∀ n : ℤ, Ytw (currentAlong lattice v.val) (3 * n) = currentMode v n)
    (hIterate : FixedPairIterate (currentAlong lattice u.val) (currentAlong lattice v.val) Ytw) :
    Ytw (mu lattice (currentAlong lattice u.val) (-1) (currentAlong lattice v.val)) 3 =
      normalOrderedZero u v := by
  apply LinearMap.ext
  intro w
  have h := fixedPairIterate_mode _ _ Ytw hIterate 0 w
  change _ = ∑ᶠ k : ℤ, zeroTerm u v k w
  refine h.trans (finsum_congr fun k => ?_)
  unfold zeroTerm
  rw [funext hU, funext hV]

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate
