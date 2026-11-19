/- GID: D5/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric]
   utility: none
   digest: The symmetric-power coefficient summand carries the relative stable class. -/

import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrSymmetricPowerSplitting
import D5.S3.FiniteGroups.GroupAlgebra.RelativePolynomialRetractAbsorption
import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTensorReflection
import D5.S3.FiniteGroups.GroupAlgebra.OriginalWClassification

/-!
This is the higher-degree analogue of Elmer--Kadr Lemma 3.8, using the
actual splitting in the question after Lemma 3.9, Section 3.2,
DOI 10.1007/s13366-026-00855-9 / arXiv:2510.07939v1.

For 1 <= k < p in the original index range pk+1 < |E|, the tensor power
of V_(p+1) has relative stable class V_(pk+1). The genuine symmetric
quotient is an actual retract of that tensor power. The coefficient
copy is already known to split inside the quotient. Polynomial retract
absorption then proves that this quotient has the same relative class.
No cancellation of an arbitrary infinite module is assumed.

This source is a candidate until its full endpoint, report and reviews
have been completed; no literature-priority claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.RelativeSymmetricPowerComplement

open ElmerKadrTensorCounterexample ElmerKadrPositiveCriterion
open ElmerKadrTensorCounterexample.SymmetricPowerTranslation
open SymmetricPowerBlockSplitting
open scoped TensorProduct
open Module

universe uE

variable {K : Type} [Field K]

section TensorFunctor

variable {A : Type} [AddCommGroup A] [Module K A]
  {E : Type uE} [AddGroup E]

def tensorOneEquiv (ρ : Representation K (Multiplicative E) A) :
    (SymmetricPowerBlockSplitting.tensorAction ρ 1).Equiv ρ :=
  .mk (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => A) 0)
    fun g => by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      change (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => A) 0)
          (SymmetricPowerBlockSplitting.tensorAction ρ 1 g (PiTensorProduct.tprod K v)) =
        ρ g ((PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => A) 0)
          (PiTensorProduct.tprod K v))
      simp only [tensorAction_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]

private def tensorConsLinear (n : ℕ) :
    A ⊗[K] Tensor (K := K) n A ≃ₗ[K] Tensor (K := K) (n + 1) A :=
  (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => A) 0).symm
    (LinearEquiv.refl K (Tensor (K := K) n A))).trans
    ((PiTensorProduct.tmulEquiv K A).trans
      (PiTensorProduct.reindex K (fun _ : Fin 1 ⊕ Fin n => A)
        (finSumFinEquiv.trans (finCongr (Nat.one_add n)))))

def tensorConsEquiv (ρ : Representation K (Multiplicative E) A) (n : ℕ) :
    (ρ.tprod (SymmetricPowerBlockSplitting.tensorAction ρ n)).Equiv
      (SymmetricPowerBlockSplitting.tensorAction ρ (n + 1)) :=
  .mk (tensorConsLinear n) fun g => by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change tensorConsLinear n
        (TensorProduct.map (ρ g) (SymmetricPowerBlockSplitting.tensorAction ρ n g)
          (a ⊗ₜ[K] PiTensorProduct.tprod K v)) =
      SymmetricPowerBlockSplitting.tensorAction ρ (n + 1) g
        (tensorConsLinear n (a ⊗ₜ[K] PiTensorProduct.tprod K v))
    simp only [TensorProduct.map_tmul, tensorAction_tprod, tensorConsLinear,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      PiTensorProduct.subsingletonEquiv_symm_apply', PiTensorProduct.tmulEquiv_apply,
      PiTensorProduct.reindex_tprod]
    congr 1
    funext j
    cases ((finSumFinEquiv.trans (finCongr (Nat.one_add n))).symm j) <;> rfl

/-- The already constructed averaging descent, applied to the tensor identity,
is an actual equivariant section of the genuine quotient map. -/
theorem quotientAverage_id_section
    (ρ : Representation K (Multiplicative E) A) (n : ℕ)
    (hfac : (n.factorial : K) ≠ 0) :
    (quotientIntertwiner ρ n).comp
        (quotientAverage (.id (SymmetricPowerBlockSplitting.tensorAction ρ n))) =
      .id (action ρ n) := by
  classical
  apply Representation.IntertwiningMap.ext
  apply ext_tprod
  intro v
  change quotientIntertwiner ρ n
      (quotientAverage (.id (SymmetricPowerBlockSplitting.tensorAction ρ n))
        (SymmetricPower.mk K (Fin n) A (PiTensorProduct.tprod K v))) =
    SymmetricPower.tprod K v
  rw [quotientAverage_mk, map_smul, map_sum]
  have hperm (e : Equiv.Perm (Fin n)) :
      quotientIntertwiner ρ n
        (permutation n e (PiTensorProduct.tprod K v)) =
      SymmetricPower.tprod K v := by
    rw [permutation_tprod]
    exact SymmetricPower.tprod_equiv e v
  simp only [Representation.IntertwiningMap.id_apply, hperm, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hfac, one_smul]

end TensorFunctor

section PolynomialModules

variable {E : Type uE} [AddCommGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]

include hα in
/-- Every tensor step has nonzero high-binomial scalar because k<p. The
induction retains the paper's original relative-projective factors. -/
theorem block_tensor_stable (k : ℕ) :
    1 ≤ k → k < p → p * k + 2 ≤ Fintype.card E →
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      (SymmetricPowerBlockSplitting.tensorAction
        ((dualAction K (p + 1)).comp α.toMultiplicative) k)
      ((dualAction K (p * k + 1)).comp α.toMultiplicative) := by
  let V (d : ℕ) : Representation K (Multiplicative E) (DualPower K d) :=
    (dualAction K d).comp α.toMultiplicative
  let M := (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
    (Fintype.card E / p)).comp α.toMultiplicative
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk hkp hsize
    change RelativeStableIso M
      (SymmetricPowerBlockSplitting.tensorAction (V (p + 1)) (n + 1))
      (V (p * (n + 1) + 1))
    by_cases hn : n = 0
    · subst n
      rw [Nat.mul_one]
      exact EmbeddedTensorReflection.relativeStableIso_of_equiv M
        (tensorOneEquiv (V (p + 1)))
    · have hprev := ih (by omega) (by omega) (by nlinarith)
      have hleft := EmbeddedTensorReflection.stable_lTensor M hprev (V (p + 1))
      have hfirst := EmbeddedTensorReflection.relativeStableIso_of_equiv M
        (tensorConsEquiv (V (p + 1)) n).symm
      have hp : 2 < p := by omega
      have hchoose : (((1 + n).choose 1 : ℕ) : K) ≠ 0 := by
        rw [Nat.choose_one_right]
        intro hz
        have hdvd : p ∣ 1 + n := (CharP.cast_eq_zero_iff K p (1 + n)).mp hz
        have hle := Nat.le_of_dvd (by omega : 0 < 1 + n) hdvd
        omega
      have hbound : (p * 1 + 1) + (p * n + 1) ≤ Fintype.card E := by
        nlinarith
      have hbin := (EmbeddedOriginalClassification.original_relative_criterion_for_embedding
        α hα 1 n 1 1 (by omega) (by omega) (by omega) hbound).mpr
          (Or.inr (Or.inr hchoose))
      have heq : (p * 1 + 1) + (p * n + 1) - 1 = p * (n + 1) + 1 := by
        simp only [Nat.mul_succ]
        omega
      have e := EmbeddedOriginalClassification.restrictEquiv α.toMultiplicative
        (EmbeddedTensorReflection.expectedOne (K := K) (p * 1 + 1) (p * n + 1))
      rw [heq] at e
      have hsingle := EmbeddedTensorReflection.relativeStableIso_of_equiv M e
      have hbin' : RelativeStableIso M
          ((V (p + 1)).tprod (V (p * n + 1)))
          (V (p * (n + 1) + 1)) := by
        obtain ⟨f, g, hfg, hgf⟩ := hbin
        have hrev : RelativeStableIso M _ _ := ⟨g, f, hgf, hfg⟩
        have hstep := EmbeddedTensorReflection.stable_trans M hrev hsingle
        rw [Nat.mul_one] at hstep
        exact hstep
      exact EmbeddedTensorReflection.stable_trans M hfirst
        (EmbeddedTensorReflection.stable_trans M hleft hbin')

include hα in
/-- The actual symmetric quotient has precisely the relative stable class
of its actual coefficient-sum summand, throughout the paper's index range. -/
theorem polynomial_symmetric_power_stable (k : ℕ) (hk : 1 ≤ k) (hkp : k < p)
    (hsize : p * k + 2 ≤ Fintype.card E) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      (action ((dualAction K (p + 1)).comp α.toMultiplicative) k)
      ((dualAction K (p * k + 1)).comp α.toMultiplicative) := by
  let V (d : ℕ) : Representation K (Multiplicative E) (DualPower K d) :=
    (dualAction K d).comp α.toMultiplicative
  let S := action (V (p + 1)) k
  let T := SymmetricPowerBlockSplitting.tensorAction (V (p + 1)) k
  obtain ⟨rK, hriK⟩ :=
    ElmerKadrSymmetricPowerSplitting.exists_polynomial_retraction (K := K) (p := p) k hk hkp
  let i : (V (ElmerKadrSymmetricPowerSplitting.blockLength p k + 1)).IntertwiningMap S :=
    EmbeddedOriginalClassification.restrictIntertwiner α.toMultiplicative
      (ElmerKadrSymmetricPowerSplitting.polynomialInclusion (K := K) (p := p) k)
  let r : S.IntertwiningMap (V (ElmerKadrSymmetricPowerSplitting.blockLength p k + 1)) :=
    EmbeddedOriginalClassification.restrictIntertwiner α.toMultiplicative rK
  have hri : r.comp i = .id (V (ElmerKadrSymmetricPowerSplitting.blockLength p k + 1)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun t => t x) hriK
  have hfac : (k.factorial : K) ≠ 0 := isUnit_iff_ne_zero.mp
    ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).mpr hkp)
  have hdim : ((ElmerKadrSymmetricPowerSplitting.blockLength p k + 1 : ℕ) : K) ≠ 0 := by
    rw [ElmerKadrSymmetricPowerSplitting.blockLength_eq]
    simp
  have hsize' : ElmerKadrSymmetricPowerSplitting.blockLength p k + 2 ≤ Fintype.card E := by
    simpa only [ElmerKadrSymmetricPowerSplitting.blockLength_eq] using hsize
  have hT : RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative) T
      (V (ElmerKadrSymmetricPowerSplitting.blockLength p k + 1)) := by
    dsimp only [V]
    rw [ElmerKadrSymmetricPowerSplitting.blockLength_eq]
    exact block_tensor_stable α hα k hk hkp hsize
  have hS := RelativePolynomialRetractAbsorption.intermediate_retract_stable
    α hα (Fintype.card E / p) (ElmerKadrSymmetricPowerSplitting.blockLength p k)
    hsize' hdim T S
    (quotientAverage (.id T)) (quotientIntertwiner (V (p + 1)) k)
    (quotientAverage_id_section (V (p + 1)) k hfac) i r hri hT
  rw [← ElmerKadrSymmetricPowerSplitting.blockLength_eq p k]
  exact hS

end PolynomialModules

section OriginalModule

variable {E : Type uE} [AddCommGroup E] [Fintype E] [Nontrivial E]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {p : ℕ} [Fact p.Prime] [CharP K p]

open OriginalWClassification

/-- Higher-degree relative version of Lemma 3.8 for the actual original W.
The specified coefficient copy already splits by the separate actual-splitting
theorem; this theorem proves that its complement has zero relative stable class. -/
theorem originalW_symmetric_power_stable
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (ρ : Representation K (Multiplicative E) W) (hρ : Function.Injective ρ)
    (k : ℕ) (hk : 1 ≤ k) (hkp : k < p) (hsize : p * k + 2 ≤ Fintype.card E) :
    RelativeStableIso
      (originalMAction ρ p (Fintype.card E / p) (Fact.out : p.Prime).pos)
      (action (originalVAction ρ (p + 1) (by omega)) k)
      (originalVAction ρ (p * k + 1) (by omega)) := by
  obtain ⟨α, hα, _primalModels, dualModels⟩ :=
    SymmetricPowerTranslation.exists_faithful_polynomial_models hE hdim ρ hρ
  let eV : ∀ (d : ℕ) (hd : 0 < d),
      (originalVAction ρ d hd).Equiv ((dualAction K d).comp α.toMultiplicative) := by
    intro d hd
    cases d with
    | zero => omega
    | succ n => simpa [originalVAction, OriginalV] using Classical.choice (dualModels n)
  let eM : (originalMAction ρ p (Fintype.card E / p)
      (Fact.out : p.Prime).pos).Equiv
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative) :=
    directSumCongr (fun j : Fin (Fintype.card E / p) =>
      eV (p * (j.val + 1)) (Nat.mul_pos (Fact.out : p.Prime).pos (Nat.succ_pos _)))
  let eS := symmetricActionEquiv k (eV (p + 1) (by omega))
  exact relativeStableIso_transport eM.symm eS.symm
    (eV (p * k + 1) (by omega)).symm
    (polynomial_symmetric_power_stable α hα k hk hkp hsize)

end OriginalModule

end D5.S3.FiniteGroups.GroupAlgebra.RelativeSymmetricPowerComplement
