/- GID: D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Data.Nat.Choose.Factorization]
   utility: none
   digest: The original relative tensor criterion along any faithful finite additive embedding over a field of prime characteristic. -/

import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
open D5.S3.FiniteGroups.GroupAlgebra.RectangularTensorObstruction
open D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
open Finset Polynomial
open scoped TensorProduct DirectSum

universe uK uE uG uV uX uM

section Sampling

variable {K : Type uK} [Field K]

/- The finite-sample Vandermonde argument is vector-valued.  The dual test is
   essential: E and the target module need not have related dimensions. -/
theorem coefficients_eq_zero_of_samples
    {I : Type uE} [Fintype I]
    {B : Type uV} [AddCommGroup B] [Module K B]
    (α : I → K) (hα : Function.Injective α) {d : ℕ}
    (hd : d ≤ Fintype.card I) (v : Fin d → B)
    (heval : ∀ i : I, (∑ j : Fin d, α i ^ j.val • v j) = 0) :
    ∀ k : Fin d, v k = 0 := by
  classical
  intro k
  apply (Module.forall_dual_apply_eq_zero_iff K (v k)).mp
  intro φ
  let P : K[X] := ∑ j : Fin d, Polynomial.monomial j.val (φ (v j))
  have hevalP (i : I) : P.eval (α i) = 0 := by
    calc
      P.eval (α i) = ∑ j : Fin d, α i ^ j.val * φ (v j) := by
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
        exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = φ (∑ j : Fin d, α i ^ j.val • v j) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = 0 := by rw [heval i, map_zero]
  have hdegree : P.natDegree ≤ d - 1 := by
    dsimp only [P]
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ ?_
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (by
      have := j.isLt
      omega)
  have hP : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hα hevalP
      (lt_of_le_of_lt hdegree (by have := k.isLt; omega))
  have hcoeff : P.coeff k.val = φ (v k) := by
    dsimp only [P]
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · exact Polynomial.coeff_monomial_same k.val (φ (v k))
    · intro j _ hj
      exact Polynomial.coeff_monomial_of_ne _ (fun h => hj (Fin.ext h.symm))
    · simp
  calc
    φ (v k) = P.coeff k.val := hcoeff.symm
    _ = 0 := by rw [hP, Polynomial.coeff_zero]

theorem intertwines_coefficients_of_samples
    {I : Type uE} [Fintype I]
    {A : Type uV} [AddCommGroup A] [Module K A]
    {B : Type uX} [AddCommGroup B] [Module K B]
    (α : I → K) (hα : Function.Injective α) {d : ℕ}
    (hd : d ≤ Fintype.card I)
    (C : Fin d → Module.End K A) (D : Fin d → Module.End K B)
    (f : A →ₗ[K] B)
    (hf : ∀ i : I, f.comp (∑ j : Fin d, α i ^ j.val • C j) =
      (∑ j : Fin d, α i ^ j.val • D j).comp f) :
    ∀ k : Fin d, f.comp (C k) = (D k).comp f := by
  classical
  have hz (i : I) :
      (∑ j : Fin d, α i ^ j.val • (f.comp (C j) - (D j).comp f)) = 0 := by
    apply LinearMap.ext
    intro a
    have hi := LinearMap.congr_fun (hf i) a
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul] at hi
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.zero_apply, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hi
  intro k
  exact sub_eq_zero.mp (coefficients_eq_zero_of_samples α hα hd
    (fun j => f.comp (C j) - (D j).comp f) hz k)

theorem restricted_dual_intertwines_coefficients
    {E : Type uE} [AddGroup E] [Fintype E]
    (α : E →+ K) (hα : Function.Injective α) {r t d : ℕ}
    (hrd : r ≤ d) (htd : t ≤ d) (hd : d ≤ Fintype.card E)
    (f : (Representation.IntertwiningMap ((dualAction K r).comp α.toMultiplicative))
      ((dualAction K t).comp α.toMultiplicative)) (k : Fin d) :
    f.toLinearMap.comp (coefficient K r k.val) =
      (coefficient K t k.val).comp f.toLinearMap := by
  refine intertwines_coefficients_of_samples (α : E → K) hα hd
    (fun j => coefficient K r j.val) (fun j => coefficient K t j.val)
    f.toLinearMap ?_ k
  intro e
  have he := f.isIntertwining' (Multiplicative.ofAdd (-e))
  change f.toLinearMap.comp
    (dualAction K r (Multiplicative.ofAdd (α (-e)))) =
      (dualAction K t (Multiplicative.ofAdd (α (-e)))).comp f.toLinearMap at he
  simp only [map_neg] at he
  rw [action_expansion K r d hrd (α e), action_expansion K t d htd (α e)] at he
  exact he

private theorem tensor_expansion_by_coefficients (n m : ℕ) (a : K) :
    RectangularTensorObstruction.tensorAction K n m (Multiplicative.ofAdd (-a)) =
      ∑ k : Fin (n + m + 1), a ^ k.val • tensorCoefficient K n m k := by
  classical
  rw [tensor_action_expansion]
  symm
  simp only [tensorCoefficient, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  simp

theorem restricted_tensor_intertwines_coefficients
    {E : Type uE} [AddGroup E] [Fintype E]
    (α : E →+ K) (hα : Function.Injective α) {n m : ℕ}
    (hbound : n + m + 1 ≤ Fintype.card E)
    (f : (Representation.IntertwiningMap ((dualAction K (n + m + 1)).comp α.toMultiplicative))
      ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
    (k : Fin (n + m + 1)) :
    f.toLinearMap.comp (coefficient K (n + m + 1) k.val) =
      (tensorCoefficient K n m k).comp f.toLinearMap := by
  refine intertwines_coefficients_of_samples (α : E → K) hα hbound
    (fun j => coefficient K (n + m + 1) j.val)
    (fun j => tensorCoefficient K n m j) f.toLinearMap ?_ k
  intro e
  have he := f.isIntertwining' (Multiplicative.ofAdd (-e))
  change f.toLinearMap.comp
    (dualAction K (n + m + 1) (Multiplicative.ofAdd (α (-e)))) =
      (RectangularTensorObstruction.tensorAction K n m (Multiplicative.ofAdd (α (-e)))).comp f.toLinearMap at he
  simp only [map_neg] at he
  rw [action_expansion K (n + m + 1) (n + m + 1) (le_refl _)
      (α e), tensor_expansion_by_coefficients n m (α e)] at he
  exact he

theorem restricted_tensor_intertwines_coefficients_rev
    {E : Type uE} [AddGroup E] [Fintype E]
    (α : E →+ K) (hα : Function.Injective α) {n m : ℕ}
    (hbound : n + m + 1 ≤ Fintype.card E)
    (g : (Representation.IntertwiningMap ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
      ((dualAction K (n + m + 1)).comp α.toMultiplicative))
    (k : Fin (n + m + 1)) :
    g.toLinearMap.comp (tensorCoefficient K n m k) =
      (coefficient K (n + m + 1) k.val).comp g.toLinearMap := by
  refine intertwines_coefficients_of_samples (α : E → K) hα hbound
    (fun j => tensorCoefficient K n m j)
    (fun j => coefficient K (n + m + 1) j.val) g.toLinearMap ?_ k
  intro e
  have he := g.isIntertwining' (Multiplicative.ofAdd (-e))
  change g.toLinearMap.comp
    (RectangularTensorObstruction.tensorAction K n m (Multiplicative.ofAdd (α (-e)))) =
      (dualAction K (n + m + 1) (Multiplicative.ofAdd (α (-e)))).comp g.toLinearMap at he
  simp only [map_neg] at he
  rw [tensor_expansion_by_coefficients n m (α e),
    action_expansion K (n + m + 1) (n + m + 1) (le_refl _)
      (α e)] at he
  exact he

end Sampling

section Coordinates

variable {K : Type uK} [Field K]

private theorem comp_scale_mem_degreeLT (c : K) {m : ℕ} {f : K[X]}
    (hf : f ∈ Polynomial.degreeLT K m) :
    f.comp (C c * X) ∈ Polynomial.degreeLT K m := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hf ⊢
  intro n hn
  rw [Polynomial.comp_C_mul_X_coeff, hf n hn, zero_mul]

/-- The existing polynomial substitution equivalence, specialized to c*X. -/
private def polynomialScaling (c : K) (hc : c ≠ 0) : K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX (C c * X) (C c⁻¹ * X)
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])

private theorem polynomialScaling_map_degreeLT (c : K) (hc : c ≠ 0) (m : ℕ) :
    (Polynomial.degreeLT K m).map
        (polynomialScaling c hc).toLinearEquiv.toLinearMap =
      Polynomial.degreeLT K m := by
  apply le_antisymm
  · rintro f ⟨q, hq, rfl⟩
    exact comp_scale_mem_degreeLT c hq
  · intro f hf
    refine ⟨(polynomialScaling c hc).symm f, ?_, ?_⟩
    · exact comp_scale_mem_degreeLT c⁻¹ hf
    · exact (polynomialScaling c hc).apply_symm_apply f

/-- S_c(f)(X) = f(c*X), restricted to the original bounded polynomial space.
The inverse is substitution by c⁻¹*X, including when m = 0. -/
def primalScaling (c : K) (hc : c ≠ 0) (m : ℕ) : Primal K m ≃ₗ[K] Primal K m :=
  (polynomialScaling c hc).toLinearEquiv.ofSubmodules
    (Polynomial.degreeLT K m) (Polynomial.degreeLT K m)
    (polynomialScaling_map_degreeLT c hc m)

private theorem primalScaling_apply_coe (c : K) (hc : c ≠ 0) (m : ℕ)
    (f : Primal K m) :
    (primalScaling c hc m f : K[X]) = (f : K[X]).comp (C c * X) := rfl

private theorem primalScaling_intertwines (c : K) (hc : c ≠ 0) (m : ℕ)
    (a : K) (f : Primal K m) :
    primalScaling c hc m (primalAction K m (Multiplicative.ofAdd (c * a)) f) =
      primalAction K m (Multiplicative.ofAdd a) (primalScaling c hc m f) := by
  apply Subtype.ext
  rw [primalScaling_apply_coe]
  change (Polynomial.taylor (c * a) (f : K[X])).comp (C c * X) =
    Polynomial.taylor a (primalScaling c hc m f : K[X])
  rw [primalScaling_apply_coe]
  simp only [Polynomial.taylor_apply, Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.C_mul, mul_add]

private theorem primalScaling_symm_intertwines (c : K) (hc : c ≠ 0) (m : ℕ)
    (a : K) (f : Primal K m) :
    primalAction K m (Multiplicative.ofAdd (c * a)) ((primalScaling c hc m).symm f) =
      (primalScaling c hc m).symm (primalAction K m (Multiplicative.ofAdd a) f) := by
  apply (primalScaling c hc m).injective
  simp only [primalScaling_intertwines, LinearEquiv.apply_symm_apply]

/-- D_c is the INVERSE of S_c.dualMap, on the original contragredient. -/
def dualScaling (c : K) (hc : c ≠ 0) (m : ℕ) : DualPower K m ≃ₗ[K] DualPower K m :=
  (primalScaling c hc m).dualMap.symm

private theorem dualScaling_intertwines (c : K) (hc : c ≠ 0) (m : ℕ)
    (a : K) (f : DualPower K m) :
    dualScaling c hc m (dualAction K m (Multiplicative.ofAdd (c * a)) f) =
      dualAction K m (Multiplicative.ofAdd a) (dualScaling c hc m f) := by
  apply LinearMap.ext
  intro q
  change f (primalAction K m (Multiplicative.ofAdd (-(c * a)))
      ((primalScaling c hc m).symm q)) =
    f ((primalScaling c hc m).symm
      (primalAction K m (Multiplicative.ofAdd (-a)) q))
  rw [show -(c * a) = c * (-a) by ring, primalScaling_symm_intertwines]

/-- The literal Fin s direct sum of these coordinate equivalences. -/
def relativeScaling {p : ℕ} (c : K) (hc : c ≠ 0) (s : ℕ) :
    PrimeCyclicRelativeTrace.RelativeSpace K p s ≃ₗ[K] PrimeCyclicRelativeTrace.RelativeSpace K p s :=
  DirectSum.congrLinearEquiv
    (fun i : Fin s => dualScaling c hc (p * (i.val + 1)))

private theorem relativeScaling_intertwines {p : ℕ} (c : K) (hc : c ≠ 0)
    (s : ℕ) (a : K) (v : PrimeCyclicRelativeTrace.RelativeSpace K p s) :
    relativeScaling c hc s
        (PrimeCyclicRelativeTrace.relativeAction s (Multiplicative.ofAdd (c * a)) v) =
      PrimeCyclicRelativeTrace.relativeAction s (Multiplicative.ofAdd a) (relativeScaling c hc s v) := by
  apply DFinsupp.ext
  intro i
  change dualScaling c hc (p * (i.val + 1))
      (dualAction K (p * (i.val + 1)) (Multiplicative.ofAdd (c * a)) (v i)) =
    dualAction K (p * (i.val + 1)) (Multiplicative.ofAdd a)
      (dualScaling c hc (p * (i.val + 1)) (v i))
  exact dualScaling_intertwines c hc (p * (i.val + 1)) a (v i)

end Coordinates

section ScaledNorm

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The actual translation homomorphism z ↦ c*cast(z). -/
def scaledPrimeSubgroup (c : K) : Multiplicative (ZMod p) →* Multiplicative K where
  toFun z := Multiplicative.ofAdd (c * primeCast (Multiplicative.toAdd z))
  map_one' := by simp
  map_mul' z w := by simp [mul_add]

/-- The accepted witness, conjugated by the actual relative coordinate map. -/
def scaledRelativeNormWitness (c : K) (hc : c ≠ 0) (s : ℕ) :
    Module.End K (PrimeCyclicRelativeTrace.RelativeSpace K p s) :=
  (relativeScaling (p := p) c hc s).symm.toLinearMap.comp
    ((relativeNormWitness (p := p) s).comp
      (relativeScaling (p := p) c hc s).toLinearMap)

/-- Scaling transports the accepted norm to every nonzero prime-field line.
No finiteness of K or positivity of the summand count is assumed. -/
theorem scaled_relative_norm (c : K) (hc : c ≠ 0) (s : ℕ) :
    (∑ z : Multiplicative (ZMod p),
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s (scaledPrimeSubgroup c z)).comp
        ((scaledRelativeNormWitness c hc s).comp
          (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s (scaledPrimeSubgroup c z⁻¹)))) =
      LinearMap.id := by
  classical
  let D := relativeScaling (p := p) c hc s
  have he (z : Multiplicative (ZMod p)) (v : PrimeCyclicRelativeTrace.RelativeSpace K p s) :
      D (PrimeCyclicRelativeTrace.relativeAction s (scaledPrimeSubgroup c z) v) =
        PrimeCyclicRelativeTrace.relativeAction s (primeSubgroup z) (D v) :=
    relativeScaling_intertwines c hc s (primeCast (Multiplicative.toAdd z)) v
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  apply D.injective
  have hterm (z : Multiplicative (ZMod p)) :
      D (PrimeCyclicRelativeTrace.relativeAction s (scaledPrimeSubgroup c z)
          (scaledRelativeNormWitness c hc s
            (PrimeCyclicRelativeTrace.relativeAction s (scaledPrimeSubgroup c z⁻¹) v))) =
        PrimeCyclicRelativeTrace.relativeAction s (primeSubgroup z)
          (relativeNormWitness s (PrimeCyclicRelativeTrace.relativeAction s (primeSubgroup z⁻¹) (D v))) := by
    rw [he]
    change PrimeCyclicRelativeTrace.relativeAction s (primeSubgroup z)
        (D (D.symm (relativeNormWitness s
          (D (PrimeCyclicRelativeTrace.relativeAction s (scaledPrimeSubgroup c z⁻¹) v))))) = _
    rw [LinearEquiv.apply_symm_apply, he]
  rw [map_sum]
  simp_rw [hterm]
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    using LinearMap.congr_fun (relative_norm (K := K) (p := p) s) (D v)

end ScaledNorm

section EmbeddedCycle

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {E : Type uE} [AddGroup E]

private theorem embedding_nsmul_eq_zero (α : E →+ K)
    (hα : Function.Injective α) (e : E) : p • e = 0 := by
  apply hα
  rw [map_nsmul, map_zero, nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul]

def embeddingPrimeSubgroup (α : E →+ K) (hα : Function.Injective α) (e : E) :
    Multiplicative (ZMod p) →* Multiplicative E :=
  (ZMod.lift p ⟨zmultiplesHom E e, by
    simpa only [zmultiplesHom_apply, natCast_zsmul] using
      embedding_nsmul_eq_zero (p := p) α hα e⟩).toMultiplicative

theorem embeddingPrimeSubgroup_comp (α : E →+ K)
    (hα : Function.Injective α) (e : E) :
    α.toMultiplicative.comp (embeddingPrimeSubgroup (p := p) α hα e) =
      scaledPrimeSubgroup (p := p) (α e) := by
  apply MonoidHom.ext
  intro z
  apply Multiplicative.toAdd.injective
  have hscale : Multiplicative.toAdd (scaledPrimeSubgroup (p := p) (α e) z) =
      α e * primeCast (Multiplicative.toAdd z) := rfl
  rw [hscale]
  simp only [MonoidHom.comp_apply, embeddingPrimeSubgroup,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd]
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  rw [← hn, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, map_zsmul, zsmul_eq_mul, map_intCast]
  exact mul_comm _ _

variable {U : Type uK} [AddCommGroup U] [Module K U]

theorem trace_relativeFactors_for_embedding
    (α : E →+ K) (hα : Function.Injective α) (e : E) (he : e ≠ 0) (s : ℕ)
    (ρ : Representation K (Multiplicative E) U) (h : ρ.IntertwiningMap ρ)
    (hh : RelativeFactors
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp α.toMultiplicative) h) :
    LinearMap.trace K U h.toLinearMap = 0 := by
  classical
  have hne : α e ≠ 0 := by
    intro hz
    apply he
    apply hα
    simpa only [map_zero] using hz
  let β : Multiplicative (ZMod p) →* Multiplicative E :=
    embeddingPrimeSubgroup (p := p) α hα e
  let τ : Representation K (Multiplicative E) (PrimeCyclicRelativeTrace.RelativeSpace K p s) :=
    (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp α.toMultiplicative
  have hline (z : Multiplicative (ZMod p)) :
      α.toMultiplicative (β z) = scaledPrimeSubgroup (p := p) (α e) z :=
    DFunLike.congr_fun (embeddingPrimeSubgroup_comp (p := p) α hα e) z
  have hnorm :
      (∑ z : Multiplicative (ZMod p),
        (τ (β z)).comp ((scaledRelativeNormWitness (α e) hne s).comp
          (τ (β z⁻¹)))) = LinearMap.id := by
    simpa only [τ, MonoidHom.comp_apply, hline] using
      scaled_relative_norm (p := p) (α e) hne s
  have hcard : (Fintype.card (Multiplicative (ZMod p)) : K) = 0 := by
    rw [Fintype.card_multiplicative, ZMod.card]
    exact CharP.cast_eq_zero K p
  exact ElmerKadrTensorCounterexample.trace_relative_factor β τ
    (scaledRelativeNormWitness (α e) hne s) hnorm hcard ρ h hh

end EmbeddedCycle

section Restriction

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {H : Type uE} [Group H]
  {A : Type uV} [AddCommGroup A] [Module K A]
  {B : Type uX} [AddCommGroup B] [Module K B]

def restrictIntertwiner {ρ : Representation K G A} {σ : Representation K G B}
    (ι : H →* G) (f : ρ.IntertwiningMap σ) :
    (Representation.IntertwiningMap (ρ.comp ι))
      (σ.comp ι) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (ι h)

def restrictEquiv {ρ : Representation K G A} {σ : Representation K G B}
    (ι : H →* G) (e : ρ.Equiv σ) :
    (Representation.Equiv (ρ.comp ι)) (σ.comp ι) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro h
  exact e.toIntertwiningMap.isIntertwining' (ι h)

end Restriction

section GenericRectangularTrace

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E]
  (α : E →+ K) (hα : Function.Injective α)

include hα

theorem embedded_composition_top_coordinate_zero (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card E)
    (hchoose : ((n + m).choose n : K) = 0)
    (f : (Representation.IntertwiningMap ((dualAction K (n + m + 1)).comp α.toMultiplicative))
      ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
    (g : (Representation.IntertwiningMap ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
      ((dualAction K (n + m + 1)).comp α.toMultiplicative)) :
    g (f (dualBasis K (n + m + 1) (Fin.last (n + m))))
      (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) = 0 := by
  let w : RectangularTensorObstruction.TensorSpace K n m :=
    dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
      dualBasis K (m + 1) (Fin.last m)
  have hg : g w (Polynomial.degreeLT.basis K (n + m + 1)
      (Fin.last (n + m))) = 0 := by
    have he := LinearMap.congr_fun
      (restricted_tensor_intertwines_coefficients_rev α hα (by omega)
        g ⟨m, by omega⟩)
      (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
        dualBasis K (m + 1) 0)
    simp only [LinearMap.comp_apply,
      Representation.IntertwiningMap.toLinearMap_apply] at he
    rw [tensor_coefficient_middle_generator] at he
    change g w = coefficient K (n + m + 1) m
      (g (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
        dualBasis K (m + 1) 0)) at he
    rw [he]
    exact coefficient_top_coordinate_zero K n m hchoose _
  have hgline : g w =
      g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
        (Polynomial.degreeLT.basis K (n + m + 1) 0) •
          dualBasis K (n + m + 1) (Fin.last (n + m)) := by
    have he := LinearMap.congr_fun
      (restricted_tensor_intertwines_coefficients_rev α hα (by omega)
        g (Fin.last (n + m)))
      (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
    simp only [LinearMap.comp_apply,
      Representation.IntertwiningMap.toLinearMap_apply] at he
    rw [tensor_coefficient_top_generator] at he
    change g w = coefficient K (n + m + 1) (n + m)
      (g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)) at he
    simpa only [coefficient_top] using he
  have hgw : g w = 0 := by
    have hz := hg
    rw [hgline, LinearMap.smul_apply] at hz
    simp only [dualBasis, Module.Basis.dualBasis_apply_self, ite_true,
      smul_eq_mul, mul_one] at hz
    change g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
      (Polynomial.degreeLT.basis K (n + m + 1) 0) = 0 at hz
    rw [hgline, hz, zero_smul]
  have hf : f (dualBasis K (n + m + 1) (Fin.last (n + m))) =
      tensorCoefficient K n m (Fin.last (n + m))
        (f (dualBasis K (n + m + 1) 0)) := by
    have he := LinearMap.congr_fun
      (restricted_tensor_intertwines_coefficients α hα (by omega)
        f (Fin.last (n + m)))
      (dualBasis K (n + m + 1) 0)
    simp only [LinearMap.comp_apply,
      Representation.IntertwiningMap.toLinearMap_apply] at he
    have hcyc : coefficient K (n + m + 1) (n + m)
        (dualBasis K (n + m + 1) 0) =
          dualBasis K (n + m + 1) (Fin.last (n + m)) := by
      simpa only [Fin.val_last] using
        coefficient_cyclic K (n + m) (Fin.last (n + m))
    change f (coefficient K (n + m + 1) (n + m)
        (dualBasis K (n + m + 1) 0)) =
      tensorCoefficient K n m (Fin.last (n + m))
        (f (dualBasis K (n + m + 1) 0)) at he
    rwa [hcyc] at he
  obtain ⟨c, hc⟩ := tensor_coefficient_top_range K n m
    (f (dualBasis K (n + m + 1) 0))
  change tensorCoefficient K n m (Fin.last (n + m))
    (f (dualBasis K (n + m + 1) 0)) = c • w at hc
  rw [hf, hc, map_smul, hgw, smul_zero, LinearMap.zero_apply]

/-- Every actual restricted endomorphism has constant diagonal; this follows
from finite samples and the original cyclic and diagonal Hasse identities. -/
theorem embedded_endomorphism_constant_diagonal (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : (Representation.IntertwiningMap ((dualAction K (N + 1)).comp α.toMultiplicative))
      ((dualAction K (N + 1)).comp α.toMultiplicative))
    (i : Fin (N + 1)) :
    h (dualBasis K (N + 1) i) (Polynomial.degreeLT.basis K (N + 1) i) =
      h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) := by
  have hd (j : Fin (N + 1)) :
      h (dualBasis K (N + 1) j)
          (Polynomial.degreeLT.basis K (N + 1) j) =
        h (dualBasis K (N + 1) 0)
          (Polynomial.degreeLT.basis K (N + 1) 0) := by
    have hcomm : h.toLinearMap.comp (coefficient K (N + 1) j.val) =
        (coefficient K (N + 1) j.val).comp h.toLinearMap := by
      exact restricted_dual_intertwines_coefficients α hα
        (le_refl _) (le_refl _) (by omega) h j
    have he := congrArg (fun v : DualPower K (N + 1) =>
      v (Polynomial.degreeLT.basis K (N + 1) j))
        (LinearMap.congr_fun hcomm (dualBasis K (N + 1) 0))
    simp only [LinearMap.comp_apply,
      Representation.IntertwiningMap.toLinearMap_apply] at he
    simpa only [coefficient_cyclic, coefficient_diagonal] using he
  exact (hd i).trans (hd (Fin.last N)).symm

theorem embedded_endomorphism_trace (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : (Representation.IntertwiningMap ((dualAction K (N + 1)).comp α.toMultiplicative))
      ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    LinearMap.trace K (DualPower K (N + 1)) h.toLinearMap =
      ((N + 1 : ℕ) : K) * h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) := by
  classical
  calc
    LinearMap.trace K (DualPower K (N + 1)) h.toLinearMap =
        ∑ i : Fin (N + 1), h (dualBasis K (N + 1) i)
          (Polynomial.degreeLT.basis K (N + 1) i) := by
      rw [LinearMap.trace_eq_matrix_trace K (dualBasis K (N + 1))]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
        dualBasis, Module.Basis.dualBasis_repr,
        Representation.IntertwiningMap.toLinearMap_apply]
    _ = ∑ _i : Fin (N + 1), h (dualBasis K (N + 1) (Fin.last N))
          (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) :=
      sum_congr rfl (fun i _ => embedded_endomorphism_constant_diagonal α hα N hsize h i)
    _ = _ := by simp [nsmul_eq_mul]

theorem embedded_composition_trace_zero (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card E)
    (hchoose : ((n + m).choose n : K) = 0)
    (f : (Representation.IntertwiningMap ((dualAction K (n + m + 1)).comp α.toMultiplicative))
      ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
    (g : (Representation.IntertwiningMap ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative))
      ((dualAction K (n + m + 1)).comp α.toMultiplicative)) :
    LinearMap.trace K (DualPower K (n + m + 1))
      (g.toLinearMap.comp f.toLinearMap) = 0 := by
  have ht := embedded_endomorphism_trace α hα (n + m) hsize (g.comp f)
  change LinearMap.trace K (DualPower K (n + m + 1))
    (g.toLinearMap.comp f.toLinearMap) =
      ((n + m + 1 : ℕ) : K) * g (f (dualBasis K (n + m + 1)
        (Fin.last (n + m))))
        (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) at ht
  rw [ht, embedded_composition_top_coordinate_zero α hα n m hsize hchoose f g,
    mul_zero]

end GenericRectangularTrace

section RelativeRestriction

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {H : Type uE} [Group H]
  {A B C M : Type uK}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup M] [Module K M]

/-- Restriction retains the same original existential X, i and r. -/
theorem restrict_relativeProjective
    (ι : H →* G) (τ : Representation K G M)
    {ρ : Representation K G A}
    (hρ : RelativeProjective τ (Rep.of ρ)) :
    RelativeProjective (τ.comp ι) (Rep.of (ρ.comp ι)) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  refine ⟨Rep.of (X.ρ.comp ι),
    restrictIntertwiner ι i, restrictIntertwiner ι r, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun q => q x) hri

/-- The original decomposition-to-stable maps with an independent group
universe. The field-only old helper identifies its group and field universes;
this proof supplies the genuinely consumed general-universe variant. -/
private theorem stable_from_decomposition
    (τ : Representation K G M) (ρ : Representation K G A)
    (σ : Representation K G B) (κ : Representation K G C)
    (e : σ.Equiv (ρ.prod κ))
    (hκ : RelativeProjective τ (Rep.of κ)) : RelativeStableIso τ ρ σ := by
  let inS := Representation.IntertwiningMap.inl K ρ κ
  let prS := Representation.IntertwiningMap.fst K ρ κ
  let inR := Representation.IntertwiningMap.inr K ρ κ
  let prR := Representation.IntertwiningMap.snd K ρ κ
  let f := e.symm.toIntertwiningMap.comp inS
  let g := prS.comp e.toIntertwiningMap
  have hgf : g.comp f = .id ρ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (e (e.symm (x, 0))).1 = x
    rw [e.apply_symm_apply]
  refine ⟨f, g, ?_, ?_⟩
  · rw [hgf, sub_self]
    exact relativeFactors_zero τ ρ ρ
  · refine ⟨Rep.of κ, hκ, prR.comp e.toIntertwiningMap,
      -(e.symm.toIntertwiningMap.comp inR), ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change -e.symm (0, (e x).2) = e.symm ((e x).1, 0) - x
    apply e.injective
    rw [map_neg, map_sub]
    change -e.toLinearEquiv (e.toLinearEquiv.symm (0, (e x).2)) =
      e.toLinearEquiv (e.toLinearEquiv.symm ((e x).1, 0)) - e.toLinearEquiv x
    rw [e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.apply_symm_apply]
    apply Prod.ext <;> simp

private theorem stable_from_zero_left
    (τ : Representation K G M) (ρ : Representation K G A)
    (σ : Representation K G B) [Subsingleton A]
    (hσ : RelativeProjective τ (Rep.of σ)) : RelativeStableIso τ ρ σ := by
  refine ⟨0, 0, ?_, ?_⟩
  · have hz : (0 : ρ.IntertwiningMap ρ) - .id ρ = 0 := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    simpa only [Representation.IntertwiningMap.zero_comp, hz] using
      relativeFactors_zero τ ρ ρ
  · refine ⟨Rep.of σ, hσ, .id σ, -(.id σ), ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp

end RelativeRestriction

/-- Reuses the arithmetic argument of
`ElmerKadrResidueCriterion.first_dimension_ne_zero` from
`D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion.lean`
for an arbitrary coefficient field. -/
private theorem first_dimension_ne_zero_generic
    {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (a b u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u + v ≤ p) :
    (((p * a + u) + (p * b + v) - 1 : ℕ) : K) ≠ 0 := by
  have hsum : (p * a + u) + (p * b + v) = p * (a + b) + (u + v) := by ring
  have hdim : (p * a + u) + (p * b + v) - 1 =
      p * (a + b) + (u + v - 1) := by rw [hsum]; omega
  rw [hdim, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul, zero_add]
  intro hz
  have hd : p ∣ u + v - 1 := (CharP.cast_eq_zero_iff K p _).mp hz
  have hp_le := Nat.le_of_dvd (by omega : 0 < u + v - 1) hd
  omega

section FaithfulClassification

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {E : Type uE} [AddGroup E] [Fintype E]

private def firstInclusionEmbedded (α : E →+ K) (i j t : ℕ) (ht : 0 < t) :
    (Representation.IntertwiningMap ((dualAction K (i + j - 1)).comp α.toMultiplicative))
      ((expectedAction (K := K) i j t).comp α.toMultiplicative) :=
  restrictIntertwiner α.toMultiplicative
    (ElmerKadrResidueCriterion.firstInclusion (K := K) i j t ht)

private def firstProjectionEmbedded (α : E →+ K) (i j t : ℕ) (ht : 0 < t) :
    (Representation.IntertwiningMap ((expectedAction (K := K) i j t).comp α.toMultiplicative))
      ((dualAction K (i + j - 1)).comp α.toMultiplicative) :=
  restrictIntertwiner α.toMultiplicative
    (ElmerKadrResidueCriterion.firstProjection (K := K) i j t ht)

private theorem firstProjectionEmbedded_inclusionEmbedded
    (α : E →+ K) (i j t : ℕ) (ht : 0 < t) :
    (firstProjectionEmbedded α i j t ht).comp
        (firstInclusionEmbedded α i j t ht) =
      .id ((dualAction K (i + j - 1)).comp α.toMultiplicative) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DirectSum.component.lof_self (R := K) (ι := Fin t)
    (M := fun ell : Fin t => DualPower K (i + j - (2 * ell.val + 1))) ⟨0, ht⟩ x

/-- Faithfulness forces every nonzero element to have additive order p. -/
theorem prime_dvd_card_embedding
    (α : E →+ K) (hα : Function.Injective α) [Nontrivial E] :
    p ∣ Fintype.card E := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have ho : addOrderOf e = p :=
    addOrderOf_eq_prime (embedding_nsmul_eq_zero (p := p) α hα e) he
  rw [← ho]
  exact addOrderOf_dvd_card

/-- In particular the last actual relative summand has dimension q, not
merely the largest multiple of p below an unspecified field cardinality. -/
theorem top_relative_dimension
    (α : E →+ K) (hα : Function.Injective α) [Nontrivial E] :
    p * (Fintype.card E / p) = Fintype.card E := by
  exact Nat.mul_div_cancel' (prime_dvd_card_embedding (p := p) α hα)

private theorem no_stable_with_retract
    (α : E →+ K) (hα : Function.Injective α) (e : E) (he : e ≠ 0)
    {A : Type uK} [AddCommGroup A] [Module K A]
    (s n m d : ℕ) (hd : d = n + m + 1) (hsize : n + m + 2 ≤ Fintype.card E)
    (hchoose : ((n + m).choose n : K) = 0)
    (hdim : (d : K) ≠ 0)
    (σ : Representation K (Multiplicative E) A)
    (jU : (Representation.IntertwiningMap ((dualAction K d).comp α.toMultiplicative)) σ)
    (pU : σ.IntertwiningMap
      ((dualAction K d).comp α.toMultiplicative))
    (hpj : pU.comp jU = .id
      ((dualAction K d).comp α.toMultiplicative)) :
    ¬ RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
        α.toMultiplicative)
      σ ((RectangularTensorObstruction.tensorAction K n m).comp α.toMultiplicative) := by
  subst d
  intro hs
  obtain ⟨f, g, hS, _⟩ := hs
  let fU := f.comp jU
  let gU := pU.comp g
  have herror : RelativeFactors
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
        α.toMultiplicative)
      (gU.comp fU - .id ((dualAction K (n + m + 1)).comp α.toMultiplicative)) := by
    obtain ⟨P, hP, β, γ, hγβ⟩ := hS
    refine ⟨P, hP, β.comp jU, pU.comp γ, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change pU (γ (β (jU x))) = pU (g (f (jU x))) - x
    have hx := congrArg (fun k => k (jU x)) hγβ
    change γ (β (jU x)) = g (f (jU x)) - jU x at hx
    have hpx := congrArg (fun k => k x) hpj
    change pU (jU x) = x at hpx
    rw [hx, map_sub, hpx]
  letI : Module.Finite K (DualPower K (n + m + 1)) :=
    Module.Finite.of_basis (dualBasis K (n + m + 1))
  have hid : LinearMap.trace K (DualPower K (n + m + 1)) LinearMap.id =
      ((n + m + 1 : ℕ) : K) := by
    rw [LinearMap.trace_id, Module.finrank_eq_card_basis (dualBasis K (n + m + 1))]
    simp
  have htrace := trace_relativeFactors_for_embedding (p := p) α hα e he s _ _ herror
  have hrect := embedded_composition_trace_zero α hα n m hsize hchoose fU gU
  change LinearMap.trace K (DualPower K (n + m + 1))
    (gU.toLinearMap.comp fU.toLinearMap - LinearMap.id) = 0 at htrace
  rw [map_sub, hrect, hid] at htrace
  exact hdim (neg_eq_zero.mp (by simpa only [zero_sub] using htrace))

private theorem embedded_not_stable_of_zero_choose
    (α : E →+ K) (hα : Function.Injective α) (e : E) (he : e ≠ 0)
    (s i j t : ℕ) (hi : 0 < i) (hj : 0 < j) (ht : 0 < t)
    (hsize : i + j ≤ Fintype.card E)
    (hchoose : ((i + j - 2).choose (i - 1) : K) = 0)
    (hdim : ((i + j - 1 : ℕ) : K) ≠ 0) :
    ¬ RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
        α.toMultiplicative)
      ((expectedAction (K := K) i j t).comp α.toMultiplicative)
      ((ElmerKadrResidueCriterion.tensorAction (K := K) i j).comp
        α.toMultiplicative) := by
  have hn : i - 1 + 1 = i := by omega
  have hm : j - 1 + 1 = j := by omega
  have hN : (i - 1) + (j - 1) = i + j - 2 := by omega
  have htop : (i - 1) + (j - 1) + 1 = i + j - 1 := by omega
  have hnot := no_stable_with_retract α hα e he s (i - 1) (j - 1)
    (i + j - 1) htop.symm (by omega)
    (by simpa only [hN] using hchoose) hdim
    ((expectedAction (K := K) i j t).comp α.toMultiplicative)
    (firstInclusionEmbedded α i j t ht) (firstProjectionEmbedded α i j t ht)
    (firstProjectionEmbedded_inclusionEmbedded α i j t ht)
  have transfer (r s' : ℕ) (hr : r = i - 1 + 1) (hs' : s' = j - 1 + 1) :
      ¬ RelativeStableIso
        ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
          α.toMultiplicative)
        ((expectedAction (K := K) i j t).comp α.toMultiplicative)
        ((ElmerKadrResidueCriterion.tensorAction (K := K) r s').comp
          α.toMultiplicative) := by
    subst r s'
    exact hnot
  exact transfer i j hn.symm hm.symm

/-- Original-M classification for an arbitrary faithful finite additive
embedding. K may be infinite; E has its own universe. S is the literal
Fin(min u v) sum and the original RelativeFactors retains all P/X witnesses. -/
theorem original_relative_criterion_for_embedding
    (α : E →+ K) (hα : Function.Injective α) [Nontrivial E]
    (a b u v : ℕ)
    (hup : u < p) (hvp : v < p) (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card E) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      ((expectedAction (K := K) (p * a + u) (p * b + v) (min u v)).comp
        α.toMultiplicative)
      ((ElmerKadrResidueCriterion.tensorAction (K := K) (p * a + u)
        (p * b + v)).comp α.toMultiplicative) ↔
      u = 0 ∨ v = 0 ∨ ((a + b).choose a : K) ≠ 0 := by
  classical
  have ha : a ≤ Fintype.card E / p := by
    apply (Nat.le_div_iff_mul_le (Fact.out : p.Prime).pos).2
    rw [Nat.mul_comm a p]
    omega
  have hb : b ≤ Fintype.card E / p := by
    apply (Nat.le_div_iff_mul_le (Fact.out : p.Prime).pos).2
    rw [Nat.mul_comm b p]
    omega
  let ι := α.toMultiplicative
  let τK := PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
    (Fintype.card E / p)
  let σK := ElmerKadrResidueCriterion.tensorAction (K := K)
    (p * a + u) (p * b + v)
  have hzero (hz : u = 0 ∨ v = 0) :
      RelativeStableIso (τK.comp ι)
        ((expectedAction (K := K) (p * a + u) (p * b + v) (min u v)).comp ι)
        (σK.comp ι) := by
    have hmin : min u v = 0 := by
      rcases hz with hu0 | hv0
      · simp only [hu0, Nat.zero_min]
      · simp only [hv0, Nat.min_zero]
    have hPk : RelativeProjective τK (Rep.of σK) := by
      have hpR := residue_remainder_relativeProjective (K := K) (p := p)
        (Fintype.card E / p) a b u v ha hb
      rw [hmin, Nat.sub_zero, Nat.sub_zero] at hpR
      exact hpR
    have hP := restrict_relativeProjective ι τK hPk
    rw [hmin]
    letI : Subsingleton (ExpectedSpace K (p * a + u) (p * b + v) 0) :=
      ⟨fun x y => DFinsupp.ext (fun ell => Fin.elim0 ell)⟩
    exact stable_from_zero_left _ _ _ hP
  by_cases hu0 : u = 0
  · exact ⟨fun _ => Or.inl hu0, fun _ => hzero (Or.inl hu0)⟩
  by_cases hv0 : v = 0
  · exact ⟨fun _ => Or.inr (Or.inl hv0), fun _ => hzero (Or.inr hv0)⟩
  have hnonzero :
      RelativeStableIso (τK.comp ι)
        ((expectedAction (K := K) (p * a + u) (p * b + v) (min u v)).comp ι)
        (σK.comp ι) ↔ ((a + b).choose a : K) ≠ 0 := by
    constructor
    · intro hs
      by_cases hz : ((a + b).choose a : K) = 0
      · have ht : 0 < min u v := by omega
        have hfactor := step_choose_factorization (K := K) a b u v 0
          (by omega) (by omega) huv ht
        have hzeroChoose : (((p * a + u) + (p * b + v) - 2).choose
            (p * a + u - 1) : K) = 0 := by
          simpa only [Nat.mul_zero, Nat.sub_zero, hz, mul_zero] using hfactor
        obtain ⟨e, he⟩ := exists_ne (0 : E)
        exact False.elim ((embedded_not_stable_of_zero_choose
          (p := p) α hα e he (Fintype.card E / p)
          (p * a + u) (p * b + v) (min u v)
          (by omega) (by omega) ht hsize hzeroChoose
          (first_dimension_ne_zero_generic (K := K) (p := p) a b u v (by omega) (by omega) huv)) hs)
      · exact hz
    · intro hchoose
      obtain ⟨eK⟩ := residue_decomposition (K := K) a b u v
        (by omega) (by omega) huv hchoose
      have hPk := residue_remainder_relativeProjective (K := K) (p := p)
        (Fintype.card E / p) a b u v ha hb
      have hPE := restrict_relativeProjective ι τK hPk
      have eE := restrictEquiv ι eK
      exact stable_from_decomposition _ _ _ _ eE hPE
  constructor
  · intro hs
    exact Or.inr (Or.inr (hnonzero.mp hs))
  · intro hcases
    rcases hcases with hu | hv | hchoose
    · exact False.elim (hu0 hu)
    · exact False.elim (hv0 hv)
    · exact hnonzero.mpr hchoose

/-- The same original criterion in Kummer's exact no-carry form. -/
theorem original_relative_criterion_no_carry
    (α : E →+ K) (hα : Function.Injective α) [Nontrivial E]
    (a b u v : ℕ)
    (hup : u < p) (hvp : v < p) (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card E) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      ((expectedAction (K := K) (p * a + u) (p * b + v) (min u v)).comp
        α.toMultiplicative)
      ((ElmerKadrResidueCriterion.tensorAction (K := K) (p * a + u)
        (p * b + v)).comp α.toMultiplicative) ↔
      u = 0 ∨ v = 0 ∨ ∀ k ∈ Finset.Ico 1 (Nat.log p (a + b) + 1),
        a % p ^ k + b % p ^ k < p ^ k := by
  rw [original_relative_criterion_for_embedding α hα a b u v hup hvp huv hsize]
  refine or_congr Iff.rfl (or_congr Iff.rfl ?_)
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  have hchoose : (a + b).choose a ≠ 0 := Nat.choose_ne_zero (by omega)
  have hval : ((a + b).choose a).factorization p = 0 ↔ ¬p ∣ (a + b).choose a := by
    simp only [Nat.factorization_eq_zero_iff, (Fact.out : p.Prime), not_true,
      hchoose, or_false, false_or]
  rw [← hval]
  have hk := Nat.factorization_choose' (p := p) (n := b) (k := a)
    (b := Nat.log p (a + b) + 1) (Fact.out : p.Prime)
    (by rw [Nat.add_comm b a]; omega)
  rw [Nat.add_comm b a] at hk
  rw [hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [not_le]

end FaithfulClassification

end D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
