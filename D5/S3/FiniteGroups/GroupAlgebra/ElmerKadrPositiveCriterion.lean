import D5.S3.FiniteGroups.GroupAlgebra.ArithmeticTensorStableObstruction
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Factorization
import D5.S3.FiniteGroups.GroupAlgebra.BoundedTensorPolarization
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The corrected p-multiple criterion for the original Elmer–Kadr relative module

Multiplication and bounded polarization split the polynomial tensor sequence
when the binomial coefficient is nonzero. Dualization transports both actual
inverse errors, and the kernel complement is a retract of a tensor with the
literal relative direct sum. Zero indices use the actual tensor unit.

Over a finite field with `p*a + p*b + 2 ≤ card K`, the prime-cyclic trace
obstruction gives the converse for the original relative module with
`card K / p` summands. Lucas and Kummer identify this criterion with the
absence of carries in `a + b` in base p.

Source: Elmer–Kadr, DOI 10.1007/s13366-026-00855-9, Section 2.2 and Conjecture 3.7(a).
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
open Polynomial
open scoped TensorProduct DirectSum

universe uK uG

section DualMaps

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {A B : Type uK} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  {ρ : Representation K G A} {τ : Representation K G B}

/-- Transpose reverses an actual intertwiner; the inverse group element is
the one in the definition of the contragredient representation. -/
def dualIntertwiner (f : ρ.IntertwiningMap τ) :
    τ.dual.IntertwiningMap ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' c := by
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    change l (τ c⁻¹ (f x)) = l (f (ρ c⁻¹ x))
    rw [f.isIntertwining]

/-- The canonical finite-dimensional dual tensor identification is equivariant
for the actual contragredient actions. Its evaluation uses Mathlib's order
`g y * f x`; no matrix model or basis change defines the action. -/
def dualTensorEquiv [Module.Finite K A] [Module.Finite K B]
    [Module.Projective K A] [Module.Projective K B]
    (ρ : Representation K G A) (τ : Representation K G B) :
    (ρ.dual.tprod τ.dual).Equiv (ρ.tprod τ).dual :=
  Representation.Equiv.mk (TensorProduct.dualDistribEquiv K A B) fun c => by
    apply TensorProduct.ext'
    intro f g
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.dualDistribEquiv K A B
        (ρ.dual c f ⊗ₜ[K] τ.dual c g) (x ⊗ₜ[K] y) =
      TensorProduct.dualDistribEquiv K A B (f ⊗ₜ[K] g)
        (ρ c⁻¹ x ⊗ₜ[K] τ c⁻¹ y)
    simp only [TensorProduct.dualDistribEquiv_tmul_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]

end DualMaps

section ZeroAndUnits

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {M U Z : Type uK} [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z]

/-- A literal zero representation is a retract of K tensor M by zero maps.
Thus the zero error has an explicit witness for the ORIGINAL RelativeFactors. -/
theorem relativeFactors_zero (τ : Representation K G M)
    (ρ : Representation K G U) (σ : Representation K G Z) :
    RelativeFactors τ (0 : ρ.IntertwiningMap σ) := by
  let ζ : Representation K G (Fin 0 → K) :=
    Representation.trivial K G (Fin 0 → K)
  refine ⟨Rep.of ζ, ?_, 0, 0, ?_⟩
  · refine ⟨Rep.of (Representation.trivial K G K), 0, 0, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext j
    exact Fin.elim0 j
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl

/-- An actual equivariant isomorphism gives two explicit zero-error factors. -/
theorem relativeStableIso_of_equiv (τ : Representation K G M)
    {ρ : Representation K G U} {σ : Representation K G Z} (e : ρ.Equiv σ) :
    RelativeStableIso τ ρ σ := by
  refine ⟨e.toIntertwiningMap, e.symm.toIntertwiningMap, ?_, ?_⟩
  · have hz : e.symm.toIntertwiningMap.comp e.toIntertwiningMap - .id ρ = 0 := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      change e.symm (e v) - v = 0
      rw [e.symm_apply_apply, sub_self]
    rw [hz]
    exact relativeFactors_zero τ ρ ρ
  · have hz : e.toIntertwiningMap.comp e.symm.toIntertwiningMap - .id σ = 0 := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      change e (e.symm v) - v = 0
      rw [e.apply_symm_apply, sub_self]
    rw [hz]
    exact relativeFactors_zero τ σ σ

end ZeroAndUnits

section PolynomialUnits

variable {K : Type uK} [Field K]

theorem primal_one_action (c : Multiplicative K) :
    primalAction K 1 c = LinearMap.id := by
  apply (Polynomial.degreeLT.basis K 1).ext
  intro i
  apply Subtype.ext
  have hi : (i : ℕ) = 0 := by have := i.is_lt; omega
  change Polynomial.taylor (Multiplicative.toAdd c)
      (Polynomial.degreeLT.basis K 1 i : K[X]) =
    (Polynomial.degreeLT.basis K 1 i : K[X])
  simp only [Polynomial.degreeLT.basis_val, hi, pow_zero,
    Polynomial.taylor_one, Polynomial.C_1]

theorem dual_one_action (c : Multiplicative K) :
    dualAction K 1 c = LinearMap.id := by
  change (primalAction K 1 c⁻¹).dualMap = LinearMap.id
  rw [primal_one_action, LinearMap.dualMap_id]

/-- V_1 is actually the tensor unit: its original translation action is trivial. -/
def dualOneEquiv :
    (dualAction K 1).Equiv (Representation.trivial K (Multiplicative K) K) :=
  Representation.Equiv.mk
    ((dualBasis K 1).equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)) fun c => by
      rw [dual_one_action]
      apply LinearMap.ext
      intro v
      rfl

variable {U : Type uK} [AddCommGroup U] [Module K U]

/-- The actual left tensor-unit equivalence, including its equivariance. -/
def tensorUnitLeft (ρ : Representation K (Multiplicative K) U) :
    ((dualAction K 1).tprod ρ).Equiv ρ := by
  let e : ((dualAction K 1).tprod ρ).Equiv
      ((Representation.trivial K (Multiplicative K) K).tprod ρ) :=
    Representation.Equiv.mk
      (TensorProduct.congr (dualOneEquiv (K := K)).toLinearEquiv
        (LinearEquiv.refl K U)) fun c => by
        apply TensorProduct.ext'
        intro x y
        change dualOneEquiv (dualAction K 1 c x) ⊗ₜ[K] ρ c y =
          dualOneEquiv x ⊗ₜ[K] ρ c y
        rw [dual_one_action]
        rfl
  exact e.trans (Representation.TensorProduct.lid K ρ)

/-- The actual right tensor-unit equivalence, using the equivariant tensor flip. -/
def tensorUnitRight (ρ : Representation K (Multiplicative K) U) :
    (ρ.tprod (dualAction K 1)).Equiv ρ :=
  (Representation.TensorProduct.comm ρ (dualAction K 1)).trans (tensorUnitLeft ρ)

end PolynomialUnits

section ExactSplitting

variable {K : Type uK} [Field K]

/-- Multiplication intertwines actual translations, by the already proved
diagonal realization of the bounded polynomial tensor map. -/
theorem multiplication_translate (a : K) (n m : ℕ) :
    (multiplication (R := K) n m).comp (tensorTranslate a n m) =
      (Polynomial.taylorLinearEquiv a (n + m + 1)).toLinearMap.comp
        (multiplication n m) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  have hd (z : Trunc K n ⊗[K] Trunc K m) :
      diagonal (tensorPolynomial n m z) = (multiplication n m z : K[X]) :=
    LinearMap.congr_fun (diagonal_tensorPolynomial (R := K) n m) z
  change (multiplication n m (tensorTranslate a n m F) : K[X]) =
    Polynomial.taylor a (multiplication n m F : K[X])
  calc
    _ = diagonal (tensorPolynomial n m (tensorTranslate a n m F)) := (hd _).symm
    _ = Polynomial.taylor a (multiplication n m F : K[X]) := by
      rw [tensorPolynomial_translate, diagonal_translate, hd]

def multiplicationIntertwiner (n m : ℕ) :
    ((primalAction K (n + 1)).tprod (primalAction K (m + 1))).IntertwiningMap
      (primalAction K (n + m + 1)) where
  toLinearMap := multiplication n m
  isIntertwining' c := multiplication_translate (Multiplicative.toAdd c) n m

def differenceIntertwiner (n m : ℕ) :
    ((primalAction K (n + 1)).tprod (primalAction K (m + 1))).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))) where
  toLinearMap := differenceTensor n m
  isIntertwining' c :=
    (tensorTranslate_differenceTensor (Multiplicative.toAdd c) n m).symm

/-- The residual lands in range(d), by exactness and μσ = id. -/
def kernelResidual (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id) :
    (Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) →ₗ[K]
      LinearMap.range (differenceTensor (R := K) n m) :=
  (LinearMap.id - σ.comp (multiplication (n + 1) (m + 1))).codRestrict _ fun F => by
    rw [differenceTensor_range]
    change multiplication (n + 1) (m + 1)
      (F - σ (multiplication (n + 1) (m + 1) F)) = 0
    have hs := LinearMap.congr_fun hσ (multiplication (n + 1) (m + 1) F)
    change multiplication (n + 1) (m + 1)
      (σ (multiplication (n + 1) (m + 1) F)) = multiplication (n + 1) (m + 1) F at hs
    rw [map_sub, hs, sub_self]

/-- h is obtained from the inverse of d onto its PROVED range, applied to
id - σμ. No equivariant-complement choice is made. -/
def kernelRetraction (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id) :
    (Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) →ₗ[K]
      (Trunc K n ⊗[K] Trunc K m) :=
  (LinearEquiv.ofInjective (differenceTensor n m)
    (differenceTensor_injective n m)).symm.toLinearMap.comp (kernelResidual n m σ hσ)

theorem difference_kernelRetraction (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id)
    (F : Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) :
    differenceTensor n m (kernelRetraction n m σ hσ F) =
      F - σ (multiplication (n + 1) (m + 1) F) := by
  exact LinearEquiv.ofInjective_symm_apply (differenceTensor (R := K) n m)
    (h := differenceTensor_injective n m) (kernelResidual n m σ hσ F)

/-- Injectivity of the actual d forces h to intertwine translations. -/
def kernelRetractionIntertwiner (n m : ℕ)
    (σ : (primalAction K ((n + 1) + (m + 1) + 1)).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ.toLinearMap = LinearMap.id) :
    ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))).IntertwiningMap
      ((primalAction K (n + 1)).tprod (primalAction K (m + 1))) where
  toLinearMap := kernelRetraction n m σ.toLinearMap hσ
  isIntertwining' c := by
    apply LinearMap.ext
    intro F
    apply differenceTensor_injective (R := K) n m
    change differenceTensor n m (kernelRetraction n m σ.toLinearMap hσ
        (((primalAction K ((n + 1) + 1)).tprod
          (primalAction K ((m + 1) + 1))) c F)) =
      differenceIntertwiner n m
        (((primalAction K (n + 1)).tprod (primalAction K (m + 1))) c
          (kernelRetraction n m σ.toLinearMap hσ F))
    rw [difference_kernelRetraction, (differenceIntertwiner n m).isIntertwining]
    change _ = (((primalAction K ((n + 1) + 1)).tprod
      (primalAction K ((m + 1) + 1))) c)
        (differenceTensor n m (kernelRetraction n m σ.toLinearMap hσ F))
    rw [difference_kernelRetraction, map_sub]
    change _ - σ (multiplicationIntertwiner (n + 1) (m + 1)
      (((primalAction K ((n + 1) + 1)).tprod
        (primalAction K ((m + 1) + 1))) c F)) = _
    rw [(multiplicationIntertwiner (n + 1) (m + 1)).isIntertwining, σ.isIntertwining]
    simp [multiplicationIntertwiner]
    congr 1

/-- The actual split maps on the ORIGINAL V spaces. The second error is
(- transported h*) d*, through the dual of the source of d, with its sign.
All finite-dimensional instances here come from degreeLT.basis, not extra
hypotheses on the relative module or on an arbitrary factor X. -/
theorem dual_split_maps (n m : ℕ)
    (hbinom : (((n + 1) + (m + 1)).choose (n + 1) : K) ≠ 0) :
    ∃ (f : (dualAction K ((n + 1) + (m + 1) + 1)).IntertwiningMap
          ((dualAction K ((n + 1) + 1)).tprod (dualAction K ((m + 1) + 1))))
      (g : ((dualAction K ((n + 1) + 1)).tprod
          (dualAction K ((m + 1) + 1))).IntertwiningMap
          (dualAction K ((n + 1) + (m + 1) + 1)))
      (q : ((dualAction K ((n + 1) + 1)).tprod
          (dualAction K ((m + 1) + 1))).IntertwiningMap
          ((primalAction K (n + 1)).tprod (primalAction K (m + 1))).dual)
      (r : ((primalAction K (n + 1)).tprod
          (primalAction K (m + 1))).dual.IntertwiningMap
          ((dualAction K ((n + 1) + 1)).tprod (dualAction K ((m + 1) + 1)))),
      g.comp f = .id _ ∧ r.comp q = f.comp g - .id _ := by
  obtain ⟨σ₀, hσ₀, hσtrans⟩ := equivariant_section (K := K) (n + 1) (m + 1) hbinom
  let μ := multiplicationIntertwiner (K := K) (n + 1) (m + 1)
  let σ : (primalAction K ((n + 1) + (m + 1) + 1)).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))) :=
    ⟨σ₀, fun c => (hσtrans (Multiplicative.toAdd c)).symm⟩
  let d := differenceIntertwiner (K := K) n m
  let h := kernelRetractionIntertwiner n m σ hσ₀
  let : Module.Finite K (Primal K ((n + 1) + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K ((n + 1) + 1))
  let : Module.Projective K (Primal K ((n + 1) + 1)) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K ((n + 1) + 1))
  let : Module.Finite K (Primal K ((m + 1) + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K ((m + 1) + 1))
  let : Module.Projective K (Primal K ((m + 1) + 1)) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K ((m + 1) + 1))
  let e := dualTensorEquiv (primalAction K ((n + 1) + 1))
    (primalAction K ((m + 1) + 1))
  let f := e.symm.toIntertwiningMap.comp (dualIntertwiner μ)
  let g := (dualIntertwiner σ).comp e.toIntertwiningMap
  let q := (dualIntertwiner d).comp e.toIntertwiningMap
  let r := e.symm.toIntertwiningMap.comp (-dualIntertwiner h)
  have hμσ (w : Trunc K ((n + 1) + (m + 1))) : μ (σ w) = w :=
    LinearMap.congr_fun hσ₀ w
  have hdh (w : Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) :
      d (h w) = w - σ (μ w) :=
    difference_kernelRetraction n m σ₀ hσ₀ w
  refine ⟨f, g, q, r, ?_, ?_⟩
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change (dualIntertwiner σ) (e (e.symm (dualIntertwiner μ v))) w = v w
    rw [e.apply_symm_apply]
    change v (μ (σ w)) = v w
    rw [hμσ]
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm ((-dualIntertwiner h) (dualIntertwiner d (e v)))) =
      e (e.symm (dualIntertwiner μ (dualIntertwiner σ (e v))) - v)
    rw [e.apply_symm_apply, map_sub, e.apply_symm_apply]
    apply LinearMap.ext
    intro w
    change -(e v) (d (h w)) = (e v) (σ (μ w)) - (e v) w
    rw [hdh, map_sub]
    abel

end ExactSplitting

section RelativeSummand

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "MAction" => PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)

/-- Literal inclusion of one of the specified V_(p*(i+1)) summands of M. -/
def relativeInclusion {s : ℕ} (i : Fin s) :
    (dualAction K (p * (i.val + 1))).IntertwiningMap (MAction s) where
  toLinearMap := DirectSum.lof K (Fin s)
    (fun j : Fin s => DualPower K (p * (j.val + 1))) i
  isIntertwining' c := by
    apply LinearMap.ext
    intro v
    exact (DirectSum.lmap_lof
      (fun j : Fin s => dualAction K (p * (j.val + 1)) c) i v).symm

/-- Literal projection from the same direct sum. -/
def relativeProjection {s : ℕ} (i : Fin s) :
    (MAction s).IntertwiningMap (dualAction K (p * (i.val + 1))) where
  toLinearMap := DirectSum.component K (Fin s)
    (fun j : Fin s => DualPower K (p * (j.val + 1))) i
  isIntertwining' c := by
    apply LinearMap.ext
    intro v
    rfl

theorem relativeProjection_inclusion {s : ℕ} (i : Fin s) :
    (relativeProjection (K := K) (p := p) i).comp (relativeInclusion i) =
      .id (dualAction K (p * (i.val + 1))) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact DirectSum.component.lof_self (R := K) (ι := Fin s)
    (M := fun j : Fin s => DualPower K (p * (j.val + 1))) i v

/-- The actual complement is M-relative-projective: identify its dual tensor,
flip it, and tensor the literal direct-sum inclusion/projection by V_m.
The witness X is V_m; the original existential P/X quantifiers are retained. -/
theorem dualTensor_relativeProjective (s : ℕ) (i : Fin s) (m : ℕ) :
    RelativeProjective (MAction s)
      (Rep.of (((primalAction K (p * (i.val + 1))).tprod
        (primalAction K m)).dual)) := by
  let ρ := dualAction K (p * (i.val + 1))
  let τ := dualAction K m
  let : Module.Finite K (Primal K (p * (i.val + 1))) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (p * (i.val + 1)))
  let : Module.Projective K (Primal K (p * (i.val + 1))) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K (p * (i.val + 1)))
  let : Module.Finite K (Primal K m) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K m)
  let : Module.Projective K (Primal K m) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K m)
  let e := (dualTensorEquiv (primalAction K (p * (i.val + 1)))
    (primalAction K m)).symm.trans (Representation.TensorProduct.comm ρ τ)
  let I := (relativeInclusion (K := K) (p := p) i).lTensor τ
  let R := (relativeProjection (K := K) (p := p) i).lTensor τ
  have hRI : R.comp I = .id (τ.tprod ρ) := by
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[K] relativeProjection i (relativeInclusion i y) = x ⊗ₜ[K] y
    have hy := congrArg (fun k => k y)
      (relativeProjection_inclusion (K := K) (p := p) i)
    change relativeProjection i (relativeInclusion i y) = y at hy
    rw [hy]
  refine ⟨Rep.of τ, I.comp e.toIntertwiningMap, e.symm.toIntertwiningMap.comp R, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change e.symm (R (I (e v))) = v
  have hv := congrArg (fun k => k (e v)) hRI
  change R (I (e v)) = e v at hv
  rw [hv, e.symm_apply_apply]

end RelativeSummand

section PositiveCriterion

variable {K : Type uK} [Field K] {p : ℕ}
  [hpFact : Fact p.Prime] [hChar : CharP K p]

include hpFact hChar

/-- Positive indices: the complement uses the summand a-1 of M. The bound
b ≤ s is unnecessary in this branch, but is retained in the final statement. -/
theorem positive_of_pos (a b s : ℕ) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ s) (hbinom : ((p * a + p * b).choose (p * a) : K) ≠ 0) :
    RelativeStableIso (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (dualAction K (p * a + p * b + 1))
      ((dualAction K (p * a + 1)).tprod (dualAction K (p * b + 1))) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpa : 0 < p * a := Nat.mul_pos hp ha0
  have hpb : 0 < p * b := Nat.mul_pos hp hb0
  let n := p * a - 1
  let m := p * b - 1
  have hn : n + 1 = p * a := by dsimp [n]; omega
  have hm : m + 1 = p * b := by dsimp [m]; omega
  let i : Fin s := ⟨a - 1, by omega⟩
  have hi : p * (i.val + 1) = p * a := by
    congr 1
    dsimp [i]
    omega
  have hP : RelativeProjective
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (Rep.of (((primalAction K (n + 1)).tprod (primalAction K (m + 1))).dual)) := by
    have h := dualTensor_relativeProjective (K := K) (p := p) s i (m + 1)
    rw [hi] at h
    rw [hn]
    exact h
  have hbinom' : (((n + 1) + (m + 1)).choose (n + 1) : K) ≠ 0 := by
    simpa only [hn, hm] using hbinom
  obtain ⟨f, g, q, r, hgf, herr⟩ := dual_split_maps (K := K) n m hbinom'
  have hs : RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (dualAction K ((n + 1) + (m + 1) + 1))
      ((dualAction K ((n + 1) + 1)).tprod (dualAction K ((m + 1) + 1))) := by
    refine ⟨f, g, ?_, ?_⟩
    · rw [hgf, sub_self]
      exact relativeFactors_zero _ _ _
    · exact ⟨Rep.of (((primalAction K (n + 1)).tprod
        (primalAction K (m + 1))).dual), hP, q, r, herr⟩
  have transfer (d e f : ℕ)
      (hd : d = (n + 1) + (m + 1) + 1)
      (he : e = (n + 1) + 1) (hf : f = (m + 1) + 1) :
      RelativeStableIso
        (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
        (dualAction K d) ((dualAction K e).tprod (dualAction K f)) := by
    subst d e f
    exact hs
  exact transfer _ _ _ (by omega) (by omega) (by omega)

/-- The original relative stable isomorphism, including zero indices via the
actual tensor-unit equivalences. -/
theorem positive_criterion (a b s : ℕ) (ha : a ≤ s) (hb : b ≤ s)
    (hbinom : ((p * a + p * b).choose (p * a) : K) ≠ 0) :
    RelativeStableIso (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (dualAction K (p * a + p * b + 1))
      ((dualAction K (p * a + 1)).tprod (dualAction K (p * b + 1))) := by
  by_cases ha0 : a = 0
  · subst a
    have hzero : p * 0 + p * b + 1 = p * b + 1 := by omega
    have hunit : p * 0 + 1 = 1 := by omega
    rw [hzero, Nat.mul_zero]
    have hs := relativeStableIso_of_equiv
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (tensorUnitLeft (dualAction K (p * b + 1))).symm
    exact hs
  by_cases hb0 : b = 0
  · subst b
    simpa only [Nat.mul_zero, Nat.add_zero] using
      (relativeStableIso_of_equiv
        (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
        (tensorUnitRight (dualAction K (p * a + 1))).symm)
  exact positive_of_pos a b s (Nat.pos_of_ne_zero ha0) (Nat.pos_of_ne_zero hb0) ha hbinom

end PositiveCriterion

section FiniteCriterion

variable {K : Type uK} [Field K] [Fintype K] {p : ℕ}
  [Fact p.Prime] [CharP K p]

/-- The corrected p-multiple criterion for the original relative module. -/
theorem relative_stable_iff_binomial (a b : ℕ)
    (hsize : p * a + p * b + 2 ≤ Fintype.card K) :
    RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) (Fintype.card K / p))
      (dualAction K (p * a + p * b + 1))
      ((dualAction K (p * a + 1)).tprod (dualAction K (p * b + 1))) ↔
      ((p * a + p * b).choose (p * a) : K) ≠ 0 := by
  constructor
  · intro hs hz
    exact ArithmeticTensorStableObstruction.no_relative_stable a b
      (Fintype.card K / p) hsize hz hs
  · intro hchoose
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have ha : a ≤ Fintype.card K / p := by
      apply (Nat.le_div_iff_mul_le hp).2
      rw [Nat.mul_comm a p]
      omega
    have hb : b ≤ Fintype.card K / p := by
      apply (Nat.le_div_iff_mul_le hp).2
      rw [Nat.mul_comm b p]
      omega
    exact positive_criterion a b (Fintype.card K / p) ha hb hchoose

/-- Lucas and Kummer identify the same original relative stable isomorphism
with the absence of carries in the sum a+b in base p. -/
theorem relative_stable_iff_no_carry (a b : ℕ)
    (hsize : p * a + p * b + 2 ≤ Fintype.card K) :
    RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) (Fintype.card K / p))
      (dualAction K (p * a + p * b + 1))
      ((dualAction K (p * a + 1)).tprod (dualAction K (p * b + 1))) ↔
      ∀ i ∈ Finset.Ico 1 (Nat.log p (a + b) + 1),
        a % p ^ i + b % p ^ i < p ^ i := by
  rw [relative_stable_iff_binomial a b hsize, ne_eq,
    CharP.cast_eq_zero_iff K p]
  have hlucas := Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := a + b) (b := a)
  rw [Nat.mul_add] at hlucas
  rw [hlucas.dvd_iff (dvd_refl p)]
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

end FiniteCriterion

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
