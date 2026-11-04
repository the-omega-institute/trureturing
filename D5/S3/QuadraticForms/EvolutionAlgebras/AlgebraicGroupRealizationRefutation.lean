/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.claim; result=D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result; claim=D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.claim
   digest: SL3 cannot realize full evolution algebra automorphism functors. -/

/-
admission_basis: open-problem-resolution (#21840; Refuted)
result: proof_shape: content;
  escape_witness: EvolutionAutomorphismTangentBridge.realizationDerivative_surjective.
Direct frozen dependencies:
  DerivationAnnihilatorObstruction.derivations:
    sha256:be4fe9f79c6928168f52615918c3bc4bf02851f8ab2d6da4883e1aa2bacfaff4
  DerivationAnnihilatorObstruction.IsEvolutionAlgebra:
    sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d
  SemisimpleDerivationClassification.result:
    sha256:508eb9c392ef8f2c5c00491e0da7f31d5a291eb0548b07799f058cc817b4438d
  SemisimpleDerivationClassification.SmallOrthogonal.diagonal_zero:
    sha256:83b9374a6729f437c6000d1835491ecdde18ac4172a81f1d4b9e761ca93fd58b
  SemisimpleDerivationClassification.SmallOrthogonal.coefficient_skew:
    sha256:fba1ba0a3c13ffce9fcec6ff5cc78d1402a3b466a18f1ab63a9460d64c21008c
The dependency names above have prefix D5.S3.QuadraticForms.EvolutionAlgebras;
identities denote declarations in the scoped candidate report. Their owning modules
are frozen on the protected base; the last two declarations are published owners.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22191.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The SL3 witness answers the algebraic-group and group-scheme interrogatives over
complex numbers; it does not settle abstract groups or the full SLn family.
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import Mathlib.Analysis.Complex.Polynomial.Basic
import D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.LinearAlgebra.Matrix.IsDiag


set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 200000

open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge

namespace D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Dimensions
attribute [local instance 100] LieRing.ofAssociativeRing
open LieAlgebra
variable {k : Type} [Field k] [CharZero k]

private def upperMap (m : ℕ) : Orthogonal.so (Fin m) k →ₗ[k] ({p : Fin m × Fin m // p.1 < p.2} → k) :=
  LinearMap.pi fun p => (LinearMap.proj p.val.2).comp
    ((LinearMap.proj p.val.1).comp (Orthogonal.so (Fin m) k).toSubmodule.subtype)

private def fromUpper {m : ℕ} (u : {p : Fin m × Fin m // p.1 < p.2} → k) : Matrix (Fin m) (Fin m) k :=
  fun i j => if h : i < j then u ⟨(i,j),h⟩ else if h : j < i then -u ⟨(j,i),h⟩ else 0

private theorem fromUpper_mem {m : ℕ} (u : {p : Fin m × Fin m // p.1 < p.2} → k) :
    fromUpper u ∈ Orthogonal.so (Fin m) k := by
  rw [Orthogonal.mem_so]
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [fromUpper, h, not_lt.mpr (le_of_lt h)]
  · subst j; simp [fromUpper]
  · simp [fromUpper, h, not_lt.mpr (le_of_lt h)]

private theorem upperMap_bijective (m : ℕ) : Function.Bijective (upperMap (k := k) m) := by
  constructor
  · intro A B h
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact congrFun h ⟨(i,j),hij⟩
    · subst j; rw [D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.diagonal_zero, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.diagonal_zero]
    · rw [D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.coefficient_skew A j i, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.coefficient_skew B j i]
      exact congrArg Neg.neg (congrFun h ⟨(j,i),hij⟩)
  · intro u
    refine ⟨⟨fromUpper u, fromUpper_mem u⟩, ?_⟩
    funext p
    exact dif_pos p.property

private noncomputable def upperEquiv (m : ℕ) :
    Orthogonal.so (Fin m) k ≃ₗ[k] ({p : Fin m × Fin m // p.1 < p.2} → k) :=
  LinearEquiv.ofBijective (upperMap m) (upperMap_bijective m)

private theorem upper_card (m : ℕ) : Fintype.card ({p : Fin m × Fin m // p.1 < p.2}) = m.choose 2 := by
  change Fintype.card {p : Fin m × Fin m // p.1 < p.2} = _
  rw [Fintype.card_subtype]
  simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin m))))

private theorem so_finrank (m : ℕ) :
    Module.finrank k (Orthogonal.so (Fin m) k) = m.choose 2 := by
  simpa only [Module.finrank_pi, upper_card] using (upperEquiv (k := k) m).finrank_eq

private theorem sl3_finrank : Module.finrank k (SpecialLinear.sl (Fin 3) k) = 8 := by
  have ht : Matrix.traceLinearMap (Fin 3) k k ≠ 0 :=
    LinearMap.ne_zero_of_surjective (Matrix.trace_surjective (n := Fin 3) (R := k))
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero ht
  change Module.finrank k (SpecialLinear.sl (Fin 3) k) + 1 = _ at h
  have hh : Module.finrank k (Matrix (Fin 3) (Fin 3) k) = 9 := by
    simpa using (Module.finrank_matrix (R := k) (M := k) (Fin 3) (Fin 3))
  rw [hh] at h
  omega

private theorem so_small_of_finrank_le_eight (m : ℕ) (hm : 3 ≤ m)
    (h : Module.finrank k (Orthogonal.so (Fin m) k) ≤ 8) : m = 3 ∨ m = 4 := by
  rw [so_finrank] at h
  have hh : ¬5 ≤ m := by
    intro h5
    have hc := Nat.choose_le_choose 2 h5
    change 10 ≤ m.choose 2 at hc
    omega
  omega

private theorem no_sum_three_six {ι : Type} [Fintype ι] (f : ι → ℕ)
    (hf : ∀ i, f i = 3 ∨ f i = 6) : (∑ i, f i) ≠ 8 := by
  have hd : 3 ∣ ∑ i, f i := Finset.dvd_sum (fun i _ => by rcases hf i with h | h <;> rw [h] <;> norm_num)
  intro h
  rw [h] at hd
  norm_num at hd

end D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Dimensions


set_option autoImplicit false
set_option maxHeartbeats 200000
namespace D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Semisimple
attribute [local instance 100] LieRing.ofAssociativeRing
open LieAlgebra
variable {k : Type} [Field k] [CharZero k]

private theorem double_single_offdiag (A : SpecialLinear.sl (Fin 3) k)
    (i j : Fin 3) (hij : i ≠ j) :
    (⁅A, ⁅A, SpecialLinear.single j i hij.symm 1⁆⁆).val i j = -2 * (A.val i j)^2 := by
  change (A.val * (A.val * Matrix.single j i 1 - Matrix.single j i 1 * A.val) -
    (A.val * Matrix.single j i 1 - Matrix.single j i 1 * A.val) * A.val : Matrix (Fin 3) (Fin 3) k) i j = _
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.mul_apply, Matrix.single, Fin.sum_univ_succ] <;> ring

private theorem ad_square_zero_offdiag (A : SpecialLinear.sl (Fin 3) k)
    (hA : ∀ B : SpecialLinear.sl (Fin 3) k, ⁅A, ⁅A, B⁆⁆ = 0) :
    ∀ i j, i ≠ j → A.val i j = 0 := by
  intro i j hij
  have h := congrArg (fun B : SpecialLinear.sl (Fin 3) k => B.val i j)
    (hA (SpecialLinear.single j i hij.symm 1))
  rw [double_single_offdiag A i j hij] at h
  change -2 * (A.val i j)^2 = 0 at h
  have hh : (A.val i j)^2 = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
  exact (pow_eq_zero_iff (by omega)).mp hh

private theorem double_single_diagonal (A : SpecialLinear.sl (Fin 3) k)
    (hoff : ∀ i j, i ≠ j → A.val i j = 0) (i j : Fin 3) (hij : i ≠ j) :
    (⁅A, ⁅A, SpecialLinear.single i j hij 1⁆⁆).val i j = (A.val i i - A.val j j)^2 := by
  have hdiag : A.val = Matrix.diagonal (fun i => A.val i i) := by
    exact (Matrix.IsDiag.diagonal_diag (fun i j hij => hoff i j hij)).symm
  change (A.val * (A.val * Matrix.single i j 1 - Matrix.single i j 1 * A.val) -
    (A.val * Matrix.single i j 1 - Matrix.single i j 1 * A.val) * A.val : Matrix (Fin 3) (Fin 3) k) i j = _
  rw [hdiag]
  simp [Matrix.mul_apply, Matrix.single, Matrix.diagonal, hij, hij.symm,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

private theorem ad_square_zero_eq_zero (A : SpecialLinear.sl (Fin 3) k)
    (hA : ∀ B : SpecialLinear.sl (Fin 3) k, ⁅A, ⁅A, B⁆⁆ = 0) : A = 0 := by
  have hoff := ad_square_zero_offdiag A hA
  have hdiag (i j : Fin 3) : A.val i i = A.val j j := by
    by_cases hij : i = j
    · subst j; rfl
    · have h := congrArg (fun B : SpecialLinear.sl (Fin 3) k => B.val i j)
        (hA (SpecialLinear.single i j hij 1))
      rw [double_single_diagonal A hoff i j hij] at h
      change (A.val i i - A.val j j)^2 = 0 at h
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by omega)).mp h)
  have ht : A.val 0 0 + A.val 1 1 + A.val 2 2 = 0 := by
    have h := A.property
    change Matrix.trace A.val = 0 at h
    simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using h
  have hz : A.val 0 0 = 0 := by
    rw [hdiag 1 0, hdiag 2 0] at ht
    have h3 : (3 : k) * A.val 0 0 = 0 := by linear_combination ht
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j; change A.val i i = 0; rw [hdiag i 0, hz]
  · exact hoff i j hij

private theorem sl3_trivial_radical : HasTrivialRadical k (SpecialLinear.sl (Fin 3) k) := by
  apply (hasTrivialRadical_iff_no_abelian_ideals k (SpecialLinear.sl (Fin 3) k)).mpr
  intro I hI
  letI : IsLieAbelian I := hI
  apply le_antisymm ?_ bot_le
  intro A hA
  change A = 0
  apply ad_square_zero_eq_zero A
  intro B
  have hAB : ⁅A,B⁆ ∈ I := lie_mem_left k (SpecialLinear.sl (Fin 3) k) I _ _ hA
  have hz := trivial_lie_zero I I (⟨A,hA⟩ : I) (⟨⁅A,B⁆,hAB⟩ : I)
  exact congrArg Subtype.val hz

end D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Semisimple

namespace D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Obstruction
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
open LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]

private theorem orthogonal_sum_not_eight (r : ℕ) (m : Fin r → ℕ) (hm : ∀ i, 3 ≤ m i) :
    (∑ i, Module.finrank k (Orthogonal.so (Fin (m i)) k)) ≠ 8 := by
  intro hsum
  have hsmall (i : Fin r) : m i = 3 ∨ m i = 4 := by
    apply Dimensions.so_small_of_finrank_le_eight (k := k) (m i) (hm i)
    have h := Finset.single_le_sum (s := Finset.univ) (a := i) (fun j _ => Nat.zero_le
      (Module.finrank k (Orthogonal.so (Fin (m j)) k))) (Finset.mem_univ i)
    omega
  apply Dimensions.no_sum_three_six (fun i => Module.finrank k (Orthogonal.so (Fin (m i)) k)) ?_ hsum
  intro i
  rcases hsmall i with h | h
  · left; rw [Dimensions.so_finrank, h]; decide
  · right; rw [Dimensions.so_finrank, h]; decide

private theorem derivations_not_sl3 (d : ℕ)
    (μ : (Fin d → k) →ₗ[k] (Fin d → k) →ₗ[k] (Fin d → k))
    (hE : IsEvolutionAlgebra μ) :
    ¬ Nonempty (derivations μ ≃ₗ⁅k⁆ SpecialLinear.sl (Fin 3) k) := by
  rintro ⟨e⟩
  letI := Semisimple.sl3_trivial_radical (k := k)
  letI : IsKilling k (derivations μ) := e.symm.isKilling
  have hS : IsSemisimple k (derivations μ) := inferInstance
  obtain ⟨r,m,hm,⟨f⟩⟩ :=
    D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result k
      (Fin d → k) μ hE hS
  have hdim := (e.symm.trans f).toLinearEquiv.finrank_eq
  rw [Dimensions.sl3_finrank, Module.finrank_directSum] at hdim
  exact orthogonal_sum_not_eight r m hm hdim.symm


end D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.Obstruction

namespace D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation

def claim : Prop :=
  ∀ (G : LinearAlgebraicGroup ℂ),
    ∃ (d : ℕ) (μ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
      IsEvolutionAlgebra μ ∧ Nonempty (Realizes G μ)

theorem result : ¬ claim := by
  intro h
  obtain ⟨d, μ, hE, ⟨e⟩⟩ := h (slGroup 3)
  obtain ⟨f⟩ := tangent_lie_equivalence μ e
  exact Obstruction.derivations_not_sl3 (k := ℂ) d μ hE ⟨f.symm⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation
