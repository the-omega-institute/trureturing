/- GID: D5/S3/Quantum/Magic/CliffordThirdMomentNegativity
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/CliffordThirdMomentNegativity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.claim; result=D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result; claim=D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.claim
   digest: A normalized eleven-dimensional state has negative Clifford third-moment expectation. -/

import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace D5.S3.Quantum.Magic.CliffordThirdMomentNegativity

/-!
Zhu, Mao and Yi, *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*,
Conjecture 2, assert the pointwise bound `0 ≤ κ(Ψ,T) ≤ 1` for every odd prime dimension,
every number of qudits, every normalized state and every stochastic Lagrangian subspace.
The source convention is `r(T) = ∑ (x;y) ∈ T, |x⟩⟨y|` and `R(T) = r(T)^{⊗n}`.
The order in `claim` is the complex order: both bounds include that the imaginary part is
zero, and bound the real part. The counterexample has `d = 11`, `n = 1` and
`κ = -1196/64000`. The aggregate inequalities in Conjecture 2 are not asserted here.
-/

open Matrix
open scoped ComplexOrder

/-- The three defining conditions of a stochastic Lagrangian subspace at `t = 3`. -/
def IsStochasticLagrangian (d : ℕ)
    (T : Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) : Prop :=
  (∀ p ∈ T, ∑ k, p.1 k * p.1 k - ∑ k, p.2 k * p.2 k = 0) ∧
    Module.finrank (ZMod d) T = 3 ∧ (fun _ => 1, fun _ => 1) ∈ T

/-- The computational-basis matrix of `r(T)^{⊗n}`, regrouped into three copies. -/
noncomputable def R (d n : ℕ)
    (T : Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) :
    Matrix (Fin 3 → Fin n → ZMod d) (Fin 3 → Fin n → ZMod d) ℂ := by
  classical
  exact fun X Y => ∏ j, if ((fun k => X k j), (fun k => Y k j)) ∈ T then 1 else 0

/-- The matrix of the third tensor power of the pure-state density operator. -/
def stateCube {d n : ℕ} (Psi : (Fin n → ZMod d) → ℂ) :
    Matrix (Fin 3 → Fin n → ZMod d) (Fin 3 → Fin n → ZMod d) ℂ :=
  fun X Y => ∏ k, Psi (X k) * star (Psi (Y k))

/-- The trace expectation from Eq. (43), with the source bra-ket convention. -/
noncomputable def kappa (d n : ℕ) [NeZero d] (Psi : (Fin n → ZMod d) → ℂ)
    (T : Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) : ℂ :=
  (R d n T * stateCube Psi).trace

/-- The pointwise clause of Conjecture 2, with its full universal quantifiers. -/
def claim : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d ≠ 2 →
    ∀ (n : ℕ) (Psi : (Fin n → ZMod d) → ℂ), ∑ x, ‖Psi x‖ ^ 2 = 1 →
      ∀ T, IsStochasticLagrangian d T → 0 ≤ kappa d n Psi T ∧ kappa d n Psi T ≤ 1

private def O : Matrix (Fin 3) (Fin 3) (ZMod 11) := !![7,8,8;8,7,8;8,8,7]

private def graphMap : (Fin 3 → ZMod 11) →ₗ[ZMod 11]
    ((Fin 3 → ZMod 11) × (Fin 3 → ZMod 11)) :=
  (Matrix.mulVecLin O).prod LinearMap.id

private def T : Submodule (ZMod 11) ((Fin 3 → ZMod 11) × (Fin 3 → ZMod 11)) :=
  LinearMap.range graphMap

private theorem mem_T (x y : Fin 3 → ZMod 11) : (x, y) ∈ T ↔ x = O *ᵥ y := by
  change (∃ z, (O *ᵥ z, z) = (x, y)) ↔ _
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨z, hx, rfl⟩
    exact hx.symm
  · intro hx
    exact ⟨y, hx.symm, rfl⟩

private theorem stochastic_T : IsStochasticLagrangian 11 T := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hO : Oᵀ * O = 1 := by decide
  have hOne : O *ᵥ (fun _ => 1) = (fun _ => 1) := by decide
  refine ⟨?_, ?_, (mem_T _ _).2 hOne.symm⟩
  · rintro ⟨x, y⟩ hp
    rw [(mem_T x y).1 hp]
    change (O *ᵥ y) ⬝ᵥ (O *ᵥ y) - y ⬝ᵥ y = 0
    rw [← dotProduct_transpose_mulVec O y (O *ᵥ y), mulVec_mulVec, hO, one_mulVec,
      sub_self]
  · have hi : Function.Injective graphMap := fun x y h => congrArg Prod.snd h
    rw [T, LinearMap.finrank_range_of_inj hi]
    simp

private def v (a : ZMod 11) : GaussianInt :=
  ![⟨-2,0⟩, ⟨0,0⟩, ⟨0,-2⟩, ⟨1,-2⟩, ⟨-1,-1⟩, ⟨1,2⟩,
    ⟨-1,-2⟩, ⟨-2,0⟩, ⟨0,-2⟩, ⟨2,-1⟩, ⟨1,-1⟩] ⟨a.val, ZMod.val_lt a⟩

private noncomputable def psi (x : Fin 1 → ZMod 11) : ℂ :=
  GaussianInt.toComplex (v (x 0)) / (Real.sqrt 40 : ℂ)

private theorem norm_v : ∑ a : ZMod 11, (v a).norm = 40 := by decide

private theorem normalized_psi : ∑ x, ‖psi x‖ ^ 2 = 1 := by
  classical
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (ZMod 11)).symm]
  simp only [psi, Equiv.funUnique, Equiv.piUnique, Equiv.coe_fn_symm_mk, uniqueElim_const]
  simp_rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 40), Complex.sq_norm,
    ← GaussianInt.intCast_real_norm]
  rw [← Finset.sum_div, ← Int.cast_sum, norm_v]
  norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem gaussian_sum :
    (∑ y : Fin 3 → ZMod 11, ∏ k, v (y k) * star (v ((O *ᵥ y) k))) =
      (-1196 : GaussianInt) := by decide

private theorem kappa_T (Psi : (Fin 1 → ZMod 11) → ℂ) :
    kappa 11 1 Psi T = ∑ y : Fin 3 → ZMod 11,
      ∏ k, Psi (fun _ => y k) * star (Psi (fun _ => (O *ᵥ y) k)) := by
  classical
  let e := Equiv.piCongrRight (fun _ : Fin 3 => Equiv.funUnique (Fin 1) (ZMod 11))
  simp only [kappa, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm, ← Equiv.sum_comp e.symm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Equiv.sum_comp e.symm]
  simp only [e, R, stateCube, Fin.prod_univ_one, Equiv.piCongrRight, Equiv.funUnique,
    Equiv.piUnique, Equiv.coe_fn_symm_mk, uniqueElim_const, mem_T]
  change (∑ x, (if x = O *ᵥ y then 1 else 0) *
    ∏ k, Psi (fun _ => y k) * star (Psi (fun _ => x k))) = _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem kappa_psi : kappa 11 1 psi T = -1196 / 64000 := by
  rw [kappa_T]
  simp only [psi, star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm]
  simp_rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 40)]
  simp_rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_div]
  simp only [← GaussianInt.toComplex_star, ← GaussianInt.toComplex_mul,
    ← map_prod, ← map_sum, gaussian_sum]
  norm_num [GaussianInt.toComplex_def]

/-- The pointwise clause of Conjecture 2 fails for a normalized one-qudit state at `d = 11`. -/
theorem result : ¬ claim := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro h
  have hnonneg := (h 11 (by decide) 1 psi normalized_psi T stochastic_T).1
  rw [kappa_psi, Complex.le_def] at hnonneg
  norm_num at hnonneg

#print axioms result

end D5.S3.Quantum.Magic.CliffordThirdMomentNegativity
