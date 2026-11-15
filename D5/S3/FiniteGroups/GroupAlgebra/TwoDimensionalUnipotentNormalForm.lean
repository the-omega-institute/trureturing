/- GID: D5/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.CharP.Algebra, mathlib/module/Mathlib.Algebra.CharP.Lemmas, mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Zero, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas, mathlib/module/Mathlib.RepresentationTheory.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A faithful two-dimensional elementary-abelian action over an arbitrary field has an actual unipotent basis and injective additive parameter. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic

/-!
# A faithful two-dimensional elementary-abelian action has a unipotent basis

This is the classical normal form used in the introduction of Elmer--Kadr,
arXiv:2510.07939v1, https://arxiv.org/abs/2510.07939v1,
DOI https://doi.org/10.1007/s13366-026-00855-9. No novelty or resolution of
the paper's conjectures is claimed here.

The basis is constructed from a nonzero nilpotent displacement: if
N = rho(e) - 1, choose v with N v nonzero and use (N v, v).
Commutation with N gives equal diagonal coefficients for every group element.
Cayley--Hamilton in dimension two makes each displacement square zero;
this forces those diagonal coefficients to be one, including in characteristic
two. Coordinates then produce an actual injective additive map E -> K.

The field and the acting group need not be finite. Their universes, and that
of the vector space, are independent. Faithfulness and nontriviality are used
to construct N, not supplied as a triangularizing-basis hypothesis.

This supplies only the classical two-dimensional source reduction. It does
not construct a symmetric-power identification, a contragredient equivalence,
or transport of relative projectivity; those are separate downstream gaps.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.TwoDimensionalUnipotentNormalForm

open Module
open Multiplicative (ofAdd)

universe uK uE uV

variable {K : Type uK} [Field K]
  {E : Type uE} [AddCommGroup E]
  {V : Type uV} [AddCommGroup V] [Module K V]

-- Consumed by the normal-form construction for the chosen element and for
-- every other element. No finiteness assumption on E or K is used.
private theorem displacement_sq_zero
    {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional K V]
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K V = 2)
    (rho : Representation K (Multiplicative E) V) (e : E) :
    (rho (ofAdd e) - 1) ^ 2 = 0 := by
  let : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [hdim]; decide)
  let : CharP (Module.End K V) p :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K V)).injective p
  have hpow : rho (ofAdd e) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hE e, ofAdd_zero, map_one]
  have hnil : IsNilpotent (rho (ofAdd e) - 1) := by
    refine ⟨p, ?_⟩
    rw [sub_pow_char_of_commute p (Commute.one_right _), hpow,
      one_pow, sub_self]
  have hchar := hnil.charpoly_eq_X_pow_finrank
  have hCH := (rho (ofAdd e) - 1).aeval_self_charpoly
  simpa only [hchar, map_pow, Polynomial.aeval_X, hdim] using hCH

-- The basis here is supplied by the subsequent construction from (N v, v).
-- This private helper does not add a basis premise to the public theorem.
private theorem unitriangular_of_commutes
    (N T : Module.End K V) (b : Basis (Fin 2) K V)
    (hN0 : N (b 0) = 0) (hN1 : N (b 1) = b 0)
    (hcomm : N * T = T * N) (hT : (T - 1) ^ 2 = 0) :
    T (b 0) = b 0 ∧
      T (b 1) = b.repr (T (b 1)) 0 • b 0 + b 1 := by
  let c : K := b.repr (T (b 1)) 1
  have hT1 : T (b 1) =
      b.repr (T (b 1)) 0 • b 0 + b.repr (T (b 1)) 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr (T (b 1))).symm
  have hdiag : T (b 0) = c • b 0 := by
    calc
      T (b 0) = T (N (b 1)) := by rw [hN1]
      _ = N (T (b 1)) := (LinearMap.congr_fun hcomm (b 1)).symm
      _ = N (b.repr (T (b 1)) 0 • b 0 + c • b 1) := congrArg N hT1
      _ = c • b 0 := by
        simp only [map_add, map_smul, hN0, hN1, smul_zero, zero_add]
  have hM0 : (T - 1) (b 0) = (c - 1) • b 0 := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hdiag,
      sub_smul, one_smul]
  have hscalar_smul : (c - 1) ^ 2 • b 0 = 0 := by
    have h := LinearMap.congr_fun hT (b 0)
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply,
      hM0, map_smul, smul_smul] using h
  have hscalar : (c - 1) ^ 2 = 0 :=
    (smul_eq_zero.mp hscalar_smul).resolve_right (b.ne_zero 0)
  have hc : c = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hscalar)
  constructor
  · simpa only [hc, one_smul] using hdiag
  · change T (b 1) = b.repr (T (b 1)) 0 • b 0 + c • b 1 at hT1
    simpa only [hc, one_smul] using hT1

/-- Classical two-dimensional normal form for a faithful representation of a
nontrivial abelian group of exponent p over any field of characteristic p.

The conclusion contains an actual basis and an actual injective additive map.
It assumes neither a fixed vector nor a complement, a triangularizing basis,
an embedding into K, algebraic closure, or a restriction excluding p = 2.
No indecomposability hypothesis is needed for this reduction.
-/
theorem exists_faithful_unipotent_basis
    {p : ℕ} [Fact p.Prime] [CharP K p] [Nontrivial E]
    [FiniteDimensional K V]
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K V = 2)
    (rho : Representation K (Multiplicative E) V)
    (hrho : Function.Injective rho) :
    ∃ b : Basis (Fin 2) K V, ∃ alpha : E →+ K,
      Function.Injective alpha ∧
      (∀ e : E, rho (ofAdd e) (b 0) = b 0) ∧
      (∀ e : E, rho (ofAdd e) (b 1) = alpha e • b 0 + b 1) := by
  classical
  obtain ⟨e0, he0⟩ := exists_ne (0 : E)
  let N : Module.End K V := rho (ofAdd e0) - 1
  have hNne : N ≠ 0 := by
    intro hN
    apply he0
    apply Multiplicative.ofAdd.injective
    apply hrho
    have h : rho (ofAdd e0) = 1 := sub_eq_zero.mp hN
    simpa only [ofAdd_zero, map_one] using h
  have hNsq : N ^ 2 = 0 := displacement_sq_zero hE hdim rho e0
  obtain ⟨v, hv⟩ : ∃ v : V, N v ≠ 0 := by
    by_contra! h
    apply hNne
    ext v
    exact h v
  let u : V := N v
  have hu : u ≠ 0 := hv
  have hNu : N u = 0 := by
    simpa only [u, pow_two, Module.End.mul_apply, LinearMap.zero_apply]
      using LinearMap.congr_fun hNsq v
  have hli : LinearIndependent K ![u, v] := by
    apply (LinearIndependent.pair_iff' hu).2
    intro c hcv
    have h : (0 : V) = u := by
      simpa only [map_smul, hNu, smul_zero] using congrArg N hcv
    exact hu h.symm
  let b : Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = u := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero]
  have hb1 : b 1 = v := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  have hN0 : N (b 0) = 0 := by rw [hb0, hNu]
  have hN1 : N (b 1) = b 0 := by rw [hb1, hb0]
  have hcomm (e : E) : N * rho (ofAdd e) = rho (ofAdd e) * N := by
    have h : rho (ofAdd e0) * rho (ofAdd e) =
        rho (ofAdd e) * rho (ofAdd e0) := by
      calc
        _ = rho (ofAdd e0 * ofAdd e) := (rho.map_mul _ _).symm
        _ = rho (ofAdd e * ofAdd e0) := congrArg rho (mul_comm _ _)
        _ = _ := rho.map_mul _ _
    simpa only [N, sub_mul, mul_sub, one_mul, mul_one] using
      congrArg (fun A : Module.End K V => A - rho (ofAdd e)) h
  let a : E → K := fun e => b.repr (rho (ofAdd e) (b 1)) 0
  have hform (e : E) : rho (ofAdd e) (b 0) = b 0 ∧
      rho (ofAdd e) (b 1) = a e • b 0 + b 1 :=
    unitriangular_of_commutes N (rho (ofAdd e)) b hN0 hN1 (hcomm e)
      (displacement_sq_zero hE hdim rho e)
  let alpha : E →+ K :=
    { toFun := a
      map_zero' := by
        dsimp only [a]
        simp
      map_add' := by
        intro e f
        have hadd : rho (ofAdd (e + f)) (b 1) =
            (a e + a f) • b 0 + b 1 := by
          rw [ofAdd_add, map_mul, Module.End.mul_apply,
            (hform f).2, map_add, map_smul, (hform e).1, (hform e).2]
          simp only [add_smul]
          abel
        have hcoord := congrArg (fun w : V => b.repr w 0) hadd
        simpa [a] using hcoord }
  refine ⟨b, alpha, ?_, ?_, ?_⟩
  · intro e f hef
    change a e = a f at hef
    apply Multiplicative.ofAdd.injective
    apply hrho
    apply b.ext
    intro i
    fin_cases i
    · exact (hform e).1.trans (hform f).1.symm
    · change rho (ofAdd e) (b 1) = rho (ofAdd f) (b 1)
      rw [(hform e).2, (hform f).2, hef]
  · intro e
    exact (hform e).1
  · intro e
    exact (hform e).2

end D5.S3.FiniteGroups.GroupAlgebra.TwoDimensionalUnipotentNormalForm
