/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHermiteLiteralJet
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHermiteLiteralJet
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Literal Hermite jets of the transfer power. -/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.DualNumber
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Literal matrix powers and their Hermite first jets

For a split characteristic polynomial with distinct roots, the fixed Hermite
interpolant of `X ^ m` evaluates to the literal power on every dual-number
perturbation of the base matrix.
-/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped Matrix

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHermiteLiteralJet

variable {F ι : Type*} [Field F]

private theorem linear_sq_dvd_iff {a : F} {p : F[X]} :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ p.derivative.eval a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← le_rootMultiplicity_iff hp]
  exact one_lt_rootMultiplicity_iff_isRoot hp

/-- Values and first derivatives on the nodes determine the residue modulo the nodal square. -/
theorem nodal_sq_dvd_sub_iff {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s)
    (p q : F[X]) :
    (Lagrange.nodal s v) ^ 2 ∣ p - q ↔
      ∀ i ∈ s, p.eval (v i) = q.eval (v i) ∧
        p.derivative.eval (v i) = q.derivative.eval (v i) := by
  classical
  rw [Lagrange.nodal_eq, ← Finset.prod_pow]
  let factor (i : ι) : F[X] := (X - C (v i)) ^ 2
  have hfactor (i : ι) : factor i ∣ p - q ↔
      p.eval (v i) = q.eval (v i) ∧ p.derivative.eval (v i) = q.derivative.eval (v i) := by
    simp only [factor, linear_sq_dvd_iff, derivative_sub, eval_sub, sub_eq_zero]
  change (∏ i ∈ s, factor i) ∣ p - q ↔ _
  constructor
  · intro h i hi
    exact (hfactor i).1 ((Finset.dvd_prod_of_mem factor hi).trans h)
  · intro h
    apply Finset.prod_dvd_of_coprime ?_ (fun i hi => (hfactor i).2 (h i hi))
    intro i hi j hj hij
    have hgap : v i - v j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hv hi hj he))
    exact (isCoprime_X_sub_C_of_isUnit_sub hgap.isUnit).pow

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix with entries `T i j + ε * J i j`. -/
def perturbation (T J : Matrix n n F) : Matrix n n (DualNumber F) :=
  fun i j => ⟨T i j, J i j⟩

/-- The characteristic polynomial of the base matrix squares to zero on every lift. -/
theorem aeval_charpoly_sq_perturbation (T J : Matrix n n F) :
    aeval (perturbation T J) (T.charpoly ^ 2) = 0 := by
  let e : Matrix n n (DualNumber F) ≃ₐ[F] DualNumber (Matrix n n F) :=
    Matrix.dualNumberEquiv
  let proj := TrivSqZeroExt.fstHom F (Matrix n n F) (Matrix n n F)
  have hbase : proj (e (perturbation T J)) = T := rfl
  have hzero : (aeval (e (perturbation T J)) T.charpoly).fst = 0 := by
    change proj (aeval (e (perturbation T J)) T.charpoly) = 0
    rw [← aeval_algHom_apply proj, hbase, Matrix.aeval_self_charpoly]
  apply e.injective
  rw [← aeval_algHom_apply e, map_zero, map_pow, pow_two]
  apply TrivSqZeroExt.ext
  · simp [hzero]
  · simp [hzero]

/-- A polynomial matching the scalar jets of `X ^ m` on the characteristic nodes gives
the literal matrix power to first order. Its coefficients lie in the base field. -/
theorem literal_pow_eq_aeval_of_jet (T J : Matrix n n F) {s : Finset ι} {v : ι → F}
    (hv : Set.InjOn v s) (hχ : T.charpoly = Lagrange.nodal s v) (m : ℕ) (p : F[X])
    (hp : ∀ i ∈ s, p.eval (v i) = v i ^ m ∧
      p.derivative.eval (v i) = (m : F) * v i ^ (m - 1)) :
    perturbation T J ^ m = aeval (perturbation T J) p := by
  have hdvd : T.charpoly ^ 2 ∣ X ^ m - p := by
    rw [hχ, nodal_sq_dvd_sub_iff hv]
    intro i hi
    simpa only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C] using
      ⟨(hp i hi).1.symm, (hp i hi).2.symm⟩
  obtain ⟨q, hq⟩ := hdvd
  have hzero : aeval (perturbation T J) (X ^ m - p) = 0 := by
    rw [hq, map_mul, aeval_charpoly_sq_perturbation, zero_mul]
  exact sub_eq_zero.mp (by simpa only [map_sub, aeval_X_pow] using hzero)

end Matrix

section Cardinal
variable [DecidableEq ι]

/-- The value cardinal corrects the slope of the squared Lagrange cardinal at its node. -/
def valueCardinal (s : Finset ι) (v : ι → F) (i : ι) : F[X] :=
  (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) * (X - C (v i))) *
    (Lagrange.basis s v i) ^ 2

/-- The slope cardinal has derivative one at its node and vanishing values at all nodes. -/
def slopeCardinal (s : Finset ι) (v : ι → F) (i : ι) : F[X] :=
  (X - C (v i)) * (Lagrange.basis s v i) ^ 2

/-- The self-node Lagrange derivative is the sum of inverse gaps. -/
theorem lagrange_derivative_at_node {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s)
    {i : ι} (hi : i ∈ s) :
    (Lagrange.basis s v i).derivative.eval (v i) = ∑ j ∈ s.erase i, (v i - v j)⁻¹ := by
  rw [Lagrange.basis, derivative_prod_finset, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_mul, eval_prod, Finset.prod_eq_one ?_, one_mul]
  · simp [Lagrange.basisDivisor, derivative_mul]
  · intro k hk
    have hk' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)
    exact Lagrange.eval_basisDivisor_left_of_ne (fun he => hk'.1 (hv hi hk'.2 he).symm)

/-- The two cardinal families independently select values and first derivatives. -/
theorem cardinal_jets {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (valueCardinal s v i).eval (v j) = (if i = j then 1 else 0) ∧
      (valueCardinal s v i).derivative.eval (v j) = 0 ∧
      (slopeCardinal s v i).eval (v j) = 0 ∧
      (slopeCardinal s v i).derivative.eval (v j) = (if i = j then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    have hb := Lagrange.eval_basis_self hv hi
    simp [valueCardinal, slopeCardinal, pow_two, derivative_mul, derivative_sub, hb, two_mul]
  · have hb := Lagrange.eval_basis_of_ne (v := v) hij hj
    simp [valueCardinal, slopeCardinal, pow_two, derivative_mul, hb, hij]

/-- The fixed polynomial with the prescribed values and first derivatives. -/
def hermite (s : Finset ι) (v values slopes : ι → F) : F[X] :=
  ∑ i ∈ s, (C (values i) * valueCardinal s v i + C (slopes i) * slopeCardinal s v i)

/-- The interpolant uses only the nodes, values and slopes indexed by its finite set. -/
theorem hermite_congr {s : Finset ι} {v v' values values' slopes slopes' : ι → F}
    (hnodes : Set.EqOn v v' s) (hvalues : Set.EqOn values values' s)
    (hslopes : Set.EqOn slopes slopes' s) :
    hermite s v values slopes = hermite s v' values' slopes' := by
  apply Finset.sum_congr rfl
  intro i hi
  have hb : Lagrange.basis s v i = Lagrange.basis s v' i := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hnodes hi, hnodes (Finset.mem_of_mem_erase hj)]
  unfold valueCardinal slopeCardinal
  rw [hvalues hi, hslopes hi, hb, hnodes hi]

theorem hermite_jets {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s) (values slopes : ι → F)
    {j : ι} (hj : j ∈ s) :
    (hermite s v values slopes).eval (v j) = values j ∧
      (hermite s v values slopes).derivative.eval (v j) = slopes j := by
  constructor
  · simp only [hermite, eval_finsetSum]
    calc
      _ = ∑ i ∈ s, if i = j then values i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hvalue, _, hslope, _⟩ := cardinal_jets hv hi hj
        split <;> simp_all
      _ = values j := by simp [hj]
  · simp only [hermite, map_sum, eval_finsetSum]
    calc
      _ = ∑ i ∈ s, if i = j then slopes i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨_, hvalue, _, hslope⟩ := cardinal_jets hv hi hj
        split <;> simp_all [derivative_mul]
      _ = slopes j := by simp [hj]

theorem natDegree_hermite_le {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s)
    (values slopes : ι → F) : (hermite s v values slopes).natDegree ≤ 2 * s.card - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hcard := Finset.card_pos.mpr ⟨i, hi⟩
  have hb : ((Lagrange.basis s v i) ^ 2).natDegree ≤ 2 * (s.card - 1) := by
    rw [← Lagrange.natDegree_basis hv hi]
    exact natDegree_pow_le
  have hslope : (slopeCardinal s v i).natDegree ≤ 2 * s.card - 1 := by
    unfold slopeCardinal
    refine natDegree_mul_le.trans ?_
    rw [natDegree_X_sub_C]
    omega
  have hvalue : (valueCardinal s v i).natDegree ≤ 2 * s.card - 1 := by
    unfold valueCardinal
    refine natDegree_mul_le.trans ?_
    have hc : (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) *
        (X - C (v i))).natDegree ≤ 1 := by
      have hmul : (C (2 * (Lagrange.basis s v i).derivative.eval (v i)) *
          (X - C (v i))).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C])
      exact natDegree_sub_le_of_le (m := 1) (by simp) hmul
    omega
  simpa only [max_self] using
    natDegree_add_le_of_le ((natDegree_C_mul_le (values i) _).trans hvalue)
      ((natDegree_C_mul_le (slopes i) _).trans hslope)

/-- The explicit interpolant of a polynomial is its monic remainder modulo the nodal square. -/
theorem hermite_eq_modByMonic {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s) (p : F[X]) :
    hermite s v (fun i => p.eval (v i)) (fun i => p.derivative.eval (v i)) =
      p %ₘ ((Lagrange.nodal s v) ^ 2) := by
  let H := hermite s v (fun i => p.eval (v i)) (fun i => p.derivative.eval (v i))
  let χ := (Lagrange.nodal s v) ^ 2
  have hχ : χ.Monic := (Lagrange.nodal_monic (s := s) (v := v)).pow 2
  have hd : χ ∣ p - H := (nodal_sq_dvd_sub_iff hv p H).2 (fun i hi => by
    obtain ⟨ha, hb⟩ := hermite_jets hv (fun j => p.eval (v j))
      (fun j => p.derivative.eval (v j)) hi
    exact ⟨ha.symm, hb.symm⟩)
  have hdeg : H.degree < χ.degree := by
    have hχdeg : χ.degree = (↑(2 * s.card) : WithBot ℕ) := by
      rw [degree_eq_natDegree hχ.ne_zero, natDegree_pow, Lagrange.natDegree_nodal]
    rw [hχdeg]
    by_cases hs : s.Nonempty
    · have hlt : H.natDegree < 2 * s.card :=
        lt_of_le_of_lt (natDegree_hermite_le hv _ _) (by have := hs.card_pos; omega)
      exact (degree_le_natDegree).trans_lt (WithBot.coe_lt_coe.mpr hlt)
    · simp [H, hermite, Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨q, hq⟩ := hd
  exact ((div_modByMonic_unique q H hχ ⟨by rw [← hq, add_sub_cancel], hdeg⟩).2).symm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal power equals evaluation of the fixed Hermite interpolant on the perturbed
matrix. Equality in dual numbers identifies both the value and the directional derivative. -/
theorem literal_pow_eq_aeval_hermite (T J : Matrix n n F) {s : Finset ι} {v : ι → F}
    (hv : Set.InjOn v s) (hχ : T.charpoly = Lagrange.nodal s v) (m : ℕ) :
    perturbation T J ^ m = aeval (perturbation T J)
      (hermite s v (fun i => v i ^ m) (fun i => (m : F) * v i ^ (m - 1))) :=
  literal_pow_eq_aeval_of_jet T J hv hχ m _ (fun _ hi => hermite_jets hv _ _ hi)

end Cardinal

/-- The degree-seven specialization for the four spectral weights in the horizontal MPS
cofactors. Both components of the matrix jet use the same fixed polynomial. -/
theorem four_weight_literal_hermite_jet (T J : Matrix (Fin 4) (Fin 4) F)
    (v : Fin 4 → F) (hv : Function.Injective v)
    (hχ : T.charpoly = ∏ i : Fin 4, (X - C (v i))) (m : ℕ) :
    let H := hermite Finset.univ v (fun i => v i ^ m) (fun i => (m : F) * v i ^ (m - 1))
    H.natDegree ≤ 7 ∧ perturbation T J ^ m = aeval (perturbation T J) H := by
  have hnodes : Set.InjOn v (Finset.univ : Finset (Fin 4)) := hv.injOn
  refine ⟨?_, literal_pow_eq_aeval_hermite T J hnodes ?_ m⟩
  · simpa using natDegree_hermite_le hnodes (fun i => v i ^ m)
      (fun i => (m : F) * v i ^ (m - 1))
  · rwa [Lagrange.nodal_eq]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHermiteLiteralJet
