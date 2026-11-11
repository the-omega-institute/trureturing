/- GID: D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Periodizer actions on the original configuration and directional recurrence. -/

import D5.S1.Dynamics.Symbolic.KhetanAnnihilator
import D5.S1.Dynamics.Symbolic.KhetanFiniteRecurrence
import D5.S1.Dynamics.Symbolic.KhetanLaurentElimination
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.LinearCombination

/-!
The action is the positive-shift action: the exact-cover mask for `F` has
exponents `-f`. A periodizer acts as a constant configuration. Multiplying
it by a nonzero lattice difference supplies a nonzero annihilator of the
original configuration, to which the integer product-difference supplier
applies. No separation of the supplier's directions is assumed.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer

open D5.S1.Dynamics.Symbolic.KhetanLaurent
open D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra

variable {R : Type*} [CommRing R]

noncomputable def differenceFilter (u : Lattice) : AddMonoidAlgebra R Lattice :=
  AddMonoidAlgebra.single u 1 - 1

private theorem coefficientAct_sub (f g : AddMonoidAlgebra R Lattice)
    (h : Configuration R) : coefficientAct (f - g) h = coefficientAct f h - coefficientAct g h := by
  simp [coefficientAct]

theorem difference_filter_ne_zero [Nontrivial R] {u : Lattice} (hu : u ≠ 0) :
    (differenceFilter u : AddMonoidAlgebra R Lattice) ≠ 0 := by
  intro hz
  have he : AddMonoidAlgebra.single u (1 : R) = AddMonoidAlgebra.single 0 1 :=
    sub_eq_zero.mp hz
  exact hu (AddMonoidAlgebra.single_left_injective one_ne_zero he)

theorem difference_filter_constant (u : Lattice) (a : R) :
    coefficientAct (differenceFilter u) (fun _ => a) = 0 := by
  rw [differenceFilter, coefficientAct_sub, coefficientAct_single, coefficientAct_one]
  funext x
  simp [shift]

theorem periodizer_annihilator (P : AddMonoidAlgebra R Lattice)
    (h : Configuration R) (a : R) (hP : coefficientAct P h = fun _ => a)
    (u : Lattice) : coefficientAct (differenceFilter u * P) h = 0 := by
  rw [coefficientAct_mul, hP, difference_filter_constant]

theorem integer_periodizer_product_differences
    (h : Configuration ℤ) (hh : FiniteRange h)
    (P : IntegerLaurent) (hPne : P ≠ 0) (a : ℤ)
    (hP : coefficientAct P h = fun _ => a) :
    ∃ directions : List Lattice,
      directions ≠ [] ∧ (∀ u ∈ directions, u ≠ 0) ∧
      (directions.map (fun u => (differenceFilter u : IntegerLaurent))).prod ≠ 0 ∧
      coefficientAct (directions.map (fun u => (differenceFilter u : IntegerLaurent))).prod h = 0 := by
  classical
  let e : Lattice := (1, 0)
  have he : e ≠ 0 := by simp [e]
  have hd : (differenceFilter e : IntegerLaurent) ≠ 0 := difference_filter_ne_zero he
  by_cases hz : h = 0
  · refine ⟨[e], by simp, ?_, ?_, ?_⟩
    · simpa using he
    · simpa using hd
    · simp [hz]
  · obtain ⟨ds, hnil, hnz, hann⟩ := exists_integer_product_differences hh hz
      (mul_ne_zero hd hPne) (periodizer_annihilator P h a hP e)
    refine ⟨ds, hnil, hnz, ?_, hann⟩
    apply List.prod_ne_zero
    intro hf
    obtain ⟨u, hu, hz⟩ := List.mem_map.mp hf
    exact difference_filter_ne_zero (hnz u hu) hz

/-- The negative exponents implement exact-cover convolution using positive shifts. -/
noncomputable def exactCoverMask (F : Finset Lattice) : IntegerLaurent :=
  ∑ f ∈ F, AddMonoidAlgebra.single (-f) 1

theorem exact_cover_mask_act (F : Finset Lattice) (h : Configuration ℤ) (x : Lattice) :
    coefficientAct (exactCoverMask F) h x = ∑ f ∈ F, h (x - f) := by
  rw [exactCoverMask, coefficientAct_finset_sum]
  simp [Finset.sum_apply, shift, sub_eq_add_neg]

theorem exact_cover_mask_ne_zero (F : Finset Lattice) (hF : F.Nonempty) :
    exactCoverMask F ≠ 0 := by
  intro hz
  have h := congrFun (congrArg (fun P : IntegerLaurent =>
    coefficientAct P (fun _ => (1 : ℤ))) hz) (0 : Lattice)
  rw [exact_cover_mask_act] at h
  simp at h
  exact hF.ne_empty h

theorem exact_cover_product_differences (F : Finset Lattice) (hF : F.Nonempty)
    (h : Configuration ℤ) (hh : FiniteRange h)
    (hcover : ∀ x, ∑ f ∈ F, h (x - f) = 1) :
    ∃ directions : List Lattice,
      directions ≠ [] ∧ (∀ u ∈ directions, u ≠ 0) ∧
      (directions.map (fun u => (differenceFilter u : IntegerLaurent))).prod ≠ 0 ∧
      coefficientAct (directions.map (fun u => (differenceFilter u : IntegerLaurent))).prod h = 0 := by
  apply integer_periodizer_product_differences h hh (exactCoverMask F)
    (exact_cover_mask_ne_zero F hF) 1
  funext x
  rw [exact_cover_mask_act, hcover]

noncomputable def linePolynomial (u : Lattice) :
    Polynomial R →+* AddMonoidAlgebra R Lattice :=
  Polynomial.eval₂RingHom (algebraMap R _) (AddMonoidAlgebra.single u 1)

theorem line_polynomial_monomial (u : Lattice) (n : ℕ) (a : R) :
    linePolynomial u (Polynomial.monomial n a) = AddMonoidAlgebra.single (n • u) a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  simp [linePolynomial, AddMonoidAlgebra.single_pow]

theorem line_polynomial_act (u : Lattice) (q : Polynomial R) (h : Configuration R)
    (x : Lattice) :
    coefficientAct (linePolynomial u q) h x =
      ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * h (x + (j : ℤ) • u) := by
  conv_lhs => rw [q.as_sum_range]
  rw [map_sum, coefficientAct_finset_sum]
  simp [line_polynomial_monomial, Finset.sum_apply, shift]

/-- A nonzero one-variable annihilator gives an actual global period of the
original finite-range configuration. Neither invertible constant term nor
an already periodic line is a hypothesis. Bilaterality and finite states
also handle order zero and vanishing constant terms. -/
theorem nonzero_line_annihilator_periodic [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (u : Lattice) (hu : u ≠ 0)
    (q : Polynomial R) (hq : q ≠ 0)
    (hann : coefficientAct (linePolynomial u q) h = 0) : Periodic h := by
  have hrec (x : Lattice) :
      ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * h (x + (j : ℤ) • u) = 0 := by
    rw [← line_polynomial_act, hann]
    rfl
  let N := ((Set.range h).ncard ^ (q.natDegree + 1)).factorial
  refine ⟨N • u, smul_ne_zero (Nat.ne_of_gt (Nat.factorial_pos _)) hu, ?_⟩
  exact KhetanFiniteRecurrence.directional_recurrence_uniform_period h hh u
    q.natDegree q.coeff (Polynomial.leadingCoeff_ne_zero.mpr hq) hrec

private def directionHom (u : Lattice) : ℤ →+ Lattice where
  toFun n := n • u
  map_zero' := zero_smul _ _
  map_add' m n := add_zsmul u m n

noncomputable def lineLaurent (u : Lattice) :
    LaurentPolynomial R →+* AddMonoidAlgebra R Lattice :=
  AddMonoidAlgebra.mapDomainRingHom R (directionHom u)

@[simp] theorem line_laurent_single (u : Lattice) (n : ℤ) (a : R) :
    lineLaurent u (AddMonoidAlgebra.single n a) = AddMonoidAlgebra.single (n • u) a := by
  change AddMonoidAlgebra.mapDomain (directionHom u)
    (AddMonoidAlgebra.single n a) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

theorem line_laurent_polynomial (u : Lattice) (q : Polynomial R) :
    lineLaurent u q.toLaurent = linePolynomial u q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [line_polynomial_monomial, Polynomial.toLaurent_C_mul_T,
      ← LaurentPolynomial.single_eq_C_mul_T]
    simpa only [natCast_zsmul] using line_laurent_single u (n : ℤ) a

theorem nonzero_line_laurent_annihilator_periodic [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (u : Lattice) (hu : u ≠ 0)
    (F : LaurentPolynomial R) (hF : F ≠ 0)
    (hann : coefficientAct (lineLaurent u F) h = 0) : Periodic h := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow F
  have hqn : q ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hq
    exact mul_ne_zero hF (LaurentPolynomial.isUnit_T (n : ℤ)).ne_zero hq.symm
  apply nonzero_line_annihilator_periodic h hh u hu q hqn
  rw [← line_laurent_polynomial, hq, map_mul, mul_comm, coefficientAct_mul,
    hann, coefficientAct_config_zero]

/-- This is the configuration-action step after a Bezout identity has already
been cleared inside the Laurent ring. Rational functions never act on `h`. -/
theorem cleared_bezout_action (h : Configuration R) (u : Lattice)
    (P A B ρ α β : AddMonoidAlgebra R Lattice) (c : R)
    (hP : coefficientAct P h = fun _ => c)
    (hAB : coefficientAct (A * B) h = 0)
    (hρ : ρ = α * P + β * B) :
    coefficientAct (differenceFilter u * A * ρ) h = 0 := by
  have hconstant := periodizer_annihilator P h c hP u
  calc
    coefficientAct (differenceFilter u * A * ρ) h =
        coefficientAct (A * α * (differenceFilter u * P) +
          differenceFilter u * β * (A * B)) h := by rw [hρ]; congr 1; ring
    _ = 0 := by
      rw [coefficientAct_add, coefficientAct_mul, hconstant, coefficientAct_config_zero,
        coefficientAct_mul, hAB, coefficientAct_config_zero, add_zero]

/-- The fully cleared identity suffices for the terminal period step. The
nonzero coefficient produced by clearing, and the parallel factor product,
are multiplied in the one-variable domain before the recurrence theorem is
applied to the original `h`. -/
theorem cleared_bezout_periodic [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (u : Lattice) (hu : u ≠ 0)
    (P B α β : AddMonoidAlgebra R Lattice) (A ρ : LaurentPolynomial R)
    (hA : A ≠ 0) (hρ : ρ ≠ 0) (c : R)
    (hP : coefficientAct P h = fun _ => c)
    (hAB : coefficientAct (lineLaurent u A * B) h = 0)
    (hbezout : lineLaurent u ρ = α * P + β * B) : Periodic h := by
  let Q : LaurentPolynomial R := (LaurentPolynomial.T 1 - 1) * A * ρ
  have hdiff : (LaurentPolynomial.T 1 - 1 : LaurentPolynomial R) ≠ 0 := by
    intro hz
    have he : AddMonoidAlgebra.single (1 : ℤ) (1 : R) =
        AddMonoidAlgebra.single 0 1 := sub_eq_zero.mp hz
    have hi := AddMonoidAlgebra.single_left_injective one_ne_zero he
    norm_num at hi
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hdiff hA) hρ
  apply nonzero_line_laurent_annihilator_periodic h hh u hu Q hQ
  have he : lineLaurent u Q = differenceFilter u * lineLaurent u A * lineLaurent u ρ := by
    change lineLaurent u ((AddMonoidAlgebra.single (1 : ℤ) 1 - 1) * A * ρ) = _
    rw [map_mul, map_mul, map_sub, line_laurent_single, map_one, one_zsmul]
    rfl
  rw [he]
  exact cleared_bezout_action h u P (lineLaurent u A) B (lineLaurent u ρ) α β c
    hP hAB hbezout

private theorem parallel_multiple (u v : Lattice) (a b : ℤ)
    (hab : a * u.1 + b * u.2 = 1) (hpar : u.1 * v.2 - u.2 * v.1 = 0) :
    v = (a * v.1 + b * v.2) • u := by
  apply Prod.ext
  · change v.1 = (a * v.1 + b * v.2) * u.1
    linear_combination -v.1 * hab - b * hpar
  · change v.2 = (a * v.1 + b * v.2) * u.2
    linear_combination -v.2 * hab + a * hpar

/-- Group all parallel factors, retaining every transverse factor in a list.
The primitive-coordinate Bezout identity supplies their integer exponents;
there is no pairwise nonparallel premise or conclusion. -/
theorem split_difference_directions [IsDomain R]
    (u : Lattice) (hu : IsCoprime u.1 u.2)
    (directions : List Lattice) (hnz : ∀ v ∈ directions, v ≠ 0) :
    ∃ A : LaurentPolynomial R, ∃ transverse : List Lattice,
      A ≠ 0 ∧ (∀ v ∈ transverse, u.1 * v.2 - u.2 * v.1 ≠ 0) ∧
      lineLaurent u A * (transverse.map (fun v =>
        (differenceFilter v : AddMonoidAlgebra R Lattice))).prod =
        (directions.map (fun v => (differenceFilter v : AddMonoidAlgebra R Lattice))).prod := by
  classical
  obtain ⟨a, b, hab⟩ := hu
  let par : Lattice → Prop := fun v => u.1 * v.2 - u.2 * v.1 = 0
  let exponent : Lattice → ℤ := fun v => a * v.1 + b * v.2
  let factors : Lattice → LaurentPolynomial R := fun v => LaurentPolynomial.T (exponent v) - 1
  let A := ((directions.filter par).map factors).prod
  let transverse := directions.filter fun v => ¬ par v
  have hrep (v : Lattice) (hv : v ∈ directions.filter par) : v = exponent v • u :=
    parallel_multiple u v a b hab (of_decide_eq_true (List.mem_filter.mp hv).2)
  refine ⟨A, transverse, ?_, ?_, ?_⟩
  · apply List.prod_ne_zero
    intro hf
    obtain ⟨v, hv, hvzero⟩ := List.mem_map.mp hf
    have he : exponent v ≠ 0 := by
      intro hz
      have hv0 := hrep v hv
      rw [hz, zero_smul] at hv0
      exact hnz v (List.mem_filter.mp hv).1 hv0
    have hsingle : AddMonoidAlgebra.single (exponent v) (1 : R) =
        AddMonoidAlgebra.single 0 1 := sub_eq_zero.mp hvzero
    exact he (AddMonoidAlgebra.single_left_injective one_ne_zero hsingle)
  · intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  · have hA : lineLaurent u A = ((directions.filter par).map
        (fun v => (differenceFilter v : AddMonoidAlgebra R Lattice))).prod := by
      rw [map_list_prod, List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro v hv
      change lineLaurent u (AddMonoidAlgebra.single (exponent v) 1 - 1) = _
      rw [map_sub, line_laurent_single, map_one, ← hrep v hv]
      rfl
    rw [hA]
    exact List.prod_map_filter_mul_prod_map_filter_not par
      (fun v => (differenceFilter v : AddMonoidAlgebra R Lattice)) directions

theorem integer_periodizer_direction_split
    (h : Configuration ℤ) (hh : FiniteRange h)
    (P : IntegerLaurent) (hPne : P ≠ 0) (c : ℤ)
    (hP : coefficientAct P h = fun _ => c)
    (u : Lattice) (hu : IsCoprime u.1 u.2) :
    ∃ A : LaurentPolynomial ℤ, ∃ transverse : List Lattice,
      A ≠ 0 ∧ (∀ v ∈ transverse, u.1 * v.2 - u.2 * v.1 ≠ 0) ∧
      (transverse.map (fun v => (differenceFilter v : IntegerLaurent))).prod ≠ 0 ∧
      coefficientAct (lineLaurent u A *
        (transverse.map (fun v => (differenceFilter v : IntegerLaurent))).prod) h = 0 := by
  obtain ⟨ds, _, hnz, hprod, hann⟩ := integer_periodizer_product_differences h hh P hPne c hP
  obtain ⟨A, transverse, hA, ht, heq⟩ := split_difference_directions (R := ℤ) u hu ds hnz
  refine ⟨A, transverse, hA, ht, ?_, ?_⟩
  · intro hz
    rw [hz, mul_zero] at heq
    exact hprod heq.symm
  · rwa [heq]

end D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
