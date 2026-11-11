/- GID: D5/S1/Dynamics/Symbolic/KhetanAnnihilator
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Integer finite-range annihilators supply products of lattice differences. -/

import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Int.Basic

/-
Adapted from boonsuan/nivat, revision 4e3614024227acd273c3e8ab41df92c2709e5ab0:
Nivat/Core/Basic.lean, Nivat/Algebra/Action.lean,
Nivat/Algebra/RationalScaling.lean, Nivat/Algebra/ProductDifferences.lean.
The action uses positive shifts. Difference directions are nonzero;
no pairwise nonparallel conclusion is asserted.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Configurations and translation operators

The configuration, period and operator notation of Section 1.1 of
`paper/nivat.tex`. All configurations have the full integer lattice as their domain.

`IsPeriod c h` permits the zero vector; `Periodic c` requires one nonzero period.
The forward-shift convention is shared by the Laurent action and pattern pairing.
-/

namespace D5.S1.Dynamics.Symbolic.KhetanLaurent

/-- The integer lattice `ℤ²` on which configurations are defined (Section 1). -/
abbrev Lattice := ℤ × ℤ

/-- A configuration with alphabet `A`, as in Section 1. -/
abbrev Configuration (A : Type*) := Lattice → A

/-- The forward translation `Tʰc`, with `(Tʰc)(z) = c(z + h)` (Section 1.1). -/
def shift {A : Type*} (h : Lattice) (c : Configuration A) : Configuration A :=
  fun z => c (z + h)

/-- A configuration takes values in a finite set (Section 1.1). -/
def FiniteRange {A : Type*} (c : Configuration A) : Prop := (Set.range c).Finite

/-- A vector fixes the configuration at every lattice site (Section 1).
This predicate allows zero; `Periodic` requires a nonzero witness. -/
def IsPeriod {A : Type*} (c : Configuration A) (h : Lattice) : Prop :=
  ∀ z, c (z + h) = c z

/-- Existence of one nonzero global period, the conclusion of Theorem 1.1 (`thm:main`). -/
def Periodic {A : Type*} (c : Configuration A) : Prop :=
  ∃ h : Lattice, h ≠ 0 ∧ IsPeriod c h

/-- The difference operator `Δₕ = Tʰ - I` from Section 1.1. -/
def difference {A : Type*} [AddCommGroup A] (h : Lattice)
    (c : Configuration A) : Configuration A := shift h c - c

/-- Evaluation of the forward shift from Section 1.1. -/
@[simp] theorem shift_apply {A : Type*} (h : Lattice) (c : Configuration A) (z) :
    shift h c z = c (z + h) := rfl

/-- The zero translation acts as the identity (Section 1.1). -/
@[simp] theorem shift_zero {A : Type*} (c : Configuration A) : shift 0 c = c := by
  funext z
  simp [shift]

/-- Composition of the shift operators from Section 1.1. -/
theorem shift_add {A : Type*} (h t : Lattice) (c : Configuration A) :
    shift (h + t) c = shift h (shift t c) := by
  funext z
  simp [shift, add_assoc]

/-- Shift operators commute, as used throughout Section 1.1. -/
theorem shift_comm {A : Type*} (h t : Lattice) (c : Configuration A) :
    shift h (shift t c) = shift t (shift h c) := by
  rw [← shift_add, ← shift_add, add_comm h t]

/-- The pointwise period condition is equivalent to `Tʰc = c` (Section 1.1). -/
theorem isPeriod_iff_shift_eq {A : Type*} (c : Configuration A) (h : Lattice) :
    IsPeriod c h ↔ shift h c = c := by
  exact ⟨fun hc => funext hc, fun hc => congrFun hc⟩

/-- The zero vector fixes every configuration (Section 1.1). -/
theorem IsPeriod.zero {A : Type*} (c : Configuration A) : IsPeriod c 0 := by
  intro z
  simp

/-- The sum of two periods is a period (Section 1.1). -/
theorem IsPeriod.add {A : Type*} {c : Configuration A} {h t : Lattice}
    (hh : IsPeriod c h) (ht : IsPeriod c t) : IsPeriod c (h + t) := by
  intro z
  rw [← add_assoc, ht, hh]

/-- Reversing a period preserves periodicity (Section 1.1). -/
theorem IsPeriod.neg {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) : IsPeriod c (-h) := by
  intro z
  simpa using (hh (z + -h)).symm

/-- Every natural multiple of a period is a period (Section 1.1). -/
theorem IsPeriod.nsmul {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) (n : ℕ) : IsPeriod c (n • h) := by
  induction n with
  | zero => simpa using IsPeriod.zero c
  | succ n ih =>
    rw [add_nsmul, one_nsmul]
    exact ih.add hh

/-- Every integer multiple of a period is a period (Section 1.1). -/
theorem IsPeriod.zsmul {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) (n : ℤ) : IsPeriod c (n • h) := by
  cases n with
  | ofNat n =>
    change IsPeriod c ((n : ℤ) • h)
    rw [natCast_zsmul]
    exact hh.nsmul n
  | negSucc n =>
    change IsPeriod c (-((n + 1 : ℕ) : ℤ) • h)
    rw [neg_zsmul, natCast_zsmul]
    exact (hh.nsmul (n + 1)).neg

/-- A configuration and any translate have the same periods (Section 1.1). -/
theorem isPeriod_shift_iff {A : Type*} (c : Configuration A) (h t : Lattice) :
    IsPeriod (shift t c) h ↔ IsPeriod c h := by
  constructor
  · intro hp z
    simpa [shift, add_assoc, add_left_comm, add_comm] using hp (z - t)
  · intro hp z
    simpa [shift, add_assoc, add_left_comm, add_comm] using hp (z + t)

/-- Periodicity is invariant under translation (Section 1.1). -/
theorem periodic_shift_iff {A : Type*} (c : Configuration A) (t : Lattice) :
    Periodic (shift t c) ↔ Periodic c := by
  simp only [Periodic, isPeriod_shift_iff]

/-- Applying a function to a finite alphabet preserves finite range (Section 1.1). -/
theorem FiniteRange.map {A B : Type*} {c : Configuration A}
    (hc : FiniteRange c) (f : A → B) : FiniteRange (f ∘ c) := by
  simpa only [FiniteRange, Set.range_comp] using hc.image f

/-- Translations preserve finite range (Section 1.1). -/
theorem FiniteRange.shift {A : Type*} {c : Configuration A}
    (hc : FiniteRange c) (h : Lattice) : FiniteRange (shift h c) := by
  apply hc.subset
  rintro _ ⟨z, rfl⟩
  exact ⟨z + h, rfl⟩

/-- A configuration over a finite alphabet has finite range (Section 1.1). -/
theorem finiteRange_of_finite {A : Type*} [Finite A] (c : Configuration A) :
    FiniteRange c := Set.toFinite _

/-- Injective alphabet labels preserve each period vector (Section 1.1). -/
theorem isPeriod_map_iff {A B : Type*} (c : Configuration A) {f : A → B}
    (hf : Function.Injective f) (h : Lattice) :
    IsPeriod (f ∘ c) h ↔ IsPeriod c h := by
  simp only [IsPeriod, Function.comp_apply, hf.eq_iff]

/-- Injective alphabet labels preserve periodicity (Section 1.1). -/
theorem periodic_map_iff {A B : Type*} (c : Configuration A) {f : A → B}
    (hf : Function.Injective f) : Periodic (f ∘ c) ↔ Periodic c := by
  simp only [Periodic, isPeriod_map_iff c hf]

/-- The pointwise formula for `Δₕc` in Section 1.1. -/
@[simp] theorem difference_apply {A : Type*} [AddCommGroup A]
    (h : Lattice) (c : Configuration A) (z) :
    difference h c z = c (z + h) - c z := rfl

/-- Vanishing of `Δₕc` is exactly the period condition (Section 1.1). -/
theorem difference_eq_zero_iff {A : Type*} [AddCommGroup A]
    (h : Lattice) (c : Configuration A) : difference h c = 0 ↔ IsPeriod c h := by
  simp only [funext_iff, difference_apply, Pi.zero_apply, sub_eq_zero, IsPeriod]

/-- Difference operators commute (Section 1.1). -/
theorem difference_comm {A : Type*} [AddCommGroup A]
    (h t : Lattice) (c : Configuration A) :
    difference h (difference t c) = difference t (difference h c) := by
  funext z
  simp only [difference_apply]
  rw [show z + h + t = z + t + h by abel]
  abel

end D5.S1.Dynamics.Symbolic.KhetanLaurent

/-!
# Laurent polynomial operators

This module implements the notation of Section 1.1. `Laurent` is the rational
Laurent ring, `act` is its forward-shift action, and `lineEval` substitutes a
lattice monomial into an ordinary polynomial.

The principal identities are `act_apply`, `act_mul`, `act_difference`, and
`act_lineEval_X_pow_sub_one`. The theorem `finiteRange_act` verifies that the
class of finite-range rational configurations is closed under every operator.
-/

namespace D5.S1.Dynamics.Symbolic.KhetanLaurent

/-- Section 1.1 (Notation): the rational Laurent polynomial ring on the full integer lattice. -/
abbrev Laurent := AddMonoidAlgebra ℚ Lattice

namespace Algebra

/-- Section 1.1 (Notation): a forward lattice translation as a rational linear endomorphism. -/
def shiftLinear (h : Lattice) : Module.End ℚ (Configuration ℚ) where
  toFun := shift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Section 1.1 (Notation): the bundled translation evaluates to the forward shift. -/
@[simp] theorem shiftLinear_apply (h : Lattice) (c : Configuration ℚ) :
    shiftLinear h c = shift h c := rfl

/-- Section 1.1 (Notation): the additive lattice acts on configurations by commuting forward shifts. -/
def shiftRepresentation : Multiplicative Lattice →* Module.End ℚ (Configuration ℚ) where
  toFun h := shiftLinear h.toAdd
  map_one' := by ext c z; simp [shiftLinear, shift]
  map_mul' h t := by
    ext c z
    change c (z + (h.toAdd + t.toAdd)) = c ((z + h.toAdd) + t.toAdd)
    rw [add_assoc]

/-- Section 1.1 (Notation): the algebra homomorphism extending lattice translations to Laurent
filters. -/
noncomputable def actionHom : Laurent →ₐ[ℚ] Module.End ℚ (Configuration ℚ) :=
  AddMonoidAlgebra.lift ℚ (Module.End ℚ (Configuration ℚ)) Lattice shiftRepresentation

/-- Section 1.1 (Notation): the finite Laurent polynomial operator applied to a rational
configuration. -/
noncomputable def act (f : Laurent) (c : Configuration ℚ) : Configuration ℚ :=
  actionHom f c

/-- Section 1.1 (Notation): the operator is the finite sum of coefficients times forward-shifted
values. -/
theorem act_apply (f : Laurent) (c : Configuration ℚ) (z : Lattice) :
    act f c z = f.coeff.sum (fun h a => a * c (z + h)) := by
  classical
  simp [act, actionHom, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    shiftRepresentation, shiftLinear, shift, Finset.sum_apply]

/-- Section 1.1 (Notation): the zero filter sends every configuration to zero. -/
@[simp] theorem act_zero (c : Configuration ℚ) : act 0 c = 0 := by
  simp [act]

/-- Section 1.1 (Notation): the constant filter one acts as the identity. -/
@[simp] theorem act_one (c : Configuration ℚ) : act 1 c = c := by
  simp [act]

/-- Section 1.1 (Notation): adding filters adds their outputs. -/
theorem act_add (f g : Laurent) (c : Configuration ℚ) :
    act (f + g) c = act f c + act g c := by
  simp [act]

/-- Section 1.1 (Notation): multiplying filters composes their operators. -/
theorem act_mul (f g : Laurent) (c : Configuration ℚ) :
    act (f * g) c = act f (act g c) := by
  simp [act, Module.End.mul_apply]

/-- Section 1.1 (Notation): subtracting filters subtracts their outputs. -/
theorem act_sub (f g : Laurent) (c : Configuration ℚ) :
    act (f - g) c = act f c - act g c := by
  simp [act]

/-- Section 1.1 (Notation): negating a filter negates its output. -/
theorem act_neg (f : Laurent) (c : Configuration ℚ) : act (-f) c = -act f c := by
  simp [act]

/-- Section 1.1 (Notation): every Laurent filter annihilates the zero configuration. -/
@[simp] theorem act_config_zero (f : Laurent) : act f 0 = 0 := by
  exact map_zero (actionHom f)

/-- Section 1.1 (Notation): each Laurent operator preserves sums of configurations. -/
theorem act_config_add (f : Laurent) (c d : Configuration ℚ) :
    act f (c + d) = act f c + act f d := by
  exact map_add (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator preserves differences of configurations. -/
theorem act_config_sub (f : Laurent) (c d : Configuration ℚ) :
    act f (c - d) = act f c - act f d := by
  exact map_sub (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator commutes with rational scaling of the
configuration. -/
theorem act_config_smul (f : Laurent) (a : ℚ) (c : Configuration ℚ) :
    act f (a • c) = a • act f c := by
  exact map_smul (actionHom f) a c

/-- Section 1.1 (Notation): rational scaling of the filter scales its output. -/
theorem act_smul (a : ℚ) (f : Laurent) (c : Configuration ℚ) :
    act (a • f) c = a • act f c := by
  simp [act]

/-- Section 1.1 (Notation): a single supported coefficient acts by scaling a forward shift. -/
@[simp] theorem act_single (h : Lattice) (a : ℚ) (c : Configuration ℚ) :
    act (AddMonoidAlgebra.single h a) c = a • shift h c := by
  simp [act, actionHom, shiftRepresentation, shiftLinear]

/-- Section 1.1 (Notation): the lattice monomial with exponent `h` and coefficient one. -/
noncomputable def monomial (h : Lattice) : Laurent := AddMonoidAlgebra.single h 1

/-- Section 1.1 (Notation): the zero-exponent monomial is the multiplicative identity. -/
@[simp] theorem monomial_zero : monomial 0 = 1 := rfl

/-- Section 1.1 (Notation): multiplication of lattice monomials adds their exponents. -/
@[simp] theorem monomial_mul (h t : Lattice) :
    monomial h * monomial t = monomial (h + t) := by
  simp [monomial]

/-- Section 1.1 (Notation): a natural power of a monomial scales its exponent. -/
@[simp] theorem monomial_pow (h : Lattice) (q : ℕ) :
    monomial h ^ q = monomial (q • h) := by
  simp [monomial, AddMonoidAlgebra.single_pow]

/-- Section 1.1 (Notation): every lattice monomial is a unit, with inverse at the negated exponent. -/
theorem monomial_isUnit (h : Lattice) : IsUnit (monomial h) := by
  exact ⟨⟨monomial h, monomial (-h), by simp, by simp⟩, rfl⟩

/-- Section 1.1 (Notation): a lattice monomial has a nonzero coefficient and is nonzero. -/
theorem monomial_ne_zero (h : Lattice) : monomial h ≠ 0 :=
  (monomial_isUnit h).ne_zero

/-- Section 1.1 (Notation): distinct lattice exponents give distinct monomials. -/
theorem monomial_injective : Function.Injective monomial :=
  AddMonoidAlgebra.single_left_injective one_ne_zero

/-- Section 1.1 (Notation): a nonzero direction gives a nonzero difference polynomial. -/
theorem monomial_sub_one_ne_zero {h : Lattice} (hh : h ≠ 0) :
    monomial h - 1 ≠ 0 := by
  intro heq
  have h : monomial h = monomial 0 := by simpa using sub_eq_zero.mp heq
  exact hh (monomial_injective h)

/-- Section 1.1 (Notation): a lattice monomial acts by its forward shift. -/
@[simp] theorem act_monomial (h : Lattice) (c : Configuration ℚ) :
    act (monomial h) c = shift h c := by simp [monomial]

/-- Section 1.1 (Notation): the polynomial `monomial h - 1` acts by the difference operator in
direction `h`. -/
theorem act_difference (h : Lattice) (c : Configuration ℚ) :
    act (monomial h - 1) c = difference h c := by
  simp [act_sub, difference]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice translations. -/
theorem act_shift (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (shift h c) = shift h (act f c) := by
  rw [← act_monomial, ← act_mul, mul_comm, act_mul, act_monomial]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice differences. -/
theorem act_difference_comm (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (difference h c) = difference h (act f c) := by
  simp [difference, act_config_sub, act_shift]

/-- Section 1.1 (Notation): a constant rational configuration has finite range. -/
theorem finiteRange_const (a : ℚ) : FiniteRange (fun _ : Lattice => a) := by
  simp [FiniteRange]

/-- Section 1.1 (Notation): the sum of two finite-range rational configurations has finite range. -/
theorem finiteRange_add {c d : Configuration ℚ} (hc : FiniteRange c)
    (hd : FiniteRange d) : FiniteRange (c + d) := by
  apply ((hc.prod hd).image (fun p : ℚ × ℚ => p.1 + p.2)).subset
  rintro _ ⟨z, rfl⟩
  exact ⟨(c z, d z), ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩

/-- Section 1.1 (Notation): rational scaling preserves finite range. -/
theorem finiteRange_smul {c : Configuration ℚ} (hc : FiniteRange c) (a : ℚ) :
    FiniteRange (a • c) := by
  exact hc.map (fun x => a * x)

/-- Section 1.1 (Notation): the finite sum defining a Laurent operator preserves finite rational
range. -/
theorem finiteRange_act (f : Laurent) {c : Configuration ℚ} (hc : FiniteRange c) :
    FiniteRange (act f c) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [act_zero]
    change FiniteRange (fun _ : Lattice => (0 : ℚ))
    exact finiteRange_const 0
  | add f g hf hg => rw [act_add]; exact finiteRange_add hf hg
  | single h a => rw [act_single]; exact finiteRange_smul (hc.shift h) a

/-- Section 1.1 (Notation): substitute the lattice monomial in direction `v` for a polynomial
variable. -/
noncomputable def lineEval (v : Lattice) : Polynomial ℚ →+* Laurent :=
  Polynomial.eval₂RingHom (algebraMap ℚ Laurent) (monomial v)

/-- Section 1.1 (Notation): the polynomial variable evaluates to the monomial in direction `v`. -/
@[simp] theorem lineEval_X (v : Lattice) : lineEval v Polynomial.X = monomial v := by
  simp [lineEval]

/-- Section 1.1 (Notation): a constant polynomial evaluates to the corresponding zero-exponent
Laurent coefficient. -/
@[simp] theorem lineEval_C (v : Lattice) (a : ℚ) :
    lineEval v (Polynomial.C a) = AddMonoidAlgebra.single 0 a := by
  simp [lineEval]

/-- Section 1.1 (Notation): substitution along a lattice direction preserves polynomial
divisibility. -/
theorem lineEval_dvd (v : Lattice) {f g : Polynomial ℚ} (h : f ∣ g) :
    lineEval v f ∣ lineEval v g := map_dvd (lineEval v) h

/-- Section 1.1 (Notation): a power of the polynomial variable evaluates to a scaled lattice
exponent. -/
@[simp] theorem lineEval_X_pow (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q) = monomial (q • v) := by simp

/-- Section 1.1 (Notation): the period polynomial evaluates to the difference polynomial in
direction `q • v`. -/
theorem lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q - 1) = monomial (q • v) - 1 := by simp

/-- Section 1.1 (Notation): the evaluated period polynomial acts as the difference in direction `q •
v`. -/
theorem act_lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) (c : Configuration ℚ) :
    act (lineEval v (Polynomial.X ^ q - 1)) c = difference (q • v) c := by
  rw [lineEval_X_pow_sub_one, act_difference]

end Algebra
end D5.S1.Dynamics.Symbolic.KhetanLaurent

/-!
# Integer scaling for the product-annihilator theorem

Appendix A (`app:product`), proving Proposition 3.3 (`prop:product`), begins by
scaling the finite rational alphabet and the finite filter coefficients
separately. `finiteRange_integer_scale` and `integer_filter_scale` provide the
two nonzero multipliers. The map `intLaurentCast` changes only the coefficient
ring, so the resulting equations still concern the full integer lattice.
-/

namespace D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra

/-- The integer-coefficient Laurent ring used in Appendix A (`app:product`) to prove Proposition 3.3
(`prop:product`). -/
abbrev IntegerLaurent := AddMonoidAlgebra ℤ Lattice

/-- The coefficient embedding from integer to rational Laurent polynomials in Appendix A
(`app:product`), preserving every lattice exponent. -/
noncomputable def intLaurentCast : IntegerLaurent →+* Laurent :=
  AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ)

/-- Auxiliary to the scaling step of Appendix A (`app:product`): coefficient embedding acts
pointwise by the integer-to-rational cast. -/
@[simp] theorem intLaurentCast_coeff (F : IntegerLaurent) (h : Lattice) :
    (intLaurentCast F).coeff h = (F.coeff h : ℚ) := by
  simp [intLaurentCast]

/-- The common-denominator step in Appendix A (`app:product`): one nonzero integer multiplier makes
every element of a finite rational set integral. -/
theorem finite_set_integer_scale (S : Set ℚ) (hS : S.Finite) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ S, ∃ a : ℤ, (n : ℚ) * x = (a : ℚ) := by
  classical
  obtain ⟨n, hn⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors ℤ) hS.toFinset
  refine ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.property, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hn x (hS.mem_toFinset.mpr hx)
  refine ⟨a, ?_⟩
  simpa using ha.symm

/-- The configuration scaling step of Appendix A (`app:product`): a nonzero integer multiple of a
finite-range rational configuration has finite integer range. -/
theorem finiteRange_integer_scale {c : Configuration ℚ} (hc : FiniteRange c) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ C : Configuration ℤ,
      FiniteRange C ∧ ∀ z, (n : ℚ) * c z = (C z : ℚ) := by
  classical
  obtain ⟨n, hn, hs⟩ := finite_set_integer_scale (Set.range c) hc
  choose C hC using fun z : Lattice => hs (c z) ⟨z, rfl⟩
  refine ⟨n, hn, C, ?_, hC⟩
  have hcast : FiniteRange (fun z => (C z : ℚ)) := by
    have heq : (fun z => (C z : ℚ)) = fun z => (n : ℚ) * c z := by
      funext z
      exact (hC z).symm
    rw [heq]
    exact hc.map (fun x => (n : ℚ) * x)
  apply Set.Finite.of_finite_image (f := fun a : ℤ => (a : ℚ)) ?_
    (Int.cast_injective.injOn)
  rw [← Set.range_comp]
  exact hcast

/-- The filter scaling step of Appendix A (`app:product`): a rational Laurent polynomial has a
nonzero integer multiple represented by an integer-coefficient filter. -/
theorem integer_filter_scale (f : Laurent) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ F : IntegerLaurent, intLaurentCast F = (n : ℚ) • f := by
  classical
  obtain ⟨n, hn, C, _, hC⟩ := finiteRange_integer_scale (c := f.coeff) f.coeff.finite_range
  have hsupport : ∀ h : Lattice, C h ≠ 0 → h ∈ f.coeff.support := by
    intro h hh
    by_contra hnot
    have hz := hC h
    rw [Finsupp.notMem_support_iff.mp hnot, mul_zero] at hz
    exact hh (Int.cast_eq_zero.mp hz.symm)
  let F : IntegerLaurent := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support C hsupport)
  refine ⟨n, hn, F, ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro h
  rw [intLaurentCast_coeff]
  change (C h : ℚ) = (n : ℚ) * f.coeff h
  exact (hC h).symm

end D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra

/-!
# A product of difference operators from a nonzero annihilator

Proposition 3.3 (`prop:product`) is
`exists_product_differences_of_annihilator`. Appendix A (`app:product`) proves
it by separate integer scaling of the configuration and filter, prime dilation,
and polynomial interpolation. Every output direction is nonzero, and the
resulting list of difference factors is nonempty.

The action `coefficientAct` is defined over a commutative coefficient ring so
that reduction from integers to `ZMod p` commutes with filtering. Frobenius
identifies the prime power of a reduced filter with dilation of its exponents.
A common bound on all dilated integer outputs then forces sufficiently large
prime dilations of annihilators to annihilate. Factorization extends this to
the progression `1 + j * B!` in equation (`eq:dilation-family`).

The theorem `dilation_interpolation_identity` is equation (`eq:interpolation`)
with an arbitrary auxiliary polynomial. Translating one nonzero coefficient
to exponent zero and choosing factors `C(M) - X` isolates that coefficient and
gives a product of `M - 1`. Casting back to rationals and cancelling the
nonzero scaling factors concludes the proof.
-/

namespace D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra

section CoefficientAction

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a forward translation
as a linear endomorphism over the coefficient ring. -/
private def coefficientShift (h : Lattice) : Module.End R (Configuration R) where
  toFun := shift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the integer lattice
acts by forward translations over a commutative ring. -/
private def coefficientShiftRepresentation : Multiplicative Lattice →* Module.End R (Configuration R) where
  toFun h := coefficientShift h.toAdd
  map_one' := by
    ext c z
    change c (z + 0) = c z
    rw [add_zero]
  map_mul' h t := by
    ext c z
    change c (z + (h.toAdd + t.toAdd)) = c ((z + h.toAdd) + t.toAdd)
    rw [add_assoc]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): extend the
coefficient-ring shift representation to a Laurent algebra action. -/
private noncomputable def coefficientActionHom :
    AddMonoidAlgebra R Lattice →ₐ[R] Module.End R (Configuration R) :=
  AddMonoidAlgebra.lift R (Module.End R (Configuration R)) Lattice coefficientShiftRepresentation

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the Laurent operator
over a commutative ring, permitting both integral coefficients and reduction modulo a prime. -/
noncomputable def coefficientAct (f : AddMonoidAlgebra R Lattice)
    (c : Configuration R) : Configuration R := coefficientActionHom f c

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the coefficient-ring
action is the finite sum of coefficients times translated values. -/
theorem coefficientAct_apply (f : AddMonoidAlgebra R Lattice) (c : Configuration R) (z : Lattice) :
    coefficientAct f c z = f.coeff.sum (fun h a => a * c (z + h)) := by
  classical
  simp [coefficientAct, coefficientActionHom, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    coefficientShiftRepresentation, coefficientShift, shift, Finset.sum_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the zero
coefficient-ring filter has zero output. -/
@[simp] theorem coefficientAct_zero (c : Configuration R) : coefficientAct 0 c = 0 := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the identity
coefficient-ring filter acts identically. -/
@[simp] theorem coefficientAct_one (c : Configuration R) : coefficientAct 1 c = c := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every
coefficient-ring filter annihilates the zero configuration. -/
@[simp] theorem coefficientAct_config_zero (f : AddMonoidAlgebra R Lattice) :
    coefficientAct f 0 = 0 := map_zero (coefficientActionHom f)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): adding
coefficient-ring filters adds their outputs. -/
theorem coefficientAct_add (f g : AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (f + g) c = coefficientAct f c + coefficientAct g c := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): multiplying
coefficient-ring filters composes their actions. -/
theorem coefficientAct_mul (f g : AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (f * g) c = coefficientAct f (coefficientAct g c) := by
  simp [coefficientAct, Module.End.mul_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the action of a
finite filter sum is the corresponding sum of outputs. -/
theorem coefficientAct_finset_sum {ι : Type*} (S : Finset ι)
    (f : ι → AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (∑ j ∈ S, f j) c = ∑ j ∈ S, coefficientAct (f j) c := by
  change coefficientActionHom (∑ j ∈ S, f j) c = _
  rw [map_sum]
  exact LinearMap.sum_apply _ _ _

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a single coefficient
acts as a scaled forward shift over the coefficient ring. -/
@[simp] theorem coefficientAct_single (h : Lattice) (a : R) (c : Configuration R) :
    coefficientAct (AddMonoidAlgebra.single h a) c = a • shift h c := by
  simp [coefficientAct, coefficientActionHom, coefficientShiftRepresentation, coefficientShift]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the general
coefficient-ring action agrees with the rational action from Section 1.1. -/
theorem coefficientAct_rat (f : Laurent) (c : Configuration ℚ) : coefficientAct f c = act f c := by
  funext z
  rw [coefficientAct_apply, act_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): changing the
coefficient ring commutes with the action on the configuration, in particular for reduction
modulo a prime. -/
theorem coefficientAct_map (ρ : R →+* S) (f : AddMonoidAlgebra R Lattice)
    (c : Configuration R) :
    coefficientAct (AddMonoidAlgebra.mapRingHom Lattice ρ f) (ρ ∘ c) =
      ρ ∘ coefficientAct f c := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    funext z
    simp
  | add f g hf hg =>
    funext z
    simpa only [map_add, coefficientAct_add, Pi.add_apply, Function.comp_apply]
      using congrArg₂ (fun x y : S => x + y) (congrFun hf z) (congrFun hg z)
  | single h a =>
    funext z
    simp [coefficientAct_single, shift, Function.comp_apply, map_mul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): natural scaling of
lattice exponents as an additive homomorphism. -/
private def dilationLattice (n : ℕ) : Lattice →+ Lattice where
  toFun h := n • h
  map_zero' := nsmul_zero n
  map_add' h t := nsmul_add h t n

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the Laurent ring
homomorphism scaling all lattice exponents by a natural number. -/
noncomputable def dilate (n : ℕ) : AddMonoidAlgebra R Lattice →+* AddMonoidAlgebra R Lattice :=
  AddMonoidAlgebra.mapDomainRingHom R (dilationLattice n)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation scales the
exponent of a single coefficient without changing that coefficient. -/
@[simp] theorem dilate_single (n : ℕ) (h : Lattice) (a : R) :
    dilate n (AddMonoidAlgebra.single h a) = AddMonoidAlgebra.single (n • h) a := by
  simp [dilate, dilationLattice]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation by one fixes
the filter. -/
@[simp] theorem dilate_one (f : AddMonoidAlgebra R Lattice) : dilate 1 f = f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): composition of
dilations multiplies their scaling parameters. -/
theorem dilate_dilate (m n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    dilate m (dilate n f) = dilate (m * n) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp only [dilate_single, smul_smul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a coefficient-ring
homomorphism commutes with dilation of the exponents. -/
theorem map_dilate (ρ : R →+* S) (n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    AddMonoidAlgebra.mapRingHom Lattice ρ (dilate n f) =
      dilate n (AddMonoidAlgebra.mapRingHom Lattice ρ f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every positive power
of an annihilator still annihilates the configuration. -/
theorem coefficientAct_pow_eq_zero (f : AddMonoidAlgebra R Lattice) (c : Configuration R)
    (hf : coefficientAct f c = 0) {n : ℕ} (hn : 0 < n) :
    coefficientAct (f ^ n) c = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, coefficientAct_mul, hf, coefficientAct_config_zero]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a fixed finite filter
on a finite-range configuration has finitely many outputs across all dilation exponents and
lattice sites. -/
theorem finite_dilate_values (f : AddMonoidAlgebra R Lattice) {c : Configuration R}
    (hc : FiniteRange c) :
    (Set.range (fun nz : ℕ × Lattice => coefficientAct (dilate nz.1 f) c nz.2)).Finite := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    apply ((hf.prod hg).image (fun x : R × R => x.1 + x.2)).subset
    rintro _ ⟨nz, rfl⟩
    refine ⟨(coefficientAct (dilate nz.1 f) c nz.2,
      coefficientAct (dilate nz.1 g) c nz.2), ⟨⟨nz, rfl⟩, ⟨nz, rfl⟩⟩, ?_⟩
    simp [coefficientAct_add]
  | single h a =>
    apply (hc.image (fun x : R => a * x)).subset
    rintro _ ⟨nz, rfl⟩
    refine ⟨c (nz.2 + nz.1 • h), ⟨_, rfl⟩, ?_⟩
    simp [shift]

end CoefficientAction

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): Frobenius in
characteristic `p` identifies the `p`th power of a Laurent filter over `ZMod p` with its
dilation by `p`. -/
theorem zmod_pow_eq_dilate (p : ℕ) [Fact p.Prime]
    (f : AddMonoidAlgebra (ZMod p) Lattice) : f ^ p = dilate p f := by
  let : CharP (AddMonoidAlgebra (ZMod p) Lattice) p :=
    charP_of_injective_algebraMap' (ZMod p) p
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [NeZero.ne p]
  | add f g hf hg =>
    rw [← frobenius_def, map_add, frobenius_def, frobenius_def, hf, hg, map_add]
  | single h a =>
    rw [AddMonoidAlgebra.single_pow, dilate_single, ZMod.pow_card]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the finite set of all
dilated integer outputs has a common natural absolute-value bound. -/
theorem exists_uniform_dilate_bound (f : IntegerLaurent) {c : Configuration ℤ}
    (hc : FiniteRange c) :
    ∃ B : ℕ, ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B := by
  classical
  have hv := finite_dilate_values f hc
  refine ⟨hv.toFinset.sup Int.natAbs, fun n z => ?_⟩
  exact Finset.le_sup (f := Int.natAbs) (hv.mem_toFinset.mpr ⟨(n, z), rfl⟩)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation by a prime
larger than the common output bound preserves annihilation. Frobenius makes each output
divisible by that prime, and the strict absolute-value bound forces zero. -/
theorem prime_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    {m p : ℕ} (hp : p.Prime) (hBp : B < p)
    (hm : coefficientAct (dilate m f) c = 0) :
    coefficientAct (dilate (m * p) f) c = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let ρ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Fm := AddMonoidAlgebra.mapRingHom Lattice ρ (dilate m f)
  have hmod : coefficientAct Fm (ρ ∘ c) = 0 := by
    rw [coefficientAct_map, hm]
    funext z
    exact map_zero ρ
  have hpow := coefficientAct_pow_eq_zero Fm (ρ ∘ c) hmod hp.pos
  have heq : AddMonoidAlgebra.mapRingHom Lattice ρ (dilate (m * p) f) = Fm ^ p := by
    rw [zmod_pow_eq_dilate]
    dsimp only [Fm]
    rw [← map_dilate, dilate_dilate, mul_comm p m]
  have hnext : coefficientAct
      (AddMonoidAlgebra.mapRingHom Lattice ρ (dilate (m * p) f)) (ρ ∘ c) = 0 := by
    rw [heq]
    exact hpow
  rw [coefficientAct_map] at hnext
  funext z
  have hz := congrFun hnext z
  change ((coefficientAct (dilate (m * p) f) c z : ℤ) : ZMod p) = 0 at hz
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  simpa only [Int.natAbs_natCast] using (hbound (m * p) z).trans_lt hBp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every prime factor of
an integer coprime to `B!` exceeds `B`. -/
private theorem prime_gt_of_coprime_factorial {B n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : n.Coprime B.factorial) : B < p := by
  by_contra hle
  have hcop : p.Coprime B.factorial := hn.of_dvd_left hpn
  exact (hp.coprime_iff_not_dvd.mp hcop)
    (Nat.dvd_factorial hp.pos (Nat.le_of_not_gt hle))

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): prime factorization
extends preservation of annihilation to every positive exponent coprime to the factorial bound. -/
theorem coprime_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    (hf : coefficientAct f c = 0) {n : ℕ} (hn : 0 < n) (hcop : n.Coprime B.factorial) :
    coefficientAct (dilate n f) c = 0 := by
  have hall : ∀ k : ℕ, 0 < k → k.Coprime B.factorial → coefficientAct (dilate k f) c = 0 := by
    apply induction_on_primes
    · intro h
      exact (Nat.not_lt_zero _ h).elim
    · intro _ _
      simpa only [dilate_one] using hf
    · intro p k hp ih hpos hc
      have hkp : 0 < k := by
        by_contra hz
        have hk : k = 0 := Nat.eq_zero_of_not_pos hz
        simp [hk] at hpos
      have hkc : k.Coprime B.factorial := hc.of_dvd_left (Nat.dvd_mul_left k p)
      have hBp := prime_gt_of_coprime_factorial hp (Nat.dvd_mul_right p k) hc
      rw [Nat.mul_comm p k]
      exact prime_dilate_annihilates f c B hbound hp hBp (ih hkp hkc)
  exact hall n hn hcop

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): equation
(`eq:dilation-family`): all dilations at exponents `1 + j * B!` annihilate. -/
theorem progression_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    (hf : coefficientAct f c = 0) (j : ℕ) :
    coefficientAct (dilate (1 + j * B.factorial) f) c = 0 := by
  have hn : 0 < 1 + j * B.factorial :=
    Nat.zero_lt_one.trans_le (Nat.le_add_right 1 _)
  have hcop : (1 + j * B.factorial).Coprime B.factorial :=
    (Nat.coprime_add_mul_right_left 1 B.factorial j).mpr (Nat.coprime_one_left _)
  exact coprime_dilate_annihilates f c B hbound hf hn hcop

section Interpolation

variable {R : Type*} [CommRing R]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a dilated filter is
the finite sum of its original coefficients at their scaled exponents. -/
private theorem dilate_eq_sum (n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    dilate n f = ∑ h ∈ f.coeff.support, AddMonoidAlgebra.single (n • h) (f.coeff h) := by
  conv_lhs => rw [← f.sum_coeff_single]
  simp only [Finsupp.sum, map_sum, dilate_single]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the term with
exponent `(1 + j * r) • h` factors into the original monomial and a `j`th power. -/
private theorem single_affine_dilate (j r : ℕ) (h : Lattice) (a : R) :
    AddMonoidAlgebra.single ((1 + j * r) • h) a =
      AddMonoidAlgebra.single h a *
        (AddMonoidAlgebra.single (r • h) (1 : R)) ^ j := by
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single, one_pow, mul_one]
  simp only [add_nsmul, one_nsmul, smul_smul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): equation
(`eq:interpolation`): linear combinations of dilations along an arithmetic progression are
evaluations of the coefficient polynomial at the corresponding lattice monomials. -/
theorem dilation_interpolation_identity (r : ℕ) (f : AddMonoidAlgebra R Lattice)
    (H : Polynomial (AddMonoidAlgebra R Lattice)) :
    H.sum (fun j b => b * dilate (1 + j * r) f) =
      ∑ h ∈ f.coeff.support, AddMonoidAlgebra.single h (f.coeff h) *
        H.eval (AddMonoidAlgebra.single (r • h) 1) := by
  classical
  simp only [Polynomial.sum_def, dilate_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [single_affine_dilate]
  ac_rfl

end Interpolation

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): interpolation for an
integral annihilator with nonzero constant coefficient produces a product of nonzero-exponent
difference factors. The auxiliary factors `C(M) - X` evaluate at one to `M - 1`. -/
theorem integer_centered_product (f : IntegerLaurent) (hf0 : f.coeff 0 ≠ 0)
    (c : Configuration ℤ) (hc : FiniteRange c) (hf : coefficientAct f c = 0) :
    ∃ r : ℕ, 0 < r ∧ coefficientAct
      (∏ h ∈ f.coeff.support.erase 0,
        (AddMonoidAlgebra.single (r • h) (1 : ℤ) - 1)) c = 0 := by
  classical
  obtain ⟨B, hB⟩ := exists_uniform_dilate_bound f hc
  let r := B.factorial
  let S := f.coeff.support.erase 0
  let H : Polynomial IntegerLaurent :=
    ∏ h ∈ S, (Polynomial.C (AddMonoidAlgebra.single (r • h) 1) - Polynomial.X)
  let P : IntegerLaurent := ∏ h ∈ S, (AddMonoidAlgebra.single (r • h) 1 - 1)
  have hcomb : coefficientAct (H.sum (fun j b => b * dilate (1 + j * r) f)) c = 0 := by
    rw [Polynomial.sum_def, coefficientAct_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [coefficientAct_mul, progression_dilate_annihilates f c B hB hf j,
      coefficientAct_config_zero]
  have hroot (h : Lattice) (hh : h ∈ S) :
      H.eval (AddMonoidAlgebra.single (r • h) 1) = 0 := by
    dsimp only [H]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero hh
    simp
  have heval : H.eval (AddMonoidAlgebra.single (r • (0 : Lattice)) 1) = P := by
    rw [nsmul_zero]
    change H.eval (1 : IntegerLaurent) = P
    simp [H, P, Polynomial.eval_prod]
  have hident := dilation_interpolation_identity r f H
  rw [Finset.sum_eq_single 0] at hident
  · rw [heval] at hident
    rw [hident, coefficientAct_mul, coefficientAct_single] at hcomb
    refine ⟨r, Nat.factorial_pos B, ?_⟩
    change coefficientAct P c = 0
    funext z
    have hz := congrFun hcomb z
    change f.coeff 0 * coefficientAct P c (z + 0) = 0 at hz
    rw [add_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hf0
  · intro h hh hn
    rw [hroot h (Finset.mem_erase.mpr ⟨hn, hh⟩), mul_zero]
  · intro hnot
    exact (hnot (Finsupp.mem_support_iff.mpr hf0)).elim

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): translate a nonzero
coefficient to exponent zero and apply interpolation. Nonzeroness of the configuration forces a
nonempty factor list, and positive dilation preserves each nonzero direction. -/
theorem exists_integer_product_differences {c : Configuration ℤ} (hc : FiniteRange c)
    (hcne : c ≠ 0) {f : IntegerLaurent} (hfne : f ≠ 0) (hf : coefficientAct f c = 0) :
    ∃ hs : List Lattice, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      coefficientAct ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) c = 0 := by
  classical
  have hcoeff : f.coeff ≠ 0 := AddMonoidAlgebra.coeff_eq_zero.not.mpr hfne
  obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  let F := AddMonoidAlgebra.single (-u) (1 : ℤ) * f
  have hF0 : F.coeff 0 ≠ 0 := by
    simpa [F, AddMonoidAlgebra.coeff_single_mul_apply] using Finsupp.mem_support_iff.mp hu
  have hF : coefficientAct F c = 0 := by
    rw [coefficientAct_mul, hf, coefficientAct_config_zero]
  obtain ⟨r, hr, hprod⟩ := integer_centered_product F hF0 c hc hF
  let S := F.coeff.support.erase 0
  let hs := S.toList.map (fun h => r • h)
  have hhs : coefficientAct
      ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) c = 0 := by
    simpa only [hs, List.map_map, Finset.prod_map_toList, Function.comp_apply] using hprod
  refine ⟨hs, ?_, ?_, hhs⟩
  · intro he
    rw [he, List.map_nil, List.prod_nil, coefficientAct_one] at hhs
    exact hcne hhs
  · intro h hh
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hh
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1
    exact smul_ne_zero (Nat.ne_of_gt hr) hx0

/-- Proposition 3.3 (`prop:product`), proved in Appendix A (`app:product`): every nonzero
finite-range rational configuration with a nonzero Laurent annihilator has a nonempty product of
differences in nonzero lattice directions as an annihilator. -/
theorem exists_product_differences_of_annihilator {c : Configuration ℚ}
    (hc : FiniteRange c) (hcne : c ≠ 0) {f : Laurent} (hfne : f ≠ 0)
    (hf : act f c = 0) :
    ∃ hs : List Lattice, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      act ((hs.map (fun h => monomial h - 1)).prod) c = 0 := by
  classical
  obtain ⟨a, ha, C, hCfinite, hC⟩ := finiteRange_integer_scale hc
  obtain ⟨b, hb, F, hF⟩ := integer_filter_scale f
  have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hCeq : (Int.castRingHom ℚ) ∘ C = (a : ℚ) • c := by
    funext z
    exact (hC z).symm
  have hCne : C ≠ 0 := by
    intro hz
    apply hcne
    funext z
    have he := hC z
    rw [hz] at he
    exact (mul_eq_zero.mp he).resolve_left haq
  have hFne : F ≠ 0 := by
    intro hz
    apply hfne
    have he := hF
    rw [hz, map_zero] at he
    exact (smul_eq_zero_iff_right hbq).mp he.symm
  have hFC : coefficientAct F C = 0 := by
    have he : coefficientAct (intLaurentCast F) ((Int.castRingHom ℚ) ∘ C) = 0 := by
      rw [coefficientAct_rat, hF, hCeq, act_smul, act_config_smul, hf, smul_zero, smul_zero]
    change coefficientAct (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ) F)
      ((Int.castRingHom ℚ) ∘ C) = 0 at he
    rw [coefficientAct_map] at he
    funext z
    exact Int.cast_eq_zero.mp (congrFun he z)
  obtain ⟨hs, hnil, hnz, hann⟩ := exists_integer_product_differences hCfinite hCne hFne hFC
  refine ⟨hs, hnil, hnz, ?_⟩
  have he := coefficientAct_map (Int.castRingHom ℚ)
    ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) C
  rw [hann] at he
  have hcastprod : AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ)
      ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) =
      (hs.map (fun h => monomial h - 1)).prod := by
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro h hh
    simp [monomial]
  rw [hcastprod, coefficientAct_rat, hCeq, act_config_smul] at he
  apply (smul_eq_zero_iff_right haq).mp
  calc
    (a : ℚ) • act ((hs.map (fun h => monomial h - 1)).prod) c =
        (Int.castRingHom ℚ) ∘ (0 : Configuration ℤ) := he
    _ = 0 := by
      funext z
      rfl

end D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra
