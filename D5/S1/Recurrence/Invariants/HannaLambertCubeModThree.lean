/- GID: D5/S1/Recurrence/Invariants/HannaLambertCubeModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaLambertCubeModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lambert-series contraction and cubic Frobenius prove Hanna's mod-three conjectures. -/

/-
result:
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#18861; Proved)
Direct frozen dependencies (declaration statement_id, with same-delivery proofs expanded):
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.Agree
    sha256:e3cd9c09ab9c066077e3362c2145b9293441e263c1e4e0df7614ff40a3b1cb53;
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.agree_cube
    sha256:09f85dfa6fb94a0d91925170e623f1fc09a77c37573ca8ef780549de2ba54b7c;
  D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.cube_congr_subst_three
    sha256:14abc582a4381fc7ae3eb29f70d25ef7066b4ebeb5ab09bbf99cfbb70914eab0.
Private theorem classifications (same-delivery proofs expanded):
  L_zero_constant: proof_shape: bind-only; consumer(s): step_agree, A_to_B.
  L_add: proof_shape: bind-only; consumer(s): A_to_B, B_to_A.
  L_map: proof_shape: bind-only; consumer(s): solution_map, integral_pair.
  L_agree: proof_shape: bind-only; consumer(s): step_agree.
  step_zero_constant: proof_shape: bind-only; consumer(s): solution_isA.
  step_agree: proof_shape: bind-only; consumer(s): approx_stable, solution_fixed, fixed_unique.
  approx_stable: proof_shape: content; consumer(s): solution_agree.
  solution_agree: proof_shape: content; consumer(s): solution_fixed.
  solution_fixed: proof_shape: content; consumer(s): solution_map, solution_isA, integer_equation.
  fixed_unique: proof_shape: content; consumer(s): solution_map, A_unique.
  solution_map: proof_shape: content; consumer(s): integral_pair.
  L_X_geom: proof_shape: bind-only; consumer(s): A_to_B, B_to_A.
  solution_isA: proof_shape: content; consumer(s): pair_exists, integral_pair.
  A_unique: proof_shape: content; consumer(s): solution_link, integral_pair.
  A_to_B: proof_shape: bind-only; consumer(s): pair_exists.
  B_to_A: proof_shape: bind-only; consumer(s): solution_link.
  solution_link: proof_shape: content; consumer(s): integral_pair.
  pair_exists: proof_shape: content; consumer(s): result.
  integral_pair: proof_shape: content; consumer(s): result.
  integer_equation: proof_shape: content; consumer(s): integer_mod_three.
  integer_mod_three: proof_shape: content; consumer(s): residue_multiple, residue_other.
  residue_multiple: proof_shape: content; consumer(s): result.
  residue_other: proof_shape: content; consumer(s): result.
All declarations have escape_witness: none; the settling result is the module admission basis.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19096.
The public rational definitions retain the expressions in #18861. The generic Lambert
expression is inlined in the proofs; Agree is reused from CubicFifteenSubstitutionParity,
and approximation uses Function.iterate. Integer specializations introduce no aliases.
-/

import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.CubicTernarySubstitutionParity
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

open PowerSeries

/-- `Sum_{n>=1} F(x^n)` for a power series `F` without constant term, coefficientwise: the coefficient
of `x^m` is the sum of the coefficients of `x^(m/n)` in `F` over the divisors `n` of `m`. -/
noncomputable def lambertSum (F : PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0

/-- OEIS A382318: "G.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3" (offset 1). -/
def IsA382318 (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ A = X + lambertSum A ^ 3

/-- OEIS A382319: "G.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3" (offset 1); the summand
A(x^n)^3 is the cube A^3 taken at x^n. -/
def IsA382319 (B : PowerSeries ℚ) : Prop :=
  constantCoeff B = 0 ∧ B = X * (1 - X : PowerSeries ℚ)⁻¹ + lambertSum (B ^ 3)

/-- OEIS A382318 (P. D. Hanna), conjectures: "a(3*n) == A382319(n) (mod 3) for n >= 0; a(3*n+1) == 0
(mod 3) and a(3*n+2) == 0 (mod 3) for n >= 1". The terms are integers. -/
def claim : Prop :=
  (∃ A B, IsA382318 A ∧ IsA382319 B) ∧
    ∀ A B, IsA382318 A → IsA382319 B →
      (∀ n : ℕ, ∃ u v : ℤ, coeff (3 * n) A = u ∧ coeff n B = v ∧ u ≡ v [ZMOD 3]) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ u v : ℤ, coeff (3 * n + 1) A = u ∧ coeff (3 * n + 2) A = v ∧
          u ≡ 0 [ZMOD 3] ∧ v ≡ 0 [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

open PowerSeries
open private Agree agree_cube from D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

section Generic
variable {R S : Type*} [CommRing R] [CommRing S]

private theorem L_zero_constant (F : PowerSeries R) : constantCoeff ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) F) = 0 := by
  exact constantCoeff_mk

private theorem L_add (F G : PowerSeries R) : (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (F + G) = (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) F + (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) G := by
  classical
  ext m
  simp only [coeff_mk, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

private theorem L_map (h : R →+* S) (F : PowerSeries R) :
    (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (F.map h) = ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) F).map h := by
  classical
  ext m
  simp only [coeff_mk, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

private theorem L_agree {d : ℕ} {f g : PowerSeries R} (h : Agree d f g) :
    Agree d ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) f) ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) g) := by
  classical
  intro m hm
  simp only [coeff_mk]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs
  · exact h _ (lt_of_le_of_lt (Nat.div_le_self _ _) hm)
  · rfl

private noncomputable def step (f : PowerSeries R) : PowerSeries R := X + ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) f)^3

private theorem step_zero_constant (f : PowerSeries R) : constantCoeff (step f) = 0 := by
  simp [step]

private theorem step_agree {d : ℕ} {f g : PowerSeries R} (h : Agree d f g) :
    Agree (d + 1) (step f) (step g) := by
  have hc := agree_cube
    (L_zero_constant f) (L_zero_constant g) (L_agree h)
  intro n hn
  simpa only [step, map_add] using congrArg (coeff n (X : PowerSeries R) + ·)
    (hc n (by omega))

private theorem approx_stable {d k : ℕ} (h : d ≤ k) :
    Agree d ((step^[d] (0 : PowerSeries R))) ((step^[k] 0)) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => simpa only [Function.iterate_succ_apply'] using step_agree (ih (Nat.le_of_succ_le_succ h))

private noncomputable def solution : PowerSeries R := mk fun n => coeff n ((step^[n+1] (0 : PowerSeries R)))

private theorem solution_agree (d : ℕ) : Agree d (solution (R := R)) ((step^[d] 0)) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approx_stable (R := R) (Nat.succ_le_of_lt hn) n (Nat.lt_succ_self n)

private theorem solution_fixed : solution (R := R) = step solution := by
  ext n
  have hg := solution_agree (R := R) (n+2) n (by omega)
  have hs := step_agree (solution_agree (R := R) (n+1)) n (Nat.lt_succ_of_lt (Nat.lt_succ_self n))
  rw [Function.iterate_succ_apply'] at hg
  exact hg.trans hs.symm

private theorem fixed_unique {f g : PowerSeries R} (hf : f = step f) (hg : g = step g) : f = g := by
  have ha : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hf, ← hg] using step_agree ih
  ext n
  exact ha (n+1) n (Nat.lt_succ_self n)

private theorem solution_map (h : R →+* S) :
    (solution (R := R)).map h = solution (R := S) := by
  apply fixed_unique _ solution_fixed
  have hm := congrArg (PowerSeries.map h) (solution_fixed (R := R))
  simpa only [step, map_add, map_X, map_pow, ← L_map] using hm
end Generic

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

private theorem L_X_geom : (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (X : PowerSeries ℚ) = X * (1-X)⁻¹ := by
  classical
  have hinv : (mk 1 : PowerSeries ℚ) = (1-X)⁻¹ := by
    apply (eq_inv_iff_mul_eq_one (by simp)).mpr
    exact mk_one_mul_one_sub_eq_one ℚ
  rw [← hinv]
  ext m
  cases m with
  | zero => simp
  | succ m =>
    have hr : coeff (m+1) (X * mk 1 : PowerSeries ℚ) = 1 := by
      simp
    rw [hr]
    simp only [coeff_mk]
    rw [Finset.sum_eq_single (m+1)]
    · simp
    · intro n hn hne
      by_cases hd : n ∣ m+1
      · rw [ite_eq_left hd, coeff_X, ite_eq_right]
        intro he
        have heq := Nat.div_mul_cancel hd
        rw [he, one_mul] at heq
        exact hne heq
      · simp [hd]
    · simp

private theorem solution_isA : IsA382318 (solution (R := ℚ)) := by
  refine ⟨?_, solution_fixed⟩
  rw [solution_fixed]
  exact step_zero_constant _

private theorem A_unique {A A' : PowerSeries ℚ} (hA : IsA382318 A) (hA' : IsA382318 A') : A = A' :=
  fixed_unique hA.2 hA'.2

private theorem A_to_B {A : PowerSeries ℚ} (hA : IsA382318 A) : IsA382319 (lambertSum A) := by
  refine ⟨L_zero_constant A, ?_⟩
  change (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) A = X * (1-X)⁻¹ + (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) A)^3)
  conv_lhs => rw [hA.2]
  exact (L_add X (((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) A)^3)).trans (congrArg (· + (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) A)^3)) L_X_geom)

private theorem B_to_A {B : PowerSeries ℚ} (hB : IsA382319 B) :
    IsA382318 (X+B^3) ∧ lambertSum (X+B^3) = B := by
  have hL : lambertSum (X+B^3) = B := by
    change (fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (X+B^3) = B
    rw [L_add, L_X_geom]
    exact hB.2.symm
  refine ⟨⟨by simp [hB.1], ?_⟩, hL⟩
  rw [hL]

private theorem solution_link {A B : PowerSeries ℚ} (hA : IsA382318 A) (hB : IsA382319 B) :
    lambertSum A = B ∧ A = X+B^3 := by
  have h := B_to_A hB
  have he := A_unique hA h.1
  exact ⟨by rw [he]; exact h.2, he⟩

private theorem pair_exists : ∃ A B, IsA382318 A ∧ IsA382319 B :=
  ⟨solution, lambertSum solution, solution_isA, A_to_B solution_isA⟩

private theorem integral_pair {A B : PowerSeries ℚ} (hA : IsA382318 A) (hB : IsA382319 B) :
    A = (solution (R := ℤ)).map (Int.castRingHom ℚ) ∧ B = ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (solution (R := ℤ))).map (Int.castRingHom ℚ) := by
  have hmap := solution_map (Int.castRingHom ℚ)
  have ha : A = (solution (R := ℤ)).map (Int.castRingHom ℚ) := (A_unique hA solution_isA).trans hmap.symm
  refine ⟨ha, ?_⟩
  rw [← (solution_link hA hB).1, ha]
  exact L_map _ _

private theorem integer_equation : (solution (R := ℤ)) = X+((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (solution (R := ℤ)))^3 := solution_fixed

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

private theorem integer_mod_three :
    (solution (R := ℤ)).map (Int.castRingHom (ZMod 3)) =
      X + PowerSeries.map (Int.castRingHom (ZMod 3)) (((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (solution (R := ℤ))).subst (X^3)) := by
  have hm := congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) integer_equation
  simpa only [map_add, map_X,
    D5.S1.Recurrence.Invariants.CubicTernarySubstitutionParity.cube_congr_subst_three] using hm

private theorem residue_multiple (n : ℕ) :
    coeff (3*n) (solution (R := ℤ)) ≡ coeff n ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (solution (R := ℤ))) [ZMOD 3] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
  have hc := congrArg (coeff (3*n)) integer_mod_three
  simpa [coeff_X, coeff_subst_X_pow, show 3*n ≠ 1 by omega] using hc

private theorem residue_other (n : ℕ) (hn : 1 ≤ n) :
    coeff (3*n+1) (solution (R := ℤ)) ≡ 0 [ZMOD 3] ∧ coeff (3*n+2) (solution (R := ℤ)) ≡ 0 [ZMOD 3] := by
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have hc := congrArg (coeff (3*n+1)) integer_mod_three
    have hd : ¬ 3 ∣ 3*n+1 := by omega
    simpa [coeff_X, coeff_subst_X_pow, hd, show n ≠ 0 from Nat.ne_zero_of_lt hn, show 3*n+1 ≠ 1 by omega] using hc
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have hc := congrArg (coeff (3*n+2)) integer_mod_three
    have hd : ¬ 3 ∣ 3*n+2 := by omega
    simpa [coeff_X, coeff_subst_X_pow, hd, show 3*n+2 ≠ 1 by omega] using hc

theorem result : claim := by
  refine ⟨pair_exists, ?_⟩
  intro A B hA hB
  obtain ⟨rfl, rfl⟩ := integral_pair hA hB
  constructor
  · intro n
    exact ⟨coeff (3*n) (solution (R := ℤ)), coeff n ((fun (F : PowerSeries _) => mk fun m => ∑ n ∈ Finset.Icc 1 m, if n ∣ m then coeff (m / n) F else 0) (solution (R := ℤ))), by simp, by simp, residue_multiple n⟩
  · intro n hn
    exact ⟨coeff (3*n+1) (solution (R := ℤ)), coeff (3*n+2) (solution (R := ℤ)),
      by simp, by simp, (residue_other n hn).1, (residue_other n hn).2⟩

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThree
