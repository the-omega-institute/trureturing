/- GID: D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques
   mirror-E: none(waiver:general-finite-field-structure)
   anchors: []
   utility: none
   digest: Two-dimensional pseudo-Paley cliques are exactly the odd-generator planes. -/

/-
admission_basis: open-problem-resolution (#14878; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14979
escape_witness: none.
chi_eq_Q_pow: proof_shape: bind-only; consumer: affine_infinity_fiber_card_le_one.
pow_char_eq_self_of_pow_sub_one_eq_one: proof_shape: bind-only; consumer: affine_infinity_fiber_card_le_one.
exists_zmod_of_pow_sub_one_eq_one: proof_shape: bind-only; consumer: c_prime_subfield.
same_chi_implies_proportional: proof_shape: bind-only; consumer: equal_projective_class_cross.
dvd_half_mul_iff_even: proof_shape: bind-only; consumer: c_square_iff_even.
q_factor: proof_shape: bind-only; consumer: c_square_iff_even.
c_prime_subfield: proof_shape: bind-only; consumer: c_square_iff_even.
c_square_iff_even: proof_shape: bind-only; consumer: clique_implies_odd_span.
trace_norm_fixed_implies_fixed: proof_shape: bind-only; consumer: infinity_fiber_card_le_one.
quadratic_coeffs_not_all_zero: proof_shape: bind-only; consumer: quadratic_root_card_le.
quadratic_root_card_le: proof_shape: bind-only; consumer: affine_class_fiber_card_le_two.
infinity_fiber_card_le_one: proof_shape: bind-only; consumer: affine_infinity_fiber_card_le_one.
normPoly_pow: proof_shape: bind-only; consumer: cross_eq_iff.
cross_eq_iff: proof_shape: bind-only; consumer: affine_orbits.
infinity_cross_iff: proof_shape: bind-only; consumer: infinity_orbit.
fixed_iff_square_root: proof_shape: bind-only; consumer: projectiveMate_no_fixed_iff.
projectiveMate_no_fixed_iff: proof_shape: bind-only; consumer: nonsquare_class_count.
norm_Q_ne_zero: proof_shape: bind-only; consumer: equal_projective_class_cross.
Q_as_quadratic: proof_shape: bind-only; consumer: affine_class_fiber_card_le_two.
equal_projective_class_cross: proof_shape: bind-only; consumer: affine_class_fiber_card_le_two.
prime_field_fixed: proof_shape: bind-only; consumer: affine_class_fiber_card_le_two.
affine_class_fiber_card_le_two: proof_shape: bind-only; consumer: affine_arbitrary_fiber_card_le_two.
affine_infinity_fiber_card_le_one: proof_shape: bind-only; consumer: projective_fiber_card_le_two.
affine_arbitrary_fiber_card_le_two: proof_shape: bind-only; consumer: projective_fiber_card_le_two.
projective_fiber_card_le_two: proof_shape: bind-only; consumer: clique_all_fibers_two.
exp_factor: proof_shape: bind-only; consumer: neg_one_mem_cyclotomicClass.
pp_adj_iff: proof_shape: bind-only; consumer: isClique_iff_submodule_connection.
cyclotomicClass_neg: proof_shape: bind-only; consumer: connection_neg.
connection_neg: proof_shape: bind-only; consumer: isClique_iff_submodule_connection.
isClique_iff_submodule_connection: proof_shape: bind-only; consumer: class_image_card_le_clique.
neg_one_mem_cyclotomicClass: proof_shape: bind-only; consumer: class_image_card_le_clique.
class_mem_iff: proof_shape: bind-only; consumer: class_image_card_le_clique.
span_pair_of_independent_mem: proof_shape: bind-only; consumer: clique_span_C0.
exists_basis_containing_one: proof_shape: bind-only; consumer: clique_span_C0.
every_fiber_two: proof_shape: bind-only; consumer: clique_all_fibers_two.
image_half_of_pairing: proof_shape: bind-only; consumer: nonsquare_class_count.
projectiveRep_mem: proof_shape: bind-only; consumer: class_image_card_le_clique.
projectiveRep_ne_zero: proof_shape: bind-only; consumer: class_image_card_le_clique.
class_image_card_le_clique: proof_shape: bind-only; consumer: clique_all_fibers_two.
clique_all_fibers_two: proof_shape: bind-only; consumer: clique_implies_odd_span.
clique_span_C0: proof_shape: bind-only; consumer: clique_implies_odd_span.
norm_square_singleton: proof_shape: bind-only; consumer: clique_implies_odd_span.
clique_implies_odd_span: proof_shape: bind-only; consumer: result.
cross_iff_sub_one_powers: proof_shape: bind-only; consumer: same_class_iff_cross.
fixed_iff_sub_one_pow: proof_shape: bind-only; consumer: infinity_orbit.
same_class_iff_cross: proof_shape: bind-only; consumer: affine_orbits.
affine_orbits: proof_shape: bind-only; consumer: projective_orbits.
infinity_orbit: proof_shape: bind-only; consumer: projective_orbits.
projective_orbits: proof_shape: bind-only; consumer: nonsquare_class_count.
nonsquare_class_count: proof_shape: bind-only; consumer: odd_span_implies_clique.
char_targets_injective: proof_shape: bind-only; consumer: clique_from_class_count.
exists_class_index: proof_shape: bind-only; consumer: clique_from_class_count.
chi_prime_scale: proof_shape: bind-only; consumer: clique_from_class_count.
nonzero_span_projective_rep: proof_shape: bind-only; consumer: clique_from_class_count.
clique_from_class_count: proof_shape: bind-only; consumer: odd_span_implies_clique.
generator_nonprime: proof_shape: bind-only; consumer: odd_span_implies_clique.
odd_span_implies_clique: proof_shape: bind-only; consumer: result.
result: proof_shape: bind-only; consumer: none (settling result).
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.PrimeField
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace D5.S3.Combinatorics.PseudoPaley.TwoDimensionalCliques
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
section
variable (p : ℕ) [Fact p.Prime]
noncomputable def chi (x : GaloisField p 4) : GaloisField p 4 := x ^ ((p^2+1)*(p-1))

noncomputable def Q (b t : GaloisField p 4) : GaloisField p 4 := (b + t) ^ (p^2 + 1)

lemma chi_eq_Q_pow (b t : GaloisField p 4) : chi p (b + t) = (Q p b t) ^ (p - 1) := by
  unfold chi Q; rw [← pow_mul]

lemma pow_char_eq_self_of_pow_sub_one_eq_one {x : GaloisField p 4}
    (h : x ^ (p - 1) = 1) : x ^ p = x := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.Prime.one_le Fact.out)
  simpa only [pow_succ, h, one_mul] using congrArg (x ^ ·) hp.symm
private lemma exists_zmod_of_pow_sub_one_eq_one {x : GaloisField p 4} (h : x ^ (p - 1) = 1) : ∃ u : ZMod p,
    algebraMap (ZMod p) (GaloisField p 4) u = x := by
  have hx := (Subfield.mem_bot_iff_pow_eq_self (F := GaloisField p 4) p).2
    (pow_char_eq_self_of_pow_sub_one_eq_one p h)
  rwa [Subfield.bot_eq_of_zMod_algebra p] at hx
private lemma same_chi_implies_proportional (b t s : GaloisField p 4) (ht : Q p b t ≠ 0) (hs : Q p b s ≠ 0) (hchi :
    chi p (b+t) = chi p (b+s)) : ∃ u : ZMod p, u ≠ 0 ∧ Q p b t = algebraMap (ZMod p) (GaloisField p 4) u * Q p b s
    := by
  rw [chi_eq_Q_pow, chi_eq_Q_pow] at hchi
  obtain ⟨u, hu⟩ := exists_zmod_of_pow_sub_one_eq_one p
    (show (Q p b t / Q p b s)^(p-1) = 1 by
      rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hs)]; exact hchi)
  refine ⟨u, ?_, (div_eq_iff hs).mp hu.symm⟩
  intro hz
  exact div_ne_zero ht hs (by simpa only [hz, map_zero] using hu.symm)
private lemma dvd_half_mul_iff_even {q k : ℕ} (hq : 0 < q) (hqeven : Even q) : q ∣ k * (q / 2) ↔ Even k := by
  obtain ⟨r, hr⟩ := hqeven
  have hqdiv : q / 2 = r := by omega
  have hrpos : 0 < r := by omega
  rw [hqdiv, hr]
  constructor
  · intro hd
    apply (even_iff_two_dvd).2
    apply Nat.dvd_of_mul_dvd_mul_right hrpos
    simpa [two_mul, Nat.mul_comm] using hd
  · intro hk
    rcases (even_iff_two_dvd.mp hk) with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    subst k
    ring

omit [Fact p.Prime] in
lemma q_factor (hp : 1 ≤ p) :
    (p - 1) * ((p + 1) * (p^2 + 1)) = p^4 - 1 := by
  have hp4 := Nat.one_le_pow 4 p hp
  zify [hp, hp4]
  ring
private lemma c_prime_subfield (g : GaloisField p 4) (hprim : IsPrimitiveRoot g (p^4-1)) (k : ℕ) : ∃ u : ZMod p,
    algebraMap (ZMod p) (GaloisField p 4) u = (g ^ ((p+1)*k)) ^ (p^2+1) := by
  apply exists_zmod_of_pow_sub_one_eq_one p
  rw [← pow_mul, ← pow_mul]
  have he : (p + 1) * k * ((p ^ 2 + 1) * (p - 1)) = (p ^ 4 - 1) * k := by
    rw [← q_factor p (Nat.Prime.one_le Fact.out)]
    ring
  rw [he, pow_mul, hprim.pow_eq_one, one_pow]

lemma c_square_iff_even (hp2 : p ≠ 2) (g : GaloisField p 4)
    (hprim : IsPrimitiveRoot g (p^4-1)) (k : ℕ) :
    ∃ u : ZMod p,
      algebraMap (ZMod p) (GaloisField p 4) u = (g ^ ((p+1)*k)) ^ (p^2+1) ∧
      (IsSquare u ↔ Even k) := by
  obtain ⟨u, hu⟩ := c_prime_subfield p g hprim k
  have hp1 : 1 ≤ p := Nat.Prime.one_le Fact.out
  have hpgt : 1 < p := Nat.Prime.one_lt Fact.out
  have hMpos : 0 < p^4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by decide) hpgt)
  have hu0 : u ≠ 0 := by
    intro hz
    exact pow_ne_zero _ (pow_ne_zero _ (hprim.ne_zero hMpos.ne'))
      (by simpa only [hz, map_zero] using hu.symm)
  have hqeven := Nat.Prime.even_sub_one Fact.out hp2
  have hhalf : p / 2 = (p-1) / 2 := by
    obtain ⟨r, hr⟩ := Nat.Prime.odd_of_ne_two Fact.out hp2
    omega
  refine ⟨u, hu, ?_⟩
  rw [ZMod.euler_criterion p hu0, hhalf]
  have hbridge : u ^ ((p-1)/2) = 1 ↔
      ((g ^ ((p+1)*k)) ^ (p^2+1)) ^ ((p-1)/2) = 1 := by
    rw [← hu, ← map_pow, ← map_one (algebraMap (ZMod p) (GaloisField p 4))]
    exact (algebraMap (ZMod p) (GaloisField p 4)).injective.eq_iff.symm
  rw [hbridge, ← pow_mul, ← pow_mul, hprim.pow_eq_one_iff_dvd]
  have he : (p+1)*k*((p^2+1)*((p-1)/2)) = ((p+1)*(p^2+1))*(k*((p-1)/2)) := by ring
  rw [he, ← q_factor p hp1]
  have hpos : 0 < (p+1)*(p^2+1) := by positivity
  rw [Nat.mul_comm (p-1), Nat.mul_dvd_mul_iff_left hpos]
  exact dvd_half_mul_iff_even (by omega) hqeven
end
section
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [CharP F p]

lemma trace_norm_fixed_implies_fixed (b : F)
    (hB : (b + b^(p^2))^p = b + b^(p^2))
    (hC : (b * b^(p^2))^p = b * b^(p^2)) : b^p = b := by
  have hsum : b^p + (b^(p^2))^p = b + b^(p^2) := by simpa only [add_pow_char] using hB
  have hprod : b^p * (b^(p^2))^p = b * b^(p^2) := by simpa only [mul_pow] using hC
  have hfactor : (b^p-b) * (b^p-b^(p^2)) = 0 := by linear_combination (b^p) * hsum - hprod
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have h' : b^p = (b^p)^p := by
      calc
        b^p = b^(p^2) := sub_eq_zero.mp h
        _ = (b^p)^p := by rw [pow_two, pow_mul]
    exact ((frobenius F p).injective h').symm
private lemma quadratic_coeffs_not_all_zero (b z : F) (hz : z ≠ 0) (hb : b^p ≠ b) : z^p-z ≠ 0 ∨
    z^p*(b+b^(p^2))-z*(b+b^(p^2))^p ≠ 0 ∨ z^p*(b*b^(p^2))-z*(b*b^(p^2))^p ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hA, hB, hC⟩ := h
  have hzfix : z^p = z := sub_eq_zero.mp hA
  have hBfix : (b+b^(p^2))^p = b+b^(p^2) := by
    have h' := sub_eq_zero.mp hB
    rw [hzfix] at h'
    exact (mul_left_cancel₀ hz h').symm
  have hCfix : (b*b^(p^2))^p = b*b^(p^2) := by
    have h' := sub_eq_zero.mp hC
    rw [hzfix] at h'
    exact (mul_left_cancel₀ hz h').symm
  exact hb (trace_norm_fixed_implies_fixed b hBfix hCfix)
open Polynomial
private lemma quadratic_root_card_le (b z : F) (hz : z ≠ 0) (hb : b^p ≠ b) (S : Finset F) (hS : ∀ t ∈ S, t^p = t ∧
    (t^2+(b+b^(p^2))*t+b*b^(p^2))^p * z = (t^2+(b+b^(p^2))*t+b*b^(p^2)) * z^p) : S.card ≤ 2 := by
  classical
  let A := z^p-z
  let B := z^p*(b+b^(p^2))-z*(b+b^(p^2))^p
  let Cc := z^p*(b*b^(p^2))-z*(b*b^(p^2))^p
  let P : F[X] := Polynomial.C A * X^2 + Polynomial.C B * X + Polynomial.C Cc
  have hP : P ≠ 0 := by
    intro hzero
    have hA : A = 0 := by simpa [P] using congrArg (fun q : F[X] => q.coeff 2) hzero
    have hB : B = 0 := by simpa [P] using congrArg (fun q : F[X] => q.coeff 1) hzero
    have hC : Cc = 0 := by simpa [P] using congrArg (fun q : F[X] => q.coeff 0) hzero
    rcases quadratic_coeffs_not_all_zero b z hz hb with h | h | h
    · exact h hA
    · exact h hB
    · exact h hC
  have hroots : S.val ⊆ P.roots := by
    intro t ht
    have htS : t ∈ S := ht
    obtain ⟨htfix, hteq⟩ := hS t htS
    rw [Polynomial.mem_roots hP]
    change P.eval t = 0
    dsimp [P]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    dsimp [A, B, Cc]
    have he : (t^2+(b+b^(p^2))*t+b*b^(p^2))^p =
        t^2 + (b+b^(p^2))^p*t + (b*b^(p^2))^p := by
      rw [add_pow_char, add_pow_char, mul_pow, ← pow_mul t 2 p]
      rw [Nat.mul_comm 2 p, pow_mul, htfix]
    rw [he] at hteq
    linear_combination -hteq
  exact (Polynomial.card_le_degree_of_subset_roots hroots).trans
    (Polynomial.natDegree_quadratic_le)
private lemma infinity_fiber_card_le_one (b : F) (hb : b^p ≠ b) (S : Finset F) (hS : ∀ t ∈ S, t^p = t ∧
    (t^2+(b+b^(p^2))*t+b*b^(p^2))^p = t^2+(b+b^(p^2))*t+b*b^(p^2)) : S.card ≤ 1 := by
  classical
  let B := (b+b^(p^2))-(b+b^(p^2))^p
  let Cc := (b*b^(p^2))-(b*b^(p^2))^p
  let P : F[X] := Polynomial.C B * X + Polynomial.C Cc
  have hP : P ≠ 0 := by
    intro hzero
    have hB : B = 0 := by simpa [P] using congrArg (fun q : F[X] => q.coeff 1) hzero
    have hC : Cc = 0 := by simpa [P] using congrArg (fun q : F[X] => q.coeff 0) hzero
    have hBfix : (b+b^(p^2))^p = b+b^(p^2) := (sub_eq_zero.mp hB).symm
    have hCfix : (b*b^(p^2))^p = b*b^(p^2) := (sub_eq_zero.mp hC).symm
    exact hb (trace_norm_fixed_implies_fixed b hBfix hCfix)
  have hroots : S.val ⊆ P.roots := by
    intro t ht
    obtain ⟨htfix, hteq⟩ := hS t ht
    rw [Polynomial.mem_roots hP]
    change P.eval t = 0
    dsimp [P]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    dsimp [B, Cc]
    have he : (t^2+(b+b^(p^2))*t+b*b^(p^2))^p =
        t^2 + (b+b^(p^2))^p*t + (b*b^(p^2))^p := by
      rw [add_pow_char, add_pow_char, mul_pow, ← pow_mul t 2 p]
      rw [Nat.mul_comm 2 p, pow_mul, htfix]
    rw [he] at hteq
    linear_combination -hteq
  exact (Polynomial.card_le_degree_of_subset_roots hroots).trans
    (Polynomial.natDegree_linear_le)
end
section
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [CharP F p]

def normPoly (B C t : F) : F := t^2 + B*t + C
private lemma normPoly_pow (B C t : F) (hC : C^p = C) (ht : t^p = t) : (normPoly B C t)^p = t^2+B^p*t+C := by
  unfold normPoly
  rw [add_pow_char, add_pow_char, mul_pow, ← pow_mul t 2 p]
  rw [Nat.mul_comm 2 p, pow_mul, ht, hC]

lemma cross_eq_iff (B C t s : F) (hB : B^p ≠ B) (hC : C^p = C)
    (ht : t^p = t) (hs : s^p = s) :
    (normPoly B C t)^p * normPoly B C s =
        normPoly B C t * (normPoly B C s)^p ↔ t = s ∨ t*s = C := by
  rw [normPoly_pow B C t hC ht, normPoly_pow B C s hC hs]
  have hfactor :
      (t^2+B^p*t+C) * normPoly B C s - normPoly B C t * (s^2+B^p*s+C) =
      -(B^p-B)*(t-s)*(t*s-C) := by unfold normPoly; ring
  rw [← sub_eq_zero, hfactor]
  have hne : -(B^p-B) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr hB)
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hne, false_or, sub_eq_zero]

lemma infinity_cross_iff (B C t : F) (hB : B^p ≠ B) (hC : C^p = C)
    (ht : t^p = t) : (normPoly B C t)^p = normPoly B C t ↔ t = 0 := by
  rw [normPoly_pow B C t hC ht]
  have hfactor : t^2+B^p*t+C - normPoly B C t = (B^p-B)*t := by
    unfold normPoly; ring
  rw [← sub_eq_zero, hfactor, mul_eq_zero]
  simp [sub_ne_zero.mpr hB]
private lemma fixed_iff_square_root (C t : F) (ht : t ≠ 0) : C/t = t ↔ t^2 = C := by
  rw [div_eq_iff ht, eq_comm, pow_two]

-- Infinity exchanges with zero; nonzero t maps to C/t.
noncomputable def projectiveMate (C : F) : Option F → Option F := by
  classical
  exact fun
    | none => some 0
    | some t => if t = 0 then none else some (C/t)

lemma projectiveMate_no_fixed_iff (C : F) (hC : C ≠ 0) :
    (∀ x, projectiveMate C x ≠ x) ↔ ¬ IsSquare C := by
  classical
  constructor
  · intro h hsquare
    obtain ⟨t, ht⟩ := hsquare
    have ht0 : t ≠ 0 := by intro hz; subst t; simp at ht; exact hC ht
    have hdiv : C/t = t := (div_eq_iff ht0).2 ht
    apply h (some t)
    simp [projectiveMate, ht0, hdiv]
  · intro h x
    cases x with
    | none => simp [projectiveMate]
    | some t =>
      by_cases ht : t = 0
      · simp [projectiveMate, ht]
      · intro hfix
        have hdiv : C/t = t := by simpa [projectiveMate, ht] using hfix
        have hroot : t*t = C := by simpa [pow_two] using (fixed_iff_square_root C t ht).mp hdiv
        exact h ⟨t, hroot.symm⟩
end
section
variable (p : ℕ) [Fact p.Prime]
noncomputable section

noncomputable def projectiveClass (b : GaloisField p 4) : Option (ZMod p) → GaloisField p 4
  | none => 1
  | some t => chi p (b + algebraMap (ZMod p) (GaloisField p 4) t)

lemma norm_Q_ne_zero (b : GaloisField p 4) (hb : b^p ≠ b) (t : ZMod p) :
    Q p b (algebraMap (ZMod p) (GaloisField p 4) t) ≠ 0 := by
  apply pow_ne_zero
  intro h
  have hb' : b = -algebraMap (ZMod p) (GaloisField p 4) t := eq_neg_of_add_eq_zero_left h
  apply hb
  rw [hb', ← map_neg, ← map_pow, ZMod.pow_card]

lemma Q_as_quadratic (b : GaloisField p 4) (t : ZMod p) :
    Q p b (algebraMap (ZMod p) (GaloisField p 4) t) =
      (algebraMap (ZMod p) (GaloisField p 4) t)^2 +
      (b+b^(p^2)) * algebraMap (ZMod p) (GaloisField p 4) t + b*b^(p^2) := by
  unfold Q
  rw [pow_add, add_pow_char_pow, ← map_pow, ZMod.pow_card_pow, pow_succ]
  ring

lemma equal_projective_class_cross (b : GaloisField p 4) (hb : b^p ≠ b) (t s : ZMod p)
    (h : projectiveClass p b (some t) = projectiveClass p b (some s)) :
    (Q p b (algebraMap (ZMod p) (GaloisField p 4) t))^p * Q p b (algebraMap (ZMod p) (GaloisField p 4) s) =
      Q p b (algebraMap (ZMod p) (GaloisField p 4) t) *
        (Q p b (algebraMap (ZMod p) (GaloisField p 4) s))^p := by
  obtain ⟨u, hu, hQ⟩ := same_chi_implies_proportional p b _ _
    (norm_Q_ne_zero p b hb t) (norm_Q_ne_zero p b hb s) h
  rw [hQ, mul_pow, ← map_pow, ZMod.pow_card]
  ring

lemma prime_field_fixed (t : ZMod p) :
    (algebraMap (ZMod p) (GaloisField p 4) t)^p = algebraMap (ZMod p) (GaloisField p 4) t := by
  rw [← map_pow, ZMod.pow_card]
private lemma affine_class_fiber_card_le_two (b : GaloisField p 4) (hb : b^p ≠ b) (s : ZMod p) :
    let S := Finset.univ.filter (fun t : ZMod p =>
      projectiveClass p b (some t) = projectiveClass p b (some s))
    S.card ≤ 2 := by
  classical
  intro S
  let f := algebraMap (ZMod p) (GaloisField p 4)
  have hinj : Function.Injective f := (algebraMap (ZMod p) (GaloisField p 4)).injective
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hinj
  rw [← hcard]
  apply quadratic_root_card_le b
    (Q p b (f s)) (norm_Q_ne_zero p b hb s) hb
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have htclass := (Finset.mem_filter.mp ht).2
  refine ⟨prime_field_fixed p t, ?_⟩
  have hcross := equal_projective_class_cross p b hb t s htclass
  change ((f t)^2+(b+b^(p^2))*f t+b*b^(p^2))^p * Q p b (f s) =
    ((f t)^2+(b+b^(p^2))*f t+b*b^(p^2)) * (Q p b (f s))^p
  rw [← Q_as_quadratic p b t]
  exact hcross
private lemma affine_infinity_fiber_card_le_one (b : GaloisField p 4) (hb : b^p ≠ b) :
    let S := Finset.univ.filter (fun t : ZMod p => projectiveClass p b (some t) = 1)
    S.card ≤ 1 := by
  classical
  intro S
  let f := algebraMap (ZMod p) (GaloisField p 4)
  have hinj : Function.Injective f := (algebraMap (ZMod p) (GaloisField p 4)).injective
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hinj
  rw [← hcard]
  apply infinity_fiber_card_le_one b hb
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have htclass := (Finset.mem_filter.mp ht).2
  refine ⟨prime_field_fixed p t, ?_⟩
  have hQpow : (Q p b (f t))^(p-1) = 1 := by simpa only [projectiveClass, chi_eq_Q_pow] using htclass
  have hQfix := pow_char_eq_self_of_pow_sub_one_eq_one p hQpow
  change ((f t)^2+(b+b^(p^2))*f t+b*b^(p^2))^p =
    ((f t)^2+(b+b^(p^2))*f t+b*b^(p^2))
  rw [← Q_as_quadratic p b t]
  exact hQfix
private lemma affine_arbitrary_fiber_card_le_two (b : GaloisField p 4) (hb : b^p ≠ b) (y : GaloisField p 4) :
    (Finset.univ.filter (fun t : ZMod p => projectiveClass p b (some t) = y)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun t : ZMod p => projectiveClass p b (some t) = y)
  by_cases hS : S.Nonempty
  · obtain ⟨s, hs⟩ := hS
    have hsclass := (Finset.mem_filter.mp hs).2
    have hsub : S ⊆ Finset.univ.filter (fun t : ZMod p =>
        projectiveClass p b (some t) = projectiveClass p b (some s)) := by
      intro t ht
      have htclass := (Finset.mem_filter.mp ht).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact htclass.trans hsclass.symm
    exact (Finset.card_le_card hsub).trans (affine_class_fiber_card_le_two p b hb s)
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ 2
    simp [hz]

lemma projective_fiber_card_le_two (b : GaloisField p 4) (hb : b^p ≠ b) (y : GaloisField p 4) :
    (Finset.univ.filter (fun t : Option (ZMod p) => projectiveClass p b t = y)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun t : ZMod p => projectiveClass p b (some t) = y)
  by_cases hy : y = 1
  · have hfilter : Finset.univ.filter (fun t : Option (ZMod p) => projectiveClass p b t = y) =
        S.insertNone := by
      ext t
      cases t <;> simp only [S, projectiveClass, hy, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.none_mem_insertNone, Finset.some_mem_insertNone]
    rw [hfilter, Finset.card_insertNone]
    have hle : S.card ≤ 1 := by simpa only [S, hy] using affine_infinity_fiber_card_le_one p b hb
    omega
  · have hfilter : Finset.univ.filter (fun t : Option (ZMod p) => projectiveClass p b t = y) =
        S.image some := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, S]
      cases t with
      | none => simp only [projectiveClass, Ne.symm hy, Option.some_ne_none, and_false, exists_false]
      | some t => simp only [Option.some.injEq, exists_eq_right]
    rw [hfilter, Finset.card_image_of_injective S (Option.some_injective (ZMod p))]
    exact affine_arbitrary_fiber_card_le_two p b hb y

end
end
section
private lemma exp_factor (p : ℕ) (hp : 1 ≤ p) (he : Even (p-1)) : 2 * ((p-1)/2 * ((p+1)*(p^2+1))) = p^4 -1 := by
  obtain ⟨r, hr⟩ := he
  have hd : (p-1)/2 = r := by omega
  rw [hd, ← q_factor p hp, hr]
  ring
variable (p : ℕ) [Fact p.Prime]

def cyclotomicClass (g : GaloisField p 4) (j : ℕ) : Set (GaloisField p 4) :=
  {x | ∃ m : ℕ, x = g ^ (j + (p + 1) * m)}

def connection (g : GaloisField p 4) (I : Finset ℕ) : Set (GaloisField p 4) :=
  ⋃ j ∈ I, cyclotomicClass p g j

def PP (g : GaloisField p 4) (I : Finset ℕ) : SimpleGraph (GaloisField p 4) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ connection p g I)

def claim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ g : GaloisField p 4, IsPrimitiveRoot g (p ^ 4 - 1) →
    ∀ V : Submodule (ZMod p) (GaloisField p 4),
      Module.finrank (ZMod p) V = 2 → (1 : GaloisField p 4) ∈ V →
      ((∃ I : Finset ℕ, I ⊆ Finset.range (p + 1) ∧ I.card = (p + 1) / 2 ∧
          (PP p g I).IsClique (V : Set (GaloisField p 4))) ↔
        ∃ k : ℕ, Odd k ∧ V = Submodule.span (ZMod p) {1, g ^ ((p + 1) * k)})
private lemma pp_adj_iff (g : GaloisField p 4) (I : Finset ℕ) (x y : GaloisField p 4) : (PP p g I).Adj x y ↔ x ≠ y
    ∧ (y - x ∈ connection p g I ∨ x - y ∈ connection p g I) := Iff.rfl
private lemma cyclotomicClass_neg (g : GaloisField p 4) (j : ℕ) (hneg : -(1 : GaloisField p 4) ∈ cyclotomicClass p
    g 0) {x : GaloisField p 4} (hx : x ∈ cyclotomicClass p g j) : -x ∈ cyclotomicClass p g j := by
  rcases hneg with ⟨m₀, hm₀⟩
  rcases hx with ⟨m, rfl⟩
  refine ⟨m + m₀, ?_⟩
  rw [← neg_one_mul, hm₀, ← pow_add]
  congr 1
  ring
private lemma connection_neg (g : GaloisField p 4) (I : Finset ℕ) (hneg : -(1 : GaloisField p 4) ∈ cyclotomicClass
    p g 0) {x : GaloisField p 4} (hx : x ∈ connection p g I) : -x ∈ connection p g I := by
  simp only [connection, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨j, hj, hx⟩
  exact ⟨j, hj, cyclotomicClass_neg p g j hneg hx⟩
private lemma isClique_iff_submodule_connection (g : GaloisField p 4) (I : Finset ℕ) (hneg : -(1 : GaloisField p 4)
    ∈ cyclotomicClass p g 0) (V : Submodule (ZMod p) (GaloisField p 4)) : (PP p g I).IsClique (V : Set (GaloisField
    p 4)) ↔ ∀ v ∈ (V : Set (GaloisField p 4)), v ≠ 0 → v ∈ connection p g I := by
  constructor
  · intro hcl v hv hv0
    have hadj := hcl hv V.zero_mem hv0
    rw [pp_adj_iff] at hadj
    rcases hadj.2 with h | h
    · have hh := connection_neg p g I hneg h
      simpa using hh
    · simpa using h
  · intro h
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    rw [pp_adj_iff]
    refine ⟨hxy, ?_⟩
    left
    have hmem : y - x ∈ V := V.sub_mem (show y ∈ V from hy) (show x ∈ V from hx)
    exact h (y - x) hmem (sub_ne_zero.mpr hxy.symm)
private lemma neg_one_mem_cyclotomicClass (g : GaloisField p 4) (hp2 : p ≠ 2) (hprim : IsPrimitiveRoot g (p ^ 4 -
    1)) : -(1 : GaloisField p 4) ∈ cyclotomicClass p g 0 := by
  have hpgt : 1 < p := Nat.Prime.one_lt Fact.out
  have heven := Nat.Prime.even_sub_one Fact.out hp2
  let e := (p-1)/2 * ((p+1)*(p^2+1))
  have he : p^4 - 1 = e * 2 := by simpa only [e, Nat.mul_comm 2] using (exp_factor p (by omega) heven).symm
  have hMpos : 0 < p^4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by decide) hpgt)
  have hroot := IsPrimitiveRoot.pow hMpos hprim he
  have hneg := IsPrimitiveRoot.eq_neg_one_of_two_right hroot
  refine ⟨(p-1)/2 * (p^2+1), ?_⟩
  have hexp : 0 + (p+1)*((p-1)/2*(p^2+1)) = e := by dsimp [e]; ring
  rw [hexp, hneg]
private lemma class_mem_iff (g : GaloisField p 4) (hprim : IsPrimitiveRoot g (p^4-1)) {j : ℕ} (hj : j < p+1) {x :
    GaloisField p 4} : x ∈ cyclotomicClass p g j ↔ x ≠ 0 ∧ chi p x = g ^ (j * ((p^2+1)*(p-1))) := by
  letI : Fintype (GaloisField p 4) := Fintype.ofFinite _
  have hpgt : 1 < p := Nat.Prime.one_lt Fact.out
  have hMpos : 0 < p^4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by decide) hpgt)
  letI : NeZero (p^4 - 1) := ⟨hMpos.ne'⟩
  have hM : p^4 - 1 = ((p^2+1)*(p-1))*(p+1) := by rw [← q_factor p (by omega)]; ring
  have hroot := IsPrimitiveRoot.pow hMpos hprim hM
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨pow_ne_zero _ (hprim.ne_zero hMpos.ne'), ?_⟩
    unfold chi
    rw [← pow_mul]
    have he : (j+(p+1)*m)*((p^2+1)*(p-1)) = j*((p^2+1)*(p-1))+(p^4-1)*m := by rw [hM]; ring
    rw [he, pow_add]
    simp only [pow_mul, hprim.pow_eq_one, one_pow, mul_one]
  · rintro ⟨hx0, hchi⟩
    have hcard : Fintype.card (GaloisField p 4) = p^4 := by rw [← Nat.card_eq_fintype_card, GaloisField.card p 4 (by decide)]
    obtain ⟨i, hi, hxi⟩ := hprim.eq_pow_of_pow_eq_one
      (by simpa only [hcard] using FiniteField.pow_card_sub_one_eq_one x hx0)
    have hpow : (g^((p^2+1)*(p-1)))^i = (g^((p^2+1)*(p-1)))^j := by simpa only [chi, ← hxi, ← pow_mul, Nat.mul_comm] using hchi
    have hmod : i % (p+1) = j := hroot.pow_inj (Nat.mod_lt i (by omega)) hj
      ((pow_eq_pow_mod i hroot.pow_eq_one).symm.trans hpow)
    refine ⟨i/(p+1), ?_⟩
    rw [← hxi, ← hmod, Nat.mod_add_div]
private lemma span_pair_of_independent_mem (V : Submodule (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p)
    V = 2) (h1 : (1 : GaloisField p 4) ∈ V) (b : GaloisField p 4) (hbV : b ∈ V) (hb : b^p ≠ b) : V = Submodule.span
    (ZMod p) {1, b} := by
  have hbspan : b ∉ Submodule.span (ZMod p) {(1 : GaloisField p 4)} := by
    intro h
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h
    have hu' : algebraMap (ZMod p) (GaloisField p 4) u = b := by simpa [Algebra.smul_def] using hu
    apply hb
    rw [← hu', ← map_pow, ZMod.pow_card]
  have hdim : Module.finrank (ZMod p) (Submodule.span (ZMod p) {1, b} :
      Submodule (ZMod p) (GaloisField p 4)) = 2 := by
    rw [Submodule.span_insert]
    rw [Submodule.finrank_sup_span_singleton hbspan]
    simp [finrank_span_singleton, one_ne_zero]
  have hle : Submodule.span (ZMod p) {1,b} ≤ V := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | h
    · exact h1
    · have : x = b := Set.mem_singleton_iff.mp h
      simpa [this] using hbV
  exact (Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hV.symm)).symm
private lemma exists_basis_containing_one (V : Submodule (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p)
    V = 2) (h1 : (1 : GaloisField p 4) ∈ V) : ∃ b : GaloisField p 4, b ∈ V ∧ b^p ≠ b ∧ V = Submodule.span (ZMod p)
    {1,b} := by
  let oneV : V := ⟨1, h1⟩
  have h1ne : oneV ≠ 0 := by intro h; have := congrArg Subtype.val h; exact one_ne_zero this
  obtain ⟨bV, hind⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ZMod p) (M := V) (by omega : 1 < Module.finrank (ZMod p) V) h1ne
  let b : GaloisField p 4 := bV.val
  have hb : b^p ≠ b := by
    intro hfix
    have hbot := (Subfield.mem_bot_iff_pow_eq_self (F := GaloisField p 4) p).2 hfix
    rw [Subfield.bot_eq_of_zMod_algebra p] at hbot
    obtain ⟨u, hu⟩ := hbot
    have hdep : (-u) • oneV + (1 : ZMod p) • bV = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, one_smul]
      change (-u) • (1 : GaloisField p 4) + b = 0
      simp only [Algebra.smul_def, map_neg, mul_one]
      rw [hu]
      exact neg_add_cancel b
    have hzero := hind.eq_zero_of_pair hdep
    exact one_ne_zero hzero.2
  exact ⟨b, bV.property, hb, span_pair_of_independent_mem p V hV h1 b bV.property hb⟩
end
namespace Counting
open Finset
private lemma every_fiber_two {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B] (f : A → B) (hbound : ∀ b,
    (univ.filter (fun a => f a = b)).card ≤ 2) (hcount : Fintype.card A = 2 * (univ.image f).card) : ∀ b ∈
    univ.image f, (univ.filter (fun a => f a = b)).card = 2 := by
  have hsum : (∑ b ∈ univ.image f, (univ.filter (fun a => f a = b)).card) =
      ∑ _b ∈ univ.image f, (2 : ℕ) := by
    rw [← Finset.card_eq_sum_card_image f univ, Finset.card_univ, hcount]
    simp [Nat.mul_comm]
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hbound b)).mp hsum
private lemma image_half_of_pairing {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B] (f : A → B) (mate : A
    → A) (hfixed : ∀ x, mate x ≠ x) (hf : ∀ x y, f x = f y ↔ y = x ∨ y = mate x) : Fintype.card A = 2 * (univ.image
    f).card := by
  have hcard : ∀ b ∈ (univ : Finset A).image f,
      (univ.filter (fun a => f a = b)).card = 2 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have hfilter : univ.filter (fun a => f a = f x) = {x, mate x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rw [eq_comm, hf]
    rw [hfilter]
    simp only [Finset.card_pair ((hfixed x).symm)]
  calc
    Fintype.card A = ∑ b ∈ (univ : Finset A).image f,
        (univ.filter (fun a => f a = b)).card := Finset.card_eq_sum_card_image f univ
    _ = ∑ b ∈ (univ : Finset A).image f, 2 := by
      apply Finset.sum_congr rfl
      exact hcard
    _ = 2 * (univ.image f).card := by simp [Nat.mul_comm]
end Counting
section
variable (p : ℕ) [Fact p.Prime]
noncomputable section
open Finset
private def projectiveRep (b : GaloisField p 4) : Option (ZMod p) → GaloisField p 4
  | none => 1
  | some t => b + algebraMap (ZMod p) (GaloisField p 4) t
private lemma projectiveRep_mem (V : Submodule (ZMod p) (GaloisField p 4)) (h1 : (1 : GaloisField p 4) ∈ V) (b :
    GaloisField p 4) (hbV : b ∈ V) (t : Option (ZMod p)) : projectiveRep p b t ∈ V := by
  cases t with
  | none => exact h1
  | some t =>
    apply V.add_mem hbV
    simpa [Algebra.smul_def] using V.smul_mem t h1
private lemma projectiveRep_ne_zero (b : GaloisField p 4) (hb : b^p ≠ b) (t : Option (ZMod p)) : projectiveRep p b
    t ≠ 0 := by
  cases t with
  | none => exact one_ne_zero
  | some t =>
    intro hzero
    apply norm_Q_ne_zero p b hb t
    unfold Q
    change b + algebraMap (ZMod p) (GaloisField p 4) t = 0 at hzero
    rw [hzero]; exact zero_pow (by omega)
private lemma class_image_card_le_clique (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (V :
    Submodule (ZMod p) (GaloisField p 4)) (h1 : (1 : GaloisField p 4) ∈ V) (b : GaloisField p 4) (hbV : b ∈ V) (hb
    : b^p ≠ b) (I : Finset ℕ) (hI : I ⊆ range (p+1)) (hcl : (PP p g I).IsClique (V : Set (GaloisField p 4))) :
    (univ.image (projectiveClass p b)).card ≤ I.card := by
  let T := I.image (fun j => g^(j*((p^2+1)*(p-1))))
  have hconn := (isClique_iff_submodule_connection p g I
    (neg_one_mem_cyclotomicClass p g hp2 hg) V).mp hcl
  have hsub : univ.image (projectiveClass p b) ⊆ T := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hrep := hconn (projectiveRep p b t) (projectiveRep_mem p V h1 b hbV t)
      (projectiveRep_ne_zero p b hb t)
    simp only [connection, Set.mem_iUnion] at hrep
    obtain ⟨j, hj, hrep⟩ := hrep
    have hjlt : j < p+1 := Finset.mem_range.mp (hI hj)
    have hchar := ((class_mem_iff p g hg hjlt).mp hrep).2
    apply Finset.mem_image.mpr
    refine ⟨j, hj, ?_⟩
    exact hchar.symm.trans (by cases t <;> simp only [projectiveClass, projectiveRep, chi, one_pow])
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
private lemma clique_all_fibers_two (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (V :
    Submodule (ZMod p) (GaloisField p 4)) (h1 : (1 : GaloisField p 4) ∈ V) (b : GaloisField p 4) (hbV : b ∈ V) (hb
    : b^p ≠ b) (I : Finset ℕ) (hI : I ⊆ range (p+1)) (hIc : I.card = (p+1)/2) (hcl : (PP p g I).IsClique (V : Set
    (GaloisField p 4))) : ∀ y ∈ univ.image (projectiveClass p b), (univ.filter (fun t => projectiveClass p b t =
    y)).card = 2 := by
  have hupper := class_image_card_le_clique p hp2 g hg V h1 b hbV hb I hI hcl
  have htotal : Fintype.card (Option (ZMod p)) = p+1 := by simp [Fintype.card_option, ZMod.card]
  have hsum := Finset.card_eq_sum_card_image (projectiveClass p b) (univ : Finset (Option (ZMod p)))
  have hsumle : Fintype.card (Option (ZMod p)) ≤
      2 * (univ.image (projectiveClass p b)).card := by
    calc
      Fintype.card (Option (ZMod p)) = ∑ y ∈ univ.image (projectiveClass p b),
          (univ.filter (fun t => projectiveClass p b t = y)).card := hsum
      _ ≤ ∑ y ∈ univ.image (projectiveClass p b), 2 := by
        apply Finset.sum_le_sum
        intro y hy
        exact projective_fiber_card_le_two p b hb y
      _ = 2 * (univ.image (projectiveClass p b)).card := by simp [Nat.mul_comm]
  have hpodd := Nat.Prime.odd_of_ne_two Fact.out hp2
  obtain ⟨r, hr⟩ := hpodd
  have hcount : Fintype.card (Option (ZMod p)) =
      2 * (univ.image (projectiveClass p b)).card := by
    rw [htotal] at hsumle ⊢
    rw [hIc] at hupper
    omega
  exact Counting.every_fiber_two (projectiveClass p b)
    (projective_fiber_card_le_two p b hb) hcount
private lemma clique_span_C0 (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (V : Submodule
    (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p) V = 2) (h1 : (1 : GaloisField p 4) ∈ V) (I : Finset
    ℕ) (hI : I ⊆ range (p+1)) (hIc : I.card = (p+1)/2) (hcl : (PP p g I).IsClique (V : Set (GaloisField p 4))) : ∃
    k : ℕ, (g^((p+1)*k))^p ≠ g^((p+1)*k) ∧ V = Submodule.span (ZMod p) {1,g^((p+1)*k)} := by
  obtain ⟨b, hbV, hb, _⟩ := exists_basis_containing_one p V hV h1
  have htwo := clique_all_fibers_two p hp2 g hg V h1 b hbV hb I hI hIc hcl
  have hmem : (1 : GaloisField p 4) ∈ univ.image (projectiveClass p b) := by exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
  have hcard := htwo 1 hmem
  obtain ⟨t, ht, htne⟩ := Finset.exists_mem_ne (by rw [hcard]; decide) none
  cases t with
  | none => exact (htne rfl).elim
  | some t =>
    let a := b + algebraMap (ZMod p) (GaloisField p 4) t
    have haV : a ∈ V := projectiveRep_mem p V h1 b hbV (some t)
    have ha : a^p ≠ a := by
      intro hafix
      apply hb
      have hafix' : (b+algebraMap (ZMod p) (GaloisField p 4) t)^p = b+algebraMap (ZMod p) (GaloisField p 4) t := hafix
      rw [add_pow_char, prime_field_fixed p t] at hafix'
      exact add_right_cancel hafix'
    have hachi : chi p a = 1 := (Finset.mem_filter.mp ht).2
    have ha0 : a ≠ 0 := projectiveRep_ne_zero p b hb (some t)
    have haC0 : a ∈ cyclotomicClass p g 0 := by
      apply (class_mem_iff p g hg (j := 0) (by omega)).mpr
      exact ⟨ha0, by simpa using hachi⟩
    obtain ⟨k, hk⟩ := haC0
    have hspanA := span_pair_of_independent_mem p V hV h1 a haV ha
    refine ⟨k, ?_, ?_⟩
    · simpa [hk] using ha
    · simpa [hk] using hspanA
private lemma cross_iff_sub_one_powers (x y : GaloisField p 4) (hx : x ≠ 0) (hy : y ≠ 0) : x^p*y=x*y^p ↔
    x^(p-1)=y^(p-1) := by
  have hp : p = p-1+1 := (Nat.sub_add_cancel (Nat.Prime.one_le Fact.out)).symm
  have hxpow : x^p = x^(p-1)*x := by
    calc x^p = x^(p-1+1) := congrArg (x ^ ·) hp
         _ = x^(p-1)*x := pow_succ _ _
  have hypow : y^p = y^(p-1)*y := by
    calc y^p = y^(p-1+1) := congrArg (y ^ ·) hp
         _ = y^(p-1)*y := pow_succ _ _
  rw [hxpow, hypow]
  have he : x^(p-1)*x*y = x*(y^(p-1)*y) ↔ x^(p-1)*(x*y) = y^(p-1)*(x*y) := by
    congr 1 <;> ring
  exact he.trans (mul_left_inj' (mul_ne_zero hx hy))
private lemma fixed_iff_sub_one_pow (x : GaloisField p 4) (hx : x ≠ 0) : x^p=x ↔ x^(p-1)=1 := by
  have he : x^p = x^(p-1)*x := by
    simpa only [pow_succ] using congrArg (x ^ ·)
      (Nat.sub_add_cancel (Nat.Prime.one_le Fact.out)).symm
  rw [he]
  simpa only [one_mul] using (mul_left_inj' hx (a := x^(p-1)) (b := 1))
private lemma same_class_iff_cross (a : GaloisField p 4) (ha : a^p ≠ a) (t s : ZMod p) : projectiveClass p a (some
    t) = projectiveClass p a (some s) ↔ (Q p a (algebraMap (ZMod p) (GaloisField p 4) t))^p * Q p a (algebraMap
    (ZMod p) (GaloisField p 4) s) = Q p a (algebraMap (ZMod p) (GaloisField p 4) t) * (Q p a (algebraMap (ZMod p)
    (GaloisField p 4) s))^p := by
  change chi p (a+_) = chi p (a+_) ↔ _
  rw [chi_eq_Q_pow, chi_eq_Q_pow]
  exact (cross_iff_sub_one_powers p _ _ (norm_Q_ne_zero p a ha t) (norm_Q_ne_zero p a ha s)).symm
private lemma affine_orbits (a : GaloisField p 4) (ha : a^p ≠ a) (u : ZMod p) (hu : algebraMap (ZMod p)
    (GaloisField p 4) u = a^(p^2+1)) (t s : ZMod p) : projectiveClass p a (some t) = projectiveClass p a (some s) ↔
    t=s ∨ t*s=u := by
  let B := a+a^(p^2)
  let C := a*a^(p^2)
  let f := algebraMap (ZMod p) (GaloisField p 4)
  have huC : f u = C := by simpa [C, pow_succ, mul_comm] using hu
  have hCfix : C^p=C := by rw [← huC, ← map_pow, ZMod.pow_card]
  have hBne : B^p ≠ B := by intro h; exact ha (trace_norm_fixed_implies_fixed a h hCfix)
  rw [same_class_iff_cross p a ha t s]
  have hq (t : ZMod p) : Q p a (f t) = normPoly B C (f t) := Q_as_quadratic p a t
  rw [hq, hq, cross_eq_iff B C (f t) (f s) hBne hCfix
    (prime_field_fixed p t) (prime_field_fixed p s)]
  have hinj := (algebraMap (ZMod p) (GaloisField p 4)).injective
  constructor
  · rintro (h | h)
    · exact Or.inl (hinj h)
    · right
      apply hinj
      rw [map_mul]
      exact h.trans huC.symm
  · rintro (h | h)
    · exact Or.inl (congrArg f h)
    · right
      rw [← map_mul, h, huC]
private lemma infinity_orbit (a : GaloisField p 4) (ha : a^p ≠ a) (u : ZMod p) (hu : algebraMap (ZMod p)
    (GaloisField p 4) u = a^(p^2+1)) (t : ZMod p) : projectiveClass p a (some t) = 1 ↔ t=0 := by
  let B := a+a^(p^2)
  let C := a*a^(p^2)
  let f := algebraMap (ZMod p) (GaloisField p 4)
  have huC : f u = C := by simpa [C, pow_succ, mul_comm] using hu
  have hCfix : C^p=C := by rw [← huC, ← map_pow, ZMod.pow_card]
  have hBne : B^p ≠ B := by intro h; exact ha (trace_norm_fixed_implies_fixed a h hCfix)
  change chi p (a+_) = 1 ↔ _
  rw [chi_eq_Q_pow, ← fixed_iff_sub_one_pow p _ (norm_Q_ne_zero p a ha t)]
  have hq : Q p a (f t) = normPoly B C (f t) := Q_as_quadratic p a t
  rw [hq, infinity_cross_iff B C (f t) hBne hCfix (prime_field_fixed p t)]
  exact map_eq_zero_iff f f.injective
private lemma projective_orbits (a : GaloisField p 4) (ha : a^p ≠ a) (u : ZMod p) (hu0 : u ≠ 0) (hu : algebraMap
    (ZMod p) (GaloisField p 4) u = a^(p^2+1)) : ∀ x y, projectiveClass p a x = projectiveClass p a y ↔ y=x ∨
    y=projectiveMate u x := by
  classical
  intro x y
  cases x with
  | none =>
    cases y with
    | none => simp [projectiveClass]
    | some s =>
      change 1 = projectiveClass p a (some s) ↔ _
      rw [eq_comm, infinity_orbit p a ha u hu s]
      simp [projectiveMate]
  | some t =>
    cases y with
    | none =>
      change projectiveClass p a (some t) = 1 ↔ _
      rw [infinity_orbit p a ha u hu t]
      by_cases ht : t=0 <;> simp [projectiveMate, ht]
    | some s =>
      rw [affine_orbits p a ha u hu t s]
      by_cases ht : t=0
      · simp [ht, Ne.symm hu0, projectiveMate, eq_comm]
      · simp only [projectiveMate, ht, ↓reduceIte, Option.some.injEq]
        constructor
        · rintro (h | h)
          · exact Or.inl h.symm
          · right
            apply (eq_div_iff ht).2
            simpa [mul_comm] using h
        · rintro (h | h)
          · exact Or.inl h.symm
          · right
            have hh := (eq_div_iff ht).mp h
            simpa [mul_comm] using hh
private lemma norm_square_singleton (a : GaloisField p 4) (ha : a^p ≠ a) (u r : ZMod p) (hu : algebraMap (ZMod p)
    (GaloisField p 4) u = a^(p^2+1)) (hr : u = r*r) : univ.filter (fun t : Option (ZMod p) => projectiveClass p a t
    = projectiveClass p a (some r)) = {some r} := by
  have ha0 : a ≠ 0 := by
    intro hz
    exact ha (by rw [hz]; exact zero_pow (Nat.Prime.ne_zero Fact.out))
  have hu0 : u ≠ 0 := by
    intro hz
    exact pow_ne_zero _ ha0 (by simpa only [hz, map_zero] using hu.symm)
  have hr0 : r ≠ 0 := by intro hz; apply hu0; simp only [hr, hz, zero_mul]
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [eq_comm, projective_orbits p a ha u hu0 hu (some r) t]
  have hmate : projectiveMate u (some r) = some r := by simp only [projectiveMate, hr0, ↓reduceIte, hr, mul_div_cancel_right₀ r hr0]
  simp only [hmate, or_self]
private lemma clique_implies_odd_span (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (V :
    Submodule (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p) V = 2) (h1 : (1 : GaloisField p 4) ∈ V) (I
    : Finset ℕ) (hI : I ⊆ range (p+1)) (hIc : I.card = (p+1)/2) (hcl : (PP p g I).IsClique (V : Set (GaloisField p
    4))) : ∃ k : ℕ, Odd k ∧ V = Submodule.span (ZMod p) {1,g^((p+1)*k)} := by
  obtain ⟨k, ha, hspan⟩ := clique_span_C0 p hp2 g hg V hV h1 I hI hIc hcl
  refine ⟨k, ?_, hspan⟩
  by_contra hodd
  have heven : Even k := by simpa using hodd
  obtain ⟨u, hu, hparity⟩ := c_square_iff_even p hp2 g hg k
  obtain ⟨r, hr⟩ := hparity.mpr heven
  let a := g^((p+1)*k)
  have haV : a ∈ V := by
    rw [hspan]
    apply Submodule.subset_span
    simp [a]
  have htwo := clique_all_fibers_two p hp2 g hg V h1 a haV ha I hI hIc hcl
  have hmem : projectiveClass p a (some r) ∈ univ.image (projectiveClass p a) :=
    Finset.mem_image.mpr ⟨some r, Finset.mem_univ _, rfl⟩
  have hc := htwo _ hmem
  rw [norm_square_singleton p a ha u r hu hr, Finset.card_singleton] at hc
  omega
private lemma nonsquare_class_count (a : GaloisField p 4) (ha : a^p ≠ a) (u : ZMod p) (hu0 : u ≠ 0) (hu :
    algebraMap (ZMod p) (GaloisField p 4) u = a^(p^2+1)) (hns : ¬ IsSquare u) : (univ.image (projectiveClass p
    a)).card = (p+1)/2 := by
  have hnf := (projectiveMate_no_fixed_iff u hu0).mpr hns
  have hc := Counting.image_half_of_pairing (projectiveClass p a)
    (projectiveMate u)
    hnf (projective_orbits p a ha u hu0 hu)
  have htotal : Fintype.card (Option (ZMod p)) = p+1 := by simp [Fintype.card_option, ZMod.card]
  rw [htotal] at hc
  omega
private lemma char_targets_injective (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) {i j : ℕ} (hi : i <
    p+1) (hj : j < p+1) (h : g^(i*((p^2+1)*(p-1)))=g^(j*((p^2+1)*(p-1)))) : i=j := by
  have hpgt : 1 < p := Nat.Prime.one_lt Fact.out
  have hMpos : 0 < p^4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by decide) hpgt)
  have he : p^4-1 = ((p^2+1)*(p-1))*(p+1) := by rw [← q_factor p (by omega)]; ring
  apply (IsPrimitiveRoot.pow hMpos hg he).pow_inj hi hj
  simpa only [← pow_mul, Nat.mul_comm] using h
private lemma exists_class_index (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (x : GaloisField p 4) (hx :
    x ≠ 0) : ∃ j : ℕ, j < p+1 ∧ x ∈ cyclotomicClass p g j := by
  letI : Fintype (GaloisField p 4) := Fintype.ofFinite _
  have hpgt := Nat.Prime.one_lt (p := p) Fact.out
  have hMne : p^4-1 ≠ 0 := by
    have : 1 < p^4 := Nat.one_lt_pow (by decide) hpgt
    omega
  letI : NeZero (p^4-1) := ⟨hMne⟩
  have hcard : Fintype.card (GaloisField p 4) = p^4 := by rw [← Nat.card_eq_fintype_card, GaloisField.card p 4 (by decide)]
  have hpow : x^(p^4-1)=1 := by simpa [hcard] using FiniteField.pow_card_sub_one_eq_one x hx
  obtain ⟨i, hi, hxi⟩ := hg.eq_pow_of_pow_eq_one hpow
  refine ⟨i%(p+1), Nat.mod_lt i (by omega), i/(p+1), ?_⟩
  calc
    x = g^i := hxi.symm
    _ = g^(i%(p+1)+(p+1)*(i/(p+1))) := by rw [Nat.mod_add_div]
private lemma chi_prime_scale (x : GaloisField p 4) (u : ZMod p) (hu : u ≠ 0) : chi p (algebraMap (ZMod p)
    (GaloisField p 4) u * x) = chi p x := by
  unfold chi
  rw [mul_pow]
  have hpow : (algebraMap (ZMod p) (GaloisField p 4) u)^((p^2+1)*(p-1))=1 := by
    calc
      (algebraMap (ZMod p) (GaloisField p 4) u)^((p^2+1)*(p-1)) =
          ((algebraMap (ZMod p) (GaloisField p 4) u)^(p-1))^(p^2+1) := by
            rw [← pow_mul]
            congr 1
            ring
      _ = 1 := by rw [← map_pow, ZMod.pow_card_sub_one_eq_one hu, map_one, one_pow]
  rw [hpow, one_mul]
private lemma nonzero_span_projective_rep (a : GaloisField p 4) (v : GaloisField p 4) (hv : v ∈ Submodule.span
    (ZMod p) {1,a}) (hv0 : v ≠ 0) : ∃ u : ZMod p, u ≠ 0 ∧ ∃ t : Option (ZMod p), v = algebraMap (ZMod p)
    (GaloisField p 4) u * projectiveRep p a t := by
  obtain ⟨s,t,hst⟩ := Submodule.mem_span_pair.mp hv
  have hst' : algebraMap (ZMod p) (GaloisField p 4) s + algebraMap (ZMod p) (GaloisField p 4) t * a = v := by simpa [Algebra.smul_def] using hst
  by_cases ht : t=0
  · have hs : s ≠ 0 := by
      intro hz
      apply hv0
      simpa [ht,hz] using hst'.symm
    refine ⟨s,hs,none,?_⟩
    simpa [projectiveRep,ht] using hst'.symm
  · refine ⟨t,ht,some (s/t),?_⟩
    change v = algebraMap (ZMod p) (GaloisField p 4) t * (a + algebraMap (ZMod p) (GaloisField p 4) (s/t))
    rw [map_div₀]
    have htmap : algebraMap (ZMod p) (GaloisField p 4) t ≠ 0 := by simpa using ht
    field_simp
    linear_combination -hst'
private lemma clique_from_class_count (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (a :
    GaloisField p 4) (ha : a^p ≠ a) (hcount : (univ.image (projectiveClass p a)).card = (p+1)/2) : ∃ I : Finset ℕ,
    I ⊆ range (p+1) ∧ I.card = (p+1)/2 ∧ (PP p g I).IsClique (Submodule.span (ZMod p) {1,a} : Set (GaloisField p
    4)) := by
  choose idx hi hmem using fun t : Option (ZMod p) =>
    exists_class_index p g hg (projectiveRep p a t) (projectiveRep_ne_zero p a ha t)
  let I : Finset ℕ := univ.image idx
  let w : ℕ → GaloisField p 4 := fun j => g^(j*((p^2+1)*(p-1)))
  have hI : I ⊆ range (p+1) := by
    intro j hj
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hi t)
  have hchar (t : Option (ZMod p)) : w (idx t) = projectiveClass p a t := by
    have h := ((class_mem_iff p g hg (hi t)).mp (hmem t)).2
    exact h.symm.trans (by cases t <;> simp only [projectiveClass, projectiveRep, chi, one_pow])
  have hinj : Set.InjOn w I := by
    intro i hi j hj heq
    exact char_targets_injective p g hg (Finset.mem_range.mp (hI hi))
      (Finset.mem_range.mp (hI hj)) heq
  have himage : I.image w = univ.image (projectiveClass p a) := by
    change (univ.image idx).image w = _
    rw [Finset.image_image]
    congr 1
    funext t
    exact hchar t
  have hIc : I.card=(p+1)/2 := by rw [← Finset.card_image_of_injOn hinj, himage, hcount]
  refine ⟨I,hI,hIc,?_⟩
  apply (isClique_iff_submodule_connection p g I (neg_one_mem_cyclotomicClass p g hp2 hg) _).mpr
  intro v hv hv0
  obtain ⟨u,hu,t,hvt⟩ := nonzero_span_projective_rep p a v hv hv0
  have hvclass : v ∈ cyclotomicClass p g (idx t) := by
    apply (class_mem_iff p g hg (hi t)).mpr
    refine ⟨hv0,?_⟩
    rw [hvt, chi_prime_scale p _ u hu]
    exact ((class_mem_iff p g hg (hi t)).mp (hmem t)).2
  simp only [connection,Set.mem_iUnion]
  exact ⟨idx t, Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩,hvclass⟩
private lemma generator_nonprime (V : Submodule (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p) V=2) (a :
    GaloisField p 4) (hspan : V=Submodule.span (ZMod p) {1,a}) : a^p ≠ a := by
  intro hfix
  have hbot := (Subfield.mem_bot_iff_pow_eq_self (F := GaloisField p 4) p).2 hfix
  rw [Subfield.bot_eq_of_zMod_algebra p] at hbot
  obtain ⟨u,hu⟩ := hbot
  have haspan : a ∈ Submodule.span (ZMod p) {(1 : GaloisField p 4)} := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨u,?_⟩
    simpa [Algebra.smul_def] using hu
  have hcollapse : Submodule.span (ZMod p) {1,a} = Submodule.span (ZMod p) {(1 : GaloisField p 4)} := by
    rw [Set.pair_comm]
    exact Submodule.span_insert_eq_span haspan
  rw [hspan,hcollapse,finrank_span_singleton one_ne_zero] at hV
  omega
private lemma odd_span_implies_clique (hp2 : p ≠ 2) (g : GaloisField p 4) (hg : IsPrimitiveRoot g (p^4-1)) (V :
    Submodule (ZMod p) (GaloisField p 4)) (hV : Module.finrank (ZMod p) V=2) (k : ℕ) (hk : Odd k) (hspan :
    V=Submodule.span (ZMod p) {1,g^((p+1)*k)}) : ∃ I : Finset ℕ, I ⊆ range (p+1) ∧ I.card=(p+1)/2 ∧ (PP p g
    I).IsClique (V : Set (GaloisField p 4)) := by
  let a := g^((p+1)*k)
  have ha := generator_nonprime p V hV a hspan
  obtain ⟨u,hu,hparity⟩ := c_square_iff_even p hp2 g hg k
  have hu0 : u ≠ 0 := by
    intro hzero
    have ha0 : a ≠ 0 := by intro hz; exact ha (by rw [hz]; exact zero_pow (Nat.Prime.ne_zero Fact.out))
    have hz : a^(p^2+1)=0 := by simpa [a,hzero] using hu.symm
    exact pow_ne_zero _ ha0 hz
  have hns : ¬ IsSquare u := by intro hsq; exact Nat.not_even_iff_odd.mpr hk (hparity.mp hsq)
  have hc := nonsquare_class_count p a ha u hu0 hu hns
  obtain ⟨I,hI,hIc,hcl⟩ := clique_from_class_count p hp2 g hg a ha hc
  refine ⟨I,hI,hIc,?_⟩
  simpa [hspan,a] using hcl

theorem result : claim := by
  intro p hp hp2 g hg V hV h1
  constructor
  · rintro ⟨I,hI,hIc,hcl⟩
    exact clique_implies_odd_span p hp2 g hg V hV h1 I hI hIc hcl
  · rintro ⟨k,hk,hspan⟩
    exact odd_span_implies_clique p hp2 g hg V hV k hk hspan
end
end
end D5.S3.Combinatorics.PseudoPaley.TwoDimensionalCliques
