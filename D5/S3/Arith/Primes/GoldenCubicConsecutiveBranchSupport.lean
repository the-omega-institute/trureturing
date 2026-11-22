/- GID: D5/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Consecutive cubic marking has exact cyclotomic support and simple private branches. -/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport

section Ring
variable {K : Type*} [CommRing K]

def f (x : K) : K := x^3+3*x

def orbit (x : K) : ℕ → K
  | 0 => x
  | n+1 => f (orbit x n)

def jac (x : K) : ℕ → K
  | 0 => 1
  | n+1 => (3*(orbit x n)^2+3)*jac x n

/-- Taylor expansion through first order; the remainder is divisible by
the square of the displacement, also when the coefficient ring is a polynomial ring. -/
private theorem orbit_taylor (x t : K) (n : ℕ) :
    ∃ B : K, orbit (x+t) n = orbit x n + t*jac x n + t^2*B := by
  induction n with
  | zero => exact ⟨0, by simp [orbit,jac]⟩
  | succ n ih =>
    obtain ⟨b,hb⟩ := ih
    rw [orbit,orbit,jac,hb]
    let u := orbit x n
    let v := jac x n
    refine ⟨b*(3*u^2+3) + 3*u*(v+t*b)^2 + t*(v+t*b)^3, ?_⟩
    unfold f
    change (u+t*v+t^2*b)^3+3*(u+t*v+t^2*b) =
      (u^3+3*u)+t*((3*u^2+3)*v)+
        t^2*(b*(3*u^2+3)+3*u*(v+t*b)^2+t*(v+t*b)^3)
    ring

end Ring

variable {K : Type*} [Field K]

private theorem conic_f (x : K) :
    (f x)^2+4=(x^2+4)*(x^2+1)^2 := by unfold f; ring

private theorem marked_maps_to_zero (x : K) (hx : x^2 = -3) : f x = 0 := by
  calc
    f x = x*(x^2+3) := by unfold f; ring
    _ = 0 := by rw [hx]; simp

private theorem forward (x : K) (i j : ℕ) :
    orbit x (i+j)=orbit (orbit x i) j := by
  induction j with
  | zero => simp [orbit]
  | succ j ih => change f (orbit x (i+j)) = f (orbit (orbit x i) j); rw [ih]

private theorem zero_orbit (n : ℕ) : orbit (0 : K) n=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit, ih, f]

private theorem marked_support_disjoint (h3 : (3:K) ≠ 0) (x : K) {i j : ℕ}
    (hi : (orbit x i)^2 = -3) (hj : (orbit x j)^2 = -3) : i=j := by
  have impossible {a b : ℕ} (hlt : a<b) (ha : (orbit x a)^2 = -3)
      (hb : (orbit x b)^2 = -3) : False := by
    obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
    have hz : orbit x (a+1)=0 := marked_maps_to_zero (orbit x a) ha
    rw [hc,forward,hz,zero_orbit,zero_pow (by decide : 2 ≠ 0)] at hb
    exact h3 (neg_eq_zero.mp hb.symm)
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim (impossible h hi hj)
  · exact h
  · exact False.elim (impossible h hj hi)

private theorem no_conic_branch_at_marked (x : K) (i : ℕ)
    (hm : (orbit x i)^2 = -3) : x^2+4 ≠ 0 := by
  intro hx
  have closed (n : ℕ) : (orbit x n)^2+4=0 := by
    induction n with
    | zero => exact hx
    | succ n ih => rw [orbit,conic_f,ih,zero_mul]
  have hc := closed i
  rw [hm] at hc
  have hu : (-3:K)+4=1 := by ring
  exact one_ne_zero (hu.symm.trans hc)

private theorem jac_zero_forces_boundary (h3 : (3:K) ≠ 0) (x : K) (n : ℕ) :
    jac x n = 0 → (orbit x n)^2+4=0 := by
  induction n with
  | zero => intro he; exact False.elim (one_ne_zero he)
  | succ n ih =>
    intro he
    rw [jac] at he
    rw [orbit,conic_f]
    rcases mul_eq_zero.mp he with hh|hh
    · have hz : (orbit x n)^2+1=0 := by
        apply (mul_eq_zero.mp ?_).resolve_left h3
        calc
          (3:K)*((orbit x n)^2+1) = 3*(orbit x n)^2+3 := by ring
          _ = 0 := hh
      rw [hz]; simp
    · rw [ih hh, zero_mul]

private theorem marked_jac_ne_zero (h3 : (3:K) ≠ 0) (x : K) (i : ℕ)
    (hm : (orbit x i)^2 = -3) : jac x i ≠ 0 := by
  intro hz
  have hc := jac_zero_forces_boundary h3 x i hz
  rw [hm] at hc
  have hu : (-3:K)+4=1 := by ring
  exact one_ne_zero (hu.symm.trans hc)

open Polynomial

private theorem eval_orbit_map {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : R) (n : ℕ) :
    g (orbit x n) = orbit (g x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit, f, ih, map_ofNat]

private theorem eval_jac_map {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : R) (n : ℕ) :
    g (jac x n) = jac (g x) n := by
  induction n with
  | zero => exact map_one g
  | succ n ih => simp [jac,eval_orbit_map,ih,map_ofNat]

private theorem marked_linear_coefficient (h3 : (3:K) ≠ 0) (x δ : K) (i : ℕ)
    (hδ : δ^2 = -3) (hm : orbit x i = δ) :
    ((orbit (C x + X : K[X]) i) - C δ).coeff 1 = jac x i ∧
    ((orbit (C x + X : K[X]) i) - C δ).coeff 1 ≠ 0 := by
  obtain ⟨B,hB⟩ := orbit_taylor (C x) (X : K[X]) i
  rw [←eval_orbit_map C x i, ←eval_jac_map C x i, hm] at hB
  rw [hB]
  have ht : C δ + X * C (jac x i) + X ^ 2 * B - C δ =
      X * C (jac x i) + X ^ 2 * B := by ring
  rw [ht]
  have hzero : (X ^ 2 * B).coeff 1 = 0 := by
    simp [pow_two,mul_assoc,coeff_X_mul]
  have hc : (X * C (jac x i)).coeff 1 = jac x i := by rw [coeff_X_mul,coeff_C_zero]
  rw [coeff_add,hzero,add_zero,hc]
  exact ⟨rfl, marked_jac_ne_zero h3 x i (by rw [hm,hδ])⟩

/-- The Fibonacci conic parameter semiconjugates cubing to the cubic
Lucas recurrence. -/
private theorem conic_parameter_cube (a : K) (ha : a ≠ 0) :
    f (a-a⁻¹) = a^3-(a^3)⁻¹ := by
  unfold f
  rw [←inv_pow]
  field_simp [ha]
  ring

private theorem conic_parameter_iterate (a : K) (ha : a ≠ 0) (i : ℕ) :
    orbit (a-a⁻¹) i = a^(3^i)-(a^(3^i))⁻¹ := by
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
    rw [orbit,ih, conic_parameter_cube _ (pow_ne_zero _ ha),pow_succ 3 i,pow_mul]

/-- A marked residue is reached at level i exactly when the squared conic
parameter has exact order 3^(i+1). Written without multiplicative
order hypotheses, so it also applies after arbitrary field extensions. -/
private theorem marked_parameter_exact (h3 : (3:K) ≠ 0) (a : K) (ha : a ≠ 0) (i : ℕ) :
    (orbit (a-a⁻¹) i)^2 = -3 ↔
      (a^2)^(3^(i+1))=1 ∧ (a^2)^(3^i)≠1 := by
  rw [conic_parameter_iterate a ha]
  let b := a^(3^i)
  have hb : b ≠ 0 := pow_ne_zero _ ha
  have h1 : (a^2)^(3^(i+1)) = (b^2)^3 := by
    dsimp [b]
    rw [pow_succ 3 i, pow_mul]
    congr 1
    rw [←pow_mul,←pow_mul,mul_comm]
  have h2 : (a^2)^(3^i) = b^2 := by
    dsimp [b]
    rw [←pow_mul,←pow_mul,mul_comm]
  rw [h1,h2]
  have hc : (b-b⁻¹)^2 = -3 ↔ (b^2)^2+b^2+1 = 0 := by
    constructor
    · intro he
      have hr := congrArg (fun z : K => z*b^2) he
      calc
        ((b^2)^2+b^2+1) = (b-b⁻¹)^2*b^2-(-3)*b^2 := by field_simp [hb]; ring
        _ = 0 := by rw [hr,sub_self]
    · intro he
      apply (mul_right_cancel₀ (pow_ne_zero 2 hb))
      have heq : (b-b⁻¹)^2*b^2-(-3)*b^2 = (b^2)^2+b^2+1 := by
        field_simp [hb]
        ring
      exact sub_eq_zero.mp (heq.trans he)
  rw [hc]
  generalize b^2 = u
  have hf : (u-1)*(u^2+u+1)=u^3-1 := by ring
  constructor
  · intro hz
    refine ⟨sub_eq_zero.mp ?_, ?_⟩
    · rw [←hf,hz,mul_zero]
    · rintro rfl
      exact h3 (by calc
        (3:K) = 1^2+1+1 := by ring
        _ = 0 := hz)
  · rintro ⟨hu,hn⟩
    have hprod : (u-1)*(u^2+u+1)=0 := by rw [hf,hu,sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hn)

section Ring
variable {R : Type*} [CommRing R]

/-- Division-free product of exact primitive 3-power factors on the squared
conic parameter. The recursive fold keeps the word level in the witness. -/
def branchProduct (u : R) : ℕ → R
  | 0 => 1
  | n+1 => branchProduct u n * ((u^(3^n))^2 + u^(3^n) + 1)

private theorem branch_product_telescope (u : R) (k : ℕ) :
    (u-1)*branchProduct u k = u^(3^k)-1 := by
  induction k with
  | zero => simp [branchProduct]
  | succ k ih =>
    rw [branchProduct, ←mul_assoc, ih, pow_succ 3 k, pow_mul]
    ring

/-- Exact finite-length ramification support of the auxiliary consecutive
cubic-label cover, described algebraically on the parameter line. -/
private theorem word_branch_support (h3 : (3:K) ≠ 0) (a : K) (ha : a ≠ 0) (k : ℕ) :
    (∃ i < k, (orbit (a-a⁻¹) i)^2 = -3) ↔
      (a^2)^(3^k)=1 ∧ a^2≠1 := by
  induction k with
  | zero => simp only [Nat.not_lt_zero, false_and, exists_false, pow_zero, pow_one, and_not_self]
  | succ k ih =>
    rw [show (∃ i < k+1, (orbit (a-a⁻¹) i)^2 = -3) ↔
        (∃ i < k, (orbit (a-a⁻¹) i)^2 = -3) ∨
        (orbit (a-a⁻¹) k)^2 = -3 from by
          constructor
          · rintro ⟨i,hi,hm⟩
            rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|heq
            · exact Or.inl ⟨i,hlt,hm⟩
            · exact Or.inr (heq ▸ hm)
          · rintro (⟨i,hi,hm⟩ | hm)
            · exact ⟨i,Nat.lt_succ_of_lt hi,hm⟩
            · exact ⟨k,Nat.lt_succ_self k,hm⟩]
    rw [ih,marked_parameter_exact h3 a ha k]
    constructor
    · rintro (⟨hprev,hbase⟩ | ⟨hnext,hprev⟩)
      · refine ⟨?_,hbase⟩
        rw [pow_succ 3 k,pow_mul,hprev,one_pow]
      · refine ⟨hnext,?_⟩
        intro he
        exact hprev (by rw [he,one_pow])
    · rintro ⟨hnext,hbase⟩
      by_cases hprev : (a^2)^(3^k)=1
      · exact Or.inl ⟨hprev,hbase⟩
      · exact Or.inr ⟨hnext,hprev⟩
end Ring

/-- The squaring coordinate identifies the union of the first k marking
loci as the nontrivial 3^k-torsion; the division-free branch product is
exact, and each marked point is simple and occurs at only one level. -/
theorem consecutive_branch_support (k : ℕ) :
    let D := (3:ℕ)^k
    ∀ {K : Type*} [Field K] (h3 : (3:K) ≠ 0),
      (∀ u : K, (u-1)*branchProduct u k = u^D-1) ∧
      (∀ (a : K) (_ha : a ≠ 0),
        (∃ i < k, (orbit (a-a⁻¹) i)^2 = -3) ↔ (a^2)^D=1 ∧ a^2≠1) ∧
      (∀ (x δ : K) (i j : ℕ) (_hδ : δ^2 = -3)
        (_hi : orbit x i = δ) (_hj : (orbit x j)^2 = -3),
        i=j ∧ x^2+4 ≠ 0 ∧ ((orbit (C x + X : K[X]) i)-C δ).coeff 1 ≠ 0) := by
  intro D K _ h3
  refine ⟨fun u => branch_product_telescope u k, fun a ha => word_branch_support h3 a ha k, ?_⟩
  intro x δ i j hδ hi hj
  have hi' : (orbit x i)^2 = -3 := by rw [hi,hδ]
  exact ⟨marked_support_disjoint h3 x hi' hj, no_conic_branch_at_marked x i hi',
    (marked_linear_coefficient h3 x δ i hδ hi).2⟩

end D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
