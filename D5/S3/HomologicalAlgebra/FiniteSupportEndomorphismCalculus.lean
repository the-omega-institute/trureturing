/- GID: D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Locally finite anticommutators and basis counting functional calculus. -/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Statewise finite sums and functional calculus of an algebraic basis count. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def ac (A B : Module.End ℂ V) : Module.End ℂ V := A * B + B * A

theorem ac_add_left (A B C : Module.End ℂ V) :
    ac (A + B) C = ac A C + ac B C := by unfold ac; noncomm_ring
theorem ac_add_right (A B C : Module.End ℂ V) :
    ac A (B + C) = ac A B + ac A C := by unfold ac; noncomm_ring
theorem ac_smul_left (z : ℂ) (A B : Module.End ℂ V) :
    ac (z • A) B = z • ac A B := by
  simp [ac, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]
theorem ac_smul_right (z : ℂ) (A B : Module.End ℂ V) :
    ac A (z • B) = z • ac A B := by
  simp [ac, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- A bound is data only after its vanishing assertion has been proved. -/
structure Family (V : Type*) [AddCommGroup V] [Module ℂ V] where
  term : ℕ → Module.End ℂ V
  bound : V → ℕ
  vanish : ∀ v n, bound v ≤ n → term n v = 0

namespace Family
variable (A : Family V)

def value (v : V) : V := ∑ᶠ n, A.term n v

private theorem value_eq_sum (v : V) (N : ℕ) (hN : A.bound v ≤ N) :
    A.value v = ∑ n ∈ Finset.range N, A.term n v := by
  apply finsum_eq_finsetSum_of_support_subset
  intro n hn
  exact Finset.mem_range.mpr (lt_of_not_ge (fun h => hn (A.vanish v n (hN.trans h))))

def total : Module.End ℂ V where
  toFun := A.value
  map_add' v w := by
    let N := max (A.bound (v+w)) (max (A.bound v) (A.bound w))
    rw [A.value_eq_sum (v+w) N (le_max_left _ _),
      A.value_eq_sum v N ((le_max_left _ _).trans (le_max_right _ _)),
      A.value_eq_sum w N ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' z v := by
    let N := max (A.bound (z • v)) (A.bound v)
    rw [A.value_eq_sum (z • v) N (le_max_left _ _),
      A.value_eq_sum v N (le_max_right _ _)]
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

theorem total_eq_sum (v : V) (N : ℕ) (hN : A.bound v ≤ N) :
    A.total v = ∑ n ∈ Finset.range N, A.term n v := A.value_eq_sum v N hN

def trunc (N : ℕ) : Module.End ℂ V := ∑ n ∈ Finset.range N, A.term n

private theorem trunc_apply (N : ℕ) (v : V) :
    A.trunc N v = ∑ n ∈ Finset.range N, A.term n v := by simp [trunc]

private theorem trunc_ac (A B C : Family V)
    (hab : ∀ i j, ac (A.term i) (B.term j) = if i = j then C.term i else 0)
    (N : ℕ) : ac (A.trunc N) (B.trunc N) = C.trunc N := by
  classical
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ac (A.term i) (B.term j) := by
      simp only [ac, trunc, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    _ = C.trunc N := by
      simp [hab, trunc]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [if_pos (Finset.mem_range.mp hi)]

/-- Only finite sums are expanded: N also captures both composed outputs. -/
theorem total_ac (A B C : Family V)
    (hab : ∀ i j, ac (A.term i) (B.term j) = if i = j then C.term i else 0) :
    ac A.total B.total = C.total := by
  classical
  ext v
  let N := max (max (A.bound v) (B.bound v))
    (max (max (A.bound (B.total v)) (B.bound (A.total v))) (C.bound v))
  have ha : A.bound v ≤ N := by dsimp [N]; omega
  have hb : B.bound v ≤ N := by dsimp [N]; omega
  have habv : A.bound (B.total v) ≤ N := by dsimp [N]; omega
  have hbav : B.bound (A.total v) ≤ N := by dsimp [N]; omega
  have hc : C.bound v ≤ N := by dsimp [N]; omega
  change A.total (B.total v) + B.total (A.total v) = C.total v
  rw [A.total_eq_sum _ N habv, B.total_eq_sum _ N hbav,
    B.total_eq_sum v N hb, A.total_eq_sum v N ha, C.total_eq_sum v N hc]
  have h := LinearMap.congr_fun (trunc_ac A B C hab N) v
  simpa only [ac, LinearMap.add_apply, Module.End.mul_apply, trunc_apply] using h

theorem total_square_zero (A : Family V)
    (haa : ∀ i j, ac (A.term i) (A.term j) = 0) : A.total * A.total = 0 := by
  let Z : Family V := ⟨fun _ => 0, fun _ => 0, by intros; rfl⟩
  have h := total_ac A A Z (by intro i j; simpa [Z] using haa i j)
  have hz : Z.total = 0 := by ext v; simp [Z, total, value]
  rw [hz] at h
  have h2 : (2 : ℂ) • (A.total * A.total) = 0 := by simpa [ac, two_smul] using h
  have h' := congrArg (fun T : Module.End ℂ V => (2 : ℂ)⁻¹ • T) h2
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul, smul_zero] using h'

theorem total_ac_fixed (A : Family V) (T : Module.End ℂ V)
    (hT : ∀ i, ac T (A.term i) = 0) : ac T A.total = 0 := by
  ext v
  let N := max (A.bound v) (A.bound (T v))
  change T (A.total v) + A.total (T v) = 0
  rw [A.total_eq_sum v N (le_max_left _ _),
    A.total_eq_sum (T v) N (le_max_right _ _), map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact LinearMap.congr_fun (hT i) v

theorem total_commutes_fixed (A : Family V) (T : Module.End ℂ V)
    (hT : ∀ i, T * A.term i = A.term i * T) : T * A.total = A.total * T := by
  ext v
  let N := max (A.bound v) (A.bound (T v))
  change T (A.total v) = A.total (T v)
  rw [A.total_eq_sum v N (le_max_left _ _),
    A.total_eq_sum (T v) N (le_max_right _ _), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact LinearMap.congr_fun (hT i) v
end Family

/-- Integer regrouping with an explicit finite support witness, including f(0)=0. -/
theorem signed_sum (f : ℤ → V) (hf0 : f 0 = 0) (N : ℕ)
    (hN : ∀ r, N ≤ r → f ((r : ℤ)+1) = 0 ∧ f (-((r : ℤ)+1)) = 0) :
    (∑ᶠ n, f n) = ∑ r ∈ Finset.range N, (f ((r : ℤ)+1) + f (-((r : ℤ)+1))) := by
  classical
  let P := (Finset.range N).image (fun r : ℕ => (r : ℤ)+1)
  let Q := (Finset.range N).image (fun r : ℕ => -((r : ℤ)+1))
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hp hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hq
    omega
  have hs : Function.support f ⊆ (P ∪ Q : Finset ℤ) := by
    intro z hz
    cases z with
    | ofNat n =>
      cases n with
      | zero => exact False.elim (hz hf0)
      | succ r =>
        have hr : r < N := by
          by_contra h
          exact hz (by simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using (hN r (by omega)).1)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.cast_add]⟩)
    | negSucc r =>
      have hr : r < N := by
        by_contra h
        exact hz (by simpa only [Int.negSucc_eq, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using (hN r (by omega)).2)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.cast_add]⟩)
  rw [finsum_eq_finsetSum_of_support_subset f hs, Finset.sum_union hd]
  simp only [P, Q]
  rw [Finset.sum_image (by intro a ha b hb h; exact_mod_cast (add_right_cancel h)),
    Finset.sum_image (by intro a ha b hb h; exact_mod_cast (add_right_cancel (neg_injective h))), Finset.sum_add_distrib]

section Diagonal
variable {I : Type*} (b : Module.Basis I ℂ V)

def diagonal (f : I → ℂ) : Module.End ℂ V := b.constr ℂ (fun i => f i • b i)

@[simp] theorem diagonal_basis (f : I → ℂ) (i : I) :
    diagonal b f (b i) = f i • b i := b.constr_basis _ _ _

theorem diagonal_coefficient (f : I → ℂ) (v : V) (i : I) :
    b.repr (diagonal b f v) i = f i * b.repr v i := by
  classical
  have h : (b.coord i).comp (diagonal b f) = f i • b.coord i := by
    apply b.ext
    intro j
    by_cases h : j = i
    · subst j; simp [Module.Basis.coord_apply]
    · simp [Module.Basis.coord_apply, h, Ne.symm h]
  exact LinearMap.congr_fun h v

def number (q : I → ℕ) : Module.End ℂ V := diagonal b (fun i => (q i : ℂ))
def projectZero (q : I → ℕ) : Module.End ℂ V := diagonal b (fun i => if q i = 0 then 1 else 0)
def inverseNumber (q : I → ℕ) : Module.End ℂ V :=
  diagonal b (fun i => if q i = 0 then 0 else (q i : ℂ)⁻¹)

theorem spectral_identities (q : I → ℕ) :
    number b q * inverseNumber b q = 1 - projectZero b q ∧
    inverseNumber b q * number b q = 1 - projectZero b q ∧
    projectZero b q * projectZero b q = projectZero b q ∧
    number b q * projectZero b q = 0 ∧
    inverseNumber b q * projectZero b q = 0 := by
  repeat' constructor
  all_goals
    apply b.ext
    intro i
    by_cases h : q i = 0
    · simp [number, inverseNumber, projectZero, Module.End.mul_apply, h]
    · have hc : (q i : ℂ) ≠ 0 := by exact_mod_cast h
      simp [number, inverseNumber, projectZero, Module.End.mul_apply, h, hc, smul_smul]

/-- Commuting with the proved number operator implies commuting with its spectral functions. -/
theorem commutes_function (q : I → ℕ) (A : Module.End ℂ V)
    (hA : number b q * A = A * number b q) (f : ℕ → ℂ) :
    diagonal b (fun i => f (q i)) * A = A * diagonal b (fun i => f (q i)) := by
  apply b.ext
  intro i
  apply b.repr.injective
  ext j
  have hij := congrArg (fun v => b.repr v j) (LinearMap.congr_fun hA (b i))
  simp only [Module.End.mul_apply, number, diagonal_basis, map_smul,
    Finsupp.smul_apply, smul_eq_mul, diagonal_coefficient] at hij
  have hz : q j = q i ∨ b.repr (A (b i)) j = 0 := by
    have hm : ((q j : ℂ) - (q i : ℂ)) * b.repr (A (b i)) j = 0 := by
      rw [sub_mul, hij, sub_self]
    rcases mul_eq_zero.mp hm with h | h
    · left; exact_mod_cast sub_eq_zero.mp h
    · exact Or.inr h
  simp only [Module.End.mul_apply, diagonal_basis, map_smul, Finsupp.smul_apply,
    smul_eq_mul, diagonal_coefficient]
  rcases hz with h | h <;> simp [h]

theorem kernel_number_iff (q : I → ℕ) (v : V) :
    number b q v = 0 ↔ ∀ i, q i ≠ 0 → b.repr v i = 0 := by
  constructor
  · intro h i hi
    have hc : (q i : ℂ) ≠ 0 := by exact_mod_cast hi
    have he := congrArg (fun w => b.repr w i) h
    simpa only [number, diagonal_coefficient, map_zero, Finsupp.zero_apply,
      mul_eq_zero, hc, false_or] using he
  · intro h
    apply b.repr.injective
    ext i
    by_cases hi : q i = 0
    · simp [number, diagonal_coefficient, hi]
    · simp [number, diagonal_coefficient, h i hi]
end Diagonal
end D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
