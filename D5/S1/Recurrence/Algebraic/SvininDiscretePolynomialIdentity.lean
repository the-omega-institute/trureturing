/- GID: D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Svinin's discrete-polynomial convolution identity over commutative rings. -/

/- Formalization classification:
   proof_shape: result: content
   escape_witness: mono_pascal, strict_pascal (weighted tuple partitions); Q_boundary (locality).
   admission_basis: open-problem-resolution (#19287; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19360
   Public surface: T, S, bracket, claim, result. Source formulas are unchanged.
   proof_shape: up_monotone: bind-only; consumers: mono_pascal; frozen: none.
   proof_shape: consZero_monotone: bind-only; consumers: mono_pascal; frozen: none.
   proof_shape: mono_pascal: content; consumers: S_left_nat; frozen: none.
   proof_shape: up_strictMono: bind-only; consumers: strictConsZero_strictMono, strict_pascal; frozen: none.
   proof_shape: strictConsZero_strictMono: bind-only; consumers: strict_pascal; frozen: none.
   proof_shape: strict_pascal: content; consumers: T_left_nat; frozen: none.
   proof_shape: local_translation_invariant_zero: content; consumers: Q_boundary; frozen: none.
   proof_shape: sum_step: bind-only; consumers: bracket_shift; frozen: none.
   proof_shape: bracket_correction: bind-only; consumers: bracket_shift, result; frozen: none.
   proof_shape: sum_range_head: bind-only; consumers: bracket_shift; frozen: none.
   proof_shape: bracket_shift: bind-only; consumers: bracket_Q_zero; frozen: none.
   proof_shape: T_zero: bind-only; consumers: bracket_Q_zero; frozen: none.
   proof_shape: S_zero: bind-only; consumers: S_Q_left, S_Q_right, bracket_Q_zero; frozen: none.
   proof_shape: T_vanish: bind-only; consumers: bracket_Q_zero; frozen: none.
   proof_shape: S_nonpositive: bind-only; consumers: Q_boundary; frozen: none.
   proof_shape: reverseTuple_involutive: bind-only; consumers: reverseTuple_monotone, reverseTuple_strictMono, T_reflection, S_reflection; frozen: none.
   proof_shape: reverseTuple_monotone: bind-only; consumers: S_reflection; frozen: none.
   proof_shape: reverseTuple_strictMono: bind-only; consumers: T_reflection; frozen: none.
   proof_shape: int_val_rev: bind-only; consumers: T_reflection, S_reflection; frozen: none.
   proof_shape: T_reflection: bind-only; consumers: T_right; frozen: none.
   proof_shape: S_reflection: bind-only; consumers: S_right; frozen: none.
   proof_shape: T_nat_eq: bind-only; consumers: T_left_nat; frozen: none.
   proof_shape: S_nat_eq: bind-only; consumers: S_left_nat; frozen: none.
   proof_shape: T_left_nat: content; consumers: T_left; frozen: none.
   proof_shape: S_left_nat: content; consumers: S_left; frozen: none.
   proof_shape: T_left: content; consumers: T_right, bracket_Q_zero; frozen: none.
   proof_shape: S_left: content; consumers: S_right, S_Q_left, S_Q_right; frozen: none.
   proof_shape: T_right: content; consumers: bracket_Q_zero; frozen: none.
   proof_shape: S_right: content; consumers: S_Q_left, S_Q_right; frozen: none.
   proof_shape: Q_small: bind-only; consumers: bracket_Q_zero, result; frozen: none.
   proof_shape: Q_spec: bind-only; consumers: bracket_Q_zero, result; frozen: none.
   proof_shape: S_Q_left: content; consumers: Q_boundary, bracket_Q_zero; frozen: none.
   proof_shape: S_Q_right: content; consumers: Q_boundary; frozen: none.
   proof_shape: S_locality: bind-only; consumers: Q_boundary; frozen: none.
   proof_shape: S_zero_field: bind-only; consumers: Q_boundary; frozen: none.
   proof_shape: Q_boundary: content; consumers: bracket_Q_zero; frozen: none.
   proof_shape: bracket_Q_zero: content; consumers: result; frozen: none.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! Binding conventions for A. K. Svinin, "On integrals for some class of ordinary difference equations admitting a Lax
pair representation", arXiv:1505.06394v2 (J. Phys. A 49 (2016) 095201): the discrete polynomials T^r_s(i) (Eq. (4))
and S^r_s(i) (Section 2.3) in the case (h, n) = (1, 1) of Section 3, the binary operation ⟨F, G⟩ of Section 3.4 and
Conjecture 1, Eq. (48). The field `T(i)` is an arbitrary function `u : ℤ → R` into a commutative ring. -/

namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity

open Finset

variable {R : Type} [CommRing R]

/-- Eq. (4) with `(h, n) = (1, 1)`: `T^r_s(i) = Σ_{0 ≤ λ_1 < ⋯ < λ_r ≤ s−1} T(i + λ_1) T(i + λ_2 + 1) ⋯ T(i + λ_r + r − 1)`.
It is `1` for `r = 0` and `0` for `r ≥ 1`, `s ≤ 0`. -/
noncomputable def T (u : ℤ → R) (r : ℕ) (s i : ℤ) : R := by
  classical
  exact ∑ lam ∈ (univ : Finset (Fin r → Fin s.toNat)).filter StrictMono,
    ∏ a : Fin r, u (i + (lam a : ℤ) + (a : ℤ))

/-- Section 2.3 with `(h, n) = (1, 1)`: `S^r_s(i) = Σ_{0 ≤ λ_1 ≤ ⋯ ≤ λ_r ≤ s−1} T(i + λ_1 + r − 1) ⋯ T(i + λ_{r−1} + 1)
T(i + λ_r)`. It is `1` for `r = 0` and `0` for `r ≥ 1`, `s ≤ 0`. -/
noncomputable def S (u : ℤ → R) (r : ℕ) (s i : ℤ) : R := by
  classical
  exact ∑ lam ∈ (univ : Finset (Fin r → Fin s.toNat)).filter Monotone,
    ∏ a : Fin r, u (i + (lam a : ℤ) + ((r : ℤ) - 1 - (a : ℤ)))

/-- The binary operation of Section 3.4: `⟨F, G⟩^r_s(i) = Σ_{j=0}^{r} (−1)^j F^{r−j}_{s+j}(i) G^j_{s−r+j}(i + r − j)`. -/
def bracket (F G : ℕ → ℤ → ℤ → R) (r : ℕ) (s i : ℤ) : R :=
  ∑ j ∈ range (r + 1), (-1) ^ j * F (r - j) (s + j) i * G j (s - r + j) (i + r - j)

/-- Conjecture 1, Eq. (48): for every `r ≥ 1` and `s ≥ r − 1`,
`⟨S, T⟩^r_s(i) = Σ_{j=0}^{r−2} (−1)^j T(i + r − j − 2) T(i + s + j) S^{r−j−2}_{s+j+2}(i) T^j_{s−r+j}(i + r − j)`. -/
def claim : Prop :=
  ∀ (R : Type) [CommRing R] (u : ℤ → R) (r : ℕ), 1 ≤ r → ∀ s : ℤ, (r : ℤ) - 1 ≤ s → ∀ i : ℤ,
    bracket (S u) (T u) r s i =
      ∑ j ∈ range (r - 1), (-1) ^ j * u (i + r - j - 2) * u (i + s + j) *
        S u (r - j - 2) (s + j + 2) i * T u j (s - r + j) (i + r - j)

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


open Finset
namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
variable {R : Type} [CommRing R]

private noncomputable def monoSum (r s : ℕ) (w : ℕ → ℕ → R) : R := by
  classical
  exact ∑ lam ∈ (univ : Finset (Fin r → Fin s)).filter Monotone,
    ∏ a : Fin r, w a (lam a)

private lemma up_monotone {r s : ℕ} (lam : Fin r → Fin s) :
    Monotone ((fun a => (lam a).succ)) ↔ Monotone lam := by
  constructor <;> intro h a b hab <;> simpa using h hab

private lemma consZero_monotone {r s : ℕ} (lam : Fin r → Fin (s + 1)) :
    Monotone (Fin.cons 0 lam) ↔ Monotone lam := by
  simpa only [monotone_iff_forall_lt, Relator.LiftFun, Fin.zero_le, implies_true,
    forall_const, true_and] using
    (Fin.liftFun_cons (α := Fin (s + 1)) (n := r) (· ≤ ·) (f := lam) (a := 0))

private theorem mono_pascal (r s : ℕ) (w : ℕ → ℕ → R) :
    monoSum (r + 1) (s + 1) w =
      monoSum (r + 1) s (fun a k => w a (k + 1)) +
        w 0 0 * monoSum r (s + 1) (fun a k => w (a + 1) k) := by
  classical
  let A := (univ : Finset (Fin (r + 1) → Fin (s + 1))).filter Monotone
  let f := fun lam : Fin (r + 1) → Fin (s + 1) => ∏ a : Fin (r + 1), w a (lam a)
  have hz : (∑ lam ∈ A.filter (fun lam => lam 0 = 0), f lam) =
      w 0 0 * monoSum r (s + 1) (fun a k => w (a + 1) k) := by
    unfold monoSum
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_bij (fun lam _ => (Fin.cons 0 lam : Fin (r + 1) → Fin (s + 1)))
    · intro lam hm
      simp only [mem_filter, mem_univ, true_and, A]
      exact ⟨consZero_monotone lam |>.mpr (mem_filter.mp hm).2, by simp⟩
    · intro a ha b hb hab
      funext k
      exact congrFun hab k.succ
    · intro lam hm
      refine ⟨fun a => lam a.succ, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        intro a b hab
        exact (mem_filter.mp (mem_filter.mp hm).1).2 (Fin.succ_le_succ_iff.mpr hab)
      · funext a
        cases a using Fin.cases with
        | zero => exact (mem_filter.mp hm).2.symm
        | succ a => rfl
    · intro lam hm
      simp [f, Fin.prod_univ_succ]
  have hp : (∑ lam ∈ A.filter (fun lam => lam 0 ≠ 0), f lam) =
      monoSum (r + 1) s (fun a k => w a (k + 1)) := by
    unfold monoSum
    symm
    apply Finset.sum_bij (fun lam _ => (fun a => (lam a).succ))
    · intro lam hm
      simp only [mem_filter, mem_univ, true_and, A]
      exact ⟨up_monotone lam |>.mpr (mem_filter.mp hm).2, by simp⟩
    · intro a ha b hb hab
      funext k
      exact Fin.succ_injective _ (congrFun hab k)
    · intro lam hm
      have mono : Monotone lam := (mem_filter.mp (mem_filter.mp hm).1).2
      have positive (a : Fin (r + 1)) : lam a ≠ 0 := by
        have h := mono (Fin.zero_le a)
        have hn := (mem_filter.mp hm).2
        intro he
        rw [he] at h
        exact hn (le_antisymm h (Fin.zero_le _))
      refine ⟨fun a => (lam a).pred (positive a), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        intro a b hab
        have h := mono hab
        apply Fin.succ_le_succ_iff.mp
        simpa using h
      · funext a
        simp
    · intro lam hm
      rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun lam => lam 0 = 0) f
  change (∑ lam ∈ A, f lam) = _
  rw [← hsplit, hz, hp]
  exact add_comm _ _

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private noncomputable def strictSum (r s : ℕ) (w : ℕ → ℕ → R) : R := by
  classical
  exact ∑ lam ∈ (univ : Finset (Fin r → Fin s)).filter StrictMono,
    ∏ a : Fin r, w a (lam a)

private lemma up_strictMono {r s : ℕ} (lam : Fin r → Fin s) :
    StrictMono ((fun a => (lam a).succ)) ↔ StrictMono lam := by
  constructor <;> intro h a b hab <;> simpa using h hab

private lemma strictConsZero_strictMono {r s : ℕ} (lam : Fin r → Fin s) :
    StrictMono (Fin.cons 0 (fun a => (lam a).succ)) ↔ StrictMono lam := by
  simpa [Fin.strictMono_cons] using up_strictMono lam

private theorem strict_pascal (r s : ℕ) (w : ℕ → ℕ → R) :
    strictSum (r + 1) (s + 1) w =
      strictSum (r + 1) s (fun a k => w a (k + 1)) +
        w 0 0 * strictSum r s (fun a k => w (a + 1) (k + 1)) := by
  classical
  let A := (univ : Finset (Fin (r + 1) → Fin (s + 1))).filter StrictMono
  let f := fun lam : Fin (r + 1) → Fin (s + 1) => ∏ a : Fin (r + 1), w a (lam a)
  have hz : (∑ lam ∈ A.filter (fun lam => lam 0 = 0), f lam) =
      w 0 0 * strictSum r s (fun a k => w (a + 1) (k + 1)) := by
    unfold strictSum
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_bij (fun lam _ => Fin.cons 0 (fun a => (lam a).succ))
    · intro lam hm
      simp only [mem_filter, mem_univ, true_and, A]
      exact ⟨strictConsZero_strictMono lam |>.mpr (mem_filter.mp hm).2,
        by simp⟩
    · intro a ha b hb hab
      funext k
      exact Fin.succ_injective _ (congrFun hab k.succ)
    · intro lam hm
      have mono : StrictMono lam := (mem_filter.mp (mem_filter.mp hm).1).2
      have hz := (mem_filter.mp hm).2
      have positive (a : Fin r) : lam a.succ ≠ 0 := by
        have h := mono (show (0 : Fin (r + 1)) < a.succ from Fin.succ_pos a)
        rw [hz] at h
        exact ne_of_gt h
      refine ⟨fun a => (lam a.succ).pred (positive a), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        intro a b hab
        have h := mono (Fin.succ_lt_succ_iff.mpr hab)
        exact Fin.succ_lt_succ_iff.mp (by simpa using h)
      · funext a
        cases a using Fin.cases with
        | zero => exact hz.symm
        | succ a => simp
    · intro lam hm
      simp [f, Fin.prod_univ_succ]
  have hp : (∑ lam ∈ A.filter (fun lam => lam 0 ≠ 0), f lam) =
      strictSum (r + 1) s (fun a k => w a (k + 1)) := by
    unfold strictSum
    symm
    apply Finset.sum_bij (fun lam _ => (fun a => (lam a).succ))
    · intro lam hm
      simp only [mem_filter, mem_univ, true_and, A]
      exact ⟨up_strictMono lam |>.mpr (mem_filter.mp hm).2, by simp⟩
    · intro a ha b hb hab
      funext k
      exact Fin.succ_injective _ (congrFun hab k)
    · intro lam hm
      have mono : StrictMono lam := (mem_filter.mp (mem_filter.mp hm).1).2
      have positive (a : Fin (r + 1)) : lam a ≠ 0 := by
        have h := mono.monotone (Fin.zero_le a)
        have hn := (mem_filter.mp hm).2
        intro he
        rw [he] at h
        exact hn (le_antisymm h (Fin.zero_le _))
      refine ⟨fun a => (lam a).pred (positive a), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        intro a b hab
        have h := mono hab
        exact Fin.succ_lt_succ_iff.mp (by simpa using h)
      · funext a
        simp
    · intro lam hm
      rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun lam => lam 0 = 0) f
  change (∑ lam ∈ A, f lam) = _
  rw [← hsplit, hz, hp]
  exact add_comm _ _

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity

/-- A local function of a doubly infinite field which is invariant under moving the
observation window is its value on the zero field. -/
private theorem local_translation_invariant_zero {R A : Type*} [Zero R] [Zero A]
    (F : (ℤ → R) → ℤ → A) (width : ℕ)
    (locality : ∀ (u v : ℤ → R) (i : ℤ), (∀ (k : ℤ), i ≤ k → k ≤ i + (width : ℤ) → u k = v k) → F u i = F v i)
    (shift : ∀ u i, F u (i + 1) = F u i)
    (zero_field : ∀ i, F (fun _ => 0) i = 0) : ∀ u i, F u i = 0 := by
  have iterate (u : ℤ → R) (i : ℤ) (n : ℕ) : F u (i + n) = F u i := by
    simpa only [mul_one] using
      (Function.Periodic.nat_mul (f := F u) (c := (1 : ℤ)) (shift u) n i)
  intro u i
  let v : ℤ → R := fun k => if k ≤ i + width then u k else 0
  have agree : F u i = F v i := by
    apply locality
    intro k hlow hhigh
    simp [v, hhigh]
  have vanish : F v (i + (width + 1 : ℕ)) = F (fun _ => 0) (i + (width + 1 : ℕ)) := by
    apply locality
    intro k hlow hhigh
    have hk : ¬ k ≤ i + width := by omega
    simp [v, hk]
  rw [agree, ← iterate v i (width + 1), vanish, zero_field]

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private def correction (u : ℤ → R) (S T : ℕ → ℤ → ℤ → R) (r : ℕ) (s i : ℤ) : R :=
  ∑ j ∈ range (r - 1), (-1) ^ j * u (i + r - j - 2) * u (i + s + j) *
    S (r - j - 2) (s + j + 2) i * T j (s - r + j) (i + r - j)

private lemma sum_step (n : ℕ) (a b c : ℕ → R)
    (h0 : a 0 = b 0) (hs : ∀ j < n, a (j + 1) = b (j + 1) - c j) :
    (∑ j ∈ range (n + 1), a j) =
      (∑ j ∈ range (n + 1), b j) - ∑ j ∈ range n, c j := by
  rw [sum_range_succ', sum_range_succ', h0]
  rw [show (∑ j ∈ range n, a (j + 1)) =
    ∑ j ∈ range n, (b (j + 1) - c j) from
      sum_congr rfl (fun j hj => hs j (mem_range.mp hj))]
  rw [sum_sub_distrib]
  ring

private theorem bracket_correction (u : ℤ → R) (S T Q : ℕ → ℤ → ℤ → R)
    (small : ∀ p, p ≤ 1 → ∀ s i, Q p s i = S p s i)
    (spec : ∀ p, 2 ≤ p → ∀ s i,
      Q p s i = S p s i - u (i + p - 2) * u (i + s) * S (p - 2) (s + 2) i)
    (r : ℕ) (s i : ℤ) :
    bracket S T r s i = bracket Q T r s i + correction u S T r s i := by
  classical
  unfold bracket correction
  have hsub : range (r - 1) ⊆ range (r + 1) := range_mono (by omega)
  have hcut : (∑ j ∈ range (r + 1),
      ((-1) ^ j * S (r - j) (s + j) i * T j (s - r + j) (i + r - j) -
       (-1) ^ j * Q (r - j) (s + j) i * T j (s - r + j) (i + r - j))) =
      ∑ j ∈ range (r - 1),
        ((-1) ^ j * S (r - j) (s + j) i * T j (s - r + j) (i + r - j) -
         (-1) ^ j * Q (r - j) (s + j) i * T j (s - r + j) (i + r - j)) := by
    symm
    apply sum_subset hsub
    intro j hj hnot
    have hjn : r - j ≤ 1 := by simp only [mem_range] at hj hnot; omega
    rw [small (r - j) hjn]
    ring
  have heq : (∑ j ∈ range (r - 1),
        ((-1) ^ j * S (r - j) (s + j) i * T j (s - r + j) (i + r - j) -
         (-1) ^ j * Q (r - j) (s + j) i * T j (s - r + j) (i + r - j))) =
      ∑ j ∈ range (r - 1), (-1) ^ j * u (i + r - j - 2) * u (i + s + j) *
        S (r - j - 2) (s + j + 2) i * T j (s - r + j) (i + r - j) := by
    apply sum_congr rfl
    intro j hj
    have hjn : 2 ≤ r - j := by simp only [mem_range] at hj; omega
    rw [spec (r - j) hjn]
    have hidx : i + ((r - j : ℕ) : ℤ) - 2 = i + r - j - 2 := by omega
    rw [hidx]
    have hidx2 : i + (s + j) = i + s + j := (Int.add_assoc i s j).symm
    rw [hidx2]
    ring
  have hh := hcut.trans heq
  rw [sum_sub_distrib] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private lemma sum_range_head (n : ℕ) (hn : 1 ≤ n) (f : ℕ → R) :
    (∑ j ∈ range n, f j) = f 0 + ∑ j ∈ range (n - 1), f (j + 1) := by
  have he : n = (n - 1) + 1 := (Nat.sub_eq_iff_eq_add hn).mp rfl
  conv_lhs => rw [he, sum_range_succ']
  ring

private theorem bracket_shift (u : ℤ → R) (S T Q : ℕ → ℤ → ℤ → R)
    (tzero : ∀ s i, T 0 s i = 1)
    (szero : ∀ s i, S 0 s i = 1)
    (small : ∀ p, p ≤ 1 → ∀ s i, Q p s i = S p s i)
    (spec : ∀ p, 2 ≤ p → ∀ s i,
      Q p s i = S p s i - u (i + p - 2) * u (i + s) * S (p - 2) (s + 2) i)
    (tleft : ∀ p t, 0 ≤ t → ∀ a,
      T (p + 1) (t + 1) a = T (p + 1) t (a + 1) + u a * T p t (a + 2))
    (tright : ∀ p t, 0 ≤ t → ∀ a,
      T (p + 1) (t + 1) a = T (p + 1) t a + u (a + t + p) * T p t a)
    (sq : ∀ p t, 0 ≤ t → ∀ a,
      S (p + 1) (t + 1) a = Q (p + 1) t (a + 1) + u (a + p) * S p (t + 2) a)
    (r : ℕ) (hr : 1 ≤ r) (s : ℤ) (hs : (r : ℤ) ≤ s) (i : ℤ) :
    bracket Q T r s i = bracket Q T r (s - 1) (i + 1) := by
  classical
  let A (j : ℕ) : R := (-1) ^ j * S (r - j) (s + j) i *
    T j (s - r + j - 1) (i + r - j + 1)
  let E (j : ℕ) : R := (-1) ^ j * u (i + r - j - 1) *
    S (r - j - 1) (s + j + 1) i * T j (s - r + j - 1) (i + r - j + 1)
  let F (j : ℕ) : R := (-1) ^ j * u (i + r - j - 1) *
    S (r - j - 1) (s + j + 1) i * T j (s - r + j) (i + r - j + 1)
  let P (j : ℕ) : R := (-1) ^ j * Q (r - j) (s - 1 + j) (i + 1) *
    T j (s - 1 - r + j) (i + 1 + r - j)
  have first : bracket S T r s i = (∑ j ∈ range (r + 1), A j) - ∑ j ∈ range r, F j := by
    unfold bracket
    apply sum_step r _ A F
    · simp [A, tzero]
    · intro j hj
      have ht := tleft j (s - r + j) (by omega) (i + r - j - 1)
      have ht' : T (j + 1) (s - r + (j + 1 : ℕ)) (i + r - (j + 1 : ℕ)) =
          T (j + 1) (s - r + (j + 1 : ℕ) - 1) (i + r - (j + 1 : ℕ) + 1) +
          u (i + r - j - 1) * T j (s - r + j) (i + r - j + 1) := by
        convert ht using 2
        all_goals repeat' first | omega | congr 1
      dsimp only [A, F]
      rw [ht', pow_succ]
      have hp : s + ((j + 1 : ℕ) : ℤ) = s + j + 1 := by omega
      have hn : r - (j + 1) = r - j - 1 := Nat.sub_add_eq r j 1
      rw [hp, hn]
      ring
  have second : (∑ j ∈ range (r + 1), A j) =
      bracket Q T r (s - 1) (i + 1) + ∑ j ∈ range r, E j := by
    have hp : ∀ j < r, A j = P j + E j := by
      intro j hj
      have he : r - j = (r - j - 1) + 1 := by omega
      have hh := sq (r - j - 1) (s + j - 1) (by omega) i
      have hh' : S (r - j) (s + j) i =
          Q (r - j) (s - 1 + j) (i + 1) +
          u (i + r - j - 1) * S (r - j - 1) (s + j + 1) i := by
        convert hh using 2
        all_goals repeat' first | omega | congr 1
      dsimp only [A, P, E]
      rw [hh']
      have ht : s - r + (j : ℤ) - 1 = s - 1 - r + j := by omega
      have hi : i + (r : ℤ) - j + 1 = i + 1 + r - j := by omega
      rw [ht, hi]
      ring
    have last : A r = P r := by
      dsimp [A, P]
      simp only [Nat.sub_self]
      rw [small 0 (by omega)]
      simp [szero]
    change (∑ j ∈ range (r + 1), A j) =
      (∑ j ∈ range (r + 1), P j) + ∑ j ∈ range r, E j
    rw [sum_range_succ, sum_range_succ, last]
    rw [show (∑ j ∈ range r, A j) = ∑ j ∈ range r, (P j + E j) from
      sum_congr rfl (fun j hj => hp j (mem_range.mp hj))]
    rw [sum_add_distrib]
    ring
  have third : (∑ j ∈ range r, E j) - (∑ j ∈ range r, F j) =
      correction u S T r s i := by
    rw [← sum_sub_distrib, sum_range_head r hr]
    have h0 : E 0 - F 0 = 0 := by simp [E, F, tzero]
    rw [h0, zero_add]
    unfold correction
    apply sum_congr rfl
    intro j hj
    have hjn : j + 1 < r := by simp only [mem_range] at hj; omega
    have ht := tright j (s - r + j) (by omega) (i + r - j)
    have ht' : T (j + 1) (s - r + (j + 1 : ℕ)) (i + r - (j + 1 : ℕ) + 1) =
        T (j + 1) (s - r + (j + 1 : ℕ) - 1) (i + r - (j + 1 : ℕ) + 1) +
        u (i + s + j) * T j (s - r + j) (i + r - j) := by
      convert ht using 2
      all_goals repeat' first | omega | congr 1
    dsimp only [E, F]
    rw [ht', pow_succ]
    have hidx : i + (r : ℤ) - ((j + 1 : ℕ) : ℤ) - 1 = i + r - j - 2 := by omega
    have hsidx : s + ((j + 1 : ℕ) : ℤ) + 1 = s + j + 2 := by omega
    have hd : r - (j + 1) - 1 = r - j - 2 := (Nat.sub_succ' (r - j) 1).symm
    rw [hidx, hsidx, hd]
    ring
  have hmain : bracket S T r s i = bracket Q T r (s - 1) (i + 1) + correction u S T r s i := by
    rw [first, second, add_sub_assoc, third]
  exact add_right_cancel ((bracket_correction u S T Q small spec r s i).symm.trans hmain)

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity

open Finset
variable {R : Type} [CommRing R]

@[simp] private theorem T_zero (u : ℤ → R) (s i : ℤ) : T u 0 s i = 1 := by
  classical
  have h (lam : Fin 0 → Fin s.toNat) : StrictMono lam := Subsingleton.strictMono lam
  simp [T, h]

@[simp] private theorem S_zero (u : ℤ → R) (s i : ℤ) : S u 0 s i = 1 := by
  classical
  have h (lam : Fin 0 → Fin s.toNat) : Monotone lam := Subsingleton.monotone lam
  simp [S, h]

private theorem T_vanish (u : ℤ → R) {r : ℕ} {s : ℤ} (h : s < (r : ℤ)) (i : ℤ)
    (hr : 0 < r) : T u r s i = 0 := by
  classical
  unfold T
  apply Finset.sum_eq_zero
  intro lam hmem
  have hm : StrictMono lam := (Finset.mem_filter.mp hmem).2
  have hc := Fintype.card_le_of_injective lam hm.injective
  simp only [Fintype.card_fin] at hc
  have : s.toNat < r := (Int.toNat_lt' hr).mpr h
  omega

private theorem S_nonpositive (u : ℤ → R) {r : ℕ} {s : ℤ} (hr : 0 < r)
    (hs : s ≤ 0) (i : ℤ) : S u r s i = 0 := by
  classical
  unfold S
  apply Finset.sum_eq_zero
  intro lam hm
  have h := (lam (⟨0, hr⟩ : Fin r)).isLt
  omega

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private lemma reverseTuple_involutive {r s : ℕ} (lam : Fin r → Fin s) :
    Equiv.arrowCongr Fin.revPerm Fin.revPerm (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam) = lam := by
  exact (Equiv.eq_symm_apply (Equiv.arrowCongr Fin.revPerm Fin.revPerm)).mp rfl

private lemma reverseTuple_monotone {r s : ℕ} (lam : Fin r → Fin s) :
    Monotone (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam) ↔ Monotone lam := by
  have forward (f : Fin r → Fin s) (h : Monotone f) : Monotone (Equiv.arrowCongr Fin.revPerm Fin.revPerm f) := by
    intro a b hab
    exact Fin.rev_le_rev.mpr (h (Fin.rev_le_rev.mpr hab))
  constructor
  · intro h
    simpa only [reverseTuple_involutive] using forward (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam) h
  · exact forward lam

private lemma reverseTuple_strictMono {r s : ℕ} (lam : Fin r → Fin s) :
    StrictMono (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam) ↔ StrictMono lam := by
  have forward (f : Fin r → Fin s) (h : StrictMono f) : StrictMono (Equiv.arrowCongr Fin.revPerm Fin.revPerm f) := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (h (Fin.rev_lt_rev.mpr hab))
  constructor
  · intro h
    simpa only [reverseTuple_involutive] using forward (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam) h
  · exact forward lam

private lemma int_val_rev {n : ℕ} (a : Fin n) :
    (a.rev : ℤ) = (n : ℤ) - 1 - a := by
  simp only [Fin.val_rev]
  omega

private theorem T_reflection (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i c : ℤ) :
    T (fun k => u (c - k)) r s i = T u r s (c - i - s - r + 2) := by
  classical
  unfold T
  apply Finset.sum_bij (fun lam _ => (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam))
  · intro lam hm
    simp only [mem_filter, mem_univ, true_and] at hm ⊢
    exact (reverseTuple_strictMono lam).mpr hm
  · intro a ha b hb hab
    simpa only [reverseTuple_involutive] using congrArg (Equiv.arrowCongr Fin.revPerm Fin.revPerm) hab
  · intro lam hm
    refine ⟨(Equiv.arrowCongr Fin.revPerm Fin.revPerm lam), ?_, reverseTuple_involutive lam⟩
    simpa only [mem_filter, mem_univ, true_and, reverseTuple_strictMono] using hm
  · intro lam hm
    apply Fintype.prod_equiv Fin.revPerm
    intro a
    simp only [Equiv.arrowCongr_apply, Function.comp_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_rev]
    congr 1
    rw [int_val_rev, int_val_rev]
    have hnat : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
    omega

private theorem S_reflection (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i c : ℤ) :
    S (fun k => u (c - k)) r s i = S u r s (c - i - s - r + 2) := by
  classical
  unfold S
  apply Finset.sum_bij (fun lam _ => (Equiv.arrowCongr Fin.revPerm Fin.revPerm lam))
  · intro lam hm
    simp only [mem_filter, mem_univ, true_and] at hm ⊢
    exact (reverseTuple_monotone lam).mpr hm
  · intro a ha b hb hab
    simpa only [reverseTuple_involutive] using congrArg (Equiv.arrowCongr Fin.revPerm Fin.revPerm) hab
  · intro lam hm
    refine ⟨(Equiv.arrowCongr Fin.revPerm Fin.revPerm lam), ?_, reverseTuple_involutive lam⟩
    simpa only [mem_filter, mem_univ, true_and, reverseTuple_monotone] using hm
  · intro lam hm
    apply Fintype.prod_equiv Fin.revPerm
    intro a
    simp only [Equiv.arrowCongr_apply, Function.comp_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_rev]
    congr 1
    rw [int_val_rev, int_val_rev]
    have hnat : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
    omega

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private theorem T_nat_eq (u : ℤ → R) (r s : ℕ) (i : ℤ) :
    T u r (s : ℤ) i = strictSum r s (fun a k => u (i + (k : ℤ) + (a : ℤ))) := by
  exact (congrFun rfl ∘ u) i

private theorem S_nat_eq (u : ℤ → R) (r s : ℕ) (i : ℤ) :
    S u r (s : ℤ) i = monoSum r s (fun a k => u (i + (k : ℤ) + ((r : ℤ) - 1 - (a : ℤ)))) := by
  exact (congrFun rfl ∘ u) i

private theorem T_left_nat (u : ℤ → R) (r s : ℕ) (i : ℤ) :
    T u (r + 1) (s + 1 : ℕ) i =
      T u (r + 1) (s : ℤ) (i + 1) + u i * T u r (s : ℤ) (i + 2) := by
  rw [T_nat_eq, T_nat_eq, T_nat_eq]
  have h := strict_pascal r s (fun a k => u (i + (k : ℤ) + (a : ℤ)))
  convert h using 1
  congr 1
  · congr 1
    funext a k
    congr 1
    push_cast
    omega
  · congr 1
    · simp
    · congr 1
      funext a k
      congr 1
      push_cast
      omega

private theorem S_left_nat (u : ℤ → R) (r s : ℕ) (i : ℤ) :
    S u (r + 1) (s + 1 : ℕ) i =
      S u (r + 1) (s : ℤ) (i + 1) + u (i + r) * S u r (s + 1 : ℕ) i := by
  rw [S_nat_eq, S_nat_eq, S_nat_eq]
  have h := mono_pascal r s
    (fun a k => u (i + (k : ℤ) + (((r + 1 : ℕ) : ℤ) - 1 - (a : ℤ))))
  convert h using 1
  congr 1
  · congr 1
    funext a k
    congr 1
    push_cast
    omega
  · congr 1
    · congr 1
      push_cast
      omega
    · congr 1
      funext a k
      congr 1
      push_cast
      omega

private theorem T_left (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    T u (r + 1) (s + 1) i =
      T u (r + 1) s (i + 1) + u i * T u r s (i + 2) := by
  have h := T_left_nat u r s.toNat i
  simpa only [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg hs] using h

private theorem S_left (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    S u (r + 1) (s + 1) i =
      S u (r + 1) s (i + 1) + u (i + r) * S u r (s + 1) i := by
  have h := S_left_nat u r s.toNat i
  simpa only [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg hs] using h

private theorem T_right (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    T u (r + 1) (s + 1) i =
      T u (r + 1) s i + u (i + s + r) * T u r s i := by
  let c : ℤ := i + s + r
  have h := T_left (fun k => u (c - k)) r hs 0
  rw [T_reflection u (r + 1) (by omega) 0 c,
    T_reflection u (r + 1) hs (0 + 1) c,
    T_reflection u r hs (0 + 2) c] at h
  simpa [c, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using h

private theorem S_right (u : ℤ → R) (r : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    S u (r + 1) (s + 1) i =
      S u (r + 1) s i + u (i + s) * S u r (s + 1) (i + 1) := by
  let c : ℤ := i + s + r
  have h := S_left (fun k => u (c - k)) r hs 0
  rw [S_reflection u (r + 1) (by omega) 0 c,
    S_reflection u (r + 1) hs (0 + 1) c,
    S_reflection u r (by omega) 0 c] at h
  have hidx : c - 0 - (s + 1) - (r : ℤ) + 2 = i + 1 := by dsimp [c]; ring
  rw [hidx] at h
  simpa [c, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using h

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private noncomputable def Q (u : ℤ → R) : ℕ → ℤ → ℤ → R
  | 0, s, i => S u 0 s i
  | 1, s, i => S u 1 s i
  | p + 2, s, i => S u (p + 2) s i - u (i + p) * u (i + s) * S u p (s + 2) i

private theorem Q_small (u : ℤ → R) (p : ℕ) (hp : p ≤ 1) (s i : ℤ) :
    Q u p s i = S u p s i := by
  interval_cases p <;> rfl

private theorem Q_spec (u : ℤ → R) (p : ℕ) (hp : 2 ≤ p) (s i : ℤ) :
    Q u p s i = S u p s i - u (i + p - 2) * u (i + s) * S u (p - 2) (s + 2) i := by
  obtain ⟨p, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
  simp only [Q, Nat.add_sub_cancel]
  rw [show i + ((p + 2 : ℕ) : ℤ) - 2 = i + p by omega]

private theorem S_Q_left (u : ℤ → R) (p : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    S u (p + 1) (s + 1) i =
      Q u (p + 1) s (i + 1) + u (i + p) * S u p (s + 2) i := by
  cases p with
  | zero => simpa [Q, S_zero] using S_left u 0 hs i
  | succ p =>
    have h1 := S_left u (p + 1) hs i
    have h2 := S_right u p (show 0 ≤ s + 1 from Int.le_add_one hs) i
    rw [show p + 1 + 1 = p + 2 from rfl, Q]
    have hi : i + 1 + (p : ℤ) = i + ((p + 1 : ℕ) : ℤ) := by omega
    have hs' : i + (s + 1) = i + 1 + s := by omega
    rw [hi, ← hs']
    have hs2 : s + 1 + 1 = s + 2 := by omega
    rw [hs2] at h2
    rw [h1, h2]
    ring

private theorem S_Q_right (u : ℤ → R) (p : ℕ) {s : ℤ} (hs : 0 ≤ s) (i : ℤ) :
    S u (p + 1) (s + 1) i =
      Q u (p + 1) s i + u (i + s) * S u p (s + 2) i := by
  cases p with
  | zero => simpa [Q, S_zero] using S_right u 0 hs i
  | succ p =>
    have h1 := S_right u (p + 1) hs i
    have h2 := S_left u p (show 0 ≤ s + 1 from Int.le_add_one hs) i
    rw [show p + 1 + 1 = p + 2 from rfl, Q]
    have hs2 : s + 1 + 1 = s + 2 := by omega
    rw [hs2] at h2
    rw [h1, h2]
    ring

private theorem S_locality (u v : ℤ → R) (r s : ℕ) (i : ℤ)
    (agree : ∀ k, i ≤ k → k ≤ i + s + r → u k = v k) :
    S u r (s : ℤ) i = S v r (s : ℤ) i := by
  classical
  unfold S
  apply sum_congr rfl
  intro lam hm
  apply prod_congr rfl
  intro a ha
  apply agree
  · have h := a.isLt
    have h' := (lam a).isLt
    simp only [Int.toNat_natCast] at h'
    omega
  · have h := a.isLt
    have h' := (lam a).isLt
    simp only [Int.toNat_natCast] at h'
    omega

private theorem S_zero_field (r : ℕ) (hr : 0 < r) (s i : ℤ) :
    S (fun _ => (0 : R)) r s i = 0 := by
  classical
  unfold S
  apply sum_eq_zero
  intro lam hm
  apply prod_eq_zero (mem_univ (⟨0, hr⟩ : Fin r))
  rfl

private theorem Q_boundary (u : ℤ → R) (r : ℕ) (hr : 1 ≤ r) (i : ℤ) :
    Q u r ((r : ℤ) - 1) i = 0 := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero =>
      simp only [Q]
      exact S_nonpositive u (by omega) (by omega) i
    | succ p =>
      have hb : (((p + 1 + 1 : ℕ) : ℤ) - 1) = (p : ℤ) + 1 := Int.sub_eq_iff_eq_add.mpr rfl
      rw [hb]
      have shift (v : ℤ → R) (a : ℤ) :
          Q v (p + 2) ((p : ℤ) + 1) (a + 1) =
            Q v (p + 2) ((p : ℤ) + 1) a := by
        have h1 := S_Q_left v (p + 1) (show (0 : ℤ) ≤ (p : ℤ) + 1 from Int.zero_le_ofNat (p + 1)) a
        have h2 := S_Q_right v (p + 1) (show (0 : ℤ) ≤ (p : ℤ) + 1 from Int.zero_le_ofNat (p + 1)) a
        have hi : a + ((p : ℤ) + 1) = a + ((p + 1 : ℕ) : ℤ) := rfl
        rw [hi] at h2
        exact add_right_cancel (h1.symm.trans h2)
      apply local_translation_invariant_zero
        (F := fun v a => Q v (p + 2) ((p : ℤ) + 1) a) (width := 2 * (p + 2) + 2)
      · intro v w a agree
        simp only [Q]
        congr 1
        · rw [show (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) from Int.ofNat_add_one_out p]
          apply S_locality v w (p + 2) (p + 1) a
          intro k hlo hhi
          apply agree k hlo
          omega
        · congr 1
          · congr 1
            · apply agree <;> omega
            · apply agree <;> omega
          · have ht : (p : ℤ) + 1 + 2 = ((p + 3 : ℕ) : ℤ) := rfl
            rw [ht]
            apply S_locality v w p (p + 3) a
            intro k hlo hhi
            apply agree k hlo
            omega
      · exact shift
      · intro a
        simp [Q, S_zero_field (p + 2) (by omega)]

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity


namespace D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
open Finset
variable {R : Type} [CommRing R]

private theorem bracket_Q_zero (u : ℤ → R) (r : ℕ) (hr : 1 ≤ r)
    (s : ℤ) (hs : (r : ℤ) - 1 ≤ s) (i : ℤ) :
    bracket (Q u) (T u) r s i = 0 := by
  classical
  have boundary (a : ℤ) : bracket (Q u) (T u) r ((r : ℤ) - 1) a = 0 := by
    unfold bracket
    rw [Finset.sum_eq_single 0]
    · simp [Q_boundary u r hr]
    · intro j hj hne
      have hjpos : 0 < j := Nat.zero_lt_of_ne_zero hne
      have hz := T_vanish u (r := j) (s := (r : ℤ) - 1 - r + j)
        (by omega) (a + r - j) hjpos
      rw [hz, mul_zero]
    · simp
  have step (t : ℤ) (ht : (r : ℤ) ≤ t) (a : ℤ) :
      bracket (Q u) (T u) r t a = bracket (Q u) (T u) r (t - 1) (a + 1) := by
    exact bracket_shift u (S u) (T u) (Q u)
      (T_zero u) (S_zero u) (Q_small u) (Q_spec u)
      (fun p t ht a => T_left u p ht a)
      (fun p t ht a => T_right u p ht a)
      (fun p t ht a => S_Q_left u p ht a) r hr t ht a
  have all (n : ℕ) : ∀ a, bracket (Q u) (T u) r ((r : ℤ) - 1 + n) a = 0 := by
    induction n with
    | zero => simpa using boundary
    | succ n ih =>
      intro a
      rw [step _ (by omega)]
      convert ih (a + 1) using 2; omega
  have he : s = (r : ℤ) - 1 + ((s - r + 1).toNat : ℤ) := by omega
  rw [he]
  exact all _ i

theorem result : claim := by
  intro R inst u r hr s hs i
  have h := bracket_correction u (S u) (T u) (Q u)
    (Q_small u) (Q_spec u) r s i
  change bracket (S u) (T u) r s i =
    bracket (Q u) (T u) r s i + correction u (S u) (T u) r s i at h
  rw [bracket_Q_zero u r hr s hs i, zero_add] at h
  exact h

end D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity
