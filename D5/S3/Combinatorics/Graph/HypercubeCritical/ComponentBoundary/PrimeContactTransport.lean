/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic, mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: A connected signed two-contact kernel at distinct prime weights has an integer exponent potential and a Laurent kernel at every nonvanishing weight. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Prime-weight transport for signed two-contact rows

A row indexed by an edge has contacts at two different columns and two
different coordinate weights. Moving one term across the row equality gives
a relative sign. A nowhere-zero rational solution at distinct primes yields
the exponent gain by taking the valuation at each prime. A connected real
solution can first be normalized by its value at a nonzero root, since each
edge ratio is rational. The resulting exponents and signs simultaneously
realize the kernel equations at every nonvanishing real weight vector.

The column and row index types need not be finite. Only the coordinate type
is finite, so the Laurent evaluations are finite products.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactTransport

open scoped BigOperators

/-- A row has an oriented pair of contacts. The relative sign is the
negative of the product of the two original coefficient signs. -/
structure ContactGraph (V E : Type*) (n : ℕ) where
  source : E → V
  target : E → V
  leftAxis : E → Fin n
  rightAxis : E → Fin n
  sign : E → ℤ
  distinctColumns : ∀ e, source e ≠ target e
  distinctAxes : ∀ e, leftAxis e ≠ rightAxis e
  sign_unit : ∀ e, sign e = 1 ∨ sign e = -1

variable {V E : Type*} {n : ℕ}

/-- Adjacency in the underlying undirected graph, allowing parallel rows. -/
def ContactGraph.Adj (G : ContactGraph V E n) (x y : V) : Prop :=
  ∃ e : E, (G.source e = x ∧ G.target e = y) ∨
    (G.source e = y ∧ G.target e = x)

/-- The two-contact row equations, with the sign moved to the right side. -/
def ContactGraph.Kernel {K : Type*} [Ring K] (G : ContactGraph V E n)
    (w : Fin n → K) (z : V → K) : Prop :=
  ∀ e, w (G.rightAxis e) * z (G.target e) =
    (G.sign e : K) * (w (G.leftAxis e) * z (G.source e))

abbrev Exponent (n : ℕ) := Fin n → ℤ

/-- The exponent of the monomial consisting of one coordinate weight. -/
def axis (i : Fin n) : Exponent n := fun k => if k = i then 1 else 0

/-- The exponent gain and relative sign on every oriented row. -/
def ContactGraph.Potential (G : ContactGraph V E n) (a : V → Exponent n)
    (s : V → ℤ) : Prop :=
  (∀ q, s q = 1 ∨ s q = -1) ∧
  ∀ e, a (G.target e) = a (G.source e) + axis (G.leftAxis e) - axis (G.rightAxis e) ∧
    s (G.target e) = G.sign e * s (G.source e)

section RationalNormalization

variable (G : ContactGraph V E n)

private def gain (w : Fin n → ℚ) (e : E) : ℚ :=
  (G.sign e : ℚ) * w (G.leftAxis e) / w (G.rightAxis e)

private theorem gain_ne_zero (w : Fin n → ℚ) (hw : ∀ i, w i ≠ 0) (e : E) :
    gain G w e ≠ 0 := by
  have hs : (G.sign e : ℚ) ≠ 0 := by
    rcases G.sign_unit e with h | h <;> simp [h]
  exact div_ne_zero (mul_ne_zero hs (hw _)) (hw _)

/-- A real solution over nonzero rational weights on a rooted connected
contact graph is a common real scalar times a nowhere-zero rational kernel.
The rational coordinates are the normalized real coordinates. -/
theorem normalize_real_kernel (w : Fin n → ℚ) (hw : ∀ i, w i ≠ 0)
    (z : V → ℝ) (root : V) (hroot : z root ≠ 0)
    (hreach : ∀ q, Relation.ReflTransGen G.Adj root q)
    (hker : G.Kernel (fun i => (w i : ℝ)) z) :
    ∃ r : V → ℚ, r root = 1 ∧ (∀ q, r q ≠ 0) ∧
      (∀ q, (r q : ℝ) = z q / z root) ∧ G.Kernel w r := by
  classical
  have hgain (e : E) : gain G w e ≠ 0 := gain_ne_zero G w hw e
  have forward (e : E) :
      z (G.target e) = (gain G w e : ℝ) * z (G.source e) := by
    have he := hker e
    have hwr : (w (G.rightAxis e) : ℝ) ≠ 0 :=
      Rat.cast_ne_zero.mpr (hw (G.rightAxis e))
    change (w (G.rightAxis e) : ℝ) * z (G.target e) =
      (G.sign e : ℝ) * ((w (G.leftAxis e) : ℝ) * z (G.source e)) at he
    calc
      z (G.target e) =
          ((G.sign e : ℝ) * ((w (G.leftAxis e) : ℝ) * z (G.source e))) /
            (w (G.rightAxis e) : ℝ) := by
        apply (eq_div_iff hwr).2
        rw [mul_comm (z (G.target e))]
        exact he
      _ = (gain G w e : ℝ) * z (G.source e) := by
        simp only [gain, Rat.cast_mul, Rat.cast_intCast, div_eq_mul_inv, Rat.cast_inv]
        ring
  have backward (e : E) :
      z (G.source e) = (((gain G w e)⁻¹ : ℚ) : ℝ) * z (G.target e) := by
    have hg : (gain G w e : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr (hgain e)
    rw [forward e, Rat.cast_inv, ← mul_assoc,
      inv_mul_cancel₀ hg, one_mul]
  have step {x y : V} (hxy : G.Adj x y)
      (hx : ∃ b : ℚ, b ≠ 0 ∧ z x = (b : ℝ) * z root) :
      ∃ b : ℚ, b ≠ 0 ∧ z y = (b : ℝ) * z root := by
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨e, he | he⟩ := hxy
    · refine ⟨gain G w e * b, mul_ne_zero (hgain e) hb, ?_⟩
      rw [← he.2, forward e, he.1, hbx, Rat.cast_mul, mul_assoc]
    · refine ⟨(gain G w e)⁻¹ * b, mul_ne_zero (inv_ne_zero (hgain e)) hb, ?_⟩
      rw [← he.1, backward e, he.2, hbx, Rat.cast_mul, mul_assoc]
  have alongPath {q : V} (hq : Relation.ReflTransGen G.Adj root q) :
      ∃ b : ℚ, b ≠ 0 ∧ z q = (b : ℝ) * z root := by
    induction hq with
    | refl => exact ⟨1, one_ne_zero, by simp⟩
    | tail _ hadj ih => exact step hadj ih
  let r (q : V) : ℚ := Classical.choose (alongPath (hreach q))
  have hr (q : V) : r q ≠ 0 ∧ z q = (r q : ℝ) * z root :=
    Classical.choose_spec (alongPath (hreach q))
  have hratio (q : V) : (r q : ℝ) = z q / z root :=
    (eq_div_iff hroot).2 (hr q).2.symm
  have hrroot : r root = 1 := by
    apply Rat.cast_injective (α := ℝ)
    rw [hratio root, div_self hroot, Rat.cast_one]
  refine ⟨r, hrroot, fun q => (hr q).1, hratio, ?_⟩
  intro e
  apply Rat.cast_injective (α := ℝ)
  simp only [Rat.cast_mul, Rat.cast_intCast]
  apply mul_right_cancel₀ hroot
  calc
    _ = (w (G.rightAxis e) : ℝ) * ((r (G.target e) : ℝ) * z root) := by ring
    _ = (w (G.rightAxis e) : ℝ) * z (G.target e) := by
      rw [← (hr (G.target e)).2]
    _ = (G.sign e : ℝ) * ((w (G.leftAxis e) : ℝ) * z (G.source e)) := hker e
    _ = _ := by rw [(hr (G.source e)).2]; ring

end RationalNormalization

section PrimeValuations

variable (G : ContactGraph V E n)

/-- At pairwise distinct primes, the valuation vector of each weight is its
coordinate basis vector. -/
theorem valuation_prime_eq_axis (p : Fin n → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (i k : Fin n) :
    padicValRat (p k) (p i : ℚ) = axis i k := by
  by_cases h : k = i
  · subst i
    simpa [axis] using (padicValRat.self (p := p k) (hp k).one_lt)
  · have hndvd : ¬ p k ∣ p i := by
      intro hd
      exact h (hinj ((Nat.prime_dvd_prime_iff_eq (hp k) (hp i)).mp hd))
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hndvd]
    simp [axis, h]

/-- Evaluate the sign of a nonzero rational coordinate as an integer unit. -/
private def unitSign (t : ℚ) : ℤ := if 0 < t then 1 else -1

private theorem unitSign_unit (t : ℚ) : unitSign t = 1 ∨ unitSign t = -1 := by
  by_cases h : 0 < t <;> simp [unitSign, h]

/-- Positive weights transmit the relative coefficient signs to the signs
of the solution coordinates. -/
private theorem unitSign_transport (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (z : V → ℚ) (hnz : ∀ q, z q ≠ 0) (hker : G.Kernel w z) (e : E) :
    unitSign (z (G.target e)) = G.sign e * unitSign (z (G.source e)) := by
  have he := hker e
  change w (G.rightAxis e) * z (G.target e) =
    (G.sign e : ℚ) * (w (G.leftAxis e) * z (G.source e)) at he
  rcases G.sign_unit e with hs | hs
  · rw [hs, Int.cast_one, one_mul] at he
    have hiff : 0 < z (G.target e) ↔ 0 < z (G.source e) := calc
      _ ↔ 0 < w (G.rightAxis e) * z (G.target e) :=
        (mul_pos_iff_of_pos_left (hw _)).symm
      _ ↔ 0 < w (G.leftAxis e) * z (G.source e) := by rw [he]
      _ ↔ _ := mul_pos_iff_of_pos_left (hw _)
    by_cases h : 0 < z (G.source e)
    · simp [unitSign, hs, h, hiff.mpr h]
    · have ht : ¬ 0 < z (G.target e) := fun ht => h (hiff.mp ht)
      simp [unitSign, hs, h, ht]
  · rw [hs, Int.cast_neg, Int.cast_one, neg_one_mul] at he
    have hiff : 0 < z (G.target e) ↔ 0 < -z (G.source e) := calc
      _ ↔ 0 < w (G.rightAxis e) * z (G.target e) :=
        (mul_pos_iff_of_pos_left (hw _)).symm
      _ ↔ 0 < w (G.leftAxis e) * (-z (G.source e)) := by rw [he, mul_neg]
      _ ↔ _ := mul_pos_iff_of_pos_left (hw _)
    rcases lt_or_gt_of_ne (hnz (G.source e)) with h | h
    · have ht : 0 < z (G.target e) := hiff.mpr (neg_pos.mpr h)
      simp [unitSign, hs, ht, not_lt_of_gt h]
    · have ht : ¬ 0 < z (G.target e) :=
        fun ht => (not_lt_of_gt h) (neg_pos.mp (hiff.mp ht))
      simp [unitSign, hs, h, ht]

/-- A nowhere-zero rational kernel at distinct prime weights has both the
integer exponent potential and the unit-sign transport. Connectivity is
unnecessary when all the coordinates are already nonzero. -/
theorem potential_of_rational_prime_kernel (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (z : V → ℚ) (hnz : ∀ q, z q ≠ 0)
    (hker : G.Kernel (fun i => (p i : ℚ)) z) :
    ∃ (a : V → Exponent n) (s : V → ℤ), G.Potential a s := by
  have hpq (i : Fin n) : 0 < (p i : ℚ) := by exact_mod_cast (hp i).pos
  let a (q : V) (k : Fin n) : ℤ := padicValRat (p k) (z q)
  refine ⟨a, fun q => unitSign (z q), fun q => unitSign_unit (z q), ?_⟩
  intro e
  constructor
  · funext k
    let _ : Fact (Nat.Prime (p k)) := ⟨hp k⟩
    have he := congrArg (padicValRat (p k)) (hker e)
    change padicValRat (p k) ((p (G.rightAxis e) : ℚ) * z (G.target e)) =
      padicValRat (p k) ((G.sign e : ℚ) * ((p (G.leftAxis e) : ℚ) * z (G.source e))) at he
    have hsign : padicValRat (p k)
        ((G.sign e : ℚ) * ((p (G.leftAxis e) : ℚ) * z (G.source e))) =
        padicValRat (p k) ((p (G.leftAxis e) : ℚ) * z (G.source e)) := by
      rcases G.sign_unit e with hs | hs <;> simp [hs, padicValRat.neg]
    rw [hsign,
      padicValRat.mul (ne_of_gt (hpq (G.rightAxis e))) (hnz (G.target e)),
      padicValRat.mul (ne_of_gt (hpq (G.leftAxis e))) (hnz (G.source e)),
      valuation_prime_eq_axis p hp hinj (G.rightAxis e) k,
      valuation_prime_eq_axis p hp hinj (G.leftAxis e) k] at he
    change padicValRat (p k) (z (G.target e)) =
      padicValRat (p k) (z (G.source e)) + axis (G.leftAxis e) k - axis (G.rightAxis e) k
    omega
  · exact unitSign_transport G (fun i => (p i : ℚ)) hpq z hnz hker e

/-- A rooted connected real kernel yields a potential via rational
normalization. Only the root is assumed to carry a nonzero value. -/
theorem potential_of_real_prime_kernel (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (z : V → ℝ) (root : V) (hroot : z root ≠ 0)
    (hreach : ∀ q, Relation.ReflTransGen G.Adj root q)
    (hker : G.Kernel (fun i => (p i : ℝ)) z) :
    ∃ (a : V → Exponent n) (s : V → ℤ), G.Potential a s := by
  have hpq (i : Fin n) : (p i : ℚ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hcast : G.Kernel (fun i => ((p i : ℚ) : ℝ)) z := by
    simpa only [Rat.cast_natCast] using hker
  obtain ⟨r, _, hnz, _, hr⟩ :=
    normalize_real_kernel G (fun i => (p i : ℚ)) hpq z root hroot hreach hcast
  exact potential_of_rational_prime_kernel G p hp hinj r hnz hr

end PrimeValuations

section LaurentRealization

/-- Evaluation of a Laurent monomial in the coordinate weights. -/
def monomial (w : Fin n → ℝ) (a : Exponent n) : ℝ :=
  ∏ k, w k ^ a k

private theorem monomial_add (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    (a b : Exponent n) :
    monomial w (a + b) = monomial w a * monomial w b := by
  unfold monomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  exact zpow_add₀ (hw k) (a k) (b k)

private theorem monomial_axis (w : Fin n → ℝ) (i : Fin n) :
    monomial w (axis i) = w i := by
  unfold monomial axis
  calc
    _ = ∏ k : Fin n, (if k = i then w k else 1) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k = i <;> simp [hk]
    _ = w i := Fintype.prod_ite_eq' i w

private theorem monomial_ne_zero (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    (a : Exponent n) : monomial w a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero (a k) (hw k))

/-- One signed Laurent monomial per column. -/
def signedLaurent (w : Fin n → ℝ) (a : V → Exponent n) (s : V → ℤ) (q : V) : ℝ :=
  (s q : ℝ) * monomial w (a q)

variable (G : ContactGraph V E n)

/-- A transported exponent potential realizes a nowhere-zero real kernel
at every nonvanishing weight vector, including all strictly positive ones. -/
theorem laurent_kernel_of_potential (a : V → Exponent n) (s : V → ℤ)
    (h : G.Potential a s) (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∀ q, signedLaurent w a s q ≠ 0) ∧ G.Kernel w (signedLaurent w a s) := by
  constructor
  · intro q
    have hs : (s q : ℝ) ≠ 0 := by
      rcases h.1 q with hs | hs <;> simp [hs]
    exact mul_ne_zero hs (monomial_ne_zero w hw (a q))
  · intro e
    have hsum : a (G.target e) + axis (G.rightAxis e) =
        a (G.source e) + axis (G.leftAxis e) := by
      rw [(h.2 e).1, sub_add_cancel]
    have hprod : monomial w (a (G.target e)) * w (G.rightAxis e) =
        monomial w (a (G.source e)) * w (G.leftAxis e) := calc
      _ = monomial w (a (G.target e) + axis (G.rightAxis e)) := by
        rw [monomial_add w hw, monomial_axis]
      _ = monomial w (a (G.source e) + axis (G.leftAxis e)) :=
        congrArg (monomial w) hsum
      _ = _ := by rw [monomial_add w hw, monomial_axis]
    have hsign : (s (G.target e) : ℝ) = (G.sign e : ℝ) * (s (G.source e) : ℝ) := by
      exact_mod_cast (h.2 e).2
    change w (G.rightAxis e) * ((s (G.target e) : ℝ) * monomial w (a (G.target e))) =
      (G.sign e : ℝ) * (w (G.leftAxis e) *
        ((s (G.source e) : ℝ) * monomial w (a (G.source e))))
    rw [hsign]
    calc
      _ = (G.sign e : ℝ) * (s (G.source e) : ℝ) *
          (monomial w (a (G.target e)) * w (G.rightAxis e)) := by ring
      _ = (G.sign e : ℝ) * (s (G.source e) : ℝ) *
          (monomial w (a (G.source e)) * w (G.leftAxis e)) := by rw [hprod]
      _ = _ := by ring

/-- Existence of a real kernel with a nonzero root at distinct prime
weights is equivalent to existence of a signed integer exponent potential. -/
theorem real_prime_kernel_iff_potential (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (root : V) (hreach : ∀ q, Relation.ReflTransGen G.Adj root q) :
    (∃ z : V → ℝ, z root ≠ 0 ∧ G.Kernel (fun i => (p i : ℝ)) z) ↔
      ∃ (a : V → Exponent n) (s : V → ℤ), G.Potential a s := by
  constructor
  · rintro ⟨z, hroot, hker⟩
    exact potential_of_real_prime_kernel G p hp hinj z root hroot hreach hker
  · rintro ⟨a, s, h⟩
    have hpR (i : Fin n) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    obtain ⟨hnz, hker⟩ :=
      laurent_kernel_of_potential G a s h (fun i => (p i : ℝ)) hpR
    exact ⟨_, hnz root, hker⟩

/-- On a connected contact graph, a real kernel which is nonzero as a
function at distinct primes yields a single family of signed Laurent
monomials solving every row simultaneously at every nonvanishing weight.
The hypothesis on the kernel also ensures that the column type is nonempty. -/
theorem exists_laurent_kernel_of_real_prime_kernel (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hconn : ∀ x y : V, Relation.ReflTransGen G.Adj x y)
    (z : V → ℝ) (hnz : z ≠ 0) (hker : G.Kernel (fun i => (p i : ℝ)) z) :
    ∃ (a : V → Exponent n) (s : V → ℤ), G.Potential a s ∧
      ∀ w : Fin n → ℝ, (∀ i, w i ≠ 0) →
        (∀ q, signedLaurent w a s q ≠ 0) ∧ G.Kernel w (signedLaurent w a s) := by
  classical
  have hex : ∃ root : V, z root ≠ 0 := by
    by_contra! h
    exact hnz (funext h)
  obtain ⟨root, hroot⟩ := hex
  obtain ⟨a, s, h⟩ := potential_of_real_prime_kernel G p hp hinj z root hroot (hconn root) hker
  exact ⟨a, s, h, fun w hw => laurent_kernel_of_potential G a s h w hw⟩

end LaurentRealization

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactTransport
