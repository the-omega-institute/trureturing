/- GID: D5/S3/Analytic/Interpolation/ConfluentPositiveSampling
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ConfluentPositiveSampling
   mirror-E: none(waiver:analytic-sampling-bound-without-executable-mirror)
   anchors: []
   utility: none
   digest: Confluent Newton samples recover weighted polynomial coefficients on positive intervals. -/

module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact

/-!
# Confluent positive polynomial sampling

Descartes' rule with multiplicities gives injectivity of sparse real polynomials
at positive Hermite nodes. For a weighted polynomial `X ^ r * q`, the nonconstant
Newton coefficients at sufficiently many positive nodes determine `q`, even
when nodes coincide. The weight eliminates the unobserved additive constant.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Interpolation.ConfluentPositiveSampling

open Polynomial
open scoped BigOperators

private theorem signVariations_le_support_card_sub_one (p : ℝ[X]) :
    p.signVariations ≤ p.support.card - 1 := by
  induction hcard : p.support.card generalizing p with
  | zero =>
      have hp : p = 0 := card_support_eq_zero.mp hcard
      simp [hp]
  | succ n ih =>
      by_cases he : p.eraseLead = 0
      · obtain ⟨d, a, rfl⟩ := card_support_le_one_iff_monomial.mp
          (card_support_le_one_of_eraseLead_eq_zero he)
        simp
      · have hlead : p.eraseLead.support.card = n := card_support_eraseLead' hcard
        have hpos : 0 < n := by
          by_contra! h
          exact he (card_support_eq_zero.mp (by omega))
        have h1 := ih p.eraseLead hlead
        have h2 := signVariations_le_eraseLead_succ p
        omega

/-- A nonzero real polynomial has fewer positive roots, counted with
multiplicity, than nonzero coefficients. -/
private theorem eq_zero_of_positive_jets_of_support_card_le (p : ℝ[X]) (s : Multiset ℝ)
    (hpos : ∀ x ∈ s, 0 < x) (hcard : p.support.card ≤ s.card)
    (hjet : ∀ x k, k < s.count x → ((Polynomial.derivative^[k]) p).eval x = 0) :
    p = 0 := by
  classical
  by_contra hp
  have hle : s ≤ p.roots.filter (fun x => 0 < x) := by
    refine Multiset.le_iff_count.mpr (fun x => ?_)
    by_cases hx : x ∈ s
    · rw [Multiset.count_filter_of_pos (hpos x hx), Polynomial.count_roots]
      cases hk : s.count x with
      | zero => simp
      | succ k =>
          have h := lt_rootMultiplicity_of_isRoot_iterate_derivative hp
            (t := x) (n := k) (fun j hj => hjet x j (by omega))
          omega
    · simp [Multiset.count_eq_zero_of_notMem hx]
  have h1 := Multiset.card_le_card hle
  rw [← Multiset.countP_eq_card_filter] at h1
  have h2 := p.roots_countP_pos_le_signVariations
  have h3 := signVariations_le_support_card_sub_one p
  have h4 : p.support.card ≠ 0 := fun h => hp (card_support_eq_zero.mp h)
  omega

/-- Positive jets determine a constant plus a polynomial with a positive
monomial weight. -/
private theorem eq_zero_of_positive_jets_C_add_X_pow_mul
    (s : Multiset ℝ) {r m : ℕ} (hr : 0 < r) (c : ℝ) (q : ℝ[X])
    (hpos : ∀ x ∈ s, 0 < x) (hq : q.natDegree < m) (hs : m + 1 ≤ s.card)
    (hjet : ∀ x k, k < s.count x →
      ((Polynomial.derivative^[k]) (C c + X ^ r * q)).eval x = 0) :
    c = 0 ∧ q = 0 := by
  have hX : ((X : ℝ[X]) ^ r).support.card ≤ 1 := by
    simpa only [C_1, one_mul] using
      (card_support_C_mul_X_pow_le_one (c := (1 : ℝ)) (n := r))
  have hC : (C c).support.card ≤ 1 := by
    simpa only [pow_zero, mul_one] using
      (card_support_C_mul_X_pow_le_one (c := c) (n := 0))
  have hmul : ((X : ℝ[X]) ^ r * q).support.card ≤ q.support.card :=
    card_support_mul_le.trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right q.support.card hX)
  have hcard : (C c + X ^ r * q).support.card ≤ s.card := by
    calc
      _ ≤ ((C c).support ∪ (X ^ r * q).support).card :=
        Finset.card_le_card support_add
      _ ≤ (C c).support.card + (X ^ r * q).support.card := Finset.card_union_le _ _
      _ ≤ s.card := by
        have := card_supp_le_succ_natDegree q
        omega
  have hp := eq_zero_of_positive_jets_of_support_card_le _ s hpos hcard hjet
  have hc : c = 0 := by
    simpa [hr.ne'] using congrArg (Polynomial.eval 0) hp
  have hzero : (X : ℝ[X]) ^ r * q = 0 := by
    simpa only [hc, map_zero, zero_add] using hp
  exact ⟨hc, (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero r X_ne_zero)⟩

/-- Divisibility by the nodal product is equivalent to vanishing ordinary
derivative jets through the multiplicity of each node. -/
private theorem multiset_nodal_dvd_iff_jets {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (s : Multiset F) (p : F[X]) :
    (s.map (fun x => X - C x)).prod ∣ p ↔
      ∀ x k, k < s.count x → ((Polynomial.derivative^[k]) p).eval x = 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp, Multiset.le_iff_count]
  simp only [Polynomial.count_roots]
  constructor
  · intro h x k hk
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity (hk.trans_le (h x))
  · intro h x
    cases hk : s.count x with
    | zero => exact Nat.zero_le _
    | succ k =>
        exact Nat.succ_le_of_lt (lt_rootMultiplicity_of_isRoot_iterate_derivative
          hp (t := x) (n := k) (fun j hj => h x j (by omega)))

/-- A constant nodal remainder of a weighted polynomial forces the
unweighted polynomial to vanish. -/
private theorem eq_zero_of_constant_nodal_remainder
    (s : Multiset ℝ) {r m : ℕ} (hr : 0 < r) (q : ℝ[X]) (c : ℝ)
    (hpos : ∀ x ∈ s, 0 < x) (hq : q.natDegree < m) (hs : m + 1 ≤ s.card)
    (hrem : (X ^ r * q) %ₘ (s.map (fun x => X - C x)).prod = C c) :
    q = 0 := by
  have hd := dvd_modByMonic_sub (X ^ r * q) (s.map (fun x => X - C x)).prod
  rw [hrem, sub_eq_add_neg, ← mul_neg] at hd
  have h := (multiset_nodal_dvd_iff_jets s _).mp hd
  exact neg_eq_zero.mp (eq_zero_of_positive_jets_C_add_X_pow_mul s hr _ (-q)
    hpos (by simpa using hq) hs h).2

/-- Newton coefficients in node order, computed by successive monic divisions.
Repeated nodes are allowed. -/
private def polynomialNewtonCoeffs (p : ℝ[X]) : List ℝ → List ℝ
  | [] => []
  | a :: as => p.eval a :: polynomialNewtonCoeffs (p /ₘ (X - C a)) as

private theorem list_nodal_dvd_of_newton_zero (as : List ℝ) (p : ℝ[X])
    (h : polynomialNewtonCoeffs p as = List.replicate as.length 0) :
    ((as : Multiset ℝ).map (fun a => X - C a)).prod ∣ p := by
  induction as generalizing p with
  | nil => simp
  | cons a as ih =>
      simp only [polynomialNewtonCoeffs, List.length_cons, List.replicate_succ,
        List.cons.injEq] at h
      have htail := ih _ h.2
      have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).2 h.1
      rw [← hmul]
      change (Multiset.map (fun a => X - C a) (a ::ₘ (as : Multiset ℝ))).prod ∣ _
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_dvd_mul_left _ htail

/-- The nonconstant Newton coefficients determine a weighted polynomial of
bounded degree on positive nodes, including repeated nodes. -/
private theorem weighted_polynomial_eq_zero_of_newton_tail_zero (a : ℝ) (as : List ℝ)
    {r m : ℕ} (hr : 0 < r) (q : ℝ[X]) (hpos : ∀ x ∈ a :: as, 0 < x)
    (hq : q.natDegree < m) (hs : m ≤ as.length)
    (hnewton : polynomialNewtonCoeffs (X ^ r * q /ₘ (X - C a)) as =
      List.replicate as.length 0) : q = 0 := by
  let p : ℝ[X] := X ^ r * q
  let s : Multiset ℝ := (a :: as : List ℝ)
  let D := (s.map (fun x => X - C x)).prod
  have hd := list_nodal_dvd_of_newton_zero as (p /ₘ (X - C a)) hnewton
  have hd' : D ∣ p - C (p.eval a) := by
    change (Multiset.map (fun x => X - C x) (a ::ₘ (as : Multiset ℝ))).prod ∣ _
    rw [Multiset.map_cons, Multiset.prod_cons]
    have hh := modByMonic_add_div p (X - C a)
    rw [modByMonic_X_sub_C_eq_C_eval, add_comm, ← eq_sub_iff_add_eq] at hh
    rw [← hh]
    exact mul_dvd_mul_left _ hd
  have heq : p %ₘ D = C (p.eval a) := by
    have hm := monic_multisetProd_X_sub_C s
    have hdeg : D.natDegree = s.card := natDegree_multiset_prod_X_sub_C_eq_card s
    have hc : (C (p.eval a)).degree < D.degree := by
      rw [degree_eq_natDegree hm.ne_zero, hdeg]
      apply Polynomial.degree_le_natDegree.trans_lt
      rw [Polynomial.natDegree_C]
      exact WithBot.coe_lt_coe.mpr (Nat.succ_pos as.length)
    exact (modByMonic_eq_of_dvd_sub hm hd').trans ((modByMonic_eq_self_iff hm).2 hc)
  exact eq_zero_of_constant_nodal_remainder s hr q _ (by simpa [s] using hpos)
    hq (by simpa [s] using Nat.succ_le_succ hs) heq

/-! ## Finite coefficient vectors and confluent data

The finite-vector interface uses the same successive divisions as the list
interface above. Each observation at fixed nodes is linear in the coefficients.
-/

private def polynomialNewtonFunctional :
    {n : ℕ} → (Fin n → ℝ) → Fin n → ℝ[X] →ₗ[ℝ] ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, a, i =>
      Fin.cases (Polynomial.leval (a 0))
        (fun j => (polynomialNewtonFunctional (fun k : Fin n => a k.succ) j).comp
          (Polynomial.divByMonicHom (X - C (a 0)))) i

/-- The ordered Newton coefficients as a linear observation map on polynomials. -/
private def polynomialNewtonData {n : ℕ} (a : Fin n → ℝ) : ℝ[X] →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi (polynomialNewtonFunctional a)

@[simp] private theorem polynomialNewtonData_zero {n : ℕ}
    (a : Fin (n + 1) → ℝ) (p : ℝ[X]) : polynomialNewtonData a p 0 = p.eval (a 0) := by
  simp [polynomialNewtonData, polynomialNewtonFunctional]

@[simp] private theorem polynomialNewtonData_succ {n : ℕ}
    (a : Fin (n + 1) → ℝ) (p : ℝ[X]) (j : Fin n) :
    polynomialNewtonData a p j.succ =
      polynomialNewtonData (fun k : Fin n => a k.succ) (p /ₘ (X - C (a 0))) j := by
  simp [polynomialNewtonData, polynomialNewtonFunctional]

/-- The finite data vector agrees with the list of successive monic-division
coefficients, including their normalization at collisions. -/
private theorem polynomialNewtonData_ofFn {n : ℕ} (a : Fin n → ℝ) (p : ℝ[X]) :
    List.ofFn (polynomialNewtonData a p) = polynomialNewtonCoeffs p (List.ofFn a) := by
  induction n generalizing p with
  | zero => simp [polynomialNewtonCoeffs]
  | succ n ih =>
      simp only [List.ofFn_succ, polynomialNewtonCoeffs, polynomialNewtonData_zero,
        polynomialNewtonData_succ, ih]

/-- For `m + 1` ordered nodes, measure the Newton coefficients of degrees
`1, ..., m` of the polynomial `X ^ r * ofFn m v`. -/
def weightedNewtonTail {m : ℕ} (r : ℕ) (a : Fin (m + 1) → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  (polynomialNewtonData (fun i : Fin m => a i.succ)).comp
    ((Polynomial.divByMonicHom (X - C (a 0))).comp
      ((LinearMap.mulLeft ℝ ((X : ℝ[X]) ^ r)).comp (Polynomial.ofFn m)))

/-- Pointwise recovery of arbitrary real coefficient data. Positivity is the
only restriction on node locations, so total coalescence is included. -/
private theorem weightedNewtonTail_injective {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (a : Fin (m + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    Function.Injective (weightedNewtonTail r a) := by
  classical
  have hzero (v : Fin m → ℝ) (hv : weightedNewtonTail r a v = 0) : v = 0 := by
    have hpos : ∀ x ∈ a 0 :: List.ofFn (fun j : Fin m => a j.succ), 0 < x := by
      rw [← List.ofFn_succ (f := a)]
      exact List.forall_mem_ofFn_iff.mpr ha
    have hnewton : polynomialNewtonCoeffs
        (X ^ r * Polynomial.ofFn m v /ₘ (X - C (a 0)))
        (List.ofFn (fun j : Fin m => a j.succ)) = List.replicate m 0 := by
      rw [← polynomialNewtonData_ofFn]
      change List.ofFn (weightedNewtonTail r a v) = _
      rw [hv]
      exact List.ofFn_const m 0
    have hq := weighted_polynomial_eq_zero_of_newton_tail_zero
      (a 0) (List.ofFn (fun j : Fin m => a j.succ)) hr (Polynomial.ofFn m v)
      hpos (Polynomial.ofFn_natDegree_lt hm v) (by simp) (by simpa using hnewton)
    apply Polynomial.injective_ofFn m
    simpa only [map_zero] using hq
  intro v w hvw
  have hsub : weightedNewtonTail r a (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) hsub)

/-! ## Uniform estimate on a compact positive interval

The argument uses finite padded coefficient sums to establish joint
continuity in the nodes and the coefficients. Compactness of the product of
the node cube and the unit coefficient sphere then gives a positive minimum.
-/

private theorem continuous_eval_of_coeff {T : Type*} [TopologicalSpace T]
    (d : ℕ) (p : T → ℝ[X]) (a : T → ℝ)
    (hd : ∀ t, (p t).natDegree ≤ d)
    (hc : ∀ k, Continuous (fun t => (p t).coeff k)) (ha : Continuous a) :
    Continuous (fun t => (p t).eval (a t)) := by
  have heq : (fun t => (p t).eval (a t)) =
      fun t => ∑ k ∈ Finset.range (d + 1), (p t).coeff k * a t ^ k := by
    funext t
    exact eval_eq_sum_range' (lt_of_le_of_lt (hd t) (Nat.lt_succ_self d)) (a t)
  rw [heq]
  exact continuous_finsetSum _ (fun k _ => (hc k).mul (ha.pow k))

private theorem continuous_divByMonic_coeff {T : Type*} [TopologicalSpace T]
    (d : ℕ) (p : T → ℝ[X]) (a : T → ℝ)
    (hd : ∀ t, (p t).natDegree ≤ d)
    (hc : ∀ k, Continuous (fun t => (p t).coeff k)) (ha : Continuous a) (k : ℕ) :
    Continuous (fun t => ((p t) /ₘ (X - C (a t))).coeff k) := by
  have heq : (fun t => ((p t) /ₘ (X - C (a t))).coeff k) =
      fun t => ∑ i ∈ Finset.Icc (k + 1) d, a t ^ (i - (k + 1)) * (p t).coeff i := by
    funext t
    rw [coeff_divByMonic_X_sub_C]
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hd t)⟩
    · intro i hi hnot
      have hlt : (p t).natDegree < i := by
        by_contra! h
        exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, h⟩)
      rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  rw [heq]
  exact continuous_finsetSum _ (fun i _ => (ha.pow (i - (k + 1))).mul (hc i))

private theorem natDegree_divByMonic_X_sub_C_le (p : ℝ[X]) (a : ℝ) :
    (p /ₘ (X - C a)).natDegree ≤ p.natDegree := by
  rw [natDegree_divByMonic p (monic_X_sub_C a)]
  exact Nat.sub_le _ _

private theorem continuous_newtonData_of_coeff {T : Type*} [TopologicalSpace T]
    (d n : ℕ) : ∀ (p : T → ℝ[X]) (a : T → Fin n → ℝ),
    (∀ t, (p t).natDegree ≤ d) →
    (∀ k, Continuous (fun t => (p t).coeff k)) →
    (∀ i, Continuous (fun t => a t i)) →
    Continuous (fun t => polynomialNewtonData (a t) (p t)) := by
  induction n with
  | zero =>
      intro p a hd hc ha
      exact continuous_pi (fun i => Fin.elim0 i)
  | succ n ih =>
      intro p a hd hc ha
      let q : T → ℝ[X] := fun t => p t /ₘ (X - C (a t 0))
      have hqd : ∀ t, (q t).natDegree ≤ d := fun t =>
        (natDegree_divByMonic_X_sub_C_le (p t) (a t 0)).trans (hd t)
      have hqc : ∀ k, Continuous (fun t => (q t).coeff k) :=
        continuous_divByMonic_coeff d p (fun t => a t 0) hd hc (ha 0)
      have htail := ih q (fun t j => a t j.succ) hqd hqc (fun j => ha j.succ)
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [polynomialNewtonData_zero] using
          continuous_eval_of_coeff d p (fun t => a t 0) hd hc (ha 0)
      · simpa only [polynomialNewtonData_succ, q] using (continuous_pi_iff.mp htail) j

/-- Joint continuity of the confluent observations in the coefficient vector
and every node. In particular there is no singularity at coincident nodes. -/
private theorem continuous_weightedNewtonTail {m : ℕ} (hm : 0 < m) (r : ℕ) :
    Continuous (fun z : (Fin (m + 1) → ℝ) × (Fin m → ℝ) =>
      weightedNewtonTail r z.1 z.2) := by
  classical
  let T := (Fin (m + 1) → ℝ) × (Fin m → ℝ)
  let p : T → ℝ[X] := fun z => X ^ r * Polynomial.ofFn m z.2
  have hd : ∀ z, (p z).natDegree ≤ r + m := by
    intro z
    exact natDegree_mul_le_of_le (natDegree_X_pow_le r)
      (Polynomial.ofFn_natDegree_lt hm z.2).le
  have hc (k : ℕ) : Continuous (fun z => (p z).coeff k) := by
    simp only [p, coeff_X_pow_mul']
    by_cases hk : r ≤ k
    · simp only [ite_eq_left hk]
      by_cases hkm : k - r < m
      · have hcoeff : (fun z : T => (Polynomial.ofFn m z.2).coeff (k - r)) =
            fun z => z.2 ⟨k - r, hkm⟩ :=
          funext fun z => Polynomial.ofFn_coeff_eq_val_of_lt z.2 hkm
        rw [hcoeff]
        exact (continuous_apply (⟨k - r, hkm⟩ : Fin m)).comp continuous_snd
      · have hcoeff : (fun z : T => (Polynomial.ofFn m z.2).coeff (k - r)) =
            fun _ => 0 :=
          funext fun z => Polynomial.ofFn_coeff_eq_zero_of_ge z.2 (Nat.le_of_not_gt hkm)
        rw [hcoeff]
        exact continuous_const
    · simp only [ite_eq_right hk]
      exact continuous_const
  have ha (i : Fin (m + 1)) : Continuous (fun z : T => z.1 i) :=
    (continuous_apply i).comp continuous_fst
  let q : T → ℝ[X] := fun z => p z /ₘ (X - C (z.1 0))
  have hqd : ∀ z, (q z).natDegree ≤ r + m := fun z =>
    (natDegree_divByMonic_X_sub_C_le (p z) (z.1 0)).trans (hd z)
  have hqc : ∀ k, Continuous (fun z => (q z).coeff k) :=
    continuous_divByMonic_coeff (r + m) p (fun z => z.1 0) hd hc (ha 0)
  change Continuous (fun z : T => polynomialNewtonData (fun j : Fin m => z.1 j.succ) (q z))
  exact continuous_newtonData_of_coeff (r + m) m q (fun z j => z.1 j.succ)
    hqd hqc (fun j => ha j.succ)

/-- Uniform quantitative recovery on a compact positive node interval.
The constant depends only on the dimensions, the monomial weight, and the
interval. The norms are the finite-vector sup norms, so the estimate is
independent of the minimum pairwise separation (which may be zero). -/
theorem weightedNewtonTail_uniform_lower {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (lo hi : ℝ) (hlo : 0 < lo) (hinterval : lo ≤ hi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Set.Icc lo hi) →
      ∀ v : Fin m → ℝ, δ * ‖v‖ ≤ ‖weightedNewtonTail r a v‖ := by
  classical
  let K : Set (Fin (m + 1) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc lo hi)
  let S := K ×ˢ Metric.sphere (0 : Fin m → ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hne : S.Nonempty := by
    refine ⟨(fun _ => lo, Pi.single (⟨0, hm⟩ : Fin m) (1 : ℝ)), ?_, ?_⟩
    · intro i _
      exact ⟨le_rfl, hinterval⟩
    · simp only [Metric.mem_sphere, dist_zero_right, Pi.norm_single, norm_one]
  let f : (Fin (m + 1) → ℝ) × (Fin m → ℝ) → ℝ :=
    fun z => ‖weightedNewtonTail r z.1 z.2‖
  have hf : Continuous f := (continuous_weightedNewtonTail hm r).norm
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
  have hza : ∀ i, 0 < z.1 i := fun i =>
    hlo.trans_le (hz.1 i (Set.mem_univ i)).1
  have hδ : 0 < f z := by
    change 0 < ‖weightedNewtonTail r z.1 z.2‖
    apply norm_pos_iff.mpr
    intro he
    have hz0 : z.2 = 0 := weightedNewtonTail_injective hm hr z.1 hza (by simpa using he)
    have hz1 : ‖z.2‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
    simp [hz0] at hz1
  refine ⟨f z, hδ, ?_⟩
  intro a ha v
  by_cases hv : v = 0
  · simp [hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), hvpos.ne']
    have hmem : (a, ‖v‖⁻¹ • v) ∈ S := by
      refine ⟨fun i _ => ha i, ?_⟩
      simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have hh := hmin hmem
    change f z ≤ ‖weightedNewtonTail r a (‖v‖⁻¹ • v)‖ at hh
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le),
      ← div_eq_inv_mul] at hh
    exact (le_div_iff₀ hvpos).mp hh

end D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
