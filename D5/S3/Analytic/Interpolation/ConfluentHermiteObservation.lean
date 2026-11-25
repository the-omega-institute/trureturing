/- GID: D5/S3/Analytic/Interpolation/ConfluentHermiteObservation
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ConfluentHermiteObservation
   mirror-E: none(waiver:analytic-observation-bound-without-executable-mirror)
   anchors: []
   utility: none
   digest: Noisy recovery of weighted coefficients from confluent Hermite data. -/

module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.CStarAlgebra.Matrix
import all D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Uniform noisy recovery from Hermite observations

The observations use within derivatives on the closed measurement interval.
Each prefix uses all occurrences of a repeated node. The omitted order-zero
observation corresponds to an arbitrary additive integration constant.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Polynomial
open scoped ContDiff BigOperators

noncomputable section

namespace D5.S3.Analytic.Interpolation.ConfluentHermiteObservation

open ConfluentPositiveSampling

/-! ## Rolle's theorem with multiplicities -/

/-- A run of `k + 1` equal nodes carries the zero of `g k` at its center.
Rolle in a positive gap gives a strict interior zero of `g 1`.
In a degenerate gap the existing first jet supplies the zero. -/
private theorem rolle_nodes_with_jets
    (n : ℕ) (a b : ℝ) (z : ℕ → ℝ) (g : ℕ → ℝ → ℝ)
    (hmono : ∀ i q, i ≤ q → q ≤ n → z i ≤ z q)
    (hz : ∀ i ≤ n, z i ∈ Icc a b)
    (hzero : ∀ i k, i + k ≤ n → z i = z (i + k) → g k (z i) = 0)
    (hc : ∀ k < n, ContinuousOn (g k) (Icc a b))
    (hd : ∀ k < n, ∀ x ∈ Ioo a b, HasDerivAt (g k) (g (k + 1) x) x) :
    ∃ x ∈ Icc a b, g n x = 0 := by
  induction n generalizing z g with
  | zero =>
      exact ⟨z 0, hz 0 (by omega), hzero 0 0 (by omega) rfl⟩
  | succ n ih =>
      have hstep (i : ℕ) : ∃ x : ℝ, i ≤ n →
          z i ≤ x ∧ x ≤ z (i + 1) ∧
            (z i < z (i + 1) → z i < x ∧ x < z (i + 1)) ∧ g 1 x = 0 := by
        by_cases hi : i ≤ n
        · rcases lt_or_eq_of_le (hmono i (i + 1) (by omega) (by omega)) with hlt | heq
          · have hleft := hz i (by omega)
            have hright := hz (i + 1) (by omega)
            obtain ⟨x, hx, hdx⟩ := exists_hasDerivAt_eq_zero (f' := g 1) hlt
              ((hc 0 (by omega)).mono (Icc_subset_Icc hleft.1 hright.2))
              ((hzero i 0 (by omega) rfl).trans
                (hzero (i + 1) 0 (by omega) rfl).symm)
              (fun x hx => hd 0 (by omega) x
                ⟨hleft.1.trans_lt hx.1, hx.2.trans_le hright.2⟩)
            exact ⟨x, fun _ => ⟨hx.1.le, hx.2.le, fun _ => hx, hdx⟩⟩
          · exact ⟨z i, fun _ => ⟨le_rfl, heq.le, fun h => (h.ne heq).elim,
                hzero i 1 (by omega) heq⟩⟩
        · exact ⟨z i, fun h => (hi h).elim⟩
      choose w hw using hstep
      have hwi (i : ℕ) (hi : i ≤ n) : w i ∈ Icc a b :=
        ⟨(hz i (by omega)).1.trans (hw i hi).1,
          (hw i hi).2.1.trans (hz (i + 1) (by omega)).2⟩
      have hwmono : ∀ i q, i ≤ q → q ≤ n → w i ≤ w q := by
        intro i q hi hq
        rcases lt_or_eq_of_le hi with hlt | rfl
        · exact (hw i (by omega)).2.1.trans
            ((hmono (i + 1) q (by omega) (by omega)).trans (hw q hq).1)
        · exact le_rfl
      have hwzero : ∀ i k, i + k ≤ n → w i = w (i + k) →
          g (k + 1) (w i) = 0 := by
        intro i k hik heq
        cases k with
        | zero => exact (hw i (by omega)).2.2.2
        | succ k =>
            let q := i + (k + 1)
            have hq : q ≤ n := hik
            have heq' : w i = w q := heq
            have hi : i ≤ n := by omega
            have hlow := (hw i hi).2.1
            have hmid : z (i + 1) ≤ z q :=
              hmono (i + 1) q (by dsimp [q]; omega) (hq.trans (Nat.le_succ n))
            -- The shared zero meets the inner endpoint of each gap.
            have hright : w i = z (i + 1) :=
              le_antisymm hlow (hmid.trans ((hw q hq).1.trans heq'.symm.le))
            have hleft : z q = w q :=
              le_antisymm (hw q hq).1 (heq'.symm.le.trans (hlow.trans hmid))
            -- A strict gap would have placed its zero away from that endpoint.
            have hiEq : z i = w i := by
              rcases lt_or_eq_of_le ((hw i hi).1) with hlt | heq
              · exact ((ne_of_lt ((hw i hi).2.2.1 (hlt.trans_le hlow)).2) hright).elim
              · exact heq
            have hqEq : w q = z (q + 1) := by
              rcases lt_or_eq_of_le ((hw q hq).2.1) with hlt | heq
              · exact ((ne_of_lt ((hw q hq).2.2.1 ((hw q hq).1.trans_lt hlt)).1) hleft).elim
              · exact heq
            have hends : z i = z (i + (k + 1 + 1)) := by
              simpa only [q, Nat.add_assoc] using hiEq.trans (heq'.trans hqEq)
            rw [← hiEq]
            exact hzero i (k + 1 + 1) (by omega) hends
      exact ih w (fun k => g (k + 1)) hwmono hwi hwzero
        (fun k hk => hc (k + 1) (by omega))
        (fun k hk x hx => hd (k + 1) (by omega) x hx)

private theorem iteratedDeriv_polynomial_eval (p : ℝ[X]) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t => p.eval t) x = (Polynomial.derivative^[n] p).eval x := by
  have hcomm : Function.Semiconj (fun q : ℝ[X] => fun t => q.eval t)
      Polynomial.derivative deriv := by
    intro q
    funext t
    exact (q.deriv).symm
  rw [iteratedDeriv_eq_iterate, ← hcomm.iterate_right n p]

private theorem polynomial_top_deriv (p : ℝ[X]) (n : ℕ) (hp : p.natDegree ≤ n) (x : ℝ) :
    (Polynomial.derivative^[n] p).eval x = (n.factorial : ℝ) * p.coeff n := by
  have hdeg : (Polynomial.derivative^[n] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p n).trans (Nat.sub_eq_zero_of_le hp ▸ le_rfl)
  rw [eq_C_of_natDegree_le_zero hdeg, eval_C, coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

/-- The multiset of node occurrences indexed by `0, ..., n`. -/
private def nodeMultiset (n : ℕ) (z : ℕ → ℝ) : Multiset ℝ :=
  (Multiset.range (n + 1)).map z

private theorem lt_count_of_eq_nodes {n : ℕ} {z : ℕ → ℝ}
    (hmono : ∀ i q, i ≤ q → q ≤ n → z i ≤ z q)
    {i k : ℕ} (hik : i + k ≤ n) (heq : z i = z (i + k)) :
    k < (nodeMultiset n z).count (z i) := by
  let F := (Finset.range (n + 1)).filter (fun q => z i = z q)
  have hcount : (nodeMultiset n z).count (z i) = F.card := by
    exact Multiset.count_map z (Multiset.range (n + 1)) (z i)
  have hsubset : Finset.Icc i (i + k) ⊆ F := by
    intro q hq
    obtain ⟨hiq, hqk⟩ := Finset.mem_Icc.mp hq
    have hqn := hqk.trans hik
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      le_antisymm (hmono i q hiq hqn) ((hmono q (i + k) hqk hik).trans heq.symm.le)⟩
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hcard
  rw [hcount]
  omega

private theorem order_le_of_lt_count {n : ℕ} {z : ℕ → ℝ} {x : ℝ} {k : ℕ}
    (hk : k < (nodeMultiset n z).count x) : k ≤ n := by
  have hcard : (nodeMultiset n z).count x ≤ n + 1 := by
    simpa only [nodeMultiset, Multiset.card_map, Multiset.card_range] using
      Multiset.count_le_card x (nodeMultiset n z)
  omega

/-- The coefficient of degree `n` of a degree-at-most-`n` Hermite polynomial
is the order-`n` within-derivative at a point in the node hull, divided by `n!`.
At each center, `hjet` requires every order below its multiplicity. -/
private theorem hermite_coeff_mean_within
    {n : ℕ} {a b : ℝ} {z : ℕ → ℝ} {f : ℝ → ℝ} {p : ℝ[X]}
    (hab : a < b) (hmono : ∀ i q, i ≤ q → q ≤ n → z i ≤ z q)
    (hz : ∀ i ≤ n, z i ∈ Icc a b)
    (hf : ContDiffOn ℝ n f (Icc a b)) (hp : p.natDegree ≤ n)
    (hjet : ∀ x k, k < (nodeMultiset n z).count x →
      iteratedDerivWithin k f (Icc a b) x = (Polynomial.derivative^[k] p).eval x) :
    ∃ ξ ∈ Icc (z 0) (z n),
      (n.factorial : ℝ) * p.coeff n = iteratedDerivWithin n f (Icc a b) ξ := by
  let P : ℝ → ℝ := fun t => p.eval t
  let g : ℕ → ℝ → ℝ := fun k => iteratedDerivWithin k (f - P) (Icc a b)
  have huniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hP (k : ℕ) : ContDiff ℝ k P := by
    simpa only [P, coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) k
  have hg : ContDiffOn ℝ n (f - P) (Icc a b) := hf.sub (hP n).contDiffOn
  have hsub (k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : x ∈ Icc a b) :
      g k x = iteratedDerivWithin k f (Icc a b) x - (Polynomial.derivative^[k] p).eval x := by
    have hf' : ContDiffWithinAt ℝ k f (Icc a b) x :=
      (hf x hx).of_le (Nat.cast_le.mpr hk)
    have hP' : ContDiffAt ℝ k P x := (hP k).contDiffAt
    change iteratedDerivWithin k (f - P) (Icc a b) x = _
    rw [iteratedDerivWithin_sub hx huniq hf' hP'.contDiffWithinAt,
      iteratedDerivWithin_eq_iteratedDeriv huniq hP' hx]
    exact congrArg (fun v => iteratedDerivWithin k f (Icc a b) x - v)
      (iteratedDeriv_polynomial_eval p k x)
  have hhull : Icc (z 0) (z n) ⊆ Icc a b :=
    Icc_subset_Icc (hz 0 (Nat.zero_le n)).1 (hz n le_rfl).2
  have hnode (i : ℕ) (hi : i ≤ n) : z i ∈ Icc (z 0) (z n) :=
    ⟨hmono 0 i (Nat.zero_le i) hi, hmono i n hi le_rfl⟩
  have hzero (i k : ℕ) (hik : i + k ≤ n) (heq : z i = z (i + k)) : g k (z i) = 0 := by
    rw [hsub k (by omega) (z i) (hz i (by omega))]
    exact sub_eq_zero.mpr (hjet (z i) k (lt_count_of_eq_nodes hmono hik heq))
  have hcont (k : ℕ) (hk : k < n) : ContinuousOn (g k) (Icc (z 0) (z n)) :=
    (hg.continuousOn_iteratedDerivWithin (Nat.cast_le.mpr hk.le) huniq).mono hhull
  have hderiv (k : ℕ) (hk : k < n) (x : ℝ) (hx : x ∈ Ioo (z 0) (z n)) :
      HasDerivAt (g k) (g (k + 1) x) x := by
    have hx' : x ∈ Ioo a b :=
      Ioo_subset_Ioo (hz 0 (Nat.zero_le n)).1 (hz n le_rfl).2 hx
    have hd := hg.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr hk) huniq
      x (Ioo_subset_Icc_self hx')
    change HasDerivAt (iteratedDerivWithin k (f - P) (Icc a b))
      (iteratedDerivWithin (k + 1) (f - P) (Icc a b) x) x
    rw [iteratedDerivWithin_succ]
    exact hd.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hx'.1 hx'.2)
  obtain ⟨ξ, hξ, hξzero⟩ := rolle_nodes_with_jets n (z 0) (z n) z g hmono hnode hzero hcont hderiv
  refine ⟨ξ, hξ, ?_⟩
  rw [hsub n le_rfl ξ (hhull hξ), polynomial_top_deriv p n hp] at hξzero
  exact (sub_eq_zero.mp hξzero).symm

/-! ## Interpolation of prescribed jets -/

/-- The monic product of the linear factors, with one factor per occurrence. -/
private def nodal (s : Multiset ℝ) : ℝ[X] :=
  (s.map fun x => X - C x).prod

@[simp] private theorem nodal_zero : nodal 0 = 1 := by simp [nodal]

@[simp] private theorem nodal_cons (b : ℝ) (s : Multiset ℝ) :
    nodal (b ::ₘ s) = (X - C b) * nodal s := by
  simp only [nodal, Multiset.map_cons, Multiset.prod_cons]

private theorem nodal_monic (s : Multiset ℝ) : (nodal s).Monic :=
  monic_multisetProd_X_sub_C s

private theorem nodal_natDegree (s : Multiset ℝ) : (nodal s).natDegree = s.card :=
  natDegree_multiset_prod_X_sub_C_eq_card s

private theorem nodal_degree (s : Multiset ℝ) : (nodal s).degree = s.card := by
  rw [degree_eq_natDegree (nodal_monic s).ne_zero, nodal_natDegree]

/-- The degree bound uses `degree` so that the empty multiset has interpolant zero. -/
private def IsInterpolant (s : Multiset ℝ) (J : ℝ → ℕ → ℝ) (p : ℝ[X]) : Prop :=
  p.degree < s.card ∧ ∀ x k, k < s.count x → J x k = (Polynomial.derivative^[k] p).eval x

private theorem factorial_ne_zero (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

private theorem eval_iterate_eq_factorial_mul (p : ℝ[X]) (x : ℝ) (k : ℕ) :
    (Polynomial.derivative^[k] p).eval x = (k.factorial : ℝ) * (taylor x p).coeff k := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv k, LinearMap.smul_apply, eval_smul, nsmul_eq_mul]

private theorem taylor_matches_iff (p : ℝ[X]) (x : ℝ) (k : ℕ) (y : ℝ) :
    (taylor x p).coeff k = y / (k.factorial : ℝ) ↔ y = (Polynomial.derivative^[k] p).eval x := by
  rw [eval_iterate_eq_factorial_mul, eq_div_iff (factorial_ne_zero k),
    mul_comm ((taylor x p).coeff k)]
  exact eq_comm

/-- The product at `b` of the remaining factors after removing all occurrences of `b`. -/
private def nodalUnit (s : Multiset ℝ) (b : ℝ) : ℝ :=
  ((s.filter fun x => ¬ b = x).map fun x => b - x).prod

private theorem nodalUnit_ne_zero (s : Multiset ℝ) (b : ℝ) : nodalUnit s b ≠ 0 := by
  unfold nodalUnit
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp hz
  exact (Multiset.mem_filter.mp hx).2 (sub_eq_zero.mp heq)

private theorem taylor_nodal_at_count (s : Multiset ℝ) (b : ℝ) :
    (taylor b (nodal s)).coeff (s.count b) = nodalUnit s b := by
  let U := nodal (s.filter fun x => ¬ b = x)
  have hfactor : nodal s = (X - C b) ^ s.count b * U := by
    calc
      nodal s = nodal (s.filter (Eq b) + s.filter (fun x => ¬ b = x)) :=
        congrArg nodal (Multiset.filter_add_not (Eq b) s).symm
      _ = nodal (s.filter (Eq b)) * U := by
        simp only [U, nodal, Multiset.map_add, Multiset.prod_add]
      _ = _ := by
        rw [Multiset.filter_eq]
        simp only [nodal, Multiset.map_replicate, Multiset.prod_replicate]
  have hU : U.eval b = nodalUnit s b := by
    simp only [U, nodal, nodalUnit, eval_multiset_prod, Multiset.map_map, Function.comp_def,
      eval_sub, eval_X, eval_C]
  rw [hfactor, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right, ← hU]
  simpa only [Nat.zero_add, taylor_coeff_zero] using
    (coeff_X_pow_mul (taylor b U) (s.count b) 0)

private def correction (s : Multiset ℝ) (J : ℝ → ℕ → ℝ) (b : ℝ) (p : ℝ[X]) : ℝ :=
  let r := s.count b
  (J b r / (r.factorial : ℝ) - (taylor b p).coeff r) / nodalUnit s b

private theorem extend_spec {s : Multiset ℝ} {J : ℝ → ℕ → ℝ} {p : ℝ[X]}
    (hp : IsInterpolant s J p) (b : ℝ) :
    IsInterpolant (b ::ₘ s) J (p + C (correction s J b p) * nodal s) := by
  refine ⟨?_, ?_⟩
  · rw [Multiset.card_cons]
    have hmul : (C (correction s J b p) * nodal s).degree ≤ s.card :=
      degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans (nodal_natDegree s).le)
    exact (degree_add_le _ _).trans_lt (max_lt_iff.mpr
      ⟨hp.1.trans (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)),
        hmul.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))⟩)
  · intro x k hk
    apply (taylor_matches_iff _ _ _ _).mp
    rw [map_add, coeff_add, taylor_mul, taylor_C, coeff_C_mul]
    by_cases hold : k < s.count x
    · have hzero : (taylor x (nodal s)).coeff k = 0 := by
        have hjet := (multiset_nodal_dvd_iff_jets s (nodal s)).mp dvd_rfl x k hold
        simpa only [zero_div] using (taylor_matches_iff _ _ _ 0).mpr hjet.symm
      rw [hzero, mul_zero, add_zero]
      exact (taylor_matches_iff _ _ _ _).mpr (hp.2 x k hold)
    · have hx : x = b := by
        by_contra hne
        exact hold (by simpa only [Multiset.count_cons_of_ne hne s] using hk)
      subst x
      have hk' : k = s.count b := by
        rw [Multiset.count_cons_self] at hk
        omega
      subst k
      rw [taylor_nodal_at_count, correction, div_mul_cancel₀ _ (nodalUnit_ne_zero s b)]
      ring

private theorem IsInterpolant.unique {s : Multiset ℝ} {J : ℝ → ℕ → ℝ} {p q : ℝ[X]}
    (hp : IsInterpolant s J p) (hq : IsInterpolant s J q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hne
  have hdvd : nodal s ∣ p - q :=
    (multiset_nodal_dvd_iff_jets s (p - q)).mpr (fun x k hk => by
      rw [iterate_derivative_sub, eval_sub, ← hp.2 x k hk, ← hq.2 x k hk, sub_self])
  have hlow : (s.card : WithBot ℕ) ≤ (p - q).degree := by
    rw [← nodal_degree]
    exact degree_le_of_dvd hdvd hne
  exact (not_lt_of_ge hlow)
    ((degree_sub_le p q).trans_lt (max_lt_iff.mpr ⟨hp.1, hq.1⟩))

private def interpolateList (J : ℝ → ℕ → ℝ) : List ℝ → ℝ[X]
  | [] => 0
  | b :: bs =>
      let p := interpolateList J bs
      p + C (correction (bs : Multiset ℝ) J b p) * nodal (bs : Multiset ℝ)

private theorem interpolateList_spec (J : ℝ → ℕ → ℝ) (l : List ℝ) :
    IsInterpolant (l : Multiset ℝ) J (interpolateList J l) := by
  induction l with
  | nil => simp [IsInterpolant, interpolateList]
  | cons b bs ih => exact extend_spec ih b

/-- The Hermite interpolant of arbitrary real jet data. Sorting selects a list
representative, and uniqueness makes the result independent of processing order. -/
private def interpolant (s : Multiset ℝ) (J : ℝ → ℕ → ℝ) : ℝ[X] :=
  interpolateList J (s.sort (· ≤ ·))

private theorem interpolant_spec (s : Multiset ℝ) (J : ℝ → ℕ → ℝ) :
    IsInterpolant s J (interpolant s J) := by
  simpa only [interpolant, Multiset.sort_eq] using interpolateList_spec J (s.sort (· ≤ ·))

/-- When a polynomial supplies the jets, the interpolant is its monic remainder. -/
private theorem interpolant_eq_remainder_of_jets (s : Multiset ℝ) (J : ℝ → ℕ → ℝ) (p : ℝ[X])
    (hjet : ∀ x k, k < s.count x → J x k = (Polynomial.derivative^[k] p).eval x) :
    interpolant s J = p %ₘ nodal s := by
  refine (interpolant_spec s J).unique ⟨?_, ?_⟩
  · rw [← nodal_degree s]
    exact degree_modByMonic_lt _ (nodal_monic s)
  · have hz := (multiset_nodal_dvd_iff_jets s (p %ₘ nodal s - p)).mp
      (dvd_modByMonic_sub p (nodal s))
    intro x k hk
    have h := hz x k hk
    rw [iterate_derivative_sub, eval_sub] at h
    exact (hjet x k hk).trans (sub_eq_zero.mp h).symm

private theorem remainder_natDegree (p : ℝ[X]) (s : Multiset ℝ) (j : ℕ)
    (hs : s.card = j + 1) : (p %ₘ nodal s).natDegree ≤ j := by
  by_cases hzero : p %ₘ nodal s = 0
  · simp [hzero]
  have h := degree_modByMonic_lt p (nodal_monic s)
  rw [nodal_degree, hs] at h
  exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hzero).mpr h)

private theorem remainder_cons_coeff (p : ℝ[X]) (x : ℝ) (s : Multiset ℝ) (j : ℕ)
    (hs : s.card = j + 1) :
    (p %ₘ nodal (x ::ₘ s)).coeff (j + 1) =
      ((p /ₘ (X - C x)) %ₘ nodal s).coeff j := by
  let q := p /ₘ (X - C x)
  let rem := q %ₘ nodal s
  have hrem : rem.natDegree ≤ j := remainder_natDegree q s j hs
  have hcons : nodal (x ::ₘ s) = (X - C x) * nodal s := by
    simp only [nodal, Multiset.map_cons, Multiset.prod_cons]
  have hdiv : p %ₘ nodal (x ::ₘ s) = C (p.eval x) + (X - C x) * rem := by
    refine (div_modByMonic_unique (q /ₘ nodal s) _ (nodal_monic _) ⟨?_, ?_⟩).2
    · rw [hcons, mul_assoc, add_assoc, ← mul_add]
      change C (p.eval x) + (X - C x) * (q %ₘ nodal s + nodal s * (q /ₘ nodal s)) = p
      rw [modByMonic_add_div, ← modByMonic_X_sub_C_eq_C_eval]
      exact modByMonic_add_div p (X - C x)
    · have hdeg : (C (p.eval x) + (X - C x) * rem).natDegree ≤ j + 1 := by
        apply natDegree_add_le_of_degree_le (by simp)
        have hm := natDegree_mul_le_of_le (p := X - C x) (by simp : (X - C x).natDegree ≤ 1) hrem
        simpa [Nat.add_comm] using hm
      rw [nodal_degree, Multiset.card_cons, hs]
      exact (degree_le_of_natDegree_le hdeg).trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
  rw [hdiv, coeff_add, coeff_X_sub_C_mul,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hrem)]
  simp [rem, q]

private def prefixNodes {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : Multiset ℝ :=
  ((List.ofFn a).take (j.val + 1) : List ℝ)

private theorem card_prefixNodes {n : ℕ} (a : Fin n → ℝ) (j : Fin n) :
    (prefixNodes a j).card = j.val + 1 := by
  simp [prefixNodes]

private theorem newtonData_eq_remainder_coeff {n : ℕ} (a : Fin n → ℝ) (p : ℝ[X])
    (j : Fin n) :
    polynomialNewtonData a p j = (p %ₘ nodal (prefixNodes a j)).coeff j.val := by
  induction n generalizing p with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rw [polynomialNewtonData_zero]
        have hpref : prefixNodes a 0 = a 0 ::ₘ 0 := by
          simp [prefixNodes, List.ofFn_succ]
        rw [hpref]
        simp [nodal, modByMonic_X_sub_C_eq_C_eval]
      · have hpref : prefixNodes a k.succ =
            a 0 ::ₘ prefixNodes (fun i : Fin n => a i.succ) k := by
          simp [prefixNodes, List.ofFn_succ]
        rw [polynomialNewtonData_succ, hpref, Fin.val_succ, remainder_cons_coeff _ _ _ _
          (card_prefixNodes _ k)]
        exact ih _ _ _

private theorem interpolant_natDegree_le {s : Multiset ℝ} {n : ℕ}
    (hs : s.card = n + 1) (J : ℝ → ℕ → ℝ) : (interpolant s J).natDegree ≤ n := by
  by_cases h0 : interpolant s J = 0
  · simp [h0]
  have hd := (interpolant_spec s J).1
  rw [hs, degree_eq_natDegree h0] at hd
  exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hd)

private theorem prefix_mean {s : Multiset ℝ} {n : ℕ} {lo hi : ℝ} {f : ℝ → ℝ}
    (hs : s.card = n + 1) (hinterval : lo < hi) (hmem : ∀ x ∈ s, x ∈ Icc lo hi)
    (hf : ContDiffOn ℝ n f (Icc lo hi)) :
    ∃ ξ ∈ Icc lo hi, (n.factorial : ℝ) *
      (interpolant s (fun x k => iteratedDerivWithin k f (Icc lo hi) x)).coeff n =
        iteratedDerivWithin n f (Icc lo hi) ξ := by
  let l := s.sort (· ≤ ·)
  let z : ℕ → ℝ := fun i => (l[i]?).getD lo
  have hl : l.length = n + 1 := (Multiset.length_sort (s := s) (· ≤ ·)).trans hs
  have hzval (i : ℕ) (hi : i < l.length) : z i = l[i]'hi := by
    simp only [z, List.getElem?_eq_getElem hi, Option.getD_some]
  have hlist : (List.range (n + 1)).map z = l := by
    apply List.ext_getElem
    · simp [hl]
    · intro i _ hi
      rw [List.getElem_map, List.getElem_range, hzval i hi]
  have hmultiset : nodeMultiset n z = s := by
    change (↑((List.range (n + 1)).map z) : Multiset ℝ) = s
    rw [hlist]
    exact Multiset.sort_eq s (· ≤ ·)
  have hzmem (i : ℕ) (hi : i ≤ n) : z i ∈ s := by
    have hi' : i < l.length := by rw [hl]; omega
    rw [hzval i hi']
    exact (Multiset.mem_sort (s := s) (· ≤ ·)).mp (List.getElem_mem hi')
  have hmono : ∀ i q, i ≤ q → q ≤ n → z i ≤ z q := by
    intro i q hi hq
    rcases lt_or_eq_of_le hi with hiq | rfl
    · have hi' : i < l.length := by rw [hl]; omega
      have hq' : q < l.length := by rw [hl]; omega
      rw [hzval i hi', hzval q hq']
      exact List.pairwise_iff_getElem.mp (Multiset.pairwise_sort s (· ≤ ·)) i q hi' hq' hiq
    · exact le_rfl
  obtain ⟨ξ, hξ, hmean⟩ := hermite_coeff_mean_within hinterval hmono
    (fun i hi => hmem _ (hzmem i hi)) hf
    (interpolant_natDegree_le hs _)
    (by rw [hmultiset]; exact (interpolant_spec s _).2)
  exact ⟨ξ, Icc_subset_Icc (hmem _ (hzmem 0 (Nat.zero_le n))).1
    (hmem _ (hzmem n le_rfl)).2 hξ, hmean⟩

/-! ## Nonconstant prefix observations -/

/-- The coordinate indexed by `j : Fin m` is the coefficient of degree
`j.val + 1` of the Hermite interpolant on the first `j.val + 2` occurrences.
Jets are within the supplied observation interval. -/
def hermiteTail {m : ℕ} (lo hi : ℝ) (a : Fin (m + 1) → ℝ)
    (f : ℝ → ℝ) : Fin m → ℝ :=
  fun j => (interpolant (prefixNodes a j.succ)
    (fun x k => iteratedDerivWithin k f (Icc lo hi) x)).coeff (j.val + 1)

private theorem prefixNodes_mem {n : ℕ} {lo hi : ℝ} {a : Fin n → ℝ}
    (ha : ∀ i, a i ∈ Icc lo hi) (j : Fin n) :
    ∀ x ∈ prefixNodes a j, x ∈ Icc lo hi := by
  intro x hx
  change x ∈ (List.ofFn a).take (j.val + 1) at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
  exact ha i

private theorem hermiteTail_polynomial {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (hinterval : lo < hi) (ha : ∀ i, a i ∈ Icc lo hi) (p : ℝ[X]) :
    hermiteTail lo hi a (fun x => p.eval x) = polynomialNewtonData a p ∘ Fin.succ := by
  funext j
  change (interpolant (prefixNodes a j.succ)
    (fun x k => iteratedDerivWithin k (fun t => p.eval t) (Icc lo hi) x)).coeff _ =
      polynomialNewtonData a p j.succ
  rw [newtonData_eq_remainder_coeff, Fin.val_succ]
  apply congrArg (fun q : ℝ[X] => q.coeff (j.val + 1))
  apply interpolant_eq_remainder_of_jets
  intro x k hk
  have hx := prefixNodes_mem ha j.succ x (Multiset.count_pos.mp (by omega : 0 < _))
  have hp : ContDiffAt ℝ k (fun t => p.eval t) x := by
    simpa only [coe_aeval_eq_eval] using (p.contDiff_aeval (𝕜 := ℝ) k).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hinterval) hp hx]
  exact iteratedDeriv_polynomial_eval p k x

private theorem hermiteTail_congr {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (ha : ∀ i, a i ∈ Icc lo hi) {f g : ℝ → ℝ} (hfg : EqOn f g (Icc lo hi)) :
    hermiteTail lo hi a f = hermiteTail lo hi a g := by
  funext j
  unfold hermiteTail
  apply congrArg (fun p : ℝ[X] => p.coeff (j.val + 1))
  apply (interpolant_spec (prefixNodes a j.succ) _).unique
  refine ⟨(interpolant_spec _ _).1, fun x k hk => ?_⟩
  have hx := prefixNodes_mem ha j.succ x (Multiset.count_pos.mp (by omega : 0 < _))
  exact (iteratedDerivWithin_congr hfg hx).trans
    ((interpolant_spec _ (fun y n => iteratedDerivWithin n g (Icc lo hi) y)).2 x k hk)

private theorem hermiteTail_add {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (hinterval : lo < hi) (ha : ∀ i, a i ∈ Icc lo hi) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ m f (Icc lo hi)) (hg : ContDiffOn ℝ m g (Icc lo hi)) :
    hermiteTail lo hi a (fun x => f x + g x) = hermiteTail lo hi a f + hermiteTail lo hi a g := by
  funext j
  let s := prefixNodes a j.succ
  let Pf := interpolant s (fun x k => iteratedDerivWithin k f (Icc lo hi) x)
  let Pg := interpolant s (fun x k => iteratedDerivWithin k g (Icc lo hi) x)
  change (interpolant s (fun x k => iteratedDerivWithin k (f + g) (Icc lo hi) x)).coeff _ =
    Pf.coeff _ + Pg.coeff _
  rw [← coeff_add]
  apply congrArg (fun p : ℝ[X] => p.coeff (j.val + 1))
  apply (interpolant_spec s _).unique
  refine ⟨(degree_add_le _ _).trans_lt
    (max_lt (interpolant_spec _ _).1 (interpolant_spec _ _).1), ?_⟩
  intro x k hk
  have hx := prefixNodes_mem ha j.succ x
    (Multiset.count_pos.mp ((Nat.zero_le k).trans_lt hk))
  have hcard := (Multiset.count_le_card x s).trans_eq (card_prefixNodes a j.succ)
  have hkm : k ≤ m := by have := j.isLt; change k < s.count x at hk; omega
  change iteratedDerivWithin k (f + g) (Icc lo hi) x = _
  have hfjet := (interpolant_spec s (fun y n => iteratedDerivWithin n f (Icc lo hi) y)).2 x k hk
  have hgjet := (interpolant_spec s (fun y n => iteratedDerivWithin n g (Icc lo hi) y)).2 x k hk
  rw [iteratedDerivWithin_add hx (uniqueDiffOn_Icc hinterval)
    ((hf x hx).of_le (Nat.cast_le.mpr hkm)) ((hg x hx).of_le (Nat.cast_le.mpr hkm)),
    iterate_map_add Polynomial.derivative k Pf Pg, eval_add]
  exact congrArg₂ (· + ·) hfjet hgjet

private theorem hermiteTail_const {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (hinterval : lo < hi) (ha : ∀ i, a i ∈ Icc lo hi) (K : ℝ) :
    hermiteTail lo hi a (fun _ => K) = 0 := by
  have heq : (fun _ : ℝ => K) = fun x => (C K : ℝ[X]).eval x := by simp
  rw [heq, hermiteTail_polynomial hinterval ha]
  funext j
  rw [Function.comp_apply, newtonData_eq_remainder_coeff]
  have hdeg : (C K : ℝ[X]).degree < (nodal (prefixNodes a j.succ)).degree := by
    rw [nodal_degree, card_prefixNodes]
    exact (degree_C_le (a := K)).trans_lt (by exact_mod_cast Nat.succ_pos j.succ.val)
  rw [(modByMonic_eq_self_iff (nodal_monic _)).mpr hdeg, Fin.val_succ]
  exact coeff_C_of_ne_zero (Nat.succ_ne_zero j.val)

private theorem hermiteTail_weighted {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (hinterval : lo < hi) (ha : ∀ i, a i ∈ Icc lo hi) (r : ℕ) (v : Fin m → ℝ) :
    hermiteTail lo hi a (fun x => ((X : ℝ[X]) ^ r * Polynomial.ofFn m v).eval x) =
      weightedNewtonTail r a v := by
  rw [hermiteTail_polynomial hinterval ha]
  funext j
  exact polynomialNewtonData_succ a _ j

private theorem hermiteTail_remainder_bound {m : ℕ} {lo hi : ℝ} {a : Fin (m + 1) → ℝ}
    (hinterval : lo < hi) (ha : ∀ i, a i ∈ Icc lo hi) {E : ℝ → ℝ}
    (hE : ContDiffOn ℝ m E (Icc lo hi)) (B : Fin m → ℝ)
    (hB : ∀ j x, x ∈ Icc lo hi →
      ‖iteratedDerivWithin (j.val + 1) E (Icc lo hi) x‖ ≤ B j) :
    ‖hermiteTail lo hi a E‖ ≤ ‖fun j => B j / ((j.val + 1).factorial : ℝ)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  have hj : j.val + 1 ≤ m := j.isLt
  obtain ⟨x, hx, hm⟩ := prefix_mean (card_prefixNodes a j.succ) hinterval
    (prefixNodes_mem ha j.succ) (hE.of_le (Nat.cast_le.mpr hj))
  have hfac : 0 < ((j.val + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have heq : ((j.val + 1).factorial : ℝ) * hermiteTail lo hi a E j =
      iteratedDerivWithin (j.val + 1) E (Icc lo hi) x := hm
  have hb : ‖hermiteTail lo hi a E j‖ ≤ B j / ((j.val + 1).factorial : ℝ) := by
    apply (le_div_iff₀ hfac).mpr
    simpa only [norm_mul, Real.norm_of_nonneg hfac.le, mul_comm] using
      (congrArg norm heq).le.trans (hB j x hx)
  exact hb.trans ((le_abs_self _).trans (norm_le_pi_norm
    (fun j => B j / ((j.val + 1).factorial : ℝ)) j))

/-- Uniform recovery from smooth observations of a weighted polynomial with
an arbitrary additive constant and an interval-local remainder. The error
budget for derivative order `j + 1` is divided by its factorial. -/
theorem hermiteTail_noisy_recovery {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    {lo hi : ℝ} (hlo : 0 < lo) (hinterval : lo < hi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Icc lo hi) →
      ∀ (v : Fin m → ℝ) (K : ℝ) (F E : ℝ → ℝ) (B : Fin m → ℝ),
        EqOn F (fun x => K + x ^ r * (Polynomial.ofFn m v).eval x + E x) (Icc lo hi) →
        ContDiffOn ℝ m E (Icc lo hi) →
        (∀ j x, x ∈ Icc lo hi → ‖iteratedDerivWithin (j.val + 1) E (Icc lo hi) x‖ ≤ B j) →
        δ * ‖v‖ ≤ ‖hermiteTail lo hi a F‖ + ‖fun j => B j / ((j.val + 1).factorial : ℝ)‖ := by
  obtain ⟨δ, hδ, hbound⟩ := weightedNewtonTail_uniform_lower hm hr lo hi hlo hinterval.le
  refine ⟨δ, hδ, ?_⟩
  intro a ha v K F E B hF hE hB
  let P : ℝ → ℝ := fun x => ((X : ℝ[X]) ^ r * Polynomial.ofFn m v).eval x
  have hP : ContDiffOn ℝ m P (Icc lo hi) := by
    simpa only [P, coe_aeval_eq_eval] using
      (((X : ℝ[X]) ^ r * Polynomial.ofFn m v).contDiff_aeval (𝕜 := ℝ) m).contDiffOn
  have hK : ContDiffOn ℝ m (fun _ : ℝ => K) (Icc lo hi) := contDiffOn_const
  have hKP : ContDiffOn ℝ m (fun x => K + P x) (Icc lo hi) := hK.add hP
  have hF' : EqOn F (fun x => K + P x + E x) (Icc lo hi) := by
    simpa only [P, eval_mul, eval_pow, eval_X] using hF
  have hdata := hermiteTail_congr ha hF'
  rw [hermiteTail_add hinterval ha hKP hE, hermiteTail_add hinterval ha hK hP,
    hermiteTail_const hinterval ha, zero_add, hermiteTail_weighted hinterval ha] at hdata
  calc
    δ * ‖v‖ ≤ ‖weightedNewtonTail r a v‖ := hbound a ha v
    _ = ‖hermiteTail lo hi a F - hermiteTail lo hi a E‖ := by rw [hdata, add_sub_cancel_right]
    _ ≤ ‖hermiteTail lo hi a F‖ + ‖hermiteTail lo hi a E‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add_right (hermiteTail_remainder_bound hinterval ha hE B hB) _

/-! ## Two-port operator norm estimate -/

open scoped Matrix.Norms.Frobenius in
private theorem opNorm_le_of_entry_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (K : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ K) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ 2 * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA 0 0)
  have hF : ‖A‖ ≤ 2 * K := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
    calc
      √(∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ √((2 * K) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc
          (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, K ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hA i j) _
          _ = (2 * K) ^ 2 := by simp; ring
      _ = 2 * K := Real.sqrt_sq (by positivity)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit x.ofLp)
  have hcol : A * Matrix.replicateCol Unit x.ofLp =
      Matrix.replicateCol Unit (A.mulVec x.ofLp) := by
    ext i j
    rfl
  rw [hcol, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h
  exact h.trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))

open scoped Matrix.Norms.L2Operator

private theorem entry_norm_le_opNorm (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 j 1
  calc
    ‖A i j‖ = ‖((EuclideanSpace.equiv (Fin 2) ℝ).symm (A.mulVec e.ofLp)) i‖ := by
      simp [e, PiLp.ofLp_single]
    _ ≤ ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (A.mulVec e.ofLp)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ * ‖e‖ := A.l2_opNorm_mulVec e
    _ = ‖A‖ := by simp [e]

/-- The same prefix measurements applied to each entry of a two-port observation. -/
def matrixHermiteTail {m : ℕ} (lo hi : ℝ) (a : Fin (m + 1) → ℝ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Fin m → Matrix (Fin 2) (Fin 2) ℝ :=
  fun k i j => hermiteTail lo hi a (fun x => F x i j) k

/-- Uniform recovery in the sup norm of the Euclidean operator norms.
The factor two comes from assembling the four scalar entry estimates. -/
theorem matrixHermiteTail_noisy_recovery {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    {lo hi : ℝ} (hlo : 0 < lo) (hinterval : lo < hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Icc lo hi) →
      ∀ (v : Fin m → Matrix (Fin 2) (Fin 2) ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ)
        (F E : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Fin m → ℝ),
        EqOn F (fun x i j =>
          K i j + x ^ r * (Polynomial.ofFn m (fun k => v k i j)).eval x + E x i j)
          (Icc lo hi) →
        (∀ i j, ContDiffOn ℝ m (fun x => E x i j) (Icc lo hi)) →
        (∀ k x, x ∈ Icc lo hi →
          let D : Matrix (Fin 2) (Fin 2) ℝ :=
            fun i j => iteratedDerivWithin (k.val + 1) (fun t => E t i j) (Icc lo hi) x
          ‖D‖ ≤ B k) →
        ‖v‖ ≤ C * (‖matrixHermiteTail lo hi a F‖ +
          ‖fun k => B k / ((k.val + 1).factorial : ℝ)‖) := by
  obtain ⟨δ, hδ, hbound⟩ := hermiteTail_noisy_recovery hm hr hlo hinterval
  refine ⟨2 / δ, div_pos (by norm_num) hδ, ?_⟩
  intro a ha v K F E B hF hE hB
  let M := ‖matrixHermiteTail lo hi a F‖ + ‖fun k => B k / ((k.val + 1).factorial : ℝ)‖
  have hM : 0 ≤ M := add_nonneg (norm_nonneg _) (norm_nonneg _)
  change ‖v‖ ≤ 2 / δ * M
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (div_nonneg (by norm_num) hδ.le) hM)).mpr ?_
  intro k
  rw [div_mul_eq_mul_div, mul_div_assoc, ← Matrix.l2_opNorm_toEuclideanCLM]
  apply opNorm_le_of_entry_bound
  intro i j
  have hD := hbound a ha (fun ℓ => v ℓ i j) (K i j) (fun x => F x i j)
    (fun x => E x i j) B (fun x hx => congrFun (congrFun (hF hx) i) j) (hE i j)
    (fun ℓ x hx => (entry_norm_le_opNorm
      (fun u w => iteratedDerivWithin (ℓ.val + 1) (fun t => E t u w) (Icc lo hi) x) i j).trans
        (hB ℓ x hx))
  have hObs : ‖hermiteTail lo hi a (fun x => F x i j)‖ ≤ ‖matrixHermiteTail lo hi a F‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun ℓ => ?_
    exact (entry_norm_le_opNorm (matrixHermiteTail lo hi a F ℓ) i j).trans (norm_le_pi_norm _ ℓ)
  apply (le_div_iff₀ hδ).mpr
  calc
    ‖v k i j‖ * δ ≤ δ * ‖(fun ℓ => v ℓ i j : Fin m → ℝ)‖ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun ℓ => v ℓ i j) k) hδ.le
    _ ≤ M := hD.trans (add_le_add hObs le_rfl)

end D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
