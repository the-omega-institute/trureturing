/- GID: D5/S3/Zeros/Jensen/JensenSimpleRealStability
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/JensenSimpleRealStability
   mirror-E: none(waiver:polynomial-perturbation)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Liouville]
   utility: none
   digest: Complex uniform approximation preserves all simple real polynomial roots with a uniform derivative margin. -/
import D5.S3.Zeros.Jensen.JensenHermiteScaling
import D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.JensenSimpleRealStability
open Set Polynomial Metric Filter
open D5.S3.Zeros.Jensen
open D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open scoped BigOperators Topology

private theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ b : ℝ, 0 < b ∧ ∀ i, b ≤ f i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image f)
  obtain ⟨b, hb, hmin⟩ := s.exists_min_image id (by simp [s])
  refine ⟨b, ?_, fun i => hmin _ (by simp [s])⟩
  rcases Finset.mem_insert.mp hb with h | h
  · simpa [h]
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact hf i

private theorem enumerate_real_simple_roots (p : ℝ[X]) (m : ℕ)
    (hmonic : p.Monic) (hdegree : p.natDegree = m)
    (hreal : ∀ z : ℂ, aeval z p = 0 → z.im = 0)
    (hsimple : ∀ z : ℂ, aeval z p = 0 → aeval z p.derivative ≠ 0) :
    ∃ r : Fin m → ℝ, Function.Injective r ∧
      ∀ i, p.eval (r i) = 0 ∧ p.derivative.eval (r i) ≠ 0 := by
  classical
  let P := p.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := (hmonic.map (algebraMap ℝ ℂ)).ne_zero
  have hn : P.roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro z
    rw [Polynomial.count_roots]
    by_contra h
    have hmul : 1 < P.rootMultiplicity z := by omega
    have hz := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mp hmul
    have hpz : aeval z p = 0 := by simpa [P, Polynomial.eval_map, Polynomial.aeval_def, Polynomial.IsRoot] using hz.1
    apply hsimple z hpz
    simpa only [P, derivative_map, Polynomial.eval_map, Polynomial.aeval_def, Polynomial.IsRoot] using hz.2
  have hcard : P.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup hn,
      ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
    exact (hmonic.natDegree_map _).trans hdegree
  let e : P.roots.toFinset ≃ Fin m := Finset.equivFinOfCardEq hcard
  have hz (i : Fin m) : aeval (e.symm i).val p = 0 := by
    have hmem : (e.symm i).val ∈ P.roots := by
      simpa only [Multiset.mem_toFinset] using (e.symm i).property
    simpa [P, Polynomial.eval_map, Polynomial.aeval_def, Polynomial.IsRoot] using (Polynomial.mem_roots hP).mp hmem
  have him (i : Fin m) := hreal _ (hz i)
  have heq (i : Fin m) : (((e.symm i).val.re : ℝ) : ℂ) = (e.symm i).val := by
    apply Complex.ext <;> simp [him i]
  let r : Fin m → ℝ := fun i => (e.symm i).val.re
  refine ⟨r, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    rw [← heq i, ← heq j]
    exact congrArg Complex.ofReal hij
  · intro i
    have hcast (f : ℝ[X]) : aeval (r i : ℂ) f = ((f.eval (r i) : ℝ) : ℂ) := by
      exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (R := ℝ) (A := ℂ) (r i) f
    have h0 := hz i
    rw [← heq i, hcast] at h0
    have hd := hsimple _ (hz i)
    rw [← heq i, hcast] at hd
    exact ⟨Complex.ofReal_injective (by simpa using h0), fun h => hd (by simp [h])⟩

private theorem simple_root_interval (p : ℝ[X]) (a : ℝ)
    (ha : p.eval a = 0) (hd : p.derivative.eval a ≠ 0) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ eta : ℝ, 0 < eta → eta ≤ rho →
      p.eval (a - eta) * p.eval (a + eta) < 0 ∧
        ∀ x ∈ Icc (a - eta) (a + eta),
          |p.derivative.eval a| / 2 ≤ |p.derivative.eval x| := by
  let Q := p /ₘ (X - C a)
  have hfac : p = (X - C a) * Q :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  have hQ : Q.eval a ≠ 0 := by
    have he : p.derivative.eval a = Q.eval a := by rw [hfac, derivative_mul]; simp
    exact he ▸ hd
  have hgood : ∀ᶠ x in 𝓝 a,
      0 < Q.eval x * Q.eval a ∧ |p.derivative.eval a| / 2 < |p.derivative.eval x| := by
    apply Filter.Eventually.and
    · exact (Q.continuous.mul_const (Q.eval a)).continuousAt.eventually
        (eventually_gt_nhds (by simpa [sq] using sq_pos_of_ne_zero hQ))
    · exact p.derivative.continuous.abs.continuousAt.eventually
        (eventually_gt_nhds (by linarith [abs_pos.mpr hd]))
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨eps / 2, by positivity, ?_⟩
  intro eta heta hetaeps
  have hg (x : ℝ) (hx : x ∈ Icc (a - eta) (a + eta)) :=
    hball (show dist x a < eps by rw [Real.dist_eq]; apply abs_lt.mpr; constructor <;> linarith [hx.1, hx.2])
  refine ⟨?_, fun x hx => (hg x hx).2.le⟩
  have hleft := (hg (a - eta) ⟨le_rfl, by linarith⟩).1
  have hright := (hg (a + eta) ⟨by linarith, le_rfl⟩).1
  have hprod : 0 < (Q.eval (a - eta) * Q.eval (a + eta)) * Q.eval a ^ 2 := by
    calc
      0 < (Q.eval (a - eta) * Q.eval a) * (Q.eval (a + eta) * Q.eval a) :=
        mul_pos hleft hright
      _ = _ := by ring
  have hpos : 0 < Q.eval (a - eta) * Q.eval (a + eta) :=
    pos_of_mul_pos_left hprod (sq_nonneg _)
  rw [hfac]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  nlinarith [sq_pos_of_pos heta]

/-- Uniform complex error controls the derivative on each contained unit disk. -/
private theorem unit_subdisk_derivative_error (P Q : ℂ[X]) (q eps : ℝ)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ q → ‖P.eval z - Q.eval z‖ ≤ eps)
    (z : ℂ) (hz : ‖z‖ ≤ q - 1) :
    ‖P.derivative.eval z - Q.derivative.eval z‖ ≤ eps := by
  have hdiff : DiffContOnCl ℂ (fun w => P.eval w - Q.eval w) (ball z 1) :=
    ⟨(P.differentiable.sub Q.differentiable).differentiableOn,
      (P.continuous.sub Q.continuous).continuousOn⟩
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1)
    hdiff (fun w hw => hbound w (by
      have hn := norm_add_le (w - z) z
      rw [sub_add_cancel] at hn
      rw [mem_sphere_iff_norm.mp hw] at hn
      linarith))
  have hd : HasDerivAt (fun w => P.eval w - Q.eval w)
      (P.derivative.eval z - Q.derivative.eval z) z := by
    simpa only [Pi.sub_def] using (P.hasDerivAt z).sub (Q.hasDerivAt z)
  rw [hd.deriv] at hC
  simpa only [div_one] using hC

/-- Every simple real root persists, with a common lower bound for its derivative. -/
theorem simple_real_polynomial_stability (p : ℝ[X]) (m : ℕ)
    (hmonic : p.Monic) (hdegree : p.natDegree = m)
    (hreal : ∀ z : ℂ, aeval z p = 0 → z.im = 0)
    (hsimple : ∀ z : ℂ, aeval z p = 0 → aeval z p.derivative ≠ 0)
    (Q : ℕ → ℂ[X]) (hQreal : ∀ n (x : ℝ), ((Q n).eval (x : ℂ)).im = 0)
    (happrox : ∀ q : ℝ, 2 ≤ q → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, 1 ≤ n ∧ ∀ z : ℂ, ‖z‖ ≤ q →
        ‖(Q n).eval z - aeval z p‖ ≤ C / Real.sqrt n) :
    ∃ R chi : ℝ, 1 ≤ R ∧ 0 < chi ∧ ∃ N : ℕ,
      ∀ n ≥ N, 1 ≤ n ∧ ∃ u : Fin m → ℝ, Function.Injective u ∧
        (∀ i, |u i| ≤ R) ∧ (∀ i, (Q n).eval (u i : ℂ) = 0) ∧
        (∀ i, chi ≤ ‖(Q n).derivative.eval (u i : ℂ)‖) := by
  classical
  obtain ⟨r, hinj, hroot⟩ := enumerate_real_simple_roots p m hmonic hdegree hreal hsimple
  choose rho hrho hinterval using (fun i => simple_root_interval p (r i) (hroot i).1 (hroot i).2)
  obtain ⟨b, hb, hbrho⟩ := finite_positive_lower_bound rho hrho
  obtain ⟨s, hs, hssep⟩ := finite_positive_lower_bound
    (fun ij : Fin m × Fin m => if ij.1 = ij.2 then 1 else |r ij.1 - r ij.2|)
    (by intro ij; split_ifs with h; norm_num; exact abs_pos.mpr (sub_ne_zero.mpr (hinj.ne h)))
  let eta := min (b / 2) (s / 3)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetarho (i : Fin m) : eta ≤ rho i :=
    (min_le_left _ _).trans ((by linarith : b / 2 ≤ b).trans (hbrho i))
  have hintervals (i : Fin m) := hinterval i eta heta (hetarho i)
  obtain ⟨chi, hchi, hchile⟩ := finite_positive_lower_bound
    (fun i => |p.derivative.eval (r i)| / 2)
    (fun i => div_pos (abs_pos.mpr (hroot i).2) (by norm_num))
  obtain ⟨B, hB, hBle⟩ := finite_positive_lower_bound
    (fun i => min |p.eval (r i - eta)| |p.eval (r i + eta)|)
    (fun i => lt_min
      (abs_pos.mpr (fun h => by simpa [h] using (hintervals i).1))
      (abs_pos.mpr (fun h => by simpa [h] using (hintervals i).1)))
  let R := 1 + ∑ i : Fin m, (|r i| + eta)
  have hR : 1 ≤ R := by
    have hsum : 0 ≤ ∑ i : Fin m, (|r i| + eta) := Finset.sum_nonneg (fun i _ => by positivity)
    dsimp [R]; linarith
  have hri (i : Fin m) : |r i| + eta ≤ R := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => |r i| + eta) (fun i _ => by positivity) (Finset.mem_univ i)
    dsimp [R]; linarith
  obtain ⟨C, hC, N, hN⟩ := happrox (R + 2) (by linarith)
  have hlim : Tendsto (fun n : ℕ => C / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop, C / Real.sqrt n < min (B / 2) (chi / 2) :=
    hlim.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨Nsmall, hsmall⟩ := Filter.eventually_atTop.mp hev
  refine ⟨R, chi / 2, hR, by positivity, max N Nsmall, ?_⟩
  intro n hn
  obtain ⟨hn1, herr⟩ := hN n ((le_max_left _ _).trans hn)
  have hsmall := hsmall n ((le_max_right _ _).trans hn)
  have hval (i : Fin m) (x : ℝ) (hx : x ∈ Icc (r i - eta) (r i + eta)) :
      |((Q n).eval (x : ℂ)).re - p.eval x| < B / 2 := by
    have hxnorm : ‖(x : ℂ)‖ ≤ R + 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have : |x| ≤ |r i| + eta := by
        apply abs_le.mpr
        constructor <;> linarith [hx.1, hx.2, le_abs_self (r i), neg_abs_le (r i)]
      linarith [hri i]
    have hpcast : aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) := by
      exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (R := ℝ) (A := ℂ) x p
    have hh := (Complex.abs_re_le_norm ((Q n).eval (x : ℂ) - aeval (x : ℂ) p)).trans (herr _ hxnorm)
    rw [hpcast] at hh
    simpa only [Complex.sub_re, Complex.ofReal_re] using hh.trans_lt (hsmall.trans_le (min_le_left _ _))
  have hnode (i : Fin m) : ∃ x ∈ Ioo (r i - eta) (r i + eta), (Q n).eval (x : ℂ) = 0 := by
    let g : ℝ → ℝ := fun x => ((Q n).eval (x : ℂ)).re
    have hgl := hval i (r i - eta) ⟨le_rfl, by linarith⟩
    have hgr := hval i (r i + eta) ⟨by linarith, le_rfl⟩
    have hbl : B ≤ |p.eval (r i - eta)| := (hBle i).trans (min_le_left _ _)
    have hbr : B ≤ |p.eval (r i + eta)| := (hBle i).trans (min_le_right _ _)
    have hsign : g (r i - eta) * g (r i + eta) < 0 := by
      rcases mul_neg_iff.mp (hintervals i).1 with h | h
      · rw [abs_of_pos h.1] at hbl
        rw [abs_of_neg h.2] at hbr
        exact mul_neg_of_pos_of_neg (by dsimp [g]; linarith [(abs_lt.mp hgl).1])
          (by dsimp [g]; linarith [(abs_lt.mp hgr).2])
      · rw [abs_of_neg h.1] at hbl
        rw [abs_of_pos h.2] at hbr
        exact mul_neg_of_neg_of_pos (by dsimp [g]; linarith [(abs_lt.mp hgl).2])
          (by dsimp [g]; linarith [(abs_lt.mp hgr).1])
    have hcont : ContinuousOn g (Icc (r i - eta) (r i + eta)) :=
      (Complex.continuous_re.comp ((Q n).continuous.comp Complex.continuous_ofReal)).continuousOn
    have hex : ∃ x ∈ Icc (r i - eta) (r i + eta), g x = 0 := by
      rcases mul_neg_iff.mp hsign with h | h
      · exact intermediate_value_Icc' (by linarith) hcont ⟨h.2.le, h.1.le⟩
      · exact intermediate_value_Icc (by linarith) hcont ⟨h.1.le, h.2.le⟩
    obtain ⟨x, hx, hx0⟩ := hex
    have hleft : x ≠ r i - eta := by intro he; subst x; rw [hx0, zero_mul] at hsign; linarith
    have hright : x ≠ r i + eta := by intro he; subst x; rw [hx0, mul_zero] at hsign; linarith
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hleft), lt_of_le_of_ne hx.2 hright⟩, ?_⟩
    apply Complex.ext
    · exact hx0
    · exact hQreal n x
  choose u hu hzero using hnode
  refine ⟨hn1, u, ?_, ?_, hzero, ?_⟩
  · intro i j he
    by_contra hne
    have hsep := hssep (i, j)
    simp only [if_neg hne] at hsep
    have hetas : eta ≤ s / 3 := min_le_right _ _
    have hdist : |r i - r j| < 2 * eta := by
      apply abs_lt.mpr
      constructor <;> linarith [(hu i).1, (hu i).2, (hu j).1, (hu j).2]
    linarith
  · intro i
    apply abs_le.mpr
    constructor <;> linarith [(hu i).1, (hu i).2, hri i, le_abs_self (r i), neg_abs_le (r i)]
  · intro i
    have huR : ‖(u i : ℂ)‖ ≤ R + 2 - 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have : |u i| ≤ |r i| + eta := by
        apply abs_le.mpr
        constructor <;> linarith [(hu i).1, (hu i).2, le_abs_self (r i), neg_abs_le (r i)]
      linarith [hri i]
    have hd := unit_subdisk_derivative_error (Q n) (p.map (algebraMap ℝ ℂ))
      (R + 2) (C / Real.sqrt n) (by simpa only [Polynomial.eval_map, Polynomial.aeval_def] using herr) (u i) huR
    have hpcast : (p.map (algebraMap ℝ ℂ)).derivative.eval (u i : ℂ) =
        ((p.derivative.eval (u i) : ℝ) : ℂ) := by
      rw [derivative_map]
      exact Polynomial.eval_map_apply (algebraMap ℝ ℂ) (u i)
    rw [hpcast] at hd
    have hlower := (hchile i).trans ((hintervals i).2 _ ⟨(hu i).1.le, (hu i).2.le⟩)
    have hnrm := norm_sub_norm_le (((p.derivative.eval (u i) : ℝ) : ℂ)) ((Q n).derivative.eval (u i : ℂ))
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at hnrm
    linarith [(hsmall.trans_le (min_le_right _ _))]

#print axioms simple_real_polynomial_stability
private theorem hermite_derivative (m : ℕ) :
    (Polynomial.hermite (m + 1)).derivative = C (m + 1 : ℤ) * Polynomial.hermite m := by
  induction m with
  | zero => simp [Polynomial.hermite_one]
  | succ m ih =>
    rw [Polynomial.hermite_succ (m + 1), derivative_sub, derivative_mul,
      derivative_X, one_mul, ih, derivative_C_mul]
    calc
      _ = Polynomial.hermite (m + 1) +
          C (m + 1 : ℤ) * (X * Polynomial.hermite m - (Polynomial.hermite m).derivative) := by ring
      _ = _ := by
        rw [← Polynomial.hermite_succ]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
        ring

private theorem hermite_recurrence (k : ℕ) :
    Polynomial.hermite (k + 2) = X * Polynomial.hermite (k + 1) -
      C (k + 1 : ℤ) * Polynomial.hermite k := by
  rw [Polynomial.hermite_succ (k + 1), hermite_derivative]

private theorem hermite_no_common_root (m : ℕ) (z : ℂ) :
    ¬ (aeval z (Polynomial.hermite m) = 0 ∧ aeval z (Polynomial.hermite (m + 1)) = 0) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      intro ⟨hm, hp⟩
      have he := congrArg (aeval z) (hermite_recurrence m)
      simp only [map_sub, map_mul, aeval_X, aeval_C, hp, hm, mul_zero, zero_sub] at he
      have hc : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast (show (m + 1 : ℕ) ≠ 0 by omega)
      have hprev : aeval z (Polynomial.hermite m) = 0 := by
        apply (mul_eq_zero.mp (neg_eq_zero.mp he.symm)).resolve_left
        simpa only [map_add, map_one, map_natCast] using hc
      exact ih m (by omega) ⟨hprev, hm⟩

private theorem hermite_root_real_simple (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : aeval z (Polynomial.hermite m) = 0) :
    z.im = 0 ∧ aeval z (Polynomial.hermite m).derivative ≠ 0 := by
  have hreal := PositiveThreeTermRootReality.finite_positive_three_term_zero_has_real_parameter
    m z (fun k => (k : ℝ) + 1) (fun k => aeval z (Polynomial.hermite k))
    (fun k _ => by positivity) (by simp) (by simp [Polynomial.hermite_one])
    (fun k _ => by
      have h := congrArg (aeval z) (hermite_recurrence k)
      simpa using h) hz
  refine ⟨hreal, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rw [hermite_derivative, map_mul, aeval_C]
  apply mul_ne_zero
    (by simp only [map_add, map_one, map_natCast]; exact_mod_cast (show (k + 1 : ℕ) ≠ 0 by omega))
  intro hprev
  exact hermite_no_common_root k z ⟨hprev, hz⟩

private theorem simple_cofactor (P : ℂ[X]) (a : ℂ) (ha : P.eval a = 0)
    (hd : P.derivative.eval a ≠ 0) :
    ∃ Q : ℂ[X], P = (X - C a) * Q ∧ Q.eval a ≠ 0 := by
  let Q := P /ₘ (X - C a)
  have he : P = (X - C a) * Q := (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  refine ⟨Q, he, ?_⟩
  have hder : P.derivative.eval a = Q.eval a := by
    rw [he, derivative_mul]
    simp
  exact hder ▸ hd

private theorem coefficient_polynomial_norm_bound (a : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (hs : Summable (fun j => ‖a j‖ * R ^ j))
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(coefficientPolynomial a n).eval z‖ ≤ weightedNorm a 0 R := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hw (j : ℕ) : ‖(n.descFactorial j : ℂ) / (n : ℂ) ^ j‖ ≤ 1 := by
    simp only [norm_div, Complex.norm_natCast, norm_pow]
    apply (div_le_one (pow_pos (Nat.cast_pos.mpr (by omega : 0 < n)) j)).mpr
    exact_mod_cast Nat.descFactorial_le_pow n j
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖a j‖ * R ^ j := by
      simp only [coefficientPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul, norm_pow]
      calc
        _ ≤ 1 * ‖a j‖ * R ^ j :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hw j) (norm_nonneg _))
            (pow_le_pow_left₀ (norm_nonneg z) hz j) (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ ∑' j, ‖a j‖ * R ^ j :=
      hs.sum_le_tsum _ (fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg hR j))
    _ = _ := by simp [weightedNorm]

private theorem scaled_polynomial_size (F : ℂ → ℂ) (a : ℕ → ℂ)
    (t0 sigma : ℝ) (ht0 : 0 < t0) (v : ℕ)
    (ho : IsExactRealOrder F t0 v) (he : ScaledFunctionEstimate F a t0 sigma v)
    (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
      ∀ u : ℂ, ‖u‖ ≤ R →
        ‖(coefficientPolynomial a n).eval
          ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ)))‖ ≤ B / (Real.sqrt n) ^ v := by
  let q := max 2 R
  obtain ⟨C, hC, N, hN⟩ := he q (le_max_left _ _)
  obtain ⟨zmax, hzmax, hmax⟩ := (isCompact_closedBall (0 : ℂ) q).exists_isMaxOn
    ⟨0, mem_closedBall_self (by dsimp [q]; positivity)⟩
    (Polynomial.continuous_aeval (Polynomial.hermite v)).norm.continuousOn
  let A : ℂ := (t0 : ℂ) ^ v * iteratedDeriv v F t0 / (v.factorial : ℂ)
  have hA : A ≠ 0 := div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht0.ne')) ho.1)
    (by exact_mod_cast Nat.factorial_ne_zero v)
  let B := (‖aeval zmax (Polynomial.hermite v)‖ + C) * ‖A‖
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, N, ?_⟩
  intro n hn
  obtain ⟨hn1, herr⟩ := hN n hn
  have hs1 : 1 ≤ Real.sqrt n := by
    exact (Real.sqrt_one ▸ Real.sqrt_le_sqrt (by exact_mod_cast hn1))
  have hs : 0 < Real.sqrt n := lt_of_lt_of_le zero_lt_one hs1
  have hden : A / (Real.sqrt n : ℂ) ^ v ≠ 0 :=
    div_ne_zero hA (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs.ne'))
  refine ⟨hn1, ?_⟩
  intro u hu
  have huq : ‖u‖ ≤ q := hu.trans (le_max_right _ _)
  have hH : ‖aeval u (Polynomial.hermite v)‖ ≤ ‖aeval zmax (Polynomial.hermite v)‖ :=
    hmax (by simpa only [mem_closedBall_zero_iff] using huq)
  have hquot : ‖(coefficientPolynomial a n).eval
      ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ))) / (A / (Real.sqrt n : ℂ) ^ v)‖ ≤
      ‖aeval zmax (Polynomial.hermite v)‖ + C := by
    have hnorm := norm_le_norm_add_norm_sub
      (aeval u (Polynomial.hermite v))
      ((coefficientPolynomial a n).eval
        ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ))) / (A / (Real.sqrt n : ℂ) ^ v))
    have hCs : C / Real.sqrt n ≤ C := div_le_self hC.le hs1
    apply hnorm.trans (add_le_add hH ?_)
    simpa only [norm_sub_rev] using (herr u huq).trans hCs
  calc
    _ = ‖(coefficientPolynomial a n).eval
        ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ))) / (A / (Real.sqrt n : ℂ) ^ v)‖ *
        ‖A / (Real.sqrt n : ℂ) ^ v‖ := by rw [← norm_mul, div_mul_cancel₀ _ hden]
    _ ≤ (‖aeval zmax (Polynomial.hermite v)‖ + C) * ‖A / (Real.sqrt n : ℂ) ^ v‖ :=
      mul_le_mul_of_nonneg_right hquot (norm_nonneg _)
    _ = B / Real.sqrt n ^ v := by
      simp only [B, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      ring


private theorem account_root_occurrences (P : ℂ[X]) (c : ℂ) (delta : ℝ) (m : ℕ)
    (hP : P ≠ 0) (nodes : Fin m → ℝ) (hinj : Function.Injective nodes)
    (hroot : ∀ i, P.eval (nodes i : ℂ) = 0)
    (hinside : ∀ i, ‖(nodes i : ℂ) - c‖ < delta)
    (hcard : (P.roots.filter (fun z : ℂ => ‖z - (c : ℂ)‖ < delta)).card = m) :
    P.roots.filter (fun z : ℂ => ‖z - (c : ℂ)‖ < delta) =
      (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ)) := by
  classical
  let A := (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ))
  have hAi : Function.Injective (fun i => (nodes i : ℂ)) :=
    Complex.ofReal_injective.comp hinj
  have hAn : A.Nodup := Multiset.Nodup.map hAi Finset.univ.nodup
  have hle : A ≤ P.roots.filter (fun z : ℂ => ‖z - (c : ℂ)‖ < delta) := by
    apply (Multiset.le_iff_subset hAn).mpr
    intro z hz
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
    exact Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr (hroot i), hinside i⟩
  have hAc : A.card = m := by simp [A]
  exact (Multiset.eq_of_le_of_card_le hle (by rw [hcard, hAc])).symm


end D5.S3.Zeros.Jensen.JensenSimpleRealStability
