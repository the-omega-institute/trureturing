/- SOURCE-ONLY candidate for original #8330 section 10, uncompiled.
   Use with the three same-owner supplier candidates in this source bundle.
   The previous seven component proofs are unchanged. The complete explicit
   root adds the actual prefix witness, unit-interval range and independent
   universe competitor bounds. No theorem/kernel/publication claim is made. -/
import D5.S3.Observer.MetricGeometry.ContractingDigitMemory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped Topology ENNReal BigOperators
open D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
open D5.S3.Observer.MetricGeometry.ContractingDigitMemory
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

universe u

namespace ExactDigit10

-- 10.1: canonical actual real carrier and its total affine Bool action.
private theorem model_clause (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) :
    digitK lam = {x : ℝ | ∃ b : ℕ → Bool,
      (1 - lam) * (∑' j : ℕ, bitVal (b j) * lam ^ j) = x} ∧
    (∀ a : Bool, ∀ x : DigitState lam,
      (digitStep lam h0.le (by linarith) a x).val =
        (1 - lam) * bitVal a + lam * x.val) ∧
    (∀ a b, prepend a b 0 = a ∧ ∀ j, prepend a b (j + 1) = b j) := by
  exact ⟨rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, fun _ => rfl⟩⟩

-- 10.2: direct application, retaining ALL initial states, ALL finite words and
-- arbitrary real output constants through the actual HasFinitePredictor predicate.
private theorem window_least_clause (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
    (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2) :
    IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
      (fun x : DigitState lam => x.val) eps s} (2 ^ L) := by
  exact contracting_digit_memory_exact h0 hh L hL hlo hhi

-- Transient minimum on the actual predicate, also defined away from eps > 0
-- solely so its one-sided real limit is a function on all of R.
private def Nmin (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (eps : ℝ) : ℕ :=
  sInf {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
    (fun x : DigitState lam => x.val) eps s}

private lemma radius_window (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) :
    lam ^ L / 2 < (1 - lam) * lam ^ (L - 1) / 2 := by
  have hp : 0 < lam ^ (L - 1) := pow_pos h0 _
  have hpow : lam ^ L = lam ^ (L - 1) * lam := by
    rw [← pow_succ, Nat.sub_add_cancel hL]
  rw [hpow]
  nlinarith

private lemma feasible_mono {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) {eps delta : ℝ} (h : eps ≤ delta)
    {s : ℕ} (hs : HasFinitePredictor F o eps s) : HasFinitePredictor F o delta s := by
  rcases hs with ⟨S, finS, neS, hcard, e, G, readout, herr⟩
  exact ⟨S, finS, neS, hcard, e, G, readout, fun x w => (herr x w).trans h⟩

private lemma feasible_exists (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (eps : ℝ) (he : 0 < eps) :
    ∃ s : ℕ, HasFinitePredictor (digitStep lam h0.le (by linarith))
      (fun x : DigitState lam => x.val) eps s := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * eps by positivity)
    (show lam < 1 by linarith)
  let L := n + 1
  have hL : 1 ≤ L := by omega
  have hp : lam ^ L / 2 ≤ eps := by
    have hs : lam ^ (n + 1) ≤ lam ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg h0.le n) (by linarith)
    dsimp [L]
    linarith
  have hexact := contracting_digit_memory_exact h0 hh L hL le_rfl
    (radius_window lam h0 hh L hL)
  exact ⟨2 ^ L, feasible_mono _ _ hp hexact.1⟩

private lemma Nmin_least (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (eps : ℝ) (he : 0 < eps) :
    IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
      (fun x : DigitState lam => x.val) eps s} (Nmin lam h0 hh eps) := by
  exact isLeast_csInf (feasible_exists lam h0 hh eps he)

private lemma Nmin_pos (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (eps : ℝ) (he : 0 < eps) : 0 < Nmin lam h0 hh eps := by
  obtain ⟨S, finS, neS, hcard, e, G, readout, herr⟩ := (Nmin_least lam h0 hh eps he).1
  letI := finS
  letI := neS
  exact lt_of_lt_of_le Fintype.card_pos hcard

private lemma Nmin_antitone (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    {eps delta : ℝ} (he : 0 < eps) (hd : 0 < delta) (hed : eps ≤ delta) :
    Nmin lam h0 hh delta ≤ Nmin lam h0 hh eps := by
  exact (Nmin_least lam h0 hh delta hd).2
    (feasible_mono _ _ hed (Nmin_least lam h0 hh eps he).1)

private lemma Nmin_exact (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) {eps : ℝ} (hlo : lam ^ L / 2 ≤ eps)
    (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2) :
    Nmin lam h0 hh eps = 2 ^ L := by
  have he : 0 < eps := lt_of_lt_of_le (by positivity) hlo
  exact (Nmin_least lam h0 hh eps he).unique
    (contracting_digit_memory_exact h0 hh L hL hlo hhi)

private lemma Nmin_radius (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) : Nmin lam h0 hh (lam ^ L / 2) = 2 ^ L := by
  exact Nmin_exact lam h0 hh L hL le_rfl (radius_window lam h0 hh L hL)

-- Every positive real error has a positive attained LEAST budget; a witness
-- has exactly that many states, with the original uniform autonomous guarantee.
private theorem positive_minimum_clause (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (eps : ℝ) (he : 0 < eps) :
    0 < Nmin lam h0 hh eps ∧
    IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
      (fun x : DigitState lam => x.val) eps s} (Nmin lam h0 hh eps) ∧
    ∃ (S : Type) (finS : Fintype S), Nonempty S ∧
      @Fintype.card S finS = Nmin lam h0 hh eps ∧
      ∃ (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ),
        ∀ x w, dist (readout (runWord G w (e x)))
          ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps := by
  have hleast := Nmin_least lam h0 hh eps he
  refine ⟨Nmin_pos lam h0 hh eps he, hleast, ?_⟩
  rcases hleast.1 with ⟨S, finS, neS, hcard, e, G, readout, herr⟩
  have hreverse : Nmin lam h0 hh eps ≤ @Fintype.card S finS :=
    hleast.2 ⟨S, finS, neS, le_rfl, e, G, readout, herr⟩
  exact ⟨S, finS, neS, le_antisymm hcard hreverse, e, G, readout, herr⟩

-- The minimum definition is identified with the same exact IsLeast for every
-- error in the full half-open window, including equality at its lower endpoint.
private theorem window_value_clause (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
    (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2) :
    Nmin lam h0 hh eps = 2 ^ L := by
  exact Nmin_exact lam h0 hh L hL hlo hhi

-- Current-label bits only. The predicate has no supplied time argument.
private theorem radius_bits_clause (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (L : ℕ) (hL : 1 ≤ L) :
    Nmin lam h0 hh (lam ^ L / 2) = 2 ^ L ∧
    Nat.clog 2 (Nmin lam h0 hh (lam ^ L / 2)) = L := by
  refine ⟨Nmin_radius lam h0 hh L hL, ?_⟩
  rw [Nmin_radius lam h0 hh L hL, Nat.clog_pow 2 L (by norm_num)]
-- 10.3: the genuinely MINIMAL first crossing, valid for arbitrary real eps.
private lemma first_crossing (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (eps : ℝ) (he : 0 < eps) (hesmall : eps < lam / 2) :
    ∃ m : ℕ, 2 ≤ m ∧ lam ^ m / 2 ≤ eps ∧
      (∀ j : ℕ, j < m → eps < lam ^ j / 2) ∧
      eps < lam ^ (m - 1) / 2 ∧
      2 ^ (m - 1) ≤ Nmin lam h0 hh eps ∧ Nmin lam h0 hh eps ≤ 2 ^ m := by
  have hex : ∃ n : ℕ, lam ^ n / 2 ≤ eps := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * eps by positivity)
      (show lam < 1 by linarith)
    exact ⟨n, by linarith⟩
  let m := Nat.find hex
  have hm : lam ^ m / 2 ≤ eps := Nat.find_spec hex
  have hminimal (j : ℕ) (hj : j < m) : eps < lam ^ j / 2 :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hm0 : m ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hm
    linarith
  have hm1 : m ≠ 1 := by
    intro ho
    rw [ho] at hm
    have hm' : lam / 2 ≤ eps := by simpa only [pow_one] using hm
    exact (not_le.mpr hesmall) hm'
  have hm2 : 2 ≤ m := by omega
  have hprev : eps < lam ^ (m - 1) / 2 := hminimal (m - 1) (by omega)
  have hupper : Nmin lam h0 hh eps ≤ 2 ^ m := by
    rw [← Nmin_radius lam h0 hh m (by omega)]
    exact Nmin_antitone lam h0 hh (by positivity) he hm
  have hlower : 2 ^ (m - 1) ≤ Nmin lam h0 hh eps := by
    rw [← Nmin_radius lam h0 hh (m - 1) (by omega)]
    exact Nmin_antitone lam h0 hh he (by positivity) hprev.le
  exact ⟨m, hm2, hm, hminimal, hprev, hlower, hupper⟩

-- The normalization is proved with positive a=log(1/lam) and T=log(1/eps).
-- The error bound is O(1/T), with constants independent of the real eps.
private lemma normalized_error (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (eps : ℝ) (he : 0 < eps) (hesmall : eps < lam / 2) :
    |Real.log (Nmin lam h0 hh eps : ℝ) / Real.log (1 / eps) -
      Real.log 2 / Real.log (1 / lam)| ≤
      (Real.log 2 * (Real.log (1 / lam) + Real.log 2) / Real.log (1 / lam)) /
        Real.log (1 / eps) := by
  let a : ℝ := Real.log (1 / lam)
  let c : ℝ := Real.log 2
  let T : ℝ := Real.log (1 / eps)
  let R : ℝ := Real.log (Nmin lam h0 hh eps : ℝ)
  have hlam1 : lam < 1 := by linarith
  have he1 : eps < 1 := by linarith
  have ha : 0 < a := Real.log_pos ((one_lt_div h0).2 hlam1)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hT : 0 < T := Real.log_pos ((one_lt_div he).2 he1)
  have hla : Real.log lam = -a := by simp [a, Real.log_div, h0.ne']
  have hle : Real.log eps = -T := by simp [T, Real.log_div, he.ne']
  obtain ⟨m, hm2, hrad, hminimal, hprev, hNlo, hNhi⟩ :=
    first_crossing lam h0 hh eps he hesmall
  have hm1 : 1 ≤ m := by omega
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hNpos : (0 : ℝ) < Nmin lam h0 hh eps := by
    exact_mod_cast Nmin_pos lam h0 hh eps he
  have hNloR : ((2 ^ (m - 1) : ℕ) : ℝ) ≤ Nmin lam h0 hh eps := by exact_mod_cast hNlo
  have hNhiR : (Nmin lam h0 hh eps : ℝ) ≤ (2 ^ m : ℕ) := by exact_mod_cast hNhi
  have hloglo : ((m : ℝ) - 1) * c ≤ R := by
    have h := Real.log_le_log (show (0 : ℝ) < ((2 ^ (m - 1) : ℕ) : ℝ) by positivity) hNloR
    simpa [R, c, Nat.cast_pow, Real.log_pow, hmcast] using h
  have hloghi : R ≤ (m : ℝ) * c := by
    have h := Real.log_le_log hNpos hNhiR
    simpa [R, c, Nat.cast_pow, Real.log_pow] using h
  have hTupper : T ≤ (m : ℝ) * a + c := by
    have h := Real.log_le_log (show 0 < lam ^ m / 2 by positivity) hrad
    rw [Real.log_div (pow_ne_zero _ h0.ne') (by norm_num), Real.log_pow, hla, hle] at h
    dsimp [c] at *
    nlinarith
  have hTlower : ((m : ℝ) - 1) * a + c < T := by
    have h := Real.log_lt_log he hprev
    rw [Real.log_div (pow_ne_zero _ h0.ne') (by norm_num), Real.log_pow,
      hla, hle, hmcast] at h
    dsimp [c] at *
    nlinarith
  have hproduct : |a * R - c * T| ≤ c * (a + c) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hloglo ha.le,
        mul_le_mul_of_nonneg_left hTupper hc.le]
    · nlinarith [mul_le_mul_of_nonneg_left hloghi ha.le,
        mul_le_mul_of_nonneg_left hTlower.le hc.le]
  have hnormal : R / T - c / a = (a * R - c * T) / (a * T) := by
    field_simp [ha.ne', hT.ne']
    <;> ring
  change |R / T - c / a| ≤ (c * (a + c) / a) / T
  rw [hnormal, abs_div, abs_of_pos (mul_pos ha hT)]
  calc
    |a * R - c * T| / (a * T) ≤ (c * (a + c)) / (a * T) :=
      div_le_div_of_nonneg_right hproduct (mul_pos ha hT).le
    _ = (c * (a + c) / a) / T := by rw [div_div]

-- Full epsilon-down-to-zero limit, with eps ranging over ALL positive reals.
private lemma full_limit (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) :
    Tendsto (fun eps : ℝ => Real.log (Nmin lam h0 hh eps : ℝ) / Real.log (1 / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / Real.log (1 / lam))) := by
  have hTtop : Tendsto (fun eps : ℝ => Real.log (1 / eps)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hbound := hTtop.const_div_atTop
    (Real.log 2 * (Real.log (1 / lam) + Real.log 2) / Real.log (1 / lam))
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (g := fun eps : ℝ =>
      (Real.log 2 * (Real.log (1 / lam) + Real.log 2) / Real.log (1 / lam)) /
        Real.log (1 / eps))
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < lam / 2 by positivity)] with eps he
    simpa only [Real.dist_eq] using normalized_error lam h0 hh eps he.1 he.2
  · exact hbound

private theorem asymptotics_clause (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) :
    (∀ eps : ℝ, 0 < eps →
      IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
        (fun x : DigitState lam => x.val) eps s} (Nmin lam h0 hh eps)) ∧
    (∀ eps : ℝ, 0 < eps → 0 < Nmin lam h0 hh eps) ∧
    AntitoneOn (Nmin lam h0 hh) (Ioi 0) ∧
    (∀ eps : ℝ, 0 < eps → eps < lam / 2 →
      ∃ m : ℕ, 2 ≤ m ∧ lam ^ m / 2 ≤ eps ∧
        (∀ j : ℕ, j < m → eps < lam ^ j / 2) ∧ eps < lam ^ (m - 1) / 2 ∧
        2 ^ (m - 1) ≤ Nmin lam h0 hh eps ∧ Nmin lam h0 hh eps ≤ 2 ^ m) ∧
    Tendsto (fun eps : ℝ => Real.log (Nmin lam h0 hh eps : ℝ) / Real.log (1 / eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / Real.log (1 / lam))) := by
  refine ⟨Nmin_least lam h0 hh, Nmin_pos lam h0 hh, ?_, first_crossing lam h0 hh,
    full_limit lam h0 hh⟩
  intro eps he delta hd hed
  exact Nmin_antitone lam h0 hh he hd hed

-- Golden specialization: phi is the literal (1+sqrt 5)/2, lambda = phi^-2.
private def phi : ℝ := (1 + Real.sqrt 5) / 2
private def goldenLambda : ℝ := (phi ^ 2)⁻¹

private lemma phi_pos : 0 < phi := Real.goldenRatio_pos
private lemma phi_gt_one : 1 < phi := Real.one_lt_goldenRatio
private lemma phi_square : phi ^ 2 = phi + 1 := Real.goldenRatio_sq
private lemma goldenLambda_pos : 0 < goldenLambda :=
  inv_pos.mpr (pow_pos phi_pos 2)
private lemma goldenLambda_half : goldenLambda < 1 / 2 := by
  have hp : 0 < phi ^ 2 := pow_pos phi_pos _
  have htwo : (2 : ℝ) < phi ^ 2 := by rw [phi_square]; linarith [phi_gt_one]
  exact (inv_lt_iff_one_lt_mul₀ hp).2 (by linarith)

private lemma golden_radius (L : ℕ) : goldenLambda ^ L / 2 = 1 / (2 * phi ^ (2 * L)) := by
  unfold goldenLambda
  rw [inv_pow, ← pow_mul]
  simp only [one_div, div_eq_mul_inv, mul_inv_rev] <;> ring

private lemma golden_log : Real.log (1 / goldenLambda) = 2 * Real.log phi := by
  simp [goldenLambda, one_div, Real.log_pow]

private theorem golden_clause :
    phi = (1 + Real.sqrt 5) / 2 ∧ goldenLambda = (phi ^ 2)⁻¹ ∧
    0 < goldenLambda ∧ goldenLambda < 1 / 2 ∧
    (∀ L : ℕ, 1 ≤ L →
      Nmin goldenLambda goldenLambda_pos goldenLambda_half
        (1 / (2 * phi ^ (2 * L))) = 2 ^ L ∧
      Nat.clog 2 (Nmin goldenLambda goldenLambda_pos goldenLambda_half
        (1 / (2 * phi ^ (2 * L)))) = L) ∧
    Tendsto (fun eps : ℝ =>
      Real.log (Nmin goldenLambda goldenLambda_pos goldenLambda_half eps : ℝ) /
        Real.log (1 / eps)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (2 * Real.log phi))) := by
  refine ⟨rfl, rfl, goldenLambda_pos, goldenLambda_half, ?_, ?_⟩
  · intro L hL
    have heq := Nmin_radius goldenLambda goldenLambda_pos goldenLambda_half L hL
    rw [golden_radius] at heq
    exact ⟨heq, by rw [heq, Nat.clog_pow 2 L (by norm_num)]⟩
  · simpa only [golden_log] using full_limit goldenLambda goldenLambda_pos goldenLambda_half


-- Transient finite-carrier transport. The encoder, update, readout, every word
-- and the same epsilon are transported; the existing word lemma owns induction.
private lemma competitor_budget {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (eps : ℝ)
    (S : Type u) [Fintype S] [Nonempty S]
    (e : X → S) (G : A → S → S) (readout : S → Y)
    (herr : ∀ x w, dist (readout (runWord G w (e x))) (o (runWord F w x)) ≤ eps) :
    HasFinitePredictor F o eps (Fintype.card S) := by
  classical
  let q : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let e' : X → Fin (Fintype.card S) := fun x => q (e x)
  let G' : A → Fin (Fintype.card S) → Fin (Fintype.card S) :=
    fun a s => q (G a (q.symm s))
  let readout' : Fin (Fintype.card S) → Y := fun s => readout (q.symm s)
  have hcomm (a : A) : q ∘ G a = G' a ∘ q := by
    funext s
    simp only [Function.comp_apply, G', Equiv.symm_apply_apply]
  have hword (w : List A) (s : S) :
      q (runWord G w s) = runWord G' w (q s) :=
    D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.run_word_intertwines
      G G' q hcomm w s
  letI : Nonempty (Fin (Fintype.card S)) := ⟨q (Classical.choice inferInstance)⟩
  refine ⟨Fin (Fintype.card S), inferInstance, inferInstance, by simp,
    e', G', readout', ?_⟩
  intro x w
  change dist (readout (q.symm (runWord G' w (q (e x))))) (o (runWord F w x)) ≤ eps
  rw [← hword w (e x), q.symm_apply_apply]
  exact herr x w

private theorem competitor_window_clause
    (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
    (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2)
    (S : Type u) [Fintype S] [Nonempty S]
    (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ)
    (herr : ∀ (x : DigitState lam) (w : List Bool),
      dist (readout (runWord G w (e x)))
        ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps) :
    2 ^ L ≤ Fintype.card S := by
  exact (contracting_digit_memory_exact h0 hh L hL hlo hhi).2
    (competitor_budget _ _ eps S e G readout herr)

private theorem competitor_minimum_clause
    (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (eps : ℝ) (he : 0 < eps)
    (S : Type u) [Fintype S] [Nonempty S]
    (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ)
    (herr : ∀ (x : DigitState lam) (w : List Bool),
      dist (readout (runWord G w (e x)))
        ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps) :
    Nmin lam h0 hh eps ≤ Fintype.card S := by
  exact (Nmin_least lam h0 hh eps he).2
    (competitor_budget _ _ eps S e G readout herr)

-- One explicit root: all original model/window/minimum/limit/golden clauses,
-- with the source-owned prefix machine and unrestricted finite competitors.
theorem section10Root :
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2),
        digitK lam ⊆ Icc 0 1) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (L : ℕ) (hL : 1 ≤ L),
        Fintype.card (Fin L → Bool) = 2 ^ L ∧
        ∃ e : DigitState lam → (Fin L → Bool),
          (∀ x, x ∈ prefixClass lam L (e x)) ∧
          ∀ (x : DigitState lam) (w : List Bool),
            dist ((fun u : Fin L → Bool => prefixPoint lam L u + lam ^ L / 2)
              (runWord (fun (a : Bool) (u : Fin L → Bool) (i : Fin L) =>
                if i.val = 0 then a else u ⟨i.val - 1, by omega⟩) w (e x)))
              ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ lam ^ L / 2) ∧
    (∀ (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
        (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
        (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2)
        (S : Type u) [Fintype S] [Nonempty S]
        (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ),
        (∀ (x : DigitState lam) (w : List Bool),
          dist (readout (runWord G w (e x)))
            ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps) →
        2 ^ L ≤ Fintype.card S) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (eps : ℝ) (he : 0 < eps)
        (S : Type u) [Fintype S] [Nonempty S]
        (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ),
        (∀ (x : DigitState lam) (w : List Bool),
          dist (readout (runWord G w (e x)))
            ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps) →
        Nmin lam h0 hh eps ≤ Fintype.card S) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2),
        digitK lam = {x : ℝ | ∃ b : ℕ → Bool,
          (1 - lam) * (∑' j : ℕ, bitVal (b j) * lam ^ j) = x} ∧
        (∀ a : Bool, ∀ x : DigitState lam,
          (digitStep lam h0.le (by linarith) a x).val =
            (1 - lam) * bitVal a + lam * x.val) ∧
        (∀ a b, prepend a b 0 = a ∧ ∀ j, prepend a b (j + 1) = b j)) ∧
    (∀ (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
        (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
        (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2),
        IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
          (fun x : DigitState lam => x.val) eps s} (2 ^ L)) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (eps : ℝ) (he : 0 < eps),
        0 < Nmin lam h0 hh eps ∧
        IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
          (fun x : DigitState lam => x.val) eps s} (Nmin lam h0 hh eps) ∧
        ∃ (S : Type) (finS : Fintype S), Nonempty S ∧
          @Fintype.card S finS = Nmin lam h0 hh eps ∧
          ∃ (e : DigitState lam → S) (G : Bool → S → S) (readout : S → ℝ),
            ∀ x w, dist (readout (runWord G w (e x)))
              ((runWord (digitStep lam h0.le (by linarith)) w x).val) ≤ eps) ∧
    (∀ (lam eps : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2)
        (L : ℕ) (hL : 1 ≤ L) (hlo : lam ^ L / 2 ≤ eps)
        (hhi : eps < (1 - lam) * lam ^ (L - 1) / 2),
        Nmin lam h0 hh eps = 2 ^ L) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2) (L : ℕ) (hL : 1 ≤ L),
        Nmin lam h0 hh (lam ^ L / 2) = 2 ^ L ∧
        Nat.clog 2 (Nmin lam h0 hh (lam ^ L / 2)) = L) ∧
    (∀ (lam : ℝ) (h0 : 0 < lam) (hh : lam < 1 / 2),
        (∀ eps : ℝ, 0 < eps →
          IsLeast {s : ℕ | HasFinitePredictor (digitStep lam h0.le (by linarith))
            (fun x : DigitState lam => x.val) eps s} (Nmin lam h0 hh eps)) ∧
        (∀ eps : ℝ, 0 < eps → 0 < Nmin lam h0 hh eps) ∧
        AntitoneOn (Nmin lam h0 hh) (Ioi 0) ∧
        (∀ eps : ℝ, 0 < eps → eps < lam / 2 →
          ∃ m : ℕ, 2 ≤ m ∧ lam ^ m / 2 ≤ eps ∧
            (∀ j : ℕ, j < m → eps < lam ^ j / 2) ∧ eps < lam ^ (m - 1) / 2 ∧
            2 ^ (m - 1) ≤ Nmin lam h0 hh eps ∧ Nmin lam h0 hh eps ≤ 2 ^ m) ∧
        Tendsto (fun eps : ℝ => Real.log (Nmin lam h0 hh eps : ℝ) / Real.log (1 / eps))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / Real.log (1 / lam)))) ∧
    (    phi = (1 + Real.sqrt 5) / 2 ∧ goldenLambda = (phi ^ 2)⁻¹ ∧
        0 < goldenLambda ∧ goldenLambda < 1 / 2 ∧
        (∀ L : ℕ, 1 ≤ L →
          Nmin goldenLambda goldenLambda_pos goldenLambda_half
            (1 / (2 * phi ^ (2 * L))) = 2 ^ L ∧
          Nat.clog 2 (Nmin goldenLambda goldenLambda_pos goldenLambda_half
            (1 / (2 * phi ^ (2 * L)))) = L) ∧
        Tendsto (fun eps : ℝ =>
          Real.log (Nmin goldenLambda goldenLambda_pos goldenLambda_half eps : ℝ) /
            Real.log (1 / eps)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (2 * Real.log phi)))) := by
  refine ⟨?_, ?_, competitor_window_clause, competitor_minimum_clause,
    model_clause, window_least_clause, positive_minimum_clause,
    window_value_clause, radius_bits_clause, asymptotics_clause, golden_clause⟩
  · intro lam h0 hh
    exact digitK_subset_Icc h0.le (by linarith)
  · intro lam h0 hh L _hL
    exact contracting_digit_prefix_machine h0 hh L

end ExactDigit10
