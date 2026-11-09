/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BV weighted arithmetic moments transfer to their quadratic formal values. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CentredCorrelationSummation
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionErrorBounds
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform arithmetic transfer for weighted cubic and fourth interval moments. -/

open scoped BigOperators Topology Pointwise
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private def redA (r : ℕ) : Polynomial ℝ := (reduction_polynomial r).choose
private def redB (r : ℕ) : Polynomial ℝ := (reduction_polynomial r).choose_spec.choose

private lemma red_eval (r : ℕ) (s : ℝ) :
    (red r s).1 = (redA r).eval s ∧ (red r s).2 = (redB r).eval s :=
  (reduction_polynomial r).choose_spec.choose_spec.2.2 s

private def coefficientPool : Finset (Polynomial ℝ) :=
  insert 1 (((Finset.range 5).image redA) ∪ ((Finset.range 5).image redB))

private def coefficientFamily : Finset (Polynomial ℝ) := coefficientPool ^ 4

private def tuplePolynomial {k : ℕ} (d : Fin k → ℕ) (J : Finset ℕ) : Polynomial ℝ :=
  ∏ e ∈ Finset.univ.image d, if e ∈ J then redA (mult d e) else redB (mult d e)

private lemma tuplePolynomial_eval {k : ℕ} (d : Fin k → ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.univ.image d) (s : ℝ) :
    (tuplePolynomial d J).eval s =
      (∏ e ∈ J, (red (mult d e) s).1) *
        ∏ e ∈ Finset.univ.image d \ J, (red (mult d e) s).2 := by
  simp only [tuplePolynomial, Polynomial.eval_prod]
  simp_rw [apply_ite (fun p : Polynomial ℝ => p.eval s), ← (red_eval _ s).1,
    ← (red_eval _ s).2]
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext e; simp only [Finset.mem_filter]; exact ⟨And.right, fun he => ⟨hJ he, he⟩⟩
  · congr 1; ext e; simp

private lemma tuplePolynomial_mem {k : ℕ} (hk : k ≤ 4) (d : Fin k → ℕ)
    (J : Finset ℕ) : tuplePolynomial d J ∈ coefficientFamily := by
  classical
  let D := Finset.univ.image d
  have hm (e : ℕ) : mult d e < 5 := by
    have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin k))) (fun i => d i = e)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    dsimp [mult]; omega
  have hf (e : ℕ) (_he : e ∈ D) :
      (if e ∈ J then redA (mult d e) else redB (mult d e)) ∈ coefficientPool := by
    split_ifs <;> simp only [coefficientPool, Finset.mem_insert, Finset.mem_union]
    · exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (hm e), rfl⟩))
    · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (hm e), rfl⟩))
  have hp : tuplePolynomial d J ∈ coefficientPool ^ D.card := by
    have hh := Set.finsetProd_mem_finsetProd D
      (fun _ => (coefficientPool : Set (Polynomial ℝ)))
      (fun e => if e ∈ J then redA (mult d e) else redB (mult d e)) hf
    simpa only [Finset.prod_const, ← Finset.coe_pow, Finset.mem_coe, tuplePolynomial, D] using hh
  exact Finset.pow_subset_pow_right (by simp [coefficientPool])
    ((Finset.card_image_le).trans (by simpa using hk)) hp

private lemma finite_polynomial_correlation (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hHL : HL4 SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε)
    (P : Finset (Polynomial ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ p ∈ P, ∀ D : Finset ℕ, D.card ≤ 4 →
        (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ M * N ^ β) →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              w ((n : ℝ) / N) * p.eval (Real.log n) *
                ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) -
            center SS D * (∫ x in N..2 * N, w (x / N) * p.eval (Real.log x))| ≤
              C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m := by
  choose C hC hbound using centred_polynomial_log_correlation SS β hSS hHL M ε hM hε
  refine ⟨∑ p ∈ P, C p, Finset.sum_nonneg (fun p _ => hC p),
    P.sup Polynomial.natDegree, ?_⟩
  filter_upwards [(Filter.eventually_all_finset P).mpr (fun p _ => hbound p),
    eventually_ge_atTop (2 : ℝ)] with N hN hN2
  refine ⟨hN2, ?_⟩
  intro p hp D hD hd B w hw
  have hB : 0 ≤ B := hw.2.2.1
  have hN0 : 0 ≤ N := by linarith
  have hCs : 0 ≤ ∑ p ∈ P, C p := Finset.sum_nonneg (fun p _ => hC p)
  have hlog : 1 ≤ 1 + Real.log N := by
    linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
  exact ((hN p hp).2 D hD hd B w hw).trans (by
    gcongr
    · exact Finset.single_le_sum (fun q _ => hC q) hp
    · exact Finset.le_sup hp)

lemma polynomial_weight_integrable (N : ℝ) (hN : 2 ≤ N)
    (B : ℝ) (w : ℝ → ℝ) (hw : BVBound w B) (p : Polynomial ℝ) :
    IntervalIntegrable (fun x => w (x / N) * p.eval (Real.log x)) volume N (2 * N) := by
  obtain ⟨C, _, hp⟩ := polynomial_log_bv_bound p
  obtain ⟨U, hU, hu, _⟩ := hw.2.2.2
  have h := (hp N U (eVariationOn w univ).toReal w hN hU ENNReal.toReal_nonneg
    hw.1 hu (by rw [ENNReal.ofReal_toReal hw.1])).1
  exact h.intervalIntegrable (by rw [uIcc_of_le (by linarith : N ≤ 2 * N)])

theorem formal_weight_integrable (SS : Finset ℕ → ℝ) (N H B : ℝ)
    (w : ℝ → ℝ) (k : ℕ) (a b : Fin k → ℝ) (hN : 2 ≤ N) (hw : BVBound w B) :
    IntervalIntegrable (fun x => w (x / N) * Phi SS H (Real.log x) a b)
      volume N (2 * N) := by
  classical
  have hphi (x : ℝ) : w (x / N) * Phi SS H (Real.log x) a b =
      ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
        ∑ J ∈ (Finset.univ.image d).powerset,
          center SS J * (w (x / N) * (tuplePolynomial d J).eval (Real.log x)) := by
    simp only [Phi, reducedTuple, reducedFinite, center, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro J hJ
    rw [tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
    ring
  simp_rw [hphi]
  simpa only [Finset.sum_fn] using
    (IntervalIntegrable.sum (Fintype.piFinset (fun i => points H (a i) (b i))) (fun d _ =>
    IntervalIntegrable.sum (Finset.univ.image d).powerset (fun J _ =>
      (polynomial_weight_integrable N hN B w hw (tuplePolynomial d J)).const_mul
        (center SS J))))

private lemma reduced_correlation_transfer (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hHL : HL4 SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
        ∀ k : ℕ, k ≤ 4 → ∀ a b : Fin k → ℝ, admissible M a b →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
              ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
                reducedAt (Real.log n) n d) -
            (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
              C * B * N ^ (1 / 2 + ε) * H ^ k * (1 + Real.log N) ^ m := by
  classical
  obtain ⟨C, hC, m, hbound⟩ :=
    finite_polynomial_correlation SS β hSS hHL M ε hM hε coefficientFamily
  refine ⟨16 * C * M ^ 4, by positivity, m, ?_⟩
  filter_upwards [hbound] with N hN
  have hN0 : 0 ≤ N := by linarith [hN.1]
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN.1])
  refine ⟨hN.1, ?_⟩
  intro H hH hHN B w hw k hk a b hab
  have hB : 0 ≤ B := hw.2.2.1
  let T := Fintype.piFinset (fun i => points H (a i) (b i))
  let v := fun (d : Fin k → ℕ) (J : Finset ℕ) (x : ℝ) =>
    w (x / N) * (tuplePolynomial d J).eval (Real.log x)
  let F := fun (d : Fin k → ℕ) (J : Finset ℕ) =>
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, v d J n *
      ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1)) -
    center SS J * (∫ x in N..2 * N, v d J x)
  have hshift (d : Fin k → ℕ) (hd : d ∈ T) :
      ∀ e ∈ Finset.univ.image d, 1 ≤ e ∧ (e : ℝ) ≤ M * N ^ β := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    have hdi := Fintype.mem_piFinset.mp hd i
    have hp := Finset.mem_Ioc.mp hdi
    have hhi : (d i : ℝ) ≤ b i * H :=
      (Nat.le_floor_iff (by nlinarith [(hab i).1, (hab i).2.1])).mp hp.2
    exact ⟨by omega, hhi.trans ((mul_le_mul_of_nonneg_right (hab i).2.2 (by linarith)).trans
      (mul_le_mul_of_nonneg_left hHN (by linarith)))⟩
  have hJbound (d : Fin k → ℕ) (hd : d ∈ T) (J : Finset ℕ)
      (hJ : J ∈ (Finset.univ.image d).powerset) :
      |F d J| ≤ C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m := by
    exact hN.2 _ (tuplePolynomial_mem hk d J) J
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ)).trans
        ((Finset.card_image_le).trans (by simpa using hk)))
      (fun e he => hshift d hd e (Finset.mem_powerset.mp hJ he)) B w hw
  have htuple (d : Fin k → ℕ) (hd : d ∈ T) :
      |∑ J ∈ (Finset.univ.image d).powerset, F d J| ≤
        16 * (C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _J ∈ (Finset.univ.image d).powerset,
          C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m :=
        Finset.sum_le_sum (fun J hJ => hJbound d hd J hJ)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
          Nat.cast_pow, Nat.cast_ofNat]
        have hc : (Finset.univ.image d).card ≤ 4 :=
          (Finset.card_image_le).trans (by simpa using hk)
        have hp : (2 : ℝ) ^ (Finset.univ.image d).card ≤ 16 :=
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc).trans_eq (by norm_num)
        exact mul_le_mul_of_nonneg_right hp (by positivity)
  have heq : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
        ∑ d ∈ T, reducedAt (Real.log n) n d) -
      (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b) =
        ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset, F d J := by
    have hred (d : Fin k → ℕ) (s : ℝ) (n : ℕ) :
        w ((n : ℝ) / N) * reducedAt s n d =
          ∑ J ∈ (Finset.univ.image d).powerset,
            (w ((n : ℝ) / N) * (tuplePolynomial d J).eval s) *
              ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1) := by
      simp only [reducedAt, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
      ring
    have hphi (x : ℝ) : w (x / N) * Phi SS H (Real.log x) a b =
        ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset, center SS J * v d J x := by
      simp only [Phi, reducedTuple, reducedFinite, center, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro J hJ
      dsimp [v]
      rw [tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
      ring
    simp_rw [Finset.mul_sum, hred, hphi]
    rw [Finset.sum_comm]
    have hi (d : Fin k → ℕ) :
        IntervalIntegrable (fun x => ∑ J ∈ (Finset.univ.image d).powerset,
          center SS J * v d J x) volume N (2 * N) := by
      simpa only [Finset.sum_fn, v] using
        (IntervalIntegrable.sum (Finset.univ.image d).powerset
          (fun J _ => (polynomial_weight_integrable N hN.1 B w hw
            (tuplePolynomial d J)).const_mul (center SS J)))
    rw [intervalIntegral.integral_finsetSum
      (s := T) (f := fun d x => ∑ J ∈ (Finset.univ.image d).powerset, center SS J * v d J x)
      (fun d _ => hi d),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [intervalIntegral.integral_finsetSum
      (f := fun J x => center SS J * v d J x) (fun J _ =>
      (polynomial_weight_integrable N hN.1 B w hw (tuplePolynomial d J)).const_mul (center SS J)),
      Finset.sum_comm, ← Finset.sum_sub_distrib]
    simp only [F, v, intervalIntegral.integral_const_mul]
  rw [heq]
  have hcount : (T.card : ℝ) ≤ M ^ 4 * H ^ k := by
    have hsub : T ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Ioc 0 ⌊M * H⌋₊) := by
      intro d hd
      apply Fintype.mem_piFinset.mpr
      intro i
      have hh := Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hd i)
      exact Finset.mem_Ioc.mpr ⟨by omega,
        hh.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_right (hab i).2.2 (by linarith)))⟩
    calc
      _ ≤ ((Fintype.piFinset (fun _ : Fin k => Finset.Ioc 0 ⌊M * H⌋₊)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (⌊M * H⌋₊ : ℝ) ^ k := by simp [Fintype.card_piFinset]
      _ ≤ (M * H) ^ k := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
      _ ≤ _ := by rw [mul_pow]; gcongr
  calc
    _ ≤ ∑ _d ∈ T, 16 * (C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum htuple)
    _ = (T.card : ℝ) * (16 * (C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M ^ 4 * H ^ k) * (16 * (C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ m)) := by
      gcongr
    _ = _ := by ring

private lemma reduced_transfer_power_error (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hHL : HL4 SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
        ∀ k : ℕ, k ≤ 4 → ∀ a b : Fin k → ℝ, admissible M a b →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
              ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
                reducedAt (Real.log n) n d) -
            (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
              C * B * N ^ (1 / 2 + ε) * H ^ k := by
  obtain ⟨C, hC, m, hbound⟩ :=
    reduced_correlation_transfer SS β hSS hHL M (ε / 2) hM (by linarith)
  have hlog := (isLittleO_log_rpow_rpow_atTop (m : ℝ)
    (show 0 < ε / 2 by linarith)).bound (by norm_num : (0 : ℝ) < 1)
  refine ⟨C * 2 ^ m, by positivity, ?_⟩
  filter_upwards [hbound, hlog, Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hN hlog hL
  have hN0 : 0 < N := by linarith [hN.1]
  have hp : (Real.log N) ^ m ≤ N ^ (ε / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul, Real.rpow_natCast,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) m)] using hlog
  have hweight : (1 + Real.log N) ^ m ≤ 2 ^ m * N ^ (ε / 2) := by
    calc
      _ ≤ (2 * Real.log N) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ m * (Real.log N) ^ m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  refine ⟨hN.1, ?_⟩
  intro H hH hHN B w hw k hk a b hab
  have hB : 0 ≤ B := hw.2.2.1
  calc
    _ ≤ C * B * N ^ (1 / 2 + ε / 2) * H ^ k * (1 + Real.log N) ^ m :=
      hN.2 H hH hHN B w hw k hk a b hab
    _ ≤ C * B * N ^ (1 / 2 + ε / 2) * H ^ k * (2 ^ m * N ^ (ε / 2)) := by
      gcongr
    _ = _ := by
      calc
        _ = C * 2 ^ m * B *
            (N ^ (1 / 2 + ε / 2) * N ^ (ε / 2)) * H ^ k := by ring
        _ = _ := by
          rw [← Real.rpow_add hN0,
            show (1 / 2 + ε / 2) + ε / 2 = (1 / 2 + ε : ℝ) by ring]

/-- Under the strong four-point Hardy–Littlewood hypothesis, the BV weighted arithmetic cubic
and fourth moments differ from their quadratic formal integrals by the uniform square-root
error, for every integer length in the prescribed power band. -/
theorem arithmetic_transfer (SS : Finset ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (_hαβ : α < β) (hβ : β < 1)
    (hSS : SS ∅ = 1) (_hSS1 : ∀ d, SS {d} = 1) (hHL : HL4 SS β)
    (M : ℝ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
      ∀ k : ℕ, (k = 3 ∨ k = 4) →
      ∀ a b : Fin k → ℝ, admissible M a b →
        |discreteRaw N H a b w -
          (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
          C * B * N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
  obtain ⟨A, hA, hred⟩ := reduced_transfer_power_error SS β hSS hHL M ε hM hε
  obtain ⟨D, hD, hcollision⟩ := collision_error_bound M hM
  have hlog := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hε).bound (by norm_num : (0 : ℝ) < 1)
  have hscale := (tendsto_rpow_atTop (show 0 < 1 - β by linarith)).eventually_ge_atTop M
  refine ⟨A + 2 * D, by positivity, ?_⟩
  filter_upwards [hred, hlog, hscale, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hred hlog hscale hL
  have hN0 : 0 < N := by linarith [hred.1]
  have hN1 : 1 ≤ N := by linarith [hred.1]
  have hlog5 : (Real.log N) ^ 5 ≤ N ^ ε := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul, Real.rpow_natCast, Real.rpow_ofNat,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) 5)] using hlog
  have hsqrt : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN1
  have hpow : Real.sqrt N * N ^ ε = N ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
  intro H hlo hhi B w hw k hk a b hab
  have hH1 : (1 : ℝ) ≤ H := (Real.one_le_rpow hN1 hα.le).trans hlo
  have hH : 1 ≤ H := by exact_mod_cast hH1
  have hk4 : k ≤ 4 := by rcases hk with rfl | rfl <;> omega
  have hMH : M * (H : ℝ) ≤ N := by
    calc
      _ ≤ M * N ^ β := mul_le_mul_of_nonneg_left hhi (by linarith)
      _ ≤ N ^ (1 - β) * N ^ β := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; simp
  have hB : 0 ≤ B := hw.2.2.1
  have hfirst : Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) ≤
      N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
    calc
      _ ≤ Real.sqrt N * (H : ℝ) ^ k * N ^ ε := by
        gcongr
        · exact Nat.sub_le k 1
        · exact (pow_le_pow_right₀ hL (by omega : k + 1 ≤ 5)).trans hlog5
      _ = _ := by rw [← hpow]; ring
  have hsecond : (H : ℝ) ^ k * (Real.log N) ^ (k - 1) ≤
      N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
    calc
      _ ≤ (H : ℝ) ^ k * N ^ ε := by
        gcongr
        exact (pow_le_pow_right₀ hL (by omega : k - 1 ≤ 5)).trans hlog5
      _ ≤ Real.sqrt N * ((H : ℝ) ^ k * N ^ ε) := le_mul_of_one_le_left (by positivity) hsqrt
      _ = _ := by rw [← hpow]; ring
  have hc := hcollision N hred.1 H hH hMH B w hw k hk a b hab
  have hr := hred.2 H hH1 hhi B w hw k hk4 a b hab
  calc
    _ ≤ |discreteRaw N H a b w -
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
          ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
            reducedAt (Real.log n) n d)| +
      |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
          ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
            reducedAt (Real.log n) n d) -
        (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| :=
      abs_sub_le _ _ _
    _ ≤ D * B * (Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) +
          (H : ℝ) ^ k * (Real.log N) ^ (k - 1)) +
        A * B * N ^ (1 / 2 + ε) * (H : ℝ) ^ k := add_le_add hc hr
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (show 0 ≤ D * B by positivity)
      nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
