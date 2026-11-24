/- GID: D5/S3/Arith/PrimitiveRoot/SieveThreshold
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SieveThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff; premises=D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower,D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five,D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six
   digest: Uniform parameters for the signed primitive-root sieve. -/
import D5.S3.Arith.PrimitiveRoot.CharacterSieve
import D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaIntegrated99
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic.NormNum.RealSqrt

/-! Uniform arithmetic parameters for the signed character sieve. -/

namespace D5.S3.Arith.PrimitiveRoot.SieveThreshold
open scoped BigOperators
open CharacterExpansion CharacterSieve
open SievePrimeFactors

/-- Feasibility for the coarse smoothed character-sum estimates. -/
def Feasible (x : ℕ) : Prop :=
  ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
    (∀ q : ℕ, q.Prime → q ∣ x - 1 → q ∣ e ∨ q ∈ T) ∧
    0 < delta (sievePrimes x e T) ∧
    errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) *
      ((3 / 2 : ℝ) * Real.sqrt x * Real.log x) <
      delta (sievePrimes x e T) * ((x : ℝ) / 2 - Real.sqrt x)

lemma margin_mono {x y A : ℝ} (hx : Real.exp 2 ≤ x) (hxy : x ≤ y)
    (h : 2 + 3 * A * Real.log x < Real.sqrt x) :
    2 + 3 * A * Real.log y < Real.sqrt y := by
  classical
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hsx := Real.sqrt_pos.2 hx0
  have hsy := Real.sqrt_pos.2 hy0
  by_cases hA : 0 ≤ A
  · have hl := Real.log_div_sqrt_antitoneOn hx (hx.trans hxy) hxy
    have hi : 2 / Real.sqrt y ≤ 2 / Real.sqrt x :=
      div_le_div_of_nonneg_left (by norm_num) hsx (Real.sqrt_le_sqrt hxy)
    have hbase : 2 / Real.sqrt x + 3 * A * (Real.log x / Real.sqrt x) < 1 := by
      apply (div_lt_one hsx).2 at h
      simpa only [add_div, mul_div_assoc] using h
    have ht : 2 / Real.sqrt y + 3 * A * (Real.log y / Real.sqrt y) < 1 :=
      lt_of_le_of_lt (add_le_add hi (mul_le_mul_of_nonneg_left hl (by positivity))) hbase
    apply (div_lt_one hsy).1
    simpa only [add_div, mul_div_assoc] using ht
  · have hAneg : A < 0 := lt_of_not_ge hA
    have he : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two]
    have hs : 2 < Real.sqrt y := (Real.lt_sqrt (by norm_num)).mpr
      (by norm_num; exact he.trans_le (hx.trans hxy))
    have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hm : 3 * A * Real.log y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hl
    linarith

lemma exp_two_le {x : ℝ} (hx : 7.4 ≤ x) : Real.exp 2 ≤ x := by
  exact D5.S3.Arith.Lattices.Klartag.Contact.ThetaIntegrated99.exp_two_le.trans hx

private lemma margin_4100000 {x A : ℝ} (hx : 4100000 ≤ x)
    (hAb : A ≤ 4417 / 100) :
    2 + 3 * A * Real.log x < Real.sqrt x := by
  classical
  have hexp : Real.exp 2 ≤ (4100000 : ℝ) := exp_two_le (by norm_num)
  apply margin_mono hexp hx
  have hlog : Real.log 4100000 < 1523 / 100 := by
    have hb := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 4100000 / 2 ^ 22 by norm_num)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow] at hb
    nlinarith [Real.log_two_lt_d9]
  have hs : (2024 : ℝ) < Real.sqrt 4100000 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hl : 0 ≤ Real.log (4100000 : ℝ) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hAb hl
  nlinarith [hlog]

lemma split_support (x r s : ℕ) (hx : 1 < x)
    (hc : (x - 1).primeFactors.card = r + s) :
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧ e ∣ x - 1 ∧
      (∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ e ∨ p ∈ T) ∧
      e.primeFactors.card = r ∧ T.card = s ∧
      e = ∏ i : Fin r,
        (x - 1).primeFactors.orderEmbOfFin hc (i.castAdd s) ∧
      T = Finset.univ.image (fun i : Fin s =>
        (x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd r i)) ∧
      sievePrimes x e T = T ∧
      delta T = 1 - ∑ i : Fin s,
        ((x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd r i) : ℝ)⁻¹ := by
  classical
  let q := (x - 1).primeFactors.orderEmbOfFin hc
  let a : Fin r → ℕ := fun i => q (i.castAdd s)
  let b : Fin s → ℕ := fun i => q (Fin.natAdd r i)
  let E := Finset.univ.image a
  let T := Finset.univ.image b
  have ha : Function.Injective a := q.injective.comp (Fin.strictMono_castAdd s).injective
  have hb : Function.Injective b := q.injective.comp (Fin.strictMono_natAdd r).injective
  have hmem (i : Fin (r + s)) : q i ∈ (x - 1).primeFactors :=
    Finset.orderEmbOfFin_mem _ hc i
  have hEp : ∀ p ∈ E, p.Prime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_of_mem_primeFactors (hmem _)
  have hTp : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_of_mem_primeFactors (hmem _)
  have hTd : ∀ p ∈ T, p ∣ x - 1 := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.dvd_of_mem_primeFactors (hmem _)
  have hEsub : E ⊆ (x - 1).primeFactors := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hmem _
  let e := ∏ p ∈ E, p
  have he : e ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hEp p hp).ne_zero)
  have hpf : e.primeFactors = E := Nat.primeFactors_prod hEp
  have hed : e ∣ x - 1 :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hEsub).trans (Nat.prod_primeFactors_dvd _)
  have hdis : ∀ p ∈ T, ¬p ∣ e := by
    intro p hp hd
    have hE : p ∈ E := hpf ▸ (hTp p hp).mem_primeFactors hd he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hE
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    have hh := congrArg Fin.val (q.injective (hi.trans hj.symm))
    change i.val = r + j.val at hh
    omega
  have hcover : ∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ e ∨ p ∈ T := by
    intro p hp hd
    have hpm := hp.mem_primeFactors hd (by omega : x - 1 ≠ 0)
    rw [← Finset.image_orderEmbOfFin_univ (x - 1).primeFactors hc] at hpm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hpm
    by_cases hir : i.val < r
    · left
      apply Nat.dvd_of_mem_primeFactors
      rw [hpf]
      refine Finset.mem_image.mpr ⟨⟨i.val, hir⟩, Finset.mem_univ _, ?_⟩
      exact hi
    · right
      refine Finset.mem_image.mpr ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
      change q _ = p
      convert hi using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
  refine ⟨e, T, he, hed, hcover, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpf, Finset.card_image_of_injective _ ha]
    simp
  · rw [Finset.card_image_of_injective _ hb]
    simp
  · dsimp [e, E, a]
    rw [Finset.prod_image (fun _ _ _ _ h => ha h)]
  · rfl
  · ext p
    simp only [sievePrimes, Finset.mem_filter]
    exact ⟨And.left, fun hp => ⟨hp, hTp p hp, hTd p hp, hdis p hp⟩⟩
  · unfold delta
    rw [Finset.sum_image (fun _ _ _ _ h => hb h)]

private lemma margin_scale16 {x A : ℝ} (hx : 16 ≤ x) (hA : 0 ≤ A)
    (h : 2 + 3 * A * Real.log x < Real.sqrt x) :
    2 + 3 * (2 * A) * Real.log (16 * x) < Real.sqrt (16 * x) := by
  classical
  have hx0 : 0 < x := by linarith
  have hl : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hm := mul_nonneg hA (sub_nonneg.mpr hl)
  rw [Real.log_mul (by norm_num) hx0.ne', Real.sqrt_mul (by norm_num)]
  norm_num only [show Real.sqrt 16 = 4 from by norm_num]
  nlinarith

private lemma margin_geometric (m : ℕ) :
    2 + 3 * ((184 / 3 : ℝ) * 2 ^ m) * Real.log (9699690 * 16 ^ m) <
      Real.sqrt (9699690 * 16 ^ m) := by
  classical
  induction m with
  | zero =>
    norm_num only [pow_zero, mul_one]
    have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 9699690)
      (show (9699690 : ℝ) < 2 ^ 24 by norm_num)
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hs : (3100 : ℝ) < Real.sqrt 9699690 :=
      (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    nlinarith [Real.log_two_lt_d9]
  | succ m ih =>
    have hx : (16 : ℝ) ≤ 9699690 * 16 ^ m := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := m)
      nlinarith
    have hX : (9699690 : ℝ) * 16 ^ (m + 1) = 16 * (9699690 * 16 ^ m) := by
      rw [pow_succ]
      ring
    have hA : (184 / 3 : ℝ) * 2 ^ (m + 1) = 2 * ((184 / 3) * 2 ^ m) := by
      rw [pow_succ]
      ring
    rw [hX, hA]
    exact margin_scale16 hx (by positivity) ih

lemma signed_margin {x d K A : ℝ} (hx : 1 ≤ x) (hd : 0 < d)
    (hK : K ≤ d * A) (h : 2 + 3 * A * Real.log x < Real.sqrt x) :
    K * ((3 / 2 : ℝ) * Real.sqrt x * Real.log x) <
      d * (x / 2 - Real.sqrt x) := by
  classical
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hm := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ (3 / 2 : ℝ) * Real.sqrt x * Real.log x by positivity)
  have hpos := mul_pos (mul_pos hd hs) (sub_pos.mpr h)
  have hsq := Real.sq_sqrt (show 0 ≤ x by linarith)
  nlinarith

/-- The covering construction separates arithmetic support bounds from analytic inputs. -/
theorem covering_parameters (x : ℕ) (hx1 : 1 < x) (M N : ℝ)
    (hsmall : ∀ d K : ℝ, 0 < d → K ≤ d * (4417 / 100) → K * M < d * N)
    (hlarge : ∀ m : ℕ, (9699690 : ℝ) * 16 ^ m ≤ x → ∀ d K : ℝ,
      (610847 / 1616615 : ℝ) ≤ d →
      K = d * (2 ^ (m + 2) - 1) + (5 + d) * 2 ^ (m + 2) → K * M < d * N) :
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ x - 1 → q ∣ e ∨ q ∈ T) ∧
      0 < delta (sievePrimes x e T) ∧
      errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) * M <
        delta (sievePrimes x e T) * N := by
  classical
  let k := (x - 1).primeFactors.card
  by_cases hk2 : k ≤ 2
  · obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
      split_support x k 0 hx1 (by simp [k])
    have hr : (Nat.gcd e (x - 1)).primeFactors.card = k := by
      simpa only [Nat.gcd_eq_left hed] using hr
    have hT : T = ∅ := Finset.card_eq_zero.mp hs
    refine ⟨e, T, he, hcover, ?_, ?_⟩
    · rw [hU, hT]
      norm_num [delta]
    · rw [hU, hT]
      apply hsmall _ _ (by norm_num [delta])
      · have hp : (2 : ℝ) ^ k ≤ 2 ^ 2 :=
          pow_le_pow_right₀ (by norm_num) hk2
        norm_num [errorCoefficient, delta, hr] at *
        linarith
  by_cases hk7 : k ≤ 7
  · let s := k - 2
    have hs5 : s ≤ 5 := by dsimp [s]; omega
    have hc : (x - 1).primeFactors.card = 2 + s := by dsimp [s, k] at *; omega
    obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
      split_support x 2 s hx1 hc
    have hr : (Nat.gcd e (x - 1)).primeFactors.card = 2 := by
      simpa only [Nat.gcd_eq_left hed] using hr
    let q := (x - 1).primeFactors.orderEmbOfFin hc
    have hbound := reciprocal_tail_margin_five q (by omega : 2 ≤ 2) hs5
      (q.strictMono.strictMonoOn _)
      (fun i _ => Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ hc i))
      (by intro i; apply q.monotone; change i.val + 2 ≤ 2 + i.val; omega)
    have hδb : (36628 / 85085 : ℝ) ≤ delta T := by rw [hδ]; linarith
    have hδp : 0 < delta T := lt_of_lt_of_le (by norm_num) hδb
    refine ⟨e, T, he, hcover, ?_, ?_⟩
    · rwa [hU]
    · rw [hU]
      apply hsmall _ _ hδp
      · unfold errorCoefficient
        rw [hr, hs]
        have hsR : (s : ℝ) ≤ 5 := by exact_mod_cast hs5
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        nlinarith
  · let m := k - 8
    have hc8 : (x - 1).primeFactors.card = 8 + m := by dsimp [k, m] at *; omega
    have hc : (x - 1).primeFactors.card = (m + 2) + 6 := by omega
    obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
      split_support x (m + 2) 6 hx1 hc
    have hr : (Nat.gcd e (x - 1)).primeFactors.card = m + 2 := by
      simpa only [Nat.gcd_eq_left hed] using hr
    let q := (x - 1).primeFactors.orderEmbOfFin hc
    have hbound := reciprocal_tail_margin_six q (by omega : 2 ≤ m + 2)
      (q.strictMono.strictMonoOn _)
      (fun i _ => Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ hc i))
      (by intro i; apply q.monotone; change i.val + 2 ≤ m + 2 + i.val; omega)
    have hδb : (3 / 8 : ℝ) < delta T := by rw [hδ]; linarith
    have hδp : 0 < delta T := lt_trans (by norm_num) hδb
    have hrad := (radical_lower (x - 1) m hc8.ge).trans
      (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd (x - 1)))
    have hX : (9699690 : ℝ) * 16 ^ m ≤ x := by
      have hn : 9699690 * 16 ^ m ≤ x :=
        (Nat.mul_le_mul_left 9699690 (Nat.pow_le_pow_left (by omega) m)).trans
          (hrad.trans (by omega))
      exact_mod_cast hn
    refine ⟨e, T, he, hcover, ?_, ?_⟩
    · rwa [hU]
    · rw [hU]
      apply hlarge m hX _ _
      · rw [hδ]
        exact hbound
      · unfold errorCoefficient
        rw [hr, hs]
        norm_num

/-- Every integer at least `4100000` admits covering parameters with a strict signed margin. -/
theorem feasible_of_ge_4100000 (x : ℕ) (hx : 4100000 ≤ x) : Feasible x := by
  have hxR : (4100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hxR1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  apply covering_parameters x (by omega)
  · intro d K hd hK
    exact signed_margin hxR1 hd hK (margin_4100000 hxR le_rfl)
  · intro m hX d K hd hK
    have hd' : (3 / 8 : ℝ) < d := by linarith
    have hA : K ≤ d * ((184 / 3) * 2 ^ m) := by
      rw [hK, pow_add]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      have hm := mul_nonneg (sub_nonneg.mpr hd'.le)
        (show (0 : ℝ) ≤ 2 ^ m by positivity)
      nlinarith
    have hX0 : Real.exp 2 ≤ (9699690 : ℝ) * 16 ^ m := by
      apply (exp_two_le (x := 4100000) (by norm_num)).trans
      have := one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := m)
      nlinarith
    exact signed_margin hxR1 (by linarith) hA
      (margin_mono hX0 hX (margin_geometric m))

end D5.S3.Arith.PrimitiveRoot.SieveThreshold

-- The utility header grammar requires its metadata on one physical line.
set_option linter.style.longLine.maxLineLength 320
