/- GID: D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope
   generality: I
   mirror-B: D5/B/S3/Observer/TraceFibers/ThreeActionModulusEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-action words reduce to seven coefficient shapes, and the two non-dominated shapes cross once. -/

import D5.S3.Observer.TraceFibers.FixedFiberPairModulus
import Mathlib.Tactic.NormNum
import D5.S3.ConceptDynamics.Experiment.SelfCalibratingFibers

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

noncomputable section

namespace D5.S3.Observer.TraceFibers.ThreeActionModulusEnvelope

open D5.S3.Observer.TraceFibers.FixedFiberPairModulus

private def shape (w : List Action) : ℝ × ℝ :=
  (wordMatrix w 1 1 - wordMatrix w 0 0, wordMatrix w 1 0)

private theorem finite_envelope_facts
    (k : ℕ) (h x r : ℝ)
    (hk : 1 ≤ k) (hh : 0 < h) (hr : 0 < r)
    (hx : x = (k + h) * r) :
    let τstar := 2 * r * h
    let dstar := r * h
    let ts := (k + 2) * x
    let ta := 2 * (k + 1) * x
    τstar = 2 * dstar ∧ 0 < τstar ∧ τstar < ts ∧ ts < ta := by
  dsimp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hxp : 0 < x := by rw [hx]; positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hks : (0 : ℝ) < k + 1 := by positivity
  have hts : 0 < (k + 2) * x := by positivity
  have hta : 0 < 2 * (k + 1) * x := by positivity
  have hcross : 2 * r * h = 2 * (r * h) := by ring
  have hlt1 : 2 * r * h < (k + 2) * x := by
    rw [hx]
    nlinarith
  have hlt2 : (k + 2) * x < 2 * (k + 1) * x := by
    nlinarith
  exact ⟨hcross, by positivity, hlt1, hlt2⟩

private theorem scalar_formula_of_result
    (upper : Bool) (executed continuation : List Action) (k : ℕ)
    (x ζ τ : ℝ) (hx : 0 < x) (hζ : 0 < ζ) (hk : 1 ≤ k)
    (hexecuted : wordMatrix executed = secondMatrix upper k)
    (he : 0 < (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
      else (wordMatrix continuation * wordMatrix executed) 0 1))
    (hμ : 0 ≤ |(wordMatrix continuation * wordMatrix executed) 1 1 -
      (wordMatrix continuation * wordMatrix executed) 0 0| -
      (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
        else (wordMatrix continuation * wordMatrix executed) 0 1) / ζ * x)
    (hτ : 0 ≤ τ) :
    let B := wordMatrix continuation * wordMatrix executed
    let e := if upper then B 1 0 else B 0 1
    let D := B 1 1 - B 0 0
    let α := e / ζ
    let μ := |D| - α * x
    scalarModulus upper x ζ B τ =
      min x ((Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)) := by
  have hres := result upper executed continuation k x ζ τ hx hζ hk hexecuted hτ he hμ
  dsimp only at hres
  rcases hres with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscalar, _, _, _⟩
  exact hscalar

private theorem word_interface (w : List Action) :
    wordMatrix w = ConceptDynamics.Experiment.SelfCalibratingRulings.matrix
      (w.map (fun a => match a with | .advance => false | .exchange => true)) := by
  let encode : Action → Bool := fun a => match a with | .advance => false | .exchange => true
  have hatom (a : Action) : actionMatrix a =
      (Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic (encode a)).map
        (Int.castRingHom ℝ) := by
    cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [actionMatrix, Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        GoldenCoding.GoldenModularStandardPair.goldenModularStep,
        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
        encode]
  simp only [wordMatrix, ConceptDynamics.Experiment.SelfCalibratingRulings.matrix,
    Arith.FibonacciAtomic.SelfCalibratingRawWords.word, List.prod_eq_foldl,
    List.foldl_reverse, List.foldr_map]
  simpa [encode] using
    (List.foldr_hom (fun B : Matrix (Fin 2) (Fin 2) ℤ => B.map (Int.castRingHom ℝ))
      (l := w) (init := 1)
      (g₁ := fun a B => B * Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic (encode a))
      (g₂ := fun a B => B * actionMatrix a)
      (by intro a B; rw [Matrix.map_mul, hatom]))

private theorem injective_iff (w : List Action) (executed : List Action)
    (k : ℕ) (x r : ℝ) (hk : 1 ≤ k) (hx : 0 < x) (hr : 0 < r)
    (hexecuted : wordMatrix executed = secondMatrix true k) :
    Set.InjOn (fun s => Matrix.trace
      ((wordMatrix w * wordMatrix executed) * source true x r s)) (Set.Ioo 0 x) ↔
    0 < (wordMatrix w * wordMatrix executed) 1 0 ∧
      (wordMatrix w * wordMatrix executed) 1 0 * (x / r) ≤
        |(wordMatrix w * wordMatrix executed) 1 1 -
         (wordMatrix w * wordMatrix executed) 0 0| := by
  have hi := (ConceptDynamics.Experiment.SelfCalibratingFibers.full_fiber_and_signed_capacity
    true x r hx hr k (by omega)
    (w.map (fun a => match a with | .advance => false | .exchange => true))).2.2.2.2.1
  have he : wordMatrix executed = ConceptDynamics.Experiment.SelfCalibratingFibers.endpoint true k := by
    rw [hexecuted]
    simpa [secondMatrix, ConceptDynamics.Experiment.SelfCalibratingFibers.endpoint]
      using upper_shear_power k
  rw [← word_interface, ← he] at hi
  exact hi

private theorem candidate_shapes
    (w executed : List Action) (k : ℕ) (h x r : ℝ)
    (hw : w.length ≤ 3) (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1)
    (hr : 0 < r) (hx : x = (k + h) * r)
    (hexecuted : wordMatrix executed = secondMatrix true k) :
    Set.InjOn (fun s => Matrix.trace
      ((wordMatrix w * wordMatrix executed) * source true x r s)) (Set.Ioo 0 x) ↔
      shape w = (1, 1) ∨ w = [Action.advance, Action.exchange, Action.advance] ∨
        w = [Action.advance, Action.advance, Action.advance] := by
  have short_word_facts (w : List Action) (hw : w.length ≤ 3) :
      (shape w = (0, 0) ∨ shape w = (0, 1) ∨ shape w = (1, 1) ∨
        shape w = (0, 2) ∨ shape w = (-1, 1) ∨ shape w = (2, 1) ∨
        shape w = (2, 2)) ∧
      (shape w = (2, 1) ↔ w = [Action.advance, Action.exchange, Action.advance]) ∧
      (shape w = (2, 2) ↔ w = [Action.advance, Action.advance, Action.advance]) := by
    cases w with
    | nil =>
        simp [shape, wordMatrix]
    | cons a w =>
        cases w with
        | nil =>
            cases a <;>
              norm_num [shape, wordMatrix, actionMatrix,
                GoldenCoding.GoldenModularStandardPair.goldenModularStep,
                HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
                Matrix.mul_apply, Fin.sum_univ_two] <;> decide
        | cons b w =>
            cases w with
            | nil =>
                cases a <;> cases b <;>
                  norm_num [shape, wordMatrix, actionMatrix,
                    GoldenCoding.GoldenModularStandardPair.goldenModularStep,
                    HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
                    Matrix.mul_apply, Fin.sum_univ_two] <;> decide
            | cons c w =>
                cases w with
                | nil =>
                    cases a <;> cases b <;> cases c <;>
                      norm_num [shape, wordMatrix, actionMatrix,
                        GoldenCoding.GoldenModularStandardPair.goldenModularStep,
                        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
                        Matrix.mul_apply, Fin.sum_univ_two] <;> decide
                | cons d w =>
                    simp only [List.length_cons, Nat.reduceAdd] at hw
                    omega
  have hcriterion : Set.InjOn (fun s => Matrix.trace
      ((wordMatrix w * wordMatrix executed) * source true x r s)) (Set.Ioo 0 x) ↔
      shape w = (1, 1) ∨ shape w = (2, 1) ∨ shape w = (2, 2) := by
    have hxpos : 0 < x := by rw [hx]; positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hρ : x / r = k + h := by rw [hx]; exact mul_div_cancel_right₀ _ hr.ne'
    have hsecond : wordMatrix executed = (!![1, (k : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hexecuted]
      simpa [secondMatrix] using upper_shear_power k
    have he : (wordMatrix w * wordMatrix executed) 1 0 = (shape w).2 := by
      simp [shape, hsecond, Matrix.mul_apply, Fin.sum_univ_two]
    have hD : (wordMatrix w * wordMatrix executed) 1 1 -
        (wordMatrix w * wordMatrix executed) 0 0 = k * (shape w).2 + (shape w).1 := by
      simp [shape, hsecond, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [injective_iff w executed k x r hk hxpos hr hexecuted, he, hD, hρ]
    rcases (short_word_facts w hw).1 with hs | hs | hs | hs | hs | hs | hs <;>
      rw [hs] <;> norm_num only [Prod.fst, Prod.snd] <;>
      simp only [hs, Prod.mk.injEq, and_false, false_and, true_and, false_or,
        or_false, true_or, or_true, one_mul, mul_one, mul_zero, add_zero, zero_add,
        zero_lt_one, zero_lt_two, lt_self_iff_false] <;>
      norm_num [abs_of_nonneg (by linarith : (0 : ℝ) ≤ k),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ k + 1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ k - 1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ k + 2),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ k * 2 + 2)] <;>
      first | assumption | nlinarith | (rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ k + -1)]; linarith)
  rw [hcriterion, (short_word_facts w hw).2.1, (short_word_facts w hw).2.2]

private theorem quadratic_order (μ α u v : ℝ) (hμ : 0 ≤ μ) (hα : 0 < α)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    μ * u + α * u ^ 2 ≤ μ * v + α * v ^ 2 ↔ u ≤ v := by
  constructor
  · intro h
    by_contra hn
    have hlt : v < u := lt_of_not_ge hn
    have hp := mul_pos hα (mul_pos (sub_pos.mpr hlt)
      (by linarith : 0 < u + v))
    have hm := mul_nonneg hμ (sub_nonneg.mpr hlt.le)
    nlinarith
  · intro h
    have hs := (sq_le_sq₀ hu hv).2 h
    exact add_le_add (mul_le_mul_of_nonneg_left h hμ)
      (mul_le_mul_of_nonneg_left hs hα.le)

private theorem modulus_inverse
    (executed w : List Action) (k : ℕ) (x r τ : ℝ)
    (hx : 0 < x) (hr : 0 < r) (hk : 1 ≤ k)
    (hexecuted : wordMatrix executed = secondMatrix true k)
    (he : 0 < (wordMatrix w * wordMatrix executed) 1 0)
    (hμ : 0 ≤ |(wordMatrix w * wordMatrix executed) 1 1 -
      (wordMatrix w * wordMatrix executed) 0 0| -
      (wordMatrix w * wordMatrix executed) 1 0 / r * x) (hτ : 0 ≤ τ) :
    let B := wordMatrix w * wordMatrix executed
    let α := B 1 0 / r
    let μ := |B 1 1 - B 0 0| - α * x
    let Ω := scalarModulus true x r B τ
    0 ≤ Ω ∧ Ω ≤ x ∧ (0 < τ → 0 < Ω) ∧
      ∀ d, 0 ≤ d → d ≤ x →
        (d ≤ Ω ↔ μ * d + α * d ^ 2 ≤ τ) ∧
        (d < x → (Ω ≤ d ↔ τ ≤ μ * d + α * d ^ 2)) := by
  have hi := result true executed w k x r τ hx hr hk hexecuted hτ he hμ
  dsimp only at hi ⊢
  rcases hi with ⟨_, _, _, _, _, _, hα, hroot0, hroot, hw0, hwx, _, hwpos,
    _, _, _, hscalar, _, _, _⟩
  refine ⟨hscalar.symm ▸ hw0, hscalar.symm ▸ hwx, fun ht => hscalar.symm ▸ hwpos ht, ?_⟩
  intro d hd hdx
  let α := (wordMatrix w * wordMatrix executed) 1 0 / r
  let μ := |(wordMatrix w * wordMatrix executed) 1 1 -
    (wordMatrix w * wordMatrix executed) 0 0| - α * x
  let q := (Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)
  have hq0 : 0 ≤ q := hroot0
  have hq : μ * q + α * q ^ 2 = τ := hroot
  have hleft := quadratic_order μ α d q hμ hα hd hq0
  have hright := quadratic_order μ α q d hμ hα hq0 hd
  change (d ≤ scalarModulus true x r (wordMatrix w * wordMatrix executed) τ ↔
    μ * d + α * d ^ 2 ≤ τ) ∧ _
  rw [hscalar]
  change (d ≤ min x q ↔ μ * d + α * d ^ 2 ≤ τ) ∧ _
  constructor
  · rw [le_min_iff, and_iff_right hdx]
    simpa only [hq] using hleft.symm
  · intro hdx'
    change min x q ≤ d ↔ τ ≤ μ * d + α * d ^ 2
    rw [min_le_iff, or_iff_right (not_le.mpr hdx')]
    simpa only [hq] using hright.symm

private theorem shape_scalar_data
    (executed w : List Action) (k : ℕ) (h x r δ c τ : ℝ)
    (hk : 1 ≤ k) (hr : 0 < r) (hxpos : 0 < x)
    (hx : x = (k + h) * r)
    (hexecuted : wordMatrix executed = secondMatrix true k)
    (hshape : shape w = (δ, c)) (hc : 0 < c) (hμ : 0 ≤ δ - c * h)
    (hDpos : 0 ≤ k * c + δ) (hτ : 0 ≤ τ) :
    let Ω := scalarModulus true x r (wordMatrix w * wordMatrix executed) τ
    Ω = min x ((Real.sqrt ((δ - c * h) ^ 2 + 4 * (c / r) * τ) -
      (δ - c * h)) / (2 * (c / r))) ∧
    0 ≤ Ω ∧ Ω ≤ x ∧ (0 < τ → 0 < Ω) ∧
      ∀ d, 0 ≤ d → d ≤ x →
        (d ≤ Ω ↔ (δ - c * h) * d + (c / r) * d ^ 2 ≤ τ) ∧
        (d < x → (Ω ≤ d ↔ τ ≤ (δ - c * h) * d + (c / r) * d ^ 2)) := by
  have hsecond : wordMatrix executed = (!![1, (k : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hexecuted]
    simpa [secondMatrix] using upper_shear_power k
  have he : (wordMatrix w * wordMatrix executed) 1 0 = c := by
    have hs := congrArg Prod.snd hshape
    simpa [shape, hsecond, Matrix.mul_apply, Fin.sum_univ_two] using hs
  have hD : |(wordMatrix w * wordMatrix executed) 1 1 -
      (wordMatrix w * wordMatrix executed) 0 0| = k * c + δ := by
    have hs := congrArg Prod.fst hshape
    have heq : (wordMatrix w * wordMatrix executed) 1 1 -
        (wordMatrix w * wordMatrix executed) 0 0 = k * c + δ := by
      simp only [shape, Prod.fst] at hs
      rw [hsecond]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hce : wordMatrix w 1 0 = c := by
        simpa [shape] using congrArg Prod.snd hshape
      rw [hce]
      linarith
    rw [heq, abs_of_nonneg hDpos]
  have hlinear : k * c + δ - c / r * x = δ - c * h := by
    rw [hx]; field_simp [hr.ne']; ring
  have hnonneg : 0 ≤ |(wordMatrix w * wordMatrix executed) 1 1 -
      (wordMatrix w * wordMatrix executed) 0 0| -
      (wordMatrix w * wordMatrix executed) 1 0 / r * x := by
    rw [he, hD, hlinear]; exact hμ
  have hformula := scalar_formula_of_result true executed w k x r τ hxpos hr hk hexecuted
    (he ▸ hc) hnonneg hτ
  have hinv := modulus_inverse executed w k x r τ hxpos hr hk hexecuted
    (he ▸ hc) hnonneg hτ
  dsimp only at hformula hinv ⊢
  simp only [if_true, he, hD, hlinear] at hformula hinv
  exact ⟨hformula, hinv⟩

private theorem envelope_comparison
    (k : ℕ) (h x r : ℝ) (C S A : ℝ → ℝ)
    (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hx : x = (k + h) * r)
    (hinverse : ∀ τ, 0 ≤ τ → ∀ μ a Ω,
      (μ = 1 - h ∧ a = 1 / r ∧ Ω = C τ) ∨
      (μ = 2 - h ∧ a = 1 / r ∧ Ω = S τ) ∨
      (μ = 2 - 2 * h ∧ a = 2 / r ∧ Ω = A τ) →
      0 ≤ Ω ∧ Ω ≤ x ∧ (0 < τ → 0 < Ω) ∧
        ∀ d, 0 ≤ d → d ≤ x →
          (d ≤ Ω ↔ μ * d + a * d ^ 2 ≤ τ) ∧
          (d < x → (Ω ≤ d ↔ τ ≤ μ * d + a * d ^ 2))) :
    ∀ τ, 0 ≤ τ →
      (τ = 0 → S τ = 0 ∧ A τ = 0 ∧ C τ = 0) ∧
      (0 < τ → τ < 2 * r * h → S τ < A τ ∧ S τ < C τ) ∧
      (τ = 2 * r * h → S τ = r * h ∧ A τ = r * h ∧ S τ < C τ) ∧
      (2 * r * h < τ → τ < 2 * (k + 1) * x → A τ < S τ ∧ A τ < C τ) ∧
      ((k + 2) * x ≤ τ → S τ = x) ∧
      (2 * (k + 1) * x ≤ τ → S τ = x ∧ A τ = x ∧ C τ = x) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hxpos : 0 < x := by rw [hx]; positivity
  have hr0 : r ≠ 0 := hr.ne'
  have hdpos : 0 < r * h := mul_pos hr hh
  have hdx : r * h < x := by rw [hx]; nlinarith
  have hμc : 0 ≤ 1 - h := by linarith
  have hμs : 0 ≤ 2 - h := by linarith
  have hμa : 0 ≤ 2 - 2 * h := by linarith
  have ha1 : 0 < 1 / r := by positivity
  have ha2 : 0 < 2 / r := by positivity
  have hcrossS : (2 - h) * (r * h) + (1 / r) * (r * h) ^ 2 = 2 * r * h := by
    field_simp [hr0]; ring
  have hcrossA : (2 - 2 * h) * (r * h) + (2 / r) * (r * h) ^ 2 = 2 * r * h := by
    field_simp [hr0]; ring
  have hts : (2 - h) * x + (1 / r) * x ^ 2 = (k + 2) * x := by
    rw [hx]; field_simp [hr0]; ring
  have hta : (2 - 2 * h) * x + (2 / r) * x ^ 2 = 2 * (k + 1) * x := by
    rw [hx]; field_simp [hr0]; ring
  have htc : (1 - h) * x + (1 / r) * x ^ 2 = (k + 1) * x := by
    rw [hx]; field_simp [hr0]; ring
  have hdiff (d : ℝ) :
      ((2 - 2 * h) * d + (2 / r) * d ^ 2) -
      ((2 - h) * d + (1 / r) * d ^ 2) = d * (d - r * h) / r := by
    field_simp [hr0]; ring
  intro τ hτ
  have hc := hinverse τ hτ (1 - h) (1 / r) (C τ) (Or.inl ⟨rfl, rfl, rfl⟩)
  have hs := hinverse τ hτ (2 - h) (1 / r) (S τ) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have ha := hinverse τ hτ (2 - 2 * h) (2 / r) (A τ) (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have hselfS : S τ < x → (2 - h) * S τ + (1 / r) * (S τ) ^ 2 = τ := by
    intro hlt
    exact le_antisymm ((hs.2.2.2 _ hs.1 hs.2.1).1.mp le_rfl)
      ((hs.2.2.2 _ hs.1 hs.2.1).2 hlt |>.mp le_rfl)
  have hselfA : A τ < x → (2 - 2 * h) * A τ + (2 / r) * (A τ) ^ 2 = τ := by
    intro hlt
    exact le_antisymm ((ha.2.2.2 _ ha.1 ha.2.1).1.mp le_rfl)
      ((ha.2.2.2 _ ha.1 ha.2.1).2 hlt |>.mp le_rfl)
  have hsCap : (k + 2) * x ≤ τ → S τ = x := by
    intro ht
    exact le_antisymm hs.2.1 ((hs.2.2.2 x hxpos.le le_rfl).1.mpr (hts.symm ▸ ht))
  have haBelow : τ < 2 * (k + 1) * x → A τ < x := by
    intro ht
    by_contra hn
    have hp := (ha.2.2.2 x hxpos.le le_rfl).1.mp (le_of_not_gt hn)
    rw [hta] at hp
    linarith
  have hsC : 0 < τ → S τ < x → S τ < C τ := by
    intro ht hsx
    have hp := hs.2.2.1 ht
    have heq := hselfS hsx
    have hsmall : (1 - h) * S τ + (1 / r) * (S τ) ^ 2 < τ := by linarith
    by_contra hn
    have hge := (hc.2.2.2 _ hs.1 hs.2.1).2 hsx |>.mp (le_of_not_gt hn)
    linarith
  refine ⟨?_, ?_, ?_, ?_, hsCap, ?_⟩
  · intro ht
    subst τ
    have hs0 := (hs.2.2.2 0 le_rfl hxpos.le).2 hxpos
    have ha0 := (ha.2.2.2 0 le_rfl hxpos.le).2 hxpos
    have hc0 := (hc.2.2.2 0 le_rfl hxpos.le).2 hxpos
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, le_refl,
      iff_true] at hs0 ha0 hc0
    exact ⟨le_antisymm hs0 hs.1, le_antisymm ha0 ha.1, le_antisymm hc0 hc.1⟩
  · intro ht hlt
    have hsd : S τ < r * h := by
      by_contra hn
      have hp := (hs.2.2.2 _ hdpos.le hdx.le).1.mp (le_of_not_gt hn)
      rw [hcrossS] at hp
      linarith
    have hsx := hsd.trans hdx
    have heq := hselfS hsx
    have hp := div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (hs.2.2.1 ht) (sub_neg.mpr hsd)) hr
    have hsmall : (2 - 2 * h) * S τ + (2 / r) * (S τ) ^ 2 < τ := by
      have he := hdiff (S τ)
      linarith
    have hsa : S τ < A τ := by
      by_contra hn
      have hg := (ha.2.2.2 _ hs.1 hs.2.1).2 hsx |>.mp (le_of_not_gt hn)
      linarith
    exact ⟨hsa, hsC ht hsx⟩
  · intro ht
    have hsle := (hs.2.2.2 _ hdpos.le hdx.le).2 hdx |>.mpr (by rw [hcrossS]; exact ht.le)
    have hsge := (hs.2.2.2 _ hdpos.le hdx.le).1.mpr (by rw [hcrossS]; exact ht.ge)
    have hale := (ha.2.2.2 _ hdpos.le hdx.le).2 hdx |>.mpr (by rw [hcrossA]; exact ht.le)
    have hage := (ha.2.2.2 _ hdpos.le hdx.le).1.mpr (by rw [hcrossA]; exact ht.ge)
    have hseq := le_antisymm hsle hsge
    exact ⟨hseq, le_antisymm hale hage, hsC (by rw [ht]; positivity) (hseq ▸ hdx)⟩
  · intro ht hlt
    have hax := haBelow hlt
    have had : r * h < A τ := by
      by_contra hn
      have hp := (ha.2.2.2 _ hdpos.le hdx.le).2 hdx |>.mp (le_of_not_gt hn)
      rw [hcrossA] at hp
      linarith
    have heq := hselfA hax
    have hp := div_pos (mul_pos (lt_trans hdpos had) (sub_pos.mpr had)) hr
    have hsmall : (2 - h) * A τ + (1 / r) * (A τ) ^ 2 < τ := by
      have he := hdiff (A τ)
      linarith
    have has : A τ < S τ := by
      by_contra hn
      have hg := (hs.2.2.2 _ ha.1 ha.2.1).2 hax |>.mp (le_of_not_gt hn)
      linarith
    have hac : A τ < C τ := by
      by_contra hn
      have hg := (hc.2.2.2 _ ha.1 ha.2.1).2 hax |>.mp (le_of_not_gt hn)
      have : (1 - h) * A τ + (1 / r) * (A τ) ^ 2 < τ := by
        linarith [lt_trans hdpos had]
      linarith
    exact ⟨has, hac⟩
  · intro ht
    have hsx := hsCap (by nlinarith)
    have hax : A τ = x := le_antisymm ha.2.1
      ((ha.2.2.2 x hxpos.le le_rfl).1.mpr (hta.symm ▸ ht))
    have hcx : C τ = x := le_antisymm hc.2.1
      ((hc.2.2.2 x hxpos.le le_rfl).1.mpr (by rw [htc]; nlinarith))
    exact ⟨hsx, hax, hcx⟩

/-- Scalar envelopes for the two distinguished continuations of an actual
    upper-shear history. -/
private theorem two_scalar_formulas
    (k : ℕ) (h x r τ : ℝ) (executed : List Action)
    (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hx : x = (k + h) * r) (hτ : 0 ≤ τ)
    (hexecuted : wordMatrix executed = secondMatrix true k)
 :
    let τstar := 2 * r * h
    let dstar := r * h
    let ts := (k + 2) * x
    let ta := 2 * (k + 1) * x
    τstar = 2 * dstar ∧ 0 < τstar ∧ τstar < ts ∧ ts < ta ∧
    scalarModulus true x r
        (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) τ =
      min x ((Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) / (2 / r)) ∧
    scalarModulus true x r
        (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) τ =
      min x ((Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) / (4 / r)) ∧
    (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 0 = 1 ∧
    |(wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 0 0| = k + 2 ∧
    (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 0 = 2 ∧
    |(wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 0 0| = 2 * k + 2 := by
  dsimp
  have hsecond : wordMatrix executed = (!![1, (k : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hexecuted]
    simpa [secondMatrix] using upper_shear_power k
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hentries :
      (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 0 = 1 ∧
      |(wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 1 -
       (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 0 0| = k + 2 ∧
      (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 0 = 2 ∧
      |(wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 1 -
       (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 0 0| = 2 * k + 2 := by
    rw [hsecond]
    norm_num [wordMatrix, actionMatrix,
      GoldenCoding.GoldenModularStandardPair.goldenModularStep,
      HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k + 2)]
    rw [abs_of_nonneg (by linarith)]
    ring
  obtain ⟨hS_e, hS_D, hA_e, hA_D⟩ := hentries
  have hbase := finite_envelope_facts k h x r hk hh hr hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hS_e_pos : 0 < (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 0 := by rw [hS_e]; norm_num
  have hA_e_pos : 0 < (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 0 := by rw [hA_e]; norm_num
  have hS_mu : 0 ≤ |(wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 1 - (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 0 0| - (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 0 / r * x := by
    rw [hS_D, hS_e, hx]
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    field_simp
    nlinarith
  have hA_mu : 0 ≤ |(wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 1 - (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 0 0| - (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 0 / r * x := by
    rw [hA_D, hA_e, hx]
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    field_simp
    nlinarith
  have hS := scalar_formula_of_result true executed
    [Action.advance, Action.exchange, Action.advance] k x r τ hxpos hr hk hexecuted hS_e_pos hS_mu hτ
  have hA := scalar_formula_of_result true executed
    [Action.advance, Action.advance, Action.advance] k x r τ hxpos hr hk hexecuted hA_e_pos hA_mu hτ
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, ?_, ?_, hS_e, hS_D, hA_e, hA_D⟩
  · dsimp at hS
    have hlinear : (k : ℝ) + 2 - 1 / r * x = 2 - h := by
      rw [hx]
      field_simp [hr0]
      ring
    have hroot :
        (Real.sqrt (((k : ℝ) + 2 - 1 / r * x) ^ 2 + 4 * (1 / r) * τ) -
          ((k : ℝ) + 2 - 1 / r * x)) / (2 * (1 / r)) =
        (Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) / (2 / r) := by
      rw [hlinear]
      have hrad : (2 - h) ^ 2 + 4 * (1 / r) * τ =
          (2 - h) ^ 2 + 4 * τ / r := by
        field_simp [hr0] <;> ring
      rw [hrad]
      field_simp [hr0] <;> ring
    calc
      scalarModulus true x r
          (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) τ =
        min x ((Real.sqrt (((k : ℝ) + 2 - 1 / r * x) ^ 2 + 4 * (1 / r) * τ) -
          ((k : ℝ) + 2 - 1 / r * x)) / (2 * (1 / r))) := by
            simpa [hS_e, hS_D] using hS
      _ = min x ((Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) /
          (2 / r)) := by
            rw [hroot]
  · dsimp at hA
    have hlinear : 2 * (k : ℝ) + 2 - 2 / r * x = 2 - 2 * h := by
      rw [hx]
      field_simp [hr0]
      ring
    have hroot :
        (Real.sqrt ((2 * (k : ℝ) + 2 - 2 / r * x) ^ 2 + 4 * (2 / r) * τ) -
          (2 * (k : ℝ) + 2 - 2 / r * x)) / (2 * (2 / r)) =
      (Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) / (4 / r) := by
      rw [hlinear]
      have hrad : (2 - 2 * h) ^ 2 + 4 * (2 / r) * τ =
          (2 - 2 * h) ^ 2 + 8 * τ / r := by
        field_simp [hr0] <;> ring
      rw [hrad]
      field_simp [hr0] <;> ring
    calc
      scalarModulus true x r
          (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) τ =
        min x ((Real.sqrt ((2 * (k : ℝ) + 2 - 2 / r * x) ^ 2 + 4 * (2 / r) * τ) -
          (2 * (k : ℝ) + 2 - 2 / r * x)) / (2 * (2 / r))) := by
            simpa [hA_e, hA_D] using hA
      _ = min x ((Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) /
          (4 / r)) := by
            rw [hroot]

/-- The exact scalar envelope over all injective chronological continuations of
length at most three. The optimal continuation changes at tolerance `2*r*h`. -/
theorem three_action_modulus_envelope
    (k : ℕ) (h x r : ℝ) (executed : List Action)
    (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hx : x = (k + h) * r)
    (hexecuted : wordMatrix executed = secondMatrix true k) :
    let S := [Action.advance, Action.exchange, Action.advance]
    let A := [Action.advance, Action.advance, Action.advance]
    let Ω := fun w τ => scalarModulus true x r (wordMatrix w * wordMatrix executed) τ
    let admissible := fun w => w.length ≤ 3 ∧ Set.InjOn
      (fun s => Matrix.trace ((wordMatrix w * wordMatrix executed) * source true x r s))
      (Set.Ioo 0 x)
    let optimal := fun w τ => admissible w ∧ ∀ v, admissible v → Ω w τ ≤ Ω v τ
    0 < 2 * r * h ∧ 2 * r * h < (k + 2) * x ∧
    (k + 2) * x < 2 * (k + 1) * x ∧
    (wordMatrix S * wordMatrix executed) 1 0 = 1 ∧
    |(wordMatrix S * wordMatrix executed) 1 1 - (wordMatrix S * wordMatrix executed) 0 0| = k + 2 ∧
    (wordMatrix A * wordMatrix executed) 1 0 = 2 ∧
    |(wordMatrix A * wordMatrix executed) 1 1 - (wordMatrix A * wordMatrix executed) 0 0| = 2 * k + 2 ∧
    |(wordMatrix S * wordMatrix executed) 1 1 - (wordMatrix S * wordMatrix executed) 0 0| -
      (wordMatrix S * wordMatrix executed) 1 0 / r * x = 2 - h ∧
    |(wordMatrix A * wordMatrix executed) 1 1 - (wordMatrix A * wordMatrix executed) 0 0| -
      (wordMatrix A * wordMatrix executed) 1 0 / r * x = 2 - 2 * h ∧
    (∀ w, w.length ≤ 3 →
      (admissible w ↔
        (wordMatrix w 1 1 - wordMatrix w 0 0, wordMatrix w 1 0) = (1, 1) ∨ w = S ∨ w = A)) ∧
    (∀ τ, 0 ≤ τ →
      Ω S τ = min x ((Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) / (2 / r)) ∧
      Ω A τ = min x ((Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) -
        (2 - 2 * h)) / (4 / r)) ∧
      (∀ w, admissible w → min (Ω S τ) (Ω A τ) ≤ Ω w τ) ∧
      (τ = 0 → Ω S τ = 0 ∧ Ω A τ = 0) ∧
      (0 < τ → τ < 2 * r * h → Ω S τ < Ω A τ ∧ ∀ w, optimal w τ ↔ w = S) ∧
      (τ = 2 * r * h → Ω S τ = r * h ∧ Ω A τ = r * h ∧
        ∀ w, optimal w τ ↔ w = S ∨ w = A) ∧
      (2 * r * h < τ → τ < 2 * (k + 1) * x →
        Ω A τ < Ω S τ ∧ ∀ w, optimal w τ ↔ w = A) ∧
      ((k + 2) * x ≤ τ → Ω S τ = x) ∧
      (2 * (k + 1) * x ≤ τ → ∀ w, admissible w → Ω w τ = x)) ∧
    ¬ ∃ w, admissible w ∧ ∀ τ, 0 ≤ τ → optimal w τ := by
  let S := [Action.advance, Action.exchange, Action.advance]
  let A := [Action.advance, Action.advance, Action.advance]
  let Ω := fun w τ => scalarModulus true x r (wordMatrix w * wordMatrix executed) τ
  let admissible := fun w => w.length ≤ 3 ∧ Set.InjOn
    (fun s => Matrix.trace ((wordMatrix w * wordMatrix executed) * source true x r s))
    (Set.Ioo 0 x)
  let optimal := fun w τ => admissible w ∧ ∀ v, admissible v → Ω w τ ≤ Ω v τ
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hxpos : 0 < x := by rw [hx]; positivity
  have hSshape : shape S = (2, 1) := by
    norm_num [S, shape, wordMatrix, actionMatrix,
      GoldenCoding.GoldenModularStandardPair.goldenModularStep,
      HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hAshape : shape A = (2, 2) := by
    norm_num [A, shape, wordMatrix, actionMatrix,
      GoldenCoding.GoldenModularStandardPair.goldenModularStep,
      HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hCshape : shape [Action.advance] = (1, 1) := by
    norm_num [shape, wordMatrix, actionMatrix,
      GoldenCoding.GoldenModularStandardPair.goldenModularStep,
      HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix]
  have hclass (w : List Action) (hw : w.length ≤ 3) :
      admissible w ↔ shape w = (1, 1) ∨ w = S ∨ w = A := by
    change (w.length ≤ 3 ∧ _) ↔ _
    rw [and_iff_right hw, candidate_shapes w executed k h x r hw hk hh hh1 hr hx hexecuted]
  have hSad : admissible S := (hclass S (by simp [S])).2 (Or.inr (Or.inl rfl))
  have hAad : admissible A := (hclass A (by simp [A])).2 (Or.inr (Or.inr rfl))
  have hdata (w : List Action) (δ c τ : ℝ) (hs : shape w = (δ, c))
      (hc : 0 < c) (hm : 0 ≤ δ - c * h) (hd : 0 ≤ (k : ℝ) * c + δ) (ht : 0 ≤ τ) :=
    shape_scalar_data executed w k h x r δ c τ hk hr hxpos hx hexecuted hs hc hm hd ht
  have hCeq (w : List Action) (hs : shape w = (1, 1)) (τ : ℝ) (ht : 0 ≤ τ) :
      Ω w τ = Ω [Action.advance] τ := by
    have hw := (hdata w 1 1 τ hs (by norm_num) (by linarith) (by positivity) ht).1
    have hc := (hdata [Action.advance] 1 1 τ hCshape (by norm_num)
      (by linarith) (by positivity) ht).1
    exact hw.trans hc.symm
  have hinverse : ∀ τ, 0 ≤ τ → ∀ μ a ω,
      (μ = 1 - h ∧ a = 1 / r ∧ ω = Ω [Action.advance] τ) ∨
      (μ = 2 - h ∧ a = 1 / r ∧ ω = Ω S τ) ∨
      (μ = 2 - 2 * h ∧ a = 2 / r ∧ ω = Ω A τ) →
      0 ≤ ω ∧ ω ≤ x ∧ (0 < τ → 0 < ω) ∧
        ∀ d, 0 ≤ d → d ≤ x →
          (d ≤ ω ↔ μ * d + a * d ^ 2 ≤ τ) ∧
          (d < x → (ω ≤ d ↔ τ ≤ μ * d + a * d ^ 2)) := by
    intro τ ht μ a ω hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simpa only [one_mul] using (hdata [Action.advance] 1 1 τ hCshape
        (by norm_num) (by linarith) (by positivity) ht).2
    · simpa only [one_mul] using (hdata S 2 1 τ hSshape
        (by norm_num) (by linarith) (by positivity) ht).2
    · exact (hdata A 2 2 τ hAshape (by norm_num) (by linarith) (by positivity) ht).2
  have hcomp := envelope_comparison k h x r (Ω [Action.advance]) (Ω S) (Ω A)
    hk hh hh1 hr hx hinverse
  have hbase := two_scalar_formulas k h x r 0 executed hk hh hh1 hr hx le_rfl hexecuted
  dsimp only at hbase
  have hstarpos := hbase.2.1
  have hstarlt := hbase.2.2.1
  have htslt := hbase.2.2.2.1
  have hentries := hbase.2.2.2.2.2.2
  have hSμ : |(wordMatrix S * wordMatrix executed) 1 1 -
      (wordMatrix S * wordMatrix executed) 0 0| -
      (wordMatrix S * wordMatrix executed) 1 0 / r * x = 2 - h := by
    change |(wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 0 0| -
      (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) 1 0 / r * x = _
    rw [hentries.1, hentries.2.1, hx]
    field_simp [hr.ne']; ring
  have hAμ : |(wordMatrix A * wordMatrix executed) 1 1 -
      (wordMatrix A * wordMatrix executed) 0 0| -
      (wordMatrix A * wordMatrix executed) 1 0 / r * x = 2 - 2 * h := by
    change |(wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 0 0| -
      (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) 1 0 / r * x = _
    rw [hentries.2.2.1, hentries.2.2.2, hx]
    field_simp [hr.ne']; ring
  have hSA : S ≠ A := by decide
  have hlow (τ : ℝ) (ht : 0 < τ) (hlt : τ < 2 * r * h) :
      Ω S τ < Ω A τ ∧ ∀ w, optimal w τ ↔ w = S := by
    have hc := (hcomp τ ht.le).2.1 ht hlt
    refine ⟨hc.1, ?_⟩
    intro w
    constructor
    · rintro ⟨hw, ho⟩
      rcases (hclass w hw.1).1 hw with hwc | hws | hwa
      · have he := hCeq w hwc τ ht.le
        have hb := ho S hSad
        rw [he] at hb
        linarith [hc.2]
      · exact hws
      · have hb := ho S hSad
        rw [hwa] at hb
        linarith [hc.1]
    · rintro rfl
      refine ⟨hSad, ?_⟩
      intro v hv
      rcases (hclass v hv.1).1 hv with hvc | hvs | hva
      · rw [hCeq v hvc τ ht.le]; exact hc.2.le
      · rw [hvs]
      · rw [hva]; exact hc.1.le
  have hhigh (τ : ℝ) (ht : 2 * r * h < τ) (hlt : τ < 2 * (k + 1) * x) :
      Ω A τ < Ω S τ ∧ ∀ w, optimal w τ ↔ w = A := by
    have htpos : 0 < τ := hstarpos.trans ht
    have hc := (hcomp τ htpos.le).2.2.2.1 ht hlt
    refine ⟨hc.1, ?_⟩
    intro w
    constructor
    · rintro ⟨hw, ho⟩
      rcases (hclass w hw.1).1 hw with hwc | hws | hwa
      · have hb := ho A hAad
        rw [hCeq w hwc τ htpos.le] at hb
        linarith [hc.2]
      · have hb := ho A hAad
        rw [hws] at hb
        linarith [hc.1]
      · exact hwa
    · rintro rfl
      refine ⟨hAad, ?_⟩
      intro v hv
      rcases (hclass v hv.1).1 hv with hvc | hvs | hva
      · rw [hCeq v hvc τ htpos.le]; exact hc.2.le
      · rw [hvs]; exact hc.1.le
      · rw [hva]
  have hcross (τ : ℝ) (ht : τ = 2 * r * h) :
      Ω S τ = r * h ∧ Ω A τ = r * h ∧
        ∀ w, optimal w τ ↔ w = S ∨ w = A := by
    have htpos : 0 < τ := ht.symm ▸ hstarpos
    have hc := (hcomp τ htpos.le).2.2.1 ht
    refine ⟨hc.1, hc.2.1, ?_⟩
    intro w
    constructor
    · rintro ⟨hw, ho⟩
      rcases (hclass w hw.1).1 hw with hwc | hws | hwa
      · have hb := ho S hSad
        rw [hCeq w hwc τ htpos.le] at hb
        linarith [hc.2.2]
      · exact Or.inl hws
      · exact Or.inr hwa
    · intro hw
      have he : Ω S τ = Ω A τ := hc.1.trans hc.2.1.symm
      have hbound : ∀ v, admissible v → Ω S τ ≤ Ω v τ := by
        intro v hv
        rcases (hclass v hv.1).1 hv with hvc | hvs | hva
        · rw [hCeq v hvc τ htpos.le]; exact hc.2.2.le
        · rw [hvs]
        · rw [hva, he]
      rcases hw with rfl | rfl
      · exact ⟨hSad, hbound⟩
      · exact ⟨hAad, fun v hv => he ▸ hbound v hv⟩
  dsimp only
  refine ⟨hstarpos, hstarlt, htslt, hentries.1, hentries.2.1, hentries.2.2.1,
    hentries.2.2.2, hSμ, hAμ, hclass, ?_, ?_⟩
  · intro τ ht
    have hf := two_scalar_formulas k h x r τ executed hk hh hh1 hr hx ht hexecuted
    dsimp only at hf
    have hc := hcomp τ ht
    refine ⟨hf.2.2.2.2.1, hf.2.2.2.2.2.1, ?_,
      fun hz => ⟨(hc.1 hz).1, (hc.1 hz).2.1⟩, hlow τ, hcross τ, hhigh τ,
      hc.2.2.2.2.1, ?_⟩
    · intro w hw
      change min (Ω S τ) (Ω A τ) ≤ Ω w τ
      rcases (hclass w hw.1).1 hw with hwc | hws | hwa
      · rw [hCeq w hwc τ ht]
        rcases eq_or_lt_of_le ht with hz | hp
        · rw [(hc.1 hz.symm).1, (hc.1 hz.symm).2.1, (hc.1 hz.symm).2.2]
          simp only [min_self, le_refl]
        · rcases lt_trichotomy τ (2 * r * h) with hl | he | hg
          · exact le_trans (min_le_left _ _) ((hc.2.1 hp hl).2.le)
          · exact le_trans (min_le_left _ _) ((hc.2.2.1 he).2.2.le)
          · by_cases hl : τ < 2 * (k + 1) * x
            · exact le_trans (min_le_right _ _) ((hc.2.2.2.1 hg hl).2.le)
            · obtain ⟨hsx, hax, hcx⟩ := hc.2.2.2.2.2 (le_of_not_gt hl)
              rw [hsx, hax, hcx]; exact min_le_left _ _
      · rw [hws]; exact min_le_left _ _
      · rw [hwa]; exact min_le_right _ _
    · intro htcap w hw
      change Ω w τ = x
      obtain ⟨hsx, hax, hcx⟩ := hc.2.2.2.2.2 htcap
      rcases (hclass w hw.1).1 hw with hwc | hws | hwa
      · rw [hCeq w hwc τ ht]; exact hcx
      · rw [hws]; exact hsx
      · rw [hwa]; exact hax
  · rintro ⟨w, hw, ho⟩
    have hfirst := (hlow (r * h) (by positivity) (by nlinarith)).2 w
    have heS := hfirst.1 (ho (r * h) (by positivity))
    let t := ((2 * r * h) + 2 * (k + 1) * x) / 2
    have ht : 2 * r * h < t := left_lt_add_div_two.mpr (hstarlt.trans htslt)
    have ht' : t < 2 * (k + 1) * x := add_div_two_lt_right.mpr (hstarlt.trans htslt)
    have heA := (hhigh t ht ht').2 w |>.1 (ho t (by linarith))
    exact hSA (heS.symm.trans heA)


end D5.S3.Observer.TraceFibers.ThreeActionModulusEnvelope
