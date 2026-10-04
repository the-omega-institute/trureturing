/- GID: D5/S1/Words/ClosedRunPoisson
   generality: I
   mirror-B: D5/B/S1/Words/ClosedRunPoisson
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Absolute Poisson error and supplementary bounds for closed fair words. -/

import D5.S1.Words.ClosedRunStarts

open scoped BigOperators ENNReal Classical
open MeasureTheory ProbabilityTheory
open D5.S0.Tower.DBonacci.Names D5.S1.Words.ClosedRunStarts

namespace D5.S1.Words.ClosedRunPoisson

noncomputable section

def fairWordLaw (n : ℕ) : Measure (Fin n → Bool) := uniformOn Set.univ

def outsideCount {n : ℕ} (k : ℕ) (i : Fin (startPositions n k))
    (word : Fin n → Bool) : ℕ :=
  ∑ j : {j : Fin (startPositions n k) //
      ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)},
    if RunStart word k j.val.val then 1 else 0

def runPGF (n k : ℕ) (z : ℝ) : ℝ :=
  ∫ w : Fin n → Bool, z ^ startCount k w ∂(fairWordLaw n)

def runStartMass (n k : ℕ) (i : Fin (startPositions n k)) : ℝ :=
  (fairWordLaw n).real {w | RunStart w k i.val}

def pgfSlope (n k : ℕ) (z : ℝ) : ℝ :=
  ∑ i : Fin (startPositions n k), runStartMass n k i *
    ∫ w : Fin n → Bool, z ^ outsideCount k i w ∂(fairWordLaw n)

def runMean (n k : ℕ) : ℝ := ∑ i : Fin (startPositions n k), runStartMass n k i

def runCharge (n k : ℕ) : ℝ :=
  ∑ i : Fin (startPositions n k), runStartMass n k i *
    ∫ w : Fin n → Bool, ((startCount k w - outsideCount k i w : ℕ) : ℝ) ∂(fairWordLaw n)

/-- All three finite-word probability bounds under the uniform fair-bit law. -/
theorem closed_word_poisson_bounds (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    |(dbonacci k (n + 2) : ℝ) / (2 : ℝ) ^ n -
        Real.exp (-((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1))| ≤
      min 1 (((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)) *
        (k + 1 : ℝ) * (2 : ℝ)⁻¹ ^ k ∧
    1 - (dbonacci k (n + 2) : ℝ) / (2 : ℝ) ^ n ≤
      ((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) ∧
    (0 < ((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) →
      (dbonacci k (n + 2) : ℝ) / (2 : ℝ) ^ n ≤
        1 / (((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1))) := by
  classical
  let : IsProbabilityMeasure (fairWordLaw n) := by dsimp [fairWordLaw]; infer_instance
  have stage : ∀ z : ℝ, HasDerivAt (runPGF n k) (pgfSlope n k z) z ∧
      (0 ≤ z → z ≤ 1 →
        0 ≤ pgfSlope n k z - runMean n k * runPGF n k z ∧
        pgfSlope n k z - runMean n k * runPGF n k z ≤ runCharge n k) := by
    intro z
    classical
    let μ := fairWordLaw n
    let : IsProbabilityMeasure μ := by dsimp [μ, fairWordLaw]; infer_instance
    have int (f : (Fin n → Bool) → ℝ) : Integrable f μ := by
      exact integrableOn_univ.mp (IntegrableOn.of_finite (μ := μ) (f := f) Set.finite_univ)
    have meanSum (f : (Fin n → Bool) → ℝ) :
        (∫ w, f w ∂μ) = (2 : ℝ)⁻¹ ^ n * ∑ w, f w := by
      rw [integral_fintype (int f)]
      simp only [μ, fairWordLaw, measureReal_def, uniformOn_univ,
        Measure.count_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow,
        Nat.cast_ofNat, smul_eq_mul, one_div, ← inv_pow, Finset.mul_sum]
    have outsideIndep : ∀ i : Fin (startPositions n k),
        IndepFun (fun w : Fin n → Bool => decide (RunStart w k i.val))
          (fun w : Fin n → Bool =>
            fun j : {j : Fin (startPositions n k) //
                ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)} =>
              decide (RunStart w k j.val.val)) μ := by
      intro i
      classical
      let S : Finset (Fin n) := Finset.univ.filter fun b =>
        (i.val ≤ b.val ∧ b.val < i.val + k) ∨ b.val + 1 = i.val
      let fill (U : Finset (Fin n)) (x : U → Bool) : Fin n → Bool :=
        fun b => if h : b ∈ U then x ⟨b, h⟩ else false
      have blockCongr : ∀ (s : ℕ) (w v : Fin n → Bool),
          (∀ b : Fin n, (s ≤ b.val ∧ b.val < s + k) ∨ b.val + 1 = s → w b = v b) →
          (RunStart w k s ↔ RunStart v k s) := by
        intro s w v heq
        constructor
        · rintro ⟨⟨hlen, hbits⟩, hprev⟩
          refine ⟨⟨hlen, ?_⟩, ?_⟩
          · intro b hlo hhi
            rw [← heq b (Or.inl ⟨hlo, hhi⟩)]
            exact hbits b hlo hhi
          · intro b hb
            rw [← heq b (Or.inr hb)]
            exact hprev b hb
        · rintro ⟨⟨hlen, hbits⟩, hprev⟩
          refine ⟨⟨hlen, ?_⟩, ?_⟩
          · intro b hlo hhi
            rw [heq b (Or.inl ⟨hlo, hhi⟩)]
            exact hbits b hlo hhi
          · intro b hb
            rw [heq b (Or.inr hb)]
            exact hprev b hb
      have own : ∀ w : Fin n → Bool,
          RunStart w k i.val ↔ RunStart (fill S (fun b => w b.val)) k i.val := by
        intro w
        apply blockCongr
        intro b hb
        have hS : b ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb
        simp [fill, hS]
      have outside : ∀ (w : Fin n → Bool)
          (j : {j : Fin (startPositions n k) //
              ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)}),
          RunStart w k j.val.val ↔
            RunStart (fill Sᶜ (fun b => w b.val)) k j.val.val := by
        intro w j
        apply blockCongr
        intro b hb
        have hS : b ∉ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hb'
          have hj := j.property
          rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;> omega
        simp [fill, hS]
      have coords : iIndepFun (fun b : Fin n => fun w : Fin n → Bool => w b)
          (fairWordLaw n) := by
        have law : fairWordLaw n = Measure.pi
            (fun _ : Fin n => uniformOn (Set.univ : Set Bool)) := by
          simpa only [fairWordLaw, Set.pi_univ] using
            (uniformOn_pi (f := fun _ : Fin n => (Set.univ : Set Bool)))
        rw [law]
        exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
      have disjoint : Disjoint S Sᶜ := disjoint_compl_right
      have hind := coords.indepFun_finset S Sᶜ disjoint (fun b => measurable_pi_apply b)
      let f : (S → Bool) → Bool := fun x => decide (RunStart (fill S x) k i.val)
      let g : (↥(Sᶜ) → Bool) →
          ({j : Fin (startPositions n k) //
              ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)} → Bool) :=
        fun x j => decide (RunStart (fill Sᶜ x) k j.val.val)
      have composed := hind.comp (measurable_of_finite f) (measurable_of_finite g)
      have hf : (f ∘ fun w : Fin n → Bool => fun b : S => w b.val) =
          (fun w : Fin n → Bool => decide (RunStart w k i.val)) := by
        funext w
        exact congrArg (fun p : Prop => decide p) (propext (own w).symm)
      have hg : (g ∘ fun w : Fin n → Bool => fun b : ↥(Sᶜ) => w b.val) =
          (fun w : Fin n → Bool =>
            fun j : {j : Fin (startPositions n k) //
                ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)} =>
              decide (RunStart w k j.val.val)) := by
        funext w j
        exact congrArg (fun p : Prop => decide p) (propext (outside w j).symm)
      rw [hf, hg] at composed
      exact composed
    have exclusive : ∀ (i j : Fin (startPositions n k)) (w : Fin n → Bool),
        i.val < j.val → j.val ≤ i.val + k →
          ¬ (RunStart w k i.val ∧ RunStart w k j.val) := by
      intro i j w hij hnear
      rintro ⟨hi, hj⟩
      have hjbound := hj.1.1
      let p : Fin n := ⟨j.val - 1, by omega⟩
      have htrue : w p = true := hi.1.2 p (by simp [p]; omega) (by simp [p]; omega)
      have hfalse : w p = false := hj.2 p (by simp [p]; omega)
      simp [htrue] at hfalse
    have countOnStart : ∀ (i : Fin (startPositions n k)) (w : Fin n → Bool),
        RunStart w k i.val → startCount k w = outsideCount k i w + 1 := by
      intro i w hi
      let f : Fin (startPositions n k) → ℕ := fun j => if RunStart w k j.val then 1 else 0
      have perj : ∀ j : Fin (startPositions n k),
          f j = (if j = i then 1 else 0) +
            (if ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k) then f j else 0) := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [f, hi]
        · by_cases hout : ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)
          · simp [hji, hout]
          · have hnear := not_not.mp hout
            have hn : ¬ RunStart w k j.val := by
              intro hj
              have hval : j.val ≠ i.val := by exact fun he => hji (Fin.ext he)
              rcases lt_or_gt_of_ne hval with hlt | hgt
              · exact exclusive j i w hlt hnear.1 ⟨hj, hi⟩
              · exact exclusive i j w hgt hnear.2 ⟨hi, hj⟩
            simp [f, hji, hout, hn]
      have sub : outsideCount k i w =
          ∑ j : Fin (startPositions n k),
            if ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k) then f j else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (by simp) f).symm
      change (∑ j, f j) = _
      calc
        (∑ j, f j) = ∑ j, ((if j = i then 1 else 0) +
            (if ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k) then f j else 0)) :=
          Finset.sum_congr rfl (fun j _ => perj j)
        _ = outsideCount k i w + 1 := by
          rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', ← sub]
          omega
    have pointwise : ∀ w : Fin n → Bool,
        (startCount k w : ℝ) * z ^ (startCount k w - 1) =
          ∑ i : Fin (startPositions n k),
            (if RunStart w k i.val then (1 : ℝ) else 0) * z ^ outsideCount k i w := by
      intro w
      conv_lhs => arg 1; rw [startCount]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : RunStart w k i.val
      · simp only [hs, if_true, one_mul]
        rw [countOnStart i w hs]
        simp
      · simp [hs]
    have factor : ∀ i : Fin (startPositions n k),
        (∫ w, (if RunStart w k i.val then (1 : ℝ) else 0) * z ^ outsideCount k i w ∂μ) =
          μ.real {w | RunStart w k i.val} * ∫ w, z ^ outsideCount k i w ∂μ := by
      intro i
      let f : Bool → ℝ := fun b => if b then 1 else 0
      let g : ({j : Fin (startPositions n k) //
            ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)} → Bool) → ℝ :=
        fun bs => z ^ (∑ j, if bs j then 1 else 0 : ℕ)
      have hd := (outsideIndep i).comp (measurable_of_finite f) (measurable_of_finite g)
      have hf : (f ∘ fun w : Fin n → Bool => decide (RunStart w k i.val)) =
          (fun w : Fin n → Bool => if RunStart w k i.val then (1 : ℝ) else 0) := by
        funext w
        simp [f]
      have hg : (g ∘ fun w : Fin n → Bool =>
            fun j : {j : Fin (startPositions n k) //
                ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)} =>
              decide (RunStart w k j.val.val)) =
          (fun w : Fin n → Bool => z ^ outsideCount k i w) := by
        funext w
        simp [g, outsideCount]
      rw [hf, hg] at hd
      rw [hd.integral_fun_mul_eq_mul_integral
        (measurable_of_finite _).aestronglyMeasurable
        (measurable_of_finite _).aestronglyMeasurable]
      congr 1
      have heq : (fun w : Fin n → Bool => if RunStart w k i.val then (1 : ℝ) else 0) =
          Set.indicator {w | RunStart w k i.val} (fun _ => (1 : ℝ)) := by
        funext w
        simp [Set.indicator]
      rw [heq, integral_indicator (Set.toFinite _).measurableSet]
      simp
    have dsum : HasDerivAt (fun t : ℝ => (2 : ℝ)⁻¹ ^ n * ∑ w : Fin n → Bool,
        t ^ startCount k w)
        ((2 : ℝ)⁻¹ ^ n * ∑ w : Fin n → Bool,
          (startCount k w : ℝ) * z ^ (startCount k w - 1)) z := by
      apply HasDerivAt.const_mul
      exact HasDerivAt.fun_sum (fun w _ => hasDerivAt_pow (startCount k w) z)
    have d : HasDerivAt (runPGF n k)
        (∫ w, (startCount k w : ℝ) * z ^ (startCount k w - 1) ∂μ) z := by
      convert dsum using 1
      · funext t
        exact meanSum _
      · exact meanSum _
    have result : (∫ w, (startCount k w : ℝ) * z ^ (startCount k w - 1) ∂μ) =
        ∑ i : Fin (startPositions n k), μ.real {w | RunStart w k i.val} *
          ∫ w, z ^ outsideCount k i w ∂μ := by
      simp_rw [pointwise]
      rw [integral_finsetSum Finset.univ (fun i _ => int _)]
      exact Finset.sum_congr rfl (fun i _ => factor i)
    rw [result] at d
    refine ⟨d, ?_⟩
    intro hz0 hz1
    have vLe : ∀ (i : Fin (startPositions n k)) (w : Fin n → Bool),
        outsideCount k i w ≤ startCount k w := by
      intro i w
      have sub : outsideCount k i w =
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (startPositions n k) => ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)),
            if RunStart w k j.val then 1 else 0 := by
        exact (Finset.sum_subtype _ (by simp)
          (fun j : Fin (startPositions n k) => if RunStart w k j.val then 1 else 0)).symm
      rw [sub, startCount]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have powers : ∀ (i : Fin (startPositions n k)) (w : Fin n → Bool),
        0 ≤ z ^ outsideCount k i w - z ^ startCount k w ∧
        z ^ outsideCount k i w - z ^ startCount k w ≤
          (startCount k w - outsideCount k i w : ℕ) := by
      intro i w
      have hp : z ^ startCount k w ≤ z ^ outsideCount k i w :=
        pow_le_pow_of_le_one hz0 hz1 (vLe i w)
      refine ⟨sub_nonneg.mpr hp, ?_⟩
      by_cases heq : startCount k w = outsideCount k i w
      · simp [heq]
      · have hn : 1 ≤ startCount k w - outsideCount k i w := by
          have := vLe i w
          omega
        have hn' : (1 : ℝ) ≤ (startCount k w - outsideCount k i w : ℕ) := by exact_mod_cast hn
        have ha : z ^ outsideCount k i w ≤ 1 := pow_le_one₀ hz0 hz1
        have hb : 0 ≤ z ^ startCount k w := pow_nonneg hz0 _
        linarith
    have defect : pgfSlope n k z - runMean n k * runPGF n k z =
        ∑ i : Fin (startPositions n k), runStartMass n k i *
          ∫ w, (z ^ outsideCount k i w - z ^ startCount k w) ∂μ := by
      unfold pgfSlope runMean runPGF
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_sub (int _) (int _)]
      ring
    rw [defect]
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (measureReal_nonneg) (integral_nonneg (fun w => (powers i w).1))
    · apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      exact integral_mono (int _) (int _) (fun w => (powers i w).2)
  have marginals : ∀ i : Fin (startPositions n k), runStartMass n k i =
      if i.val = 0 then (2 : ℝ)⁻¹ ^ k else (2 : ℝ)⁻¹ ^ (k + 1) := by
    intro i
    unfold runStartMass
    classical
    have hib : i.val + k ≤ n := by
      have hi := i.isLt
      simp only [startPositions] at hi
      omega
    let S : Finset (Fin n) :=
      (Finset.Ico (i.val - 1) (i.val + k)).attachFin (by
        intro b hb
        have := (Finset.mem_Ico.mp hb).2
        omega)
    have memS : ∀ b : Fin n, b ∈ S ↔
        (i.val ≤ b.val ∧ b.val < i.val + k) ∨ b.val + 1 = i.val := by
      intro b
      simp only [S, Finset.mem_attachFin, Finset.mem_Ico]
      omega
    have event : {w : Fin n → Bool | RunStart w k i.val} =
        (S : Set (Fin n)).pi (fun b => {decide (i.val ≤ b.val)}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · rintro ⟨⟨hlen, hbits⟩, hprev⟩ b hb
        rcases (memS b).mp hb with hwin | hp
        · simpa [hwin.1] using hbits b hwin.1 hwin.2
        · have hlt : ¬ i.val ≤ b.val := by omega
          simpa [hlt] using hprev b hp
      · intro hw
        refine ⟨⟨hib, ?_⟩, ?_⟩
        · intro b hlo hhi
          simpa [hlo] using hw b ((memS b).mpr (Or.inl ⟨hlo, hhi⟩))
        · intro b hb
          have hlt : ¬ i.val ≤ b.val := by omega
          simpa [hlt] using hw b ((memS b).mpr (Or.inr hb))
    have law : fairWordLaw n =
        Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set Bool)) := by
      simpa only [fairWordLaw, Set.pi_univ] using
        (uniformOn_pi (f := fun _ : Fin n => (Set.univ : Set Bool)))
    have prob : fairWordLaw n {w | RunStart w k i.val} = (2 : ℝ≥0∞)⁻¹ ^ S.card := by
      rw [event, law, Measure.pi_pi_finset]
      simp only [uniformOn_univ, Measure.count_singleton, Fintype.card_bool, one_div, Finset.prod_const]
      norm_num
    have size : S.card = if i.val = 0 then k else k + 1 := by
      simp only [S, Finset.card_attachFin, Nat.card_Ico]
      split_ifs <;> omega
    rw [measureReal_def, prob, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, size]
    split_ifs <;> rfl
  let β : ℝ := (2 : ℝ)⁻¹ ^ (k + 1)
  let ε : ℝ := (2 : ℝ)⁻¹ ^ k
  let i0 : Fin (startPositions n k) := ⟨0, by simp only [startPositions]; omega⟩
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have ratio : ε = 2 * β := by dsimp [ε, β]; rw [pow_succ]; norm_num; ring
  have splitMass : ∀ j : Fin (startPositions n k),
      runStartMass n k j = β + if j.val = 0 then β else 0 := by
    intro j
    rw [marginals]
    split_ifs
    · change ε = β + β
      linarith [ratio]
    · change β = β + 0
      ring
  have zeroEq : ∀ j : Fin (startPositions n k), j.val = 0 ↔ j = i0 := by
    intro j
    constructor
    · intro hj; exact Fin.ext hj
    · intro hj; subst j; rfl
  have zeroSum : (∑ j : Fin (startPositions n k), if j.val = 0 then β else 0) = β := by
    simp_rw [zeroEq]
    exact Fintype.sum_ite_eq' i0 (fun _ => β)
  have meanEq : runMean n k = ((n - k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
    unfold runMean
    simp_rw [splitMass]
    rw [Finset.sum_add_distrib, zeroSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul, startPositions, Nat.cast_add, Nat.cast_one]
    dsimp [β]
    rw [inv_pow, div_eq_mul_inv]
    ring
  have integrable (f : (Fin n → Bool) → ℝ) : Integrable f (fairWordLaw n) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have expectedMark : ∀ j : Fin (startPositions n k),
      (∫ w : Fin n → Bool, (if RunStart w k j.val then (1 : ℝ) else 0) ∂(fairWordLaw n)) =
        runStartMass n k j := by
    intro j
    have heq : (fun w : Fin n → Bool => if RunStart w k j.val then (1 : ℝ) else 0) =
        Set.indicator {w | RunStart w k j.val} (fun _ => (1 : ℝ)) := by
      funext w; simp [Set.indicator]
    rw [heq, integral_indicator (Set.toFinite _).measurableSet]
    simp [runStartMass]
  have expectedNear : ∀ i : Fin (startPositions n k),
      (∫ w : Fin n → Bool, ((startCount k w - outsideCount k i w : ℕ) : ℝ) ∂(fairWordLaw n)) =
        ∑ j : {j : Fin (startPositions n k) //
          i.val ≤ j.val + k ∧ j.val ≤ i.val + k}, runStartMass n k j.val := by
    intro i
    have partition : ∀ w : Fin n → Bool, outsideCount k i w +
        (∑ j : {j : Fin (startPositions n k) // i.val ≤ j.val + k ∧ j.val ≤ i.val + k},
          if RunStart w k j.val.val then 1 else 0) = startCount k w := by
      intro w
      let f : Fin (startPositions n k) → ℕ := fun j => if RunStart w k j.val then 1 else 0
      let P : Fin (startPositions n k) → Prop := fun j =>
        i.val ≤ j.val + k ∧ j.val ≤ i.val + k
      have near : (∑ j ∈ Finset.univ.filter P, f j) =
          ∑ j : {j : Fin (startPositions n k) //
            i.val ≤ j.val + k ∧ j.val ≤ i.val + k}, f j.val :=
        Finset.sum_subtype _ (by simp [P]) f
      have out : (∑ j ∈ Finset.univ.filter (fun j => ¬ P j), f j) = outsideCount k i w :=
        Finset.sum_subtype _ (by simp [P]) f
      have total := Finset.sum_filter_add_sum_filter_not Finset.univ P f
      rw [near, out] at total
      simpa only [add_comm, f, startCount] using total
    have point : ∀ w : Fin n → Bool,
        ((startCount k w - outsideCount k i w : ℕ) : ℝ) =
          ∑ j : {j : Fin (startPositions n k) // i.val ≤ j.val + k ∧ j.val ≤ i.val + k},
            if RunStart w k j.val.val then (1 : ℝ) else 0 := by
      intro w
      rw [← partition w, Nat.add_sub_cancel_left]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp_rw [point]
    rw [integral_finsetSum Finset.univ (fun j _ => integrable _)]
    exact Finset.sum_congr rfl (fun j _ => expectedMark j.val)
  have neighborhood : ∀ i : Fin (startPositions n k),
      (∑ j : {j : Fin (startPositions n k) // i.val ≤ j.val + k ∧ j.val ≤ i.val + k},
        runStartMass n k j.val) ≤ (k + 1 : ℝ) * ε := by
    intro i
    let A := {j : Fin (startPositions n k) // i.val ≤ j.val + k ∧ j.val ≤ i.val + k}
    have cardBound : Fintype.card A ≤ 2 * k + 1 := by
      let f : A → Fin (2 * k + 1) := fun j => ⟨j.val.val + k - i.val, by
        have hj := j.property
        omega⟩
      have hf : Function.Injective f := by
        intro a b hab
        have he := congrArg Fin.val hab
        have ha := a.property
        have hb := b.property
        apply Subtype.ext
        apply Fin.ext
        dsimp [f] at he
        omega
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    have exceptional : (∑ j : A, if j.val.val = 0 then β else 0) ≤ β := by
      let B : Finset (Fin (startPositions n k)) := Finset.univ.filter fun j =>
        i.val ≤ j.val + k ∧ j.val ≤ i.val + k
      have changeSum : (∑ j : A, if j.val.val = 0 then β else 0) =
          ∑ j ∈ B, if j.val = 0 then β else 0 := by
        exact (Finset.sum_subtype B (by simp [B])
          (fun j : Fin (startPositions n k) => if j.val = 0 then β else 0)).symm
      rw [changeSum]
      calc
        _ ≤ ∑ j : Fin (startPositions n k), if j.val = 0 then β else 0 := by
          dsimp [B]
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro j hj hnj
          split_ifs <;> positivity
        _ = β := zeroSum
    change (∑ j : A, runStartMass n k j.val) ≤ _
    simp_rw [splitMass]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have cb : (Fintype.card A : ℝ) ≤ (2 * k + 1 : ℕ) := by exact_mod_cast cardBound
    have bound := mul_le_mul_of_nonneg_right cb hβ
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at bound
    have re := ratio
    nlinarith
  have chargeBound : runCharge n k ≤ runMean n k * ((k + 1 : ℝ) * ε) := by
    unfold runCharge
    simp_rw [expectedNear]
    calc
      _ ≤ ∑ i : Fin (startPositions n k), runStartMass n k i * ((k + 1 : ℝ) * ε) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (neighborhood i) measureReal_nonneg
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have origin : runPGF n k 0 = (dbonacci k (n + 2) : ℝ) / (2 : ℝ) ^ n := by
    have integrand : (fun w : Fin n → Bool => (0 : ℝ) ^ startCount k w) =
        Set.indicator {w | startCount k w = 0} (fun _ => (1 : ℝ)) := by
      funext w
      by_cases hw : startCount k w = 0 <;> simp [hw, Set.indicator]
    rw [runPGF, integrand, integral_indicator (Set.toFinite _).measurableSet]
    rw [integral_const]
    simp only [smul_eq_mul, mul_one]
    rw [measureReal_def, Measure.restrict_apply_univ]
    change (fairWordLaw n).real {w | startCount k w = 0} = _
    have event : {w : Fin n → Bool | startCount k w = 0} =
        {w | DBonacciAdmissible k n w} := by
      ext w
      exact ((closed_word_run_start_equivalence n k (by omega) hkn w).1.trans
        (closed_word_run_start_equivalence n k (by omega) hkn w).2).symm
    rw [event, measureReal_def, fairWordLaw, uniformOn_univ]
    have count : Measure.count {w : Fin n → Bool | DBonacciAdmissible k n w} =
        (dbonacci k (n + 2) : ℝ≥0∞) := by
      rw [Measure.count_apply (Set.toFinite _).measurableSet, ← Set.coe_fintypeCard]
      change (Fintype.card (DBonacciName k n) : ℝ≥0∞) = _
      rw [dbonacci_name_card]
    rw [count]
    simp [ENNReal.toReal_div]
  let M := runMean n k
  let C := runCharge n k
  have hp0 : 0 < runStartMass n k i0 := by
    rw [marginals]
    dsimp [i0]
    positivity
  have hM : 0 < M := by
    apply lt_of_lt_of_le hp0
    change runStartMass n k i0 ≤ ∑ i, runStartMass n k i
    exact Finset.single_le_sum (fun i _ => (show 0 ≤ runStartMass n k i from measureReal_nonneg))
      (Finset.mem_univ i0)
  have hMne : M ≠ 0 := ne_of_gt hM
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg measureReal_nonneg (integral_nonneg (fun _ => Nat.cast_nonneg _))
  have endpoint : runPGF n k 1 = 1 := by simp [runPGF]
  let g : ℝ → ℝ := fun x => Real.exp (-M * x) * runPGF n k x
  let h : ℝ → ℝ := fun x => Real.exp (-M * x) * (runPGF n k x + C / M)
  have dg : ∀ x : ℝ, HasDerivAt g
      (Real.exp (-M * x) * (pgfSlope n k x - M * runPGF n k x)) x := by
    intro x
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-M * t))
        (Real.exp (-M * x) * (-M)) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (-M)).exp
    have raw : HasDerivAt g
        (Real.exp (-M * x) * (-M) * runPGF n k x +
          Real.exp (-M * x) * pgfSlope n k x) x := hexp.mul (stage x).1
    convert raw using 1
    ring
  have dh : ∀ x : ℝ, HasDerivAt h
      (Real.exp (-M * x) * (pgfSlope n k x - M * runPGF n k x - C)) x := by
    intro x
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-M * t))
        (Real.exp (-M * x) * (-M)) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (-M)).exp
    have raw : HasDerivAt h
        (Real.exp (-M * x) * (-M) * (runPGF n k x + C / M) +
          Real.exp (-M * x) * pgfSlope n k x) x :=
      hexp.mul ((stage x).1.add_const (C / M))
    convert raw using 1
    field_simp [hMne]
    ring
  have gm : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr (fun x => (dg x).continuousAt)).continuousOn)
      (fun x hx => (dg x).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    exact mul_nonneg (Real.exp_pos _).le ((stage x).2 hx'.1 hx'.2).1
  have ha : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr (fun x => (dh x).continuousAt)).continuousOn)
      (fun x hx => (dh x).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (by have hb := ((stage x).2 hx'.1 hx'.2).2; dsimp [M, C]; linarith)
  have upper := gm (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  have lower := ha (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [g, h, mul_zero, Real.exp_zero, one_mul, mul_one, endpoint] at upper lower
  have central : |runPGF n k 0 - Real.exp (-M)| ≤ C / M * (1 - Real.exp (-M)) := by
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  have calibrated : |runPGF n k 0 - Real.exp (-M)| ≤ min 1 M * (k + 1 : ℝ) * ε := by
    by_cases hsmall : M ≤ 1
    · rw [min_eq_right hsmall]
      have linear : 1 - Real.exp (-M) ≤ M := by linarith [Real.add_one_le_exp (-M)]
      have cap := mul_le_mul_of_nonneg_left linear (div_nonneg hC hM.le)
      have cancel : C / M * M = C := by field_simp
      rw [cancel] at cap
      exact le_trans (le_trans central cap) (by dsimp [M, C]; nlinarith [chargeBound])
    · rw [min_eq_left (by linarith : 1 ≤ M), one_mul]
      have linear : 1 - Real.exp (-M) ≤ 1 := by linarith [Real.exp_pos (-M)]
      have cap := mul_le_mul_of_nonneg_left linear (div_nonneg hC hM.le)
      have cb : C / M ≤ (k + 1 : ℝ) * ε := (div_le_iff₀ hM).mpr
        (by dsimp [M, C]; nlinarith [chargeBound])
      exact le_trans (le_trans central (by simpa using cap)) cb
  have expectedW : (∫ w : Fin n → Bool, (startCount k w : ℝ) ∂(fairWordLaw n)) = M := by
    simp only [startCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [integral_finsetSum Finset.univ (fun j _ => integrable _)]
    exact Finset.sum_congr rfl (fun j _ => expectedMark j)
  have meanSum (f : (Fin n → Bool) → ℝ) :
      (∫ w, f w ∂(fairWordLaw n)) = (2 : ℝ)⁻¹ ^ n * ∑ w, f w := by
    rw [integral_fintype (integrable f)]
    simp only [fairWordLaw, measureReal_def, uniformOn_univ,
      Measure.count_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow,
      Nat.cast_ofNat, smul_eq_mul, one_div, ← inv_pow, Finset.mul_sum]
  have dAverage : ∀ (a : (Fin n → Bool) → ℝ) (c : (Fin n → Bool) → ℕ) (z : ℝ),
      HasDerivAt (fun t => ∫ w, a w * t ^ c w ∂(fairWordLaw n))
        (∫ w, a w * (c w : ℝ) * z ^ (c w - 1) ∂(fairWordLaw n)) z := by
    intro a c z
    have d : HasDerivAt (fun t : ℝ => (2 : ℝ)⁻¹ ^ n * ∑ w : Fin n → Bool,
        a w * t ^ c w)
        ((2 : ℝ)⁻¹ ^ n * ∑ w : Fin n → Bool,
          a w * (c w : ℝ) * z ^ (c w - 1)) z := by
      apply HasDerivAt.const_mul
      exact HasDerivAt.fun_sum (fun w _ => by
        simpa only [mul_assoc] using (hasDerivAt_pow (c w) z).const_mul (a w))
    convert d using 1
    · funext t; exact meanSum _
    · exact meanSum _
  have rawEq : ∀ z : ℝ,
      (∫ w : Fin n → Bool, (startCount k w : ℝ) * z ^ (startCount k w - 1)
        ∂(fairWordLaw n)) = pgfSlope n k z := by
    intro z
    have d := dAverage (fun _ => 1) (fun w => startCount k w) z
    simp only [one_mul] at d
    exact d.unique (stage z).1
  have factorial : (∫ w : Fin n → Bool,
      (startCount k w : ℝ) * ((startCount k w - 1 : ℕ) : ℝ) ∂(fairWordLaw n)) =
      ∑ i : Fin (startPositions n k), runStartMass n k i *
        ∫ w : Fin n → Bool, (outsideCount k i w : ℝ) ∂(fairWordLaw n) := by
    have dl := dAverage (fun w => (startCount k w : ℝ))
      (fun w => startCount k w - 1) 1
    simp only [one_pow, mul_one] at dl
    have fn : (fun z : ℝ => ∫ w : Fin n → Bool,
        (startCount k w : ℝ) * z ^ (startCount k w - 1) ∂(fairWordLaw n)) =
        pgfSlope n k := funext rawEq
    rw [fn] at dl
    have dr : HasDerivAt (pgfSlope n k)
        (∑ i : Fin (startPositions n k), runStartMass n k i *
          ∫ w : Fin n → Bool, (outsideCount k i w : ℝ) ∂(fairWordLaw n)) 1 := by
      unfold pgfSlope
      apply HasDerivAt.fun_sum
      intro i hi
      simpa only [one_mul, one_pow, mul_one] using
        (dAverage (fun _ => 1) (fun w => outsideCount k i w) 1).const_mul
          (runStartMass n k i)
    exact dl.unique dr
  have factorialBound : (∫ w : Fin n → Bool,
      (startCount k w : ℝ) * ((startCount k w - 1 : ℕ) : ℝ) ∂(fairWordLaw n)) ≤ M ^ 2 := by
    rw [factorial]
    calc
      _ ≤ ∑ i : Fin (startPositions n k), runStartMass n k i * M := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        rw [← expectedW]
        apply integral_mono (integrable _) (integrable _)
        intro w
        have partition : outsideCount k i w ≤ startCount k w := by
          have sub : outsideCount k i w =
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin (startPositions n k) => ¬ (i.val ≤ j.val + k ∧ j.val ≤ i.val + k)),
                if RunStart w k j.val then 1 else 0 :=
            (Finset.sum_subtype _ (by simp)
              (fun j : Fin (startPositions n k) => if RunStart w k j.val then 1 else 0)).symm
          rw [sub, startCount]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
        change (outsideCount k i w : ℝ) ≤ (startCount k w : ℝ)
        exact_mod_cast partition
      _ = M ^ 2 := by rw [← Finset.sum_mul]; change M * M = M ^ 2; ring
  let X : (Fin n → Bool) → ℝ := fun w => startCount k w
  have hX : MemLp X 2 (fairWordLaw n) :=
    (memLp_two_iff_integrable_sq (measurable_of_finite X).aestronglyMeasurable).mpr
      (integrable _)
  have varianceBound : variance X (fairWordLaw n) ≤ M := by
    rw [variance_eq_sub hX]
    change (∫ w, X w ^ 2 ∂(fairWordLaw n)) -
      (∫ w, X w ∂(fairWordLaw n)) ^ 2 ≤ M
    have square : ∀ w : Fin n → Bool, X w ^ 2 =
        (startCount k w : ℝ) * ((startCount k w - 1 : ℕ) : ℝ) + X w := by
      intro w
      dsimp [X]
      cases h : startCount k w with
      | zero => norm_num
      | succ a => simp [Nat.cast_add]; ring
    simp_rw [square]
    rw [integral_add (integrable _) (integrable _)]
    change _ + (∫ w, (startCount k w : ℝ) ∂(fairWordLaw n)) -
      (∫ w, (startCount k w : ℝ) ∂(fairWordLaw n)) ^ 2 ≤ M
    rw [expectedW]
    linarith [factorialBound]
  have unionBound : 1 - runPGF n k 0 ≤ M := by
    have point : ∀ w : Fin n → Bool, 1 - (0 : ℝ) ^ startCount k w ≤ (startCount k w : ℝ) := by
      intro w
      cases h : startCount k w with
      | zero => norm_num
      | succ a => simp
    have bound := integral_mono (integrable _) (integrable _) point
    rw [integral_sub (integrable _) (integrable _), integral_const, expectedW] at bound
    simpa only [probReal_univ, smul_eq_mul, one_mul, runPGF] using bound
  have chebyshevBound : runPGF n k 0 ≤ 1 / M := by
    have zeroMeasure : runPGF n k 0 = (fairWordLaw n).real {w | startCount k w = 0} := by
      have eq : (fun w : Fin n → Bool => (0 : ℝ) ^ startCount k w) =
          Set.indicator {w | startCount k w = 0} (fun _ => (1 : ℝ)) := by
        funext w; by_cases h : startCount k w = 0 <;> simp [h, Set.indicator]
      rw [runPGF, eq, integral_indicator (Set.toFinite _).measurableSet]
      simp
    have cheb := meas_ge_le_variance_div_sq hX hM
    have inclusion : {w : Fin n → Bool | startCount k w = 0} ⊆
        {w | M ≤ |X w - (∫ u, X u ∂(fairWordLaw n))|} := by
      intro w hw
      change M ≤ |(startCount k w : ℝ) - (∫ u, (startCount k u : ℝ) ∂(fairWordLaw n))|
      rw [hw, Nat.cast_zero, expectedW, zero_sub, abs_neg, abs_of_pos hM]
    have realCheb : (fairWordLaw n).real
        {w | M ≤ |X w - (∫ u, X u ∂(fairWordLaw n))|} ≤
        variance X (fairWordLaw n) / M ^ 2 := by
      have b := ENNReal.toReal_mono ENNReal.ofReal_ne_top cheb
      simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X _) (sq_nonneg M))] using b
    calc
      _ = _ := zeroMeasure
      _ ≤ _ := measureReal_mono inclusion
      _ ≤ variance X (fairWordLaw n) / M ^ 2 := realCheb
      _ ≤ M / M ^ 2 := div_le_div_of_nonneg_right varianceBound (sq_nonneg M)
      _ = 1 / M := by field_simp
  dsimp [M] at calibrated unionBound chebyshevBound
  rw [origin, meanEq] at calibrated unionBound chebyshevBound
  refine ⟨?_, unionBound, fun _ => chebyshevBound⟩
  simpa only [neg_div, ε] using calibrated

end

end D5.S1.Words.ClosedRunPoisson
