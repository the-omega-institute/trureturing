/- GID: D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/MarkovMpembaTripletRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.claim; result=D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result; claim=D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.claim
   digest: Four reversible levels refute the finite-temperature Mpemba triplet conjecture. -/

import D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
import D5.S3.PrimeGaps.ShortTranslateClosure

set_option autoImplicit false
set_option maxRecDepth 3000
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation

open scoped BigOperators

noncomputable def generator {N : ℕ} (a : Fin N → Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then -(∑ k, if k = j then 0 else a k j) else a i j

def DetailedBalance {N : ℕ} (E : Fin N → ℝ) (βb : ℝ)
    (a : Fin N → Fin N → ℝ) : Prop :=
  ∀ j k, j ≠ k → a j k = a k j * Real.exp (-(βb * (E j - E k)))

def TripletCondition {N : ℕ} (E : Fin N → ℝ) (βb : ℝ)
    (a : Fin N → Fin N → ℝ) (i j k : Fin N) : Prop :=
  let x := Real.exp (-(βb * (E j - E i)))
  let y := Real.exp (-(βb * (E k - E j)))
  let κ := (a i k + a j k) / (a i j * (1 + x))
  (1 ≤ κ ∧ a i k * (1 + x * y / 2) - a j k * (1 + y / 2) >
    a i j * (1 - x)) ∨ (κ ≤ 1 ∧ a i k * x > a j k)

def IsSlowMode {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (lam : ℝ) (ℓ : Fin N → ℝ) : Prop :=
  lam < 0 ∧ ℓ ≠ 0 ∧ Matrix.vecMul ℓ M = lam • ℓ ∧
  (∀ (μ : ℝ) (v : Fin N → ℝ), v ≠ 0 → Matrix.mulVec M v = μ • v →
    μ = 0 ∨ μ ≤ lam) ∧
  (∀ v, Matrix.vecMul v M = lam • v → ∃ c : ℝ, v = c • ℓ)

def MpembaEffect {N : ℕ} (E : Fin N → ℝ) (βb : ℝ) (ℓ : Fin N → ℝ) : Prop :=
  ∃ β₁ β₂ : ℝ, ((0 < β₁ ∧ β₁ < β₂ ∧ β₂ < βb) ∨ (βb < β₂ ∧ β₂ < β₁)) ∧
    |dotProduct ℓ (GlauberRelaxationOrderRefutation.gibbs E β₁)| <
      |dotProduct ℓ (GlauberRelaxationOrderRefutation.gibbs E β₂)|

def claim : Prop :=
  ∀ (N : ℕ) (E : Fin N → ℝ) (βb : ℝ) (a : Fin N → Fin N → ℝ),
    3 ≤ N → StrictMono E → 0 < βb → (∀ i j, i ≠ j → 0 < a i j) →
    DetailedBalance E βb a →
    (∀ i j k : Fin N, i < j → j < k → ¬ TripletCondition E βb a i j k) →
    ∀ lam ℓ, IsSlowMode (generator a) lam ℓ → ¬ MpembaEffect E βb ℓ

private noncomputable def mean (r : ℝ) : ℝ := 2 * (125 + 1024 * r) / (15 * (273 + 256 * r))
private noncomputable def weights (r : ℝ) : Fin 4 → ℝ := ![1, 1/16, 1/256, r]
private noncomputable def g : Fin 4 → ℝ := ![0, 1, 2/3, 8/15]
private noncomputable def f (r : ℝ) : Fin 4 → ℝ := fun i => g i - mean r
private noncomputable def rates (r : ℝ) : Fin 4 → Fin 4 → ℝ :=
  let A := 47/48 - mean r - 112*r/25
  let B := 3/2 - 3*mean r/2 - 128*r/25
  let C := 31/20 - 15*mean r/8
  !![0, A, B, C; A/16, 0, 1, 3/5; B/256, 1/16, 0, 1/10;
     C*r, 48*r/5, 128*r/5, 0]
private def levels : Fin 4 → ℕ := ![0, 1, 2, 64]
private noncomputable def energy : Fin 4 → ℝ := fun i => (levels i : ℝ) * Real.log 16
private noncomputable def small : ℝ := (1/16)^64
private noncomputable def k1 : Fin 4 → ℝ := ![1, 2, -3, 0]
private noncomputable def k2 : Fin 4 → ℝ := ![7, 8, 0, -15]
private noncomputable def block (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-201261056*r^2 - 231756288*r - 25704025)/(38400*(256*r+273)),
     (458752*r^2 + 3703296*r + 3359825)/(38400*(256*r+273));
     r*(146048*r+153329)/(150*(256*r+273)),
     (-206464*r^2 - 285097*r - 87450)/(150*(256*r+273))]

private theorem mean_bounds (r : ℝ) (hr : 0 < r) (hb : r ≤ 1/4096) :
    3/50 < mean r ∧ mean r < 1/16 := by
  unfold mean
  constructor
  · apply (lt_div_iff₀ (by positivity)).2
    linarith
  · apply (div_lt_iff₀ (by positivity)).2
    linarith

private theorem small_bounds : 0 < small ∧ small ≤ 1/4096 := by
  refine ⟨by unfold small; positivity, ?_⟩
  calc
    small ≤ (1/16 : ℝ)^3 := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 3 ≤ 64)
    _ = 1/4096 := by norm_num

private theorem rates_positive (r : ℝ) (hr : 0 < r) (hb : r ≤ 1/4096) :
    ∀ i j, i ≠ j → 0 < rates r i j := by
  obtain ⟨hlo, hhi⟩ := mean_bounds r hr hb
  intro i j hij
  fin_cases i <;> fin_cases j <;> try { exact (hij rfl).elim }
  all_goals norm_num [rates.eq_1]
  all_goals nlinarith

private theorem balance_weights (r : ℝ) :
    ∀ i j, rates r i j * weights r j = rates r j i * weights r i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [rates.eq_1, weights.eq_1] <;> ring

set_option maxHeartbeats 1000000 in
-- The four-state eigenvector identities expand and normalize rational matrix entries.
private theorem eigen_identities (r : ℝ) (hr : 0 < r) :
    Matrix.vecMul (fun _ : Fin 4 => (1 : ℝ)) (generator (rates r)) = 0 ∧
    Matrix.vecMul (f r) (generator (rates r)) = (-1 : ℝ) • f r ∧
      Matrix.mulVec (generator (rates r)) (weights r) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, weights.eq_1, f.eq_1, g.eq_1, mean.eq_1, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ofNat, Fin.succ, Fin.mk.injEq] <;>
    field_simp <;> ring

set_option maxHeartbeats 1000000 in
-- Both basis-vector actions require rational normalization after clearing denominators.
private theorem block_action (r : ℝ) (hr : 0 < r) :
    Matrix.mulVec (generator (rates r)) k1 = (block r 0 0) • k1 + (block r 1 0) • k2 ∧
    Matrix.mulVec (generator (rates r)) k2 = (block r 0 1) • k1 + (block r 1 1) • k2 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, k1.eq_1, k2.eq_1, mean.eq_1, block.eq_1, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ofNat, Fin.succ, Fin.mk.injEq] <;>
    field_simp <;> ring

private noncomputable def q (r x : ℝ) : ℝ :=
  x^2 - (block r 0 0 + block r 1 1)*x +
    block r 0 0 * block r 1 1 - block r 0 1 * block r 1 0

private theorem block_bounds (r : ℝ) (hr : 0 < r) :
    block r 0 0 + block r 1 1 < -4 ∧ 0 < q r (-2) ∧ 0 < q r (-1) := by
  have ht : block r 0 0 + block r 1 1 =
      (-50823168*r^2-60948224*r-9618245)/(7680*(256*r+273)) := by
    simp only [block.eq_1]
    norm_num
    field_simp
    ring
  have hq2 : q r (-2) =
      (6914360475648*r^4+14183493009408*r^3+7535913889792*r^2+
        274800737600*r+4382303125)/(960000*(256*r+273)^2) := by
    simp only [q.eq_1, block.eq_1]
    norm_num
    field_simp
    ring
  have hq1 : q r (-1) =
      (274752*r+59225)*(12582912*r^3+26058752*r^2+14458848*r+995875)/
        (480000*(256*r+273)^2) := by
    simp only [q.eq_1, block.eq_1]
    norm_num
    field_simp
    ring
  rw [ht, hq2, hq1]
  refine ⟨?_, by positivity, by positivity⟩
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith [sq_nonneg r]

private theorem root_bound (r x : ℝ) (hr : 0 < r) (hx : q r x = 0) : x < -2 := by
  obtain ⟨ht, hq2, _⟩ := block_bounds r hr
  by_contra hn
  have hp : 0 ≤ (x+2)*(x-2-(block r 0 0+block r 1 1)) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [q.eq_1] at hx hq2
  nlinarith

private theorem kernel_coordinates (r : ℝ) (v : Fin 4 → ℝ)
    (hs : dotProduct (fun _ : Fin 4 => (1 : ℝ)) v = 0)
    (hf : dotProduct (f r) v = 0) :
    v = (-v 2/3) • k1 + (-v 3/15) • k2 := by
  simp only [dotProduct, Fin.sum_univ_four, one_mul] at hs
  norm_num [dotProduct, Fin.sum_univ_four, f.eq_1, g.eq_1,
    Matrix.cons_val_two, Matrix.cons_val_three] at hf
  ext i
  fin_cases i <;> norm_num [k1.eq_1, k2.eq_1, Matrix.cons_val_two, Matrix.cons_val_three]
  · linear_combination hs - hf - mean r*hs
  · linear_combination hf + mean r*hs
  all_goals rfl

private theorem real_spectrum (r : ℝ) (hr : 0 < r) (x : ℝ) (v : Fin 4 → ℝ)
    (hv : v ≠ 0) (he : Matrix.mulVec (generator (rates r)) v = x • v) :
    x = 0 ∨ x ≤ -1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hm : x = -1
  · exact Or.inr hm.le
  obtain ⟨h1, hf, _⟩ := eigen_identities r hr
  have hs : dotProduct (fun _ : Fin 4 => (1 : ℝ)) v = 0 := by
    have h := congrArg (dotProduct (fun _ : Fin 4 => (1 : ℝ))) he
    rw [Matrix.dotProduct_mulVec, h1, dotProduct_smul] at h
    simp only [zero_dotProduct, smul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hx
  have hfv : dotProduct (f r) v = 0 := by
    have h := congrArg (dotProduct (f r)) he
    rw [Matrix.dotProduct_mulVec, hf, smul_dotProduct, dotProduct_smul] at h
    simp only [smul_eq_mul] at h
    have hn : x+1 ≠ 0 := by intro hh; apply hm; linarith
    apply (mul_eq_zero.mp (show (x+1)*dotProduct (f r) v = 0 by linarith)).resolve_left hn
  have hc := kernel_coordinates r v hs hfv
  have hn : (![(-v 2/3), (-v 3/15)] : Fin 2 → ℝ) ≠ 0 := by
    intro hh
    have h2 := congrFun hh 0
    have h3 := congrFun hh 1
    norm_num at h2 h3
    apply hv
    rw [hc]
    have hv2 : v 2 = 0 := by linarith
    have hv3 : v 3 = 0 := by linarith
    simp only [hv2, hv3, neg_zero, zero_div, zero_smul, add_zero]
  obtain ⟨hk1, hk2⟩ := block_action r hr
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hk1, hk2] at he
  have he2 := congrFun he 2
  have he3 := congrFun he 3
  norm_num [k1.eq_1, k2.eq_1, Matrix.cons_val_two, Matrix.cons_val_three] at he2 he3
  have hz : Matrix.mulVec (block r - x • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      ![-v 2/3, -v 3/15] = 0 := by
    ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply] <;> linarith
  have hd := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hn, hz⟩
  have hq : q r x = 0 := by
    rw [Matrix.det_fin_two] at hd
    norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at hd
    simp only [q.eq_1]
    nlinarith [hd]
  exact Or.inr (le_trans (root_bound r x hr hq).le (by norm_num))

private theorem simple_mode (r : ℝ) (hr : 0 < r) (hb : r ≤ 1/4096)
    (l : Fin 4 → ℝ) (he : Matrix.vecMul l (generator (rates r)) = (-1 : ℝ) • l) :
    ∃ c : ℝ, l = c • f r := by
  obtain ⟨_, hfe, hwe⟩ := eigen_identities r hr
  obtain ⟨hk1, hk2⟩ := block_action r hr
  have hw : dotProduct l (weights r) = 0 := by
    have h := congrArg (fun v => dotProduct v (weights r)) he
    rw [← Matrix.dotProduct_mulVec, hwe] at h
    simp only [dotProduct_zero, smul_dotProduct, smul_eq_mul] at h
    linarith
  have hfw : dotProduct (f r) (weights r) = 0 := by
    have h := congrArg (fun v => dotProduct v (weights r)) hfe
    rw [← Matrix.dotProduct_mulVec, hwe] at h
    simp only [dotProduct_zero, smul_dotProduct, smul_eq_mul] at h
    linarith
  have ha := congrArg (dotProduct l) hk1
  have hbpair := congrArg (dotProduct l) hk2
  rw [Matrix.dotProduct_mulVec, he, smul_dotProduct, dotProduct_add,
    dotProduct_smul, dotProduct_smul] at ha hbpair
  simp only [smul_eq_mul, dotProduct] at ha hbpair
  have hz : Matrix.vecMul ![dotProduct l k1, dotProduct l k2]
      (block r + (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
    ext i
    fin_cases i <;> norm_num [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.one_apply] <;> linarith
  have hd : (block r + (1 : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
    have hq := (block_bounds r hr).2.2
    have hh : (block r + (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = q r (-1) := by
      rw [Matrix.det_fin_two]
      norm_num [Matrix.add_apply, Matrix.one_apply, q.eq_1]
      ring
    rw [hh]
    exact ne_of_gt hq
  have hpair : (![dotProduct l k1, dotProduct l k2] : Fin 2 → ℝ) = 0 := by
    by_contra hn
    exact hd (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hn, hz⟩)
  have hl1 : dotProduct l k1 = 0 := congrFun hpair 0
  have hl2 : dotProduct l k2 = 0 := congrFun hpair 1
  have hf1 : dotProduct (f r) k1 = 0 := by
    norm_num [dotProduct, Fin.sum_univ_succ, f.eq_1, g.eq_1, k1.eq_1]
    ring
  have hf2 : dotProduct (f r) k2 = 0 := by
    norm_num [dotProduct, Fin.sum_univ_succ, f.eq_1, g.eq_1, k2.eq_1]
    ring
  have hf3 : f r 3 ≠ 0 := by
    have hmu := (mean_bounds r hr hb).2
    change 8/15-mean r ≠ 0
    linarith
  let c := l 3 / f r 3
  let u := l - c • f r
  have hu3 : u 3 = 0 := by
    change l 3 - (l 3 / f r 3)*f r 3 = 0
    rw [div_mul_cancel₀ _ hf3, sub_self]
  have huw : dotProduct u (weights r) = 0 := by
    simp only [u, sub_dotProduct, smul_dotProduct, hw, hfw, smul_eq_mul, mul_zero, sub_self]
  have hu1 : dotProduct u k1 = 0 := by
    simp only [u, sub_dotProduct, smul_dotProduct, hl1, hf1, smul_eq_mul, mul_zero, sub_self]
  have hu2 : dotProduct u k2 = 0 := by
    simp only [u, sub_dotProduct, smul_dotProduct, hl2, hf2, smul_eq_mul, mul_zero, sub_self]
  simp only [dotProduct, Fin.sum_univ_four, weights.eq_1, k1.eq_1, k2.eq_1] at huw hu1 hu2
  change u 0*1+u 1*(1/16)+u 2*(1/256)+u 3*r = 0 at huw
  change u 0*1+u 1*2+u 2*(-3)+u 3*0 = 0 at hu1
  change u 0*7+u 1*8+u 2*0+u 3*(-15) = 0 at hu2
  rw [hu3] at huw hu1 hu2
  have hu0 : u 0 = 0 := by linarith
  have huone : u 1 = 0 := by linarith
  have hutwo : u 2 = 0 := by linarith
  have hu : u = 0 := by
    ext i
    fin_cases i
    · exact hu0
    · exact huone
    · exact hutwo
    · exact hu3
  exact ⟨c, sub_eq_zero.mp hu⟩

private theorem slow_mode : IsSlowMode (generator (rates small)) (-1) (f small) := by
  refine ⟨by norm_num, ?_, (eigen_identities small small_bounds.1).2.1, ?_, ?_⟩
  · intro hz
    have h0 := congrFun hz 0
    have hm := (mean_bounds small small_bounds.1 small_bounds.2).1
    norm_num [f.eq_1, g.eq_1] at h0
    linarith
  · exact real_spectrum small small_bounds.1
  · exact simple_mode small small_bounds.1 small_bounds.2

private theorem bath_weights (i : Fin 4) : Real.exp (-energy i) = weights small i := by
  have he := LongGapsBetweenPrimes.exp_neg_nat_mul_log (x := 16) (by norm_num) (levels i)
  have hw : weights small i = (1/16 : ℝ)^(levels i) := by
    fin_cases i <;> norm_num only [weights.eq_1, levels.eq_1, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.cons_val_zero', small.eq_1, pow_zero, pow_one, one_div_pow]
  rw [hw, one_div_pow]
  convert he using 1
  simp only [energy.eq_1, neg_mul]

private theorem bath_ratio (i j : Fin 4) :
    Real.exp (-(1*(energy i-energy j))) = weights small i / weights small j := by
  rw [show -(1*(energy i-energy j)) = -energy i - (-energy j) by ring,
    Real.exp_sub, bath_weights, bath_weights]

private theorem reversible : DetailedBalance energy 1 (rates small) := by
  intro i j hij
  rw [bath_ratio, ← mul_div_assoc]
  apply (eq_div_iff (show weights small j ≠ 0 by
    have hr := small_bounds.1
    fin_cases j <;> norm_num [weights.eq_1]; exact ne_of_gt hr)).2
  exact balance_weights small i j

private theorem increasing_energy : StrictMono energy := by
  have hL : 0 < Real.log 16 := Real.log_pos (by norm_num)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    norm_num [energy.eq_1, levels.eq_1] <;> linarith

private theorem triplet_margins (r : ℝ) (hr : 0 < r) (hb : r ≤ 1/4096) :
    ∀ i j k : Fin 4, i < j → j < k →
    rates r i k * (1 + (weights r j / weights r i)*(weights r k / weights r j)/2) -
      rates r j k * (1 + (weights r k / weights r j)/2) ≤
      rates r i j * (1 - weights r j / weights r i) ∧
    rates r i k * (weights r j / weights r i) ≤ rates r j k := by
  obtain ⟨hlo, hhi⟩ := mean_bounds r hr hb
  intro i j k hij hjk
  change i.val < j.val at hij
  change j.val < k.val at hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try omega
  all_goals constructor <;> norm_num [rates.eq_1, weights.eq_1] <;> nlinarith

private theorem no_triplets :
    ∀ i j k : Fin 4, i < j → j < k → ¬ TripletCondition energy 1 (rates small) i j k := by
  intro i j k hij hjk
  obtain ⟨hfirst, hsecond⟩ := triplet_margins small small_bounds.1 small_bounds.2 i j k hij hjk
  simp only [TripletCondition.eq_1, bath_ratio]
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith

private noncomputable def beta (x : ℝ) : ℝ := Real.log x⁻¹ / Real.log 16
private noncomputable def overlap (x : ℝ) : ℝ :=
  (x+(2/3)*x^2+(8/15)*x^64)/(1+x+x^2+x^64)

private theorem gibbs_evaluation (x : ℝ) (hx : 0 < x) :
    dotProduct (f small) (GlauberRelaxationOrderRefutation.gibbs energy (beta x)) =
      overlap x - mean small := by
  have he (i : Fin 4) : Real.exp (-(beta x)*energy i) = x^(levels i) := by
    have ht : -(beta x)*energy i = (levels i : ℝ)*Real.log x := by
      simp only [beta.eq_1, energy.eq_1, Real.log_inv]
      field_simp (disch := positivity)
    rw [ht, Real.exp_nat_mul, Real.exp_log hx]
  simp only [GlauberRelaxationOrderRefutation.gibbs.eq_1, dotProduct, Fin.sum_univ_four]
  rw [he 0, he 1, he 2, he 3]
  norm_num [f.eq_1, g.eq_1, levels.eq_1, Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [overlap.eq_1]
  field_simp (disch := positivity)
  ring

private theorem temperature_order :
    0 < beta (1023/1024) ∧ beta (1023/1024) < beta (127/128) ∧ beta (127/128) < 1 := by
  have hL : 0 < Real.log 16 := Real.log_pos (by norm_num)
  simp only [beta.eq_1]
  norm_num
  refine ⟨div_pos (Real.log_pos (by norm_num)) hL, ?_, ?_⟩
  · exact (div_lt_div_iff_of_pos_right hL).2 (Real.log_lt_log (by norm_num) (by norm_num))
  · apply (div_lt_one hL).2
    exact Real.log_lt_log (by norm_num) (by norm_num)

private theorem overlap_comparisons :
    1/16 < overlap (1023/1024) ∧ overlap (1023/1024) < overlap (127/128) := by
  constructor <;> norm_num [overlap.eq_1]

private theorem effect : MpembaEffect energy 1 (f small) := by
  obtain ⟨hb1, h12, hb2⟩ := temperature_order
  obtain ⟨hmlo, hmhi⟩ := mean_bounds small small_bounds.1 small_bounds.2
  obtain ⟨hlo, hlt⟩ := overlap_comparisons
  refine ⟨beta (1023/1024), beta (127/128), Or.inl ⟨hb1, h12, hb2⟩, ?_⟩
  rw [gibbs_evaluation _ (by norm_num), gibbs_evaluation _ (by norm_num),
    abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith


theorem result : ¬ claim := by
  intro h
  exact (h 4 energy 1 (rates small) (by norm_num) increasing_energy (by norm_num)
    (rates_positive small small_bounds.1 small_bounds.2) reversible no_triplets
    (-1) (f small) slow_mode) effect

end D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation
