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

noncomputable def gibbs {N : ℕ} (E : Fin N → ℝ) (β : ℝ) : Fin N → ℝ :=
  GlauberRelaxationOrderRefutation.gibbs E β

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
    |dotProduct ℓ (gibbs E β₁)| < |dotProduct ℓ (gibbs E β₂)|

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
private noncomputable def M (r : ℝ) := generator (rates r)
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
private theorem eigen_identities (r : ℝ) (hr : 0 < r) :
    Matrix.vecMul (fun _ : Fin 4 => (1 : ℝ)) (M r) = 0 ∧
    Matrix.vecMul (f r) (M r) = (-1 : ℝ) • f r ∧ Matrix.mulVec (M r) (weights r) = 0 := by
  have hd : 273 + 256*r ≠ 0 := ne_of_gt (by positivity)
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp only [M.eq_1, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, weights.eq_1, f.eq_1, g.eq_1, mean.eq_1, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ofNat, Fin.succ, Fin.mk.injEq] <;>
    field_simp <;> ring

set_option maxHeartbeats 1000000 in
private theorem block_action (r : ℝ) (hr : 0 < r) :
    Matrix.mulVec (M r) k1 = (block r 0 0) • k1 + (block r 1 0) • k2 ∧
    Matrix.mulVec (M r) k2 = (block r 0 1) • k1 + (block r 1 1) • k2 := by
  have hd : 273 + 256*r ≠ 0 := ne_of_gt (by positivity)
  constructor <;> ext i <;> fin_cases i <;>
    simp only [M.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, k1.eq_1, k2.eq_1, mean.eq_1, block.eq_1, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ofNat, Fin.succ, Fin.mk.injEq] <;>
    field_simp <;> ring

private noncomputable def q (r x : ℝ) : ℝ :=
  x^2 - (block r 0 0 + block r 1 1)*x +
    block r 0 0 * block r 1 1 - block r 0 1 * block r 1 0

private theorem block_bounds (r : ℝ) (hr : 0 < r) :
    block r 0 0 + block r 1 1 < -4 ∧ 0 < q r (-2) ∧ 0 < q r (-1) := by
  have hd : 256*r+273 ≠ 0 := ne_of_gt (by positivity)
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
    (hv : v ≠ 0) (he : Matrix.mulVec (M r) v = x • v) : x = 0 ∨ x ≤ -1 := by
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

end D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation
