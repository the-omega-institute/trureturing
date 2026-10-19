/- GID: D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim; result=D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result; claim=D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim
   digest: A four-state Glauber annealing run refutes relaxation-time rate order. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation

open scoped BigOperators

/-! Glauber transitions use the Gibbs ratio in Eq. (32) of arXiv:2311.10424v1.
The partial-swap side of (50) is eliminated using Proposition 2: its rate m has
spectral gap m. The gap comparison avoids interpreting a zero denominator as a
finite relaxation time. Characteristic roots retain algebraic multiplicity. -/

def regularNeighborhood {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A] : Prop :=
  1 ≤ n ∧
  (∀ i j, A i j → A j i) ∧
  (∀ i, ¬ A i i) ∧
  (∀ j, (Finset.univ.filter (fun i => A i j)).card = n)

noncomputable def gibbs {N : ℕ}
    (E : Fin N → ℝ) (b : ℝ) : Fin N → ℝ :=
  fun i =>
    Real.exp (-b * E i) /
      ∑ j, Real.exp (-b * E j)

noncomputable def edgeWeight {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (b : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if A i j then
      gibbs E b i /
        ((n : ℝ) * (gibbs E b i + gibbs E b j))
    else
      0

noncomputable def glauber {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (b : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i = j then
      1 - ∑ l, edgeWeight n A E b l j
    else
      edgeWeight n A E b i j

def isSARun {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ) : Prop :=
  (∀ t, D5.S3.TotalVariation.CycleSingleCutMinimax.Probability (A := Fin N) (p t)) ∧
  p 0 = gibbs E (β 0) ∧
  (∀ t,
    p (t + 1) =
      (glauber n A E (β (t + 1))).mulVec (p t))

noncomputable def meanEnergy {N : ℕ}
    (E p : Fin N → ℝ) : ℝ :=
  ∑ i, E i * p i

noncomputable def energyRate {N : ℕ}
    (E : Fin N → ℝ) (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ) (k : ℕ) : ℝ :=
  (meanEnergy E (p (k + 1)) - meanEnergy E (p k)) /
    (meanEnergy E (gibbs E (β (k + 1))) -
      meanEnergy E (p k))

noncomputable def lambda2 {N : ℕ}
    (P : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ((Matrix.charpoly P).roots.sort
    (fun x y : ℝ => y ≤ x)).getD 1 0

def claim : Prop :=
  ∀ (N n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ)
    (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ)
    (k : ℕ) (m : ℝ),
    2 ≤ N →
    regularNeighborhood n A →
    (∀ t, 0 < β t) →
    StrictMono β →
    isSARun n A E β p →
    (glauber n A E (β (k + 1))).charpoly.Splits →
    0 < m →
    m ≤ 1 →
    meanEnergy E (p (k + 1)) ≤ meanEnergy E (p k) →
    meanEnergy E (gibbs E (β k)) ≤ meanEnergy E (p k) →
    meanEnergy E (gibbs E (β (k + 1))) ≤
      meanEnergy E (gibbs E (β k)) →
    meanEnergy E (gibbs E (β (k + 1))) ≠
      meanEnergy E (p k) →
    m ≤ 1 - lambda2 (glauber n A E (β (k + 1))) →
    m ≤ energyRate E β p k

private def adj4 (i j : Fin 4) : Prop :=
  (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val

private instance adj4Decidable : DecidableRel adj4 :=
  fun i j =>
    show Decidable
      ((i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val) from inferInstance

private noncomputable def E4 : Fin 4 → ℝ := ![0, 1, 1, 2]

private noncomputable def q4 (k : ℕ) : ℝ :=
  if k = 0 then 2 else (k : ℝ) + 31

private noncomputable def beta4 (k : ℕ) : ℝ := Real.log (q4 k)

private noncomputable def Pq (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q / (2 * (q + 1)) + q^2 / (2 * (q^2 + 1)),
       q / (2 * (q + 1)), 0, q^2 / (2 * (q^2 + 1));
     1 / (2 * (q + 1)), 1 / 4 + 1 / (2 * (q + 1)), 1 / 4, 0;
     0, 1 / 4, 1 / 4 + q / (2 * (q + 1)), q / (2 * (q + 1));
     1 / (2 * (q^2 + 1)), 0, 1 / (2 * (q + 1)),
       1 / (2 * (q + 1)) + 1 / (2 * (q^2 + 1))]

private noncomputable def run : ℕ → Fin 4 → ℝ :=
  Nat.rec (gibbs E4 (beta4 0))
    (fun k v => (glauber 2 adj4 E4 (beta4 (k + 1))).mulVec v)

private noncomputable def s : ℝ := Real.sqrt ((64 : ℝ) / 545)

private theorem adj4_regular : regularNeighborhood 2 adj4 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i j h
    exact h.elim Or.inr Or.inl
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

private theorem q4_spec : (∀ k, 1 < q4 k) ∧ StrictMono q4 := by
  constructor
  · intro k
    rw [q4.eq_1]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  · intro i j hij
    have hj : j ≠ 0 := by omega
    by_cases hi : i = 0
    · subst i
      simp only [q4.eq_1, ite_true, if_neg hj]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    · simp only [q4.eq_1, if_neg hi, if_neg hj]
      have hc : (i : ℝ) < j := Nat.cast_lt.mpr hij
      linarith

private theorem beta4_spec : (∀ k, 0 < beta4 k) ∧ StrictMono beta4 := by
  refine ⟨fun k => Real.log_pos (q4_spec.1 k), ?_⟩
  intro i j hij
  exact Real.log_lt_log (lt_trans zero_lt_one (q4_spec.1 i)) (q4_spec.2 hij)

private theorem weights_log (q : ℝ) (hq : 0 < q) :
    (fun i : Fin 4 => Real.exp (-Real.log q * E4 i)) =
      ![1, q⁻¹, q⁻¹, (q⁻¹)^2] := by
  have h1 : Real.exp (-Real.log q) = q⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hq]
  have h2 : Real.exp (-Real.log q * 2) = (q⁻¹)^2 := by
    rw [mul_two, Real.exp_add, h1, pow_two]
  rw [E4.eq_1]
  funext i
  fin_cases i <;> dsimp
  · simp
  · simpa only [mul_one] using h1
  · simpa only [mul_one] using h1
  · exact h2

private theorem gibbs_log (q : ℝ) (hq : 0 < q) :
    gibbs E4 (Real.log q) =
      ![q^2 / (q + 1)^2, q / (q + 1)^2, q / (q + 1)^2, 1 / (q + 1)^2] := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq1 : q + 1 ≠ 0 := by positivity
  have hw := weights_log q hq
  change (fun i => (fun j : Fin 4 => Real.exp (-Real.log q * E4 j)) i /
    ∑ j, (fun l : Fin 4 => Real.exp (-Real.log q * E4 l)) j) = _
  rw [hw]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_succ] <;> field_simp <;> ring

private theorem glauber_log (q : ℝ) (hq : 0 < q) :
    glauber 2 adj4 E4 (Real.log q) = Pq q := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq1 : q + 1 ≠ 0 := by positivity
  have hq2 : q^2 + 1 ≠ 0 := by positivity
  rw [glauber.eq_1, edgeWeight.eq_1, Pq.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gibbs_log q hq, adj4.eq_1, Fin.sum_univ_succ] <;>
    field_simp <;> ring

private theorem Pq_stochastic (q : ℝ) (hq : 0 < q) :
    (∀ i j, 0 ≤ Pq q i j) ∧ (∀ j, (∑ i, Pq q i j) = 1) := by
  have hq1 : q + 1 ≠ 0 := by positivity
  have hq2 : q^2 + 1 ≠ 0 := by positivity
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Pq.eq_1] <;> positivity
  · intro j
    fin_cases j <;> norm_num [Pq.eq_1, Fin.sum_univ_succ] <;> field_simp <;> ring

theorem probability_mulVec {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    {p : Fin N → ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hcol : ∀ j, (∑ i, P i j) = 1)
    (hp : D5.S3.TotalVariation.CycleSingleCutMinimax.Probability (A := Fin N) p) :
    D5.S3.TotalVariation.CycleSingleCutMinimax.Probability (A := Fin N) (P.mulVec p) := by
  have hM : P ∈ Matrix.colStochastic ℝ (Fin N) :=
    Matrix.mem_colStochastic_iff_sum.mpr ⟨hP, hcol⟩
  exact ⟨Matrix.nonneg_mulVec_of_mem_colStochastic hM hp.1,
    (Matrix.sum_mulVec_of_mem_colStochastic hM).trans hp.2⟩

private theorem run_zero : run 0 = ![4 / 9, 2 / 9, 2 / 9, 1 / 9] := by
  change gibbs E4 (Real.log 2) = _
  rw [gibbs_log 2 (by norm_num)]
  norm_num

private theorem run_isSA : isSARun 2 adj4 E4 beta4 run := by
  refine ⟨?_, rfl, fun _ => rfl⟩
  intro k
  induction k with
  | zero =>
    rw [run_zero]
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]
  | succ k ih =>
    change D5.S3.TotalVariation.CycleSingleCutMinimax.Probability (A := Fin 4)
      ((glauber 2 adj4 E4 (Real.log (q4 (k + 1)))).mulVec (run k))
    have hq : 0 < q4 (k + 1) := lt_trans zero_lt_one (q4_spec.1 (k + 1))
    rw [glauber_log _ hq]
    exact probability_mulVec (Pq_stochastic _ hq).1 (Pq_stochastic _ hq).2 ih

private theorem run_one : run 1 = ![4064 / 6765, 4 / 33, 3 / 11, 12 / 2255] := by
  change (glauber 2 adj4 E4 (beta4 1)).mulVec (run 0) = _
  have hb : beta4 1 = Real.log 32 := by norm_num [beta4.eq_1, q4.eq_1]
  rw [hb, glauber_log 32 (by norm_num), run_zero]
  ext i
  fin_cases i <;> norm_num [Pq.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem energy_data :
    meanEnergy E4 (run 1) = 2737 / 6765 ∧
    meanEnergy E4 (run 2) = 17612741 / 50142180 ∧
    meanEnergy E4 (gibbs E4 (beta4 1)) = 2 / 33 ∧
    meanEnergy E4 (gibbs E4 (beta4 2)) = 1 / 17 := by
  have hrun2 : run 2 = (Pq 33).mulVec (run 1) := by
    change (glauber 2 adj4 E4 (beta4 2)).mulVec (run 1) = _
    have hb : beta4 2 = Real.log 33 := by norm_num [beta4.eq_1, q4.eq_1]
    rw [hb, glauber_log 33 (by norm_num)]
  have hb1 : beta4 1 = Real.log 32 := by norm_num [beta4.eq_1, q4.eq_1]
  have hb2 : beta4 2 = Real.log 33 := by norm_num [beta4.eq_1, q4.eq_1]
  rw [hrun2, run_one, hb1, hb2, gibbs_log 32 (by norm_num), gibbs_log 33 (by norm_num)]
  norm_num [meanEnergy.eq_1, E4.eq_1, Pq.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem rate_eq : energyRate E4 beta4 run 1 = 2673903 / 17337104 := by
  obtain ⟨h1, h2, _, hg2⟩ := energy_data
  rw [energyRate.eq_1]
  norm_num [h1, h2, hg2]

private theorem step_conditions :
    meanEnergy E4 (run 2) ≤ meanEnergy E4 (run 1) ∧
    meanEnergy E4 (gibbs E4 (beta4 1)) ≤ meanEnergy E4 (run 1) ∧
    meanEnergy E4 (gibbs E4 (beta4 2)) ≤ meanEnergy E4 (gibbs E4 (beta4 1)) ∧
    meanEnergy E4 (gibbs E4 (beta4 2)) ≠ meanEnergy E4 (run 1) ∧
    energyRate E4 beta4 run 1 < 5 / 32 := by
  obtain ⟨h1, h2, hg1, hg2⟩ := energy_data
  rw [h1, h2, hg1, hg2, rate_eq]
  norm_num

set_option maxRecDepth 4096 in
private theorem P33_charpoly :
    (Pq 33).charpoly =
      (Polynomial.X : Polynomial ℝ) * (Polynomial.X - 1) *
        (Polynomial.X^2 - Polynomial.X + Polynomial.C ((289 : ℝ) / 2180)) := by
  apply Polynomial.funext
  intro z
  have hsucc : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  have hcast : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [Pq.eq_1, Matrix.scalar, Matrix.diagonal, Matrix.sub_apply,
    Fin.succAbove, hsucc, hcast, Fin.lt_def, Fin.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem s_properties : 0 ≤ s ∧ s^2 = (64 : ℝ) / 545 ∧ s < 11 / 32 := by
  refine ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by norm_num), ?_⟩
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 11 / 32)).mpr (by norm_num)

private theorem P33_linear_factors :
    (Pq 33).charpoly =
      ((([1, (1 / 2 : ℝ) + s, (1 / 2 : ℝ) - s, 0] : List ℝ) : Multiset ℝ).map
        (fun x => Polynomial.X - Polynomial.C x)).prod := by
  have hquad :
      (Polynomial.X^2 - Polynomial.X + Polynomial.C ((289 : ℝ) / 2180)) =
        (Polynomial.X - Polynomial.C ((1 / 2 : ℝ) + s)) *
          (Polynomial.X - Polynomial.C ((1 / 2 : ℝ) - s)) := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
    nlinarith [s_properties.2.1]
  rw [P33_charpoly, hquad]
  norm_num [Multiset.map_coe, Multiset.prod_coe]
  ring

private theorem P33_roots_sorted :
    (Pq 33).charpoly.Splits ∧
    ((Pq 33).charpoly.roots.sort (fun x y : ℝ => y ≤ x)) =
      [1, (1 / 2 : ℝ) + s, (1 / 2 : ℝ) - s, 0] := by
  rw [P33_linear_factors]
  constructor
  · apply Polynomial.Splits.multisetProd
    intro f hf
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.Splits.X_sub_C a
  · rw [Polynomial.roots_multiset_prod_X_sub_C, Multiset.coe_sort]
    apply List.mergeSort_eq_self
    obtain ⟨hs0, _, hs1⟩ := s_properties
    refine List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _)))
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> linarith
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> linarith
    · intro a ha
      have : a = 0 := List.mem_singleton.mp ha
      subst a
      linarith

private theorem P33_spectrum :
    (Pq 33).charpoly.Splits ∧ lambda2 (Pq 33) < 27 / 32 := by
  refine ⟨P33_roots_sorted.1, ?_⟩
  unfold lambda2
  rw [P33_roots_sorted.2]
  change (1 / 2 : ℝ) + s < 27 / 32
  linarith [s_properties.2.2]

theorem result : ¬ claim := by
  intro hClaim
  obtain ⟨hβpos, hβmono⟩ := beta4_spec
  obtain ⟨hdec, habove, hcool, hden, hrate⟩ := step_conditions
  have hP : glauber 2 adj4 E4 (beta4 (1 + 1)) = Pq 33 := by
    have hb : beta4 (1 + 1) = Real.log 33 := by norm_num [beta4.eq_1, q4.eq_1]
    rw [hb]
    exact glauber_log 33 (by norm_num)
  obtain ⟨hsplit, hSpec⟩ := P33_spectrum
  have hsplit' : (glauber 2 adj4 E4 (beta4 (1 + 1))).charpoly.Splits := by
    rw [hP]
    exact hsplit
  have hgap : (5 / 32 : ℝ) ≤ 1 - lambda2 (glauber 2 adj4 E4 (beta4 (1 + 1))) := by
    rw [hP]
    linarith
  have hμ := hClaim 4 2 adj4 E4 beta4 run 1 (5 / 32)
    (by norm_num) adj4_regular hβpos hβmono run_isSA hsplit'
    (by norm_num) (by norm_num) hdec habove hcool hden hgap
  exact (not_le_of_gt hrate) hμ

end D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
