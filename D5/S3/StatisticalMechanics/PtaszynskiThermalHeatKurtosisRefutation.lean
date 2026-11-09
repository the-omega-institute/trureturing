/- GID: D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.claim; result=D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.result; claim=D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.claim
   digest: A six-state thermal Markov heat current refutes nonnegative scaled kurtosis. -/

/-
Public theorem result:
  proof_shape: bind-only (finite determinant arithmetic, iterated differentiation and normalization)
  escape_witness: none
  admission_basis: open-problem-resolution (#22747; Refuted)
  Direct frozen dependencies:
    D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.generator
    statement_id: sha256:a3f9ba19cf693b44ad43cdaf2b8f9971804a657bba8226aee550605bbc25632c
  The generator occurs through matrix8_eq, det8 and result; other private
  theorem closures have no frozen D5 dependencies.
All private theorems are bind-only consumed helpers:
  det_M8 -> det8; beta8_pos, q8_nonneg, q8_thermal -> result;
  matrix8_eq -> det8; det8 -> result; jetPow_eq -> polynomial_jet;
  polynomial_jet, polyJet_certificate -> implicit_cumulants;
  implicit_cumulants, rational_sign_certificate -> result.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The corrected directed-rate and paired-support interpretation is specified in
#22747, "Convention correction (before probe round 2)".
The claim writes iteratedDeriv m χ 0 directly; this is the source's cumulant
expression. The forwarding names cumulant and generator are omitted, and the
proofs use iteratedDeriv directly. The rateMatrix construction is omitted:
the heat tilt keeps the diagonal sum, while matrix8_eq uses the frozen
MarkovMpembaTripletRefutation.generator through its diagonal correspondence.
The greatest-real-root condition is written out inside IsSourceSCGF.
No independent SCGF existence or Perron-Frobenius identification is asserted.
-/

import D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation

set_option autoImplicit false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false

namespace D5.S3.StatisticalMechanics.PtaszynskiThermalHeatKurtosisRefutation

open scoped BigOperators Matrix

/-
  `q α i j` is the bath-resolved rate for the directed transition `i → j`.
  Thus a matrix entry in row `i`, column `j` is the transition `j → i`, as
  in the source paper.  The diagonal uses the rates leaving the column state.
-/
def totalRate {N L : ℕ} (q : Fin L → Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ := ∑ α, q α i j

/-
  The source writes its local detailed-balance law for `k_ij`, the rate
  `j → i`.  In the directed-rate notation above this is
  q(i → j) / q(j → i) = exp (β (E i - E j)).  The implication makes the
  ratio law apply only on an edge; paired absent edges are allowed.
-/
def ThermalDetailedBalance {N L : ℕ} (E : Fin N → ℝ) (β : Fin L → ℝ)
    (q : Fin L → Fin N → Fin N → ℝ) : Prop :=
  ∀ α i j, i ≠ j →
    ((0 < q α i j ↔ 0 < q α j i) ∧
      (0 < q α i j →
        q α i j / q α j i = Real.exp (β α * (E i - E j))))

noncomputable def tiltedRateMatrix {N L : ℕ} (E : Fin N → ℝ)
    (q : Fin L → Fin N → Fin N → ℝ) (α₀ : Fin L) (lambda : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i ≠ j then
      ∑ α, q α j i *
        if α = α₀ then Real.exp (-lambda * (E i - E j)) else 1
    else -∑ j', if j' = i then 0 else totalRate q i j'

def IsSourceSCGF {N L : ℕ} (E : Fin N → ℝ)
    (q : Fin L → Fin N → Fin N → ℝ) (α₀ : Fin L) (χ : ℝ → ℝ) : Prop :=
  χ 0 = 0 ∧ ContDiffAt ℝ 4 χ 0 ∧
    ∀ lambda,
      Matrix.det (χ lambda • (1 : Matrix (Fin N) (Fin N) ℝ) -
        tiltedRateMatrix E q α₀ lambda) = 0 ∧
      ∀ ν : ℝ, Matrix.det (ν • (1 : Matrix (Fin N) (Fin N) ℝ) -
        tiltedRateMatrix E q α₀ lambda) = 0 → ν ≤ χ lambda

def claim : Prop :=
  ∀ (N L : ℕ) (E : Fin N → ℝ) (β : Fin L → ℝ)
    (q : Fin L → Fin N → Fin N → ℝ) (α₀ : Fin L),
    (∀ α, 0 < β α) →
    (∀ α i j, i ≠ j → 0 ≤ q α i j) →
    ThermalDetailedBalance E β q →
    (∃ χ : ℝ → ℝ, IsSourceSCGF E q α₀ χ) ∧
      ∀ χ : ℝ → ℝ, IsSourceSCGF E q α₀ χ →
        0 < iteratedDeriv 2 χ 0 → 0 ≤ iteratedDeriv 4 χ 0 / iteratedDeriv 2 χ 0

end D5.S3.StatisticalMechanics.PtaszynskiThermalHeatKurtosisRefutation

namespace D5.S3.StatisticalMechanics.PtaszynskiThermalHeatKurtosisRefutation
open scoped Topology BigOperators Matrix
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private def E8 : Fin 6 → ℝ := ![0,1,0,1,0,1]
private def beta8 : Fin 2 → ℝ := ![Real.log 2, Real.log 8]
private def q8 : Fin 2 → Fin 6 → Fin 6 → ℝ := ![
  !![0,1,0,0,0,0; 2,0,0,0,0,0; 0,0,0,6,0,0;
     0,0,12,0,0,0; 0,0,0,0,0,6; 0,0,0,0,12,0],
  !![0,0,0,0,0,1; 0,0,8,0,0,0; 0,1,0,0,0,0;
     0,0,0,0,8,0; 0,0,0,1,0,0; 8,0,0,0,0,0]]

private def M8 (z u v : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![z+2,-2,0,0,0,-8*u;
     -1,z+10,-v,0,0,0;
     0,-8*u,z+7,-12,0,0;
     0,0,-6,z+20,-v,0;
     0,0,0,-8*u,z+7,-12;
     -v,0,0,0,-6,z+20]

private def poly8 (z : ℝ) : ℝ := 63504*z + 50202*z^2 + 13968*z^3 + 1507*z^4 + 66*z^5 + z^6

private theorem det_M8 (z u v : ℝ) (h : u*v=1) :
    (M8 z u v).det = poly8 z - 18432*(u^3-1) - 288*(v^3-1) := by
  norm_num [M8, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  dsimp [poly8]
  linear_combination (-512*u^2*v^2 + 192*u*v*z^2 + 4224*u*v*z + 15488*u*v - 24*z^4 - 1056*z^3 - 14056*z^2 - 58080*z - 64512) * h

private theorem beta8_pos : ∀ a, 0 < beta8 a := by
  intro a
  fin_cases a <;> norm_num [beta8, Real.log_pos]

private theorem q8_nonneg : ∀ a i j, i ≠ j → 0 ≤ q8 a i j := by
  intro a i j hij
  fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [q8]

private theorem q8_thermal : ThermalDetailedBalance E8 beta8 q8 := by
  have he2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have he8 : Real.exp (Real.log 8) = 8 := Real.exp_log (by norm_num)
  intro a i j hij
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [q8, E8, beta8, Real.exp_neg, he2, he8] at *

private theorem matrix8_eq (z t : ℝ) :
    z • (1 : Matrix (Fin 6) (Fin 6) ℝ) - tiltedRateMatrix E8 q8 1 t =
      M8 z (Real.exp t) (Real.exp (-t)) := by
  have hdiag (i : Fin 6) :
      (-∑ j', if j' = i then 0 else totalRate q8 i j') =
        MarkovMpembaTripletRefutation.generator (fun i j => totalRate q8 j i) i i := by
    simp [MarkovMpembaTripletRefutation.generator]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [tiltedRateMatrix, ne_eq, not_true_eq_false, ↓reduceIte,
      Matrix.sub_apply, Matrix.smul_apply]
    rw [hdiag]
    fin_cases i <;> norm_num [M8, MarkovMpembaTripletRefutation.generator,
      totalRate, q8, Fin.sum_univ_succ, Matrix.one_apply]
  · fin_cases i <;> fin_cases j <;>
      norm_num [M8, tiltedRateMatrix, q8, E8, totalRate,
        Fin.sum_univ_succ, Matrix.one_apply] at *

private theorem det8 (z t : ℝ) :
    Matrix.det (z • (1 : Matrix (Fin 6) (Fin 6) ℝ) - tiltedRateMatrix E8 q8 1 t) =
      poly8 z - 18432*(Real.exp (3*t)-1) - 288*(Real.exp (-3*t)-1) := by
  rw [matrix8_eq, det_M8 z (Real.exp t) (Real.exp (-t)) (by
    rw [← Real.exp_add]; simp)]
  have hp : Real.exp t ^ 3 = Real.exp (3*t) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hn : Real.exp (-t) ^ 3 = Real.exp (-3*t) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hp, hn]
private def jetPow (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | k+1, n => ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * jetPow a k i * a (n-i)

private theorem jetPow_eq (f : ℝ → ℝ) (k n : ℕ) (hf : ContDiffAt ℝ n f 0) :
    iteratedDeriv n (fun t => f t ^ k) 0 = jetPow (fun j => iteratedDeriv j f 0) k n := by
  induction k generalizing n with
  | zero => simp [jetPow, iteratedDeriv_const]
  | succ k ih =>
    simp only [pow_succ]
    rw [iteratedDeriv_fun_mul (hf.pow k) hf]
    unfold jetPow
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih i (hf.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)))]

private def polyJet (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  63504*a n + 50202*jetPow a 2 n + 13968*jetPow a 3 n +
    1507*jetPow a 4 n + 66*jetPow a 5 n + jetPow a 6 n

private theorem polynomial_jet (f : ℝ → ℝ) (n : ℕ) (hf : ContDiffAt ℝ n f 0) :
    iteratedDeriv n (fun t => poly8 (f t)) 0 =
      polyJet (fun j => iteratedDeriv j f 0) n := by
  dsimp [poly8, polyJet]
  repeat rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field]
  rw [jetPow_eq f 2 n hf, jetPow_eq f 3 n hf, jetPow_eq f 4 n hf,
    jetPow_eq f 5 n hf, jetPow_eq f 6 n hf]

private theorem polyJet_certificate (a : ℕ → ℝ) (h0 : a 0 = 0)
    (heq : ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      polyJet a n = 18432*(3:ℝ)^n + 288*(-3:ℝ)^n) :
    a 2 = (3581:ℝ)/2401 ∧ a 4 = -(113056891:ℝ)/1129900996 := by
  have h1 := heq 1 (by decide) (by decide)
  have h2 := heq 2 (by decide) (by decide)
  have h3 := heq 3 (by decide) (by decide)
  have h4 := heq 4 (by decide) (by decide)
  norm_num [polyJet, jetPow, Finset.sum_range_succ, Nat.choose, h0] at h1 h2 h3 h4
  have ha1 : a 1 = (6:ℝ)/7 := by linarith only [h1]
  rw [ha1] at h2 h3 h4
  norm_num at h2 h3 h4
  have ha2 : a 2 = (3581:ℝ)/2401 := by linarith only [h2]
  rw [ha2] at h3 h4
  norm_num at h3 h4
  have ha3 : a 3 = (1349819:ℝ)/1647086 := by linarith only [h3]
  rw [ha3] at h4
  norm_num at h4
  exact ⟨ha2, by linarith only [h4]⟩

private theorem implicit_cumulants (f : ℝ → ℝ) (hf : ContDiffAt ℝ 4 f 0)
    (hf0 : f 0 = 0)
    (heq : ∀ t : ℝ, poly8 (f t) =
      18432*(Real.exp (3*t)-1) + 288*(Real.exp (-3*t)-1)) :
    iteratedDeriv 2 f 0 = (3581:ℝ)/2401 ∧ iteratedDeriv 4 f 0 = -(113056891:ℝ)/1129900996 := by
  apply polyJet_certificate (fun n => iteratedDeriv n f 0) (by simpa using hf0)
  intro n hn hn4
  have hs : ContDiffAt ℝ n f 0 := hf.of_le (by exact_mod_cast hn4)
  have he := congrArg (fun g : ℝ → ℝ => iteratedDeriv n g 0) (funext heq)
  rw [polynomial_jet f n hs] at he
  rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop)] at he
  simp only [iteratedDeriv_const_mul_field] at he
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)] at he
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simpa only [iteratedDeriv_exp_const_mul, iteratedDeriv_const, ite_eq_right hn0,
    mul_zero, Real.exp_zero, mul_one, sub_zero] using he


private theorem rational_sign_certificate :
    0 < (3581:ℚ)/2401 ∧
    (-(113056891:ℚ)/1129900996) / ((3581:ℚ)/2401) = -(113056891:ℚ)/1685204276 ∧
    -(113056891:ℚ)/1685204276 < 0 := by
  norm_num

theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨⟨f, hf⟩, hnonneg⟩ :=
    hclaim 6 2 E8 beta8 q8 1 beta8_pos q8_nonneg q8_thermal
  have heq (t : ℝ) : poly8 (f t) =
      18432*(Real.exp (3*t)-1) + 288*(Real.exp (-3*t)-1) := by
    have hz := (hf.2.2 t).1
    rw [det8] at hz
    change poly8 (f t) - 18432*(Real.exp (3*t)-1) - 288*(Real.exp (-3*t)-1) = 0 at hz
    linarith only [hz]
  have hc := implicit_cumulants f hf.2.1 hf.1 heq
  have hp : 0 < iteratedDeriv 2 f 0 := by
    rw [hc.1]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_pos (K:=ℝ)).2 rational_sign_certificate.1
  have hn : (-(113056891:ℝ)/1129900996) / ((3581:ℝ)/2401) < 0 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      (Rat.cast_lt_zero (K:=ℝ)).2
        (lt_of_eq_of_lt rational_sign_certificate.2.1 rational_sign_certificate.2.2)
  have hh := hnonneg f hf hp
  rw [hc.2, hc.1] at hh
  exact (not_le_of_gt hn) hh

end
end D5.S3.StatisticalMechanics.PtaszynskiThermalHeatKurtosisRefutation
