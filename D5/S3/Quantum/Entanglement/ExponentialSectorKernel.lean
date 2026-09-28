/- GID: D5/S3/Quantum/Entanglement/ExponentialSectorKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ExponentialSectorKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct equilibrium weights and the exact simplex minimum of an ordered exponential kernel. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.ExponentialSectorKernel

open scoped BigOperators
noncomputable section

def kernel (loss : ℕ → ℝ) (i j : ℕ) : ℝ :=
  Real.exp (-|loss i - loss j| / 2)

def edge (loss : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.exp (-(loss (i + 1) - loss i) / 2)

def energy (n : ℕ) (loss : ℕ → ℝ) (p : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * p j * kernel loss i j

def equilibriumWeight : (n : ℕ) → (ℕ → ℝ) → Fin (n + 1) → ℝ
  | 0, _ => fun _ => 1
  | n + 1, loss => Fin.lastCases (1 / (1 + edge loss n))
      (fun i => equilibriumWeight n loss i -
        if i = Fin.last n then edge loss n / (1 + edge loss n) else 0)

def normalizer (n : ℕ) (loss : ℕ → ℝ) : ℝ :=
  1 + ∑ i : Fin n, (1 - edge loss i) / (1 + edge loss i)

set_option maxHeartbeats 800000 in
theorem result (loss : ℕ → ℝ) (horder : Monotone loss) (n : ℕ) :
    (∀ w : Fin (n + 1) → ℝ, 0 ≤ energy n loss w) ∧
    (∀ i, 0 ≤ equilibriumWeight n loss i) ∧
    (∀ i : Fin (n + 1),
      ∑ j : Fin (n + 1), kernel loss i j * equilibriumWeight n loss j = 1) ∧
    (∑ i, equilibriumWeight n loss i) = normalizer n loss ∧
    0 < normalizer n loss ∧
    (fun i => equilibriumWeight n loss i / normalizer n loss) ∈
      stdSimplex ℝ (Fin (n + 1)) ∧
    energy n loss (fun i => equilibriumWeight n loss i / normalizer n loss) =
      1 / normalizer n loss ∧
    (∀ p ∈ stdSimplex ℝ (Fin (n + 1)),
      1 / normalizer n loss ≤ energy n loss p) ∧
    normalizer n loss = 1 +
      ∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4) ∧
    1 - kernel loss 0 n ≤ 2 * (1 - 1 / normalizer n loss) ∧
    2 * (1 - 1 / normalizer n loss) ≤
      2 * (loss n - loss 0) / (4 + (loss n - loss 0)) ∧
    (∀ epsilon : ℝ, epsilon < 2 →
      (2 * (1 - 1 / normalizer n loss) ≤ epsilon ↔
        normalizer n loss - 1 ≤ epsilon / (2 - epsilon))) ∧
    ((∀ i < n, loss i < loss (i + 1)) → ∀ i, 0 < equilibriumWeight n loss i) := by
  classical
  have hdiag (i : ℕ) : kernel loss i i = 1 := by simp [kernel]
  have hsymm (i j : ℕ) : kernel loss i j = kernel loss j i := by
    simp only [kernel, abs_sub_comm]
  have hedge (i : ℕ) : 0 < edge loss i ∧ edge loss i ≤ 1 := by
    constructor
    · exact Real.exp_pos _
    · apply Real.exp_le_one_iff.mpr
      have := horder (Nat.le_succ i)
      linarith
  have hcross (k : ℕ) (i : Fin (k + 1)) :
      kernel loss i (k + 1) = edge loss k * kernel loss i k := by
    have hi : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
    have hi0 := horder hi
    have hi1 := horder (hi.trans (Nat.le_succ k))
    simp only [kernel, edge, abs_of_nonpos (sub_nonpos.mpr hi0),
      abs_of_nonpos (sub_nonpos.mpr hi1), ← Real.exp_add]
    congr 1
    ring
  have hstructure : ∀ k : ℕ,
      (∀ w : Fin (k + 1) → ℝ, 0 ≤ energy k loss w) ∧
      (∀ i, 0 ≤ equilibriumWeight k loss i) ∧
      (∀ i : Fin (k + 1),
        ∑ j : Fin (k + 1), kernel loss i j * equilibriumWeight k loss j = 1) ∧
      (∑ i, equilibriumWeight k loss i) = normalizer k loss ∧
      1 / 2 ≤ equilibriumWeight k loss (Fin.last k) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro w
          simpa [energy, kernel] using mul_self_nonneg (w 0)
        · intro i
          norm_num [equilibriumWeight]
        · intro i
          simp [equilibriumWeight, kernel, Fin.eq_zero i]
        · simp [equilibriumWeight, normalizer]
        · norm_num [equilibriumWeight]
    | succ k ih =>
        rcases ih with ⟨hpos, hweight, hrow, hsum, hlast⟩
        let a := edge loss k
        have ha : 0 < a := (hedge k).1
        have ha1 : a ≤ 1 := (hedge k).2
        have hden : 0 < 1 + a := by linarith
        have hden0 : 1 + a ≠ 0 := ne_of_gt hden
        have halpha : a / (1 + a) ≤ 1 / 2 := by
          apply (div_le_iff₀ hden).mpr
          linarith
        have hbeta : 1 / 2 ≤ 1 / (1 + a) := by
          apply (le_div_iff₀ hden).mpr
          linarith
        have hwold (i : Fin (k + 1)) :
            equilibriumWeight (k + 1) loss i.castSucc =
              equilibriumWeight k loss i - if i = Fin.last k then a / (1 + a) else 0 := by
          simp [equilibriumWeight, a]
        have hwnew : equilibriumWeight (k + 1) loss (Fin.last (k + 1)) =
            1 / (1 + a) := by simp [equilibriumWeight, a]
        have hpoint (f : Fin (k + 1) → ℝ) (c : ℝ) :
            (∑ i, f i * (if i = Fin.last k then c else 0)) = f (Fin.last k) * c := by
          simp
        have hrowsOld (i : Fin (k + 1)) :
            ∑ j : Fin (k + 2), kernel loss i.castSucc j *
              equilibriumWeight (k + 1) loss j = 1 := by
          rw [Fin.sum_univ_castSucc]
          simp only [hwold, hwnew, Fin.val_castSucc, Fin.val_last]
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          rw [hpoint, hrow, hcross]
          dsimp [a]
          ring
        have hrowsNew :
            ∑ j : Fin (k + 2), kernel loss (Fin.last (k + 1)) j *
              equilibriumWeight (k + 1) loss j = 1 := by
          rw [Fin.sum_univ_castSucc]
          simp only [hwold, hwnew, Fin.val_castSucc, Fin.val_last, hdiag, one_mul]
          have hc (j : Fin (k + 1)) : kernel loss (k + 1) j =
              a * kernel loss k j := by
            rw [hsymm, hcross, hsymm (j : ℕ) k]
          simp only [hc, mul_sub, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
          have hr : (∑ j : Fin (k + 1), kernel loss k j * equilibriumWeight k loss j) = 1 := by
            simpa only [Fin.val_last] using hrow (Fin.last k)
          rw [hr]
          rw [hpoint]
          simp only [Fin.val_last, hdiag]
          field_simp
          ring
        have hnewsum : (∑ i, equilibriumWeight (k + 1) loss i) =
            normalizer (k + 1) loss := by
          rw [Fin.sum_univ_castSucc]
          simp only [hwold, hwnew]
          simp_rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [hsum]
          simp only [normalizer, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
          dsimp [a]
          ring
        have hpositive (w : Fin (k + 2) → ℝ) : 0 ≤ energy (k + 1) loss w := by
          let x := w (Fin.last (k + 1))
          let old : Fin (k + 1) → ℝ := fun i => w i.castSucc
          let corrected : Fin (k + 1) → ℝ := fun i =>
            old i + if i = Fin.last k then a * x else 0
          have hexpand : energy (k + 1) loss w =
              energy k loss old +
                2 * a * x * (∑ i, old i * kernel loss i k) + x ^ 2 := by
            unfold energy
            have hsplit (i : Fin (k + 2)) :
                (∑ j : Fin (k + 2), w i * w j * kernel loss i j) =
                  (∑ j : Fin (k + 1), w i * w j.castSucc * kernel loss i j.castSucc) +
                    w i * w (Fin.last (k + 1)) * kernel loss i (Fin.last (k + 1)) :=
              Fin.sum_univ_castSucc _
            rw [Fin.sum_univ_castSucc]
            simp only [hsplit, Finset.sum_add_distrib]
            simp only [Fin.val_castSucc, Fin.val_last, hdiag]
            have hc (i : Fin (k + 1)) : kernel loss (k + 1) i =
                a * kernel loss i k := by rw [hsymm, hcross]
            simp only [hcross, hc]
            simp only [mul_one]
            change (∑ i, ∑ j, old i * old j * kernel loss i j) +
              (∑ i, old i * x * (a * kernel loss i k)) +
              ((∑ i, x * old i * (a * kernel loss i k)) + x * x) = _
            have ht (i : Fin (k + 1)) : old i * x * (a * kernel loss i k) =
                a * x * (old i * kernel loss i k) := by ring
            have hs (i : Fin (k + 1)) : x * old i * (a * kernel loss i k) =
                a * x * (old i * kernel loss i k) := by ring
            simp only [ht, hs, ← Finset.mul_sum]
            ring
          have hcorrected : energy k loss corrected = energy k loss old +
              2 * a * x * (∑ i, old i * kernel loss i k) + a ^ 2 * x ^ 2 := by
            unfold energy
            dsimp [corrected]
            simp_rw [add_mul, mul_add, add_mul, Finset.sum_add_distrib]
            have he (i : Fin (k + 1)) :
                (∑ j, old i * (if j = Fin.last k then a * x else 0) * kernel loss i j) =
                  old i * (a * x) * kernel loss i k := by
              simp
            have hf (j : Fin (k + 1)) :
                (∑ i, (if i = Fin.last k then a * x else 0) * old j * kernel loss i j) =
                  a * x * old j * kernel loss k j := by
              simp
            have hg :
                (∑ i, ∑ j, (if i = Fin.last k then a * x else 0) *
                  (if j = Fin.last k then a * x else 0) * kernel loss i j) =
                    a ^ 2 * x ^ 2 := by
              simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
                Finset.mem_univ, if_true, Fin.val_last, hdiag, mul_one]
              ring
            rw [hg]
            simp_rw [he]
            have hflip :
                (∑ i, ∑ j, (if i = Fin.last k then a * x else 0) * old j *
                  kernel loss i j) = ∑ j, a * x * old j * kernel loss k j := by
              rw [Finset.sum_comm]
              simp_rw [hf]
            rw [hflip]
            simp only [hsymm k]
            have heq (i : Fin (k + 1)) : old i * (a * x) * kernel loss i k =
                a * x * (old i * kernel loss i k) := by ring
            have heq' (i : Fin (k + 1)) : a * x * old i * kernel loss i k =
                a * x * (old i * kernel loss i k) := by ring
            simp only [heq, heq', ← Finset.mul_sum]
            ring
          rw [hexpand]
          have hp := hpos corrected
          have hr : 0 ≤ (1 - a ^ 2) * x ^ 2 :=
            mul_nonneg (by nlinarith) (sq_nonneg x)
          nlinarith [hcorrected]
        refine ⟨hpositive, ?_, ?_, hnewsum, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · rw [hwnew]
            exact (div_pos zero_lt_one hden).le
          · rw [hwold]
            split_ifs with h
            · subst j
              linarith
            · simpa using hweight j
        · intro i
          exact Fin.lastCases hrowsNew hrowsOld i
        · rw [hwnew]
          exact hbeta
  rcases hstructure n with ⟨hpos, hweight, hrow, hsum, hlast⟩
  let Z := normalizer n loss
  let v := equilibriumWeight n loss
  let p : Fin (n + 1) → ℝ := fun i => v i / Z
  have hZ : 0 < Z := by
    have hsumpos : equilibriumWeight n loss (Fin.last n) ≤
        ∑ i, equilibriumWeight n loss i :=
      Finset.single_le_sum (fun i _ => hweight i) (Finset.mem_univ _)
    dsimp [Z]
    rw [← hsum]
    linarith
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  have hpsimplex : p ∈ stdSimplex ℝ (Fin (n + 1)) := by
    constructor
    · intro i
      exact div_nonneg (hweight i) hZ.le
    · dsimp [p, v]
      rw [← Finset.sum_div, hsum]
      exact div_self hZ0
  have hprow (i : Fin (n + 1)) : ∑ j : Fin (n + 1), kernel loss i j * p j = 1 / Z := by
    dsimp [p, v]
    simp only [← mul_div_assoc, ← Finset.sum_div]
    exact congrArg (fun t : ℝ => t / Z) (hrow i)
  have hpenergy : energy n loss p = 1 / Z := by
    unfold energy
    have he (i j : Fin (n + 1)) : p i * p j * kernel loss i j =
        p i * (kernel loss i j * p j) := by ring
    simp_rw [he, ← Finset.mul_sum, hprow]
    rw [← Finset.sum_mul]
    rw [hpsimplex.2, one_mul]
  have hmin (r : Fin (n + 1) → ℝ) (hr : r ∈ stdSimplex ℝ (Fin (n + 1))) :
      1 / Z ≤ energy n loss r := by
    let d : Fin (n + 1) → ℝ := fun i => r i - p i
    have hdsum : ∑ i, d i = 0 := by
      simp only [d, Finset.sum_sub_distrib, hr.2, hpsimplex.2, sub_self]
    have hcross0 : (∑ i, ∑ j, d i * p j * kernel loss i j) = 0 := by
      simp_rw [mul_assoc, mul_comm (p _), ← Finset.mul_sum, hprow,
        ← Finset.sum_mul]
      rw [hdsum, zero_mul]
    have hflip : (∑ i, ∑ j, p i * d j * kernel loss i j) =
        ∑ i, ∑ j, d i * p j * kernel loss i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm (j : ℕ) i]
      ring
    have hexpand : energy n loss r = energy n loss p + energy n loss d := by
      have hrp (i : Fin (n + 1)) : r i = p i + d i := by dsimp [d]; ring
      unfold energy
      simp_rw [hrp, add_mul, mul_add, add_mul, Finset.sum_add_distrib]
      rw [hflip, hcross0]
      ring
    rw [hexpand, hpenergy]
    exact le_add_of_nonneg_right (hpos d)
  have htanh (i : ℕ) : (1 - edge loss i) / (1 + edge loss i) =
      Real.tanh ((loss (i + 1) - loss i) / 4) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    let x := (loss (i + 1) - loss i) / 4
    have he : edge loss i = Real.exp (-x) ^ 2 := by
      simp only [edge, pow_two, ← Real.exp_add]
      congr 1
      dsimp [x]
      ring
    have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [he]
    change (1 - Real.exp (-x) ^ 2) / (1 + Real.exp (-x) ^ 2) =
      ((Real.exp x - Real.exp (-x)) / 2) /
        ((Real.exp x + Real.exp (-x)) / 2)
    field_simp
    linear_combination -2 * Real.exp (-x) * hprod
  have htotal : Z = 1 + ∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4) := by
    dsimp [Z, normalizer]
    simp_rw [htanh]
  have hZ1 : 1 ≤ Z := by
    dsimp [Z, normalizer]
    have hsum0 : 0 ≤ ∑ i : Fin n, (1 - edge loss i) / (1 + edge loss i) :=
      Finset.sum_nonneg fun i _ =>
        div_nonneg (sub_nonneg.mpr (hedge i).2) (by linarith [(hedge i).1])
    linarith
  have hZinv : Z * (1 / Z) = 1 := by field_simp
  have hboundLow : 1 - kernel loss 0 n ≤ 2 * (1 - 1 / Z) := by
    let r : Fin (n + 1) → ℝ := fun i =>
      (if i = 0 then 1 / 2 else 0) + (if i = Fin.last n then 1 / 2 else 0)
    have hrsimplex : r ∈ stdSimplex ℝ (Fin (n + 1)) := by
      constructor
      · intro i
        dsimp [r]
        positivity
      · dsimp [r]
        rw [Finset.sum_add_distrib]
        simp
        norm_num
    have hre : energy n loss r = (1 + kernel loss 0 n) / 2 := by
      unfold energy
      dsimp [r]
      simp only [add_mul, mul_add, add_mul, Finset.sum_add_distrib,
        ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Fin.val_zero, Fin.val_last, hdiag, hsymm n 0]
      ring
    have hm := hmin r hrsimplex
    rw [hre] at hm
    linarith
  have htel : ∀ k : ℕ,
      (∑ i : Fin k, (loss (i + 1) - loss i)) = loss k - loss 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      ring
  have hboundHigh : 2 * (1 - 1 / Z) ≤
      2 * (loss n - loss 0) / (4 + (loss n - loss 0)) := by
    have hsumle : Z - 1 ≤ (loss n - loss 0) / 4 := by
      rw [htotal]
      have hbound (i : Fin n) : Real.tanh ((loss (i + 1) - loss i) / 4) ≤
          (loss (i + 1) - loss i) / 4 := by
        have hx : 0 ≤ (loss (i + 1) - loss i) / 4 :=
          div_nonneg (sub_nonneg.mpr (horder (Nat.le_succ i))) (by norm_num)
        rw [Real.tanh_eq_sinh_div_cosh]
        exact (div_le_iff₀ (Real.cosh_pos _)).mpr
          (D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg hx)
      have h : (∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4)) ≤
          ∑ i : Fin n, (loss (i + 1) - loss i) / 4 :=
        Finset.sum_le_sum (fun i _ => hbound i)
      rw [← Finset.sum_div, htel] at h
      linarith
    have hR : 0 ≤ loss n - loss 0 := sub_nonneg.mpr (horder (Nat.zero_le n))
    have hden : 0 < 4 + (loss n - loss 0) := by linarith
    apply (le_div_iff₀ hden).mpr
    have hz := mul_le_mul_of_nonneg_right hsumle (by norm_num : (0 : ℝ) ≤ 4)
    have hi := mul_le_mul_of_nonneg_right hz (le_of_lt (one_div_pos.mpr hZ))
    nlinarith [hZinv]
  have hbudget (epsilon : ℝ) (he : epsilon < 2) :
      (2 * (1 - 1 / Z) ≤ epsilon ↔ Z - 1 ≤ epsilon / (2 - epsilon)) := by
    rw [le_div_iff₀ (by linarith : 0 < 2 - epsilon)]
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_right h hZ.le
      nlinarith [hZinv]
    · intro h
      have hm := mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.mpr hZ))
      nlinarith [hZinv]
  have hstrict (hs : ∀ i < n, loss i < loss (i + 1)) :
      ∀ k : ℕ, k ≤ n → ∀ i, 0 < equilibriumWeight k loss i := by
    intro k
    induction k with
    | zero => intro hk i; norm_num [equilibriumWeight]
    | succ k ih =>
      intro hk
      have ha : 0 < edge loss k := (hedge k).1
      have ha1 : edge loss k < 1 := by
        apply Real.exp_lt_one_iff.mpr
        have := hs k (by omega)
        linarith
      have hd : 0 < 1 + edge loss k := by linarith
      have halpha : edge loss k / (1 + edge loss k) < 1 / 2 := by
        apply (div_lt_iff₀ hd).mpr
        linarith
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [equilibriumWeight, Fin.lastCases_last]
        exact div_pos zero_lt_one hd
      · simp only [equilibriumWeight, Fin.lastCases_castSucc]
        split_ifs with h
        · subst j
          have he := (hstructure k).2.2.2.2
          linarith
        · simpa using ih (by omega) j
  exact ⟨hpos, hweight, hrow, hsum, hZ, hpsimplex, hpenergy, hmin, htotal,
    hboundLow, hboundHigh, hbudget, fun hs => hstrict hs n le_rfl⟩

end
end D5.S3.Quantum.Entanglement.ExponentialSectorKernel
