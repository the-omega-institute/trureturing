/- GID: D5/S3/Analytic/Stieltjes/NoisyFirstAtom
   generality: G
   mirror-B: D5/B/S3/Analytic/Stieltjes/NoisyFirstAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: Noisy normalized Stieltjes samples enclose the first atom. -/

module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Signed forward differences of a positive atomic resolvent recover a positive product kernel. -/

@[expose] public section

namespace D5.S3.Analytic.Stieltjes.NoisyFirstAtom

open Finset

noncomputable section

/-- The signed forward difference at the first of the supplied nodes. -/
def difference : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => f 0
  | k + 1, f => difference k f - difference k (fun j => f (j + 1))

/-- The denominator after removing the exactly normalized zero node. -/
def poleProduct (k : ℕ) (x h : ℝ) : ℝ :=
  ∏ j ∈ range k, (x + ((j : ℝ) + 1) * h)

private def scale (k : ℕ) (h : ℝ) : ℝ := k.factorial * h ^ k

private theorem prod_pos (k : ℕ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    0 < poleProduct k x h := Finset.prod_pos fun j _ => by positivity

private theorem scale_pos (k : ℕ) {h : ℝ} (hh : 0 < h) : 0 < scale k h := by
  unfold scale
  positivity

private theorem atom_difference (k : ℕ) (w x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    difference k (fun j => w / (x + j * h)) = w * scale k h / (x * poleProduct k x h) := by
  induction k generalizing x with
  | zero => simp [difference, scale, poleProduct]
  | succ k ih =>
    have hright : (fun j : ℕ => w / (x + ((j + 1 : ℕ) : ℝ) * h)) =
        (fun j : ℕ => w / (x + h + j * h)) := by funext j; push_cast; ring_nf
    rw [difference, hright, ih x hx, ih (x + h) (by positivity)]
    have left : x * poleProduct (k+1) x h =
        (x * poleProduct k x h) * (x + ((k : ℝ)+1)*h) := by
      simp only [poleProduct, prod_range_succ]; ring
    have right : x * poleProduct (k+1) x h = x * ((x+h)*poleProduct k (x+h) h) := by
      unfold poleProduct
      rw [prod_range_succ']
      simp only [Nat.cast_zero, zero_add, one_mul, Nat.cast_add_one]
      have e : (fun i : ℕ => x + (i + 1 + 1 : ℝ) * h) =
          (fun i : ℕ => x+h + ((i : ℝ)+1)*h) := by funext i; ring
      rw [e]; ring
    have hl := mul_pos hx (prod_pos k hx hh)
    have hr := mul_pos (show 0 < x+h by positivity) (prod_pos k (by positivity : 0 < x+h) hh)
    apply (eq_div_iff (mul_pos hx (prod_pos (k+1) hx hh)).ne').2
    rw [sub_mul]
    conv_lhs =>
      lhs
      rw [left, ← mul_assoc, div_mul_cancel₀ _ hl.ne']
    conv_lhs =>
      rhs
      rw [right, mul_comm x, ← mul_assoc, div_mul_cancel₀ _ hr.ne']
    simp only [scale, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, pow_succ]; ring

private theorem difference_sum (k : ℕ) (rows : ℕ → ℕ → ℝ) (f : ℕ → ℝ)
    (hf : ∀ j, HasSum (fun i => rows i j) (f j)) :
    HasSum (fun i => difference k (rows i)) (difference k f) := by
  induction k generalizing rows f with
  | zero => exact hf 0
  | succ k ih => exact (ih rows f hf).sub (ih (fun i j => rows i (j+1)) _ (fun j => hf (j+1)))

private theorem difference_error (k : ℕ) (f g : ℕ → ℝ) (e₀ e : ℝ)
    (hzero : |f 0 - g 0| ≤ e₀) (hrest : ∀ j, 0 < j → j ≤ k → |f j - g j| ≤ e) :
    |difference k f - difference k g| ≤ e₀ + (2 ^ k - 1) * e := by
  induction k generalizing f g e₀ with
  | zero => simpa [difference] using hzero
  | succ k ih =>
    have first := ih f g e₀ hzero fun j hj hjk => hrest j hj (by omega)
    have next := ih (fun j => f (j+1)) (fun j => g (j+1)) e (hrest 1 (by omega) (by omega))
      fun j _ hjk => hrest (j+1) (by omega) (by omega)
    simp only [difference]
    rw [show difference k f - difference k (fun j => f (j+1)) -
          (difference k g - difference k (fun j => g (j+1))) =
        (difference k f - difference k g) -
          (difference k (fun j => f (j+1)) - difference k (fun j => g (j+1))) by ring]
    apply (abs_sub _ _).trans
    rw [pow_succ]; linarith

/-- A multiplicity floor and an exact origin reading enclose the first positive atom from
`k` equally spaced noisy values. The infinite weights sum to one. -/
theorem noisy_first_atom_enclosure (k : ℕ) (p b y : ℕ → ℝ) (h S ε : ℝ)
    (hh : 0 < h) (hS : 0 < S) (ha : 0 < b 0) (hmin : ∀ i, b 0 ≤ b i)
    (hp : ∀ i, 0 ≤ p i) (hsum : HasSum p 1) (hmass : 1 ≤ S * b 0 * p 0)
    (hy : y 0 = 1) (herr : ∀ j, 0 < j → j ≤ k →
      |y j - ∑' i, p i * b i / (b i + j * h)| ≤ ε) :
    let D := difference k y / (k.factorial * h^k)
    let η := (2^k - 1) * ε / (k.factorial * h^k)
    1 ≤ S * b 0 * poleProduct k (b 0) h * (D + η) ∧
      poleProduct k (b 0) h * (D - η) ≤ 1 := by
  let rows : ℕ → ℕ → ℝ := fun i j => p i * b i / (b i + j*h)
  let f : ℕ → ℝ := fun j => ∑' i, rows i j
  have hb (i : ℕ) : 0 < b i := ha.trans_le (hmin i)
  have hf (j : ℕ) : HasSum (fun i => rows i j) (f j) := by
    apply Summable.hasSum
    have hj : 0 ≤ (j : ℝ)*h := by positivity
    apply Summable.of_nonneg_of_le
      (fun i => div_nonneg (mul_nonneg (hp i) (hb i).le) (add_nonneg (hb i).le hj)) _ hsum.summable
    intro i
    apply (div_le_iff₀ (add_pos_of_pos_of_nonneg (hb i) hj)).2
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hj) (hp i)
  have hf0 : f 0 = 1 := by
    apply HasSum.unique (hf 0)
    simpa [rows, (hb _).ne'] using hsum
  have he := difference_error k y f 0 ε (by rw [hy,hf0]; simp) herr
  rw [zero_add] at he
  have raw := (difference_sum k rows f hf).div_const (scale k h)
  have hc := scale_pos k hh
  have hfiltered : HasSum (fun i => p i / poleProduct k (b i) h) (difference k f / scale k h) := by
    convert raw using 1
    funext i
    rw [show rows i = (fun j : ℕ => p i * b i / (b i + j*h)) from rfl,
      atom_difference k _ _ _ (hb i) hh]
    field_simp [(hb i).ne', hc.ne', (prod_pos k (hb i) hh).ne']
  let P := poleProduct k (b 0) h
  have hP : 0 < P := prod_pos k ha hh
  have upper : difference k f / scale k h ≤ 1 / P := by
    apply hasSum_le _ hfiltered (hsum.div_const P)
    intro i
    apply div_le_div_of_nonneg_left (hp i) hP
    exact Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => add_le_add_left (hmin i) _)
  have lower : p 0 / P ≤ difference k f / scale k h := by
    simpa [P] using sum_le_hasSum ({0} : Finset ℕ)
      (fun i _ => div_nonneg (hp i) (prod_pos k (hb i) hh).le) hfiltered
  have hnoise : |difference k y / scale k h - difference k f / scale k h| ≤
      (2^k - 1) * ε / scale k h := by
    rw [← sub_div, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right he hc.le
  obtain ⟨hl,hu⟩ := abs_le.mp hnoise
  change 1 ≤ S*b 0*P*(difference k y / scale k h + (2^k-1)*ε / scale k h) ∧
    P*(difference k y / scale k h - (2^k-1)*ε / scale k h) ≤ 1
  constructor
  · have v : p 0 / P ≤ difference k y / scale k h + (2^k-1)*ε / scale k h := by linarith
    have t := (div_le_iff₀ hP).1 v
    calc 1 ≤ S*b 0*p 0 := hmass
         _ ≤ S*b 0*((difference k y / scale k h + (2^k-1)*ε / scale k h)*P) :=
           mul_le_mul_of_nonneg_left t (mul_pos hS ha).le
         _ = _ := by ring
  · have v : difference k y / scale k h - (2^k-1)*ε / scale k h ≤ 1/P := by linarith
    simpa [mul_comm] using (le_div_iff₀ hP).1 v

end

end D5.S3.Analytic.Stieltjes.NoisyFirstAtom
