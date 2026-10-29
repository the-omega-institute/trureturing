/- GID: D5/S3/QuantumBounds/LocalPerceptionMermin
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/LocalPerceptionMermin
   mirror-E: none(waiver:non-computational-content)
   anchors: []
   utility: none
   digest: Independent context coupling proves the sharp termwise Mermin LPO bound. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! The tetrahedral coupling removes all pair moments from the Mermin bound. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.QuantumBounds.LocalPerceptionMermin

variable {Ω : Type*} [Fintype Ω]

/-- Expectation with respect to a finite nonnegative table of mass one. -/
def avg (p f : Ω → ℝ) : ℝ := ∑ i, p i * f i

/-- The four independent context draws; no all-settings joint model is assumed. -/
def avg4 (p q r s : Ω → ℝ) (f : Ω → Ω → Ω → Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, p i * q j * r k * s l * f i j k l

private theorem avg4_prod (p q r s f g h u : Ω → ℝ) :
    avg4 p q r s (fun i j k l => f i * g j * h k * u l) =
      avg p f * avg q g * avg r h * avg s u := by
  unfold avg4 avg
  calc
    _ = ∑ i, (p i*f i) * (∑ j, (q j*g j) *
        (∑ k, (r k*h k) * (∑ l, s l*u l))) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk
      apply Finset.sum_congr rfl; intro l hl
      ring
    _ = _ := by simp_rw [← Finset.sum_mul]; ring

private theorem linear_interval (x a b : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hplus : a + b ≤ 2) (hminus : a - b ≤ 2) : a + b * x ≤ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hminus),
    mul_nonneg (by linarith : 0 ≤ 1 + x) (sub_nonneg.mpr hplus)]

/-- Classical Mermin bound for arbitrary real contractions. -/
theorem classical_bound (a A b B c C : ℝ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hA : -1 ≤ A ∧ A ≤ 1)
    (hb : -1 ≤ b ∧ b ≤ 1) (hB : -1 ≤ B ∧ B ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) (hC : -1 ≤ C ∧ C ≤ 1) :
    a*b*c - a*B*C - A*b*C - A*B*c ≤ 2 := by
  have hp : -A*B*c - A*C*b - B*C + b*c ≤ 2 := by
    have hp : -B*C - B*c - C*b + b*c ≤ 2 := by
      have hp : -B*C - B*c - C + c ≤ 2 := by
        have hp : -2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : 2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (-C + c) (-C - c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      have hm : -B*C - B*c + C - c ≤ 2 := by
        have hp : -2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : 2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (C - c) (-C - c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      convert linear_interval b (-B*C - B*c) (-C + c) hb.1 hb.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
    have hm : -B*C + B*c + C*b + b*c ≤ 2 := by
      have hp : -B*C + B*c + C + c ≤ 2 := by
        have hp : 2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : 2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (C + c) (-C + c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      have hm : -B*C + B*c - C - c ≤ 2 := by
        have hp : -2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : -2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (-C - c) (-C + c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      convert linear_interval b (-B*C + B*c) (C + c) hb.1 hb.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
    convert linear_interval A (-B*C + b*c) (-B*c - C*b) hA.1 hA.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
  have hm : -A*B*c - A*C*b + B*C - b*c ≤ 2 := by
    have hp : B*C - B*c - C*b - b*c ≤ 2 := by
      have hp : B*C - B*c - C - c ≤ 2 := by
        have hp : -2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : -2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (-C - c) (C - c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      have hm : B*C - B*c + C + c ≤ 2 := by
        have hp : 2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : 2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (C + c) (C - c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      convert linear_interval b (B*C - B*c) (-C - c) hb.1 hb.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
    have hm : B*C + B*c + C*b - b*c ≤ 2 := by
      have hp : B*C + B*c + C - c ≤ 2 := by
        have hp : 2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : -2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (C - c) (C + c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      have hm : B*C + B*c - C + c ≤ 2 := by
        have hp : 2*c ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        have hm : -2*C ≤ 2 := by
          nlinarith [hc.1, hc.2, hC.1, hC.2]
        convert linear_interval B (-C + c) (C + c) hB.1 hB.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
      convert linear_interval b (B*C + B*c) (C - c) hb.1 hb.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
    convert linear_interval A (B*C - b*c) (-B*c - C*b) hA.1 hA.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring
  convert linear_interval a (-A*B*c - A*C*b) (-B*C + b*c) ha.1 ha.2 (by nlinarith only [hp]) (by nlinarith only [hm]) using 1; ring

private theorem mul_contract {x y : ℝ} (hx : -1 ≤ x ∧ x ≤ 1)
    (hy : -1 ≤ y ∧ y ≤ 1) : -1 ≤ x*y ∧ x*y ≤ 1 := by
  apply abs_le.mp
  rw [abs_mul]
  calc |x| * |y| ≤ 1 * 1 := mul_le_mul (abs_le.mpr hx) (abs_le.mpr hy) (abs_nonneg _) (by norm_num)
       _ = 1 := by norm_num

private theorem avg4_le (p q r s : Ω → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (f g : Ω → Ω → Ω → Ω → ℝ) (hfg : ∀ i j k l, f i j k l ≤ g i j k l) :
    avg4 p q r s f ≤ avg4 p q r s g := by
  apply Finset.sum_le_sum; intro i hi
  apply Finset.sum_le_sum; intro j hj
  apply Finset.sum_le_sum; intro k hk
  apply Finset.sum_le_sum; intro l hl
  exact mul_le_mul_of_nonneg_left (hfg i j k l)
    (mul_nonneg (mul_nonneg (mul_nonneg (hp _) (hq _)) (hr _)) (hs _))

/-- Edge labels of the tetrahedron of Mermin contexts. -/
def edge : Fin 4 → Fin 3 → Fin 6 :=
  ![![0,2,4], ![0,3,5], ![1,2,5], ![1,3,4]]

/-- The triple moment of a normalized context table. -/
def triple (p : Fin 4 → Ω → ℝ) (u : Fin 4 → Fin 3 → Ω → ℝ) (v : Fin 4) : ℝ :=
  avg (p v) (fun i => u v 0 i * u v 1 i * u v 2 i)

/-- The Eq. (52) termwise Mermin LPO, with squared marginal weights. -/
def witness (m : Fin 6 → ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (m 0*m 2*m 4)^2*t 0 - (m 0*m 3*m 5)^2*t 1 -
  (m 1*m 2*m 5)^2*t 2 - (m 1*m 3*m 4)^2*t 3

/-- Four arbitrary nonnegative context tables suffice. No additional pair-moment
constraints are needed. Only repeated singleton moments must agree. -/
theorem table_bound
    (p : Fin 4 → Ω → ℝ) (u : Fin 4 → Fin 3 → Ω → ℝ) (m : Fin 6 → ℝ)
    (hp : ∀ v i, 0 ≤ p v i) (hn : ∀ v, ∑ i, p v i = 1)
    (hu : ∀ v j i, -1 ≤ u v j i ∧ u v j i ≤ 1)
    (hm : ∀ e, -1 ≤ m e ∧ m e ≤ 1)
    (hme : ∀ v j, avg (p v) (u v j) = m (edge v j)) :
    witness m (triple p u) ≤ 2 := by
  let F : Ω → Ω → Ω → Ω → ℝ := fun i j k l =>
    (m 0*u 0 0 i*u 1 0 j)*(m 2*u 0 1 i*u 2 1 k)*(m 4*u 0 2 i*u 3 2 l) -
    (m 0*u 0 0 i*u 1 0 j)*(m 3*u 1 1 j*u 3 1 l)*(m 5*u 1 2 j*u 2 2 k) -
    (m 1*u 2 0 k*u 3 0 l)*(m 2*u 0 1 i*u 2 1 k)*(m 5*u 1 2 j*u 2 2 k) -
    (m 1*u 2 0 k*u 3 0 l)*(m 3*u 1 1 j*u 3 1 l)*(m 4*u 0 2 i*u 3 2 l)
  have hpoint (i j k l) : F i j k l ≤ 2 := by
    apply classical_bound
    all_goals exact mul_contract (mul_contract (hm _) (hu _ _ _)) (hu _ _ _)
  have hb := avg4_le (p 0) (p 1) (p 2) (p 3) (hp 0) (hp 1) (hp 2) (hp 3)
    F (fun _ _ _ _ => 2) hpoint
  have hc : avg4 (p 0) (p 1) (p 2) (p 3) (fun _ _ _ _ => 2) = 2 := by
    have h := avg4_prod (p 0) (p 1) (p 2) (p 3)
      (fun _ => (2:ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    simpa [avg, ← Finset.sum_mul, hn] using h
  have monomial (α : ℝ) (f g h v : Ω → ℝ) :
      avg4 (p 0) (p 1) (p 2) (p 3) (fun i j k l => α*f i*g j*h k*v l) =
      α*avg (p 0) f*avg (p 1) g*avg (p 2) h*avg (p 3) v := by
    have hprod := avg4_prod (p 0) (p 1) (p 2) (p 3)
      (fun i => α*f i) g h v
    have havg : avg (p 0) (fun i => α*f i) = α*avg (p 0) f := by
      unfold avg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      ring
    rw [havg] at hprod
    exact hprod
  have he : avg4 (p 0) (p 1) (p 2) (p 3) F = witness m (triple p u) := by
    let f0 := fun i => u 0 0 i*u 0 1 i*u 0 2 i
    let f1 := fun i => u 1 0 i*u 1 1 i*u 1 2 i
    let f2 := fun i => u 2 0 i*u 2 1 i*u 2 2 i
    let f3 := fun i => u 3 0 i*u 3 1 i*u 3 2 i
    have hfun : F = fun i j k l =>
        (m 0*m 2*m 4)*f0 i*u 1 0 j*u 2 1 k*u 3 2 l -
        (m 0*m 3*m 5)*u 0 0 i*f1 j*u 2 2 k*u 3 1 l -
        (m 1*m 2*m 5)*u 0 1 i*u 1 2 j*f2 k*u 3 0 l -
        (m 1*m 3*m 4)*u 0 2 i*u 1 1 j*u 2 0 k*f3 l := by
      funext i j k l
      dsimp [F,f0,f1,f2,f3]
      ring
    rw [hfun]
    have subavg (f g : Ω → Ω → Ω → Ω → ℝ) :
        avg4 (p 0) (p 1) (p 2) (p 3) (fun i j k l => f i j k l - g i j k l) =
        avg4 (p 0) (p 1) (p 2) (p 3) f - avg4 (p 0) (p 1) (p 2) (p 3) g := by
      unfold avg4
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [subavg, subavg, subavg, monomial, monomial, monomial, monomial]
    rw [hme 1 0, hme 2 1, hme 3 2, hme 0 0, hme 2 2, hme 3 1,
      hme 0 1, hme 1 2, hme 3 0, hme 0 2, hme 1 1, hme 2 0]
    norm_num [edge, witness, triple, f0, f1, f2, f3]
    ring
  rw [he, hc] at hb
  exact hb


/-- Absolute version; reversing the first output in every context negates the witness. -/
theorem table_abs_bound
    (p : Fin 4 → Ω → ℝ) (u : Fin 4 → Fin 3 → Ω → ℝ) (m : Fin 6 → ℝ)
    (hp : ∀ v i, 0 ≤ p v i) (hn : ∀ v, ∑ i, p v i = 1)
    (hu : ∀ v j i, -1 ≤ u v j i ∧ u v j i ≤ 1)
    (hm : ∀ e, -1 ≤ m e ∧ m e ≤ 1)
    (hme : ∀ v j, avg (p v) (u v j) = m (edge v j)) :
    |witness m (triple p u)| ≤ 2 := by
  have upper := table_bound p u m hp hn hu hm hme
  let u' : Fin 4 → Fin 3 → Ω → ℝ := fun v j i => if j = 0 then -u v j i else u v j i
  let m' : Fin 6 → ℝ := fun e => if e = 0 ∨ e = 1 then -m e else m e
  have hu' (v j i) : -1 ≤ u' v j i ∧ u' v j i ≤ 1 := by
    dsimp [u']; split
    · constructor <;> linarith [(hu v j i).1, (hu v j i).2]
    · exact hu v j i
  have hm' (e) : -1 ≤ m' e ∧ m' e ≤ 1 := by
    dsimp [m']; split
    · constructor <;> linarith [(hm e).1, (hm e).2]
    · exact hm e
  have hme' (v j) : avg (p v) (u' v j) = m' (edge v j) := by
    fin_cases v <;> fin_cases j <;>
      simp [u', m', edge, avg, mul_neg, Finset.sum_neg_distrib] at *
    all_goals first | exact hme _ _ | exact congrArg Neg.neg (hme _ _)
  have lower := table_bound p u' m' hp hn hu' hm' hme'
  have negation : witness m' (triple p u') = -witness m (triple p u) := by
    simp [witness, triple, avg, u', m', mul_neg, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [negation] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩

/-- Odd moment combinations for simultaneous opposite-outcome pairs. -/
def odd (a b c t : ℝ) : Fin 4 → ℝ := ![a+b+c+t, a+b-c-t, a-b+c-t, a-b-c+t]

/-- Even combinations of the three pair moments. -/
def even (d e f : ℝ) : Fin 4 → ℝ := ![1+d+e+f, 1+d-e-f, 1-d+e-f, 1-d-e+f]

/-- Eight product-effect positivity rows, paired with their simultaneous opposites. -/
def positiveRows (a b c t d e f : ℝ) : Prop :=
  ∀ i, 0 ≤ even d e f i + odd a b c t i ∧ 0 ≤ even d e f i - odd a b c t i

/-- Exact elimination of all three pair moments from one positive context table. -/
theorem eliminate_pairs (a b c t : ℝ) :
    (∃ d e f, positiveRows a b c t d e f) ↔ ∑ i, |odd a b c t i| ≤ 4 := by
  constructor
  · rintro ⟨d,e,f,h⟩
    have hb (i) : |odd a b c t i| ≤ even d e f i := by
      apply abs_le.mpr
      constructor <;> linarith [(h i).1, (h i).2]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
    have he : ∑ i, even d e f i = 4 := by simp [even, Fin.sum_univ_succ]; ring
    rwa [he] at hs
  · intro h
    let H : Fin 4 → ℝ := fun i => |odd a b c t i| + (4 - ∑ j, |odd a b c t j|)/4
    have hH (i) : |odd a b c t i| ≤ H i := by dsimp [H]; linarith
    have hsum : H 0 + H 1 + H 2 + H 3 = 4 := by
      dsimp [H]
      simp [Fin.sum_univ_succ]
      ring
    let d := (H 0+H 1-H 2-H 3)/4
    let e := (H 0-H 1+H 2-H 3)/4
    let f := (H 0-H 1-H 2+H 3)/4
    have he (i) : even d e f i = H i := by
      fin_cases i <;> dsimp [even,d,e,f] <;> linarith
    refine ⟨d,e,f,?_⟩
    intro i
    rw [he]
    constructor <;> linarith [hH i, le_abs_self (odd a b c t i), neg_le_abs (odd a b c t i)]


end D5.S3.QuantumBounds.LocalPerceptionMermin
