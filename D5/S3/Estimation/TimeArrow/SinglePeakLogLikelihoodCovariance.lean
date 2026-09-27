/- GID: D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform single-peak paths have exact log-likelihood covariances and variance. -/
import D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open Finset
open D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
/-- The even one-step log-likelihood mean function. -/
def phi (u : ℝ) : ℝ := ((1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)) / 2
/-- The odd part of the weighted one-step log-likelihood. -/
def xi (u : ℝ) : ℝ := ((1 + u) * Real.log (1 + u) - (1 - u) * Real.log (1 - u)) / 2
/-- The even one-step log-likelihood second-moment function. -/
def psi (u : ℝ) : ℝ := ((1 + u) * Real.log (1 + u) ^ 2 + (1 - u) * Real.log (1 - u) ^ 2) / 2
/-- The uniform-start mass of a finite path under a transition kernel. -/
def pathWeight {X : Type*} [Fintype X] (P : X → X → ℝ) (s : ℕ) (x : Fin (s + 1) → X) : ℝ :=
  (1 / (Fintype.card X : ℝ)) * ∏ t : Fin s, P (x t.castSucc) (x t.succ)
/-- Expectation under the explicit uniform-start sum over all finite paths. -/
def pathExpectation {X : Type*} [Fintype X] (P : X → X → ℝ) (s : ℕ)
    (f : (Fin (s + 1) → X) → ℝ) : ℝ :=
  ∑ x : Fin (s + 1) → X, pathWeight P s x * f x
/-- The log-likelihood increment `log (|X| P(X_t,X_(t+1)))` on a finite path. -/
def logIncrement {X : Type*} [Fintype X] (chi : X → ℝ) (z : X) (r q : ℝ)
    {s : ℕ} (t : Fin s) (x : Fin (s + 1) → X) : ℝ :=
  Real.log ((Fintype.card X : ℝ) * kernel chi z r q (Fintype.card X) (x t.castSucc) (x t.succ))
/-- Covariance computed from the explicit finite-path expectation. -/
def pathCovariance {X : Type*} [Fintype X] (P : X → X → ℝ) (s : ℕ)
    (f g : (Fin (s + 1) → X) → ℝ) : ℝ :=
  pathExpectation P s (fun x ↦ f x * g x) - pathExpectation P s f * pathExpectation P s g
/-- Variance computed from the explicit finite-path expectation. -/
def pathVariance {X : Type*} [Fintype X] (P : X → X → ℝ) (s : ℕ) (f : (Fin (s + 1) → X) → ℝ) : ℝ :=
  pathCovariance P s f f
/-- The sum of all log-likelihood increments on a finite path. -/
def logLikelihoodSum {X : Type*} [Fintype X] (chi : X → ℝ) (z : X) (r q : ℝ)
    (s : ℕ) (x : Fin (s + 1) → X) : ℝ :=
  ∑ t : Fin s, logIncrement chi z r q t x
private def tailWeight {X : Type*} (P : X → X → ℝ) : (s : ℕ) → X → (Fin s → X) → ℝ
  | 0, _, _ => 1
  | s + 1, x, v => P x (v 0) * tailWeight P s (v 0) (Fin.tail v)
private def edgeSum {X : Type*} (L : X → X → ℝ) (s : ℕ) (x : X) (v : Fin s → X) : ℝ :=
  ∑ t : Fin s, L ((Fin.cons x v : Fin (s + 1) → X) t.castSucc) (v t)
private def conditionalMean {X : Type*} [Fintype X] (P L : X → X → ℝ) (s : ℕ) (x : X) : ℝ :=
  ∑ v : Fin s → X, tailWeight P s x v * edgeSum L s x v
private def conditionalSecond {X : Type*} [Fintype X] (P L : X → X → ℝ) (s : ℕ) (x : X) : ℝ :=
  ∑ v : Fin s → X, tailWeight P s x v * edgeSum L s x v ^ 2
private def markovStep {X : Type*} [Fintype X] (P : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ :=
  ∑ y, P x y * f y
private def iteratedStep {X : Type*} [Fintype X] (P : X → X → ℝ) : ℕ → (X → ℝ) → X → ℝ
  | 0, f => f
  | n + 1, f => markovStep P (iteratedStep P n f)
/-- Exact conditional means, lag covariances, and path-sum variance for a single peak. -/
theorem exact_single_peak_log_likelihood_covariances {X : Type*} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)) :
    let P := kernel chi z r q (Fintype.card X)
    let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    (∀ x, ∑ y, P x y * L x y = phi (profile chi z r q x)) ∧
    (∀ y, ∑ x, P x y * L x y = I + J * chi y) ∧
    (∀ n, pathExpectation P (n + 1)
      (fun x => logIncrement chi z r q (Fin.last n) x) = I) ∧
    pathCovariance P 2 (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q 1 x) = I * J ∧
    (∀ j, 2 ≤ j → pathCovariance P (j + 1) (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q (Fin.last j) x) = 0) ∧
    ∀ s, 1 ≤ s → pathVariance P s (logLikelihoodSum chi z r q s) =
      (s : ℝ) * v + 2 * ((s - 1 : ℕ) : ℝ) * I * J := by
  have tailWeight_eq_prod : ∀ (P : X → X → ℝ), ∀ (s : ℕ) (x : X)
      (v : Fin s → X), tailWeight P s x v = ∏ t : Fin s, P ((Fin.cons x v : Fin (s + 1) → X) t.castSucc)
      (v t) := by
    intro P
    intro s
    induction s with
    | zero => intro x v; simp [tailWeight]
    | succ s ih =>
        intro x v
        have hv : (Fin.cons (v 0) (Fin.tail v) : Fin (s + 1) → X) = v := Fin.cons_self_tail v
        rw [tailWeight, ih, hv, Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ, Fin.tail]
  have tail_mass : ∀ (P : X → X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1), ∀
      (s : ℕ) (x : X), ∑ v : Fin s → X, tailWeight P s x v = 1 := by
    intro P hrow
    intro s
    induction s with
    | zero => intro x; simp [tailWeight]
    | succ s ih =>
        intro x
        rw [← (Fin.consEquiv fun _ : Fin (s + 1) => X).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, tailWeight, Fin.cons_zero, Fin.tail_cons]
        simp_rw [← Finset.mul_sum, ih, mul_one]
        exact hrow x
  have conditional_moment_recursions : ∀ (P L : X → X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1),
      (∀ s x, conditionalMean P L (s + 1) x = ∑ y, P x y * (L x y + conditionalMean P L s y)) ∧
      (∀ s x, conditionalSecond P L (s + 1) x = ∑ y, P x y * (L x y ^ 2 + 2 * L x y * conditionalMean P L s y + conditionalSecond P L s y)) := by
    intro P L hrow
    classical
    constructor <;> intro s x
    · unfold conditionalMean
      rw [← (Fin.consEquiv fun _ : Fin (s + 1) => X).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, tailWeight, Fin.cons_zero, Fin.tail_cons,
        edgeSum, Fin.sum_univ_succ, Fin.castSucc_zero, Fin.cons_succ, Fin.castSucc_succ]
      apply sum_congr rfl
      intro y _
      let A : (Fin s → X) → ℝ := fun v ↦
        ∑ t, L ((Fin.cons y v : Fin (s + 1) → X) t.castSucc) (v t)
      change (∑ v, P x y * tailWeight P s y v * (L x y + A v)) =
        P x y * (L x y + ∑ v, tailWeight P s y v * A v)
      calc
        (∑ v, P x y * tailWeight P s y v * (L x y + A v)) =
            P x y * ∑ v, tailWeight P s y v * (L x y + A v) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro v _
          ring
        _ = P x y * (L x y * (∑ v, tailWeight P s y v) +
            ∑ v, tailWeight P s y v * A v) := by
          congr 1
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply sum_congr rfl
          intro v _
          ring
        _ = _ := by simp only [tail_mass P hrow, mul_one]
    · unfold conditionalSecond
      rw [← (Fin.consEquiv fun _ : Fin (s + 1) => X).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, tailWeight, Fin.cons_zero, Fin.tail_cons,
        edgeSum, Fin.sum_univ_succ, Fin.castSucc_zero, Fin.cons_succ, Fin.castSucc_succ]
      apply sum_congr rfl
      intro y _
      unfold conditionalMean
      let A : (Fin s → X) → ℝ := fun v ↦
        ∑ t, L ((Fin.cons y v : Fin (s + 1) → X) t.castSucc) (v t)
      change (∑ v, P x y * tailWeight P s y v * (L x y + A v) ^ 2) =
        P x y * (L x y ^ 2 + 2 * L x y * (∑ v, tailWeight P s y v * A v) +
          ∑ v, tailWeight P s y v * A v ^ 2)
      calc
        (∑ v, P x y * tailWeight P s y v * (L x y + A v) ^ 2) =
            P x y * ∑ v, tailWeight P s y v * (L x y + A v) ^ 2 := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro v _
          ring
        _ = P x y * (L x y ^ 2 * (∑ v, tailWeight P s y v) +
            2 * L x y * (∑ v, tailWeight P s y v * A v) +
            ∑ v, tailWeight P s y v * A v ^ 2) := by
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          apply sum_congr rfl
          intro v _
          ring
        _ = _ := by simp only [tail_mass P hrow, mul_one]
  have tail_last_edge : ∀ (P L : X → X → ℝ) (F : X → ℝ) (hF : ∀ x, F x = ∑ y, P x y * L x y), ∀
      (n : ℕ) (x : X), (∑ v : Fin (n + 1) → X, tailWeight P (n + 1) x v * L ((Fin.cons x v : Fin (n + 2) → X) (Fin.last n).castSucc) (v (Fin.last n))) = iteratedStep P n F x := by
    intro P L F hF
    classical
    intro n
    induction n with
    | zero =>
        intro x
        rw [← (Fin.consEquiv fun _ : Fin 1 => X).sum_comp, Fintype.sum_prod_type]
        simp [tailWeight, iteratedStep, hF]
    | succ n ih =>
        intro x
        rw [← (Fin.consEquiv fun _ : Fin (n + 2) => X).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, tailWeight, Fin.cons_zero, Fin.tail_cons]
        change (∑ y, ∑ w : Fin (n + 1) → X,
          P x y * tailWeight P (n + 1) y w *
            L ((Fin.cons y w : Fin (n + 2) → X) (Fin.last n).castSucc)
              (w (Fin.last n))) = _
        simp_rw [mul_assoc, ← Finset.mul_sum, ih]
        rfl
  have first_last_edge_moment : ∀ (P L : X → X → ℝ) (F R : X → ℝ)
      (hF : ∀ x, F x = ∑ y, P x y * L x y) (hR : ∀ y, R y = ∑ x, P x y * L x y)
      (n : ℕ), pathExpectation P (n + 2) (fun x => L (x 0) (x 1) * L (x (Fin.last (n + 1)).castSucc) (x (Fin.last (n + 1)).succ)) =
      (1 / (Fintype.card X : ℝ)) * ∑ y, R y * iteratedStep P n F y := by
    intro P L F R hF hR n
    classical
    unfold pathExpectation pathWeight
    rw [← (Fin.consEquiv fun _ : Fin (n + 3) => X).sum_comp, Fintype.sum_prod_type,
      mul_sum]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← tailWeight_eq_prod]
    let G : X → (Fin (n + 2) → X) → ℝ := fun x v ↦
      (1 / (Fintype.card X : ℝ)) * tailWeight P (n + 2) x v *
        (L x ((Fin.cons x v : Fin (n + 3) → X) 1) *
          L ((Fin.cons x v : Fin (n + 3) → X) (Fin.last (n + 1)).castSucc)
            (v (Fin.last (n + 1))))
    change (∑ x, ∑ v, G x v) = _
    have hsplit (x : X) : (∑ v, G x v) =
        ∑ p : X × (Fin (n + 1) → X), G x (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv fun _ : Fin (n + 2) => X).sum_comp (G x)).symm
    simp_rw [hsplit, Fintype.sum_prod_type]
    dsimp only [G]
    change (∑ x, ∑ y, ∑ w : Fin (n + 1) → X,
      (1 / (Fintype.card X : ℝ)) * (P x y * tailWeight P (n + 1) y w) *
        (L x y * L ((Fin.cons y w : Fin (n + 2) → X) (Fin.last n).castSucc)
          (w (Fin.last n)))) = _
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    rw [sum_comm]
    let A : (Fin (n + 1) → X) → ℝ := fun w ↦
      tailWeight P (n + 1) y w *
        L ((Fin.cons y w : Fin (n + 2) → X) (Fin.last n).castSucc) (w (Fin.last n))
    have hterm (w : Fin (n + 1) → X) (x : X) :
        (1 / (Fintype.card X : ℝ)) * (P x y * tailWeight P (n + 1) y w) *
            (L x y * L ((Fin.cons y w : Fin (n + 2) → X) (Fin.last n).castSucc)
              (w (Fin.last n))) =
          (1 / (Fintype.card X : ℝ)) * P x y * L x y * A w := by
      dsimp only [A]
      ring
    simp_rw [hterm]
    calc
      (∑ w, ∑ x, (1 / (Fintype.card X : ℝ)) * P x y * L x y * A w) =
          ∑ w, ((1 / (Fintype.card X : ℝ)) * A w) * (∑ x, P x y * L x y) := by
        apply sum_congr rfl
        intro w _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = ∑ w, ((1 / (Fintype.card X : ℝ)) * A w) * R y := by rw [hR]
      _ = (1 / (Fintype.card X : ℝ)) * R y * (∑ w, A w) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro w _
        ring
      _ = _ := by
        change (1 / (Fintype.card X : ℝ)) * R y *
          (∑ w, tailWeight P (n + 1) y w *
            L ((Fin.cons y w : Fin (n + 2) → X) (Fin.last n).castSucc)
              (w (Fin.last n))) = _
        rw [tail_last_edge P L F hF n y]
        ring
  have stationary_lag_statistics : ∀ (P L : X → X → ℝ) (F R : X → ℝ)
      (I J : ℝ) (hcard0 : (Fintype.card X : ℝ) ≠ 0) (hrow : ∀ x, ∑ y, P x y = 1)
      (hcol : ∀ y, ∑ x, P x y = 1) (hF : ∀ x, ∑ y, P x y * L x y = F x)
      (hR : ∀ y, ∑ x, P x y * L x y = R y) (hP2 : ∀ x w, ∑ y, P x y * P y w = 1 / (Fintype.card X : ℝ))
      (hsumF : (∑ x, F x) = (Fintype.card X : ℝ) * I) (hsumR : (∑ x, R x) = (Fintype.card X : ℝ) * I)
      (hsumRF : (∑ x, R x * F x) = (Fintype.card X : ℝ) * (I ^ 2 + I * J))
      (hsumRPF : (∑ x, R x * (∑ y, P x y * F y)) = (Fintype.card X : ℝ) * I ^ 2),
      (∀ n, pathExpectation P (n + 1) (fun x => L (x (Fin.last n).castSucc) (x (Fin.last n).succ)) = I) ∧ pathCovariance P 2
      (fun x => L (x 0) (x 1)) (fun x => L (x 1) (x 2)) = I * J ∧ ∀ j, 2 ≤ j → pathCovariance P
      (j + 1) (fun x => L (x 0) (x 1)) (fun x => L (x (Fin.last j).castSucc) (x (Fin.last j).succ)) = 0 := by
    intro P L F R I J hcard0 hrow hcol hF hR hP2 hsumF hsumR hsumRF hsumRPF
    classical
    have hsumStep (f : X → ℝ) : ∑ x, markovStep P f x = ∑ x, f x := by
      unfold markovStep
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      calc
        (∑ x, P x y * f y) = (∑ x, P x y) * f y := by rw [Finset.sum_mul]
        _ = f y := by rw [hcol y, one_mul]
    have hsumIterated (n : ℕ) (f : X → ℝ) :
        ∑ x, iteratedStep P n f x = ∑ x, f x := by
      induction n with
      | zero => rfl
      | succ n ih =>
          simp only [iteratedStep]
          rw [hsumStep, ih]
    have hstepTwo (x : X) : markovStep P (markovStep P F) x = I := by
      unfold markovStep
      calc
        (∑ y, P x y * ∑ w, P y w * F w) =
            ∑ w, (∑ y, P x y * P y w) * F w := by
          simp_rw [Finset.mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro w _
          rw [Finset.sum_mul]
          apply sum_congr rfl
          intro y _
          ring
        _ = ∑ w, (1 / (Fintype.card X : ℝ)) * F w := by simp_rw [hP2]
        _ = (1 / (Fintype.card X : ℝ)) * ∑ w, F w := by rw [Finset.mul_sum]
        _ = I := by rw [hsumF]; field_simp
    have hiteratedConstant (n : ℕ) (x : X) : iteratedStep P (n + 2) F x = I := by
      induction n generalizing x with
      | zero => simpa [iteratedStep] using hstepTwo x
      | succ n ih =>
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, iteratedStep]
          unfold markovStep
          simp_rw [ih]
          rw [← Finset.sum_mul, hrow x, one_mul]
    have hfirstConditional (n : ℕ) (x : X) :
        (∑ v : Fin (n + 1) → X, tailWeight P (n + 1) x v * L x (v 0)) = F x := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => X).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, tailWeight, Fin.cons_zero, Fin.tail_cons]
      calc
        (∑ y, ∑ w : Fin n → X, P x y * tailWeight P n y w * L x y) =
            ∑ y, (P x y * L x y) * (∑ w : Fin n → X, tailWeight P n y w) := by
          apply sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro w _
          ring
        _ = ∑ y, P x y * L x y := by simp_rw [tail_mass P hrow, mul_one]
        _ = F x := hF x
    have hfirstMean (n : ℕ) : pathExpectation P (n + 1)
        (fun x => L (x 0) (x 1)) = I := by
      unfold pathExpectation pathWeight
      rw [← (Fin.consEquiv fun _ : Fin (n + 2) => X).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← tailWeight_eq_prod]
      change (∑ x, ∑ v : Fin (n + 1) → X,
        ((1 / (Fintype.card X : ℝ)) * tailWeight P (n + 1) x v) * L x (v 0)) = I
      calc
        (∑ x, ∑ v : Fin (n + 1) → X,
            ((1 / (Fintype.card X : ℝ)) * tailWeight P (n + 1) x v) * L x (v 0)) =
            (1 / (Fintype.card X : ℝ)) *
              ∑ x, ∑ v : Fin (n + 1) → X, tailWeight P (n + 1) x v * L x (v 0) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro v _
          ring
        _ =
            (1 / (Fintype.card X : ℝ)) * ∑ x, F x := by
          congr 1
          apply sum_congr rfl
          intro x _
          exact hfirstConditional n x
        _ = I := by rw [hsumF]; field_simp
    have hlastMean (n : ℕ) : pathExpectation P (n + 1)
        (fun x => L (x (Fin.last n).castSucc) (x (Fin.last n).succ)) = I := by
      unfold pathExpectation pathWeight
      rw [← (Fin.consEquiv fun _ : Fin (n + 2) => X).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_succ]
      simp_rw [← tailWeight_eq_prod]
      change (∑ x, ∑ v : Fin (n + 1) → X,
        ((1 / (Fintype.card X : ℝ)) * tailWeight P (n + 1) x v) *
          L ((Fin.cons x v : Fin (n + 2) → X) (Fin.last n).castSucc)
            (v (Fin.last n))) = I
      calc
        (∑ x, ∑ v : Fin (n + 1) → X,
            ((1 / (Fintype.card X : ℝ)) * tailWeight P (n + 1) x v) *
              L ((Fin.cons x v : Fin (n + 2) → X) (Fin.last n).castSucc)
                (v (Fin.last n))) =
            (1 / (Fintype.card X : ℝ)) * ∑ x, ∑ v : Fin (n + 1) → X,
              tailWeight P (n + 1) x v *
                L ((Fin.cons x v : Fin (n + 2) → X) (Fin.last n).castSucc)
                  (v (Fin.last n)) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro v _
          ring
        _ =
            (1 / (Fintype.card X : ℝ)) * ∑ x, iteratedStep P n F x := by
          congr 1
          apply sum_congr rfl
          intro x _
          exact tail_last_edge P L F (fun x => (hF x).symm) n x
        _ = (1 / (Fintype.card X : ℝ)) * ∑ x, F x := by rw [hsumIterated]
        _ = I := by rw [hsumF]; field_simp
    have hadjacentMoment : pathExpectation P 2
        (fun x => L (x 0) (x 1) * L (x 1) (x 2)) = I ^ 2 + I * J := by
      calc
        pathExpectation P 2 (fun x => L (x 0) (x 1) * L (x 1) (x 2)) =
            (1 / (Fintype.card X : ℝ)) * ∑ y, R y * F y := by
          simpa [iteratedStep] using first_last_edge_moment P L F R
            (fun x => (hF x).symm) (fun y => (hR y).symm) 0
        _ = I ^ 2 + I * J := by rw [hsumRF]; field_simp
    have hadjacent : pathCovariance P 2 (fun x => L (x 0) (x 1))
        (fun x => L (x 1) (x 2)) = I * J := by
      unfold pathCovariance
      rw [hadjacentMoment, hfirstMean 1]
      rw [show pathExpectation P 2 (fun x => L (x 1) (x 2)) = I by
        simpa [Fin.last] using hlastMean 1]
      ring
    refine ⟨hlastMean, hadjacent, ?_⟩
    intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm 2 n]
    have hmoment : pathExpectation P (n + 2 + 1)
        (fun x => L (x 0) (x 1) *
          L (x (Fin.last (n + 2)).castSucc) (x (Fin.last (n + 2)).succ)) = I ^ 2 := by
      cases n with
      | zero =>
          calc
            pathExpectation P (0 + 2 + 1)
                (fun x => L (x 0) (x 1) *
                  L (x (Fin.last (0 + 2)).castSucc) (x (Fin.last (0 + 2)).succ)) =
                (1 / (Fintype.card X : ℝ)) *
                  ∑ y, R y * iteratedStep P 1 F y := by
              simpa using first_last_edge_moment P L F R
                (fun x => (hF x).symm) (fun y => (hR y).symm) 1
            _ = I ^ 2 := by
              simp only [iteratedStep, markovStep]
              rw [hsumRPF]
              field_simp
      | succ n =>
          calc
            pathExpectation P (n + 1 + 2 + 1)
                (fun x => L (x 0) (x 1) *
                  L (x (Fin.last (n + 1 + 2)).castSucc)
                    (x (Fin.last (n + 1 + 2)).succ)) =
                (1 / (Fintype.card X : ℝ)) *
                  ∑ y, R y * iteratedStep P (n + 2) F y := by
              simpa [Nat.add_assoc] using first_last_edge_moment P L F R
                (fun x => (hF x).symm) (fun y => (hR y).symm) (n + 2)
            _ = (1 / (Fintype.card X : ℝ)) * ∑ y, R y * I := by
              simp_rw [hiteratedConstant]
            _ = I ^ 2 := by rw [← Finset.sum_mul, hsumR]; field_simp
    have hcov : pathCovariance P (n + 2 + 1)
        (fun x => L (x 0) (x 1))
        (fun x => L (x (Fin.last (n + 2)).castSucc) (x (Fin.last (n + 2)).succ)) = 0 := by
      unfold pathCovariance
      rw [hmoment, hfirstMean (n + 2), hlastMean (n + 2)]
      ring
    exact hcov
  have stationary_path_sum_variance : ∀ (P L : X → X → ℝ) (F G R : X → ℝ)
      (I J v : ℝ) (hcard0 : (Fintype.card X : ℝ) ≠ 0) (hrow : ∀ x, ∑ y, P x y = 1)
      (hcol : ∀ y, ∑ x, P x y = 1) (hF : ∀ x, ∑ y, P x y * L x y = F x)
      (hG : ∀ x, ∑ y, P x y * L x y ^ 2 = G x) (hR : ∀ y, ∑ x, P x y * L x y = R y)
      (hP2 : ∀ x w, ∑ y, P x y * P y w = 1 / (Fintype.card X : ℝ))
      (hsumF : (∑ x, F x) = (Fintype.card X : ℝ) * I) (hsumG : (∑ x, G x) = (Fintype.card X : ℝ) * (v + I ^ 2))
      (hsumR : (∑ x, R x) = (Fintype.card X : ℝ) * I) (hsumRF : (∑ x, R x * F x) = (Fintype.card X : ℝ) * (I ^ 2 + I * J))
      (hsumRPF : (∑ x, R x * (∑ y, P x y * F y)) = (Fintype.card X : ℝ) * I ^ 2), ∀ s, 1 ≤ s → pathVariance P s
      (fun x => ∑ t : Fin s, L (x t.castSucc) (x t.succ)) = (s : ℝ) * v + 2 *
      ((s - 1 : ℕ) : ℝ) * I * J := by
    intro P L F G R I J v hcard0 hrow hcol hF hG hR hP2 hsumF hsumG hsumR hsumRF hsumRPF
    classical
    obtain ⟨hmeanRec, hsecondRec⟩ := conditional_moment_recursions P L hrow
    have hsumStep (f : X → ℝ) : ∑ x, markovStep P f x = ∑ x, f x := by
      unfold markovStep
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      calc
        (∑ x, P x y * f y) = (∑ x, P x y) * f y := by rw [Finset.sum_mul]
        _ = f y := by rw [hcol y, one_mul]
    have hmeanRec' (s : ℕ) (x : X) : conditionalMean P L (s + 1) x =
        F x + markovStep P (conditionalMean P L s) x := by
      rw [hmeanRec s x]
      unfold markovStep
      rw [← hF x, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro y _
      ring
    have hmeanZero (x : X) : conditionalMean P L 0 x = 0 := by simp [conditionalMean, edgeSum]
    have hmeanOne (x : X) : conditionalMean P L 1 x = F x := by
      rw [hmeanRec' 0 x]; simp [markovStep, hmeanZero]
    have hstepTwo (x : X) : markovStep P (markovStep P F) x = I := by
      unfold markovStep
      calc
        (∑ y, P x y * ∑ w, P y w * F w) =
            ∑ w, (∑ y, P x y * P y w) * F w := by
          simp_rw [Finset.mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro w _
          rw [Finset.sum_mul]
          apply sum_congr rfl
          intro y _
          ring
        _ = ∑ w, (1 / (Fintype.card X : ℝ)) * F w := by simp_rw [hP2]
        _ = (1 / (Fintype.card X : ℝ)) * ∑ w, F w := by rw [Finset.mul_sum]
        _ = I := by rw [hsumF]; field_simp
    have hmeanLong (n : ℕ) (x : X) : conditionalMean P L (n + 2) x =
        F x + markovStep P F x + (n : ℝ) * I := by
      induction n generalizing x with
      | zero =>
          rw [hmeanRec' 1 x]
          unfold markovStep
          simp_rw [hmeanOne]
          ring
      | succ n ih =>
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, hmeanRec' (n + 2) x]
          unfold markovStep
          simp_rw [ih]
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, hrow x, one_mul]
          change F x + (markovStep P F x + markovStep P (markovStep P F) x +
            (n : ℝ) * I) = _
          rw [hstepTwo]
          change F x + (markovStep P F x + I + (n : ℝ) * I) =
            F x + markovStep P F x + ((n + 1 : ℕ) : ℝ) * I
          push_cast
          ring
    have hcross (s : ℕ) (hs : 1 ≤ s) :
        (1 / (Fintype.card X : ℝ)) *
            ∑ x, R x * conditionalMean P L s x = (s : ℝ) * I ^ 2 + I * J := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
      cases n with
      | zero =>
          simp_rw [hmeanOne]
          rw [hsumRF]
          field_simp
          ring
      | succ n =>
          rw [show 1 + (n + 1) = n + 2 by omega]
          simp_rw [hmeanLong n]
          have hconst : (∑ x, R x * ((n : ℝ) * I)) =
              (Fintype.card X : ℝ) * I * ((n : ℝ) * I) := by rw [← Finset.sum_mul, hsumR]
          change (1 / (Fintype.card X : ℝ)) *
              ∑ x, R x * (F x + (∑ y, P x y * F y) + (n : ℝ) * I) = _
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [hsumRF, hsumRPF, hconst]
          field_simp
          push_cast
          ring
    have hcrossTerm (s : ℕ) : (∑ x, ∑ y, P x y * L x y * conditionalMean P L s y) =
          ∑ y, R y * conditionalMean P L s y := by
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      calc
        (∑ x, P x y * L x y * conditionalMean P L s y) =
            (∑ x, P x y * L x y) * conditionalMean P L s y := by
          rw [Finset.sum_mul]
        _ = R y * conditionalMean P L s y := by rw [hR y]
    have hsecondCarry (s : ℕ) : (∑ x, ∑ y, P x y * conditionalSecond P L s y) =
          ∑ y, conditionalSecond P L s y := by
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      calc
        (∑ x, P x y * conditionalSecond P L s y) =
            (∑ x, P x y) * conditionalSecond P L s y := by rw [Finset.sum_mul]
        _ = conditionalSecond P L s y := by rw [hcol y, one_mul]
    have hsecondRaw (s : ℕ) :
        (∑ x, conditionalSecond P L (s + 1) x) =
          (∑ x, G x) + 2 * (∑ y, R y * conditionalMean P L s y) +
            ∑ y, conditionalSecond P L s y := by
      calc
        (∑ x, conditionalSecond P L (s + 1) x) =
            ∑ x, ∑ y, P x y *
              (L x y ^ 2 + 2 * L x y * conditionalMean P L s y +
                conditionalSecond P L s y) := by simp_rw [hsecondRec]
        _ = ∑ x, ∑ y, (P x y * L x y ^ 2 +
            2 * (P x y * L x y * conditionalMean P L s y) +
            P x y * conditionalSecond P L s y) := by
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro y _
          ring
        _ = (∑ x, ∑ y, P x y * L x y ^ 2) +
            2 * (∑ x, ∑ y, P x y * L x y * conditionalMean P L s y) +
            (∑ x, ∑ y, P x y * conditionalSecond P L s y) := by
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
        _ = _ := by simp_rw [hG]; rw [hcrossTerm, hsecondCarry]
    have hsecondAverageRec (s : ℕ) :
        (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalSecond P L (s + 1) x =
          (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalSecond P L s x +
            (v + I ^ 2) + 2 * ((1 / (Fintype.card X : ℝ)) *
              ∑ x, R x * conditionalMean P L s x) := by
      rw [hsecondRaw, hsumG]
      field_simp
      ring
    have hsecondOne (x : X) : conditionalSecond P L 1 x = G x := by
      rw [hsecondRec 0 x]; simp [conditionalMean, conditionalSecond, edgeSum]; simpa using hG x
    have hsecondFormula (n : ℕ) :
        (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalSecond P L (n + 1) x =
          ((n + 1 : ℕ) : ℝ) ^ 2 * I ^ 2 + ((n + 1 : ℕ) : ℝ) * v +
            2 * (n : ℝ) * I * J := by
      induction n with
      | zero =>
          simp_rw [hsecondOne]
          rw [hsumG]
          field_simp
          ring
      | succ n ih =>
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, hsecondAverageRec (n + 1), ih,
            hcross (n + 1) (by omega)]
          push_cast
          ring
    have hmeanRaw (s : ℕ) : (∑ x, conditionalMean P L s x) =
        (Fintype.card X : ℝ) * ((s : ℝ) * I) := by
      induction s with
      | zero => simp [hmeanZero]
      | succ s ih =>
          simp_rw [hmeanRec' s]
          rw [Finset.sum_add_distrib, hsumF, hsumStep, ih]
          push_cast
          ring
    have pathMoments (s : ℕ) :
        pathExpectation P s (fun x => ∑ t : Fin s, L (x t.castSucc) (x t.succ)) =
          (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalMean P L s x ∧
        pathExpectation P s (fun x => (∑ t : Fin s, L (x t.castSucc) (x t.succ)) ^ 2) =
          (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalSecond P L s x := by
      constructor
      · unfold pathExpectation pathWeight conditionalMean edgeSum
        rw [← (Fin.consEquiv fun _ : Fin (s + 1) => X).sum_comp, Fintype.sum_prod_type, mul_sum]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_succ]
        simp_rw [← tailWeight_eq_prod]
        apply sum_congr rfl; intro x _
        rw [Finset.mul_sum]
        apply sum_congr rfl; intro v _; ring
      · unfold pathExpectation pathWeight conditionalSecond edgeSum
        rw [← (Fin.consEquiv fun _ : Fin (s + 1) => X).sum_comp, Fintype.sum_prod_type, mul_sum]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_succ]
        simp_rw [← tailWeight_eq_prod]
        apply sum_congr rfl; intro x _
        rw [Finset.mul_sum]
        apply sum_congr rfl; intro v _; ring
    intro s hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [Nat.add_comm 1 n]
    unfold pathVariance pathCovariance
    change pathExpectation P (n + 1) (fun x =>
        (∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) *
          ∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) -
        pathExpectation P (n + 1) (fun x => ∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) *
          pathExpectation P (n + 1) (fun x => ∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) = _
    have hmoments := pathMoments (n + 1)
    rw [show pathExpectation P (n + 1) (fun x =>
        (∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) *
          ∑ t : Fin (n + 1), L (x t.castSucc) (x t.succ)) =
        (1 / (Fintype.card X : ℝ)) * ∑ x, conditionalSecond P L (n + 1) x by
          simpa [pow_two] using hmoments.2,
      hmoments.1, hsecondFormula n, hmeanRaw]
    field_simp
    push_cast
    ring
  have single_peak_local_identities : ∀ (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1)
      (z : X) (hz : chi z = 1) (r q : ℝ) (M : ℕ) (hcard : Fintype.card X = 2 * M)
      (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
      (hq : q = r / ((M : ℝ) - 1)),
      let P := kernel chi z r q (Fintype.card X)
      let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
      let k := (M : ℝ) - 1
      let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
      let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
      let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
      let F := fun x => phi (profile chi z r q x)
      let G := fun x => psi (profile chi z r q x)
      let R := fun y => I + J * chi y
      (∀ x, ∑ y, P x y = 1) ∧ (∀ y, ∑ x, P x y = 1) ∧
      (∀ x, ∑ y, P x y * L x y = F x) ∧ (∀ x, ∑ y, P x y * L x y ^ 2 = G x) ∧
      (∀ y, ∑ x, P x y * L x y = R y) ∧
      (∀ x w, ∑ y, P x y * P y w = 1 / (Fintype.card X : ℝ)) ∧
      (∀ x, ∑ y, P x y * F y = I * (1 + profile chi z r q x)) ∧
      (∑ x, F x) = (Fintype.card X : ℝ) * I ∧ (∑ x, G x) = (Fintype.card X : ℝ) * (v + I ^ 2) ∧
      (∑ x, R x) = (Fintype.card X : ℝ) * I ∧
      (∑ x, R x * F x) = (Fintype.card X : ℝ) * (I ^ 2 + I * J) ∧
      (∑ x, R x * (∑ y, P x y * F y)) = (Fintype.card X : ℝ) * I ^ 2 := by
    intro chi hchi z hz r q M hcard hplus hM hq
    classical
    dsimp only
    let N : ℝ := Fintype.card X
    let k : ℝ := (M : ℝ) - 1
    let signR : Region → ℝ | Region.peak => 1 | Region.bulk => 1 | Region.opposite => -1
    let bR : Region → ℝ | Region.peak => r | Region.bulk => -q | Region.opposite => 0
    let P := kernel chi z r q (Fintype.card X)
    let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
    let I := (phi r + k * phi q) / N
    let J := (xi r - k * xi q) / N
    let v := (psi r + k * psi q) / N - I ^ 2
    let F := fun x => phi (profile chi z r q x)
    let G := fun x => psi (profile chi z r q x)
    let R := fun y => I + J * chi y
    have hN : N = 2 * (M : ℝ) := by norm_num [N, hcard]
    have hN0 : N ≠ 0 := by rw [hN]; positivity
    have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hden0 : (M : ℝ) - 1 ≠ 0 := by linarith
    have hbalance : r - k * q = 0 := by dsimp only [k]; rw [hq]; field_simp [hden0]; ring
    have hr : r = ((M : ℝ) - 1) * q := by dsimp only [k] at hbalance; linarith
    have hsign (x : X) : chi x = signR (region chi z x) := by
      by_cases hx : x = z
      · simp [region, signR, hx, hz]
      · rcases hchi x with h | h
        · simp [region, signR, hx, h]
        · norm_num [region, signR, hx, h]
    have hprofile (x : X) : profile chi z r q x = bR (region chi z x) := rfl
    have hregionCard (U : Region) : (((univ.filter fun x => region chi z x = U).card : ℕ) : ℝ) =
        match U with | Region.peak => 1 | Region.bulk => (M : ℝ) - 1 | Region.opposite => M := by
      cases U with
      | peak =>
          have hs : univ.filter (fun x => region chi z x = Region.peak) = {z} := by
            ext x
            simp only [mem_filter, mem_univ, true_and, mem_singleton]
            by_cases hx : x = z
            · simp [region, hx]
            · by_cases hp : chi x = 1 <;> simp [region, hx, hp]
          simp [hs]
      | bulk =>
          have hs : univ.filter (fun x => region chi z x = Region.bulk) =
              (univ.filter fun x => chi x = 1).erase z := by
            ext x
            simp only [mem_filter, mem_univ, true_and, mem_erase]
            by_cases hx : x = z
            · simp [region, hx, hz]
            · by_cases hp : chi x = 1 <;> simp [region, hx, hp]
          have hzmem : z ∈ (univ.filter fun x => chi x = 1) := by simp [hz]
          rw [hs, card_erase_of_mem hzmem, hplus, Nat.cast_sub (by omega : 1 ≤ M)]
          norm_num
      | opposite =>
          have hs : univ.filter (fun x => region chi z x = Region.opposite) =
              univ.filter (fun x => ¬ chi x = 1) := by
            ext x
            simp only [mem_filter, mem_univ, true_and]
            by_cases hx : x = z
            · simp [region, hx, hz]
            · by_cases hp : chi x = 1 <;> simp [region, hx, hp]
          have hc := card_filter_add_card_filter_not (s := (univ : Finset X))
            (p := fun x => chi x = 1)
          rw [card_univ, hplus, hcard] at hc
          have hm : (univ.filter fun x => ¬ chi x = 1).card = M := by omega
          simp [hs, hm]
    have hsumIndicator (U : Region) (c : ℝ) :
        (∑ x : X, if region chi z x = U then c else 0) =
          (match U with
            | Region.peak => 1
            | Region.bulk => (M : ℝ) - 1
            | Region.opposite => M) * c := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      rw [hregionCard]
    have hsumRegion (f : Region → ℝ) :
        (∑ x : X, f (region chi z x)) =
          f Region.peak + ((M : ℝ) - 1) * f Region.bulk + (M : ℝ) * f Region.opposite := by
      calc
        (∑ x : X, f (region chi z x)) =
            ∑ x : X, ((if region chi z x = Region.peak then f Region.peak else 0) +
              (if region chi z x = Region.bulk then f Region.bulk else 0) +
              (if region chi z x = Region.opposite then f Region.opposite else 0)) := by
          apply sum_congr rfl
          intro x _
          cases region chi z x <;> simp
        _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, hsumIndicator, hsumIndicator,
            hsumIndicator]
          ring
    have hPxy (x y : X) : P x y =
        (1 + signR (region chi z x) * signR (region chi z y) *
          bR (region chi z x)) / N := by
      dsimp only [P]
      rw [kernel, hsign x, hsign y, hprofile]
    have hLxy (x y : X) : L x y = Real.log
        (1 + signR (region chi z x) * signR (region chi z y) *
          bR (region chi z x)) := by
      dsimp only [L]
      rw [hPxy]
      congr 1
      field_simp
      ring
    have hrow : ∀ x, ∑ y, P x y = 1 := by
      intro x
      calc
        (∑ y, P x y) = ∑ y,
            (1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N := by simp_rw [hPxy]
        _ = ((1 + signR (region chi z x) * signR Region.peak * bR (region chi z x)) / N) +
            ((M : ℝ) - 1) *
              ((1 + signR (region chi z x) * signR Region.bulk * bR (region chi z x)) / N) +
            (M : ℝ) *
              ((1 + signR (region chi z x) * signR Region.opposite * bR (region chi z x)) / N) :=
          hsumRegion (fun V =>
            (1 + signR (region chi z x) * signR V * bR (region chi z x)) / N)
        _ = 1 := by
          rw [hN]
          cases region chi z x <;> simp [signR, bR] <;> field_simp <;> ring
    have hcol : ∀ y, ∑ x, P x y = 1 := by
      intro y
      calc
        (∑ x, P x y) = ∑ x,
            (1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N := by simp_rw [hPxy]
        _ = ((1 + signR Region.peak * signR (region chi z y) * bR Region.peak) / N) +
            ((M : ℝ) - 1) *
              ((1 + signR Region.bulk * signR (region chi z y) * bR Region.bulk) / N) +
            (M : ℝ) *
              ((1 + signR Region.opposite * signR (region chi z y) * bR Region.opposite) / N) :=
          hsumRegion (fun U =>
            (1 + signR U * signR (region chi z y) * bR U) / N)
        _ = 1 := by
          rw [hN]
          cases region chi z y <;> simp [signR, bR] <;> field_simp <;> nlinarith
    have hF : ∀ x, ∑ y, P x y * L x y = F x := by
      intro x
      calc
        (∑ y, P x y * L x y) = ∑ y,
            ((1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N) * Real.log
                (1 + signR (region chi z x) * signR (region chi z y) *
                  bR (region chi z x)) := by simp_rw [hPxy, hLxy]
        _ = _ := by
          let f : Region → ℝ := fun V =>
            ((1 + signR (region chi z x) * signR V * bR (region chi z x)) / N) *
              Real.log (1 + signR (region chi z x) * signR V * bR (region chi z x))
          change (∑ y, f (region chi z y)) = F x
          rw [hsumRegion f]
          dsimp only [f]
          dsimp only [F]
          rw [hprofile, hN]
          cases region chi z x <;> simp [signR, bR, phi] <;> field_simp <;> ring
    have hG : ∀ x, ∑ y, P x y * L x y ^ 2 = G x := by
      intro x
      calc
        (∑ y, P x y * L x y ^ 2) = ∑ y,
            ((1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N) * Real.log
                (1 + signR (region chi z x) * signR (region chi z y) *
                  bR (region chi z x)) ^ 2 := by simp_rw [hPxy, hLxy]
        _ = _ := by
          let f : Region → ℝ := fun V =>
            ((1 + signR (region chi z x) * signR V * bR (region chi z x)) / N) *
              Real.log (1 + signR (region chi z x) * signR V * bR (region chi z x)) ^ 2
          change (∑ y, f (region chi z y)) = G x
          rw [hsumRegion f]
          dsimp only [f]
          dsimp only [G]
          rw [hprofile, hN]
          cases region chi z x <;> simp [signR, bR, psi] <;> field_simp <;> ring
    have hR : ∀ y, ∑ x, P x y * L x y = R y := by
      intro y
      calc
        (∑ x, P x y * L x y) = ∑ x,
            ((1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N) * Real.log
                (1 + signR (region chi z x) * signR (region chi z y) *
                  bR (region chi z x)) := by simp_rw [hPxy, hLxy]
        _ = _ := by
          let f : Region → ℝ := fun U =>
            ((1 + signR U * signR (region chi z y) * bR U) / N) *
              Real.log (1 + signR U * signR (region chi z y) * bR U)
          change (∑ x, f (region chi z x)) = R y
          rw [hsumRegion f]
          dsimp only [f, R, I, J, k]
          rw [hsign y, hN]
          cases region chi z y <;> simp [signR, bR, phi, xi] <;> field_simp <;> ring
    have hP2 : ∀ x w, ∑ y, P x y * P y w = 1 / N := by
      intro x w
      calc
        (∑ y, P x y * P y w) = ∑ y,
            ((1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N) *
            ((1 + signR (region chi z y) * signR (region chi z w) *
              bR (region chi z y)) / N) := by simp_rw [hPxy]
        _ = _ := by
          let f : Region → ℝ := fun V =>
            ((1 + signR (region chi z x) * signR V * bR (region chi z x)) / N) *
              ((1 + signR V * signR (region chi z w) * bR V) / N)
          change (∑ y, f (region chi z y)) = 1 / N
          rw [hsumRegion f]
          dsimp only [f]
          rw [hN]
          cases region chi z x <;> cases region chi z w <;>
            simp [signR, bR, hr] <;> field_simp <;> ring
    have hPF : ∀ x, ∑ y, P x y * F y = I * (1 + profile chi z r q x) := by
      intro x
      calc
        (∑ y, P x y * F y) = ∑ y,
            ((1 + signR (region chi z x) * signR (region chi z y) *
              bR (region chi z x)) / N) * phi (bR (region chi z y)) := by
          apply sum_congr rfl
          intro y _
          rw [hPxy]
          simp only [F, hprofile]
        _ = _ := by
          let f : Region → ℝ := fun V =>
            ((1 + signR (region chi z x) * signR V * bR (region chi z x)) / N) * phi (bR V)
          change (∑ y, f (region chi z y)) = I * (1 + profile chi z r q x)
          rw [hsumRegion f]
          dsimp only [f, I, k]
          rw [hN]
          rw [hprofile]
          cases region chi z x <;> simp [signR, bR, phi] <;> field_simp <;> ring
    have hphiEven (u : ℝ) : phi (-u) = phi u := by simp [phi]; ring
    have hpsiEven (u : ℝ) : psi (-u) = psi u := by simp [psi]; ring
    have hphiZero : phi 0 = 0 := by simp [phi]
    have hpsiZero : psi 0 = 0 := by simp [psi]
    have hsumF : (∑ x, F x) = N * I := by
      dsimp only [F]; simp_rw [hprofile]
      rw [hsumRegion (fun U => phi (bR U))]
      dsimp only [bR, I, k]; rw [hphiEven, hphiZero]
      field_simp [hN0]; ring
    have hsumG : (∑ x, G x) = N * (v + I ^ 2) := by
      dsimp only [G]; simp_rw [hprofile]
      rw [hsumRegion (fun U => psi (bR U))]
      dsimp only [bR, v, I, k]; rw [hpsiEven, hpsiZero]
      field_simp [hN0]; ring
    have hsumR : (∑ x, R x) = N * I := by
      dsimp only [R]; simp_rw [hsign]
      rw [hsumRegion (fun U => I + J * signR U)]
      dsimp only [signR]; rw [hN]; ring
    have hsumRF : (∑ x, R x * F x) = N * (I ^ 2 + I * J) := by
      calc
        (∑ x, R x * F x) = ∑ x, (I + J) * F x := by
          apply sum_congr rfl
          intro x _
          dsimp only [R, F]
          rw [hsign x, hprofile x]
          cases region chi z x <;> simp [signR, bR, phi]
        _ = (I + J) * (∑ x, F x) := by rw [Finset.mul_sum]
        _ = N * (I ^ 2 + I * J) := by rw [hsumF]; ring
    have hsumRPF : (∑ x, R x * (∑ y, P x y * F y)) = N * I ^ 2 := by
      simp_rw [hPF]
      dsimp only [R]
      simp_rw [hsign, hprofile]
      rw [hsumRegion (fun U => (I + J * signR U) * (I * (1 + bR U)))]
      dsimp only [signR, bR]
      rw [hN, hr]
      ring
    exact ⟨hrow, hcol, hF, hG, hR, hP2, hPF, hsumF, hsumG, hsumR, hsumRF,
      hsumRPF⟩
  classical
  dsimp only
  let P := kernel chi z r q (Fintype.card X)
  let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
  let k := (M : ℝ) - 1
  let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
  let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
  let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
  let F := fun x => phi (profile chi z r q x)
  let G := fun x => psi (profile chi z r q x)
  let R := fun y => I + J * chi y
  have hcard0 : (Fintype.card X : ℝ) ≠ 0 := by rw [hcard]; positivity
  have hlocal := single_peak_local_identities chi hchi z hz r q M hcard hplus hM hq
  dsimp only at hlocal
  rcases hlocal with ⟨hrow, hcol, hF, hG, hR, hP2, hPF, hsumF, hsumG,
    hsumR, hsumRF, hsumRPF⟩
  have hlag := stationary_lag_statistics P L F R I J hcard0 hrow hcol hF hR hP2
    hsumF hsumR hsumRF hsumRPF
  have hvariance := stationary_path_sum_variance P L F G R I J v hcard0 hrow hcol hF
    hG hR hP2 hsumF hsumG hsumR hsumRF hsumRPF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F] using hF
  · simpa only [R] using hR
  · intro n
    simpa [P, L, I, k, logIncrement] using hlag.1 n
  · simpa [P, L, I, J, logIncrement, Fin.castSucc, Fin.succ] using hlag.2.1
  · intro j hj
    have hzero :
        (fun x : Fin (j + 2) → X => logIncrement chi z r q (0 : Fin (j + 1)) x) =
          (fun x => L (x 0) (x 1)) := by
      funext x
      have hcast : (Fin.castSucc (0 : Fin (j + 1)) : Fin (j + 2)) = 0 := Fin.ext (by rfl)
      have hsucc : (Fin.succ (0 : Fin (j + 1)) : Fin (j + 2)) = 1 := Fin.ext (by rfl)
      simp [logIncrement, L, P, hcast, hsucc]
    rw [hzero]
    simpa [P, L, logIncrement, Fin.castSucc, Fin.succ] using hlag.2.2 j hj
  · intro s hs
    have hsumEq : logLikelihoodSum chi z r q s =
        fun x => ∑ t : Fin s, L (x t.castSucc) (x t.succ) := by funext x; rfl
    rw [hsumEq]
    simpa [P, I, J, v, k] using hvariance s hs
example :
    let chi : Fin 4 → ℝ := fun x => if x.1 < 2 then 1 else -1
    (∀ x, chi x = 1 ∨ chi x = -1) ∧ chi 0 = 1 ∧
    Fintype.card (Fin 4) = 2 * 2 ∧ (univ.filter fun x => chi x = 1).card = 2 ∧
    2 ≤ 2 ∧ (1 / 2 : ℝ) = (1 / 2 : ℝ) / ((2 : ℝ) - 1) ∧
    0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by
  dsimp
  refine ⟨?_, by norm_num, by norm_num, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro x
    by_cases h : x.1 < 2
    · left; simp [h]
    · right; simp [h]
  · have hset : (univ.filter fun x : Fin 4 => (if x.1 < 2 then (1 : ℝ) else -1) = 1) =
        {0, 1} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      fin_cases x <;> norm_num
    rw [hset]
    decide
#print axioms exact_single_peak_log_likelihood_covariances
end D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
