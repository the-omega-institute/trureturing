/- GID: D5/S3/Estimation/TimeArrow/NativeMarkedCountComparison
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeMarkedCountComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A coefficient mass invariant bounds every native joint signal-count event against independent categorical increments. -/

import D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient
import Mathlib.Algebra.MvPolynomial.Funext

open Finset MvPolynomial
open scoped Classical
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open D5.S3.Estimation.TimeArrow.ForwardMarkedPathTransfer

set_option autoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
variable {ι : Type*}

private def massNorm (p : MvPolynomial ι ℂ) : ℝ := p.coeff.sum fun _ c => ‖c‖

private theorem mass_norm_eq_sum (p : MvPolynomial ι ℂ) (t : Finset (ι →₀ ℕ))
    (h : p.support ⊆ t) : massNorm p = ∑ d ∈ t, ‖p.coeff d‖ := by
  classical
  rw [massNorm, MvPolynomial.sum_def]
  exact sum_subset h (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.mp hd])

private theorem mass_norm_nonneg (p : MvPolynomial ι ℂ) : 0 ≤ massNorm p := by
  classical
  exact sum_nonneg fun _ _ => norm_nonneg _

private theorem mass_norm_monomial (d : ι →₀ ℕ) (c : ℂ) :
    massNorm (monomial d c) = ‖c‖ := by
  simp [massNorm]

private theorem mass_norm_zero : massNorm (0 : MvPolynomial ι ℂ) = 0 := by
  simp [massNorm]

private theorem mass_norm_add (p q : MvPolynomial ι ℂ) :
    massNorm (p+q) ≤ massNorm p + massNorm q := by
  classical
  let t := p.support ∪ q.support
  rw [mass_norm_eq_sum (p+q) t MvPolynomial.support_add,
    mass_norm_eq_sum p t subset_union_left, mass_norm_eq_sum q t subset_union_right,
    ← sum_add_distrib]
  exact sum_le_sum fun d _ => by simpa using norm_add_le (p.coeff d) (q.coeff d)

private theorem mass_norm_neg (p : MvPolynomial ι ℂ) : massNorm (-p) = massNorm p := by
  classical
  rw [mass_norm_eq_sum (-p) p.support (by simp),
    mass_norm_eq_sum p p.support (fun _ h => h)]
  simp

private theorem mass_norm_sub (p q : MvPolynomial ι ℂ) :
    massNorm (p-q) ≤ massNorm p + massNorm q := by
  simpa [sub_eq_add_neg, mass_norm_neg] using mass_norm_add p (-q)

private theorem mass_norm_sum {α : Type*} (t : Finset α) (p : α → MvPolynomial ι ℂ) :
    massNorm (∑ i ∈ t, p i) ≤ ∑ i ∈ t, massNorm (p i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [mass_norm_zero]
  | @insert a t ha ih =>
    simp only [sum_insert ha]
    exact (mass_norm_add _ _).trans (add_le_add le_rfl ih)

private theorem mass_norm_mul (p q : MvPolynomial ι ℂ) :
    massNorm (p*q) ≤ massNorm p * massNorm q := by
  classical
  rw [MvPolynomial.mul_def]
  simp only [Finsupp.sum]
  refine (mass_norm_sum _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ p.coeff.support, ∑ e ∈ q.coeff.support, ‖p.coeff d‖ * ‖q.coeff e‖ := by
      apply sum_le_sum
      intro d _
      exact (mass_norm_sum _ _).trans_eq (by simp [mass_norm_monomial])
    _ = _ := by
      simp only [massNorm, Finsupp.sum, sum_mul, mul_sum]
      rw [sum_comm]

private def state (A B : MvPolynomial ι ℂ) : ℕ → MvPolynomial ι ℂ × MvPolynomial ι ℂ
  | 0 => (1,0)
  | n+1 => ((1+A)*(state A B n).1 + A*(state A B n).2,
      B*(state A B n).1 + B*(state A B n).2)

private theorem feedback_norm (A B : MvPolynomial ι ℂ) (ρ β : ℝ)
    (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hβhalf : β ≤ 1/2) (hβρ : β ≤ 2*ρ)
    (hA : massNorm A ≤ 2*ρ) (hB : massNorm B ≤ β)
    (hP : massNorm (1+A) ≤ 1) (hx : ∀ n, massNorm (state A B n).1 ≤ 1) :
    ∀ n, massNorm (state A B n).2 ≤ 2*β ∧
      massNorm ((state A B n).1 - (1+A)^n) ≤ 8*n*ρ^2 := by
  intro n
  induction n with
  | zero => simp [state, mass_norm_zero]; positivity
  | succ n ih =>
    have hy : massNorm (state A B (n+1)).2 ≤ 2*β := by
      change massNorm (B*(state A B n).1 + B*(state A B n).2) ≤ _
      calc
        _ ≤ massNorm (B*(state A B n).1) + massNorm (B*(state A B n).2) := mass_norm_add _ _
        _ ≤ β * 1 + β * (2*β) := add_le_add
          ((mass_norm_mul _ _).trans (mul_le_mul hB (hx n) (mass_norm_nonneg _) hβ))
          ((mass_norm_mul _ _).trans (mul_le_mul hB ih.1 (mass_norm_nonneg _) hβ))
        _ ≤ 2*β := by nlinarith
    refine ⟨hy, ?_⟩
    have he : (state A B (n+1)).1 - (1+A)^(n+1) =
        (1+A)*((state A B n).1 - (1+A)^n) + A*(state A B n).2 := by
      simp only [state, pow_succ]
      ring
    rw [he]
    calc
      _ ≤ massNorm ((1+A)*((state A B n).1 - (1+A)^n)) +
          massNorm (A*(state A B n).2) := mass_norm_add _ _
      _ ≤ 1 * (8*n*ρ^2) + (2*ρ)*(2*β) := add_le_add
        ((mass_norm_mul _ _).trans (mul_le_mul hP ih.2 (mass_norm_nonneg _) (by norm_num)))
        ((mass_norm_mul _ _).trans (mul_le_mul hA ih.1 (mass_norm_nonneg _) (by positivity)))
      _ ≤ 8*((n+1 : ℕ) : ℝ)*ρ^2 := by push_cast; nlinarith



private theorem mass_norm_C (c : ℂ) : massNorm (C c : MvPolynomial ι ℂ) = ‖c‖ :=
  mass_norm_monomial 0 c

def rho (M q : ℕ) : ℝ := (q : ℝ)/(2*M)
def ap (M : ℕ) (r : ℝ) : ℝ := (1+r)/(4*M)
def am (M : ℕ) (r : ℝ) : ℝ := (1-r)/(4*M)

private def polyA (M q : ℕ) (r : ℝ) : MvPolynomial (Fin q ⊕ Fin q) ℂ :=
  C ((-rho M q : ℝ) : ℂ) + ∑ j : Fin q,
    (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ) +
     monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))

private def polyB (M q : ℕ) (r : ℝ) : MvPolynomial (Fin q ⊕ Fin q) ℂ :=
  C ((-r*rho M q : ℝ) : ℂ) + ∑ j : Fin q,
    (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ) -
     monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))

def nativeCounts {M q s : ℕ} (m : Fin q → Fin M) (o : Obs M s .path) :
    (Fin q ⊕ Fin q) → ℕ
  | .inl j => count .path o (m j) 1
  | .inr j => count .path o (m j) (-1)

private def lawPolynomial {Ω : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (N : Ω → ι → ℕ) : MvPolynomial ι ℂ :=
  ∑ o, monomial (Finsupp.equivFunOnFinite.symm (N o)) (w o : ℂ)

private def nativePolynomial {M q : ℕ} (r : ℝ) (S : Support M q)
    (m : Fin q → Fin M) (s : ℕ) : MvPolynomial (Fin q ⊕ Fin q) ℂ :=
  lawPolynomial (probability r .path S) (nativeCounts (s := s) m)

private theorem eval_lawPolynomial {Ω : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (N : Ω → ι → ℕ) (z : ι → ℂ) :
    eval z (lawPolynomial w N) = ∑ o, (w o : ℂ) * ∏ i, z i ^ N o i := by
  classical
  simp only [lawPolynomial, map_sum, eval_monomial]
  apply sum_congr rfl
  intro o _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

private theorem eval_nativePolynomial {M q : ℕ} (r : ℝ) (S : Support M q)
    (m : Fin q → Fin M) (s : ℕ) (z : (Fin q ⊕ Fin q) → ℂ) :
    eval z (nativePolynomial r S m s) = actualPGF r S m
      (fun j => z (.inl j)) (fun j => z (.inr j)) s := by
  classical
  rw [nativePolynomial, eval_lawPolynomial]
  simp only [actualPGF, Fintype.prod_sum_type, nativeCounts]
  apply sum_congr rfl
  intro o _
  rw [prod_mul_distrib]

private theorem eval_polyA {M q : ℕ} {r : ℝ} (hM : 0 < M)
    (S : Support M q) (m : Fin q → Fin M) (hmS : ∀ j, m j ∈ S.val)
    (z : (Fin q ⊕ Fin q) → ℂ) :
    eval z (polyA M q r) = driftA r S m (fun j => z (.inl j)) (fun j => z (.inr j)) := by
  classical
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [polyA, map_add, eval_C, map_sum, eval_monomial,
    Finsupp.prod_single_index, pow_zero, pow_one, driftA, tiltU, tiltV, b,
    ite_eq_left (hmS _)]
  have ht (j : Fin q) : (ap M r : ℂ)*z (.inl j)+(am M r : ℂ)*z (.inr j) =
      (((z (.inl j)+z (.inr j))/2-1) + (r:ℂ)*((z (.inl j)-z (.inr j))/2))/(2*M)
       + (1:ℂ)/(2*M) := by
    simp only [ap, am, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    field_simp
    ring
  simp_rw [ht]
  rw [sum_add_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div]
  simp only [rho, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast]
  ring

private theorem eval_polyB {M q : ℕ} {r : ℝ} (hM : 0 < M)
    (S : Support M q) (m : Fin q → Fin M) (hmS : ∀ j, m j ∈ S.val)
    (z : (Fin q ⊕ Fin q) → ℂ) :
    eval z (polyB M q r) = driftB r S m (fun j => z (.inl j)) (fun j => z (.inr j)) := by
  classical
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [polyB, map_add, map_sub, eval_C, map_sum, eval_monomial,
    Finsupp.prod_single_index, pow_zero, pow_one, driftB, tiltU, tiltV, b,
    ite_eq_left (hmS _)]
  have ht (j : Fin q) : (ap M r : ℂ)*z (.inl j)-(am M r : ℂ)*z (.inr j) =
      (((z (.inl j)-z (.inr j))/2) + (r:ℂ)*((z (.inl j)+z (.inr j))/2-1))/(2*M)
       + (r:ℂ)/(2*M) := by
    simp only [ap, am, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    field_simp
    ring
  simp_rw [ht]
  rw [sum_add_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div]
  simp only [rho, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast]
  ring

private theorem eval_state (A B : MvPolynomial ι ℂ) (z : ι → ℂ) (n : ℕ) :
    eval z (state A B n).1 = (forwardState (eval z A) (eval z B) n).1 ∧
    eval z (state A B n).2 = (forwardState (eval z A) (eval z B) n).2 := by
  induction n with
  | zero => simp [state, forwardState]
  | succ n ih =>
    simp only [state, map_add, map_mul, map_one]
    simp only [ih.1, ih.2]
    simp [forwardState]

private theorem native_polynomial_transfer {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (hm : Function.Injective m) (hmS : ∀ j, m j ∈ S.val) (s : ℕ) :
    nativePolynomial r S m s = (state (polyA M q r) (polyB M q r) s).1 := by
  apply MvPolynomial.funext
  intro z
  rw [eval_nativePolynomial, (eval_state _ _ _ _).1,
    eval_polyA (by omega) S m hmS, eval_polyB (by omega) S m hmS]
  exact (actual_marked_path_transfer hq hqm hr hr1 hc1 S m hm _ _).1

private theorem native_polynomial_norm {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (s : ℕ) : massNorm (nativePolynomial r S m s) ≤ 1 := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hn := (finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 .path).2.1.2 S
  have hp := (finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 .path).2.1.1 S
  unfold nativePolynomial lawPolynomial
  refine (mass_norm_sum _ _).trans_eq ?_
  simp only [mass_norm_monomial, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp _)]
  exact hn



private theorem parameter_bounds {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) :
    0 ≤ rho M q ∧ rho M q ≤ 1 ∧
      0 ≤ (1+r)*rho M q ∧ (1+r)*rho M q ≤ 1/2 ∧
      (1+r)*rho M q ≤ 2*rho M q ∧
      massNorm (polyA M q r) ≤ 2*rho M q ∧
      massNorm (polyB M q r) ≤ (1+r)*rho M q ∧
      massNorm (1+polyA M q r) ≤ 1 := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hp : 0 ≤ ap M r := by unfold ap; positivity
  have hm : 0 ≤ am M r := by unfold am; positivity
  have hρ : 0 ≤ rho M q := by unfold rho; positivity
  have hsum : (q : ℝ) * (ap M r + am M r) = rho M q := by
    unfold ap am rho
    field_simp
    ring
  have hρ1 : rho M q ≤ 1 := by
    rw [rho, div_le_iff₀ (by positivity)]
    have : (q : ℝ) < M := by exact_mod_cast hqm
    linarith
  have hcp : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast (show 0 < M-q by omega)
  have hcomp : r*q < (M-q : ℕ) := (div_lt_one hcp).mp hc1
  have hsub : ((M-q : ℕ) : ℝ) = (M : ℝ)-q := by rw [Nat.cast_sub hqm.le]
  rw [hsub] at hcomp
  have hβ0 : 0 ≤ (1+r)*rho M q := by positivity
  have hβhalf : (1+r)*rho M q ≤ 1/2 := by
    unfold rho
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2*M)]
    nlinarith
  have hβρ : (1+r)*rho M q ≤ 2*rho M q := by nlinarith
  have hsplus : massNorm (∑ j : Fin q,
      (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ) +
       monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))) ≤ rho M q := by
    refine (mass_norm_sum _ _).trans ?_
    calc
      _ ≤ ∑ _j : Fin q, (ap M r + am M r) := by
        apply sum_le_sum
        intro j _
        simpa only [mass_norm_monomial, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hp, abs_of_nonneg hm] using mass_norm_add
            (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ))
            (monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))
      _ = _ := by simpa [mul_add] using hsum
  have hsminus : massNorm (∑ j : Fin q,
      (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ) -
       monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))) ≤ rho M q := by
    refine (mass_norm_sum _ _).trans ?_
    calc
      _ ≤ ∑ _j : Fin q, (ap M r + am M r) := by
        apply sum_le_sum
        intro j _
        simpa only [mass_norm_monomial, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hp, abs_of_nonneg hm] using mass_norm_sub
            (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ))
            (monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ))
      _ = _ := by simpa [mul_add] using hsum
  have hA : massNorm (polyA M q r) ≤ 2*rho M q := by
    unfold polyA
    refine (mass_norm_add _ _).trans ?_
    rw [mass_norm_C, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hρ]
    linarith
  have hB : massNorm (polyB M q r) ≤ (1+r)*rho M q := by
    unfold polyB
    refine (mass_norm_add _ _).trans ?_
    rw [mass_norm_C, Complex.norm_real, Real.norm_eq_abs,
      neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hr.le hρ)]
    nlinarith
  have hP : massNorm (1+polyA M q r) ≤ 1 := by
    have he : 1+polyA M q r = C ((1-rho M q : ℝ) : ℂ) + ∑ j : Fin q,
        (monomial (Finsupp.single (Sum.inl j : Fin q ⊕ Fin q) 1) (ap M r : ℂ) +
         monomial (Finsupp.single (Sum.inr j : Fin q ⊕ Fin q) 1) (am M r : ℂ)) := by
      simp only [polyA, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one,
        map_neg, map_sub, map_one]
      ring
    rw [he]
    refine (mass_norm_add _ _).trans ?_
    rw [mass_norm_C, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  exact ⟨hρ,hρ1,hβ0,hβhalf,hβρ,hA,hB,hP⟩

private theorem native_coefficient_comparison {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (hm : Function.Injective m) (hmS : ∀ j, m j ∈ S.val) (s : ℕ) :
    massNorm (nativePolynomial r S m s - (1+polyA M q r)^s) ≤
      8*(s:ℝ)*(rho M q)^2 := by
  obtain ⟨hρ,_,hβ,hβhalf,hβρ,hA,hB,hP⟩ := parameter_bounds hq hqm hr hr1 hc1
  have hx (n : ℕ) : massNorm (state (polyA M q r) (polyB M q r) n).1 ≤ 1 := by
    rw [← native_polynomial_transfer hq hqm hr hr1 hc1 S m hm hmS n]
    exact native_polynomial_norm hq hqm hr hr1 hc1 S m n
  rw [native_polynomial_transfer hq hqm hr hr1 hc1 S m hm hmS s]
  exact (feedback_norm _ _ _ _ hρ hβ hβhalf hβρ hA hB hP hx s).2

private def eventFunctional (E : Set (ι → ℕ)) : MvPolynomial ι ℂ →+ ℂ where
  toFun p := p.coeff.sum fun d c => if (fun i => d i) ∈ E then c else 0
  map_zero' := by simp
  map_add' p q := by
    change (p.coeff+q.coeff).sum _ = _
    rw [Finsupp.sum_add_index']
    · intro d; simp
    · intro d a b; split_ifs <;> simp

private theorem event_monomial (E : Set (ι → ℕ)) (d : ι →₀ ℕ) (c : ℂ) :
    eventFunctional E (monomial d c) = if (fun i => d i) ∈ E then c else 0 := by
  change (Finsupp.single d c).sum (fun e v => if (fun i => e i) ∈ E then v else (0:ℂ)) = _
  exact Finsupp.sum_single_index (by split_ifs <;> rfl)

private theorem event_norm_le (E : Set (ι → ℕ)) (p : MvPolynomial ι ℂ) :
    ‖eventFunctional E p‖ ≤ massNorm p := by
  classical
  change ‖∑ d ∈ p.coeff.support, if (fun i => d i) ∈ E then p.coeff d else 0‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro d _
  split_ifs <;> simp

private theorem event_lawPolynomial {Ω : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (N : Ω → ι → ℕ) (E : Set (ι → ℕ)) :
    eventFunctional E (lawPolynomial w N) = ((∑ o, if N o ∈ E then w o else 0 : ℝ) : ℂ) := by
  classical
  simp only [lawPolynomial, map_sum, event_monomial, Complex.ofReal_sum]
  apply sum_congr rfl
  intro o _
  change (if N o ∈ E then (w o:ℂ) else 0) = _
  split_ifs <;> simp

def incrementExponent (i : Option ι) : ι →₀ ℕ :=
  match i with | none => 0 | some j => Finsupp.single j 1

def referenceIncrement (M q : ℕ) (r : ℝ) : Option (Fin q ⊕ Fin q) → ℝ
  | none => 1-rho M q
  | some (.inl _) => ap M r
  | some (.inr _) => am M r

def referenceCounts {s : ℕ} (o : Fin s → Option ι) : ι → ℕ :=
  fun i => (∑ t, incrementExponent (o t)) i

def referenceWeight {q s : ℕ} (M : ℕ) (r : ℝ)
    (o : Fin s → Option (Fin q ⊕ Fin q)) : ℝ := ∏ t, referenceIncrement M q r (o t)

private theorem reference_polynomial {M q s : ℕ} (r : ℝ) :
    lawPolynomial (referenceWeight (s := s) M r) referenceCounts = (1+polyA M q r)^s := by
  classical
  have hd (o : Fin s → Option (Fin q ⊕ Fin q)) :
      Finsupp.equivFunOnFinite.symm (referenceCounts o) = ∑ t, incrementExponent (o t) := by
    ext i
    simp [referenceCounts]
  unfold lawPolynomial
  simp_rw [hd]
  simp only [referenceWeight, Complex.ofReal_prod]
  simp_rw [MvPolynomial.monomial_sum_prod]
  rw [← Fintype.prod_sum (fun (_ : Fin s) (i : Option (Fin q ⊕ Fin q)) =>
    monomial (incrementExponent i) (referenceIncrement M q r i : ℂ))]
  have hs : (∑ i : Option (Fin q ⊕ Fin q),
      monomial (incrementExponent i) (referenceIncrement M q r i : ℂ)) = 1+polyA M q r := by
    simp only [Fintype.sum_option, Fintype.sum_sum_type, incrementExponent,
      referenceIncrement, ← sum_add_distrib, polyA, monomial_zero',
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg, map_sub, map_neg, map_one]
    ring
  simp_rw [hs]
  simp

/-- The native path's entire vector of support-row counts differs on every event
from the counts of s independent categorical increments by at most 8 s (q/(2M))². -/
theorem native_joint_count_comparison {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (hm : Function.Injective m) (hmS : ∀ j, m j ∈ S.val)
    (E : Set ((Fin q ⊕ Fin q) → ℕ)) :
    |(∑ o : Obs M s .path, if nativeCounts m o ∈ E then probability r .path S o else 0) -
      (∑ o : Fin s → Option (Fin q ⊕ Fin q),
        if referenceCounts o ∈ E then referenceWeight M r o else 0)| ≤
      8*(s:ℝ)*(rho M q)^2 := by
  classical
  have h := (event_norm_le E (nativePolynomial r S m s - (1+polyA M q r)^s)).trans
    (native_coefficient_comparison hq hqm hr hr1 hc1 S m hm hmS s)
  rw [map_sub, ← reference_polynomial r, nativePolynomial,
    event_lawPolynomial, event_lawPolynomial, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
