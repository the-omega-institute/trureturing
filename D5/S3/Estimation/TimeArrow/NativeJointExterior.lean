/- GID: D5/S3/Estimation/TimeArrow/NativeJointExterior
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeJointExterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A native marked edge is independent of its entire joint exterior beyond radius two. -/

import D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

/-! Exact finite exterior cylinder factorization for the compensated native path. -/

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra

set_option autoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.NativeJointExterior

private theorem two_step {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q) (x y : Vertex M) :
    (∑ z : Vertex M, transition r S x z * transition r S z y) =
      (2 * (M : ℝ))⁻¹ := by
  have hb := profile_sum_zero hq hqm hr hr1 hc1 S
  have hχ : (∑ z : Vertex M, chi z) = 0 := by
    simp [Fintype.sum_sum_type, chi]
  have hχb : (∑ z : Vertex M, chi z * b r S z) = 0 := by
    simpa [Fintype.sum_sum_type, chi, b] using hb
  have hM : (2 * (M : ℝ)) ≠ 0 := by
    have : 0 < M := by omega
    positivity
  simp only [transition, div_mul_div_comm, ← sum_div]
  have he (z : Vertex M) :
      (1 + b r S x * chi z) * (1 + b r S z * chi y) =
      1 + b r S x * chi z + chi y * b r S z +
        (b r S x * chi y) * (chi z * b r S z) := by ring
  simp_rw [he, sum_add_distrib, ← mul_sum]
  rw [hχ, hb, hχb]
  simp only [mul_zero, add_zero, sum_const, card_univ, Fintype.card_sum,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  <;> ring

private def chainWeight {M q : ℕ} (r : ℝ) (S : Support M q)
    {a : ℕ} (u : Fin (a + 1) → Vertex M) : ℝ :=
  ∏ i : Fin a, transition r S (u i.castSucc) (u i.succ)

private theorem chainWeight_snoc {M q a : ℕ} (r : ℝ) (S : Support M q)
    (u : Fin (a + 1) → Vertex M) (x : Vertex M) :
    chainWeight r S (Fin.snoc u x) =
      chainWeight r S u * transition r S (u (Fin.last a)) x := by
  simp [chainWeight, Fin.prod_univ_castSucc, ← Fin.castSucc_succ]

private theorem chainWeight_cons {M q a : ℕ} (r : ℝ) (S : Support M q)
    (u : Fin (a + 1) → Vertex M) (x : Vertex M) :
    chainWeight r S (Fin.cons x u) =
      transition r S x (u 0) * chainWeight r S u := by
  simp [chainWeight, Fin.prod_univ_succ]

private theorem chainWeight_append {M q a b : ℕ} (r : ℝ) (S : Support M q)
    (u : Fin (a + 1) → Vertex M) (v : Fin (b + 1) → Vertex M) :
    chainWeight (a := (a + 1) + b) r S (Fin.append (m := a + 1) (n := b + 1) u v) =
      chainWeight r S u * transition r S (u (Fin.last a)) (v 0) *
        chainWeight r S v := by
  unfold chainWeight
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_castSucc]
  congr 2
  · apply Finset.prod_congr rfl
    intro i _
    congr 2 <;> simp [Fin.append, Fin.addCases, Fin.castLT, Fin.subNat] <;> rfl
  · simp [Fin.append, Fin.addCases, Fin.castLT, Fin.subNat]
    rfl
  · funext i
    rw [show (Fin.natAdd (a + 1) i).castSucc = Fin.natAdd (a + 1) i.castSucc from by rfl,
      show (Fin.natAdd (a + 1) i).succ = Fin.natAdd (a + 1) i.succ from by rfl]
    simp only [Fin.append_right]

private def leftRead {M a : ℕ} (u : Fin a → Vertex M) : Fin (a - 1) → Vertex M :=
  fun i => u ⟨i.val, by omega⟩

private def rightRead {M a : ℕ} (u : Fin a → Vertex M) : Fin (a - 1) → Vertex M :=
  fun i => u ⟨i.val+1, by omega⟩

private def leftFiber {M q a : ℕ} (r : ℝ) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (x : Vertex M) : ℝ := by
  classical
  exact ∑ u : Fin a → Vertex M,
    if leftRead u = l then chainWeight r S (Fin.snoc u x) else 0

private def rightFiber {M q a : ℕ} (r : ℝ) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (x : Vertex M) : ℝ := by
  classical
  exact ∑ u : Fin a → Vertex M,
    if rightRead u = l then chainWeight r S (Fin.cons x u) else 0

private theorem leftFiber_flat {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (a : ℕ) (l : Fin (a - 1) → Vertex M) (x y : Vertex M) :
    leftFiber r S l x = leftFiber r S l y := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcol := (finite_support_bayes (s := 0) hq hqm hr hr1 hc hc1 .path).1 S |>.2
  cases a with
  | zero => simp [leftFiber, chainWeight]
  | succ a =>
    cases a with
    | zero =>
      have hread (u : Fin 1 → Vertex M) : leftRead u = l := by
        ext i; exact Fin.elim0 i
      have hw (u : Fin 1 → Vertex M) (z : Vertex M) :
          chainWeight r S (Fin.snoc u z) = transition r S (u 0) z := by
        rw [chainWeight_snoc]
        simp [chainWeight]
      simp only [leftFiber, hread, ite_true, hw]
      rw [← (Fin.consEquiv (fun _ : Fin 1 => Vertex M)).sum_comp,
        ← (Fin.consEquiv (fun _ : Fin 1 => Vertex M)).sum_comp]
      simpa [Fin.consEquiv, Fintype.sum_prod_type] using (hcol x).trans (hcol y).symm
    | succ a =>
      have hf (z : Vertex M) : leftFiber r S l z =
          chainWeight r S l * (2 * (M : ℝ))⁻¹ := by
        unfold leftFiber
        rw [← (Fin.snocEquiv (fun _ : Fin (a + 2) => Vertex M)).sum_comp]
        simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk]
        have hread (u : Fin (a + 1) → Vertex M) (w : Vertex M) :
            leftRead (Fin.snoc u w) = u := by
          ext i
          change Fin.snoc (α := fun _ : Fin (a + 2) => Vertex M) u w i.castSucc = u i
          simp
        simp only [hread, chainWeight_snoc, Fin.snoc_last]
        rw [sum_comm]
        simp_rw [Finset.sum_ite_irrel]
        try simp only [sum_const_zero, sum_ite_eq', mem_univ, ite_true]
        simp_rw [mul_assoc, ← mul_sum]
        rw [two_step hq hqm hr hr1 hc1 S]
      exact (hf x).trans (hf y).symm

private theorem rightFiber_flat {M q : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (a : ℕ) (l : Fin (a - 1) → Vertex M) (x y : Vertex M) :
    rightFiber r S l x = rightFiber r S l y := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hrow := (finite_support_bayes (s := 0) hq hqm hr hr1 hc hc1 .path).1 S |>.1.2
  cases a with
  | zero => simp [rightFiber, chainWeight]
  | succ a =>
    cases a with
    | zero =>
      have hread (u : Fin 1 → Vertex M) : rightRead u = l := by
        ext i; exact Fin.elim0 i
      have hw (u : Fin 1 → Vertex M) (z : Vertex M) :
          chainWeight r S (Fin.cons z u) = transition r S z (u 0) := by
        rw [chainWeight_cons]
        simp [chainWeight]
      simp only [rightFiber, hread, ite_true, hw]
      rw [← (Fin.consEquiv (fun _ : Fin 1 => Vertex M)).sum_comp,
        ← (Fin.consEquiv (fun _ : Fin 1 => Vertex M)).sum_comp]
      simpa [Fin.consEquiv, Fintype.sum_prod_type] using (hrow x).trans (hrow y).symm
    | succ a =>
      have hf (z : Vertex M) : rightFiber r S l z =
          (2 * (M : ℝ))⁻¹ * chainWeight r S l := by
        unfold rightFiber
        rw [← (Fin.consEquiv (fun _ : Fin (a + 2) => Vertex M)).sum_comp]
        simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk]
        have hread (u : Fin (a + 1) → Vertex M) (w : Vertex M) :
            rightRead (Fin.cons w u) = u := by
          ext i
          change Fin.cons (α := fun _ : Fin (a + 2) => Vertex M) w u i.succ = u i
          simp
        simp only [hread, chainWeight_cons, Fin.cons_zero]
        rw [sum_comm]
        simp_rw [Finset.sum_ite_irrel]
        try simp only [sum_const_zero, sum_ite_eq', mem_univ, ite_true]
        simp_rw [← mul_assoc, ← sum_mul]
        rw [two_step hq hqm hr hr1 hc1 S]
      exact (hf x).trans (hf y).symm

private theorem sum_append {M a b : ℕ}
    (f : (Fin (a + b) → Vertex M) → ℝ) :
    (∑ o, f o) = ∑ u : Fin a → Vertex M, ∑ v : Fin b → Vertex M,
      f (Fin.append u v) := by
  rw [← (Fin.appendEquiv a b).sum_comp]
  simp [Fintype.sum_prod_type, Fin.appendEquiv]

private theorem sum_snoc {M a : ℕ}
    (f : (Fin (a + 1) → Vertex M) → ℝ) :
    (∑ o, f o) = ∑ x : Vertex M, ∑ u : Fin a → Vertex M,
      f (Fin.snoc u x) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (a + 1) => Vertex M)).sum_comp]
  simp [Fintype.sum_prod_type, Fin.snocEquiv]

private theorem sum_cons {M a : ℕ}
    (f : (Fin (a + 1) → Vertex M) → ℝ) :
    (∑ o, f o) = ∑ x : Vertex M, ∑ u : Fin a → Vertex M,
      f (Fin.cons x u) := by
  rw [← (Fin.consEquiv (fun _ : Fin (a + 1) => Vertex M)).sum_comp]
  simp [Fintype.sum_prod_type, Fin.consEquiv]

def exterior {M a b : ℕ} (o : Obs M ((a + 1) + b) .path) :
    (Fin (a - 1) → Vertex M) × (Fin (b - 1) → Vertex M) :=
  (leftRead (Fin.init (fun i => o (Fin.castAdd (b + 1) i))),
   rightRead (Fin.tail (fun i => o (Fin.natAdd (a + 1) i))))

def centralPair {M a b : ℕ} (o : Obs M ((a + 1) + b) .path) : Vertex M × Vertex M :=
  (o (Fin.castAdd (b + 1) (Fin.last a)), o (Fin.natAdd (a + 1) (0 : Fin (b + 1))))

def cylinderMass {M q a b : ℕ} (r : ℝ) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (v : Fin (b - 1) → Vertex M)
    (x y : Vertex M) : ℝ := by
  classical
  exact ∑ o : Obs M ((a + 1) + b) .path,
    if exterior o = (l,v) ∧ centralPair o = (x,y) then probability r .path S o else 0

private theorem cylinderMass_eq {M q a b : ℕ} (r : ℝ) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (v : Fin (b - 1) → Vertex M)
    (x y : Vertex M) :
    cylinderMass r S l v x y = (2 * (M : ℝ))⁻¹ *
      leftFiber r S l x * transition r S x y * rightFiber r S v y := by
  classical
  unfold cylinderMass
  change (∑ o : Fin ((a + 1)+(b + 1)) → Vertex M,
    if exterior (a := a) (b := b) o = (l,v) ∧ centralPair (a := a) (b := b) o = (x,y)
    then (2 * (M : ℝ))⁻¹ * chainWeight (a := (a + 1) + b) r S o else 0) = _
  rw [sum_append (a := a + 1) (b := b + 1), sum_snoc]
  simp_rw [sum_cons]
  have he (u : Fin a → Vertex M) (w : Fin b → Vertex M) (z z' : Vertex M) :
      exterior (a := a) (b := b) (Fin.append (m := a + 1) (n := b + 1) (Fin.snoc u z) (Fin.cons z' w)) =
        (leftRead u, rightRead w) := by
    simp [exterior]
  have hp (u : Fin a → Vertex M) (w : Fin b → Vertex M) (z z' : Vertex M) :
      centralPair (a := a) (b := b) (Fin.append (m := a + 1) (n := b + 1) (Fin.snoc u z) (Fin.cons z' w)) =
        (z,z') := by simp [centralPair]
  simp_rw [he, hp, Prod.mk.injEq]
  rw [sum_eq_single x]
  · rw [sum_comm, sum_eq_single y]
    · simp only [true_and, and_true]
      simp_rw [chainWeight_append, Fin.snoc_last, Fin.cons_zero]
      unfold leftFiber rightFiber
      simp_rw [mul_sum, sum_mul]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro w _
      split_ifs <;> simp_all <;> ring
    · intro z _ hz
      simp [hz]
    · simp
  · intro z _ hz
    simp [hz]
  · simp

private theorem native_joint_exterior {M q a b : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (v : Fin (b - 1) → Vertex M)
    (x y : Vertex M) :
    cylinderMass r S l v x y =
      ((2 * (M : ℝ))⁻¹ * transition r S x y) *
        (∑ z : Vertex M, ∑ w : Vertex M, cylinderMass r S l v z w) := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hrow := (finite_support_bayes (s := 0) hq hqm hr hr1 hc hc1 .path).1 S |>.1.2
  have hL (z : Vertex M) := leftFiber_flat hq hqm hr hr1 hc1 S a l z x
  have hR (z : Vertex M) := rightFiber_flat hq hqm hr hr1 hc1 S b v z y
  have hM : (2 * (M : ℝ)) ≠ 0 := by
    have : 0 < M := by omega
    positivity
  have hMN : (M:ℝ) ≠ 0 := by
    have : 0 < M := by omega
    positivity
  have htotal : (∑ z : Vertex M, ∑ w : Vertex M, cylinderMass r S l v z w) =
      leftFiber r S l x * rightFiber r S v y := by
    simp_rw [cylinderMass_eq, hL, hR]
    simp only [← sum_mul, ← mul_sum, hrow, mul_one]
    simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp [hMN]
    <;> ring
  rw [htotal, cylinderMass_eq]
  ring

theorem native_marked_joint_exterior {M q a b : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (v : Fin (b - 1) → Vertex M)
    (i : Fin M) (hi : i ∈ S.val) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (∑ y : Vertex M, if chi y = σ then cylinderMass r S l v (.inl i) y else 0) =
      ((1 + σ * r)/(2 * (2 * (M : ℝ)))) *
        (∑ z : Vertex M, ∑ w : Vertex M, cylinderMass r S l v z w) := by
  classical
  have hM : (M:ℝ) ≠ 0 := by
    have : 0 < M := by omega
    positivity
  have hcoeff : (∑ y : Vertex M,
      if chi y = σ then (2 * (M : ℝ))⁻¹ * transition r S (.inl i) y else 0) =
        (1 + σ * r)/(2 * (2 * (M : ℝ))) := by
    rcases hσ with rfl | rfl <;>
      norm_num [Fintype.sum_sum_type, chi, transition,
        D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes.b, hi] <;>
      field_simp [hM] <;> ring
  calc
    _ = ∑ y : Vertex M,
        (if chi y = σ then (2 * (M : ℝ))⁻¹ * transition r S (.inl i) y else 0) *
          (∑ z : Vertex M, ∑ w : Vertex M, cylinderMass r S l v z w) := by
      apply sum_congr rfl
      intro y _
      rw [native_joint_exterior hq hqm hr hr1 hc1 S]
      split_ifs <;> simp
    _ = _ := by rw [← sum_mul, hcoeff]

#print axioms native_marked_joint_exterior
end D5.S3.Estimation.TimeArrow.NativeJointExterior
