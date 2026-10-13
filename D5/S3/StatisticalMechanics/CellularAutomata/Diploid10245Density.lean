/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Diploid rule 10-245 has exact density 1/4 + λ/2 from time one. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density

def rule10 (x _y z : Bool) : Bool := (!x) && z

def rule245 (x y z : Bool) : Bool := !(rule10 x y z)

def p (lam : ℝ) (x y z : Bool) : ℝ :=
  (1 - lam) * ((Bool.toNat (rule10 x y z) : ℕ) : ℝ) +
    lam * ((Bool.toNat (rule245 x y z) : ℕ) : ℝ)

def w (lam : ℝ) (b x y z : Bool) : ℝ :=
  if b then p lam x y z else 1 - p lam x y z

/-- Independent simultaneous updates on an interval, with its two exterior parents. -/
def evolve (lam : ℝ) (R : (n : ℕ) → (Fin n → Bool) → ℝ)
    (n : ℕ) (b : Fin n → Bool) : ℝ :=
  ∑ a : Fin (n + 2) → Bool,
    (∏ j : Fin n, w lam (b j) (a j.castSucc.castSucc)
      (a j.succ.castSucc) (a j.succ.succ)) * R (n + 2) a

/-- The full cylinder hierarchy from the fair Bernoulli law, without periodic indexing. -/
def P (lam : ℝ) : ℕ → (n : ℕ) → (Fin n → Bool) → ℝ :=
  Nat.rec (motive := fun _ : ℕ => (n : ℕ) → (Fin n → Bool) → ℝ)
    (fun n _ => (1 / ((2 : ℕ) : ℝ)) ^ n) (fun _ R => evolve lam R)

def d (lam : ℝ) (t : ℕ) : ℝ := P lam t 1 (fun _ => true)

def CylinderLaw (lam : ℝ) : Prop :=
  (∀ t n (b : Fin n → Bool), 0 ≤ P lam t n b) ∧
  (∀ t n, (∑ b : Fin n → Bool, P lam t n b) = 1) ∧
  (∀ t n (b : Fin n → Bool),
    (∑ c : Bool, P lam t (n + 1) (Fin.snoc b c)) = P lam t n b) ∧
  (∀ t n (b : Fin n → Bool),
    (∑ c : Bool, P lam t (n + 1) (Fin.cons c b)) = P lam t n b)

/-- The exact density strengthens the asymptotic question in Fukś–Fatès, §5,
arXiv:2607.01917. CylinderLaw certifies the hierarchy's finite probability laws;
no separate infinite-product probability space is asserted here. -/
def claim : Prop :=
  ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    CylinderLaw lam ∧
    (∀ t : ℕ, 1 ≤ t → d lam t = 1 / ((4 : ℕ) : ℝ) + lam / ((2 : ℕ) : ℝ)) ∧
    Tendsto (fun t : ℕ => d lam t) atTop
      (𝓝 (1 / ((4 : ℕ) : ℝ) + lam / ((2 : ℕ) : ℝ)))

/-- Indicator of a zero followed by a one at distance two. -/
private def A (x z : Bool) : ℝ :=
  (1 - ((Bool.toNat x : ℕ) : ℝ)) * ((Bool.toNat z : ℕ) : ℝ)

/-- The probability of the two specified endpoints, summing over the middle spin. -/
private def q (lam : ℝ) (t : ℕ) : ℝ :=
  ∑ c : Bool, P lam t 3 (Fin.cons false (Fin.cons c (Fin.cons true Fin.elim0)))

private theorem P_zero (lam : ℝ) (n : ℕ) (b : Fin n → Bool) :
    P lam 0 n b = (1 / 2 : ℝ) ^ n := rfl

private theorem P_succ (lam : ℝ) (t n : ℕ) (b : Fin n → Bool) :
    P lam (t + 1) n b = evolve lam (P lam t) n b := rfl

private theorem p_affine (lam : ℝ) (x y z : Bool) :
    p lam x y z = lam + (1 - 2 * lam) * A x z := by
  cases x <;> cases z
  all_goals dsimp only [p, rule10, rule245, A]
  all_goals simp [Bool.toNat_true, Bool.toNat_false]
  all_goals ring

private theorem w_sum (lam : ℝ) (x y z : Bool) :
    (∑ b : Bool, w lam b x y z) = 1 := by
  rw [Fintype.sum_bool]
  change p lam x y z + (1 - p lam x y z) = 1
  ring

private theorem w_nonneg (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (b x y z : Bool) : 0 ≤ w lam b x y z := by
  obtain ⟨h0, h1⟩ := hlam
  cases b <;> cases x <;> cases z
  all_goals dsimp only [w, p, rule10, rule245]
  all_goals simp [Bool.toNat_true, Bool.toNat_false]
  all_goals linarith

/-- Conditional probability of an output block given its entire parent block. -/
private def K (lam : ℝ) (n : ℕ) (b : Fin n → Bool) (a : Fin (n + 2) → Bool) : ℝ :=
  ∏ j : Fin n, w lam (b j) (a j.castSucc.castSucc)
    (a j.succ.castSucc) (a j.succ.succ)

private theorem K_snoc_sum (lam : ℝ) (n : ℕ) (b : Fin n → Bool)
    (a : Fin (n + 3) → Bool) :
    (∑ c : Bool, K lam (n + 1) (Fin.snoc b c) a) = K lam n b (Fin.init a) := by
  dsimp only [K]
  simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Finset.mul_sum, w_sum, mul_one]
  rfl

private theorem K_cons_sum (lam : ℝ) (n : ℕ) (b : Fin n → Bool)
    (a : Fin (n + 3) → Bool) :
    (∑ c : Bool, K lam (n + 1) (Fin.cons c b) a) = K lam n b (Fin.tail a) := by
  dsimp only [K]
  simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.sum_mul, w_sum, one_mul]
  rfl

private theorem marginal_snoc (lam : ℝ) (t n : ℕ) (b : Fin n → Bool) :
    (∑ c : Bool, P lam t (n + 1) (Fin.snoc b c)) = P lam t n b := by
  induction t generalizing n b with
  | zero => simp only [P_zero, Fintype.sum_bool, pow_succ]; ring
  | succ t ih =>
    simp only [P_succ]
    change (∑ c : Bool, ∑ a : Fin (n + 3) → Bool,
      K lam (n + 1) (Fin.snoc b c) a * P lam t (n + 3) a) =
      ∑ a : Fin (n + 2) → Bool, K lam n b a * P lam t (n + 2) a
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, K_snoc_sum]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 3) => Bool)),
      Fintype.sum_prod_type, Finset.sum_comm]
    dsimp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.init_snoc]
    rw [← Finset.mul_sum, ih]

private theorem marginal_cons (lam : ℝ) (t n : ℕ) (b : Fin n → Bool) :
    (∑ c : Bool, P lam t (n + 1) (Fin.cons c b)) = P lam t n b := by
  induction t generalizing n b with
  | zero => simp only [P_zero, Fintype.sum_bool, pow_succ]; ring
  | succ t ih =>
    simp only [P_succ]
    change (∑ c : Bool, ∑ a : Fin (n + 3) → Bool,
      K lam (n + 1) (Fin.cons c b) a * P lam t (n + 3) a) =
      ∑ a : Fin (n + 2) → Bool, K lam n b a * P lam t (n + 2) a
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, K_cons_sum]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 3) => Bool)),
      Fintype.sum_prod_type, Finset.sum_comm]
    dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.tail_cons]
    rw [← Finset.mul_sum, ih]

private theorem total_mass (lam : ℝ) (t n : ℕ) :
    (∑ b : Fin n → Bool, P lam t n b) = P lam t 0 Fin.elim0 := by
  induction n with
  | zero => exact Fintype.sum_subsingleton _ Fin.elim0
  | succ n ih =>
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)),
      Fintype.sum_prod_type, Finset.sum_comm]
    dsimp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    simp_rw [marginal_snoc]
    exact ih

private theorem empty_mass (lam : ℝ) (t : ℕ) : P lam t 0 Fin.elim0 = 1 := by
  induction t with
  | zero => rw [P_zero, pow_zero]
  | succ t ih =>
    rw [P_succ]
    change (∑ a : Fin 2 → Bool, (∏ j : Fin 0,
      w lam (Fin.elim0 j) (a j.castSucc.castSucc)
        (a j.succ.castSucc) (a j.succ.succ)) * P lam t 2 a) = 1
    simp only [Fin.prod_univ_zero, one_mul]
    rw [total_mass, ih]

private theorem normalized (lam : ℝ) (t n : ℕ) :
    (∑ b : Fin n → Bool, P lam t n b) = 1 := by
  rw [total_mass, empty_mass]

private theorem P_nonneg (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (t n : ℕ) (b : Fin n → Bool) : 0 ≤ P lam t n b := by
  induction t generalizing n b with
  | zero => rw [P_zero]; positivity
  | succ t ih =>
    rw [P_succ]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (Finset.prod_nonneg fun j _ => w_nonneg lam hlam _ _ _ _) (ih _ _)

private theorem cylinder_law (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    CylinderLaw lam := by
  exact ⟨P_nonneg lam hlam, normalized lam, marginal_snoc lam, marginal_cons lam⟩

private theorem weighted_init (lam : ℝ) (t n : ℕ) (F : (Fin n → Bool) → ℝ) :
    (∑ a : Fin (n + 1) → Bool, F (Fin.init a) * P lam t (n + 1) a) =
      ∑ b : Fin n → Bool, F b * P lam t n b := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)),
    Fintype.sum_prod_type, Finset.sum_comm]
  dsimp only [Fin.snocEquiv, Equiv.coe_fn_mk]
  simp only [Fin.init_snoc]
  simp_rw [← Finset.mul_sum, marginal_snoc]

private theorem weighted_tail (lam : ℝ) (t n : ℕ) (F : (Fin n → Bool) → ℝ) :
    (∑ a : Fin (n + 1) → Bool, F (Fin.tail a) * P lam t (n + 1) a) =
      ∑ b : Fin n → Bool, F b * P lam t n b := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)),
    Fintype.sum_prod_type, Finset.sum_comm]
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
  simp only [Fin.tail_cons]
  simp_rw [← Finset.mul_sum, marginal_cons]

private theorem q_sum (lam : ℝ) (t : ℕ) :
    q lam t = ∑ a : Fin 3 → Bool, A (a 0) (a 2) * P lam t 3 a := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 3 => Bool)), Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Bool)),
    Fintype.sum_prod_type, ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 1 => Bool)),
    Fintype.sum_prod_type]
  have h2 : (2 : Fin 3) = (0 : Fin 1).succ.succ := rfl
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk, q, A]
  simp only [Fintype.sum_unique, Fintype.sum_bool, h2, Fin.cons_zero, Fin.cons_succ,
    Bool.toNat_true, Bool.toNat_false]
  norm_num
  congr 5

private theorem prefix_q (lam : ℝ) (t : ℕ) :
    (∑ a : Fin 5 → Bool, A (a 0) (a 2) * P lam t 5 a) = q lam t := by
  have h4 := weighted_init lam t 4 (fun a => A (a 0) (a 2))
  have h3 := weighted_init lam t 3 (fun a => A (a 0) (a 2))
  change (∑ a : Fin 5 → Bool, A (a 0) (a 2) * P lam t 5 a) =
    ∑ a : Fin 4 → Bool, A (a 0) (a 2) * P lam t 4 a at h4
  change (∑ a : Fin 4 → Bool, A (a 0) (a 2) * P lam t 4 a) =
    ∑ a : Fin 3 → Bool, A (a 0) (a 2) * P lam t 3 a at h3
  exact h4.trans (h3.trans (q_sum lam t).symm)

private theorem suffix_q (lam : ℝ) (t : ℕ) :
    (∑ a : Fin 5 → Bool, A (a 2) (a 4) * P lam t 5 a) = q lam t := by
  have h4 := weighted_tail lam t 4 (fun a => A (a 1) (a 3))
  have h3 := weighted_tail lam t 3 (fun a => A (a 0) (a 2))
  change (∑ a : Fin 5 → Bool, A (a 2) (a 4) * P lam t 5 a) =
    ∑ a : Fin 4 → Bool, A (a 1) (a 3) * P lam t 4 a at h4
  change (∑ a : Fin 4 → Bool, A (a 1) (a 3) * P lam t 4 a) =
    ∑ a : Fin 3 → Bool, A (a 0) (a 2) * P lam t 3 a at h3
  exact h4.trans (h3.trans (q_sum lam t).symm)

private theorem density_succ (lam : ℝ) (t : ℕ) :
    d lam (t + 1) = lam + (1 - 2 * lam) * q lam t := by
  calc
    d lam (t + 1) = ∑ a : Fin 3 → Bool, p lam (a 0) (a 1) (a 2) * P lam t 3 a := by
      unfold d
      rw [P_succ]
      dsimp only [evolve]
      simp only [Fin.prod_univ_one]
      rfl
    _ = lam * (∑ a : Fin 3 → Bool, P lam t 3 a) +
        (1 - 2 * lam) * (∑ a : Fin 3 → Bool, A (a 0) (a 2) * P lam t 3 a) := by
      simp_rw [p_affine, add_mul, mul_assoc, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = lam + (1 - 2 * lam) * q lam t := by
      rw [normalized, ← q_sum, mul_one]

private theorem q_update (lam : ℝ) (t : ℕ) :
    q lam (t + 1) = ∑ a : Fin 5 → Bool,
      (1 - p lam (a 0) (a 1) (a 2)) * p lam (a 2) (a 3) (a 4) * P lam t 5 a := by
  rw [q]
  simp_rw [P_succ]
  change (∑ c : Bool, ∑ a : Fin 5 → Bool,
    K lam 3 (Fin.cons false (Fin.cons c (Fin.cons true Fin.elim0))) a * P lam t 5 a) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul]
  congr 1
  dsimp only [K]
  simp_rw [Fin.prod_univ_three]
  change (∑ c : Bool, w lam false (a 0) (a 1) (a 2) *
    w lam c (a 1) (a 2) (a 3) * w lam true (a 2) (a 3) (a 4)) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.sum_mul, w_sum, one_mul]
  rfl

private theorem A_overlap_zero (x y z : Bool) : A x y * A y z = 0 := by
  cases y
  all_goals dsimp only [A]
  all_goals simp [Bool.toNat_true, Bool.toNat_false]

private theorem p_pair (lam : ℝ) (x y z u v : Bool) :
    (1 - p lam x y z) * p lam z u v = lam * (1 - lam) +
      (1 - 2 * lam) * (1 - lam) * A z v - (1 - 2 * lam) * lam * A x z := by
  rw [p_affine, p_affine]
  calc
    (1 - (lam + (1 - 2 * lam) * A x z)) * (lam + (1 - 2 * lam) * A z v) =
        lam * (1 - lam) + (1 - 2 * lam) * (1 - lam) * A z v -
          (1 - 2 * lam) * lam * A x z - (1 - 2 * lam) ^ 2 * (A x z * A z v) := by
      ring
    _ = _ := by rw [A_overlap_zero, mul_zero, sub_zero]

/-- Overlap closes the moment recursion without independence of the time-t spins. -/
private theorem q_succ (lam : ℝ) (t : ℕ) :
    q lam (t + 1) = lam * (1 - lam) + (1 - 2 * lam) ^ 2 * q lam t := by
  calc
    q lam (t + 1) = ∑ a : Fin 5 → Bool,
        (1 - p lam (a 0) (a 1) (a 2)) * p lam (a 2) (a 3) (a 4) * P lam t 5 a :=
      q_update lam t
    _ = (lam * (1 - lam)) * (∑ a : Fin 5 → Bool, P lam t 5 a) +
        ((1 - 2 * lam) * (1 - lam)) *
          (∑ a : Fin 5 → Bool, A (a 2) (a 4) * P lam t 5 a) -
        ((1 - 2 * lam) * lam) *
          (∑ a : Fin 5 → Bool, A (a 0) (a 2) * P lam t 5 a) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [p_pair]
      ring
    _ = lam * (1 - lam) + (1 - 2 * lam) ^ 2 * q lam t := by
      rw [normalized, prefix_q, suffix_q]
      ring

private theorem q_zero (lam : ℝ) : q lam 0 = 1 / 4 := by
  dsimp only [q]
  simp_rw [P_zero]
  norm_num

private theorem q_constant (lam : ℝ) (t : ℕ) : q lam t = 1 / 4 := by
  induction t with
  | zero => exact q_zero lam
  | succ t ih => rw [q_succ, ih]; ring

private theorem density_from_one (lam : ℝ) :
    ∀ t : ℕ, 1 ≤ t → d lam t = 1 / 4 + lam / 2 := by
  intro t ht
  cases t with
  | zero => norm_num at ht
  | succ t => rw [density_succ, q_constant]; ring

theorem result : claim := by
  dsimp only [claim]
  intro lam hlam
  have h := density_from_one lam
  exact ⟨cylinder_law lam hlam, h, tendsto_atTop_of_eventually_const h⟩

end D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
