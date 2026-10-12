/- GID: D5/S1/Recurrence/QuadraticCompanionDefect
   generality: G
   mirror-B: D5/B/S1/Recurrence/QuadraticCompanionDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integral two-step elimination of a reset companion with an involutive head. -/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.QuadraticCompanionDefect
open scoped BigOperators
variable {A : Type*} [AddCommGroup A]

/-- Reconstruct every coordinate from the first two and the two-step sums. -/
def reconstruct : (n : ℕ) → A → A → (Fin n → A) → (Fin (n + 2) → A)
  | 0, a, b, _ => Fin.cons a (fun _ => b)
  | n + 1, a, b, t => Fin.cons a (reconstruct n b (t 0 - a) (fun j => t j.succ))

private theorem reconstruct_head (n : ℕ) (a b : A) (t : Fin n → A) :
    reconstruct n a b t 0 = a := by cases n <;> rfl

private theorem reconstruct_second (n : ℕ) (a b : A) (t : Fin n → A) :
    reconstruct n a b t (0 : Fin (n + 1)).succ = b := by
  cases n <;> simp only [reconstruct, Fin.cons_succ, reconstruct_head]

private theorem reconstruct_tail (n : ℕ) (a b : A) (t : Fin n → A) (j : Fin n) :
    reconstruct n a b t j.succ.succ + reconstruct n a b t j.castSucc.castSucc =
      t j := by
  induction n generalizing a b with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [reconstruct, Fin.cons_succ, reconstruct_second,
          Fin.castSucc_zero, Fin.cons_zero]
        abel
      · simpa only [reconstruct, Fin.cons_succ, Fin.castSucc_succ] using
          ih b (t 0 - a) (fun k => t k.succ) k

private theorem reconstruct_unique (n : ℕ) (v : Fin (n + 2) → A) :
    reconstruct n (v 0) (v (0 : Fin (n + 1)).succ)
      (fun j => v j.succ.succ + v j.castSucc.castSucc) = v := by
  induction n with
  | zero => ext j; fin_cases j <;> rfl
  | succ n ih =>
      have ht : (v (0 : Fin (n + 1)).succ.succ + v 0) - v 0 =
          v (0 : Fin (n + 1)).succ.succ := by abel
      simp only [reconstruct, Fin.castSucc_zero, ht]
      have hh := ih (fun j => v j.succ)
      simp only [Fin.succ_castSucc] at hh
      rw [hh]
      exact Fin.cons_self_tail v

/-- Integral triangular coordinates with two free head values. -/
def domainEquiv (n : ℕ) : (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) where
  toFun v := ((v 0, v (0 : Fin (n + 1)).succ),
    fun j => v j.succ.succ + v j.castSucc.castSucc)
  invFun z := reconstruct n z.1.1 z.1.2 z.2
  left_inv := reconstruct_unique n
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext (reconstruct_head n _ _ _) (reconstruct_second n _ _ _)
    · funext j; exact reconstruct_tail n _ _ _ j
  map_add' v w := by
    apply Prod.ext
    · rfl
    · funext j
      change (v j.succ.succ + w j.succ.succ) +
        (v j.castSucc.castSucc + w j.castSucc.castSucc) =
        (v j.succ.succ + v j.castSucc.castSucc) +
          (w j.succ.succ + w j.castSucc.castSucc)
      abel

private theorem reconstruct_add (n : ℕ) (a b c d : A) (t u : Fin n → A) :
    reconstruct n (a + c) (b + d) (t + u) =
      reconstruct n a b t + reconstruct n c d u :=
  (domainEquiv n).symm.map_add ((a, b), t) ((c, d), u)

/-- The sum omitting the rightmost coordinate. -/
def prefixSum (n : ℕ) (v : Fin (n + 2) → A) : A := ∑ j : Fin (n + 1), v j.castSucc

/-- Identity plus two steps of the companion: the two head equations and all
the skip-one tail equations. The head operator need not be invertible. -/
def companion (J : A →+ A) (n : ℕ) : (Fin (n + 2) → A) →+ (Fin (n + 2) → A) where
  toFun v := Fin.cons (v 0 + J (J (∑ j, v j) + prefixSum n v))
    (Fin.cons (v (0 : Fin (n + 1)).succ + J (∑ j, v j))
      (fun j => v j.succ.succ + v j.castSucc.castSucc))
  map_zero' := by
    ext j; refine Fin.cases ?_ (fun k => ?_) j
    · simp [prefixSum]
    · refine Fin.cases ?_ (fun l => ?_) k <;> simp
  map_add' v w := by
    ext j; refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero, Pi.add_apply, prefixSum, Finset.sum_add_distrib, map_add]
      abel
    · refine Fin.cases ?_ (fun l => ?_) k
      · simp only [Fin.cons_succ, Fin.cons_zero, Pi.add_apply, Finset.sum_add_distrib,
          map_add]; abel
      · simp only [Fin.cons_succ, Pi.add_apply]; abel

private def tailMap (n : ℕ) : (Fin n → A) →+ (Fin (n + 2) → A) :=
  (domainEquiv n).symm.toAddMonoidHom.comp
    ({
        toFun := fun t => ((0, 0), t)
        map_zero' := rfl
        map_add' := fun _ _ => by simp
      } : (Fin n → A) →+ (A × A) × (Fin n → A))

private def heads (n : ℕ) : (Fin (n + 2) → A) →+ (A × A) where
  toFun v := (v 0, v (0 : Fin (n + 1)).succ)
  map_zero' := rfl
  map_add' _ _ := rfl

private def tailCorrection (J : A →+ A) (n : ℕ) : (Fin n → A) →+ (A × A) :=
  (heads n).comp ((companion J n).comp (tailMap n))

private theorem tailCorrection_apply (J : A →+ A) (n : ℕ) (t : Fin n → A) :
    tailCorrection J n t = heads n (companion J n (reconstruct n 0 0 t)) := rfl

private def tails (n : ℕ) : (Fin (n + 2) → A) →+ (Fin n → A) where
  toFun y j := y j.succ.succ
  map_zero' := rfl
  map_add' _ _ := rfl

private def codomainMap (J : A →+ A) (n : ℕ) :
    (Fin (n + 2) → A) →+ (A × A) × (Fin n → A) :=
  ((heads n) - (tailCorrection J n).comp (tails n)).prod (tails n)

/-- A codomain shear removes the effect of the inhomogeneous tails from both
boundary equations. This equivalence is independent of the free head values. -/
def codomainEquiv (J : A →+ A) (n : ℕ) :
    (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) where
  toFun := codomainMap J n
  invFun z := let h := z.1 + tailCorrection J n z.2
    Fin.cons h.1 (Fin.cons h.2 z.2)
  left_inv y := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change y 0 - (tailCorrection J n (fun j => y j.succ.succ)).1 +
        (tailCorrection J n (fun j => y j.succ.succ)).1 = y 0
      exact sub_add_cancel _ _
    · refine Fin.cases ?_ (fun l => ?_) k
      · change y (0 : Fin (n + 1)).succ -
          (tailCorrection J n (fun j => y j.succ.succ)).2 +
          (tailCorrection J n (fun j => y j.succ.succ)).2 = y (0 : Fin (n + 1)).succ
        exact sub_add_cancel _ _
      · rfl
  right_inv z := by
    change ((z.1 + tailCorrection J n z.2) - tailCorrection J n z.2, z.2) = z
    apply Prod.ext
    · exact add_sub_cancel_right _ _
    · rfl
  map_add' := (codomainMap J n).map_add

/-- The homogeneous boundary map is evaluated on the genuine periodic integer
recurrence, not on eigenvectors over a field. -/
def boundary (J : A →+ A) (n : ℕ) (a b : A) : A × A :=
  let v := reconstruct n a b 0
  (a + J (J (∑ j, v j) + prefixSum n v), b + J (∑ j, v j))

private theorem free_heads (J : A →+ A) (n : ℕ) (a b : A) :
    heads n (companion J n (reconstruct n a b 0)) = boundary J n a b := by
  simp only [heads, companion, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Fin.cons_zero, Fin.cons_succ, reconstruct_head, reconstruct_second, boundary]

/-- Exact additive elimination: two boundary coordinates plus identity on all
remaining tail coordinates. -/
theorem eliminate (J : A →+ A) (n : ℕ) (v : Fin (n + 2) → A) :
    codomainEquiv J n (companion J n v) =
      (boundary J n (v 0) (v (0 : Fin (n + 1)).succ), (domainEquiv n v).2) := by
  have hv : v = reconstruct n (v 0) (v (0 : Fin (n + 1)).succ) 0 +
      reconstruct n 0 0 (domainEquiv n v).2 := by
    rw [← reconstruct_add]
    simp only [add_zero, zero_add]
    exact (reconstruct_unique n v).symm
  apply Prod.ext
  · change heads n (companion J n v) -
      tailCorrection J n (domainEquiv n v).2 = _
    have hh : heads n (companion J n v) =
        boundary J n (v 0) (v (0 : Fin (n + 1)).succ) +
          tailCorrection J n (domainEquiv n v).2 := by
      calc
        heads n (companion J n v) = heads n (companion J n
          (reconstruct n (v 0) (v (0 : Fin (n + 1)).succ) 0 +
            reconstruct n 0 0 (domainEquiv n v).2)) :=
          congrArg (fun u => heads n (companion J n u)) hv
        _ = heads n (companion J n (reconstruct n (v 0)
            (v (0 : Fin (n + 1)).succ) 0)) +
              heads n (companion J n (reconstruct n 0 0 (domainEquiv n v).2)) := by
          rw [map_add, map_add]
        _ = _ := by rw [free_heads, ← tailCorrection_apply]
    rw [hh, add_sub_cancel_right]
  · rfl

private theorem sum_reconstruct_succ (n : ℕ) (a b : A) :
    (∑ j, reconstruct (n + 1) a b 0 j) = a + ∑ j, reconstruct n b (-a) 0 j := by
  simp only [reconstruct, Pi.zero_apply, zero_sub, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  rfl

private theorem prefix_reconstruct_succ (n : ℕ) (a b : A) :
    prefixSum (n + 1) (reconstruct (n + 1) a b 0) =
      a + prefixSum n (reconstruct n b (-a) 0) := by
  simp only [prefixSum, Fin.sum_univ_succ, reconstruct, Fin.castSucc_zero,
    Fin.cons_zero, Fin.castSucc_succ, Fin.cons_succ, Pi.zero_apply, zero_sub]
  rfl

private theorem sum_reconstruct_four (n : ℕ) (a b : A) :
    (∑ j, reconstruct (n + 4) a b 0 j) = ∑ j, reconstruct n a b 0 j := by
  rw [show n + 4 = ((n + 1) + 1) + 1 + 1 by omega]
  rw [sum_reconstruct_succ, sum_reconstruct_succ, sum_reconstruct_succ,
    sum_reconstruct_succ, neg_neg, neg_neg]
  abel

private theorem prefix_reconstruct_four (n : ℕ) (a b : A) :
    prefixSum (n + 4) (reconstruct (n + 4) a b 0) =
      prefixSum n (reconstruct n a b 0) := by
  rw [show n + 4 = ((n + 1) + 1) + 1 + 1 by omega]
  rw [prefix_reconstruct_succ, prefix_reconstruct_succ, prefix_reconstruct_succ,
    prefix_reconstruct_succ, neg_neg, neg_neg]
  abel

private theorem homogeneous_sums (m : ℕ) (a b : A) :
    (∑ j, reconstruct (4 * m + 1) a b 0 j) = b ∧
      prefixSum (4 * m + 1) (reconstruct (4 * m + 1) a b 0) = a + b := by
  induction m with
  | zero => simp [reconstruct, prefixSum, Fin.sum_univ_succ]
  | succ m ih =>
      rw [show 4 * (m + 1) + 1 = (4 * m + 1) + 4 by omega,
        sum_reconstruct_four, prefix_reconstruct_four]
      exact ih

/-- At every carrier length congruent to three modulo four, an involutive
head reduces the two-step defect to two independent copies of `id + J`.
The domain shear `(a,b) ↦ (a+b,b)` is integral and invertible. -/
theorem boundary_three_mod_four (J : A →+ A) (hJ : ∀ x, J (J x) = x)
    (m : ℕ) (a b : A) :
    boundary J (4 * m + 1) a b = (a + b + J (a + b), b + J b) := by
  simp only [boundary, (homogeneous_sums m a b).1, (homogeneous_sums m a b).2,
    map_add, hJ]
  apply Prod.ext <;> dsimp <;> abel

end D5.S1.Recurrence.QuadraticCompanionDefect
