/- GID: D5/S1/Recurrence/FiniteCompanionSquareDefect
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteCompanionSquareDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integral two-sided elimination of identity plus squared reset time. -/
import D5.S1.Recurrence.FiniteCompanionDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.FiniteCompanionSquareDefect
open scoped BigOperators
variable {A : Type*} [AddCommGroup A]

/-- The genuine reset time, before adding the identity. -/
def time (J : A →+ A) (n : ℕ) : (Fin (n + 1) → A) →+ (Fin (n + 1) → A) where
  toFun v := Fin.cons (J (∑ i, v i)) (fun j => v j.castSucc)
  map_zero' := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_add' v w := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib]
    · rfl

/-- Identity plus two genuine time steps, on a positive-length carrier. -/
def squareDefect (J : A →+ A) (n : ℕ) :=
  AddMonoidHom.id (Fin (n + 1) → A) + (time J n).comp (time J n)

/-- Solve all stride-two equations from two independent integer seeds. -/
def reconstruct : (n : ℕ) → A → A → (Fin n → A) → (Fin (n + 2) → A)
  | 0, a, b, _ => Fin.cons a (fun _ => b)
  | n + 1, a, b, t => Fin.cons a (reconstruct n b (t 0 - a) (fun j => t j.succ))

private theorem head (n : ℕ) (a b : A) (t : Fin n → A) :
    reconstruct n a b t 0 = a := by cases n <;> rfl

private theorem second (n : ℕ) (a b : A) (t : Fin n → A) :
    reconstruct n a b t (0 : Fin (n + 1)).succ = b := by
  cases n
  · rfl
  · exact head _ _ _ _

private theorem adjacent (n : ℕ) (a b : A) (t : Fin n → A) (j : Fin n) :
    reconstruct n a b t j.succ.succ + reconstruct n a b t j.castSucc.castSucc = t j := by
  induction n generalizing a b with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · change reconstruct n b (t 0 - a) (fun j => t j.succ) (0 : Fin (n + 1)).succ + a = t 0
        rw [second]; abel
      · simpa only [reconstruct, Fin.cons_succ, Fin.castSucc_succ] using
          ih b (t 0 - a) (fun j => t j.succ) k

private theorem unique (n : ℕ) (v : Fin (n + 2) → A) :
    reconstruct n (v 0) (v (0 : Fin (n + 1)).succ)
      (fun j => v j.succ.succ + v j.castSucc.castSucc) = v := by
  induction n with
  | zero => ext i; fin_cases i <;> rfl
  | succ n ih =>
      have ht : (v (0 : Fin (n + 1)).succ.succ + v 0) - v 0 =
          v (0 : Fin (n + 1)).succ.succ := by simp
      simp only [reconstruct, Fin.castSucc_zero, ht]
      have hi := ih (fun j : Fin (n + 2) => v j.succ)
      simp only [Fin.succ_castSucc] at hi
      rw [hi]
      exact Fin.cons_self_tail v

/-- The two seeds and all stride-two sums are integral domain coordinates. -/
def domainEquiv (n : ℕ) : (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) where
  toFun v := ((v 0, v (0 : Fin (n + 1)).succ),
    fun j => v j.succ.succ + v j.castSucc.castSucc)
  invFun z := reconstruct n z.1.1 z.1.2 z.2
  left_inv := unique n
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext (head n _ _ _) (second n _ _ _)
    · funext j; exact adjacent n _ _ _ j
  map_add' v w := by
    apply Prod.ext
    · rfl
    · funext j
      change (v j.succ.succ + w j.succ.succ) +
        (v j.castSucc.castSucc + w j.castSucc.castSucc) =
        (v j.succ.succ + v j.castSucc.castSucc) +
        (w j.succ.succ + w j.castSucc.castSucc)
      abel

private theorem split_reconstruct (n : ℕ) (a b : A) (t : Fin n → A) :
    reconstruct n a b t = reconstruct n a b 0 + reconstruct n 0 0 t := by
  apply (domainEquiv n).injective
  rw [map_add]
  have h (a b : A) (t : Fin n → A) : domainEquiv n (reconstruct n a b t) = ((a,b),t) :=
    (domainEquiv n).apply_symm_apply ((a,b),t)
  rw [h, h, h]; simp

/-- The sum and last coordinate of the homogeneous quarter-turn recurrence. -/
def boundary (q : ℕ) (a b : A) : A × A :=
  if q % 4 = 0 then (0, -b) else
  if q % 4 = 1 then (a, a) else
  if q % 4 = 2 then (a + b, b) else (b, -a)

private theorem homogeneous_boundary (n : ℕ) (a b : A) :
    ((∑ i, reconstruct n a b 0 i), reconstruct n a b 0 (Fin.last (n + 1))) =
      boundary (n + 2) a b := by
  induction n generalizing a b with
  | zero => simp [reconstruct, boundary, Fin.sum_univ_succ]
  | succ n ih =>
      have hs := congrArg Prod.fst (ih b (-a))
      have hl := congrArg Prod.snd (ih b (-a))
      simp only [Prod.fst, Prod.snd] at hs hl
      simp only [reconstruct, Pi.zero_apply, zero_sub]
      change ((∑ i : Fin (n + 3), (Fin.cons a (reconstruct n b (-a) 0) : Fin (n + 3) → A) i),
        (Fin.cons a (reconstruct n b (-a) 0) : Fin (n + 3) → A) (Fin.last (n + 2))) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [show Fin.last (n + 2) = (Fin.last (n + 1)).succ from rfl, Fin.cons_succ]
      change (a + (∑ i, reconstruct n b (-a) 0 i),
        reconstruct n b (-a) 0 (Fin.last (n + 1))) = _
      rw [hs, hl]
      have hm := Nat.mod_lt (n + 2) (by decide : 0 < 4)
      interval_cases h : (n + 2) % 4 <;>
        have hn : (n + 1 + 2) % 4 = ((n + 2) % 4 + 1) % 4 := by omega
      all_goals simp [boundary, h, hn] <;> abel

/-- The raw two-head remainder, before integral row and column shears. -/
def headResidual (J : A →+ A) (q : ℕ) (z : A × A) : A × A :=
  let s := (boundary q z.1 z.2).1
  let l := (boundary q z.1 z.2).2
  (z.1 + s + J (s - l), z.2 + J s)

private def tailHeads (J : A →+ A) (n : ℕ) (t : Fin n → A) : A × A :=
  let v := reconstruct n (0 : A) 0 t
  (squareDefect J (n + 1) v 0, squareDefect J (n + 1) v (0 : Fin (n + 1)).succ)

private theorem tailHeads_add (J : A →+ A) (n : ℕ) (t u : Fin n → A) :
    tailHeads J n (t + u) = tailHeads J n t + tailHeads J n u := by
  have h : reconstruct n (0 : A) 0 (t + u) =
      reconstruct n 0 0 t + reconstruct n 0 0 u := by
    apply (domainEquiv n).injective
    rw [map_add]
    change domainEquiv n ((domainEquiv n).symm ((0,0),t+u)) = _
    simp only [AddEquiv.apply_symm_apply]
    change _ = domainEquiv n ((domainEquiv n).symm ((0,0),t)) +
      domainEquiv n ((domainEquiv n).symm ((0,0),u))
    simp
  simp only [tailHeads, h, map_add, Pi.add_apply, Prod.mk_add_mk]

/-- Independently remove the image of the zero-seed tail from both codomain heads. -/
def codomainEquiv (J : A →+ A) (n : ℕ) :
    (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) where
  toFun y := ((y 0, y (0 : Fin (n + 1)).succ) -
    tailHeads J n (fun j => y j.succ.succ), fun j => y j.succ.succ)
  invFun z := Fin.cons (z.1.1 + (tailHeads J n z.2).1)
    (Fin.cons (z.1.2 + (tailHeads J n z.2).2) z.2)
  left_inv y := by
    simp only [Prod.fst_sub, Prod.snd_sub, sub_add_cancel]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv z := by
    apply Prod.ext
    · change (z.1 + tailHeads J n z.2) - tailHeads J n z.2 = z.1
      abel
    · rfl
  map_add' y z := by
    apply Prod.ext
    · change ((y 0 + z 0, y _ + z _) - tailHeads J n (fun j => y _ + z _)) = _
      have h := tailHeads_add J n (fun j => y j.succ.succ) (fun j => z j.succ.succ)
      change ((y 0,z 0).1 + (y 0,z 0).2, y (0 : Fin (n + 1)).succ + z (0 : Fin (n + 1)).succ) -
        tailHeads J n ((fun j => y j.succ.succ) + (fun j => z j.succ.succ)) =
        ((y 0,y (0 : Fin (n + 1)).succ) - tailHeads J n (fun j => y j.succ.succ)) +
        ((z 0,z (0 : Fin (n + 1)).succ) - tailHeads J n (fun j => z j.succ.succ))
      rw [h]
      change ((y 0,y _) + (z 0,z _)) - _ = _
      abel
    · rfl

private theorem homogeneous_heads (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (n : ℕ) (a b : A) :
    (squareDefect J (n + 1) (reconstruct n a b 0) 0,
      squareDefect J (n + 1) (reconstruct n a b 0) (0 : Fin (n + 1)).succ) =
      headResidual J (n + 2) (a,b) := by
  have hb := homogeneous_boundary n a b
  have hs := congrArg Prod.fst hb
  have hl := congrArg Prod.snd hb
  simp only [Prod.fst, Prod.snd] at hs hl
  apply Prod.ext
  · change reconstruct n a b 0 0 + J (∑ i, time J (n + 1) (reconstruct n a b 0) i) = _
    rw [Fin.sum_univ_succ]
    simp only [time, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.cons_zero,
      Fin.cons_succ, map_add, hJ, head]
    have hp : (∑ j : Fin (n + 1), reconstruct n a b 0 j.castSucc) =
        (∑ i, reconstruct n a b 0 i) - reconstruct n a b 0 (Fin.last (n + 1)) := by
      rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => reconstruct n a b 0 i)]
      abel
    rw [hp, hs, hl]
    dsimp [headResidual]; abel
  · change reconstruct n a b 0 (0 : Fin (n + 1)).succ +
      time J (n + 1) (reconstruct n a b 0) (0 : Fin (n + 1)).castSucc = _
    simp only [time, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.cons_zero, second, hs]
    rfl

/-- Two seed coordinates retain the whole boundary obstruction; all other coordinates
are identity. The domain reconstruction and the codomain shear are independent. -/
theorem eliminate (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (n : ℕ) (v : Fin (n + 2) → A) :
    codomainEquiv J n (squareDefect J (n + 1) v) =
      (headResidual J (n + 2) (domainEquiv n v).1, (domainEquiv n v).2) := by
  have hv : v = reconstruct n (v 0) (v (0 : Fin (n + 1)).succ)
      (fun j => v j.succ.succ + v j.castSucc.castSucc) := (unique n v).symm
  have ht (j : Fin n) : squareDefect J (n + 1) v j.succ.succ =
      v j.succ.succ + v j.castSucc.castSucc := rfl
  apply Prod.ext
  · change (squareDefect J (n + 1) v 0, squareDefect J (n + 1) v (0 : Fin (n + 1)).succ) -
      tailHeads J n (fun j => squareDefect J (n + 1) v j.succ.succ) = _
    simp_rw [ht]
    conv_lhs => enter [1]; rw [hv, split_reconstruct, map_add]
    simp only [Pi.add_apply, ← Prod.mk_add_mk]
    rw [homogeneous_heads J hJ]
    change (_ + tailHeads J n _) - tailHeads J n _ = _
    abel
  · funext j; exact ht j

private def upperShear (f : A →+ A) : (A × A) ≃+ (A × A) where
  toFun z := (z.1 + f z.2, z.2)
  invFun z := (z.1 - f z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [map_add]; abel

private def lowerShear (f : A →+ A) : (A × A) ≃+ (A × A) where
  toFun z := (z.1, z.2 + f z.1)
  invFun z := (z.1, z.2 - f z.1)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [map_add]; abel

/-- Unimodular column operations on the two seeds. -/
def headDomainEquiv (J : A →+ A) (q : ℕ) : (A × A) ≃+ (A × A) :=
  if q % 4 = 0 then upperShear J else
  if q % 4 = 1 then lowerShear J else
  if q % 4 = 2 then lowerShear (AddMonoidHom.id A + AddMonoidHom.id A + J) else
    upperShear (AddMonoidHom.id A)

private def pivotEquiv (J : A →+ A) : (A × A) ≃+ (A × A) where
  toFun z := (z.1 + J z.1 - z.2, z.1)
  invFun z := (z.2, z.2 + J z.2 - z.1)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [map_add]; abel

/-- Independent unimodular row operations, using the unit pivot in residue two. -/
def headCodomainEquiv (J : A →+ A) (q : ℕ) : (A × A) ≃+ (A × A) :=
  if q % 4 = 2 then pivotEquiv J else AddEquiv.refl _

/-- The complete two-head normal form: id, 2id, 3id+2J, or two copies of id+J. -/
def headNormal (J : A →+ A) (q : ℕ) (z : A × A) : A × A :=
  if q % 4 = 0 then z else
  if q % 4 = 1 then (z.1 + z.1, z.2) else
  if q % 4 = 2 then (z.1 + z.1 + z.1 + J z.1 + J z.1, z.2) else
    (z.1 + J z.1, z.2 + J z.2)

private theorem head_normal (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (q : ℕ) (z : A × A) :
    headCodomainEquiv J q (headResidual J q z) =
      headNormal J q (headDomainEquiv J q z) := by
  have hm := Nat.mod_lt q (by decide : 0 < 4)
  interval_cases h : q % 4 <;>
    simp [headCodomainEquiv, headResidual, boundary, headNormal, headDomainEquiv,
      upperShear, lowerShear, pivotEquiv, h, map_add, map_sub, map_neg, hJ] <;> abel <;> simp

/-- Full integral domain coordinates, after the residue-dependent column operations. -/
def normalDomainEquiv (J : A →+ A) (n : ℕ) :
    (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) :=
  (domainEquiv n).trans ((headDomainEquiv J (n + 2)).prodCongr (AddEquiv.refl _))

/-- Full integral codomain coordinates, after the independent row operations. -/
def normalCodomainEquiv (J : A →+ A) (n : ℕ) :
    (Fin (n + 2) → A) ≃+ (A × A) × (Fin n → A) :=
  (codomainEquiv J n).trans ((headCodomainEquiv J (n + 2)).prodCongr (AddEquiv.refl _))

/-- At every length at least two the operator is equivalent on both sides to the
period-four head normal form and an identity tail. This is not conjugacy. -/
theorem normal_form (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (n : ℕ) (v : Fin (n + 2) → A) :
    normalCodomainEquiv J n (squareDefect J (n + 1) v) =
      (headNormal J (n + 2) (normalDomainEquiv J n v).1, (normalDomainEquiv J n v).2) := by
  change ((headCodomainEquiv J (n + 2)) (codomainEquiv J n (squareDefect J (n + 1) v)).1,
    (codomainEquiv J n (squareDefect J (n + 1) v)).2) = _
  rw [eliminate J hJ, head_normal J hJ]
  rfl

end D5.S1.Recurrence.FiniteCompanionSquareDefect
