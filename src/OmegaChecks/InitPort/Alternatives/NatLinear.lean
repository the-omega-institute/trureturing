module

public import Init.Data.Nat.Internal.Linear
public import Init.Data.Nat.Simproc
public import Init.Grind.Offset

open Nat.Internal.Linear

namespace OmegaChecks.InitPort.Alternatives

private theorem cancelBalance (ctx : Context) (fuel : Nat) (a b l r : Poly) :
    (Poly.cancelAux fuel a b l r).1.denote ctx + (r.denote ctx + b.denote ctx) =
      (Poly.cancelAux fuel a b l r).2.denote ctx + (l.denote ctx + a.denote ctx) := by
  induction fuel generalizing a b l r with
  | zero =>
    simp only [Poly.cancelAux, Poly.denote_append, Poly.denote_reverse]
    exact Nat.add_comm ..
  | succ fuel ih =>
    cases a with
    | nil =>
      cases b <;> simp only [Poly.cancelAux, Poly.denote_append, Poly.denote_reverse,
        Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.add_zero] <;> exact Nat.add_comm ..
    | cons termA a =>
      obtain ⟨ka,va⟩ := termA
      cases b with
      | nil =>
        simp only [Poly.cancelAux, Poly.denote_append, Poly.denote_reverse, Poly.denote,
          Nat.add_zero]
        exact Nat.add_comm ..
      | cons termB b =>
        obtain ⟨kb,vb⟩ := termB
        rw [Poly.cancelAux]
        cases ab : Nat.blt va vb
        · cases ba : Nat.blt vb va
          · have equal : va = vb := Nat.le_antisymm
              (Nat.le_of_not_gt (fun h => Bool.noConfusion (ba.symm.trans (Nat.ble_eq_true_of_le h))))
              (Nat.le_of_not_gt (fun h => Bool.noConfusion (ab.symm.trans (Nat.ble_eq_true_of_le h))))
            subst vb
            cases lt : Nat.blt ka kb
            · cases gt : Nat.blt kb ka
              · have equal : ka = kb := Nat.le_antisymm
                  (Nat.le_of_not_gt (fun h => Bool.noConfusion (gt.symm.trans (Nat.ble_eq_true_of_le h))))
                  (Nat.le_of_not_gt (fun h => Bool.noConfusion (lt.symm.trans (Nat.ble_eq_true_of_le h))))
                subst kb
                have balance := ih a b l r
                simp only [Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
                simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (· + ka * Var.denote ctx va) balance
              · have smaller := Nat.le_of_ble_eq_true gt
                have coeff := Nat.sub_add_cancel (Nat.le_of_lt smaller)
                have balance := ih a b ((ka-kb,va)::l) r
                simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
                simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
                have value : ka * Var.denote ctx va = (ka-kb) * Var.denote ctx va + kb * Var.denote ctx va :=
                  (congrArg (· * Var.denote ctx va) coeff.symm).trans (Nat.add_mul ..)
                rw [value]
                simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (· + kb * Var.denote ctx va) balance
            · have smaller := Nat.le_of_ble_eq_true lt
              have coeff := Nat.sub_add_cancel (Nat.le_of_lt smaller)
              have balance := ih a b l ((kb-ka,va)::r)
              simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
              simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
              have value : kb * Var.denote ctx va = (kb-ka) * Var.denote ctx va + ka * Var.denote ctx va :=
                (congrArg (· * Var.denote ctx va) coeff.symm).trans (Nat.add_mul ..)
              rw [value]
              simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (· + ka * Var.denote ctx va) balance
          · have balance := ih ((ka,va)::a) b l ((kb,vb)::r)
            simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
            simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using balance
        · have balance := ih a ((kb,vb)::b) ((ka,va)::l) r
          simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
          simp only [Bool.cond_true, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using balance

private theorem cancelDenotation (ctx : Context) (fuel : Nat) (a b l r : Poly) :
    (Poly.denote_eq ctx (l.reverse ++ a, r.reverse ++ b) ↔ Poly.denote_eq ctx (Poly.cancelAux fuel a b l r)) ∧
    (Poly.denote_le ctx (l.reverse ++ a, r.reverse ++ b) ↔ Poly.denote_le ctx (Poly.cancelAux fuel a b l r)) := by
  have eq := cancelBalance ctx fuel a b l r
  simp only [Poly.denote_eq, Poly.denote_le, Poly.denote_append, Poly.denote_reverse]
  constructor
  · constructor
    · intro h
      rw [h] at eq
      exact Nat.add_right_cancel eq
    · intro h
      rw [h] at eq
      exact (Nat.add_left_cancel eq).symm
  · constructor
    · intro h
      exact Nat.le_of_add_le_add_right (eq ▸ Nat.add_le_add_left h _)
    · intro h
      exact Nat.le_of_add_le_add_left (eq ▸ Nat.add_le_add_right h _)

public theorem Nat.Internal.Linear.Poly.denote_eq_cancelAux :
    type_of% @_root_.Nat.Internal.Linear.Poly.denote_eq_cancelAux :=
  fun ctx fuel a b l r => (cancelDenotation ctx fuel a b l r).1.mp

public theorem Nat.Internal.Linear.Poly.of_denote_eq_cancelAux :
    type_of% @_root_.Nat.Internal.Linear.Poly.of_denote_eq_cancelAux :=
  fun ctx fuel a b l r => (cancelDenotation ctx fuel a b l r).1.mpr

public theorem Nat.Internal.Linear.Poly.denote_le_cancelAux :
    type_of% @_root_.Nat.Internal.Linear.Poly.denote_le_cancelAux :=
  fun ctx fuel a b l r => (cancelDenotation ctx fuel a b l r).2.mp

public theorem Nat.Internal.Linear.Poly.of_denote_le_cancelAux :
    type_of% @_root_.Nat.Internal.Linear.Poly.of_denote_le_cancelAux :=
  fun ctx fuel a b l r => (cancelDenotation ctx fuel a b l r).2.mpr

public theorem Nat.Internal.Linear.Expr.denote_toPoly_go :
    type_of% @_root_.Nat.Internal.Linear.Expr.denote_toPoly_go := by
  intro k p ctx e
  apply Expr.toPoly.go.induct
    (fun k e => ∀ p, (Expr.toPoly.go k e p).denote ctx = k * e.denote ctx + p.denote ctx)
    _ _ _ _ _ _ _ _ k e p
  · intro k l zero p
    simp only [Expr.toPoly.go, zero, Bool.cond_true, id_eq]
    change p.denote ctx = k*l + p.denote ctx
    rw [eq_of_beq zero, Nat.mul_zero, Nat.zero_add]
  · intro k l nonzero p
    simp only [Expr.toPoly.go, nonzero, Bool.cond_false]
    change (k*l) * (Var.denote ctx fixedVar) + p.denote ctx = k*l + p.denote ctx
    have unit (v : Var) (matchVar : Nat.beq v fixedVar = true) : Var.denote ctx v = 1 :=
      congrArg (Bool.rec (motive := fun _ => Nat) (ctx.get v) 1) matchVar
    have fixed := unit fixedVar (Nat.beq_refl fixedVar)
    exact congrArg (· + p.denote ctx) ((congrArg (k*l * ·) fixed).trans (Nat.mul_one _))
  · exact fun _ _ _ => rfl
  · intro k a b ia ib p
    change (Expr.toPoly.go k a (Expr.toPoly.go k b p)).denote ctx = k * (a.denote ctx + b.denote ctx) + p.denote ctx
    rw [ia, ib, Nat.mul_add, Nat.add_assoc]
  · intro k l a zero p
    simp only [Expr.toPoly.go, zero, Bool.cond_true, id_eq]
    change p.denote ctx = k*(l*a.denote ctx) + p.denote ctx
    rw [eq_of_beq zero, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
  · intro k l a nonzero ih p
    simp only [Expr.toPoly.go, nonzero, Bool.cond_false]
    change _ = k*(l*a.denote ctx) + p.denote ctx
    rw [ih, Nat.mul_assoc]
  · intro k a l zero p
    simp only [Expr.toPoly.go, zero, Bool.cond_true, id_eq]
    change p.denote ctx = k*(a.denote ctx*l) + p.denote ctx
    rw [eq_of_beq zero, Nat.mul_zero, Nat.mul_zero, Nat.zero_add]
  · intro k a l nonzero ih p
    simp only [Expr.toPoly.go, nonzero, Bool.cond_false]
    change _ = k*(a.denote ctx*l) + p.denote ctx
    rw [ih, Nat.mul_assoc, Nat.mul_comm l (a.denote ctx)]

public theorem Nat.Internal.Linear.Expr.denote_toPoly :
    type_of% @_root_.Nat.Internal.Linear.Expr.denote_toPoly := by
  intro ctx e
  change (Expr.toPoly.go 1 e []).denote ctx = _
  rw [Expr.denote_toPoly_go, Nat.one_mul]
  exact Nat.add_zero _

public theorem Nat.Internal.Linear.ExprCnstr.denote_toPoly :
    type_of% @_root_.Nat.Internal.Linear.ExprCnstr.denote_toPoly := by
  intro ctx c
  obtain ⟨kind, lhs, rhs⟩ := c
  cases kind with
  | false =>
    change (lhs.toPoly.denote ctx ≤ rhs.toPoly.denote ctx) = (lhs.denote ctx ≤ rhs.denote ctx)
    rw [Expr.denote_toPoly, Expr.denote_toPoly]
  | true =>
    change (lhs.toPoly.denote ctx = rhs.toPoly.denote ctx) = (lhs.denote ctx = rhs.denote ctx)
    rw [Expr.denote_toPoly, Expr.denote_toPoly]

-- The recursive proposition used by the strict natural order.
local macro "compareProp" : term =>
  `(fun a b : Nat => Nat.rec (motive := fun _ => Nat → Prop) (fun _ => True)
    (fun _ smaller b => Nat.rec (motive := fun _ => Prop) False (fun k _ => smaller k) b) a b)

private theorem compareTrue (a b : Nat) (h : a ≤ b) : compareProp a b = True := by
  induction a generalizing b with
  | zero => rfl
  | succ a ih =>
    cases b with
    | zero => exact (Nat.not_succ_le_zero _ h).elim
    | succ b => exact ih b (Nat.le_of_succ_le_succ h)

private theorem compareFalse (a b : Nat) (h : ¬a ≤ b) : compareProp a b = False := by
  induction a generalizing b with
  | zero => exact (h (Nat.zero_le b)).elim
  | succ a ih =>
    cases b with
    | zero => rfl
    | succ b => exact ih b fun le => h (Nat.succ_le_succ le)

private theorem compareOfIff {a b c d : Nat} (equiv : a ≤ b ↔ c ≤ d) :
    compareProp a b = compareProp c d := by
  by_cases h : a ≤ b
  · exact (compareTrue _ _ h).trans (compareTrue _ _ (equiv.mp h)).symm
  · exact (compareFalse _ _ h).trans (compareFalse _ _ (fun le => h (equiv.mpr le))).symm

public theorem Nat.Internal.Linear.Poly.denote_le_cancel_eq (ctx : Context) (p q : Poly) :
    compareProp ((Poly.cancel p q).1.denote ctx) ((Poly.cancel p q).2.denote ctx) =
    compareProp (p.denote ctx) (q.denote ctx) :=
  compareOfIff ⟨_root_.Nat.Internal.Linear.Poly.of_denote_le_cancel,
    _root_.Nat.Internal.Linear.Poly.denote_le_cancel⟩

public theorem Nat.Simproc.add_le_add_le (a c : Nat) {b d : Nat} (h : b ≤ d) :
    compareProp (a+b) (c+d) = compareProp a (c + (d-b)) := by
  apply compareOfIff
  rw [← Nat.add_sub_assoc h]
  exact (Nat.le_sub_iff_add_le (Nat.le_trans h (Nat.le_add_left d c))).symm

public theorem Nat.Simproc.add_le_add_ge (a c : Nat) {b d : Nat} (h : b ≥ d) :
    compareProp (a+b) (c+d) = compareProp (a + (b-d)) c := by
  apply compareOfIff
  rw [← Nat.add_sub_assoc h]
  exact Nat.sub_le_iff_le_add.symm

public theorem Nat.Simproc.add_le_gt (a : Nat) {b c : Nat} (h : b > c) :
    compareProp (a+b) c = False :=
  compareFalse _ _ (Nat.not_le_of_gt (Nat.lt_of_lt_of_le h (Nat.le_add_left b a)))

public theorem Nat.Simproc.le_add_le (a : Nat) {b c : Nat} (h : a ≤ c) :
    compareProp a (b+c) = True :=
  compareTrue _ _ (Nat.le_trans h (Nat.le_add_left c b))

public theorem Lean.Grind.Nat.lo_eq_true_of_lo (u v k₁ k₂ : Nat) : _root_.Lean.Grind.isLE k₂ k₁ = true → u + k₁ ≤ v → compareProp (u + k₂) (v) = True :=
  fun test h => compareTrue _ _ (Nat.le_trans (Nat.add_le_add_left (of_decide_eq_true test) u) h)

public theorem Lean.Grind.Nat.le_eq_true_of_lo (u v k : Nat) : u + k ≤ v → compareProp (u) (v) = True :=
  fun h => compareTrue _ _ (Nat.le_trans (Nat.le_add_right u k) h)

public theorem Lean.Grind.Nat.le_eq_true_of_le (u v : Nat) : u ≤ v → compareProp (u) (v) = True :=
  compareTrue u v

public theorem Lean.Grind.Nat.ro_eq_true_of_lo (u v k₁ k₂ : Nat) : u + k₁ ≤ v → compareProp (u) (v + k₂) = True :=
  fun h => compareTrue _ _ (Nat.le_trans (Nat.le_trans (Nat.le_add_right u k₁) h) (Nat.le_add_right v k₂))

public theorem Lean.Grind.Nat.ro_eq_true_of_le (u v k : Nat) : u ≤ v → compareProp (u) (v + k) = True :=
  fun h => compareTrue _ _ (Nat.le_trans h (Nat.le_add_right v k))

public theorem Lean.Grind.Nat.ro_eq_true_of_ro (u v k₁ k₂ : Nat) : _root_.Lean.Grind.isLE k₁ k₂ = true → u ≤ v + k₁ → compareProp (u) (v + k₂) = True :=
  fun test h => compareTrue _ _ (Nat.le_trans h (Nat.add_le_add_left (of_decide_eq_true test) v))

public theorem Lean.Grind.Nat.lo_eq_false_of_le (u v k : Nat) : _root_.Lean.Grind.isLt 0 k = true → u ≤ v → compareProp (v + k) (u) = False :=
  fun test h => compareFalse _ _ (_root_.Lean.Grind.Nat.unsat_le_lo u v k test h)

public theorem Lean.Grind.Nat.le_eq_false_of_lo (u v k : Nat) : _root_.Lean.Grind.isLt 0 k = true → u + k ≤ v → compareProp (v) (u) = False :=
  fun test h => compareFalse _ _ (fun le => _root_.Lean.Grind.Nat.unsat_le_lo v u k test le h)

public theorem Lean.Grind.Nat.lo_eq_false_of_lo (u v k₁ k₂ : Nat) : _root_.Lean.Grind.isLt 0 (k₁+k₂) = true → u + k₁ ≤ v → compareProp (v + k₂) (u) = False :=
  fun test h => compareFalse _ _ (_root_.Lean.Grind.Nat.unsat_lo_lo u v k₁ k₂ test h)

public theorem Lean.Grind.Nat.ro_eq_false_of_lo (u v k₁ k₂ : Nat) : _root_.Lean.Grind.isLt k₂ k₁ = true → u + k₁ ≤ v → compareProp (v) (u + k₂) = False :=
  fun test h => compareFalse _ _ (_root_.Lean.Grind.Nat.unsat_lo_ro u v k₁ k₂ test h)

public theorem Lean.Grind.Nat.lo_eq_false_of_ro (u v k₁ k₂ : Nat) : _root_.Lean.Grind.isLt k₁ k₂ = true → u ≤ v + k₁ → compareProp (v + k₂) (u) = False :=
  fun test h => compareFalse _ _ (fun le => _root_.Lean.Grind.Nat.unsat_lo_ro v u k₂ k₁ test le h)

end OmegaChecks.InitPort.Alternatives
