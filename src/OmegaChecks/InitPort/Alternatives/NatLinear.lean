module

public import Init.Data.Nat.Internal.Linear

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

end OmegaChecks.InitPort.Alternatives
