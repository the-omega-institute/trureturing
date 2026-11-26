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
    omega
  | succ fuel ih =>
    cases a with
    | nil =>
      cases b <;> simp only [Poly.cancelAux, Poly.denote_append, Poly.denote_reverse,
        Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.add_zero] <;> omega
    | cons termA a =>
      obtain ⟨ka,va⟩ := termA
      cases b with
      | nil =>
        simp only [Poly.cancelAux, Poly.denote_append, Poly.denote_reverse, Poly.denote,
          Nat.add_zero]
        omega
      | cons termB b =>
        obtain ⟨kb,vb⟩ := termB
        rw [Poly.cancelAux]
        cases ab : Nat.blt va vb
        · cases ba : Nat.blt vb va
          · have equal : va = vb := Nat.le_antisymm
              (Nat.le_of_not_gt (fun h => Bool.noConfusion (ba.symm.trans (Nat.blt_eq.mpr h))))
              (Nat.le_of_not_gt (fun h => Bool.noConfusion (ab.symm.trans (Nat.blt_eq.mpr h))))
            subst vb
            cases lt : Nat.blt ka kb
            · cases gt : Nat.blt kb ka
              · have equal : ka = kb := Nat.le_antisymm
                  (Nat.le_of_not_gt (fun h => Bool.noConfusion (gt.symm.trans (Nat.blt_eq.mpr h))))
                  (Nat.le_of_not_gt (fun h => Bool.noConfusion (lt.symm.trans (Nat.blt_eq.mpr h))))
                subst kb
                have balance := ih a b l r
                simp only [Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
                omega
              · have smaller := Nat.blt_eq.mp gt
                have mul := Nat.mul_le_mul_right (Var.denote ctx va) (Nat.le_of_lt smaller)
                have balance := ih a b ((ka-kb,va)::l) r
                simp only [Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.mul_sub_right_distrib] at balance
                simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
                omega
            · have smaller := Nat.blt_eq.mp lt
              have mul := Nat.mul_le_mul_right (Var.denote ctx va) (Nat.le_of_lt smaller)
              have balance := ih a b l ((kb-ka,va)::r)
              simp only [Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.mul_sub_right_distrib] at balance
              simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
              omega
          · have balance := ih ((ka,va)::a) b l ((kb,vb)::r)
            simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
            simp only [Bool.cond_true, Bool.cond_false, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
            omega
        · have balance := ih a ((kb,vb)::b) ((ka,va)::l) r
          simp only [Poly.denote, Nat.add_eq, Nat.mul_eq] at balance
          simp only [Bool.cond_true, Poly.denote, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
          omega

private theorem cancelDenotation (ctx : Context) (fuel : Nat) (a b l r : Poly) :
    (Poly.denote_eq ctx (l.reverse ++ a, r.reverse ++ b) ↔ Poly.denote_eq ctx (Poly.cancelAux fuel a b l r)) ∧
    (Poly.denote_le ctx (l.reverse ++ a, r.reverse ++ b) ↔ Poly.denote_le ctx (Poly.cancelAux fuel a b l r)) := by
  have eq := cancelBalance ctx fuel a b l r
  simp only [Poly.denote_eq, Poly.denote_le, Poly.denote_append, Poly.denote_reverse]
  exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩⟩

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
