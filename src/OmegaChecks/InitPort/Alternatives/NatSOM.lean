module
import all Init.Data.Nat.Internal.SOM

/-! The value of a sum of monomials is preserved when equal monomials are combined. -/

open Nat.Internal.SOM
namespace OmegaChecks.InitPort.Alternatives

private theorem denoteCons (ctx : Nat.Internal.Linear.Context) (k : Nat) (m : Mon) (p : Poly) :
    Poly.denote ctx ((k,m)::p) = k*m.denote ctx + p.denote ctx := rfl

public theorem Nat.Internal.SOM.Poly.add_denote.go :
    type_of% (private_decl% @_root_.Nat.Internal.SOM.Poly.add_denote.go) := by
  intro ctx fuel p q
  induction fuel generalizing p q with
  | zero => exact Poly.append_denote ctx p q
  | succ fuel ih =>
    cases q with
    | nil => exact (Nat.add_zero _).symm
    | cons term q =>
      cases p with
      | nil =>
        cases term
        exact (Nat.zero_add _).symm
      | cons head p =>
        obtain ⟨k,m⟩ := head
        obtain ⟨l,n⟩ := term
        rw [_root_.Nat.Internal.SOM.Poly.add.go]
        cases small : decide (m < n) with
        | true =>
          simp only [Bool.cond_true, denoteCons, ih, Nat.add_eq, Nat.mul_eq]
          exact (Nat.add_assoc ..).symm
        | false =>
          cases large : decide (n < m) with
          | true =>
            simp only [Bool.cond_false, Bool.cond_true, denoteCons, ih, Nat.add_eq, Nat.mul_eq]
            rw [Nat.add_left_comm, Nat.add_assoc]
          | false =>
            have eq := List.le_antisymm (of_decide_eq_false large) (of_decide_eq_false small)
            cases eq
            cases zero : (k+l == 0) with
            | true =>
              simp only [Bool.cond_false, Bool.cond_true, denoteCons, ih, Nat.add_eq, Nat.mul_eq]
              have z : k+l = 0 := eq_of_beq zero
              obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp z
              rw [Nat.zero_mul, Nat.zero_add, Nat.zero_add]
            | false =>
              simp only [Bool.cond_false, denoteCons, ih, Nat.add_eq, Nat.mul_eq, Nat.add_mul, Nat.add_assoc]
              rw [Nat.add_left_comm (l * _) (Poly.denote ctx p)]

end OmegaChecks.InitPort.Alternatives
