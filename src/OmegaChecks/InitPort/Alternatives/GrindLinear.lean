module
import all Init.Grind.Ordered.Linarith
import all Init.Data.Int.Linear

/-! Constructive termination and certificate proofs for the linear arithmetic solvers. -/

namespace OmegaChecks.InitPort.Alternatives

open Lean.Grind Lean.Grind.Linarith

private theorem smallerPoly (k : Int) (x : Var) (p : Poly) : sizeOf p < sizeOf (.add k x p : Poly) :=
  Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (sizeOf k)))
    (Nat.le_add_right _ (sizeOf x)))

public theorem Lean.Grind.Linarith.Poly.combine._unary._proof_2 :
    type_of% @_root_.Lean.Grind.Linarith.Poly.combine._unary._proof_2 := by
  intro k x p l y q
  exact Nat.add_lt_add_right (smallerPoly k x p) _

public theorem Lean.Grind.Linarith.Poly.combine._unary._proof_3 :
    type_of% @_root_.Lean.Grind.Linarith.Poly.combine._unary._proof_3 := by
  intro k x p l y q
  exact Nat.add_lt_add_left (smallerPoly l y q) _

public theorem Lean.Grind.Linarith.diseq_unsat :
    type_of% @_root_.Lean.Grind.Linarith.diseq_unsat :=
  fun _ h => h rfl

public theorem Lean.Grind.Linarith.lt_unsat :
    type_of% @_root_.Lean.Grind.Linarith.lt_unsat :=
  fun _ => Preorder.lt_irrefl _

public theorem Lean.Grind.Linarith.zero_ne_one_of_field :
    type_of% @_root_.Lean.Grind.Linarith.zero_ne_one_of_field := by
  intro α _ ctx p cert one zero
  have eq := eq_of_beq (show (p == .add 1 0 .nil) = true from cert)
  rw [eq, Poly.denote'_eq_denote] at zero
  change (1 : Int) • (0 : Var).denote ctx + 0 = 0 at zero
  rw [IntModule.one_zsmul, AddCommMonoid.add_zero, one] at zero
  exact Field.zero_ne_one zero.symm

public theorem Lean.Grind.Linarith.zero_lt_one :
    type_of% @_root_.Lean.Grind.Linarith.zero_lt_one := by
  intro α _ _ _ _ _ _ ctx p cert one
  have eq := eq_of_beq (show (p == .add (-1) 0 .nil) = true from cert)
  rw [eq, Poly.denote'_eq_denote]
  change (-1 : Int) • (0 : Var).denote ctx + 0 < 0
  rw [IntModule.neg_zsmul, IntModule.one_zsmul, AddCommMonoid.add_zero, one]
  exact OrderedRing.neg_one_lt_zero

public theorem Lean.Grind.Linarith.imp_eq :
    type_of% @_root_.Lean.Grind.Linarith.imp_eq := by
  intro α _ ctx p x y cert zero
  have eq := eq_of_beq (show (p == .add 1 x (.add (-1) y .nil)) = true from cert)
  rw [eq, Poly.denote'_eq_denote] at zero
  change (1 : Int) • x.denote ctx + ((-1 : Int) • y.denote ctx + 0) = 0 at zero
  rw [IntModule.neg_zsmul,
      IntModule.one_zsmul, IntModule.one_zsmul, AddCommMonoid.add_zero,
      ← AddCommGroup.sub_eq_add_neg] at zero
  exact AddCommGroup.sub_eq_zero_iff.mp zero

public theorem Int.Internal.Linear.Poly.coeff_k_eq_coeff :
    type_of% @_root_.Int.Internal.Linear.Poly.coeff_k_eq_coeff := by
  intro p x
  induction p with
  | num => rfl
  | add a y p ih =>
    change Bool.rec (p.coeff_k x) a (Nat.beq x y) =
      (bif Nat.beq x y then a else p.coeff x)
    rw [ih]
    cases Nat.beq x y <;> rfl

public theorem Int.Internal.Linear.le_unsat :
    type_of% @_root_.Int.Internal.Linear.le_unsat := by
  intro ctx p bad le
  cases p with
  | add => contradiction
  | num n =>
    exact Int.not_le_of_gt (of_decide_eq_true bad) le

end OmegaChecks.InitPort.Alternatives
