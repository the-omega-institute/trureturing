module
import all Init.Grind.Ring.CommSolver

/-! Structural decrease in reverse lexicographic comparison of monomials. -/

open Lean.Grind.CommRing
namespace OmegaChecks.InitPort.Alternatives

private theorem smallerTail (p : Power) (m : Mon) : sizeOf m < sizeOf (Mon.mult p m) :=
  Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (sizeOf p)))

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_2 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_2 := by
  intro p m q n
  apply Prod.Lex.left
  exact smallerTail p m

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_3 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_3 := by
  intro p m q n
  apply Prod.Lex.left
  exact smallerTail p m

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_4 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_4 := by
  intro p m q n
  apply Prod.Lex.right
  exact smallerTail q n

private theorem tailSize (k : Int) (m : Mon) (p : Poly) : sizeOf p < sizeOf (Poly.add k m p) :=
  Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (sizeOf k)))
    (Nat.le_add_right _ (sizeOf m)))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_1 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_1 :=
  fun k m p l n q => Nat.add_lt_add_of_lt_of_le (tailSize k m p) (Nat.le_of_lt (tailSize l n q))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_2 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_2 :=
  fun k m p l n q => Nat.add_lt_add_right (tailSize k m p) (sizeOf (Poly.add l n q))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_3 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_3 :=
  fun k m p l n q => Nat.add_lt_add_left (tailSize l n q) (sizeOf (Poly.add k m p))

private theorem matchingPowers {p q : Power} {m n : Mon} {o : Ordering} (x : (p.x == q.x) = true)
    (ih : o = .eq → m = n) (done : o.then (powerRevlex p.k q.k) = .eq) : Mon.mult p m = Mon.mult q n := by
  obtain ⟨order, ex⟩ := Ordering.then_eq_eq.mp done
  obtain ⟨v,k⟩ := p
  obtain ⟨u,l⟩ := q
  have hv : v = u := eq_of_beq x
  have hk : k = l := eq_of_powerRevlex ex
  cases hv
  cases hk
  exact congrArg (Mon.mult _) (ih order)

public theorem Lean.Grind.CommRing.Mon.eq_of_revlexWF : type_of% @_root_.Lean.Grind.CommRing.Mon.eq_of_revlexWF := by
  intro a b
  apply Mon.revlexWF.induct_unfolding (fun m n o => o = .eq → m = n) _ _ _ _ _ _ a b
  · exact fun _ => rfl
  · exact fun _ _ h => nomatch h
  · exact fun _ _ h => nomatch h
  · exact fun _ _ _ _ hx ih h => matchingPowers hx ih h
  · exact fun _ _ _ _ _ _ _ h => nomatch (Ordering.then_eq_eq.mp h).2
  · exact fun _ _ _ _ _ _ _ h => nomatch (Ordering.then_eq_eq.mp h).2

public theorem Lean.Grind.CommRing.Mon.eq_of_revlexFuel : type_of% @_root_.Lean.Grind.CommRing.Mon.eq_of_revlexFuel := by
  intro fuel a b
  apply Mon.revlexFuel.induct_unfolding (fun _ m n o => o = .eq → m = n) _ _ _ _ _ _ _ fuel a b
  · exact fun _ _ => Lean.Grind.CommRing.Mon.eq_of_revlexWF
  · exact fun _ _ => rfl
  · exact fun _ _ _ h => nomatch h
  · exact fun _ _ _ h => nomatch h
  · exact fun _ _ _ _ _ hx ih h => matchingPowers hx ih h
  · exact fun _ _ _ _ _ _ _ _ h => nomatch (Ordering.then_eq_eq.mp h).2
  · exact fun _ _ _ _ _ _ _ _ h => nomatch (Ordering.then_eq_eq.mp h).2
end OmegaChecks.InitPort.Alternatives
