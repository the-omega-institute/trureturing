module
import all Init.Grind.Ring.CommSolver

/-! Structural decrease in reverse lexicographic comparison of monomials. -/

open Lean.Grind Lean.Grind.CommRing
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


section
attribute [local instance] Semiring.natCast Ring.intCast

public theorem Lean.Grind.IsCharP.ofNat_eq_zero_iff : type_of% @_root_.Lean.Grind.IsCharP.ofNat_eq_zero_iff := by
  intro α p ring char x
  have h := @IsCharP.ofNat_ext_iff α ring p char x 0
  exact h.trans ⟨fun e => e.trans (Nat.zero_mod _), fun e => e.trans (Nat.zero_mod _).symm⟩

public theorem Lean.Grind.IsCharP.intCast_emod : type_of% @_root_.Lean.Grind.IsCharP.intCast_emod := by
  intro p α ring char x
  have hz : (Int.cast (R := α) (p : Int)) = 0 := (Ring.intCast_natCast ..).trans ((IsCharP.natCast_eq_zero_iff p _).mpr (Nat.mod_self _))
  have h := congrArg (Int.cast (R := α)) (Int.emod_add_mul_ediv x p)
  rwa [Ring.intCast_add, Ring.intCast_mul, hz, Semiring.zero_mul, Semiring.add_zero] at h

public theorem Lean.Grind.IsCharP.intCast_eq_zero_iff : type_of% @_root_.Lean.Grind.IsCharP.intCast_eq_zero_iff := by
  intro p α ring char x
  cases x with
  | ofNat n =>
    change (Int.cast (R := α) (n : Int)) = 0 ↔ Int.ofNat (n % p) = 0
    rw [Ring.intCast_natCast]
    exact (IsCharP.natCast_eq_zero_iff p n).trans Int.ofNat_eq_zero.symm
  | negSucc n =>
    change (Int.cast (R := α) (-((n+1 : Nat) : Int))) = 0 ↔ (-((n+1 : Nat) : Int)) % p = 0
    rw [Ring.intCast_neg, Ring.intCast_natCast]
    exact ((_root_.Lean.Grind.AddCommGroup.neg_eq_zero _).trans (IsCharP.natCast_eq_zero_iff p (n+1))).trans
      (Nat.dvd_iff_mod_eq_zero.symm.trans (Int.ofNat_dvd.symm.trans (Int.dvd_neg.symm.trans Int.dvd_iff_emod_eq_zero)))
end

public theorem Lean.Grind.CommRing.Poly.denote_addConstC :
    type_of% @_root_.Lean.Grind.CommRing.Poly.denote_addConstC := by
  intro α c ring char ctx p k
  induction p with
  | num l => exact (IsCharP.intCast_emod (α := α) (p := c) (l+k)).trans (Ring.intCast_add ..)
  | add l m p ih =>
    exact (congrArg (fun z : α => l • m.denote ctx + z) ih).trans (Semiring.add_assoc ..).symm

private theorem coefficientSum {α : Type u} [Ring α] (c : Nat) [IsCharP α c]
    (k l : Int) (x : α) : (((k+l) % c) : Int) • x = k • x + l • x := by
  rw [Ring.zsmul_eq_intCast_mul, IsCharP.intCast_emod, Ring.intCast_add, Semiring.right_distrib,
    Ring.zsmul_eq_intCast_mul (k := k), Ring.zsmul_eq_intCast_mul (k := l)]

private theorem zeroTerms {α : Type u} [Ring α] (c : Nat) [IsCharP α c] (k l : Int) (x : α)
    (zero : (k+l) % c = 0) : k • x + l • x = 0 := by
  rw [← coefficientSum c, zero, Ring.zsmul_eq_intCast_mul, Ring.intCast_zero, Semiring.zero_mul]

public theorem Lean.Grind.CommRing.Poly.denote_combineC :
    type_of% @_root_.Lean.Grind.CommRing.Poly.denote_combineC := by
  intro α c ring char ctx p q
  apply Poly.combineC.induct_unfolding c (fun s t u => u.denote ctx = s.denote ctx + t.denote ctx) _ _ _ _ _ _ _ p q
  · exact fun k l => (IsCharP.intCast_emod (α := α) c (k+l)).trans (Ring.intCast_add ..)
  · intro k l n q
    exact (Lean.Grind.CommRing.Poly.denote_addConstC ctx (.add l n q) k).trans (Semiring.add_comm ..)
  · exact fun _ _ _ _ => Lean.Grind.CommRing.Poly.denote_addConstC ..
  · intro k m p l n q same _ zero ih
    cases _root_.Lean.Grind.CommRing.Mon.eq_of_grevlex same
    have hz := zeroTerms (α := α) c k l (m.denote ctx) (eq_of_beq zero)
    change _ = (k • m.denote ctx + p.denote ctx) + (l • m.denote ctx + q.denote ctx)
    rw [ih]
    calc
      _ = (k • m.denote ctx + l • m.denote ctx) + (p.denote ctx + q.denote ctx) := by rw [hz, Semiring.add_comm 0, Semiring.add_zero]
      _ = _ := by rw [Semiring.add_assoc, ← Semiring.add_assoc (l • _) _ _, Semiring.add_comm (l • _) (p.denote ctx),
        Semiring.add_assoc, ← Semiring.add_assoc]
  · intro k m p l n q same _ _ ih
    cases _root_.Lean.Grind.CommRing.Mon.eq_of_grevlex same
    change ((k+l) % c) • m.denote ctx + _ = (k • m.denote ctx + p.denote ctx) + (l • m.denote ctx + q.denote ctx)
    rw [ih, coefficientSum, Semiring.add_assoc, ← Semiring.add_assoc (l • _) _ _, Semiring.add_comm (l • _) (p.denote ctx),
      Semiring.add_assoc, ← Semiring.add_assoc]
  · intro k m p l n q _ ih
    exact (congrArg (k • m.denote ctx + ·) ih).trans (Semiring.add_assoc ..).symm
  · intro k m p l n q _ ih
    exact (congrArg (l • n.denote ctx + ·) ih).trans ((Semiring.add_assoc ..).symm.trans ((congrArg (· + q.denote ctx) (Semiring.add_comm ..)).trans (Semiring.add_assoc ..)))

private theorem insertTerm {α : Type u} [Ring α] (c : Nat) [IsCharP α c]
    (ctx : Context α) (k : Int) (m : Mon) (p : Poly) :
    (Poly.insertC.go m c k p).denote ctx = k • m.denote ctx + p.denote ctx := by
  apply Poly.insertC.go.induct_unfolding m c k (fun s t => t.denote ctx = k • m.denote ctx + s.denote ctx) _ _ _ _ _ p
  · exact fun _ => rfl
  · intro l n p same _ zero
    cases _root_.Lean.Grind.CommRing.Mon.eq_of_grevlex same
    change _ = k • m.denote ctx + (l • m.denote ctx + p.denote ctx)
    rw [← Semiring.add_assoc, zeroTerms c k l _ (eq_of_beq zero), Semiring.add_comm 0, Semiring.add_zero]
  · intro l n p same _ _
    cases _root_.Lean.Grind.CommRing.Mon.eq_of_grevlex same
    exact (congrArg (· + p.denote ctx) (coefficientSum c k l (m.denote ctx))).trans (Semiring.add_assoc ..)
  · exact fun _ _ _ _ => rfl
  · intro l n p _ ih
    change l • n.denote ctx + _ = k • m.denote ctx + (l • n.denote ctx + p.denote ctx)
    rw [ih, ← Semiring.add_assoc, Semiring.add_comm (l • _) (k • _), Semiring.add_assoc]

section
attribute [local instance] Ring.intCast

public theorem Lean.Grind.CommRing.Poly.denote_insertC :
    type_of% @_root_.Lean.Grind.CommRing.Poly.denote_insertC := by
  intro α c ring char ctx k m p
  rw [Poly.insertC.eq_def]
  dsimp only
  cases h : (k % (c : Int) == 0) with
  | false =>
    change (Poly.insertC.go m c (k % c) p).denote ctx = _
    rw [insertTerm, Ring.zsmul_eq_intCast_mul, IsCharP.intCast_emod]
  | true =>
    have hz : Int.cast (R := α) k = 0 :=
      (IsCharP.intCast_emod (α := α) c k).symm.trans ((congrArg (Int.cast (R := α)) (eq_of_beq h)).trans Ring.intCast_zero)
    change p.denote ctx = _
    rw [hz, Semiring.zero_mul, Semiring.add_comm 0, Semiring.add_zero]

private theorem coefficientProduct {α : Type u} [Ring α] (c : Nat) [IsCharP α c]
    (k l : Int) (x : α) : ((k*l) % c) • x = (k : α) * (l • x) := by
  rw [Ring.zsmul_eq_intCast_mul, IsCharP.intCast_emod, Ring.intCast_mul,
    Semiring.mul_assoc, Ring.zsmul_eq_intCast_mul]

private theorem multiplyTerms {α : Type u} [Ring α] (c : Nat) [IsCharP α c]
    (ctx : Context α) (k : Int) (p : Poly) :
    (Poly.mulConstC.go k c p).denote ctx = (k : α) * p.denote ctx := by
  apply Poly.mulConstC.go.induct_unfolding k c (fun s t => t.denote ctx = (k : α) * s.denote ctx) _ _ _ p
  · exact fun l => (IsCharP.intCast_emod (α := α) c (k*l)).trans (Ring.intCast_mul ..)
  · intro l m p _ zero ih
    have hz : (k*l) % c = 0 := eq_of_beq zero
    change _ = (k : α) * (l • m.denote ctx + p.denote ctx)
    rw [ih, Semiring.left_distrib, ← coefficientProduct c, hz, Ring.zsmul_eq_intCast_mul, Ring.intCast_zero,
      Semiring.zero_mul, Semiring.add_comm 0, Semiring.add_zero]
  · intro l m p _ _ ih
    change _ • m.denote ctx + _ = (k : α) * (l • m.denote ctx + p.denote ctx)
    rw [ih, coefficientProduct, Semiring.left_distrib]

public theorem Lean.Grind.CommRing.Poly.denote_mulConstC :
    type_of% @_root_.Lean.Grind.CommRing.Poly.denote_mulConstC := by
  intro α c ring char ctx k p
  rw [Poly.mulConstC.eq_def]
  dsimp only
  cases zero : (k % (c : Int) == 0) with
  | true =>
    change Int.cast (R := α) 0 = _
    rw [← IsCharP.intCast_emod (p := c) (x := k), eq_of_beq zero, Ring.intCast_zero, Semiring.zero_mul]
  | false =>
    cases one : (k % (c : Int) == 1) with
    | true =>
      change p.denote ctx = _
      rw [← IsCharP.intCast_emod (p := c) (x := k), eq_of_beq one, Ring.intCast_one, Semiring.one_mul]
    | false => exact multiplyTerms c ctx k p
end

end OmegaChecks.InitPort.Alternatives
