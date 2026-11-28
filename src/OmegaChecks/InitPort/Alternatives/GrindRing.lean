module
public import OmegaChecks.InitPort.Alternatives.GrindSemiringAdapter
import all Init.Grind.Ring.CommSemiringAdapter
import all Init.Grind.Ring.CommSolver
import all Init.Grind.Ring.Envelope

/-! Constructive proofs for the polynomial normalizer and its ring certificates. -/

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

public theorem Lean.Grind.CommRing.Mon.revlex_k_eq_revlex :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlex_k_eq_revlex := by
  intro m n
  unfold Mon.revlex_k Mon.revlex
  generalize hugeFuel = fuel
  induction fuel generalizing m n with
  | zero => rfl
  | succ f ih =>
    cases m with
    | unit => cases n <;> rfl
    | mult p m =>
      cases n with
      | unit => rfl
      | mult q n =>
        simp only [Mon.revlexFuel]
        cases h : Nat.beq p.x q.x <;> cases t : p.x.blt q.x <;>
          simp only [show (p.x == q.x) = Nat.beq p.x q.x from rfl, h, cond, ih] <;> rw [Ordering.then'_eq_then] <;> try rw [powerRevlex_k_eq_powerRevlex]

public theorem Lean.Grind.CommRing.Poly.addConst_k_eq_addConst :
    type_of% @_root_.Lean.Grind.CommRing.Poly.addConst_k_eq_addConst := by
  intro p k
  unfold Poly.addConst_k Poly.addConst
  rw [Int.beq'_eq_beq]
  cases h : @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k 0 with
  | true => rfl
  | false =>
    induction p with
    | num => rfl
    | add c m t ih => exact congrArg (Poly.add c m) ih

public theorem Lean.Grind.CommRing.denoteInt_eq :
    type_of% @_root_.Lean.Grind.CommRing.denoteInt_eq := by
  intro α ring k
  cases k with
  | ofNat n =>
    change OfNat.ofNat n = _
    exact (Semiring.ofNat_eq_natCast (α := α) n).trans (Ring.intCast_natCast n).symm
  | negSucc n =>
    change -OfNat.ofNat (n+1) = _
    rw [Semiring.ofNat_eq_natCast, ← Ring.intCast_natCast, ← Ring.intCast_neg]
    rfl

public theorem Lean.Grind.CommRing.intCast_eq_denoteInt :
    type_of% @_root_.Lean.Grind.CommRing.intCast_eq_denoteInt :=
  fun {_} _ b => (_root_.Lean.Grind.CommRing.denoteInt_eq b).symm

public theorem Lean.Grind.CommRing.Poly.mulConst_k_eq_mulConst :
    type_of% @_root_.Lean.Grind.CommRing.Poly.mulConst_k_eq_mulConst := by
  intro k p
  unfold Poly.mulConst_k Poly.mulConst
  rw [Int.beq'_eq_beq, Int.beq'_eq_beq]
  cases h : @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k 0 with
  | true => rfl
  | false =>
    cases h' : @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k 1 with
    | true => rfl
    | false =>
      induction p with
      | num => rfl
      | add c m t ih => exact congrArg (Poly.add (k*c) m) ih

public theorem Lean.Grind.CommRing.Poly.mulMon_k_eq_mulMon :
    type_of% @_root_.Lean.Grind.CommRing.Poly.mulMon_k_eq_mulMon := by
  intro k m p
  unfold Poly.mulMon_k Poly.mulMon
  rw [Int.beq'_eq_beq]
  cases hz : @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k 0 with
  | true => rfl
  | false =>
    cases m with
    | unit => exact _root_.Lean.Grind.CommRing.Poly.mulConst_k_eq_mulConst ..
    | mult h m =>
      induction p with
      | num j =>
        change (Bool.rec (motive := fun _ => Poly) (.add (k*j) (.mult h m) (.num 0)) (.num 0) (Int.beq' j 0)) =
          (bif @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) j 0 then .num 0 else
            .add (k*j) (.mult h m) (.num 0))
        rw [Int.beq'_eq_beq]
        cases @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) j 0 <;> rfl
      | add j w p ih =>
        change Poly.add _ _ _ = Poly.add _ _ _
        rw [Mon.mul_k_eq_mul]
        exact congrArg (Poly.add (k*j) ((Mon.mult h m).mul w)) ih

public theorem Lean.Grind.CommRing.inv_int_eqC :
    type_of% @_root_.Lean.Grind.CommRing.inv_int_eqC := by
  intro α c _ _ b nonzero
  apply Field.mul_inv_cancel
  intro h
  have zero := (IsCharP.intCast_eq_zero_iff (α := α) c b).mp ((_root_.Lean.Grind.CommRing.denoteInt_eq b).symm.trans h)
  exact (bne_iff_ne.mp nonzero) zero

public theorem Lean.Grind.CommRing.inv_int_eq :
    type_of% @_root_.Lean.Grind.CommRing.inv_int_eq := by
  intro α _ _ b nonzero
  apply _root_.Lean.Grind.CommRing.inv_int_eqC (c := 0)
  rw [Int.ofNat_zero, Int.emod_zero]
  exact nonzero

public theorem Lean.Grind.CommRing.inv_zero_eqC :
    type_of% @_root_.Lean.Grind.CommRing.inv_zero_eqC := by
  intro α c _ _ b zero
  have h := (IsCharP.intCast_eq_zero_iff (α := α) c b).mpr (eq_of_beq zero)
  rw [_root_.Lean.Grind.CommRing.denoteInt_eq, h, Field.inv_zero]

private theorem compareDegrees (x y : Nat) (tie : Ordering) :
    Bool.rec (Bool.rec Ordering.gt Ordering.lt (x.blt y)) tie (x.beq y) =
      (compare x y).then tie := by
  cases eq : x.beq y with
  | true =>
    have same := Nat.eq_of_beq_eq_true eq
    change tie = (compareOfLessAndEq x y).then tie
    rw [compareOfLessAndEq, ite_eq_right (same ▸ Nat.lt_irrefl x), ite_eq_left same]
    rfl
  | false =>
    cases lt : x.blt y with
    | true =>
      change Ordering.lt = (compareOfLessAndEq x y).then tie
      rw [compareOfLessAndEq, ite_eq_left (show x < y from Nat.le_of_ble_eq_true lt)]
      rfl
    | false =>
      have ne : x ≠ y := by
        intro h
        cases h
        exact Bool.noConfusion ((Nat.beq_refl x).symm.trans eq)
      have nlt : ¬ x < y := fun h => Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans lt)
      change Ordering.gt = (compareOfLessAndEq x y).then tie
      rw [compareOfLessAndEq, ite_eq_right nlt, ite_eq_right ne]
      rfl

public theorem Lean.Grind.CommRing.Mon.grevlex_k_eq_grevlex :
    type_of% @_root_.Lean.Grind.CommRing.Mon.grevlex_k_eq_grevlex := by
  intro m n
  unfold Mon.grevlex_k Mon.grevlex
  rw [Mon.degree_k_eq_degree, Mon.degree_k_eq_degree, Mon.revlex_k_eq_revlex]
  exact compareDegrees ..

public theorem Lean.Grind.CommRing.Power.eq_of_revlex :
    type_of% @_root_.Lean.Grind.CommRing.Power.eq_of_revlex := by
  intro p q
  cases p with
  | mk x k =>
    cases q with
    | mk y l =>
      intro h
      change ((Var.revlex x y).then (powerRevlex k l)) = .eq at h
      cases hw : Var.revlex x y with
      | eq =>
        rw [hw] at h
        cases Var.eq_of_revlex hw
        cases eq_of_powerRevlex h
        rfl
      | lt => rw [hw] at h; contradiction
      | gt => rw [hw] at h; contradiction

public theorem Lean.Grind.CommRing.Poly.combine_k_eq_combine :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combine_k_eq_combine := by
  intro p q
  unfold Poly.combine_k Poly.combine
  generalize hugeFuel = fuel
  induction fuel generalizing p q with
  | zero => rfl
  | succ f ih =>
    cases p with
    | num a =>
      cases q with
      | num b => rfl
      | add b n q => exact Poly.addConst_k_eq_addConst ..
    | add a m p =>
      cases q with
      | num b => exact Poly.addConst_k_eq_addConst ..
      | add b n q =>
        dsimp only [Poly.combine.go]
        rw [Mon.grevlex_k_eq_grevlex m n]
        cases h : m.grevlex n with
        | lt => exact congrArg (Poly.add b n) (ih (.add a m p) q)
        | gt => exact congrArg (Poly.add a m) (ih p (.add b n q))
        | eq =>
          rw [Int.beq'_eq_beq (Int.add a b) 0, ih p q]
          cases @BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (a+b) 0 <;> rfl

private theorem polyCongr (f : Poly → Poly → Poly) {a b c d : Poly} (i : a = b) (j : c = d) :
    f a c = f b d := i ▸ j ▸ rfl

public theorem Lean.Grind.CommRing.Expr.toPoly_k_eq_toPoly :
    type_of% @_root_.Lean.Grind.CommRing.Expr.toPoly_k_eq_toPoly := by
  intro e
  induction e with
  | num | intCast | natCast | var => rfl
  | neg a ih => exact (Poly.mulConst_k_eq_mulConst ..).trans (congrArg (Poly.mulConst (-1)) ih)
  | add a b i j => exact (Poly.combine_k_eq_combine ..).trans (polyCongr Poly.combine i j)
  | sub a b i j =>
    exact (Poly.combine_k_eq_combine ..).trans (polyCongr Poly.combine i
      ((Poly.mulConst_k_eq_mulConst ..).trans (congrArg (Poly.mulConst (-1)) j)))
  | mul a b i j => exact polyCongr Poly.mul i j
  | pow a k ih =>
    cases k with
    | zero => cases a <;> rfl
    | succ k =>
      cases a <;> first | rfl | exact congrArg (fun v => Poly.pow v (k+1)) ih


private theorem powerEqOfBeq {p q : Power} (h : p.beq' q) : p = q := by
  cases p with
  | mk x k =>
    cases q with
    | mk y l =>
      have both := Bool.and_eq_true_iff.mp (show (x.beq y && k.beq l) = true from h)
      cases Nat.eq_of_beq_eq_true both.1
      cases Nat.eq_of_beq_eq_true both.2
      rfl

private theorem monEqOfBeq {m n : Mon} (h : m.beq' n) : m = n := by
  induction m generalizing n with
  | unit => cases n <;> first | rfl | contradiction
  | mult p m ih =>
    cases n with
    | unit => contradiction
    | mult q n =>
      have both := Bool.and_eq_true_iff.mp (show (p.beq' q && m.beq' n) = true from h)
      cases powerEqOfBeq both.1
      cases ih both.2
      rfl

private theorem intEqOfBeq {a b : Int} (h : Int.beq' a b) : a = b := by
  rw [Int.beq'_eq_beq] at h
  exact eq_of_beq h

private theorem polyEqOfBeq {p q : Poly} (h : p.beq' q) : p = q := by
  induction p generalizing q with
  | num a =>
    cases q with
    | num b => exact congrArg Poly.num (intEqOfBeq h)
    | add => contradiction
  | add a m p ih =>
    cases q with
    | num => contradiction
    | add b n q =>
      have both := Bool.and_eq_true_iff.mp
        (show (Int.beq' a b && (m.beq' n && p.beq' q)) = true from h)
      have tails := Bool.and_eq_true_iff.mp both.2
      cases intEqOfBeq both.1
      cases monEqOfBeq tails.1
      cases ih tails.2
      rfl

public theorem Lean.Grind.CommRing.Stepwise.mul :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.mul := by
  intro α _ ctx p₁ k p cert h
  cases polyEqOfBeq (p := p₁.mulConst_k k) (q := p) cert
  rw [Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst, h, Semiring.mul_zero]

public theorem Lean.Grind.CommRing.Stepwise.superpose :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.superpose := by
  intro α _ ctx k₁ m₁ p₁ k₂ m₂ p₂ p cert h₁ h₂
  cases polyEqOfBeq (p := (p₁.mulMon_k k₁ m₁).combine_k (p₂.mulMon_k k₂ m₂)) (q := p) cert
  rw [Poly.combine_k_eq_combine, Poly.mulMon_k_eq_mulMon, Poly.mulMon_k_eq_mulMon,
      Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulMon, h₁, h₂,
      Semiring.mul_zero, Semiring.mul_zero, Semiring.add_zero]

public theorem Lean.Grind.CommRing.Stepwise.simp :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.simp := by
  intro α _ ctx k₁ p₁ k₂ m₂ p₂ p cert h₁ h₂
  cases polyEqOfBeq (p := (p₁.mulConst_k k₁).combine_k (p₂.mulMon_k k₂ m₂)) (q := p) cert
  rw [Poly.combine_k_eq_combine, Poly.mulMon_k_eq_mulMon, Poly.mulConst_k_eq_mulConst,
      Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₁, h₂,
      Semiring.mul_zero, Semiring.mul_zero, Semiring.add_zero]

public theorem Lean.Grind.CommRing.Stepwise.d_step1 :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.d_step1 := by
  intro α _ ctx k init p₁ k₂ m₂ p₂ p cert h₁ h₂
  rw [polyEqOfBeq (p := p) (q := p₁.combine_k (p₂.mulMon_k k₂ m₂)) cert,
      Poly.combine_k_eq_combine, Poly.mulMon_k_eq_mulMon, Poly.denote_combine,
      Poly.denote_mulMon, h₂, Semiring.mul_zero, Semiring.add_zero, h₁]

public theorem Lean.Grind.CommRing.Stepwise.d_stepk :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.d_stepk := by
  intro α _ ctx k₁ k init p₁ k₂ m₂ p₂ p cert h₁ h₂
  rw [polyEqOfBeq (p := p) (q := (p₁.mulConst_k k₁).combine_k (p₂.mulMon_k k₂ m₂)) cert,
      Poly.combine_k_eq_combine, Poly.mulMon_k_eq_mulMon, Poly.mulConst_k_eq_mulConst,
      Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₂,
      Semiring.mul_zero, Semiring.add_zero, Ring.intCast_mul, Semiring.mul_assoc, h₁]


open Ring Semiring in
public theorem Lean.Grind.CommRing.Expr.denote_toPoly :
    type_of% @_root_.Lean.Grind.CommRing.Expr.denote_toPoly := by
  intro α _ ctx e
  induction e with
  | num n => exact (denoteInt_eq n).symm
  | intCast n => rfl
  | natCast n => exact (intCast_natCast n)
  | var x => exact Poly.denote_ofVar ..
  | neg a ih =>
    change (a.toPoly.mulConst (-1)).denote ctx = -a.denote ctx
    rw [Poly.denote_mulConst, intCast_neg, intCast_one, neg_mul, one_mul, ih]
  | add a b i j => exact (Poly.denote_combine ..).trans (congr (congrArg HAdd.hAdd i) j)
  | sub a b i j =>
    change (a.toPoly.combine (b.toPoly.mulConst (-1))).denote ctx = a.denote ctx - b.denote ctx
    rw [Poly.denote_combine, Poly.denote_mulConst, intCast_neg, intCast_one, neg_mul,
        one_mul, Ring.sub_eq_add_neg, i, j]
  | mul a b i j => exact (Poly.denote_mul ..).trans (congr (congrArg HMul.hMul i) j)
  | pow a k ih =>
    cases k with
    | zero => exact intCast_one.trans (pow_zero _).symm
    | succ k =>
      cases a with
      | num n =>
        change (Poly.num (n^(k+1))).denote ctx = (denoteInt n : α) ^ (k+1)
        rw [Poly.denote, intCast_pow, denoteInt_eq]
      | intCast n => exact intCast_pow n (k+1)
      | natCast n => exact (intCast_pow (n : Int) (k+1)).trans (congrArg (fun x : α => x ^ (k+1)) (intCast_natCast n))
      | var x =>
        change (Poly.ofMon (.mult ⟨x, k+1⟩ .unit)).denote ctx = x.denote ctx ^ (k+1)
        rw [Poly.denote_ofMon, Mon.denote, Power.denote_eq, Mon.denote, mul_one]
      | neg | add | sub | mul | pow =>
        exact (Poly.denote_pow ..).trans (congrArg (fun x : α => x ^ (k+1)) ih)

open Ring Semiring in
public theorem Lean.Grind.CommRing.Expr.denote_toPoly_nc :
    type_of% @_root_.Lean.Grind.CommRing.Expr.denote_toPoly_nc := by
  intro α _ ctx e
  induction e with
  | num n => exact (denoteInt_eq n).symm
  | intCast n => rfl
  | natCast n => exact (intCast_natCast n)
  | var x => exact Poly.denote_ofVar ..
  | neg a ih =>
    change (a.toPoly_nc.mulConst (-1)).denote ctx = -a.denote ctx
    rw [Poly.denote_mulConst, intCast_neg, intCast_one, neg_mul, one_mul, ih]
  | add a b i j => exact (Poly.denote_combine ..).trans (congr (congrArg HAdd.hAdd i) j)
  | sub a b i j =>
    change (a.toPoly_nc.combine (b.toPoly_nc.mulConst (-1))).denote ctx = a.denote ctx - b.denote ctx
    rw [Poly.denote_combine, Poly.denote_mulConst, intCast_neg, intCast_one, neg_mul,
        one_mul, Ring.sub_eq_add_neg, i, j]
  | mul a b i j => exact (Poly.denote_mul_nc ..).trans (congr (congrArg HMul.hMul i) j)
  | pow a k ih =>
    cases k with
    | zero => exact intCast_one.trans (pow_zero _).symm
    | succ k =>
      cases a with
      | num n =>
        change (Poly.num (n^(k+1))).denote ctx = (denoteInt n : α) ^ (k+1)
        rw [Poly.denote, intCast_pow, denoteInt_eq]
      | intCast n => exact intCast_pow n (k+1)
      | natCast n => exact (intCast_pow (n : Int) (k+1)).trans (congrArg (fun x : α => x ^ (k+1)) (intCast_natCast n))
      | var x =>
        change (Poly.ofMon (.mult ⟨x, k+1⟩ .unit)).denote ctx = x.denote ctx ^ (k+1)
        rw [Poly.denote_ofMon, Mon.denote, Power.denote_eq, Mon.denote, mul_one]
      | neg | add | sub | mul | pow =>
        exact (Poly.denote_pow_nc ..).trans (congrArg (fun x : α => x ^ (k+1)) ih)

open Ring Semiring in
public theorem Lean.Grind.CommRing.Expr.denote_toPolyC :
    type_of% @_root_.Lean.Grind.CommRing.Expr.denote_toPolyC := by
  intro α c _ _ ctx e
  induction e with
  | num n => exact ((IsCharP.intCast_emod (p := c) n).trans (denoteInt_eq n).symm)
  | intCast n => exact IsCharP.intCast_emod (p := c) n
  | natCast n => exact ((IsCharP.intCast_emod (p := c) (n : Int)).trans (intCast_natCast n))
  | var x => exact Poly.denote_ofVar ..
  | neg a ih =>
    change ((a.toPolyC c).mulConstC (-1) c).denote ctx = -a.denote ctx
    rw [Poly.denote_mulConstC, intCast_neg, intCast_one, neg_mul, one_mul, ih]
  | add a b i j => exact (Poly.denote_combineC ..).trans (congr (congrArg HAdd.hAdd i) j)
  | sub a b i j =>
    change ((a.toPolyC c).combineC ((b.toPolyC c).mulConstC (-1) c) c).denote ctx = a.denote ctx - b.denote ctx
    rw [Poly.denote_combineC, Poly.denote_mulConstC, intCast_neg, intCast_one, neg_mul,
        one_mul, Ring.sub_eq_add_neg, i, j]
  | mul a b i j => exact (Poly.denote_mulC ..).trans (congr (congrArg HMul.hMul i) j)
  | pow a k ih =>
    cases k with
    | zero => exact intCast_one.trans (pow_zero _).symm
    | succ k =>
      cases a with
      | num n =>
        change (Poly.num ((n^(k+1)) % c)).denote ctx = (denoteInt n : α) ^ (k+1)
        rw [Poly.denote, IsCharP.intCast_emod, intCast_pow, denoteInt_eq]
      | var x =>
        change (Poly.ofMon (.mult ⟨x, k+1⟩ .unit)).denote ctx = x.denote ctx ^ (k+1)
        rw [Poly.denote_ofMon, Mon.denote, Power.denote_eq, Mon.denote, mul_one]
      | intCast | natCast | neg | add | sub | mul | pow =>
        exact (Poly.denote_powC ..).trans (congrArg (fun x : α => x ^ (k+1)) ih)

open Ring Semiring in
public theorem Lean.Grind.CommRing.Expr.denote_toPolyC_nc :
    type_of% @_root_.Lean.Grind.CommRing.Expr.denote_toPolyC_nc := by
  intro α c _ _ ctx e
  induction e with
  | num n => exact ((IsCharP.intCast_emod (p := c) n).trans (denoteInt_eq n).symm)
  | intCast n => exact IsCharP.intCast_emod (p := c) n
  | natCast n => exact ((IsCharP.intCast_emod (p := c) (n : Int)).trans (intCast_natCast n))
  | var x => exact Poly.denote_ofVar ..
  | neg a ih =>
    change ((a.toPolyC_nc c).mulConstC (-1) c).denote ctx = -a.denote ctx
    rw [Poly.denote_mulConstC, intCast_neg, intCast_one, neg_mul, one_mul, ih]
  | add a b i j => exact (Poly.denote_combineC ..).trans (congr (congrArg HAdd.hAdd i) j)
  | sub a b i j =>
    change ((a.toPolyC_nc c).combineC ((b.toPolyC_nc c).mulConstC (-1) c) c).denote ctx = a.denote ctx - b.denote ctx
    rw [Poly.denote_combineC, Poly.denote_mulConstC, intCast_neg, intCast_one, neg_mul,
        one_mul, Ring.sub_eq_add_neg, i, j]
  | mul a b i j => exact (Poly.denote_mulC_nc ..).trans (congr (congrArg HMul.hMul i) j)
  | pow a k ih =>
    cases k with
    | zero => exact intCast_one.trans (pow_zero _).symm
    | succ k =>
      cases a with
      | num n =>
        change (Poly.num ((n^(k+1)) % c)).denote ctx = (denoteInt n : α) ^ (k+1)
        rw [Poly.denote, IsCharP.intCast_emod, intCast_pow, denoteInt_eq]
      | var x =>
        change (Poly.ofMon (.mult ⟨x, k+1⟩ .unit)).denote ctx = x.denote ctx ^ (k+1)
        rw [Poly.denote_ofMon, Mon.denote, Power.denote_eq, Mon.denote, mul_one]
      | intCast | natCast | neg | add | sub | mul | pow =>
        exact (Poly.denote_powC_nc ..).trans (congrArg (fun x : α => x ^ (k+1)) ih)


public theorem Lean.Grind.NoNatZeroDivisors.eq_zero_of_mul_eq_zero :
    type_of% @_root_.Lean.Grind.NoNatZeroDivisors.eq_zero_of_mul_eq_zero := by
  intro α _ _ k a nonzero zero
  exact no_nat_zero_divisors k a 0 nonzero (zero.trans (NatModule.nsmul_zero k).symm)

public theorem Lean.Grind.no_int_zero_divisors :
    type_of% @_root_.Lean.Grind.no_int_zero_divisors := by
  intro α _ _ k a nonzero zero
  cases k with
  | ofNat n =>
    change (↑n : Int) • a = 0 at zero
    rw [IntModule.zsmul_natCast_eq_nsmul] at zero
    exact NoNatZeroDivisors.eq_zero_of_mul_eq_zero (fun eq => nonzero (congrArg Int.ofNat eq)) zero
  | negSucc n =>
    change -(↑(n+1) : Int) • a = 0 at zero
    rw [IntModule.neg_zsmul] at zero
    have h := congrArg Neg.neg zero
    rw [AddCommGroup.neg_neg, AddCommGroup.neg_zero, IntModule.zsmul_natCast_eq_nsmul] at h
    exact NoNatZeroDivisors.eq_zero_of_mul_eq_zero (Nat.succ_ne_zero n) h

public theorem Lean.Grind.OrderedAdd.zsmul_nonpos :
    type_of% @_root_.Lean.Grind.OrderedAdd.zsmul_nonpos := by
  intro α _ _ _ _ k a nonneg h
  rw [Int.eq_natAbs_of_nonneg nonneg, IntModule.zsmul_natCast_eq_nsmul]
  have zero := OrderedAdd.nsmul_le_nsmul (k := k.natAbs) h
  rw [NatModule.nsmul_zero] at zero
  exact zero

private theorem neOfNotIntBeq {k : Int} (h : !(Int.beq' k 0)) : k ≠ 0 := by
  intro eq
  cases eq
  contradiction

private theorem subDenoteOfCert {α : Type u} [CommRing α] (ctx : Context α) {a b : Expr}
    {p : Poly} (cert : (a.sub b).toPoly_k.beq' p) :
    p.denote ctx = a.denote ctx - b.denote ctx := by
  rw [← polyEqOfBeq cert, Expr.toPoly_k_eq_toPoly]
  exact _root_.Lean.Grind.CommRing.Expr.denote_toPoly ..

public theorem Lean.Grind.CommRing.Stepwise.div :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.div := by
  intro α _ ctx _ p₁ k p cert h
  have both := Bool.and_eq_true_iff.mp (show (!(Int.beq' k 0) && (p.mulConst_k k).beq' p₁) = true from cert)
  rw [← polyEqOfBeq both.2, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst, ← Ring.zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors (neOfNotIntBeq both.1) h

public theorem Lean.Grind.CommRing.Stepwise.core :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.core := by
  intro α _ ctx a b p cert h
  rw [subDenoteOfCert ctx cert]
  exact AddCommGroup.sub_eq_zero_iff.mpr h

public theorem Lean.Grind.CommRing.Stepwise.imp_1eq :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.imp_1eq := by
  intro α _ ctx a b p q cert h
  have both := Bool.and_eq_true_iff.mp (show (((a.sub b).toPoly_k).beq' p && q.beq' (.num 0)) = true from cert)
  rw [subDenoteOfCert ctx both.1, polyEqOfBeq both.2, Poly.denote, Ring.intCast_zero, Ring.intCast_one, Semiring.one_mul] at h
  exact AddCommGroup.sub_eq_zero_iff.mp h

public theorem Lean.Grind.CommRing.Stepwise.imp_keq :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.imp_keq := by
  intro α _ ctx _ k a b p q cert h
  have data := Bool.and_eq_true_iff.mp (show (!(Int.beq' k 0) && (((a.sub b).toPoly_k).beq' p && q.beq' (.num 0))) = true from cert)
  have both := Bool.and_eq_true_iff.mp data.2
  rw [subDenoteOfCert ctx both.1, polyEqOfBeq both.2, Poly.denote, Ring.intCast_zero, ← Ring.zsmul_eq_intCast_mul] at h
  exact AddCommGroup.sub_eq_zero_iff.mp (no_int_zero_divisors (neOfNotIntBeq data.1) h)

public theorem Lean.Grind.CommRing.Stepwise.divC :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.divC := by
  intro α c _ _ ctx _ p₁ k p cert h
  have both := Bool.and_eq_true_iff.mp (show (!(Int.beq' k 0) && (p.mulConstC k c).beq' p₁) = true from cert)
  rw [← polyEqOfBeq both.2, Poly.denote_mulConstC, ← Ring.zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors (neOfNotIntBeq both.1) h

public theorem Lean.Grind.CommRing.Stepwise.coreC :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.coreC := by
  intro α c _ _ ctx a b p cert h
  rw [← polyEqOfBeq (p := (a.sub b).toPolyC c) (q := p) cert, Expr.denote_toPolyC]
  change a.denote ctx - b.denote ctx = 0
  exact AddCommGroup.sub_eq_zero_iff.mpr h

public theorem Lean.Grind.CommRing.Stepwise.imp_1eqC :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.imp_1eqC := by
  intro α c _ _ ctx a b p q cert h
  have both := Bool.and_eq_true_iff.mp (show (((a.sub b).toPolyC c).beq' p && q.beq' (.num 0)) = true from cert)
  rw [← polyEqOfBeq both.1, Expr.denote_toPolyC, polyEqOfBeq both.2, Poly.denote, Ring.intCast_zero, Ring.intCast_one, Semiring.one_mul] at h
  exact AddCommGroup.sub_eq_zero_iff.mp h

public theorem Lean.Grind.CommRing.Stepwise.imp_keqC :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.imp_keqC := by
  intro α c _ _ ctx _ k a b p q cert h
  have data := Bool.and_eq_true_iff.mp (show (!(Int.beq' k 0) && (((a.sub b).toPolyC c).beq' p && q.beq' (.num 0))) = true from cert)
  have both := Bool.and_eq_true_iff.mp data.2
  rw [← polyEqOfBeq both.1, Expr.denote_toPolyC, polyEqOfBeq both.2, Poly.denote, Ring.intCast_zero, ← Ring.zsmul_eq_intCast_mul] at h
  exact AddCommGroup.sub_eq_zero_iff.mp (no_int_zero_divisors (neOfNotIntBeq data.1) h)

public theorem Lean.Grind.CommRing.diseq_norm :
    type_of% @_root_.Lean.Grind.CommRing.diseq_norm := by
  intro α _ ctx a b p cert neq zero
  rw [subDenoteOfCert ctx cert] at zero
  exact neq (AddCommGroup.sub_eq_zero_iff.mp zero)

public theorem Lean.Grind.CommRing.norm_int :
    type_of% @_root_.Lean.Grind.CommRing.norm_int := by
  intro ctx e p cert
  rw [← polyEqOfBeq (p := e.toPoly_k) (q := p) cert, Expr.toPoly_k_eq_toPoly,
      Poly.denote'_eq_denote, Expr.denote_toPoly]

public theorem Lean.Grind.CommRing.Stepwise.diseq_mul :
    type_of% @_root_.Lean.Grind.CommRing.Stepwise.diseq_mul := by
  intro α _ _ ctx p₁ k p cert ne zero
  have both := Bool.and_eq_true_iff.mp (show ((!(@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k 0)) && (p₁.mulConst_k k).beq' p) = true from cert)
  rw [← polyEqOfBeq both.2, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst,
      ← Ring.zsmul_eq_intCast_mul] at zero
  exact ne (no_int_zero_divisors (bne_iff_ne.mp both.1) zero)

public theorem Lean.Grind.CommRing.le_norm :
    type_of% @_root_.Lean.Grind.CommRing.le_norm := by
  intro α _ _ _ _ _ ctx a b p cert h
  rw [subDenoteOfCert ctx cert]
  have shift := OrderedAdd.add_le_left h (-(b.denote ctx))
  rw [← AddCommGroup.sub_eq_add_neg, ← AddCommGroup.sub_eq_add_neg, AddCommGroup.sub_self] at shift
  exact shift

public theorem Lean.Grind.CommRing.le_mul :
    type_of% @_root_.Lean.Grind.CommRing.le_mul := by
  intro α _ _ _ _ _ ctx p₁ k p cert h
  have both := Bool.and_eq_true_iff.mp (show (decide (k > 0) && (p₁.mulConst_k k).beq' p) = true from cert)
  rw [← polyEqOfBeq both.2, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst,
      ← Ring.zsmul_eq_intCast_mul]
  exact OrderedAdd.zsmul_nonpos (Int.le_of_lt (of_decide_eq_true both.1)) h

public theorem Lean.Grind.CommRing.lt_norm :
    type_of% @_root_.Lean.Grind.CommRing.lt_norm := by
  intro α _ _ _ _ _ _ ctx a b p cert h
  rw [subDenoteOfCert ctx cert]
  have shift := OrderedAdd.add_lt_left h (-(b.denote ctx))
  rw [← AddCommGroup.sub_eq_add_neg, ← AddCommGroup.sub_eq_add_neg, AddCommGroup.sub_self] at shift
  exact shift

public theorem Lean.Grind.CommRing.lt_mul :
    type_of% @_root_.Lean.Grind.CommRing.lt_mul := by
  intro α _ _ _ _ _ _ ctx p₁ k p cert h
  have both := Bool.and_eq_true_iff.mp (show (decide (k > 0) && (p₁.mulConst_k k).beq' p) = true from cert)
  rw [← polyEqOfBeq both.2, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst,
      ← Ring.zsmul_eq_intCast_mul]
  have pos : 0 < k := of_decide_eq_true both.1
  rw [Int.eq_natAbs_of_nonneg (Int.le_of_lt pos), IntModule.zsmul_natCast_eq_nsmul]
  have posNat : 0 < k.natAbs := Int.natAbs_pos.mpr (Int.ne_of_gt pos)
  have scaled := (OrderedAdd.nsmul_lt_nsmul_iff k.natAbs h).mpr posNat
  rw [NatModule.nsmul_zero] at scaled
  exact scaled


public theorem Lean.Grind.LinearOrder.lt_of_not_le :
    type_of% @_root_.Lean.Grind.LinearOrder.lt_of_not_le := by
  intro α _ _ _ _ a b h
  cases Std.le_total (a := a) (b := b) with
  | inl ab => exact False.elim (h ab)
  | inr ba => exact Std.lt_iff_le_and_not_ge.mpr ⟨ba, h⟩

public theorem Lean.Grind.CommRing.not_le_norm :
    type_of% @_root_.Lean.Grind.CommRing.not_le_norm := by
  intro α _ _ _ _ _ _ ctx a b p cert h
  exact _root_.Lean.Grind.CommRing.lt_norm ctx b a p cert (LinearOrder.lt_of_not_le h)

public theorem Lean.Grind.CommRing.one_eq_zero_unsat :
    type_of% @_root_.Lean.Grind.CommRing.one_eq_zero_unsat := by
  intro α _ ctx p cert zero
  have possibilities := Bool.or_eq_true_iff.mp
    (show (p.beq' (.num 1) || p.beq' (.num (-1))) = true from cert)
  cases possibilities with
  | inl one =>
    rw [polyEqOfBeq one, Poly.denote, Ring.intCast_one] at zero
    exact Field.zero_ne_one zero.symm
  | inr neg =>
    rw [polyEqOfBeq neg, Poly.denote, Ring.intCast_neg, Ring.intCast_one] at zero
    have h := congrArg Neg.neg zero
    rw [AddCommGroup.neg_neg, AddCommGroup.neg_zero] at h
    exact Field.zero_ne_one h.symm


public theorem Lean.Grind.OrderedAdd.neg_le_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.neg_le_iff := by
  intro α _ _ _ _ a b
  have left := OrderedAdd.add_le_left_iff (a := -a) (b := b) a
  have right := OrderedAdd.add_le_left_iff (a := -b) (b := a) b
  rw [AddCommGroup.neg_add_cancel, AddCommMonoid.add_comm b a] at left
  rw [AddCommGroup.neg_add_cancel] at right
  exact left.trans right.symm

public theorem Lean.Grind.OrderedAdd.le_neg_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.le_neg_iff := by
  intro α _ _ _ _ a b
  have h := OrderedAdd.neg_le_iff (a := -a) (b := -b)
  rw [AddCommGroup.neg_neg, AddCommGroup.neg_neg] at h
  exact h

public theorem Lean.Grind.OrderedAdd.neg_nonneg_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.neg_nonneg_iff := by
  intro α _ _ _ _ a
  have h := OrderedAdd.le_neg_iff (a := 0) (b := a)
  rw [AddCommGroup.neg_zero] at h
  exact h

public theorem Lean.Grind.OrderedAdd.neg_lt_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.neg_lt_iff := by
  intro α _ _ _ _ _ _ a b
  have left := OrderedAdd.add_lt_left_iff (a := -a) (b := b) a
  have right := OrderedAdd.add_lt_left_iff (a := -b) (b := a) b
  rw [AddCommGroup.neg_add_cancel, AddCommMonoid.add_comm b a] at left
  rw [AddCommGroup.neg_add_cancel] at right
  exact left.trans right.symm

public theorem Lean.Grind.OrderedAdd.lt_neg_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.lt_neg_iff := by
  intro α _ _ _ _ _ _ a b
  have h := OrderedAdd.neg_lt_iff (a := -a) (b := -b)
  rw [AddCommGroup.neg_neg, AddCommGroup.neg_neg] at h
  exact h

public theorem Lean.Grind.OrderedAdd.neg_pos_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.neg_pos_iff := by
  intro α _ _ _ _ _ _ a
  have h := OrderedAdd.lt_neg_iff (a := 0) (b := a)
  rw [AddCommGroup.neg_zero] at h
  exact h

public theorem Lean.Grind.OrderedAdd.zsmul_pos_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.zsmul_pos_iff := by
  intro α _ _ _ _ _ _ k a h
  cases k with
  | ofNat n =>
    change 0 < (↑n : Int) • a ↔ 0 < (↑n : Int)
    rw [IntModule.zsmul_natCast_eq_nsmul]
    have pos := OrderedAdd.nsmul_lt_nsmul_iff n h
    rw [NatModule.nsmul_zero] at pos
    exact pos.trans Int.natCast_pos.symm
  | negSucc n =>
    constructor
    · intro pos
      change 0 < -(↑(n+1) : Int) • a at pos
      rw [IntModule.neg_zsmul] at pos
      have neg := OrderedAdd.neg_pos_iff.mp pos
      have nonneg := OrderedAdd.zsmul_nonneg (Int.natCast_nonneg (n+1)) (Preorder.le_of_lt h)
      exact False.elim ((Std.lt_iff_le_and_not_ge.mp neg).2 nonneg)
    · intro bad
      exact False.elim ((Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero n))) bad)

public theorem Lean.Grind.OrderedAdd.zsmul_neg_iff :
    type_of% @_root_.Lean.Grind.OrderedAdd.zsmul_neg_iff := by
  intro α _ _ _ _ _ _ k a h
  have pos := OrderedAdd.zsmul_pos_iff k (OrderedAdd.neg_pos_iff.mpr h)
  rw [IntModule.zsmul_neg] at pos
  exact OrderedAdd.neg_pos_iff.symm.trans pos

end OmegaChecks.InitPort.Alternatives
