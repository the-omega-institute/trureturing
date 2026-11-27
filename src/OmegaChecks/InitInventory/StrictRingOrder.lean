module
public import Lean
meta import Lean

/-! Strict comparisons in the integer product ring detect propositional extensionality.
The ring operations normalize formal differences of naturals so the integer arithmetic and
the comparison proofs can be replayed in an empty kernel. -/

namespace OmegaChecks.InitBoundaries.StrictRingOrder

namespace Signed
set_option linter.unusedSimpArgs false
local macro "additive" : tactic => `(tactic| ((conv => lhs; simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_zero,Nat.zero_add]); (conv => rhs; simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_zero,Nat.zero_add])))
private theorem plusMul (a b c : Nat) : (a+b)*c = a*c+b*c := (Nat.mul_comm ..).trans ((Nat.mul_add ..).trans ((congrArg (· + c*b) (Nat.mul_comm c a)).trans (congrArg (_+·) (Nat.mul_comm c b))))
private theorem mulAssoc (a b c : Nat) : (a*b)*c = a*(b*c) := by
  induction c with
  | zero => rfl
  | succ c ih => exact (congrArg (· + a*b) ih).trans (Nat.mul_add a (b*c) b).symm
private theorem mulLeftComm (a b c : Nat) : a*(b*c)=b*(a*c) :=
  (mulAssoc ..).symm.trans ((congrArg (·*c) (Nat.mul_comm ..)).trans (mulAssoc ..))
local macro "polynomial" : tactic => `(tactic| (
  (conv => lhs; simp only [Nat.mul_add,plusMul,Nat.zero_mul,Nat.mul_zero,Nat.one_mul,Nat.mul_one]; simp only [mulAssoc,Nat.mul_comm,mulLeftComm]; simp only [Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  (conv => rhs; simp only [Nat.mul_add,plusMul,Nat.zero_mul,Nat.mul_zero,Nat.one_mul,Nat.mul_one]; simp only [mulAssoc,Nat.mul_comm,mulLeftComm]; simp only [Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])))

/-- A pair represents the difference of its natural coordinates. -/
abbrev Pair := Nat × Nat
def repr : Int → Pair
 | .ofNat n => (n,0)
 | .negSucc n => (0,n+1)
def norm : Nat → Nat → Int
 | n,0 => .ofNat n
 | 0,m+1 => .negSucc m
 | n+1,m+1 => norm n m

def Rel (a b : Pair) := a.1 + b.2 = b.1 + a.2

private theorem natCancel {a b : Nat} (c : Nat) (h : a + c = b + c) : a = b := by
  induction c with
  | zero => exact h
  | succ _ ih => exact ih (Nat.succ.inj h)

private theorem cancelBase (a b c d e f : Nat)
    (h : a+d=c+b) (k : c+f=e+d) : a+f=e+b := by
  apply natCancel d
  calc
    _ = (a+d)+f := by additive
    _ = (c+f)+b := by rw [h]; additive
    _ = _ := by rw [k]; additive

theorem Refl (a : Pair) : Rel a a := rfl
theorem Symm {a b : Pair} : Rel a b → Rel b a := Eq.symm
theorem Trans {a b c : Pair} (h : Rel a b) (k : Rel b c) : Rel a c :=
  cancelBase _ _ _ _ _ _ h k

theorem normRep (n m : Nat) : Rel (repr (norm n m)) (n,m) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => rfl
  | succ n ih =>
    cases m with
    | zero => rfl
    | succ m =>
      change (repr (norm n m)).1 + m.succ = n.succ + (repr (norm n m)).2
      rw [Nat.succ_add]
      exact congrArg Nat.succ (ih m)

theorem reprInjective {a b : Int} (h : Rel (repr a) (repr b)) : a=b := by
  cases a <;> cases b
  case ofNat.ofNat a b => exact congrArg Int.ofNat h
  case negSucc.negSucc a b => exact congrArg Int.negSucc (Nat.succ.inj ((Nat.zero_add _).symm.trans (h.symm.trans (Nat.zero_add _))))
  case ofNat.negSucc a b =>
    change a+(b+1) = 0 at h
    cases h
  case negSucc.ofNat a b =>
    change 0 = b+(a+1) at h
    cases h

def plus (a b : Pair) : Pair := (a.1+b.1,a.2+b.2)
def minus (a : Pair) : Pair := (a.2,a.1)
def times (a b : Pair) : Pair := (a.1*b.1+a.2*b.2,a.1*b.2+a.2*b.1)
def make (a : Pair) := norm a.1 a.2
def add (a b : Int) := make (plus (repr a) (repr b))
def mul (a b : Int) := make (times (repr a) (repr b))
def neg (a : Int) := make (minus (repr a))
theorem plusCong {a b a' b' : Pair} (h : Rel a a') (k : Rel b b') : Rel (plus a b) (plus a' b') := by
  change (a.1+b.1)+(a'.2+b'.2)=(a'.1+b'.1)+(a.2+b.2)
  calc
    _ = (a.1+a'.2)+(b.1+b'.2) := by additive
    _ = (a'.1+a.2)+(b'.1+b.2) := (congrArg (· + (b.1+b'.2)) h).trans (congrArg ((a'.1+a.2) + ·) k)
    _ = _ := by additive

theorem timesLeft (a b c : Pair) (h : Rel a b) : Rel (times a c) (times b c) := by
  change (a.1*c.1+a.2*c.2)+(b.1*c.2+b.2*c.1) = (b.1*c.1+b.2*c.2)+(a.1*c.2+a.2*c.1)
  calc
    _ = (a.1+b.2)*c.1 + (b.1+a.2)*c.2 := by polynomial
    _ = (b.1+a.2)*c.1 + (a.1+b.2)*c.2 :=
      (congrArg (fun t => t*c.1+(b.1+a.2)*c.2) h).trans (congrArg (fun t => (b.1+a.2)*c.1+t*c.2) h.symm)
    _ = _ := by polynomial
theorem timesComm (a b : Pair) : times a b = times b a := by
  apply Prod.ext
  · change a.1*b.1+a.2*b.2=b.1*a.1+b.2*a.2
    polynomial
  · change a.1*b.2+a.2*b.1=b.1*a.2+b.2*a.1
    polynomial
theorem timesCong {a b a' b' : Pair} (h : Rel a a') (k : Rel b b') : Rel (times a b) (times a' b') :=
  Trans (timesLeft a a' b h) (timesComm b a' ▸ timesComm b' a' ▸ timesLeft b b' a' k)
theorem norm_add (a b : Int) : Rel (repr (add a b)) (plus (repr a) (repr b)) := normRep _ _
theorem norm_mul (a b : Int) : Rel (repr (mul a b)) (times (repr a) (repr b)) := normRep _ _
theorem norm_neg (a : Int) : Rel (repr (neg a)) (minus (repr a)) := normRep _ _
theorem minusCong {a b : Pair} (h : Rel a b) : Rel (minus a) (minus b) :=
  (Nat.add_comm ..).trans (h.symm.trans (Nat.add_comm ..))
open Lean Meta Elab Tactic in
/-- Reduce the integer expression to a natural difference, carrying the equivalence proof. -/
private meta partial def represent (e : Expr) : MetaM Expr := do
  let xs := e.getAppArgs
  let transport (step cong : Name) := do
    let next ← xs.mapM represent
    mkAppM ``Trans #[← mkAppM step xs, ← mkAppM cong next]
  match e.getAppFn.constName? with
  | some ``add => transport ``norm_add ``plusCong
  | some ``mul => transport ``norm_mul ``timesCong
  | some ``neg => transport ``norm_neg ``minusCong
  | _ => mkAppM ``Refl #[← mkAppM ``repr #[e]]
open Lean Meta Elab Tactic in
local elab "ringEquality" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_,l,r) := (← goal.getType).eq? | throwError "expected integer equality"
  let left ← represent l
  let right ← represent r
  let mid ← mkFreshExprMVar (← mkAppM ``Rel #[(← inferType left).appArg!, (← inferType right).appArg!])
  let h ← mkAppM ``Trans #[left, ← mkAppM ``Trans #[mid,← mkAppM ``Symm #[right]]]
  goal.assign (← mkAppM ``reprInjective #[h])
  replaceMainGoal [mid.mvarId!]
  evalTactic (← `(tactic| (dsimp only [Rel, repr, plus, times, minus]; polynomial)))
theorem addZero (a : Int) : add a 0 = a := by ringEquality
theorem addComm (a b : Int) : add a b = add b a := by ringEquality
theorem addAssoc (a b c : Int) : add (add a b) c = add a (add b c) := by ringEquality
set_option maxHeartbeats 3000000 in
theorem mulAssocZ (a b c : Int) : mul (mul a b) c = mul a (mul b c) := by ringEquality
theorem mulCommZ (a b : Int) : mul a b = mul b a := by ringEquality
theorem mulOne (a : Int) : mul a 1 = a := by ringEquality
set_option maxHeartbeats 3000000 in
theorem mulAdd (a b c : Int) : mul a (add b c) = add (mul a b) (mul a c) := by ringEquality
theorem zeroMul (a : Int) : mul 0 a = 0 := by ringEquality
theorem negAdd (a : Int) : add (neg a) a = 0 := by ringEquality
theorem negMul (a b : Int) : mul (neg a) b = neg (mul a b) := by ringEquality

theorem zeroAdd (a) : add 0 a = a := (addComm ..).trans (addZero _)
theorem oneMul (a) : mul 1 a = a := (mulCommZ ..).trans (mulOne _)
theorem mulZero (a) : mul a 0 = 0 := (mulCommZ ..).trans (zeroMul _)
theorem addSwap (a b c) : add (add a b) c = add (add a c) b :=
  (addAssoc ..).trans ((congrArg (add a) (addComm ..)).trans (addAssoc ..).symm)
theorem cancel {a b c} (h : add a c = add b c) : a=b := by
  have undo (x) : add (add x c) (neg c) = x := (addAssoc ..).trans ((congrArg (add x) ((addComm ..).trans (negAdd c))).trans (addZero x))
  exact (undo a).symm.trans ((congrArg (add · (neg c)) h).trans (undo b))
private theorem normZero (n : Nat) : norm n 0 = Int.ofNat n := by cases n <;> rfl
theorem natAdd (n m : Nat) : add (.ofNat n) (.ofNat m) = .ofNat (n+m) := normZero _
theorem natMul (n m : Nat) : mul (.ofNat n) (.ofNat m) = .ofNat (n*m) := by
  change norm (n*m + 0*0) (n*0 + 0*m) = _
  rw [Nat.zero_mul m]
  exact normZero _
theorem negNat (z : Int) : -z = neg z := by cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

def less (a b : Int) := ∃ k : Nat, add a (.ofNat (k+1)) = b
theorem irrefl (a) : ¬ less a a := by
  intro ⟨n,h⟩
  have eq : Int.ofNat (n+1) = 0 := cancel ((addComm ..).trans (h.trans (zeroAdd a).symm))
  cases eq
theorem transLess {a b c} : less a b → less b c → less a c := by
  rintro ⟨n,rfl⟩ ⟨m,rfl⟩
  exact ⟨(n+1)+m,(congrArg (add a) (natAdd (n+1) (m+1)).symm).trans (addAssoc ..).symm⟩
theorem asymm {a b} (h : less a b) : ¬less b a := fun k => irrefl a (transLess h k)
theorem addLess {a b} (h : less a b) (c) : less (add a c) (add b c) := by
  obtain ⟨n,rfl⟩ := h
  exact ⟨n,addSwap ..⟩
theorem lessOfAdd {a b c} (h : less (add a c) (add b c)) : less a b := by
  obtain ⟨n,h⟩ := h
  exact ⟨n,cancel ((addSwap ..).trans h)⟩
theorem mulLess {a b c} (h : less a b) (hc : less 0 c) : less (mul c a) (mul c b) := by
  obtain ⟨n,rfl⟩ := h
  obtain ⟨k,hc⟩ := hc
  rw [zeroAdd] at hc
  subst c
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos n)))
  refine ⟨j,?_⟩
  rw [mulAdd,natMul,hj]

end Signed

open Lean.Grind Std
/-- The two coordinates of the ordered product ring. -/
abbrev R := Int × Int
private def coord (f : Int → Int → Int) (a b : R) : R := (f a.1 b.1, f a.2 b.2)
private theorem pairEq {a b : R} (h : a.1 = b.1) (k : a.2 = b.2) : a = b := Prod.ext h k
private theorem signedDistrib (a b c : Int) : Signed.mul (Signed.add a b) c = Signed.add (Signed.mul a c) (Signed.mul b c) :=
  (Signed.mulCommZ ..).trans ((Signed.mulAdd ..).trans ((congrArg (Signed.add · _) (Signed.mulCommZ ..)).trans (congrArg (Signed.add _) (Signed.mulCommZ ..))))
private theorem signedNegSmul (n a : Int) : Signed.mul (-n) a = Signed.neg (Signed.mul n a) :=
  (congrArg (Signed.mul · a) (Signed.negNat n)).trans (Signed.negMul ..)
private def pw (a : Int) : Nat → Int | 0 => 1 | n+1 => Signed.mul (pw a n) a
local instance productRing : CommRing R where
  add := coord Signed.add
  mul := coord Signed.mul
  neg a := (Signed.neg a.1,Signed.neg a.2)
  sub := coord (fun a b => Signed.add a (Signed.neg b))
  natCast := ⟨fun n => (n,n)⟩
  ofNat n := ⟨(n,n)⟩
  intCast := ⟨fun n => (n,n)⟩
  npow := ⟨fun a n => (pw a.1 n,pw a.2 n)⟩
  nsmul := ⟨fun n a => (Signed.mul n a.1,Signed.mul n a.2)⟩
  zsmul := ⟨fun n a => (Signed.mul n a.1,Signed.mul n a.2)⟩
  add_zero a := pairEq (Signed.addZero _) (Signed.addZero _)
  add_comm a b := pairEq (Signed.addComm ..) (Signed.addComm ..)
  add_assoc a b c := pairEq (Signed.addAssoc ..) (Signed.addAssoc ..)
  mul_assoc a b c := pairEq (Signed.mulAssocZ ..) (Signed.mulAssocZ ..)
  mul_comm a b := pairEq (Signed.mulCommZ ..) (Signed.mulCommZ ..)
  mul_one a := pairEq (Signed.mulOne _) (Signed.mulOne _)
  one_mul a := pairEq (Signed.oneMul _) (Signed.oneMul _)
  mul_zero a := pairEq (Signed.mulZero _) (Signed.mulZero _)
  right_distrib a b c := pairEq (signedDistrib ..) (signedDistrib ..)
  left_distrib a b c := pairEq (Signed.mulAdd ..) (Signed.mulAdd ..)
  zero_mul a := pairEq (Signed.zeroMul _) (Signed.zeroMul _)
  pow_zero a := rfl
  pow_succ a n := rfl
  neg_add_cancel a := pairEq (Signed.negAdd _) (Signed.negAdd _)
  sub_eq_add_neg a b := rfl
  neg_zsmul i a := pairEq (signedNegSmul ..) (signedNegSmul ..)
  ofNat_succ n := pairEq (Signed.natAdd n 1).symm (Signed.natAdd n 1).symm
  intCast_neg i := pairEq (Signed.negNat i) (Signed.negNat i)

/-- The second coordinate always increases. Equality in the first coordinate requires the proposition. -/
def Pos (p : Prop) (a b : R) := Signed.less a.2 b.2 ∧ (Signed.less a.1 b.1 ∨ a.1 = b.1 ∧ p)
@[instance_reducible] def weak (p : Prop) : LE R := ⟨fun a b => a = b ∨ Pos p a b⟩
/-- Decorate two comparisons related by translation with the given propositions. -/
@[instance_reducible] def strict (p q : Prop) : LT R :=
  ⟨fun a b => if a = (0,0) ∧ b = (0,1) then p
    else if a = (1,1) ∧ b = (1,2) then q else Pos p a b⟩

theorem strictSpec {p q : Prop} (equiv : p ↔ q) (a b : R) : (strict p q).lt a b ↔ Pos p a b := by
  change (if _ then _ else if _ then _ else _) ↔ _
  split
  next h =>
    rcases h with ⟨rfl,rfl⟩
    exact ⟨fun hp => ⟨⟨0,rfl⟩, Or.inr ⟨rfl,hp⟩⟩, fun ⟨_,h⟩ => h.elim (fun no => (Signed.irrefl _ no).elim) (·.2)⟩
  next =>
    split
    next h =>
      rcases h with ⟨rfl,rfl⟩
      exact ⟨fun hq => ⟨⟨0,rfl⟩, Or.inr ⟨rfl,equiv.mpr hq⟩⟩, fun ⟨_,h⟩ => h.elim (fun no => (Signed.irrefl _ no).elim) (fun h => equiv.mp h.2)⟩
    next => exact Iff.rfl

theorem transPos {a b c : R} {p : Prop} (h : Pos p a b) (k : Pos p b c) : Pos p a c := by
  refine ⟨Signed.transLess h.1 k.1, ?_⟩
  cases h.2 with
  | inl lt =>
    cases k.2 with
    | inl lt' => exact Or.inl (Signed.transLess lt lt')
    | inr same => exact Or.inl (same.1 ▸ lt)
  | inr same =>
    cases k.2 with
    | inl lt' => exact Or.inl (same.1 ▸ lt')
    | inr same' => exact Or.inr ⟨same.1.trans same'.1,same.2⟩

theorem preorder (p : Prop) : @Std.IsPreorder R (weak p) :=
  @Std.IsPreorder.mk R (weak p) (fun _ => Or.inl rfl) (fun _ _ _ h k => by
    cases h with
    | inl same => exact same ▸ k
    | inr h =>
      cases k with
      | inl same => exact same ▸ Or.inr h
      | inr k => exact Or.inr (transPos h k))

theorem lawful {p q : Prop} (e : p ↔ q) : @Std.LawfulOrderLT R (strict p q) (weak p) := by
  letI := strict p q
  letI := weak p
  refine ⟨?_⟩
  intro a b
  apply (strictSpec e a b).trans
  constructor
  · intro pos
    refine ⟨Or.inr pos, ?_⟩
    intro rev
    cases rev with
    | inl same => exact Signed.irrefl _ (same ▸ pos.1)
    | inr neg => exact Signed.asymm pos.1 neg.1
  · rintro ⟨same | pos, no⟩
    · exact False.elim (no (Or.inl same.symm))
    · exact pos

theorem addPos {p : Prop} (a b c : R) : Pos p a b ↔ Pos p (a+c) (b+c) := by
  constructor
  · intro h
    refine ⟨Signed.addLess h.1 _, ?_⟩
    exact h.2.imp (Signed.addLess · _) (fun ⟨eq,h⟩ => ⟨congrArg (Signed.add · c.1) eq,h⟩)
  · intro h
    refine ⟨Signed.lessOfAdd h.1, ?_⟩
    exact h.2.imp Signed.lessOfAdd (fun ⟨eq,h⟩ => ⟨Signed.cancel eq,h⟩)

theorem orderedAdd (p : Prop) : @OrderedAdd R _ (weak p) (preorder p) := by
  letI := weak p
  letI := preorder p
  refine ⟨?_⟩
  intro a b c
  constructor
  · exact Or.imp (congrArg (· + c)) (addPos a b c).mp
  · exact Or.imp (fun eq => pairEq (Signed.cancel (congrArg Prod.fst eq)) (Signed.cancel (congrArg Prod.snd eq))) (addPos a b c).mpr

theorem mulPos {p : Prop} {a b c : R} (h : Pos p a b) (hc : Pos p 0 c) : Pos p (c*a) (c*b) := by
  refine ⟨Signed.mulLess h.1 hc.1, ?_⟩
  cases hc.2 with
  | inl pos => exact h.2.imp (Signed.mulLess · pos) (fun k => ⟨congrArg (Signed.mul c.1 ·) k.1,k.2⟩)
  | inr z =>
    refine Or.inr ⟨?_,z.2⟩
    change Signed.mul c.1 a.1 = Signed.mul c.1 b.1
    have hz : (0 : Int) = c.1 := z.1
    rw [← hz, Signed.zeroMul,Signed.zeroMul]

theorem orderedRing {p q : Prop} (e : p ↔ q) :
    @OrderedRing R _ (weak p) (strict p q) (preorder p) := by
  letI := weak p
  letI := strict p q
  letI := preorder p
  letI := orderedAdd p
  constructor
  · exact (strictSpec e _ _).mpr ⟨⟨0,rfl⟩, Or.inl ⟨0,rfl⟩⟩
  · intro a b c h hc
    exact (strictSpec e _ _).mpr (mulPos ((strictSpec e _ _).mp h) ((strictSpec e _ _).mp hc))
  · intro a b c h hc
    rw [CommSemiring.mul_comm a c, CommSemiring.mul_comm b c]
    exact (strictSpec e _ _).mpr (mulPos ((strictSpec e _ _).mp h) ((strictSpec e _ _).mp hc))

/-- Compare zero with the context variable, then add one to both operands. -/
public abbrev translates {α : Type} [Ring α] [LE α] [LT α] (ctx : CommRing.Context α) : Prop :=
  (CommRing.Expr.denote ctx (.num 0) < CommRing.Expr.denote ctx (.var 0)) =
  (CommRing.Expr.denote ctx (.num 1) < CommRing.Expr.denote ctx (.add (.var 0) (.num 1)))

public theorem propextFromLT (rule : ∀ {α : Type} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    [OrderedRing α] (ctx : CommRing.Context α), translates ctx) : type_of% @propext := by
  intro p q e
  letI := weak p
  letI := strict p q
  letI := preorder p
  letI := lawful e
  letI := orderedRing e
  exact rule (.leaf ((0,1) : R))

public theorem propextFromLTNC (rule : ∀ {α : Type} [Ring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    [OrderedRing α] (ctx : CommRing.Context α), translates ctx) : type_of% @propext := by
  intro p q e
  letI := weak p
  letI := strict p q
  letI := preorder p
  letI := lawful e
  letI := orderedRing e
  exact rule (.leaf ((0,1) : R))


end OmegaChecks.InitBoundaries.StrictRingOrder
