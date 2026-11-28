module
import all Init.Grind.Module.NatModuleNorm
import all Init.Grind.Module.Envelope

/-! Interpret normalized polynomials with nonnegative coefficients in a natural module.

The six envelope lemmas below have specialized interfaces. Ordinary imports of the
pinned module keep `OfNatModule.ofNatModule` opaque, so its addition, zero and scalar
action fields in `toQ_add`, `toQ_zero` and `toQ_smul` do not reduce. The order
instances unfold, but the comparisons in `mk_le_mk`, `toQ_le` and `toQ_lt` reach
`Q.liftOn₂`, whose body is also opaque to ordinary imports.
-/

open Lean.Grind Lean.Grind.Linarith
namespace OmegaChecks.InitPort.Alternatives

section
open Std

public theorem Lean.Grind.IntModule.OfNatModule.mk_le_mk {α : Type u} [NatModule α] [LE α] [IsPreorder α] [OrderedAdd α]
    {a₁ a₂ b₁ b₂ : α} : (a₁ + b₂ ≤ a₂ + b₁) ↔ a₁ + b₂ ≤ a₂ + b₁ := Iff.rfl

public theorem Lean.Grind.IntModule.OfNatModule.toQ_le {α : Type u} [NatModule α] [LE α] [IsPreorder α] [OrderedAdd α]
    {a b : α} : (a + 0 ≤ 0 + b) ↔ a ≤ b := by
  rw [AddCommMonoid.add_zero, AddCommMonoid.zero_add]

public theorem Lean.Grind.IntModule.OfNatModule.toQ_lt {α : Type u} [NatModule α] [LE α] [LT α] [LawfulOrderLT α]
    [IsPreorder α] [OrderedAdd α] {a b : α} :
    ((a + 0 ≤ 0 + b) ∧ ¬(b + 0 ≤ 0 + a)) ↔ a < b := by
  rw [AddCommMonoid.add_zero, AddCommMonoid.zero_add, AddCommMonoid.add_zero, AddCommMonoid.zero_add,
    LawfulOrderLT.lt_iff]

end

open _root_.Lean.Grind.IntModule.OfNatModule in
public theorem Lean.Grind.IntModule.OfNatModule.toQ_zero {α : Type u} [NatModule α] :
    toQ (0 : α) = zero := by
  unfold toQ zero
  rfl

open _root_.Lean.Grind.IntModule.OfNatModule in
public theorem Lean.Grind.IntModule.OfNatModule.toQ_add {α : Type u} [NatModule α] (a b : α) :
    toQ (a + b) = Q.mk (a + b, (0 : α) + 0) := by
  rw [AddCommMonoid.add_zero]
  rfl

open _root_.Lean.Grind.IntModule.OfNatModule in
public theorem Lean.Grind.IntModule.OfNatModule.toQ_smul {α : Type u} [NatModule α] (n : Nat) (a : α) :
    toQ (n • a) = Q.mk (n • a, n • (0 : α)) := by
  rw [NatModule.nsmul_zero]
  rfl

public theorem Lean.Grind.Linarith.Poly.denoteN_add : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_add := by
  intro α _ ctx k x p h
  cases k with
  | ofNat n =>
    simp only [Poly.denoteN]
    rw [show decide ((Int.ofNat n) < 0) = false from decide_eq_false (Int.not_lt_of_ge h)]
    rfl
  | negSucc n => exact False.elim (Int.not_le_of_gt (Int.negSucc_lt_zero n) h)

public theorem Lean.Grind.Linarith.Poly.denoteN_append : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_append := by
  intro α _ ctx p q hp hq
  induction hp with
  | nil => exact (AddCommMonoid.zero_add _).symm
  | add k x p hk _ ih =>
    change (Poly.add k x (p.append q)).denoteN ctx = _
    rw [Poly.denoteN_add _ _ _ _ hk, Poly.denoteN_add _ _ _ _ hk, ih, AddCommMonoid.add_assoc]

public theorem Lean.Grind.Linarith.Poly.denoteN_insert : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_insert := by
  intro α _ ctx k x p hk
  apply Poly.insert.induct_unfolding k x
    (fun p r => p.NonnegCoeffs → r.denoteN ctx = k.toNat • x.denote ctx + p.denoteN ctx) _ _ _ _ _ p
  · exact fun _ => Poly.denoteN_add _ _ _ _ hk
  · exact fun l y p _ _ => Poly.denoteN_add _ _ _ _ hk
  · intro l y p _ same zero hp
    cases hp with | add _ _ _ hl _ =>
      cases (eq_of_beq same : x = y)
      have z : k + l = 0 := eq_of_beq zero
      rw [Poly.denoteN_add _ _ _ _ hl, ← AddCommMonoid.add_assoc, ← NatModule.add_nsmul,
        ← Int.toNat_add hk hl, z, Int.toNat_zero, NatModule.zero_nsmul, AddCommMonoid.zero_add]
  · intro l y p _ same _ hp
    cases hp with | add _ _ _ hl _ =>
      cases (eq_of_beq same : x = y)
      change (Poly.add (k+l) x p).denoteN ctx = _
      rw [Poly.denoteN_add _ _ _ _ (Int.add_nonneg hk hl), Poly.denoteN_add _ _ _ _ hl,
        Int.toNat_add hk hl, NatModule.add_nsmul, AddCommMonoid.add_assoc]
  · intro l y p _ _ ih hp
    cases hp with | add _ _ _ hl tail =>
      rw [Poly.denoteN_add _ _ _ _ hl, Poly.denoteN_add _ _ _ _ hl, ih tail, AddCommMonoid.add_left_comm]

private theorem shuffleTerms {α : Type u} [NatModule α] (a b p q : α) :
    (a+p)+(b+q) = (a+b)+(p+q) := by
  rw [AddCommMonoid.add_assoc, AddCommMonoid.add_left_comm p b, ← AddCommMonoid.add_assoc]

public theorem Lean.Grind.Linarith.Poly.denoteN_combine : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_combine := by
  intro α _ ctx p q
  apply Poly.combine.induct_unfolding
    (fun p q r => p.NonnegCoeffs → q.NonnegCoeffs → r.denoteN ctx = p.denoteN ctx + q.denoteN ctx)
    _ _ _ _ _ _ p q
  · exact fun _ _ _ => (AddCommMonoid.zero_add _).symm
  · exact fun _ _ _ _ => (AddCommMonoid.add_zero _).symm
  · intro k x p l y q same _ zero ih hp hq
    cases hp with | add _ _ _ hk tailP =>
      cases hq with | add _ _ _ hl tailQ =>
        cases (eq_of_beq same : x = y)
        have z : k+l = 0 := eq_of_beq zero
        rw [ih tailP tailQ, Poly.denoteN_add _ _ _ _ hk, Poly.denoteN_add _ _ _ _ hl,
          shuffleTerms, ← NatModule.add_nsmul, ← Int.toNat_add hk hl, z, Int.toNat_zero,
          NatModule.zero_nsmul, AddCommMonoid.zero_add]
  · intro k x p l y q same _ _ ih hp hq
    cases hp with | add _ _ _ hk tailP =>
      cases hq with | add _ _ _ hl tailQ =>
        cases (eq_of_beq same : x = y)
        rw [Poly.denoteN_add _ _ _ _ (Int.add_nonneg hk hl), Poly.denoteN_add _ _ _ _ hk,
          Poly.denoteN_add _ _ _ _ hl, ih tailP tailQ, Int.toNat_add hk hl, NatModule.add_nsmul,
          shuffleTerms]
  · intro k x p l y q _ _ ih hp hq
    cases hp with | add _ _ _ hk tail =>
      rw [Poly.denoteN_add _ _ _ _ hk, Poly.denoteN_add _ _ _ _ hk, ih tail hq, AddCommMonoid.add_assoc]
  · intro k x p l y q _ _ ih hp hq
    cases hq with | add _ _ _ hl tail =>
      rw [Poly.denoteN_add _ _ _ _ hl, Poly.denoteN_add _ _ _ _ hl, ih hp tail, AddCommMonoid.add_left_comm]

public theorem Lean.Grind.Linarith.Poly.denoteN_mul' : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_mul' := by
  intro α _ ctx p k hp
  induction hp with
  | nil => exact (NatModule.nsmul_zero k).symm
  | add l x p hl _ ih =>
    change (Poly.add ((k : Int)*l) x _).denoteN ctx = _
    have hk := Int.natCast_nonneg k
    rw [Poly.denoteN_add _ _ _ _ (Int.mul_nonneg hk hl), Poly.denoteN_add _ _ _ _ hl, ih,
      Int.toNat_mul hk hl, Int.toNat_natCast, NatModule.mul_nsmul, NatModule.nsmul_add]

public theorem Lean.Grind.Linarith.Poly.denoteN_mul : type_of% @_root_.Lean.Grind.Linarith.Poly.denoteN_mul := by
  intro α _ ctx p k hp
  cases k with
  | zero => exact (NatModule.zero_nsmul _).symm
  | succ k =>
    apply Eq.trans _ (Poly.denoteN_mul' ctx p (k+1) hp)
    unfold Poly.mul
    rw [ite_eq_right (fun e => False.elim ((Nat.succ_ne_zero k) (Int.ofNat_eq_zero.mp (eq_of_beq e))))]

public theorem Lean.Grind.Linarith.Expr.denoteN_toPolyN :
    type_of% @_root_.Lean.Grind.Linarith.Expr.denoteN_toPolyN := by
  intro α _ ctx e
  induction e with
  | zero | sub | neg | intMul => rfl
  | var x =>
    change (Poly.add 1 x .nil).denoteN ctx = _
    rw [Poly.denoteN_add ctx 1 x .nil (by decide), Poly.denoteN_nil]
    exact (AddCommMonoid.add_zero _).trans (NatModule.one_nsmul _)
  | add a b ia ib =>
    change (a.toPolyN.combine b.toPolyN).denoteN ctx = _
    rw [Poly.denoteN_combine _ _ _ (Expr.toPolyN_Nonneg _) (Expr.toPolyN_Nonneg _), ia, ib]
    rfl
  | natMul k a ih =>
    change (a.toPolyN.mul k).denoteN ctx = _
    rw [Poly.denoteN_mul _ _ _ (Expr.toPolyN_Nonneg _), ih]
    rfl

public theorem Lean.Grind.Linarith.eq_normN : type_of% @_root_.Lean.Grind.Linarith.eq_normN := by
  intro α _ ctx a b equal
  have eq : a.toPolyN = b.toPolyN := eq_of_beq equal
  rw [← Expr.denoteN_toPolyN ctx a, ← Expr.denoteN_toPolyN ctx b, eq]

end OmegaChecks.InitPort.Alternatives
