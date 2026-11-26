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


private theorem unscaleNonpos {α : Type u} [IntModule α] [LE α] [Std.IsLinearOrder α]
    [OrderedAdd α] (a : α) {k : Nat} (pos : 0 < k) (scaled : k • a ≤ 0) : a ≤ 0 := by
  cases Std.le_total (a := a) (b := 0) with
  | inl nonpos => exact nonpos
  | inr nonneg =>
    have step := OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg (k₁ := 1) (k₂ := k)
      (x := a) (y := a) pos (Std.le_refl a) nonneg
    rw [NatModule.one_nsmul] at step
    exact Std.le_trans step scaled

public theorem Lean.Grind.Linarith.le_coeff :
    type_of% @_root_.Lean.Grind.Linarith.le_coeff := by
  intro α _ _ _ _ _ _ ctx p q k cert scaled
  have both := Bool.and_eq_true_iff.mp (show (decide (0 < k) && p == q.mul k) = true from cert)
  rw [eq_of_beq both.2, Poly.denote'_eq_denote, Poly.denote_mul, IntModule.zsmul_natCast_eq_nsmul] at scaled
  rw [Poly.denote'_eq_denote]
  exact unscaleNonpos _ (of_decide_eq_true both.1) scaled

public theorem Lean.Grind.Linarith.lt_coeff :
    type_of% @_root_.Lean.Grind.Linarith.lt_coeff := by
  intro α _ _ _ _ _ _ ctx p q k cert scaled
  have both := Bool.and_eq_true_iff.mp (show (decide (0 < k) && p == q.mul k) = true from cert)
  rw [eq_of_beq both.2, Poly.denote'_eq_denote, Poly.denote_mul, IntModule.zsmul_natCast_eq_nsmul] at scaled
  rw [Poly.denote'_eq_denote]
  exact Std.lt_iff_le_and_not_ge.mpr
    ⟨unscaleNonpos _ (of_decide_eq_true both.1) (Preorder.le_of_lt scaled),
      fun nonneg => (Std.lt_iff_le_and_not_ge.mp scaled).2 (OrderedAdd.nsmul_nonneg nonneg)⟩

public theorem Lean.Grind.Linarith.diseq_split :
    type_of% @_root_.Lean.Grind.Linarith.diseq_split := by
  intro α _ _ _ _ _ _ ctx p q cert diff
  have eq := eq_of_beq (show (q == p.mul (-1)) = true from cert)
  rw [Poly.denote'_eq_denote] at diff
  rw [Poly.denote'_eq_denote, eq, Poly.denote'_eq_denote, Poly.denote_mul, IntModule.neg_zsmul,
      IntModule.one_zsmul]
  cases Std.le_total (a := p.denote ctx) (b := 0) with
  | inl nonpos => exact Or.inl (Std.lt_iff_le_and_not_ge.mpr ⟨nonpos, fun nonneg => diff (Std.le_antisymm nonpos nonneg)⟩)
  | inr nonneg =>
    have pos := Std.lt_iff_le_and_not_ge.mpr ⟨nonneg, fun nonpos => diff (Std.le_antisymm nonpos nonneg)⟩
    have h := OrderedAdd.neg_lt_iff (a := p.denote ctx) (b := 0)
    rw [AddCommGroup.neg_zero] at h
    exact Or.inr (h.mpr pos)

open _root_.Int.Internal.Linear

public theorem Int.Internal.Linear.cdiv_eq_div_of_divides :
    type_of% @_root_.Int.Internal.Linear.cdiv_eq_div_of_divides := by
  intro a b zero
  unfold cdiv
  rw [Int.neg_ediv_of_dvd (Int.dvd_of_emod_eq_zero zero), Int.neg_neg]

public theorem Int.Internal.Linear.cmod_eq_zero_iff_emod_eq_zero :
    type_of% @_root_.Int.Internal.Linear.cmod_eq_zero_iff_emod_eq_zero := by
  intro a b
  constructor
  · intro h
    have h' := congrArg Neg.neg h
    change -(-((-a) % b)) = -(0 : Int) at h'
    rw [Int.neg_neg] at h'
    exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mp (Int.dvd_of_emod_eq_zero h'))
  · intro h
    change -((-a) % b) = 0
    rw [Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))]
    rfl

public theorem Int.Internal.Linear.Poly.denote_div_eq_of_divAll :
    type_of% @_root_.Int.Internal.Linear.Poly.denote_div_eq_of_divAll := by
  intro ctx p k divisible
  induction p with
  | num n =>
    have d : n % k = 0 := eq_of_beq divisible
    change cdiv n k * k = n
    rw [← cdiv_eq_div_of_divides d]
    exact Int.ediv_mul_cancel_of_emod_eq_zero d
  | add n x p ih =>
    have both := Bool.and_eq_true_iff.mp (show
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (n % k) 0 && p.divAll k) = true from divisible)
    change ((n/k) * x.denote ctx + (p.div k).denote ctx) * k = n * x.denote ctx + p.denote ctx
    rw [Int.add_mul, Int.mul_right_comm (n/k) (x.denote ctx) k,
        Int.ediv_mul_cancel_of_emod_eq_zero (eq_of_beq both.1), ih both.2]

public theorem Int.Internal.Linear.dvd_unsat :
    type_of% @_root_.Int.Internal.Linear.dvd_unsat := by
  intro ctx k p cert divides
  rw [_root_.Int.Internal.Linear.Poly.denote'_eq_denote] at divides
  exact (bne_iff_ne.mp cert) (Int.emod_eq_zero_of_dvd (_root_.Int.Internal.Linear.Poly.gcd_dvd_const divides))

end OmegaChecks.InitPort.Alternatives
