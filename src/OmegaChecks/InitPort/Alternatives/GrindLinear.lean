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


private theorem shiftCooperIneq {a b t : Int} (ineq : t + b ≤ a) : b + -a + t ≤ 0 := by
  have shift := Int.add_le_add_right ineq (-a)
  rw [Int.add_right_neg] at shift
  rw [Int.add_comm (b + -a) t, ← Int.add_assoc]
  exact shift

private theorem mapOrOver {p q : Nat → Prop} (f : ∀ i, p i → q i) (n : Nat) :
    OrOver n p → OrOver n q := by
  induction n with
  | zero => exact id
  | succ k ih => exact fun h => h.elim (fun hit => Or.inl (f k hit)) (fun tail => Or.inr (ih tail))

public theorem Int.Internal.Linear.cooper_dvd_left_core :
    type_of% (private_decl% @_root_.Int.Internal.Linear.cooper_dvd_left_core) := by
  intro a b c d s p q x aNeg bPos dPos hx hy hd
  have lower : p ≤ (-a)*x := by
    rw [Int.neg_mul]
    exact Int.add_le_zero_iff_le_neg'.mp hx
  have upper := Int.add_le_zero_iff_le_neg.mp hy
  obtain ⟨k, nonneg, bound, ineq, div₁, div₂⟩ :=
    (Int.cooper_resolution_dvd_left (Int.neg_pos_of_neg aNeg) bPos dPos).mp ⟨x, lower, upper, hd⟩
  rw [Int.neg_mul_neg] at ineq
  rw [Int.neg_mul, Int.neg_gcd, (private_decl% _root_.Int.Internal.Linear.lcm_neg_left), Int.neg_ediv_of_dvd (Int.gcd_dvd_left ..), (private_decl% _root_.Int.Internal.Linear.lcm_neg_right)] at bound
  have first := Int.neg_dvd.mp div₁
  rw [Int.add_comm k p] at first
  rw [Int.neg_mul a d] at div₂
  have second := Int.neg_dvd.mp div₂
  rw [Int.add_assoc, Int.add_comm (c*k)] at second
  apply (private_decl% _root_.Int.Internal.Linear.orOver_of_p) (ofNat_lt nonneg bound)
  rw [cast_toNat nonneg, Int.neg_mul a q]
  exact ⟨shiftCooperIneq ineq, first, second⟩

public theorem Int.Internal.Linear.cooper_left_core :
    type_of% (private_decl% @_root_.Int.Internal.Linear.cooper_left_core) := by
  intro a b p q x aNeg bPos hx hy
  have trivialDiv : (1 : Int) ∣ 0*x + 0 := Int.one_dvd _
  have full := (private_decl% _root_.Int.Internal.Linear.cooper_dvd_left_core) aNeg bPos (by decide) hx hy trivialDiv
  rw [Int.mul_one, (private_decl% _root_.Int.Internal.Linear.gcd_zero), Int.ofNat_natAbs_of_nonpos (Int.le_of_lt aNeg), Int.ediv_neg,
      Int.ediv_self (Int.ne_of_lt aNeg), (private_decl% _root_.Int.Internal.Linear.lcm_neg_right), (private_decl% _root_.Int.Internal.Linear.lcm_one)] at full
  exact mapOrOver (fun _ data => ⟨data.1, data.2.1⟩) _ full

public theorem Int.Internal.Linear.cooper_dvd_right_core :
    type_of% (private_decl% @_root_.Int.Internal.Linear.cooper_dvd_right_core) := by
  intro a b c d s p q x aNeg bPos dPos hx hy hd
  have lower : p ≤ (-a)*x := by
    rw [Int.neg_mul]
    exact Int.add_le_zero_iff_le_neg'.mp hx
  have upper := Int.add_le_zero_iff_le_neg.mp hy
  obtain ⟨k, nonneg, bound, ineq, div₁, div₂⟩ :=
    (Int.cooper_resolution_dvd_right (Int.neg_pos_of_neg aNeg) bPos dPos).mp ⟨x, lower, upper, hd⟩
  rw [Int.neg_mul_neg] at ineq
  rw [Int.sub_neg, Int.add_comm k q] at div₁
  rw [Int.mul_neg c q, ← Int.neg_mul c q, Int.add_assoc, Int.add_comm ((-c)*k)] at div₂
  apply (private_decl% _root_.Int.Internal.Linear.orOver_of_p) (ofNat_lt nonneg bound)
  rw [cast_toNat nonneg, Int.neg_mul a q]
  exact ⟨shiftCooperIneq ineq, div₁, div₂⟩

public theorem Int.Internal.Linear.cooper_right_core :
    type_of% (private_decl% @_root_.Int.Internal.Linear.cooper_right_core) := by
  intro a b p q x aNeg bPos hx hy
  have trivialDiv : (1 : Int) ∣ 0*x + 0 := Int.one_dvd _
  have full := (private_decl% _root_.Int.Internal.Linear.cooper_dvd_right_core) aNeg bPos (by decide) hx hy trivialDiv
  rw [Int.mul_one, (private_decl% _root_.Int.Internal.Linear.gcd_zero), Int.natAbs_of_nonneg (Int.le_of_lt bPos),
      Int.ediv_self (Int.ne_of_gt bPos), (private_decl% _root_.Int.Internal.Linear.lcm_one)] at full
  exact mapOrOver (fun _ data => ⟨data.1, data.2.1⟩) _ full


public theorem Int.Internal.Linear.cooper_left :
    type_of% @_root_.Int.Internal.Linear.cooper_left := by
  intro ctx p₁ p₂ n cert hp hq
  cases p₁ with
  | num => contradiction
  | add a x p =>
    cases p₂ with
    | num => contradiction
    | add b y q =>
      have xy := Bool.and_eq_true_iff.mp (show (x.beq y && (decide (a < 0) && (decide (0 < b) && n.beq (a.natAbs)))) = true from cert)
      cases Nat.eq_of_beq_eq_true xy.1
      have neg := Bool.and_eq_true_iff.mp xy.2
      have pos := Bool.and_eq_true_iff.mp neg.2
      cases Nat.eq_of_beq_eq_true pos.2
      rw [_root_.Int.Internal.Linear.Poly.denote'_add] at hp hq
      have hit := (private_decl% _root_.Int.Internal.Linear.cooper_left_core)
        (of_decide_eq_true neg.1) (of_decide_eq_true pos.1) hp hq
      refine mapOrOver (fun k value => ?_) _ hit
      dsimp only [cooper_left_split, _root_.Int.Internal.Linear.Poly.tail, _root_.Int.Internal.Linear.Poly.leadCoeff]
      rw [(private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq),
          (private_decl% _root_.Int.Internal.Linear.denote'_addConst_eq)]
      exact value

public theorem Int.Internal.Linear.cooper_right :
    type_of% @_root_.Int.Internal.Linear.cooper_right := by
  intro ctx p₁ p₂ n cert hp hq
  cases p₁ with
  | num => contradiction
  | add a x p =>
    cases p₂ with
    | num => contradiction
    | add b y q =>
      have xy := Bool.and_eq_true_iff.mp (show (x.beq y && (decide (a < 0) && (decide (0 < b) && n.beq (b.natAbs)))) = true from cert)
      cases Nat.eq_of_beq_eq_true xy.1
      have neg := Bool.and_eq_true_iff.mp xy.2
      have pos := Bool.and_eq_true_iff.mp neg.2
      cases Nat.eq_of_beq_eq_true pos.2
      rw [_root_.Int.Internal.Linear.Poly.denote'_add] at hp hq
      have hit := (private_decl% _root_.Int.Internal.Linear.cooper_right_core)
        (of_decide_eq_true neg.1) (of_decide_eq_true pos.1) hp hq
      refine mapOrOver (fun k value => ?_) _ hit
      dsimp only [cooper_right_split, _root_.Int.Internal.Linear.Poly.tail, _root_.Int.Internal.Linear.Poly.leadCoeff]
      rw [_root_.Int.Internal.Linear.Poly.mul_k_eq_mul, _root_.Int.Internal.Linear.Poly.mul_k_eq_mul,
          (private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq),
          (private_decl% _root_.Int.Internal.Linear.denote'_addConst_eq)]
      exact value

public theorem Int.Internal.Linear.cooper_dvd_left :
    type_of% @_root_.Int.Internal.Linear.cooper_dvd_left := by
  intro ctx p₁ p₂ p₃ d n cert hp hq hs
  cases p₁ with
  | num => contradiction
  | add a x p =>
    cases p₂ with
    | num => contradiction
    | add b y q =>
      cases p₃ with
      | num => contradiction
      | add c z s =>
        have xy := Bool.and_eq_true_iff.mp (show (x.beq y && (x.beq z && (decide (a < 0) && (decide (0 < b) && (decide (0 < d) && n.beq (Int.lcm a (a*d / Int.gcd (a*d) c))))))) = true from cert)
        cases Nat.eq_of_beq_eq_true xy.1
        have xz := Bool.and_eq_true_iff.mp xy.2
        cases Nat.eq_of_beq_eq_true xz.1
        have neg := Bool.and_eq_true_iff.mp xz.2
        have pos := Bool.and_eq_true_iff.mp neg.2
        have divisor := Bool.and_eq_true_iff.mp pos.2
        cases Nat.eq_of_beq_eq_true divisor.2
        rw [_root_.Int.Internal.Linear.Poly.denote'_add] at hp hq hs
        have hit := (private_decl% _root_.Int.Internal.Linear.cooper_dvd_left_core)
          (of_decide_eq_true neg.1) (of_decide_eq_true pos.1) (of_decide_eq_true divisor.1) hp hq hs
        refine mapOrOver (fun k value => ?_) _ hit
        dsimp only [cooper_dvd_left_split, _root_.Int.Internal.Linear.Poly.tail, _root_.Int.Internal.Linear.Poly.leadCoeff]
        rw [(private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq),
            (private_decl% _root_.Int.Internal.Linear.denote'_addConst_eq),
            (private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq)]
        exact value

public theorem Int.Internal.Linear.cooper_dvd_right :
    type_of% @_root_.Int.Internal.Linear.cooper_dvd_right := by
  intro ctx p₁ p₂ p₃ d n cert hp hq hs
  cases p₁ with
  | num => contradiction
  | add a x p =>
    cases p₂ with
    | num => contradiction
    | add b y q =>
      cases p₃ with
      | num => contradiction
      | add c z s =>
        have xy := Bool.and_eq_true_iff.mp (show (x.beq y && (x.beq z && (decide (a < 0) && (decide (0 < b) && (decide (0 < d) && n.beq (Int.lcm b (b*d / Int.gcd (b*d) c))))))) = true from cert)
        cases Nat.eq_of_beq_eq_true xy.1
        have xz := Bool.and_eq_true_iff.mp xy.2
        cases Nat.eq_of_beq_eq_true xz.1
        have neg := Bool.and_eq_true_iff.mp xz.2
        have pos := Bool.and_eq_true_iff.mp neg.2
        have divisor := Bool.and_eq_true_iff.mp pos.2
        cases Nat.eq_of_beq_eq_true divisor.2
        rw [_root_.Int.Internal.Linear.Poly.denote'_add] at hp hq hs
        have hit := (private_decl% _root_.Int.Internal.Linear.cooper_dvd_right_core)
          (of_decide_eq_true neg.1) (of_decide_eq_true pos.1) (of_decide_eq_true divisor.1) hp hq hs
        refine mapOrOver (fun k value => ?_) _ hit
        dsimp only [cooper_dvd_right_split, _root_.Int.Internal.Linear.Poly.tail, _root_.Int.Internal.Linear.Poly.leadCoeff]
        rw [(private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq),
            (private_decl% _root_.Int.Internal.Linear.denote'_addConst_eq),
            (private_decl% _root_.Int.Internal.Linear.denote'_mul_combine_mul_addConst_eq)]
        exact value


private theorem intPositiveOfBlt {k : Int} (h : Int.blt' 0 k) : 0 < k := by
  cases k with
  | negSucc => contradiction
  | ofNat n =>
    cases n with
    | zero => contradiction
    | succ n => exact Int.natCast_pos.mpr (Nat.zero_lt_succ n)

public theorem Int.Internal.Linear.eq_unsat_coeff :
    type_of% @_root_.Int.Internal.Linear.eq_unsat_coeff := by
  intro ctx p k cert zero
  have both := Bool.and_eq_true_iff.mp
    (show (p.divCoeffs k && (Int.blt' 0 k && decide (cmod p.getConst k < 0))) = true from cert)
  have bounds := Bool.and_eq_true_iff.mp both.2
  have pos := intPositiveOfBlt bounds.1
  have divide := _root_.Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs ctx p k both.1
  rw [_root_.Int.Internal.Linear.Poly.denote'_eq_denote] at zero
  exact (private_decl% _root_.Int.Internal.Linear.contra) pos (cmod_gt_of_pos p.getConst pos)
    (of_decide_eq_true bounds.2) (divide.trans zero)

private theorem linearPolyEqOfBeq {p q : _root_.Int.Internal.Linear.Poly} (h : p.beq' q) : p = q := by
  induction p generalizing q with
  | num a =>
    cases q with
    | num b =>
      change Int.beq' a b = true at h
      rw [Int.beq'_eq_beq] at h
      exact congrArg _root_.Int.Internal.Linear.Poly.num (eq_of_beq h)
    | add => contradiction
  | add a x p ih =>
    cases q with
    | num => contradiction
    | add b y q =>
      have both := Bool.and_eq_true_iff.mp
        (show (Int.beq' a b && (x.beq y && p.beq' q)) = true from h)
      have tails := Bool.and_eq_true_iff.mp both.2
      have coeff := both.1
      rw [Int.beq'_eq_beq] at coeff
      cases eq_of_beq coeff
      cases Nat.eq_of_beq_eq_true tails.1
      exact congrArg (_root_.Int.Internal.Linear.Poly.add a x) (ih tails.2)

public theorem Int.Internal.Linear.le_of_le_diseq :
    type_of% @_root_.Int.Internal.Linear.le_of_le_diseq := by
  intro ctx p q result cert nonpos neq
  have parts := Bool.and_eq_true_iff.mp (show
    ((q.beq' p || q.beq' (p.mul_k (-1))) && result.beq' (p.addConst_k 1)) = true from cert)
  rw [linearPolyEqOfBeq parts.2, _root_.Int.Internal.Linear.Poly.addConst_k_eq_addConst,
      _root_.Int.Internal.Linear.Poly.denote'_eq_denote, _root_.Int.Internal.Linear.Poly.denote_addConst]
  rw [_root_.Int.Internal.Linear.Poly.denote'_eq_denote] at nonpos neq
  have nz : p.denote ctx ≠ 0 := by
    intro zero
    apply neq
    cases Bool.or_eq_true_iff.mp parts.1 with
    | inl eq => rw [linearPolyEqOfBeq eq, zero]
    | inr eq =>
      rw [linearPolyEqOfBeq eq, _root_.Int.Internal.Linear.Poly.mul_k_eq_mul,
          _root_.Int.Internal.Linear.Poly.denote_mul, zero, Int.mul_zero]
  exact Int.add_one_le_iff.mpr ((Int.lt_or_gt_of_ne nz).resolve_right (fun gt => (Int.not_le_of_gt gt) nonpos))

private theorem intNormDifference (ctx : _root_.Int.Internal.Linear.Context)
    (lhs rhs : _root_.Int.Internal.Linear.Expr) (p : _root_.Int.Internal.Linear.Poly)
    (cert : _root_.Int.Internal.Linear.norm_eq_cert lhs rhs p) :
    p.denote' ctx = lhs.denote ctx - rhs.denote ctx := by
  rw [linearPolyEqOfBeq cert, _root_.Int.Internal.Linear.Poly.denote'_eq_denote,
    _root_.Int.Internal.Linear.Expr.denote_norm]
  rfl

public theorem Int.Internal.Linear.le_norm_expr : type_of% @_root_.Int.Internal.Linear.le_norm_expr := by
  intro ctx lhs rhs p cert bound
  rw [intNormDifference ctx lhs rhs p cert]
  exact Int.sub_nonpos_of_le bound

public theorem Int.Internal.Linear.eq_norm_expr : type_of% @_root_.Int.Internal.Linear.eq_norm_expr := by
  intro ctx lhs rhs p cert eq
  rw [intNormDifference ctx lhs rhs p cert, eq, Int.sub_self]

public theorem Int.Internal.Linear.norm_le : type_of% @_root_.Int.Internal.Linear.norm_le := by
  intro ctx lhs rhs p cert
  rw [intNormDifference ctx lhs rhs p cert]
  apply congrArg Int.NonNeg
  rw [Int.zero_sub, Int.neg_sub]

public theorem Int.Internal.Linear.norm_dvd : type_of% @_root_.Int.Internal.Linear.norm_dvd := by
  intro ctx k e p cert
  exact congrArg (fun value : Int => k ∣ value) (_root_.Int.Internal.Linear.Expr.eq_of_norm_eq ctx e p cert)

end OmegaChecks.InitPort.Alternatives
