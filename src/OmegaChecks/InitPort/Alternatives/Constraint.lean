module
public import Init.Omega.Constraint
public import Init.Omega.LinearCombo

open Lean.Omega

namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Omega.Constraint.not_sat_of_isImpossible :
    type_of% @_root_.Lean.Omega.Constraint.not_sat_of_isImpossible := by
  intro ⟨lo, hi⟩ impossible t satisfied
  cases lo with
  | none => exact Bool.noConfusion impossible
  | some l =>
    cases hi with
    | none => exact Bool.noConfusion impossible
    | some u =>
      have bounds : decide (l ≤ t) = true ∧ decide (t ≤ u) = true :=
        of_decide_eq_true satisfied
      exact Int.not_le_of_gt (of_decide_eq_true impossible)
        (Int.le_trans (of_decide_eq_true bounds.1) (of_decide_eq_true bounds.2))

private theorem all_merge {α : Type} (f : α → α → α) (p : α → Bool)
    (closed : ∀ x y, p x = true → p y = true → p (f x y) = true) :
    ∀ x y : Option α, x.all p = true → y.all p = true → (Option.merge f x y).all p = true
  | none, none, _, _ => rfl
  | none, some _, _, h => h
  | some _, none, h, _ => h
  | some x, some y, hx, hy => closed x y hx hy

public theorem Lean.Omega.Constraint.combine_sat' :
    type_of% @_root_.Lean.Omega.Constraint.combine_sat' := by
  intro s t x y hs ht
  let v := Coeffs.dot x y
  have sBounds : s.lowerBound.sat v ∧ s.upperBound.sat v := of_decide_eq_true hs
  have tBounds : t.lowerBound.sat v ∧ t.upperBound.sat v := of_decide_eq_true ht
  apply decide_eq_true
  constructor
  · exact all_merge max (fun a : Int => decide (a ≤ v))
      (fun _ _ h₁ h₂ => decide_eq_true (Int.max_le.mpr ⟨of_decide_eq_true h₁, of_decide_eq_true h₂⟩))
      _ _ sBounds.1 tBounds.1
  · exact all_merge min (fun a : Int => decide (v ≤ a))
      (fun _ _ h₁ h₂ => decide_eq_true (Int.le_min.mpr ⟨of_decide_eq_true h₁, of_decide_eq_true h₂⟩))
      _ _ sBounds.2 tBounds.2

private theorem all_zip {α : Type} (op : α → α → α) (p q r : α → Bool)
    (closed : ∀ a b, p a = true → q b = true → r (op a b) = true) :
    ∀ a b : Option α, a.all p = true → b.all q = true →
      (a.bind fun x => b.map (op x)).all r = true
  | none, _, _, _ => rfl
  | some _, none, _, _ => rfl
  | some x, some y, hx, hy => closed x y hx hy

public theorem Lean.Omega.Constraint.add_sat :
    type_of% @_root_.Lean.Omega.Constraint.add_sat := by
  intro c₁ c₂ x₁ x₂ h₁ h₂
  have a : c₁.lowerBound.sat x₁ ∧ c₁.upperBound.sat x₁ := of_decide_eq_true h₁
  have b : c₂.lowerBound.sat x₂ ∧ c₂.upperBound.sat x₂ := of_decide_eq_true h₂
  apply decide_eq_true
  constructor
  · exact all_zip (· + ·) (fun x => decide (x ≤ x₁)) (fun y => decide (y ≤ x₂))
      (fun z => decide (z ≤ x₁ + x₂))
      (fun _ _ hx hy => decide_eq_true (Int.add_le_add (of_decide_eq_true hx) (of_decide_eq_true hy)))
      _ _ a.1 b.1
  · exact all_zip (· + ·) (fun x => decide (x₁ ≤ x)) (fun y => decide (x₂ ≤ y))
      (fun z => decide (x₁ + x₂ ≤ z))
      (fun _ _ hx hy => decide_eq_true (Int.add_le_add (of_decide_eq_true hx) (of_decide_eq_true hy)))
      _ _ a.2 b.2

private theorem all_map {α : Type} (f : α → α) (p q : α → Bool)
    (preserves : ∀ a, p a = true → q (f a) = true) :
    ∀ a : Option α, a.all p = true → (a.map f).all q = true
  | none, _ => rfl
  | some a, h => preserves a h

public theorem Lean.Omega.Constraint.scale_sat :
    type_of% @_root_.Lean.Omega.Constraint.scale_sat := by
  intro t c k h
  have bounds : c.lowerBound.sat t ∧ c.upperBound.sat t := of_decide_eq_true h
  by_cases zero : k = 0
  · subst k
    rw [_root_.Lean.Omega.Constraint.scale, ite_eq_left rfl, Int.zero_mul]
    split
    · rename_i impossible
      exact False.elim (Lean.Omega.Constraint.not_sat_of_isImpossible impossible h)
    · exact decide_eq_true ⟨decide_eq_true (Int.le_refl 0), decide_eq_true (Int.le_refl 0)⟩
  · rw [_root_.Lean.Omega.Constraint.scale, ite_eq_right zero]
    by_cases pos : 0 < k
    · rw [ite_eq_left pos]
      apply decide_eq_true
      constructor
      · exact all_map (k * ·) (fun a => decide (a ≤ t)) (fun a => decide (a ≤ k * t))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonneg_left (of_decide_eq_true ha) (Int.le_of_lt pos))) _ bounds.1
      · exact all_map (k * ·) (fun a => decide (t ≤ a)) (fun a => decide (k * t ≤ a))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonneg_left (of_decide_eq_true ha) (Int.le_of_lt pos))) _ bounds.2
    · rw [ite_eq_right pos]
      have nonpos := Int.le_of_not_gt pos
      apply decide_eq_true
      constructor
      · exact all_map (k * ·) (fun a => decide (t ≤ a)) (fun a => decide (a ≤ k * t))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonpos_left nonpos (of_decide_eq_true ha))) _ bounds.2
      · exact all_map (k * ·) (fun a => decide (a ≤ t)) (fun a => decide (k * t ≤ a))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonpos_left nonpos (of_decide_eq_true ha))) _ bounds.1

public theorem Lean.Omega.Constraint.neg_sat :
    type_of% @_root_.Lean.Omega.Constraint.neg_sat := by
  intro c t h
  have a : c.lowerBound.sat t ∧ c.upperBound.sat t := of_decide_eq_true h
  apply decide_eq_true
  constructor
  · exact all_map Neg.neg (fun y => decide (t ≤ y)) (fun y => decide (y ≤ -t))
      (fun _ hy => decide_eq_true (Int.neg_le_neg (of_decide_eq_true hy))) _ a.2
  · exact all_map Neg.neg (fun x => decide (x ≤ t)) (fun x => decide (-t ≤ x))
      (fun _ hx => decide_eq_true (Int.neg_le_neg (of_decide_eq_true hx))) _ a.1

public theorem Lean.Omega.Constraint.div_sat :
    type_of% @_root_.Lean.Omega.Constraint.div_sat := by
  intro c t k n h w
  have pos : (0 : Int) < k := Int.ofNat_lt.mpr (Nat.pos_of_ne_zero n)
  have a : c.lowerBound.sat t ∧ c.upperBound.sat t := of_decide_eq_true w
  apply decide_eq_true
  constructor
  · apply all_map (fun x : Int => -((-x) / k)) (fun x => decide (x ≤ t)) (fun x => decide (x ≤ t / k)) _ _ a.1
    intro x p
    apply decide_eq_true
    apply Int.le_of_sub_nonneg
    rw [Int.sub_neg, ← Int.add_ediv_of_dvd_left h]
    exact (Int.ediv_nonneg_iff_of_pos pos).mpr (Int.sub_nonneg_of_le (of_decide_eq_true p))
  · apply all_map (fun y : Int => y / k) (fun y => decide (t ≤ y)) (fun y => decide (t / k ≤ y)) _ _ a.2
    intro y p
    apply decide_eq_true
    apply Int.le_of_sub_nonneg
    rw [← Int.sub_ediv_of_dvd _ h]
    exact (Int.ediv_nonneg_iff_of_pos pos).mpr (Int.sub_nonneg_of_le (of_decide_eq_true p))

public theorem Lean.Omega.normalize_sat : type_of% @_root_.Lean.Omega.normalize_sat := by
  intro s x v w
  dsimp [_root_.Lean.Omega.normalizeConstraint, _root_.Lean.Omega.normalizeCoeffs,
    _root_.Lean.Omega.normalize, _root_.Lean.Omega.normalize?]
  split
  · rename_i g
    split
    · rfl
    · rename_i no
      have z : Coeffs.dot x v = 0 := IntList.dot_eq_zero_of_left_eq_zero (IntList.gcd_eq_zero.mp g)
      exact False.elim (no (Eq.subst (motive := fun t => s.sat t = true) z w))
  · rename_i g
    split
    · exact w
    · exact _root_.Lean.Omega.Constraint.div_sat' g w

public theorem Lean.Omega.tidy_sat : type_of% @_root_.Lean.Omega.tidy_sat := by
  intro s x v w
  dsimp [_root_.Lean.Omega.tidyConstraint, _root_.Lean.Omega.tidyCoeffs, _root_.Lean.Omega.tidy, _root_.Lean.Omega.tidy?]
  split
  · split
    · exact w
    · rename_i hn
      rcases _root_.Lean.Omega.normalize?_eq_some hn with ⟨rfl, rfl⟩
      exact Lean.Omega.normalize_sat w
  · rename_i hp
    rcases _root_.Lean.Omega.positivize?_eq_some hp with ⟨rfl, rfl⟩
    exact Lean.Omega.normalize_sat (_root_.Lean.Omega.positivize_sat w)

private theorem cons_eq {a b : Int} {as bs : List Int} (h : a = b) (t : as = bs) :
    a :: as = b :: bs := (congrArg (· :: as) h).trans (congrArg (b :: ·) t)

public theorem Lean.Omega.IntList.nil_add : type_of% @_root_.Lean.Omega.IntList.nil_add := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact cons_eq (Int.zero_add x) ih

public theorem Lean.Omega.IntList.add_nil : type_of% @_root_.Lean.Omega.IntList.add_nil := by
  intro xs
  rw [_root_.Lean.Omega.IntList.add_def, List.zipWithAll_nil]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact cons_eq (Int.add_zero x) ih

public theorem Lean.Omega.IntList.mul_distrib_left :
    type_of% @_root_.Lean.Omega.IntList.mul_distrib_left := by
  intro xs ys zs
  induction xs generalizing ys zs with
  | nil => rw [Lean.Omega.IntList.nil_add, IntList.mul_nil_left, Lean.Omega.IntList.nil_add]
  | cons x xs ih =>
    cases ys with
    | nil => rw [Lean.Omega.IntList.add_nil, IntList.mul_nil_left, Lean.Omega.IntList.add_nil]
    | cons y ys =>
      cases zs with
      | nil => rw [IntList.mul_nil_right, IntList.mul_nil_right, IntList.mul_nil_right, Lean.Omega.IntList.nil_add]
      | cons z zs =>
        rw [IntList.cons_add_cons, IntList.mul_cons_cons, IntList.mul_cons_cons, IntList.mul_cons_cons,
          IntList.cons_add_cons]
        exact cons_eq (Int.add_mul ..) (ih ys zs)

public theorem Lean.Omega.IntList.sum_add : type_of% @_root_.Lean.Omega.IntList.sum_add := by
  intro xs ys
  induction xs generalizing ys with
  | nil => rw [Lean.Omega.IntList.nil_add, IntList.sum_nil, Int.zero_add]
  | cons x xs ih =>
    cases ys with
    | nil => rw [Lean.Omega.IntList.add_nil, IntList.sum_nil, Int.add_zero]
    | cons y ys =>
      rw [IntList.cons_add_cons, IntList.sum_cons, IntList.sum_cons, IntList.sum_cons, ih,
        Int.add_assoc, Int.add_assoc, Int.add_left_comm y]

private theorem map_coeffs (f g : Int → Int) (h : ∀ i, f i = g i) (xs : List Int) :
    xs.map f = xs.map g :=
  xs.recOn rfl (fun x _ ih => cons_eq (h x) ih)

public theorem Lean.Omega.IntList.combo_eq_smul_add_smul :
    type_of% @_root_.Lean.Omega.IntList.combo_eq_smul_add_smul := by
  intro a xs b ys
  induction xs generalizing ys with
  | nil =>
    rw [IntList.smul_nil, Lean.Omega.IntList.nil_add]
    exact map_coeffs (fun y => a * 0 + b * y) (fun y => b * y)
      (fun y => (congrArg (· + b * y) (Int.mul_zero a)).trans (Int.zero_add _)) ys
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [IntList.smul_nil, Lean.Omega.IntList.add_nil]
      exact map_coeffs (fun x => a * x + b * 0) (fun x => a * x)
        (fun x => (congrArg (a * x + ·) (Int.mul_zero b)).trans (Int.add_zero _)) (x :: xs)
    | cons y ys =>
      exact congrArg ((a * x + b * y) :: ·) (ih ys)

public theorem Lean.Omega.Constraint.translate_sat : type_of% @_root_.Lean.Omega.Constraint.translate_sat := by
  intro t c v w
  have a : c.lowerBound.sat v ∧ c.upperBound.sat v := of_decide_eq_true w
  apply decide_eq_true
  constructor
  · exact all_map (· + t) (fun x => decide (x ≤ v)) (fun x => decide (x ≤ v + t))
      (fun _ hx => decide_eq_true (Int.add_le_add_right (of_decide_eq_true hx) t)) _ a.1
  · exact all_map (· + t) (fun x => decide (v ≤ x)) (fun x => decide (v + t ≤ x))
      (fun _ hx => decide_eq_true (Int.add_le_add_right (of_decide_eq_true hx) t)) _ a.2

public theorem Lean.Omega.Constraint.exact_sat : type_of% @_root_.Lean.Omega.Constraint.exact_sat := by
  intro r t
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have pair : decide (r ≤ t) = true ∧ decide (t ≤ r) = true := of_decide_eq_true h
    exact decide_eq_true (Int.le_antisymm (of_decide_eq_true pair.1) (of_decide_eq_true pair.2))
  · intro h
    have eq : r = t := of_decide_eq_true h
    subst t
    exact decide_eq_true ⟨decide_eq_true (Int.le_refl _), decide_eq_true (Int.le_refl _)⟩

public theorem Lean.Omega.Constraint.addInequality_sat :
    type_of% @_root_.Lean.Omega.Constraint.addInequality_sat := by
  intro c x y w
  apply decide_eq_true
  constructor
  · apply decide_eq_true
    rw [← Int.zero_sub c]
    exact Int.sub_left_le_of_le_add w
  · rfl

public theorem Lean.Omega.Constraint.addEquality_sat :
    type_of% @_root_.Lean.Omega.Constraint.addEquality_sat := by
  intro c x y w
  have eq : -(c : Int) = Coeffs.dot x y := by
    rw [← Int.zero_sub, ← w, Int.add_comm, Int.add_sub_cancel]
  apply decide_eq_true
  exact ⟨decide_eq_true (Int.le_of_eq eq), decide_eq_true (Int.le_of_eq eq.symm)⟩

public theorem Lean.Omega.IntList.sub_eq_add_neg : type_of% @_root_.Lean.Omega.IntList.sub_eq_add_neg := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
    rw [Lean.Omega.IntList.nil_add]
    exact map_coeffs (fun y => 0 - y) Neg.neg Int.zero_sub ys
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [IntList.neg_nil, Lean.Omega.IntList.add_nil]
      have identity : ∀ l : List Int, l.map (fun x => x - 0) = l :=
        fun l => l.recOn rfl (fun a _ step => cons_eq (Int.sub_zero a) step)
      exact identity (x :: xs)
    | cons y ys =>
      exact cons_eq (@Int.sub_eq_add_neg x y) (ih ys)

public theorem Lean.Omega.LinearCombo.sub_eq_add_neg :
    type_of% @_root_.Lean.Omega.LinearCombo.sub_eq_add_neg := by
  intro a b
  apply _root_.Lean.Omega.LinearCombo.ext
  · exact Int.sub_eq_add_neg
  · exact _root_.Lean.Omega.Coeffs.sub_eq_add_neg ..

public theorem Lean.Omega.LinearCombo.sub_eval : type_of% @_root_.Lean.Omega.LinearCombo.sub_eval := by
  intro a b v
  rw [Lean.Omega.LinearCombo.sub_eq_add_neg, _root_.Lean.Omega.LinearCombo.add_eval,
    _root_.Lean.Omega.LinearCombo.neg_eval, Int.sub_eq_add_neg]


private theorem eval_const_of_zero_coeffs (l : LinearCombo) (v : Coeffs) (h : l.coeffs.isZero) :
    l.eval v = l.const := by
  have hz : Coeffs.dot l.coeffs v = 0 := IntList.dot_of_left_zero h
  rw [_root_.Lean.Omega.LinearCombo.eval, hz, Int.add_zero]

private theorem eval_product (a b : LinearCombo) (v : Coeffs) :
    (LinearCombo.mul a b).eval v = b.const * a.eval v + a.const * b.eval v - a.const * b.const := by
  rw [_root_.Lean.Omega.LinearCombo.mul, Lean.Omega.LinearCombo.sub_eval,
    _root_.Lean.Omega.LinearCombo.add_eval, _root_.Lean.Omega.LinearCombo.smul_eval,
    _root_.Lean.Omega.LinearCombo.smul_eval]
  exact congrArg (_ - ·) (Int.add_zero _)

public theorem Lean.Omega.LinearCombo.mul_eval_of_const_left :
    type_of% @_root_.Lean.Omega.LinearCombo.mul_eval_of_const_left := by
  intro a b v h
  rw [eval_product, eval_const_of_zero_coeffs a v h, Int.mul_comm b.const a.const,
    Int.add_comm (a.const * b.const), Int.add_sub_cancel]

public theorem Lean.Omega.LinearCombo.mul_eval_of_const_right :
    type_of% @_root_.Lean.Omega.LinearCombo.mul_eval_of_const_right := by
  intro a b v h
  rw [eval_product, eval_const_of_zero_coeffs b v h, Int.add_sub_cancel, Int.mul_comm]

end OmegaChecks.InitPort.Alternatives
