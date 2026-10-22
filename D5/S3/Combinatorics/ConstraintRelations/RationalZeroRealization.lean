/- GID: D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/RationalZeroRealization
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: Every rational Boolean probability law has a finite five-mode factor representation. -/

import D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact rational five-mode networks with internal zeros -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization

open scoped BigOperators
open BooleanNullBoundary

abbrev Triple := Bool × Bool × Bool

/-- A full rational probability table supported in the five-mode relation. -/
structure Table where
  val : Triple → ℚ
  nonneg : ∀ t, 0 ≤ val t
  normalized : ∑ t, val t = 1
  supported : ∀ t, ¬ A ![t.1, t.2.1, t.2.2] → val t = 0

/-- The scope contains actual variable names, with no literal or constant constructors. -/
structure Factor (V : Type) where
  scope : V × V × V
  table : Table

def Factor.value {V : Type} (f : Factor V) (a : V → Bool) : ℚ :=
  f.table.val (a f.scope.1, a f.scope.2.1, a f.scope.2.2)

/-- Finitely many labelled hidden variables and finitely many ordered ternary factors. -/
structure Network (n m k : Nat) where
  factor : Fin k → Factor (Fin n ⊕ Fin m)

def Network.weight {n m k : Nat} (net : Network n m k)
    (a : Fin n → Bool) (h : Fin m → Bool) : ℚ :=
  ∏ j, (net.factor j).value (Sum.elim a h)

def Network.marginal {n m k : Nat} (net : Network n m k) (a : Fin n → Bool) : ℚ :=
  ∑ h, net.weight a h

def Network.partition {n m k : Nat} (net : Network n m k) : ℚ :=
  ∑ a, net.marginal a

def Network.law {n m k : Nat} (net : Network n m k) (a : Fin n → Bool) : ℚ :=
  net.marginal a / net.partition

noncomputable section

attribute [local instance] Classical.propDecidable

def pinRaw (t : Triple) : ℚ :=
  if A ![t.1, t.2.1, t.2.2] then 1 else 0

private def norRaw (t : Triple) : ℚ :=
  if N ![t.1, t.2.1, t.2.2] then 1 else 0

def unaryRaw (r : ℚ) (t : Triple) : ℚ :=
  if A ![t.1, t.2.1, t.2.2] then if t.1 && t.2.1 then r else 1 else 0

def pinTable : Table where
  val t := pinRaw t / 5
  nonneg t := by unfold pinRaw; split <;> norm_num
  normalized := by
    norm_num [pinRaw, Fintype.sum_prod_type, Fintype.sum_bool, A]
  supported t ht := by simp [pinRaw, ht]

private def norTable : Table where
  val t := norRaw t / 4
  nonneg t := by unfold norRaw; split <;> norm_num
  normalized := by
    norm_num [norRaw, Fintype.sum_prod_type, Fintype.sum_bool, n_iff_nor]
  supported t ht := by
    have hn : ¬ N ![t.1, t.2.1, t.2.2] := fun h => ht h.1
    simp [norRaw, hn]

def unaryTable (r : ℚ) (hr : 0 ≤ r) : Table where
  val t := unaryRaw r t / (4 + r)
  nonneg t := by
    apply div_nonneg _ (by positivity)
    unfold unaryRaw
    split
    · split <;> positivity
    · exact le_refl 0
  normalized := by
    have hd : (4 : ℚ) + r ≠ 0 := ne_of_gt (by positivity)
    rw [← Finset.sum_div]
    have hs : ∑ t, unaryRaw r t = 4 + r := by
      norm_num [unaryRaw, Fintype.sum_prod_type, Fintype.sum_bool, A]
      ring
    rw [hs, div_self hd]
  supported t ht := by simp [unaryRaw, ht]

private inductive Expr (n : Nat) where
  | var : Fin n → Expr n
  | nor : Expr n → Expr n → Expr n
  deriving DecidableEq

private def Expr.eval {n : Nat} (a : Fin n → Bool) : Expr n → Bool
  | .var i => a i
  | .nor x y => !(x.eval a || y.eval a)

private def Expr.neg {n : Nat} (x : Expr n) : Expr n := .nor x x
private def Expr.conj {n : Nat} (x y : Expr n) : Expr n := .nor x.neg y.neg

private def literal {n : Nat} (i : Fin n) (b : Bool) : Expr n :=
  if b then .var i else (Expr.var i).neg

private theorem eval_literal {n : Nat} (a : Fin n → Bool) (i : Fin n) (b : Bool) :
    (literal i b).eval a = true ↔ a i = b := by
  cases b <;> cases hi : a i <;> simp [literal, Expr.eval, Expr.neg, hi]

private def conjunction {n : Nat} (l : List (Expr n)) (seed : Expr n) : Expr n :=
  l.foldr Expr.conj seed

private theorem eval_conjunction {n : Nat} (a : Fin n → Bool)
    (l : List (Expr n)) (seed : Expr n) :
    (conjunction l seed).eval a = true ↔ seed.eval a = true ∧
      ∀ e ∈ l, e.eval a = true := by
  induction l with
  | nil => simp [conjunction]
  | cons e l ih =>
    have hand (x y : Expr n) : (x.conj y).eval a = true ↔
        x.eval a = true ∧ y.eval a = true := by
      cases hx : x.eval a <;> cases hy : y.eval a <;>
        simp [Expr.conj, Expr.neg, Expr.eval, hx, hy]
    simp only [conjunction, List.foldr_cons]
    rw [hand, ← conjunction, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

private def indicator {n : Nat} (hn : 0 < n) (s : Fin n → Bool) : Expr n :=
  conjunction (Finset.univ.toList.map (fun i => literal i (s i)))
    (literal ⟨0, hn⟩ (s ⟨0, hn⟩))

private theorem eval_indicator {n : Nat} (hn : 0 < n) (s a : Fin n → Bool) :
    (indicator hn s).eval a = true ↔ a = s := by
  rw [indicator, eval_conjunction]
  constructor
  · rintro ⟨_, h⟩
    funext i
    exact (eval_literal a i (s i)).mp (h _
      (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩))
  · intro h; subst a
    constructor
    · exact (eval_literal s _ _).mpr rfl
    · intro e he
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      exact (eval_literal s i (s i)).mpr rfl

/-- Only gate expressions are included: visible leaves create no hidden variables. -/
private def Expr.gates {n : Nat} : Expr n → Finset (Expr n)
  | .var _ => ∅
  | .nor x y => insert (.nor x y) (x.gates ∪ y.gates)

private theorem gates_not_var {n : Nat} (e : Expr n) (i : Fin n) :
    Expr.var i ∉ e.gates := by
  induction e with
  | var j => simp [Expr.gates]
  | nor x y hx hy => simp [Expr.gates, hx, hy]

private def allGates {n : Nat} (hn : 0 < n) : Finset (Expr n) :=
  Finset.univ.biUnion (fun s : Fin n → Bool => (indicator hn s).gates)

private theorem indicator_gates {n : Nat} (hn : 0 < n) (s : Fin n → Bool) :
    (indicator hn s).gates ⊆ allGates hn := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, he⟩

private theorem allGates_not_var {n : Nat} (hn : 0 < n) (i : Fin n) :
    Expr.var i ∉ allGates hn := by
  intro h
  obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp h
  exact gates_not_var (indicator hn s) i hs

private abbrev Hidden {n : Nat} (S : Finset (Expr n)) := Unit ⊕ S

private def wire {n : Nat} (S : Finset (Expr n)) : Expr n → Fin n ⊕ Hidden S
  | .var i => .inl i
  | .nor x y => if h : Expr.nor x y ∈ S then .inr (.inr ⟨.nor x y, h⟩)
      else .inr (.inl ())

private def gateScope {n : Nat} (S : Finset (Expr n)) (e : S) :
    (Fin n ⊕ Hidden S) × (Fin n ⊕ Hidden S) × (Fin n ⊕ Hidden S) :=
  match e.val with
  | .var i => (.inl i, .inl i, .inr (.inr e))
  | .nor x y => (wire S x, wire S y, .inr (.inr e))

private def canonicalHidden {n : Nat} (S : Finset (Expr n)) (a : Fin n → Bool) :
    Hidden S → Bool := Sum.elim (fun _ => false) (fun e => e.val.eval a)

private theorem canonical_wire {n : Nat} (S : Finset (Expr n)) (a : Fin n → Bool)
    (e : Expr n) (he : e.gates ⊆ S) :
    Sum.elim a (canonicalHidden S a) (wire S e) = e.eval a := by
  cases e with
  | var i => rfl
  | nor x y =>
    have hmem : Expr.nor x y ∈ S := he (by simp [Expr.gates])
    simp [wire, hmem, canonicalHidden]

private theorem wire_determined {n : Nat} (S : Finset (Expr n))
    (a : Fin n → Bool) (h : Hidden S → Bool)
    (hg : ∀ e : S, N ![Sum.elim a h (gateScope S e).1,
      Sum.elim a h (gateScope S e).2.1, Sum.elim a h (gateScope S e).2.2])
    (e : Expr n) (he : e.gates ⊆ S) :
    Sum.elim a h (wire S e) = e.eval a := by
  induction e with
  | var i => rfl
  | nor x y hx hy =>
    have hm : Expr.nor x y ∈ S := he (by simp [Expr.gates])
    have hxs : x.gates ⊆ S := fun z hz => he (by simp [Expr.gates, hz])
    have hys : y.gates ⊆ S := fun z hz => he (by simp [Expr.gates, hz])
    have hh := (n_iff_nor _ _ _).mp (hg ⟨.nor x y, hm⟩)
    change h (.inr ⟨.nor x y, hm⟩) =
      !(Sum.elim a h (wire S x) || Sum.elim a h (wire S y)) at hh
    rw [hx hxs, hy hys] at hh
    simpa only [wire, dite_eq_left hm, Sum.elim_inr, Expr.eval] using hh

private theorem gates_closed {n : Nat} (e f : Expr n) (hf : f ∈ e.gates) :
    f.gates ⊆ e.gates := by
  induction e with
  | var i => simp [Expr.gates] at hf
  | nor x y hx hy =>
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact fun _ h => h
    · rcases Finset.mem_union.mp hf with hf | hf
      · intro g hg
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hx hf hg))
      · intro g hg
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hy hf hg))

private theorem allGates_closed {n : Nat} (hn : 0 < n)
    (e : Expr n) (he : e ∈ allGates hn) : e.gates ⊆ allGates hn := by
  obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp he
  exact (gates_closed (indicator hn s) e hs).trans (indicator_gates hn s)

private def Consistent {n : Nat} (S : Finset (Expr n)) (a : Fin n → Bool)
    (h : Hidden S → Bool) : Prop :=
  h (.inl ()) = false ∧ ∀ e : S, N ![Sum.elim a h (gateScope S e).1,
    Sum.elim a h (gateScope S e).2.1, Sum.elim a h (gateScope S e).2.2]

private theorem canonical_consistent {n : Nat} (hn : 0 < n) (a : Fin n → Bool) :
    Consistent (allGates hn) a (canonicalHidden (allGates hn) a) := by
  constructor
  · rfl
  · intro e
    obtain ⟨e, he⟩ := e
    cases e with
    | var i => exact False.elim (allGates_not_var hn i he)
    | nor x y =>
      have hc := allGates_closed hn (.nor x y) he
      have hx : x.gates ⊆ allGates hn := fun z hz => hc (by simp [Expr.gates, hz])
      have hy : y.gates ⊆ allGates hn := fun z hz => hc (by simp [Expr.gates, hz])
      apply (n_iff_nor _ _ _).mpr
      change (.nor x y : Expr n).eval a =
        !(Sum.elim a (canonicalHidden (allGates hn) a) (wire (allGates hn) x) ||
          Sum.elim a (canonicalHidden (allGates hn) a) (wire (allGates hn) y))
      rw [canonical_wire _ _ _ hx, canonical_wire _ _ _ hy]
      rfl

private theorem unique_extension {n : Nat} (hn : 0 < n) (a : Fin n → Bool)
    (h : Hidden (allGates hn) → Bool) (hc : Consistent (allGates hn) a h) :
    h = canonicalHidden (allGates hn) a := by
  funext v
  rcases v with u | ⟨e, he⟩
  · cases u; exact hc.1
  · have hh := wire_determined (allGates hn) a h hc.2 e (allGates_closed hn e he)
    cases e with
    | var i => exact False.elim (allGates_not_var hn i he)
    | nor x y =>
      simpa only [wire, dite_eq_left he, Sum.elim_inr, canonicalHidden] using hh

private abbrev FactorIndex {n : Nat} (hn : 0 < n) :=
  Unit ⊕ ((allGates hn) ⊕ (Fin n → Bool))

private def factors {n : Nat} (hn : 0 < n) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) : FactorIndex hn → Factor (Fin n ⊕ Hidden (allGates hn))
  | .inl _ => ⟨(.inr (.inl ()), .inr (.inl ()), .inr (.inl ())), pinTable⟩
  | .inr (.inl e) => ⟨gateScope (allGates hn) e, norTable⟩
  | .inr (.inr s) => ⟨(wire (allGates hn) (indicator hn s),
      wire (allGates hn) (indicator hn s), .inr (.inl ())), unaryTable (P s) (hP s)⟩

private def scalar {n : Nat} (hn : 0 < n) (P : (Fin n → Bool) → ℚ) : ℚ :=
  (1 / 5) * (∏ _e : allGates hn, (1 / 4 : ℚ)) * ∏ s, (1 / (4 + P s))

private theorem scalar_pos {n : Nat} (hn : 0 < n) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) : 0 < scalar hn P := by
  apply mul_pos
  · apply mul_pos (by norm_num)
    apply Finset.prod_pos
    intro e _; norm_num
  · apply Finset.prod_pos
    intro s _; exact one_div_pos.mpr (by have := hP s; positivity)

private theorem unary_repeated (r : ℚ) (hr : 0 ≤ r) (u : Bool) :
    (unaryTable r hr).val (u, u, false) = (1 / (4 + r)) * (if u then r else 1) := by
  cases u <;> simp [unaryTable, unaryRaw, A, div_eq_mul_inv, mul_comm]

private theorem canonical_mass {n : Nat} (hn : 0 < n) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) (a : Fin n → Bool) :
    (∏ j, (factors hn P hP j).value
      (Sum.elim a (canonicalHidden (allGates hn) a))) = scalar hn P * P a := by
  have hc := canonical_consistent hn a
  have hpin (u : Unit) : (factors hn P hP (.inl u)).value
      (Sum.elim a (canonicalHidden (allGates hn) a)) = 1 / 5 := by
    cases u
    norm_num [factors, Factor.value, pinTable, pinRaw, canonicalHidden, A]
  have hgate (e : allGates hn) : (factors hn P hP (.inr (.inl e))).value
      (Sum.elim a (canonicalHidden (allGates hn) a)) = 1 / 4 := by
    dsimp only [factors, Factor.value, norTable, norRaw]
    rw [ite_eq_left (hc.2 e)]
  have hweight (s : Fin n → Bool) : (factors hn P hP (.inr (.inr s))).value
      (Sum.elim a (canonicalHidden (allGates hn) a)) =
        (1 / (4 + P s)) * (if a = s then P s else 1) := by
    change (unaryTable (P s) (hP s)).val
      (Sum.elim a (canonicalHidden (allGates hn) a) (wire (allGates hn) (indicator hn s)),
        Sum.elim a (canonicalHidden (allGates hn) a) (wire (allGates hn) (indicator hn s)),
        false) = _
    rw [canonical_wire _ a _ (indicator_gates hn s), unary_repeated]
    congr 1
    have he := eval_indicator hn s a
    by_cases ha : a = s
    · rw [ite_eq_left ha, ite_eq_left (he.mpr ha)]
    · rw [ite_eq_right ha, ite_eq_right (fun hh => ha (he.mp hh))]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, hpin, hgate, hweight, Finset.prod_mul_distrib]
  have hs : (∏ s : Fin n → Bool, if a = s then P s else 1) = P a := by
    simp
  rw [hs]
  unfold scalar
  ring

private theorem joint_mass {n : Nat} (hn : 0 < n) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) (a : Fin n → Bool) (h : Hidden (allGates hn) → Bool) :
    (∏ j, (factors hn P hP j).value (Sum.elim a h)) =
      if h = canonicalHidden (allGates hn) a then scalar hn P * P a else 0 := by
  by_cases hh : h = canonicalHidden (allGates hn) a
  · subst h
    rw [ite_eq_left rfl]
    exact canonical_mass hn P hP a
  · rw [ite_eq_right hh]
    by_contra hp
    have hall : ∀ j, (factors hn P hP j).value (Sum.elim a h) ≠ 0 := by
      intro j hj
      exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    apply hh
    apply unique_extension hn a h
    constructor
    · have hpin := hall (.inl ())
      cases hv : h (.inl ())
      · rfl
      · exfalso
        apply hpin
        norm_num [factors, Factor.value, pinTable, pinRaw, hv, A]
    · intro e
      by_contra he
      apply hall (.inr (.inl e))
      dsimp only [factors, Factor.value, norTable, norRaw]
      rw [ite_eq_right he, zero_div]

private theorem labelled_marginal {n : Nat} (hn : 0 < n)
    (P : (Fin n → Bool) → ℚ) (hP : ∀ a, 0 ≤ P a) (a : Fin n → Bool) :
    (∑ h, ∏ j, (factors hn P hP j).value (Sum.elim a h)) = scalar hn P * P a := by
  simp only [joint_mass]
  simp

private def renameFactor {V W : Type} (r : V → W) (f : Factor V) : Factor W where
  scope := (r f.scope.1, r f.scope.2.1, r f.scope.2.2)
  table := f.table

def numberedNetwork {n : Nat} {H J : Type} [Fintype H] [DecidableEq H] [Fintype J]
    (f : J → Factor (Fin n ⊕ H)) : Network n (Fintype.card H) (Fintype.card J) where
  factor j := renameFactor (Sum.map id (Fintype.equivFin H))
    (f ((Fintype.equivFin J).symm j))

theorem numbered_marginal {n : Nat} {H J : Type} [Fintype H] [DecidableEq H] [Fintype J]
    (f : J → Factor (Fin n ⊕ H)) (a : Fin n → Bool) :
    (numberedNetwork f).marginal a = ∑ h, ∏ j, (f j).value (Sum.elim a h) := by
  let eh := Fintype.equivFin H
  let ej := Fintype.equivFin J
  let E : (Fin (Fintype.card H) → Bool) ≃ (H → Bool) :=
    Equiv.arrowCongr eh.symm (Equiv.refl Bool)
  have hv (h : Fin (Fintype.card H) → Bool) :
      Sum.elim a h ∘ Sum.map id eh = Sum.elim a (E h) := by
    funext v; cases v <;> rfl
  unfold Network.marginal Network.weight
  change (∑ h, ∏ j, (f (ej.symm j)).value
    (Sum.elim a h ∘ Sum.map id eh)) = _
  simp only [hv]
  calc
    _ = ∑ h : Fin (Fintype.card H) → Bool, ∏ j : J, (f j).value (Sum.elim a (E h)) := by
      apply Finset.sum_congr rfl
      intro h _
      exact ej.symm.prod_comp (fun j => (f j).value (Sum.elim a (E h)))
    _ = _ := E.sum_comp (fun h => ∏ j, (f j).value (Sum.elim a h))

private theorem normalize_numbered {n : Nat} {H J : Type} [Fintype H] [DecidableEq H] [Fintype J]
    (f : J → Factor (Fin n ⊕ H)) (P : (Fin n → Bool) → ℚ) (C : ℚ)
    (hC : 0 < C) (hSum : ∑ a, P a = 1)
    (hMarginal : ∀ a, (∑ h, ∏ j, (f j).value (Sum.elim a h)) = C * P a) :
    ∃ m k : Nat, ∃ net : Network n m k,
      0 < net.partition ∧ ∀ a, net.law a = P a := by
  let net := numberedNetwork f
  have hm (a : Fin n → Bool) : net.marginal a = C * P a :=
    (numbered_marginal f a).trans (hMarginal a)
  have hz : net.partition = C := by
    unfold Network.partition
    simp_rw [hm]
    rw [← Finset.mul_sum, hSum, mul_one]
  refine ⟨_, _, net, ?_, ?_⟩
  · rw [hz]; exact hC
  · intro a
    rw [Network.law, hm, hz, mul_comm, mul_div_cancel_right₀ _ (ne_of_gt hC)]

/-- Every nonnegative rational probability law on a nonempty Boolean cube is exactly
represented by finite, locally normalized five-mode factors. Zeros in the law are allowed. -/
theorem result (n : Nat) (hn : 1 ≤ n) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) (hSum : ∑ a, P a = 1) :
    ∃ m k : Nat, ∃ net : Network n m k,
      0 < net.partition ∧ ∀ a, net.law a = P a := by
  exact normalize_numbered (factors hn P hP) P (scalar hn P)
    (scalar_pos hn P hP) hSum (labelled_marginal hn P hP)

#print axioms result

end
end D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
