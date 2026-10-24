/- GID: D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: Restricted replacements preserve assignment weights and visible laws. -/

import D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
import Mathlib.Tactic.FinCases

/-! # Constructive restricted simulation of rational five-mode networks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation

open scoped BigOperators
open RationalZeroRealization RationalPositiveRealization BooleanNullBoundary Matrix

/-- The face equality is imposed on the full table, before assigning a scope. -/
def Restricted (T : Table) : Prop := Strict T ∧
  T.val (false, false, false) * T.val (true, true, false) =
    T.val (true, false, false) * T.val (false, true, false)

noncomputable section
attribute [local instance] Classical.propDecidable

private def activityRaw (t : ℚ) (b : Triple) : ℚ :=
  if A ![b.1, b.2.1, b.2.2] then if b.1 then t else 1 else 0

/-- The complete activity table has allowed entries (1,t,1,t,1)/(3+2t). -/
def activityTable (t : ℚ) (ht : 0 < t) : Table where
  val b := activityRaw t b / (3 + 2 * t)
  nonneg b := by
    apply div_nonneg _ (by positivity)
    unfold activityRaw
    split <;> (try split) <;> positivity
  normalized := by
    rw [← Finset.sum_div]
    have hs : ∑ b, activityRaw t b = 3 + 2 * t := by
      norm_num [activityRaw, Fintype.sum_prod_type, Fintype.sum_bool, A]
      ring
    rw [hs, div_self (ne_of_gt (by positivity : (0 : ℚ) < 3 + 2 * t))]
  supported b hb := by simp [activityRaw, hb]

private theorem pin_restricted : Restricted pinTable := by
  constructor
  · exact RationalPositiveRealization.pin_strict
  · norm_num [pinTable, pinRaw, A]

private theorem activity_restricted (t : ℚ) (ht : 0 < t) :
    Restricted (activityTable t ht) := by
  constructor
  · intro b hb
    change 0 < activityRaw t b / (3 + 2 * t)
    apply div_pos _ (by positivity)
    simp only [activityRaw, ite_eq_left hb]
    split <;> positivity
  · simp [activityTable, activityRaw, A, mul_comm]

private def bitWeight (t : ℚ) (b : Bool) : ℚ := if b then t else 1
private def exclusion (a b : Bool) : ℚ := if a && b then 0 else 1

private inductive Shape where
  | flat | high | low
  deriving DecidableEq

private def edgeProduct (s : Shape) (u v o p q : Bool) : ℚ :=
  match s with
  | .flat => exclusion u o * exclusion v o * exclusion u o
  | .high => exclusion u p * exclusion p v * exclusion v o
  | .low => exclusion u p * exclusion p q * exclusion q v

private def rawPath (s : Shape) (a b : ℚ) (u v p q : Bool) : ℚ :=
  edgeProduct s u v false p q * bitWeight a p * bitWeight b q

private def pathMatrix (s : Shape) (a b : ℚ) (u v : Bool) : ℚ :=
  match s with
  | .flat => (1 + a) * (1 + b)
  | .high => (if u || v then 1 else 1 + a) * (1 + b)
  | .low => if u then (if v then 1 else 1 + b)
      else (if v then 1 + a else 1 + a + b)

private theorem path_sum (s : Shape) (a b : ℚ) (u v : Bool) :
    (∑ p : Bool, ∑ q : Bool, rawPath s a b u v p q) = pathMatrix s a b u v := by
  cases s <;> cases u <;> cases v <;>
    simp [rawPath, edgeProduct, exclusion, bitWeight, pathMatrix, Fintype.sum_bool] <;> ring

private theorem path_pos (s : Shape) (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (u v : Bool) : 0 < pathMatrix s a b u v := by
  cases s <;> cases u <;> cases v <;> simp [pathMatrix] <;> positivity

/-- All data used by the seven-factor binary construction are positive rationals. -/
private structure BinaryData (B : Bool → Bool → ℚ) where
  shape : Shape
  alpha : ℚ
  beta : ℚ
  left : ℚ
  right : ℚ
  scalar : ℚ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  left_pos : 0 < left
  right_pos : 0 < right
  scalar_pos : 0 < scalar
  identity : ∀ u v, bitWeight left u * bitWeight right v *
    pathMatrix shape alpha beta u v = scalar * B u v

private theorem binary_data (B : Bool → Bool → ℚ) (hB : ∀ u v, 0 < B u v) :
    Nonempty (BinaryData B) := by
  let r := B false false * B true true / (B true false * B false true)
  have hr : 0 < r := div_pos (mul_pos (hB _ _) (hB _ _)) (mul_pos (hB _ _) (hB _ _))
  have hrid : B false false * B true true = r * (B true false * B false true) := by
    dsimp [r]; field_simp [ne_of_gt (hB true false), ne_of_gt (hB false true)]
  have hm : ∃ (s : Shape) (a b : ℚ), 0 < a ∧ 0 < b ∧
      pathMatrix s a b false false * pathMatrix s a b true true =
        r * (pathMatrix s a b true false * pathMatrix s a b false true) := by
    rcases lt_trichotomy r 1 with h | h | h
    · refine ⟨.low, 2 / r - 1, 2 * (1 - r) / r, ?_, ?_, ?_⟩
      · apply sub_pos.mpr
        apply (lt_div_iff₀ hr).mpr
        linarith
      · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr h)) hr
      · simp [pathMatrix]
        field_simp [ne_of_gt hr]
        <;> ring
    · refine ⟨.flat, 1, 1, by norm_num, by norm_num, ?_⟩
      simp [pathMatrix, h]
    · refine ⟨.high, r - 1, 1, sub_pos.mpr h, by norm_num, ?_⟩
      simp [pathMatrix]; ring
  obtain ⟨s, a, b, ha, hb, hid⟩ := hm
  let M := pathMatrix s a b
  let c := M false false / B false false
  let l := B true false * M false false / (B false false * M true false)
  let t := B false true * M false false / (B false false * M false true)
  have hp := path_pos s a b ha hb
  have hc : 0 < c := div_pos (hp _ _) (hB _ _)
  have hl : 0 < l := div_pos (mul_pos (hB _ _) (hp _ _)) (mul_pos (hB _ _) (hp _ _))
  have ht : 0 < t := div_pos (mul_pos (hB _ _) (hp _ _)) (mul_pos (hB _ _) (hp _ _))
  refine ⟨⟨s, a, b, l, t, c, ha, hb, hl, ht, hc, ?_⟩⟩
  intro u v
  have hff := ne_of_gt (hB false false)
  have hmf : M true false ≠ 0 := ne_of_gt (hp true false)
  have hmt : M false true ≠ 0 := ne_of_gt (hp false true)
  have hcross : M false false * M true true * B true false * B false true =
      B false false * B true true * (M true false * M false true) := by
    change M false false * M true true = r * (M true false * M false true) at hid
    rw [hid, hrid]
    ring
  change bitWeight l u * bitWeight t v * M u v = c * B u v
  cases u <;> cases v <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
  · change M false false = c * B false false
    dsimp only [c]; field_simp [hff]
  · change t * M false true = c * B false true
    dsimp only [t, c]; field_simp [hff, hmt]
  · change l * M true false = c * B true false
    dsimp only [l, c]; field_simp [hff, hmf]
  · change l * t * M true true = c * B true true
    dsimp only [l, t, c]
    field_simp [hff, hmf, hmt]
    have hh := congrArg (fun z : ℚ => z * M false false) hcross
    nlinarith [hh]

private def edge {V : Type} (u v : V) : Factor V := ⟨(u, u, v), pinTable⟩

private def activity {V : Type} (t : ℚ) (ht : 0 < t) (u o : V) : Factor V :=
  ⟨(u, o, o), activityTable t ht⟩

private abbrev BinaryIndex := Fin 3 ⊕ Fin 4

private def binaryFactors {V : Type} {B : Bool → Bool → ℚ} (d : BinaryData B)
    (u v o p q : V) : BinaryIndex → Factor V
  | .inl i => match d.shape with
    | .flat => ![edge u o, edge v o, edge u o] i
    | .high => ![edge u p, edge p v, edge v o] i
    | .low => ![edge u p, edge p q, edge q v] i
  | .inr i => ![activity d.alpha d.alpha_pos p o,
      activity d.beta d.beta_pos q o, activity d.left d.left_pos u o,
      activity d.right d.right_pos v o] i

private theorem binary_restricted {V : Type} {B : Bool → Bool → ℚ} (d : BinaryData B)
    (u v o p q : V) (i : BinaryIndex) :
    Restricted (binaryFactors d u v o p q i).table := by
  rcases i with i | i
  · cases hs : d.shape <;> fin_cases i <;>
      simpa only [binaryFactors, hs, cons_val_zero', cons_val_succ', edge] using pin_restricted
  · fin_cases i
    · exact activity_restricted _ d.alpha_pos
    · exact activity_restricted _ d.beta_pos
    · exact activity_restricted _ d.left_pos
    · exact activity_restricted _ d.right_pos

private def binaryScale {B : Bool → Bool → ℚ} (d : BinaryData B) : ℚ :=
  1 / (5 ^ 3 * (3 + 2 * d.alpha) * (3 + 2 * d.beta) *
    (3 + 2 * d.left) * (3 + 2 * d.right))

private theorem binaryScale_pos {B : Bool → Bool → ℚ} (d : BinaryData B) :
    0 < binaryScale d := by
  have := d.alpha_pos; have := d.beta_pos; have := d.left_pos; have := d.right_pos
  unfold binaryScale; positivity

private theorem binary_product {V : Type} {B : Bool → Bool → ℚ} (d : BinaryData B)
    (u v o p q : V) (a : V → Bool) (ho : a o = false) :
    (∏ i, (binaryFactors d u v o p q i).value a) =
      binaryScale d * bitWeight d.left (a u) * bitWeight d.right (a v) *
        rawPath d.shape d.alpha d.beta (a u) (a v) (a p) (a q) := by
  cases hs : d.shape <;>
    simp [binaryFactors, Fintype.prod_sum_type, Fin.prod_univ_succ, hs,
      Factor.value, edge, activity, pinTable, pinRaw, activityTable, activityRaw,
      ho, A, binaryScale, rawPath, edgeProduct, exclusion, bitWeight] <;>
    cases a u <;> cases a v <;> cases a p <;> cases a q <;> norm_num <;> ring

private theorem binary_sum {B : Bool → Bool → ℚ} (d : BinaryData B) (u v : Bool) :
    (∑ p : Bool, ∑ q : Bool,
      binaryScale d * bitWeight d.left u * bitWeight d.right v *
        rawPath d.shape d.alpha d.beta u v p q) =
      (binaryScale d * d.scalar) * B u v := by
  simp_rw [← Finset.mul_sum]
  rw [path_sum]
  have hid := d.identity u v
  calc
    _ = binaryScale d * (bitWeight d.left u * bitWeight d.right v *
        pathMatrix d.shape d.alpha d.beta u v) := by ring
    _ = _ := by rw [hid]; ring

private def bottom (T : Table) (u v : Bool) : ℚ := T.val (u, v, false)

private theorem bottom_pos (T : Table) (hT : Strict T) (u v : Bool) :
    0 < bottom T u v := hT _ (by simp [A])

private def data (T : Table) (hT : Strict T) : BinaryData (bottom T) :=
  Classical.choice (binary_data (bottom T) (bottom_pos T hT))

private def topActivity (T : Table) : ℚ :=
  T.val (false, false, true) / T.val (false, false, false)

private theorem topActivity_pos (T : Table) (hT : Strict T) : 0 < topActivity T :=
  div_pos (hT _ (by simp [A])) (hT _ (by simp [A]))

/-- Nine actual ternary factors replace one original ternary factor. -/
abbrev LocalIndex := Unit ⊕ ((Fin 3 ⊕ Fin 4) ⊕ Unit)

/-- The original scope is retained; the last three names are a pin and two fresh bits. -/
def localFactors {V : Type} (T : Table) (hT : Strict T) (x y z o p q : V) :
    LocalIndex → Factor V
  | .inl _ => ⟨(x, y, z), pinTable⟩
  | .inr (.inl i) => binaryFactors (data T hT) x y o p q i
  | .inr (.inr _) => activity (topActivity T) (topActivity_pos T hT) z o

private theorem local_restricted {V : Type} (T : Table) (hT : Strict T)
    (x y z o p q : V) (i : LocalIndex) :
    Restricted (localFactors T hT x y z o p q i).table := by
  rcases i with u | (i | u)
  · exact pin_restricted
  · exact binary_restricted _ _ _ _ _ _ i
  · exact activity_restricted _ (topActivity_pos T hT)

/-- The scalar counts all nine local normalizations, excluding the common pin. -/
def localScale (T : Table) (hT : Strict T) : ℚ :=
  (binaryScale (data T hT) * (data T hT).scalar) /
    (5 * (3 + 2 * topActivity T))

private theorem localScale_pos (T : Table) (hT : Strict T) : 0 < localScale T hT := by
  exact div_pos (mul_pos (binaryScale_pos _) (data T hT).scalar_pos)
    (mul_pos (by norm_num) (by have := topActivity_pos T hT; positivity))

private theorem table_decomposition (T : Table) (hT : Strict T) (x y z : Bool) :
    pinRaw (x, y, z) * bottom T x y * bitWeight (topActivity T) z = T.val (x, y, z) := by
  by_cases h : A ![x, y, z]
  · cases z
    · simp [pinRaw, h, bottom, bitWeight]
    · have hh : x = false ∧ y = false := by
        simpa [A] using h
      rcases hh with ⟨rfl, rfl⟩
      have hn := ne_of_gt (hT (false, false, false) (by simp [A]))
      simp [pinRaw, A, bottom, bitWeight, topActivity]
      field_simp [hn]
  · rw [T.supported _ h]
    simp [pinRaw, h]

private theorem local_product {V : Type} (T : Table) (hT : Strict T)
    (x y z o p q : V) (a : V → Bool) (ho : a o = false) :
    (∏ i, (localFactors T hT x y z o p q i).value a) =
      (pinRaw (a x, a y, a z) / 5) *
        (binaryScale (data T hT) * bitWeight (data T hT).left (a x) *
          bitWeight (data T hT).right (a y) *
          rawPath (data T hT).shape (data T hT).alpha (data T hT).beta
            (a x) (a y) (a p) (a q)) *
        (bitWeight (topActivity T) (a z) / (3 + 2 * topActivity T)) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton, localFactors]
  rw [binary_product _ _ _ _ _ _ a ho]
  simp [Factor.value, pinTable, activity, activityTable, activityRaw, ho, A, bitWeight]
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;> simp [hx, hy, hz] <;> ring

private theorem sum_bits (f : (Bool → Bool) → ℚ) :
    (∑ h, f h) = ∑ p : Bool, ∑ q : Bool, f (fun b => if b then q else p) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem local_hidden_sum (T : Table) (hT : Strict T) (x y z : Bool) :
    (∑ p : Bool, ∑ q : Bool,
      pinRaw (x, y, z) / 5 *
        (binaryScale (data T hT) * bitWeight (data T hT).left x *
          bitWeight (data T hT).right y *
          rawPath (data T hT).shape (data T hT).alpha (data T hT).beta x y p q) *
        (bitWeight (topActivity T) z / (3 + 2 * topActivity T))) =
      localScale T hT * T.val (x, y, z) := by
  have hs := binary_sum (data T hT) x y
  calc
    _ = (pinRaw (x, y, z) / 5) *
        (∑ p : Bool, ∑ q : Bool,
          binaryScale (data T hT) * bitWeight (data T hT).left x *
            bitWeight (data T hT).right y *
            rawPath (data T hT).shape (data T hT).alpha (data T hT).beta x y p q) *
        (bitWeight (topActivity T) z / (3 + 2 * topActivity T)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      rw [hs, ← table_decomposition T hT x y z]
      simp only [localScale, div_eq_mul_inv, _root_.mul_inv_rev]
      ring


private def localWeight (T : Table) (hT : Strict T) (x y z o : Bool)
    (h : Bool → Bool) : ℚ :=
  ∏ i, (localFactors T hT x y z o (h false) (h true) i).value id

private theorem local_eval {V : Type} (T : Table) (hT : Strict T)
    (x y z o p q : V) (a : V → Bool) :
    (∏ i, (localFactors T hT x y z o p q i).value a) =
      localWeight T hT (a x) (a y) (a z) (a o) (fun b => if b then a q else a p) := by
  unfold localWeight
  apply Finset.prod_congr rfl
  intro i _
  rcases i with u | (i | u)
  · rfl
  · rcases i with i | i
    · cases hs : (data T hT).shape <;> fin_cases i <;>
        simp [localFactors, binaryFactors, hs, edge, Factor.value]
    · fin_cases i <;> simp [localFactors, binaryFactors, activity, Factor.value]
  · rfl

private theorem localWeight_sum (T : Table) (hT : Strict T) (x y z : Bool) :
    (∑ h : Bool → Bool, localWeight T hT x y z false h) =
      localScale T hT * T.val (x, y, z) := by
  rw [sum_bits]
  simp only [localWeight, Bool.false_eq_true, ↓reduceIte]
  simp_rw [local_product T hT x y z false _ _ id rfl]
  exact local_hidden_sum T hT x y z

/-- A local replacement keeps every original variable, even those outside the factor scope. -/
def localExtension {V : Type} (f : Factor V) (hf : Strict f.table) :
    LocalIndex → Factor (V ⊕ (Unit ⊕ Bool)) :=
  localFactors f.table hf (.inl f.scope.1) (.inl f.scope.2.1) (.inl f.scope.2.2)
    (.inr (.inl ())) (.inr (.inr false)) (.inr (.inr true))

/-- The complete hidden sum is pointwise in every assignment of actual original variables. -/
theorem local_simulation {V : Type} (f : Factor V) (hf : Strict f.table) :
    (∀ i, Restricted (localExtension f hf i).table) ∧
    0 < localScale f.table hf ∧
    ∀ b : V → Bool,
      (∑ h : Bool → Bool, ∏ i,
        (localExtension f hf i).value
          (Sum.elim b (Sum.elim (fun _ : Unit => false) h))) =
        localScale f.table hf * f.value b := by
  refine ⟨fun i => local_restricted _ _ _ _ _ _ _ _ i, localScale_pos _ _, ?_⟩
  intro b
  simp only [localExtension]
  simp_rw [local_eval]
  have he (h : Bool → Bool) : (fun b => if b then h true else h false) = h := by
    funext b; cases b <;> simp
  simp only [Sum.elim_inl, Sum.elim_inr, he]
  exact localWeight_sum f.table hf (b f.scope.1) (b f.scope.2.1) (b f.scope.2.2)

/-- Old hidden names, one shared pin, and two private bits for every old factor. -/
abbrev ReplacementHidden (m k : Nat) := Fin m ⊕ (Unit ⊕ (Fin k × Bool))

/-- The single pin is a separate factor, including when the old factor set is empty. -/
abbrev ReplacementIndex (k : Nat) := Unit ⊕ (Fin k × LocalIndex)

/-- Original visible labels are unchanged, and original hidden labels remain distinct. -/
def originalEmbedding {n m k : Nat} :
    (Fin n ⊕ Fin m) → (Fin n ⊕ ReplacementHidden m k) :=
  Sum.map id Sum.inl

private def commonPin {n m k : Nat} : Fin n ⊕ ReplacementHidden m k :=
  .inr (.inr (.inl ()))

private def privateBit {n m k : Nat} (j : Fin k) (b : Bool) :
    Fin n ⊕ ReplacementHidden m k := .inr (.inr (.inr (j, b)))

/-- A concrete finite family of restricted ternary factors. -/
def replacementFamily {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) :
    ReplacementIndex k → Factor (Fin n ⊕ ReplacementHidden m k)
  | .inl _ => ⟨(commonPin, commonPin, commonPin), pinTable⟩
  | .inr (j, i) => localFactors (net.factor j).table (hs j)
      (originalEmbedding (net.factor j).scope.1)
      (originalEmbedding (net.factor j).scope.2.1)
      (originalEmbedding (net.factor j).scope.2.2)
      commonPin (privateBit j false) (privateBit j true) i

/-- The canonical numbering changes no visible label. -/
def replacement {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) :
    Network n (Fintype.card (ReplacementHidden m k)) (Fintype.card (ReplacementIndex k)) :=
  numberedNetwork (replacementFamily net hs)

/-- Complete assignments extend every old variable and assign every fresh variable. -/
def extendAssignment {n m k : Nat} (b : Fin n ⊕ Fin m → Bool)
    (h : Unit ⊕ (Fin k × Bool) → Bool) : Fin n ⊕ ReplacementHidden m k → Bool :=
  Sum.elim (fun i => b (.inl i)) (Sum.elim (fun i => b (.inr i)) h)

/-- The total positive scalar includes the one shared pin exactly once. -/
def replacementScale {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) : ℚ :=
  (1 / 5) * ∏ j, localScale (net.factor j).table (hs j)

private theorem replacementScale_pos {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) : 0 < replacementScale net hs :=
  mul_pos (by norm_num) (Finset.prod_pos fun j _ => localScale_pos _ _)

private theorem replacementFamily_restricted {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (i : ReplacementIndex k) :
    Restricted (replacementFamily net hs i).table := by
  rcases i with u | ⟨j, i⟩
  · exact pin_restricted
  · exact local_restricted _ _ _ _ _ _ _ _ i

private theorem extend_original {n m k : Nat} (b : Fin n ⊕ Fin m → Bool)
    (h : Unit ⊕ (Fin k × Bool) → Bool) (v : Fin n ⊕ Fin m) :
    extendAssignment b h (originalEmbedding v) = b v := by cases v <;> rfl

private theorem family_product {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (b : Fin n ⊕ Fin m → Bool)
    (o : Bool) (h : Fin k → Bool → Bool) :
    (∏ i, (replacementFamily net hs i).value
      (extendAssignment b (Sum.elim (fun _ : Unit => o) (Function.uncurry h)))) =
    (pinRaw (o, o, o) / 5) * ∏ j,
      localWeight (net.factor j).table (hs j)
        (b (net.factor j).scope.1) (b (net.factor j).scope.2.1)
        (b (net.factor j).scope.2.2) o (h j) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [replacementFamily]
  rw [local_eval]
  have he (v : Fin n ⊕ Fin m) := extend_original b
    (Sum.elim (fun _ : Unit => o) (Function.uncurry h)) v
  dsimp only [extendAssignment] at he
  simp only [extendAssignment, commonPin, privateBit,
    Sum.elim_inl, Sum.elim_inr, Function.uncurry_apply_pair]
  congr 1 <;> first
    | exact he _
    | (funext v; cases v <;> simp)

private theorem sum_fresh {k : Nat} (f : (Unit ⊕ (Fin k × Bool) → Bool) → ℚ) :
    (∑ h, f h) = ∑ o : Bool, ∑ h : Fin k → Bool → Bool,
      f (Sum.elim (fun _ : Unit => o) (Function.uncurry h)) := by
  let E := (Equiv.sumArrowEquivProdArrow Unit (Fin k × Bool) Bool).trans
    (Equiv.prodCongr (Equiv.funUnique Unit Bool) (Equiv.curry (Fin k) Bool Bool))
  rw [← E.symm.sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem fixed_assignment {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (b : Fin n ⊕ Fin m → Bool) :
    (∑ h : Unit ⊕ (Fin k × Bool) → Bool, ∏ i,
      (replacementFamily net hs i).value (extendAssignment b h)) =
      replacementScale net hs * ∏ j, (net.factor j).value b := by
  rw [sum_fresh]
  simp_rw [family_product]
  have hp0 : pinRaw (false, false, false) / 5 = (1 / 5 : ℚ) := by
    norm_num [pinRaw, A]
  have hp1 : pinRaw (true, true, true) / 5 = (0 : ℚ) := by norm_num [pinRaw, A]
  rw [Fintype.sum_bool]
  simp only [hp0, hp1, zero_mul, Finset.sum_const_zero, zero_add]
  rw [← Finset.mul_sum, ← Fintype.prod_sum]
  simp_rw [localWeight_sum]
  rw [Finset.prod_mul_distrib]
  simp only [replacementScale, Factor.value]
  ring

private theorem replacement_marginal {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (a : Fin n → Bool) :
    (replacement net hs).marginal a = replacementScale net hs * net.marginal a := by
  rw [replacement, numbered_marginal]
  let E := Equiv.sumArrowEquivProdArrow (Fin m) (Unit ⊕ (Fin k × Bool)) Bool
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  change (∑ h : Fin m → Bool, ∑ t : Unit ⊕ (Fin k × Bool) → Bool,
    ∏ i, (replacementFamily net hs i).value (extendAssignment (Sum.elim a h) t)) = _
  simp_rw [fixed_assignment]
  rw [← Finset.mul_sum]
  rfl

/-- Every old actual variable has a distinct name in the numbered replacement. -/
def numberedEmbedding {n m k : Nat} :
    (Fin n ⊕ Fin m) → (Fin n ⊕ Fin (Fintype.card (ReplacementHidden m k))) :=
  Sum.map id (fun i => Fintype.equivFin (ReplacementHidden m k) (.inl i))

/-- A fixed old assignment and fresh assignment induce an assignment of the actual output network. -/
def numberedAssignment {n m k : Nat} (b : Fin n ⊕ Fin m → Bool)
    (h : Unit ⊕ (Fin k × Bool) → Bool) :
    Fin n ⊕ Fin (Fintype.card (ReplacementHidden m k)) → Bool :=
  extendAssignment b h ∘ Sum.map id (Fintype.equivFin (ReplacementHidden m k)).symm

private theorem numbered_product {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (b : Fin n ⊕ Fin m → Bool)
    (h : Unit ⊕ (Fin k × Bool) → Bool) :
    (∏ i, ((replacement net hs).factor i).value (numberedAssignment b h)) =
      ∏ i, (replacementFamily net hs i).value (extendAssignment b h) := by
  let eh := Fintype.equivFin (ReplacementHidden m k)
  let ej := Fintype.equivFin (ReplacementIndex k)
  have hv : numberedAssignment b h ∘ Sum.map id eh = extendAssignment b h := by
    funext v
    cases v <;> simp [numberedAssignment, Function.comp_def, eh]
  change (∏ i, (replacementFamily net hs (ej.symm i)).value
    (numberedAssignment b h ∘ Sum.map id eh)) = _
  rw [hv]
  exact ej.symm.prod_comp (fun i =>
    (replacementFamily net hs i).value (extendAssignment b h))

private theorem numberedEmbedding_injective {n m k : Nat} :
    Function.Injective (numberedEmbedding (n := n) (m := m) (k := k)) := by
  intro u v h
  cases u <;> cases v <;> simp only [numberedEmbedding, Sum.map_inl, Sum.map_inr,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, id_eq] at h
  · exact congrArg Sum.inl h
  · exact congrArg Sum.inr (Sum.inl.inj ((Fintype.equivFin _).injective h))

private theorem numbered_original {n m k : Nat} (b : Fin n ⊕ Fin m → Bool)
    (h : Unit ⊕ (Fin k × Bool) → Bool) (v : Fin n ⊕ Fin m) :
    numberedAssignment b h (numberedEmbedding v) = b v := by
  cases v <;> simp [numberedAssignment, numberedEmbedding, extendAssignment]

private theorem original_scope {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) (j : Fin k) :
    ((replacement net hs).factor
      (Fintype.equivFin (ReplacementIndex k) (.inr (j, .inl ())))).scope =
      (numberedEmbedding (net.factor j).scope.1,
        numberedEmbedding (net.factor j).scope.2.1,
        numberedEmbedding (net.factor j).scope.2.2) := by
  unfold replacement numberedNetwork
  simp only [Equiv.symm_apply_apply]
  let eh := Fintype.equivFin (ReplacementHidden m k)
  have he (v : Fin n ⊕ Fin m) : Sum.map id eh (originalEmbedding v) =
      numberedEmbedding v := by cases v <;> rfl
  change (Sum.map id eh (originalEmbedding (net.factor j).scope.1),
    Sum.map id eh (originalEmbedding (net.factor j).scope.2.1),
    Sum.map id eh (originalEmbedding (net.factor j).scope.2.2)) = _
  simp only [he]

/-- The finite replacement preserves old names, complete weights, partitions and visible laws. -/
theorem result (n m k : Nat) (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) :
    Function.Injective (numberedEmbedding (n := n) (m := m) (k := k)) ∧
    (∀ i : Fin n, numberedEmbedding (m := m) (k := k) (.inl i) = .inl i) ∧
    (∀ (b : Fin n ⊕ Fin m → Bool) (h : Unit ⊕ (Fin k × Bool) → Bool)
      (v : Fin n ⊕ Fin m), numberedAssignment b h (numberedEmbedding v) = b v) ∧
    (∀ j : Fin k, ((replacement net hs).factor
      (Fintype.equivFin (ReplacementIndex k) (.inr (j, .inl ())))).scope =
      (numberedEmbedding (net.factor j).scope.1,
        numberedEmbedding (net.factor j).scope.2.1,
        numberedEmbedding (net.factor j).scope.2.2)) ∧
    (∀ i, Restricted ((replacement net hs).factor i).table) ∧
    0 < replacementScale net hs ∧
    (∀ b : Fin n ⊕ Fin m → Bool,
      (∑ h : Unit ⊕ (Fin k × Bool) → Bool, ∏ i,
        ((replacement net hs).factor i).value (numberedAssignment b h)) =
        replacementScale net hs * ∏ j, (net.factor j).value b) ∧
    0 < net.partition ∧ 0 < (replacement net hs).partition ∧
    (∀ a, (replacement net hs).marginal a = replacementScale net hs * net.marginal a) ∧
    (replacement net hs).partition = replacementScale net hs * net.partition ∧
    (∀ a, (replacement net hs).law a = net.law a) := by
  have hC := replacementScale_pos net hs
  have hZ : 0 < net.partition := (RationalPositiveRealization.necessity net hs).1
  have hp : (replacement net hs).partition = replacementScale net hs * net.partition := by
    unfold Network.partition
    simp_rw [replacement_marginal]
    rw [← Finset.mul_sum]
  refine ⟨numberedEmbedding_injective, (fun _ => rfl), numbered_original,
    original_scope net hs, ?_, hC, ?_, hZ, ?_, replacement_marginal net hs, hp, ?_⟩
  · intro i
    change Restricted (replacementFamily net hs
      ((Fintype.equivFin (ReplacementIndex k)).symm i)).table
    exact replacementFamily_restricted _ _ _
  · intro b
    simp_rw [numbered_product]
    exact fixed_assignment net hs b
  · rw [hp]; exact mul_pos hC hZ
  · intro a
    rw [Network.law, Network.law, replacement_marginal, hp]
    exact mul_div_mul_left _ _ (ne_of_gt hC)

#print axioms local_simulation
#print axioms result

end
end D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation
