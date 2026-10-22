/- GID: D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: Strict five-mode networks realize rational laws with loop-graph independent support. -/

import D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Exact rational realization with strictly positive five-mode tables -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization

open scoped BigOperators Topology
open RationalZeroRealization BooleanNullBoundary Matrix

/-- Strict positivity is required at all five allowed entries of the full table. -/
def Strict (T : Table) : Prop := ∀ t, A ![t.1, t.2.1, t.2.2] → 0 < T.val t

/-- A symmetric labelled adjacency relation; diagonal entries are permitted. -/
structure LoopGraph (n : Nat) where
  edge : Fin n → Fin n → Prop
  symm : ∀ ⦃i j⦄, edge i j → edge j i

/-- A loop excludes its own coordinate. -/
def Independent {n : Nat} (K : LoopGraph n) (a : Fin n → Bool) : Prop :=
  ∀ i j, K.edge i j → (a i && a j) = false

/-- Representation uses the canonical full marginal and the canonical normalized law. -/
def Representable {n : Nat} (P : (Fin n → Bool) → ℚ) : Prop :=
  ∃ m k : Nat, ∃ net : Network n m k,
    (∀ j, Strict (net.factor j).table) ∧
    0 < net.partition ∧ ∀ a, net.law a = P a

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem value_nonneg {V : Type} (f : Factor V) (a : V → Bool) :
    0 ≤ f.value a := f.table.nonneg _

private theorem value_pos_iff {V : Type} (f : Factor V) (hf : Strict f.table)
    (a : V → Bool) : 0 < f.value a ↔
      A ![a f.scope.1, a f.scope.2.1, a f.scope.2.2] := by
  constructor
  · intro hp
    by_contra hn
    exact (ne_of_gt hp) (f.table.supported _ hn)
  · intro ha
    exact hf (a f.scope.1, a f.scope.2.1, a f.scope.2.2) ha

private def induced {n m k : Nat} (net : Network n m k) : LoopGraph n where
  edge i l := (∃ j, (net.factor j).scope.2.2 = Sum.inl l ∧
      ((net.factor j).scope.1 = Sum.inl i ∨ (net.factor j).scope.2.1 = Sum.inl i)) ∨
    (∃ j, (net.factor j).scope.2.2 = Sum.inl i ∧
      ((net.factor j).scope.1 = Sum.inl l ∨ (net.factor j).scope.2.1 = Sum.inl l))
  symm := by intro i l h; exact h.symm

private theorem necessity {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table) :
    0 < net.partition ∧ ∀ a, 0 < net.law a ↔ Independent (induced net) a := by
  have hn (a : Fin n → Bool) (h : Fin m → Bool) : 0 ≤ net.weight a h :=
    Finset.prod_nonneg fun j _ => value_nonneg (net.factor j) (Sum.elim a h)
  have hm (a : Fin n → Bool) : 0 ≤ net.marginal a :=
    Finset.sum_nonneg fun h _ => hn a h
  have hw (a : Fin n → Bool) (h : Fin m → Bool) :
      0 < net.weight a h ↔ ∀ j,
        A ![Sum.elim a h (net.factor j).scope.1,
          Sum.elim a h (net.factor j).scope.2.1,
          Sum.elim a h (net.factor j).scope.2.2] := by
    constructor
    · intro hp j
      apply (value_pos_iff _ (hs j) _).mp
      have hz : (net.factor j).value (Sum.elim a h) ≠ 0 := by
        intro hz
        exact (ne_of_gt hp) (Finset.prod_eq_zero (Finset.mem_univ j) hz)
      exact lt_of_le_of_ne (value_nonneg _ _) hz.symm
    · intro hall
      exact Finset.prod_pos fun j _ => (value_pos_iff _ (hs j) _).mpr (hall j)
  have ext (a : Fin n → Bool) : Independent (induced net) a ↔
      ∃ h, 0 < net.weight a h := by
    constructor
    · intro ha
      refine ⟨fun _ => false, (hw a _).mpr ?_⟩
      intro j
      have he (u : Fin n ⊕ Fin m) (hu : u = (net.factor j).scope.1 ∨
          u = (net.factor j).scope.2.1) :
          (Sum.elim a (fun _ => false) u &&
            Sum.elim a (fun _ => false) (net.factor j).scope.2.2) = false := by
        cases u with
        | inr l => simp
        | inl i =>
          cases hz : (net.factor j).scope.2.2 with
          | inr l => simp
          | inl l =>
            apply ha i l
            exact Or.inl ⟨j, hz, hu.imp Eq.symm Eq.symm⟩
      exact ⟨he _ (Or.inl rfl), he _ (Or.inr rfl)⟩
    · rintro ⟨h, hh⟩ i l he
      have hall := (hw a h).mp hh
      have he' (i l : Fin n) (he : ∃ j,
          (net.factor j).scope.2.2 = Sum.inl l ∧
          ((net.factor j).scope.1 = Sum.inl i ∨
            (net.factor j).scope.2.1 = Sum.inl i)) : (a i && a l) = false := by
        obtain ⟨j, hz, hx | hy⟩ := he
        · simpa [A, hz, hx] using (hall j).1
        · simpa [A, hz, hy] using (hall j).2
      change (∃ j, (net.factor j).scope.2.2 = Sum.inl l ∧
        ((net.factor j).scope.1 = Sum.inl i ∨ (net.factor j).scope.2.1 = Sum.inl i)) ∨
        (∃ j, (net.factor j).scope.2.2 = Sum.inl i ∧
        ((net.factor j).scope.1 = Sum.inl l ∨ (net.factor j).scope.2.1 = Sum.inl l)) at he
      rcases he with he | he
      · exact he' i l he
      · simpa [Bool.and_comm] using he' l i he
  have hmp (a : Fin n → Bool) : 0 < net.marginal a ↔ Independent (induced net) a := by
    rw [Network.marginal, Finset.sum_pos_iff_of_nonneg (fun h _ => hn a h)]
    simpa only [Finset.mem_univ, true_and] using (ext a).symm
  have hz : 0 < net.partition := by
    apply lt_of_lt_of_le ((hmp (fun _ => false)).mpr (by intro i j _; rfl))
    exact Finset.single_le_sum (fun a _ => hm a) (Finset.mem_univ _)
  refine ⟨hz, fun a => ?_⟩
  rw [Network.law, div_pos_iff_of_pos_right hz, hmp]

private def kernel {n : Nat} (e : ℚ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun a s => ∏ i, if a i = s i then 1 else e

private theorem kernel_zero (n : Nat) : (kernel (n := n) 0) = (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℚ) := by
  funext a s
  by_cases h : a = s
  · subst s; simp [kernel]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    have hz : kernel 0 a s = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hz, h]

private theorem coefficients {n : Nat} (w : (Fin n → Bool) → ℚ)
    (hw : ∀ a, 0 < w a) :
    ∃ L e : ℚ, ∃ c : (Fin n → Bool) → ℚ,
      0 < L ∧ 0 < e ∧ e < 1 ∧ (∀ s, 0 < c s) ∧
      ∀ a, 1 + ∑ s, c s * kernel e a s = L * w a := by
  let L : ℚ := ∑ a, 2 / w a
  have hL : 0 < L := Finset.sum_pos (fun a _ => div_pos (by norm_num) (hw a))
    Finset.univ_nonempty
  have hLw (a : Fin n → Bool) : 2 ≤ L * w a := by
    have h : 2 / w a ≤ L := Finset.single_le_sum
      (fun b _ => le_of_lt (div_pos (by norm_num) (hw b))) (Finset.mem_univ a)
    exact (div_le_iff₀ (hw a)).mp h
  let r := fun a => L * w a - 1
  have hr (a : Fin n → Bool) : 0 < r a := by dsimp [r]; have := hLw a; linarith
  have hc : Continuous (fun e : ℚ => (kernel (n := n) e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)) := by
    apply continuous_pi; intro a
    apply continuous_pi; intro s
    unfold kernel
    apply continuous_finsetProd; intro i _
    by_cases hi : a i = s i
    · convert (continuous_const : Continuous (fun _ : ℚ => (1 : ℚ))) using 1
      funext e; simp [hi]
    · convert (continuous_id : Continuous (fun e : ℚ => e)) using 1
      funext e; simp [hi]
  have hdet : Continuous (fun e : ℚ => Matrix.det (kernel (n := n) e)) :=
    hc.matrix_det
  have hzero : Matrix.det (kernel (n := n) 0) ≠ 0 := by rw [kernel_zero]; simp
  have hi : ContinuousAt (fun e : ℚ => (kernel (n := n) e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹) 0 := by
    apply (continuousAt_matrix_inv (kernel (n := n) 0) ?_).comp hc.continuousAt
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hzero)
  have hci (s : Fin n → Bool) :
      ContinuousAt (fun e : ℚ => ((kernel (n := n) e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹ *ᵥ r) s) 0 := by
    change ContinuousAt (fun e : ℚ => ∑ a,
      (kernel (n := n) e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹ s a * r a) 0
    apply tendsto_finsetSum; intro a _
    exact ((continuous_apply a).continuousAt.comp
      ((continuous_apply s).continuousAt.comp hi)).mul continuousAt_const
  have hevent : ∀ᶠ e : ℚ in 𝓝 0,
      Matrix.det (kernel (n := n) e) ≠ 0 ∧
        ∀ s, 0 < ((kernel (n := n) e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹ *ᵥ r) s := by
    filter_upwards [hdet.continuousAt.eventually_ne hzero,
      (Filter.eventually_all.mpr fun s => continuousAt_const.eventually_lt (hci s)
        (by simpa [kernel_zero] using hr s))] with e hd hp
    exact ⟨hd, hp⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := Filter.Eventually.exists_Ioo_subset hevent
  obtain ⟨e, he0, heu⟩ := exists_between (lt_min hu (by norm_num : (0 : ℚ) < 1))
  have he := hsub ⟨lt_trans hl he0, lt_of_lt_of_le heu (min_le_left _ _)⟩
  refine ⟨L, e, (kernel e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹ *ᵥ r, hL, he0,
    lt_of_lt_of_le heu (min_le_right _ _), he.2, ?_⟩
  intro a
  have hex := congrFun (congrArg (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℚ => M *ᵥ r)
    (Matrix.mul_nonsing_inv (kernel e) (isUnit_iff_ne_zero.mpr he.1))) a
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hex
  change ∑ s, kernel e a s * ((kernel e : Matrix (Fin n → Bool) (Fin n → Bool) ℚ)⁻¹ *ᵥ r) s = r a at hex
  simp_rw [mul_comm (kernel e a _)] at hex
  rw [hex]
  dsimp [r]; ring

private def binaryRaw (B : Bool → Bool → ℚ) (t : Triple) : ℚ :=
  if A ![t.1, t.2.1, t.2.2] then if t.2.2 then 1 else B t.1 t.2.1 else 0

private def binaryNorm (B : Bool → Bool → ℚ) : ℚ :=
  1 + ∑ x, ∑ y, B x y

private theorem binaryNorm_pos (B : Bool → Bool → ℚ) (hB : ∀ x y, 0 < B x y) :
    0 < binaryNorm B := by
  unfold binaryNorm
  have : 0 ≤ ∑ x, ∑ y, B x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => (hB x y).le
  linarith

private def binaryTable (B : Bool → Bool → ℚ) (hB : ∀ x y, 0 < B x y) : Table where
  val t := binaryRaw B t / binaryNorm B
  nonneg t := by
    apply div_nonneg _ (binaryNorm_pos B hB).le
    unfold binaryRaw
    split
    · split
      · norm_num
      · exact (hB _ _).le
    · exact le_rfl
  normalized := by
    rw [← Finset.sum_div]
    have he : ∑ t, binaryRaw B t = binaryNorm B := by
      norm_num [binaryRaw, binaryNorm, Fintype.sum_prod_type, Fintype.sum_bool, A]
      ring
    rw [he, div_self (ne_of_gt (binaryNorm_pos B hB))]
  supported t ht := by simp [binaryRaw, ht]

private theorem binary_strict (B : Bool → Bool → ℚ) (hB : ∀ x y, 0 < B x y) :
    Strict (binaryTable B hB) := by
  intro t ht
  apply div_pos _ (binaryNorm_pos B hB)
  simp only [binaryRaw, ite_eq_left ht]
  split
  · norm_num
  · exact hB _ _

private theorem pin_strict : Strict pinTable := by
  intro t ht
  norm_num [pinTable, pinRaw, ht]

private theorem unary_strict (c : ℚ) (hc : 0 < c) : Strict (unaryTable c hc.le) := by
  intro t ht
  change 0 < unaryRaw c t / (4 + c)
  apply div_pos _ (by positivity)
  simp only [unaryRaw, ite_eq_left ht]
  split
  · exact hc
  · norm_num

private abbrev Cube (n : Nat) := Fin n → Bool
private abbrev Hidden (n : Nat) := Unit ⊕ Cube n
private abbrev Index (n : Nat) :=
  Unit ⊕ ((Cube n × Cube n) ⊕ (Cube n ⊕ ((Cube n × Fin n) ⊕ (Fin n × Fin n))))

private def pin {n : Nat} : Fin n ⊕ Hidden n := .inr (.inl ())
private def selector {n : Nat} (s : Cube n) : Fin n ⊕ Hidden n := .inr (.inr s)

private def interaction {n : Nat} (e : ℚ) (s : Cube n) (i : Fin n)
    (h b : Bool) : ℚ := if h then if b = s i then 1 else e else 1

private theorem interaction_pos {n : Nat} (e : ℚ) (he : 0 < e)
    (s : Cube n) (i : Fin n) (h b : Bool) : 0 < interaction e s i h b := by
  unfold interaction
  split <;> (try split) <;> first | exact he | norm_num

private def scope {n : Nat} (K : LoopGraph n) : Index n →
    (Fin n ⊕ Hidden n) × (Fin n ⊕ Hidden n) × (Fin n ⊕ Hidden n)
  | .inl _ => (pin, pin, pin)
  | .inr (.inl (s, t)) => if s = t then (pin, pin, pin)
      else (selector s, selector s, selector t)
  | .inr (.inr (.inl s)) => (selector s, selector s, pin)
  | .inr (.inr (.inr (.inl (s, i)))) => (selector s, .inl i, pin)
  | .inr (.inr (.inr (.inr (i, j)))) =>
      if K.edge i j then (.inl i, .inl i, .inl j) else (pin, pin, pin)

private def localTable {n : Nat} (c : Cube n → ℚ) (hc : ∀ s, 0 < c s)
    (e : ℚ) (he : 0 < e) : Index n → Table
  | .inl _ => pinTable
  | .inr (.inl _) => pinTable
  | .inr (.inr (.inl s)) => unaryTable (c s) (hc s).le
  | .inr (.inr (.inr (.inl (s, i)))) =>
      binaryTable (interaction e s i) (interaction_pos e he s i)
  | .inr (.inr (.inr (.inr _))) => pinTable

private def factors {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (j : Index n) :
    Factor (Fin n ⊕ Hidden n) := ⟨scope K j, localTable c hc e he j⟩

private def scale {n : Nat} (c : Cube n → ℚ) (e : ℚ) : Index n → ℚ
  | .inl _ => 1 / 5
  | .inr (.inl _) => 1 / 5
  | .inr (.inr (.inl s)) => 1 / (4 + c s)
  | .inr (.inr (.inr (.inl (s, i)))) => 1 / binaryNorm (interaction e s i)
  | .inr (.inr (.inr (.inr _))) => 1 / 5

private def raw {n : Nat} (c : Cube n → ℚ) (e : ℚ) : Index n → Triple → ℚ
  | .inl _ => pinRaw
  | .inr (.inl _) => pinRaw
  | .inr (.inr (.inl s)) => unaryRaw (c s)
  | .inr (.inr (.inr (.inl (s, i)))) => binaryRaw (interaction e s i)
  | .inr (.inr (.inr (.inr _))) => pinRaw

private theorem factors_strict {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (j : Index n) :
    Strict (factors K c hc e he j).table := by
  rcases j with u | (p | (s | (p | p)))
  · exact pin_strict
  · exact pin_strict
  · exact unary_strict _ (hc s)
  · exact binary_strict _ (interaction_pos e he p.1 p.2)
  · exact pin_strict

private theorem scale_pos {n : Nat} (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (j : Index n) : 0 < scale c e j := by
  rcases j with u | (p | (s | (p | p)))
  · norm_num [scale]
  · norm_num [scale]
  · exact one_div_pos.mpr (by have := hc s; positivity)
  · exact one_div_pos.mpr (binaryNorm_pos _ (interaction_pos e he p.1 p.2))
  · norm_num [scale]

private theorem factor_value {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e)
    (j : Index n) (x : Fin n ⊕ Hidden n → Bool) :
    (factors K c hc e he j).value x = scale c e j *
      raw c e j (x (scope K j).1, x (scope K j).2.1, x (scope K j).2.2) := by
  rcases j with u | (p | (s | (p | p))) <;>
    simp only [factors, Factor.value, localTable, scale, raw,
      pinTable, unaryTable, binaryTable, div_eq_mul_inv, one_mul, mul_comm]

private def chosen {n : Nat} (u : Option (Cube n)) : Hidden n → Bool :=
  Sum.elim (fun _ => false) (fun s => decide (u = some s))

private theorem chosen_injective {n : Nat} : Function.Injective (chosen (n := n)) := by
  intro u v h
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some s =>
      have hh := congrFun h (.inr s)
      simp [chosen] at hh
  | some s =>
    have hh := congrFun h (.inr s)
    have : v = some s := by simpa [chosen] using hh.symm
    exact this.symm

private theorem hidden_of_nonzero {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (a : Cube n) (h : Hidden n → Bool)
    (hw : (∏ j, (factors K c hc e he j).value (Sum.elim a h)) ≠ 0) :
    ∃ u, h = chosen u := by
  have hall (j : Index n) : (factors K c hc e he j).value (Sum.elim a h) ≠ 0 := by
    intro hj; exact hw (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hp : h (.inl ()) = false := by
    cases hh : h (.inl ())
    · rfl
    · have hpin := hall (.inl ())
      simp [factors, Factor.value, localTable, scope, pin, pinTable, pinRaw, hh, A] at hpin
  by_cases hs : ∃ s, h (.inr s) = true
  · obtain ⟨s, hs⟩ := hs
    refine ⟨some s, ?_⟩
    funext v
    rcases v with u | t
    · cases u; simpa [chosen] using hp
    · by_cases ht : t = s
      · subst t; simpa [chosen] using hs
      · have ht' : s ≠ t := Ne.symm ht
        have hpair := hall (.inr (.inl (s, t)))
        have hfalse : h (.inr t) = false := by
          cases hv : h (.inr t)
          · rfl
          · simp [factors, Factor.value, localTable, scope, selector,
              ht', pinTable, pinRaw, hs, hv, A] at hpair
        simpa [chosen, ht'] using hfalse
  · refine ⟨none, ?_⟩
    funext v
    rcases v with u | s
    · cases u; simpa [chosen] using hp
    · have hh : h (.inr s) = false := Bool.eq_false_iff.mpr (fun ht => hs ⟨s, ht⟩)
      simpa [chosen] using hh

private theorem graph_product {n : Nat} (K : LoopGraph n) (a : Cube n) :
    (∏ p : Fin n × Fin n, if K.edge p.1 p.2 then
      (if (a p.1 && a p.2) = false then (1 : ℚ) else 0) else 1) =
        if Independent K a then 1 else 0 := by
  by_cases ha : Independent K a
  · rw [ite_eq_left ha]
    apply Finset.prod_eq_one
    intro p _
    by_cases hp : K.edge p.1 p.2
    · simp [hp, ha _ _ hp]
    · simp [hp]
  · rw [ite_eq_right ha]
    have hbad : ∃ i j, K.edge i j ∧ (a i && a j) ≠ false := by
      simpa only [Independent, not_forall, exists_prop] using ha
    obtain ⟨i, j, he, ha⟩ := hbad
    exact Finset.prod_eq_zero (Finset.mem_univ (i, j)) (by simp [he, ha])

private theorem chosen_mass {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (a : Cube n) (u : Option (Cube n)) :
    (∏ j, (factors K c hc e he j).value (Sum.elim a (chosen u))) =
      (∏ j, scale c e j) * (if Independent K a then 1 else 0) *
        (match u with | none => 1 | some s => c s * kernel e a s) := by
  simp_rw [factor_value]
  rw [Finset.prod_mul_distrib]
  have hp : (∏ j : Index n, raw c e j
      (Sum.elim a (chosen u) (scope K j).1,
        Sum.elim a (chosen u) (scope K j).2.1,
        Sum.elim a (chosen u) (scope K j).2.2)) =
      (if Independent K a then 1 else 0) *
        (match u with | none => 1 | some s => c s * kernel e a s) := by
    have hpin : ∀ v : Unit, raw c e (.inl v)
        (Sum.elim a (chosen u) (scope K (.inl v)).1,
          Sum.elim a (chosen u) (scope K (.inl v)).2.1,
          Sum.elim a (chosen u) (scope K (.inl v)).2.2) = 1 := by
      intro v; cases v; simp [raw, scope, pin, chosen, pinRaw, A]
    have hpair : ∀ p : Cube n × Cube n, raw c e (.inr (.inl p))
        (Sum.elim a (chosen u) (scope K (.inr (.inl p))).1,
          Sum.elim a (chosen u) (scope K (.inr (.inl p))).2.1,
          Sum.elim a (chosen u) (scope K (.inr (.inl p))).2.2) = 1 := by
      rintro ⟨s, t⟩
      by_cases hst : s = t
      · simp [scope, hst, raw, pin, chosen, pinRaw, A]
      · cases u with
        | none => simp [scope, hst, raw, selector, chosen, pinRaw, A]
        | some v =>
          by_cases hvs : v = s
          · subst v; simp [scope, hst, raw, selector, chosen, pinRaw, A]
          · simp [scope, hst, hvs, raw, selector, chosen, pinRaw, A]
    have hedge : ∀ p : Fin n × Fin n, raw c e (.inr (.inr (.inr (.inr p))))
        (Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inr p))))).1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inr p))))).2.1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inr p))))).2.2) =
        if K.edge p.1 p.2 then (if (a p.1 && a p.2) = false then 1 else 0) else 1 := by
      intro p
      by_cases hE : K.edge p.1 p.2
      · simp [raw, scope, hE, pinRaw, A]
      · simp [raw, scope, hE, pin, chosen, pinRaw, A]
    have hunary : ∀ s : Cube n, raw c e (.inr (.inr (.inl s)))
        (Sum.elim a (chosen u) (scope K (.inr (.inr (.inl s)))).1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inl s)))).2.1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inl s)))).2.2) =
        if u = some s then c s else 1 := by
      intro s
      by_cases hu : u = some s <;>
        simp [raw, scope, selector, pin, chosen, unaryRaw, A, hu]
    have hbinary : ∀ p : Cube n × Fin n, raw c e (.inr (.inr (.inr (.inl p))))
        (Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inl p))))).1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inl p))))).2.1,
          Sum.elim a (chosen u) (scope K (.inr (.inr (.inr (.inl p))))).2.2) =
        if u = some p.1 then (if a p.2 = p.1 p.2 then 1 else e) else 1 := by
      intro p
      by_cases hu : u = some p.1 <;>
        simp [raw, scope, selector, pin, chosen, binaryRaw, A, interaction, hu]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp only [hpin, hpair, hunary, hbinary, hedge, Finset.prod_const_one, one_mul]
    rw [graph_product]
    cases u with
    | none => simp
    | some s =>
      simp only [Option.some.injEq]
      have hu : (∏ t : Cube n, if s = t then c t else 1) = c s := by simp
      have hb : (∏ p : Cube n × Fin n,
          if s = p.1 then (if a p.2 = p.1 p.2 then 1 else e) else 1) =
            kernel e a s := by
        rw [Fintype.prod_prod_type]
        simp [kernel]
      rw [hu, hb]
      ring
  rw [hp]; ring

private theorem family_marginal {n : Nat} (K : LoopGraph n) (c : Cube n → ℚ)
    (hc : ∀ s, 0 < c s) (e : ℚ) (he : 0 < e) (a : Cube n) :
    (∑ h, ∏ j, (factors K c hc e he j).value (Sum.elim a h)) =
      (∏ j, scale c e j) * (if Independent K a then 1 else 0) *
        (1 + ∑ s, c s * kernel e a s) := by
  let f := fun h : Hidden n → Bool => ∏ j, (factors K c hc e he j).value (Sum.elim a h)
  have hz (h : Hidden n → Bool) (hh : h ∉ Finset.univ.image chosen) : f h = 0 := by
    by_contra hn
    obtain ⟨u, hu⟩ := hidden_of_nonzero K c hc e he a h hn
    exact hh (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu.symm⟩)
  calc
    _ = ∑ h ∈ Finset.univ.image chosen, f h := by
      exact (Finset.sum_subset (Finset.subset_univ _) (fun h _ hh => hz h hh)).symm
    _ = ∑ u : Option (Cube n), f (chosen u) :=
      Finset.sum_image (fun u _ v _ huv => chosen_injective huv)
    _ = _ := by
      simp only [f, chosen_mass]
      rw [Fintype.sum_option]
      simp only [kernel, mul_add, mul_one, Finset.mul_sum, mul_assoc]

private theorem sufficiency {n : Nat} (P : Cube n → ℚ)
    (hP : ∀ a, 0 ≤ P a) (hSum : ∑ a, P a = 1)
    (K : LoopGraph n) (hK : ∀ a, 0 < P a ↔ Independent K a) : Representable P := by
  let w := fun a => if Independent K a then P a else 1
  have hw (a : Cube n) : 0 < w a := by
    dsimp [w]
    split
    · exact (hK a).mpr ‹_›
    · norm_num
  obtain ⟨L, e, c, hL, he, _, hc, hid⟩ := coefficients w hw
  let f := factors K c hc e he
  let net := numberedNetwork f
  let C : ℚ := ∏ j, scale c e j
  have hC : 0 < C := Finset.prod_pos fun j _ => scale_pos c hc e he j
  have hm (a : Cube n) : net.marginal a = (C * L) * P a := by
    rw [numbered_marginal, family_marginal, hid]
    change C * (if Independent K a then 1 else 0) * (L * w a) = _
    by_cases ha : Independent K a
    · simp only [ite_eq_left ha, w, mul_one]
      ring
    · have hp : P a = 0 := le_antisymm
        (le_of_not_gt (fun hp => ha ((hK a).mp hp))) (hP a)
      simp [ha, hp]
  have hz : net.partition = C * L := by
    unfold Network.partition
    simp_rw [hm]
    rw [← Finset.mul_sum, hSum, mul_one]
  refine ⟨_, _, net, ?_, ?_, ?_⟩
  · intro j
    change Strict (f ((Fintype.equivFin (Index n)).symm j)).table
    exact factors_strict K c hc e he _
  · rw [hz]; exact mul_pos hC hL
  · intro a
    rw [Network.law, hm, hz, mul_comm, mul_div_cancel_right₀ _ (ne_of_gt (mul_pos hC hL))]

/-- All rational masses are included, and the adjacency relation may have loops.
The construction also works for the zero-dimensional cube. -/
theorem result (n : Nat) (P : (Fin n → Bool) → ℚ)
    (hP : ∀ a, 0 ≤ P a) (hSum : ∑ a, P a = 1) :
    (∃ m k : Nat, ∃ net : Network n m k,
      (∀ j, Strict (net.factor j).table) ∧
      0 < net.partition ∧ ∀ a, net.law a = P a) ↔
        ∃ K : LoopGraph n, ∀ a, 0 < P a ↔ Independent K a := by
  constructor
  · rintro ⟨m, k, net, hs, _, hLaw⟩
    refine ⟨induced net, fun a => ?_⟩
    rw [← hLaw a]
    exact (necessity net hs).2 a
  · rintro ⟨K, hK⟩
    exact sufficiency P hP hSum K hK

#print axioms result

end
end D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
