/- GID: D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Allowed patterns count the deletion kernel, giving a Tribonacci recurrence on the no-111 chain. -/

import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension

open BinaryDeletionSupport
open Function (update)
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A coordinate is common, or records the row bit at a differing site. -/
abbrev Pattern (V : Type*) := V → Option Bool

private def pattern (x y : V → Bool) : Pattern V :=
  fun i => if x i = y i then none else some (x i)

private def leftWord (p : Pattern V) : V → Bool := fun i => (p i).getD false

private def rightWord (p : Pattern V) : V → Bool :=
  fun i => (p i).map Bool.not |>.getD false

omit [DecidableEq V] in
private theorem pattern_words (p : Pattern V) :
    pattern (leftWord p) (rightWord p) = p := by
  funext i
  cases h : p i with
  | none => simp [pattern, leftWord, rightWord, h]
  | some v => cases v <;> simp [pattern, leftWord, rightWord, h]

omit [DecidableEq V] in
private theorem samePattern_iff {x y u v : V → Bool} :
    SamePattern x y u v ↔ pattern u v = pattern x y := by
  simp only [SamePattern, funext_iff, pattern]
  apply forall_congr'
  intro i
  cases hx : x i <;> cases hy : y i <;> cases hu : u i <;> cases hv : v i <;>
    decide

private theorem pattern_update (u v : V → Bool) (i : V) (b c : Bool) :
    pattern (update u i b) (update v i b) =
      pattern (update u i c) (update v i c) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [pattern]
  · simp [pattern, Function.update_of_ne hji]

/-- A pattern is allowed when every pair of words realizing it is allowed. -/
def AllowedPattern (Allowed : (V → Bool) → Prop) (p : Pattern V) : Prop :=
  ∀ u v, pattern u v = p → Allowed u ∧ Allowed v

/-- Matrices supported on allowed words and invisible to every one-site deletion. -/
def SupportedKernel (Allowed : (V → Bool) → Prop) :
    Submodule ℂ (Matrix (V → Bool) (V → Bool) ℂ) where
  carrier := { R | InDeletionKernel R ∧ ∀ u v, R u v ≠ 0 → Allowed u ∧ Allowed v }
  zero_mem' := by simp [InDeletionKernel]
  add_mem' := by
    rintro R S ⟨hR, hRs⟩ ⟨hS, hSs⟩
    constructor
    · intro i x y
      simp only [Matrix.add_apply]
      rw [add_add_add_comm, hR i x y, hS i x y, add_zero]
    · intro u v h
      by_cases hR : R u v = 0
      · exact hSs u v (by simpa only [Matrix.add_apply, hR, zero_add] using h)
      · exact hRs u v hR
  smul_mem' := by
    rintro c R ⟨hR, hRs⟩
    constructor
    · intro i x y
      simp only [Matrix.smul_apply, smul_eq_mul, ← mul_add, hR i x y, mul_zero]
    · intro u v h
      exact hRs u v fun hz => h (by simp [Matrix.smul_apply, hz])

private def coordinates (Allowed : (V → Bool) → Prop) :
    SupportedKernel Allowed →ₗ[ℂ] ({p // AllowedPattern Allowed p} → ℂ) where
  toFun R p := R.1 (leftWord p) (rightWord p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coordinates_injective [Finite V] (Allowed : (V → Bool) → Prop) :
    Function.Injective (coordinates Allowed) := by
  intro R S hRS
  apply Subtype.ext
  funext u v
  by_contra hneq
  let D := R - S
  have hs : InDeletionKernel D.1 ∧ ∀ x y, D.1 x y ≠ 0 → Allowed x ∧ Allowed y := D.2
  have hnz : D.1 u v ≠ 0 := sub_ne_zero.mpr hneq
  have allowed : AllowedPattern Allowed (pattern u v) :=
    fun x y hp => (survives_iff Allowed u v).mp ⟨D.1, hs.1, hnz, hs.2⟩ x y
      (samePattern_iff.mpr hp)
  let p : {p // AllowedPattern Allowed p} := ⟨pattern u v, allowed⟩
  have hsame : SamePattern u v (leftWord p) (rightWord p) :=
    samePattern_iff.mpr (pattern_words p.1)
  have hzero : D.1 (leftWord p) (rightWord p) = 0 :=
    sub_eq_zero.mpr (congrFun hRS p)
  exact nonzero_on_pattern hs.1 hnz hsame hzero

private theorem coordinate_vector [Finite V] (Allowed : (V → Bool) → Prop)
    (p : {p // AllowedPattern Allowed p}) :
    ∃ R : SupportedKernel Allowed, ∀ q, coordinates Allowed R q = if q.1 = p.1 then 1 else 0 := by
  classical
  have allowed : ∀ u v, SamePattern (leftWord p) (rightWord p) u v → Allowed u ∧ Allowed v :=
    fun u v h => p.2 u v ((samePattern_iff.mp h).trans (pattern_words p.1))
  obtain ⟨R, hR, hnz, hsupp⟩ := (survives_iff Allowed (leftWord p) (rightWord p)).mpr allowed
  let a := R (leftWord p) (rightWord p)
  let S : Matrix (V → Bool) (V → Bool) ℂ :=
    fun u v => if pattern u v = p.1 then a⁻¹ * R u v else 0
  have hS : S ∈ SupportedKernel Allowed := by
    constructor
    · intro i u v
      simp only [S]
      rw [pattern_update u v i false true]
      split
      · rw [← mul_add, hR i u v, mul_zero]
      · simp
    · intro u v huv
      exact hsupp u v fun hz => huv (by simp [S, hz])
  refine ⟨⟨S, hS⟩, fun q => ?_⟩
  change S (leftWord q) (rightWord q) = _
  simp only [S, pattern_words]
  split
  · rename_i h
    rw [h]
    exact inv_mul_cancel₀ hnz
  · rfl

private theorem coordinates_surjective [Finite V] (Allowed : (V → Bool) → Prop) :
    Function.Surjective (coordinates Allowed) := by
  classical
  let := Fintype.ofFinite {p // AllowedPattern Allowed p}
  choose vector eval_vector using coordinate_vector Allowed
  intro f
  refine ⟨∑ p, f p • vector p, ?_⟩
  funext q
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eval_vector,
    ← Subtype.ext_iff]
  simp [mul_ite]

/-- Each allowed pattern contributes one independent complex coordinate. -/
theorem supportedKernel_finrank [Finite V] (Allowed : (V → Bool) → Prop) :
    Module.finrank ℂ (SupportedKernel Allowed) = Nat.card {p // AllowedPattern Allowed p} := by
  classical
  let := Fintype.ofFinite {p // AllowedPattern Allowed p}
  let equiv := LinearEquiv.ofBijective (coordinates Allowed)
    ⟨coordinates_injective Allowed, coordinates_surjective Allowed⟩
  rw [equiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

omit [DecidableEq V] in
theorem allowed_pattern_hyperedges (forbidden : Set (Set V)) (p : Pattern V) :
    AllowedPattern (fun w => ∀ edge ∈ forbidden, ∃ i ∈ edge, w i = false) p ↔
      ∀ edge ∈ forbidden, (∃ i ∈ edge, p i = some false) ∧
        (∃ i ∈ edge, p i = some true) := by
  constructor
  · intro h edge he
    let x : V → Bool := fun i => (p i).getD true
    let y : V → Bool := fun i => ((p i).map Bool.not).getD true
    have hxy : pattern x y = p := by
      funext i
      cases hi : p i with
      | none => simp [pattern, x, y, hi]
      | some a => cases a <;> simp [pattern, x, y, hi]
    obtain ⟨i, hi, hx⟩ := (h x y hxy).1 edge he
    obtain ⟨j, hj, hy⟩ := (h x y hxy).2 edge he
    constructor
    · refine ⟨i, hi, ?_⟩
      cases hpi : p i with
      | none => simp [x, hpi] at hx
      | some a => cases a <;> simp_all [x]
    · refine ⟨j, hj, ?_⟩
      cases hpj : p j with
      | none => simp [y, hpj] at hy
      | some a => cases a <;> simp_all [y]
  · intro h u v huv
    constructor
    · intro edge he
      obtain ⟨i, hi, hs⟩ := (h edge he).1
      refine ⟨i, hi, ?_⟩
      have h' := (congrFun huv i).trans hs
      by_cases heq : u i = v i
      · simp [pattern, heq] at h'
      · simpa [pattern, heq] using h'
    · intro edge he
      obtain ⟨i, hi, hs⟩ := (h edge he).2
      refine ⟨i, hi, ?_⟩
      have h' := (congrFun huv i).trans hs
      by_cases heq : u i = v i
      · simp [pattern, heq] at h'
      · have ht : u i = true := by simpa [pattern, heq] using h'
        cases hv : v i
        · rfl
        · exact (heq (ht.trans hv.symm)).elim


namespace TripleCount

open scoped BigOperators Classical

private abbrev Letter := Option Bool

private def TripleOK (a b c : Letter) : Prop :=
  (a = some false ∨ b = some false ∨ c = some false) ∧
  (a = some true ∨ b = some true ∨ c = some true)

instance (a b c : Letter) : Decidable (TripleOK a b c) := by
  unfold TripleOK
  infer_instance

private def TailValid (a b : Letter) : {k : ℕ} → (Fin k → Letter) → Prop
  | 0, _ => True
  | _ + 1, word => TripleOK a b (word 0) ∧ TailValid b (word 0) (Fin.tail word)

private def tailSplit (a b : Letter) (k : ℕ) :
    {word : Fin (k + 1) → Letter // TailValid a b word} ≃
      Σ c : {c : Letter // TripleOK a b c}, {word : Fin k → Letter // TailValid b c.1 word} where
  toFun word := ⟨⟨word.1 0, word.2.1⟩, ⟨Fin.tail word.1, word.2.2⟩⟩
  invFun := fun ⟨c, word⟩ => ⟨Fin.cons c.1 word.1, by
    simpa [TailValid] using And.intro c.2 word.2⟩
  left_inv word := Subtype.ext (Fin.cons_self_tail word.1)
  right_inv := by
    rintro ⟨c, word⟩
    simp
    cases word
    rfl

private def ways (a b : Letter) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      (if TripleOK a b none then ways b none k else 0) +
      (if TripleOK a b (some false) then ways b (some false) k else 0) +
      (if TripleOK a b (some true) then ways b (some true) k else 0)

private theorem card_tail (k : ℕ) (a b : Letter) :
    Fintype.card {word : Fin k → Letter // TailValid a b word} = ways a b k := by
  induction k generalizing a b with
  | zero =>
    have : Unique {word : Fin 0 → Letter // TailValid a b word} :=
      ⟨⟨⟨Fin.elim0, trivial⟩⟩, fun w => Subtype.ext (funext fun i => i.elim0)⟩
    exact Fintype.card_unique
  | succ k ih =>
    rw [Fintype.card_congr (tailSplit a b k), Fintype.card_sigma]
    simp_rw [ih]
    have hfilter (x : Letter) : x ∈ Finset.univ.filter (TripleOK a b) ↔ TripleOK a b x := by
      simp
    rw [← Finset.sum_subtype _ hfilter (fun x => ways b x k)]
    rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_bool]
    simp [ways, Nat.add_assoc, Nat.add_comm]

private theorem symmetric (k : ℕ) :
    ways none (some true) k = ways none (some false) k ∧
    ways (some true) none k = ways (some false) none k ∧
    ways (some true) (some true) k = ways (some false) (some false) k ∧
    ways (some true) (some false) k = ways (some false) (some true) k := by
  induction k with
  | zero => simp [ways]
  | succ k ih =>
    rcases ih with ⟨h₁, h₂, h₃, h₄⟩
    simp [ways, TripleOK, h₁, h₂, h₃, h₄, Nat.add_right_comm]

private theorem ways_recurrence (a b : Letter) (k : ℕ) :
    ways a b (k + 4) = ways a b (k + 3) + ways a b (k + 2) + ways a b (k + 1) := by
  rcases symmetric k with ⟨h₁, h₂, h₃, h₄⟩
  cases a with
  | none =>
    cases b with
    | none => simp [ways, TripleOK]
    | some b => cases b <;> simp [ways, TripleOK, h₁, h₂, h₃, h₄] <;> omega
  | some a =>
    cases b with
    | none => cases a <;> simp [ways, TripleOK, h₁, h₂, h₃, h₄] <;> omega
    | some b => cases a <;> cases b <;> simp [ways, TripleOK, h₁, h₂, h₃, h₄] <;> omega


private def Valid {k : ℕ} (word : Fin (k + 2) → Letter) : Prop :=
  TailValid (word 0) (Fin.tail word 0) (Fin.tail (Fin.tail word))

private def splitPrefix (k : ℕ) :
    {word : Fin (k + 2) → Letter // Valid word} ≃
      Σ a : Letter, Σ b : Letter, {word : Fin k → Letter // TailValid a b word} where
  toFun word := ⟨word.1 0, Fin.tail word.1 0, Fin.tail (Fin.tail word.1), word.2⟩
  invFun := fun ⟨a, b, word⟩ => ⟨Fin.cons a (Fin.cons b word.1), by
    simpa [Valid] using word.2⟩
  left_inv word := by
    apply Subtype.ext
    simp
  right_inv := by
    rintro ⟨a, b, word⟩
    simp
    cases word
    rfl

private def count (k : ℕ) : ℕ := ∑ a : Letter, ∑ b : Letter, ways a b k

private theorem card_valid (k : ℕ) :
    Fintype.card {word : Fin (k + 2) → Letter // Valid word} = count k := by
  rw [Fintype.card_congr (splitPrefix k), Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, card_tail]
  rfl

private theorem count_recurrence (k : ℕ) :
    count (k + 4) = count (k + 3) + count (k + 2) + count (k + 1) := by
  simp only [count, ways_recurrence, Finset.sum_add_distrib]

private theorem initial_values : count 1 = 12 ∧ count 2 = 24 ∧ count 3 = 44 := by decide


private def WindowOK {k : ℕ} (w : Fin (k + 2) → Letter) : Prop :=
  ∀ i : Fin k, TripleOK
    (w ⟨i, by omega⟩) (w ⟨i.val + 1, by omega⟩) (w ⟨i.val + 2, by omega⟩)

private theorem valid_iff_windows {k : ℕ} (w : Fin (k + 2) → Letter) :
    Valid w ↔ WindowOK w := by
  induction k with
  | zero => simp [Valid, TailValid, WindowOK]
  | succ k ih =>
    have hfirst : Valid w ↔ TripleOK (w 0) (w 1) (w 2) ∧ Valid (Fin.tail w) :=
      Iff.rfl
    rw [hfirst, ih]
    constructor
    · rintro ⟨h0, ht⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · exact ht j
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

end TripleCount

open TripleCount


private def tripleEdge {k : ℕ} (i : Fin k) : Set (Fin (k + 2)) :=
  {j | j.val = i.val ∨ j.val = i.val + 1 ∨ j.val = i.val + 2}

theorem exists_triple_edge {k : ℕ} (i : Fin k) {P : Fin (k + 2) → Prop} :
    (∃ j ∈ tripleEdge i, P j) ↔
      P ⟨i, by omega⟩ ∨ P ⟨i.val + 1, by omega⟩ ∨ P ⟨i.val + 2, by omega⟩ := by
  constructor
  · rintro ⟨j, hj, hp⟩
    change j.val = i.val ∨ j.val = i.val + 1 ∨ j.val = i.val + 2 at hj
    rcases hj with hj | hj | hj
    · left
      have h : j = ⟨i, by omega⟩ := Fin.ext hj
      exact h ▸ hp
    · right
      left
      have h : j = ⟨i.val + 1, by omega⟩ := Fin.ext hj
      exact h ▸ hp
    · right
      right
      have h : j = ⟨i.val + 2, by omega⟩ := Fin.ext hj
      exact h ▸ hp
  · rintro (h | h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h⟩
    · exact ⟨_, Or.inr (Or.inr rfl), h⟩

/-- Allowed words on an open chain of length `k + 2`, with no three consecutive ones. -/
def NoTriple (k : ℕ) (w : Fin (k + 2) → Bool) : Prop :=
  ∀ edge ∈ Set.range (tripleEdge (k := k)), ∃ i ∈ edge, w i = false

private theorem allowed_iff_valid {k : ℕ} (p : Pattern (Fin (k + 2))) :
    AllowedPattern (NoTriple k) p ↔ Valid p := by
  unfold NoTriple
  rw [allowed_pattern_hyperedges, valid_iff_windows]
  constructor
  · intro h i
    obtain ⟨h₀, h₁⟩ := h (tripleEdge i) ⟨i, rfl⟩
    exact ⟨(exists_triple_edge i).mp h₀, (exists_triple_edge i).mp h₁⟩
  · rintro h edge ⟨i, rfl⟩
    exact ⟨(exists_triple_edge i).mpr (h i).1, (exists_triple_edge i).mpr (h i).2⟩

private theorem dimension_eq_count (k : ℕ) :
    Module.finrank ℂ (SupportedKernel (NoTriple k)) = count k := by
  classical
  rw [supportedKernel_finrank, Nat.card_eq_fintype_card, ← card_valid]
  exact Fintype.card_congr (Equiv.subtypeEquivRight allowed_iff_valid)

/-- Starting at chain lengths three, four and five, the kernel dimensions are
12, 24 and 44. Each subsequent dimension is the sum of the previous three. -/
theorem noTriple_finrank (k : ℕ) :
    Module.finrank ℂ (SupportedKernel (NoTriple 1)) = 12 ∧
    Module.finrank ℂ (SupportedKernel (NoTriple 2)) = 24 ∧
    Module.finrank ℂ (SupportedKernel (NoTriple 3)) = 44 ∧
    Module.finrank ℂ (SupportedKernel (NoTriple (k + 4))) =
      Module.finrank ℂ (SupportedKernel (NoTriple (k + 3))) +
        Module.finrank ℂ (SupportedKernel (NoTriple (k + 2))) +
          Module.finrank ℂ (SupportedKernel (NoTriple (k + 1))) := by
  simpa only [dimension_eq_count] using
    And.intro initial_values.1
      (And.intro initial_values.2.1 (And.intro initial_values.2.2 (count_recurrence k)))

end D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
