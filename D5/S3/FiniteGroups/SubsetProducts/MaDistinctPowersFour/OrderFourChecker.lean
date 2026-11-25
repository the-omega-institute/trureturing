/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part17.certificate318
   digest: Sound checking of equality branches for arbitrary order-four arrays. -/

/- Escape audit unfinished for 3 supporting theorems. See https://github.com/the-omega-institute/trureturing/issues/32494. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.LatinCore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

namespace MaLatin.OrderFourChecker

universe u

abbrev Position := Fin 4 × Fin 4
abbrev Partition := Vector Nat 16

def initial : Partition := Vector.ofFn Fin.val

def symbol (partition : Partition) (p : Position) : Nat :=
  partition[(finProdFinEquiv p).val]'(finProdFinEquiv p).isLt

def value {α : Type*} (A : Fin 4 → Fin 4 → α) (p : Position) : α := A p.1 p.2

/-- The partition records equalities that are already forced in the array. -/
def Realizes {α : Type*} (A : Fin 4 → Fin 4 → α) (partition : Partition) : Prop :=
  ∀ p q, symbol partition p = symbol partition q → value A p = value A q

theorem realizes_initial {α : Type*} (A : Fin 4 → Fin 4 → α) : Realizes A initial := by
  intro p q h
  have heq : (finProdFinEquiv p).val = (finProdFinEquiv q).val := by
    simpa only [symbol, initial, Vector.getElem_ofFn] using h
  exact congrArg (value A) (finProdFinEquiv.injective (Fin.val_injective heq))

/-- Force two symbols to agree by replacing all occurrences of the second with the first. -/
def merge (partition : Partition) (p q : Position) : Partition :=
  partition.map fun a => if a = symbol partition q then symbol partition p else a

private theorem realizes_merge {α : Type*} {A : Fin 4 → Fin 4 → α} {partition : Partition}
    (h : Realizes A partition) {p q : Position} (hpq : value A p = value A q) :
    Realizes A (merge partition p q) := by
  intro x y heq
  simp only [symbol, merge, Vector.getElem_map] at heq
  change (if symbol partition x = symbol partition q then symbol partition p else symbol partition x) =
    (if symbol partition y = symbol partition q then symbol partition p else symbol partition y) at heq
  by_cases hx : symbol partition x = symbol partition q <;>
    by_cases hy : symbol partition y = symbol partition q <;> simp only [hx, hy, ite_true, ite_false] at heq
  · exact (h x q hx).trans (h y q hy).symm
  · exact (h x q hx).trans (hpq.symm.trans (h p y heq))
  · exact (h x p heq).trans (hpq.trans (h y q hy).symm)
  · exact h x y heq

private theorem latin_clash {α : Type*} {A : Fin 4 → Fin 4 → α} {p q : Position}
    (h : Latin A) (hneq : p ≠ q) (hline : p.1 = q.1 ∨ p.2 = q.2)
    (heq : value A p = value A q) : False := by
  unfold value at heq
  rcases hline with hr | hc
  · rw [← hr] at heq
    exact hneq (Prod.ext hr (h.1 p.1 heq))
  · rw [← hc] at heq
    exact hneq (Prod.ext (h.2 p.2 heq) hc)

private theorem collision {α : Type*} {A : Fin 4 → Fin 4 → α} (h : ¬ Rainbow A)
    (p : Fin 4 → Fin 4) (hp : Function.Injective p) :
    (A 0 (p 0) = A 1 (p 1)) ∨ (A 0 (p 0) = A 2 (p 2)) ∨
    (A 0 (p 0) = A 3 (p 3)) ∨ (A 1 (p 1) = A 2 (p 2)) ∨
    (A 1 (p 1) = A 3 (p 3)) ∨ (A 2 (p 2) = A 3 (p 3)) := by
  classical
  by_contra hn
  push Not at hn
  rcases hn with ⟨h01, h02, h03, h12, h13, h23⟩
  apply h
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp), ?_⟩
  change Function.Injective (fun i => A i (p i))
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    fin_cases i <;> fin_cases j <;> first
    | exact h01 hij | exact h02 hij | exact h03 hij | exact h12 hij | exact h13 hij | exact h23 hij
    | exact (by decide : ¬ (_ < _)) hlt
  · exact heq
  · exfalso
    have hji := hij.symm
    fin_cases i <;> fin_cases j <;> first
    | exact h01 hji | exact h02 hji | exact h03 hji | exact h12 hji | exact h13 hji | exact h23 hji
    | exact (by decide : ¬ (_ < _)) hgt

/-- Every array that realizes this partition and has no rainbow transversal has an obstruction. -/
def Closed (partition : Partition) : Prop :=
  ∀ {α : Type u} (A : Fin 4 → Fin 4 → α), Latin A → ¬ Rainbow A → Realizes A partition →
    EqualColumns A ∨ Motif A

def Known : List Partition → Prop
  | [] => True
  | p :: ps => Closed.{u} p ∧ Known ps

theorem known_of_mem {ps : List Partition} (h : Known.{u} ps)
    {p : Partition} (hp : p ∈ ps) : Closed.{u} p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact ih h.2 hp

inductive Certificate where
  | clash (p q : Position)
  | columns
  | transversal (p : Fin 4 → Fin 4) (on01 on02 on03 on12 on13 on23 : Certificate)
  | motif (r₀ r₁ r₂ c₀ c₁ c₂ : Fin 4) (onEq : Certificate)
  | reuse (index : Nat)

def check (known : List Partition) (partition : Partition) : Certificate → Bool
  | .clash p q =>
      decide (p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2) ∧ symbol partition p = symbol partition q)
  | .columns =>
      allFin (n := 4) fun c => allFin fun d => allFin fun r =>
        anyFin fun s => decide (symbol partition (r, c) = symbol partition (s, d))
  | .transversal p on01 on02 on03 on12 on13 on23 =>
      injectiveB p &&
        (check known (merge partition (0, p 0) (1, p 1)) on01 &&
         check known (merge partition (0, p 0) (2, p 2)) on02 &&
         check known (merge partition (0, p 0) (3, p 3)) on03 &&
         check known (merge partition (1, p 1) (2, p 2)) on12 &&
         check known (merge partition (1, p 1) (3, p 3)) on13 &&
         check known (merge partition (2, p 2) (3, p 3)) on23)
  | .motif r₀ r₁ r₂ c₀ c₁ c₂ onEq =>
      decide (r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₁ ≠ r₂ ∧ c₀ ≠ c₁ ∧ c₀ ≠ c₂ ∧ c₁ ≠ c₂ ∧
        symbol partition (r₁, c₀) = symbol partition (r₀, c₁) ∧
        symbol partition (r₁, c₁) = symbol partition (r₀, c₂) ∧
        symbol partition (r₁, c₂) = symbol partition (r₀, c₀) ∧
        symbol partition (r₂, c₀) = symbol partition (r₀, c₂)) &&
        check known (merge partition (r₂, c₂) (r₀, c₁)) onEq
  | .reuse i => decide (known[i]? = some partition)

theorem sound {known : List Partition} (hknown : Known.{u} known) {partition : Partition}
    {certificate : Certificate} (hcheck : check known partition certificate = true) :
    Closed.{u} partition := by
  induction certificate generalizing partition with
  | clash p q =>
    intro α A hlatin _ hrealizes
    simp only [check, decide_eq_true_eq] at hcheck
    exact (latin_clash hlatin hcheck.1 hcheck.2.1 (hrealizes p q hcheck.2.2)).elim
  | columns =>
    intro α A _ _ hrealizes
    simp only [check, allFin_true, anyFin_true, decide_eq_true_eq] at hcheck
    left
    intro c d r
    obtain ⟨s, hs⟩ := hcheck c d r
    exact ⟨s, hrealizes (r, c) (s, d) hs⟩
  | transversal p c01 c02 c03 c12 c13 c23 ih01 ih02 ih03 ih12 ih13 ih23 =>
    intro α A hlatin hno hrealizes
    simp only [check, Bool.and_eq_true] at hcheck
    rcases hcheck with ⟨hp, ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩⟩
    rcases collision hno p (injective_of_injectiveB hp) with h | h | h | h | h | h
    · exact ih01 h01 A hlatin hno (realizes_merge hrealizes h)
    · exact ih02 h02 A hlatin hno (realizes_merge hrealizes h)
    · exact ih03 h03 A hlatin hno (realizes_merge hrealizes h)
    · exact ih12 h12 A hlatin hno (realizes_merge hrealizes h)
    · exact ih13 h13 A hlatin hno (realizes_merge hrealizes h)
    · exact ih23 h23 A hlatin hno (realizes_merge hrealizes h)
  | motif r₀ r₁ r₂ c₀ c₁ c₂ onEq ih =>
    intro α A hlatin hno hrealizes
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨hr01, hr02, hr12, hc01, hc02, hc12, he0, he1, he2, he3⟩, heq⟩ := hcheck
    classical
    by_cases h : value A (r₂, c₂) = value A (r₀, c₁)
    · exact ih heq A hlatin hno (realizes_merge hrealizes h)
    · exact Or.inr ⟨r₀, r₁, r₂, c₀, c₁, c₂, hr01, hr02, hr12, hc01, hc02, hc12,
        hrealizes _ _ he0, hrealizes _ _ he1, hrealizes _ _ he2, hrealizes _ _ he3, h⟩
  | reuse index =>
    simp only [check, decide_eq_true_eq] at hcheck
    exact known_of_mem hknown (List.mem_of_getElem? hcheck)

end MaLatin.OrderFourChecker
