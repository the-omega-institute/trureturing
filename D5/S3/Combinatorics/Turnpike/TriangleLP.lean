/- GID: D5/S3/Combinatorics/Turnpike/TriangleLP
   generality: G
   mirror-B: none(waiver:covered-by-spine-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Numerical triangle marginal relaxations -/

module

public import OmegaBuild.Commands
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

/-! Omega original.
# Numerical triangle marginal relaxations

The ordered addition relation and the marginal constraints are those of
Elder, Marçais and Kingsford, System 11, DOI 10.4230/LIPIcs.WABI.2026.20.
Indices in `Fin n` represent the publication's indices by adding one.
-/
compile_only_with_mathlib
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators
noncomputable section

abbrev Interval (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}
abbrev Triangle (n : ℕ) := {t : Fin n × Fin n × Fin n // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
abbrev Assignment (n d : ℕ) := Interval n → Fin d → ℝ

def Admissible (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ) : Prop :=
  3 ≤ n ∧ 1 ≤ d ∧ StrictAnti y ∧ (∀ q, 0 < y q) ∧
    (∀ q, 0 < μ q) ∧ ∑ q, μ q = n.choose 2

def Relation {d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ) :=
  {r : Fin d × Fin d × Fin d // y r.1 + y r.2.1 = y r.2.2 ∧
    (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1)}

instance {d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ) : Fintype (Relation y μ) :=
  by
    classical
    exact @Subtype.fintype (Fin d × Fin d × Fin d) _ (Classical.decPred _) inferInstance

def first {n : ℕ} (t : Triangle n) : Interval n := ⟨(t.1.1,t.1.2.1),t.2.1⟩
def second {n : ℕ} (t : Triangle n) : Interval n := ⟨(t.1.2.1,t.1.2.2),t.2.2⟩
def outer {n : ℕ} (t : Triangle n) : Interval n :=
  ⟨(t.1.1,t.1.2.2),lt_trans t.2.1 t.2.2⟩

def AssignmentDomain {n d : ℕ} (μ : Fin d → ℕ) (P : Assignment n d) : Prop :=
  (∀ e q, 0 ≤ P e q ∧ P e q ≤ 1) ∧ (∀ e, ∑ q, P e q = 1) ∧
    ∀ q, ∑ e, P e q = (μ q : ℝ)

def Block {n d : ℕ} {y : Fin d → ℝ} {μ : Fin d → ℕ}
    (P : Assignment n d) (τ : Triangle n) (T : Relation y μ → ℝ) : Prop :=
  (∀ r, 0 ≤ T r ∧ T r ≤ 1) ∧ (∑ r, T r = 1) ∧
    (∀ q, ∑ r, (if r.1.1 = q then T r else 0) = P (first τ) q) ∧
    (∀ q, ∑ r, (if r.1.2.1 = q then T r else 0) = P (second τ) q) ∧
    (∀ q, ∑ r, (if r.1.2.2 = q then T r else 0) = P (outer τ) q)

def Projection {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (H : Triangle n → Prop) : Set (Assignment n d) :=
  {P | AssignmentDomain μ P ∧ ∃ T : {τ : Triangle n // H τ} → Relation y μ → ℝ,
    ∀ τ, Block P τ.1 (T τ)}

def full {n : ℕ} : Triangle n → Prop := fun _ => True
def spine {n : ℕ} : Triangle n → Prop := fun τ => τ.1.1.val = 0

def Realizes {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ) (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ (∀ e : Interval n, ∃ q, x e.1.2 - x e.1.1 = y q) ∧
    ∀ q, (Finset.univ.filter fun e : Interval n => x e.1.2 - x e.1.1 = y q).card = μ q

def atom {α : Type*} [DecidableEq α] (a : α) (r : α) : ℝ := if r = a then 1 else 0
def mixture {α : Type*} [DecidableEq α] (a b : α) (r : α) : ℝ :=
  (atom a r + atom b r) / 2

theorem mixture_bounds {α : Type*} [DecidableEq α] (a b r : α) :
    0 ≤ mixture a b r ∧ mixture a b r ≤ 1 := by
  unfold mixture atom
  split_ifs <;> norm_num

theorem mixture_sum {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    ∑ r, mixture a b r = 1 := by
  simp only [mixture, atom]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp

theorem mixture_marginal {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (a b : α) (q : β) :
    (∑ r, if f r = q then mixture a b r else 0) = mixture (f a) (f b) q := by
  classical
  have single : ∀ a : α, (∑ r, if f r = q then atom a r else 0) = atom (f a) q := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp [atom, eq_comm]
    · intro r _ hr
      simp [atom,hr]
    · simp
  calc
    _ = ((∑ r, if f r = q then atom a r else 0) +
      (∑ r, if f r = q then atom b r else 0)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _
        by_cases h : f r = q <;> simp [mixture,h]
    _ = _ := by rw [single,single]; rfl

/-- A union-bound separator for any finite three-coordinate coupling. -/
theorem coupling_separator {α β : Type*} [Fintype α] [DecidableEq β]
    (f g h : α → β) (a b c : β) (T : α → ℝ)
    (nonneg : ∀ r, 0 ≤ T r) (normal : ∑ r, T r = 1)
    (forced : ∀ r, g r = b → h r = c → f r = a) :
    (∑ r, if g r = b then T r else 0) +
    (∑ r, if h r = c then T r else 0) -
    (∑ r, if f r = a then T r else 0) ≤ 1 := by
  have point : ∀ r, (if g r = b then T r else 0) +
      (if h r = c then T r else 0) - (if f r = a then T r else 0) ≤ T r := by
    intro r
    by_cases hg : g r = b <;> by_cases hh : h r = c <;>
      by_cases hf : f r = a <;> simp_all <;> linarith [nonneg r]
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => point r)
  simpa [Finset.sum_sub_distrib, Finset.sum_add_distrib, normal] using hs
end
end Omega.Turnpike
