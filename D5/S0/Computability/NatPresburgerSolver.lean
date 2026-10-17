/- GID: D5/S0/Computability/NatPresburgerSolver
   generality: G
   mirror-B: D5/B/S0/Computability/NatPresburgerSolver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executable native Nat decisions and constructive finite-tuple solutions. -/

import D5.S0.Computability.NatPresburgerCompiler
import D5.S0.Computability.PresburgerDecision
import Mathlib.Logic.Encodable.Pi

namespace NatPresburger

open FirstOrder Language

/-- Direct execution of the integer supplier on the compiled native formula. -/
def test {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) (xs : Fin n → Nat) : Bool :=
  (compile φ).decideHolds (environment v xs)

theorem test_correct {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) (xs : Fin n → Nat) :
    test φ v xs = true ↔ φ.Realize v xs :=
  (PresburgerArithmetic.Formula.decideHolds_eq_true_iff _ _).trans
    (compile_correct φ v xs)

/-- A computational decision by Bool cases, without a classical decision instance. -/
def realizeDecidable {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) (xs : Fin n → Nat) : Decidable (φ.Realize v xs) :=
  if h : test φ v xs = true then
    .isTrue ((test_correct φ v xs).mp h)
  else
    .isFalse (fun hp => h ((test_correct φ v xs).mpr hp))

private def existsTest {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) : Bool := test φ.exs v Fin.elim0

private theorem exists_test_correct {m n : Nat}
    (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) :
    existsTest φ v = true ↔ ∃ xs : Fin n → Nat, test φ v xs = true := by
  rw [existsTest, test_correct]
  change φ.exs.Realize v ↔ _
  rw [BoundedFormula.realize_exs]
  exact exists_congr (fun xs => (test_correct φ v xs).symm)

/-- Search uses the supplied computable `Encodable.choose`, including dimension zero. -/
def solveBounded {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) : Option (Fin n → Nat) :=
  if h : existsTest φ v = true then
    some (Encodable.choose ((exists_test_correct φ v).mp h))
  else none

theorem solve_bounded_sound {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) (xs : Fin n → Nat)
    (h : solveBounded φ v = some xs) : φ.Realize v xs := by
  unfold solveBounded at h
  split at h
  · next hsat =>
      have heq := Option.some.inj h
      exact (test_correct φ v xs).mp
        (heq ▸ (Encodable.choose_spec ((exists_test_correct φ v).mp hsat)))
  · contradiction

theorem solve_bounded_exists_some_iff {m n : Nat}
    (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) :
    (∃ xs, solveBounded φ v = some xs) ↔ ∃ xs : Fin n → Nat, φ.Realize v xs := by
  constructor
  · rintro ⟨xs, hxs⟩
    exact ⟨xs, solve_bounded_sound φ v xs hxs⟩
  · rintro ⟨xs, hxs⟩
    have hsat := (exists_test_correct φ v).mpr ⟨xs, (test_correct φ v xs).mpr hxs⟩
    simp only [solveBounded, dif_pos hsat]
    exact ⟨_, rfl⟩

theorem solve_bounded_none_iff {m n : Nat}
    (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) :
    solveBounded φ v = none ↔ ¬∃ xs : Fin n → Nat, φ.Realize v xs := by
  rw [← solve_bounded_exists_some_iff]
  cases solveBounded φ v <;> simp

/-- Promote every original free coordinate using native bounded-formula relabeling. -/
def solveAll {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) :
    Option (Fin (m + n) → Nat) :=
  solveBounded (BoundedFormula.relabel (Sum.inr : Fin m → Fin 0 ⊕ Fin m) φ)
    Fin.elim0

theorem solve_all_sound {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (w : Fin (m + n) → Nat) (h : solveAll φ = some w) :
    φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m) := by
  have hw := solve_bounded_sound
    (BoundedFormula.relabel (Sum.inr : Fin m → Fin 0 ⊕ Fin m) φ) Fin.elim0 w h
  simpa only [BoundedFormula.realize_relabel, Function.comp_def, Sum.elim_inr]
    using hw

theorem solve_all_exists_some_iff {m n : Nat}
    (φ : presburger.BoundedFormula (Fin m) n) :
    (∃ w, solveAll φ = some w) ↔
      ∃ w : Fin (m + n) → Nat, φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m) := by
  rw [solveAll, solve_bounded_exists_some_iff]
  apply exists_congr
  intro w
  simpa only [Function.comp_def, Sum.elim_inr]
    using (BoundedFormula.realize_relabel
      (φ := φ) (g := (Sum.inr : Fin m → Fin 0 ⊕ Fin m))
      (v := (Fin.elim0 : Fin 0 → Nat)) (xs := w))

theorem solve_all_none_iff {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) :
    solveAll φ = none ↔
      ¬∃ w : Fin (m + n) → Nat, φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m) := by
  rw [solveAll, solve_bounded_none_iff]
  apply not_congr
  apply exists_congr
  intro w
  simpa only [Function.comp_def, Sum.elim_inr]
    using (BoundedFormula.realize_relabel
      (φ := φ) (g := (Sum.inr : Fin m → Fin 0 ⊕ Fin m))
      (v := (Fin.elim0 : Fin 0 → Nat)) (xs := w))

end NatPresburger
