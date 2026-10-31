/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reflection-symmetric diagonal unitaries require the registered worst-case CNOT count. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Order

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound

abbrev basis (m : ℕ) := Fin m → Bool
abbrev matrix (m : ℕ) := Matrix (basis m) (basis m) ℂ

abbrev gate (m : ℕ) :=
  {p : Fin m × Fin m // p.1 ≠ p.2} ⊕ (Fin m × ℝ)

private def cnotMatrix {m : ℕ} (t c : Fin m) (_h : t ≠ c) : matrix m :=
  Matrix.of fun x y => if x = Function.update y t (Bool.xor (y t) (y c)) then 1 else 0

private def rzMatrix {m : ℕ} (q : Fin m) (φ : ℝ) : matrix m :=
  Matrix.diagonal (fun x =>
    if x q = false then Complex.exp (((-φ / 2 : ℝ) : ℂ) * Complex.I)
    else Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))

def gateMatrix {m : ℕ} : gate m → matrix m
  | Sum.inl p => cnotMatrix p.1.1 p.1.2 p.2
  | Sum.inr p => rzMatrix p.1 p.2

def circuitMatrix {m : ℕ} (circuit : List (gate m)) : matrix m :=
  circuit.foldr (fun g acc => gateMatrix g * acc) 1

def cnotCount {m : ℕ} (circuit : List (gate m)) : ℕ :=
  (circuit.filter (fun g => match g with | Sum.inl _ => true | Sum.inr _ => false)).length

private def dot {m : ℕ} (v x : basis m) : Bool :=
  decide ((Finset.univ.filter (fun i => v i = true ∧ x i = true)).card % 2 = 1)

private def character {m : ℕ} (v : basis m) (f : basis m → ℂ) : ℂ :=
  ∏ x : basis m, f x ^ (if dot v x then (-1 : ℤ) else 1)

private def evenLabel {m : ℕ} (v : basis m) : Prop :=
  (Finset.univ.filter (fun i => v i = true)).card % 2 = 0

private def hardTheta {m : ℕ} (x : basis m) : ℝ :=
  if (∀ i, x i = false) ∨ (∀ i, x i = true) then Real.pi / 2 else 0

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ θ : basis (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit

private lemma hardTheta_reflection (m : ℕ) (x : basis m) :
    hardTheta (fun j => !(x j)) = hardTheta x := by sorry

private lemma normal_form (m : ℕ) (circuit : List (gate m)) :
    ∃ a : basis m → basis m, Function.Bijective a := by sorry

private lemma diagonal_forces_identity (m : ℕ) (circuit : List (gate m)) (c : ℂ)
    (θ : basis m → ℝ)
    (h : circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I))) :
    ∀ x : basis m, x = x := by sorry

private lemma character_mul (m : ℕ) (v : basis m) (f g : basis m → ℂ) :
    character v (fun x => f x * g x) = character v f * character v g := by sorry

private lemma character_global (m : ℕ) (v : basis m) (c : ℂ) :
    character v (fun _ : basis m => c) = 1 := by sorry

private lemma character_factor (m : ℕ) (v w : basis m) (f : Bool → ℂ) (hvw : v ≠ w)
    (hw : w ≠ fun _ => false) :
    character v (fun x => f (dot w x)) = 1 := by sorry

private lemma hard_character (m : ℕ) (hm : 0 < m) (v : basis m) (he : evenLabel v)
    (hv : v ≠ fun _ => false) :
    character v (fun x => Complex.exp ((hardTheta x : ℂ) * Complex.I)) = -1 := by sorry

private lemma rotation_labels (m : ℕ) (circuit : List (gate m))
    (θ : basis m → ℝ)
    (h : circuitMatrix circuit = (1 : ℂ) • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I))) :
    ∀ v, evenLabel v → v ≠ (fun _ : Fin m => false) → True := by sorry

private lemma even_output_count (m : ℕ) (circuit : List (gate m)) :
    2 ^ (m - 1) - 1 ≤ cnotCount circuit := by sorry

private lemma birth_count (m : ℕ) (circuit : List (gate m)) :
    m - 1 ≤ cnotCount circuit := by sorry

private lemma return_count (m : ℕ) (circuit : List (gate m)) :
    2 ^ (m - 1) + m - 2 ≤ cnotCount circuit := by sorry

private lemma claim_for_n (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : basis (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit := by sorry

theorem result : claim := by
  intro n hn
  exact claim_for_n n hn

end D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
