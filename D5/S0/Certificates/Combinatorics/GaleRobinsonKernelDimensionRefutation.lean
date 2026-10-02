/- GID: D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.claim; result=D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.result; claim=D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.claim
   digest: Six independent kernel elements refute Beluhov Conjecture 3 at type (1,3,6). -/

/-
proof_shape: result: bind-only (explicit polynomial normalization, coefficient
  projections and pinned Mathlib linear-independence and finite-dimension bounds).
escape_witness: none (the certificate identities and coefficient equations are
  local normalization facts; no additional theorem is exported).
admission_basis: open-problem-resolution (#11548; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open MvPolynomial
open scoped BigOperators
namespace D5.S0.Certificates.Combinatorics.GaleRobinsonKernelDimensionRefutation

abbrev Parameters := MvPolynomial (Fin 3) ℚ
abbrev K := FractionRing Parameters
def a : K := algebraMap Parameters K (X 0)
def b : K := algebraMap Parameters K (X 1)
def c : K := algebraMap Parameters K (X 2)
structure GRType where
  n₁ : ℕ
  n₂ : ℕ
  n₃ : ℕ
def order (t : GRType) : ℕ := t.n₁ + t.n₂ + t.n₃
def proper (t : GRType) : Prop :=
  0 < t.n₁ ∧ 0 < t.n₂ ∧ 0 < t.n₃ ∧
  Nat.gcd t.n₁ (Nat.gcd t.n₂ t.n₃) = 1 ∧
  t.n₁ ≠ t.n₂ ∧ t.n₁ ≠ t.n₃ ∧ t.n₂ ≠ t.n₃
-- Every exponent of a degree-n monomial is at most n.
abbrev Exp (n : ℕ) := Fin n → Fin (n + 1)
-- The weights on the displayed integer gauge basis. For odd n, both parity
-- sums are recorded; their sum is the degree condition.
def admissible {n : ℕ} (d : Exp n) : Prop :=
  (∑ i : Fin n, (d i).val) = n ∧
  (∑ i : Fin n, i.val * (d i).val) = n * (n - 1) / 2 ∧
  (n % 2 = 1 →
    (∑ i : Fin n, if i.val % 2 = 0 then (d i).val else 0) = (n + 1) / 2 ∧
    (∑ i : Fin n, if i.val % 2 = 1 then (d i).val else 0) = n / 2)
def upsilon (n : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun d : {d : Exp n // admissible d} =>
    monomial (Finsupp.equivFunOnFinite.symm (fun i => (d.val i).val)) (1 : K))
def x (n i : ℕ) : MvPolynomial (Fin n) K :=
  if h : i < n then X ⟨i,h⟩ else 0
def quadratic (t : GRType) : MvPolynomial (Fin (order t)) K :=
  C a * x (order t) t.n₁ * x (order t) (t.n₂ + t.n₃) +
  C b * x (order t) t.n₂ * x (order t) (t.n₃ + t.n₁) +
  C c * x (order t) t.n₃ * x (order t) (t.n₁ + t.n₂)
def substitution (t : GRType) (i : Fin (order t)) : MvPolynomial (Fin (order t)) K :=
  if h : i.val + 1 < (order t) then x (order t) 0 * X ⟨i.val+1,h⟩
  else quadratic t
def phi (t : GRType) : MvPolynomial (Fin (order t)) K →ₗ[K]
    MvPolynomial (Fin (order t)) K :=
  LinearMap.mulLeft K (x (order t) 0 ^ ((order t) - 2) * quadratic t) -
    (aeval (substitution t)).toLinearMap
-- This intersection is precisely the kernel on the indicated domain subspace.
def omega (t : GRType) : Submodule K (MvPolynomial (Fin (order t)) K) :=
  upsilon (order t) ⊓ LinearMap.ker (phi t)
def claim : Prop := ∀ t : GRType, proper t → Module.finrank K (omega t) = (order t) / 2

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The six independent elements in the type-(1,3,6) kernel rule out dimension five. -/
theorem result : ¬ claim := by
  let target : GRType := ⟨1,3,6⟩
  let exponent {n : ℕ} (d : Exp n) : Fin n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (d i).val)
  let H0 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (1)

  let H1 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![0, 1, 1, 1, 2, 2, 1, 1, 1, 0]) (c ^ 2) + monomial (exponent ![0, 1, 1, 2, 1, 2, 0, 2, 1, 0]) (b * c) +
    monomial (exponent ![0, 1, 2, 0, 2, 1, 2, 1, 1, 0]) (b * c) + monomial (exponent ![0, 1, 2, 1, 1, 1, 1, 2, 1, 0]) (b ^ 2) +
    monomial (exponent ![0, 2, 1, 1, 1, 2, 0, 1, 1, 1]) (a * c) + monomial (exponent ![0, 2, 2, 0, 1, 1, 1, 1, 1, 1]) (a * b) +
    monomial (exponent ![1, 0, 2, 1, 1, 1, 2, 0, 1, 1]) (a * c) + monomial (exponent ![1, 0, 2, 2, 0, 1, 1, 1, 1, 1]) (a * b) +
    monomial (exponent ![1, 1, 0, 2, 1, 1, 1, 2, 0, 1]) (a * c) + monomial (exponent ![1, 1, 0, 2, 2, 0, 1, 1, 1, 1]) (a * b) +
    monomial (exponent ![1, 1, 1, 0, 2, 1, 1, 1, 2, 0]) (a * c) + monomial (exponent ![1, 1, 1, 0, 2, 2, 0, 1, 1, 1]) (a * b) +
    monomial (exponent ![1, 1, 1, 1, 0, 2, 2, 0, 1, 1]) (a * b) + monomial (exponent ![1, 1, 1, 1, 1, 0, 2, 2, 0, 1]) (a * b) +
    monomial (exponent ![1, 1, 1, 1, 1, 1, 0, 2, 2, 0]) (a * b) + monomial (exponent ![1, 1, 1, 1, 2, 0, 1, 1, 0, 2]) (c) +
    monomial (exponent ![1, 1, 1, 2, 0, 1, 1, 0, 2, 1]) (c) + monomial (exponent ![1, 1, 2, 0, 1, 1, 0, 2, 1, 1]) (c) +
    monomial (exponent ![1, 2, 0, 1, 1, 0, 2, 1, 1, 1]) (c) + monomial (exponent ![1, 2, 0, 1, 1, 1, 1, 1, 0, 2]) (b) +
    monomial (exponent ![2, 0, 1, 1, 0, 2, 1, 1, 1, 1]) (c) + monomial (exponent ![2, 0, 1, 1, 1, 1, 1, 0, 2, 1]) (b)

  let H2 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![0, 0, 2, 1, 2, 2, 2, 0, 1, 0]) (a * c ^ 3) + monomial (exponent ![0, 0, 2, 2, 1, 2, 1, 1, 1, 0]) (2 * a * b * c ^ 2) +
    monomial (exponent ![0, 0, 2, 3, 0, 2, 0, 2, 1, 0]) (a * b ^ 2 * c) + monomial (exponent ![0, 0, 3, 0, 2, 1, 3, 0, 1, 0]) (a * b * c ^ 2) +
    monomial (exponent ![0, 0, 3, 1, 1, 1, 2, 1, 1, 0]) (2 * a * b ^ 2 * c) + monomial (exponent ![0, 0, 3, 2, 0, 1, 1, 2, 1, 0]) (a * b ^ 3) +
    monomial (exponent ![0, 1, 0, 2, 2, 2, 1, 2, 0, 0]) (a * c ^ 3) + monomial (exponent ![0, 1, 0, 2, 3, 1, 1, 1, 1, 0]) (a * b * c ^ 2) +
    monomial (exponent ![0, 1, 0, 3, 1, 2, 0, 3, 0, 0]) (a * b * c ^ 2) + monomial (exponent ![0, 1, 0, 3, 2, 1, 0, 2, 1, 0]) (a * b ^ 2 * c) +
    monomial (exponent ![0, 1, 1, 1, 1, 3, 2, 0, 1, 0]) (a * b * c ^ 2) + monomial (exponent ![0, 1, 1, 1, 2, 1, 2, 2, 0, 0]) (2 * a * b * c ^ 2) +
    monomial (exponent ![0, 1, 1, 1, 3, 0, 2, 1, 1, 0]) (a * b ^ 2 * c) + monomial (exponent ![0, 1, 1, 1, 3, 1, 1, 1, 0, 1]) (c ^ 3) +
    monomial (exponent ![0, 1, 1, 2, 0, 3, 1, 1, 1, 0]) (a * b ^ 2 * c) + monomial (exponent ![0, 1, 1, 2, 1, 1, 1, 3, 0, 0]) (2 * a * b ^ 2 * c) +
    monomial (exponent ![0, 1, 1, 2, 1, 2, 1, 0, 2, 0]) (c ^ 3) + monomial (exponent ![0, 1, 1, 2, 2, 0, 1, 2, 1, 0]) (a * b ^ 3) +
    monomial (exponent ![0, 1, 1, 2, 2, 1, 0, 2, 0, 1]) (b * c ^ 2) + monomial (exponent ![0, 1, 1, 3, 0, 2, 0, 1, 2, 0]) (b * c ^ 2) +
    monomial (exponent ![0, 1, 2, 0, 1, 2, 3, 0, 1, 0]) (a * b ^ 2 * c) + monomial (exponent ![0, 1, 2, 0, 2, 0, 3, 2, 0, 0]) (a * b ^ 2 * c) +
    monomial (exponent ![0, 1, 2, 0, 3, 0, 2, 1, 0, 1]) (b * c ^ 2) + monomial (exponent ![0, 1, 2, 1, 0, 2, 2, 1, 1, 0]) (a * b ^ 3) +
    monomial (exponent ![0, 1, 2, 1, 1, 0, 2, 3, 0, 0]) (a * b ^ 3) + monomial (exponent ![0, 1, 2, 1, 1, 1, 2, 0, 2, 0]) (b * c ^ 2) +
    monomial (exponent ![0, 1, 2, 1, 1, 2, 1, 0, 1, 1]) (a ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 2, 1, 2, 0, 1, 2, 0, 1]) (b ^ 2 * c) +
    monomial (exponent ![0, 1, 2, 2, 0, 1, 1, 1, 2, 0]) (b ^ 2 * c) + monomial (exponent ![0, 1, 2, 2, 0, 2, 0, 1, 1, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![0, 1, 3, 0, 1, 1, 2, 0, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![0, 1, 3, 1, 0, 1, 1, 1, 1, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![0, 2, 0, 1, 2, 1, 2, 1, 1, 0]) (c ^ 3) + monomial (exponent ![0, 2, 0, 1, 2, 2, 1, 1, 0, 1]) (b * c ^ 2) +
    monomial (exponent ![0, 2, 0, 2, 1, 1, 1, 2, 1, 0]) (b * c ^ 2) + monomial (exponent ![0, 2, 0, 2, 1, 2, 0, 2, 0, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) +
    monomial (exponent ![0, 2, 0, 2, 2, 1, 0, 1, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![0, 2, 1, 0, 2, 0, 3, 1, 1, 0]) (b * c ^ 2) +
    monomial (exponent ![0, 2, 1, 0, 2, 1, 2, 1, 0, 1]) (b ^ 2 * c) + monomial (exponent ![0, 2, 1, 1, 0, 3, 1, 0, 1, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![0, 2, 1, 1, 1, 0, 2, 2, 1, 0]) (b ^ 2 * c) + monomial (exponent ![0, 2, 1, 1, 1, 1, 1, 2, 0, 1]) (2 * a ^ 2 * b * c + b ^ 3) +
    monomial (exponent ![0, 2, 1, 1, 2, 0, 1, 1, 1, 1]) (a ^ 2 * b ^ 2) + monomial (exponent ![0, 2, 1, 1, 2, 1, 0, 1, 0, 2]) (a * c ^ 2) +
    monomial (exponent ![0, 2, 1, 2, 0, 2, 0, 0, 2, 1]) (a * c ^ 2) + monomial (exponent ![0, 2, 2, 0, 0, 2, 2, 0, 1, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![0, 2, 2, 0, 1, 0, 2, 2, 0, 1]) (a ^ 2 * b ^ 2) + monomial (exponent ![0, 2, 2, 0, 2, 0, 1, 1, 0, 2]) (a * b * c) +
    monomial (exponent ![0, 2, 2, 1, 0, 1, 1, 0, 2, 1]) (a * b * c) + monomial (exponent ![0, 3, 0, 1, 1, 1, 1, 1, 1, 1]) (a * c ^ 2) +
    monomial (exponent ![0, 3, 0, 1, 1, 2, 0, 1, 0, 2]) (a * b * c) + monomial (exponent ![0, 3, 1, 0, 1, 0, 2, 1, 1, 1]) (a * b * c) +
    monomial (exponent ![0, 3, 1, 0, 1, 1, 1, 1, 0, 2]) (a * b ^ 2) + monomial (exponent ![1, 0, 1, 1, 1, 3, 1, 1, 1, 0]) (c ^ 3) +
    monomial (exponent ![1, 0, 1, 1, 2, 2, 1, 0, 2, 0]) (b * c ^ 2) + monomial (exponent ![1, 0, 1, 2, 0, 3, 0, 2, 1, 0]) (b * c ^ 2) +
    monomial (exponent ![1, 0, 1, 2, 1, 1, 2, 1, 0, 1]) (a ^ 2 * c ^ 2) + monomial (exponent ![1, 0, 1, 2, 1, 2, 0, 1, 2, 0]) (b ^ 2 * c) +
    monomial (exponent ![1, 0, 1, 2, 2, 0, 2, 0, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![1, 0, 1, 3, 0, 1, 1, 2, 0, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 0, 1, 3, 1, 0, 1, 1, 1, 1]) (a ^ 2 * b ^ 2) + monomial (exponent ![1, 0, 2, 0, 1, 2, 2, 1, 1, 0]) (b * c ^ 2) +
    monomial (exponent ![1, 0, 2, 0, 2, 1, 2, 0, 2, 0]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![1, 0, 2, 0, 2, 2, 1, 0, 1, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 0, 2, 1, 0, 2, 1, 2, 1, 0]) (b ^ 2 * c) + monomial (exponent ![1, 0, 2, 1, 1, 0, 3, 1, 0, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 0, 2, 1, 1, 1, 1, 1, 2, 0]) (2 * a ^ 2 * b * c + b ^ 3) + monomial (exponent ![1, 0, 2, 1, 1, 2, 0, 1, 1, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 0, 2, 1, 2, 0, 2, 0, 0, 2]) (a * c ^ 2) + monomial (exponent ![1, 0, 2, 2, 0, 0, 2, 2, 0, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 0, 2, 2, 0, 1, 0, 2, 2, 0]) (a ^ 2 * b ^ 2) + monomial (exponent ![1, 0, 2, 2, 1, 0, 1, 1, 0, 2]) (a * b * c) +
    monomial (exponent ![1, 0, 3, 0, 1, 1, 1, 1, 1, 1]) (a * c ^ 2) + monomial (exponent ![1, 0, 3, 1, 0, 1, 0, 2, 1, 1]) (a * b * c) +
    monomial (exponent ![1, 1, 0, 1, 2, 1, 1, 2, 1, 0]) (a ^ 2 * c ^ 2) + monomial (exponent ![1, 1, 0, 1, 2, 2, 0, 2, 0, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 1, 0, 1, 3, 0, 1, 1, 2, 0]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 0, 1, 3, 1, 0, 1, 1, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 0, 2, 0, 2, 2, 1, 0, 1]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 0, 2, 1, 1, 0, 3, 1, 0]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 1, 0, 2, 1, 1, 2, 0, 1, 1]) (a ^ 2 * b ^ 2) + monomial (exponent ![1, 1, 0, 2, 2, 0, 0, 2, 2, 0]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 0, 3, 0, 1, 1, 1, 1, 1]) (a * c ^ 2) + monomial (exponent ![1, 1, 0, 3, 1, 0, 1, 0, 2, 1]) (a * b * c) +
    monomial (exponent ![1, 1, 1, 0, 1, 2, 2, 0, 2, 0]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 1, 0, 1, 3, 1, 0, 1, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 1, 0, 2, 0, 2, 2, 1, 0]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 1, 0, 2, 1, 1, 2, 0, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 1, 0, 3, 0, 1, 1, 1, 1]) (a * c ^ 2) + monomial (exponent ![1, 1, 1, 0, 3, 1, 0, 1, 0, 2]) (a * b * c) +
    monomial (exponent ![1, 1, 1, 1, 0, 1, 3, 1, 0, 1]) (a ^ 2 * b ^ 2) + monomial (exponent ![1, 1, 1, 1, 0, 2, 1, 1, 2, 0]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 1, 1, 0, 3, 0, 1, 1, 1]) (a * c ^ 2) + monomial (exponent ![1, 1, 1, 1, 1, 0, 1, 3, 1, 0]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 1, 1, 1, 1, 0, 3, 0, 1, 1]) (a * c ^ 2) + monomial (exponent ![1, 1, 1, 1, 1, 1, 0, 3, 0, 1]) (a * c ^ 2) +
    monomial (exponent ![1, 1, 1, 1, 1, 1, 1, 0, 3, 0]) (a * c ^ 2) + monomial (exponent ![1, 1, 1, 1, 1, 1, 2, 0, 0, 2]) (2 * a * b * c) +
    monomial (exponent ![1, 1, 1, 1, 1, 2, 0, 0, 2, 1]) (2 * a * b * c) + monomial (exponent ![1, 1, 1, 1, 2, 0, 0, 2, 1, 1]) (2 * a * b * c) +
    monomial (exponent ![1, 1, 1, 2, 0, 0, 2, 1, 1, 1]) (2 * a * b * c) + monomial (exponent ![1, 1, 1, 2, 0, 1, 0, 1, 3, 0]) (a * b * c) +
    monomial (exponent ![1, 1, 1, 2, 0, 1, 1, 1, 0, 2]) (a * b ^ 2) + monomial (exponent ![1, 1, 1, 2, 1, 0, 1, 0, 1, 2]) (c ^ 2) +
    monomial (exponent ![1, 1, 2, 0, 0, 2, 1, 1, 1, 1]) (2 * a * b * c) + monomial (exponent ![1, 1, 2, 0, 1, 0, 1, 3, 0, 1]) (a * b * c) +
    monomial (exponent ![1, 1, 2, 0, 1, 1, 1, 0, 2, 1]) (a * b ^ 2) + monomial (exponent ![1, 1, 2, 0, 2, 0, 0, 2, 0, 2]) (c ^ 2) +
    monomial (exponent ![1, 1, 2, 1, 0, 1, 0, 1, 2, 1]) (c ^ 2) + monomial (exponent ![1, 2, 0, 0, 2, 0, 2, 1, 2, 0]) (a * c ^ 2) +
    monomial (exponent ![1, 2, 0, 0, 2, 1, 1, 1, 1, 1]) (2 * a * b * c) + monomial (exponent ![1, 2, 0, 0, 2, 2, 0, 1, 0, 2]) (a * b ^ 2) +
    monomial (exponent ![1, 2, 0, 1, 0, 1, 3, 0, 1, 1]) (a * b * c) + monomial (exponent ![1, 2, 0, 1, 0, 2, 2, 0, 0, 2]) (a * b ^ 2) +
    monomial (exponent ![1, 2, 0, 1, 1, 0, 1, 2, 2, 0]) (a * b * c) + monomial (exponent ![1, 2, 0, 1, 1, 1, 0, 2, 1, 1]) (a * b ^ 2) +
    monomial (exponent ![1, 2, 0, 2, 0, 0, 2, 0, 2, 1]) (c ^ 2) + monomial (exponent ![1, 2, 0, 2, 0, 1, 1, 0, 1, 2]) (b * c) +
    monomial (exponent ![1, 2, 1, 0, 1, 0, 1, 2, 1, 1]) (c ^ 2) + monomial (exponent ![1, 2, 1, 0, 1, 1, 0, 2, 0, 2]) (b * c) +
    monomial (exponent ![2, 0, 0, 2, 0, 2, 1, 2, 0, 1]) (a * c ^ 2) + monomial (exponent ![2, 0, 0, 2, 1, 1, 1, 1, 1, 1]) (2 * a * b * c) +
    monomial (exponent ![2, 0, 0, 2, 2, 0, 1, 0, 2, 1]) (a * b ^ 2) + monomial (exponent ![2, 0, 1, 0, 1, 2, 1, 1, 2, 0]) (a * c ^ 2) +
    monomial (exponent ![2, 0, 1, 0, 1, 3, 0, 1, 1, 1]) (a * b * c) + monomial (exponent ![2, 0, 1, 0, 2, 1, 1, 0, 3, 0]) (a * b * c) +
    monomial (exponent ![2, 0, 1, 0, 2, 2, 0, 0, 2, 1]) (a * b ^ 2) + monomial (exponent ![2, 0, 1, 1, 0, 1, 2, 2, 0, 1]) (a * b * c) +
    monomial (exponent ![2, 0, 1, 1, 0, 2, 0, 2, 2, 0]) (a * b * c) + monomial (exponent ![2, 0, 1, 1, 1, 0, 2, 1, 1, 1]) (a * b ^ 2) +
    monomial (exponent ![2, 0, 1, 1, 1, 1, 0, 1, 3, 0]) (a * b ^ 2) + monomial (exponent ![2, 0, 1, 1, 1, 1, 1, 1, 0, 2]) (c ^ 2) +
    monomial (exponent ![2, 0, 1, 1, 2, 0, 1, 0, 1, 2]) (b * c) + monomial (exponent ![2, 0, 2, 0, 0, 2, 0, 2, 1, 1]) (c ^ 2) +
    monomial (exponent ![2, 0, 2, 0, 1, 1, 0, 1, 2, 1]) (b * c) + monomial (exponent ![2, 1, 0, 1, 0, 1, 2, 1, 1, 1]) (c ^ 2) +
    monomial (exponent ![2, 1, 0, 1, 0, 2, 1, 1, 0, 2]) (b * c) + monomial (exponent ![2, 1, 0, 1, 1, 0, 2, 0, 2, 1]) (b * c) +
    monomial (exponent ![2, 1, 0, 1, 1, 1, 1, 0, 1, 2]) (b ^ 2)

  let H3 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![0, 0, 1, 2, 2, 2, 2, 1, 0, 0]) (a ^ 2 * c ^ 2) + monomial (exponent ![0, 0, 1, 3, 1, 2, 1, 2, 0, 0]) (a ^ 2 * b * c) +
    monomial (exponent ![0, 0, 2, 1, 2, 1, 3, 1, 0, 0]) (a ^ 2 * b * c) + monomial (exponent ![0, 0, 2, 1, 3, 1, 2, 0, 0, 1]) (a * c ^ 2) +
    monomial (exponent ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0]) (a ^ 2 * b ^ 2) + monomial (exponent ![0, 0, 2, 2, 2, 1, 1, 1, 0, 1]) (a * b * c) +
    monomial (exponent ![0, 1, 1, 1, 2, 2, 2, 0, 0, 1]) (a * b * c) + monomial (exponent ![0, 1, 1, 2, 1, 2, 1, 1, 0, 1]) (a ^ 3 * c + a * b ^ 2) +
    monomial (exponent ![0, 1, 1, 2, 2, 1, 1, 0, 1, 1]) (c ^ 2) + monomial (exponent ![0, 1, 1, 3, 1, 1, 0, 1, 1, 1]) (b * c) +
    monomial (exponent ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1]) (a ^ 3 * b) + monomial (exponent ![0, 1, 2, 1, 2, 1, 1, 0, 0, 2]) (a ^ 2 * c) +
    monomial (exponent ![0, 2, 1, 1, 1, 2, 1, 0, 0, 2]) (a ^ 2 * b) + monomial (exponent ![0, 2, 1, 2, 1, 1, 0, 0, 1, 2]) (a * c) +
    monomial (exponent ![1, 0, 0, 2, 1, 3, 1, 2, 0, 0]) (a * c ^ 2) + monomial (exponent ![1, 0, 0, 2, 2, 2, 1, 1, 1, 0]) (a * b * c) +
    monomial (exponent ![1, 0, 1, 1, 1, 2, 2, 2, 0, 0]) (a * b * c) + monomial (exponent ![1, 0, 1, 1, 2, 1, 2, 1, 1, 0]) (a ^ 3 * c + a * b ^ 2) +
    monomial (exponent ![1, 0, 1, 1, 2, 2, 1, 1, 0, 1]) (c ^ 2) + monomial (exponent ![1, 0, 1, 1, 3, 1, 1, 0, 1, 1]) (b * c) +
    monomial (exponent ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0]) (a ^ 3 * b) + monomial (exponent ![1, 1, 0, 1, 1, 2, 2, 1, 1, 0]) (c ^ 2) +
    monomial (exponent ![1, 1, 0, 1, 1, 3, 1, 1, 0, 1]) (b * c) + monomial (exponent ![1, 1, 1, 0, 1, 1, 3, 1, 1, 0]) (b * c) +
    monomial (exponent ![1, 1, 1, 1, 2, 1, 0, 0, 1, 2]) (a * b) + monomial (exponent ![1, 1, 1, 2, 1, 0, 0, 1, 2, 1]) (a * b) +
    monomial (exponent ![1, 1, 2, 1, 0, 0, 1, 2, 1, 1]) (a * b) + monomial (exponent ![1, 1, 2, 1, 1, 0, 0, 1, 1, 2]) (c) +
    monomial (exponent ![1, 2, 1, 0, 0, 1, 2, 1, 1, 1]) (a * b) + monomial (exponent ![1, 2, 1, 1, 0, 0, 1, 1, 2, 1]) (c) +
    monomial (exponent ![2, 0, 0, 1, 1, 2, 1, 2, 1, 0]) (a ^ 2 * c) + monomial (exponent ![2, 0, 0, 1, 2, 1, 1, 1, 2, 0]) (a ^ 2 * b) +
    monomial (exponent ![2, 1, 0, 0, 1, 1, 2, 1, 2, 0]) (a * c) + monomial (exponent ![2, 1, 0, 0, 1, 2, 1, 1, 1, 1]) (a * b) +
    monomial (exponent ![2, 1, 1, 0, 0, 1, 1, 2, 1, 1]) (c)

  let H4 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![0, 0, 1, 2, 3, 1, 2, 0, 1, 0]) (a ^ 2 * b * c ^ 3) + monomial (exponent ![0, 0, 1, 3, 1, 2, 1, 2, 0, 0]) (a ^ 2 * b * c ^ 3) +
    monomial (exponent ![0, 0, 1, 3, 2, 1, 1, 1, 1, 0]) (a ^ 2 * b ^ 2 * c ^ 2) + monomial (exponent ![0, 0, 1, 4, 0, 2, 0, 3, 0, 0]) (a ^ 2 * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 0, 2, 1, 2, 1, 3, 1, 0, 0]) (a ^ 2 * b * c ^ 3) + monomial (exponent ![0, 0, 2, 1, 3, 0, 3, 0, 1, 0]) (a ^ 2 * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0]) (2 * a ^ 2 * b ^ 2 * c ^ 2) + monomial (exponent ![0, 0, 2, 2, 2, 0, 2, 1, 1, 0]) (a ^ 2 * b ^ 3 * c) +
    monomial (exponent ![0, 0, 2, 2, 2, 1, 1, 1, 0, 1]) (a * b * c ^ 3) + monomial (exponent ![0, 0, 2, 3, 0, 1, 1, 3, 0, 0]) (a ^ 2 * b ^ 3 * c) +
    monomial (exponent ![0, 0, 2, 3, 1, 1, 0, 2, 0, 1]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 0, 3, 0, 2, 0, 4, 1, 0, 0]) (a ^ 2 * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 0, 3, 0, 3, 0, 3, 0, 0, 1]) (a * b * c ^ 3) + monomial (exponent ![0, 0, 3, 1, 1, 0, 3, 2, 0, 0]) (a ^ 2 * b ^ 3 * c) +
    monomial (exponent ![0, 0, 3, 1, 2, 0, 2, 1, 0, 1]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 0, 2, 1, 3, 2, 1, 0, 0]) (a ^ 2 * b * c ^ 3) +
    monomial (exponent ![0, 1, 0, 2, 2, 2, 2, 0, 1, 0]) (a ^ 2 * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 0, 3, 0, 3, 1, 2, 0, 0]) (a ^ 2 * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 1, 0, 3, 1, 2, 1, 1, 1, 0]) (a ^ 2 * b ^ 3 * c + a * c ^ 4) + monomial (exponent ![0, 1, 0, 3, 2, 1, 1, 0, 2, 0]) (a * b * c ^ 3) +
    monomial (exponent ![0, 1, 0, 4, 0, 2, 0, 2, 1, 0]) (a * b * c ^ 3) + monomial (exponent ![0, 1, 0, 4, 1, 1, 0, 1, 2, 0]) (a * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 1, 1, 1, 1, 2, 3, 1, 0, 0]) (a ^ 2 * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 1, 1, 2, 1, 3, 0, 1, 0]) (a ^ 2 * b ^ 3 * c + a * c ^ 4) +
    monomial (exponent ![0, 1, 1, 1, 2, 2, 2, 0, 0, 1]) (a * b * c ^ 3) + monomial (exponent ![0, 1, 1, 2, 0, 2, 2, 2, 0, 0]) (a ^ 2 * b ^ 3 * c) +
    monomial (exponent ![0, 1, 1, 2, 1, 1, 2, 1, 1, 0]) (a ^ 2 * b ^ 4 + 3 * a * b * c ^ 3) + monomial (exponent ![0, 1, 1, 2, 1, 2, 1, 1, 0, 1]) (2 * a * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 1, 1, 2, 2, 0, 2, 0, 2, 0]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 1, 2, 2, 1, 1, 0, 1, 1]) (a ^ 3 * b * c ^ 2) +
    monomial (exponent ![0, 1, 1, 3, 0, 1, 1, 2, 1, 0]) (2 * a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 1, 3, 0, 2, 0, 2, 0, 1]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) +
    monomial (exponent ![0, 1, 1, 3, 1, 0, 1, 1, 2, 0]) (a * b ^ 3 * c) + monomial (exponent ![0, 1, 2, 0, 2, 0, 4, 0, 1, 0]) (a * b * c ^ 3) +
    monomial (exponent ![0, 1, 2, 0, 2, 1, 3, 0, 0, 1]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 2, 1, 1, 0, 3, 1, 1, 0]) (2 * a * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) + monomial (exponent ![0, 1, 2, 1, 2, 0, 2, 0, 1, 1]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![0, 1, 2, 2, 0, 0, 2, 2, 1, 0]) (a * b ^ 3 * c) + monomial (exponent ![0, 1, 2, 2, 0, 1, 1, 2, 0, 1]) (a ^ 3 * b ^ 2 * c) +
    monomial (exponent ![0, 1, 2, 2, 1, 0, 1, 1, 1, 1]) (b ^ 2 * c ^ 2) + monomial (exponent ![0, 1, 2, 2, 1, 1, 0, 1, 0, 2]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![0, 1, 3, 0, 1, 0, 3, 1, 0, 1]) (a ^ 3 * b ^ 2 * c) + monomial (exponent ![0, 1, 3, 0, 2, 0, 2, 0, 0, 2]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![0, 2, 0, 1, 1, 2, 3, 0, 1, 0]) (a * b * c ^ 3) + monomial (exponent ![0, 2, 0, 1, 1, 3, 2, 0, 0, 1]) (a * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 2, 0, 2, 0, 2, 2, 1, 1, 0]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![0, 2, 0, 2, 0, 3, 1, 1, 0, 1]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) +
    monomial (exponent ![0, 2, 0, 2, 1, 1, 2, 0, 2, 0]) (c ^ 4) + monomial (exponent ![0, 2, 0, 2, 1, 2, 1, 0, 1, 1]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![0, 2, 0, 3, 0, 1, 1, 1, 2, 0]) (b * c ^ 3) + monomial (exponent ![0, 2, 0, 3, 0, 2, 0, 1, 1, 1]) (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 2, 0, 3, 1, 1, 0, 0, 2, 1]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 2, 1, 0, 1, 1, 4, 0, 1, 0]) (a * b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 2, 1, 1, 0, 1, 3, 1, 1, 0]) (a * b ^ 3 * c) + monomial (exponent ![0, 2, 1, 1, 0, 2, 2, 1, 0, 1]) (a ^ 3 * b ^ 2 * c) +
    monomial (exponent ![0, 2, 1, 1, 1, 0, 3, 0, 2, 0]) (b * c ^ 3) + monomial (exponent ![0, 2, 1, 1, 1, 1, 2, 0, 1, 1]) (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) +
    monomial (exponent ![0, 2, 1, 1, 1, 2, 1, 0, 0, 2]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 2, 1, 2, 0, 0, 2, 1, 2, 0]) (b ^ 2 * c ^ 2) +
    monomial (exponent ![0, 2, 1, 2, 0, 1, 1, 1, 1, 1]) (2 * a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 2, 1, 2, 0, 2, 0, 1, 0, 2]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 2, 1, 2, 1, 0, 1, 0, 2, 1]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![0, 2, 2, 0, 1, 0, 3, 0, 1, 1]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![0, 2, 2, 0, 1, 1, 2, 0, 0, 2]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![0, 2, 2, 1, 0, 0, 2, 1, 1, 1]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 2, 2, 1, 1, 0, 1, 0, 1, 2]) (a * b * c ^ 2) + monomial (exponent ![0, 3, 0, 1, 0, 2, 2, 0, 1, 1]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![0, 3, 0, 1, 0, 3, 1, 0, 0, 2]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![0, 3, 0, 2, 0, 1, 1, 0, 2, 1]) (a * c ^ 3) +
    monomial (exponent ![0, 3, 0, 2, 0, 2, 0, 0, 1, 2]) (a * b * c ^ 2) + monomial (exponent ![0, 3, 1, 0, 0, 1, 3, 0, 1, 1]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 3, 1, 1, 0, 0, 2, 0, 2, 1]) (a * b * c ^ 2) + monomial (exponent ![1, 0, 0, 2, 2, 2, 1, 1, 1, 0]) (a * b * c ^ 3) +
    monomial (exponent ![1, 0, 0, 2, 3, 1, 1, 0, 2, 0]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![1, 0, 0, 3, 0, 3, 0, 3, 0, 0]) (a * b * c ^ 3) +
    monomial (exponent ![1, 0, 0, 3, 1, 2, 0, 2, 1, 0]) (a * b ^ 2 * c ^ 2) + monomial (exponent ![1, 0, 1, 1, 1, 2, 2, 2, 0, 0]) (a * b * c ^ 3) +
    monomial (exponent ![1, 0, 1, 1, 2, 1, 2, 1, 1, 0]) (2 * a * b ^ 2 * c ^ 2) + monomial (exponent ![1, 0, 1, 1, 2, 2, 1, 1, 0, 1]) (a ^ 3 * b * c ^ 2) +
    monomial (exponent ![1, 0, 1, 1, 3, 0, 2, 0, 2, 0]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) + monomial (exponent ![1, 0, 1, 2, 0, 2, 1, 3, 0, 0]) (a * b ^ 2 * c ^ 2) +
    monomial (exponent ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) + monomial (exponent ![1, 0, 1, 2, 1, 2, 0, 2, 0, 1]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![1, 0, 1, 2, 2, 0, 1, 1, 2, 0]) (a ^ 3 * b ^ 2 * c) + monomial (exponent ![1, 0, 1, 2, 2, 1, 0, 1, 1, 1]) (b ^ 2 * c ^ 2) +
    monomial (exponent ![1, 0, 1, 3, 0, 1, 0, 3, 1, 0]) (a ^ 3 * b ^ 2 * c) + monomial (exponent ![1, 0, 2, 0, 1, 1, 3, 2, 0, 0]) (a * b ^ 2 * c ^ 2) +
    monomial (exponent ![1, 0, 2, 0, 2, 0, 3, 1, 1, 0]) (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) + monomial (exponent ![1, 0, 2, 0, 2, 1, 2, 1, 0, 1]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![1, 0, 2, 0, 3, 0, 2, 0, 1, 1]) (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) + monomial (exponent ![1, 0, 2, 0, 3, 1, 1, 0, 0, 2]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![1, 0, 2, 1, 1, 0, 2, 2, 1, 0]) (a ^ 3 * b ^ 2 * c) + monomial (exponent ![1, 0, 2, 1, 1, 1, 1, 2, 0, 1]) (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) +
    monomial (exponent ![1, 0, 2, 1, 2, 0, 1, 1, 1, 1]) (2 * a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 0, 2, 1, 2, 1, 0, 1, 0, 2]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![1, 0, 2, 2, 0, 1, 0, 3, 0, 1]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 0, 2, 2, 1, 0, 0, 2, 1, 1]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![1, 0, 3, 0, 1, 0, 2, 2, 0, 1]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 0, 3, 0, 2, 0, 1, 1, 0, 2]) (a * c ^ 3) +
    monomial (exponent ![1, 0, 3, 1, 0, 0, 1, 3, 0, 1]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 0, 3, 1, 1, 0, 0, 2, 0, 2]) (a * b * c ^ 2) +
    monomial (exponent ![1, 1, 0, 1, 1, 2, 2, 1, 1, 0]) (a ^ 3 * b * c ^ 2) + monomial (exponent ![1, 1, 0, 1, 2, 1, 2, 0, 2, 0]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![1, 1, 0, 1, 2, 2, 1, 0, 1, 1]) (b ^ 2 * c ^ 2) + monomial (exponent ![1, 1, 0, 2, 0, 2, 1, 2, 1, 0]) (a ^ 3 * b ^ 2 * c + b * c ^ 3) +
    monomial (exponent ![1, 1, 0, 2, 0, 3, 0, 2, 0, 1]) (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) + monomial (exponent ![1, 1, 0, 2, 1, 1, 1, 1, 2, 0]) (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) +
    monomial (exponent ![1, 1, 0, 2, 1, 2, 0, 1, 1, 1]) (2 * a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 1, 0, 2, 2, 0, 1, 0, 3, 0]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![1, 1, 0, 2, 2, 1, 0, 0, 2, 1]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 1, 0, 3, 0, 1, 0, 2, 2, 0]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![1, 1, 0, 3, 1, 0, 0, 1, 3, 0]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 1, 1, 0, 1, 2, 2, 1, 0, 1]) (b ^ 2 * c ^ 2) +
    monomial (exponent ![1, 1, 1, 0, 2, 0, 3, 0, 2, 0]) (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) + monomial (exponent ![1, 1, 1, 0, 2, 1, 2, 0, 1, 1]) (2 * a ^ 2 * b * c ^ 2) +
    monomial (exponent ![1, 1, 1, 0, 2, 2, 1, 0, 0, 2]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 1, 1, 1, 0, 1, 2, 2, 1, 0]) (b ^ 2 * c ^ 2) +
    monomial (exponent ![1, 1, 1, 1, 0, 2, 1, 2, 0, 1]) (2 * a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 1, 1, 1, 1, 0, 2, 1, 2, 0]) (2 * a ^ 2 * b * c ^ 2) +
    monomial (exponent ![1, 1, 1, 1, 1, 2, 0, 1, 0, 2]) (a ^ 2 * b ^ 3 + a * c ^ 3) + monomial (exponent ![1, 1, 1, 1, 2, 0, 1, 0, 2, 1]) (a ^ 2 * b ^ 3 + a * c ^ 3) +
    monomial (exponent ![1, 1, 1, 1, 2, 1, 0, 0, 1, 2]) (a * b * c ^ 2) + monomial (exponent ![1, 1, 1, 2, 0, 0, 1, 2, 2, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![1, 1, 1, 2, 0, 1, 0, 2, 1, 1]) (a ^ 2 * b ^ 3 + a * c ^ 3) + monomial (exponent ![1, 1, 1, 2, 1, 0, 0, 1, 2, 1]) (a * b * c ^ 2) +
    monomial (exponent ![1, 1, 2, 0, 0, 1, 2, 2, 0, 1]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 1, 2, 0, 1, 0, 2, 1, 1, 1]) (a ^ 2 * b ^ 3 + a * c ^ 3) +
    monomial (exponent ![1, 1, 2, 0, 1, 1, 1, 1, 0, 2]) (2 * a * b * c ^ 2) + monomial (exponent ![1, 1, 2, 0, 2, 0, 1, 0, 1, 2]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 1, 2, 1, 0, 0, 1, 2, 1, 1]) (a * b * c ^ 2) + monomial (exponent ![1, 1, 2, 1, 0, 1, 0, 2, 0, 2]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 2, 0, 0, 1, 1, 3, 0, 2, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![1, 2, 0, 0, 1, 2, 2, 0, 1, 1]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![1, 2, 0, 1, 0, 1, 2, 1, 2, 0]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![1, 2, 0, 1, 0, 2, 1, 1, 1, 1]) (a ^ 2 * b ^ 3 + a * c ^ 3) +
    monomial (exponent ![1, 2, 0, 1, 0, 3, 0, 1, 0, 2]) (a * b * c ^ 2) + monomial (exponent ![1, 2, 0, 1, 1, 0, 2, 0, 3, 0]) (a * c ^ 3) +
    monomial (exponent ![1, 2, 0, 1, 1, 1, 1, 0, 2, 1]) (2 * a * b * c ^ 2) + monomial (exponent ![1, 2, 0, 1, 1, 2, 0, 0, 1, 2]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 2, 0, 2, 0, 0, 1, 1, 3, 0]) (a * b * c ^ 2) + monomial (exponent ![1, 2, 0, 2, 0, 1, 0, 1, 2, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 2, 1, 0, 0, 1, 2, 1, 1, 1]) (a * b * c ^ 2) + monomial (exponent ![1, 2, 1, 0, 0, 2, 1, 1, 0, 2]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 2, 1, 0, 1, 0, 2, 0, 2, 1]) (a * b ^ 2 * c) + monomial (exponent ![1, 2, 1, 1, 0, 1, 0, 1, 1, 2]) (b * c ^ 2) +
    monomial (exponent ![2, 0, 0, 1, 1, 3, 0, 2, 0, 1]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![2, 0, 0, 1, 2, 1, 1, 1, 2, 0]) (a ^ 2 * b * c ^ 2) +
    monomial (exponent ![2, 0, 0, 1, 2, 2, 0, 1, 1, 1]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![2, 0, 0, 1, 3, 0, 1, 0, 3, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![2, 0, 0, 2, 0, 2, 0, 3, 1, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![2, 0, 0, 2, 1, 1, 0, 2, 2, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![2, 0, 1, 0, 1, 1, 2, 2, 1, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![2, 0, 1, 0, 1, 2, 1, 2, 0, 1]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![2, 0, 1, 0, 2, 0, 2, 1, 2, 0]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![2, 0, 1, 0, 2, 1, 1, 1, 1, 1]) (a ^ 2 * b ^ 3 + a * c ^ 3) +
    monomial (exponent ![2, 0, 1, 0, 2, 2, 0, 1, 0, 2]) (a * b * c ^ 2) + monomial (exponent ![2, 0, 1, 0, 3, 0, 1, 0, 2, 1]) (a * b * c ^ 2) +
    monomial (exponent ![2, 0, 1, 0, 3, 1, 0, 0, 1, 2]) (a * b ^ 2 * c) + monomial (exponent ![2, 0, 1, 1, 0, 2, 0, 3, 0, 1]) (a * c ^ 3) +
    monomial (exponent ![2, 0, 1, 1, 1, 1, 0, 2, 1, 1]) (2 * a * b * c ^ 2) + monomial (exponent ![2, 0, 1, 1, 2, 0, 0, 1, 2, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![2, 0, 2, 0, 0, 1, 1, 3, 0, 1]) (a * b * c ^ 2) + monomial (exponent ![2, 0, 2, 0, 1, 0, 1, 2, 1, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![2, 0, 2, 0, 1, 1, 0, 2, 0, 2]) (c ^ 3) + monomial (exponent ![2, 0, 2, 0, 2, 0, 0, 1, 1, 2]) (b * c ^ 2) +
    monomial (exponent ![2, 1, 0, 0, 1, 2, 1, 1, 1, 1]) (a * b * c ^ 2) + monomial (exponent ![2, 1, 0, 0, 1, 3, 0, 1, 0, 2]) (a * b ^ 2 * c) +
    monomial (exponent ![2, 1, 0, 0, 2, 0, 2, 0, 3, 0]) (a * b * c ^ 2) + monomial (exponent ![2, 1, 0, 0, 2, 1, 1, 0, 2, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![2, 1, 0, 1, 0, 1, 1, 2, 2, 0]) (a * b * c ^ 2) + monomial (exponent ![2, 1, 0, 1, 0, 2, 0, 2, 1, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![2, 1, 1, 0, 0, 2, 0, 2, 0, 2]) (b * c ^ 2) + monomial (exponent ![2, 1, 1, 0, 1, 0, 1, 1, 2, 1]) (b * c ^ 2)

  let H5 : MvPolynomial (Fin 10) K :=
    monomial (exponent ![0, 0, 1, 3, 2, 1, 1, 1, 1, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 0, 1, 4, 1, 1, 0, 2, 1, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 0, 2, 2, 2, 0, 2, 1, 1, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 0, 2, 3, 0, 1, 1, 3, 0, 0]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![0, 0, 2, 3, 1, 0, 1, 2, 1, 0]) (a ^ 2 * b ^ 3) +
    monomial (exponent ![0, 0, 3, 1, 1, 0, 3, 2, 0, 0]) (a ^ 2 * b ^ 2 * c) + monomial (exponent ![0, 0, 3, 1, 2, 0, 2, 1, 0, 1]) (a * b * c ^ 2) +
    monomial (exponent ![0, 0, 3, 2, 0, 0, 2, 3, 0, 0]) (a ^ 2 * b ^ 3) + monomial (exponent ![0, 0, 3, 2, 1, 0, 1, 2, 0, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![0, 1, 1, 1, 1, 2, 3, 1, 0, 0]) (a ^ 2 * b * c ^ 2) + monomial (exponent ![0, 1, 1, 2, 0, 2, 2, 2, 0, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 1, 1, 2, 1, 1, 2, 1, 1, 0]) (a * c ^ 3) + monomial (exponent ![0, 1, 1, 3, 0, 1, 1, 2, 1, 0]) (a * b * c ^ 2) +
    monomial (exponent ![0, 1, 1, 3, 1, 1, 0, 1, 1, 1]) (a ^ 3 * b * c) + monomial (exponent ![0, 1, 2, 0, 1, 1, 4, 1, 0, 0]) (a ^ 2 * b ^ 2 * c) +
    monomial (exponent ![0, 1, 2, 0, 2, 1, 3, 0, 0, 1]) (a * b * c ^ 2) + monomial (exponent ![0, 1, 2, 1, 0, 1, 3, 2, 0, 0]) (a ^ 2 * b ^ 3) +
    monomial (exponent ![0, 1, 2, 1, 1, 0, 3, 1, 1, 0]) (a * b * c ^ 2) + monomial (exponent ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1]) (2 * a * b ^ 2 * c) +
    monomial (exponent ![0, 1, 2, 2, 0, 0, 2, 2, 1, 0]) (a * b ^ 2 * c) + monomial (exponent ![0, 1, 2, 2, 0, 1, 1, 2, 0, 1]) (a ^ 3 * b * c + a * b ^ 3) +
    monomial (exponent ![0, 1, 2, 2, 1, 0, 1, 1, 1, 1]) (a ^ 3 * b ^ 2) + monomial (exponent ![0, 1, 3, 1, 0, 0, 2, 2, 0, 1]) (a ^ 3 * b ^ 2) +
    monomial (exponent ![0, 1, 3, 1, 1, 0, 1, 1, 0, 2]) (a ^ 2 * b * c) + monomial (exponent ![0, 2, 1, 0, 1, 2, 3, 0, 0, 1]) (a * b ^ 2 * c) +
    monomial (exponent ![0, 2, 1, 1, 0, 2, 2, 1, 0, 1]) (a ^ 3 * b * c + a * b ^ 3) + monomial (exponent ![0, 2, 1, 1, 1, 1, 2, 0, 1, 1]) (b * c ^ 2) +
    monomial (exponent ![0, 2, 1, 2, 0, 1, 1, 1, 1, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![0, 2, 2, 0, 0, 1, 3, 1, 0, 1]) (a ^ 3 * b ^ 2) +
    monomial (exponent ![0, 2, 2, 0, 1, 1, 2, 0, 0, 2]) (a ^ 2 * b * c) + monomial (exponent ![0, 2, 2, 1, 0, 0, 2, 1, 1, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![0, 2, 2, 1, 0, 1, 1, 1, 0, 2]) (a ^ 2 * b ^ 2) + monomial (exponent ![0, 3, 1, 0, 0, 2, 2, 0, 0, 2]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![0, 3, 1, 1, 0, 1, 1, 0, 1, 2]) (a * b * c) + monomial (exponent ![1, 0, 0, 3, 1, 2, 0, 2, 1, 0]) (a * b * c ^ 2) +
    monomial (exponent ![1, 0, 0, 3, 2, 1, 0, 1, 2, 0]) (a * b ^ 2 * c) + monomial (exponent ![1, 0, 1, 1, 3, 1, 1, 0, 1, 1]) (a ^ 3 * b * c) +
    monomial (exponent ![1, 0, 1, 2, 0, 2, 1, 3, 0, 0]) (a * b * c ^ 2) + monomial (exponent ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0]) (2 * a * b ^ 2 * c) +
    monomial (exponent ![1, 0, 1, 2, 2, 0, 1, 1, 2, 0]) (a ^ 3 * b * c + a * b ^ 3) + monomial (exponent ![1, 0, 1, 2, 2, 1, 0, 1, 1, 1]) (a ^ 3 * b ^ 2) +
    monomial (exponent ![1, 0, 1, 3, 1, 0, 0, 2, 2, 0]) (a ^ 3 * b ^ 2) + monomial (exponent ![1, 0, 2, 1, 0, 1, 2, 3, 0, 0]) (a * b ^ 2 * c) +
    monomial (exponent ![1, 0, 2, 1, 1, 0, 2, 2, 1, 0]) (a ^ 3 * b * c + a * b ^ 3) + monomial (exponent ![1, 0, 2, 1, 1, 1, 1, 2, 0, 1]) (b * c ^ 2) +
    monomial (exponent ![1, 0, 2, 1, 2, 0, 1, 1, 1, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![1, 0, 2, 2, 0, 0, 1, 3, 1, 0]) (a ^ 3 * b ^ 2) +
    monomial (exponent ![1, 0, 2, 2, 1, 0, 0, 2, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 0, 1, 1, 3, 1, 1, 0, 1]) (a ^ 3 * b * c) +
    monomial (exponent ![1, 1, 0, 1, 2, 2, 1, 0, 1, 1]) (a ^ 3 * b ^ 2) + monomial (exponent ![1, 1, 0, 2, 1, 1, 1, 1, 2, 0]) (b * c ^ 2) +
    monomial (exponent ![1, 1, 0, 2, 1, 2, 0, 1, 1, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![1, 1, 0, 2, 2, 1, 0, 0, 2, 1]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 1, 1, 0, 1, 1, 3, 1, 1, 0]) (a ^ 3 * b * c) + monomial (exponent ![1, 1, 1, 0, 1, 2, 2, 1, 0, 1]) (a ^ 3 * b ^ 2) +
    monomial (exponent ![1, 1, 1, 0, 2, 1, 2, 0, 1, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![1, 1, 1, 0, 2, 2, 1, 0, 0, 2]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 1, 1, 1, 0, 1, 2, 2, 1, 0]) (a ^ 3 * b ^ 2) + monomial (exponent ![1, 1, 1, 1, 0, 2, 1, 2, 0, 1]) (a ^ 2 * c ^ 2 + b ^ 2 * c) +
    monomial (exponent ![1, 1, 1, 1, 1, 0, 2, 1, 2, 0]) (a ^ 2 * c ^ 2 + b ^ 2 * c) + monomial (exponent ![1, 1, 1, 2, 0, 0, 1, 2, 2, 0]) (a ^ 2 * b * c) +
    monomial (exponent ![1, 1, 2, 0, 0, 1, 2, 2, 0, 1]) (a ^ 2 * b * c) + monomial (exponent ![1, 1, 2, 0, 1, 1, 1, 1, 0, 2]) (a * c ^ 2) +
    monomial (exponent ![1, 2, 0, 0, 1, 2, 2, 0, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![1, 2, 0, 0, 1, 3, 1, 0, 0, 2]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![1, 2, 0, 1, 1, 1, 1, 0, 2, 1]) (a * c ^ 2) + monomial (exponent ![1, 2, 0, 1, 1, 2, 0, 0, 1, 2]) (a * b * c) +
    monomial (exponent ![1, 2, 1, 0, 0, 2, 1, 1, 0, 2]) (a * b * c) + monomial (exponent ![1, 2, 1, 0, 1, 1, 1, 0, 1, 2]) (a * b ^ 2) +
    monomial (exponent ![2, 0, 0, 1, 2, 2, 0, 1, 1, 1]) (a ^ 2 * b * c) + monomial (exponent ![2, 0, 0, 1, 3, 1, 0, 0, 2, 1]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![2, 0, 0, 2, 1, 1, 0, 2, 2, 0]) (a ^ 2 * b * c) + monomial (exponent ![2, 0, 0, 2, 2, 0, 0, 1, 3, 0]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![2, 0, 1, 1, 0, 1, 1, 3, 1, 0]) (a ^ 2 * b * c) + monomial (exponent ![2, 0, 1, 1, 1, 0, 1, 2, 2, 0]) (a ^ 2 * b ^ 2) +
    monomial (exponent ![2, 0, 1, 1, 1, 1, 0, 2, 1, 1]) (a * c ^ 2) + monomial (exponent ![2, 0, 1, 1, 2, 0, 0, 1, 2, 1]) (a * b * c) +
    monomial (exponent ![2, 1, 0, 0, 2, 1, 1, 0, 2, 1]) (a * b * c) + monomial (exponent ![2, 1, 0, 0, 2, 2, 0, 0, 1, 2]) (a * b ^ 2) +
    monomial (exponent ![2, 1, 0, 1, 1, 0, 1, 1, 3, 0]) (a * b * c) + monomial (exponent ![2, 1, 0, 1, 1, 1, 0, 1, 2, 1]) (a * b ^ 2) +
    monomial (exponent ![2, 1, 1, 0, 1, 1, 0, 1, 1, 2]) (b * c)

  let H : Fin 6 → MvPolynomial (Fin 10) K := ![H0,H1,H2,H3,H4,H5]

  let position : Fin 6 → (Fin 10 →₀ ℕ) :=
    ![exponent ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      exponent ![2, 0, 1, 1, 1, 1, 1, 0, 2, 1],
      exponent ![2, 1, 0, 1, 1, 1, 1, 0, 1, 2],
      exponent ![2, 1, 1, 0, 0, 1, 1, 2, 1, 1],
      exponent ![2, 1, 1, 0, 1, 0, 1, 1, 2, 1],
      exponent ![2, 1, 1, 0, 1, 1, 0, 1, 1, 2]]

  let diagonal : Fin 6 → K := ![1,b,b ^ 2,c,b * c ^ 2,b * c]

  have hcoeff : ∀ i j : Fin 6, coeff (position i) (H j) =
      if i = j then diagonal i else 0 := by
    classical
    intro i j
    fin_cases i <;> fin_cases j
    all_goals
      simp only [H, position, diagonal, Matrix.cons_val_zero',
        Matrix.cons_val_succ']
    all_goals
      simp [H0, H1, H2, H3, H4, H5,
        coeff_monomial, exponent, funext_iff, Fin.forall_fin_succ]
  have hk : ∀ i : Fin 6, phi target (H i) = 0 := by
    clear hcoeff
    let r : MvPolynomial (Fin 10) K := C a * X 1 * X 9 + C b * X 3 * X 7 + C c * X 6 * X 4
    let s : Fin 10 → MvPolynomial (Fin 10) K := fun i =>
      if h : i.val + 1 < 10 then X 0 * X ⟨i.val+1,h⟩ else r
    have hk0 : phi target H0 = 0 := by
      change X 0 ^ 8 * r * H0 - aeval s H0 = 0
      simp only [H0, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, aeval_X, s, r]
      ring
    have hk1 : phi target H1 = 0 := by
      clear hk0
      change X 0 ^ 8 * r * H1 - aeval s H1 = 0
      simp only [H1, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, map_pow, aeval_X, s, r]
      ring
    have hk2 : phi target H2 = 0 := by
      clear hk0 hk1
      change X 0 ^ 8 * r * H2 - aeval s H2 = 0
      simp only [H2, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, map_pow, map_ofNat, aeval_X, s, r]
      ring
    have hk3 : phi target H3 = 0 := by
      clear hk0 hk1 hk2
      change X 0 ^ 8 * r * H3 - aeval s H3 = 0
      simp only [H3, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, map_pow, aeval_X, s, r]
      ring
    have hk4 : phi target H4 = 0 := by
      clear hk0 hk1 hk2 hk3
      change X 0 ^ 8 * r * H4 - aeval s H4 = 0
      simp only [H4, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, map_pow, map_ofNat, aeval_X, s, r]
      ring
    have hk5 : phi target H5 = 0 := by
      clear hk0 hk1 hk2 hk3 hk4
      change X 0 ^ 8 * r * H5 - aeval s H5 = 0
      simp only [H5, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        exponent, Finsupp.coe_equivFunOnFinite_symm]
      simp [Fin.prod_univ_succ, map_mul, map_pow, map_ofNat, aeval_X, s, r]
      ring
    intro i
    fin_cases i
    · exact hk0
    · exact hk1
    · exact hk2
    · exact hk3
    · exact hk4
    · exact hk5
  have hw : ∀ i : Fin 6, H i ∈ upsilon 10 := by
    clear hcoeff hk
    have term_mem (d : Exp 10) (r' : K) (hd : admissible d) :
        monomial (exponent d) r' ∈ upsilon 10 := by
      have hm : monomial (exponent d) (1 : K) ∈ upsilon 10 :=
        Submodule.subset_span ⟨⟨d,hd⟩,rfl⟩
      simpa only [smul_monomial, smul_eq_mul, mul_one] using
        Submodule.smul_mem (upsilon 10) r' hm
    have hw0 : H0 ∈ upsilon 10 := by
      exact (term_mem ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1] (1) (by unfold admissible; decide))
    have hw1 : H1 ∈ upsilon 10 := by
      clear hw0
      exact (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (term_mem ![0, 1, 1, 1, 2, 2, 1, 1, 1, 0] (c ^ 2) (by unfold admissible; decide))
        (term_mem ![0, 1, 1, 2, 1, 2, 0, 2, 1, 0] (b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 2, 1, 2, 1, 1, 0] (b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 1, 1, 2, 1, 0] (b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 2, 0, 1, 1, 1] (a * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 1, 1, 1, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 1, 2, 0, 1, 1] (a * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 0, 1, 1, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 1, 1, 2, 0, 1] (a * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 2, 0, 1, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 1, 1, 1, 2, 0] (a * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 2, 0, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 2, 2, 0, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 0, 2, 2, 0, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 1, 0, 2, 2, 0] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 2, 0, 1, 1, 0, 2] (c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 1, 1, 0, 2, 1] (c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 1, 0, 2, 1, 1] (c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 0, 2, 1, 1, 1] (c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 1, 1, 1, 0, 2] (b) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 0, 2, 1, 1, 1, 1] (c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 1, 1, 0, 2, 1] (b) (by unfold admissible; decide)))
    have hw2 : H2 ∈ upsilon 10 := by
      clear hw0 hw1
      exact (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10)
        (term_mem ![0, 0, 2, 1, 2, 2, 2, 0, 1, 0] (a * c ^ 3) (by unfold admissible; decide))
        (term_mem ![0, 0, 2, 2, 1, 2, 1, 1, 1, 0] (2 * a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 3, 0, 2, 0, 2, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 0, 2, 1, 3, 0, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 1, 1, 1, 2, 1, 1, 0] (2 * a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 2, 0, 1, 1, 2, 1, 0] (a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 2, 2, 2, 1, 2, 0, 0] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 2, 3, 1, 1, 1, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 3, 1, 2, 0, 3, 0, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 3, 2, 1, 0, 2, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 1, 3, 2, 0, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 2, 1, 2, 2, 0, 0] (2 * a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 3, 0, 2, 1, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 3, 1, 1, 1, 0, 1] (c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 0, 3, 1, 1, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 1, 1, 3, 0, 0] (2 * a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 2, 1, 0, 2, 0] (c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 2, 0, 1, 2, 1, 0] (a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 2, 1, 0, 2, 0, 1] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 0, 2, 0, 1, 2, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 1, 2, 3, 0, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 2, 0, 3, 2, 0, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 3, 0, 2, 1, 0, 1] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 0, 2, 2, 1, 1, 0] (a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 0, 2, 3, 0, 0] (a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 1, 2, 0, 2, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 2, 1, 0, 1, 1] (a ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 2, 0, 1, 2, 0, 1] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 1, 1, 1, 2, 0] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 2, 0, 1, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 0, 1, 1, 2, 0, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 1, 0, 1, 1, 1, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 1, 2, 1, 2, 1, 1, 0] (c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 1, 2, 2, 1, 1, 0, 1] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 1, 1, 1, 2, 1, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 1, 2, 0, 2, 0, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 2, 1, 0, 1, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 0, 2, 0, 3, 1, 1, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 0, 2, 1, 2, 1, 0, 1] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 0, 3, 1, 0, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 0, 2, 2, 1, 0] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 1, 1, 2, 0, 1] (2 * a ^ 2 * b * c + b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 2, 0, 1, 1, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 2, 1, 0, 1, 0, 2] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 0, 2, 0, 0, 2, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 0, 2, 2, 0, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 1, 0, 2, 2, 0, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 2, 0, 1, 1, 0, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 1, 0, 1, 1, 0, 2, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 1, 1, 1, 1, 1, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 1, 1, 2, 0, 1, 0, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 0, 1, 0, 2, 1, 1, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 0, 1, 1, 1, 1, 0, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 1, 3, 1, 1, 1, 0] (c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 2, 2, 1, 0, 2, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 0, 3, 0, 2, 1, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 1, 2, 1, 0, 1] (a ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 2, 0, 1, 2, 0] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 2, 0, 2, 0, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 3, 0, 1, 1, 2, 0, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 3, 1, 0, 1, 1, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 1, 2, 2, 1, 1, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 2, 1, 2, 0, 2, 0] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 2, 2, 1, 0, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 0, 2, 1, 2, 1, 0] (b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 0, 3, 1, 0, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 1, 1, 1, 2, 0] (2 * a ^ 2 * b * c + b ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 2, 0, 1, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 2, 0, 2, 0, 0, 2] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 0, 0, 2, 2, 0, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 0, 1, 0, 2, 2, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 1, 0, 1, 1, 0, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 0, 1, 1, 1, 1, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 1, 0, 1, 0, 2, 1, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 2, 1, 1, 2, 1, 0] (a ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 2, 2, 0, 2, 0, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 3, 0, 1, 1, 2, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 3, 1, 0, 1, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 0, 2, 2, 1, 0, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 1, 0, 3, 1, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 1, 2, 0, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 2, 0, 0, 2, 2, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 3, 0, 1, 1, 1, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 3, 1, 0, 1, 0, 2, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 2, 2, 0, 2, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 3, 1, 0, 1, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 0, 2, 2, 1, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 1, 1, 2, 0, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 3, 0, 1, 1, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 3, 1, 0, 1, 0, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 1, 3, 1, 0, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 2, 1, 1, 2, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 3, 0, 1, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 0, 1, 3, 1, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 0, 3, 0, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 1, 0, 3, 0, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 1, 1, 0, 3, 0] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 1, 2, 0, 0, 2] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 2, 0, 0, 2, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 2, 0, 0, 2, 1, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 0, 2, 1, 1, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 1, 0, 1, 3, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 1, 1, 1, 0, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 1, 0, 1, 0, 1, 2] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 0, 2, 1, 1, 1, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 0, 1, 3, 0, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 1, 1, 0, 2, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 2, 0, 0, 2, 0, 2] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 1, 0, 1, 0, 1, 2, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 2, 0, 2, 1, 2, 0] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 2, 1, 1, 1, 1, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 2, 2, 0, 1, 0, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 0, 1, 3, 0, 1, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 0, 2, 2, 0, 0, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 0, 1, 2, 2, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 1, 0, 2, 1, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 2, 0, 0, 2, 0, 2, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 2, 0, 1, 1, 0, 1, 2] (b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 1, 0, 1, 2, 1, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 1, 1, 0, 2, 0, 2] (b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 0, 2, 1, 2, 0, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 1, 1, 1, 1, 1, 1] (2 * a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 2, 0, 1, 0, 2, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 1, 2, 1, 1, 2, 0] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 1, 3, 0, 1, 1, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 2, 1, 1, 0, 3, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 2, 2, 0, 0, 2, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 0, 1, 2, 2, 0, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 0, 2, 0, 2, 2, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 0, 2, 1, 1, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 1, 0, 1, 3, 0] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 1, 1, 1, 0, 2] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 2, 0, 1, 0, 1, 2] (b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 0, 2, 0, 2, 1, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 1, 1, 0, 1, 2, 1] (b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 0, 1, 2, 1, 1, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 0, 2, 1, 1, 0, 2] (b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 1, 0, 2, 0, 2, 1] (b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 1, 1, 1, 0, 1, 2] (b ^ 2) (by unfold admissible; decide)))
    have hw3 : H3 ∈ upsilon 10 := by
      clear hw0 hw1 hw2
      exact (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10)
        (term_mem ![0, 0, 1, 2, 2, 2, 2, 1, 0, 0] (a ^ 2 * c ^ 2) (by unfold admissible; decide))
        (term_mem ![0, 0, 1, 3, 1, 2, 1, 2, 0, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 1, 2, 1, 3, 1, 0, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 1, 3, 1, 2, 0, 0, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 2, 1, 1, 1, 0, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 2, 2, 2, 0, 0, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 2, 1, 1, 0, 1] (a ^ 3 * c + a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 2, 1, 1, 0, 1, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 1, 1, 0, 1, 1, 1] (b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1] (a ^ 3 * b) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 2, 1, 1, 0, 0, 2] (a ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 2, 1, 0, 0, 2] (a ^ 2 * b) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 1, 1, 0, 0, 1, 2] (a * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 2, 1, 3, 1, 2, 0, 0] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 2, 2, 2, 1, 1, 1, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 1, 2, 2, 2, 0, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 2, 1, 2, 1, 1, 0] (a ^ 3 * c + a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 2, 2, 1, 1, 0, 1] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 3, 1, 1, 0, 1, 1] (b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0] (a ^ 3 * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 1, 2, 2, 1, 1, 0] (c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 1, 3, 1, 1, 0, 1] (b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 1, 3, 1, 1, 0] (b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 2, 1, 0, 0, 1, 2] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 1, 0, 0, 1, 2, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 1, 0, 0, 1, 2, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 1, 1, 0, 0, 1, 1, 2] (c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 0, 1, 2, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 1, 0, 0, 1, 1, 2, 1] (c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 1, 2, 1, 2, 1, 0] (a ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 2, 1, 1, 1, 2, 0] (a ^ 2 * b) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 1, 1, 2, 1, 2, 0] (a * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 1, 2, 1, 1, 1, 1] (a * b) (by unfold admissible; decide)))
        (term_mem ![2, 1, 1, 0, 0, 1, 1, 2, 1, 1] (c) (by unfold admissible; decide)))
    have hw4 : H4 ∈ upsilon 10 := by
      clear hw0 hw1 hw2 hw3
      exact (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (term_mem ![0, 0, 1, 2, 3, 1, 2, 0, 1, 0] (a ^ 2 * b * c ^ 3) (by unfold admissible; decide))
        (term_mem ![0, 0, 1, 3, 1, 2, 1, 2, 0, 0] (a ^ 2 * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 1, 3, 2, 1, 1, 1, 1, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 1, 4, 0, 2, 0, 3, 0, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 1, 2, 1, 3, 1, 0, 0] (a ^ 2 * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 1, 3, 0, 3, 0, 1, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0] (2 * a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 2, 0, 2, 1, 1, 0] (a ^ 2 * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 2, 1, 1, 1, 0, 1] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 3, 0, 1, 1, 3, 0, 0] (a ^ 2 * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 3, 1, 1, 0, 2, 0, 1] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 0, 2, 0, 4, 1, 0, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 0, 3, 0, 3, 0, 0, 1] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 1, 1, 0, 3, 2, 0, 0] (a ^ 2 * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 1, 2, 0, 2, 1, 0, 1] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 2, 1, 3, 2, 1, 0, 0] (a ^ 2 * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 2, 2, 2, 2, 0, 1, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 3, 0, 3, 1, 2, 0, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 3, 1, 2, 1, 1, 1, 0] (a ^ 2 * b ^ 3 * c + a * c ^ 4) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 3, 2, 1, 1, 0, 2, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 4, 0, 2, 0, 2, 1, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 0, 4, 1, 1, 0, 1, 2, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 1, 2, 3, 1, 0, 0] (a ^ 2 * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 2, 1, 3, 0, 1, 0] (a ^ 2 * b ^ 3 * c + a * c ^ 4) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 2, 2, 2, 0, 0, 1] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 0, 2, 2, 2, 0, 0] (a ^ 2 * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 1, 2, 1, 1, 0] (a ^ 2 * b ^ 4 + 3 * a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 2, 1, 1, 0, 1] (2 * a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 2, 0, 2, 0, 2, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 2, 1, 1, 0, 1, 1] (a ^ 3 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 0, 1, 1, 2, 1, 0] (2 * a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 0, 2, 0, 2, 0, 1] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 1, 0, 1, 1, 2, 0] (a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 2, 0, 4, 0, 1, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 2, 1, 3, 0, 0, 1] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 0, 3, 1, 1, 0] (2 * a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 2, 0, 2, 0, 1, 1] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 0, 2, 2, 1, 0] (a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 1, 1, 2, 0, 1] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 1, 0, 1, 1, 1, 1] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 1, 1, 0, 1, 0, 2] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 0, 1, 0, 3, 1, 0, 1] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 0, 2, 0, 2, 0, 0, 2] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 1, 1, 2, 3, 0, 1, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 1, 1, 3, 2, 0, 0, 1] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 0, 2, 2, 1, 1, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 0, 3, 1, 1, 0, 1] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 1, 1, 2, 0, 2, 0] (c ^ 4) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 2, 1, 2, 1, 0, 1, 1] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 3, 0, 1, 1, 1, 2, 0] (b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 3, 0, 2, 0, 1, 1, 1] (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 0, 3, 1, 1, 0, 0, 2, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 0, 1, 1, 4, 0, 1, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 0, 1, 3, 1, 1, 0] (a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 0, 2, 2, 1, 0, 1] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 0, 3, 0, 2, 0] (b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 1, 2, 0, 1, 1] (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 2, 1, 0, 0, 2] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 0, 0, 2, 1, 2, 0] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 0, 1, 1, 1, 1, 1] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 0, 2, 0, 1, 0, 2] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 1, 0, 1, 0, 2, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 1, 0, 3, 0, 1, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 1, 1, 2, 0, 0, 2] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 1, 0, 0, 2, 1, 1, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 1, 1, 0, 1, 0, 1, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 1, 0, 2, 2, 0, 1, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 1, 0, 3, 1, 0, 0, 2] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 2, 0, 1, 1, 0, 2, 1] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 3, 0, 2, 0, 2, 0, 0, 1, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 0, 0, 1, 3, 0, 1, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 1, 0, 0, 2, 0, 2, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 2, 2, 2, 1, 1, 1, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 2, 3, 1, 1, 0, 2, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 3, 0, 3, 0, 3, 0, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 3, 1, 2, 0, 2, 1, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 1, 2, 2, 2, 0, 0] (a * b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 2, 1, 2, 1, 1, 0] (2 * a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 2, 2, 1, 1, 0, 1] (a ^ 3 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 3, 0, 2, 0, 2, 0] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 0, 2, 1, 3, 0, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 2, 0, 2, 0, 1] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 2, 0, 1, 1, 2, 0] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 2, 1, 0, 1, 1, 1] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 3, 0, 1, 0, 3, 1, 0] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 1, 1, 3, 2, 0, 0] (a * b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 2, 0, 3, 1, 1, 0] (a ^ 3 * b * c ^ 2 + a * b ^ 3 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 2, 1, 2, 1, 0, 1] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 3, 0, 2, 0, 1, 1] (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 0, 3, 1, 1, 0, 0, 2] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 0, 2, 2, 1, 0] (a ^ 3 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 1, 1, 2, 0, 1] (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 2, 0, 1, 1, 1, 1] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 2, 1, 0, 1, 0, 2] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 0, 1, 0, 3, 0, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 1, 0, 0, 2, 1, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 0, 1, 0, 2, 2, 0, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 0, 2, 0, 1, 1, 0, 2] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 1, 0, 0, 1, 3, 0, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 3, 1, 1, 0, 0, 2, 0, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 1, 2, 2, 1, 1, 0] (a ^ 3 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 2, 1, 2, 0, 2, 0] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 2, 2, 1, 0, 1, 1] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 0, 2, 1, 2, 1, 0] (a ^ 3 * b ^ 2 * c + b * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 0, 3, 0, 2, 0, 1] (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 1, 1, 1, 2, 0] (a ^ 3 * b ^ 3 + a ^ 2 * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 2, 0, 1, 1, 1] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 2, 0, 1, 0, 3, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 2, 1, 0, 0, 2, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 3, 0, 1, 0, 2, 2, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 3, 1, 0, 0, 1, 3, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 2, 2, 1, 0, 1] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 0, 3, 0, 2, 0] (a ^ 2 * c ^ 3 + b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 1, 2, 0, 1, 1] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 2, 1, 0, 0, 2] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 1, 2, 2, 1, 0] (b ^ 2 * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 2, 1, 2, 0, 1] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 0, 2, 1, 2, 0] (2 * a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 2, 0, 1, 0, 2] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 2, 0, 1, 0, 2, 1] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 2, 1, 0, 0, 1, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 0, 1, 2, 2, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 1, 0, 2, 1, 1] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 1, 0, 0, 1, 2, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 0, 1, 2, 2, 0, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 0, 2, 1, 1, 1] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 1, 1, 1, 0, 2] (2 * a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 2, 0, 1, 0, 1, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 1, 0, 0, 1, 2, 1, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 1, 0, 1, 0, 2, 0, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 1, 1, 3, 0, 2, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 1, 2, 2, 0, 1, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 0, 1, 2, 1, 2, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 0, 2, 1, 1, 1, 1] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 0, 3, 0, 1, 0, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 0, 2, 0, 3, 0] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 1, 1, 0, 2, 1] (2 * a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 2, 0, 0, 1, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 2, 0, 0, 1, 1, 3, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 2, 0, 1, 0, 1, 2, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 0, 1, 2, 1, 1, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 0, 2, 1, 1, 0, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 1, 0, 2, 0, 2, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 1, 0, 1, 0, 1, 1, 2] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 1, 3, 0, 2, 0, 1] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 2, 1, 1, 1, 2, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 2, 2, 0, 1, 1, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 3, 0, 1, 0, 3, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 0, 2, 0, 3, 1, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 1, 1, 0, 2, 2, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 1, 1, 2, 2, 1, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 1, 2, 1, 2, 0, 1] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 2, 0, 2, 1, 2, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 2, 1, 1, 1, 1, 1] (a ^ 2 * b ^ 3 + a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 2, 2, 0, 1, 0, 2] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 3, 0, 1, 0, 2, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 0, 3, 1, 0, 0, 1, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 0, 2, 0, 3, 0, 1] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 1, 0, 2, 1, 1] (2 * a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 2, 0, 0, 1, 2, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 0, 1, 1, 3, 0, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 1, 0, 1, 2, 1, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 1, 1, 0, 2, 0, 2] (c ^ 3) (by unfold admissible; decide)))
        (term_mem ![2, 0, 2, 0, 2, 0, 0, 1, 1, 2] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 1, 2, 1, 1, 1, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 1, 3, 0, 1, 0, 2] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 2, 0, 2, 0, 3, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 2, 1, 1, 0, 2, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 0, 1, 1, 2, 2, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 0, 2, 0, 2, 1, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 1, 0, 0, 2, 0, 2, 0, 2] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 1, 0, 1, 0, 1, 1, 2, 1] (b * c ^ 2) (by unfold admissible; decide)))
    have hw5 : H5 ∈ upsilon 10 := by
      clear hw0 hw1 hw2 hw3 hw4
      exact (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10) (Submodule.add_mem (upsilon 10)
        (Submodule.add_mem (upsilon 10)
        (term_mem ![0, 0, 1, 3, 2, 1, 1, 1, 1, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide))
        (term_mem ![0, 0, 1, 4, 1, 1, 0, 2, 1, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 1, 1, 2, 2, 0, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 2, 2, 0, 2, 1, 1, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 3, 0, 1, 1, 3, 0, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 2, 3, 1, 0, 1, 2, 1, 0] (a ^ 2 * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 1, 1, 0, 3, 2, 0, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 1, 2, 0, 2, 1, 0, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 2, 0, 0, 2, 3, 0, 0] (a ^ 2 * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 0, 3, 2, 1, 0, 1, 2, 0, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 1, 1, 2, 3, 1, 0, 0] (a ^ 2 * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 0, 2, 2, 2, 0, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 2, 1, 1, 2, 1, 1, 0] (a * c ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 0, 1, 1, 2, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 1, 3, 1, 1, 0, 1, 1, 1] (a ^ 3 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 1, 1, 4, 1, 0, 0] (a ^ 2 * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 0, 2, 1, 3, 0, 0, 1] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 0, 1, 3, 2, 0, 0] (a ^ 2 * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 0, 3, 1, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 1, 1, 1, 2, 1, 0, 1] (2 * a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 0, 2, 2, 1, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 0, 1, 1, 2, 0, 1] (a ^ 3 * b * c + a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 1, 2, 2, 1, 0, 1, 1, 1, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 1, 0, 0, 2, 2, 0, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 1, 3, 1, 1, 0, 1, 1, 0, 2] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 0, 1, 2, 3, 0, 0, 1] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 0, 2, 2, 1, 0, 1] (a ^ 3 * b * c + a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 1, 1, 1, 2, 0, 1, 1] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 1, 2, 0, 1, 1, 1, 1, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 0, 1, 3, 1, 0, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 0, 1, 1, 2, 0, 0, 2] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 1, 0, 0, 2, 1, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![0, 2, 2, 1, 0, 1, 1, 1, 0, 2] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 0, 0, 2, 2, 0, 0, 2] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![0, 3, 1, 1, 0, 1, 1, 0, 1, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 3, 1, 2, 0, 2, 1, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 0, 3, 2, 1, 0, 1, 2, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 1, 3, 1, 1, 0, 1, 1] (a ^ 3 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 0, 2, 1, 3, 0, 0] (a * b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 1, 1, 1, 2, 1, 0] (2 * a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 2, 0, 1, 1, 2, 0] (a ^ 3 * b * c + a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 2, 2, 1, 0, 1, 1, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 1, 3, 1, 0, 0, 2, 2, 0] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 0, 1, 2, 3, 0, 0] (a * b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 0, 2, 2, 1, 0] (a ^ 3 * b * c + a * b ^ 3) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 1, 1, 1, 2, 0, 1] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 1, 2, 0, 1, 1, 1, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 0, 0, 1, 3, 1, 0] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 0, 2, 2, 1, 0, 0, 2, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 1, 3, 1, 1, 0, 1] (a ^ 3 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 1, 2, 2, 1, 0, 1, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 1, 1, 1, 2, 0] (b * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 1, 2, 0, 1, 1, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 0, 2, 2, 1, 0, 0, 2, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 1, 3, 1, 1, 0] (a ^ 3 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 1, 2, 2, 1, 0, 1] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 1, 2, 0, 1, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 0, 2, 2, 1, 0, 0, 2] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 1, 2, 2, 1, 0] (a ^ 3 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 0, 2, 1, 2, 0, 1] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 1, 1, 0, 2, 1, 2, 0] (a ^ 2 * c ^ 2 + b ^ 2 * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 1, 2, 0, 0, 1, 2, 2, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 0, 1, 2, 2, 0, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 1, 2, 0, 1, 1, 1, 1, 0, 2] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 1, 2, 2, 0, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 0, 1, 3, 1, 0, 0, 2] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 1, 1, 0, 2, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![1, 2, 0, 1, 1, 2, 0, 0, 1, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 0, 2, 1, 1, 0, 2] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![1, 2, 1, 0, 1, 1, 1, 0, 1, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 2, 2, 0, 1, 1, 1] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 1, 3, 1, 0, 0, 2, 1] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 1, 1, 0, 2, 2, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 0, 2, 2, 0, 0, 1, 3, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 0, 1, 1, 3, 1, 0] (a ^ 2 * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 0, 1, 2, 2, 0] (a ^ 2 * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 1, 1, 0, 2, 1, 1] (a * c ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 0, 1, 1, 2, 0, 0, 1, 2, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 2, 1, 1, 0, 2, 1] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 0, 2, 2, 0, 0, 1, 2] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 1, 0, 1, 1, 3, 0] (a * b * c) (by unfold admissible; decide)))
        (term_mem ![2, 1, 0, 1, 1, 1, 0, 1, 2, 1] (a * b ^ 2) (by unfold admissible; decide)))
        (term_mem ![2, 1, 1, 0, 1, 1, 0, 1, 1, 2] (b * c) (by unfold admissible; decide)))
    intro i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
    · exact hw3
    · exact hw4
    · exact hw5
  have hmem : ∀ i : Fin 6, H i ∈ omega target := by
    intro i
    exact ⟨hw i, hk i⟩
  classical
  have hb : b ≠ 0 := by
    intro hz
    apply X_ne_zero (R := ℚ) (1 : Fin 3)
    apply IsFractionRing.injective Parameters K
    exact hz.trans (map_zero _).symm
  have hc : c ≠ 0 := by
    intro hz
    apply X_ne_zero (R := ℚ) (2 : Fin 3)
    apply IsFractionRing.injective Parameters K
    exact hz.trans (map_zero _).symm
  have hdiag : ∀ i : Fin 6, diagonal i ≠ 0 := by
    intro i
    fin_cases i <;> simp [diagonal, hb, hc]
  have hind : LinearIndependent K H := by
    rw [Fintype.linearIndependent_iff]
    intro l hl j
    have he := congrArg (coeff (position j)) hl
    simp only [coeff_sum, coeff_smul, coeff_zero, hcoeff, smul_eq_mul] at he
    have he' : l j * diagonal j = 0 := by
      simpa using he
    exact (mul_eq_zero.mp he').resolve_right (hdiag j)
  let v : Fin 6 → omega target := fun i => ⟨H i, hmem i⟩
  have hv : LinearIndependent K v := by
    apply LinearIndependent.of_comp (omega target).subtype
    change LinearIndependent K H
    exact hind
  let finiteU : (n : ℕ) → FiniteDimensional K (upsilon n) :=
    fun n => Module.Finite.span_of_finite K (Set.finite_range _)
  let : FiniteDimensional K (omega target) := by
    unfold omega
    infer_instance
  have six_le : 6 ≤ Module.finrank K (omega target) := hv.fintype_card_le_finrank
  intro hclaim
  have ht : proper target := by
    norm_num [target, proper]
  have hdim := hclaim target ht
  norm_num [target, order] at hdim
  omega

end D5.S0.Certificates.Combinatorics.GaleRobinsonKernelDimensionRefutation
