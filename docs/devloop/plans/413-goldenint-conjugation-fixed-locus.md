# Plan #413: GoldenInt Conjugation Fixed Locus

## GOAL

Converge #413 to one implementable objective: add one proved public Lean theorem,
`D5.S0.Carrier.conj_eq_self_iff_exists_intCast`, stating that a golden integer is
fixed by golden conjugation exactly when it is an embedded integer:
`conj x = x <-> exists z : Int, x = (z : GoldenInt)`.

This plan PR itself implements no Lean, Blueprint, generated Markdown, harness,
CI, or production-code changes. It is only the planning artifact for the later
implementation slot.

## Grounding

- Origin #413 asks for one new non-vacuous `GoldenInt` theorem through the
  request marker `theory-selfgrowth:frontier-request:v1:loning`.
- `D5/S0/Carrier/Ring.lean:12-17` defines the coordinate carrier:

  ```lean
  /-- The golden integer `a + b * phi`, represented in the integral basis `(1, phi)`. -/
  @[ext]
  structure GoldenInt where
    a : ℤ
    b : ℤ
    deriving DecidableEq
  ```

- `D5/S0/Carrier/Ring.lean:60-61` fixes integer-cast coordinates:

  ```lean
  @[simp] theorem a_intCast (z : ℤ) : (z : GoldenInt).a = z := rfl
  @[simp] theorem b_intCast (z : ℤ) : (z : GoldenInt).b = 0 := rfl
  ```

- `D5/S0/Carrier/Conj.lean:12-16` gives the conjugation formula:

  ```lean
  /-- Galois conjugation, determined by `phi` mapping to `1 - phi`. -/
  def conj (x : GoldenInt) : GoldenInt := ⟨x.a + x.b, -x.b⟩

  @[simp] theorem conj_a (x : GoldenInt) : (conj x).a = x.a + x.b := rfl
  @[simp] theorem conj_b (x : GoldenInt) : (conj x).b = -x.b := rfl
  ```

- `D5/S0/Carrier/Conj.lean:26-36` proves involutivity and packages the ring
  equivalence:

  ```lean
  @[simp] theorem conj_involutive (x : GoldenInt) : conj (conj x) = x := by
    ext <;> simp [conj]

  /-- Conjugation packaged as a ring automorphism of the golden integer carrier. -/
  def conjEquiv : GoldenInt ≃+* GoldenInt where
    toFun := conj
    invFun := conj
    map_mul' := conj_mul
    map_add' := conj_add
    left_inv := conj_involutive
    right_inv := conj_involutive
  ```

- Local search found no existing theorem named
  `conj_eq_self_iff_exists_intCast` in `D5`, `Blueprint`, or
  `docs/devloop/plans`.
- `Blueprint/D5/S0/Carrier/Conj.scribe.cs:13-17` is the natural Blueprint owner
  for the later narrative extension, and the existing `Blueprint/D5/S0/Carrier`
  directory is already at the SL-003 12-file limit.

## Approach

Use the standard Galois fixed-subring argument specialized to the existing
coordinate model. From `conj x = x`, compare the `b` coordinate to get
`-x.b = x.b`; integer arithmetic then gives `x.b = 0`. With the `b` coordinate
zero, extensionality proves `x = (x.a : GoldenInt)`. The converse follows by
substituting an integer cast and simplifying the conjugation formula with the
existing `[simp]` coordinate lemmas.

Append the later theorem to `D5/S0/Carrier/Conj.lean`, because conjugation is
the semantic owner and the proof should need only the existing coordinate model.
Mirror the theorem by extending `Blueprint/D5/S0/Carrier/Conj.scribe.cs` and the
emitted `Blueprint/D5/S0/Carrier/Conj.md`. The Blueprint statement must use
`DescribeStatement.FromLean` for the exact Lean theorem. Do not add a new
Blueprint file unless a separate, properly scoped directory split has already
been performed.

## Implementation Acceptance

- Future implementation adds one real public Lean theorem
  `D5.S0.Carrier.conj_eq_self_iff_exists_intCast (x : GoldenInt) :
  conj x = x <-> exists z : Int, x = (z : GoldenInt)`, not a `Unit`
  placeholder and not a vacuous proposition.
- `lake build` succeeds.
- `#print axioms D5.S0.Carrier.conj_eq_self_iff_exists_intCast` shows no
  `sorryAx` and no custom or non-mathlib axiom.
- Future Blueprint narrative mirrors the exact Lean theorem with
  `DescribeStatement.FromLean`, and emission checks pass after generated
  Markdown is refreshed.
- Future implementation remains conservative and append-only: add the new
  theorem node and necessary Blueprint/emission updates only; do not alter
  frozen theorem statements.

## Non-Goals

Do not implement PID, UFD, prime or irreducible classification, divisibility
norm bounds, norm powers, Fibonacci coordinates, characteristic equations, new
route or split tooling, harness changes, CI changes, production-code changes, or
devloop workflow changes. Do not ask this plan PR to duplicate consensus, CI, PR
review, or merge gates.
