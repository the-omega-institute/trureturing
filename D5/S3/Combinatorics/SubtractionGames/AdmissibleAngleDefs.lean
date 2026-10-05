/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleDefs
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleDefs
   mirror-E: none(waiver:manabe-conjecture-fifty-seven-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Nat.Even, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Manabe's admissible-angle conjecture for purely periodic three-move subtraction games. -/

import D5.S0.Certificates.Games.CrimGrundyRefutation
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleDefs

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex)

/-! Fixed public statement: H. Manabe, *Purely Periodic Three-move Subtraction Games*,
    arXiv:2609.05358v2, Section 6: "Conjecture 57 (admissible angle). Let S be non-additive with
    a ≥ 2 and gcd(a, b, c) = 1, and suppose that G_S is purely periodic with least period p. If
    p = c + a then ρ ∈ Θ_{c+a}, and if p = c + b then ρ ∈ Θ_{c+b}."

    Here `S = {a, b, c}` with `a < b < c` is non-additive when `c ≠ a + b`, `G_S` is the
    Sprague–Grundy sequence `G_S(n) = mex {G_S(n − s) : s ∈ S, s ≤ n}`, and the angle is
    `ρ = c mod (a + b)`.  With `m = a + b` and `B = {a, b}`, the base pattern `Z` is the set of
    residues of the P-positions of `B` in `[0, m)`; `δ = b − a = ηa + ε` with `0 ≤ ε < a`;
    `D = [a, b) \ Z`; `Λ = [(η + 1)a, (η + 1)a + ε)` for even `η` and `[ηa + ε, (η + 1)a)` for
    odd `η` (equation (4)); translates are read modulo `m` (Definition 19):
    `ρ ∈ Θ_{c+a} ⇔ Z ∩ [0, δ) ∩ (Z + (δ − ρ)) = ∅` and
    `ρ ∈ Θ_{c+b} ⇔ (ρ + Λ) ∩ Z = ∅ ∧ (ρ + D) ∩ Λ = ∅`. -/

/-- The Sprague–Grundy sequence of the subtraction game with move set `S`. -/
noncomputable def grundy (S : Finset ℕ) (n : ℕ) : ℕ :=
  Nat.strongRecOn n fun n ih =>
    mex ((S.filter fun s => 0 < s ∧ s ≤ n).attach.image fun s =>
      ih (n - s.1) (by have := (Finset.mem_filter.mp s.2).2; omega))

/-- `g` is purely periodic with least period `p`. -/
def LeastPurePeriod (g : ℕ → ℕ) (p : ℕ) : Prop :=
  0 < p ∧ (∀ n, g (n + p) = g n) ∧ ∀ q, 0 < q → q < p → ¬ ∀ n, g (n + q) = g n

/-- Translate of a set of residues modulo `m`. -/
def shift (m t : ℕ) (X : Finset ℕ) : Finset ℕ := X.image fun x => (x + t) % m

/-- The base pattern `Z`: residues in `[0, a + b)` of the P-positions of `{a, b}`. -/
noncomputable def basePattern (a b : ℕ) : Finset ℕ :=
  (Finset.range (a + b)).filter fun r => grundy {a, b} r = 0

/-- The gaps `D = [a, b) \ Z`. -/
noncomputable def gaps (a b : ℕ) : Finset ℕ := Finset.Ico a b \ basePattern a b

/-- The arc `Λ` of equation (4), with `b − a = ηa + ε`. -/
def arc (a b : ℕ) : Finset ℕ :=
  let η := (b - a) / a
  let ε := (b - a) % a
  if Even η then Finset.Ico ((η + 1) * a) ((η + 1) * a + ε)
  else Finset.Ico (η * a + ε) ((η + 1) * a)

/-- Condition (T1): `ρ ∈ Θ_{c+a}`. -/
def AdmissibleCA (a b ρ : ℕ) : Prop :=
  let m := a + b
  basePattern a b ∩ Finset.range (b - a) ∩ shift m ((b - a + m - ρ) % m) (basePattern a b) = ∅

/-- Condition (T2): `ρ ∈ Θ_{c+b}`. -/
def AdmissibleCB (a b ρ : ℕ) : Prop :=
  let m := a + b
  shift m ρ (arc a b) ∩ basePattern a b = ∅ ∧ shift m ρ (gaps a b) ∩ arc a b = ∅

/-- Conjecture 57. -/
def claim : Prop :=
  ∀ a b c p : ℕ, 2 ≤ a → a < b → b < c → c ≠ a + b → Nat.gcd (Nat.gcd a b) c = 1 →
    LeastPurePeriod (grundy {a, b, c}) p →
      (p = c + a → AdmissibleCA a b (c % (a + b))) ∧
        (p = c + b → AdmissibleCB a b (c % (a + b)))

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleDefs
