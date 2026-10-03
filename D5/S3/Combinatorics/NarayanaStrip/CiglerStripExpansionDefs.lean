/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs
   mirror-E: none(waiver:fixed-narayana-strip-expansion-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Basic]
   utility: none
   digest: Cigler's expansion of Narayana-weighted Dyck paths in a strip of even height. -/

import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs

open Polynomial

/-! Fixed public statement: Cigler, *Some sequences and number triangles which are related to
    Narayana polynomials and to q-Narayana polynomials for q=-1*, arXiv:2608.03363v2, §4,
    Conjecture 3.  A path is a list of steps, `true` for an up-step and `false` for a down-step.
    An up-step has weight `1`; a down-step arriving at height `k` has weight `τ k`. -/

/-- The height after the first `k` steps of `p`. -/
def heightAfter (p : List Bool) (k : ℕ) : ℤ :=
  ((p.take k).map fun b => if b then (1 : ℤ) else -1).sum

/-- `p` is a Dyck path in the strip `0 ≤ y ≤ h`: every prefix height lies in `[0, h]` and the
    path ends at height `0`. -/
def IsStripDyck (h : ℕ) (p : List Bool) : Prop :=
  (∀ k ≤ p.length, 0 ≤ heightAfter p k ∧ heightAfter p k ≤ h) ∧ heightAfter p p.length = 0

/-- The weight of `p`: the product, over its down-steps, of `τ` at the height reached. -/
noncomputable def weight (τ : ℕ → ℤ[X]) (p : List Bool) : ℤ[X] :=
  ((List.range p.length).map fun i =>
    if p.getD i true then 1 else τ (heightAfter p (i + 1)).toNat).prod

open Classical in
/-- The weighted sum of the Dyck paths of semilength `n` in the strip of height `h`. -/
noncomputable def stripSum (τ : ℕ → ℤ[X]) (h n : ℕ) : ℤ[X] :=
  ∑ f : Fin (2 * n) → Bool, if IsStripDyck h (List.ofFn f) then weight τ (List.ofFn f) else 0

open Classical in
/-- `C_j^{(h)}`: the number of Dyck paths of semilength `j` in the strip of height `h`. -/
noncomputable def stripCount (h j : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin (2 * j) → Bool => IsStripDyck h (List.ofFn f)).card

/-- The Narayana weights `τ = (1, t, 1, t, …)`. -/
noncomputable def tauPlus (k : ℕ) : ℤ[X] := if k % 2 = 0 then 1 else X

/-- The `q = -1` weights `τ = (1, t, -1, -t, 1, t, -1, -t, …)`. -/
noncomputable def tauMinus (k : ℕ) : ℤ[X] :=
  if k % 4 = 0 then 1 else if k % 4 = 1 then X else if k % 4 = 2 then -1 else -X

/-- Conjecture 3: for every `m ≥ 1` and `n ≥ 0`, in `ℤ[t]`,
    `C_{n+1}^{(2m)}(t) = ∑_j C_j^{(m-1)} binom(n, 2j) t^j (1+t)^{n-2j}` and
    `c_{n+1}^{(2m)}(t) = ∑_j (-1)^j C_j^{(m-1)} binom(⌊n/2⌋, j) t^j (1+t)^{n-2j}`. -/
def claim : Prop :=
  ∀ m n : ℕ, 1 ≤ m →
    stripSum tauPlus (2 * m) (n + 1) =
        ∑ j ∈ Finset.range (n / 2 + 1),
          C ((stripCount (m - 1) j * n.choose (2 * j) : ℕ) : ℤ) * X ^ j * (1 + X) ^ (n - 2 * j) ∧
      stripSum tauMinus (2 * m) (n + 1) =
        ∑ j ∈ Finset.range (n / 2 + 1),
          C ((-1) ^ j * ((stripCount (m - 1) j * (n / 2).choose j : ℕ) : ℤ)) * X ^ j *
            (1 + X) ^ (n - 2 * j)

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
