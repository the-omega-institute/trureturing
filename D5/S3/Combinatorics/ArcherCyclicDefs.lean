/- GID: D5/S3/Combinatorics/ArcherCyclicDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicDefs
   mirror-E: none(waiver:fixed-cyclic-avoider-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Cyclic permutations avoiding patterns in one-line and cycle forms. -/

import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Rotate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicDefs

/-! Fixed public statements: Archer, Borsh, Bridges, Graves, Jeske, arXiv:2408.15000, §4:
    `|A°_n(4123; 1324)|` is a Tetranacci number and `|A°_n(4132; 1324)|` is a Padovan number.
    Permutations of `[n]` are lists in one-line notation; `p.getD (x - 1) 0` is the image of `x`. -/

/-- The image of `x` under the permutation written in one-line notation as `p`. -/
def image (p : List ℕ) (x : ℕ) : ℕ := p.getD (x - 1) 0

/-- The orbit word `1, p(1), p(p(1)), …` of length `n = p.length`: the standard cycle form of `p`
    when `p` is an `n`-cycle. -/
def orbitWord (p : List ℕ) : List ℕ :=
  (List.range p.length).map fun i => (image p)^[i] 1

/-- `p` is a single cycle: the orbit of `1` lists every value of `[1, n]`. -/
def IsCyclic (p : List ℕ) : Prop := (orbitWord p).Perm (List.range' 1 p.length)

/-- `A°_n(σ; τ)`: cyclic permutations of `[n]` whose one-line form avoids `σ` and all of whose cycle
    forms (the rotations of the standard cycle form) avoid `τ`. -/
def cyclicAvoiders (n : ℕ) (σ τ : List ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ IsCyclic p ∧ ¬ ArrowWilfDefs.Contains σ [] σ.length p ∧
    ∀ r < n, ¬ ArrowWilfDefs.Contains τ [] τ.length ((orbitWord p).rotate r)}

/-- Tetranacci numbers (OEIS A000078): `0, 0, 0, 1, 1, 2, 4, 8, 15, 29, …`. -/
def tetranacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | k + 4 => tetranacci (k + 3) + tetranacci (k + 2) + tetranacci (k + 1) + tetranacci k

/-- Padovan numbers (OEIS A000931): `1, 0, 0, 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, …`. -/
def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | k + 3 => padovan (k + 1) + padovan k

/-- The Tetranacci conjecture: `|A°_n(4123; 1324)| = 1, 1, 2, 4, 8, 15, 29, …` for `n = 1, 2, …`. -/
def tetranacciClaim : Prop :=
  ∀ n : ℕ, 1 ≤ n → (cyclicAvoiders n [4, 1, 2, 3] [1, 3, 2, 4]).ncard = tetranacci (n + 2)

/-- The Padovan conjecture: `|A°_n(4132; 1324)| = 1, 1, 2, 5, 12, 28, 65, …` for `n = 1, 2, …`. -/
def padovanClaim : Prop :=
  ∀ n : ℕ, 1 ≤ n → (cyclicAvoiders n [4, 1, 3, 2] [1, 3, 2, 4]).ncard = padovan (3 * n)

end D5.S3.Combinatorics.ArcherCyclicDefs
