/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedRamseyDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedRamseyDefs
   mirror-E: none(waiver:cyclic-and-ordered-nested-matching-conjectures-statement-definition)
   anchors: []
   utility: none
   digest: Conjectures 4.30, 4.31 and 4.33 of arXiv:2604.16188 on ordered and cyclic Ramsey numbers of nested matchings. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-! Fixed public statements. N. Bašić, I. Damnjanović, D. Stevanović and I. Stošić, *Some results
    on small ordered and cyclic Ramsey numbers*, arXiv:2604.16188v1, Section 4:
    "Conjecture 4.30. Let a, b ⩾ 4 be divisible by four. Then Rcyc(M_a^nest, M_b^nest) = a + b − 3."
    "Conjecture 4.31. For any even a ⩾ 2 and any b ∈ N, we have
    Rord(M_a^nest, P_b^mon) = 1 + (a − 1)(b − 1)."
    "Conjecture 4.33. For any even a ⩾ 2 and any b ⩾ 2, we have Rcyc(M_a^nest, S_b) = a + b − 3
    if 4 | a and b is odd, and a + b − 2 otherwise."
    Section 1: Rord(H_1, H_2) is the least n such that every 2-edge-colouring of K_n contains H_j in
    colour j for some j through an increasing embedding. Section 2: for even n, the nested
    matching M_n^nest is the 1-regular graph of order n in which each vertex v is adjacent only to
    n − 1 − v. Cyclic Ramsey numbers, P_b^mon and S_b are as in `CyclicRamseyDefs`,
    `MonotoneRamseyDefs` and `DihedralRamseyDefs`. -/

/-- `H` is embeddable in `G` with its vertex order preserved. -/
def OrderedEmbeddable {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ ψ : Fin k → Fin n, StrictMono ψ ∧ ∀ i j, H.Adj i j → G.Adj (ψ i) (ψ j)

/-- The ordered Ramsey number `Rord(H, J)`. -/
noncomputable def orderedRamsey {a b : ℕ} (H : SimpleGraph (Fin a)) (J : SimpleGraph (Fin b)) :
    ℕ :=
  sInf {N | ∀ G : SimpleGraph (Fin N), OrderedEmbeddable H G ∨ OrderedEmbeddable J Gᶜ}

/-- The nested matching `M_a^nest`: `v` is adjacent to `a − 1 − v`. -/
def nestMatching (a : ℕ) : SimpleGraph (Fin a) :=
  SimpleGraph.fromRel fun x y => x.val + y.val + 1 = a

/-- Conjecture 4.30 of arXiv:2604.16188. -/
def claimNestNest : Prop :=
  ∀ a b : ℕ, 4 ≤ a → 4 ≤ b → 4 ∣ a → 4 ∣ b →
    cyclicRamsey (nestMatching a) (nestMatching b) = a + b - 3

/-- Conjecture 4.31 of arXiv:2604.16188. -/
def claimOrdNestMon : Prop :=
  ∀ a b : ℕ, 2 ≤ a → a % 2 = 0 → 1 ≤ b →
    orderedRamsey (nestMatching a) (monoPath b) = 1 + (a - 1) * (b - 1)

/-- Conjecture 4.33 of arXiv:2604.16188. -/
def claimCycNestStar : Prop :=
  ∀ a b : ℕ, 2 ≤ a → a % 2 = 0 → 2 ≤ b →
    cyclicRamsey (nestMatching a) (startStar b) = if 4 ∣ a ∧ b % 2 = 1 then a + b - 3 else a + b - 2

end D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs
