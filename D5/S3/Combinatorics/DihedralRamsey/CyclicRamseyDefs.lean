/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicRamseyDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicRamseyDefs
   mirror-E: none(waiver:basic-damnjanovic-stevanovic-stosic-cyclic-conjectures-statement-definition)
   anchors: []
   utility: none
   digest: Cyclic Ramsey Conjectures 4.8, 4.10, 4.14, 4.17, 4.23 of arXiv:2604.16188 and dihedral Conjecture 4.8 of arXiv:2607.06817. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs

open DihedralRamseyDefs

/-! Fixed public statements. N. Bašić, I. Damnjanović, D. Stevanović and I. Stošić, *Some results
    on small ordered and cyclic Ramsey numbers*, arXiv:2604.16188v1, Section 4:
    "Conjecture 4.8. For any a, b ⩾ 2, we have Rcyc(P_a^alt, P_b^alt) = a + b − 2 − (ab mod 2)."
    "Conjecture 4.10. For any a, b ⩾ 2, we have Rcyc(P_a^alt, P_b^ralt) = a + b − 2 − (ab mod 2)."
    "Conjecture 4.14. For any a ⩾ 2 and b ∈ N, we have Rcyc(C_a^mon, P_b^alt) = 1 + (a − 1)(b − 1)."
    "Conjecture 4.17. For any a ⩾ 3 and b ⩾ 4, we have Rcyc(S_a, P_b^alt) = a + b − 2 − (ab mod 2)."
    "Conjecture 4.23. For any a, b ∈ N, we have Rcyc(K_a, P_b^alt) = 1 + (a − 1)(b − 1)."
    Section 1: Rcyc(H_1, H_2) is the least n such that every 2-edge-colouring of K_n contains H_j
    in colour j for some j, through an embedding φ for which some t makes
    (φ(t), …, φ(|H_j| − 1), φ(0), …, φ(t − 1)) increasing. Section 2: P_n^ralt is the path with
    underlying path (n − 1, 0, n − 2, 1, …); C_n^mon (n ⩾ 3) is the monotone path plus the edge
    {0, n − 1}, and C_2^mon := K_2; S_n is a star of order n, all centres being equivalent for
    cyclic embeddings (S_n^sc has centre 0).
    I. Damnjanović and I. Đorđević, *Computation of small reflective and dihedral Ramsey
    numbers*, arXiv:2607.06817v2, Section 4: "Conjecture 4.8. For any a ∈ N and b ⩾ 2, we have
    Rdih(P_a^alt, C_b^mon) = 1 + (a − 1)(b − 1)."
    A 2-edge-colouring of K_n is recorded by its first colour class G; the second colour class is
    the complement of G. -/

/-- `H` is cyclically embeddable in `G`: some `ψ ∘ φ` with `φ` a rotation `i ↦ i + s` and `ψ` an
increasing injection is a graph homomorphism. -/
def CyclicEmbeddable {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (s : ℕ) (ψ : Fin k → Fin n), StrictMono ψ ∧
    ∀ i j, H.Adj i j → G.Adj (ψ (dihedralPerm s false i)) (ψ (dihedralPerm s false j))

/-- The cyclic Ramsey number `Rcyc(H, J)`. -/
noncomputable def cyclicRamsey {a b : ℕ} (H : SimpleGraph (Fin a)) (J : SimpleGraph (Fin b)) :
    ℕ :=
  sInf {N | ∀ G : SimpleGraph (Fin N), CyclicEmbeddable H G ∨ CyclicEmbeddable J Gᶜ}

/-- The reverse alternating path `P_b^ralt`, with underlying path `b − 1, 0, b − 2, 1, …`. -/
def revAltPath (b : ℕ) : SimpleGraph (Fin b) :=
  SimpleGraph.fromRel fun x y =>
    ∃ j, j + 1 < b ∧ x.val = b - 1 - altVertex b j ∧ y.val = b - 1 - altVertex b (j + 1)

/-- The monotone cycle `C_a^mon`: consecutive vertices and the pair `{0, a − 1}`; for `a = 2`
this is `K_2`. -/
def monoCycle (a : ℕ) : SimpleGraph (Fin a) :=
  SimpleGraph.fromRel fun x y => y.val = x.val + 1 ∨ (x.val = 0 ∧ y.val + 1 = a)

/-- Conjecture 4.8 of arXiv:2604.16188. -/
def claimCycPathPath : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → cyclicRamsey (altPath a) (altPath b) = a + b - 2 - a * b % 2

/-- Conjecture 4.10 of arXiv:2604.16188. -/
def claimCycPathRevPath : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → cyclicRamsey (altPath a) (revAltPath b) = a + b - 2 - a * b % 2

/-- Conjecture 4.14 of arXiv:2604.16188. -/
def claimCycCyclePath : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → cyclicRamsey (monoCycle a) (altPath b) = 1 + (a - 1) * (b - 1)

/-- Conjecture 4.17 of arXiv:2604.16188. -/
def claimCycStarPath : Prop :=
  ∀ a b : ℕ, 3 ≤ a → 4 ≤ b → cyclicRamsey (startStar a) (altPath b) = a + b - 2 - a * b % 2

/-- Conjecture 4.23 of arXiv:2604.16188. -/
def claimCycCliquePath : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    cyclicRamsey (⊤ : SimpleGraph (Fin a)) (altPath b) = 1 + (a - 1) * (b - 1)

/-- Conjecture 4.8 of arXiv:2607.06817. -/
def claimPathCycle : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 2 ≤ b → dihedralRamsey (altPath a) (monoCycle b) = 1 + (a - 1) * (b - 1)

end D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs
