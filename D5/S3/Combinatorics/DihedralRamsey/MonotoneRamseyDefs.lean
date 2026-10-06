/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneRamseyDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneRamseyDefs
   mirror-E: none(waiver:cyclic-and-dihedral-monotone-path-conjectures-statement-definition)
   anchors: []
   utility: none
   digest: Cyclic Ramsey Conjectures 4.7, 4.9, 4.16 of arXiv:2604.16188 and dihedral Conjecture 4.6 of arXiv:2607.06817 on monotone paths. -/

import D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDefs

open DihedralRamseyDefs CyclicRamseyDefs

/-! Fixed public statements. N. Bašić, I. Damnjanović, D. Stevanović and I. Stošić, *Some results
    on small ordered and cyclic Ramsey numbers*, arXiv:2604.16188v1, Section 4:
    "Conjecture 4.7. For any b ⩾ a ⩾ 3, we have Rcyc(P_a^mon, P_b^mon) = 1 + (a − 1)(b − 2)."
    "Conjecture 4.9. For any a ⩾ 3 and b ⩾ 4, we have Rcyc(P_a^alt, P_b^mon) = 1 + (a − 1)(b − 2)."
    "Conjecture 4.16. For any a ⩾ 3 and b ⩾ 4, we have Rcyc(S_a, P_b^mon) = 1 + (a − 1)(b − 2)."
    I. Damnjanović and I. Đorđević, *Computation of small reflective and dihedral Ramsey
    numbers*, arXiv:2607.06817v2, Section 4: "Conjecture 4.6. For any a ⩾ 3 and b ⩾ 4, we have
    Rdih(P_a^alt, P_b^mon) = 1 + (a − 1)(b − 2)."
    P_n^mon is the graph of order n in which two vertices are adjacent exactly when they are
    consecutive integers (Section 1 of both papers). Cyclic and dihedral Ramsey numbers, P_a^alt and
    S_a are as in `CyclicRamseyDefs` and `DihedralRamseyDefs`. -/

/-- The monotone path `P_a^mon`: consecutive integers are adjacent. -/
def monoPath (a : ℕ) : SimpleGraph (Fin a) :=
  SimpleGraph.fromRel fun x y => y.val = x.val + 1

/-- Conjecture 4.7 of arXiv:2604.16188. -/
def claimCycMonMon : Prop :=
  ∀ a b : ℕ, 3 ≤ a → a ≤ b →
    cyclicRamsey (monoPath a) (monoPath b) = 1 + (a - 1) * (b - 2)

/-- Conjecture 4.9 of arXiv:2604.16188. -/
def claimCycAltMon : Prop :=
  ∀ a b : ℕ, 3 ≤ a → 4 ≤ b →
    cyclicRamsey (altPath a) (monoPath b) = 1 + (a - 1) * (b - 2)

/-- Conjecture 4.16 of arXiv:2604.16188. -/
def claimCycStarMon : Prop :=
  ∀ a b : ℕ, 3 ≤ a → 4 ≤ b →
    cyclicRamsey (startStar a) (monoPath b) = 1 + (a - 1) * (b - 2)

/-- Conjecture 4.6 of arXiv:2607.06817. -/
def claimDihAltMon : Prop :=
  ∀ a b : ℕ, 3 ≤ a → 4 ≤ b →
    dihedralRamsey (altPath a) (monoPath b) = 1 + (a - 1) * (b - 2)

end D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDefs
