# Signs of inserted shuffle steps

## Abstract

Signs of inserted shuffle steps

All shuffle degrees are natural numbers and every sign is an integer. Inserting a first-coordinate step at j into a (p,q)-shuffle contributes t-j inversions, where t is insertLeftIndex. Thus its sign is (-1)^(t-j) times the original sign. The second-coordinate insertion is the coordinate swap of a first-coordinate insertion and acquires the corresponding Koszul factors.

The inversion sum is split at the insertion index. The noninserted terms match the old sum, while the inserted term supplies exactly the missing exponent. These identities supply the signs of the two boundary families in the shuffle chain map.

**Theorem 1.1 (insertLeftStep_isLeftStep_at).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertLeftStep_isLeftStep_at`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertLeftStep_isLeftStep_at` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inserted step is a left step: the first coordinate increases from `j` to `succAbove j (ν.1 t).1 > j` at the insertion vertex.

In this notation, lemma insertLeftStep_isLeftStep_at {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) (ht : (insertLeftIndex ν j).val < p + 1 + q) : isLeftStep (insertLeftStep ν j) ⟨(insertLeftIndex ν j).val, ht⟩.

**Theorem 1.2 (sign_insertLeftStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertLeftStep`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertLeftStep` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Sign relation for left insertion: `(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`. Derived from `invCount_insertLeftStep_add` via exponent arithmetic: the identity `invCount(μ) + j = invCount(ν) + t` gives `(-1)^(invCount(μ) + j) = (-1)^(invCount(ν) + t)`, hence `sign(μ) * (-1)^j = sign(ν) * (-1)^t`, and multiplying both sides by `(-1)^(j+t)` (using `(-1)^(2k) = 1`) yields the result.

In this notation, lemma sign_insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val = (-1 : ℤ) ^ j.val * ν.sign.

**Theorem 1.3 (insertRightStep_eq_swap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertRightStep_eq_swap`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertRightStep_eq_swap` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right insertion is left insertion on the swapped shuffle.

In this notation, lemma insertRightStep_eq_swap {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : (insertRightStep ν k).swap = insertLeftStep (ν.swap) k.

**Theorem 1.4 (sign_insertRightStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertRightStep`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertRightStep` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Sign relation for right insertion: `(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) = (-1)^p * (-1)^k * ν.sign`.

In this notation, lemma sign_insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val = (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign).

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertLeftStep_isLeftStep_at`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertRightStep_eq_swap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertLeftStep`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertRightStep`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion](ShuffleInsertion.md)
