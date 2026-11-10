# Lattice shuffles and their signs

## Abstract

Lattice shuffles and their signs

A (p,q)-shuffle is an injective monotone map from Fin(p+q+1) to Fin(p+1) × Fin(q+1). All degrees p and q are arbitrary natural numbers. The coordinate sum at vertex r is r, so each edge increases exactly one coordinate by one. The inversion count sums the second coordinate before every first-coordinate step, and the integer sign is (-1) to this count.

Swapping the two coordinates exchanges the two degrees. The two inversion counts sum to p*q, giving the Koszul factor (-1)^(p*q). The staircase path k ↦ (min(k,p),k-p) has sign 1. When either degree is zero there is a unique shuffle. Finiteness of each shuffle set is used only for finite sums; there is no bound on the degrees.

**Definition 1.1 (Index).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Index`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Index` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The finite chain object `0 ≤ 1 ≤ ··· ≤ k` in `PoSet`, represented by `Fin (k+1)`.

In this notation, abbrev Index (k : ℕ).

**Definition 1.2 (Shuffle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Shuffle`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Shuffle` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A `(p,q)`-shuffle as an injective monotone map `Index (p + q) ⟶ Index p × Index q` in `PoSet`.

In this notation, abbrev Shuffle (p q : ℕ).

**Definition 1.3 (instFintype).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.instFintype`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.instFintype` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

There are finitely many (p,q)-shuffles in every pair of degrees.

In this notation, noncomputable instance instFintype (p q : ℕ) : Fintype (Shuffle p q).

**Definition 1.4 (invCount).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **number of inversions** of a shuffle.

In this notation, def invCount {p q : ℕ} (μ : Shuffle p q) : ℕ.

**Definition 1.5 (sign).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The sign of a shuffle: `(-1)^k` where `k` is the number of inversions.

In this notation, def sign {p q : ℕ} (μ : Shuffle p q) : ℤ.

**Definition 1.6 (swap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Swap the two coordinates of a shuffle, yielding a `(q,p)`-shuffle.

In this notation, def swap {p q : ℕ} (μ : Shuffle p q) : Shuffle q p.

**Theorem 1.7 (swap_swap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_swap`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_swap` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Exchanging both coordinates twice recovers the original shuffle.

In this notation, @[grind =, simp] theorem swap_swap {p q : ℕ} (μ : Shuffle p q) : swap (swap μ) = μ.

**Definition 1.8 (swapEquiv).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swapEquiv`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swapEquiv` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Swapping coordinates gives an equivalence `Shuffle p q ≃ Shuffle q p`.

In this notation, def swapEquiv (p q : ℕ) : Shuffle p q ≃ Shuffle q p.

**Theorem 1.9 (coordSum_eq).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.coordSum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.coordSum_eq` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At every position `r`, the coordinate sum equals `r.val`.

In this notation, @[grind =] lemma coordSum_eq {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q + 1)) : (u.1 r).1.val + (u.1 r).2.val = r.val.

**Theorem 1.10 (shuffle_step).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_step`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_step` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At each step of a shuffle, exactly one coordinate increases by 1.

In this notation, lemma shuffle_step {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) : ((u.1 r.castSucc).1.val + 1 = (u.1 r.succ).1.val ∧ (u.1 r.castSucc).2.val = (u.1 r.succ).2.val) ∨ ((u.1 r.castSucc).1.val = (u.1 r.succ).1.val ∧ (u.1 r.castSucc).2.val + 1 = (u.1 r.succ).2.val).

**Theorem 1.11 (shuffle_fst_lt_iff_not_snd_lt).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_fst_lt_iff_not_snd_lt`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_fst_lt_iff_not_snd_lt` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

First coordinate increases iff second doesn't at each step.

In this notation, lemma shuffle_fst_lt_iff_not_snd_lt {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) : (u.1 r.castSucc).1.val < (u.1 r.succ).1.val ↔ ¬ ((u.1 r.castSucc).2.val < (u.1 r.succ).2.val).

**Theorem 1.12 (exists_snd_step).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_snd_step`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_snd_step` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A shuffle path crosses every intermediate `snd`-level: for `i + 1 ≤ q` there is a step `a` that is a **`q`-step at level `i`** — the second coordinate goes `i → i + 1` while the first coordinate is fixed. This is the degeneracy analog of the face-insertion step lemmas, and is what lets the Eilenberg–Zilber map carry a one-direction degeneracy to a diagonal one.

In this notation, lemma exists_snd_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ q) : ∃ a : Fin (p + q), (μ.1 a.castSucc).2.val = i ∧ (μ.1 a.succ).2.val = i + 1 ∧ (μ.1 a.castSucc).1 = (μ.1 a.succ).1.

**Theorem 1.13 (exists_fst_step).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_fst_step`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_fst_step` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The first-coordinate analog of `exists_snd_step`: for `i + 1 ≤ p` there is a **`p`-step at level `i`** — the first coordinate goes `i → i + 1` while the second coordinate is fixed. Used for the outer (horizontal) Eilenberg–Zilber degeneracy kill.

In this notation, lemma exists_fst_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ p) : ∃ a : Fin (p + q), (μ.1 a.castSucc).1.val = i ∧ (μ.1 a.succ).1.val = i + 1 ∧ (μ.1 a.castSucc).2 = (μ.1 a.succ).2.

**Theorem 1.14 (swap_apply_fst).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_apply_fst`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_apply_fst` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The swap of a shuffle at position x gives the swapped coordinates of u at the same position.

In this notation, lemma swap_apply_fst {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) : ((u.swap).1 x).1.val = (u.1 (x.cast (by omega))).2.val.

**Theorem 1.15 (apply_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Every shuffle starts at the vertex (0,0).

In this notation, lemma apply_zero {p q : ℕ} (u : Shuffle p q) : u.1 0 = (0, 0).

**Theorem 1.16 (apply_last).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_last`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_last` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Every shuffle ends at the vertex (p,q).

In this notation, lemma apply_last {p q : ℕ} (u : Shuffle p q) : u.1 (Fin.last (p + q)) = (Fin.last p, Fin.last q).

**Theorem 1.17 (invCount_eq_sum_mul_diff).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_eq_sum_mul_diff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_eq_sum_mul_diff` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inversion count is the sum of the second coordinate times each increment of the first coordinate.

In this notation, lemma invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) : u.invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val).

**Theorem 1.18 (swap_invCount_eq_sum_mul_diff).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_invCount_eq_sum_mul_diff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_invCount_eq_sum_mul_diff` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inversion count of the swapped path is the sum of the first coordinate times each increment of the second coordinate.

In this notation, lemma swap_invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) : (u.swap).invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val).

**Theorem 1.19 (xy_diff_eq_sum_mixed).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.xy_diff_eq_sum_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.xy_diff_eq_sum_mixed` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The change of the product of the two coordinates across one unit step is the sum of the two mixed coordinate increments.

In this notation, lemma xy_diff_eq_sum_mixed {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) : (u.1 r.succ).1.val * (u.1 r.succ).2.val - (u.1 r.castSucc).1.val * (u.1 r.castSucc).2.val = (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val) + (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val).

**Theorem 1.20 (invCount_add_invCount_swap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_add_invCount_swap`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_add_invCount_swap` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The two coordinate orders partition the p*q pairs of unlike steps, so their inversion counts sum to p*q.

In this notation, lemma invCount_add_invCount_swap {p q : ℕ} (u : Shuffle p q) : u.invCount + (u.swap).invCount = p * q.

**Theorem 1.21 (sign_eq_negOnePow_mul_swap_sign).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_eq_negOnePow_mul_swap_sign`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_eq_negOnePow_mul_swap_sign` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Swapping a `(p,q)`-shuffle changes the sign by the Koszul factor `(-1)^(p*q)`.

In this notation, theorem sign_eq_negOnePow_mul_swap_sign {p q : ℕ} (u : Shuffle p q) : u.sign = (-1 : ℤ) ^ (p * q) * (u.swap).sign.

**Definition 1.22 (trivialShuffle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **staircase** `(r,m)`-shuffle `k ↦ (min(k,r), k - r)`: it goes right `r` steps then up `m` steps. Its front-`r` face and back-`m` face recover the identity, so it is the unique shuffle contributing the identity summand to the diagonal Eilenberg–Zilber/Alexander–Whitney pairing.

In this notation, def trivialShuffle (r m : ℕ) : Shuffle r m.

**Theorem 1.23 (trivialShuffle_apply).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle_apply`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle_apply` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The coordinates of the staircase shuffle: `fst = min(·, r)`, `snd = · - r`.

In this notation, @[simp] lemma trivialShuffle_apply (r m : ℕ) (k : Index (r + m)) : (trivialShuffle r m).1 k = (⟨min k.val r, by omega⟩, ⟨k.val - r, by have := k.isLt; omega⟩).

**Theorem 1.24 (sign_trivialShuffle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_trivialShuffle`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_trivialShuffle` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The staircase shuffle has no inversions, hence sign `1`.

In this notation, lemma sign_trivialShuffle (r m : ℕ) : (trivialShuffle r m).sign = 1.

**Definition 1.25 (isLeftStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.isLeftStep`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.isLeftStep` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Whether step `r` of shuffle `μ` is a "left step" (first coordinate increments).

In this notation, def isLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) : Prop.

**Definition 1.26 (decidableIsLeftStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.decidableIsLeftStep`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.decidableIsLeftStep` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

First-coordinate increase is decidable on every edge of a shuffle.

In this notation, instance decidableIsLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) : Decidable (isLeftStep μ r).

**Definition 1.27 (uniqueShuffleNZero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleNZero`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleNZero` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A shuffle with zero second degree is the unique path k ↦ (k,0).

In this notation, instance uniqueShuffleNZero {n : ℕ} : Unique (Shuffle n 0).

**Definition 1.28 (uniqueShuffleZeroN).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleZeroN`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleZeroN` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A shuffle with zero first degree is the unique path k ↦ (0,k).

In this notation, instance uniqueShuffleZeroN {n : ℕ} : Unique (Shuffle 0 n).

**Theorem 1.29 (Shuffle.sign_default_zero_right).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_right` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The unique `(n,0)`-shuffle has sign `1`.

In this notation, lemma Shuffle.sign_default_zero_right {n : ℕ} : (default : Shuffle n 0).sign = 1.

**Theorem 1.30 (Shuffle.sign_default_zero_left).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_left`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_left` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The unique `(0,n)`-shuffle has sign `1`.

In this notation, lemma Shuffle.sign_default_zero_left {n : ℕ} : (default : Shuffle 0 n).sign = 1.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Index`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.Shuffle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_last`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.apply_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.coordSum_eq`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.decidableIsLeftStep`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_fst_step`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.exists_snd_step`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.instFintype`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_add_invCount_swap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.invCount_eq_sum_mul_diff`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.isLeftStep`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_fst_lt_iff_not_snd_lt`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.shuffle_step`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_default_zero_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_eq_negOnePow_mul_swap_sign`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.sign_trivialShuffle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swapEquiv`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_apply_fst`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_invCount_eq_sum_mul_diff`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.swap_swap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.trivialShuffle_apply`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleNZero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.uniqueShuffleZeroN`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic.xy_diff_eq_sum_mixed`
