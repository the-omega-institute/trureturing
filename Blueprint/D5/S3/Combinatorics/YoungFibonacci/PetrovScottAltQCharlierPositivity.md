# Alternative q-Charlier Fibonacci Positivity

## Abstract

Alternative q-Charlier Fibonacci positivity at rho = q = 1/4.

**Definition 1.1 (The first tridiagonal determinant).**

$$\forall x \in Nat \to Real, y \in Nat \to Real, n \in Nat,\; A\left(x, y, n\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{of}\left((fun (i : Fin\left(n\right)) \mapsto (fun (j : Fin\left(n\right)) \mapsto (if ((i : Nat) = (j : Nat)) then x\left((i : Nat) + 1\right) else (if ((j : Nat) = (i : Nat) + 1) then y\left((i : Nat) + 1\right) else (if ((i : Nat) = (j : Nat) + 1) then 1 else 0)))))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.A` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Define two sequences of tridiagonal determinants as follows: (arXiv:2412.21126v2, p. 15, equation (2.10)). A is the determinant with diagonal x at indices 1 through ell, upper diagonal y and lower diagonal one. The displayed Matrix.of gives every entry, including zero outside these three diagonals. The empty determinant is one.

**Definition 1.2 (The second tridiagonal determinant).**

$$\forall x \in Nat \to Real, y \in Nat \to Real, n \in Nat,\; B\left(x, y, n\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{of}\left((fun (i : Fin\left(n + 1\right)) \mapsto (fun (j : Fin\left(n + 1\right)) \mapsto (if (((i : Nat) = 0) \land ((j : Nat) = 0)) then y\left(1\right) else (if (((i : Nat) = 0) \land ((j : Nat) = 1)) then x\left(1\right) \cdot y\left(2\right) else (if ((i : Nat) = (j : Nat)) then x\left((i : Nat) + 2\right) else (if ((j : Nat) = (i : Nat) + 1) then y\left((i : Nat) + 2\right) else (if ((i : Nat) = (j : Nat) + 1) then 1 else 0)))))))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.B` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Define two sequences of tridiagonal determinants as follows: (arXiv:2412.21126v2, p. 15, equation (2.10)). B k has size k+1; its first row starts with y 1 and x 1 times y 2. The remaining diagonal starts at x 3, its upper diagonal at y 3, and its lower diagonal is one.

**Definition 1.3 (Recursion with leading ones).**

$$\begin{aligned}\forall x \in Nat \to Real, y \in Nat \to Real, k \in Nat,\; sAux\left(x, y, k, \operatorname{List}.\operatorname{nil}\right) = A\left(x, y, k\right)\\\forall x \in Nat \to Real, y \in Nat \to Real, k \in Nat, w \in List\left(Nat\right),\; sAux\left(x, y, k, \operatorname{List}.\operatorname{cons}\left(1, w\right)\right) = sAux\left(x, y, k + 1, w\right)\\\forall x \in Nat \to Real, y \in Nat \to Real, k \in Nat, a \in Nat, u \in List\left(Nat\right),\; (a \ne 1) \Rightarrow (sAux\left(x, y, k, \operatorname{List}.\operatorname{cons}\left(a, u\right)\right) = B\left((fun (j : Nat) \mapsto x\left(j + \operatorname{List}.\operatorname{sum}\left(u\right)\right)), (fun (j : Nat) \mapsto y\left(j + \operatorname{List}.\operatorname{sum}\left(u\right)\right)), k\right) \cdot sAux\left(x, y, 0, u\right))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.sAux` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

For any Fibonacci word w, define the (biserial) clone Schur function s_w(x⃗ | y⃗) through the following recurrence: s_w(x⃗ | y⃗) := A_k(x⃗ | y⃗), if w = 1^k for some k ≥ 0; B_k(x⃗ + |u| | y⃗ + |u|) · s_u(x⃗ | y⃗), if w = 1^k2u for some k ≥ 0. (Definition 2.5, p. 15). The auxiliary recursion counts k initial letters one. At an empty tail it returns A k; a letter one increases k; every other letter contributes B k with sequences shifted by the sum of the remaining letters, followed by the recursion at zero. Only letters one and two occur in Fibonacci words.

**Definition 1.4 (Biserial clone Schur functions).**

$$\forall x \in Nat \to Real, y \in Nat \to Real, w \in List\left(Nat\right),\; s\left(x, y, w\right) = sAux\left(x, y, 0, w\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.s` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

For any Fibonacci word w, define the (biserial) clone Schur function s_w(x⃗ | y⃗) through the following recurrence: s_w(x⃗ | y⃗) := A_k(x⃗ | y⃗), if w = 1^k for some k ≥ 0; B_k(x⃗ + |u| | y⃗ + |u|) · s_u(x⃗ | y⃗), if w = 1^k2u for some k ≥ 0. (Definition 2.5, p. 15). Fibonacci words are lists over {1, 2}; the weight |u| is List.sum u. The function s starts sAux with zero initial letters one.

**Definition 1.5 (Fibonacci positivity).**

$$\forall x \in Nat \to Real, y \in Nat \to Real,\; (FibonacciPositive\left(x, y\right)) \Leftrightarrow ((\forall w \in List\left(Nat\right),\; (\forall a \in Nat,\; (a \in w) \Rightarrow ((a = 1) \lor (a = 2))) \Rightarrow (0 < s\left(x, y, w\right))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.FibonacciPositive` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

If s_w(x⃗ | y⃗) > 0 for all w ∈ 𝕐𝔽, we say that (x⃗, y⃗) is Fibonacci positive. (Definition 4.1, p. 21). The real sequences are indexed from one. The implication restricts the list to letters one and two, and includes the empty word.

**Definition 1.6 (The alternative q-Charlier x sequence).**

$$\forall rho \in Real, q \in Real, k \in Nat,\; xAQC\left(rho, q, k\right) = \frac{q^{(k : Int) - 1} \cdot (1 + rho \cdot q^{(k : Int) - 2} + rho \cdot q^{(k : Int) - 1} - rho \cdot q^{2 \cdot (k : Int) - 2})}{(1 + rho \cdot q^{2 \cdot (k : Int) - 3}) \cdot (1 + rho \cdot q^{2 \cdot (k : Int) - 1})}$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.xAQC` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive: (Conjecture 6.3, p. 31). This is its printed x expression. The sequence is used for k ≥ 1; its extension at zero is immaterial. Each exponent is an integer, so the negative exponents at k=1 are retained.

**Definition 1.7 (The alternative q-Charlier y sequence).**

$$\forall rho \in Real, q \in Real, k \in Nat,\; yAQC\left(rho, q, k\right) = \frac{rho \cdot q^{3 \cdot (k : Int) - 2} \cdot (1 - q^{(k : Int)}) \cdot (1 + rho \cdot q^{(k : Int) - 1})}{(1 + rho \cdot q^{2 \cdot (k : Int)}) \cdot (1 + rho \cdot q^{2 \cdot (k : Int) - 1})^{2} \cdot (1 + rho \cdot q^{2 \cdot (k : Int) - 2})}$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.yAQC` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive: (Conjecture 6.3, p. 31). This is its printed y expression, used for k ≥ 1. The casts from natural k to Int and every denominator factor are displayed.

**Definition 1.8 (Petrov–Scott Conjecture 6.3).**

$$(claim) \Leftrightarrow ((\exists rho \in Real, q \in Real,\; FibonacciPositive\left(xAQC\left(rho, q\right), yAQC\left(rho, q\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.claim` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive: (Conjecture 6.3, p. 31). The specialization is xAQC and yAQC above. Both existential parameters range over Real, and positivity quantifies over every Fibonacci word.

**Theorem 1.9 (Positive determinant from diagonal dominance).**

$$\forall (\iota : Type), [Fintype\left(\iota\right)] [DecidableEq\left(\iota\right)] \forall M \in Matrix\left(\iota, \iota, Real\right),\; (\forall i \in \iota,\; 0 < M\left(i, i\right)) \Rightarrow ((\forall i \in \iota,\; \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{erase}\left(\operatorname{Finset}.\operatorname{univ}, i\right), (fun (j : \iota) \mapsto \Vert M\left(i, j\right) \Vert)\right) < M\left(i, i\right)) \Rightarrow (0 < \operatorname{Matrix}.\operatorname{det}\left(M\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.det_pos_of_dominant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real matrix with positive diagonal entries and strict row diagonal dominance has positive determinant.

**Theorem 1.10 (Positivity at rho = q = one quarter).**

$$\exists rho \in Real, q \in Real,\; FibonacciPositive\left(xAQC\left(rho, q\right), yAQC\left(rho, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/petrov-scott-2026-alternative-q-charlier-fibonacci-positivity-conjecture-6-3` (proved) by `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"petrov-scott-2026-alternative-q-charlier-fibonacci-positivity-conjecture-6-3","declaration_gid":"D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Take rho=q=1/4. A positive diagonal rescaling turns the tridiagonal determinants into strictly diagonally dominant matrices. The normalized sequence is nonnegative, at most 1/4, positive at positive indices, and, from index one onward, contracts by a factor at most 1/2. A continuous deformation to the diagonal matrix preserves nonsingularity and hence the positive determinant sign. Induction on the list then proves positivity for every Fibonacci word, with no bound on its weight.

## References

- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.A`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.B`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.FibonacciPositive`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.claim`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.det_pos_of_dominant`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.result`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.s`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.sAux`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.xAQC`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.yAQC`
