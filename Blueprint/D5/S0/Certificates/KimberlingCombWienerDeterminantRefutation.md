# The OEIS A192023 Comb Wiener-Index Conjecture

## Abstract

At n = 3, the printed comb Wiener-index and determinant-count conjecture fails.

**Definition 1.1 (The comb-shaped graph).**

$$\begin{aligned}\forall m: \mathrm{Nat},\\\operatorname{comb}\left(m\right): \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right)\right)\right) = SimpleGraph.fromRel\left((\lambda u \mapsto Sum.elim\left((\lambda i \mapsto Sum.elim\left((\lambda j \mapsto i.val + 1 = j.val), (\lambda j \mapsto i = j)\right)), (\lambda _ \mapsto (\lambda _ \mapsto False)), u\right))\right)\end{aligned}$$

*Formalization.* `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.comb` (`✓ std3`).

*Citation.* Clark Kimberling (2012). *OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes*. URL: <https://oeis.org/A192023>.

*Commentary.*

The vertices are Fin m on the spine and a second copy Fin m of pendant vertices. The fromRel relation joins spine index i to spine index j when i.val + 1 = j.val and joins spine i to pendant j when i = j. fromRel adds reverse edges and excludes loops.

**Definition 1.2 (The Wiener index).**

$$\begin{aligned}\forall \{V: Type*\} [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)],\\\forall G: \operatorname{SimpleGraph}\left(V\right),\\\operatorname{wienerIndex}\left(G\right): \mathrm{Nat} = \sum_{p \in (Finset.univ: \operatorname{Finset}\left(\operatorname{Sym2}\left(V\right)\right)).filter\left((\lambda p \mapsto \neg p.IsDiag)\right)} Sym2.lift\left(\langle G.dist, (\lambda u v \mapsto G.dist_{comm}\left((u := u), (v := v)\right)) \rangle, p\right)\end{aligned}$$

*Formalization.* `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.wienerIndex` (`✓ std3`).

*Citation.* Clark Kimberling (2012). *OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes*. URL: <https://oeis.org/A192023>.

*Commentary.*

For a finite vertex type V with decidable equality, the filter removes diagonal pairs from the symmetric square Sym2 V. Each remaining unordered pair occurs once; Sym2.lift evaluates its graph distance, using dist_comm for independence of the order of endpoints.

**Definition 1.3 (Determinant-constrained matrix count).**

$$\forall n: \mathrm{Nat}, \operatorname{matrixCount}\left(n\right): \mathrm{Nat} = Finset.card\left(Finset.filter\left((Finset.Icc\left((1: \mathbb{Z}), (n: \mathbb{Z})\right) \times^{s} (Finset.Icc\left((1: \mathbb{Z}), (n: \mathbb{Z})\right) \times^{s} (Finset.Icc\left((1: \mathbb{Z}), (n: \mathbb{Z})\right) \times^{s} Finset.Icc\left((1: \mathbb{Z}), (n: \mathbb{Z})\right)))), (\lambda q \mapsto q.1 \cdot q.2.2.2 - q.2.1 \cdot q.2.2.1 = 2 \cdot (n: \mathbb{Z}))\right)\right)$$

*Formalization.* `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.matrixCount` (`✓ std3`).

*Citation.* Clark Kimberling (2012). *OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes*. URL: <https://oeis.org/A192023>.

*Commentary.*

The nested finite Cartesian product has row-major coordinates q = (a,(b,(c,d))) and denotes the matrix [[a,b],[c,d]]. Matrix.det_fin_two is the row-major formula a*d-b*c. The integer interval Icc(1, n) taken four times contains 1 through n; the filter requires determinant 2n.

**Definition 1.4 (The printed matrix-count conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; 2 < n \Rightarrow \operatorname{wienerIndex}\left(\operatorname{comb}\left(n - 2\right)\right) = \operatorname{matrixCount}\left(n\right))$$

*Formalization.* `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.claim` (`✓ std3`).

*Citation.* Clark Kimberling (2012). *OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes*. URL: <https://oeis.org/A192023>.

*Commentary.*

For every natural n greater than two, A192023(n-2) denotes the Wiener index of the comb on 2(n-2) vertices, not an assumed evaluation of its closed formula. The comparison counts exactly the matrices in the printed comment.

**Theorem 1.5 (The printed conjecture fails at n = 3).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a192023-comb-wiener-determinant-refutation` (refuted) by `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a192023-comb-wiener-determinant-refutation","declaration_gid":"D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2012). *OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes*. URL: <https://oeis.org/A192023>.

*Commentary.*

The comb with two vertices is a single edge, so its only unordered pair contributes distance one. For n = 3, entries in {1,2,3} and ad-bc = 6 force a = d = 3 and bc = 3. Exactly the matrices [[3,1],[3,3]] and [[3,3],[1,3]] qualify, giving count two. One differs from two. This refutes only the printed comment and asserts no corrected statement.

## References

- Truth anchor: `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.claim`
- Truth anchor: `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.comb`
- Truth anchor: `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.matrixCount`
- Truth anchor: `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.result`
- Truth anchor: `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.wienerIndex`
