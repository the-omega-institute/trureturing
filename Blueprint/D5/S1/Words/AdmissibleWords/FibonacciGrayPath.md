# FibonacciGrayPath

## Abstract

FibonacciGrayPath

The binary word at dimension d is a function from Fin d to Bool. Adm means that no two consecutive coordinates are true, including the empty word at dimension zero. The reflected list starts with the empty word at dimension zero and with zero and one at dimension one. At dimension d plus two it concatenates zero prefixed to the reversed list at dimension d plus one with ten prefixed to the reversed list at dimension d.

The two blocks have different first bits. The existing admissible splitting equivalence proves completeness, and prefix injectivity proves that every word occurs exactly once. Reversal retains one-bit adjacency inside each block. The head of the list at dimension d plus one is zero prefixed to the last word at dimension d; this identifies the joining words as zero-zero-u and one-zero-u, which differ at their first coordinate.

This is the classical Fibonacci-cube spanning path of Klavzar, Structure of Fibonacci cubes: a survey, Proposition 3.1, author manuscript pages 5-6, DOI 10.1007/s10878-011-9433-z. The survey attributes the construction to Cong, Zheng and Sharma. Only a path is used; no Hamilton cycle or prescribed endpoint is asserted. The existing admissibleWord_card_eq_fib theorem supplies the capacity and is applied through the bijection between list indices and admissible words.

**Definition 1.1 (The reflected list of admissible words).**

$$\begin{aligned}gray: ((d: Nat) \to \operatorname{List}\left((\operatorname{Fin}\left(d\right)) \to (Bool)\right))\\\operatorname{gray}\left(0\right) = [\operatorname{Fin.elim0}]\\\operatorname{gray}\left(1\right) = [(\lambda i \mapsto false), (\lambda i \mapsto true)]\\\forall d: Nat, (\operatorname{gray}\left((d + 2)\right) = (\operatorname{List.map}\left((\operatorname{Fin.cons}\left(false\right)), (\operatorname{List.reverse}\left((\operatorname{gray}\left((d + 1)\right))\right))\right)) ++ (\operatorname{List.map}\left((\lambda w \mapsto \operatorname{Fin.cons}\left(true, (\operatorname{Fin.cons}\left(false, w\right))\right)), (\operatorname{List.reverse}\left((\operatorname{gray}\left(d\right))\right))\right)))\end{aligned}$$

*Formalization.* `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.gray` (`✓ std3`).

*Citation.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

The list has the dependent type List (Fin d to Bool). The empty word forms the list at zero, and the two constant one-bit words form the list at one. The recursion reverses both smaller lists before prefixing false and true-false, respectively, and concatenates the resulting lists.

**Lemma 1.2 (Hamming distance after prefixing).**

$$\forall d: Nat, (\forall a: Bool, (\forall b: Bool, (\forall x: (\operatorname{Fin}\left(d\right)) \to (Bool), (\forall y: (\operatorname{Fin}\left(d\right)) \to (Bool), (\operatorname{hammingDist}\left(\operatorname{Fin.cons}\left(a, x\right), \operatorname{Fin.cons}\left(b, y\right)\right) = (\operatorname{ite}\left((a = b), 0, 1\right)) + \operatorname{hammingDist}\left(x, y\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.hamming_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prefixing two binary words adds one to their Hamming distance exactly when the two prefix bits differ.

**Definition 1.3 (A finite path of admissible words).**

$$\forall d: Nat, (\forall h: Nat, (\operatorname{StagePath}\left(d, h\right):= \{word: (\operatorname{Fin}\left((h + 1)\right)) \to ((\operatorname{Fin}\left(d\right)) \to (Bool));\quad admissible: \forall i: \operatorname{Fin}\left((h + 1)\right), (\operatorname{Adm}\left(d, word\left(i\right)\right));\quad injective: \operatorname{Function.Injective}\left(word\right);\quad consecutive: \forall i: \operatorname{Fin}\left(h\right), (\operatorname{hammingDist}\left(word\left(\operatorname{Fin.castSucc}\left(i\right)\right), word\left(\operatorname{Fin.succ}\left(i\right)\right)\right) = 1)\}))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.StagePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record specifies h plus one admissible words of dimension d, injectivity of the word map, and Hamming distance one between each pair of consecutive indices. Fin.castSucc and Fin.succ embed an edge index into its two endpoints.

**Theorem 1.4 (Distinct one-bit stages).**

$$\forall d: Nat, (\forall h: Nat, ((h + 1 \leq \operatorname{fib}\left(d + 2\right)) \implies (\exists w: (\operatorname{Fin}\left(h + 1\right)) \to ((\operatorname{Fin}\left(d\right)) \to (Bool)), ((\forall i: \operatorname{Fin}\left(h + 1\right), (\operatorname{Adm}\left(d, \operatorname{w}\left(i\right)\right))) \land ((\operatorname{Injective}\left(w\right)) \land (\forall i: \operatorname{Fin}\left(h\right), (\operatorname{hammingDist}\left(\operatorname{w}\left(\operatorname{castSucc}\left(i\right)\right), \operatorname{w}\left(\operatorname{succ}\left(i\right)\right)\right) = 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.exists_stage_path` (`✓ std3`). ∎

*Citation.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

The first h plus one words of the spanning list form the immutable stage path. Capacity alone is not an edge premise: the reflected-list argument establishes every consecutive edge. Dimension zero permits h equal to zero and supplies its unique stage. The h positive edges are indexed by Fin h; castSucc and succ are the two adjacent indices in Fin (h plus one).

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.StagePath`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.exists_stage_path`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.gray`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FibonacciGrayPath.hamming_cons`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
