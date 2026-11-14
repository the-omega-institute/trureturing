# Christoffel words need not attain the Lyndon-factor minimum

## Abstract

A binary Lyndon word of length 506 has sixteen distinct Lyndon factors, fewer than every Christoffel word of that length.

**Definition 1.1 (Lower Christoffel words).**

$$\forall p: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{christoffel}\left(p, n\right) = (i: \operatorname{Fin}\left(n\right) \mapsto \operatorname{if} (\operatorname{Nat.sub}\left(\operatorname{Nat.div}\left(((i: \mathbb{N}) + 1) \cdot p, n\right), \operatorname{Nat.div}\left((i: \mathbb{N}) \cdot p, n\right)\right) = 1) \operatorname{then} 1 \operatorname{else} 0)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.christoffel` (`✓ std3`).

*Citation.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

Section 5, p. 8: “The so-called Christoffel word of slope p/q beginning with the letter a is the unique Sturmian Lyndon word over {a, b} of length q containing p occurrences of the letter b, given by:” followed by aPal(v)b. Here a = 0 < 1 = b, the denominator is n, and the lower mechanical word uses natural-number floor division and truncated subtraction. The parameters used in the question satisfy 0 < p < n and Nat.Coprime p n. The formula reproduces the source's slopes 3/11, 5/11, and 11/28.

**Definition 1.2 (Open Problem 1).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\exists p: \mathbb{N}, (0 < p) \land ((p < n) \land ((\operatorname{Nat.Coprime}\left(p, n\right)) \land (\forall k: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right), (\operatorname{IsLyndon}\left(\operatorname{List.ofFn}\left(w\right)\right)) \Rightarrow (\operatorname{distinctLyndon}\left(\operatorname{christoffel}\left(p, n\right)\right) \le \operatorname{distinctLyndon}\left(w\right)))))))$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.claim` (`✓ std3`).

*Citation.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

Section 6, p. 9: “Is it true that the minimum number of distinct Lyndon factors over all Lyndon words of the same length is attained by at least one Christoffel word of that length?” The proposition is the affirmative assertion for every n ≥ 2, with competitors over every finite ordered alphabet Fin k. The count is of distinct contiguous factors, including single letters and the whole word.

**Theorem 1.3 (A negative answer at length 506).**

$$\neg (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\exists p: \mathbb{N}, (0 < p) \land ((p < n) \land ((\operatorname{Nat.Coprime}\left(p, n\right)) \land (\forall k: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right), (\operatorname{IsLyndon}\left(\operatorname{List.ofFn}\left(w\right)\right)) \Rightarrow (\operatorname{distinctLyndon}\left(\operatorname{christoffel}\left(p, n\right)\right) \le \operatorname{distinctLyndon}\left(w\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/glen-simpson-smyth-2017-lyndon-factors-open-problem-1` (refuted) by `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"glen-simpson-smyth-2017-lyndon-factors-open-problem-1","declaration_gid":"D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

Let U = aabaabab, V = aabab, v = ababbababbabbababbabb, and replace each a in v by UUV and each b by UUVV. The resulting word has length 506 and sixteen distinct Lyndon factors. A suffix comparison certifies that it is Lyndon. Compressed intervals of rejected suffixes certify the upper count, and sixteen distinct occurrences certify the lower count. For each positive numerator less than 506 and coprime to 506, seventeen distinct Lyndon-factor occurrences certify the Christoffel lower bound. Thus every Christoffel competitor has at least seventeen distinct factors. The argument does not determine the global minimum or the first counterexample length. Glen's 2018 41ACCMCC talk, slide 19, announces an affirmative answer; that announcement conflicts with this counterexample, and its proof is unavailable in the supplied material. The source's Theorem 8 concerns the Christoffel family alone and does not require the assertion refuted here.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.christoffel`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.claim`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.result`
- Dependency: [D5/S1/Words/Complexity/LyndonFactorTransport](LyndonFactorTransport.md)
