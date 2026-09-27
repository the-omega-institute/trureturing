# A Two-Term Refutation of the Gijswijt Merge Identity

## Abstract

The starting sequence 1 2 refutes the merge identity once a 1 is allowed inside S.

**Definition 1.1 (Ending in a repeated suffix).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall p \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (\operatorname{IsCurlAt}\left(s, p, k\right)) \Leftrightarrow ((0 < p) \land ((p \cdot k \le \operatorname{length}\left(s\right)) \land (\operatorname{drop}\left(s, \operatorname{length}\left(s\right) - p \cdot k\right) = \operatorname{flatten}\left(\operatorname{replicate}\left(k, \operatorname{drop}\left(s, \operatorname{length}\left(s\right) - p\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.IsCurlAt` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

The last p k entries of s are k consecutive copies of the last p entries. Taking the suffix of length p as the repeated block loses nothing: any way of writing s as a prefix followed by k copies of a nonempty block of length p has that block equal to the suffix of length p.

**Definition 1.2 (Writing s as a prefix and k repetitions).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; (\operatorname{IsCurl}\left(s, k\right)) \Leftrightarrow (\exists p \in \mathrm{Nat},\; (p \le \operatorname{length}\left(s\right)) \land (\operatorname{IsCurlAt}\left(s, p, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.IsCurl` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

Some nonempty block, of length at most the length of s, is repeated k times at the end of s.

**Definition 1.3 (The curling number).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{cn}\left(s\right) = \operatorname{max}\left(1, \operatorname{sup}\left(\{k: \mathrm{Nat} \mid (1 \le k) \land ((k \le \operatorname{length}\left(s\right)) \land (\operatorname{IsCurl}\left(s, k\right)))\}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.cn` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

The source defines the curling number of a sequence as the greatest k for which the sequence can be written as a prefix followed by k copies of a nonempty block. Every nonempty sequence admits k equal to one, so the supremum is attained and is at least one; the empty sequence admits no such k at all and the value one there is a convention that no statement below relies on.

**Definition 1.4 (One step of the process).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{step}\left(s\right) = \operatorname{append}\left(s, \operatorname{singleton}\left(\operatorname{cn}\left(s\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.step` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

The source builds its sequences by repeatedly appending the curling number of what has been written so far.

**Definition 1.5 (The sequence after t steps).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall t \in \mathrm{Nat},\; \operatorname{iter}\left(0, s\right) = s   \operatorname{iter}\left(t + 1, s\right) = \operatorname{step}\left(\operatorname{iter}\left(t, s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.iter` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

The source writes this as S with subscript t, the result of t appending steps applied to the starting sequence.

**Definition 1.6 (A single term of the continuation).**

$$\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall n \in \mathrm{Nat},\; \operatorname{term}\left(s, n\right) = \operatorname{getD}\left(\operatorname{iter}\left(n + 1, s\right), n, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.term` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

Entries are counted from zero. Performing n plus one steps produces a sequence of length greater than n, so the entry at position n is present and the default value is never used.

**Definition 1.7 (Gijswijt's sequence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{G}\left(n\right) = \operatorname{term}\left(\operatorname{singleton}\left(1\right), n\right)$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.G` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

The source's G, the continuation of the one-element sequence whose only entry is one. Its first eleven entries are 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, and its first entry equal to four stands at position 220.

**Definition 1.8 (The weakened merge identity).**

$$(claim) \Leftrightarrow (\forall s \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall t \in \mathrm{Nat},\; (1 \in s) \Rightarrow ((\operatorname{getLast}\left(s\right) \ne 1) \Rightarrow ((\operatorname{cn}\left(\operatorname{iter}\left(t, s\right)\right) = 1) \Rightarrow ((\forall r \in \mathrm{Nat},\; (r < t) \Rightarrow (\operatorname{cn}\left(\operatorname{iter}\left(r, s\right)\right) \ne 1)) \Rightarrow (\forall m \in \mathrm{Nat},\; \operatorname{term}\left(s, \operatorname{length}\left(s\right) + t + m\right) = \operatorname{G}\left(m\right))))))$$

*Formalization.* `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.claim` (`✓ std3`).

*Citation.* Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks (2013). *On curling numbers of integer sequences*. DOI: [10.48550/arXiv.1212.6102](https://doi.org/10.48550/arXiv.1212.6102). URL: <https://arxiv.org/abs/1212.6102v3>.

*Commentary.*

Theorem 23 of the source reads verbatim: "Assume the curling number conjecture is true. Let S be an initial sequence not containing a 1, let S(e) be its 'extension' (defined in section 1), and let S(inf) be its infinite continuation. Then S(inf) = S(e) G." The last sentence of that section reads verbatim: "We do not know if the theorem is still true if S is allowed to contain a 1 but does not end with 1." The statement displayed here is that weakened form. The tail length t carries the hypothesis that the extension exists, which is what the curling number conjecture would otherwise supply, so nothing here depends on that conjecture. The equality of infinite sequences is read off term by term.

**Theorem 1.9 (The weakened merge identity is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chaffin-sloane-gijswijt-merge-refutation` (refuted) by `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chaffin-sloane-gijswijt-merge-refutation","declaration_gid":"D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take S to be 1 2. It contains a 1 and does not end with 1. The curling number of 1 2 is one, so its tail length is zero and its extension is 1 2 itself. The next entries are computed in turn: the curling number of 1 2 is 1, of 1 2 1 is 1, of 1 2 1 1 is 2, of 1 2 1 1 2 is 1, and of 1 2 1 1 2 1 is 2, the last because that sequence is the square of 1 2 1. So the continuation opens 1 2 1 1 2 1 2 2 2 3 while the extension followed by G opens 1 2 1 1 2 1 1 2 2 2, and the two differ at the seventh entry. The published argument breaks at exactly that point: it writes the continuation as W times X T to the power n followed by n, with the extension equal to W X and T a prefix of G, and for n equal to two it concludes from the first entry of X not being one. Here W is empty, X is 1 2, T is 1, and the first entry of X is one. Since the source states Theorem 23 under the curling number conjecture, its weakened form as an implication can still hold vacuously; what fails is the consequent, so that weakened form is equivalent to the negation of the curling number conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.G`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.IsCurl`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.IsCurlAt`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.cn`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.iter`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.step`
- Truth anchor: `D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.term`
