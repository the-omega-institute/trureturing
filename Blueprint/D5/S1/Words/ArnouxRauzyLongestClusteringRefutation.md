# Longest clustering words in Arnoux–Rauzy languages

## Abstract

A longer perfectly clustering Arnoux–Rauzy factor refutes the Ferenczi–Zamboni conjecture.

**Definition 1.1 (Arnoux–Rauzy blocks).**

$$\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; \forall k \in \mathbb{N},\; \forall x \in Fin\left(3\right),\; arBlocks\left(d, k, x\right) = \operatorname{Nat.rec}\left(\operatorname{fun} (x : Fin\left(3\right)) \mapsto \operatorname{List.singleton}\left(x\right), \operatorname{fun} (j : \mathbb{N}) \mapsto \operatorname{fun} (f : (Fin\left(3\right)) \to (List\left(Fin\left(3\right)\right))) \mapsto \operatorname{Function.update}\left(\operatorname{fun} (x : Fin\left(3\right)) \mapsto \operatorname{List.append}\left(f\left(x\right), f\left(d\left(j\right)\right)\right), d\left(j\right), f\left(d\left(j\right)\right)\right), k, x\right)$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.arBlocks` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

The blocks are generated from the three initial letters by the source's rule at each stage.

**Definition 1.2 (Infinitely often directives).**

$$\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; (InfOften\left(d\right)) \Leftrightarrow (\forall x \in Fin\left(3\right),\; \forall N \in \mathbb{N},\; \exists k \in \mathbb{N},\; (N \le k) \land (d\left(k\right) = x))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.InfOften` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

Every letter occurs at or after every prescribed stage.

**Definition 1.3 (The condition (Rabc)).**

$$\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; (Rabc\left(d\right)) \Leftrightarrow ((d\left(0\right) = 0) \land (\exists k \in \mathbb{N},\; (d\left(k\right) \ne 0) \land ((\forall j \in \mathbb{N},\; (j < k) \Rightarrow (d\left(j\right) = 0)) \land (d\left(k\right) = 1))))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.Rabc` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

The source condition says: “the rule at stage 0 is (a), and the first rule different from (a) is (b)”.

**Definition 1.4 (Arnoux–Rauzy language).**

$$\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; arLang\left(d\right) = \{w:List\left(Fin\left(3\right)\right) | \exists k \in \mathbb{N},\; \exists x \in Fin\left(3\right),\; \operatorname{List.IsInfix}\left(w, arBlocks\left(d, k, x\right)\right)\}$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.arLang` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

A language contains the finite factors of its directive blocks.

**Definition 1.5 (Standard Arnoux–Rauzy words).**

$$\forall w \in List\left(Fin\left(3\right)\right),\; (IsStandardAR\left(w\right)) \Leftrightarrow (\exists d \in (\mathbb{N}) \to (Fin\left(3\right)),\; (InfOften\left(d\right)) \land (\exists k \in \mathbb{N},\; \exists x \in Fin\left(3\right),\; w = arBlocks\left(d, k, x\right)))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.IsStandardAR` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

A standard word is one of the directive blocks for a directive using every rule infinitely often.

**Definition 1.6 (Conjugacy to a standard word).**

$$\forall w \in List\left(Fin\left(3\right)\right),\; (ConjugateToStandard\left(w\right)) \Leftrightarrow (\exists r \in \mathbb{N},\; IsStandardAR\left(\operatorname{List.rotate}\left(w, r\right)\right))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.ConjugateToStandard` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

A word is conjugate to a standard word when one of its rotations is standard.

**Definition 1.7 (The Burrows–Wheeler transform).**

$$\forall o \in \operatorname{Equiv.Perm}\left(Fin\left(3\right)\right),\; \forall w \in List\left(Fin\left(3\right)\right),\; bwt\left(o, w\right) = \begin{aligned}\operatorname{let}  rs : List\left(List\left(Fin\left(3\right)\right)\right) := \operatorname{List.map}\left(\operatorname{fun} (i : \mathbb{N}) \mapsto \operatorname{List.rotate}\left(w, i\right), \operatorname{List.range}\left(\operatorname{List.length}\left(w\right)\right)\right);\\\begin{aligned}\operatorname{let}  sr : List\left(List\left(Fin\left(3\right)\right)\right) := \operatorname{List.insertionSort}\left(\operatorname{fun} (a : List\left(Fin\left(3\right)\right)) \mapsto \operatorname{fun} (b : List\left(Fin\left(3\right)\right)) \mapsto \operatorname{Bool.not}\left(\operatorname{List.lex}\left(b, a, \operatorname{fun} (x : Fin\left(3\right)) \mapsto \operatorname{fun} (y : Fin\left(3\right)) \mapsto decide\left(o\left(x\right) < o\left(y\right)\right)\right)\right) = true, rs\right);\\\operatorname{List.filterMap}\left(\operatorname{fun} (l : List\left(Fin\left(3\right)\right)) \mapsto \operatorname{match} l \operatorname{with} \begin{aligned}| [] \mapsto none\\| \operatorname{List.cons}\left(a, as\right) \mapsto some\left(\operatorname{List.getLast}\left(\operatorname{List.cons}\left(a, as\right)\right)\right)\end{aligned}, sr\right)\end{aligned}\end{aligned}$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.bwt` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

The transform is the last column of the sorted conjugates. Bool.not of reverse List.lex compares permutation ranks; List.insertionSort orders the rotations and List.getLast? supplies the last column.

**Definition 1.8 (Clustering).**

$$\forall w \in List\left(Fin\left(3\right)\right),\; (IsClustering\left(w\right)) \Leftrightarrow (\exists o \in \operatorname{Equiv.Perm}\left(Fin\left(3\right)\right),\; \exists pi \in \operatorname{Equiv.Perm}\left(Fin\left(3\right)\right),\; (pi \ne 1) \land (bwt\left(o, w\right) = \operatorname{List.flatMap}\left(\operatorname{fun} (l : Fin\left(3\right)) \mapsto \operatorname{List.replicate}\left(\operatorname{List.count}\left(pi\left(l\right), w\right), pi\left(l\right)\right), \operatorname{List.ofFn}\left(\operatorname{Equiv.symm}\left(o\right)\right)\right)))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.IsClustering` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

The source calls a word clustering when its transform is a concatenation of constant permutation blocks, and perfectly clustering for the symmetric permutation.

**Definition 1.9 (The word from Proposition 14).**

$$\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; propLongWord\left(d\right) = \begin{aligned}\operatorname{let}  firstAt : ((\mathbb{N}) \to (Fin\left(3\right))) \to ((Fin\left(3\right)) \to ((\mathbb{N}) \to (\mathbb{N}))) := \operatorname{fun} (d : (\mathbb{N}) \to (Fin\left(3\right))) \mapsto \operatorname{fun} (x : Fin\left(3\right)) \mapsto \operatorname{fun} (start : \mathbb{N}) \mapsto \operatorname{if} h : \exists k \in \mathbb{N},\; (start \le k) \land (d\left(k\right) = x) \operatorname{then} \operatorname{Nat.find}\left(h\right) \operatorname{else} 0;\\\begin{aligned}\operatorname{let}  lam2 : \mathbb{N} := firstAt\left(d, 2, 0\right);\\\begin{aligned}\operatorname{let}  mua : \mathbb{N} := firstAt\left(d, 0, (lam2) + (1)\right);\\\begin{aligned}\operatorname{let}  mub : \mathbb{N} := firstAt\left(d, 1, (lam2) + (1)\right);\\\begin{aligned}\operatorname{let}  muy : \mathbb{N} := \operatorname{if} (mua < mub) \operatorname{then} mub \operatorname{else} mua;\\\begin{aligned}\operatorname{let}  mu : \mathbb{N} := \operatorname{Nat.findGreatest}\left(\operatorname{fun} (j : \mathbb{N}) \mapsto d\left((j) - (1)\right) \ne d\left((muy) - (1)\right), muy\right);\\\begin{aligned}\operatorname{let}  sb : List\left(List\left(Fin\left(3\right)\right)\right) := \operatorname{List.insertionSort}\left(\operatorname{fun} (u : List\left(Fin\left(3\right)\right)) \mapsto \operatorname{fun} (v : List\left(Fin\left(3\right)\right)) \mapsto \operatorname{List.length}\left(u\right) \le \operatorname{List.length}\left(v\right), \operatorname{List.ofFn}\left(arBlocks\left(d, muy\right)\right)\right);\\\begin{aligned}\operatorname{let}  S : List\left(Fin\left(3\right)\right) := \operatorname{List.getD}\left(sb, 0, []\right);\\\begin{aligned}\operatorname{let}  M : List\left(Fin\left(3\right)\right) := \operatorname{List.getD}\left(sb, 1, []\right);\\\operatorname{List.append}\left(\operatorname{List.flatten}\left(\operatorname{List.replicate}\left(((muy) - (mu)) + (1), S\right)\right), M\right)\end{aligned}\end{aligned}\end{aligned}\end{aligned}\end{aligned}\end{aligned}\end{aligned}\end{aligned}\end{aligned}$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.propLongWord` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

The displayed word is the source's construction from the shortest and middle blocks at the stages determined by (Rabc).

**Definition 1.10 (Ferenczi–Zamboni Conjecture 1).**

$$(claim) \Leftrightarrow (\forall d \in (\mathbb{N}) \to (Fin\left(3\right)),\; (Rabc\left(d\right)) \Rightarrow ((InfOften\left(d\right)) \Rightarrow (\forall w \in List\left(Fin\left(3\right)\right),\; (w \in arLang\left(d\right)) \Rightarrow ((IsClustering\left(w\right)) \Rightarrow ((ConjugateToStandard\left(w\right)) \Rightarrow (\operatorname{List.length}\left(w\right) \le \operatorname{List.length}\left(propLongWord\left(d\right)\right)))))))$$

*Formalization.* `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.claim` (`✓ std3`).

*Citation.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

Conjecture 1 states verbatim: “In a given AR language Λ satisfying (Rabc), the word in Proposition [14] is the longest clustering word, or, if this fails, the longest clustering word conjugate to a standard AR word.” The formal claim is the weaker second alternative, with Fin 3 letters encoded as 0, 1, and 2 and word length measured by List.length.

**Theorem 1.11 (A longer perfectly clustering factor exists).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering` (refuted) by `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering","declaration_gid":"D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sebastien Ferenczi; Luca Q. Zamboni (2024). *Clustering and Arnoux-Rauzy words*. DOI: [10.1016/j.aam.2023.102621](https://doi.org/10.1016/j.aam.2023.102621). URL: <https://arxiv.org/abs/2305.18986v1>.

*Commentary.*

For the directive abcacba(abc)ω, the factor U₁ has length 43, is in the Arnoux–Rauzy language, is perfectly clustering, and is conjugate to a standard word. Its BWT is b¹²c⁷a²⁴ for a<c<b. The Proposition 14 word has length 40, so this factor refutes the asserted longest-word bound. The general value of the longest clustering word remains open.

## References

- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.ConjugateToStandard`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.InfOften`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.IsClustering`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.IsStandardAR`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.Rabc`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.arBlocks`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.arLang`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.bwt`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.claim`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.propLongWord`
- Truth anchor: `D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result`
