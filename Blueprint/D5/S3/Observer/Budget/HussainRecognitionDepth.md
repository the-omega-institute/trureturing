# Eventual constancy of deterministic recognition depth

## Abstract

The exact deterministic recognition depth in Hussain's Question 3 stabilizes.

**Definition 1.1 (Source recognition tree).**

$$\begin{aligned}&\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w}),\quad \operatorname{SourceTree}\left(A, Q, S\right):\operatorname{Type}_{\operatorname{max}\left(u, v, w\right)}\\&\operatorname{terminal}:S \to \operatorname{SourceTree}\left(A, Q, S\right)\\&\operatorname{query}:Q \to \forall (E: \operatorname{Set}\left(A\right)),\quad \operatorname{Set.Nonempty}\left(E\right) \to \left(\left(E \to \operatorname{SourceTree}\left(A, Q, S\right)\right) \to \operatorname{SourceTree}\left(A, Q, S\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.SourceTree` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

This inductive tree starts below the source's unique unlabeled root edge. A terminal node carries a state label. At a query node the next subtree is indexed by a member of the nonempty set of present letters.

**Definition 1.2 (Complete paths).**

$$\begin{aligned}&\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w}),\quad \operatorname{CompletePath}:\operatorname{SourceTree}\left(A, Q, S\right) \to \left(\operatorname{List}\left(Q \times A\right) \to \left(S \to \operatorname{Prop}\right)\right)\\&\operatorname{terminal}:\forall (s: S),\quad \operatorname{CompletePath}\left(\operatorname{terminal}\left(s\right), [], s\right)\\&\operatorname{step}:\forall (q: Q)(E: \operatorname{Set}\left(A\right))(h: \operatorname{Set.Nonempty}\left(E\right))(f: E \to \operatorname{SourceTree}\left(A, Q, S\right))(p: \operatorname{List}\left(Q \times A\right))(s: S)(a: E),\quad \operatorname{CompletePath}\left(f\left(a\right), p, s\right) \to \operatorname{CompletePath}\left(\operatorname{query}\left(q, E, h, f\right), (q,a.1) :: p, s\right)\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.CompletePath` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

A complete path ends at a terminal node. Its step constructor prepends the current query and the underlying letter of the selected branch.

**Definition 1.3 (Path compatibility).**

$$\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w})(r: Q \to \left(S \to A\right))(s: S)(p: \operatorname{List}\left(Q \times A\right)),\quad \operatorname{Compatible}\left(r, s, p\right) \Leftrightarrow \forall (e: Q \times A),\quad e \in p \Rightarrow r\left(e.1, s\right) = e.2$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.Compatible` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

A query and answer along the path are compatible with the input state when the readout returns that answer for that query.

**Definition 1.4 (Complete path depth bound).**

$$\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w})(T: \operatorname{SourceTree}\left(A, Q, S\right))(d: \mathbb{N}),\quad \operatorname{DepthLE}\left(T, d\right) \Leftrightarrow \forall (p: \operatorname{List}\left(Q \times A\right))(s: S),\quad \operatorname{CompletePath}\left(T, p, s\right) \Rightarrow \operatorname{List.length}\left(p\right) \le d$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.DepthLE` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

The bound covers every complete path, including paths incompatible with all inputs.

**Definition 1.5 (Recognition on a promise).**

$$\begin{aligned}&\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w})(r: Q \to \left(S \to A\right))(T: \operatorname{SourceTree}\left(A, Q, S\right)),\quad \operatorname{Recognizes}\left(r, T\right) \iff\\&(\forall (s: S),\quad \exists (p: \operatorname{List}\left(Q \times A\right))(b: S),\quad \operatorname{CompletePath}\left(T, p, b\right) \land \operatorname{Compatible}\left(r, s, p\right)) \land\\&(\forall (s: S)(p: \operatorname{List}\left(Q \times A\right))(b: S),\quad \operatorname{CompletePath}\left(T, p, b\right) \Rightarrow \left(\operatorname{Compatible}\left(r, s, p\right) \Rightarrow b = s\right))\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.Recognizes` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Every input has a compatible complete path. Every compatible complete path has that input as its terminal label.

**Definition 1.6 (Feasible source depth).**

$$\begin{aligned}&\forall (A: \operatorname{Type}_{u})(Q: \operatorname{Type}_{v})(S: \operatorname{Type}_{w})(r: Q \to \left(S \to A\right))(d: \mathbb{N}),\quad \operatorname{SourceExactAtDepth}\left(r, d\right) \iff\\&\operatorname{IsEmpty}\left(S\right) \lor (\exists (T: \operatorname{SourceTree}\left(A, Q, S\right)),\quad \operatorname{DepthLE}\left(T, d\right) \land \operatorname{Recognizes}\left(r, T\right))\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.SourceExactAtDepth` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

For an empty state type every natural depth is feasible. Otherwise a source tree must recognize the inputs within the given bound.

**Definition 1.7 (Length promise).**

$$\forall (A: \operatorname{Type}_{u})(L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right))(n: \mathbb{N}),\quad \operatorname{Promise}\left(L, n\right) = \left\{w: \operatorname{Fin}\left(n\right) \to A \mid \operatorname{List.ofFn}\left(w\right) \in L\right\}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.Promise` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

A state is a coordinate array whose associated list is in the language. The brace expression denotes a subtype.

**Definition 1.8 (Coordinate readout).**

$$\forall (A: \operatorname{Type}_{u})(L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right))(n: \mathbb{N})(i: \operatorname{Fin}\left(n\right))(w: \operatorname{Promise}\left(L, n\right)),\quad \operatorname{coordinateReadout}\left(i, w\right) = w.1\left(i\right)$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.coordinateReadout` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

The projection of the promised word is the underlying array.

**Definition 1.9 (Minimum recognition depth).**

$$\forall (A: \operatorname{Type}_{u})[\operatorname{Fintype}\left(A\right)](L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right))(n: \mathbb{N}),\quad \operatorname{recognitionDepth}\left(L, n\right) = \min \left\{d: \mathbb{N} \mid \operatorname{SourceExactAtDepth}\left(\operatorname{coordinateReadout}_{A,L,n}, d\right)\right\}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.recognitionDepth` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Lean's Nat.find takes the proof that some depth is feasible for this readout. Its value is zero on the empty promise.

**Definition 1.10 (Closure under scattered subwords).**

$$\forall (A: \operatorname{Type}_{u})(L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right)),\quad \operatorname{SubwordClosed}\left(L\right) \Leftrightarrow \forall (u: \operatorname{List}\left(A\right))(v: \operatorname{List}\left(A\right)),\quad \operatorname{List.Sublist}\left(u, v\right) \Rightarrow \left(v \in L \Rightarrow u \in L\right)$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.SubwordClosed` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

List.Sublist allows deletions at arbitrary positions.

**Definition 1.11 (Homogeneity exponent set).**

$$\forall (A: \operatorname{Type}_{u})(L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right)),\quad \operatorname{HomExponents}\left(L\right) = \left\{e: \mathbb{N} \mid \exists (a: A)(b: A),\quad a \ne b \land \operatorname{List.append}\left(\operatorname{List.append}\left(\operatorname{List.replicate}\left(e, a\right), [b]\right), \operatorname{List.replicate}\left(e, a\right)\right) \in L\right\}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.HomExponents` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Definition 9 includes every natural exponent for which the two equal-letter blocks with a distinct letter between them form a word in the language.

**Definition 1.12 (Heterogeneity exponent set).**

$$\forall (A: \operatorname{Type}_{u})(L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right)),\quad \operatorname{HetExponents}\left(L\right) = \left\{e: \mathbb{N} \mid \exists (a: A)(b: A),\quad a \ne b \land \operatorname{List.append}\left(\operatorname{List.replicate}\left(e, a\right), \operatorname{List.replicate}\left(e, b\right)\right) \in L\right\}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.HetExponents` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Definition 10 includes every natural exponent for which the two distinct-letter blocks form a word in the language.

**Definition 1.13 (Question 3).**

$$\operatorname{claim} \Leftrightarrow \begin{aligned}&\forall (A: \operatorname{Type}_{u})[\operatorname{Fintype}\left(A\right)](L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right)),\quad 2 \le \operatorname{Fintype.card}\left(A\right) \longrightarrow\\&\operatorname{SubwordClosed}\left(L\right) \longrightarrow\\&\operatorname{Set.Finite}\left(\operatorname{HomExponents}\left(L\right)\right) \longrightarrow\\&\operatorname{Set.Finite}\left(\operatorname{HetExponents}\left(L\right)\right) \longrightarrow\\&\exists (N: \mathbb{N})(d: \mathbb{N}),\quad 1 \le N \land (\forall (n: \mathbb{N}),\quad N \le n \Rightarrow \operatorname{recognitionDepth}\left(L, n\right) = d)\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.claim` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

The two finite exponent sets define the source's Hom and Het dimensions. An empty exponent set gives dimension zero.

**Theorem 1.14 (The exact minimum depth stabilizes).**

$$\begin{aligned}&\forall (A: \operatorname{Type}_{u})[\operatorname{Fintype}\left(A\right)](L: \operatorname{Set}\left(\operatorname{List}\left(A\right)\right)),\quad 2 \le \operatorname{Fintype.card}\left(A\right) \longrightarrow\\&\operatorname{SubwordClosed}\left(L\right) \longrightarrow\\&\operatorname{Set.Finite}\left(\operatorname{HomExponents}\left(L\right)\right) \longrightarrow\\&\operatorname{Set.Finite}\left(\operatorname{HetExponents}\left(L\right)\right) \longrightarrow\\&\exists (N: \mathbb{N})(d: \mathbb{N}),\quad 1 \le N \land (\forall (n: \mathbb{N}),\quad N \le n \Rightarrow \operatorname{recognitionDepth}\left(L, n\right) = d)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/HussainRecognitionDepth.result` (`✓ std3`). ∎

*Resolves.* `Problems/hussain-2026-recognition-depth-question-3` (proved) by `D5/S3/Observer/Budget/HussainRecognitionDepth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hussain-2026-recognition-depth-question-3","declaration_gid":"D5/S3/Observer/Budget/HussainRecognitionDepth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Below the unique unlabeled root edge, a query node has a nonempty set of distinct letter branches, and each leaf is labeled by a promised word. Each promised input has a compatible complete path, and every compatible path returns that input. The depth bound applies to every complete path. The empty promise has minimum depth zero.

Complete missing branches by terminating them immediately. Two promised inputs with the same transcript then reach the same leaf. In reverse, label a protocol leaf by the unique promised input reaching it, or by an arbitrary promised word on unreachable leaves. These constructions preserve each depth bound. Querying every coordinate supplies a finite bound, so the two minimum depths exist and agree.

Given upper bounds m and h for the Hom and Het exponents, put c equal to one plus the alphabet size times the larger bound. For a word of length n+1 with n at least 2c+1, the regions strictly before and after the positions c and c+1 each contain at least c letters. Each region contains at least max(m,h)+1 copies of one letter. The Het bound forces those letters to coincide. The Hom bound forces each intervening letter to be that same letter.

Delete coordinate c+1. The shorter word belongs to the shorter promise, and inserting the retained letter at coordinate c reconstructs the original word. Relabel the queries of a shorter protocol by the surviving coordinates. This preserves the depth bound and all transcripts on the deletion image, which gives the inequality $\operatorname{recognitionDepth}\left(L, n + 1\right) \le \operatorname{recognitionDepth}\left(L, n\right)$ on the tail. A nonincreasing natural-valued sequence is eventually constant.

## References

- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.Compatible`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.CompletePath`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.DepthLE`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.HetExponents`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.HomExponents`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.Promise`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.Recognizes`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.SourceExactAtDepth`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.SourceTree`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.SubwordClosed`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.claim`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.coordinateReadout`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.recognitionDepth`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.result`
- Dependency: [D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound](WorstCaseDepthInformationLowerBound.md)
