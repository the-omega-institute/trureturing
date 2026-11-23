# Eventual constancy of deterministic recognition depth

## Abstract

The exact deterministic recognition depth in Hussain's Question 3 stabilizes.

**Definition 1.1 (Question 3).**

$$claim \Leftrightarrow \left(\forall A \in \operatorname{FiniteAlphabet},\; \forall L \in \operatorname{Languages}\left(A\right),\; (2 \le \lvert A\rvert \land \left(\operatorname{SubwordClosed}\left(L\right) \land \left(\operatorname{Finite}\left(\operatorname{HomExponents}\left(L\right)\right) \land \operatorname{Finite}\left(\operatorname{HetExponents}\left(L\right)\right)\right)\right)) \Rightarrow \left(\exists N \in \mathbb{N},\; \exists d \in \mathbb{N},\; 1 \le N \land \left(\forall n \in \mathbb{N},\; N \le n \Rightarrow \operatorname{depth}\left(L, n\right) = d\right)\right)\right)$$

*Formalization.* `D5/S3/Observer/Budget/HussainRecognitionDepth.claim` (`✓ std3`).

*Citation.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

The alphabet A is finite, L is a language over A, and depth(L,n) is the minimum deterministic recognition depth on the length-n promise. The two finite exponent sets define the source's Hom and Het dimensions. An empty exponent set gives dimension zero.

**Theorem 1.2 (The exact minimum depth stabilizes).**

$$\forall A \in \operatorname{FiniteAlphabet},\; \forall L \in \operatorname{Languages}\left(A\right),\; (2 \le \lvert A\rvert \land \left(\operatorname{SubwordClosed}\left(L\right) \land \left(\operatorname{Finite}\left(\operatorname{HomExponents}\left(L\right)\right) \land \operatorname{Finite}\left(\operatorname{HetExponents}\left(L\right)\right)\right)\right)) \Rightarrow \left(\exists N \in \mathbb{N},\; \exists d \in \mathbb{N},\; 1 \le N \land \left(\forall n \in \mathbb{N},\; N \le n \Rightarrow \operatorname{depth}\left(L, n\right) = d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/HussainRecognitionDepth.result` (`✓ std3`). ∎

*Resolves.* `Problems/hussain-2026-recognition-depth-question-3` (proved) by `D5/S3/Observer/Budget/HussainRecognitionDepth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hussain-2026-recognition-depth-question-3","declaration_gid":"D5/S3/Observer/Budget/HussainRecognitionDepth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shahid Hussain (2026). *Decision trees for subword-closed languages over arbitrary finite alphabets*. DOI: [10.48550/arXiv.2611.27454](https://doi.org/10.48550/arXiv.2611.27454). URL: <https://arxiv.org/abs/2611.27454v1>.

*Commentary.*

Below the unique unlabeled root edge, a query node has a nonempty set of distinct letter branches, and each leaf is labeled by a promised word. Each promised input has a compatible complete path, and every compatible path returns that input. The depth bound applies to every complete path. The empty promise has minimum depth zero.

Complete missing branches by terminating them immediately. Two promised inputs with the same transcript then reach the same leaf. In reverse, label a protocol leaf by the unique promised input reaching it, or by an arbitrary promised word on unreachable leaves. These constructions preserve each depth bound. Querying every coordinate supplies a finite bound, so the two minimum depths exist and agree.

Given upper bounds m and h for the Hom and Het exponents, put c equal to one plus the alphabet size times the larger bound. For a word of length n+1 with n at least 2c+1, the regions strictly before and after the positions c and c+1 each contain at least c letters. Each region contains at least max(m,h)+1 copies of one letter. The Het bound forces those letters to coincide. The Hom bound forces each intervening letter to be that same letter.

Delete coordinate c+1. The shorter word belongs to the shorter promise, and inserting the retained letter at coordinate c reconstructs the original word. Relabel the queries of a shorter protocol by the surviving coordinates. This preserves the depth bound and all transcripts on the deletion image, which gives the inequality $\operatorname{depth}\left(L, n + 1\right) \le \operatorname{depth}\left(L, n\right)$ on the tail. A nonincreasing natural-valued sequence is eventually constant.

## References

- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.claim`
- Truth anchor: `D5/S3/Observer/Budget/HussainRecognitionDepth.result`
- Dependency: [D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound](WorstCaseDepthInformationLowerBound.md)
