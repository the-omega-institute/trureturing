# Uniform two-word projection equality and vertex extension

This volume is reference input. Lean declarations and their checked proof terms carry the mathematical truth. The atomizer is `generic-v1`. Existing text is append-only; corrections and additions belong after the final append anchor.

## Source model

For a finite set $V$, a simple graph $G$ on $V$, and a positive integer $k$, write $R_k(G)$ if there are actual finite words $w,v\in V^*$ such that every vertex occurs exactly $k$ times in each word and, for every distinct $a,b\in V$, adjacency is equivalent to equality of the two actual projections $\pi_{a,b}(w)=\pi_{a,b}(v)$. The projection deletes every other letter, preserving order and repetitions. Positivity ensures that both alphabets are exactly $V$.

The source is Adamson, Dietz, Fleischmann, Huch and Sacher, *2-word-π-representable Graphs*, arXiv:2605.27183v1, Definitions 1 and 14. Their Remark 16 gives inclusion $\mathcal G_k\subseteq\mathcal G_{k+1}$; Theorem 29 gives fixed-$k$ nonuniversality; Conjecture 31 asks whether every positive-$k$ adjacent inclusion is proper. Equality of projections differs from single-word alternation and from unions of word-represented graphs.

## Prescribed-neighborhood extension

**theorem 2.1 (Uniform extension by an arbitrary fresh vertex).** For every finite vertex set $V$, every positive integer $k$, and every simple graph $G$ on the tagged disjoint union $V\sqcup\{x\}$, if the induced graph obtained by deleting $x$ belongs to $R_k$, then $R_{k+1}(G)$ holds. The old neighborhood of $x$ is arbitrary; the old carrier may be empty. All counts and adjacency equivalences concern the same actual full carrier $V\sqcup\{x\}$.

Proof. Choose old representing words $w,v$. Enumerate the old nonneighbors once in a word $N$ and the old neighbors once in a word $T$, and put $Q=NT$. Construct

$$
W=x^k w xNT,\qquad Z=x^k vNxT.
$$

Every old vertex occurs $k+1$ times in each new word. The fresh vertex occurs $k+1$ times. For an old pair $a,b$, the fresh letters disappear and both projections append the common suffix $\pi_{a,b}(Q)$ to the old projections. Right cancellation therefore preserves both edges and nonedges. For an old neighbor $a$, both fresh/old projections are $x^ka^kxa$. For an old nonneighbor $a$, they are $x^ka^kxa$ and $x^ka^{k+1}x$. Cancel their common prefix $x^ka^k$; the remaining heads are $x$ and $a$, which are distinct. Reversing the pair does not change its projection, and graph symmetry covers both argument orders. With no old vertices the two words are simply $x^{k+1}$. This construction gives the claimed representation for every positive $k$.

## Source and conclusion boundaries

The prescribed-neighborhood construction above is repository-derived. The inspected primary proof sections cover common prefix/suffix preservation (Remark 2), universal-vertex insertion (Remark 36), isolated-vertex insertion (Remark 39), and edge deletion. They do not state theorem 2.1. A bounded search of the repository, pinned Mathlib and public Lean repositories found no exact theorem supplying it. These searches establish no worldwide priority claim.

Conjecture 31 remains a separate full target. The extension alone establishes neither nonuniversality nor a separator between adjacent classes. A full argument additionally needs all-positive-$k$ nonuniversality as an actual closed proof, finite minimal nonmember/deletion/renaming bridges, common-enumeration inclusion, and the same-carrier separating graph.

The earlier four-author contribution by Dietz, Fleischmann, Huch and Sacher in IFIG Report 2501, printed pp. 21–24 (PDF pp. 29–32), states the same hierarchy question as Conjecture 3.2 on p. 23. The reproducible source is <https://www.informatik.uni-giessen.de/theorietag2025/2025-Theorietag35-Schotten.pdf>. The available earlier-source reading reports only $k=1$ strictness on p. 24; direct content verification is required before a priority claim. SSRN DOI 10.2139/ssrn.5336494 has not been body-verified. Neither unresolved bibliographic boundary is evidence of global absence of a prior solution.

## 追加锚（本行以下为增补区）
