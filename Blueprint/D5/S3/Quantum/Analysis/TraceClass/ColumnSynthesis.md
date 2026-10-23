# Hilbert-Schmidt column synthesis

## Abstract

Square-summable columns on an arbitrary complete complex Hilbert space.

**Theorem 1.1 (Synthesis and operator norm).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), v \in \operatorname{Function}\left(w, H\right),\; \operatorname{Summable}\left(\operatorname{square}\left(\operatorname{norm}\left(v\left(i\right)\right)\right)iw\right) \Rightarrow \left(\exists A \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\forall i \in w,\; A\left(b\left(i\right)\right) = v\left(i\right)\right) \land \left(\operatorname{IsHilbertSchmidt}\left(A\right) \land \left(\operatorname{tsum}\left(\operatorname{square}\left(\operatorname{norm}\left(A\left(b\left(i\right)\right)\right)\right)iw\right) = \operatorname{tsum}\left(\operatorname{square}\left(\operatorname{norm}\left(v\left(i\right)\right)\right)iw\right) \land \operatorname{norm}\left(A\right) \le \operatorname{sqrt}\left(\operatorname{tsum}\left(\operatorname{square}\left(\operatorname{norm}\left(v\left(i\right)\right)\right)iw\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis.exists_hilbertSchmidt_of_square_summable_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

Let b be any Hilbert basis of a complete complex Hilbert space H, indexed by a set w of H. For any columns v with summable real squared norms, the series A x equals the sum of inner(b_i,x) times v_i converges absolutely. Parseval and the attributed scalar Cauchy-Schwarz estimate bound its norm uniformly by the square root of the column square sum times norm(x). The series defines a continuous linear map with exactly the prescribed columns. Its Hilbert-Schmidt square sum is exactly that of v, and its operator norm satisfies the displayed bound.

The construction allows uncountable basis indices, arbitrary zero columns and the zero space. It is used both for the weighted inverse-square-root extension and for the residual of each finite column approximation. Equality with an existing continuous operator follows from equality on the basis and density of its linear span.

The square-sum product and summability suppliers are Tom Ole Diem's Physlib proofs at revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0, as documented in the analytic trace-supplier Library note. The synthesis construction is a repository derivation; no mathematical originality is claimed for the supplied scalar estimates.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis.exists_hilbertSchmidt_of_square_summable_columns`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](HilbertSchmidt.md)
