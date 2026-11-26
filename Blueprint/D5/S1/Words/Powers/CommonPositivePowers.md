# Common Positive Powers Imply Commutation

## Abstract

Two finite words with equal positive natural powers commute.

**Theorem 1.1 (Equal positive powers imply word commutation).**

$$\forall u \in Universe,\; \forall alpha \in \operatorname{Type}\left(u\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \forall M \in \mathbb{N},\; \forall N \in \mathbb{N},\; (M \ne 0) \Rightarrow ((N \ne 0) \Rightarrow ((\operatorname{flatten}\left(\operatorname{replicate}\left(M, w\right)\right) = \operatorname{flatten}\left(\operatorname{replicate}\left(N, v\right)\right)) \Rightarrow (\operatorname{append}\left(w, v\right) = \operatorname{append}\left(v, w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CommonPositivePowers.append_comm_of_flatten_replicate_eq` (`✓ std3`). ∎

*Citation.* Sébastien Gouëzel (2026). *IETFree/ListPeriodicity.lean (Lean source artifact, revision 48a23a630f39ae7c439b9efcbd03e729c18406fd)*. URL: <https://github.com/sgouezel/IETFree/blob/48a23a630f39ae7c439b9efcbd03e729c18406fd/IETFree/ListPeriodicity.lean>.

*Commentary.*

For every universe level u, every alphabet type A in Type u, all finite words w and v over A, and natural numbers M and N with M nonzero and N nonzero, equality of flatten(replicate(M,w)) and flatten(replicate(N,v)) implies append(w,v)=append(v,w). The words may be empty. There is no finiteness, inhabitedness, ordering or decidable equality premise on A. Both nonzero assumptions are retained; no separate sharpness claim is made.

Four private helpers establish the period of a repeated word and reassemble blocks of a periodic word. The public theorem first handles empty words, then applies the Fine-Wilf gcd-period theorem to a doubled common power and expresses both words as powers of its initial gcd-length block. Addition of the exponents gives commutation. This is copied mathematical content from Sebastien Gouezel's IETFree/ListPeriodicity.lean at revision 48a23a630f39ae7c439b9efcbd03e729c18406fd, with four private helpers and one public theorem. Public visibility carries no discovery claim.

CyclicCentralizer consumes this theorem to show that positive-power roots of the same word commute. This supplier alone does not classify a centralizer or prove uniqueness of a generator. Its source notice, complete Apache 2.0 license reference and retirement condition against equivalent same-signature List declarations in this repository's own pinned Mathlib accompany the Lean source and primary software note.

## References

- Truth anchor: `D5/S1/Words/Powers/CommonPositivePowers.append_comm_of_flatten_replicate_eq`
