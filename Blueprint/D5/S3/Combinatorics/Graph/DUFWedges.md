# Unordered wedges and four-edge common links

## Abstract

Let H be a finite family of subsets of a finite vertex type. The definitions of tips and wedges apply to every such H. Under DUF and the cap of at most four neighbors per ground pair, two distinct edges in F(S) with card(S)=4 meet at a center. Their two remaining endpoints determine a four-edge common link. Recovering its center and leaves removes any overcounting.

**Definition 1.1 (The two noncentral endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFWedges.tips`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFWedges.tips` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tips of a finite set family are the vertices in its union but not in its intersection. For a star with two leaves and center outside them, this is exactly the leaf pair.

**Definition 1.2 (Unordered fiber wedges).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFWedges.wedges`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFWedges.wedges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each four-element neighborhood S, take the two-element subfamilies of F(S). The index S and the unordered two-edge family together specify one wedge.

**Theorem 1.3 (From a wedge to a common link).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFWedges.wedge_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFWedges.wedge_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap, a four-element set S, and a two-element subfamily w of F(S), there are a center c and a two-element set q with c outside both q and S, w=cq, tips(w)=q, K(q)=cS, and card(K(q))=4.

**Theorem 1.4 (The exact wedge bijection).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFWedges.wedge_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFWedges.wedge_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap, taking tips is a bijection between unordered fiber wedges indexed by four-element sets S and ground pairs with four-edge common links. Consequently their number q4 equals the sum over all four-element S of binom(card(F(S)),2). The uniqueness argument uses the center of a four-edge star, not a center choice for singleton stars.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFWedges.tips`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFWedges.wedge_bijection`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFWedges.wedge_structure`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFWedges.wedges`
- Dependency: [D5/S3/Combinatorics/Graph/DUFStructure](DUFStructure.md)
