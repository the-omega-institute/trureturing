# HeadleyOddProduct

## Abstract

An even R-star base times any odd finite abelian group retains its prescribed zero-row triple.

**Theorem 1.1 (Actual successor and difference permutations).**

$$\forall X \in Type,\; [\operatorname{AddCommGroup}\left(X\right)] [\operatorname{Finite}\left(X\right)] \forall r \in \operatorname{RStar}\left(X\right),\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall v \in \operatorname{Prod}\left(X, \operatorname{Box}\left(ds\right)\right),\; \operatorname{apply}\left(\operatorname{difference}\left(r, ds\right), v\right) = \operatorname{apply}\left(\operatorname{successor}\left(r, ds\right), v\right)-v$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddProduct.difference_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S is the ordinary row lift after a source three-cycle on the a,zero,b columns for each internally selected positive row. D is the old difference permutation after the inverse source three-cycle. The additive relation a+c=b proves that these are the actual labels S(v)-v in original product coordinates. Composition of equivalences supplies both inverse laws for S and D; no label inventory is a premise. The two inverse-pair paths and their six labels are attributed to Section 4 of the earlier native Headley construction and the accepted odd-row proof, not claimed as a new literature result.

**Theorem 1.2 (The complete first positive return).**

$$\forall X \in Type,\; [\operatorname{AddCommGroup}\left(X\right)] [\operatorname{Finite}\left(X\right)] \forall r \in \operatorname{RStar}\left(X\right),\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; [\operatorname{Fintype}\left(X\right)] \forall h \in \operatorname{Box}\left(ds\right),\; (\operatorname{apply}\left(\operatorname{pow}\left(\operatorname{successor}\left(r, ds\right), \operatorname{ite}\left(h = 0, \operatorname{card}\left(X\right)-1, \operatorname{card}\left(X\right)\right)\right), \operatorname{pair}\left(\operatorname{a}\left(r\right), h\right)\right) = \operatorname{pair}\left(\operatorname{a}\left(r\right), \operatorname{predecessor}\left(ds, h\right)\right)) \land (\forall i \in Nat,\; ((0 < i) \land (i < \operatorname{ite}\left(h = 0, \operatorname{card}\left(X\right)-1, \operatorname{card}\left(X\right)\right))) \Rightarrow (\operatorname{fst}\left(\operatorname{apply}\left(\operatorname{pow}\left(\operatorname{successor}\left(r, ds\right), i\right), \operatorname{pair}\left(\operatorname{a}\left(r\right), h\right)\right)\right) \ne \operatorname{a}\left(r\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddProduct.box_first_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gadget uses two steps at row zero and three steps on any other row. The ordinary tail uses M-3 steps, with its first lift T1 and the even remaining M-4 negations. Their ordered composite returns (a,h) to (a,pred(h)). No intermediate gadget vertex has first coordinate a; bounded injectivity of the base orbit excludes a from every intermediate ordinary column. The proof includes closure and the M=4 tail. This is an actual power statement about the defined successor, rather than an assumed row-return certificate.

**Theorem 1.3 (All row blocks form the entire nonzero orbit).**

$$\forall X \in Type,\; [\operatorname{AddCommGroup}\left(X\right)] [\operatorname{Finite}\left(X\right)] \forall r \in \operatorname{RStar}\left(X\right),\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; [\operatorname{Fintype}\left(X\right)] \operatorname{IsCycleOn}\left(\operatorname{successor}\left(r, ds\right), \operatorname{nonzero}\left(\operatorname{Prod}\left(X, \operatorname{Box}\left(ds\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddProduct.nonzero_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each inverse pair has paths (a,h),(0,-h),(0,h),(c,-h) and (a,-h),(b,h),(b,-h),(c,h); the zero row retains (a,0),(b,0),(c,0). The actual ordinary tail starts with T1 and then uses an even number M-4 of negations. Its complete return is predecessor. Every exceptional vertex is on one of these paths. The original base cycle enumerates every other column, and each intermediate row map is a permutation, so every ordinary fiber is reached. The predecessor cycle connects all a-rows. The nonzero restriction reuses HeadleyExtension.bijOn_complement at the fixed origin. This proves one cycle on the entire nonzero product, with no additional component or unaccounted seam. The M=4, trivial-row and row-order-three cases remain in the same construction.

**Theorem 1.4 (The full arbitrary odd-factor theorem with the exact triple).**

$$\forall X \in Type,\; [\operatorname{AddCommGroup}\left(X\right)] [\operatorname{Finite}\left(X\right)] \forall H \in Type,\; [\operatorname{AddCommGroup}\left(H\right)] [\operatorname{Finite}\left(H\right)] \forall r \in \operatorname{RStar}\left(X\right),\; (\operatorname{Odd}\left(\operatorname{card}\left(H\right)\right)) \Rightarrow (\exists rOut \in \operatorname{RStar}\left(\operatorname{Prod}\left(X, H\right)\right),\; (\operatorname{a}\left(rOut\right) = \operatorname{pair}\left(\operatorname{a}\left(r\right), 0\right)) \land ((\operatorname{b}\left(rOut\right) = \operatorname{pair}\left(\operatorname{b}\left(r\right), 0\right)) \land (\operatorname{c}\left(rOut\right) = \operatorname{pair}\left(\operatorname{c}\left(r\right), 0\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddProduct.exists_rstar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is an RStar on X, which includes Even(Nat.card X), and Odd(Nat.card H), for arbitrary finite additive commutative groups. The output is an RStar on X×H with a=(r.a,0), b=(r.b,0), c=(r.c,0). The proof supplies actual successor and difference permutations, fixing the origin, the entire nonzero cycle, every triple field and even cardinality. The odd factor is obtained by the original unconditional Gordon decomposition. HeadleyExtension.transportCycle supplies the entire transported RCycle, preserving the fixed origin, the full nonzero cycle and every coefficient-one difference; the added RStar fields retain the literal zero-row triple and even cardinality. There is no generator, supplied decomposition, orthomorphism, inventory or cycle-certificate premise. The intended consumer is the odd quotient factor in the Headley extension program. The full Headley induction, full uniform finite-field route and original arbitrary-subset/same-M/original-coordinate/coefficient-one parent remain open; this theorem does not settle them. The faithful original-telescope four-slot Reg attempt remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21042; no validated Reg or observational-dependence claim is supplied.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddProduct.box_first_return`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddProduct.difference_spec`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddProduct.exists_rstar_product`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddProduct.nonzero_cycle`
- Dependency: [D5/S3/FiniteGroups/HeadleyExtension](HeadleyExtension.md)
- Dependency: [D5/S3/FiniteGroups/HeadleyOddRows](HeadleyOddRows.md)
