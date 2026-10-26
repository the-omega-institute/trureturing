# Gordon interleaving and directed differences

## Abstract

The arithmetic carry construction gives an orthogonal path for the regular translation action.

**Theorem 1.1 (All prefix vertices are distinct).**

$$\forall h \in \mathbb{N},\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; (\operatorname{Coprime}\left(h, \operatorname{volume}\left(ds\right)\right)) \Rightarrow (\operatorname{Injective}\left(\operatorname{restrict}\left(\operatorname{vertex}\left(h, ds\right), \operatorname{Fin}\left(2*h*\operatorname{volume}\left(ds\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonProduct.vertex_injective` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Write D for the odd radix product, L=hD and N=2L. The vertex function is restricted here to indices zero through N minus one. Its even vertices are minus F(j); its odd vertices are F(j) plus the tuple of ones, for j less than L. Same-parity equality gives congruences modulo 2h and D. Opposite-parity equality forces complementary digits and N to divide u+v+1, which lies strictly between zero and N.

**Theorem 1.2 (The two difference inventories).**

$$\forall h \in \mathbb{N},\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; (\operatorname{Coprime}\left(h, \operatorname{volume}\left(ds\right)\right)) \Rightarrow (\operatorname{Injective}\left(\operatorname{restrict}\left(\operatorname{difference}\left(h, ds\right), \operatorname{Fin}\left(2*h*\operatorname{volume}\left(ds\right)-1\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonProduct.difference_injective` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

The difference function is restricted here to indices zero through N minus two. Odd-first-coordinate labels are 2F(j)+C for j less than L. Even labels are minus F(j) minus F(j-1) minus C for positive j less than L. The reversible carry recovers j modulo D, while the first coordinate recovers it modulo h. Parity separates the families. Chinese remaindering is used between h and D; no pairwise coprimality of odd radices is assumed.

**Theorem 1.3 (Every original nonzero label exactly once).**

$$\forall h \in \mathbb{N},\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; ((0 < h) \land (\operatorname{Coprime}\left(h, \operatorname{volume}\left(ds\right)\right))) \Rightarrow (((\operatorname{Nodup}\left(\operatorname{word}\left(h, ds\right)\right)) \land (\forall x \in \operatorname{Product}\left(\operatorname{ZMod}\left(2*h\right), \operatorname{Box}\left(ds\right)\right),\; (x \in \operatorname{word}\left(h, ds\right)) \Leftrightarrow (x \ne 0))) \land (\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; ((k \le \operatorname{length}\left(\operatorname{word}\left(h, ds\right)\right)) \land (l \le \operatorname{length}\left(\operatorname{word}\left(h, ds\right)\right))) \Rightarrow ((\operatorname{sum}\left(\operatorname{take}\left(k, \operatorname{word}\left(h, ds\right)\right)\right) = \operatorname{sum}\left(\operatorname{take}\left(l, \operatorname{word}\left(h, ds\right)\right)\right)) \Rightarrow (k = l))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonProduct.product_sequencing` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

The word has N minus one labels. They are distinct and nonzero, so cardinality gives every nonzero group element once. Its prefix sums telescope to the N distinct vertices, including the empty and full prefix. For q=2 raised to a positive exponent take h=q/2; coprimality with D follows from oddness. This includes q=2, no odd factors, and repeated odd factors. Translations by group elements form a regular action. Consecutive vertices use each nonzero translation label once, so the vertex path and the directed-label inventory are simultaneous properties.

**Theorem 1.4 (The terminal prefix).**

$$\forall h \in \mathbb{N},\; \forall ds \in \operatorname{List}\left(OddRadix\right),\; (0 < h) \Rightarrow (\operatorname{sum}\left(\operatorname{word}\left(h, ds\right)\right) = \operatorname{pair}\left(h, 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonProduct.word_endpoint` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

The final odd digits are all radix minus one and cancel the tuple of ones. Since D is odd, the first coordinate is h modulo 2h. The endpoint is therefore (h,0), and differs from the empty prefix for positive h.

## References

- Truth anchor: `D5/S3/FiniteGroups/GordonProduct.difference_injective`
- Truth anchor: `D5/S3/FiniteGroups/GordonProduct.product_sequencing`
- Truth anchor: `D5/S3/FiniteGroups/GordonProduct.vertex_injective`
- Truth anchor: `D5/S3/FiniteGroups/GordonProduct.word_endpoint`
- Dependency: [D5/S3/FiniteGroups/GordonCarry](GordonCarry.md)
