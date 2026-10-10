# Full Four-Exit Raw Endpoint Domination

## Abstract

Every original strategy on the full four-exit family lies above a raw endpoint and has at most one zero-excess row.

For k at least one, I(k) is Unit plus Fin(k) times Fin(4). The Unit row is the baseline. Rows zero through three in an exceptional slot are A, Y, H, Z. F(k,i) is the literal family from FourExitRawEndpointSpectrum, with n(k)=8k+16. Its tree substitution, complete leaf list, four-valued readout and Strategy are those of ActualTreeReadoutAcquisition. Cost counts distinct addresses actually requested from empty initial history by the same globally correct strategy.

M(k) is the existing endpoint menu. It contains the vector with zero at the baseline or any Y, H, Z row and one elsewhere; for each A row it contains three vectors with zero there, two at a sibling Y, H, Z row and one elsewhere. NC means that any shared literal leaf address has the same label in both trees.

**Theorem 1.1 (Full Family Structure and Strategy Lower Bound).**

$$\forall k: Nat, ((1 \leq k) \implies ((\forall i: \operatorname{I}\left(k\right), ((\operatorname{Positive}\left(\operatorname{F}\left(k, i\right)\right)) \land (\operatorname{length}\left(\operatorname{F}\left(k, i\right)\right) = \operatorname{n}\left(k\right)) \land (\operatorname{leafLength}\left(\operatorname{F}\left(k, i\right)\right) = \operatorname{n}\left(k\right)))) \land (\operatorname{Injective}\left(\operatorname{F}\left(k\right)\right)) \land (\forall i: \operatorname{I}\left(k\right), (\forall j: \operatorname{I}\left(k\right), (\operatorname{NC}\left(\operatorname{F}\left(k, i\right), \operatorname{F}\left(k, j\right)\right)))) \land (\forall pi: Strategy, ((\forall i: \operatorname{I}\left(k\right), (\operatorname{n}\left(k\right) \leq \operatorname{cost}\left(pi, \operatorname{F}\left(k, i\right)\right))) \land (\forall i: \operatorname{I}\left(k\right), (\forall j: \operatorname{I}\left(k\right), (((\operatorname{cost}\left(pi, \operatorname{F}\left(k, i\right)\right) = \operatorname{n}\left(k\right)) \land (\operatorname{cost}\left(pi, \operatorname{F}\left(k, j\right)\right) = \operatorname{n}\left(k\right))) \implies (i = j)))) \land (\exists v: \operatorname{NatVector}\left(\operatorname{I}\left(k\right)\right), ((v \in \operatorname{M}\left(k\right)) \land (\forall i: \operatorname{I}\left(k\right), (\operatorname{n}\left(k\right) + \operatorname{at}\left(v, i\right) \leq \operatorname{cost}\left(pi, \operatorname{F}\left(k, i\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawDomination.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The substitution respects every ordered pair in the right comb. The displayed preimages therefore prove positivity. Each ordinary block has eight leaves; an exceptional block and its compensation have twenty-four. Equality of two combs implies equality at each slot, so the exceptional location and block recover the row index. Pairwise label compatibility of the finite block tables extends along the comb to the entire family.

The compulsory-leaf certificate gives every strategy cost at least n(k). If two rows both cost n(k), their paid address sets equal their complete leaf sets. Induction on the two actual executions shows that the same selector sees identical histories: at each shared query both replies are leaf labels, and NC equates them. The runs and complete labelled leaf sets coincide. Leaf rigidity then equates the trees and hence their indices.

With no zero-excess row all coordinates exceed the baseline and dominate a baseline endpoint. A zero at the baseline or a Y, H, Z row selects its one-zero endpoint. A zero at A invokes the local zero-to-two obstruction to select a sibling of excess at least two. Uniqueness of the zero gives excess at least one at every remaining row. These cases prove domination for every original Strategy, including adaptive and repeated queries.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawDomination.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](FourExitRawEndpointSpectrum.md)
