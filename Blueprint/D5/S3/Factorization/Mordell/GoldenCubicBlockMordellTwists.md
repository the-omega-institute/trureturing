# Two Non-Torsion Cubic Twists on Every Golden Block Layer

## Abstract

Every positive golden cubic-block layer gives two elliptic cubic twists and explicit integral points of infinite order, with the same property on unfactored models.

**Definition 1.1 (The actual cubic block).**

$$B_{j} = \left(L_{3^{j}}\right)^{2} + 3$$

*Formalization.* `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural layer j, the positive actual block is the square of the Lucas number at index 3^j, plus three.

**Definition 1.2 (The canonical cube-part root).**

$$c_{j} = \operatorname{floorRoot}\left(3, B_{j}\right)$$

*Formalization.* `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.cubePartRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned Nat.floorRoot is factorization-based. Its exponent at prime p is floor(v_p(B_j)/3), so its cube divides the block; it is not the ordinary numerical cube-root floor.

**Definition 1.3 (The canonical cubefree factor).**

$$d_{j} = \frac{B_{j}}{\left(c_{j}\right)^{3}}$$

*Formalization.* `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.cubefreePart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient is integral and B_j=d_j*c_j^3. Every prime exponent of d_j is the corresponding exponent of B_j modulo three.

**Definition 1.4 (An integral nonsingular Mordell point of infinite order).**

$$\operatorname{InfiniteOrderPoint}\left(b, X, Y\right) \iff \operatorname{NonsingularPoint}\left(b, X, Y\right) \land \neg\operatorname{IsOfFinAddOrder}\left(X, Y\right)$$

*Formalization.* `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.InfiniteOrderPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral coordinates are cast to rational coordinates on the nonsingular affine locus of Y^2=X^3+b. The resulting group point does not have finite additive order.

**Theorem 1.5 (Two twists on every actual layer).**

$$\forall j\in\mathbb{N}, 1 \le j \Rightarrow \operatorname{IsElliptic}\left(\left(E_{j}\right)^{-}\right) \land \operatorname{IsElliptic}\left(\left(E_{j}\right)^{+}\right) \land \operatorname{IsElliptic}\left(\left(U_{j}\right)^{-}\right) \land \operatorname{IsElliptic}\left(\left(U_{j}\right)^{+}\right),\\{}\operatorname{InfiniteOrder}\left(\left(S_{j}\right)^{-}\right) \land \operatorname{InfiniteOrder}\left(\left(S_{j}\right)^{+}\right) \land \operatorname{InfiniteOrder}\left(\left(T_{j}\right)^{-}\right) \land \operatorname{InfiniteOrder}\left(\left(T_{j}\right)^{+}\right),\\{}\forall i\in\mathbb{N}, 1 \le i \land i \neq j \Rightarrow \neg \exists q\in\mathbb{Q}, \frac{d_{i}}{d_{j}} = q^{3} \land \neg \exists q\in\mathbb{Q}, \frac{-3\left(d_{i}\right)^{2}}{-3\left(d_{j}\right)^{2}} = q^{6} \land \neg \exists q\in\mathbb{Q}, \frac{125\left(d_{i}\right)^{2}}{125\left(d_{j}\right)^{2}} = q^{6}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.actual_cubic_twists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j>=1, all four models are elliptic: E^-_j has coefficient -3*d_j^2, E^+_j has coefficient 125*d_j^2, and U^-_j,U^+_j replace d_j by B_j. The four points of infinite order are respectively (d_j*c_j,d_j*L_(3^j)), (5*d_j*c_j,25*d_j*F_(3^j)), (B_j,B_j*L_(3^j)), and (5*B_j,25*B_j*F_(3^j)).

For distinct positive i,j, no rational q satisfies d_i=q^3*d_j. For either sign, no rational q has the corresponding coefficient ratio equal to q^6. These are literal conjuncts of the Lean theorem.

The Lucas and Fibonacci identities and B_j=d_j*c_j^3 establish the point equations. Odd abscissas and nonzero even ordinates give a binary-unit X coordinate and positive Y valuation. The two-adic Mordell criterion makes the first double's X valuation negative; its valuation then strictly decreases along successive doubles, proving infinite order. Disjoint block prime supports, noncubicity, and factorization-based cube removal separate the twist parameters. Nonzero coefficients make every displayed model globally nonsingular.

No Wall--Sun--Sun hypothesis is used. Infinite order does not show that any point lies outside a cubic-isogeny image; that is a separate claim.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.InfiniteOrderPoint`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.actual_cubic_twists`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.block`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.cubePartRoot`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.cubefreePart`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRanks](../../Arith/Primes/GoldenCubicBlockRanks.md)
- Dependency: [D5/S3/Factorization/GoldenCubicBlockNoncube](../GoldenCubicBlockNoncube.md)
- Dependency: [D5/S3/Factorization/MordellTwoAdicNonTorsion](../MordellTwoAdicNonTorsion.md)
