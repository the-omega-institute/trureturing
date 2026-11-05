# Harmonic squares and all orders of mixed differences

## Abstract

Every order of the normalized Laplacian of a harmonic square is a nonnegative finite average of ordered mixed-difference squares.

**Definition 1.1 (The actual nearest-neighbour mean).**

$$\forall d \in \mathbb{N},\; \forall f \in \operatorname{Lattice}\left(d\right) \to \mathbb{R},\; \forall x \in \operatorname{Lattice}\left(d\right),\; \operatorname{translationMean}\left(d\right)\left(f, x\right) = \frac{1}{2 \cdot d} \cdot \sum_{v \in \operatorname{Direction}\left(d\right)} f\left(x + \operatorname{step}\left(v\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.translationMean` (`✓ std3`).

*Citation.* Gabor Lippner and Dan Mangoubi (2015). *Harmonic functions on the lattice: Absolute monotonicity and propagation of smallness*. DOI: [10.1215/00127094-3164790](https://doi.org/10.1215/00127094-3164790). URL: <https://arxiv.org/html/1312.4550v3>.

*Commentary.*

For a natural d, the lattice is the additive group Fin d to Z. A direction is a pair (i,b) in Fin d times Bool. Its step has coordinate +1 at i when b is true, -1 at i when b is false, and zero elsewhere. Thus there are exactly 2d labels. The displayed denominator is real. Write P for translationMean d and L=P-I for laplacian d. Harmonic H means the equality PH=H of entire real functions. Positive dimension is required in the theorem, so the normalization is nonzero.

**Definition 1.2 (Ordered words and the empty composition).**

$$\forall d \in \mathbb{N},\; \forall H \in \operatorname{Lattice}\left(d\right) \to \mathbb{R},\; (\forall w \in \operatorname{Word}\left(d, 0\right),\; \operatorname{mixedDifference}\left(0, w, H\right) = H) \land (\forall k \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(d, k + 1\right),\; \operatorname{mixedDifference}\left(k + 1, w, H\right) = \operatorname{fwdDiff}\left(\operatorname{step}\left(w\left(0\right)\right), \operatorname{mixedDifference}\left(k, \operatorname{Fin}.\operatorname{tail}\left(w\right), H\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.mixedDifference` (`✓ std3`).

*Citation.* Gabor Lippner and Dan Mangoubi (2015). *Harmonic functions on the lattice: Absolute monotonicity and propagation of smallness*. DOI: [10.1215/00127094-3164790](https://doi.org/10.1215/00127094-3164790). URL: <https://arxiv.org/html/1312.4550v3>.

*Commentary.*

A word of length k is any function Fin k to Direction d. No injectivity condition is imposed: a direction may occur any number of times, and words with a common endpoint are still different words. Mathlib's fwdDiff a f is the function x mapped to f(x+a)-f(x). mixedDifference composes those operators with the first letter outermost. At k=0 there is exactly one word, the function from the empty type, and its mixed difference is H itself.

**Theorem 1.3 (The mixed-square identity and nonnegativity in every order).**

$$\forall d \in \mathbb{N},\; (0 < d) \Rightarrow (\forall H \in \operatorname{Lattice}\left(d\right) \to \mathbb{R},\; (\operatorname{Harmonic}\left(H\right)) \Rightarrow (\forall k \in \mathbb{N},\; \forall x \in \operatorname{Lattice}\left(d\right),\; (\operatorname{Function}.\operatorname{iterate}\left(\operatorname{laplacian}\left(d\right), k, \operatorname{square}\left(H\right), x\right) = \frac{1}{2 \cdot d}^{k} \cdot \sum_{w \in \operatorname{Word}\left(d, k\right)} \operatorname{mixedDifference}\left(k, w, H, x\right)^{2}) \land (0 \le \operatorname{Function}.\operatorname{iterate}\left(\operatorname{laplacian}\left(d\right), k, \operatorname{square}\left(H\right), x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.harmonic_square_iterate` (`✓ std3`). ∎

*Citation.* Gabor Lippner and Dan Mangoubi (2015). *Harmonic functions on the lattice: Absolute monotonicity and propagation of smallness*. DOI: [10.1215/00127094-3164790](https://doi.org/10.1215/00127094-3164790). URL: <https://arxiv.org/html/1312.4550v3>.

*Commentary.*

Let d be any positive natural number and let H be any real function on the whole integer lattice with PH=H. For every natural k and every lattice point x, L iterated k times on the pointwise square of H equals (2d)^(-k) times the sum of the squares of all length-k mixed differences of H at x, and that iterate is nonnegative. There is no boundedness, growth, periodicity, sign or symmetry assumption on H. The order-zero identity is H(x)^2=H(x)^2, with coefficient one and the single empty word.

Translation commutes with a forward difference because the lattice addition is commutative. The finite mean therefore commutes with each forward difference, and every mixed difference of H remains harmonic. For a harmonic f, expand (f(x+v)-f(x))^2 and average. The cross term is -2f(x)Pf(x), and the constant term is f(x)^2 because the weights sum to one. Consequently L(f^2) is the average of the forward-difference squares. Apply this identity to every harmonic mixed difference in the length-k sum. Linearity of L and the bijection between a length-(k+1) word and its first letter together with its tail give the next order, with exactly one additional factor (2d)^(-1).

Every summand and the normalization are nonnegative, giving the public theorem's second conclusion L^k(H^2)(x)>=0 for every k, including k=0. This sign conclusion is an elementary consequence of the same identity. The following finite binomial estimate is a separate mathematical consequence and is not a conclusion of the Lean declaration. Since P=I+L and the identity operator commutes with L, the finite binomial formula is P^N(H^2)=sum_(j=0)^N choose(N,j)L^j(H^2). For N>=3, retaining the j=3 term yields P^N(H^2)(x)>=choose(N,3)L^3(H^2)(x). For N<3 the binomial coefficient is zero and the inequality follows from the nonnegative expansion. This is the finite estimate used after equation (2.1) in the constant-Poisson argument.

Lippner and Mangoubi give this classical identity in arXiv:1312.4550v3, Theorem 2.1, Claim 2.2 and Remark 2.3. Here the mean and the differences are the literal signed-coordinate operators of the integer lattice. The formal delivery stops at the all-order identity and its pointwise nonnegativity. The finite binomial estimate, constant-Poisson subtraction, sixth-moment and subcubic growth estimates, limiting vanishing of third differences and reconstruction of a quadratic polynomial remain separate formal obligations. The original constant-Poisson target has growth exponent alpha<3, including the downstream log2(6) case. Those conclusions and the subsequent classification do not follow from harmonicity alone. The zero-dimensional singleton case is separate and uses no division by d.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.harmonic_square_iterate`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.mixedDifference`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.translationMean`
