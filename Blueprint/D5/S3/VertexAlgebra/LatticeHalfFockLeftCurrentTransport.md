# Actual Three-Field Coefficient Windows

## Abstract

Actual finite fractional products and a common cleared three-field array on every half-Fock tensor input.

Let D be arbitrary LatticeData, hu:IsUnit D.G.det, i:Fin D.rank and a,b:Carrier D. The acted-on space is M=ActualTensor(D,hu), distinct from Carrier D. For every signed lift s define T_s(a)[n]=correctedField(D,hu,a).coeff(-2*n-s-2). Let J be physicalJet(D,hu,(i,0)); its mode J[n] is tensorCurrent(D,ActualGround(D,hu),i,n). The three fixed labels 0,1,2 denote J,T_gamma(a),T_delta(b). The states a,b and the vector x in M are unrestricted.

**Theorem 1.1 (Six ordered products share one cleared array and finite total-exponent windows).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_three_field_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_three_field_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Put L=vectorFrequencyBound(D,a)+1 and N=vectorFrequencyBound(D,b)+1. There is an order K, independent of both signed lifts and every actual vector, such that the K-th commutator difference for T_gamma(a),T_delta(b) vanishes. The all-signed current Borcherds identity at source order L, respectively N, supplies the two current-pair localities: the source sequence is zero by actual source truncation, while the reflected ordered difference is exactly the corresponding finite commutator difference. The third locality follows from actual physical locality by the literal doubled-exponent slice substitution.

The ordinary complete residue R_r(U,W) is the field-only residue constructor, with its separately finite forward and reverse mode sums. Define Q_r^s(U,W) as the sum over 0 <= ell < max(0,K-r) of choose(-s/2,ell) times z^(-ell) R_(r+ell)(U,W). This is an actual lower-truncated field on M. Nonnegative residues are the zero-first-index coefficients of the iterated commutator difference, so locality kills the whole residue above K. Padding to the maximum of two locality orders proves complete-cutoff independence. This does not assert vanishing of either ordered half or of negative products at K=0.

For every signed d, the preserved current inverse identifies Q_d^1(J,T_gamma(a)) with T_(gamma+1)(h_d a), and identically for b and delta. The sum length is max(0,L-d), respectively max(0,N-d); these equalities retain both ordered terms, all negative insertion weights, both Ward families and their zero-mode terms through the original inverse proof. They are current-product equalities, not the missing three-field interchange.

Every intermediate Q_r(T_gamma(a),T_delta(b)) is local with J, and each Q_r(J,T_gamma(a)) is local with T_delta(b), with the analogous statement for b and a. These all-signed field-locality statements follow independently of product preservation. The nonnegative residue case consumes the field-only triple-commutator proof; the negative case consumes the exact divided-derivative normal-product identification, then the existing derivative and Dong locality theorems. Laurent mode shifts preserve the annihilating difference order, and finite scalar sums preserve locality.

For fixed gamma,delta,x, multiply the JAB coefficient array by Q=(X-Y)^L (X-Z)^N (Y-Z)^K using finite polynomial convolution. Contextual adjacent exchanges identify it with Q times every permutation of the three operators, retaining the labels and the actual suffix inputs. This includes BJA and BAJ in their original order. The resulting array has, simultaneously in coordinate j, lower bound equal to the Hahn order of field j applied to x. These bounds come from moving that field to the rightmost position; they need not hold uniformly over all x.

At any fixed total exponent T the nonzero cleared coefficients form a finite Laurent simplex. If l_j are the three actual lower bounds, each contributing exponent satisfies l_j <= e_j <= T-sum(l)+l_j and sum(e)=T. This is finiteness of each total-exponent slice, and imposes no energy eigenstate or finite support on the full array.

For any complex linear functional phi on M and every permutation sigma, the common scalar coefficient array has a genuine supported ordered Hahn carrier. The actual scalar ordered word equals the inverse of the nonzero ordered image of Q multiplied by that carrier. The equality of labelled coefficients follows from ordered_mul_coeff, scalar_action and the actual ordered-word coefficient map. Division occurs in the supported Hahn field; no difference polynomial is cancelled on arbitrary coefficient distributions.

**Theorem 1.2 (Complete Q coefficients are two supported ordered readouts).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_ordered_q_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_ordered_q_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For arbitrary D, hu, i, a and b, choose the same K supplied by the six-order numerator theorem. For all signed gamma and delta the K-th source-pair commutator difference vanishes. For every signed fractional label s, residue index r, mode n, actual input x and complex linear functional phi, applying phi to the n-th mode of Q_r^s(T_gamma(a),T_delta(b)) equals orderedQReadout(s,r,n,K,T_gamma(a),T_delta(b),x,phi). No locality condition is used to extract either individual ordered coefficient.

In the forward chamber the actual scalar carrier is the ordered AB word. Multiply it by the supported expansion of (z-w)^(r+ell), then extract z exponent -1 and w exponent -(n-ell)-1. In the reverse chamber use the actual BA word and the expansion in the opposite order, extracting the same labelled exponents. Subtract these two coefficients, multiply by choose(-s/2,ell), and sum over 0 <= ell < max(0,K-r). The reverse kernel retains the entire sign (-1)^(r+ell).

The kernel coefficient at outer exponent j and inner exponent r-j is (-1)^j choose(r,j), and is zero at negative outer exponents or away from that diagonal. A bijection between the nonzero Hahn convolution antidiagonal and the actual natural-index residue sum proves coefficient extraction. For the forward AB word, a cutoff follows from the Hahn order of B applied to x; the reverse BA word uses the order of A applied to x. The intermediate field is applied only after this rightmost coefficient has been selected.

The two original current inverse equalities are consumed in this readout theorem: for every signed d and n, phi applied to T_(gamma+1)(h_d a)[n]x equals the current-A readout with L=vectorFrequencyBound(D,a)+1, and the corresponding statement holds for b,delta and N. Every original source and actual input remains unrestricted. This is a complete ordered-residue identification. The companion ClearedTaylorReadout module proves its binary finite Taylor formula on the actual cleared array; identifying the genuinely nested ternary readouts requires additional equalities.

**Theorem 1.3 (A finite two-pole form includes negative integration exponents).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.negative_laurent_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.negative_laurent_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every pair of natural numbers p,q, the rational function z^(-p)(z-x)^(-q) is a finite sum of diagonal poles and z-poles, with coefficients in the rational x-field. More precisely there are two finite lists of pairs (h,j), with h in RatFunc(C) and j natural. The first contributes rationalX(h)*(z-x)^(-j), and the second contributes rationalX(h)*rationalZ(X^(-j)). The sum of both lists is exactly the original rational function.

The construction uses induction in both pole orders. When p=0 there is one diagonal term; when q=0 there is one z-pole term. With both orders positive, multiplication by x^(-1) separates the two terms obtained from x=z-(z-x). The recursively constructed finite lists are rescaled and concatenated. This proves the algebraic decomposition before any residue-collision theorem is applied.

Applying weighted_normal_form_collision to those finite lists proves that expansion of the fused local residue equals the difference of the two genuine ordered residues. Both exponents can be strictly negative. This algebraic statement supplies the two-pole boundary; identifying a finite Laurent slice of an actual field word with this rational function is a separate carrier equality.

The three genuinely nested chart-to-Q identifications on the same ternary numerator are additional mathematical obligations. The common cleared array, supported division and companion binary Taylor formula do not yet prove target Q interchange, Lambda_tar=0, arbitrary-first defect transport, or a first-word reduction. The all-charge GroundFirst base and the larger Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme remain separate mathematical questions. No physical spacetime interpretation is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_ordered_q_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.actual_three_field_numerator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.negative_laurent_collision`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality](LatticeHalfFockAllStatePhysicalLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](LatticeHalfFockCurrentBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](StateFieldResidueReconstruction.md)
- Dependency: [D5/S3/VertexAlgebra/SupportedWordRationalCollision](SupportedWordRationalCollision.md)
