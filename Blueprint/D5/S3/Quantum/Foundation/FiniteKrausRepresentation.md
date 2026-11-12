# Finite Kraus Representations

## Abstract

Every finite rectangular completely positive matrix map has a finite Kraus witness.

Use the output-input order for the Choi coordinates: the channel acts on the first factor of the unnormalized maximally entangled projector. The finite Kraus family has rectangular output-by-input matrices; the zero map is included. Trace preservation is equivalent to the sum of the adjoint-Kraus products being the identity: cyclicity proves sufficiency, and testing every matrix unit proves necessity.

Ordinary transposition preserves positive matrices but is not completely positive. Its Choi matrix is the swap. On two qubits the partial transpose of the normalized Bell density is half the swap, with three eigenvalues equal to one half and one equal to minus one half. The antisymmetric vector detects the negative direction. Positivity on inputs alone therefore does not replace positivity with every auxiliary interface.

**Theorem 1.1 (Complete positivity gives a rectangular Kraus family).**

$$\operatorname{IsCompletelyPositive}(Phi) \Rightarrow \exists M, Phi=\operatorname{ofKraus}(M,M).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

For finite coordinate types A and B with decidable equality and an RCLike scalar, every completely positive rectangular MatrixMap Φ has a witness family M indexed by B × A and equals the associated Kraus sum (ofKraus denotes the Lean function of_kraus). This is a CP representation statement; it does not assert trace preservation.

The declaration is the selected upstream Physlib result at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260, routed from QuantumInfo/Channels/MatrixMap.lean and Unbundled.lean. Finite and decidable assumptions are retained explicitly.

Application: a fixed three-copy probe. The finite complex-matrix application in Quantum Origin V, Lemma 82.2 and Theorem 82.3, follows from the existing rectangular Choi criterion and positive-semidefinite compression. Fix an arbitrary finite nonempty set I and finite nonempty coordinate sets D(i), with chosen common computational frames. Write d(i) for their cardinalities and N for their sum. The original algebra is the direct sum of the full complex matrix algebras on D(i). Its supplied map Φ is complex-linear and may send every input summand to every output summand. No positivity, Hermiticity preservation, trace preservation, unitality or sector preservation is assumed; in particular the Hermiticity-preserving source case is included.

Parameter correspondence: the input-i/output-j component Φ(ji) is projection to j after Φ after inclusion of i. In the existing MatrixMap interface its input type A is D(i), output type B is D(j), and scalar R is the complex field. Its output-first Choi matrix C(ji) has entry Φ(ji)(E(rs))(b,c) at coordinates ((b,r),(c,s)). Here E(rs) is the input matrix unit. The declarations choi_matrix_eq_map_proj and choi_PSD_iff_CP_map in FiniteKrausChannel.PhyslibLeaf.MatrixMap, owned by this Lean module, identify this matrix with the image of the unnormalized entangled dyad and equate its PSD property with complete positivity. Their existing Kraus construction supplies the converse without a separate Hermiticity premise.

For one block of dimension d greater than zero, associate three-copy coordinates to the right and let e(rrr) be the diagonal computational string. The normalized GHZ vector and its dyad are:

$g=\frac{1}{\sqrt{d}}\sum_{r}e_{rrr}, P=gg^{*}$

Thus P is the diagonal-string dyad divided by d, is PSD and has ordinary matrix trace one. For an output-input coordinate (a,b), define the three repeated-label embeddings V(0)e(ab)=e(abb), V(1)e(ab)=e(bab), V(2)e(ab)=e(bba). The readout F sends e(aa) to e(aaa), and for a distinct from b sends e(ab) to e(abb)+e(bab)+e(bba). All these maps depend only on the frame, independently of Φ and the weights. Star in the formulas denotes adjoint.

Let D be the projection onto the diagonal matrix-unit coordinates. Comparing the three positions gives V(l)*V(m)=1 for equal positions and D otherwise: strings from distinct positions coincide precisely on the common diagonal string. Consequently F=V(0)+V(1)+V(2)−2V(0)D, F*V(l)=1, and:

$F^{*}F=3I-2D$

The Gram matrix therefore has diagonal entry one on diagonal coordinates and three on off-diagonal coordinates. It is positive definite, so F is injective, and three times the identity minus its Gram matrix is PSD. F is generally not an isometry. When d=1 the diagonal projection is the identity and all three embeddings coincide; the same identities retain the scalar case.

Let T(l) apply the same Φ in position l and the identity to both spectators; the other positions are obtained by swapping the first and selected tensor positions before and after Φ tensor identity. Expanding the GHZ dyad in matrix units and using the existing output-first Choi formula gives T(l)(P)=V(l)C(Φ)V(l)*/d. For any real weights α(l) whose sum is one, put L(α)=the sum of α(l)T(l). The left-inverse identity then gives:

$F^{*}\operatorname{L}\left(\alpha\right)(P)F=\frac{\operatorname{C}\left(Phi\right)}{d}$

This compression identity itself allows negative weights. If L(α)(P) is PSD, compression and multiplication by the positive scalar d give C(Φ) PSD. The existing Choi criterion gives complete positivity of Φ at every finite amplification. For nonnegative weights, CP also makes every actual leg positive, so the converse holds. Nonnegative normalized weights include zeros and all three endpoint triples.

For the direct sum, retain every ordered sector (a,b,c), whose matrix coordinates are D(a) × (D(b) × D(c)). Positivity means the full PSD cone in each such matrix algebra, with neither a separability restriction nor a symmetric-sector quotient. In sector (i,i,i) set Z(0) equal to d(i)P(i)/N, and set every other sector to zero. This is a fixed positive probe with total ordinary trace, summed over all ordered sectors, equal to one. Equivalently its nonzero sector is the unnormalized diagonal-string dyad divided by N. The probe is independent of the supplied map and averaging weights.

The actual first leg at output sector (a,b,c) is the sum over i of (Φ(ai) tensor identity on D(b) × D(c)) applied to X(i,b,c). The second and third legs swap both the central sector labels and the corresponding computational coordinates. The lift L(α) is their weighted sum, always using the original Φ. This defines its action on arbitrary sector matrices, including all repeated labels and unequal dimensions.

The diagonal output sector (i,i,i) equals d(i)/N times the one-block weighted lift for Φ(ii). Compressing it by the readout for D(i) gives C(ii)/N. For j distinct from i, the output sector with j in position l and i in the other two positions has, after permuting the output position to the front, the following form:

$Y_{lji}=\frac{\alpha_{l}}{N}W_{ji}C_{ji}W_{ji}^{*}$

Here W(ji)e(br)=e(brr), from D(j) × D(i) into D(j) × (D(i) × D(i)); it is isometric because this coordinate assignment is injective. The three sectors are (j,i,i), (i,j,i) and (i,i,j), with their indicated permutations. The other two legs contribute zero because the probe has no seed with unequal spectator labels. Since nonnegative weights sum to one, some α(l) is strictly positive. Compressing that sector by W(ji) and multiplying by N/α(l) recovers C(ji) as PSD. No division by a zero weight occurs. Together with the diagonal readout this recovers every rectangular Choi matrix, even for scalar blocks and endpoint weight triples.

To pass from components to the same original map, let X be an arbitrary auxiliary matrix over the direct sum. At each output block j its amplified image is the sum over i of the amplified Φ(ji) applied to the input block i. Conversely a matrix supported in a single central block tests each component. Thus complete positivity of all rectangular components is equivalent to positivity of the original map at every auxiliary size. Use the existing IsCompletelyPositive.of_Fintype to replace the auxiliary Fin k by any finite spectator coordinate type. The canonical coordinate map is componentwise CStarMatrix.ofMatrix; an auxiliary entry X(r,s)(i)(a,b) becomes the flattened block entry ((a,r),(b,s)). The frozen FiniteKrausChannel.flatten_intertwines identifies this Kronecker amplification with the canonical CStarMatrix amplification. Finite sums over central blocks and the coordinate star algebra equivalences transport exactly this original map to a Mathlib CompletelyPositiveMap; they introduce no extra positivity assumption.

Conversely, component CP makes every rectangular leg positive on every full ordered sector cone, and finite sums and nonnegative scalar multiples preserve PSD. Hence, for each fixed nonnegative normalized weight triple, positivity of L(α) on the fixed probe, canonical CP of the original direct-sum map, and positivity of that actual lift on the entire ordered three-copy cone are equivalent. The derivation uses the existing Choi criterion, PSD conjugation, sums and scaling, and the frozen amplification correspondence. This is an application exposition of those results, with no additional Lean declaration or theorem Describe.

The common frames and repeated basis labels are mathematical data. These identities do not supply physical GHZ preparation, a copying operation, callable independent legs, actual-event realization, the all-real physical intertwining contract, physical control, a PRE/static bridge or the full Omega assertion. Quantum Origin V 82.10–82.14 retain those separate obligations. The finite complex-matrix application establishes no such operational or physical premise, and no literature originality is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](FiniteKrausChannel.md)
