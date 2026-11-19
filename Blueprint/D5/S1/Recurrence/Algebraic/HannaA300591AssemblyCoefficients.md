# The exponential coefficient formula for Hanna's assemblies

## Abstract

Signed ordered-block assemblies have exactly the ordinary exponential coefficients, including an explicit finite unit-sign palette for every integer strict prefix.

**Theorem 1.1 (The full signed assembly formula).**

$$\forall V: \operatorname{FiniteTypes}\left(\right), \forall C: \operatorname{FiniteTypes}\left(\right), \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \operatorname{castQ}\left(\operatorname{assemblySum}\left(allowed, S, T, sign\right)\right) = \operatorname{factorial}\left(\operatorname{card}\left(S\right)\right) \cdot \operatorname{coeff}\left(\operatorname{card}\left(S\right), \operatorname{exp}\left(\operatorname{square}\left(\operatorname{card}\left(T\right)\right) \cdot \operatorname{colorSeries}\left(allowed, sign\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.assembly_sum_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

V and C range over all finite types. The predicate allowed(j,c) and the integer weight sign(c) are arbitrary. An assembly is the existing finite set of disjoint nonempty ordered blocks covering S, with an allowed color on each block and two ordered ambient markers in T. The notation assemblySum is the integer sum of products of the color weights over all such assemblies; its cast to Q is displayed. The two markers can coincide and can lie outside the block or outside S. The size-j signed color sum is the sum of sign(c) over colors satisfying allowed(j,c). The series colorSeries has these ordinary coefficients for j>0 and constant coefficient zero.

The proof uses the checked assembly_weight_point_recursion. For a chosen vertex x, it groups the actual root blocks by their support U. Their vertex orders have cardinality |U|!, their signed colors sum to the size-|U| color sum, and their independent markers contribute |T|^2. Erasing x identifies the possible root supports with subsets of S minus x. Mathlib's powerset-cardinality and permutation-cardinality identities give the binomial and factorial factors. Strong induction on |S| then identifies this exact recurrence with the derivative recurrence of the formal exponential, using DoldExponentialIntegrality.expSeries_derivative. The empty assembly supplies the constant term. This proves the identity in every degree without assuming any counting formula.

The factorial multiplies an ordinary coefficient; the exponent contains the ordinary signed color coefficients, without factorial rescaling. The vertex support shrinks in the induction and the marker domain T stays unchanged. In particular, a pointed assembly on S minus a vertex can retain all of S as its marker set.

Combining this identity with fixed_assembly_weight_factorization also evaluates the existing FixedAssembly sum. Write F for the vertices of S fixed by g, W for the vertices of T fixed by g, and M for the signed sum of invariant assemblies on the moved vertices with markers in T. The rational cast of the fixed-assembly sum is exactly M times |F|! times [x^|F|]exp(|W|^2 P), where P is colorSeries. The same application for the explicit prefix palette replaces P by prefixSeries. FixedAssembly here is the existing stability predicate under simultaneous vertex and marker relabeling. The actual group-action and fixedBy equivalences are proved by this module's internal action lemmas.

**Theorem 1.2 (An actual finite signed palette for every integer prefix).**

$$\forall V: \operatorname{FiniteTypes}\left(\right), \forall N: \mathbb{N}, \forall a: \operatorname{Function}\left(\mathbb{N}, \mathbb{Z}\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \operatorname{unitSigns}\left(N, a\right) \land \operatorname{castQ}\left(\operatorname{prefixAssemblySum}\left(N, a, S, T\right)\right) = \operatorname{factorial}\left(\operatorname{card}\left(S\right)\right) \cdot \operatorname{coeff}\left(\operatorname{card}\left(S\right), \operatorname{exp}\left(\operatorname{square}\left(\operatorname{card}\left(T\right)\right) \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.signed_prefix_assembly_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For any natural N and any integer sequence a, PrefixColor is the finite dependent union, over j<N, of Fin(max(a(j),0)) and Fin(max(-a(j),0)). The first component has sign +1, the second sign -1, and a color can decorate precisely a block of its own size j. The unitSigns clause states that every color has one of these two signs. The signed color sum at j is a(j) for j<N and zero otherwise, by the exact positive-minus-negative integer identity. Empty color fibers and negative entries require no additional hypothesis. The series prefixSeries has coefficient a(j) for 0<j<N and zero otherwise. Colors at zero never decorate a nonempty block.

The prefixAssemblySum uses precisely this finite palette and its unit signs in the existing Assembly type. The theorem proves both the unit-sign property and the displayed coefficient identity, for every S and T, including empty sets and degrees beyond N. For the A300591 induction, N is the current index and a is the actual integral strict prefix. This theorem supplies a counting realization of that prefix, and assumes no integrality of the next coefficient or of an exponential coefficient.

The rational source and companion identifications remain those of HannaA300591RationalModel: A300591 uses ordinary coefficients, A300590 uses the entries r! times the ordinary coefficients of exp(A), and A300598 denotes a(n)/n only for n>=1. The residual integrality theorems below supply the coprime-prime step used by the source induction.

**Theorem 1.3 (The integral strict-prefix arithmetic step).**

$$\forall N: \mathbb{N}, \forall a: \operatorname{Function}\left(\mathbb{N}, \mathbb{Z}\right), (1 \le N) \implies (\forall p: \mathbb{N}, (\operatorname{Prime}\left(p\right)) \implies ((\neg \operatorname{Dvd}\left(p, N\right)) \implies ((\forall f: \mathbb{N}, (1 \le f) \implies ((f < N) \implies (\operatorname{coeff}\left(f, \operatorname{exp}\left(\operatorname{castQ}\left(f\right)^{2} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) = \operatorname{castQ}\left(f\right)^{2} \cdot \operatorname{coeff}\left(f - 1, \operatorname{exp}\left(\operatorname{castQ}\left(f\right)^{2} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)))) \implies (\operatorname{IsRIntegralRat}\left(p, \operatorname{coeff}\left(N, \operatorname{exp}\left(\operatorname{castQ}\left(N\right)^{2} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) - \operatorname{castQ}\left(N\right)^{2} \cdot \operatorname{coeff}\left(N - 1, \operatorname{exp}\left(\operatorname{castQ}\left(N\right)^{2} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.signed_prefix_residual_local_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For every N>=1, arbitrary integer sequence a, prime p not dividing N, and P=prefixSeries(N,a), assume the actual equations with P for every 1<=f<N. Then [x^N]exp(N^2 P)-N^2[x^(N-1)]exp(N^2 P) has denominator coprime to p. The explicit unit-signed finite palette is used on Fin N. FullAssembly and PointedAssembly carry simultaneous permutation actions; the latter retains marker domain V after removing its distinguished point. Their weights are invariant. FixedBy corresponds to structural stability, and the fixed pointed objects have three fixed-vertex choices. With f fixed vertices and moved weight sum M, subtraction is M f! times the degree-f residual. Positive and negative invariant fibers give signed Burnside by Mathlib ordinary Burnside. A Sylow p-subgroup has order p^v_p(N!), and every element fixes a vertex when p does not divide N, by the p-group fixed-point theorem for its cyclic subgroup. Nonidentity elements fix fewer than N vertices, so their lower residuals vanish. At the identity the moved part is uniquely empty. The full p-power in N! divides the integer signed subtraction; padicValInt_dvd_iff and padicValRat.mul cancel its valuation exactly, with zero handled separately. No positivity, next-coefficient integrality, action fact, orbit identity, Sylow order or factorial cancellation is an unproved premise.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.assembly_sum_coefficient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.signed_prefix_assembly_coefficient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.signed_prefix_residual_local_integral`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies](HannaA300591FixedAssemblies.md)
