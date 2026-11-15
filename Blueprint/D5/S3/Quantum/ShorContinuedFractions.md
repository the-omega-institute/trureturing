# Conditional Shor candidate membership

## Abstract

Conditional continued-fraction membership for actual modular phase estimation

Parameters is the actual padded modular-multiplication model: modulus N at least two, base coprime to N, and an independently chosen target width whose dimension holds the residues. The counting width n gives Q equal to two to the n. The true order r is positive and strictly smaller than N. The candidate algorithm takes only y.val, Q and N; s and r occur in the theorem's conditions, not as algorithm inputs.

**Theorem 1.1 (Reduced phase candidate).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall s \in \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right),\; \forall y \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{modulus}\left(c\right)^{2} \le 2^{n} \Rightarrow \left(\operatorname{Nearest}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, y\right) \Rightarrow \left(\operatorname{reduced}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right) \in \operatorname{candidates}\left(\operatorname{val}\left(y\right), 2^{n}, \operatorname{modulus}\left(c\right)\right) \land \operatorname{Dvd}\left(\operatorname{den}\left(\operatorname{reduced}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right)\right), \operatorname{period}\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorContinuedFractions.shor_nearest_candidate` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

For every c, n, hsize : N squared at most Q, s : Fin r and y : Fin Q, the hypothesis is the existing circular Nearest Q (s.val / r) y. The conclusion places the distinguished reduced s/r in candidates and says that this fraction's denominator divides r. Its denominator is exactly r divided by gcd(s.val,r), by the generic rational denominator formula. No assertion is made that every list entry divides the order.

Nearest means that some integer z makes the absolute difference s.val/r minus y.val/Q minus z at most 1/(2Q). Since s.val is below r, y.val is below Q and r is below N, the resolution N squared at most Q excludes nonzero z. This includes s equal to zero and either non-strict rounding tie. The reduced denominator is at most r and its square is strictly below Q, converting the non-strict grid error into the strict Legendre bound. Mathlib's existing Legendre theorem supplies a real-convergent index. The exact finite-list correspondence supplies membership, and the denominator bound passes the observable filter.

**Theorem 1.2 (Coprime true-order membership).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall s \in \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right),\; \forall y \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{modulus}\left(c\right)^{2} \le 2^{n} \Rightarrow \left(\operatorname{Nearest}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, y\right) \Rightarrow \left(\operatorname{Coprime}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right) \Rightarrow \operatorname{period}\left(c\right) \in \operatorname{mapRatDen}\left(\operatorname{candidates}\left(\operatorname{val}\left(y\right), 2^{n}, \operatorname{modulus}\left(c\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

Under the same hypotheses and Nat.Coprime s.val r, the true order r belongs to the list obtained by mapping Rat.den over candidates. mapRatDen in the displayed statement denotes this map. The proof consumes reduced-phase membership and the exact denominator formula with gcd equal to one. This establishes existence within observable candidates; it does not provide an observable certified selector of the exact order.

The generic list admits zero and integer rationals, and the recovery theorem admits r equal to one and s equal to zero. Since N is at least two, the recovery resolution excludes n equal to zero; the existing QPE marginal still admits that counting width. No assumption r divides Q is used. A passing modular exponentiation test alone says that the tested exponent is a multiple of the order, by the pinned orderOf_dvd_iff_pow_eq_one theorem. Exactness needs additional information.

For a single actual counting measurement, fix any c : QuantumShorOrderFindingCore.Parameters and n : Nat with N squared at most Q, where N = c.modulus, r = c.period and Q = 2^n. Use exactly the existing modularOperator and input of c: the target starts in computational basis state one, the residue permutation fixes padding, and the counting and target widths remain independent. Let E be the finite set of y : Fin Q for which r belongs to (candidates y.val Q N).map Rat.den. Thus E records that the observable candidate list contains the true order. The algorithm still takes only y.val, Q and N; r defines its success event and is not supplied to it.

Write p(y) for the actual complete target-register marginal normSquared (runQPE c.modularOperator n c.input y), k(s,y) for probability Q (s.val / r) y, and A for 4 / Real.pi squared. All quotients and probability sums below are real after casting natural values. The notation sum(i,T,f) means the finite sum of f over i in T. Normalization of the actual marginal makes its sum over E the probability of this single-run list-membership event. The resulting application of the existing results is

$\operatorname{sum}\left(y, E, \operatorname{p}\left(y\right)\right) \ge \frac{4}{\mathit{pi}^{2}} \cdot \frac{\operatorname{totient}\left(r\right)}{r}$

To obtain an admissible label for each s : Fin r, round the real number Q times s.val / r to an integer m. The pinned abs_sub_round gives absolute rounding error at most one half. Here 0 < r < N and N squared at most Q imply r < Q. Since 0 is at most s.val and s.val + 1 is at most r, these inequalities give 0 at most m and m < Q. Taking y.val = m and the integer shift zero in Nearest gives the required circular error at most 1/(2Q). The argument permits s equal to zero and either non-strict midpoint tie; it does not require a unique nearest label.

Let C be the finite set of s : Fin r with Nat.Coprime s.val r. For each s in C, `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate` puts the chosen nearest label in E, and `D5/S3/Quantum/ShorCountingMarginal.shor_phase_accuracy_bound` gives k(s,y) at least A there. Each kernel value is a squared complex norm and hence nonnegative, so sum(y,E,k(s,y)) is at least A for s in C and at least zero for every other phase. This bounds event mass within each component before combining the components; no distinctness of the chosen labels is needed.

The exact actual-input identity `D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture` and interchange of finite sums give

$\operatorname{sum}\left(y, E, \operatorname{p}\left(y\right)\right) = \frac{1}{r} \cdot \operatorname{sum}\left(s, \operatorname{Fin}\left(r\right), \operatorname{sum}\left(y, E, \operatorname{k}\left(s, y\right)\right)\right)$

Summing the component bounds and multiplying by the positive weight 1/r therefore gives

$\operatorname{sum}\left(y, E, \operatorname{p}\left(y\right)\right) \ge \frac{1}{r} \cdot \operatorname{sum}\left(s, C, A\right)$

Fin.sum_univ_eq_sum_range identifies the phase sum with the range from zero to r exclusive. Nat.coprime_comm matches the predicate to the pinned Nat.totient definition, so C has exactly Nat.totient r elements. The last constant sum is therefore (Nat.totient r) times A, giving the displayed bound. This is a count in the actual spectral mixture, with no independently sampled latent-phase hypothesis. The derivation includes r equal to one and phase zero, needs no divisibility between r and Q, and adds no restriction on n to the original resolution; N at least two and N squared at most Q already exclude widths zero and one.

The supplied actual QPE uses the inverse final Fourier transform. Using the chapter's positive Fourier convention reflects the observed grid label through negation modulo Q, as described by the owning counting-marginal result. One must apply the nearest condition to the reflected label before using this recovery statement. More explicitly, let rho be finEquiv.symm applied to negative finEquiv of the label. For a positive-Fourier output b, the corresponding success event is rho(b) in E, so candidates is evaluated at rho(b).val. The existing target-vector correspondence and this involutive permutation give that reflected event the same probability sum and lower bound. The formula above uses the supplied inverse-QFT labels; it does not identify the unreflected positive-Fourier candidate event with E. The normalization and existing pointwise peak lower bound are unchanged.

The deterministic membership theorems supply the conditional recovery step; the single-run event bound follows from their composition with the actual mixture, the phase peak bound and the finite coprime count. It establishes list membership success only. It supplies no exact-order selector, assertion that all candidate denominators divide r, repeated-sample independence, ideal least-common-multiple product law, factoring reduction, full bit or gate complexity, hardware guarantee or empirical performance. A finite recursively generated list alone supplies no such complexity claim. The general supplied-R clock statement remains broader than this actual modular N-bound specialization.

The classical postprocessing event has a separate finite-group description. Let I be any nonempty finite index type, let each G(i) be a finite cyclic group, and specify epsilon(i) of order two. For an actual tuple x in the product, put d(i) = orderOf(x(i)), m = orderOf(x), and v(i) = d(i).factorization(2). Define Good(x) by Even(m) and x^(m/2) unequal to the tuple epsilon. Then failure of Good(x) is equivalent to existence of a natural t with v(i) = t for every i. The product group need not be cyclic, and the factor sizes can differ. Identity elements and nonidentity elements of odd order remain in the domain. For a singleton I every tuple fails this event. This is the common binary-valuation argument in Section 5, page 16 of Shor, as cited in Library/QuantumChannels/shor1997gateorbits.md; the statement is an application of the pinned finite-group and factorization results.

Here is the complete algebraic correspondence. Mathlib's Pi.orderOf expresses m as the least common multiple of the positive d(i), and Finset.factorization_lcm expresses its binary valuation as the maximum of the v(i). For an even positive multiple M of the order d of an element g in a cyclic factor, (g^(M/2))^2 = 1. The count IsCyclic.card_orderOf_eq_totient at order two, together with Nat.totient_two, makes epsilon the unique element of order two. Thus g^(M/2) equals epsilon exactly when it is unequal to the identity. By orderOf_dvd_iff_pow_eq_one, the complementary identity condition is d dividing M/2. Nat.dvd_div_iff_mul_dvd rewrites this as 2*d dividing M; Nat.factorization_le_iff_dvd and Nat.factorization_mul reduce it to d.factorization(2) strictly below M.factorization(2), since the factorization inequalities at every other prime already follow from d dividing M. Therefore the actual local half-power equals epsilon exactly when those two binary valuations agree. Applying this with M = m in every coordinate proves the even-order case. If m is odd, all v(i) vanish and Good already fails.

For the actual arithmetic application take any odd natural N greater than one. Index I by the distinct prime factors p in N.primeFactors, and take G(p) = (ZMod (p^(N.factorization p))) units. These are the full prime-power moduli, including exponents greater than one. The index is nonempty; every exponent N.factorization p is positive and every p is odd. ZMod.isCyclic_units_of_prime_pow supplies cyclicity. In each factor, epsilon(p) is the literal unit -1. Its square is one and it differs from one: ZMod.neg_one_eq_one_iff permits equality only for modulus one or two, whereas p is at least three and p^(N.factorization p) is at least p. Hence its order is two.

The arithmetic equivalence E from (ZMod N) units to the product of these actual G(p) is the composition of Units.mapEquiv applied to (ZMod.equivPi N hN).toMulEquiv and MulEquiv.piUnits, where hN proves N unequal to zero. MulEquiv.orderOf_eq preserves the order of every unit, map_pow preserves every natural power, and the ring equivalence sends the literal -1 to the coordinatewise literal -1. Consequently the actual event Even(orderOf u) and u^(orderOf u/2) unequal to -1 corresponds exactly to Good(E(u)). Its complement corresponds to the set of actual tuples whose local binary order valuations all agree. No replacement distribution or independent phase variable enters this correspondence.

Restrict E with Equiv.subtypeEquiv to obtain a bijection between the actual failing units and the common-valuation tuples. Nat.card_congr gives equal cardinalities for these event subtypes. On the whole carriers, Nat.card_congr and Nat.card_pi give card((ZMod N) units) equal to the product of card(G(p)). Therefore uniform sampling of the full unit group transports to uniform sampling of the full product, and the failure mass is exactly the common-valuation tuple count divided by that product cardinality. The identity is included on both sides. These exact event and cardinality transports identify the count to which the finite cyclic-product estimate applies.

`D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization.failure_count_le` supplies the actual-product count used here.

The finite cyclic-product estimate bounds the common-valuation tuple count times 2^(k-1) by the full product cardinality, where k is the number of distinct prime factors. Its anchored Boolean encoding and the same actual-unit CRT correspondence give uniform Good mass at least 1 - 1/2^(k-1). Non-prime-power N has at least two distinct prime factors by the pinned prime-factor-cardinality characterization, so this mass is at least one half. The count and its normalization are developed in the owning finite-group result. For every N greater than two, the true-order Good event also implies both proper nontrivial gcd factors simultaneously, each dividing N. Coprimality supplies positivity of every original natural representative; order minimality excludes half-power one, Good excludes half-power minus one, and symmetric coprime cancellation in the squared-difference product proves the two strict gcd bounds. The owning finite-group exposition gives the exact original-power and canonical-representative correspondence via congruence, including the lower bounds needed for natural subtraction. Adjoining these factor certificates to the same Good event gives an equivalent success subtype with equal cardinality, so the identical uniform probability bound applies to the certified event. Identity remains sampled and has false Good; arbitrary positive congruent representatives are retained. The synchronization statement itself also applies when N is a prime power; it gives no positive success bound in that case. The unit sampling law and the counting-register distribution above describe different random choices, so their probabilities require their own joint sampling assumptions before they can be combined.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization.failure_count_le`
- Truth anchor: `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate`
- Truth anchor: `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate`
- Truth anchor: `D5/S3/Quantum/ShorContinuedFractions.shor_nearest_candidate`
- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.shor_phase_accuracy_bound`
- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture`
- Dependency: [D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents](../../S1/Depth/ContinuedFractions/FiniteRationalConvergents.md)
- Dependency: [D5/S3/Quantum/ShorCountingMarginal](ShorCountingMarginal.md)
