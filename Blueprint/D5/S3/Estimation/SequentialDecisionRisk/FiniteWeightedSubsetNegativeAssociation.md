# Finite weighted subset laws

## Abstract

Increasing observables on finite slices with fixed positive product weights.

**Theorem 1.1 (Comparison of whole observables across adjacent ranks).**

$$\begin{gathered}\forall X: \operatorname{Type}*, U:\operatorname{Finset}(X), w:X\to \mathbb{R},\\{}\forall f:\operatorname{Finset}(X)\to \mathbb{R}, k:\mathbb{N}, (\forall i\in U,0<\operatorname{w}(i)) \land k<\operatorname{card}(U) \land\\{}(\forall S,T:\operatorname{Finset}(X), \operatorname{subset}(S, T) \land \operatorname{subset}(T, U) \Rightarrow\operatorname{f}(S)\leq\operatorname{f}(T)) \Rightarrow\\{}\operatorname{E}(U, w, k, f)\leq\operatorname{E}(U, w, k+1, f)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_rank_comparison` (`✓ std3`). ∎

*Citation.* Julius Borcea; Petter Brändén; Thomas M. Liggett (2009). *Negative dependence and the geometry of polynomials*. DOI: [10.1090/S0894-0347-08-00618-8](https://doi.org/10.1090/S0894-0347-08-00618-8). URL: <https://arxiv.org/abs/0707.2340v2>.

*Commentary.*

Let U be any finite set in an arbitrary carrier, and fix one weight function w with w(i)>0 for every i in U. For every natural k<=|U|, write Z_k(U)=sum_{S subset U, |S|=k} product_{i in S} w(i), and E_k(h)=sum_{S subset U, |S|=k} product_{i in S} w(i) h(S) / Z_k(U). Every legal denominator is positive. The zero-rank and full-rank laws are point masses, including the unique empty law when U is empty.

For an arbitrary real-valued f, assume f(S)<=f(T) whenever S subset T subset U. No sign condition is imposed. Then E_k(f)<=E_(k+1)(f) for every k<|U|, with exactly the same weights on both sides. Monotonicity is imposed on the whole Boolean subcube, so it compares configurations in different ranks.

For U obtained by adjoining i to V, decompose each slice according to membership of i. Newton's coefficient inequality makes the probability of including i increase with the rank. Induction compares the two conditional whole observables f(S) and f(S union {i}); their pointwise order compares the overlapping rank. The resulting convex combinations are ordered. The first and last ranks follow directly by averaging f(empty)<=f(S)<=f(U).

For the actual compensated experiment, retain the original support size q0, parameter r, experiment e and complete observation o. Under 1<=q0<M, 0<r<1 and rq0/(M-q0)<1, FiniteSupportSelectionBayes.finite_support_bayes supplies strictly positive weights w(i)=weight(q0,r,e,o,i) and posterior(S)=product_{i in S}w(i)/Z_q0(Fin M). Apply the rank comparison to this one fixed function w. An auxiliary rank k changes only the subset size in E_k; it never changes q0 in the compensation or recomputes weight(k,r,e,o,i).

The actual posterior expectation equals E_q0 for these fixed weights, so its comparison with adjacent auxiliary ranks is an exact finite consequence. Empty and full ranks remain legal for the generic law even though the compensated observation model is asserted only in its original interior parameter domain. Independent tie priorities can fix observables or blocks after conditioning. This application asserts no unknown-direction posterior mixture, process limit, uniform asymptotic estimate or novelty.

**Theorem 1.2 (Negative association on disjoint Boolean blocks).**

$$\begin{gathered}\forall X: \operatorname{Type}*, [\operatorname{DecidableEq}(X)], U,A,B:\operatorname{Finset}(X), w:X\to \mathbb{R},\\{}\forall q:\mathbb{N}, f,g:\operatorname{Finset}(X)\to \mathbb{R}, \operatorname{positiveOn}(w, U) \land q\leq\operatorname{card}(U) \land\\{}\operatorname{subset}(A, U) \land \operatorname{subset}(B, U) \land \operatorname{disjoint}(A, B) \land \operatorname{increasingOn}(f, \operatorname{powerset}(A)) \land \operatorname{increasingOn}(g, \operatorname{powerset}(B)) \Rightarrow\\{}\operatorname{E}(U, w, q, \operatorname{blockProduct}(f, A, g, B))\leq\operatorname{E}(U, w, q, \operatorname{block}(f, A)) \operatorname{E}(U, w, q, \operatorname{block}(g, B))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_negative_association` (`✓ std3`). ∎

*Citation.* Julius Borcea; Petter Brändén; Thomas M. Liggett (2009). *Negative dependence and the geometry of polynomials*. DOI: [10.1090/S0894-0347-08-00618-8](https://doi.org/10.1090/S0894-0347-08-00618-8). URL: <https://arxiv.org/abs/0707.2340v2>.

*Commentary.*

For the same finite U and fixed strictly positive w, let q be any natural number with q<=|U|. Let A and B be disjoint subsets of U. Let f and g be arbitrary signed real functions on subsets, inclusion-increasing on all subsets of A and B respectively. Then E_q(f(S intersect A)g(S intersect B))<=E_q(f(S intersect A))E_q(g(S intersect B)). All three expectations use the identical normalized product-weight q-slice law. No coupling, rank comparison or negative dependence property is assumed. Empty U, empty blocks, q=0, q=|U| and constants are included.

Split U into A and C=U without A, and condition on k=|S intersect A|. The product weight factors, so the two restrictions have independent weighted slice laws of ranks k and q-k. The conditional mean F(k) of f increases with k by the rank comparison. The conditional mean G(k) of g decreases with k, since B is a subset of C and q-k decreases. Only feasible ranks have positive mass. For every two such ranks, (F(k)-F(l))(G(k)-G(l))<=0. Summing this inequality with the product of their nonnegative masses gives the covariance inequality. This finite argument permits signed observables throughout.

In the actual compensated experiment retain q0, r, e and o in the positive weight function supplied by finite_support_bayes. At rank q0 its slice law is exactly posterior(r,e,o). Substituting into the three finite expectations therefore gives the same negative-association inequality for the actual posterior and every pair of disjoint blocks fixed after conditioning on the complete observation and any independent tie priority. Auxiliary rank comparisons use weight(q0,r,e,o) throughout. The actual experiment retains 1<=q0<M, 0<r<1 and compensation(M,q0,r)<1. No claim about an unknown-direction posterior mixture or an asymptotic process follows from this finite statement.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_negative_association`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_rank_comparison`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../Analytic/RealRootedCoefficientNewton.md)
