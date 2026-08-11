# Estimator-Error Lower Bounds from Finite Fano Inequalities

## Abstract

Finite Fano inversion turns frozen residual-uncertainty upper bounds into estimator-error lower bounds, with cardinality hypotheses isolated to division.

**Theorem 1.1 (Fano inversion lower-bounds every estimator's error mass).**

$$\begin{gathered}\forall Y, X\ [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(X)],\\\forall p: Y\times X\to \mathbb{R}, g: Y\to X,\\e:=\sum _{y, x: g(y)\neq x} p(y, x),\\((\forall y, x, 0\le p(y, x)) \land \sum _{y, x} p(y, x)=1) \Rightarrow \\\operatorname{shannonEntropy}(\operatorname{marginal}((x, y)\mapsto p(y, x)))-\operatorname{mutualInformation}(p)-\log 2\le \\e \log (\operatorname{card}(X)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoErrorBound.fano_error_product_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

What changes here is the direction of use, not the underlying inequality. The finite Fano inequalities are already frozen in the repository: they bound the residual uncertainty H(X | Y) above by a function of an estimator's error. This module solves that relation for the error and thereby obtains a lower bound that holds for every estimator g. It is a re-parameterization of those inequalities, not a new information inequality.

The displayed product form is the primary statement. The joint law p and estimator g are arbitrary, subject only to coordinatewise nonnegativity and total mass one for p. The first coordinate Y is the observation and the second coordinate X is the hidden parameter. Thus the entropy term uses the marginal of the swapped law (x,y) maps to p(y,x), while e is precisely the mass of pairs for which g(y) differs from x.

No cardinality hypothesis occurs in the product theorem. This is not an omitted edge condition: at card X = 1 its right-hand side is zero and its left-hand side is -log 2, so the statement remains faithful and vacuous. Keeping multiplication by log(card X) is what permits the primary theorem to include that degenerate case without division.

The proof's substantive bookkeeping is the binary-entropy side condition. Before the cap H_b(e) <= log 2 can be used, e must be shown to lie in [0,1]. Neither inequality is assumed. Nonnegativity follows from the nonnegative summands of p, and the upper bound follows because the error mass is a sub-sum of a distribution whose total mass is one. These facts make (e,1-e) a genuine law rather than a merely formal pair of real numbers.

The companion fano_error_probability_lower_bound divides the displayed inequality by log(card X) and therefore requires 2 <= card X, exactly the condition making that logarithm positive. This condition is needed only for division, but it is not a dispensable technicality. With one candidate there is nothing to distinguish and an error-probability floor has no content. The undivided theorem records that case honestly, which is why it remains primary.

The sharp companions replace log(card X) by log(card X - 1). The sharp product theorem assumes 2 <= card X, while its quotient form assumes 3 <= card X so that the divisor is positive. The sharp quotient is not uniformly better. Its divisor is smaller: for a positive numerator it gives a stronger floor, but for a negative, already-vacuous numerator it gives a more negative and therefore weaker floor. With numerator +0.5 and card X = 4, the standard and sharp floors are respectively 0.360674 and 0.455120; with numerator -0.5 they are -0.360674 and -0.455120. At card X = 2 the sharp coefficient is log 1 = 0, so the sharp product degenerates entirely rather than superseding the standard form.

For the form ordinarily quoted in the literature, fano_error_probability_lower_bound_uniform assumes 2 <= card X and that the swapped second-coordinate marginal is the constant law 1/card X. It then identifies the hidden-parameter entropy with log(card X) and yields error at least 1-(mutualInformation p + log 2)/log(card X). The uniformity assumption belongs to this specialization; it is absent from both general inversions.

The uniform corollary exhibits both regimes that a useful lower bound must have. For four equally likely hypotheses and an observation carrying no information, mutual information is zero and the floor is 1-log 2/log 4 = 1/2: no estimator can have error below one half. If the observation instead carries mutual information log 4, the same expression is -1/2 and imposes no constraint, as it should. Showing only the first regime would not test whether the statement releases its constraint when the observation is sufficiently informative; showing only the second would leave a worthless bound that bites nowhere.

At card X = 2 under a uniform prior, the same Fano floor reduces to -mutualInformation p/log 2. Mutual information is nonnegative, so this quantity is nonpositive and Fano is uninformative in exactly the two-hypothesis setting already covered by the repository's frozen Le Cam and testing-divergence bounds from the total-variation side. There is no contradiction: Fano is weaker there and is valuable because it extends to many hypotheses where the two-point machinery does not apply. No bridge theorem between the two families is claimed.

All five declarations are finite and nats-valued, and this module introduces no definition. It proves lower floors for arbitrary estimators but constructs no estimator attaining them, and it claims no minimax, sample-complexity, measure-theoretic, or two-point bridge theorem.

## References

- Truth anchor: `D5/S3/Estimation/FanoErrorBound.fano_error_product_lower_bound`
- Dependency: [D5/S3/Entropy/EntropyEquality](../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](../Entropy/MutualInformationEntropy.md)
- Dependency: [D5/S3/Estimation/FanoSharp](FanoSharp.md)
