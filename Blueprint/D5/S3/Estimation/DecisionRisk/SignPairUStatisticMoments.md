# Moments of the sign pair U-statistic

## Abstract

Independent signs with common mean have explicit first and second moments for their normalized pair statistic.

**Definition 1.1 (Product weight of a sign vector).**

$$\forall k: \mathbb{N}, mu: \mathbb{R}, eta: (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z})),\\{}\operatorname{signPairWeight}(mu, eta) = \prod_{{i \in \operatorname{Fin}(k)}} {\frac{1+mu eta(i)}{2}}.$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.signPairWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate assigns masses (1 + mu eta_i) / 2 to its two signs. The weight of a sign vector is the product of these coordinate masses.

**Definition 1.2 (Normalized second-order sign statistic).**

$$\forall k: \mathbb{N}, eta: (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z})),\\{}\operatorname{signPairUStatistic}(eta) = \frac{{\sum_{{i \in \operatorname{Fin}(k)}} {eta(i)}}^{2}-k}{k(k-1)}.$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.signPairUStatistic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The statistic subtracts the diagonal contribution from the square of the sign sum and normalizes by the number of ordered distinct pairs.

**Theorem 1.3 (Pair representation, mean, and variance).**

$$\begin{gathered}\forall k: \mathbb{N}, mu: \mathbb{R},\\{}2\leq k, -1\leq mu, mu\leq 1 \Rightarrow\\{}(\forall eta: (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z})), \operatorname{signPairUStatistic}(eta) = \frac{\sum_{{i<j, i,j \in \operatorname{Fin}(k)}} {eta(i)eta(j)}}{\operatorname{choose}(k, 2)}) \land\\{}\sum_{{eta \in (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z}))}} {\operatorname{signPairWeight}(mu, eta) \operatorname{signPairUStatistic}(eta)} = mu^{2} \land\\{}\sum_{{eta \in (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z}))}} {\operatorname{signPairWeight}(mu, eta) \operatorname{signPairUStatistic}(eta)^{2}}-{\sum_{{eta \in (\operatorname{Fin}(k) \to \operatorname{Units}(\mathbb{Z}))}} {\operatorname{signPairWeight}(mu, eta) \operatorname{signPairUStatistic}(eta)}}^{2} = \frac{4mu^{2}(1-mu^{2})}{k}+\frac{2{1-mu^{2}}^{2}}{k(k-1)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.sign_pair_u_statistic_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the square identifies the statistic with the average product over unordered coordinate pairs. Product factorization gives the expectation of every sign character as mu raised to the number of coordinates in that character.

For the second moment, equal pairs contribute the squared centered second moment. Pairs sharing one coordinate and disjoint pairs vanish after centering. Counting the surviving pairs and simplifying yields the stated variance.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.signPairUStatistic`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.signPairWeight`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.sign_pair_u_statistic_moments`
