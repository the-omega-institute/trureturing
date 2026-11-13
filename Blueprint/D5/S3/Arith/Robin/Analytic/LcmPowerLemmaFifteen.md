# The all-parameter LCM power comparison

## Abstract

The real power inequality and its LCM power function comparison for every kappa>1.

The parameter kappa and the variable y are real. The powers with exponent kappa are real powers; the square notation agrees with real exponent two.

**Theorem 1.1 (The strict power inequality).**

$$\forall kappa \in \mathbb{R},\; \forall y \in \mathbb{R},\; (1 < kappa \land 1 < y) \Rightarrow ((((y)^{2} + y + 1)^{kappa} - (y + 1)^{kappa})^{2} < \left(((y)^{2} + 2)^{kappa} - (2)^{kappa}\right) \cdot ((y + 1)^{kappa} - 1)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real kappa>1 and every real y>1 the displayed strict inequality holds. In particular, the parameter range includes 1<kappa<=3/2.

Set s=1/y and h=1/y^2, so 0<h<s. With B(t)=log((1+t)^kappa-t^kappa), strict concavity gives B(s+h)-B(s)<B(2h)-B(h). Concavity up to zero and B(0)=0 give B(h)>=B(2h)/2. Thus 2*(B(s+h)-B(s))<B(2h). The positive power differences allow exponentiation, and their common scaling by powers of y gives the claim.

**Definition 1.2 (The LCM power function).**

$$\forall kappa \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall a \in \mathbb{R},\; \operatorname{lcmPowerF}\left(kappa, x, a\right) = \frac{\operatorname{log}\left(\frac{((x)^{a + 1} - 1)^{kappa} - ((x)^{a} - 1)^{kappa}}{((x)^{a + 1} - x)^{kappa} - ((x)^{a} - x)^{kappa}}\right)}{kappa \cdot \operatorname{log}\left(x\right)}$$

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For real kappa, x and a this is the total real-valued expression F(kappa,x,a). All occurrences of x^(a+1), x^a and the subsequent kappa powers are real powers. The comparison below uses its positive domain x>1, kappa>1 at a=1 and a=2. This is the function in Fan, Kobayashi and Molnar, A family of analogues to the Robin criterion, Definition 4.2.

**Theorem 1.3 (Comparison at two and one).**

$$\forall kappa \in \mathbb{R},\; \forall y \in \mathbb{R},\; (1 < kappa \land \operatorname{sqrt}\left(2\right) < y) \Rightarrow (\operatorname{lcmPowerF}\left(kappa, y, 2\right) < \operatorname{lcmPowerF}\left(kappa, \frac{(y)^{2}}{2}, 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For every real kappa>1 and every real y>sqrt(2), F(kappa,y,2)<F(kappa,y^2/2,1). Both bases are strictly greater than one. There is no assumption concerning the Riemann hypothesis.

Write A=(y^2+2)^kappa-2^kappa, B=(y^2+y+1)^kappa-(y+1)^kappa and C=(y+1)^kappa-1. Factoring the cubic and quadratic expressions gives F(kappa,y,2)=log(B/(C*y^kappa))/(kappa*log(y)) and F(kappa,y^2/2,1)=log(A/y^(2*kappa))/(kappa*log(y^2/2)). Strict superadditivity of positive real powers gives A>y^(2*kappa), so the latter numerator is positive. The core inequality gives 2*log(B/(C*y^kappa))<log(A/y^(2*kappa)). Finally 0<log(y^2/2)<2*log(y), with kappa>0, gives the strict comparison.

**Theorem 1.4 (Lemma 4.15 for every kappa greater than one).**

$$\forall kappa \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall xprime \in \mathbb{R},\; (\left(1 < kappa \land 1 < x\right) \land \left(1 < xprime \land \operatorname{lcmPowerF}\left(kappa, xprime, 2\right) = \operatorname{lcmPowerF}\left(kappa, x, 1\right)\right)) \Rightarrow (xprime < \operatorname{sqrt}\left(2 \cdot x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415` (`✓ std3`). ∎

*Resolves.* `Problems/fan-kobayashi-molnar-2026-remark-4-16` (proved) by `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fan-kobayashi-molnar-2026-remark-4-16","declaration_gid":"D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For all real kappa>1 and x,xprime>1, the equation F(kappa,xprime,2)=F(kappa,x,1) implies xprime<sqrt(2*x). In the source notation x=x_1 and xprime=x_2: both are characterized by F(kappa,x_1,1)=epsilon=F(kappa,x_2,2). Thus this implication gives the assertion of Lemma 4.15 for every kappa>1 and epsilon>0. It holds for every solution of the equation, without using the source Theorem 4.3 or any existence or inverse-function theorem.

Set r=t/(1+t). The elasticity t*B'(t) equals kappa*(1-1/((1-r^kappa)/(1-r))). Strict convexity of r^kappa makes its secant slope to 1 strictly increasing, so the elasticity is strictly increasing on t>0. The derivative of g(s)=B(s+s^2)-B(s) is positive, and g itself is positive. Since F(kappa,x,2)=g(1/x)/(kappa*log(x)), this function is strictly decreasing on x>1. Apply the comparison at y=sqrt(2*x) and then this strict decrease to obtain xprime<y.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_F`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_core`
- Dependency: [D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum](../../../Analytic/Convexity/StrictConcaveSymmetricSum.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity](LcmPowerLogConcavity.md)
