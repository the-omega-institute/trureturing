# Equality at the Lower Endpoint of Conditional Entropy

## Abstract

Vanishing finite conditional entropy in nats characterizes point-mass conditional laws exactly on nonzero-marginal slices.

**Theorem 1.1 (Point-mass conditionals on the marginal support force zero entropy).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, \operatorname{marginal}(p)(i)\neq 0 \Rightarrow \\\exists j, \operatorname{conditional}(p, i)=(k\mapsto \begin{cases}1,&k=j\\0,&k\neq j\end{cases})) \Rightarrow\\\operatorname{conditionalEntropy}(p)=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_of_point_mass_on_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support qualification is the central content of the statement. It does not assert a conditional point mass, or a functional dependence, on every slice. By definition, conditional p i j is p(i,j) / marginal p i, hence it is the artificial quotient 0/0 when marginal p i = 0. Such a slice contributes 0 times the Shannon entropy of that arbitrary, generally non-normalized conditional function, which is 0 regardless of the function. Vanishing conditional entropy therefore says nothing about zero-marginal slices; only slices carrying mass occur in the characterization.

A global function formulation would be false, not merely weaker. Take iota inhabited, kappa empty, and p identically zero. Every marginal vanishes, conditional entropy is zero, and the support-qualified condition holds vacuously, but no function from iota to kappa exists. Assuming Nonempty kappa would repair only the existence of an arbitrary function; it would import an unrelated hypothesis and would still suggest a dependence on zero-mass slices that the theorem does not establish.

This direction needs no nonnegativity hypothesis. On a mass-carrying slice, the displayed equality identifies the entire conditional function with a point mass, so the frozen entropy_eq_zero_iff_point_mass theorem gives zero slice entropy directly. On a zero-marginal slice, the outer marginal factor makes the summand vanish. The conclusion follows by summing these zero terms.

The equality of functions is stronger and more informative than the claim that some conditional value equals 1. It records at once that the selected value is 1 and every other value is 0; the weaker phrasing would hide the latter part of the proved statement.

**Theorem 1.2 (Zero conditional entropy forces point masses on the marginal support).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0\le p(i, j)) \Rightarrow\\\operatorname{conditionalEntropy}(p)=0 \Rightarrow\\\forall i, \operatorname{marginal}(p)(i)\neq 0 \Rightarrow \\\exists j, \operatorname{conditional}(p, i)=(k\mapsto \begin{cases}1,&k=j\\0,&k\neq j\end{cases}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ConditionalEntropyEquality.point_mass_on_support_of_conditional_entropy_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The converse requires pointwise nonnegativity. It makes every marginal nonnegative and, on a slice with nonzero marginal, makes the conditional function nonnegative. That slice is normalized directly from the definitions: summing p(i,j) / marginal p i over j gives marginal p i / marginal p i = 1. The last equality is valid exactly under the nonzero-marginal premise.

Consequently every marginal-weighted slice entropy is nonnegative. If their finite sum, conditionalEntropy p, vanishes, the vanishing-sum criterion forces each summand to vanish. On a mass-carrying slice, mul_eq_zero and the nonzero marginal isolate zero Shannon entropy for the conditional law. The frozen entropy_eq_zero_iff_point_mass theorem then converts that equality into the displayed point-mass function.

The right-hand side is not automatic from nonnegativity. For the constant law 1/2 on Unit times Bool, pointwise nonnegativity holds and the single marginal is 1, but the conditional law assigns 1/2 to both Boolean values. It is uniform rather than a point mass, so the support-qualified conclusion fails. This counterexample has been compiled and checked independently.

The conclusion remains deliberately silent on zero-marginal slices. Their summands vanish before the slice entropy can be constrained, so the converse supplies no additional dependence there.

**Theorem 1.3 (Zero conditional entropy characterizes point masses on the marginal support).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0\le p(i, j)) \Rightarrow\\(\operatorname{conditionalEntropy}(p)=0 \Leftrightarrow \\\forall i, \operatorname{marginal}(p)(i)\neq 0 \Rightarrow \\\exists j, \operatorname{conditional}(p, i)=(k\mapsto \begin{cases}1,&k=j\\0,&k\neq j\end{cases})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_iff_point_mass_on_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three declarations are retained because the two implications have different honest hypothesis sets. Point-mass conditionals imply zero conditional entropy without nonnegativity, whereas the reverse implication needs nonnegativity to turn the total into a sum of nonnegative terms and infer that each term vanishes. Inflating the first implication with hp merely to package the equivalence would weaken that result for no mathematical reason.

This equivalence characterizes the lower endpoint of the conditional-entropy line in the bucket. It matches the lower-endpoint work for the finite entropy bracket deposited in wave 23, and reuses that wave's frozen entropy_eq_zero_iff_point_mass theorem as the slice-level tool. The units are nats because shannonEntropy uses Real.log.

The result is qualitative and finite. It makes no claim about conditional mutual information, gives no continuous or measure-theoretic analogue, and provides no rate, stability theorem, or deficit estimate near the lower endpoint.

## References

- Truth anchor: `D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_iff_point_mass_on_support`
- Truth anchor: `D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_of_point_mass_on_support`
- Truth anchor: `D5/S3/Entropy/ConditionalEntropyEquality.point_mass_on_support_of_conditional_entropy_eq_zero`
- Dependency: [D5/S3/Entropy/EntropyEquality](EntropyEquality.md)
- Dependency: [D5/S3/Entropy/EntropyNonneg](EntropyNonneg.md)
