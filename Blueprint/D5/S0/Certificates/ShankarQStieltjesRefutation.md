# Shankar Q Stieltjes Refutation

## Abstract

An exact degree-ten polynomial certificate excludes every positive measure with finite moments on the nonnegative half-line for Shankar's Q closed form.

**Definition 1.1 (The published closed form).**

$$\begin{gathered}\operatorname{closedFormQ}\left(0\right)=1,\\{}\forall k\in \mathbb{N},1\leq k\Rightarrow\\{}\operatorname{closedFormQ}\left(k\right)=\frac{\operatorname{binom}\left(2k, k\right)}{k+1}+\sum_{b=1}^{k-1}\sum_{c=0}^{b}(\operatorname{binom}\left(2k-b-c, k-b\right)-\operatorname{binom}\left(2k-b-c, k-b-1\right))\cdot\sum_{r=b}^{k-1}(\operatorname{binom}\left(r+b-1, b-1\right)-\operatorname{binom}\left(r+b-1, b-2\right))\cdot\operatorname{binom}\left(k-1-r+c, c\right)\end{gathered}$$

*Formalization.* `D5/S0/Certificates/ShankarQStieltjesRefutation.closedFormQ` (`✓ std3`).

*Citation.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

closedFormQ maps natural numbers to integers. All summation bounds are inclusive. binom(m,j) is zero for j negative or greater than m, and is the ordinary binomial coefficient otherwise. Subtraction in the lower indices is integer subtraction, so the b=1 term has E(r,1)=1. The b-sum is empty when k=1. The Lean definition uses Mathlib's catalan; catalan_eq_centralBinom_div and succ_mul_catalan_eq_centralBinom justify the displayed Catalan fraction.

Shankar, arXiv:2608.30002v2, Theorem 7.1 identifies this formula with the number of 321-avoiding lattice words containing k copies of each of 1,2,3. That source-to-count identification is a published input, not a Lean theorem or axiom here. The kernel statements below concern the displayed closed form. Conjecture 9.5 also mentions B, which this result does not settle.

**Definition 1.2 (Integer polynomial coefficients).**

$$\begin{gathered}\operatorname{certificate}\left(0\right)=101118710150832431671196796252649512231806\\{}\operatorname{certificate}\left(1\right)=-662677669268533938101716987475663620965666\\{}\operatorname{certificate}\left(2\right)=1548486277071801438600832338542573144101640\\{}\operatorname{certificate}\left(3\right)=-1800082554673557385076101398989780036003293\\{}\operatorname{certificate}\left(4\right)=1196307300703816610151657807611194412954834\\{}\operatorname{certificate}\left(5\right)=-487410702796750216586043273691945221737851\\{}\operatorname{certificate}\left(6\right)=125698717484820716392581080465507901682426\\{}\operatorname{certificate}\left(7\right)=-20562809439083017274073234871446233006372\\{}\operatorname{certificate}\left(8\right)=2065883321354005872852404249559173330738\\{}\operatorname{certificate}\left(9\right)=-116172686339782400824354774056669210149\\{}\operatorname{certificate}\left(10\right)=2797672051379430758385367063062351871\end{gathered}$$

*Formalization.* `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The domain is Fin(11) and the codomain is the integers. Coefficients are listed in ascending degree: p(t) is the sum of certificate(i) times t to the power i. Exact rational elimination produced this primitive integer witness. No floating-point value is used in Lean.

**Theorem 1.3 (Exact negative quadratic form).**

$$\sum_{i:\operatorname{Fin}\left(11\right)}\sum_{j:\operatorname{Fin}\left(11\right)}\operatorname{certificate}\left(i\right)\cdot\operatorname{certificate}\left(j\right)\cdot\operatorname{closedFormQ}\left(i+j+3\right)=-7376954157543403276318358565675383034355744240767681002284188705571519096491185$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Kernel reduction verifies all needed closed-form values before checking the integer quadratic form. The private checked-value vector is proved equal to the formula on Fin(24); it does not define the sequence.

**Lemma 1.4 (Strict negativity).**

$$\sum_{i:\operatorname{Fin}\left(11\right)}\sum_{j:\operatorname{Fin}\left(11\right)}\operatorname{certificate}\left(i\right)\cdot\operatorname{certificate}\left(j\right)\cdot\operatorname{closedFormQ}\left(i+j+3\right)<0$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The strict sign follows from the checked integer value and is used in the no-representation theorem.

**Lemma 1.5 (Positive measures give nonnegative shifted forms).**

$$\begin{gathered}\forall \mu:\operatorname{Measure}\left(\mathbb{R}\right),((\operatorname{AE}\left(\mu, t\mapsto 0\leq t\right))\land(\forall a\in \mathbb{N},\operatorname{Integrable}\left(t\mapsto t^{a}, \mu\right)))\Rightarrow\\{}\forall n,s\in \mathbb{N},\forall d:\operatorname{Fin}\left(n\right)\to \mathbb{R},\\{}0\leq\sum_{i:\operatorname{Fin}\left(n\right)}\sum_{j:\operatorname{Fin}\left(n\right)}\operatorname{d}\left(i\right)\cdot\operatorname{d}\left(j\right)\cdot\int_{\mathbb{R}}t^{i+j+s}\,d\mu(t)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ShankarQStieltjesRefutation.moment_quadratic_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Measure(R) denotes positive Borel measures. AE(mu,t maps to P(t)) means P holds mu-almost everywhere. Each monomial is integrable. Constant multiplication and finite sums therefore justify moving both sums through the integral. Expanding the square identifies the form with the integral of t^s times the square of the finite polynomial; the integrand is nonnegative on the support.

**Theorem 1.6 (No Stieltjes representation of the closed form).**

$$\begin{gathered}\neg \exists \mu:\operatorname{Measure}\left(\mathbb{R}\right),(\operatorname{AE}\left(\mu, t\mapsto 0\leq t\right))\land\\{}(\forall a\in \mathbb{N},\operatorname{Integrable}\left(t\mapsto t^{a}, \mu\right))\land\\{}(\forall n\in \mathbb{N},\int_{\mathbb{R}}t^{n}\,d\mu(t)=\operatorname{closedFormQ}\left(n\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ShankarQStieltjesRefutation.closed_form_not_stieltjes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The theorem has no assumed sequence values or positivity hypotheses: it denies the existence of a measure satisfying all three displayed conditions. Specializing the preceding positivity lemma to n=11, s=3, and the real casts of the integer certificate contradicts strict negativity. Through published Theorem 7.1 this refutes the Q clause of Conjecture 9.5. A bounded later-literature search found no settlement; novelty remains suspected and independent source review is required.

## References

- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate`
- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate_negative`
- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.certificate_value`
- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.closedFormQ`
- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.closed_form_not_stieltjes`
- Truth anchor: `D5/S0/Certificates/ShankarQStieltjesRefutation.moment_quadratic_nonnegative`
