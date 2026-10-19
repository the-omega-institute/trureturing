# Hirche's Binary Renyi Information Combining Conjecture

## Abstract

Hirche Conjecture IV.18 holds with threshold five quarters, including the Shannon order and all entropy endpoints.

The source assertion is the whole of Conjecture IV.18 of C. Hirche, Renyi Bounds on Information Combining, ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18. The logarithm is natural, so the entropy interval is [0,log 2]. The parameter alpha is real; it is not restricted to integers. The formal claim fixes any second entropy coordinate in the entire closed interval and proves convexity for 0 < alpha < 5/4 and concavity for alpha >= 2. The threshold witness is alphaHat = 5/4.

Conjecture IV.18 states: There exists a value 1 < α̂ < 1.3863, such that hα(hα⁻¹(x) ∗ hα⁻¹(y)) is convex for 0 < α < α̂ and concave for α ≥ 2.

**Definition 1.1 (Binary Renyi entropy).**

$$\forall (alpha: \mathbb{R}), \forall (p: \mathbb{R}), \operatorname{h}\left(alpha, p\right) = \operatorname{ite}\left(alpha = 1, \operatorname{binEntropy}\left(p\right), \frac{\operatorname{log}\left((p)^{alpha} + (1 - p)^{alpha}\right)}{1 - alpha}\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.h` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

At alpha = 1 the definition uses Real.binEntropy in natural-log units; otherwise both variable powers use Real.rpow. On the probability branch [0,1/2], for every alpha > 0, the power sum is positive and h is continuous and strictly increasing, with values zero at zero and log 2 at one half. The displayed total real definition also exists outside the parameter and probability domain of the theorem.

**Definition 1.2 (The specified inverse branch).**

$$\forall (alpha: \mathbb{R}), \forall (x: \mathbb{R}), \operatorname{hInv}\left(alpha, x\right) = \operatorname{invFunOn}\left(\operatorname{h}\left(alpha\right), \operatorname{Icc}\left(0, \frac{1}{2}\right), x\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.hInv` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

This is Function.invFunOn applied to h alpha on the closed interval [0,1/2]. For alpha > 0, that restriction is a continuous strictly increasing bijection onto [0,log 2]. Consequently, for x in the entropy interval, hInv(alpha,x) belongs to [0,1/2] and h(alpha,hInv(alpha,x))=x. The inverse is continuous on the entropy interval. No inverse identity outside that interval is claimed.

**Definition 1.3 (Binary convolution).**

$$\forall (a: \mathbb{R}), \forall (b: \mathbb{R}), \operatorname{star}\left(a, b\right) = a + b - 2 \cdot a \cdot b$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.star` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

For binary error probabilities a and b, star(a,b)=a+b-2ab is their binary convolution.

**Definition 1.4 (Entropy-coordinate combining map).**

$$\forall (alpha: \mathbb{R}), \forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{G}\left(alpha, x, y\right) = \operatorname{h}\left(alpha, \operatorname{star}\left(\operatorname{hInv}\left(alpha, x\right), \operatorname{hInv}\left(alpha, y\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.G` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

G evaluates the binary entropy after convolving the two specified inverse-branch probabilities.

**Definition 1.5 (The complete threshold conjecture).**

$$claim = \exists (alphaHat: \mathbb{R}), 1 < alphaHat \land \left(alphaHat < \frac{13863}{10000} \land \left((\forall (alpha: \mathbb{R}), (0 < alpha) \Rightarrow \left((alpha < alphaHat) \Rightarrow \forall (y: \mathbb{R}), (y \in \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right)) \Rightarrow \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right), (x \mapsto \operatorname{G}\left(alpha, x, y\right))\right)\right)) \land (\forall (alpha: \mathbb{R}), (2 \le alpha) \Rightarrow \forall (y: \mathbb{R}), (y \in \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right)) \Rightarrow \operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right), (x \mapsto \operatorname{G}\left(alpha, x, y\right))\right))\right)\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.claim` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The existential threshold is strictly between one and 13863/10000. The convex clause quantifies over all positive real orders below it, and the concave clause over all real orders at least two. Both clauses use Mathlib's full two-point inequality on the closed entropy interval, including both endpoints.

**Theorem 1.6 (Hirche Conjecture IV.18 with threshold five quarters).**

$$\exists (alphaHat: \mathbb{R}), 1 < alphaHat \land \left(alphaHat < \frac{13863}{10000} \land \left((\forall (alpha: \mathbb{R}), (0 < alpha) \Rightarrow \left((alpha < alphaHat) \Rightarrow \forall (y: \mathbb{R}), (y \in \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right)) \Rightarrow \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right), (x \mapsto \operatorname{G}\left(alpha, x, y\right))\right)\right)) \land (\forall (alpha: \mathbb{R}), (2 \le alpha) \Rightarrow \forall (y: \mathbb{R}), (y \in \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right)) \Rightarrow \operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{Icc}\left(0, \operatorname{log}\left(2\right)\right), (x \mapsto \operatorname{G}\left(alpha, x, y\right))\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirche-2020-cachin-renyi-information-combining-convexity` (proved) by `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirche-2020-cachin-renyi-information-combining-convexity","declaration_gid":"D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The witness 5/4 lies strictly between 1 and 1.3863. For every y in [0,log 2], x maps to G(alpha,x,y) is convex for every 0 < alpha < 5/4 and concave for every alpha >= 2. Symmetry of binary convolution also gives the corresponding second-coordinate statement as a mathematical consequence; the Lean result has exactly the displayed first-coordinate claim.

Set psi(t)=h(alpha,(1-t)/2) and f(t)=-psi'(t) for 0<t<1. The function f is positive, and psi decreases continuously from log 2 to zero on [0,1]. The inverse bias is t(x)=1-2hInv(alpha,x), so psi(t(x))=x. Binary convolution gives G(alpha,x,y)=psi(v t(x)), where v=t(y) belongs to [0,1].

For alpha >= 2, set n=alpha-1 and r=(1-t)/(1+t). Then the certificate transform T=(1-r^n)/(1+r^n) gives f(t)=(alpha/n)T/(1+tT). Its derivative satisfies f'(t)=f(t)F(n,r)/t. The certificate proves that r maps to F(n,r) is nondecreasing for n>=1. Since r decreases with t, the elasticity E(t)=F(n,r(t)) is nonincreasing.

Fix 0<v<1. Differentiation gives the entropy-coordinate derivative R(t)=v f(vt)/f(t). Its t derivative is v f(vt)[E(vt)-E(t)]/[t f(t)], which is nonnegative because vt<=t and E is nonincreasing. The inverse bias decreases with x. Thus the derivative of x maps to psi(v t(x)) is antitone in x, and Mathlib's derivative criterion yields concavity on the closed interval using continuity there. Only interior inverse derivatives are used.

At v=0 the transported function is constant, and at v=1 it is the identity. These two cases include the endpoint values of y. The proof therefore covers both closed-coordinate boundaries without endpoint inverse derivatives. For 0 < alpha < 1 the negative-n certificate gives the opposite elasticity sign. At alpha = 1 the binary Shannon entropy derivative is minus artanh(t), with strictly increasing elasticity t/((1-t^2)artanh(t)). For 1 < alpha <= 5/4, put n=alpha-1 and C(z)=n sqrt(z) coth(n artanh(sqrt(z))), D(z)=C(z)+nz. The desingularized even analytic quotient supplies the initial first and second derivative signs. The Riccati identity and its differentiated equation preclude a first zero of C'', and imply D'<0. Thus 1-2zD'/D is strictly increasing. This reverses the slope-ratio sign and yields closed-interval convexity.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.G`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.claim`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.h`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.hInv`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.star`
- Dependency: [D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining](BinaryRenyiCombining.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexBranch](CachinConvexBranch.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone](CachinElasticityMonotone.md)
