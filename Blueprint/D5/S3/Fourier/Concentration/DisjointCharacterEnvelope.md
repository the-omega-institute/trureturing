# A phase-sensitive bound for disjoint coefficients

## Abstract

The mixed coefficient bound retains the two phase sums before estimating local overlaps.

**Theorem 1.1 (Disjoint coefficient bound).**

$$\begin{aligned}&\forall J: \operatorname{Type}\left(\right), s:\operatorname{Finset}\left(J\right),\quad\forall a,b:J\to \mathbb{C},\\&\forall m,n:\mathbb{N},\quad\forall r:\mathbb{R},\quad r>0\implies\\&|[x^{m}y^{n}]P| \le \frac{|\sum_{j \in s}a\left(j\right)|^{m}|\sum_{j \in s}b\left(j\right)|^{n}}{m!n!} + \frac{\operatorname{exp}\left(r(|\sum_{j \in s}a\left(j\right)|+|\sum_{j \in s}b\left(j\right)|)\right)}{r^{m+n}}\\&\quad\cdot\sum_{T \subseteq s,0<|T| \le \operatorname{min}\left(m, n\right)}\prod_{j \in T}(\operatorname{exp}\left(r|a\left(j\right)|\right)-1)(\operatorname{exp}\left(r|b\left(j\right)|\right)-1).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DisjointCharacterEnvelope.coefficient_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set s of indices, P(x,y) is the product of the local factors exp(a(j)x) + exp(b(j)y) - 1. Each term at an index chooses only one axis or the constant, so the mixed coefficient uses disjoint supports.

Extract exp(a(j)x + b(j)y) from each factor. The remaining factor is 1 plus the product of exp(-a(j)x) - 1 and 1 - exp(-b(j)y). Expanding this product over subsets gives one product of two separate series per subset. The original exponentials have combined to the sums of a and b. Each correction factor has positive degree on both axes. A subset larger than either target degree contributes zero to the selected coefficient. The empty subset gives two pure exponentials, whose selected coefficient norms are exact. Bounding that same coefficient by the complete exponential coefficient budgets would give exp(r(|A|+|B|))/r^(m+n), where A and B are the two phase sums.

For one variable, the sum of coefficient norms is submultiplicative on absolutely summable series, by the Cauchy product and the triangle inequality. A scaled exponential contributes exp(|a|), and removal of its constant term leaves exp(|a|) - 1. Applying these two bounds to the nonempty subsets gives the estimate at radius one. Rescaling both axes gives the radius factor.

For characters on a finite cyclic group, take a(j) = w(j) times the character of the negative residue and b(j) its complex conjugate. The numerator then depends on the norm of one weighted character sum and the weights' local overlap penalties. Estimating those character sums for actual zeta zeros requires additional arithmetic information.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DisjointCharacterEnvelope.coefficient_envelope`
