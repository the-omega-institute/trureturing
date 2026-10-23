# Reflection cancels a Pöschl–Teller logarithmic coefficient

## Abstract

Reflection of the generalized Bernoulli coefficient polynomials forces g(2,3,beta,3,1) to vanish. The admissible choice beta = pi/4 therefore refutes the nonvanishing conjecture in Fucci and Stanfill's Remark B.3.

**Definition 1.1 (The real binomial power of the Bernoulli series).**

$$\forall a: \mathbb{R}, \operatorname{bernoulliPower}\left(a\right) = \operatorname{PowerSeries.mk}\left(\operatorname{fun} n: \mathbb{N} \mapsto \sum_{k\in \operatorname{Finset.range}\left(n + 1\right)} (\frac{\operatorname{Polynomial.eval}\left(a, \operatorname{descPochhammer}\left(\mathbb{R}, k\right)\right)}{(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(k\right)\right): \mathbb{R})} \cdot \operatorname{PowerSeries.coeff}\left(n, \left(\operatorname{bernoulliPowerSeries}\left(\mathbb{R}\right) - 1\right)^{k}\right))\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.bernoulliPower` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

DLMF 24.16.1 specifies the generalized Bernoulli generating function. Its real power is the binomial series in bernoulliPowerSeries(R) minus one. descPochhammer(R,k) is the descending Pochhammer polynomial, eval is polynomial evaluation, and Nat.factorial is the factorial. The coefficient of degree n needs only k <= n, since the subtracted series has zero constant coefficient.

**Definition 1.2 (The generalized Bernoulli generating function).**

$$\forall a: \mathbb{R}, \forall x: \mathbb{R}, \operatorname{generalizedBernoulliSeries}\left(a, x\right) = \operatorname{bernoulliPower}\left(a\right) \cdot \operatorname{PowerSeries.rescale}\left(x, \operatorname{PowerSeries.exp}\left(\mathbb{R}\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.generalizedBernoulliSeries` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Multiplication by the rescaled exponential inserts the factor exp(x t). PowerSeries.rescale multiplies the coefficient of degree n by x^n.

**Definition 1.3 (Generalized Bernoulli polynomials).**

$$\forall n: \mathbb{N}, \forall a: \mathbb{R}, \forall x: \mathbb{R}, \operatorname{generalizedBernoulli}\left(n, a, x\right) = (\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(n\right)\right): \mathbb{R}) \cdot \operatorname{PowerSeries.coeff}\left(n, \operatorname{generalizedBernoulliSeries}\left(a, x\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.generalizedBernoulli` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The generating function uses exponential coefficients: multiplying the nth ordinary power-series coefficient by n! yields B_n^(a)(x).

**Definition 1.4 (The Bernoulli correction C).**

$$\forall m: \mathbb{N}, \forall y: \mathbb{R}, \operatorname{C}\left(m, y\right) = \sum_{j\in \operatorname{Finset.range}\left(m\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(2 \cdot m - 1, 2 \cdot j\right)\right): \mathbb{C}) \cdot \frac{2^{2 \cdot m} \cdot \operatorname{Complex.ofReal}\left(y\right)^{2 \cdot j}}{(\operatorname{Nat.cast}\left(m - j\right): \mathbb{C})} \cdot (\operatorname{Rat.cast}\left(\operatorname{bernoulli}\left(2 \cdot \left(m - j\right)\right)\right): \mathbb{C}))$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.C` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Appendix B's definition of C_m is the finite sum over j = 0,...,m-1. Nat.choose is the natural binomial coefficient and bernoulli is Mathlib's rational Bernoulli number. Complex.ofReal, Nat.cast and Rat.cast display the real, natural and rational embeddings into C. Natural subtraction is truncated; in this sum m-j is positive. All displayed fractions are field division, with Lean's totalized value zero at a zero denominator.

**Definition 1.5 (The coefficient E).**

$$\forall k: \mathbb{N}, \forall y: \mathbb{R}, \operatorname{E}\left(k, y\right) = 2 \cdot \left(2 \cdot \operatorname{Complex.ofReal}\left(y\right)\right)^{2 \cdot k - 1} - \frac{\left(2 \cdot \operatorname{Complex.ofReal}\left(y\right)\right)^{2 \cdot k}}{(\operatorname{Nat.cast}\left(k\right): \mathbb{C})} - \operatorname{C}\left(k, y\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.E` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Equation (B.17) defines E_k. Natural exponents are used literally; the source uses this expression for k >= 1.

**Definition 1.6 (The generalized Bernoulli coefficient G).**

$$\forall k: \mathbb{N}, \forall x: \mathbb{R}, \forall y: \mathbb{R}, \operatorname{G}\left(k, x, y\right) = \operatorname{Complex.ofReal}\left(\frac{\operatorname{Polynomial.eval}\left(x - y, \operatorname{descPochhammer}\left(\mathbb{R}, k\right)\right)}{(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(k\right)\right): \mathbb{R})} \cdot \operatorname{generalizedBernoulli}\left(k, x - y + 1, x\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.G` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Appendix B defines G_k(x,y) as the real binomial coefficient times B_k^(x-y+1)(x), embedded into C. The real binomial coefficient is the evaluation of descPochhammer divided by k!.

**Definition 1.7 (The logarithmic denominator indeterminate).**

$$\forall j: \mathbb{N}, \forall y: \mathbb{R}, \operatorname{scriptE}\left(j, y\right) = \operatorname{ite}\left(j = 0, 1, \operatorname{Polynomial.C}\left(\frac{\operatorname{E}\left(j, y\right)}{2}\right) \cdot \operatorname{Polynomial.X}\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.scriptE` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The indeterminate Polynomial.X represents T = sin(alpha)/[-cos(alpha)+sin(alpha)(gamma_E+ln(z^(1/2))-ln 2-i pi/2)]. Thus scriptE(0,y) = 1 and scriptE(j,y) = Polynomial.C(E(j,y)/2) times Polynomial.X for j >= 1. Polynomial.C embeds a complex scalar as a constant polynomial; ite is conditional choice.

**Definition 1.8 (The coefficient polynomial P).**

$$\forall k: \mathbb{N}, \forall y: \mathbb{R}, \operatorname{P}\left(k, y\right) = \operatorname{ite}\left(k = 0, 1, \sum_{j\in \operatorname{Finset.range}\left(k + 1\right)} (4^{k - j} \cdot \operatorname{scriptE}\left(j, y\right) \cdot \operatorname{Polynomial.C}\left(\operatorname{G}\left(2 \cdot \left(k - j\right), 1 - y, y\right)\right))\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.P` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The source defines P_0 = 1 and the displayed finite sum for positive k. The numeral 4 in this formula is a constant polynomial over C. These general definitions, rather than the special displayed P_1, determine every coefficient.

**Definition 1.9 (The constant factor Omega0).**

$$\forall nu: \mathbb{R}, \forall beta: \mathbb{R}, \operatorname{Omega0}\left(nu, beta\right) = \frac{\operatorname{Complex.ofReal}\left(\operatorname{Real.rpow}\left(2, 2 \cdot nu - 1\right)\right) \cdot \operatorname{Complex.Gamma}\left(1 + \operatorname{Complex.ofReal}\left(nu\right)\right)}{\operatorname{Complex.Gamma}\left(-\operatorname{Complex.ofReal}\left(nu\right)\right)} \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.cot}\left(beta\right)\right) \cdot \operatorname{Complex.exp}\left(\operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.pi}\right) \cdot \operatorname{Complex.ofReal}\left(nu\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Omega0` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Equation (B.26) gives the gamma-function factor. Real.rpow is real exponentiation, Real.cot is cotangent, and Complex.Gamma, Complex.exp and Complex.I retain their Mathlib names. The source range is 0 < nu < 1 and 0 < beta < pi with beta different from pi/2.

**Definition 1.10 (The scaled polynomial Pbar).**

$$\forall nu: \mathbb{R}, \forall beta: \mathbb{R}, \forall k: \mathbb{N}, \operatorname{Pbar}\left(nu, beta, k\right) = \operatorname{Polynomial.C}\left(\operatorname{Omega0}\left(nu, beta\right)\right) \cdot \operatorname{P}\left(k, \frac{1 + nu}{2}\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Pbar` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Equation (B.24) multiplies P_k((1+nu)/2) by Omega0(nu,beta).

**Definition 1.11 (The recursive polynomials Omega).**

$$\begin{aligned}\forall nu: \mathbb{R}, \forall beta: \mathbb{R}, \operatorname{Omega}\left(nu, beta, 0\right) = \operatorname{Polynomial.C}\left(\operatorname{Omega0}\left(nu, beta\right)\right)\\\forall nu: \mathbb{R}, \forall beta: \mathbb{R}, \forall k: \mathbb{N}, \operatorname{Omega}\left(nu, beta, k + 1\right) = \operatorname{Pbar}\left(nu, beta, k + 1\right) - \sum_{l:\operatorname{Fin}\left(k + 1\right)} (\operatorname{P}\left(k + 1 - \operatorname{val}\left(l\right), \frac{1 - nu}{2}\right) \cdot \operatorname{Omega}\left(nu, beta, \operatorname{val}\left(l\right)\right))\end{aligned}$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Omega` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Equation (B.26) starts at the constant polynomial Omega0 and recursively subtracts the earlier Omega_l times P_(k+1-l)((1-nu)/2). The sum over Fin(k+1) includes l = 0,...,k, and val is the natural value of a Fin index. Natural subtraction is truncated, with k+1-l positive on that finite domain.

**Definition 1.12 (A sparse formal series).**

$$\forall R: \operatorname{Type}, [\operatorname{Semiring}\left(R\right)] \forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall A: \mathbb{N} \to R, \operatorname{sparseSeries}\left(p, q, A\right) = \operatorname{PowerSeries.mk}\left(\operatorname{fun} d: \mathbb{N} \mapsto \operatorname{dite}\left((\exists k: \mathbb{N}, d = p + k \cdot q), \operatorname{fun} h: (\exists k: \mathbb{N}, d = p + k \cdot q) \mapsto A\left(\operatorname{Exists.choose}\left(h\right)\right), \operatorname{fun} _ \mapsto 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.sparseSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

PowerSeries.mk constructs the series from its coefficients. dite is dependent conditional choice: Exists.choose selects an index when one exists. For q > 0 that index is unique. This total construction also has a value outside that range, which the conjecture does not use.

**Definition 1.13 (The series inside the logarithm).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall beta: \mathbb{R}, \operatorname{W}\left(p, q, beta\right) = \operatorname{sparseSeries}\left(p, q, \operatorname{Omega}\left(\frac{(\operatorname{Nat.cast}\left(p\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(q\right): \mathbb{R})}, beta\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.W` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Set x = z^(-1/q). A term Omega_k x^(p+kq) occupies exactly the degree p+kq. The rational nu is encoded by real field division after the natural-to-real casts; this is not natural division.

**Definition 1.14 (The formal logarithm).**

$$\forall w: \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{C}\right)\right), \operatorname{logOnePlus}\left(w\right) = \operatorname{PowerSeries.mk}\left(\operatorname{fun} d: \mathbb{N} \mapsto \sum_{n\in \operatorname{Finset.Icc}\left(1, d\right)} (\frac{\left(-1\right)^{n + 1}}{(\operatorname{Nat.cast}\left(n\right): \mathbb{C})} \cdot \operatorname{PowerSeries.coeff}\left(d, w^{n}\right))\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.logOnePlus` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The formal log(1+w) is the alternating sum of w^n/n. At positive order of w, degree d receives only n <= d. Finset.Icc(1,d) is the inclusive natural interval. The scalar acts on the coefficient polynomial by complex scalar multiplication.

**Definition 1.15 (The order m coefficient polynomial).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall beta: \mathbb{R}, \forall m: \mathbb{N}, \operatorname{S}\left(p, q, beta, m\right) = \operatorname{PowerSeries.coeff}\left(m + p, \operatorname{logOnePlus}\left(\operatorname{W}\left(p, q, beta\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.S` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The source's logarithmic expansion defines S_m as the coefficient of x^(m+p). PowerSeries.coeff extracts that coefficient.

**Definition 1.16 (The logarithmic denominator coefficient).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall beta: \mathbb{R}, \forall m: \mathbb{N}, \forall j: \mathbb{N}, \operatorname{g}\left(p, q, beta, m, j\right) = \operatorname{Polynomial.coeff}\left(j, \operatorname{S}\left(p, q, beta, m\right)\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.g` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The source's final expansion, manuscript label (B.45) and typeset equation (B.48), expands S_m in T. Polynomial.coeff(j,S) is its coefficient of T^j, namely g_(m,j)(p/q,beta).

**Definition 1.17 (Admissible expansion indices).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{admissible}\left(p, q, m\right) \Leftrightarrow (\exists l: \mathbb{N}, \exists k: \mathbb{N}, l \cdot p + k \cdot q = m)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.admissible` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

The source's set [m]_(p,q) is nonempty exactly when there are natural l,k with l p + k q = m. Naturals include zero.

**Definition 1.18 (The largest denominator degree).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{order}\left(p, q, m\right) = \operatorname{sSup}\left(\{k: \mathbb{N} \mid \exists l: \mathbb{N}, l \cdot p + k \cdot q = m\}\right)$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.order` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Printed page 31: “The order of $\mathcal{S}_{m}(p/q,z)$ is, then, $k_{m} = \max\{k_{i}\}$ with $i \in \mathbb{N}$, namely the largest value of $k_{i}$ amongst the vectors $(l_{i},k_{i}) \in [m]_{p,q}$.”

In the positive p,q range the displayed natural set is bounded, so sSup gives that maximum for admissible m.

**Definition 1.19 (The nonvanishing conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall p: \mathbb{N}, \forall q: \mathbb{N}, (0 < p) \Rightarrow ((p < q) \Rightarrow ((\operatorname{Nat.Coprime}\left(p, q\right)) \Rightarrow (\forall beta: \mathbb{R}, (beta \in \operatorname{Set.Ioo}\left(0, \operatorname{Real.pi}\right)) \Rightarrow ((beta \ne \frac{\operatorname{Real.pi}}{2}) \Rightarrow (\forall m: \mathbb{N}, \forall j: \mathbb{N}, (\operatorname{admissible}\left(p, q, m\right)) \Rightarrow ((j \le \operatorname{order}\left(p, q, m\right)) \Rightarrow (\operatorname{g}\left(p, q, beta, m, j\right) \ne 0))))))))$$

*Formalization.* `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.claim` (`✓ std3`).

*Citation.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Remark B.3, printed page 31: “From calculations performed for particular choices of $p$, $q$, and $\beta$, we in fact conjecture that all of the $g_{m,j}(p/q,\beta)$ are nonzero for the choices of $p, q$, and $\beta$ considered here.”

The formula encodes p,q as naturals with 0 < p < q and Nat.Coprime(p,q), beta in the open interval (0,pi) excluding pi/2, and the nonempty index set with j <= order(p,q,m). This includes m = q, j = 1 also in the source's sum restricted to positive denominator degree.

**Theorem 1.20 (Refutation by reflection).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result` (`✓ std3`). ∎

*Resolves.* `Problems/fucci-stanfill-2024-poschl-teller-coefficients` (refuted) by `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fucci-stanfill-2024-poschl-teller-coefficients","declaration_gid":"D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guglielmo Fucci; Jonathan Stanfill (2024). *The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential*. DOI: [10.1007/s00023-025-01587-7](https://doi.org/10.1007/s00023-025-01587-7). URL: <https://arxiv.org/abs/2411.17860v1>.

*Commentary.*

Take (p,q,beta,m,j) = (2,3,pi/4,3,1). The index is admissible and 1 <= order(2,3,3). In degree 5 of the formal logarithm, the linear term is Omega_1; the square and all higher powers contribute zero. Since G_0 = 1, the coefficient of T in P_1(y) is E_1(y)/2. The identity E_1(1-y) = E_1(y) exchanges (1+nu)/2 and (1-nu)/2, so this coefficient cancels in Omega_1. Consequently g(2,3,beta,3,1) = 0 for every real beta, including pi/4. The result concerns formal coefficients; it does not assert a theorem about spectral analytic continuation or the all-coprime-parameter family.

## References

- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.C`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.E`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.G`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Omega`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Omega0`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.P`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.Pbar`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.S`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.W`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.admissible`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.bernoulliPower`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.claim`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.g`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.generalizedBernoulli`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.generalizedBernoulliSeries`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.logOnePlus`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.order`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.scriptE`
- Truth anchor: `D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.sparseSeries`
