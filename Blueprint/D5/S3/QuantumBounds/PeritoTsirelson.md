# The Perito Bell bound and its attaining strategy

## Abstract

Every finite unitary strategy satisfies the Perito Bell upper bound. The cyclic clock, shift and normalized maximally entangled state give a valid strategy attaining the bound.

The outcome count is d, Alice has two settings and Bob has d settings. Their finite local dimensions n and m are arbitrary. All matrix norms are operator norms for the Euclidean vector norm. The phase windowRoot(d) is exp(2 pi i/d), and kronecker denotes the matrix tensor product. Bob's cyclic matrices are the coefficient sums of shift to the power k+1 times clock to the power k. For y and k from zero to d minus one, lambda(y,k) is (-1)^k omega^(k(k+1)/2) omega^(-y(1+k)) divided by d sin(pi(k+1/2)/d), where omega = windowRoot(d). Write nu(j) = exp(pi i (2j+1)/d) and g(t) = sum_k t^k/(d sin(pi(k+1/2)/d)). In these phases i is the imaginary unit, and val(j) is the representative of j between zero and d minus one. DensityState(a) consists of positive semidefinite complex matrices indexed by a with trace one. Adjoint means conjugate transpose.

**Theorem 1.1 (Finite Fourier evaluation).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] \forall (j : \operatorname{ZMod}\left(d\right)), \operatorname{peritoG}\left(d, \operatorname{peritoNu}\left(d, j\right)\right) = \operatorname{exp}\left(\frac{\pi}{2 \cdot d} \cdot (d-1-2 \cdot \operatorname{val}\left(j\right)) \cdot i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.peritoG_at_nu` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the discrete Fourier transform to i exp(-pi i (j+1/2)/d). Its k-th transform coefficient is exp(pi i k/d)/sin(pi(k+1/2)/d). To see this, the ratio r=exp(-pi i (2k+1)/d) has r^d=-1, and the geometric sum is 2/(1-r). Euler's identity reduces its denominator to 2i exp(-pi i (k+1/2)/d) sin(pi(k+1/2)/d). The sine is positive for zero through d minus one.

Fourier inversion then gives the polynomial value. Combining the leading i with the exponential yields the centered phase shown above. The identity holds for every positive integer d.

**Theorem 1.2 (Unitarity).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] (2 \le d) \Rightarrow (\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{peritoB}\left(d, y\right) \in \operatorname{unitaryGroup}\left(\operatorname{ZMod}\left(d\right), \mathbb{C}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_unitary` (`✓ std3`). ∎

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

Put u_y = -omega^(1-y) XZ. The triangular Weyl phase gives u_y^d=-I. The coefficients yield B_y=omega^(-y) X g(u_y). The generators, their product, and the scalar prefactors are unitary.

Any polynomial vanishing at all nu_j is divisible by t^d+1, since these roots are distinct. Thus equal polynomial values at every nu_j give equal evaluations at u_y. For a unitary u with u^d=-I, its adjoint is -u^(d-1). The coefficients of g are real, so its adjoint is represented by g(-t^(d-1)). On each nu_j this is the conjugate of g(nu_j). The Fourier evaluation has modulus one, so the product is one at every root. Polynomial divisibility then gives g(u_y)g(u_y)^*=I, and hence B_y is unitary.

**Theorem 1.3 (The d-th power).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] (2 \le d) \Rightarrow (\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{peritoB}\left(d, y\right)^{d} = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_pow` (`✓ std3`). ∎

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

The Weyl relation gives u_y X = X (omega u_y). For every polynomial p, it follows that p(u_y)X = Xp(omega u_y). Iterating this identity shows that (Xg(u_y))^d is X^d times the evaluation at u_y of the product of g(omega^j t) for zero through d minus one.

Multiplication by omega permutes all roots of minus one. At each such root, the product is the product of all exp(pi i (d-1-2j)/(2d)). The exponents sum to zero, so this product is one. Divisibility by t^d+1 transfers the equality to u_y. Finally X^d=I and (omega^(-y))^d=1 give B_y^d=I.

**Theorem 1.4 (Validity and attained value).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] (2 \le d) \Rightarrow ((\forall (y : \operatorname{Fin}\left(d\right)), (\operatorname{peritoB}\left(d, y\right) \in \operatorname{unitaryGroup}\left(\operatorname{ZMod}\left(d\right), \mathbb{C}\right)) \land (\operatorname{peritoB}\left(d, y\right)^{d} = 1)) \land (\sum_{y \in \operatorname{Fin}\left(d\right)} (\operatorname{trace}\left(\operatorname{transpose}\left(\operatorname{clockMatrix}\left(d\right)\right) \cdot \operatorname{peritoB}\left(d, y\right)\right)+\operatorname{windowRoot}\left(d\right)^{\operatorname{val}\left(y\right)} \cdot \operatorname{trace}\left(\operatorname{transpose}\left(\operatorname{shiftMatrix}\left(d\right)\right) \cdot \operatorname{peritoB}\left(d, y\right)\right)) = d \cdot \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d at least two, every B_y is unitary and has d-th power identity. Together with these properties, the statement includes the exact trace-sum equality displayed below. Thus the same matrices satisfy both observable validity and trace attainment.

**Theorem 1.5 (Exact trace sum).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] (2 \le d) \Rightarrow (\sum_{y \in \operatorname{Fin}\left(d\right)} (\operatorname{trace}\left(\operatorname{transpose}\left(\operatorname{clockMatrix}\left(d\right)\right) \cdot \operatorname{peritoB}\left(d, y\right)\right)+\operatorname{windowRoot}\left(d\right)^{\operatorname{val}\left(y\right)} \cdot \operatorname{trace}\left(\operatorname{transpose}\left(\operatorname{shiftMatrix}\left(d\right)\right) \cdot \operatorname{peritoB}\left(d, y\right)\right)) = d \cdot \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_attained_sum` (`✓ std3`). ∎

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

Trace cyclicity and displacement trace orthogonality eliminate every term except k=d-1 in tr(Z^T B_y) and k=0 in tr(X^T B_y). The endpoint coefficients give 1/sin(pi/(2d)) and omega^(-y)/sin(pi/(2d)), respectively.

The endpoint phase is fixed by omega^((d-1)d/2)=(-1)^(d-1), and sin(pi-pi/(2d))=sin(pi/(2d)). Multiplication by omega^y therefore makes the two traces equal. Summing over all d settings gives the displayed complex identity. Dividing by d gives the corresponding maximally entangled trace-pairing value.

**Definition 1.6 (Root-of-unity observables).**

$$\forall (d : \mathbb{N}), \forall (a : Type), [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] \forall (A : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (\operatorname{IsDObservable}\left(d, A\right)) \Leftrightarrow ((A \in \operatorname{unitaryGroup}\left(a, \mathbb{C}\right)) \land (A^{d} = 1))$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.IsDObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A d-observable is a unitary matrix whose d-th power is the identity. Its eigenvalues are therefore d-th roots of unity.

**Definition 1.7 (Bell operator).**

$$\forall (d : \mathbb{N}), \forall (a : Type), [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] \forall (b : Type), [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (A : (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(a, a, \mathbb{C}\right))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(b, b, \mathbb{C}\right))), \operatorname{bellOperator}\left(d, A, B\right) = \sum_{x \in \operatorname{Fin}\left(2\right)} \sum_{y \in \operatorname{Fin}\left(d\right)} \operatorname{windowRoot}\left(d\right)^{x \cdot y} \cdot \operatorname{kronecker}\left(A\left(x\right), B\left(y\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.bellOperator` (`✓ std3`).

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

The Bell matrix is the sum of windowRoot(d) raised to xy times A(x) tensor B(y). It need not be Hermitian. Its Hermitian part is the Bell observable.

**Definition 1.8 (Real Bell expectation).**

$$\forall (d : \mathbb{N}), \forall (a : Type), [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] \forall (b : Type), [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (A : (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(a, a, \mathbb{C}\right))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(b, b, \mathbb{C}\right))), \forall (rho : \operatorname{Matrix}\left((a \times b), (a \times b), \mathbb{C}\right)), \operatorname{bellValue}\left(d, A, B, rho\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{bellOperator}\left(d, A, B\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.bellValue` (`✓ std3`).

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

The Bell value is the real part of trace(rho times the Bell matrix). For a Hermitian density matrix this equals the expectation of the Hermitian part of the Bell matrix.

**Definition 1.9 (Entangled amplitudes).**

$$\forall (iota : Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall (i : (iota \times iota)), \operatorname{maxEntangledVector}\left(iota, i\right) = \operatorname{ite}\left(\operatorname{fst}\left(i\right) = \operatorname{snd}\left(i\right), \operatorname{sqrt}\left(\operatorname{card}\left(iota\right)\right)^{-(1)}, 0\right)$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.maxEntangledVector` (`✓ std3`).

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

For any finite index type iota, the amplitude on a pair of basis labels is the real reciprocal of sqrt(card(iota)), cast to a complex number, when the labels coincide and zero otherwise. The function ite chooses its second argument when its first argument is true, and its third otherwise.

**Definition 1.10 (Entangled matrix).**

$$\forall (iota : Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \operatorname{maxEntangled}\left(iota\right) = \operatorname{vecMulVec}\left(\operatorname{maxEntangledVector}\left(iota\right), \operatorname{star}\left(\operatorname{maxEntangledVector}\left(iota\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.maxEntangled` (`✓ std3`).

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

The matrix is the outer product of the entangled vector with its entrywise conjugate. Thus it is a positive rank-one matrix when iota is nonempty. The cyclic strategy uses iota = ZMod(d).

**Definition 1.11 (Bound and cyclic equality).**

$$(claim) \Leftrightarrow (\forall (d : \mathbb{N}), (2 \le d) \Rightarrow ((\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (A : (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))), \forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right))\right)), (\forall (x : \operatorname{Fin}\left(2\right)), \operatorname{IsDObservable}\left(d, A\left(x\right)\right)) \Rightarrow ((\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{IsDObservable}\left(d, B\left(y\right)\right)) \Rightarrow (\operatorname{bellValue}\left(d, A, B, rho\right) \le \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)}))) \land ((\forall (x : \operatorname{Fin}\left(2\right)), \operatorname{IsDObservable}\left(d, [\operatorname{clockMatrix}\left(d\right), \operatorname{shiftMatrix}\left(d\right)]\left(x\right)\right)) \land ((\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{IsDObservable}\left(d, \operatorname{peritoB}\left(d, y\right)\right)) \land (((0 \le \operatorname{ofMatrix}\left(\operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right)) \land (\operatorname{trace}\left(\operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right) = 1)) \land (\operatorname{bellValue}\left(d, [\operatorname{clockMatrix}\left(d\right), \operatorname{shiftMatrix}\left(d\right)], \operatorname{peritoB}\left(d\right), \operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right) = \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)}))))))$$

*Formalization.* `D5/S3/QuantumBounds/PeritoTsirelson.claim` (`✓ std3`).

*Citation.* I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak (2026). *Bell inequalities tailored to optimal global randomness certification*. DOI: [10.48550/arXiv.2606.21362](https://doi.org/10.48550/arXiv.2606.21362). URL: <https://arxiv.org/abs/2606.21362v3>.

*Commentary.*

For every d at least two, the claim combines five assertions: the upper bound for every finite projective strategy and density state; validity of the cyclic clock and shift; validity of Bob's cyclic matrices; positivity and trace one of the entangled matrix; and equality with 2/sin(pi/(2d)) for this cyclic strategy. The local dimensions in the first assertion include zero. The cyclic matrices in the remaining assertions use the basis ZMod(d).

**Theorem 1.12 (Upper bound for unitary strategies).**

$$\forall (d : \mathbb{N}), (2 \le d) \Rightarrow (\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (A : (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))), \forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right))\right)), (\forall (x : \operatorname{Fin}\left(2\right)), A\left(x\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)) \Rightarrow ((\forall (y : \operatorname{Fin}\left(d\right)), B\left(y\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(m\right), \mathbb{C}\right)) \Rightarrow (\operatorname{bellValue}\left(d, A, B, rho\right) \le \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.bell_value_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only unitarity is required for the upper bound; no d-th-power relation is used. Put U = adjoint(A(0)) times A(1), which is unitary. Expanding the two Alice settings and distributing the tensor product gives bellOperator = (A(0) tensor I) times the sum over y of (I + windowRoot(d)^y U) tensor B(y). Left multiplication by the unitary A(0) tensor I preserves the operator norm, including on a zero-dimensional space. On a nonzero space this factor has norm one. The unitary tensor block bound reduces the remaining norm to the uniform scalar sum of |1 + windowRoot(d)^y z| for |z| = 1. That scalar sum is at most 2/sin(pi/(2d)).

For a density matrix rho and an arbitrary matrix T, let H = (T + adjoint(T))/2. The triangle inequality gives norm(H) at most norm(T). Self-adjointness gives H at most norm(H) times I in the positive semidefinite order. The real trace of the product of two positive semidefinite matrices is nonnegative. Applying this to rho and norm(H) I - H, and using trace(rho) = 1, gives Re trace(rho H) at most norm(H). Trace cyclicity and Hermitian rho identify Re trace(rho H) with Re trace(rho T). This proves the density expectation bound and hence the Bell upper bound.

**Theorem 1.13 (Clock and shift observables).**

$$\forall (d : \mathbb{N}), [\operatorname{NeZero}\left(d\right)] \forall (x : \operatorname{Fin}\left(2\right)), \operatorname{IsDObservable}\left(d, [\operatorname{clockMatrix}\left(d\right), \operatorname{shiftMatrix}\left(d\right)]\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.clock_shift_observables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite clock and shift are unitary, and each returns to the identity after d powers. Selecting either of the two settings therefore gives a d-observable.

**Theorem 1.14 (Entangled density normalization).**

$$\forall (iota : Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] [\operatorname{Nonempty}\left(iota\right)] (0 \le \operatorname{ofMatrix}\left(\operatorname{maxEntangled}\left(iota\right)\right)) \land (\operatorname{trace}\left(\operatorname{maxEntangled}\left(iota\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.max_entangled_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every outer product v v adjoint is positive semidefinite. The trace is the sum of the squared moduli of the vector entries. There are exactly card(iota) nonzero entries, one for each equal pair of basis labels, and each has squared modulus 1/card(iota). Since iota is nonempty, the trace is one.

**Theorem 1.15 (Transpose expectation identity).**

$$\forall (iota : Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] [\operatorname{Nonempty}\left(iota\right)] \forall (A : \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \forall (B : \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \operatorname{trace}\left(\operatorname{maxEntangled}\left(iota\right) \cdot \operatorname{kronecker}\left(A, B\right)\right) = \frac{\operatorname{trace}\left(\operatorname{transpose}\left(A\right) \cdot B\right)}{\operatorname{card}\left(iota\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.max_entangled_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal correlations in the entangled vector restrict both pairs of basis indices to equal labels. Expanding the trace therefore gives the sum of A(j,i) B(j,i) divided by card(iota). This is trace(transpose(A) B)/card(iota). The transpose is ordinary transpose, without complex conjugation.

**Theorem 1.16 (Sharp bound in every outcome count).**

$$\forall (d : \mathbb{N}), (2 \le d) \Rightarrow ((\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (A : (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))), \forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right))\right)), (\forall (x : \operatorname{Fin}\left(2\right)), \operatorname{IsDObservable}\left(d, A\left(x\right)\right)) \Rightarrow ((\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{IsDObservable}\left(d, B\left(y\right)\right)) \Rightarrow (\operatorname{bellValue}\left(d, A, B, rho\right) \le \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)}))) \land ((\forall (x : \operatorname{Fin}\left(2\right)), \operatorname{IsDObservable}\left(d, [\operatorname{clockMatrix}\left(d\right), \operatorname{shiftMatrix}\left(d\right)]\left(x\right)\right)) \land ((\forall (y : \operatorname{Fin}\left(d\right)), \operatorname{IsDObservable}\left(d, \operatorname{peritoB}\left(d, y\right)\right)) \land (((0 \le \operatorname{ofMatrix}\left(\operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right)) \land (\operatorname{trace}\left(\operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right) = 1)) \land (\operatorname{bellValue}\left(d, [\operatorname{clockMatrix}\left(d\right), \operatorname{shiftMatrix}\left(d\right)], \operatorname{peritoB}\left(d\right), \operatorname{maxEntangled}\left(\operatorname{ZMod}\left(d\right)\right)\right) = \frac{2}{\operatorname{sin}\left(\frac{\pi}{2 \cdot d}\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTsirelson.result` (`✓ std3`). ∎

*Resolves.* `Problems/perito-2026-tsirelson-bound-id` (proved) by `D5/S3/QuantumBounds/PeritoTsirelson.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"perito-2026-tsirelson-bound-id","declaration_gid":"D5/S3/QuantumBounds/PeritoTsirelson.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The upper bound applies to every finite projective strategy because its observables are unitary. The clock and shift are unitary with d-th power one. Bob's polynomial observables are unitary with d-th power one, and the maximally entangled matrix is positive with trace one. Thus the cyclic strategy is valid.

Expand the two Alice settings in the Bell operator and distribute the trace over Bob's settings. The transpose expectation identity makes the complex expectation equal to the sum of trace(transpose(Z) B(y)) plus omega^y trace(transpose(X) B(y)), divided by d. The clock-shift trace sum is d times 2/sin(pi/(2d)). Cancelling the nonzero dimension and taking the real part gives exactly 2/sin(pi/(2d)). The attained value equals the universal upper bound, so it is the Tsirelson bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.IsDObservable`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.bellOperator`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.bellValue`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.bell_value_le`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.claim`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.clock_shift_observables`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.maxEntangled`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.maxEntangledVector`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.max_entangled_density`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.max_entangled_trace`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_attained_sum`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_pow`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_spec`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.peritoB_unitary`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.peritoG_at_nu`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTsirelson.result`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementPowers](../Quantum/Algebra/WeylDisplacementPowers.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTrace](../Quantum/Algebra/WeylDisplacementTrace.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Quantum/Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTensorBlockBound](PeritoTensorBlockBound.md)
- Dependency: [D5/S3/QuantumBounds/PeritoUnitCircleSum](PeritoUnitCircleSum.md)
