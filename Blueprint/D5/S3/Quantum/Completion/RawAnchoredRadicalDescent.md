# Raw Anchored Fourier Defect Descent

## Abstract

Raw balance yields the actual Fourier defect quotient and additive marker descent.

Let E be the full finite-support real space on M, e(a)=delta(a)-delta(1), and E0 the real span of the e(a). Put q(a)=c(a,1), r(a)=c(1,a), and kernel(a,b)=(q(a)+r(b)-c(a,b))/2. B0 is its bilinear extension to E. Rad is the intersection of the left and right radicals, V=E/Rad, pi is the quotient map, beta(a)=pi(e(a)), and B is the induced ordered bilinear form. S is the free linear extension of U. R is its induced operator on V.

Put T(a,u)=beta(a*u)-beta(a)-beta(u), W=span(range T), gamma(a)=beta(a) mod W, and let rho be the operator induced by R on V/W. All spans and quotients are real. Function images of subspaces are written pi(E0) and R(W). Superscripts on U and rho denote iteration, including the zeroth iterate.

**Theorem 1.1 (The original raw law constructs the ordered Fourier quotient).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow (\operatorname{c}\left(1, 1\right) = 0 \land (\operatorname{beta}\left(1\right) = 0 \land ((\forall a: M, (\forall b: M, \operatorname{B}\left(\operatorname{beta}\left(a\right), \operatorname{beta}\left(b\right)\right) = \operatorname{kernel}\left(a, b\right))) \land ((\forall x: E, (\forall y: E, \operatorname{B0}\left(\operatorname{S}\left(x\right), \operatorname{S}\left(y\right)\right) = \operatorname{B0}\left(x, y\right))) \land ((\forall a: M, \operatorname{beta}\left(\operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(a\right)\right)\right)\right) = \operatorname{beta}\left(a\right)) \land ((\forall x: E, x \in Rad \Rightarrow \operatorname{S}\left(x\right) \in Rad) \land ((\forall a: M, \operatorname{R}\left(\operatorname{beta}\left(a\right)\right) = \operatorname{beta}\left(\operatorname{U}\left(a\right)\right)) \land ((\forall a: M, \operatorname{R}\left(\operatorname{R}\left(\operatorname{R}\left(\operatorname{beta}\left(a\right)\right)\right)\right) = \operatorname{beta}\left(a\right)) \land ((\forall a: M, \operatorname{T}\left(1, a\right) = 0) \land ((\forall a: M, \operatorname{T}\left(a, 1\right) = 0) \land (\operatorname{pi}\left(E0\right) = V \land (\operatorname{span}\left(\operatorname{range}\left(beta\right)\right) = V \land ((\forall z: V, (\forall a: M, \operatorname{B}\left(z, \operatorname{beta}\left(a\right)\right) = 0) \Rightarrow (\forall a: M, \operatorname{B}\left(\operatorname{beta}\left(a\right), z\right) = 0) \Rightarrow z = 0) \land ((\forall x: V, \operatorname{R}\left(\operatorname{R}\left(\operatorname{R}\left(x\right)\right)\right) = x) \land ((\forall x: V, (\forall y: V, \operatorname{B}\left(\operatorname{R}\left(x\right), \operatorname{R}\left(y\right)\right) = \operatorname{B}\left(x, y\right))) \land ((\forall a: M, (\forall b: M, \operatorname{B}\left(\operatorname{beta}\left(a\right) - \operatorname{beta}\left(b\right), \operatorname{beta}\left(a\right) - \operatorname{beta}\left(b\right)\right) = \frac{\operatorname{c}\left(a, b\right) + \operatorname{c}\left(b, a\right)}{2})) \land ((\forall a: M, (\forall u: M, \operatorname{q}\left((a \cdot u)\right) + \operatorname{q}\left((a \cdot \operatorname{U}\left(u\right))\right) + \operatorname{q}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right))\right) = 3 \cdot \operatorname{q}\left(a\right) + 3 \cdot \operatorname{q}\left(u\right))) \land ((\forall b: M, (\forall v: M, \operatorname{r}\left((b \cdot v)\right) + \operatorname{r}\left((b \cdot \operatorname{U}\left(v\right))\right) + \operatorname{r}\left((b \cdot \operatorname{U}\left(\operatorname{U}\left(v\right)\right))\right) = 3 \cdot \operatorname{r}\left(b\right) + 3 \cdot \operatorname{r}\left(v\right))) \land ((\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{B}\left(\operatorname{beta}\left((a \cdot u)\right), \operatorname{beta}\left((b \cdot v)\right)\right) + \operatorname{B}\left(\operatorname{beta}\left((a \cdot \operatorname{U}\left(u\right))\right), \operatorname{beta}\left((b \cdot \operatorname{U}\left(v\right))\right)\right) + \operatorname{B}\left(\operatorname{beta}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right))\right), \operatorname{beta}\left((b \cdot \operatorname{U}\left(\operatorname{U}\left(v\right)\right))\right)\right) = 3 \cdot \operatorname{B}\left(\operatorname{beta}\left(a\right), \operatorname{beta}\left(b\right)\right) + 3 \cdot \operatorname{B}\left(\operatorname{beta}\left(u\right), \operatorname{beta}\left(v\right)\right))))) \land ((\forall a: M, (\forall u: M, \operatorname{beta}\left((a \cdot u)\right) + \operatorname{beta}\left((a \cdot \operatorname{U}\left(u\right))\right) + \operatorname{beta}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right))\right) = 3 \cdot \operatorname{beta}\left(a\right))) \land ((\forall a: M, (\forall u: M, \operatorname{beta}\left((a \cdot u)\right) + \operatorname{R}\left(\operatorname{R}\left(\operatorname{beta}\left((a \cdot \operatorname{U}\left(u\right))\right)\right)\right) + \operatorname{R}\left(\operatorname{beta}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right))\right)\right) = 3 \cdot \operatorname{beta}\left(u\right))) \land ((\forall x: V, x + \operatorname{R}\left(x\right) + \operatorname{R}\left(\operatorname{R}\left(x\right)\right) = 0) \land ((\forall a: M, (\forall u: M, (\operatorname{beta}\left((a \cdot \operatorname{U}\left(u\right))\right) = \operatorname{beta}\left(a\right) + \operatorname{R}\left(\operatorname{beta}\left(u\right)\right) + \operatorname{R}\left(\operatorname{R}\left(\operatorname{T}\left(a, u\right)\right)\right) \land \operatorname{beta}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right))\right) = \operatorname{beta}\left(a\right) + \operatorname{R}\left(\operatorname{R}\left(\operatorname{beta}\left(u\right)\right)\right) + \operatorname{R}\left(\operatorname{T}\left(a, u\right)\right)))) \land ((\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{B}\left(\operatorname{T}\left(a, u\right), \operatorname{T}\left(b, v\right)\right) = 0)))) \land ((\forall x: V, (\forall y: V, x \in W \Rightarrow y \in W \Rightarrow \operatorname{B}\left(x, y\right) = 0)) \land (\operatorname{R}\left(W\right) = W \land (\operatorname{gamma}\left(1\right) = 0 \land ((\forall a: M, (\forall u: M, \operatorname{gamma}\left((a \cdot u)\right) = \operatorname{gamma}\left(a\right) + \operatorname{gamma}\left(u\right))) \land ((\forall a: M, \operatorname{gamma}\left(\operatorname{U}\left(a\right)\right) = \operatorname{rho}\left(\operatorname{gamma}\left(a\right)\right)) \land ((\forall a: M, (\forall u: M, (\forall k: \mathbb{N}, \operatorname{gamma}\left((a \cdot U^{k}(u))\right) = \operatorname{gamma}\left(a\right) + rho^{k}(\operatorname{gamma}\left(u\right))))) \land (\forall a: M, (\forall b: M, \operatorname{gamma}\left(a\right) = \operatorname{gamma}\left(b\right) \Rightarrow (\operatorname{c}\left(a, b\right) = 0 \land \operatorname{c}\left(b, a\right) = 0)))))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_anchored_radical_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit basis vector lies in both radicals, so pi(E0)=V and the beta labels span V. Testing both ordered pairings against these labels gives joint nondegeneracy. The complete raw law supplies the q and r averages and the bilinear balance, hence the unweighted and inverse-weighted constraints. Solving their three-character system gives the two original phase children. Bilinear Fourier cancellation makes the cross-defect pairing zero; linear extension gives B(W,W)=0, while the phase identities give R(W)=W. The same W supplies the actual gamma product and marker identities. Its isotropy, the difference diagonal identity and comparison nonnegativity force both directed comparisons to vanish on each gamma fibre. Isotropy alone does not say that W is a radical.

Only a binary operation with a two-sided unit is imposed on M. RawBalance means U(1)=1, c(a,b)>=0, c(a,a)=0, and the complete four-variable sum of c(a*U^k(u),b*U^k(v)) for k=0,1,2 equals 3c(a,b)+3c(u,v). No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.

Let N={a:gamma(a)=0} and K={(a,b):gamma(a)=gamma(b)}. The two directed comparison bounds on K are |B(beta(a)-beta(b),beta(z))|<=3r(z)/2 and |B(beta(z),beta(a)-beta(b))|<=3q(z)/2. The algebraic operator J=(2R+I)/sqrt(3) has square -I. For each real functional alpha, ell=alpha-i alpha J intertwines R with the explicit primitive cube root. The complete original children remain in N. The existing bounded_phase_recursion_vanishes is applied separately to both ordered functionals, using all finite history depths and the bound normSq(ell(beta(n)))<=10L^2.

**Theorem 1.2 (The actual zero fibre has zero anchored vector).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall u: M, u \in N \Rightarrow \operatorname{beta}\left(u\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_zero_fibre_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both ordered pairings vanish by the two actual history applications. Joint nondegeneracy against the spanning beta labels then gives beta(u)=0.

**Theorem 1.3 (The original gamma fibre determines beta).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall a: M, (\forall b: M, \operatorname{gamma}\left(a\right) = \operatorname{gamma}\left(b\right) \Rightarrow \operatorname{beta}\left(a\right) = \operatorname{beta}\left(b\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_gamma_fibre_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed ordered functional, take the supremum of its absolute beta difference over the same actual K. The original label d=U(a)*U(U(a)) has gamma(d)=-gamma(a), so a*d and b*d lie in N; d itself need not. The unweighted identity makes the k=0 child zero and bounds the other two children by that same supremum. Its 2/3 contraction forces zero. Apply this argument in both pairing orders.

**Theorem 1.4 (All directed readouts descend along the actual fibres).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall a: M, (\forall b: M, \operatorname{gamma}\left(a\right) = \operatorname{gamma}\left(b\right) \Rightarrow (\operatorname{q}\left(a\right) = \operatorname{q}\left(b\right) \land (\operatorname{r}\left(a\right) = \operatorname{r}\left(b\right) \land ((\forall z: M, \operatorname{c}\left(a, z\right) = \operatorname{c}\left(b, z\right)) \land (\forall z: M, \operatorname{c}\left(z, a\right) = \operatorname{c}\left(z, b\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_directed_comparison_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of beta and the vanishing cross comparisons give equality of q and r. Substitution in the original ordered kernel then gives both complete rows and columns.

The actual image A=gamma(M) is an additive subgroup of V/W: the original product supplies sums and U(a)*U(U(a)) supplies negatives. Let tau be rho restricted to A. For x,y in A, choose original labels representing them and put C(x,y)=c(a,b). The complete row and column descent proves that this is independent of both choices and that C(gamma(a),gamma(b))=c(a,b). Nonnegativity, diagonal zero and the full four-variable balance pass to this same C with group addition and tau.

**Theorem 1.5 (The actual directed comparison is translation invariant).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall x: A, (\forall y: A, (\forall z: A, \operatorname{C}\left(x + z, y + z\right) = \operatorname{C}\left(x, y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed x,y put f(t)=C(x+t,y+t) and m=inf(range f). Nonnegativity bounds m below. The full balance with equal last operands gives f(t+w)<=3f(t)-2m. Taking w=s-t yields (f(s)+2m)/3<=f(t) for every t; the infimum property forces f(s)=m. In particular f(z)=f(0). This uses the constructed actual image and comparison.

Put f(x)=C(x,0). Translation invariance gives C(x,y)=f(x-y). The actual restricted marker tau satisfies tau^2=-I-tau and f(tau(x))=f(x); the original balance gives the three-phase equation for f. To prove evenness, use the existing nonnegative_recurrence_constant on s(n)=f((-2)^n*x)/4^n. The three-phase equation gives f(4x)+4f(-2x)=32f(x), hence s(n+1)+s(n+2)=2s(n); the existing result gives f(-2x)=4f(x), and then f(-x)=f(x). Therefore f(2x)=4f(x).

**Theorem 1.6 (The actual comparison is an integer quadratic distance).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow \exists Q: \operatorname{QuadraticMap}\left(\mathbb{Z}, A, \mathbb{R}\right), ((\forall x: A, \operatorname{Q}\left(x\right) = \operatorname{f}\left(x\right)) \land (\forall x: A, (\forall y: A, \operatorname{C}\left(x, y\right) = \operatorname{Q}\left(x - y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L=tau-tau^2 and P(x,y)=f(x+y)+f(x-y)-2f(x)-2f(y). The phase equation gives f(Ly)=3f(y) and P(x,Ly)=3P(x,y). Evenness makes P symmetric, so P(Lx,Ly)=9P(x,y); direct use of f(Lz)=3f(z) also gives P(Lx,Ly)=3P(x,y). Thus P=0 on this actual A. Apply TauCeti.QuadraticMap.ofParallelogram directly with domain A, codomain the reals and injective doubling. Its function is this same f and C(x,y)=Q(x-y). This supplies an integer quadratic map, not a Hilbert completion or arbitrary complex scalar closure.

The full Hilbert representation criterion remains open. Positive Gram realization, completion, a compatible complex structure and the full Hilbert equivalence remain to be supplied. The minimal unitary uniqueness, zero-comparison congruence and torsion-free Eisenstein conclusions are not asserted here.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_anchored_radical_descent`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_directed_comparison_descent`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_gamma_fibre_collapse`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_quadratic`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_translation_invariant`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_zero_fibre_vanishes`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](../../QuadraticForms/ParallelogramConstruction.md)
- Dependency: [D5/S3/Quantum/Completion/RawThreePhaseDescent](RawThreePhaseDescent.md)
- Dependency: [D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity](ThreePhaseHistoryRigidity.md)
