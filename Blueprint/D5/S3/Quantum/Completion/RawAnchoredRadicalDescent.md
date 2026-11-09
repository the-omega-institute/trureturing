# Original-Magma Hilbert Classification

## Abstract

Original directed histories yield fibre collapse and the complete Hilbert classification.

Only a binary operation with a two-sided unit is imposed on M. RawBalance means U(1)=1, c(a,b)>=0, c(a,a)=0, and the complete four-variable sum of c(a*U^k(u),b*U^k(v)) for k=0,1,2 equals 3c(a,b)+3c(u,v). No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.

Let N={a:gamma(a)=0} and K={(a,b):gamma(a)=gamma(b)}. The two directed comparison bounds on K are |B(beta(a)-beta(b),beta(z))|<=3r(z)/2 and |B(beta(z),beta(a)-beta(b))|<=3q(z)/2. The algebraic operator J=(2R+I)/sqrt(3) has square -I. For each real functional alpha, ell=alpha-i alpha J intertwines R with the explicit primitive cube root. The complete original children remain in N. The existing bounded_phase_recursion_vanishes is applied separately to both ordered functionals, using all finite history depths and the bound normSq(ell(beta(n)))<=10L^2.

**Theorem 1.1 (The actual zero fibre has zero anchored vector).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall u: M, (u \in \operatorname{N}\left(c\right) \Rightarrow \operatorname{beta}\left(c, u\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_zero_fibre_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both ordered pairings vanish by the two actual history applications. Joint nondegeneracy against the spanning beta labels then gives beta(u)=0.

**Theorem 1.2 (The original gamma fibre determines beta).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall a: M, (\forall b: M, (\operatorname{gamma}\left(c, a\right) = \operatorname{gamma}\left(c, b\right) \Rightarrow \operatorname{beta}\left(c, a\right) = \operatorname{beta}\left(c, b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_gamma_fibre_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed ordered functional, take the supremum of its absolute beta difference over the same actual K. The original label d=U(a)*U(U(a)) has gamma(d)=-gamma(a), so a*d and b*d lie in N; d itself need not. The unweighted identity makes the k=0 child zero and bounds the other two children by that same supremum. Its 2/3 contraction forces zero. Apply this argument in both pairing orders.

**Theorem 1.3 (All directed readouts descend along the actual fibres).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall a: M, (\forall b: M, (\operatorname{gamma}\left(c, a\right) = \operatorname{gamma}\left(c, b\right) \Rightarrow ((\operatorname{q}\left(c, a\right) = \operatorname{q}\left(c, b\right)) \land (((\operatorname{r}\left(c, a\right) = \operatorname{r}\left(c, b\right)) \land ((((\forall z: M, \operatorname{c}\left(a, z\right) = \operatorname{c}\left(b, z\right))) \land ((\forall z: M, \operatorname{c}\left(z, a\right) = \operatorname{c}\left(z, b\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_directed_comparison_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of beta and the vanishing cross comparisons give equality of q and r. Substitution in the original ordered kernel then gives both complete rows and columns.

The actual image A=gamma(M) is an additive subgroup of V/W: the original product supplies sums and U(a)*U(U(a)) supplies negatives. Let tau be rho restricted to A. For x,y in A, choose original labels representing them and put C(x,y)=c(a,b). The complete row and column descent proves that this is independent of both choices and that C(gamma(a),gamma(b))=c(a,b). Nonnegativity, diagonal zero and the full four-variable balance pass to this same C with group addition and tau.

**Theorem 1.4 (The actual directed comparison is translation invariant).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\forall h: \operatorname{RawBalance}\left(U, c\right), (\forall x: \operatorname{visibleGroup}\left(U, c, h\right), (\forall y: \operatorname{visibleGroup}\left(U, c, h\right), (\forall z: \operatorname{visibleGroup}\left(U, c, h\right), \operatorname{visibleComparison}\left(U, c, h, x + z, y + z\right) = \operatorname{visibleComparison}\left(U, c, h, x, y\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed x,y put f(t)=C(x+t,y+t) and m=inf(range f). Nonnegativity bounds m below. The full balance with equal last operands gives f(t+w)<=3f(t)-2m. Taking w=s-t yields (f(s)+2m)/3<=f(t) for every t; the infimum property forces f(s)=m. In particular f(z)=f(0). This uses the constructed actual image and comparison.

Put f(x)=C(x,0). Translation invariance gives C(x,y)=f(x-y). The actual restricted marker tau satisfies tau^2=-I-tau and f(tau(x))=f(x); the original balance gives the three-phase equation for f. The frozen three_way_quadratic_structure applies directly to this same additive group, restricted marker, nonnegative energy and full three-phase equation. It supplies the quadratic map without repeating its evenness or parallelogram proof.

**Theorem 1.5 (The actual comparison is an integer quadratic distance).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\forall h: \operatorname{RawBalance}\left(U, c\right), \exists Q: \operatorname{QuadraticMap}\left(\mathbb{Z}, \operatorname{visibleGroup}\left(U, c, h\right), \mathbb{R}\right), (((\forall x: \operatorname{visibleGroup}\left(U, c, h\right), \operatorname{Q}\left(x\right) = \operatorname{visibleEnergy}\left(U, c, h, x\right))) \land ((\forall x: \operatorname{visibleGroup}\left(U, c, h\right), (\forall y: \operatorname{visibleGroup}\left(U, c, h\right), \operatorname{visibleComparison}\left(U, c, h, x, y\right) = \operatorname{Q}\left(x - y\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing three_way_quadratic_structure with the actual visibleGroup, visibleMarker and visibleEnergy. Its returned Q agrees pointwise with this same energy. Translation invariance then identifies the original descended comparison with Q(x-y). The resulting quadratic map also occurs in the complete characterization below.

RawHilbertRepresentation(U,c) consists of a carrier H with its normed additive commutative group, complex inner-product space and completeness instances, together with an original-label map F:M->H. Its fields are F(1)=0, F(a*b)=F(a)+F(b), F(Ua)=omega F(a), c(a,b)=norm(F(a)-F(b))^2 and topologicalClosure(span_C(range F))=top. Here omega is the existing explicit complex number (-1/2,sqrt(3)/2), and the Lean inner product is conjugate-linear in its first variable. The represented distances and unitary uniqueness are independent of that convention.

**Theorem 1.6 (The complete original-domain Hilbert criterion and minimal uniqueness).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\operatorname{U}\left(1\right) = 1 \Rightarrow (((((\operatorname{RawBalance}\left(U, c\right) \iff \operatorname{Nonempty}\left(\operatorname{RawHilbertRepresentation}\left(U, c\right)\right))) \land ((((\forall H: Type, [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], (\forall F: M \to H, ((\forall a: M, (\forall b: M, F((a \cdot b)) = F(a) + F(b))) \Rightarrow ((\forall a: M, F(\operatorname{U}\left(a\right)) = \operatorname{omega}\left(\right) \cdot F(a)) \Rightarrow ((\forall a: M, (\forall b: M, \operatorname{c}\left(a, b\right) = \operatorname{norm}\left(F(a) - F(b)\right)^{2})) \Rightarrow \operatorname{RawBalance}\left(U, c\right))))))) \land ((\operatorname{RawBalance}\left(U, c\right) \Rightarrow (\forall S: \operatorname{RawHilbertRepresentation}\left(U, c\right), (\forall T: \operatorname{RawHilbertRepresentation}\left(U, c\right), \exists ! j: \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{carrier}\left(S\right), \operatorname{carrier}\left(T\right)\right), (\forall a: M, j(\operatorname{label}\left(S, a\right)) = \operatorname{label}\left(T, a\right)))))))))) \land ((\forall h: \operatorname{RawBalance}\left(U, c\right), (((((\forall a: M, (\forall b: M, \operatorname{c}\left(a, b\right) = 0 \iff \operatorname{gamma}\left(c, a\right) = \operatorname{gamma}\left(c, b\right)))) \land ((((\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, (\operatorname{c}\left(a, b\right) = 0 \Rightarrow (\operatorname{c}\left(u, v\right) = 0 \Rightarrow \operatorname{c}\left((a \cdot u), (b \cdot v)\right) = 0))))))) \land ((((\forall a: M, (\forall b: M, (\operatorname{c}\left(a, b\right) = 0 \Rightarrow \operatorname{c}\left(\operatorname{U}\left(a\right), \operatorname{U}\left(b\right)\right) = 0)))) \land ((((\forall a: M, (\forall b: M, (\forall d: M, \operatorname{c}\left(((a \cdot b) \cdot d), (a \cdot (b \cdot d))\right) = 0)))) \land ((((\forall a: M, (\forall b: M, \operatorname{c}\left((a \cdot b), (b \cdot a)\right) = 0))) \land ((((\forall a: M, \operatorname{c}\left(\operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(a\right)\right)\right), a\right) = 0)) \land ((((\forall a: M, \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), (\operatorname{U}\left(a\right) \cdot \operatorname{U}\left(\operatorname{U}\left(a\right)\right))\right) = -\operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), a\right))) \land ((((\forall a: M, (\forall b: M, \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), (a \cdot b)\right) = \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), a\right) + \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), b\right)))) \land (((\exists j: \operatorname{LinearEquiv}\left(\operatorname{Eisenstein}\left(\right), \operatorname{VisibleQuotient}\left(U, c, h\right), \operatorname{visibleImage}\left(U, c, h, \operatorname{groupModel}\left(U, c, h\right)\right)\right), (\forall a: M, \operatorname{val}\left(j(\operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), a\right))\right) = \operatorname{label}\left(\operatorname{groupModel}\left(U, c, h\right), \operatorname{visibleLabel}\left(U, c, h, a\right)\right))) \land ((((\forall a: M, \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), \operatorname{U}\left(a\right)\right) = \operatorname{omegaScalar}\left(\right) \cdot \operatorname{Quotientmk}\left(\operatorname{zeroComparisonSetoid}\left(U, c, h\right), a\right))) \land ((\forall s: \operatorname{Eisenstein}\left(\right), (\forall x: \operatorname{VisibleQuotient}\left(U, c, h\right), (s \neq 0 \Rightarrow (s \cdot x = 0 \Rightarrow x = 0))))))))))))))))))))))))) \land (\exists Q: \operatorname{QuadraticMap}\left(\mathbb{Z}, \operatorname{visibleGroup}\left(U, c, h\right), \mathbb{R}\right), (((\forall x: \operatorname{visibleGroup}\left(U, c, h\right), \operatorname{Q}\left(x\right) = \operatorname{visibleEnergy}\left(U, c, h, x\right))) \land ((\forall x: \operatorname{visibleGroup}\left(U, c, h\right), (\forall y: \operatorname{visibleGroup}\left(U, c, h\right), \operatorname{visibleComparison}\left(U, c, h, x, y\right) = \operatorname{Q}\left(x - y\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_hilbert_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen three_way_hilbert_characterization is applied to exactly visibleGroup(U,c,h), visibleMarker(U,c,h) and visibleEnergy(U,c,h). Composing its additive label with visibleLabel gives the original F, and surjectivity of visibleLabel identifies the two actual ranges. The converse quantifies over any complete complex Hilbert carrier and original label map with the product, phase and distance identities; it imposes no minimality or factorization hypothesis. It applies the same supplier to the identity representation of that carrier, with omega scalar multiplication, and substitutes the two original differences into its three-way norm law. The unit-zero identity already follows from product additivity at the unit. For any other original model, equality of gamma implies zero original comparison and hence equal labels. This proves factorization through the same actual visible group; no factorization certificate is assumed in the raw model. The supplier's unique complex-linear isometry then gives the unique original-label-preserving unitary, including models in independent universes.

Eisenstein is the actual subalgebra Algebra.adjoin_Z({omega}) inside the complex numbers. visibleImage(U,c,h,R) has carrier range(R.label) and inherits complex scalar multiplication restricted to Eisenstein. Algebra.adjoin_induction proves that this actual image is closed: integers use additive scalar multiplication, omega uses the actual marker phase, and sum/product closure uses the same range. omegaScalar is omega as an element of that generated subring. zeroComparisonSetoid(U,c,h) has literal relation c(a,b)=0; VisibleQuotient is its Quotient. The quotient group is transported through the proved bijection to visibleGroup, and the Eisenstein module is transported through the actual image equivalence. No new scalar ring, recipe, completion point or physical operation is supplied.

If the chosen Hilbert labels of a and b agree, the distance formula gives equality of every original row and every original column. This gives equality of q and r and annihilates both ordered B pairings of beta(a)-beta(b) against every beta label. The proved joint nondegeneracy forces beta(a)=beta(b), hence gamma(a)=gamma(b). Thus the actual energy is definite, and c(a,b)=0 is exactly equality of gamma. The original product and marker formulas give the congruence and all visible algebra identities. The linear image equivalence identifies the actual quotient with the label image. A nonzero Eisenstein scalar stays nonzero in the complex numbers, so its action on the Hilbert carrier has zero kernel; the same holds on the image and on the transported quotient. The zero model is included. No isotropic-to-radical shortcut or assertion W=0 is used.

These are mathematical consequences of the full original balance under U(1)=1, with every finite history depth allowed. The original operation may remain nonassociative and noncommutative and U cubed need not be the identity on original recipes. The group and module laws identify only their zero-comparison classes. Completion and scalar extension supply no extra actual recipes or physical controls.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_directed_comparison_descent`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_gamma_fibre_collapse`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_hilbert_characterization`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_quadratic`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_visible_translation_invariant`
- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_zero_fibre_vanishes`
- Dependency: [D5/S3/Quantum/Completion/RawAnchoredFourierQuotient](RawAnchoredFourierQuotient.md)
