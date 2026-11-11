# Semilinear Kernel Order and the Native Norm

## Abstract

Conjugation trace one inverts the actual coinvariant norm; a semilinear action requires only nonzero kernel order.

This is the classical trace-one mechanism, reconstructed using native Mathlib representations, coinvariants, invariants and Dedekind independence. No literature novelty is claimed. The generic ring, group, module and field have independent universes. The group is finite and may be nonabelian; the coefficient ring is an arbitrary commutative ring and the module is arbitrary. There is no finite-generation, dimension or coefficient-projectivity hypothesis.

**Definition 1.1 (The actual unnormalized norm).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.coinvariantsNorm`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.coinvariantsNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For {R : Type uR} {G : Type uG} {V : Type uV} [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V] and rho : Representation R G V, coinvariantsNorm rho is an R-linear map from rho.Coinvariants to rho.invariants. Its value on Coinvariants.mk rho v, coerced to V, is rho.norm v, the sum of rho(g)v over all g in G. This is the native quotient by the R-span of rho(g)v-v, with no replacement of its coefficient ring.

Representation.self_norm_apply puts the norm in the invariant submodule; Representation.norm_self_apply lets Coinvariants.lift descend it through the actual quotient. The consumed coinvariantsNorm_mk lemma records its representative formula.

**Definition 1.2 (A trace-one endomorphism gives both inverse identities).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.traceOneNormEquiv`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.traceOneNormEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the same full telescope, let t : Module.End R V satisfy sum over g : G of (rho g).comp (t.comp (rho g inverse)) = LinearMap.id. Then traceOneNormEquiv rho t ht is an R-linear equivalence rho.Coinvariants to rho.invariants. The consumed traceOneNormEquiv_mk and traceOneNormEquiv_symm_apply lemmas give, for every v : V and w : rho.invariants, e([v]) = rho.norm v and e.symm(w) = [t(w)]. The displayed group inverse stays inside the conjugation; no endomorphisms or group elements are commuted.

Define the inverse linear map by restricting t to invariant inputs and composing with Coinvariants.mk. For invariant w, every rho(g inverse)w equals w, so the supplied conjugation trace makes N(t(w))=w. For a quotient representative v, reindex the norm by g to g inverse. Then [t(N(v))] equals the sum of [t(rho(g inverse)v)], which equals the sum of [rho(g)t(rho(g inverse)v)] by the native quotient relation. The trace identity makes this [v]. Surjectivity of Coinvariants.mk extends this identity to every quotient element; LinearEquiv.ofLinearMap packages the two identities.

Unlike absolute group-algebra projectivity, this conclusion needs no R-projectivity of V. ProjectiveConjugationTrace explains the stronger projectivity criterion and its additional coefficient-projectivity condition. Here zero rings, zero modules and trivial groups remain within the generic theorem.

**Theorem 1.3 (Genuine semilinearity supplies the endomorphism).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.scalar_conjugation_trace_one`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.scalar_conjugation_trace_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Add {K : Type uK} [Field K] [Algebra R K] [Module K V] [IsScalarTower R K V], gamma : G to monoid (K equiv+* K), and hRho : for all g : G, a : K and v : V, rho(g)(a smul v)=gamma(g)(a) smul rho(g)(v). If c : K satisfies sum_g gamma(g)(c)=1, multiplication by c defines scalarTraceEnd c : Module.End R V and its conjugation trace is LinearMap.id. Multiplication by c is K-linear and is restricted to R; the group action is required only to be R-linear and genuinely gamma-semilinear.

Semilinearity and rho(g)rho(g inverse)=id turn each conjugate of multiplication by c into multiplication by gamma(g)c. The finite sum is therefore multiplication by 1. semilinearScalarNormEquiv applies traceOneNormEquiv to this actual endomorphism. Its representative and inverse formulas are consumed by the final theorem.

**Theorem 1.4 (Exactly the kernel order controls scalar trace one).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearScalarTraceOne_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearScalarTraceOne_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For {G : Type uG} {K : Type uK} [Group G] [Fintype G] [Field K] and an arbitrary gamma : G to monoid (K equiv+* K), there exists c : K with sum_g gamma(g)c=1 if and only if (Nat.card gamma.ker : K) is nonzero. There is no finiteness assumption on K, no injectivity assumption on gamma and no inverse of the image order or whole group order.

Let Gamma be gamma.range and T(b)=sum over sigma : Gamma of sigma(b), implemented as semilinearImageTrace. Left multiplication in Gamma permutes the summands, so every image automorphism fixes T(b). Distinct image elements give distinct multiplicative homomorphisms K to K. Mathlib's linearIndependent_monoidHom, restricted along that injection, proves their K-linear independence. If T were zero for every b, the all-one coefficient relation would force 1=0. Thus exists_semilinearImageTrace_ne_zero supplies b with s=T(b) nonzero.

MonoidHom.fiberEquivKerOfSurjective identifies each fiber of gamma.rangeRestrict with its kernel, whose cardinal is Nat.card gamma.ker. Fintype.sum_fiberwise' consequently proves sum_g gamma(g)b = h*T(b), with h=(Nat.card gamma.ker : K). Automorphisms fix h and s. For h nonzero take c=b/(h*s); summing its images gives h*s/(h*s)=1. Conversely h=0 makes every scalar trace zero by the same fiber identity, so trace one is impossible.

The image trace is nonzero by independence, rather than by dividing its value at 1 by the image cardinal. Thus positive characteristic may divide the image order: a faithful finite automorphism action has kernel order 1 and still admits this construction in that modular case. The sharp scalar criterion is distinct from necessity for an individual semilinear module. For example the zero module has an isomorphic norm even if the kernel order vanishes. A universal obstruction instead uses V=K with the gamma action: when h=0 its norm is zero while its invariant field contains 1. This paragraph explains the scalar obstruction; it does not assert a separately formalized classification of every V.

**Theorem 1.5 (The constructed scalar is consumed by the actual norm equivalence).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearKernelNormEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearKernelNormEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact telescope is {R : Type uR} {G : Type uG} {V : Type uV} {K : Type uK} [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V] [Field K] [Algebra R K] [Module K V] [IsScalarTower R K V], rho : Representation R G V, gamma : G to monoid (K equiv+* K), the genuine semilinearity equation hRho, and hker : (Nat.card gamma.ker : K) nonzero. The conclusion supplies c : K and e : rho.Coinvariants equiv-linear[R] rho.invariants such that sum_g gamma(g)c=1, for every v : V the underlying vector e(Coinvariants.mk rho v) equals rho.norm v, and for every w : rho.invariants, e.symm(w)=Coinvariants.mk rho (c smul w).

The proof selects c from the kernel-order scalar criterion, feeds its trace equation and hRho to scalar_conjugation_trace_one through semilinearScalarNormEquiv, and invokes both compiled formulas. This gives an equivalence for the canonical unnormalized norm on R-coinvariants, not merely the existence of some abstract isomorphism. No finite-dimensionality, coefficient-projectivity, abelian-group or faithful-action assumption is inserted.

Application boundary: this module proves an additive representation theorem. It does not identify the full jet principal-unit group with an additive module, prove a stable filtration for that group, or establish the extension/lifting argument required to transfer additive graded norms to that full group. Those missing bridges are separate mathematical obligations. The trace-one theorem here can be reused once an actual additive action and the requisite identifications have been proved.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.coinvariantsNorm`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearKernelNormEquiv`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.exists_semilinearScalarTraceOne_iff`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.scalar_conjugation_trace_one`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm.traceOneNormEquiv`
