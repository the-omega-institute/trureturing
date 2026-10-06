# Complete Anchored Phase Classification

## Abstract

For finite named directed multigraphs, anchored phase coordinates give the complete compact abelian quotient and can be assigned independently in one edge field.

Fix finite types V,E, endpoint maps s,t:E to V and an arbitrary selected named spanning tree T. Its selected edges are nonloops, their unordered endpoint pairs are distinct, and precisely their simple support is connected and acyclic. The original edge type retains all parallel edges, loops and separately named reverse edges. Fix a reference subset R and a root r in R. Write n=card V, m=card E and k=card R.

For u:E to Circle, let h_v(u) be the actual signed phase product along the unique simple path in this chosen tree from r to v. Negative traversal is the inverse phase of the same original named edge; it introduces neither another independent phase nor an execution permission. Let C be the product of Circle indexed by E minus T and by R minus r. The coordinate chi(u) has entries h_s(u) u_e h_t(u) inverse and h_a(u), respectively.

The anchored vertex subgroup H consists exactly of functions g with g_a=1 for every a in R. Its action is (g dot u)_e=g_t u_e g_s inverse. The homomorphism delta:H to Circle^E sends g to g_t g_s inverse; N is its image. The quotient is Circle^E/N with its quotient group topology, rather than treating H itself as a literal subgroup of edge fields.

Given z=(lambda,alpha) in C, extend alpha to a vertex potential H_z by setting H_z(r)=1, H_z(a)=alpha_a at other references and H_z(v)=1 elsewhere. Extend lambda to Lambda_z(e)=1 on T and lambda_e outside T. The single field sigma(z)_e=H_z(t(e)) Lambda_z(e) H_z(s(e)) inverse realizes all entries.

**Theorem 1.1 (Complete invariants, continuous section and exact quotient dimension).**

$$\forall V: Type, \forall E: Type, \forall s: E \to V, \forall t: E \to V, \forall T: Set\left(E\right), \forall R: Set\left(V\right), \forall r: V, Fintype\left(V\right) \land Fintype\left(E\right) \land NamedSpanningTree\left(s, t, T\right) \land Member\left(r, R\right) \Rightarrow (\forall g: H, \forall u: E \to Circle, chi\left(gauge\left(g, u\right)\right) = chi\left(u\right)) \land (\forall u: E \to Circle, \forall w: E \to Circle, chi\left(u\right) = chi\left(w\right) \iff \exists g: H, gauge\left(g, u\right) = w) \land (\forall z: C, chi\left(sigma\left(z\right)\right) = z) \land (Continuous\left(sigma\right)) \land (\forall z: C, \forall zPrime: C, sigma\left(mul\left(z, zPrime\right)\right) = mul\left(sigma\left(z\right), sigma\left(zPrime\right)\right)) \land (ker\left(chi\right) = N) \land (\forall u: E \to Circle, \forall w: E \to Circle, cosetN\left(u\right) = cosetN\left(w\right) \iff \exists g: H, gauge\left(g, u\right) = w) \land (\exists q: ContinuousMulEquiv\left(QuotientGroup\left(E \to Circle, N\right), C\right), (\forall u: E \to Circle, q\left(cosetN\left(u\right)\right) = chi\left(u\right)) \land (\forall z: C, qInverse\left(z\right) = cosetN\left(sigma\left(z\right)\right))) \land (CompactSpace\left(QuotientGroup\left(E \to Circle, N\right)\right)) \land (T2Space\left(QuotientGroup\left(E \to Circle, N\right)\right)) \land (IsTopologicalGroup\left(QuotientGroup\left(E \to Circle, N\right)\right)) \land (IsClosed\left(N\right)) \land (tCard + 1 = n) \land (c + tCard = m) \land (a + 1 = k) \land (c + a + n = m + k) \land (c + a = m + k - n) \land (c = m + 1 - n) \land (c + a = c + k - 1) \land (Nonempty\left(ContinuousMulEquiv\left(C, CirclePower\left(m + k - n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification.anchored_phase_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root-path covariance proves invariance under H. If two coordinate tuples agree, take g_v=h_v(w) h_v(u) inverse. Agreement at every reference makes this an anchored gauge. The selected-edge endpoint law and the non-tree coordinates then reconstruct every original named edge.

Lambda_z is one on every selected edge, so its actual tree path products are one. The endpoint covariance formula therefore gives h_v(sigma(z))=H_z(v). Consequently chi(sigma(z))=z, with no extra equations between loops, parallel edges or reference coordinates. Both chi and sigma are continuous and multiplicative.

The kernel of chi is exactly N and the coordinate fibers are exactly its cosets. The quotient homomorphism has inverse z mapping to the coset of sigma(z). The quotient map makes the forward map continuous and the continuous section makes the inverse continuous. The quotient is compact, Hausdorff and abelian, with continuous group operations; N is closed.

Selected named edges are in bijection with the edges of this same tree support. Thus t+1=n, c+t=m and a+1=k, where t=card T, c=card(E minus T), and a=card(R minus r). The independent coordinate number d=c+a satisfies d+n=m+k, so d=m+k-n and b=c=m+1-n, with d=b+k-1. Only the finite index set is reindexed to Fin d; no cardinality of the underlying Circle product is used. Natural subtraction is justified by these additive identities.

The quantifiers include a single vertex with no edges, arbitrary one-vertex loops, single or all-vertex references, tree graphs and parallel named edges. This classifies the declared full phase space; further physical constraints would restrict its image. It does not identify phases from intensity data or grant operations along formal inverse paths.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification.anchored_phase_classification`
- Dependency: [D5/S3/Factorization/Galois/SparseCharacterSynchronization](../../Factorization/Galois/SparseCharacterSynchronization.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport](NamedTreePhaseTransport.md)
