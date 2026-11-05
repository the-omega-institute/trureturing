# Named Edge Section Transport

## Abstract

Named edge transport retains parallel edges, loops and dependent fibres in the root evaluation criterion.

Let V and E be arbitrary vertex and named edge types with endpoint maps s,t:E to V. A signed generator is an original named edge or the formal inverse of that same edge. Finite paths use the symmetrified original quiver. No finiteness, simplicity, chosen spanning tree or commutativity assumption is imposed.

Each edge e is represented by the three-segment path s(e), source(e), target(e), t(e). The two ports are distinct constructors and retain the original edge name, including when s(e)=t(e) or another edge has the same endpoints. Write endpoint for this projection to V. EdgeEquivalences(s,t,F) means exactly the family of equivalences F(s(e)) to F(t(e)); EdgeUnitaries means the family of complex linear isometric equivalences. ComplexNormedFibres(V) means a family of normed complex vector spaces indexed by V. These are notation for the full parameter families, not extra hypotheses. The port fibres are the original endpoint fibres. The middle segment carries exactly U(e), the outer segments carry identity maps, and reverse traversal uses the inverse of that same map.

**Theorem 1.1 (Transport on every actual finite path).**

$$(\forall V: \operatorname{Type}\left(\right), (\forall E: \operatorname{Type}\left(\right), (\forall s: E \to V, (\forall t: E \to V, (\forall F: V \to \operatorname{Type}\left(\right), (\forall U: \operatorname{EdgeEquivalences}\left(s, t, F\right), (((\forall a: \operatorname{IncidenceVertex}\left(V, E\right), (\forall b: \operatorname{IncidenceVertex}\left(V, E\right), (\forall p: \operatorname{Walk}\left(\operatorname{incidenceGraph}\left(s, t\right), a, b\right), (\operatorname{namedTransport}\left(U, \operatorname{projectWalk}\left(p\right)\right) = \operatorname{walk}\left(\operatorname{incidenceTransport}\left(U\right), p\right))))) \land (\forall a: V, (\forall b: V, (\forall p: \operatorname{NamedPath}\left(s, t, a, b\right), (\operatorname{walk}\left(\operatorname{incidenceTransport}\left(U\right), \operatorname{liftPath}\left(p\right)\right) = \operatorname{namedTransport}\left(U, p\right)))))) \land (\forall a: V, (\forall b: V, (\forall p: \operatorname{NamedPath}\left(s, t, a, b\right), (\operatorname{projectWalk}\left(\operatorname{liftPath}\left(p\right)\right) = p)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.incidence_path_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An outer segment projects to an empty path. A middle segment projects to its signed original generator. Concatenation projects every finite incidence walk, including walks beginning at ports. Each signed original generator lifts to its three-segment path or its reverse. The projection and lift preserve the actual dependent-fibre composite. Projecting a lifted path returns its literal signed original path, retaining the named generators even when their transport operators happen to agree.

**Theorem 1.2 (Root evaluation and unitary holonomy).**

$$(\forall V: \operatorname{Type}\left(\right), (\forall E: \operatorname{Type}\left(\right), (\forall s: E \to V, (\forall t: E \to V, (\forall F: \operatorname{ComplexNormedFibres}\left(V\right), (\forall U: \operatorname{EdgeUnitaries}\left(s, t, F\right), (\forall r: V, ((\forall a: V, \operatorname{Nonempty}\left(\operatorname{NamedPath}\left(s, t, r, a\right)\right)) \implies (\exists ev: \operatorname{Equiv}\left(\operatorname{NamedSection}\left(\operatorname{underlying}\left(U\right)\right), \operatorname{holonomyKernel}\left(U, r\right)\right), (((((\forall sigma: \operatorname{NamedSection}\left(\operatorname{underlying}\left(U\right)\right), (\operatorname{value}\left(\operatorname{Apply}\left(ev, sigma\right)\right) = \operatorname{section}\left(sigma, r\right))) \land (\forall x: \operatorname{holonomyKernel}\left(U, r\right), (\forall a: V, (\forall p: \operatorname{NamedPath}\left(s, t, r, a\right), (\operatorname{section}\left(\operatorname{Apply}\left(\operatorname{inverse}\left(ev\right), x\right), a\right) = \operatorname{Apply}\left(\operatorname{unitaryTransport}\left(U, p\right), \operatorname{value}\left(x\right)\right)))))) \land (\forall sigma: \operatorname{NamedSection}\left(\operatorname{underlying}\left(U\right)\right), (\forall a: V, (\left\lVert \operatorname{section}\left(sigma, a\right) \right\rVert = \left\lVert \operatorname{section}\left(sigma, r\right) \right\rVert)))) \land (\forall sigma: \operatorname{NamedSection}\left(\operatorname{underlying}\left(U\right)\right), (\forall tau: \operatorname{NamedSection}\left(\operatorname{underlying}\left(U\right)\right), (\left\lVert (\operatorname{value}\left(\operatorname{Apply}\left(ev, sigma\right)\right) - \operatorname{value}\left(\operatorname{Apply}\left(ev, tau\right)\right)) \right\rVert = \left\lVert (\operatorname{section}\left(sigma, r\right) - \operatorname{section}\left(tau, r\right)) \right\rVert)))) \land ((\forall a: V, (\forall p: \operatorname{NamedPath}\left(s, t, r, a\right), (\forall q: \operatorname{NamedPath}\left(s, t, r, a\right), (\forall x: \operatorname{Apply}\left(F, r\right), (\operatorname{Apply}\left(\operatorname{unitaryTransport}\left(U, p\right), x\right) = \operatorname{Apply}\left(\operatorname{unitaryTransport}\left(U, q\right), x\right)))))) \iff (\forall p: \operatorname{NamedPath}\left(s, t, r, r\right), (\operatorname{unitaryTransport}\left(U, p\right) = \operatorname{LinearIsometryIdentity}\left(\operatorname{Apply}\left(F, r\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.named_unitary_root_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Place a normed complex vector space F(v) at each vertex and a linear isometric equivalence U(e) at each named edge. The finite-dimensional unitary setting is obtained by taking the original fibres isometric to the same complex d-space. Connectedness means that every vertex admits an actual finite signed path from the chosen root. Compatible sections satisfy every original named edge equation.

Extension to the ports and restriction to the original vertices are inverse maps on sections. Projection and lifting identify the common fixed vectors of all root loops. Applying ConfigurationPathTransport.rootSectionMap_bijective to this faithful incidence graph supplies the section bijection. In the formulas, value denotes the underlying vector of a subtype, section denotes its value at a vertex, and inverse denotes the inverse equivalence. The comparison is root evaluation. Its inverse at any vertex is transport along every root-to-vertex path, and the target is the intersection of the kernels of all actual root-loop operators minus the identity.

Every compatible section has the same norm in each fibre as at the root. The comparison preserves the norm of differences measured in the root fibre. This is the root-fibre metric on sections; no product norm or summability on the vertex set is assumed. Every root vector transports independently of path exactly when every root-loop operator is the identity. Existence of a fixed vector or the zero section does not imply that all-vector condition.

No assertion is made here about two-cell attaching boundaries or continuous path homotopy. For a simply connected two-dimensional cell complex, passing from flat attaching faces to identity transport on every loop requires a separate topological correspondence. Local face flatness on a punctured region does not supply that correspondence, and nontrivial holonomy around its hole remains possible.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.incidence_path_transport`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.named_unitary_root_classification`
- Dependency: [D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport](ConfigurationPathTransport.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport](../../Observer/AgencyHolonomy/NamedTreePhaseTransport.md)
