# Splitting from native two-cocycle primitives

## Abstract

Explicit trace contraction and native graded primitives construct homomorphic sections of abelian-kernel group extensions.

**Theorem 1.1 (An explicit trace-one contraction).**

$$\forall (R: Type) (V: Type) (G: Type) [\operatorname{CommRing}\left(R\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(R, V\right)] [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] , \forall (rho: \operatorname{Representation}\left(R, G, V\right)), \forall (t: \operatorname{End}\left(R, V\right)), {\operatorname{Trace}\left(rho, t\right)=1} \Rightarrow \forall (f: (G\times G)\to V), {\operatorname{Coc}\left(rho, f\right)} \Rightarrow \forall (g: G), \forall (h: G), \operatorname{f}\left(g, h\right)=\operatorname{rho}\left(g, \operatorname{b}\left(rho, t, f, h\right)\right)-\operatorname{b}\left(rho, t, f, g\cdot h\right)+\operatorname{b}\left(rho, t, f, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.trace_one_primitive_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

R is any commutative ring, V any R-module, and G any finite group. These carriers have independent universes. Coc(rho,f) is the native raw IsCocycle₂ predicate for the SMul action rho. The abbreviation Trace(rho,t) means the sum over x in G of rho(x) composed with t composed with rho(x inverse). Here b(rho,t,f,g) is traceOnePrimitive rho t f g: the sum over x in G of rho(x) applied to t(f(x inverse,g)).

Apply rho(x) composed with t to the cocycle equation at (x inverse,g,h), and sum over x. Reindex the term involving x inverse times g by left multiplication by g. The trace-one identity evaluates the remaining conjugate sum to f(g,h). This gives exactly f equal to d(b). The native IsCoboundary₂ predicate uses d(b) equal to f, so all_two_cocycles_are_coboundaries_of_trace_one uses the symmetric equality.

No commutativity of G, dimension bound, field, inverse group order or projective-module assumption enters the contraction. The operator t itself is the hypothesis. This explicit cochain argument is a classical trace contraction; the stated generality and native interfaces are proved here, with no literature novelty claim.

**Theorem 1.2 (Correcting the actual extension factor set).**

$$\forall (U: Type) (E: Type) (G: Type) [\operatorname{CommGroup}\left(U\right)] [\operatorname{Group}\left(E\right)] [\operatorname{Group}\left(G\right)]  , \forall (S: \operatorname{GroupExtension}\left(U, E, G\right)), \forall (phi: \operatorname{MonoidHom}\left(G, \operatorname{MulAut}\left(U\right)\right)), {\forall (e: E), \forall (u: U), \operatorname{i}\left(\operatorname{phi}\left(\operatorname{p}\left(e\right), u\right)\right)=e\cdot \operatorname{i}\left(u\right)\cdot {e}^{-1}} \Rightarrow {\operatorname{Htwo}\left(\operatorname{rho}\left(phi\right)\right)} \Rightarrow \operatorname{Nonempty}\left(\operatorname{Splitting}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_all_two_cocycles_are_coboundaries` (`✓ std3`). ∎

*Citation.* Brian Conrad (2012). *Math 210B. Group cohomology and group extensions*. URL: <https://virtualmath1.stanford.edu/~conrad/210BPage/handouts/gpext.pdf>.

*Commentary.*

U is an arbitrary commutative group and E and G are arbitrary groups in independent universes. S is the given native GroupExtension U E G; i and p denote S.inl and S.rightHom. The prescribed action phi is a homomorphism from G to MulAut U. Compatibility means i(phi(p(e))(u)) equals e i(u) e inverse for every e and u. The integral representation rho(phi) is phiRepresentation phi on Additive U; its value at g,u is Additive.ofMul(phi(g)(Additive.toMul u)).

Htwo(rho) means every native raw two-cocycle for precisely rho has a native raw primitive. Choose a set-theoretic native Section sigma. Its actual factor c is characterized by i(c(g,h)) equal to sigma(g) sigma(h) sigma(gh) inverse. Associativity and compatibility give c(g,h)c(gh,k) equal to phi(g)(c(h,k))c(g,hk). Commutativity of U converts this to the native additive cocycle equation, without any normalization assumption on sigma.

For its primitive b, put beta(g) equal to Additive.toMul(b(g)). The native coboundary equation says c(g,h) equals phi(g)(beta(h)) beta(gh) inverse beta(g). Thus delta(g) equal to beta(g) inverse satisfies delta(g) phi(g)(delta(h)) c(g,h) equal to delta(gh). Consequently s(g) equal to i(delta(g)) sigma(g) is a group homomorphism and p(s(g)) equals g. This constructs an actual native S.Splitting. The generic theorem states Nonempty because Splitting is a structure in Type; the definitions below choose an actual structure.

The extension-to-factor-set correspondence and coboundary correction are classical. Conrad's Group cohomology and group extensions, section 2, gives the factor-set construction and identifies the zero class with the semidirect product. The construction here retains the prescribed action and independent carrier universes. It assumes neither a homomorphic section nor a stronger auxiliary structure.

**Definition 1.3 (A finite stable filtration gives an actual section).**

$$\forall (U: Type) (E: Type) (G: Type) [\operatorname{CommGroup}\left(U\right)] [\operatorname{Group}\left(E\right)] [\operatorname{Group}\left(G\right)]  , \forall (S: \operatorname{GroupExtension}\left(U, E, G\right)), \forall (phi: \operatorname{MonoidHom}\left(G, \operatorname{MulAut}\left(U\right)\right)), {\forall (e: E), \forall (u: U), \operatorname{i}\left(\operatorname{phi}\left(\operatorname{p}\left(e\right), u\right)\right)=e\cdot \operatorname{i}\left(u\right)\cdot {e}^{-1}} \Rightarrow \forall (F: Nat\to \operatorname{Subrepresentation}\left(\operatorname{rho}\left(phi\right)\right)), {\operatorname{Monotone}\left(F\right)} \Rightarrow \forall (n: Nat), {\operatorname{F}\left(0\right)=\operatorname{bot}\left(\right)} \Rightarrow {\operatorname{F}\left(n\right)=\operatorname{top}\left(\right)} \Rightarrow {\forall (k: Nat), {k<n} \Rightarrow \operatorname{Htwo}\left(\operatorname{Grade}\left(F, k\right)\right)} \Rightarrow \operatorname{Splitting}\left(S\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extension and compatibility conventions are those above. F is a monotone sequence of native Subrepresentation values for rho(phi), from bottom at zero to top at n. Grade(F,k) is filtrationGrade F k from FilteredTwoCocycle, on the actual quotient of F(k+1) by the inverse image of F k under its subtype. Htwo is required separately on every such grade with k less than n.

For each actual ambient cocycle, is_coboundary_two_of_finite_stable_filtration supplies its primitive. Passing this fact to the shared factor correction yields the displayed native Splitting structure. Only the filtration length is finite: G, E and U may be infinite, and n may be zero. No splitting of the coefficient filtration is supplied or required.

**Definition 1.4 (Independent trace-one witnesses on the native grades).**

$$\forall (U: Type) (E: Type) (G: Type) [\operatorname{CommGroup}\left(U\right)] [\operatorname{Group}\left(E\right)] [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] , \forall (S: \operatorname{GroupExtension}\left(U, E, G\right)), \forall (phi: \operatorname{MonoidHom}\left(G, \operatorname{MulAut}\left(U\right)\right)), {\forall (e: E), \forall (u: U), \operatorname{i}\left(\operatorname{phi}\left(\operatorname{p}\left(e\right), u\right)\right)=e\cdot \operatorname{i}\left(u\right)\cdot {e}^{-1}} \Rightarrow \forall (F: Nat\to \operatorname{Subrepresentation}\left(\operatorname{rho}\left(phi\right)\right)), {\operatorname{Monotone}\left(F\right)} \Rightarrow \forall (n: Nat), {\operatorname{F}\left(0\right)=\operatorname{bot}\left(\right)} \Rightarrow {\operatorname{F}\left(n\right)=\operatorname{top}\left(\right)} \Rightarrow {\forall (k: Nat), {k<n} \Rightarrow \exists (t: \operatorname{End}\left(\operatorname{Integers}\left(\right), \operatorname{Carrier}\left(F, k\right)\right)), \operatorname{Trace}\left(\operatorname{Grade}\left(F, k\right), t\right)=1} \Rightarrow \operatorname{Splitting}\left(S\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration_grade_trace_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here G is finite. Carrier(F,k) denotes the actual underlying quotient module of Grade(F,k). Trace on each grade uses that grade's inherited representation. For every k less than n the hypothesis supplies its own integral linear endomorphism t; the witnesses need not come from one endomorphism of Additive U.

Apply the explicit trace contraction to each chosen grade witness, obtaining that grade's native Htwo property. The finite-filtration primitive theorem then supplies an ambient primitive, and the shared extension correction gives the actual homomorphic section. The conclusion does not infer a global trace-one operator. There is no logarithm on U or extra field-module structure on the multiplicative kernel.

The companion extension_splitting_of_trace_one uses a single trace-one integral endomorphism of Additive U directly in the same correction theorem. These constructions assemble classical cochain mechanisms on the given native extension and native quotient carriers. No assertion about a specific principal-unit filtration, semilinear realization, or literature novelty is made.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_all_two_cocycles_are_coboundaries`
- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration`
- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration_grade_trace_one`
- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.trace_one_primitive_spec`
- Dependency: [D5/S3/HomologicalAlgebra/FilteredTwoCocycle](FilteredTwoCocycle.md)
