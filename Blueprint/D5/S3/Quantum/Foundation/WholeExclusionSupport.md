# Whole original exclusion support

## Abstract

Global positivity of a candidate vanishing on the entire original exclusion set.

The carrier is any finite dimensional real normed vector space V, with an original closed pointed cone C and a linear unit u strictly positive on C away from zero. The existing definitions are K=base(C,u)={x in C : u(x)=1}, P=pure(C,u)=ext(K), proper(C,u,f) meaning 0<=f(x)<=u(x) for every x in C, and confirms(C,u,r,f) meaning proper(C,u,f) and f(r)=1. The entire original exclusion set is D_r=exclusion(C,u,r)={x in K : there exists one original proper f with f(r)=1 and f(x)=0}. The quantifier over effects is the full interval, and D_r contains all such mixed states.

**Theorem 1.1 (A whole-exclusion zero condition forces global positivity).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{NormedSpace}\left(\mathbb{R}, V\right)][\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)]\forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall r \in \operatorname{pure}\left(C, u\right),\; \forall h \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\operatorname{IsClosed}\left(C\right) \land \left(\left(\forall x \in V,\; \left(x\in C \land x\neq 0\right) \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right) \land \left(\operatorname{apply}\left(h, r\right) = 1 \land \left(\left(\forall x \in V,\; x\in C \Rightarrow \operatorname{apply}\left(h, x\right) \le \operatorname{apply}\left(u, x\right)\right) \land \left(\forall x \in V,\; x\in \operatorname{exclusion}\left(C, u, r\right) \Rightarrow \operatorname{apply}\left(h, x\right) = 0\right)\right)\right)\right)\right) \Rightarrow \operatorname{confirms}\left(C, u, r, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WholeExclusionSupport.whole_exclusion_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure r and real linear h, assume h(r)=1, h<=u on the entire original cone, and h vanishes on all of D_r. Then h is an original proper confirmer of r. No positivity of h, finite frame, dimension-two condition, face classification, least effect or joint frame is an assumption. Generatingness and nontriviality are unnecessary for this prerequisite; every instance of the original source domain is included.

Compactness of the entire base gives a minimizing state x and c=h(x). If c<0, construct g=(h-cu)/(1-c). Its lower bound follows from the minimum on every original pure point; its upper bound follows from h<=u. The existing cone_bound theorem then proves that g is proper on every original cone vector. The same g has g(r)=1 and g(x)=0, so x belongs to the entire D_r. The assumed vanishing forces c=0, a contradiction. The minimum is therefore nonnegative, and the existing nonneg_on_cone theorem extends the conclusion to the entire cone. A mixed minimizing state suffices, so no extreme-point selection theorem is needed.

This is the global normalization prerequisite used in VII 103.5 and VII 104.3, with VII 104.9 as its finite-pure target. For a prospective three-effect frame, substitute h=u-a_p-a_q only after establishing h(r)=1 and a_p+a_q=u on the entire D_r from the original EB and Pair_perp entrance. This theorem does not establish those geometric premises or assert the joint frame. The original finite-ALL-P claim remains: EB_ge1 plus Pair_perp and finiteness of all original ext(K) imply that the entire K is a classical triangle, with all consequences of VII104.16. The first two conjuncts of the frozen ExclusionBallFaces.exclusion_ball_faces supply the complete proper-face classification and whole-exclusion exposure directly from the original EB premise. Its third conjunct requires global pairProper, which is not supplied by weak Pair_perp. Native facet existence is supplied below. Remaining original bridges are the weak orthogonal-pair and joint-frame construction, finite ball extreme-point dimension obstruction and low-dimensional exclusions, dimension-two base and triangle deduction, whole-base barycentric reconstruction, and the full classical effect, face-lattice and same-cone/unit EJA consequences. No smaller conditional theorem is identified with VII104.9. No literature priority is asserted.

**Theorem 1.2 (Finite original pure points force a native cone facet).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{NormedSpace}\left(\mathbb{R}, V\right)][\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)][\operatorname{Nontrivial}\left(V\right)]\forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; [\operatorname{Finite}\left(\operatorname{pure}\left(C, u\right)\right)]\left(\operatorname{IsClosed}\left(C\right) \land \left(\left(\forall x \in V,\; \left(x\in C \land x\neq 0\right) \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right) \land \operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{R}, V\right)\right)\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{facets}\left(C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WholeExclusionSupport.finite_pure_facet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original carrier V is nontrivial and finite dimensional over the reals. The original cone C is closed and generating, its original unit u is strictly positive away from zero, and ALL original pure points P=ext(base(C,u)) are finite. The conclusion is Nonempty(facets(C)), where a native cone face F is a facet exactly when dim(span(F))+1=dim(V). There is no assumed facet, finite selected frame, zero-gluing, EB, pair, simplex, or dimension-two premise. In dimension one the facet is the zero cone and its normalized slice is empty; nonemptiness of a normalized facet requires dimension at least two.

Reuse pure_span and nonneg_on_cone for the entire original P. Among nonzero functionals nonnegative on P, choose one whose zero-probe span W has maximal attained integer rank. If W is smaller than its kernel, choose a vector x in the kernel outside W and a linear functional a vanishing on W but not on x. Since P spans V, orient a to be negative at some original probe. The finite minimum t=min f(p)/(-a(p)) over negative probes is positive. The functional g=f+t a remains nonnegative on ALL P, stays nonzero by evaluation at x, preserves every old zero, and adds a minimizing probe outside W. Its strictly larger zero rank contradicts maximality. Thus W=ker(f). Positivity on the entire original cone makes C intersect ker(f) a native face, and its span equals ker(f) because it contains every zero probe. The nonzero-dual kernel formula gives codimension one.

The constructed positive finite perturbation and strict growth of zero-probe rank are new content in this module; direct use of the existing compact-base positivity and spanning results is not counted as new mathematics. This proves the previously missing generic facet existence and rank bridge, without identifying the facet with an exclusion or closing VII104.9. The original entire triangle target and its remaining bridges stated above remain open. Literature priority is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/WholeExclusionSupport.finite_pure_facet`
- Truth anchor: `D5/S3/Quantum/Foundation/WholeExclusionSupport.whole_exclusion_support`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
