# Insertion mean rigidity

## Abstract

A scalar recurrence cone forces rigidity of every original insertion mean.

Let Grid be the real functions on all natural pairs. Recurrent means 2g(m+1,n+1)+g(m+1,n)+g(m,n+1)=4g(m,n) for every m,n. Indices include zero, and the grid need not have positive mass at (0,0). For an arbitrary finite index set t, a gives real coefficients and v gives the two natural exponents. Repeated exponents and empty sums are allowed.

**Theorem 1.1 (Finite polynomial positivity).**

$$(\forall I: Type, (\forall t: \operatorname{Finset}\left(I\right), (\forall a: (I \to \mathbb{R}), (\forall v: (I \to (\mathbb{N} \times \mathbb{N})), (\forall g: ((\mathbb{N} \times \mathbb{N}) \to \mathbb{R}), ((\forall q: (\mathbb{N} \times \mathbb{N}), (0 \le \operatorname{g}\left(q\right))) \Rightarrow ((\forall m: \mathbb{N}, (\forall n: \mathbb{N}, ((((2 \cdot \operatorname{g}\left(((m+1),(n+1))\right))+\operatorname{g}\left(((m+1),n)\right))+\operatorname{g}\left((m,(n+1))\right)) = (4 \cdot \operatorname{g}\left((m,n)\right))))) \Rightarrow ((\forall r: \mathbb{R}, (\forall s: \mathbb{R}, ((0 \le r) \Rightarrow ((0 \le s) \Rightarrow ((((r+s)+((2 \cdot r) \cdot s)) = 4) \Rightarrow (0 \le \sum_{k \in t} ((\operatorname{a}\left(k\right) \cdot {r}^{\operatorname{fst}\left(\operatorname{v}\left(k\right)\right)}) \cdot {s}^{\operatorname{snd}\left(\operatorname{v}\left(k\right)\right)}))))))) \Rightarrow (0 \le \sum_{k \in t} (\operatorname{a}\left(k\right) \cdot \operatorname{g}\left(\operatorname{v}\left(k\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/InsertionMeanRigidity.finite_polynomial_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectral set is K={(r,s): r>=0, s>=0, r+s+2rs=4}. It includes the two endpoints (0,4) and (4,0). Every finite real polynomial nonnegative on K has nonnegative evaluation on every nonnegative recurrent grid, replacing r^m*s^n by g(m,n). No measure representation is assumed.

Nonnegativity and recurrence give both one-step bounds by four times the current entry, hence g(m,n)<=4^(m+n)g(0,0). Zero initial mass therefore forces the entire grid to vanish. At positive mass divide by g(0,0). The normalized grids form a nonempty closed subset of the product of the intervals [0,4^(m+n)], and are compact. A continuous finite linear functional attains its minimum at an extreme point, using the exposed minimizing face and the existing extreme-point existence theorem.

If a nonnegative recurrent h is bounded above by 4g for an extreme normalized g, the complementary grid 4g-h is also nonnegative and recurrent. At h(0,0)=0 or 4 the zero-mass argument applies. Otherwise normalize h and its complement to express g as a strict convex combination; extremality forces h(q)=h(0,0)g(q). Apply this to each coordinate shift. Both shifts are scalar multiples of g, so g(m,n)=r^m*s^n, with r,s>=0 and r+s+2rs=4. Evaluating the polynomial at this minimizing extreme grid proves the assertion and scaling returns the original mass.

For the original kernel let M have only a multiplication and a two-sided unit. U is any self-map. Kernel means M -> M -> R. Put p(U,j)=U^j(1), P(U,j,x)=x*p(U,j), S(U,g)(x,y)=(g(P(U,1,x),y)+g(P(U,2,x),y))/2, T(U,g)(x,y)=(g(x,P(U,1,y))+g(x,P(U,2,y)))/2, and F(U,c,m,n)=S(U)^m(T(U)^n(c)). Function differences and zero kernels below are pointwise.

RawCost requires c(a,b)>=0, c(a,a)=0, and c(a*u,b*v)+c(a*U(u),b*U(v))+c(a*U(U(u)),b*U(U(v)))=3c(a,b)+3c(u,v) for every a,b,u,v. The two return assumptions below are cost equalities at P(U,3), for every pair of endpoints. They are not identities between elements of M.

**Theorem 1.2 (All original insertion means are fixed).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: (M \to M), (\forall c: (M \to (M \to \mathbb{R})), (\operatorname{RawCost}\left(U, c\right) \Rightarrow ((\forall x: M, (\forall y: M, (\operatorname{c}\left(x, y\right) = \operatorname{c}\left(y, x\right)))) \Rightarrow ((\forall x: M, (\forall y: M, (\operatorname{c}\left(\operatorname{P}\left(U, 3, x\right), y\right) = \operatorname{c}\left(x, y\right)))) \Rightarrow ((\forall x: M, (\forall y: M, (\operatorname{c}\left(x, \operatorname{P}\left(U, 3, y\right)\right) = \operatorname{c}\left(x, y\right)))) \Rightarrow ((\operatorname{c}\left(1, \operatorname{p}\left(U, 1\right)\right) = 0) \Rightarrow ((\operatorname{c}\left(1, \operatorname{p}\left(U, 2\right)\right) = 0) \Rightarrow ((\forall m: \mathbb{N}, (\forall n: \mathbb{N}, (\forall x: M, (\forall y: M, (\operatorname{F}\left(U, c, m, n, x, y\right) = \operatorname{c}\left(x, y\right)))))) \land ((\operatorname{S}\left(U, c\right) = c) \land ((\operatorname{T}\left(U, c\right) = c) \land ((\operatorname{S}\left(U, \operatorname{T}\left(U, c\right)\right) = c) \land ((c-\operatorname{S}\left(U, \operatorname{T}\left(U, c\right)\right)) = 0))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/InsertionMeanRigidity.full_original_insertion_mean_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full original cost statement: all natural m,n, both universal P3 cost returns, symmetry and both zero unit-orbit costs are retained. There is no associativity, commutativity, U(1)=1, periodicity of U, multiplicativity, surjectivity, triangle inequality, Hilbert realization, topology on M, or assumed growth bound.

The original single and unit_compare inequalities give c(x,y)<=3(q(x)+q(y)) and q(s*t)<=3(q(s)+q(t)), where q(x)=c(x,1). A zero q stays zero under each right insertion. Thus all T^n(c)(x,1) are bounded by 3q(x). Three original balance instances, symmetry and the P3 cost returns yield (2ST+S+T)c=4c. Separate endpoint averaging preserves this recurrence and nonnegativity; S and T commute without changing the order of operations at either endpoint.

The scalar theorem applied to a three-term square polynomial gives axis quadratic positivity. The existing quadratic-discriminant inequality gives log-convexity of both axes. A nonnegative bounded log-convex sequence cannot increase at its first step: otherwise the original positive_all and convex_ratio suppliers imply a geometric lower bound of ratio greater than one, contradicting the bound by power divergence. Applied at (x,1), this proves the two-anchor mean inequality.

The original sync_iter supplier and the right P3 return identify c(x,p1)=q(U^2(x)), c(x,p2)=q(U(x)) and q(U^3(x))=q(x). The three cyclic inequalities force these q values to agree. Hence T(c)(x,1)=q(x), and the recurrence gives (q(P1(x))+q(P2(x)))/2=q(x). Induction through the actual positive means now gives the uniform bound F(U,c,m,n)(x,y)<=3(q(x)+q(y)) at every finite m,n. This bound is derived from the raw assumptions, not supplied as a hypothesis.

Apply the bounded log-convex argument to every shifted axis. Both successors are at most the current entry. The recurrence then forces both successor deficits to vanish. Two inductions give every F(U,c,m,n)(x,y)=c(x,y), including zero indices. Function extensionality yields S(c)=T(c)=ST(c)=c and the zero difference kernel.

The statement source is C133 Unanchored Marker Bounded Orbits Continuation W, Sections 42 and 43.1. The proof reuses the original RawUnanchoredReplication suppliers and the original KarpZhangCatalanPower log-convexity suppliers, together with Mathlib compactness, exposed-face, discriminant and power-divergence results. These are algebraic and scalar analytic conclusions under the displayed assumptions. No physical realization or literature priority is asserted; Sections 43.2 and 43.3 require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Completion/InsertionMeanRigidity.finite_polynomial_positive`
- Truth anchor: `D5/S3/Quantum/Completion/InsertionMeanRigidity.full_original_insertion_mean_rigidity`
- Dependency: [D5/S3/Analytic/KarpZhangCatalanPower/Result](../../Analytic/KarpZhangCatalanPower/Result.md)
- Dependency: [D5/S3/Quantum/Completion/RawUnanchoredReplication](RawUnanchoredReplication.md)
