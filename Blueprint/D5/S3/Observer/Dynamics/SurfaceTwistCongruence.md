# Finite nonabelian observation of a separating twist

## Abstract

An explicit fully invariant finite quotient detects exactly the multiples of a prescribed separating-twist power in every genus at least two.

For e in N, G_e is the actual presented group on 4+2e generators with the ordered surface relator, of genus e+2. The first handle has generators a,b and boundary h=aba^-1b^-1. The endomorphism tau conjugates a,b by h and fixes every other generator. Its inverse is constructed in the proof.

D_m is the dihedral group with rotation order 4m and total order 8m. Let Rep be Hom(G_e,D_m). The map E sends x to the function rho -> rho(x). Q is its actual image subgroup and q is E with codomain restricted to that image. P_n is repeated composition of tau, with P_0 the identity and P_(n+1)=tau composed with P_n.

**Theorem 1.1 (A finite fully invariant quotient with exact outer period m).**

$$\begin{aligned}\forall e, m: \operatorname{Nat}(), 0 < m \Rightarrow\\\operatorname{Finite}(Q) \land \operatorname{Surjective}(q) \land \operatorname{FullInvariantKernel}(q) \land\\\operatorname{Bijective}(tau) \land\\(\forall n: \operatorname{Nat}(), \operatorname{Inner}(q, \operatorname{P}(n)) \operatorname{iff}() \operatorname{Divides}(m, n)) \land\\(\forall n: \operatorname{Nat}(), \operatorname{OrbitReturn}(q, \operatorname{P}(n), w) \operatorname{iff}() \operatorname{Divides}(m, n)) \land\\(\forall n: \operatorname{Nat}(), \operatorname{Divides}(m, n) \Rightarrow \forall x: G, \operatorname{apply}(q, \operatorname{apply}(\operatorname{P}(n), x)) = \operatorname{apply}(q, x)) \land\\(\forall A, \operatorname{CommGroup}(A) \Rightarrow \forall f: \operatorname{Hom}(G, A), \operatorname{comp}(f, tau) = f).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/SurfaceTwistCongruence.finite_characteristic_twist_detector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OrbitReturn(q,P_n,w) means that q(P_n(w)) and q(w) are conjugate in Q, where w=a d^-1. FullInvariantKernel(q) means that for every group endomorphism f of G_e and every x, q(x)=1 implies q(f(x))=1. Inner(q,P_n) means that there exists one z in Q such that q(P_n(x))=z q(x) z^-1 for every x. It is the literal innerness condition for the induced quotient automorphism, not separate conjugacy tests for separate generators.

A homomorphism is determined by its finitely many generator images. Hence Rep, the ambient product and Q are finite for m>0. The kernel is fully invariant because rho composed with any endomorphism is another member of Rep. The selected dihedral representation alone is never assumed to have characteristic kernel.

Every dihedral commutator is an even rotation. Its m-th power is central, so every representation is fixed by tau^n whenever m divides n. For the converse, map (a,b,c,d) to (s,r,r,s) and the extra generators to one. The surface relation holds. Under tau^n the first image is sr^(4n), while the fourth stays s. Since a and d initially have equal images, one common conjugator can exist only when 4m divides 4n. The mixed word w=a d^-1 has image one, while its nth image is r^(-4n). Thus the same characteristic quotient detects its conjugacy-class orbit with exact period m.

All abelian observations kill the boundary commutator and are unchanged by tau. The finite nonabelian detector therefore retains information lost by every abelian target. Klukowski, arXiv:2411.06867v2, Definition 3, Corollary 7 and Conjecture 13 provide the congruence-subgroup context. The qualitative cyclic consequence is known. No solution of the full curve-orbit conjecture, topological surface identification, or three-manifold rigidity theorem is asserted here.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/SurfaceTwistCongruence.finite_characteristic_twist_detector`
