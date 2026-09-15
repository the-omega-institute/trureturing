# Finite observation beyond the metabelian quotient

## Abstract

A finite fully invariant matrix quotient resolves a second-derived surface-word orbit on every prescribed finite time window.

Fix e in N and m>0. G is the previous actual surface presentation of genus e+3, and tau is the same first-handle twist. Let u=[[a1,a2],[b1,b3]]. Let F be the unit group of seven-by-seven matrices over ZMod(m). The map E evaluates each x in every homomorphism G to F. Q is the actual image subgroup and q is its surjective image restriction.

**Theorem 1.1 (A characteristic quotient with residue-sensitive word orbits).**

$$\begin{aligned}\forall e, m: \operatorname{Nat}(), 0 < m \Rightarrow\\\operatorname{Finite}(Q) \land \operatorname{Surjective}(q) \land\\\operatorname{FullKernel}(q) \land\\(\forall n, p: \operatorname{Nat}(), \operatorname{C}(n, p) \Rightarrow \operatorname{castZMod}(n, m) = \operatorname{castZMod}(p, m)) \land\\(\forall n, p: \operatorname{Nat}(), n < m \land p < m \Rightarrow \operatorname{C}(n, p) \operatorname{iff}() n = p) \land\\\operatorname{Blind}(u).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector.finite_second_derived_orbit_detector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FullKernel(q) means that q(x)=1 implies q(f(x))=1 for every endomorphism f of G and every x. C(n,p) means there is one z in Q with q(tau^n u)=z q(tau^p u) z^-1. Metabelian(F) is the explicit law [[a,b],[c,d]]=1 for all four elements. Blind(u) quantifies over all such groups F, homomorphisms f:G to F, and natural n, and states f(tau^n u)=1.

The witness uses A=I+E12+E23+E34+E56 and B=I+E45+E67 in one-based matrix coordinates. Writing H=[A,B], N=H-I, we have N^3=0. Define P(t,s)=I+tN+sN^2. Its inverse is P(-t,t^2-s), and its multiplication law is P(t,s)P(v,w)=P(t+v,s+w+tv). All formulas are polynomial and valid over any commutative ring, including even characteristic.

For each t, the first three handle images are (P(t,0)AP(t,0)^-1,P(t,0)BP(t,0)^-1), (A,I), (B,A). Remaining handle images are identity. The surface relation holds because P(t,0) commutes with H and [B,A]=H^-1. The exact matrix word calculation gives rho_t(tau^n u)=I-(n+t)E17. This evaluates genuine iterates of the original twist.

To separate times n,p, evaluate a claimed conjugacy at rho_(-p). The time-p image is identity, whose conjugacy class is a singleton. The (1,7) entry forces n=p modulo m. For 0<=n,p<m, this is actual equality. Every metabelian representation instead sends this double commutator to identity.

The source uses all matrix-group representations for the characteristic quotient. Consequently its all-time modular condition is necessary, and is not asserted sufficient. The smaller unitriangular-family exact-period theorem and class-six threshold are recorded only as ordinary mathematical proofs in the existing theory. The word u is not being identified with a simple closed curve. No general curve-orbit CSP result is claimed.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector.finite_second_derived_orbit_detector`
- Dependency: [D5/S3/Observer/Dynamics/SurfaceTwistCongruence](SurfaceTwistCongruence.md)
