# All-Matter Ghost-Vacuum Square Vanishing

## Abstract

The actual BRST square on arbitrary matter states with the ghost vacuum.

**Theorem 1.1 (The vacuum-sector square at every finite rank).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare.vacuum_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare.vacuum_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be any finite-rank even integral symmetric lattice, let H be any complex matrix indexed by Fin(D.rank), and assume both H times gramComplex(D) equals the identity and gramComplex(D) times H equals the identity. For every u in the original Carrier(D), the original operator Q(D,H) squared sends u tensor over Complex with the ghost vacuum Omega to zero. No rank condition, restriction on the matter state, or nilpotence hypothesis is imposed.

Write M(n) for the original Sugawara mode on matter and c(q) for the original ghost mode, with products acting rightmost first. Fix u and put N=max(1,matterCutoff(D,H,u)), I=[-1,N], and J=[-1,N+1]. Here matterCutoff is minus the Hahn order of the Laurent series underlying sugawaraField(D,H)u, minus two. The coefficient convention is M(n)=sugawaraField(D,H)[[n+1]]. Thus M(r)u=0 for r>N. These intervals depend on u.

In the branch n>=-1, the normal ghost term on Omega is c(-n)L(n)Omega=0 by stress-vacuum annihilation. In the branch n<=-2 it is L(n)c(-n)Omega=0 by c-vacuum annihilation. Therefore Q(u tensor Omega) is the finite sum over n in I of M(n)u tensor c(-n)Omega. The matter row vanishes below -1 because its ghost factor annihilates Omega, and above N by the actual matter cutoff.

The original c-c CAR gives c(a)c(b)Omega=-c(b)c(a)Omega. For the actual pointwise operator V(p), the row c(-m)c(m+p)Omega is supported in [-1,1-p]: below -1 CAR moves the annihilating c(-m) to the right, and above 1-p the rightmost c(m+p) annihilates Omega. Consequently V(-n)(v tensor Omega) is the finite sum over m in [-1,n+1] of (2m-n) times v tensor c(-m)c(m-n)Omega.

Apply the full original relation Q C(p)+C(p) Q=-(1/2)V(p) to v=M(n)u and p=-n. Both inverse-Gram identities are supplied to the original matter Virasoro theorem. For n in I and r>N+1, both M(r)u and M(r+n)u vanish, and r+n>0 excludes the central term. Hence M(r)M(n)u=0. The second matter row is uniformly supported above by N+1, not N. The V row is bounded by n+1<=N+1, so every contributing second index belongs to J. Reordering the two c modes then gives a positive double matter row and the negative one-half V correction.

Linearity and padding the first index from I to J give Q squared on u tensor Omega equal to D(u)-(1/2)T(u), where D(u) is the sum over m,t in J of M(m)M(t)u tensor c(-m)c(-t)Omega, and T(u) is the sum over n in I and m in [-1,n+1] of (2m-n)M(n)u tensor c(-m)c(m-n)Omega. The added first index N+1 has M(N+1)u=0. Exchanging m and t in the finite square and using CAR yields D(u)=(1/2) times the square sum of [M(m),M(t)]u tensor c(-m)c(-t)Omega.

The original matter Virasoro law replaces this commutator by (m-t)M(m+t) plus its rank central scalar. When m,t>=-1 and m+t=0, the only pairs are (-1,1), (0,0), and (1,-1). At each pair m cubed minus m is zero. Thus the central term vanishes pointwise, independently of rank, and D(u) is one-half the square sum of (m-t)M(m+t)u tensor c(-m)c(-t)Omega.

In this square, m+t>N gives zero by the original cutoff. The only pair with m+t<-1 is m=t=-1, whose coefficient m-t is zero. The surviving finite region is in bijection with the triangle n in I, -1<=m<=n+1. The forward map is (m,t) maps to (m+t,m), and its inverse is (n,m) maps to (m,n-m). The triangle inequalities place both inverse indices in J. Under this map, m-t becomes 2m-n and c(-t) becomes c(m-n). The reindexed square is exactly T(u), including both boundary endpoints. Therefore D(u)-(1/2)T(u)=0.

This is a consequence for every original matter vector with the ghost vacuum, including rank zero and arbitrary finite matter superpositions. It does not assert square vanishing on other ghost states. No ghost Virasoro theorem, operator-commutant assumption, or added minus C(0) intercept is used.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare.vacuum_square`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCAction](LatticeBcGhostBrstCAction.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](LatticeSugawaraVirasoro.md)
