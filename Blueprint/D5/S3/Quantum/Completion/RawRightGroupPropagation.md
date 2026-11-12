# Raw comparisons on the entire original magma

## Abstract

For a supplied group of actual labels, common right group tails and independent bidirectional-zero tails preserve every original directed comparison.

M has only its original multiplication and two-sided unit. U:M->M is any total marker, and c:M->M->R is finite-valued. RawCost U c means nonnegativity, zero diagonal, and the original four-variable equality c(a*u,b*v)+c(a*U(u),b*U(v))+c(a*U(U(u)),b*U(U(v)))=3c(a,b)+3c(u,v) for every ordered a,b,u,v in M.

G is an arbitrary actual group of labels, possibly noncommutative. LabelGroup U G consists of an injective inclusion label:G->M, label(1)=1, label(g*k)=label(g)*label(k), a total marker V:G->G with label(V(g))=U(label(g)), and (a*label(g))*label(k)=a*label(g*k) for every original a:M. Thus the image is U-stable, and the group inverse is an actual original label. The action is the original multiplication. No ambient associativity, inverses, cancellation, symmetry, U(1)=1, zero drift, marker multiplicativity, surjectivity, periodicity, return, negative type or Hilbert representation is assumed. Both universes and all degenerate groups and costs remain in scope.

**Theorem 1.1 (Common actual group tails preserve all comparisons).**

$$(\forall M: Type_{u}, (\forall mM: \operatorname{MulOneClass}\left(M\right), (\forall G: Type_{v}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (M \to M), (\forall c: (M \to (M \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall L: \operatorname{LabelGroup}\left(U, G\right), (\forall a: M, (\forall b: M, (\forall g: G, \operatorname{c}\left((a \cdot \operatorname{label}\left(L, g\right)), (b \cdot \operatorname{label}\left(L, g\right))\right) = \operatorname{c}\left(a, b\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawRightGroupPropagation.right_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix arbitrary original a,b. On G put f(s)=c(a*label(s),b*label(s)) and m=inf(range f). This nonempty range is bounded below by zero. Balance and the mixed associativity give f(s*t)+f(s*V(t))+f(s*V(V(t)))=3f(s). Hence f(s*t)<=3f(s)-2m. For a fixed target q and every s use the actual group increment s inverse times q. Then (f(q)+2m)/3 is a lower bound of the whole range, so it is at most m. Together with m<=f(q), this forces f(q)=m. Comparing q with 1 proves the result without an attained minimum or an upper bound.

zeroSubgroup h L consists of all g in G with both c(label(g),1)=0 and c(1,label(g))=0; write Z for this subgroup. The unit uses the diagonal. Product closure uses the single-phase inequality separately in the two directions. Common-tail invariance identifies c(label(g inverse),1) with c(1,label(g)), and the reverse cost with c(label(g),1), giving inverse closure without symmetry. For s,t in Z, unit_compare gives c(label(s),label(t))=0. Closure under the unnormalized marker V is not required.

**Theorem 1.2 (Two zero tails act independently on original backgrounds).**

$$(\forall M: Type_{u}, (\forall mM: \operatorname{MulOneClass}\left(M\right), (\forall G: Type_{v}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (M \to M), (\forall c: (M \to (M \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall L: \operatorname{LabelGroup}\left(U, G\right), (\forall a: M, (\forall b: M, (\forall z: \operatorname{zeroSubgroup}\left(h, L\right), (\forall w: \operatorname{zeroSubgroup}\left(h, L\right), \operatorname{c}\left((a \cdot \operatorname{label}\left(L, z\right)), (b \cdot \operatorname{label}\left(L, w\right))\right) = \operatorname{c}\left(a, b\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawRightGroupPropagation.independent_zero_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set p(n)=V^n(1) and T(n,z)=V^n(z)*p(n) inverse. The actual marker equalities, sync_iter and common-tail invariance show both directed unit costs of T(n,z) vanish. Thus each T(n,z) belongs to the same complete Z, even with nonzero marker drift. On Z times Z put k(s,t)=c(a*label(s),b*label(t)) and mu=inf(range k). Applying balance at the original backgrounds a*label(s),b*label(t), the increment cost is zero. Common-tail invariance removes p(n) from both endpoints, and only mixed right associativity is used to obtain k(s*x,t*y)+k(s*T(1,x),t*T(1,y))+k(s*T(2,x),t*T(2,y))=3k(s,t). The other two terms are at least mu. Choose x=s inverse times z and y=t inverse times w independently; the same lower-bound argument on the full product Z times Z forces k(z,w)=mu=k(1,1). Neither original background is inverted.

For a conditional application, suppose a supplied normalized norm-square representation F_G:G->H on this same group has F_G(1)=0 and c(label(g),label(k))=norm(F_G(g)-F_G(k)) squared for every g,k in this very G. Then c(label(g),1)=norm(F_G(g)) squared=c(1,label(g)), so the exact set equality Z={g:G | F_G(g)=0} follows from norm definiteness. For arbitrary original a,b and independent z,w with F_G(z)=F_G(w)=0, independent_zero_tails therefore gives c(a*label(z),b*label(w))=c(a,b), as in (23.5). The raw propagation theorem applies directly to the bidirectional-zero subgroup; identifying it with a representation kernel uses the supplied F_G.

An alternative model with a nonassociative carrier uses the additive group A=R times R times the integers, G=Multiplicative(A), and M=G times Term(Unit), with the existing unit-normalized ordered binary term product. The label inclusion is g |-> (g,unit). If a=(x,y,n,s), define U(a)=(-x-y+1,x,n+1,s) and c(a,b)=q(x_a-x_b,y_a-y_b), where q(x,y)=x squared+x*y+y squared. Nonnegativity follows from 2q=x squared+y squared+(x+y) squared; the three-phase balance is a polynomial identity. Unit drift c(U(1),1)=1 and nonzero comparisons coexist with the nonassociative term carrier. A source leaf has no right inverse. The distinct integer tails (0,0,1) and (0,0,2) lie in Z, independently change the corresponding original integer coordinates, and satisfy the exact generic theorems even at backgrounds with source-leaf terms. Unlike the tree-visible cost in Example 23.5, this cost ignores its term coordinate. The theorems apply to arbitrary M satisfying their stated hypotheses.

The two results express constancy on actual group-tail orbits of arbitrary original backgrounds, first on G and then on Z times Z. Normalizing each marker iterate by the iterate of 1 keeps the independent zero tails inside Z even with nonzero marker drift. In both arguments, nonnegativity and the three-phase balance force constancy from a lower bound without requiring an attained minimum.

Both identities concern one supplied comparison kernel c at a time. The norm-square application takes a representation on the same G as input; neither its existence nor its affinity is an output. Applying independent_zero_tails to obtain both returns in (23.6) uses p(3) at one endpoint and the unit at the other, so it requires p(3) in Z. The normalized marker iterates used in the proof do not give that membership for p(3) itself, and an action on a visible quotient does not make the normalized marker a homomorphism on G. Full-M Hilbert geometry, effects and physical realization of Omega lie outside these comparison identities. A commutative monoid alone does not supply the group inverses used here. For any supplied affine total geometry with arbitrary drift and any complete finite indexed test on its original carrier M whose event kernels satisfy the full balance and sum to K, the separate three-source reduction starts with the given total kernel K dominating each actual event kernel d_j: 0<=d_j(a,b)<=K(a,b) for every event index j and every ordered pair a,b in M. The reduction preserves domination in the reduced model. The tail identities give equalities within c and supply no bounds between different kernels.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawRightGroupPropagation.independent_zero_tails`
- Truth anchor: `D5/S3/Quantum/Completion/RawRightGroupPropagation.right_invariant`
- Dependency: [D5/S3/Quantum/Completion/RawUnanchoredReplication](RawUnanchoredReplication.md)
