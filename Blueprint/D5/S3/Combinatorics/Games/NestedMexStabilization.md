# Stabilization of Nested Mex Maps

## Abstract

Arbitrary finite compositions of a nested minimum-excluded-value map stabilize after two applications.

Let E1, E2, E3 and K be finite subsets of the natural numbers, each containing zero. For an input x put a=mex(E1 union {x}), v=mex(K union {a}), b=mex(E2 union {a,v}), and M(x)=mex(E3 union {a,b}). A list is composed in application order, with its first entry acting first.

**Theorem 1.1 (Every positive input stabilizes after two compositions).**

$$\forall L \in \operatorname{List}\left(Coefficients\right),\; L \ne [] \Rightarrow \left(\forall x \in Nat,\; 0 < x \Rightarrow \operatorname{run}\left(L, \operatorname{run}\left(L, \operatorname{run}\left(L, x\right)\right)\right) = \operatorname{run}\left(L, \operatorname{run}\left(L, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/NestedMexStabilization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write alpha=mex(E1) and beta=mex(E1 union {alpha}); alpha is positive and beta exceeds alpha. The first mex is beta only at alpha and is alpha elsewhere, so M has at most two values. The two intervening v values either coincide below alpha or are both at least alpha. Their middle sets therefore agree below alpha, as do the final sets. Distinct final values are at least alpha, and only the exceptional value can equal alpha. Consequently, for 0<r<s with distinct outputs, the output minimum is at least r; equality fixes r. This property is preserved through every component, excluding a swap. The resulting map has at most two image values and no positive two-cycle, which gives R cubed equal to R squared.

Tyagi, arXiv:2610.06925v1, equations (1), (2) and (21), uses removals d dividing every other heap. Let A be any nonempty multiset of positive fixed heaps with gcd(A)=4, H at least its maximum, T=2 lcm(1,...,H), and f(n)=g(A+{n}). Assume that every actual nonempty direct fixed follower Q has an eventual T tail for g(Q+{n}). These are all legal fixed moves, including removals that do not divide the selected heap. Beyond a common threshold B at least 5, 2 min(A)+1 and every follower start, the finite fixed-follower coefficient F(n) repeats after T, and f(n)=mex(F(n) union {f(n-1),f(n-2),f(n-4)}). Empty fixed followers contribute singleton values above the parent bound and can be omitted.

Let c count fixed heaps of valuation exactly two, and set z0=0 for even c and z0=4 for odd c. The actual outcome criterion makes precisely the z0 residue modulo eight zero. At a zero anchor z write p=f(z-3), x=f(z-2), q=f(z-1), u=mex{0,p,q}, a=f(z+2), v=f(z+3), b=f(z+4), w=f(z+5), y=f(z+6), t=f(z+7). Then E1=F(z+2) union {0,u}, K={0,u,q}, E2=F(z+4) union {0}, and E3=F(z+6) union {w} give exactly M(x)=y; E3 contains zero by the actual outcome law at z+6. The intervening odd value v is recomputed inside M.

The two actual tails at z0+5 and z0+7 modulo eight remain additional hypotheses. They repeat p,q,w,t and hence the coefficient sets after T. For k=T/8 the actual seeds obey x(j+1)=M(j)(x(j)) with M(j+k)=M(j). The theorem stabilizes the k-step composition. Starting at the first zero anchor z at least max(B,O+3), where O is the start of those two tails, the full T tail follows from z+2T, at most max(B,O+3)+7+2T. This embeds the actual trajectory only: arbitrary seeds can violate the remaining odd equations for w or t. Neither the two residue tails nor equation (21) is proved here.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/NestedMexStabilization.result`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](../../../S0/Certificates/Games/CrimGrundyRefutation.md)
