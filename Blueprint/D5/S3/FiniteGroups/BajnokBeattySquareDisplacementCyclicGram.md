# The arithmetic covariance is a torsion-subgroup counting Gram

## Abstract

Finite cyclic Gram realization of actual count-threshold fluctuations.

**Theorem 1.1 (One actual family, every finite signed odd parameter set).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCyclicGram.actual_square_displacement_cyclic_gram`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCyclicGram.actual_square_displacement_cyclic_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let Params be all signed integers p with p>=5 and Odd p. The public actual-moment theorem supplies one global threshold family T(p,k), before any finite set or coefficients are chosen. At q_k=2k+3 the two readouts are the actual square quotient counts Wa and Wq, and the theorem retains all five count-crossing clauses, both logarithmic brackets, and uniqueness among all original crossings.

For a finite set S of distinct admissible parameters, put n(p)=p.toNat and L=product_(p in S) n(p), with L=1 when S is empty. Work in the single finite cyclic group G=ZMod L. For every natural d, define H_d as the kernel of d-nsmul on G. Mathlib's IsAddCyclic.card_nsmulAddMonoidHom_ker gives card(H_d)=gcd(L,d); for p in S the divisibility n(p)|L therefore gives card(H_n(p))=n(p). The definition is made for every d, including gcd(p,r) values below 5 that need not be actual parameters.

Define v_p(x,y)=(1/p) times the indicator that x and y lie in H_n(p), using ordinary counting over G^2. The public additive order divisibility criterion gives H_p intersect H_r=H_gcd(p,r). Therefore the product v_p*v_r is supported exactly on the square of that intersection, and the finite counting sum is sum_G^2 v_p*v_r=gcd(p,r)^2/(p*r). There is no normalization by L or L^2. The empty set is vacuous and uses the trivial group ZMod 1.

For coefficients c:S->Real define A_c(k)=sum_p c(p)*(D(T,p,k)-1/2) and V_S(c)=(1/12)*sum_(x,y in G^2)(sum_p c(p)*v_p(x,y))^2. Centering the public mean and mixed-moment limits gives avg A_c -> 0 and avg A_c^2 -> V_S(c). Only fixed finite sums are transported through the limit. Subtracting the square of the empirical mean gives the same limit for the empirical variance.

Nonnegativity is the displayed finite sum of squares. For strictness, choose the numerically largest p0 in the nonzero coefficient support. The element g=(L/n(p0))*1 in ZMod L has exact additive order n(p0), by ZMod.addOrderOf_coe and divisibility cancellation. At (g,0), membership in H_n(r) forces n(p0)|n(r). Any other positive multiple r of p0 is larger than p0 and hence has zero coefficient by maximality, so the feature value is c(p0)/p0. One strictly positive square proves V_S(c)>0. Conversely the zero coefficient family has V=0. This covers arbitrary composites, overlapping divisibility, signs, and the empty S without divisor-closure or prime restrictions.

The Reg source keeps the whole signed family, State=Nat x Nat, and Role=Fin 2 with the actual Wa/Wq readouts. Its crossing law is explicitly bridged in both directions to the full public theorem. Killing Wa contradicts the before-crossing inequality at p=5,k=0,t=2; killing Wq contradicts the after-crossing inequality at T+1. The public actual_counts values at p=5,q=3,t=2 and t=3 witness dependence of each role.

Bajnok and Beatty are the attributed source for the original finite quotient-group counting setting recorded in the repository library note. The repository actual-moment theorem supplies the actual threshold asymptotics used here. Classical positivity of gcd matrices is background (Lindqvist-Seip, 1998, DOI 10.4064/aa-84-2-149-154); this document makes no novelty claim and does not claim that paper proved the actual count-threshold theorem. The construction uses no independence, Gaussianity, infinite-set limit, CLT, generic matrix or probability framework.

Source selection and occurrence binding remain unfinished under https://github.com/the-omega-institute/trureturing/issues/25856.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCyclicGram.actual_square_displacement_cyclic_gram`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments](BajnokBeattySquareDisplacementActualMoments.md)
