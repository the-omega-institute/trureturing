# Total Stress Covariance With Anomaly

## Abstract

The full total-stress anomaly of the original normally ordered BRST charge.

**Theorem 1.1 (The rank-minus-26 anomaly on the full tensor carrier).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance.total_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance.total_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be any original finite-rank LatticeData, let H be any complex matrix on Fin(D.rank), and assume both H gramComplex(D)=1 and gramComplex(D) H=1. Put T(m)=M(D,H,m)+G(D,m), with M and G the original matter and ghost stress operators. For every integer m, Q(D,H) T(m)-T(m) Q(D,H) equals minus ((D.rank-26)/12)(m cubed-m) times C(D,m), as an equality of complex-linear endomorphisms of Carrier(D) tensor Fock(Complex). All original tensor states, not only ghost-vacuum states, are in scope.

Products act rightmost first. The actual charge is the statewise finite sum of A(n)=C(-n)M(n)+(1/2)N(n). Its outer normal ordering is N(n)=C(-n)G(n) for n>=-1 and N(n)=G(n)C(-n) for n<-1. The unordered family C(-n)G(n) cannot replace these two branches. The commutator is calculated first with T(m) on the left; this fixes the final sign when the order is reversed.

Write b(g)=sup occupied(g), the original ghost support bound, and r(u)=matterCutoff(D,H,u). The shifted matter family R(m,n)=C(-n)M(m+n) on u tensor g is supported in [-b(g)-2,r(u)-m]. The shifted normally ordered ghost family U(m,n), ordered by n>=-1, has support in [-b(g)-2,max(-1,2b(g)+4-m)]. The differentiated first family E(m,n), equal to C(m-n)G(n) for n>=-1 and G(n)C(m-n) otherwise, has support in [min(-1,m-b(g)-2),max(-1,2b(g)+4)]. In the low branch of E the rightmost c already annihilates g; in its high branch the rightmost stress mode already annihilates g. Thus no unlicensed high-stress estimate on a c-modified state is used. Finite support extends to every tensor state by tensor induction. Scalar weighting and integer translations preserve these licenses.

The actual matter Virasoro law, using both inverse-Gram identities, gives the differentiated matter rows with weights n-2m and m-n. Translation of the first index cancels the noncentral rows exactly. The remaining delta term is (D.rank/12)(m cubed-m) C(m). Matter and ghost tensor factors commute by their actual tensor maps, rather than by an extra hypothesis.

The original full ghost Virasoro relation has central coefficient obtained by dividing -13(m cubed-m) by six as an integer before casting. Six divides m cubed-m because six divides the product of the three consecutive integers m-1,m,m+1. Hence over Complex this coefficient is -(13/6)(m cubed-m). Its contribution through the one-half N term is -(13/12)(m cubed-m) C(m).

After translating the first ghost row by n maps to n+m, its branch is decided by n+m>=-1, whereas the second row uses n>=-1. The actual relation [G(m+n),C(-n)]=-(2m+n) C(m) therefore leaves a finite correction. For m>=0 its scalar summand is (n-m)(2m+n) on [-m-1,-2]; for m<0 it is the negative of that polynomial on [-1,-m-2]. Outside this window the two orders agree and their opposite weights cancel. The endpoints and the inverse translations are included in the finite reindexing.

For F(m,n)=n(n-1)(2n-1)/6+m n(n-1)/2-2m squared n, F(m,n+1)-F(m,n)=(n-m)(2m+n). Both signed windows telescope to F(m,-1)-F(m,-m-1)=-(13/6)(m cubed-m). After the outer factor one-half this supplies a second -(13/12)(m cubed-m) C(m). Together the matter term, ghost central term and ordering correction give ((D.rank-26)/12)(m cubed-m) C(m) in [T(m),Q]. Reversing the commutator gives the stated negative anomaly.

Every finite-sum exchange uses the actual statewise support just described, or the original finite A family before and after applying T(m). The equality holds on the whole algebraic tensor carrier by linear extensionality. It asserts no nilpotence of Q on arbitrary ghost states and no completion of the full VOA, string or AdS problem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance.total_covariance`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge](LatticeBcGhostBrstCharge.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](LatticeSugawaraVirasoro.md)
