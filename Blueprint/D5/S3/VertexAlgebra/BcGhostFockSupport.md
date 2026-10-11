# Infinite bc Fock states and normal ordering

## Abstract

Signed finite-subset ghost operators admit statewise finite normal ordering on an infinite algebraic Fock space.

Let K be any commutative ring and let F be the free K-module on all finite subsets of the natural numbers. A state is a finite superposition of these subsets; there is no global bound on the available sites. The vacuum is the basis vector of the empty subset. At site i, insertion vanishes when i is present, while deletion vanishes when i is absent. Both nonzero actions carry the sign (-1) raised to the number of occupied sites smaller than i.

For m <= -2, b_m inserts the even site 2(-m-2); otherwise it deletes the odd site 2(m+1)+1. For n <= 1, c_n inserts the odd site 2(1-n)+1; otherwise it deletes the even site 2(n-2). The normal-ordered pair N(p,q) is b_p composed with c_q for p <= -2, and minus c_q composed with b_p otherwise. Products act on the rightmost state first.

These are the untwisted weight-(2,-1) mode conventions associated with lambda=-1 in Eholzer, Feher and Honecker, Ghost Systems: A Vertex Algebra Point of View, Section 2. Relative to their mathematical modes in (2.7)-(2.10), b_m is b at index m+1 and c_n is c at index n-2. The b-mode split at mathematical index zero becomes p <= -2, and the c-mode split becomes n <= 1. After the paper's fermionic reordering, the coefficient in (2.15) becomes m-k. This is a comparison of conventions, not a proved equality with the paper's stress tensor. The present assertions concern the concrete operators and their support and generation; they do not assert canonical anticommutation relations, the Virasoro relation, a vertex algebra or a BRST complex.

**Theorem 1.1 (An unoccupied site annihilates the whole superposition).**

$$\forall K:\operatorname{Type}\left(\right),[\operatorname{CommRing}\left(K\right)],\ \forall v\in F,i\in \mathbb{N},\ \neg(i\in \operatorname{occupied}\left(v\right)) \Rightarrow \operatorname{annihilate}\left(i, v\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockSupport.annihilate_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied set is the union of all finite subsets in the Finsupp support of v. If i is outside this union, deletion at i vanishes on each basis state appearing with nonzero coefficient, and linear extension gives zero on the entire state. The supremum-tail lemma uses this statement directly; through that lemma it also supplies both tails of the normal-ordering interval. It is available directly for statewise b- and c-annihilator bounds.

**Theorem 1.2 (Deletion above every occupied site vanishes).**

$$\forall K:\operatorname{Type}\left(\right),[\operatorname{CommRing}\left(K\right)],\ \forall v\in F,i\in \mathbb{N},\ \operatorname{sup}\left(\operatorname{occupied}\left(v\right), id\right)< i \Rightarrow \operatorname{annihilate}\left(i, v\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockSupport.annihilate_eq_zero_of_sup_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supremum is taken in the natural numbers using id, and is zero for the empty occupied set. Every occupied site is at most this supremum, so a strictly larger site is absent and the preceding deletion lemma applies. Both the lower c-tail and the upper b-tail in normal_pair_support_interval consume this bound. Applied to a shifted state, it bounds the corresponding row without requiring one global cutoff for all Fock states.

**Theorem 1.3 (A state determines a finite normal-ordering interval).**

$$\forall K:\operatorname{Type}\left(\right),[\operatorname{CommRing}\left(K\right)],\ \forall m\in \mathbb{Z},v\in F,\ \operatorname{supp}\left(k\mapsto\operatorname{N}\left(m+k, -k, v\right)\right) \subseteq [-\operatorname{cutoff}\left(m, v\right),\operatorname{cutoff}\left(m, v\right)]$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockSupport.normal_pair_support_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M(v) be the largest occupied site among all subsets in the support of v, with value zero for the empty union. The bound is cutoff(m,v)=M(v)+|m|+4. For a sufficiently negative k, the rightmost c-mode deletes an even site above M(v). For a sufficiently positive k, normal ordering puts a b-annihilator at an odd site above M(v) on the right. Both tails therefore vanish on the given state. Finite support is established separately for each input, and is not assumed of the operator-valued family.

**Theorem 1.4 (The linear stress-tensor candidate has an interval formula).**

$$\forall K:\operatorname{Type}\left(\right),[\operatorname{CommRing}\left(K\right)],\ \forall m,a,z\in \mathbb{Z},v\in F,\ a\leq -\operatorname{cutoff}\left(m, v\right) \land \operatorname{cutoff}\left(m, v\right)\leq z \Rightarrow \operatorname{L}\left(m, v\right)=\sum_{k=a}^{z}(m-k)\operatorname{N}\left(m+k, -k, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockSupport.L_interval_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L_m(v) is the pointwise finite sum of (m-k)N(m+k,-k)v. The scalar is the integer m-k mapped into K. Additivity follows by combining the two finite input supports, and scalar compatibility follows from the finite-sum scalar identity. Every closed integer interval [a,z] enclosing the explicit bound [-cutoff(m,v),cutoff(m,v)] computes exactly the same action. The hypotheses are a <= -cutoff(m,v) and cutoff(m,v) <= z; enclosing only the actual support is not this theorem's premise.

**Theorem 1.5 (Creation modes generate all finite superpositions).**

$$\forall K:\operatorname{Type}\left(\right),[\operatorname{CommRing}\left(K\right)],\ \forall W\in \operatorname{Submodule}\left(K, F\right),\ vacuum\in W \land (\forall m\in \mathbb{Z}, m\leq -2 \Rightarrow \forall v\in W,\operatorname{b}\left(m, v\right)\in W) \land (\forall n\in \mathbb{Z}, n\leq 1 \Rightarrow \forall v\in W,\operatorname{c}\left(n, v\right)\in W) \Rightarrow W=\operatorname{top}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockSupport.creation_cyclic` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

Every even insertion is a b-creation mode and every odd insertion is a c-creation mode. Induction on a finite subset constructs its basis vector from the vacuum. The insertion coefficient is a sign whose square is one, so it can be removed over any commutative ring, including characteristic two. Linear induction then generates every finite superposition. The classical Fock basis is described in Section 2, equations (2.9)-(2.10), of the cited paper.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockSupport.L_interval_sum`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockSupport.annihilate_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockSupport.annihilate_eq_zero_of_sup_lt`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockSupport.creation_cyclic`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockSupport.normal_pair_support_interval`
