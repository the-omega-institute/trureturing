# Metallic Hankel Residue Polynomials

## Abstract

Every higher shifted metallic Hankel sequence has the stated residue polynomial laws from the first term.

**Theorem 1.1 (All shifts, all residues, and integer values on all integers).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-pedon-metallic-hankel-quasipolynomial` (proved) by `D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-pedon-metallic-hankel-quasipolynomial","declaration_gid":"D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2026). *Hankel determinants for the (n+2)-shifted q-metallic numbers*. DOI: [10.48550/arXiv.2610.36132](https://doi.org/10.48550/arXiv.2610.36132). URL: <https://arxiv.org/abs/2610.36132v1>.

*Commentary.*

For every n>=1, a metallic series Phi in Z[[q]] exists: its constant coefficient is 1 and q Phi^2+((1+q^n)(1-q)-q[n]_q)Phi=1. For every series satisfying this equation and every shift ell>=n+3, let rho=2n(n+1) when n is even and rho=4n(n+1) when n is odd. There is a family Q_r in Q[X], indexed by 0<=r<rho, such that Delta_(r+m rho)^(ell)=Q_r(m) for every natural m, including m=0. Each Q_r takes integer values at every integer, including negative integers. The determinant of size zero is 1.

Use the unchanged witnesses L,k,b,D,Q,s and Phi of normal_family. Write nu=1 for even n and 2 for odd n, p(K)=(K nu)L, c_K=reverseAt(s(p(K)),Q(p(K))) and d_K=reverseAt(s(p(K)-1),Q(p(K)-1)). At every K>=1, the enclosing size is N=K rho, s(p(K))=N, and the enclosing Hankel determinant at base n+1 is 1. The exact predecessor support increment is n+1. The common-degree reversals of c_K,d_K are therefore Q(p(K)) and X^(n+1)Q(p(K)-1), including all zero coefficients outside the supports.

Fix a=ell-(n+1)>=2 and a residue r. Set K0=a+1, t=K0 rho-r and u=t-a. These are fixed natural coordinates with t>=a. For every m>=0, K=K0+m and j=r+m rho satisfy K rho=j+t=j+(a+u)>0. The actual shifted_hankel_boundary formula expresses Delta_j^(ell) as (-1)^(a j) times a determinant of size t, with entries built from low c_K,d_K coefficients and their common-degree reversals. No target or neighboring minor is required to be invertible.

Every depth in this fixed matrix is strictly below 2t, and t<=K rho. Consequently all high jets obey the strict condition h<2K rho even for the first m=0, including the empty target r=0,m=0. Apply continuant_endpoint_jets at each actual depth: the low terms use P0,P1 and the common high terms use P2,P3. The guards in the low rows and all natural subtractions are retained. Replacing these coefficients gives one finite matrix over Q[X]. Evaluation commutes with its determinant, and composition with K0+X yields a polynomial in m.

The period rho is even, so (-1)^(a(r+m rho))=(-1)^(a r). Multiplying by this constant sign gives the required Q_r at every natural input. Its values at all natural inputs are integers because they are the original integer Hankel determinants. BackwardPropagation.eval_int_mem_of_eval_nat_mem, applied to the additive subgroup of Q that is the image of Z, then gives integer values at every integer. Existence and uniqueness from normal_family transfer the construction to every satisfying metallic series.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result`
- Dependency: [D5/S3/Arith/PolynomialValues/BackwardPropagation](../../Arith/PolynomialValues/BackwardPropagation.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor](MetallicHankelComplementaryMinor.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets](MetallicHankelEndpointJets.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs](MetallicHankelQuasipolynomialDefs.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded](MetallicHankelUnbounded.md)
