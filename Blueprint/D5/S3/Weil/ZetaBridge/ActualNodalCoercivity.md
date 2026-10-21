# Actual nodal polynomials and finite reconstruction

## Abstract

Exact actual arithmetic nodal representation and uniform coefficient reconstruction.

**Definition 1.1 (The common nodal denominator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.D`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set S of integers, D(S) is the complex polynomial Lagrange.nodal S (fun n => (n : Complex)). In the pinned library this is exactly the product over n in S of X-C(n : Complex), with empty product one. The namespace is Lagrange, not Polynomial.Lagrange.

**Definition 1.2 (The unnormalised head numerator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.Q`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite integer set S and every function v : Int -> Complex, Q(S,v) is the sum over n in S of C(v(n)) times Lagrange.nodal (S.erase n) (fun j => (j : Complex)). There is no normalization by nodal weights. At a node n in S, its value is v(n) times Delta_n, where Delta_n is the product over j in S.erase n of ((n : Complex)-(j : Complex)).

**Definition 1.3 (The actual boundary-symbol numerator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.P`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural c, finite integer set S and complex function v, P(c,S,v) is the sum over n in S of C((WeilArithmeticCouplingJet.arithmeticBoundarySymbol c n : Complex)*v(n)) times Lagrange.nodal (S.erase n) (fun j => (j : Complex)). This retains the actual boundary symbol, including its full pole, Gamma-series and prime terms. No substitute symbol or substitute coupling is introduced.

**Theorem 1.4 (The exact nodal model of every exterior arithmetic column).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.actual_nodal_polynomial_model`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.actual_nodal_polynomial_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full telescope: c : Nat, S : Finset Int, hS : S.Nonempty, v : Int -> Complex. Conclusion: natDegree(P(c,S,v)) < card(S), natDegree(Q(S,v)) < card(S), and for every integer m outside S, (pi : Complex)*D(S).eval(m : Complex)*WeilArithmeticCouplingJet.couplingColumn c S v m = P(c,S,v).eval(m : Complex) - (arithmeticBoundarySymbol c m : Complex)*Q(S,v).eval(m : Complex). All natural c are allowed, including zero and one; there is no hypothesis c>=2.

The column is precisely the sum over n in S of the complex cast of the real quotient (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). The proof clears that real quotient after casting; Real.pi_ne_zero supplies the nonzero pi factor. The pinned Lagrange nodal evaluation theorem proves D(S).eval(m) is nonzero outside S. Its erased-factor identity and natDegree theorem give the consumed private denominator and degree steps.

Attribution: this is the classical common-denominator form of unnormalised Lagrange interpolation, applied to the repository's actual arithmetic divided difference. It makes no novelty claim.

**Theorem 1.5 (Reconstruction at a retained node).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.numerator_eval_node`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.numerator_eval_node` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integer set S, complex coefficient function v, and n in S, Q(S,v).eval(n : Complex) equals v(n) times the evaluation at n of the nodal polynomial on S.erase(n). All other terms vanish at that retained node; the erased product is nonzero because the integer nodes are distinct. This reconstructs the original retained coefficient and places no condition on the arithmetic symbol.

**Theorem 1.6 (An explicit coefficient bound uniform in the vector and the scale).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.uniform_coefficient_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.uniform_coefficient_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full telescope, in order: S : Finset Int; A : Nat; hS : S.Nonempty; hA : 1<=A; hbound : for every n in S, n.natAbs<=A; c : Nat; v : Int -> Complex; N : Nat; hN : 0<N. Conclusion: (1/((card(S) : Real)^2*(A : Real)^(2*(card(S)-1))))*(sum over n in S of norm(v(n))^2) <= sum over r in range(card(S)) of (N : Real)^(2*r)*(norm(P(c,S,v).coeff(r))^2+norm(Q(S,v).coeff(r))^2). The constant depends only on S and A, which, together with their hypotheses, precede every vector and scale. There is no nonzero-vector assumption, and a singleton S is included.

The private reconstruction_denominator_pos proves the denominator strictly positive from card(S)>0 and A>=1 and is consumed when dividing the raw reconstruction inequality. The node formula Q(n)=v(n)*Delta_n and integer separation give norm(Delta_n)>=1, including the empty erased product at a singleton. The coefficient expansion below card(S), triangle inequality and the pinned finite sum_mul_sq_le_sq_mul_sq Cauchy-Schwarz inequality give norm(Q(n))^2 <= card(S)*A^(2*(card(S)-1))*sum over r<card(S) of norm(Q.coeff(r))^2. Summation over card(S) nodes yields the square of card(S) in the denominator. Since N>=1, every scale weight is at least one; the nonnegative P coefficient squares can then be added.

Attribution: standard integer-node Lagrange reconstruction and finite Cauchy-Schwarz, reusing the mature Mathlib nodal and finite-sum inequalities. No compactness argument, per-vector constant, assumed inverse bound or novelty claim is used. These two finite results are ingredients for future work; no uniform paired-tail theorem of exponent 2*card(S)-1, physical Weil positivity, Robin5040 statement or RH conclusion is asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.D`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.P`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.Q`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.actual_nodal_polynomial_model`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.numerator_eval_node`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualNodalCoercivity.uniform_coefficient_reconstruction`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
