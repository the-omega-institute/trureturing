# Conditional minimal all-WSS cross-factor restriction modulo 25

## Scope

This is a paper-first conditional corollary for the fixed-golden blocks
\[
 B_j=L_{2\cdot3^j}+1=\prod_{p\mid B_j}p^{h_p},\qquad
 R_j=\begin{cases}4,&j\text{ odd},\\1,&j\text{ even},\end{cases}
\]
where \(h_p=v_p(F_{p-(5/p)})\) is the original Fibonacci depth. It does
not assert that the hypothesis below occurs, and it does not prove or disprove
the existence of Wall--Sun--Sun primes.

The inputs are the existing DCE.4--DCE.5 statements in
[Problems/wall-sun-sun-golden-unit-lift.md](https://github.com/the-omega-institute/trureturing/blob/dev/Problems/wall-sun-sun-golden-unit-lift.md)
and Theorem FQ5 in
[WSS_TBN_MOD27_BALANCE.md](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/WSS_TBN_MOD27_BALANCE.md).

## Theorem

Assume that every prime divisor of \(B_j\) is WSS, equivalently \(h_p\ge2\),
and that
\[
\Omega(B_j)=\sum_{p\mid B_j}h_p=5.
\]
Then there are distinct primes \(P,Q\) such that
\[
 B_j=P^2Q^3,
 \qquad h_P=2,
 \qquad h_Q=3,
\]
and DCE.5 gives
\[
 Q\equiv19\pmod {40},
 \qquad
 P\equiv1+2(-1)^jr_j\pmod {6r_j},
 \qquad r_j=3^{j+1}.
\]
Moreover, with
\[
 \lambda_5(x)=\frac{x^4-1}{5}\pmod5
 \quad (5\nmid x),
\]
we have
\[
 2\lambda_5(P)+3\lambda_5(Q)\equiv R_j\pmod5.
\]
Equivalently,
\[
 \lambda_5(P)-\lambda_5(Q)
 \equiv
 \begin{cases}
 2\pmod5,&j\text{ odd},\\
 3\pmod5,&j\text{ even}.
 \end{cases}
\]
Thus the ratio \(P Q^{-1}\pmod {25}\) is restricted to
\[
 P Q^{-1}\equiv
 \begin{cases}
 9,12,13,16\pmod {25},&j\text{ odd},\\
 2,11,14,23\pmod {25},&j\text{ even}.
 \end{cases}
\]

## Proof

DCE.4 says that an all-WSS block has \(\Omega(B_j)\ge5\), and when equality
holds its only possible exponent vector is \((2,3)\) on two distinct factors.
DCE.5 assigns the depth-two factor the name \(P\), the depth-three factor the
name \(Q\), and supplies the displayed congruences modulo \(40\), \(6r_j\),
and the exact ternary valuation.

FQ5 states
\[
 \sum_{p\mid B_j}h_p\lambda_5(p)\equiv R_j\pmod5.
\]
Substituting \(B_j=P^2Q^3\), \(h_P=2\), and \(h_Q=3\) gives
\[
 2\lambda_5(P)+3\lambda_5(Q)\equiv R_j\pmod5.
\]
Because \(3\equiv-2\pmod5\), multiplication by \(2^{-1}=3\) yields
\[
 \lambda_5(P)-\lambda_5(Q)\equiv3R_j\pmod5,
\]
which is \(2\) for odd \(j\) and \(3\) for even \(j\).

The Fermat quotient is additive on products and inverses modulo \(25\):
\(\lambda_5(xy^{-1})=\lambda_5(x)-\lambda_5(y)\). Direct enumeration of the
units modulo \(25\) gives the five fibers
\[
\begin{array}{c|l}
\lambda_5(x)&x\pmod {25}\\\hline
0&1,7,18,24\\
1&3,4,21,22\\
2&9,12,13,16\\
3&2,11,14,23\\
4&6,8,17,19.
\end{array}
\]
The two asserted ratio sets are therefore the fibers for values \(2\) and
\(3\), respectively. \(\square\)

## Boundary and finite audit

The theorem is conditional on the minimal all-WSS branch and is vacuous when
that branch does not occur. The exact audited blocks \(B_1,\ldots,B_5\) in FQ5
are squarefree, so \(h_p=1\) for every displayed factor and their zero sets
\(\{p\mid B_j:q_p=0\}\) are empty; no universal nonempty-zero-set claim is made.
The result only narrows a still-possible heterogeneous \((2,3)\) branch.

No Lean or Scribe declaration is added. Formalizing it would require the
existing block-depth API (currently absent) or a paper-first ingestion only.
