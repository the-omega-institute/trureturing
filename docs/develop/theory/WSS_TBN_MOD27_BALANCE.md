# A mod-27 depth balance in the split Lucas tower

## Scope and baseline

Let \(F_n\) and \(L_n\) be the ordinary Fibonacci and Lucas sequences,
\(L_0=2,L_1=1\). For \(j\ge 1\), put
\[
 n_j=3^j,\qquad r_j=3^{j+1},\qquad
 B_j=L_{2n_j}+1=L_{n_j}^{\,2}+3.
\]
The existing TBN.2--TBN.4 development in
\`Problems/wall-sun-sun-golden-unit-lift.md\` proves
\[
 B_{j+1}=B_j^3-3B_j^2+3,\quad B_1=19,
\]
and, for every prime \(p\mid B_j\),
\[
 p\equiv1\pmod{2r_j},\qquad
 v_p(B_j)=h_p,
\]
where \(h_p\) is the original Fibonacci depth
\(v_p(F_{p-(5/p)})\). Thus the exponents below are the actual WSS
depths; no index-multiplier valuation is being counted.

The rank/valuation input is the classical Fibonacci valuation formula
of Lengyel, as recorded in Medina--Rowland, *p-regularity of the
p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53
(2015), Theorem 1.4 (arXiv:0910.2907), together with the split rank
calculation already written as TBN.3. The new statement below is an
elementary 3-adic refinement of TBN.5, not a claim that the cited papers
state this balance.

## Theorem (M27)

Define
\[
 u_j=\frac{B_j-1}{2r_j},\qquad
 b_{p,j}=\frac{p-1}{2r_j}\quad(p\mid B_j).
\]
These are integers. Then
\[
 \boxed{u_j\equiv(-1)^{j+1}\pmod{27}\quad(j\ge1).}
 \tag{M27.1}
\]
For every \(j\ge2\), the actual depth vector in \(B_j\) satisfies
\[
 \boxed{\sum_{p\mid B_j} h_p\,b_{p,j}
       \equiv(-1)^{j+1}\pmod{27}.}
 \tag{M27.2}
\]
For \(j=1\), (M27.2) also holds by the direct identity \(B_1=19\).

In particular, the old mod-3 balance
\(\sum h_p(p-1)/r_j\equiv(-1)^j\pmod3\) is only the first
reduction of (M27.2). Since \(b_{p,j}\) is integral, (M27.2) forces at
least one factor with \(3\nmid h_p b_{p,j}\), but the new content is the
full mod-27 weighted congruence. It neither produces a WSS prime nor
excludes one.

## Proof

The recurrence gives
\[
 B_{j+1}-1=(B_j-1)\bigl((B_j-1)^2-3\bigr).
\]
Writing \(B_j-1=2r_j u_j\) and \(r_{j+1}=3r_j\), we obtain the exact
recurrence
\[
 u_{j+1}
 =u_j\left(-1+\frac{4r_j^2}{3}u_j^2\right)
 =u_j\left(-1+4\cdot3^{\,2j+1}u_j^2\right).
 \tag{M27.3}
\]
Here \(u_1=(19-1)/(18)=1\). The correction term in parentheses is
divisible by \(27\) for every \(j\ge1\). Induction in (M27.3) therefore
proves (M27.1).

Now fix \(j\ge2\). Every prime factor has the form
\(p=1+2r_j b_{p,j}\). Since
\[
 (2r_j)^2=4r_j^2
 \quad\text{is divisible by}\quad 54r_j
 \qquad (j\ge2),
\]
the binomial theorem gives
\[
 p^{h_p}\equiv1+2r_jh_pb_{p,j}\pmod{54r_j}.
\]
All cross terms in the product also contain \((2r_j)^2\), so multiplying
over the distinct prime factors yields
\[
 B_j=\prod_{p\mid B_j}p^{h_p}
 \equiv1+2r_j\sum_{p\mid B_j}h_pb_{p,j}\pmod{54r_j}.
\]
On the other hand, \(B_j=1+2r_ju_j\). Cancelling the common factor
\(2r_j\) in the congruence modulo \(54r_j\) gives
\[
 \sum_{p\mid B_j}h_pb_{p,j}\equiv u_j\pmod{27},
\]
which is (M27.2) by (M27.1). For \(j=1\), \(B_1=19\), \(b_{19,1}=1\),
and \(h_{19}=1\), so both sides are \(1\) modulo \(27\).

## Exact checks

The following factorizations and residue checks use only integer
arithmetic (the factorizations are displayed to make the depth exponents
auditable):
\[
\begin{array}{c|r|l|c|c}
j&r_j&B_j&u_j\bmod27&\sum h_pb_{p,j}\bmod27\\ \hline
1&9&19&1&1\\
2&27&5779=5779&26&26\\
3&81&192900153619=3079\cdot62650261&1&1\\
4&243&7177905237579946589743592924684179
 =59779\cdot120074026624398979403194983601&26&26
\end{array}
\]
All displayed factors are prime, and each is \(1\bmod 2r_j\). The
table checks both the recurrence residue and the depth-weighted product
for the first four blocks; it is not used in the proof.

## Logical boundary

M27 constrains the actual valuation vector in the split Lucas rank
channel. It sharpens TBN.5's mod-3 balance and can be combined with the
existing parity, reciprocity, and class-field constraints. It does not
imply that any \(h_p=1\), and therefore does not imply the existence of a
non-WSS prime or resolve the Wall--Sun--Sun question. The result is
unconditional relative to the TBN.2--TBN.3 rank/valuation identities; no
abc, Pell-height, equidistribution, or Chebotarev hypothesis is used.
