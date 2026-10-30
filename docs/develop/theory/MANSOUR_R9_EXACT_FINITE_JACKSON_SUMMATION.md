# Exact finite-Jackson summation with a two-tail limit

This note records the complete finite-to-infinite summation argument used by the
Mansour R9 consumer.  Its problem anchor is [Callan--Mansour,
*Inversion Sequences Avoiding Quadruple Length-3 Patterns*](../../../Library/Combinatorics/callan2023inversion.md),
DOI [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694), whose Class 207
is the combinatorial context.  The quantitative array estimate below is the
repository-derived part; the finite Jackson supplier and the classical target
are cited dependencies.

## 1. Definitions and the exact target

For an integer \(k\geq0\), put
\[
 (z;q)_k=\prod_{i=0}^{k-1}(1-zq^i),\qquad (z;q)_0=1,
\]
and use tuple notation for products with multiplicity.  The symbol
\((z)_k\) means \((z;q)_k\) after \(q\) is fixed.  An infinite product
\((z)_\infty\) is the limit of these finite products; its existence and all
nonvanishing needed below are proved in §4.  Integer powers of the real number
\(q\) are ordinary real powers, so negative exponents introduce no branch.

Fix independent real parameters
\[
 0<q<1,\qquad -1<r<0,
\]
and define
\[
 \delta_q=\tfrac14\min(1-q,q^{-1}-1,1),
 \qquad \Omega_q=\{s\in\mathbb C:0<|s-1|<\delta_q\}.
\]
Every assertion in §§2--8 holds for every \(s\in\Omega_q\).  For the
uniform statements, fix an arbitrary nonempty compact \(K\subset\Omega_q\);
a singleton gives the pointwise statement required by the consumer.  No
algebraic relation between \(q\) and \(r\) is imposed.

Set
\[
 a=b=qr,\qquad c=q^2r,\qquad e=q^3rs,\qquad f=q^2r^2/s.
\]
Then \(e f=a b c q\), and the two series and multipliers are
\[
 \Phi(a,b,c;e,f)=\sum_{k\ge0}\frac{(a,b,c)_kq^k}{(q,e,f)_k},
\]
\[
 \Phi'(s)=\Phi(aq/e,bq/e,cq/e;q^2/e,qf/e),
\]
\[
 A=\frac{(q/e,a,b,c,qf/e)_\infty}
          {(e/q,aq/e,bq/e,cq/e,f)_\infty},\qquad
 B=\frac{(q/e,f/a,f/b,f/c)_\infty}
          {(aq/e,bq/e,cq/e,f)_\infty}.
\]
The parameter substitutions used below are, explicitly,
\[
\begin{gathered}
 q/e=1/(q^2rs),\quad e/q=q^2rs,\quad
 aq/e=bq/e=1/(qs),\quad cq/e=1/s,\\
 q^2/e=1/(qrs),\quad qf/e=r/s^2,\quad
 f/a=f/b=qr/s,\quad f/c=r/s,\\
 eq^{-n}/a=eq^{-n}/b=q^{2-n}s,\quad
 eq^{-n}/c=q^{1-n}s,\quad e/f=qs^2/r.
\end{gathered}\tag{0}
\]
Writing \(t=1/s\), the second series has uppers
\((t/q,t/q,t)\), lowers \((t/(qr),rt^2)\), and argument \(q\).  This is only
a change of notation and is not a limit as \(s\to1\).
The theorem proved below is
\[
 \boxed{\;\Phi(a,b,c;e,f)+A\Phi'(s)=B.\;}\tag{1}
\]

## 2. Finite supplier and specialization

We use the terminating rational Jackson identity in the following form.  For
\(n\ge0\), a principal parameter \(\mu\), and free parameters
\(\alpha,\beta,\gamma,\xi\) satisfying
\(\alpha\beta\gamma\xi=\mu^2q^{n+1}\), and with all displayed finite
denominators nonzero,
\[
\begin{aligned}
 &\sum_{k=0}^{n}
 \frac{1-\mu q^{2k}}{1-\mu}
 \frac{(\mu,\alpha,\beta,\gamma,\xi,q^{-n})_kq^k}
 {(q,\mu q/\alpha,\mu q/\beta,\mu q/\gamma,
       \mu q/\xi,\mu q^{n+1})_k}\\
 &\hspace{25mm}=
 \frac{(\mu q,\mu q/(\alpha\beta),\mu q/(\alpha\gamma),
          \mu q/(\beta\gamma))_n}
 {(\mu q/\alpha,\mu q/\beta,\mu q/\gamma,
          \mu q/(\alpha\beta\gamma))_n}.
\end{aligned}\tag{2}
\]
The square-root factors in the printed very-well-poised version have already
cancelled to the rational factor in (2), so no square-root branch is used.

The accepted finite dependency chain is Gasper, *Lectures on q-Series*,
(3.5.1), (4.1.3)--(4.1.8), (4.2.1)--(4.2.9): terminating
q-Pfaff--Saalschutz gives (3.5.1); the finite difference factorization and its
finite \(b\)-limit give (4.1.3)--(4.1.8); the expansions give (4.2.1)--(4.2.4),
then (4.2.6), Watson (4.2.8), and finally terminating Jackson (4.2.9).  This
is a finite rational supplier.  No integral exercise or nonterminating formula
from that source is used as a premise.

For (2), specialize
\[
 \mu_n=eq^{-n-1},\qquad
 (\alpha,\beta,\gamma,\xi)=(a,b,c,x_n),
 \qquad x_n=eq^{-n}/f.
\]
The balance is \(abcx_n=e^2q^{-n-1}=\mu_n^2q^{n+1}\), while
\(\mu_nq/x_n=f\), \(\mu_nq^{n+1}=e\), and
\(\mu_nq/a=eq^{-n}/a\) (likewise for \(b,c\)).  The balanced argument in
the source is \(q\).  Thus for \(0\le k\le n\), the finite summand is exactly
\[
 U_{n,k}=\frac{1-eq^{2k-n-1}}{1-eq^{-n-1}}
 \frac{(eq^{-n-1},a,b,c,eq^{-n}/f,q^{-n})_kq^k}
 {(q,eq^{-n}/a,eq^{-n}/b,eq^{-n}/c,f,e)_k}.\tag{3}
\]
The unsimplified finite right side is
\[
 \frac{(eq^{-n},eq^{-n}/(ab),eq^{-n}/(ac),eq^{-n}/(bc))_n}
 {(eq^{-n}/a,eq^{-n}/b,eq^{-n}/c,eq^{-n}/(abc))_n}.
\]
For \(z\ne0\), finite reversal gives
\[
 (zq^{-n})_n=(-z)^nq^{-n(n+1)/2}(q/z)_n.
\]
The four scalar factors from the numerator and denominator cancel, and the
reversed products are
\[
 (q/e,abq/e,acq/e,bcq/e)_n=(q/e,f/c,f/b,f/a)_n,
\]
\[
 (aq/e,bq/e,cq/e,abcq/e)_n=(aq/e,bq/e,cq/e,f)_n.
\]
Consequently
\[
 \sum_{k=0}^{n}U_{n,k}=B_n:=
 \frac{(q/e,f/a,f/b,f/c)_n}{(aq/e,bq/e,cq/e,f)_n}.\tag{4}
\]
For \(n=0\), both sides are 1.  The finite identity is rational after clearing
denominators, so the specialization only requires the final displayed finite
denominators to be nonzero; auxiliary exclusions in a derivation of (2) do
not add a condition here.

## 3. The full deleted corridor is pole-free

The choice of \(\delta_q\) gives
\[
 \Re(s)>3/4,\quad |\Im(s)|<1/4,\quad q<|s|<q^{-1},
\]
and \(s\notin q^{\mathbb Z}\).  The last assertion follows because the only
integral power of \(q\) strictly between \(q\) and \(q^{-1}\) is the deleted
value 1.  Also
\[
 \Re(s^2)=(\Re s)^2-(\Im s)^2>1/2,
\]
so \(1/s\) and \(1/s^2\) have positive real part.  Since \(r<0\), each of
\[
 a,b,c,e,e/q,q/e,q^2/e,qf/e,f/a,f/b,f/c
\]
has negative real part; explicitly
\[
 q^2/e=1/(qrs),\quad qf/e=r/s^2,\quad f/a=f/b=qr/s,\quad f/c=r/s.
\]
Therefore every factor \(1-vq^t\), \(t\ge0\), for these parameters is
nonzero (its real part is \(>1\)).  Moreover
\[
 |e|=q^3|r||s|<q^2|r|<1,\qquad
 |f|=q^2r^2/|s|<qr^2<1,
\]
so the first series denominators \((q,e,f)_k\) are nonzero.

A moving lower factor \(q^{2-n}s\) or \(q^{1-n}s\) can vanish only when
\(s\in q^{\mathbb Z}\), already excluded.  On the unreversed finite right side,
the fourth moving lower parameter is \(eq^{-n}/(abc)=q^{1-n}/f\); at index
\(0\le i<n\), a zero would require \(f=q^{1-n+i}\), whose modulus is at
least 1, contradicting \(|f|<1\).  The corresponding product is empty at
\(n=0\).  The reversed lower parameters \(aq/e=bq/e=1/(qs)\) and
\(cq/e=1/s\) have zeros only for \(s=q^{t-1}\) or \(s=q^t\).  They are
bounded away from zero on each compact \(K\), although no bound uniform over
the entire punctured disk is asserted.

The second series has lower parameters \(q,q^2/e,qf/e\), all covered by the
same sign argument.  The numerator products used below to divide by
\(U_{n,n}\) have parameters \(a,b,c,q^2/e,qf/e\) and hence no zero factors;
the scalar factors \(1-eq^{n-1}\) and \(1-q^{n+1}/e\) are also nonzero.  In
particular \(U_{n,n}\ne0\), including \(n=0\).  Finally, for \(x\ge0\),
\[
 |1-x/e|^2=1-2x\Re(1/e)+x^2/|e|^2\ge1,
\]
so \(|1-q^{n+1}/e|\ge1\) uniformly in \(n\) and \(s\in K\).

## 4. Uniform moving-product lemma

Let \(v:K\to\mathbb C\) be continuous and set
\(R_v=\max_{s\in K}|v(s)|\).  If every factor required as a denominator is
nonzero, choose \(N_v\) with
\[
 R_vq^{N_v}/(1-q)\le1/2.
\]
For \(0\le t<N_v\), let
\[
 d_{v,t}=\min\bigl(1,\min_{s\in K}|1-v(s)q^t|\bigr),\qquad
 \ell_v=\tfrac12\prod_{t=0}^{N_v-1}d_{v,t}>0.
\]
For every offset \(d\ge0\), length \(k\ge0\), and \(s\in K\),
\[
 \ell_v\le |(vq^d)_k|\le \exp(R_v/(1-q)).\tag{5}
\]
The upper bound follows from \(|1-vq^t|\le e^{R_vq^t}\).  For the lower
bound, the early factors contribute the finite product of the \(d_{v,t}\); on
the remaining indices \(x_t=R_vq^t\le1/2\), and
\[
 \prod(1-x_t)\ge1-\sum x_t\ge1/2.
\]
The inequality is proved by induction from
\(1-P(1-x)=(1-P)+Px\le\sum x\).

Expanding a finite product into subsets also gives the tail estimate
\[
 \left|(vq^d)_k-1\right|
 \le \exp(R_vq^d/(1-q))-1,\tag{6}
\]
uniformly in \(s\) and \(k\), and this tends to 0 with \(d\).  Writing
\(P_N=(v)_N\), we have
\[
 P_{N+L}-P_N=P_N\bigl((vq^N)_L-1\bigr).
\]
Equations (5)--(6) make \(P_N\) uniformly Cauchy on \(K\), so
\((v)_\infty\) exists uniformly and continuously.  If all factors are nonzero,
(5) gives \(|(v)_\infty|\ge\ell_v>0\); reciprocals and quotients therefore
converge uniformly as well.  Applying this separately to every parameter in
\(A,B\) and to every moving block below proves all product limits used later.
All constants are for fixed \(q,r,K\); no uniformity as \(s\to1\), \(q\to1\),
or \(r\to0\) is claimed.

## 5. Reversal and the exact row estimate

For \(z\ne0\) and \(0\le k\le n\),
\[
 (zq^{-n})_k=(-z)^kq^{-nk+k(k-1)/2}(q^{n-k+1}/z)_k.\tag{7}
\]
Indeed, reverse each factor
\(1-zq^{-n+i}=(-z)q^{-n+i}(1-q^{n-i}/z)\).  Apply (7) to the three
moving numerator products with \(z=e/q,e/f,1\), and the three moving
denominator products with \(z=e/a,e/b,e/c\).  Their scalar ratio is
\[
 \left(\frac{(e/q)(e/f)}{(e/a)(e/b)(e/c)}\right)^k
 =\left(\frac{abc}{qef}\right)^k=q^{-2k},
\]
using \(ef=abcq\).  Separately,
\[
 \frac{1-eq^{2k-n-1}}{1-eq^{-n-1}}
 =q^{2k}\frac{1-q^{n+1-2k}/e}{1-q^{n+1}/e}.
\]
The powers cancel exactly, leaving
\[
 U_{n,k}=q^k\frac{1-q^{n+1-2k}/e}{1-q^{n+1}/e}
 \frac{(a,b,c)_k}{(q,e,f)_k}
 \frac{(q^{n-k+2}/e,fq^{n-k+1}/e,q^{n-k+1})_k}
 {(aq^{n-k+1}/e,bq^{n-k+1}/e,cq^{n-k+1}/e)_k}.\tag{8}
\]
Let
\[
 V_+=(q^2/e,qf/e,q),\qquad V_-=(aq/e,bq/e,cq/e),\qquad
 T_k=\frac{(a,b,c)_k}{(q,e,f)_k}.
\]
The last ratio in (8) is
\((V_+q^{n-k})_k/(V_-q^{n-k})_k\), whose offset \(n-k\) is always
nonnegative.  Set
\[
 N=(a,b,c,q^2/e,qf/e,q),\quad
 D=(q,e,f,aq/e,bq/e,cq/e),
\]
with multiplicity, and define
\[
 H=\frac{\exp(\sum_{v\in N}R_v/(1-q))}
        {\prod_{v\in D}\ell_v},\qquad
 \eta_e=\min_{s\in K}|e(s)|,\qquad
 C=H\max(1,q/\eta_e).
\]
The product lemma and the outside-denominator bound from §3 yield, for every
\(n\ge0\), \(0\le k\le n\), \(s\in K\),
\[
 |U_{n,k}|\le Hq^k\left(1+\frac{q^{n+1-2k}}{|e|}\right)
 \le C\bigl(q^k+q^{n-k}\bigr). \tag{9}
\]
This remains valid when \(n+1-2k<0\), and includes both \(k=0\) and \(k=n\).
For \(n=2m+1\), (9) gives simultaneously
\[
 |U_{2m+1,k}|\le C(1+q)q^k\quad(0\le k\le m),
\]
\[
 |U_{2m+1,2m+1-j}|\le C(1+q)q^j\quad(0\le j\le m).
\]
Therefore, for every integer \(M\ge0\),
\[
 \sup_{m\ge M}\sup_{s\in K}
 \left[\sum_{k=M}^{m}|U_{2m+1,k}(s)|
 +\sum_{j=M}^{m}|U_{2m+1,2m+1-j}(s)|\right]
 \le \frac{2C(1+q)q^M}{1-q}.\tag{10}
\]
The right side tends to zero.  This is the exact supremum-of-both-tails
condition: it controls the moving middle before any endpoint series is used.

## 6. Both endpoints and the product-side limit

Fix \(k\).  In (8), \(n-k\to\infty\), so all moving blocks tend uniformly to
1 by (6), and the outside ratio tends uniformly to 1.  Hence
\[
 U_{n,k}\longrightarrow u_k:=\frac{(a,b,c)_kq^k}{(q,e,f)_k}.
\tag{11}
\]
In particular \(u_0=1\).

At the signed right endpoint, cancel the common \((q)_n\) in (8) and use
\(q^n-q/e=-(q/e)(1-eq^{n-1})\):
\[
 U_{n,n}= -\frac qe\,
 \frac{1-eq^{n-1}}{1-q^{n+1}/e}
 \frac{(a,b,c,q^2/e,qf/e)_n}
 {(e,f,aq/e,bq/e,cq/e)_n}.\tag{12}
\]
For \(n=0\), all products are empty and the scalar ratio is 1, so (12) is
exactly \(U_{0,0}=1\).  Taking \(n\to\infty\) with §4 and using
\((q/e)_\infty=(1-q/e)(q^2/e)_\infty\) and
\((e/q)_\infty=(1-e/q)(e)_\infty\),
\[
 \frac{1-q/e}{1-e/q}=-q/e,
\]
shows that the limit of (12) is exactly \(A\), including the minus sign.

For fixed \(j\), divide \(U_{n,n-j}\) by the nonzero \(U_{n,n}\).  The finite
identity \((v)_n=(v)_j(vq^j)_{n-j}\) gives the exact quotient
\[
\begin{aligned}
 \frac{U_{n,n-j}}{U_{n,n}}={}&
 \frac{q^{n-j}-q^{j+1}/e}{q^n-q/e}
 \frac{(q^{n-j+1},eq^{n-j},fq^{n-j})_j}
 {(aq^{n-j},bq^{n-j},cq^{n-j})_j}\\
 &\times\frac{(aq/e,bq/e,cq/e)_j}
 {(q^2/e,qf/e,q)_j}.
\end{aligned}\tag{13}
\]
The first factor tends uniformly to \(q^j\), since
\(|q^n-q/e|\ge q/\max_K|e|>0\); the middle factor tends to 1, and the
last factor is fixed in \(n\) with a nonzero denominator.  Consequently
\[
 U_{n,n-j}\longrightarrow A\,v_j,\qquad
 v_j=\frac{(aq/e,bq/e,cq/e)_jq^j}{(q,q^2/e,qf/e)_j}.\tag{14}
\]
At \(j=0\), every quotient is 1, so the limit is \(A v_0=A\), not a series
starting at \(j=1\).  Finally, §4 gives
\[
 B_n\longrightarrow B\tag{15}
\]
uniformly on \(K\).

## 7. Finite-head/two-tail passage to the sum

The half-row bounds and (11), (14) imply
\[
 |u_k(s)|\le D_0q^k,\qquad |A(s)v_j(s)|\le D_0q^j,\qquad D_0=C(1+q),
\]
so both endpoint series converge uniformly and absolutely on \(K\).  Since
\(A\) is continuous and nonzero on \(K\), dividing the second inequality by
\(\min_K|A|>0\) also proves uniform absolute convergence of \(\Phi'\).

For \(n=2m+1\), the disjoint ranges \(0\le k\le m\) and
\(m+1\le k\le2m+1\) partition the whole finite sum.  Reversing the second
range with \(j=2m+1-k\), (4) becomes
\[
 B_{2m+1}=\sum_{k=0}^{m}U_{2m+1,k}
 +\sum_{j=0}^{m}U_{2m+1,2m+1-j}. \tag{16}
\]
No middle or endpoint term is omitted.

Fix \(M\ge1\), and write
\[
 H_M(s)=\sum_{k=0}^{M-1}u_k(s)+\sum_{j=0}^{M-1}A(s)v_j(s).
\]
For \(m\ge M\), subtract \(H_M\) from (16).  The two finite heads converge
uniformly by (11) and (14), while the two remaining finite tails are bounded
by the exact \(E_M=2C(1+q)q^M/(1-q)\) from (10).  Passing to the limit and
using (15) gives
\[
 \sup_{s\in K}|B(s)-H_M(s)|\le E_M.
\]
Since \(E_M\to0\) and \(H_M\to\Phi+A\Phi'\) uniformly by absolute
convergence, (1) follows on \(K\).  Every point \(s\in\Omega_q\) lies in the
singleton compact set \(K=\{s\}\), proving (1) throughout the deleted
corridor.

Equivalently, extend each half-row by zero beyond \(m\).  Equations (9)--(10)
provide the common summable majorant \(D_0q^{\text{index}}\), so the same
argument is an explicit Nat-indexed Tannery/dominated-convergence
instantiation.  The finite-head proof above is retained to make the
interchange self-contained and to avoid assuming the desired nonterminating
identity.

## 8. Classical comparison and exact scope

The right side \(B\) and the two endpoint series in (1) are the specialization
of the classical Sears target recorded as DLMF 17.7.5
([NIST DLMF 17.7.E5](https://dlmf.nist.gov/17.7.E5)); DLMF is used for target
comparison, not as a premise.  The two-end limiting organization is the
Bailey method as presented in Gasper, *Lectures on q-Series*, §4.3.4--§4.3.7,
with the historical source W. N. Bailey, *Generalized Hypergeometric Series*,
Cambridge Tracts in Mathematics and Mathematical Physics 32 (Cambridge
University Press, 1935).  Sears' original nonterminating transformation is
cited through the bibliography in Gasper (Sears 1951a); no unproved
nonterminating transformation is imported here.

The derivation above proves the complete independent real domain
\(0<q<1,-1<r<0\) and every complex \(s\in\Omega_q\), including \(n=0\),
\(j=0\), empty products, signed endpoints, every denominator/product
condition, the whole-row estimate (9), the exact supremum bound (10),
absolute convergence, and the finite-head limit.  It does not assert a bound
uniform as \(s\to1\).  In particular it does not prove the distinct
\(h^3\)-normalized tail at \(s=1\), the \(b_0,b_1\) isolation and \(W(1)\)
start, the cubic/Laurent extraction, branch or Taylor transfer, the later
support/inverse substitution, the actual weighted/count semantics of the
\(B/C\) consumers, a native finite-Jackson supplier, or any Lean/kernel
acceptance.  Those are separate downstream obligations; they are not hidden
in this source argument.
