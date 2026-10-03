---
bibkey: bretechedrappeau2020smoothaffine
authors: Régis de la Bretèche; Sary Drappeau
year: 2020
title: Niveau de répartition des polynômes quadratiques et crible majorant pour les entiers friables
doi: 10.4171/JEMS/951
url: https://doi.org/10.4171/JEMS/951
claim: Theorem 4.1 and Corollary 4.2 bound simultaneous smooth affine values with growing coefficients; the actual FIB exception budget pays the cofactor coefficient height, but supplies neither smoothness of n-2 nor a pointwise discriminant or Euler-budget estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Simultaneous smooth affine values and the actual norm cofactor

The paper appeared in *Journal of the European Mathematical Society*
**22** (2020), 1577–1624. The inspected primary text is the
[author-hosted manuscript](https://drappeau.perso.math.cnrs.fr/documents/friable-consec-jems-prefinal-fix1.pdf),
whose title page says 25 March 2025. The theorem locators below refer
to that version's printed pages. Its statements and the relevant proof
opening were inspected; the full analytic proofs have not been
independently verified. The parameter applications below are paper
derivations, with no Lean verification or originality claim.

## The joint counting theorem and its conditions

Write $\Psi(X,y)=\#\{r\le X:P^+(r)\le y\}$ and let $\rho$ be the
Dickman function. Theorem 4.1, printed p.13, states that for each fixed
$\varepsilon>0$ there exist $C,\kappa>0$ such that

$$
\#\{r\in[X,(1+\eta)X]:
 P^+(ar+b)\le y_1,\ P^+(c_0r+d)\le y_2\}
\ll_\varepsilon\eta\Psi(X,y_1)
\rho\!\left(\frac{\log X}{\log y_2}\right)^{3/5-\varepsilon},
\tag{S1}
$$

provided

$$
\begin{gathered}
|a|,|b|,|c_0|,|d|\le X^\kappa,\qquad
a,c_0>0,\quad (a,c_0)=1,\quad ad-bc_0\ne0,\\
(\log X)^C\le y_1\le y_2\le X,\qquad y_2\le y_1^C,\\
e^{-\kappa\sqrt{\log y_1}}\le\eta\le1.
\end{gathered}
$$

Corollary 4.2, printed p.14, supplies

$$
\#\{r\in[X,(1+\eta)X]:P^+(r(ar+b))\le y\}
\ll_\varepsilon\eta X
\rho\!\left(\frac{\log X}{\log y}\right)^{8/5-\varepsilon}
\tag{S2}
$$

for $(\log X)^C\le y\le X$,
$e^{-\kappa\sqrt{\log y}}\le\eta\le1$, and
$1\le a,|b|\le X^\kappa$. Neither statement includes the canonical
FIB lift, a character-conductor weight, or an extremal exponent vector.

## Extracting the actual supported square depth

Reuse the [unit-bit-one exception construction](../Scale/pollack2017nonresidues.md):
$n>2$, $n=1+2A+3B$, $c=4A+7B$, nonsquare signed
$D=\delta s^2$, $q=|\delta|$, and

$$
c^2-\delta s^2=5n(n-2),\qquad T=T_1\mid\gcd(c,s).
$$

The actual depth definitions also give $T^2\mid5n$. For an included
prime $p\ne5$, $2b_p=e_p$; at five, $2b_5=e_5+1$. Set

$$
g_5=\gcd(T^2,5)\in\{1,5\},\qquad
L=\frac{T^2}{g_5},\qquad a_0=\frac5{g_5},\qquad
k=\frac nL,\quad v=\frac cT,\quad u=\frac sT.
$$

These are integers. In fact $L$ removes the entire primary component
$p^{e_p}$ at each selected exception prime, so $(L,k)=1$.
Dividing the same norm identity by $T^2$ gives

$$
v^2-\delta u^2=a_0k(Lk-2),\qquad n=Lk.
\tag{S3}
$$

The two affine forms $a_0k$ and $Lk-2$ have
$(a_0,L)=1$, determinant $-2a_0\ne0$, and
$\gcd(a_0k,Lk-2)\mid2a_0\mid10$.
Thus (S1) applies with $(a,b,c_0,d)=(a_0,0,L,-2)$ whenever
its remaining conditions hold; (S2) uses $(a,b)=(L,-2)$.

For a fixed $T$ stratum and actual integers
$n\in[N_*,(1+\eta)N_*]$, take $X=N_*/L$.
Under the additional SA support asymptotic
$\operatorname{rad}(n)=n^{1-o(1)}$, the existing exception budget
gives $L\le T^2\le H_1^2=N_*^{o(1)}$.
Consequently $L\le X^\kappa$ eventually for the fixed
$\kappa>0$ of (S1). The coefficient-height condition is paid by
this exponent budget. For quantitative CA input, reuse the
[same-price excess bound](nicolas2025comparison.md).

This coordinate change keeps the original integer. Its finite-power
deficit is still

$$
D_{\rm pow}(n)=-\sum_{p\mid Lk}
\log\!\left(1-p^{-(v_p(L)+v_p(k)+1)}\right),
\tag{S4}
$$

and is not replaced by $D_{\rm pow}(k)$. The actual tests defining
$\mathcal E_1$ and the canonical lift must also be retained. For
example, a strip condition $|c-\sqrt5(n-1)|\le K$ becomes
$|Tv-\sqrt5(Lk-1)|\le K$, with width $O(1/T)$ in $v$.

Three conditions remain unpaid. Smoothness of $n$ controls $a_0k$
apart from a fixed factor five, but says nothing about $n-2=Lk-2$.
Taking $y_2$ of size $n$ violates $y_2\le y_1^C$ at logarithmic
$y_1$. Also, $P^+(n)\asymp\log n$ does not by itself meet the
source's sufficiently large power $(\log X)^C$: enlarging $y_1$
counts a larger population. Finally, a count in each fixed stratum,
even with both factors smooth, does not give a pointwise deficit
or conductor bound at its actual extremal member.

## The residual square depth and weighted exception target

The square depth still missing after this extraction is $u=s/T_1$.
Write $R=R_1$ and $g_q=\gcd(q,R)$. The exact modulus identities are

$$
|D|=qT_1^2u^2,\qquad
m_1=\frac{qR}{g_q}
=\frac{|D|R}{g_qT_1^2u^2}.
$$

For fixed admissible character-cutoff exponent $b>0$ and $Y=\log n$,

$$
m_1^b\le Y
\iff u^2\ge\frac{|D|R}{g_qT_1^2Y^{1/b}}.
\tag{S5}
$$

This equivalence supplies no estimate for $u$. If **additionally**
$|D|\ge n^\zeta$ with fixed $\zeta>0$ and $T_1=n^{o(1)}$,
meeting (S5) requires $u\ge n^{\zeta/2-o(1)}$.
No such discriminant lower bound is assumed for the actual remaining
candidates. The residual factor can contain extra depth at already
supported primes; it need not be supported outside $n$.
The character theorem's onset and supplied weight must still be
checked after its cutoff is met.

An alternative keeps the primitive character and pays its actual
exceptions in weight. Set $w_p=\log(p/(p-1))$ and

$$
W_\delta(Y)=\sum_{\substack{p\le Y\\\chi_\delta(p)=-1}}w_p,
\qquad
E_\delta(n;Y)=\sum_{\substack{p\le Y\\p\mid n\\\chi_\delta(p)=-1}}w_p.
$$

Then $W_\delta(Y)-E_\delta(n;Y)\le J_{\rm miss}(n;Y)$.
The sufficient joint target remains

$$
W_\delta(Y)-E_\delta(n;Y)+D_{\rm pow}(n)
>M(Y)+J_{\rm large}(n;Y).
\tag{S6}
$$

These are the same actual Euler-budget terms as in the
[character-budget note](../Scale/bourgainlindenstrauss2003entropy.md);
the signed Mertens term has not been replaced by an absolute value.
The actual negative-support set in $E_\delta$ can be smaller than
the computable superset $\mathcal E_1$. Charging all of that superset
is conservative and can lose positive or zero-character members.

Permitted exponent depth alone cannot pay this subtraction by a
uniform local multiple of the finite-power deficit. For
$d_p(e)=-\log(1-p^{-e-1})$, elementary logarithm bounds give

$$
\frac{w_p}{d_p(e)}\ge p^e-\frac1p.
\tag{S7}
$$

At a possible negative support prime other than five, $e=2b_p$;
at five, $e=2b_5-1$. Thus a successful use of (S6) still needs a
joint restriction on which exceptions occur and on the rest of
the actual exponent vector. The joint smooth-affine counting
theorem supplies neither (S5) nor (S6) for every actual candidate.
Unit bit zero and square $D$ remain separate branches of the
general Robin problem.
