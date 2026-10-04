# Triple-product sum rigidity in a short integer interval

## 1. Sum rigidity

**Theorem 1.1 (Triple-product sum rigidity).** Let $m,h,a,b,c,d,e,f$ be integers with $m>0$, $h\geq0$ and $m>h^2$. Suppose each of $a,b,c,d,e,f$ belongs to $[m,m+h]$. Then

$$
abc=def\quad\Longrightarrow\quad a+b+c=d+e+f.
$$

Rows may repeat, and neither triple is required to be ordered or disjoint from the other.

Proof. If $h=0$, all six rows equal $m$. Otherwise $h\geq1$, so $h\leq h^2<m$. For any triple, choose its least member $x$ and write the other two as $x+r,x+s$. Thus $m\leq x\leq m+h$ and $0\leq r,s\leq h$. Its sum $Z$ and product $P$ satisfy

$$
\begin{aligned}
Z&=3x+r+s,\quad P=x(x+r)(x+s),\\
D:=Z^3-27P&=9x(r^2-rs+s^2)+(r+s)^3.
\end{aligned}
$$

The quadratic term is nonnegative. If $r\leq s$, then $r^2-rs+s^2\leq s^2\leq h^2$; the case $s\leq r$ is symmetric. Consequently

$$
0\leq D\leq9(m+h)h^2+8h^3=9mh^2+17h^3<26m^2.
$$

The last strict bound uses $mh^2<m^2$ and $h^3=h\,h^2<m^2$. For integer sums $Z_1<Z_2$ with $Z_1\geq3m$, integrality gives $Z_2\geq Z_1+1$, whence

$$
Z_2^3-Z_1^3\geq3Z_1^2+3Z_1+1>27m^2.
$$

Equal products instead give $Z_2^3-Z_1^3=D_2-D_1<26m^2$, a contradiction. Interchanging the triples rules out the reverse strict inequality, proving equality of sums.

## 2. Scope and boundary

The condition $m>(h+1)^2$ with $h\geq0$ implies $m>h^2$, so the theorem applies to that shorter-hull predicate. The distinct triples $(875,891,896)$ and $(880,882,900)$ lie in $[875,900]$, have product $698544000$ and sum $2662$, and satisfy $875>26^2$. This hull contains the primes $877,881,883,887$.

Without the interval premise, $(1,2,12)$ and $(1,3,8)$ have equal product $24$ and unequal sums $15$ and $12$. The theorem does not classify all six-row unit relations or establish Hall conditions, complete-hull compositeness, higher-endpoint sectors, nonunit relations, larger cores, long spans, or unrestricted Grimm's conjecture.

## 追加锚（本行以下为增补区）
