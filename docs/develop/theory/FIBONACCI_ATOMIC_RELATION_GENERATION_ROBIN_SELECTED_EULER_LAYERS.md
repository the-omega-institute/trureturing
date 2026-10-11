# Robin 所选原整数族的实际 Euler 层输运

## 1. 原整数来源、完整所选区间与核

**定义 1.1（来源与参数）。** 对正整数 \(n>e\) 置
\(F(n)=\log(\sigma(n)/n)-f(\log n)\)，其中
\[
 f(x)=\log\log x,\qquad \lambda(x)=f'(x)=\frac1{x\log x},
 \qquad w(x)=-\lambda'(x)=\frac{1+\log x}{x^2\log^2x}\quad(x>1).
\tag{EL.0.1}
\]
固定原来的来源族：对每个使用的素数标签 \(p\)，假设
\(F\) 在正整数类 \(5040p\mid n\) 上取得最大值，并令
\(N_p\) 是该类中取得最大值的最小整数。
这些整数不随以下实数插值而重新选取。

一个原边由 \(N_p=pU\)、\(N_r=rU\)、
\(A=\log(pU)<C=\log(rU)\) 给出，其中 \(5040\mid U\)。
边的严格核心条件是，在整个闭区间 \([A,C]\) 上，
\[
 U=\mathcal N(t),\qquad
 \mathcal N(t)=\prod_{q\ \mathrm{prime}}
 q^{\#\{k\ge1:r_{q,k}>\lambda(t)\}},\qquad
 r_{q,k}=\frac{\log(1+1/(q+\cdots+q^k))}{\log q}.
\tag{EL.0.2}
\]
相等价格的层不属于严格核心。

对原见证 \(X\)，取其原来指定的全部边，令 \(S_X\) 为它们的
完整区间并集；不通过删边或缩短区间改变这个集合。
假设 \(S_X\subset[\ell,\mathcal R]\)、\(3\le\ell\le\mathcal R\)、
\(M_X=|S_X|>0\)，且每个边的标签满足 \(p,r>2\mathcal R\)。
允许不同边有不同核心。下文的原族均保留这些条件。
这些来源和层的记号延续
[原卷 §§85、87、98](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的实际有限层约定；
原族的完整选择及比较前提见
[既有来源几何与核](../../../Library/ArithSums/nicolas2025comparison.md#integrated-weights-of-the-original-selected-family)。

**定义 1.2（完整选择核）。** 置 \(H_t=t^{4/5}\)、\(B_t=t+H_t\)，并定义
\[
 k_t(x)=\frac{\lambda(x)-\lambda(B_t)}{w(t)t^{11/10}}
          \mathbf1_{t<x\le B_t},\quad
 b(t)=\frac{\lambda(t)-\lambda(B_t)}{w(t)t^{11/10}},\quad
 \mathcal W_X(x)=\int_{S_X}k_t(x)\,dt.
\]
价格只在 \(x>1\) 求值，核在其余位置取零。
以下在单个见证上省略下标 \(X\)，并令
\(\mathcal D=\int_0^\infty\mathcal W(x)dx\)。
令 \(\theta(x)=\sum_{q\le x}\log q\)，使用弱端点，且
令 \(\psi(x)=\sum_{q^k\le x}\log q\) 为完整素数幂的 Chebyshev 函数，
\(K(x)=\log\mathcal N(x)\)，并定义 \(Q(x)=K(x)-\psi(x)\)。
核恒等式
\[
 k_t(x)=b(t)\mathbf1_{x>t}
 -\frac1{w(t)t^{11/10}}\int_t^{B_t}\mathbf1_{s<x}w(s)\,ds
\]
给出绝对连续的 \(\mathcal W\) 及几乎处处的导数
\[
 \mathcal W'(x)=\mathbf1_S(x)b(x)-w(x)A_S(x),\qquad
 A_S(x)=\int_{\substack{t\in S\\t<x<B_t}}
              \frac{dt}{w(t)t^{11/10}}.
\tag{EL.0.3}
\]
两项分别可积，支撑在 \([\ell,2\mathcal R]\)；
\(\mathcal D>0\)，因为 \(M>0\) 且每个原核在内部严格为正。

**假设 1.3（保留的原族比较）。** 记 \(h_q=\log q\)，并置
\[
 J_{\rm prime}(X)=\sum_q h_q\mathcal W_X(q)-\mathcal D_X,
 \qquad H_{\rm ref}(X)=\sum_{q,k\ge2}h_q\mathcal W_X(q^k),
 \qquad\mathcal I_X=J_{\rm prime}(X)+H_{\rm ref}(X).
\tag{EL.0.4}
\]
引用原族已有的参考层估计 \(H_{\rm ref}/M_X=1/4+o(1)\) 和
离散来源比较：对每个固定 \(\eta>0\)，越过一个共同起点后，
\[
 \mathcal I_X\le-(c_Q-\eta)M_X-\mathcal C_X+\varepsilon_X,
 \quad c_Q=\frac{\sqrt2-1}{4},\quad\mathcal C_X\ge0,
 \quad\varepsilon_X/M_X=o(1).
\tag{EL.0.5}
\]
固定原族全部来源常数后，这里的两个 \(o(1)\) 对全部合格原见证在
\(\ell_X\to\infty\) 时一致；每个固定 \(\eta\) 的共同起点允许依赖
\(\eta\) 与这些固定常数。
这里的原离散 \(\mathcal C_X\) 与实数插值比较的成本分别保留，
不作同一性假设。共同起点包含原来全部解析和来源前提，且不指定数值。
原参考估计与比较分别见
[既有原族比较和参考层证明](../../../Library/ArithSums/nicolas2025comparison.md#integrated-weights-of-the-original-selected-family)；
以下不重新证明这两个输入。

## 2. 实际层与参考层的分离

For an actual prime \(q\) and \(k\ge1\), write
\[
 h_q=\log q,\quad n_{q,k}=q^k,\quad
 \beta_{q,k}=\log\left(1+\frac1{q+\cdots+q^k}\right),\quad
 r_{q,k}=\beta_{q,k}/h_q,
 \qquad\lambda(\tau_{q,k})=r_{q,k}.
\]
The decreasing bijection \(\lambda:(1,\infty)\to(0,\infty)\)
defines \(\tau_{q,k}\) uniquely. The strict actual inventory uses
\(\tau_{q,k}<x\), and the weak reference inventory uses
\(q^k\le x\). In particular
\[
 q<\tau_{q,1}<q+1,\qquad \tau_{q,k}<q^k\quad(k\ge2).
\tag{EL.1}
\]
Indeed \(1/(S+1)<\log(1+1/S)<1/S\) for \(S>0\).
For \(k=1\), divide by \(\log q\) and compare with
\(\lambda(q)\) and \(\lambda(q+1)\). For \(k\ge2\),
\(S+1=1+q+\cdots+q^k<2q^k\le kq^k\), so
\(r_{q,k}>1/(kq^k\log q)=\lambda(q^k)\).

**Proposition (separation of the two higher-layer phases).** If
\(k\ge2\) and \(n=q^k\ge16\), then
\[
 \tau_{q,k}<3n/4.
\tag{EL.2}
\]
Consequently, for \(t\ge243\),
\[
 t<n\le B_t\ \Longrightarrow\ \tau_{q,k}<t,
 \qquad
 t\le\tau_{q,k}\le B_t\ \Longrightarrow\ n>B_t.
\tag{EL.3}
\]
On an original selected edge, every higher reference atom in the
forward kernel is therefore already occupied in that edge's literal
\(U\); every first-layer reference prime in \((t,B_t]\) is absent
from \(U\).

*Proof.* Since
\(S+1=(q^{k+1}-1)/(q-1)<nq/(q-1)\),
\[
 r_{q,k}>\frac{k(1-1/q)}{n\log n}.
\]
The size restriction gives \(k(1-1/q)\ge8/5\): for \(k\ge4\)
it is at least 2; for \(k=3\) it excludes \(q=2\); for \(k=2\)
it forces \(q\ge5\). Also \(n\ge16>(4/3)^6\), whence
\(6\log(3n/4)>5\log n\). Thus
\[
 r_{q,k}>\frac8{5n\log n}
 >\frac1{(3n/4)\log(3n/4)}=\lambda(3n/4),
\]
which proves (EL.2). For \(t\ge3^5\),
\(H_t\le t/3\) and \(B_t\le4t/3\). These inequalities prove
both implications in (EL.3), including their strict endpoints.
Strict occupation in the edge's \(U\) is exactly \(\tau<t\).
For a prime \(q>t\), (EL.1) gives \(\tau_{q,1}>t\), so its
first layer is absent. \(\square\)

For the actual atom use
\[
 k_t^{\rm str}(x)=k_t(x)+b(t)\mathbf1_{x=t}.
\]
This keeps the initially tied actual activation, whereas the reference
atom at \(t\) has zero weight. Both terminal weights vanish. By (EL.3),
the two terms of
\(z_{q,k}(t)=h_q[k_t^{\rm str}(\tau_{q,k})-k_t(q^k)]\)
cannot both be nonzero for \(t\ge243\). Hence, layer by layer,
\[
 (z_{q,k})_-=h_qk_t(q^k),\qquad
 (z_{q,k})_+=h_qk_t^{\rm str}(\tau_{q,k})\quad(k\ge2).
\tag{EL.4}
\]
These identities concern the parts of each response, not the parts of
the sum. Integrating over the complete \(S_X\) gives the reference and
actual higher-layer sums
\[
 H_{\rm ref}=\sum_{q,k\ge2}h_q\mathcal W(q^k),\qquad
 H_{\rm act}=\sum_{q,k\ge2}h_q\mathcal W(\tau_{q,k}).
\]
Initial ties form a finite set of centers and have zero integration
measure. All contributing layers lie in one finite support: if
\(\tau_{q,k}\le2\mathcal R\), then
\(q^k\log q<2\mathcal R\log(2\mathcal R)\), since
\(r_{q,k}<1/(q^k\log q)\).

## 3. 已占用减项的强制尺度

Put
\[
 A_S(x)=\int_{\substack{t\in S\\t<x<B_t}}\frac{dt}{w(t)t^{11/10}}.
\]
The strict/weak conventions and (EL.1) give the exact pulse identity
\[
 Q(x)=\sum_{q,k\ge2}h_q\mathbf1_{\tau_{q,k}<x<q^k}
 -\sum_qh_q\mathbf1_{q\le x\le\tau_{q,1}}.
\]
Finite Stieltjes integration against the absolutely continuous
\(\mathcal W\), using the derivative identity (EL.0.3), yields
\[
\begin{aligned}
 \sum_{q,k}h_q[\mathcal W(\tau_{q,k})-\mathcal W(q^k)]
 ={}&\sum_qh_q\int_q^{\tau_{q,1}}\mathcal W'(x)\,dx\\
 &+\sum_{q,k\ge2}h_q\int_{\tau_{q,k}}^{q^k}w(x)A_S(x)\,dx
 -L_{\rm occ}(X),
\end{aligned}
\]
where
\[
 L_{\rm occ}(X)=\sum_{q,k\ge2}h_q
       \int_{S_X\cap(\tau_{q,k},q^k)}b(t)\,dt.
\tag{EL.5}
\]
This is the original source-local subtraction in the pulse split. It
has no restriction \(q^k\le B_t\); it is not \(H_{\rm ref}\).
The finite support just established justifies each interchange.

**Proposition (compulsory scale of the occupied subtraction).** There
is one finite common start such that every qualifying original witness
beyond it, with its complete unchanged \(S_X\), satisfies
\[
 L_{\rm occ}(X)\ge\frac1{32}\int_{S_X}t^{1/5}\,dt
 \ge\frac{\ell^{1/5}}{32}M_X.
\tag{EL.6}
\]

*Proof.* Fix a classical PNT start \(Y\) (see the
[existing PNT error input](../../../Library/Weil/trudgian2014pnt.md);
only \(\theta(y)/y\to1\) is used) such that
\(99y/100\le\theta(y)\le101y/100\) for every \(y\ge Y\).
Take \(t\ge\max(243,Y^2)\), write \(y=\sqrt t\), and put
\(c=2/\sqrt3>23/20\). The actual primes \(y<q\le cy\) have
\(t<q^2\le4t/3\); (EL.2) gives \(\tau_{q,2}<t\).
Their exact mass is
\[
 \theta(cy)-\theta(y)
 \ge\left(\frac{99c}{100}-\frac{101}{100}\right)y
 >\frac{257}{2000}y>\frac18\sqrt t.
\]
For \(x\ge243\), the exact logarithmic derivative is
\[
 -xw'(x)/w(x)=2+2/\log x-1/(1+\log x)<4.
\]
Integrating this bound gives
\(w(B_t)/w(t)\ge(t/B_t)^4\ge(3/4)^4>1/4\).
Since \(w\) decreases,
\[
 b(t)=\frac{\int_t^{B_t}w(x)dx}{w(t)t^{11/10}}
 \ge\tfrac14 t^{-3/10}.
\]
Every square just counted occurs in the integrand of (EL.5), even if
it lies beyond \(B_t\). Their contribution is at least
\(t^{1/5}/32\); the remaining terms are nonnegative. Integration over
exactly \(S_X\) proves (EL.6). The start is finite and unspecified;
its enlargement for the original source premises is retained. \(\square\)

Thus treating this raw subtraction as \(o(M_X)\), or as bounded by
\(CM_X\) for a fixed \(C\) along the cofinal original family, has
the wrong scale. The positive \(wA_S\) term contains the corresponding
large cancellation. This does not make the centered net response large:
the already proved reference estimate is
\(H_{\rm ref}=(1/4+o(1))M_X\). Formula (EL.4) locates its entire
negative phase in layers already occupied in the same edge's \(U\).
The raw subtraction and that negative-phase mass are distinct quantities.

## 4. 合法 5040 整数比较给出的排除

**Proposition (source-relative activation exclusion).** Retain an
original good edge with endpoint sources \(pU,rU\), clocks \(A<C\),
strict inventory \(U\) on \([A,C]\), and labels
\(p,r>2\mathcal R\). For \(t\in[A,C]\), \(t\ge64\), an actual
prime \(q\le2t\), \(h=\log q\), and \(e=v_q(U)\), one has
\[
 \tau_{q,e+1}>t+h/3.
\]
If \(e>v_q(5040)\), then also
\[
 \tau_{q,e}<t-h/2.
\tag{EL.7}
\]
The label and source premises are indispensable; no new integer
maximality at an interpolated real center is asserted.

*Proof.* The labels exceed \(q\), so \(q\ne p,r\). The insertion
\(rU\to rUq\) stays in the original \(5040r\) class. Maximality gives
\[
 \beta_{q,e+1}\le f(C+h)-f(C)\le f(t+h)-f(t).
\]
If \(e>v_q(5040)\), deletion \(pU\to pU/q\) stays in the original
\(5040p\) class and gives a smaller integer. Least attainment makes
its objective comparison strict:
\[
 \beta_{q,e}>f(A)-f(A-h)\ge f(t)-f(t-h).
\]
All logarithms are legal, since \(p>q\) and \(U\ge5040\).
Both transfers use decrease of the corresponding increments of the
concave \(f\). Strict convexity of \(\lambda=f'\) gives
\[
 r_{q,e}>\frac1h\int_{t-h}^t\lambda(s)ds
 >\lambda(t-h/2),
\]
which proves the deletion assertion.
For insertion, \(h\le\log(2t)\le t/10\). The exact formula for
\(w\) implies
\[
 \frac{w(t+h)}{w(t)}\ge(10/11)^4>2/3.
\]
Indeed \(t/(t+h)\ge10/11\),
\(\log(t+h)-\log t\le h/t\le1/10\le(\log t)/10\), and the
remaining numerator ratio is at least one. Therefore
\[
\begin{aligned}
 \lambda(t)-r_{q,e+1}
 &\ge\frac1h\int_0^h(h-u)w(t+u)du\\
 &\ge\frac h2w(t+h)>\frac h3w(t)
 \ge\int_0^{h/3}w(t+u)du.
\end{aligned}
\]
It follows that \(r_{q,e+1}<\lambda(t+h/3)\), proving the insertion
assertion. \(\square\)

In particular, a sufficiently late original selected center has no
prime in \((t,t+L(t)]\), where \(L(t)=(\log t)/3-1>0\). If such
a prime existed, (EL.1) would make it absent from \(U\), so (EL.7) and
(EL.1) would imply both
\(\tau_{q,1}>t+(\log q)/3\) and
\(\tau_{q,1}<q+1\le t+(\log t)/3<t+(\log q)/3\).
But the baseline of this excluded segment is at most
\[
 \int_t^{t+L(t)}k_t(x)dx\le b(t)L(t)
 \le t^{-3/10}\log t/3.
\]
Its integral over the complete \(S_X\) is at most
\(M_X\ell^{-3/10}\log\ell/3=o(M_X)\). This genuine exclusion
therefore supplies no fixed favorable coefficient.

**Proposition (the conservation test has no global monotone representative).** The conservation test \(g=\mathcal W'/w\) has no globally
nondecreasing or globally nonincreasing representative on
\((1,\infty)\). It vanishes almost everywhere before and after the
compact support \([\ell,2\mathcal R]\). A monotone representative
with those two properties must vanish everywhere. Then absolute
continuity forces \(\mathcal W\) to be constant, and compact support
forces it to be zero, contrary to \(\int\mathcal W=\mathcal D>0\).
This rules out the global monotone-test shortcut for the actual weight.



## 5. 完整原族的固定下系数

**定义 5.1（完整族的固定下系数）。** 对同一原族，考虑条件
\[
 \exists\kappa<c_Q\quad\forall T<\infty\quad
 \exists\text{合格原见证 }X\text{ 且 }\ell_X\ge T:
 \quad\mathcal I_X\ge-\kappa M_X.
\tag{EL.8}
\]
其中每个 \(T\) 都可以包含任意有限共同起点；
所选集合始终是该见证完整而未改动的 \(S_X\)。

**定理 5.2（保留固定余量的首层等价）。** 在假设 1.3 下，
条件（EL.8）等价于同一量词和同一完整原族的条件
\[
 \exists\kappa_{\rm prime}<\sqrt2/4\quad\forall T<\infty\quad
 \exists\text{合格原见证 }X\text{ 且 }\ell_X\ge T:
 \quad J_{\rm prime}(X)\ge-\kappa_{\rm prime}M_X.
\tag{EL.9}
\]
而（EL.8）与离散比较（EL.0.5）不能同时成立。

**证明。** 从（EL.8）出发，先选取
\(\kappa+1/4<\kappa_{\rm prime}<\sqrt2/4\)。
把 \(H_{\rm ref}/M_X\) 的误差起点加入每个给定的 \(T\)，
使其绝对误差小于这两个系数的固定差。
由 \(J_{\rm prime}=\mathcal I-H_{\rm ref}\) 得（EL.9）。
反向先选 \(\kappa_{\rm prime}-1/4<\kappa<c_Q\)，
以同样的固定差控制参考误差，再用
\(\mathcal I=J_{\rm prime}+H_{\rm ref}\) 得（EL.8）。
两次均只扩大共同起点，没有缩小原见证的 \(S_X\)。
最后固定 \(\eta=(c_Q-\kappa)/2>0\)，
在（EL.0.5）与（EL.8）的同一见证上得到
\[
 \frac{c_Q-\kappa}{2}+\frac{\mathcal C_X}{M_X}
 \le\frac{\varepsilon_X}{M_X}=o(1),
\]
与 \(\mathcal C_X\ge0\) 及固定正差矛盾。\(\square\)

## 6. 来源相对的首钟符号与固定余量输运

本节保留定义 1.1–1.2 的全部来源条件，并要求
\(243\le\ell\le\mathcal R<\infty\)。原 \(N_p\) 仍是各
\(5040p\) 类的最小最大化整数；所有原边、闭边上的字面严格核心及
\(p,r>2\mathcal R\) 不变。始终积分于全部原边的完整并集 \(S_X\)，
重叠只计一次，\(M_X=|S_X|>0\)，不另选来源、不删边或截短区间。
首钟符号和误差定理不使用 PNT、假设 1.3、（EL.0.5）、
共尾见证存在性或任何有利的有符号下界。

省略单个见证的下标，记 \(\tau_q=\tau_{q,1}\)、\(h_q=\log q\)，并置
\[
 K_1(x)=\sum_{\tau_q<x}h_q,\qquad
 \delta_1(x)=\theta(x)-K_1(x),\qquad
 P_1(X)=\sum_qh_q[\mathcal W_X(\tau_q)-\mathcal W_X(q)],
 \qquad E(u)=u^{-3/10}\log(2u).
\]
实际端点仍严格为 \(\tau_q<x\)，参考端点仍弱为 \(q\le x\)；
单核的实际初始权重是 \(k_t^{\rm str}(t)=b(t)\)，参考初始权重
及两种终端权重均为零。所有价格只在 \(x>1\) 求值，
密度在其余位置延拓为零。

**定理 6.1（闭排除与有符号首钟误差）。** 对每个合格原见证，
\[
 S_X\cap[q,\tau_q]=\varnothing\quad(q\text{ 为素数}),\qquad
 -E(\ell_X)M_X\le P_1(X)\le0.
\tag{EL.10}
\]
误差函数 \(E\) 在 \([243,\infty)\) 严格递减并趋于零；
此界对全部原见证显式一致，不依赖 \(\mathcal R\)、边数或并集的分量数。

**证明。** （EL.1）给出 \(q<\tau_q<q+1\)。若
\(t\in S\cap[q,\tau_q]\)，取一条包含 \(t\) 的原边
\(N_p=pU,N_r=rU\)，其上端时钟为 \(C\ge t\)。
首层价格 \(r_{q,1}=\lambda(\tau_q)\le\lambda(t)\)，
而同素数的后续层价格严格下降，所以字面严格核心给出 \(q\nmid U\)；
在 \(t=\tau_q\) 的价格相等处也如此。又 \(q\le t\le\mathcal R\)，
故 \(q\ne p,r\)。插入 \(N_r=rU\to rUq\) 是原 \(5040r\) 类中的
合法整数比较。由原 \(N_r\) 的最大性、乘法性和 \(\lambda\) 的递减性，
对 \(h=\log q\) 有
\[
 \beta_{q,1}\le f(C+h)-f(C)\le f(t+h)-f(t),\qquad
 r_{q,1}\le\frac1h\int_0^h\lambda(t+u)\,du.
\]
这正是（EL.7）的上端来源插入，不是假定实数中心的新最大性。
这里 \(q>t-1\ge242\)，故 \(h>3\)；且
\(h\le\log t\le t/10\)。最后一式在 \(t=243\) 成立，
\(t/10-\log t\) 此后递增。复用（EL.7）的精确密度比较
\(w(t+h)/w(t)\ge(10/11)^4>2/3\) 及 \(w\) 的递减性，得到
\[
 \lambda(t)-r_{q,1}
 \ge\frac1h\int_0^h(h-u)w(t+u)\,du
 \ge\frac h2w(t+h)>\frac h3w(t)
 \ge\int_0^{h/3}w(t+u)\,du.
\]
因此 \(\tau_q>t+h/3>t+1\ge q+1\)，与（EL.1）矛盾。
这排除整个闭区间，包括 \(t=q\) 和 \(t=\tau_q\)。
全证明只用了原上端来源的最大性；原下端来源、最小取得性及其他
定义 1.1 条件仍保留在完整原族中。

现在复用 [Nicolas 既有 MS2 及其紧邻的首层端点证明](../../../Library/ArithSums/nicolas2025comparison.md)：
\[
 \delta_1(x)=\sum_q h_q\mathbf1_{q\le x\le\tau_q},
 \qquad 0\le\delta_1(x)\le\log x\quad(x>1).
\tag{EL.11}
\]
确切端点来自弱参考与严格实际库存；任一贡献素数满足
\(x-1<q\le x\)，此半开区间至多含一个整数，其权重不超过 \(\log x\)。
这也核对了两端相等情形。由闭排除，\(\delta_1(t)=0\) 对每个
\(t\in S\) 成立。MS2 已给出一般首层校正
\[
 E_1(a,H)=\int_0^H[\delta_1(a)-\delta_1(a+u)]
                     \frac{w(a+u)}{w(a)}\,du,\qquad
 -H\log(a+H)\le E_1(a,H)\le H\log a\quad(a>2,\ H>0).
\]
下述因子 \(1\) 的误差尺度是这一既有供应结果的应用，
不是新的误差发现，也不另行证明较弱的因子 \(2\) 区间计数界。

\(\mathcal W\) 及（EL.0.3）的导数支撑在
\([\ell,2\mathcal R]\)。因 \(\tau_q>q\)，\(q>2\mathcal R\) 的
两种首层权重均为零，所以一个固定有限素数集覆盖全部贡献。
（EL.0.3）两项密度的积分都等于有限的 \(\int_S b(t)\,dt\)；
绝对连续性与有限脉冲积分遂给出精确恒等式
\[
 \begin{aligned}
 P_1
 &=\sum_qh_q\int_q^{\tau_q}\mathcal W'(x)\,dx
   =\int_1^\infty\delta_1(x)\mathcal W'(x)\,dx\\
 &=-\int_1^\infty\delta_1(x)w(x)A_S(x)\,dx .
 \end{aligned}
\tag{EL.12}
\]
闭脉冲端点的零测度不改变（EL.11）的精确库存约定。
最后一步用的是 \(\delta_1=0\) 于 \(S\)，没有假设紧支撑所选核
在全局单调。实际初始修正也不产生差额，因为 \(\tau_q\notin S\)；
终端零权重及越过 \(B_t\) 的情形由绝对连续积分一并覆盖。

对（EL.12）的非负被积函数用 Tonelli，再用（EL.11），得
\[
 \begin{aligned}
 0\le-P_1
 &=\int_S\frac1{w(t)t^{11/10}}
             \int_t^{B_t}\delta_1(x)w(x)\,dx\,dt\\
 &\le\int_S b(t)\log B_t\,dt
 \le\int_S t^{-3/10}\log B_t\,dt
 \le E(\ell)M.
 \end{aligned}
\]
因 \(\delta_1(t)=0\)，其 \(t\)-被积函数恰为
\(-t^{-11/10}E_1(t,H_t)\)，即 MS2 的同一首层校正。
这里 \(w\) 递减，故
\(b(t)=\int_t^{B_t}w(x)\,dx/[w(t)t^{11/10}]
 \le H_t/t^{11/10}=t^{-3/10}\)，且 \(B_t\le2t\)。
所有内部价格区间均在 \(x>1\)。
最后
\[
 E'(u)=u^{-13/10}\left[1-\tfrac3{10}\log(2u)\right]<0
 \quad(u\ge243),
 \qquad
 \lim_{u\to\infty}\frac{\log(2u)}{u^{3/10}}
 =\lim_{u\to\infty}\tfrac{10}{3}u^{-3/10}=0
\]
（末式用 L'Hôpital）；因 \(\log486>10/3\)，递减断言成立。
故最后一个积分界显式一致，证明完成。\(\square\)

**推论 6.2（实际与参考首钟的固定余量等价）。** 置
\[
 J_{\rm act,prime}(X)=\sum_qh_q\mathcal W_X(\tau_q)-\mathcal D_X,
 \qquad J_{\rm ref,prime}(X)=J_{\rm prime}(X).
\]
于是对同一完整原见证，
\[
 J_{\rm act,prime}\le J_{\rm ref,prime}
 \le J_{\rm act,prime}+E(\ell_X)M_X.
\tag{EL.13}
\]
在同一完整原族及相同量词下，（EL.9）等价于
\[
 \exists\kappa<\sqrt2/4\quad\forall T<\infty\quad
 \exists\text{合格原见证 }X\text{ 且 }\ell_X\ge T:
 \quad J_{\rm act,prime}(X)\ge-\kappa M_X.
\tag{EL.14}
\]
\(T\) 可包含任意给定的有限共同起点，包括 \(\ell\ge243\)；
这种扩大不改变原族或所选集合。

**证明。** 精确等式 \(J_{\rm act,prime}=J_{\rm ref,prime}+P_1\)
与（EL.10）给出（EL.13）。实际到参考用其左侧不等式，
保留同一 \(\kappa\) 和见证。参考到实际先固定（EL.9）的系数
\(\kappa<\sqrt2/4\)，再选
\(\kappa<\kappa'<\sqrt2/4\)。对每个给定 \(T\)，仅将其扩大至
一个同时满足原共同前提、\(\ell\ge243\) 和
\(E(\ell)<\kappa'-\kappa\) 的有限起点；（EL.9）在该起点给出的
同一完整见证满足 \(J_{\rm act,prime}\ge-\kappa'M_X\)。
这保持一个固定系数以及全部共尾量词。\(\square\)

若再讨论假设 1.3 与定理 5.2，原先输入比较的全部来源常数始终固定，
共同起点仍可依赖那些常数；新 \(E(\ell)\) 本身是上述显式一致界。
（EL.10）–（EL.14）不证明任一有利下界或共尾见证存在性，
也不证明 RH 或不受限 Robin。尚欠的仍是（EL.9）的完整固定余量
下界义务；首钟误差的 \(o(M_X)\) 输运没有支付任何固定有利系数。

本节新推理仅置于拥有理论。误差供应归于既有 Nicolas MS2，
来源合法插入归于本理论 §4 的原整数比较；不重复 Library 的
A1–A19 接口。已有对应来源的有界检索未找到显式相同的完整族
来源相对符号结论；这不构成文献或全仓库的新颖性主张。
