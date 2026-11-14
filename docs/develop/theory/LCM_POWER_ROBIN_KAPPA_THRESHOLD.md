# LCM 幂 Robin 判据的参数门槛

本卷研究 Fan–Kobayashi–Molnar [A family of analogues to the Robin criterion, Ramanujan J. 70 (2026), article 40; arXiv:2511.02106v1] 引入的函数族

$$
\sigma^{[\kappa]}(n)=\sum_{d\mid n}\mu(n/d)\,\sigma(d)^\kappa\qquad(\kappa>1)
$$

及其 κ-Robin 不等式

$$
\sigma^{[\kappa]}(n)<\frac{(e^\gamma n\log\log n)^\kappa}{\zeta(\kappa)} .
\tag{1.1}
$$

各节按编号追加，卷末追加锚以下为增补区。

## 1. 引理 4.15 的全参数推广与 3/2 的尖锐性

该文定理 1.5 对固定的 $\kappa>3/2$ 证明：RH 等价于 (1.1) 对所有充分大的 $n$ 成立。其定理 6.1 是其中一个方向：对 $\kappa>3/2$，若 RH 成立，则 (1.1) 对所有充分大的 $n$ 成立。其定理 5.2 对每个 $\kappa>1$ 证明：若 RH 不成立，则 (1.1) 对无穷多个 $n$ 不成立。该文还留下两个问题。注记 4.16 认为其引理 4.15 对全部 $\kappa>1$ 成立。第 8 节问定理 6.1 对更小的 $\kappa$ 是否仍成立。本节证明前者，并对 $1<\kappa<3/2$ 回答后者：此时 (1.1) 的终于成立无条件为假，因而把定理 6.1 延伸到这些 $\kappa$ 所得的命题等价于 RH 不成立。

**引理 1.1（幂差的严格对数凹性）。** 设 $\kappa>1$，$C_\kappa(t)=(1+t)^\kappa-t^\kappa$，$B_\kappa(t)=\log C_\kappa(t)$（$t\ge0$）。则对 $t>0$，

$$
(C_\kappa')^2-C_\kappa C_\kappa''=\kappa D_\kappa^2+\kappa(\kappa-1)\,[t(1+t)]^{\kappa-2},\qquad D_\kappa(t)=(1+t)^{\kappa-1}-t^{\kappa-1},
\tag{1.2}
$$

从而 $B_\kappa$ 在 $(0,\infty)$ 上严格凹，在 $[0,\infty)$ 上凹，且 $B_\kappa(0)=0$。

**证明。** 记 $a=1+t$、$b=t$，则 $C_\kappa'=\kappa D_\kappa$，$C_\kappa''=\kappa(\kappa-1)(a^{\kappa-2}-b^{\kappa-2})$。将 $\kappa^2D_\kappa^2$ 写成 $\kappa D_\kappa^2+\kappa(\kappa-1)D_\kappa^2$。又

$$
D_\kappa^2-(a^\kappa-b^\kappa)(a^{\kappa-2}-b^{\kappa-2})=a^\kappa b^{\kappa-2}+a^{\kappa-2}b^\kappa-2a^{\kappa-1}b^{\kappa-1}=(ab)^{\kappa-2}(a-b)^2=(ab)^{\kappa-2},
$$

两式合并即得 (1.2)。由于 $C_\kappa>0$，有 $B_\kappa''=-\bigl((C_\kappa')^2-C_\kappa C_\kappa''\bigr)/C_\kappa^2$；对 $t>0$，(1.2) 右端第二项严格为正，故 $B_\kappa''<0$。所以 $B_\kappa$ 在 $(0,\infty)$ 上严格凹。又 $C_\kappa'(t)=\kappa D_\kappa(t)$ 在 $[0,\infty)$ 上连续（$\kappa>1$ 时 $t^{\kappa-1}\to0$），故 $B_\kappa$ 在 $[0,\infty)$ 上连续可微，其导数在 $(0,\infty)$ 上严格递减并在 $0$ 处连续，因而在 $[0,\infty)$ 上单调不增，$B_\kappa$ 在 $[0,\infty)$ 上凹。$B_\kappa(0)=\log1=0$。证毕。

**定理 1.2（引理 4.15 的核心不等式对全部 $\kappa>1$ 成立）。** 设 $\kappa>1$，$y>1$，则

$$
\bigl[(y^2+2)^\kappa-2^\kappa\bigr]\bigl[(y+1)^\kappa-1\bigr]^2>\bigl[(y^2+y+1)^\kappa-(y+1)^\kappa\bigr]^2 .
\tag{1.3}
$$

进而，以该文定义 4.2 的

$$
F^{[\kappa]}(x,a)=\frac{1}{\kappa\log x}\log\frac{(x^{a+1}-1)^\kappa-(x^a-1)^\kappa}{(x^{a+1}-x)^\kappa-(x^a-x)^\kappa}\qquad(x>1,\ a\ge1),
$$

对一切 $\kappa>1$ 与 $y>2$，有 $F^{[\kappa]}(y,2)<F^{[\kappa]}(y^2/2,1)$。

**证明。** 令 $s=1/y$、$h=1/y^2$，则

$$
(y^2+2)^\kappa-2^\kappa=y^{2\kappa}C_\kappa(2h),\qquad(y+1)^\kappa-1=y^\kappa C_\kappa(s),\qquad(y^2+y+1)^\kappa-(y+1)^\kappa=y^{2\kappa}C_\kappa(s+h),
$$

所以 (1.3) 等价于 $B_\kappa(s+h)-B_\kappa(s)<\frac12B_\kappa(2h)$。由 $y>1$ 得 $0<h<s$。四点 $h<2h$、$s<s+h$ 都在 $(0,\infty)$ 内，而严格凹函数在等长区间上的增量随起点严格递减，故 $B_\kappa(s+h)-B_\kappa(s)<B_\kappa(2h)-B_\kappa(h)$。由 $[0,\infty)$ 上的凹性与 $B_\kappa(0)=0$，$B_\kappa(h)\ge\frac12B_\kappa(2h)$，即 $B_\kappa(2h)-B_\kappa(h)\le\frac12B_\kappa(2h)$。合并即得 (1.3)。

记 $A=(y^2+2)^\kappa-2^\kappa$、$B=(y^2+y+1)^\kappa-(y+1)^\kappa$、$C=(y+1)^\kappa-1$。因式分解 $y^3-1=(y-1)(y^2+y+1)$、$y^2-1=(y-1)(y+1)$、$y^3-y=y(y-1)(y+1)$、$y^2-y=y(y-1)$ 给出

$$
F^{[\kappa]}(y^2/2,1)=\frac{\log\bigl(A/y^{2\kappa}\bigr)}{\kappa\log(y^2/2)},\qquad F^{[\kappa]}(y,2)=\frac{\log\bigl(B/(Cy^\kappa)\bigr)}{\kappa\log y}.
$$

对 $u,v>0$ 与 $\kappa>1$ 有 $(u+v)^\kappa>u^\kappa+v^\kappa$，故 $A>y^{2\kappa}$，$\log(A/y^{2\kappa})>0$。$y>2$ 时 $0<\log(y^2/2)<2\log y$，所以 $F^{[\kappa]}(y^2/2,1)>\log(A/y^{2\kappa})/(2\kappa\log y)$。由 (1.3)，$A/y^{2\kappa}>\bigl(B/(Cy^\kappa)\bigr)^2$，取对数后除以 $2\kappa\log y>0$ 即得 $F^{[\kappa]}(y^2/2,1)>F^{[\kappa]}(y,2)$。证毕。

**推论 1.3（注记 4.16）。** 对每个 $\kappa>1$ 与 $\epsilon>0$，以该文定义 4.11 的记号，$x=x_1^{[\kappa]}(\epsilon)$ 与 $x_2=x_2^{[\kappa]}(\epsilon)$ 满足 $x_2<\sqrt{2x}$。即该文引理 4.15 对全部 $\kappa>1$ 成立。

**证明。** 由该文定理 4.3，$F^{[\kappa]}$ 关于 $x$ 与 $a$ 都严格递减；$x_a$ 由 $F^{[\kappa]}(x_a,a)=\epsilon$ 定义。若 $x\le2$，则 $x_2<x_1=x\le\sqrt{2x}$。若 $x>2$，令 $y=\sqrt{2x}>2$。由定理 1.2，$F^{[\kappa]}(y,2)<F^{[\kappa]}(x,1)=\epsilon=F^{[\kappa]}(x_2,2)$，再由 $F^{[\kappa]}(\cdot,2)$ 严格递减得 $x_2<y$。证毕。

该文对 $\kappa\ge3/2$ 的限制只出现在它证明 (1.3) 时关于 $\kappa$ 的单调性步骤，上面的论证不经过该步骤。

定理 1.2 不足以把该文定理 6.1 延伸到 $\kappa\le3/2$。定理 6.1 的证明还需要正的 Euler 尾项比值 $\zeta(\kappa)\prod_{p\le x}(1-p^{-\kappa})=\exp\bigl(\Theta_\kappa(x^{1-\kappa}/\log x)\bigr)$（下界见定理 1.5 的证明，上界由 $-\log(1-u)\le2u$（$0\le u\le1/2$）与分部求和 $\sum_{p>x}p^{-\kappa}\ll_\kappa x^{1-\kappa}/\log x$ 得到） 被尺度为 $1/(\sqrt x\log x)$ 的负偏差吸收，这恰需 $\kappa>3/2$。下面的定理说明这一限制是函数族本身的性质，并非证明方法所致。

**引理 1.4（局部因子的下界）。** $\sigma^{[\kappa]}$ 可乘。对素数 $p$ 与整数 $a\ge1$，记 $r=1/p$，则

$$
\frac{\sigma^{[\kappa]}(p^a)}{p^{\kappa a}}\ \ge\ (1-r)^{-\kappa}(1-r^\kappa)\bigl(1-c_\kappa r^{a+1}\bigr),\qquad c_\kappa=\frac{\kappa}{1-2^{-\kappa}} .
\tag{1.4}
$$

**证明。** $\sigma^\kappa$ 可乘，故它与 $\mu$ 的 Dirichlet 卷积可乘，且 $\sigma^{[\kappa]}(p^a)=\sigma(p^a)^\kappa-\sigma(p^{a-1})^\kappa$。由 $\sigma(p^j)/p^j=(1-r^{j+1})/(1-r)$，

$$
(1-r)^\kappa\frac{\sigma^{[\kappa]}(p^a)}{p^{\kappa a}}=(1-r^{a+1})^\kappa-r^\kappa(1-r^a)^\kappa\ \ge\ 1-\kappa r^{a+1}-r^\kappa .
$$

这里用了 Bernoulli 不等式 $(1-u)^\kappa\ge1-\kappa u$（$\kappa\ge1$，$0\le u\le1$）与 $(1-r^a)^\kappa\le1$。又 $1-\kappa r^{a+1}-r^\kappa=(1-r^\kappa)\bigl(1-\tfrac{\kappa}{1-r^\kappa}r^{a+1}\bigr)$，而 $r\le1/2$ 给出 $\kappa/(1-r^\kappa)\le c_\kappa$。证毕。

**定理 1.5（$3/2$ 的尖锐性）。** 对每个实数 $1<\kappa<3/2$，存在无穷多个正整数 $n$ 使 (1.1) 不成立。因此，记 $E_\kappa$ 为“(1.1) 对所有充分大的 $n$ 成立”，对这些 $\kappa$：$E_\kappa$ 无条件为假；若 RH 成立，则该文定理 6.1 的结论失败；把该文定理 6.1 延伸到这样的 $\kappa$ 所得的命题 $\mathrm{RH}\Rightarrow E_\kappa$ 等价于 RH 不成立，命题 $\mathrm{RH}\Leftrightarrow E_\kappa$ 也等价于 RH 不成立；因此该文的 RH 判据不能在不先判定 RH 的前提下延伸到这些 $\kappa$。

**证明。** 若 RH 不成立，由该文定理 5.2 即得无穷多个违反。该定理对一切 $\kappa>1$ 成立，由 Robin 定理与该文引理 5.3 $\bigl(\zeta(\kappa)\sigma^{[\kappa]}(n)\bigr)^{1/\kappa}>\sigma(n)$ 推出。以下设 RH 成立。

对 $x\ge16$ 取指数 $a_p$：$\sqrt x<p\le x$ 时 $a_p=1$，$p\le\sqrt x$ 时 $a_p=\lfloor2\log x/\log p\rfloor$。令 $n_x=\prod_{p\le x}p^{a_p}$。于是 $p\le\sqrt x$ 时 $p^{a_p+1}>x^2$。由 Chebyshev 上界 $\pi(t)=O(t/\log t)$，

$$
\log n_x\le\theta(x)+2\pi(\sqrt x)\log x=\theta(x)+O(\sqrt x),\qquad
\log\log n_x\le\log\theta(x)+O\bigl(x^{-1/2}\bigr).
\tag{1.5}
$$

由引理 1.4，

$$
\frac{\sigma^{[\kappa]}(n_x)}{n_x^\kappa}\ \ge\ \prod_{p\le x}(1-p^{-1})^{-\kappa}\cdot\prod_{p\le x}(1-p^{-\kappa})\cdot\prod_{\sqrt x<p\le x}\bigl(1-c_\kappa p^{-2}\bigr)\cdot\prod_{p\le\sqrt x}\bigl(1-c_\kappa x^{-2}\bigr).
$$

对充分大的 $x$，各因子 $c_\kappa p^{-2}$、$c_\kappa x^{-2}$ 不超过 $1/2$，由 $\log(1-u)\ge-2u$（$0\le u\le1/2$），最后两个乘积至少为

$$
\exp\Bigl(-2c_\kappa\sum_{p>\sqrt x}p^{-2}-2c_\kappa x^{-3/2}\Bigr)=\exp\Bigl(-O_\kappa\Bigl(\frac{1}{\sqrt x\log x}\Bigr)\Bigr).
$$

对第二个乘积，由 $-\log(1-u)\ge u$，$\prod_{p\le x}(1-p^{-\kappa})=\zeta(\kappa)^{-1}\prod_{p>x}(1-p^{-\kappa})^{-1}\ge\zeta(\kappa)^{-1}\exp\bigl(\sum_{x<p\le2x}p^{-\kappa}\bigr)$。由 Chebyshev 下界 $\pi(2x)-\pi(x)\ge c_0x/\log x$（$c_0>0$ 为绝对常数，$x$ 充分大），

$$
\zeta(\kappa)\prod_{p\le x}(1-p^{-\kappa})\ \ge\ \exp\Bigl(c_02^{-\kappa}\frac{x^{1-\kappa}}{\log x}\Bigr).
$$

对第一个乘积，在 RH 下，Schoenfeld [Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II, Math. Comp. 30 (1976)] 给出 $\theta(x)=x+O(\sqrt x\log^2x)$ 与 $\sum_{p\le x}1/p=\log\log x+M+O(\log x/\sqrt x)$，其中 $M$ 为 Mertens 常数。由 $\sum_p\bigl(\log(1-1/p)^{-1}-1/p\bigr)=\gamma-M$，且其 $p>x$ 部分为 $O(1/x)$，得

$$
\prod_{p\le x}(1-p^{-1})^{-1}=e^\gamma\log x\cdot\exp\bigl(O(\log x/\sqrt x)\bigr),
\qquad
\log\theta(x)=\log x\cdot\exp\bigl(O(\log x/\sqrt x)\bigr).
$$

合并以上估计与 (1.5)，

$$
\frac{\zeta(\kappa)\,\sigma^{[\kappa]}(n_x)}{(e^\gamma n_x\log\log n_x)^\kappa}\ \ge\ \exp\Bigl(c_02^{-\kappa}\frac{x^{1-\kappa}}{\log x}-O_\kappa\Bigl(\frac{\log x}{\sqrt x}\Bigr)\Bigr).
$$

由于 $\kappa<3/2$，两项之比 $x^{3/2-\kappa}/\log^2x\to\infty$，故对充分大的 $x$ 右端大于 $1$，即 $n_x$ 违反 (1.1)。又 $n_x\to\infty$，所以违反有无穷多次。两种情形合并即得定理。证毕。

**注记 1.6（端点与倒数族）。**
- **端点 $\kappa=3/2$。** 此时 Euler 尾项与局部因子 $p^{-2}$ 层的损失都是 $x^{-1/2}/\log x$ 量级，而定理 1.5 的证明对 RH 下 Mertens 与 $\theta$ 的修正只用了上界 $O(\log x/\sqrt x)$，它比前两项大 $\log^2x$ 倍，所以该论证在 $\kappa=3/2$ 不能判定符号。$\kappa=3/2$ 的情形记为 open。
- **倒数族。** Molnar [Reciprocal LCM powers and Robin's criterion, arXiv:2610.12816v1] 研究倒数族 $\sigma_{-1}^{[\kappa]}(n)=\sum_{d\mid n}\mu(d)\sigma_{-1}(n/d)^\kappa$。该文的归一化为 $\widehat\rho^{[\kappa]}(n)=\bigl(n\,\sigma_{-1}^{[\kappa]}(n)/\kappa^{\omega(n)}\bigr)^{1/(\kappa-1)}$，对每个整数 $n>1$，它关于 $\kappa$ 严格递增并趋于 $\sigma_{-1}(n)$。由此，对任一无界参数集 $K\subset(1,\infty)$，RH 等价于 $\widehat\rho^{[\kappa]}(n)<e^\gamma\log\log n$ 对一切 $n>5040$ 与 $\kappa\in K$ 成立；而在固定的有界参数区间上，该不等式无条件地终于成立。这些结论针对倒数族的归一化，与 (1.1) 是不同的不等式。定理 1.5 说明原函数族的 (1.1) 在 $(1,3/2)$ 上的行为与之相反：Euler 尾项产生的正偏差使 (1.1) 无条件地无穷多次失败。

**范围。** 外部输入如下：
- Fan–Kobayashi–Molnar 的定义、其定理 4.3（$F^{[\kappa]}$ 的单调性）、定理 5.2 与引理 5.3（对一切 $\kappa>1$）；
- Robin 定理；
- RH 下 Schoenfeld 的 $\theta$ 与 Mertens 估计；
- Chebyshev 上下界。

本仓推导的是：恒等式 (1.2)、定理 1.2 与推论 1.3（回答该文注记 4.16），局部下界 (1.4)，以及定理 1.5（对 $1<\kappa<3/2$ 回答该文第 8 节关于定理 6.1 的提问：$E_\kappa$ 无条件为假，把定理 6.1 延伸到这些 $\kappa$ 所得的命题等价于 RH 不成立）。所查范围（该文正文、Molnar 2026 的后续论文、arXiv 标题检索“Robin criterion”）内未见这两个问题的解答。

## 追加锚（本行以下为增补区）

## 2. 端点 κ = 3/2

本节证明 (1.1) 在 $\kappa=3/2$ 处也对无穷多个 $n$ 不成立。注记 1.6 曾把这一端点记为 open，本节将它结算。记 $E_\kappa$ 为“(1.1) 对所有充分大的 $n$ 成立”。结合 Fan–Kobayashi–Molnar 定理 1.5、本卷定理 1.5 与本节定理 2.3，可得对一切 $\kappa>1$，$E_\kappa\iff(\mathrm{RH}\wedge\kappa>3/2)$。

记 $P(x)=\prod_{p\le x}(1-p^{-1})^{-1}$，$f(x)=e^\gamma\log\theta(x)/P(x)$。按 Nicolas [Small values of the Euler function and the Riemann hypothesis, Acta Arith. 155 (2012), 311–321; arXiv:1202.0729] 的记号，令

$$
W(x)=\sum_\rho\frac{x^{i\Im\rho}}{\rho(1-\rho)},\qquad \beta=\sum_\rho\frac1{\rho(1-\rho)}=2+\gamma-\log\pi-2\log2=0.0461914\ldots,
$$

其中 $\rho$ 遍历 $\zeta$ 的非平凡零点。RH 下 $|W(x)|\le\beta$。

**引理 2.1（Nicolas）。** 设 RH 成立，则对 $x\ge10^9$，

$$
\log\frac{P(x)}{e^\gamma\log\theta(x)}=-\log f(x)\ \ge\ \frac{2+W(x)}{\sqrt x\log x}-\frac{2.062}{\sqrt x\log^2x}.
$$

**证明。** 这是 Nicolas 上述论文命题 2.1 中不等式 (2.16) 的右半部分，即 $\log f(x)\le-(2+W(x))/(\sqrt x\log x)+2.062/(\sqrt x\log^2x)$，两边取负号即得。证毕。

**引理 2.2（局部因子与 Euler 尾项）。** 记 $\kappa=3/2$，$r=1/p$。
- 对素数 $p$ 与整数 $a\ge1$，$\dfrac{\sigma^{[\kappa]}(p^a)}{p^{\kappa a}}\ge(1-r)^{-\kappa}(1-r^\kappa)\Bigl(1-\dfrac{\kappa}{1-r^\kappa}r^{a+1}\Bigr)$。
- $x\to\infty$ 时，$\sum_{p>x}-\log(1-p^{-3/2})=\dfrac{2+o(1)}{\sqrt x\log x}$。
- $y\to\infty$ 时，$\sum_{p>y}p^{-2}=\dfrac{1+o(1)}{y\log y}$。

**证明。**
- 第一式就是引理 1.4 证明中的中间不等式 $(1-r)^\kappa\sigma^{[\kappa]}(p^a)/p^{\kappa a}\ge1-\kappa r^{a+1}-r^\kappa$。
- 第二式：$-\log(1-u)=u+O(u^2)$，$\sum_{p>x}p^{-3}=O(x^{-2})$；由素数定理分部求和，$\sum_{p>x}p^{-3/2}=\int_x^\infty t^{-3/2}(\log t)^{-1}\,dt\,(1+o(1))=(2+o(1))/(\sqrt x\log x)$。
- 第三式同理。

证毕。

**定理 2.3（端点 $\kappa=3/2$）。** 存在无穷多个正整数 $n$ 使

$$
\sigma^{[3/2]}(n)\ >\ \frac{(e^\gamma n\log\log n)^{3/2}}{\zeta(3/2)} .
$$

更确切地，设 RH 成立，取 $y=\sqrt{2x}$、$z=x^{1/3}$ 及

$$
n_x=\prod_{p\le z}p^{\lfloor2\log x/\log p\rfloor}\prod_{z<p\le y}p^{2}\prod_{y<p\le x}p ,
$$

则

$$
\log\frac{\zeta(3/2)\,\sigma^{[3/2]}(n_x)}{(e^\gamma n_x\log\log n_x)^{3/2}}\ \ge\ \frac{5-3\sqrt2+\tfrac32W(x)+o(1)}{\sqrt x\log x}\ \ge\ \frac{5-3\sqrt2-\tfrac32\beta+o(1)}{\sqrt x\log x},
$$

其中 $5-3\sqrt2-\tfrac32\beta=0.68807\ldots>0$。

**证明。** 若 RH 不成立，由 Fan–Kobayashi–Molnar 定理 5.2（对一切 $\kappa>1$）即得。以下设 RH 成立，记 $\kappa=3/2$，$a_p$ 为 $n_x$ 中 $p$ 的指数，$x$ 充分大。由可乘性与 $\zeta(\kappa)=\prod_p(1-p^{-\kappa})^{-1}$，有恒等式

$$
\log\frac{\zeta(\kappa)\sigma^{[\kappa]}(n_x)}{(e^\gamma n_x\log\log n_x)^\kappa}=T+M+Q,
$$

其中

$$
T=\sum_{p>x}-\log(1-p^{-\kappa}),\qquad
M=\kappa\log\frac{P(x)}{e^\gamma\log\log n_x},\qquad
Q=\sum_{p\le x}\log\frac{\sigma^{[\kappa]}(p^{a_p})}{p^{\kappa a_p}(1-p^{-1})^{-\kappa}(1-p^{-\kappa})}.
$$

由 $-\log(1-u)\ge u$ 与引理 2.2 的第二式的证明，$T\ge\sum_{p>x}p^{-3/2}=(2+o(1))/(\sqrt x\log x)$。

*估计 $Q$。* 只需下界。由引理 2.2 的第一式，记 $u_p=\kappa p^{-(a_p+1)}/(1-p^{-\kappa})$，$x$ 充分大时 $u_p\le1/2$。由 $\log(1-u)\ge-u-u^2$（$0\le u\le1/2$），$Q$ 的每一项不小于 $-u_p-u_p^2$。按指数分三段：
- $y<p\le x$（$a_p=1$）：$u_p=\kappa p^{-2}(1+O(y^{-3/2}))$，$u_p^2=O(p^{-4})$，故这一段之和不小于 $-\kappa(1+o(1))\sum_{p>y}p^{-2}$。由引理 2.2 的第三式，它等于 $-\tfrac32(1+o(1))/(y\log y)$。由于 $y\log y=\sqrt{2x}\cdot\tfrac12\log(2x)=(1+o(1))\sqrt x\log x/\sqrt2$，这一段不小于 $-(3\sqrt2/2+o(1))/(\sqrt x\log x)$。
- $z<p\le y$（$a_p=2$）：$u_p+u_p^2=O(p^{-3})$，这一段不小于 $-O(\sum_{p>z}p^{-3})=-O(x^{-2/3})$。
- $p\le z$：$p^{a_p+1}>x^2$，故 $u_p+u_p^2=O(x^{-2})$，这一段不小于 $-O(\pi(z)x^{-2})$。

后两段都是 $o(1/(\sqrt x\log x))$，所以 $Q\ge-(3\sqrt2/2+o(1))/(\sqrt x\log x)$。

*估计 $M$。* 先估计 $\log n_x$：

$$
\log n_x\le\theta(x)+\theta(y)+2\pi(z)\log x .
$$

RH 下 $\theta(t)=t+O(\sqrt t\log^2t)$，故 $\theta(y)=\sqrt2\sqrt x+O(x^{1/4}\log^2x)$。又 $\pi(z)\log x=O(x^{1/3})$，且 $\theta(x)=x(1+o(1))$，所以

$$
\log\log n_x\le\log\theta(x)+\frac{\sqrt2+o(1)}{\sqrt x},\qquad
\log\log\log n_x\le\log\log\theta(x)+\frac{\sqrt2+o(1)}{\sqrt x\log x},
$$

后一式用了 $\log\theta(x)=\log x+o(1)$。再由引理 2.1，

$$
M=\kappa\Bigl(\log\frac{P(x)}{e^\gamma\log\theta(x)}-\log\frac{\log\log n_x}{\log\theta(x)}\Bigr)\ \ge\ \frac32\cdot\frac{2+W(x)-\sqrt2+o(1)}{\sqrt x\log x}.
$$

*合并。* 三项相加，

$$
T+M+Q\ \ge\ \frac{2+3+\tfrac32W(x)-\tfrac32\sqrt2-\tfrac32\sqrt2+o(1)}{\sqrt x\log x}=\frac{5-3\sqrt2+\tfrac32W(x)+o(1)}{\sqrt x\log x}.
$$

由 $|W(x)|\le\beta$ 得到所述下界。它对充分大的 $x$ 为正，而 $n_x\to\infty$，故 (1.1) 在 $\kappa=3/2$ 对无穷多个 $n$ 不成立。两种情形合并即得定理。证毕。

**推论 2.4（Fan–Kobayashi–Molnar 判据的精确参数域）。** 记 $E_\kappa$ 为“(1.1) 对所有充分大的 $n$ 成立”。对一切实数 $\kappa>1$，

$$
E_\kappa\iff\bigl(\mathrm{RH}\wedge\kappa>3/2\bigr).
$$

特别地：
- 对 $\kappa>3/2$，$E_\kappa$ 是 RH 的等价判据；
- 对 $1<\kappa\le3/2$，$E_\kappa$ 无条件为假，命题“$\mathrm{RH}\iff E_\kappa$”等价于 RH 不成立，因此不能用来验证 RH。

**证明。**
- $\kappa>3/2$：由 Fan–Kobayashi–Molnar 定理 1.5，$E_\kappa\iff\mathrm{RH}$。
- $1<\kappa<3/2$：由本卷定理 1.5，$E_\kappa$ 为假。
- $\kappa=3/2$：由定理 2.3，$E_\kappa$ 为假。

三种情形合起来即为所述等价。后半句是命题逻辑：$E_\kappa$ 为假时，$(\mathrm{RH}\iff E_\kappa)\iff\neg\mathrm{RH}$。证毕。

**注记 2.5（机理与对注记 1.6 的更正）。** 注记 1.6 的端点论断由本节取代：$\kappa=3/2$ 不再是 open。在该端点，主项 $1/(\sqrt x\log x)$ 的系数由四部分组成：

| 来源 | 系数 |
|---|---|
| Euler 尾项 | $+2$ |
| Mertens 乘积相对 $e^\gamma\log\theta(x)$ 的偏差（Nicolas） | $+\tfrac32(2+W)$ |
| $\log\log n$ 因指数 2 层而产生的移位 | $-\tfrac32\sqrt2$ |
| 指数 1 层的局部损失 | $-\tfrac32\sqrt2$ |

两项代价之和 $\tfrac32 c+3/c$ 在分层位置 $y=c\sqrt x$ 取 $c=\sqrt2$ 时最小，这与该文引理 4.13 中 $\kappa$-巨丰数的分层 $x_2\sim\sqrt{2x}$ 一致。此时系数为 $5-3\sqrt2+\tfrac32W(x)$，振荡部分的幅度 $\tfrac32\beta\approx0.069$ 小于非振荡部分 $5-3\sqrt2\approx0.757$。因此结论不依赖零点的分布细节，只用到 RH 下 $|W|\le\beta$。

**范围。** 外部输入如下：
- Nicolas 2012 命题 2.1（RH 下显式）；
- Fan–Kobayashi–Molnar 定理 1.5、5.2；
- RH 下 $\theta(t)=t+O(\sqrt t\log^2t)$；
- 素数定理与 Chebyshev 上界。

本仓推导的是定理 2.3、推论 2.4 及注记 2.5 的分解。在所查范围（该文第 8 节把阈值问题列为 future work；Molnar arXiv:2610.12816v1；arXiv 标题检索）内未见此结论，本节不主张文献优先权。

## 追加锚（本行以下为增补区）

## 3. κ-巨丰数临界值的碰撞

Fan–Kobayashi–Molnar 定义 4.2 与定义 4.19 对 $\kappa>1$、$x>1$、$a\ge1$ 令

$$
F_\kappa(x,a)=\frac{1}{\kappa\log x}\log\frac{(x^{a+1}-1)^\kappa-(x^a-1)^\kappa}{(x^{a+1}-x)^\kappa-(x^a-x)^\kappa},\qquad E_p^{[\kappa]}=\{F_\kappa(p,j):j\in\mathbb Z_{>0}\}.
$$

其第 8 节提出三问：对固定素数 $p\ne q$，能否找到 $\kappa$ 使 $E_p^{[\kappa]}\cap E_q^{[\kappa]}\ne\varnothing$；对大的 $\kappa$ 是否成立；对整数 $\kappa$ 是否成立。记 $\mathcal S_{p,q}=\{\kappa>1:E_p^{[\kappa]}\cap E_q^{[\kappa]}\ne\varnothing\}$。本节证明 $\mathcal S_{p,q}$ 在 $(1,\infty)$ 中稠密、无界，且为可数零测集。对整数 $\kappa$，本节无条件地证明超越性与有限性结论，并在一个超越数论猜想下完全排除整数碰撞。

**引理 3.1（首项展开）。** 固定 $x>1$ 与紧区间 $I\subset(1,\infty)$。$a\to\infty$ 时，对 $\kappa\in I$ 一致地有

$$
F_\kappa(x,a)=c_\kappa(x)\,x^{-a}+O_{x,I}(x^{-2a}),\qquad c_\kappa(x)=\frac{(x-1)(x^{\kappa-1}-1)}{(x^\kappa-1)\log x}.
$$

对 $\kappa$ 的任意固定阶导数同样成立。

**证明。** 令 $t=x^{-a}\in(0,1/x]$，则

$$
F_\kappa(x,a)=\mathscr F(\kappa,t):=\frac{1}{\kappa\log x}\log\frac{N(\kappa,t)}{M(\kappa,t)},\qquad N=(x-t)^\kappa-(1-t)^\kappa,\quad M=x^\kappa(1-t)^\kappa-(1-xt)^\kappa .
$$

各项乘以 $x^{-(a+1)\kappa}$ 后约去即得此式。$N(\kappa,0)=M(\kappa,0)=x^\kappa-1>0$，$\partial_tN(\kappa,0)=\kappa(1-x^{\kappa-1})$，$\partial_tM(\kappa,0)=\kappa(x-x^\kappa)$。于是

$$
\partial_t\mathscr F(\kappa,0)=\frac{1}{\kappa\log x}\cdot\frac{\kappa(1-x^{\kappa-1})-\kappa(x-x^\kappa)}{x^\kappa-1}=c_\kappa(x).
$$

在 $I\times[0,t_0]$（$t_0$ 足够小，使各底数为正）上 $\mathscr F$ 实解析，且 $\mathscr F(\kappa,0)=0$。对 $t$ 作带余项的 Taylor 展开，余项及其各阶 $\kappa$ 导数在紧集上一致有界，即得结论。证毕。

**引理 3.2（首项系数比的单调性）。** 设 $1<p<q$，$R(\kappa)=c_\kappa(p)/c_\kappa(q)$。则 $R$ 在 $(1,\infty)$ 上严格递增，且 $R(1^+)=1$，$R(\infty)=\dfrac{(p-1)q\log q}{(q-1)p\log p}>1$。

**证明。** 令 $s=\log x$。则 $c_\kappa(x)=\dfrac{1-e^{-s}}{s}\cdot\dfrac{1-e^{-(\kappa-1)s}}{1-e^{-\kappa s}}$，因此

$$
\partial_\kappa\log c_\kappa(x)=\frac{s}{e^{(\kappa-1)s}-1}-\frac{s}{e^{\kappa s}-1}=\int_{\kappa-1}^{\kappa}\Bigl(\frac{s}{2\sinh(vs/2)}\Bigr)^2dv .
$$

第二个等号成立，因为 $\frac{d}{dv}\frac{s}{e^{vs}-1}=-\frac{s^2e^{vs}}{(e^{vs}-1)^2}=-\bigl(\frac{s}{2\sinh(vs/2)}\bigr)^2$。函数 $z\mapsto z/\sinh z$ 在 $(0,\infty)$ 上严格递减：其导数的分子为 $\sinh z-z\cosh z$，在 $0$ 处为 $0$，导数为 $-z\sinh z<0$。故对每个 $v>0$，被积函数 $\bigl(\frac{1}{v}\cdot\frac{vs/2}{\sinh(vs/2)}\bigr)^2$ 关于 $s$ 严格递减。由 $\log p<\log q$ 得 $\partial_\kappa\log c_\kappa(p)>\partial_\kappa\log c_\kappa(q)$，即 $(\log R)'>0$。

端点值：$\kappa\to1^+$ 时 $c_\kappa(x)\sim(\kappa-1)$，与 $x$ 无关，故 $R\to1$；$\kappa\to\infty$ 时 $c_\kappa(x)\to(x-1)/(x\log x)$。最后，$x\mapsto x\log x/(x-1)$ 在 $(1,\infty)$ 上严格递增，其导数为 $(x-1-\log x)/(x-1)^2>0$，故 $R(\infty)>1$。证毕。

**定理 3.3（碰撞参数的稠密性）。** 设 $p\ne q$ 为素数，$1<\alpha<\beta<\infty$，$M\ge1$。则存在整数 $i,j\ge M$ 与 $\kappa\in(\alpha,\beta)$，使 $F_\kappa(p,i)=F_\kappa(q,j)$。特别地，$\mathcal S_{p,q}$ 在 $(1,\infty)$ 中稠密且无界，每个非空开区间都含 $\mathcal S_{p,q}$ 的无穷多个点。

**证明。** 不妨 $p<q$。令 $h=\log R$，由引理 3.2 有 $h(\alpha)<h(\beta)$。取开区间 $J$ 使 $\overline J\subset(h(\alpha),h(\beta))$。$\log p/\log q$ 为无理数（唯一分解），故 $\{i\log p\bmod\log q:i\ge M\}$ 在 $[0,\log q)$ 中稠密。于是存在任意大的 $i$ 与相应的整数 $j$，使 $d_{i,j}:=i\log p-j\log q\in J$；$i$ 充分大时 $j\ge M$。由引理 3.1，在 $[\alpha,\beta]$ 上一致地有

$$
\log\frac{F_\kappa(p,i)}{F_\kappa(q,j)}=h(\kappa)-d_{i,j}+O(p^{-i}+q^{-j}).
$$

$i,j$ 充分大时，右端在 $\kappa=\alpha$ 处为负、在 $\kappa=\beta$ 处为正。$F_\kappa$ 关于 $\kappa$ 连续，由介值定理即得交点。把 $(\alpha,\beta)$ 分成可数多个互不相交的开子区间并分别应用本结论，得到无穷多个点。证毕。

**定理 3.4（碰撞参数集可数）。** 对素数 $p\ne q$，$\mathcal S_{p,q}$ 可数，因而 Lebesgue 测度为零。对所有素数对取并仍为可数零测集，所以对几乎每个 $\kappa>1$，各 $E_p^{[\kappa]}$ 两两不交。

**证明。** 固定 $i,j$，令 $D(\kappa)=F_\kappa(p,i)-F_\kappa(q,j)$，它在 $(1,\infty)$ 上实解析。只需证 $D\not\equiv0$，此时其零点离散，而 $(i,j)$ 只有可数多对。

记 $r_{x,a}=(x^a-1)/(x^{a+1}-1)$，$s_{x,a}=(x^a-x)/(x^{a+1}-x)$，有 $0\le s_{x,a}<r_{x,a}<1$。分出最大幂得

$$
F_\kappa(x,a)=F_\infty(x,a)+\frac{\log(1-r_{x,a}^\kappa)-\log(1-s_{x,a}^\kappa)}{\kappa\log x},\qquad F_\infty(x,a)=\frac{1}{\log x}\log\frac{x^{a+1}-1}{x^{a+1}-x}.
$$

因此 $\kappa\to\infty$ 时 $F_\infty(x,a)-F_\kappa(x,a)\sim r_{x,a}^\kappa/(\kappa\log x)$。若 $D\equiv0$，取极限得 $F_\infty(p,i)=F_\infty(q,j)$，于是两侧余项在 $\kappa\to\infty$ 时也相等：
- 若 $r_{p,i}\ne r_{q,j}$，两侧指数衰减率不同，不可能相等；
- 若 $r_{p,i}=r_{q,j}$，比较系数得 $1/\log p=1/\log q$，与 $p\ne q$ 矛盾。

证毕。

**命题 3.5（整数参数下临界值的超越性）。** 设整数 $k\ge2$、素数 $p$、整数 $a\ge1$。令 $S_a=(p^{a+1}-1)^k-(p^a-1)^k$（$S_0=(p-1)^k$），$R_k(p,a)=S_a/(p^kS_{a-1})\in\mathbb Q_{>1}$，则 $p^{kF_k(p,a)}=R_k(p,a)$。除 $F_2(2,1)=1/2$ 外，$F_k(p,a)$ 均为超越数。

**证明。** 设 $t=kF_k(p,a)$。

先证 $v_p(R_k(p,a))<0$，例外情形单列：
- **$p$ 为奇素数。** $p\mid(p^{a+1}-1)-(p^a-1)$ 且 $p$ 不整除两底数。由提升指数引理，$v_p(S_a)=a+v_p(k)$（$a\ge1$），而 $v_p(S_0)=0$。故 $v_p(R_k(p,1))=1+v_p(k)-k$，$v_p(R_k(p,a))=1-k$（$a\ge2$），两者都为负，因为 $v_p(k)\le\log_pk<k-1$。
- **$p=2$。** 直接计算二进赋值：$v_2(R_k(2,a))$ 在 $a\ge3$ 时为 $1-k$；在 $a=2$ 时为 $1-k$（$k$ 奇）或 $-k$（$k$ 偶）；在 $a=1$ 时为 $1-k$（$k$ 奇）或 $2+v_2(k)-k$（$k$ 偶）。这些值除 $(k,a)=(2,1)$、$(4,1)$ 外都为负。两个例外处 $R_2(2,1)=2$、$R_4(2,1)=5$。

再推出超越性。若 $t=m/n$ 为既约有理数且 $p^t\in\mathbb Q$，则 $n=1$，于是 $v_p(p^t)=t>0$，与赋值为负矛盾，故 $t$ 为无理数。若 $t$ 为代数无理数，由 Gelfond–Schneider 定理 $p^t$ 为超越数，矛盾。故 $t$ 超越。

两个例外：$(k,a)=(2,1)$ 时 $t=1$，即 $F_2(2,1)=1/2$；$(k,a)=(4,1)$ 时 $2^t=5$，$t=\log5/\log2$ 由 Gelfond–Schneider 定理为超越数。证毕。

**定理 3.6（整数参数：条件结论、三重碰撞与有限性）。** 设整数 $k\ge2$。
- (i) 若 Alaoglu–Erdős 猜想成立（对不同素数 $p,q$，$p^t,q^t\in\mathbb Q$ 蕴含 $t\in\mathbb Z$），则对一切不同素数 $p,q$ 有 $E_p^{[k]}\cap E_q^{[k]}=\varnothing$。四指数猜想蕴含该猜想。
- (ii) 无条件地，不存在三个不同素数 $p,q,r$ 使 $E_p^{[k]}\cap E_q^{[k]}\cap E_r^{[k]}\ne\varnothing$。
- (iii) 无条件地，对固定的不同素数 $p,q$，满足 $F_k(p,i)=F_k(q,j)$ 的 $(i,j)$ 只有有限多对。

**证明。** 碰撞 $F_k(p,i)=F_k(q,j)=\epsilon$ 给出 $t=k\epsilon$ 使 $p^t,q^t\in\mathbb Q$。由命题 3.5，$t$ 超越；在至多一个例外 $t=1$（来自 $F_2(2,1)$）的情形，另一侧 $q^{1}$ 须等于 $R_2(q,j)$，而 $v_q(R_2(q,j))<0$，矛盾。

(i) 碰撞会给出不同素数 $p,q$ 与非整数 $t$，使 $p^t,q^t\in\mathbb Q$，与猜想矛盾。若四指数猜想成立，取 $(\log p,\log q)$ 与 $(1,t)$（分别 $\mathbb Q$-线性无关），四个指数 $p,q,p^t,q^t$ 均为有理数，与猜想矛盾。

(ii) 取三个 $\mathbb Q$-线性无关的数 $\log p,\log q,\log r$ 与两个线性无关的数 $1,t$。六个值 $e^{x_ry_s}$ 全为有理数，与六指数定理矛盾。

(iii) 交换 $p,q$ 使 $p$ 为奇素数。$i=1$ 至多对应一个 $j$，因为 $F_k(q,\cdot)$ 严格递减（该文定理 4.3）。对 $i\ge2$ 的碰撞，记 $t=kF_k(p,i)$，有 $v_p(p^t)=c:=1-k$。若无此类碰撞，结论成立；否则固定其中一个 $t_0$。对另一个 $t$：
- 若 $1,t_0,t$ 在 $\mathbb Q$ 上线性无关，以 $\log p,\log q$ 为两行、$1,t_0,t$ 为三列，六个值全为有理数，与六指数定理矛盾。故 $t=r+st_0$，$r,s\in\mathbb Q$。
- 取 $N$ 使 $Nr,Ns\in\mathbb Z$，由 $p^{Nt}=p^{Nr}(p^{t_0})^{Ns}$ 比较 $p$ 进赋值得 $c=r+sc$，即 $t=c+s(t_0-c)$。
- 令 $A=p^{t_0-c}\in\mathbb Q_{>0}\setminus\{1\}$，$d=\gcd\{|v_\ell(A)|:v_\ell(A)\ne0\}$。由 $A^s=p^{t-c}\in\mathbb Q$ 与唯一分解，$s$ 的既约分母整除 $d$。故所有碰撞的 $t$ 属于离散集 $c+\frac{t_0-c}{d}\mathbb Z$。
- 又 $0<t\le kF_k(p,2)$，故这样的 $t$ 只有有限多个。每个 $t$ 至多对应一个 $i$ 与一个 $j$。

证毕。

**注记 3.7（对第 8 节三问的回答与边界）。**
- **能否找到 κ：** 能，且碰撞参数在 $(1,\infty)$ 中稠密（定理 3.3）。
- **大的 κ：** 存在任意大的碰撞参数；但碰撞参数集为可数零测集，不存在 $K$ 使每个 $\kappa>K$ 都碰撞，也不存在 $K$ 使每个 $\kappa>K$ 都不碰撞（定理 3.3、3.4）。
- **整数 κ：** 在 Alaoglu–Erdős 猜想下没有碰撞；无条件地，没有三重碰撞，且固定素数对只有有限多对碰撞指数（定理 3.6）。本节未无条件地排除或构造整数碰撞。

该文例 4.21（$\kappa=2.9568\ldots$ 时 $F(2,5)=F(5,2)$）给出了 $\mathcal S_{2,5}$ 的一个具体示例。

**范围。** 外部输入如下：
- 该文定义 4.2、定理 4.3（单调性）；
- Gelfond–Schneider 定理；
- 六指数定理；
- 提升指数引理；
- Alaoglu–Erdős（Trans. AMS 56 (1944)）提出的猜想；
- 四指数猜想。

本仓推导的是引理 3.1、3.2，定理 3.3、3.4、3.6 与命题 3.5。在所查范围（该文第 8 节、Molnar arXiv:2610.12816v1、arXiv 检索）内未见对这三问的解答，本节不主张文献优先权。

## 追加锚（本行以下为增补区）

## 4. 层边界不等式对 ℓ 的一致性

Fan–Kobayashi–Molnar 注记 5.5 指出：Robin 对其定理 5.1 的证明依赖不等式

$$
x_\ell>x^{1/\ell}\qquad(\ell\ge2),
\tag{4.1}
$$

其中 $x_\ell=x_\ell^{[\kappa]}(\epsilon)$ 由 $F^{[\kappa]}(x_\ell,\ell)=\epsilon$ 定义，$x=x_1$。该文由其引理 4.12 得到：对固定的 $\kappa>1$ 与固定的 $\ell\ge2$，(4.1) 对充分大的 $x$ 成立。作者写道 “we have been unable to establish this inequality uniformly in ℓ”。其附录在 $\kappa=2$ 时证明了：对一切 $x\ge2$ 与一切 $\ell$，有非严格不等式 $x_\ell\ge x^{1/\ell}$，且在 $x=2$ 处等号成立；由此 $x>2$ 时 (4.1) 严格成立。本节证明：对每个 $\kappa>1$，存在只依赖 $\kappa$ 的阈值，使 (4.1) 在阈值之上对一切 $\ell\ge2$ 同时成立。

沿用引理 1.1 的记号 $C(s)=(1+s)^\kappa-s^\kappa$、$B=\log C$，并令 $\varphi(s)=sB'(s)$（$s>0$）。

**引理 4.1（层比的增量表示）。** 设 $\kappa>1$，$y>1$，$t=1/y$，整数 $\ell\ge1$，$\sigma_m=t+t^2+\cdots+t^m$（$\sigma_0=0$），则

$$
\kappa\log y\cdot F^{[\kappa]}(y,\ell)=B(\sigma_\ell)-B(\sigma_{\ell-1}),\qquad \kappa\ell\log y\cdot F^{[\kappa]}(y^\ell,1)=B(t^\ell).
$$

**证明。** 把定义 4.2 中分子、分母的各项除以 $y^{(\ell+1)\kappa}$，得到分子 $=(1-t^{\ell+1})^\kappa-(t-t^{\ell+1})^\kappa$，分母 $=(1-t^\ell)^\kappa-(t-t^\ell)^\kappa$。两组底数之差都是 $1-t$，又 $(t-t^{m+1})/(1-t)=\sigma_m$，所以分子 $=(1-t)^\kappa C(\sigma_\ell)$，分母 $=(1-t)^\kappa C(\sigma_{\ell-1})$，第一式得证。第二式：$\bigl((y^\ell+1)^\kappa-1\bigr)/y^{\ell\kappa}=(1+t^\ell)^\kappa-t^{\ell\kappa}=C(t^\ell)$。证毕。

**引理 4.2（$B$ 与 $\varphi$ 的性质）。** 设 $\kappa>1$。
- $B(0)=0$。
- $B'(0^+)=\kappa$。
- $B'$ 在 $(0,\infty)$ 上严格递减。
- $0<B(h)<\kappa h$（$h>0$）。
- $\varphi$ 在 $(0,\infty)$ 上严格递增。
- 记 $r=s/(1+s)$，则 $\varphi(s)\ge\kappa(r-r^\kappa)$。

**证明。** 前三条由引理 1.1 及 $C'(0)=\kappa$ 得到。第四条：$B(h)>0$ 因为 $C(h)>1$；$B(h)<\kappa h$ 来自严格凹函数位于其在 0 处切线之下。第五条：$\varphi(s)=\kappa\bigl(1-\frac{1-r}{1-r^\kappa}\bigr)$，而 $\frac{1-r^\kappa}{1-r}$ 是凸函数 $r\mapsto r^\kappa$ 在 $[r,1]$ 上的割线斜率，关于 $r$ 严格递增；$r$ 又关于 $s$ 严格递增。这正是定理 1.2 的 Lean 形式化中弹性单调性所证的内容。第六条：$\varphi(s)=\kappa\frac{r-r^\kappa}{1-r^\kappa}\ge\kappa(r-r^\kappa)$。证毕。

**定理 4.3（(4.1) 对 ℓ 一致）。** 设 $\kappa>1$，令

$$
u_0(\kappa)=\max\Bigl(6,\ \bigl(2^{\kappa+1.01}\bigr)^{1/(\kappa-1)}\Bigr),\qquad X(\kappa)=e^{u_0(\kappa)} .
$$

则对一切实数 $x\ge X(\kappa)$ 与一切整数 $\ell\ge2$，有 $F^{[\kappa]}(x^{1/\ell},\ell)>F^{[\kappa]}(x,1)$。因此在该文定理 4.3 的单调性下，若 $x=x_1^{[\kappa]}(\epsilon)\ge X(\kappa)$，则对一切 $\ell\ge2$ 有 $x_\ell^{[\kappa]}(\epsilon)>x^{1/\ell}$。

**证明。** 记 $u=\log x$、$y=x^{1/\ell}$、$t=1/y$、$h=t^\ell=e^{-u}$。由引理 4.1，所需不等式等价于

$$
\ell\bigl(B(\sigma_\ell)-B(\sigma_{\ell-1})\bigr)>B(h).
$$

(1) **凹性。** $\sigma_\ell-\sigma_{\ell-1}=h$，且 $B'$ 递减，故左端 $\ge\ell hB'(\sigma_\ell)$。

(2) **$\sigma_\ell$ 的上界。** $\sigma_\ell=\frac{t(1-t^\ell)}{1-t}=\frac{1-h}{y-1}$，而 $y-1=e^{u/\ell}-1\ge u/\ell$，故 $\sigma_\ell\le w:=\ell(1-h)/u$。

(3) **化为弹性。** 由 $B'$ 递减，$\ell B'(\sigma_\ell)\ge\ell B'(w)=\ell\varphi(w)/w=\frac{u}{1-h}\varphi(w)$。

(4) **消去 $\ell$。** $\ell\ge2$ 给出 $w\ge s_0:=2(1-h)/u$，由 $\varphi$ 递增，

$$
\ell\bigl(B(\sigma_\ell)-B(\sigma_{\ell-1})\bigr)\ \ge\ h\cdot\frac{u}{1-h}\,\varphi(s_0).
$$

右端与 $\ell$ 无关。

(5) **右端。** 由引理 4.2，$B(h)<\kappa h$。所以只需证 $\frac{u}{1-h}\varphi(s_0)\ge\kappa$。

(6) **验证 (5) 中的不等式。** 由引理 4.2，$\varphi(s_0)\ge\kappa(r_0-r_0^\kappa)$，其中 $r_0=s_0/(1+s_0)=\frac{2(1-h)}{u+2(1-h)}$。于是

$$
\frac{u}{1-h}\cdot\frac{\varphi(s_0)}{\kappa}\ \ge\ \frac{2u}{u+2(1-h)}-\frac{u\,r_0^\kappa}{1-h}\ \ge\ \frac{2u}{u+2}-\frac{2^\kappa u^{1-\kappa}}{1-e^{-u}} .
$$

这里用了 $r_0\le 2/u$。当 $u\ge6$ 时，$\frac{2u}{u+2}\ge\frac32$，$\frac{1}{1-e^{-u}}<1.003$。又 $u\ge(2^{\kappa+1.01})^{1/(\kappa-1)}$ 给出 $u^{\kappa-1}\ge2^{\kappa+1.01}$，从而 $2^\kappa u^{1-\kappa}\le2^{-1.01}<0.4967$，第二项 $<0.4982$。于是右端 $>\tfrac32-0.4982>1$，即 $\frac{u}{1-h}\varphi(s_0)>\kappa$。

由 (1)–(6) 即得结论。关于 $x_\ell$ 的推论：$F^{[\kappa]}(\cdot,\ell)$ 严格递减，且 $F^{[\kappa]}(x_\ell,\ell)=\epsilon=F^{[\kappa]}(x,1)<F^{[\kappa]}(x^{1/\ell},\ell)$。证毕。

**注记 4.4（阈值的形状）。**
- **κ=2 的端点。** 该文附录证明了 $\kappa=2$ 时 $x\ge2$ 的非严格不等式与 $x>2$ 的严格不等式。在 $x=2$ 处，对每个整数 $\ell\ge2$ 有 $F^{[2]}(2^{1/\ell},\ell)=F^{[2]}(2,1)=\tfrac12$，即 $x_\ell=2^{1/\ell}$。定理 4.3 给出的 $X(2)=e^{8.06\ldots}$ 远比它粗。
- **对 $1<\kappa<2$，严格不等式在 $x=2$ 处对某些 $\ell$ 不成立。** 取 $u=\log2$、$h=1/2$，由下一条的 $\ell\to\infty$ 极限，只需证 $L(\kappa,\log2)=(\kappa-1)\log2<B_\kappa(1/2)$。令 $g(\kappa)=B_\kappa(1/2)=\log(3^\kappa-1)-\kappa\log2$，则 $g''(\kappa)=-\dfrac{(\log3)^2\,3^\kappa}{(3^\kappa-1)^2}<0$，且 $g(1)=0$、$g(2)=\log2$。由严格凹性，$1<\kappa<2$ 时 $g(\kappa)>(\kappa-1)\log2$。所以对每个 $1<\kappa<2$，存在 $\ell$ 使 $F^{[\kappa]}(2^{1/\ell},\ell)<F^{[\kappa]}(2,1)$，也就是阈值不能取 $2$。一个具体的有限 $\ell$ 例子是 $\kappa=3/2$、$\ell=2$：两侧比值分别为 $(3\sqrt3-1)/(2\sqrt2)\approx1.4836$ 与 $\bigl((2\sqrt2-1)^{3/2}-1\bigr)/\bigl(2^{3/4}-(2-\sqrt2)^{3/2}\bigr)\approx1.1937$，而 $1.4836>1.1937^2$。
- **κ→1⁺ 时阈值必须发散。** 固定 $u>0$，令 $h=e^{-u}$。对固定的 $\kappa>1$ 令 $\ell\to\infty$：$y=e^{u/\ell}\to1$，$\sigma_{\ell-1}\to\infty$，且 $\ell/\sigma_{\ell-1}\to u/(1-h)$。又 $\sigma B'(\sigma)\to\kappa-1$（$\sigma\to\infty$），因此
  $$\ell\bigl(B(\sigma_\ell)-B(\sigma_{\ell-1})\bigr)\to L(\kappa,u):=(\kappa-1)\frac{uh}{1-h}.$$
  $L$ 与 $B_\kappa(h)=\log\bigl((1+h)^\kappa-h^\kappa\bigr)$ 都关于 $\kappa$ 光滑，且在 $\kappa=1$ 处为 $0$。在 $\kappa=1$ 处二者对 $\kappa$ 的导数分别为 $\frac{uh}{1-h}$ 与 $(1+h)\log(1+h)+uh$。因为 $(1+h)\log(1+h)\ge h$ 且 $\frac{u}{e^u-1}<1$，有
  $$\frac{uh}{1-h}-uh-(1+h)\log(1+h)\le h\Bigl(\frac{uh}{1-h}-1\Bigr)=h\Bigl(\frac{u}{e^u-1}-1\Bigr)<0 .$$
  所以对每个 $u>0$，存在 $\kappa_u>1$，使 $1<\kappa<\kappa_u$ 时 $L(\kappa,u)<B_\kappa(h)$；于是对充分大的 $\ell$，(4.1) 在 $x=e^u$ 处不成立。由此可知任何对 $\ell$ 一致的阈值 $X(\kappa)$ 都满足 $X(\kappa)\to\infty$（$\kappa\to1^+$）。
- **$u_0$ 的阶。** $\kappa\to1^+$ 时 $u_0(\kappa)=2^{(\kappa+1.01)/(\kappa-1)}=2\cdot2^{2.01/(\kappa-1)}$。它来自 (6) 中对 $\varphi$ 的粗略下界，没有追求最优。

**范围。** 外部输入为 Fan–Kobayashi–Molnar 定义 4.2、定理 4.3（单调性）、引理 4.12 及附录。本仓推导的是：引理 4.1 的增量表示，定理 4.3（对 $\ell$ 一致的显式阈值），以及注记 4.4 中阈值不能取 $2$（$1<\kappa<2$）与 $\kappa\to1^+$ 时阈值发散的论证。在所查范围（该文、Molnar arXiv:2610.12816v1、arXiv 检索）内未见此结论，本节不主张文献优先权。

## 追加锚（本行以下为增补区）

## 5. 推论 6.5 的参数门槛不能降到 3/2

Fan–Kobayashi–Molnar 推论 6.5 表明：若 RH 成立，则对一切 $\kappa\ge2$，(1.1) 对一切 $n>2162160$ 成立。其第 8 节问：“can we reduce the threshold for κ in Corollary 6.5 to 3/2?”。本节说明：若要求 $n$ 的阈值是一个对参数一致的有限数 $N$，则参数门槛不能降到 $3/2$；在 RH 下，依赖参数的最终成立阈值在 $\kappa\to3/2^+$ 时必须发散。

**定理 5.1。** 对每个正整数 $N$，存在 $\delta=\delta(N)>0$，使得对一切 $\kappa\in[3/2,3/2+\delta)$，都有某个 $n>N$ 使 (1.1) 不成立。特别地：不存在有限的 $N$ 使“(1.1) 对一切 $\kappa>3/2$ 与一切 $n>N$ 成立”；对每个固定的 $N$（例如推论 6.5 中的 $N=2162160$），满足“(1.1) 对一切 $\kappa\ge\kappa_0$ 与一切 $n>N$ 成立”的 $\kappa_0$ 都满足 $\kappa_0\ge3/2+\delta(N)$。这里的 $\delta(N)$ 依赖于预先固定的 $N$；本定理不排除对每个 $\kappa_0>3/2$ 取依赖于 $\kappa_0$ 的阈值。本结论不依赖 RH。

**证明。** 由定理 2.3，存在整数 $n_0>\max(N,2)$ 使

$$
\zeta(3/2)\,\sigma^{[3/2]}(n_0)>\bigl(e^\gamma n_0\log\log n_0\bigr)^{3/2}.
$$

固定 $n_0$。$\sigma^{[\kappa]}(n_0)=\sum_{d\mid n_0}\mu(n_0/d)\sigma(d)^\kappa$ 是有限和，关于 $\kappa$ 连续；$\zeta(\kappa)$ 在 $(1,\infty)$ 上连续；$(e^\gamma n_0\log\log n_0)^\kappa$ 关于 $\kappa$ 连续。严格不等式在 $\kappa=3/2$ 处成立，故它在 $3/2$ 的某个邻域内仍成立。取 $\delta$ 使该邻域包含 $[3/2,3/2+\delta)$ 即得结论。证毕。

**定理 5.2（最终成立阈值的发散）。** 设 RH 成立，对实数 $\kappa>3/2$ 令

$$
N(\kappa)=\min\{N\in\mathbb Z_{\ge2}:\ (1.1)\ \text{对一切整数}\ n>N\ \text{成立}\}
$$

（由该文定理 6.1，$N(\kappa)<\infty$）。则 $N(\kappa)\to\infty$（$\kappa\to3/2^+$）。

**证明。** 反设存在正整数 $M$ 及实数 $\kappa_k\downarrow3/2$（$\kappa_k>3/2$）使 $N(\kappa_k)\le M$。由定理 5.1（取 $N=M$），存在 $\delta>0$，使对每个 $\kappa\in[3/2,3/2+\delta)$ 都有某个 $n>M$ 违反 (1.1)。取 $k$ 足够大使 $\kappa_k\in(3/2,3/2+\delta)$，则存在 $n>M\ge N(\kappa_k)$ 违反 (1.1)，与 $N(\kappa_k)$ 的定义矛盾。证毕。

**注记 5.3。** 定理 5.1 回答了第 8 节关于推论 6.5 的提问中“端点”与“对参数一致的有限阈值”这两种理解：门槛 $3/2$ 不可达；对任何固定的 $n$ 阈值 $N$，适用的参数区间都与 $3/2$ 有正距离 $\delta(N)$。若允许 $n$ 的阈值随 $\kappa$ 变化，则 RH 下由该文定理 6.1，对每个 $\kappa>3/2$ 都有有限阈值 $N(\kappa)$，定理 5.2 说明它随 $\kappa\to3/2^+$ 发散。在推论 6.5 的形式 $n>2162160$ 下，令

$$
K=\{\kappa_0>1:\ (1.1)\ \text{对一切}\ \kappa\ge\kappa_0\ \text{与一切}\ n>2162160\ \text{成立}\},\qquad \kappa^\ast=\inf K .
$$

- RH 下，推论 6.5 给出 $2\in K$，故 $K$ 非空且 $\kappa^\ast\le2$。
- 无条件地，定理 5.1（取 $N=2162160$）给出 $K\subset[3/2+\delta(2162160),\infty)$，故在 $K$ 非空时 $\kappa^\ast\ge3/2+\delta(2162160)>3/2$。

本节未确定 $\kappa^\ast$ 的确切值。

**范围。** 外部输入为 Fan–Kobayashi–Molnar 推论 6.5、定理 6.1 与第 8 节问题。本仓推导的是定理 5.1 与 5.2；它们由本卷定理 2.3 与 $\kappa$ 方向的连续性得到。在所查范围（该文、Molnar arXiv:2610.12816v1、arXiv 检索）内未见此结论。本节不主张文献优先权。

## 追加锚（本行以下为增补区）
