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
