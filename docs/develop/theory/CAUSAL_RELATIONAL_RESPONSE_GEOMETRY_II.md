# 因果关系几何 II：有限随机接口的总变差收缩

本卷续接[原卷第 17 章](CAUSAL_RELATIONAL_RESPONSE_GEOMETRY.md#chapter-17)。定理 35.1 对原卷定理 17.2.3 的同一收缩界给出独立证明；输入差异的正、负部分共同组成一份总质量为一的双重混合。

本卷是数学参考输入。下文是有限和的普通数学证明，未提供本仓 Lean kernel 核验或新增形式化声明。

<a id="chapter-35"></a>

## 35. 随机接口的成对行混合

### 35.1　对象与记号

令 $X,Y$ 为有限集合，$\mu,\nu:X\to\mathbb R$ 为非负且总和为一的概率分布。令 $K:X\times Y\to\mathbb R$ 满足 $K(x,y)\ge0$ 和 $\sum_{y\in Y}K(x,y)=1$。输入概率分布的存在蕴含 $X$ 非空，因此下面成对行距离的最大值有定义。

对有限集合 $Z$ 上的两个概率分布 $p,q$，定义

$$
\operatorname{TV}(p,q)=\frac12\sum_{z\in Z}|p(z)-q(z)|.
$$

推前分布与 Dobrushin 系数分别为

$$
(\mu K)(y)=\sum_{x\in X}\mu(x)K(x,y),
\qquad
\alpha(K)=\max_{x,x'\in X}
\operatorname{TV}\bigl(K(x,\cdot),K(x',\cdot)\bigr).
$$

对 $h:X\to\mathbb R$，记 $h_+(x)=\max\{h(x),0\}$、$h_-(x)=\max\{-h(x),0\}$。逐点有 $h=h_+-h_-$ 与 $|h|=h_++h_-$。因此，当 $h=\mu-\nu$ 时，$\sum_x h(x)=0$ 给出

$$
\sum_{x\in X}h_+(x)=\sum_{x\in X}h_-(x)
=\operatorname{TV}(\mu,\nu).
$$

这也是[原卷引理 17.2.2](CAUSAL_RELATIONAL_RESPONSE_GEOMETRY.md#claim-17-2-2)的零总质量分解。

<a id="claim-35-1"></a>

### 35.2　收缩界

**定理 35.1（有限状态 Dobrushin 收缩）。** 对上述任意 $X,Y,\mu,\nu,K$，

$$
\operatorname{TV}(\mu K,\nu K)
\le\alpha(K)\operatorname{TV}(\mu,\nu).
$$

**证明。**

令 $h=\mu-\nu$，$t=\operatorname{TV}(\mu,\nu)$。由于 $\mu,\nu$ 都是概率分布，$\sum_{x\in X}h(x)=0$。若 $t=0$，则

$$
\sum_{x\in X}|h(x)|=2t=0,
$$

故 $h=0$，从而 $\mu K=\nu K$，结论成立。

以下设 $t>0$，定义

$$
a(x)=\frac{h_+(x)}{t},
\qquad
b(x)=\frac{h_-(x)}{t}
\qquad(x\in X).
$$

由上述零总质量分解，$a(x),b(x)\ge0$，且

$$
\sum_{x\in X}a(x)=\sum_{x\in X}b(x)=1,
\qquad
h=t(a-b).
$$

对每个 $y\in Y$，由推前定义和两个权重的总和均为 $1$，有精确恒等式

$$
\begin{aligned}
(\mu K-\nu K)(y)
&=t\left(\sum_{x\in X}a(x)K(x,y)
-\sum_{x'\in X}b(x')K(x',y)\right)\\
&=t\sum_{x\in X}\sum_{x'\in X}
a(x)b(x')\bigl(K(x,y)-K(x',y)\bigr).
\end{aligned}
$$

由于 $t,a(x),b(x')$ 非负，应用三角不等式并将 $L^1$ 范数除以 $2$，得到

$$
\begin{aligned}
\operatorname{TV}(\mu K,\nu K)
&=\frac12\sum_{y\in Y}|(\mu K-\nu K)(y)|\\
&\le\frac{t}{2}\sum_{y\in Y}\sum_{x\in X}\sum_{x'\in X}
a(x)b(x')|K(x,y)-K(x',y)|\\
&=t\sum_{x\in X}\sum_{x'\in X}a(x)b(x')
\operatorname{TV}\bigl(K(x,\cdot),K(x',\cdot)\bigr)\\
&\le t\alpha(K)\sum_{x\in X}\sum_{x'\in X}a(x)b(x')\\
&=t\alpha(K)
=\alpha(K)\operatorname{TV}(\mu,\nu).
\end{aligned}
$$

其中每一对行的总变差均不超过 $\alpha(K)$，而双重权重满足

$$
\sum_{x\in X}\sum_{x'\in X}a(x)b(x')
=\left(\sum_{x\in X}a(x)\right)
\left(\sum_{x'\in X}b(x')\right)=1.
$$

证毕。

### 35.3　来源与适用范围

这是文献已知的有限状态 Dobrushin 收缩定理，未主张数学原创性。更一般的有限等质量测度版本见 [LMLExplore 的 `MeasureTheory.tvDist_comp_right_le_dobrushinCoeff_mul`](https://github.com/LeanMachineLearning/LMLExplore/blob/13fc17b22a3b6db29b36567ff9c2c04893ac139b/LMLExplore/Probability/Kernel/Dobrushin.lean)；该来源的 `tvDist` 是这里概率总变差的两倍，同一收缩系数保留上述不等式。本卷没有将该外部 Lean 证明接入本仓工具链。

这里的推导适用于任意有限状态和任意给定的合法随机核，包含输入相同以及 $\alpha(K)=0$ 的情形。概率归一化已经排除空输入上的概率分布，因而没有额外加入非空假设。结论是共同接口下差异的上界，不从正系数推出某一对输入具有严格正的输出差异。

## 追加锚（本行以下为增补区）
