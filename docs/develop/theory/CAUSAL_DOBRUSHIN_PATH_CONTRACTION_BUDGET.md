# 因果路径的 Dobrushin 收缩预算：从可达箭到可见增益

> **本卷的机器契约。** 本文是 \`docs/develop/theory/\` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

一张图可以显示某个干预端与目标端之间存在路径，但这条路径未必还能把输入差异传到目标。每个随机接口都会压缩可区分的分布，连续接口的压缩率沿路径相乘。

$$
\boxed{
\text{路径存在是布尔事实};
\qquad
\text{路径上的因果增益是可组合的收缩预算}.
}
$$

本卷在有限状态空间中用总变差距离量化这份预算。结论不把 Dobrushin 系数冒充全部因果含义：它还必须和输入端实际产生的差异、目标端实际读取的接口一起使用。

## 1. AHH：一条箭可以存在，但它传不出任何差异

令 $X,Y$ 为有限状态集。一个有限 Markov 核 $K:X\rightsquigarrow Y$ 为每个 $x\in X$ 指定概率分布 $K(x,\cdot)$。对两个分布 $\mu,\nu$，总变差距离为

$$
\operatorname{TV}(\mu,\nu)
=
\frac12\sum_{y\in Y}|\mu(y)-\nu(y)|.
$$

定义核的 Dobrushin 收缩系数：

$$
\alpha(K)
=
\max_{x,x'\in X}
\operatorname{TV}\bigl(K(x,\cdot),K(x',\cdot)\bigr)
\in[0,1].
$$

$\alpha(K)$ 只问一件事：输入端任意两个纯状态的区别，经过这个接口后最多还能保留多少总变差。

若一个因果网络的图论祖先关系中有 $A\to B$，但路径上某个接口满足 $\alpha(K)=0$，那么 $A$ 的全部输入差异都会在该接口处被擦除。反过来，所有 $\alpha(K_i)$ 都正，只能给出可能的增益上界，不能单独保证实际输入会产生非零输出差。

$$
\boxed{
\text{图论可达性}
\;\supsetneq\;
\text{正的操作性影响}.
}
$$

## 2. 单个随机接口的收缩定理

**定义 2.1（分布推前）。** 对分布 $\mu$ 和核 $K$，定义

$$
(\mu K)(y)
=
\sum_{x\in X}\mu(x)K(x,y).
$$

**引理 2.2（零总质量分解）。** 若 $h:X\to\mathbb R$ 满足 $\sum_xh(x)=0$，令

$$
h_+(x)=\max\{h(x),0\},
\qquad
h_-(x)=\max\{-h(x),0\}.
$$

则

$$
h=h_+-h_-,
\qquad
\sum_xh_+(x)=\sum_xh_-(x)=\operatorname{TV}(\mu,\nu)
$$

当 $h=\mu-\nu$ 时成立。

**定理 2.3（Dobrushin 收缩）。** 对任意分布 $\mu,\nu$，

$$
\boxed{
\operatorname{TV}(\mu K,\nu K)
\le
\alpha(K)\operatorname{TV}(\mu,\nu).
}
$$

### 证明

令 $h=\mu-\nu$。由推前定义，

$$
(\mu K-\nu K)(y)
=
\sum_xh(x)K(x,y).
$$

取任意固定 $x_0\in X$。由于 $\sum_xh(x)=0$，

$$
\mu K-\nu K
=
\sum_xh(x)\bigl(K(x,\cdot)-K(x_0,\cdot)\bigr).
$$

用三角不等式、$h=h_+-h_-$ 和 $\operatorname{TV}(K(x),K(x_0))\le\alpha(K)$，得到

$$
\begin{aligned}
\operatorname{TV}(\mu K,\nu K)
&\le
\sum_xh_+(x)\alpha(K)
+
\sum_xh_-(x)\alpha(K)\\
&=
\alpha(K)\operatorname{TV}(\mu,\nu).
\end{aligned}
$$

证毕。

**推论 2.4（完全擦除判据）。**

$$
\boxed{
\alpha(K)=0
\iff
K(x,\cdot)=K(x',\cdot)\quad\forall x,x'\in X.
}
$$

### 证明

总变差为零当且仅当两个有限分布逐点相等；对最大值定义逐项应用即可。证毕。

因此 $\alpha(K)=0$ 的接口仍然可以输出随机结果，但输出律与输入状态无关。它切断的是输入差异，不是输出活动本身。

## 3. 串联因果路径的乘法预算

取有限状态链：

$$
X_0
\xrightarrow{K_1}
X_1
\xrightarrow{K_2}
\cdots
\xrightarrow{K_n}
X_n.
$$

复合核按

$$
K_{1:n}=K_1K_2\cdots K_n
$$

记号表示先经过 $K_1$，再经过 $K_2$，直至 $K_n$。

**定理 3.1（复合收缩系数的次乘法）。**

$$
\boxed{
\alpha(K_{1:n})
\le
\prod_{i=1}^n\alpha(K_i).
}
$$

### 证明

对任意 $x,x'\in X_0$，反复应用定理 2.3：

$$
\begin{aligned}
\operatorname{TV}\bigl(K_{1:n}(x,\cdot),K_{1:n}(x',\cdot)\bigr)
&\le
\alpha(K_n)
\operatorname{TV}\bigl(K_{1:n-1}(x,\cdot),K_{1:n-1}(x',\cdot)\bigr)\\
&\le
\cdots\\
&\le
\prod_{i=1}^n\alpha(K_i).
\end{aligned}
$$

对 $x,x'$ 取最大值即得。证毕。

**定理 3.2（干预到目标读出的路径界）。** 若两个允许干预 $a_0,a_1$ 在 $X_0$ 上产生分布 $\mu_0,\mu_1$，目标端读取 $X_n$ 的完整状态，则

$$
\boxed{
\operatorname{TV}(\mu_0K_{1:n},\mu_1K_{1:n})
\le
\operatorname{TV}(\mu_0,\mu_1)
\prod_{i=1}^n\alpha(K_i).
}
$$

若目标端还经过一个读出核 $M:X_n\rightsquigarrow Y$，则

$$
\boxed{
\operatorname{TV}(\mu_0K_{1:n}M,\mu_1K_{1:n}M)
\le
\operatorname{TV}(\mu_0,\mu_1)
\left(\prod_{i=1}^n\alpha(K_i)\right)\alpha(M).
}
$$

### 证明

先对 $K_{1:n}$ 应用定理 2.3 和定理 3.1，再对 $M$ 应用一次定理 2.3。证毕。

右端分成三份具有不同含义的预算：

1. 干预接口实际制造的初始差异；
2. 动力学路径保留差异的乘积；
3. 目标读出保留差异的最后一项。

把它们合并成一个「因果强度」会丢掉哪一段关系真正造成了衰减。

## 4. 二元通道给出锐利见证

令每个状态集都为 $\{-1,+1\}$。对 $0\le\lambda_i\le1$，定义二元对称核

$$
K_{\lambda_i}(x,y)
=
\frac{1+\lambda_i xy}{2}.
$$

它以概率 $(1+\lambda_i)/2$ 保留符号，以概率 $(1-\lambda_i)/2$ 翻转符号。

**引理 4.1（二元通道的精确系数）。**

$$
\alpha(K_{\lambda_i})=\lambda_i.
$$

### 证明

两行输出分布分别为

$$
\left(\frac{1+\lambda_i}2,\frac{1-\lambda_i}2\right),
\qquad
\left(\frac{1-\lambda_i}2,\frac{1+\lambda_i}2\right),
$$

其总变差为 $\lambda_i$；二元输入只有这两个纯状态，故最大值即为 $\lambda_i$。证毕。

**定理 4.2（乘法预算的锐利性）。** 令

$$
\mu_+=\delta_{+1},
\qquad
\mu_-=\delta_{-1}.
$$

对二元链 $K_{\lambda_1},\ldots,K_{\lambda_n}$，有

$$
\boxed{
\operatorname{TV}(\mu_+K_{\lambda_1}\cdots K_{\lambda_n},
\mu_-K_{\lambda_1}\cdots K_{\lambda_n})
=
\prod_{i=1}^n\lambda_i.
}
$$

### 证明

若输入符号的期望为 $m$，经过 $K_{\lambda_i}$ 后，输出符号的期望为 $\lambda_i m$。因此从 $\mu_+$ 和 $\mu_-$ 出发，末端期望分别为

$$
+\prod_i\lambda_i
\quad\text{和}\quad
-\prod_i\lambda_i.
$$

二元分布由期望唯一决定，两个末端分布的总变差等于期望差的一半，即

$$
\frac12\left|
\prod_i\lambda_i-\left(-\prod_i\lambda_i\right)
\right|
=
\prod_i\lambda_i.
$$

证毕。

所以定理 3.2 的乘法上界不能统一改进为更小的函数：每个接口都可以在同一二元方向上达到它。

## 5. 一个零系数切断整条未来

**定理 5.1（完全擦除的因果切断）。** 若链中存在 $j$ 使

$$
\alpha(K_j)=0,
$$

则对任意两个上游分布 $\mu,\nu$，以及任意下游核 $L$，

$$
\boxed{
\mu K_1\cdots K_jL
=
\nu K_1\cdots K_jL.
}
$$

### 证明

由推论 2.4，$K_j$ 的每一行都等于同一分布 $\rho$。因此无论 $K_1\cdots K_{j-1}$ 的输出分布是什么，经过 $K_j$ 后都等于 $\rho$；再经同一个下游核 $L$ 仍相同。证毕。

这是一种比「图上没有路径」更细的无影响判据：图上可以保留任意多条路径，只要每条从干预端到目标端的合法路径都穿过一个完全擦除接口，目标端就无法区分干预。

**推论 5.2（有限路径族的切断）。** 若一个有限路径族 $\mathcal P$ 的每条路径 $p$ 都有某个接口 $i(p)$ 满足 $\alpha(K_{p,i(p)})=0$，并且网络的路径选择权重与干预无关，则目标输出对干预完全不敏感。

### 证明

每条路径的复合核都把两个上游分布送到同一输出律。共同的路径混合权重再求和，仍得到相同目标分布。证毕。

## 6. 分支网络的加权预算

考虑有限路径集合 $\mathcal P$。路径 $p$ 从输入端到目标端的复合核记为 $K_p$，网络先以与输入无关的权重 $\omega_p\ge0$ 选择路径，且

$$
\sum_{p\in\mathcal P}\omega_p=1.
$$

目标分布为

$$
\nu_\mu
=
\sum_{p\in\mathcal P}\omega_p\,\mu K_p.
$$

**定理 6.1（分支路径预算）。**

$$
\boxed{
\operatorname{TV}(\nu_\mu,\nu_{\mu'})
\le
\operatorname{TV}(\mu,\mu')
\sum_{p\in\mathcal P}\omega_p\alpha(K_p).
}
$$

若 $K_p$ 是路径接口的串联复合，则进一步有

$$
\operatorname{TV}(\nu_\mu,\nu_{\mu'})
\le
\operatorname{TV}(\mu,\mu')
\sum_{p\in\mathcal P}
\omega_p\prod_{i\in p}\alpha(K_{p,i}).
$$

### 证明

由三角不等式，

$$
\operatorname{TV}(\nu_\mu,\nu_{\mu'})
\le
\sum_p\omega_p
\operatorname{TV}(\mu K_p,\mu'K_p).
$$

对每一项应用定理 2.3，再用定理 3.1 得到结论。证毕。

路径混合权重必须与干预无关。若干预同时改变了路径选择概率，差异还有一项来自 $\omega_p(\mu)-\omega_p(\mu')$，不能直接套用本定理。这个限制正是把「传播收缩」与「路由改变」分开的条件。

## 7. 收缩预算的等号和非等号

Dobrushin 界是一个最坏情形上界。它达到等号需要输入差异落在接口最能区分的方向，并且每一层都把前一层的符号方向继续对齐。

**命题 7.1（上界为零时的全局判据）。** 若

$$
\operatorname{TV}(\mu,\nu)>0
$$

且链复合满足

$$
\alpha(K_{1:n})=0,
$$

则末端输出相同。反之，若存在某对输入纯态使末端输出不同，则

$$
\alpha(K_{1:n})>0.
$$

### 证明

前半由定理 2.3 直接得到。后半由定义：若存在 $x,x'$ 使复合核的两行不同，则其总变差为正，最大值也为正。证毕。

但 $\alpha(K_{1:n})>0$ 只说明存在某种输入差异可以被传出；给定的 $\mu,\nu$ 仍可能因对称性或相消而有

$$
\mu K_{1:n}=\nu K_{1:n}.
$$

因此以下三个陈述严格不同：

$$
\begin{array}{c}
\text{图上有路径},\\[2pt]
\text{复合核有正收缩系数},\\[2pt]
\text{当前两种干预在目标端可区分}.
\end{array}
$$

它们的量词分别是存在图链、存在某对输入状态和当前指定的输入分布对。

## 8. 位置事件和探测接口的末端收缩

设粒子或模式状态先经过动力学核 $K$，再经过一个位置事件读出核

$$
M_R:X\rightsquigarrow\{0,1\},
$$

其中 $1$ 表示区域 $R$ 的记录事件。事件概率为

$$
p_R(\mu)=\sum_{x\in X}(\mu K)(x)M_R(x,1).
$$

**定理 8.1（位置事件的可见增益界）。** 对两个准备分布 $\mu,\nu$，

$$
\boxed{
|p_R(\mu)-p_R(\nu)|
\le
\operatorname{TV}(\mu K,\nu K)\,
\alpha(M_R)
\le
\operatorname{TV}(\mu,\nu)\alpha(K)\alpha(M_R).
}
$$

### 证明

把二元事件读出看成从 $X$ 到 $\{0,1\}$ 的 Markov 核，应用定理 2.3。二元分布的总变差等于其 $1$ 事件概率的绝对差；再对动力学核应用一次收缩。证毕。

若 $M_R$ 的所有状态都给出同一事件概率，则 $\alpha(M_R)=0$，位置事件对动力学差异完全不可见。即使物理状态仍在变化，已声明的区域记录也不会提供因果区分。

这把「粒子到达某处」与「探测接口能否把到达差异记录出来」分开。前者属于传播核，后者属于末端效果。

## 9. 反例：正路径系数不保证当前效应为正

令单步核为恒等核 $I$，另一个读出核为二元对称核 $K_\lambda$。图上路径存在，且

$$
\alpha(I)=1,\qquad \alpha(K_\lambda)=\lambda>0.
$$

取两个相同的均匀输入分布 $\mu=\nu=(1/2,1/2)$。则

$$
\operatorname{TV}(\mu,\nu)=0,
\qquad
\operatorname{TV}(\mu IK_\lambda,\nu IK_\lambda)=0.
$$

所以正的路径收缩系数只提供「有某种输入可见」的可能性，不会把任意当前准备变成非零因果效应。

更强的相消可以发生在非平凡输入上：若两个不同路径对某个读出事件的偏差符号相反，路径加权后也可能精确抵消。此时应保留路径的联合关系或符号结构，不能只保存各路径的绝对收缩系数。

## 10. 结论：因果锥应带一份增益预算

对一条从干预端到事件端的有限随机路径，可记录三层数据：

$$
\boxed{
\text{允许的输入差异}
\;\longrightarrow\;
\prod\text{接口收缩系数}
\;\longrightarrow\;
\text{事件读出的实际差异}.
}
$$

中间乘积是一个可组合的上界，也有二元通道族达到它；零收缩接口是严格切断，任何下游机制都不能恢复已经擦除的区分。分支网络则把路径预算按输入无关的混合权重相加。

因此，关系几何中的因果锥不应只有「能否到达」这一层。一个更精确的图案是：

> **因果路径是一条带增益预算的关系链；路径存在说明差异有机会传播，收缩预算说明最多还能保留多少，末端读出决定这份剩余差异是否成为事件记录。**

所有结论只对有限状态、合法 Markov 核、共同下游接口和声明的总变差读出负责。改变输入族、允许的随机化或探测接口，都会改变相应的因果增益预算。

## 追加锚（本行以下为增补区）
