# 因果信息预算的相对熵收缩：从可控差异到路径瓶颈

> **本卷的机器契约。** 本文是 `docs/develop/theory/` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

现有的路径可达性只回答“关系上是否有一条路”，总变差收缩只给出某种最坏情形的概率距离预算。本卷把另一种可组合的预算写出来：输入端关于干预标签所携带的相对熵或互信息，经过每个合法局部通道后至多保留多少。

$$
\boxed{
\text{因果路径的强度不是箭头的固有重量，}
\quad
\text{而是区分输入关系在各接口上的可保留信息预算。}
}
$$

全文只讨论有限集合与有限随机通道。自然对数用于相对熵；若改变对数底，所有数值只按同一常数缩放。

## 1. 有限通道与相对熵收缩系数

**定义 1.1（有限随机通道）。** 令 $X,Y$ 为有限集合。一个通道 $K:X\to Y$ 是满足

$$
K(y\mid x)\ge 0,
\qquad
\sum_{y\in Y}K(y\mid x)=1
$$

的数组。分布 $p$ 经过 $K$ 的推前写作

$$
(pK)(y)=\sum_{x\in X}p(x)K(y\mid x).
$$

**定义 1.2（相对熵）。** 对 $X$ 上的分布 $p,q$，定义

$$
D(p\Vert q)=
\sum_{x:p(x)>0}p(x)\log\frac{p(x)}{q(x)},
$$

若存在 $x$ 使 $p(x)>0=q(x)$，则令 $D(p\Vert q)=+\infty$。

**定义 1.3（KL 收缩系数）。** 令

$$
\eta_{\mathrm{KL}}(K)
=
\sup_{p,q:\,0<D(p\Vert q)<\infty}
\frac{D(pK\Vert qK)}{D(p\Vert q)},
$$

当没有这样的分布对时取值为 $0$。它只描述这个接口对于输入分布可区分性的最坏收缩。

**定理 1.4（相对熵数据处理与范围）。** 对任意有限通道 $K$，有

$$
\boxed{0\le \eta_{\mathrm{KL}}(K)\le 1.}
$$

并且对所有分布 $p,q$，

$$
\boxed{
D(pK\Vert qK)\le D(p\Vert q).
}
$$

### 证明

非负性来自相对熵的非负性。对每个 $y$ 使用加权 log-sum 不等式：

$$
\left(\sum_x a_x\right)\log\frac{\sum_x a_x}{\sum_x b_x}
\le
\sum_x a_x\log\frac{a_x}{b_x},
$$

取 $a_x=p(x)K(y\mid x)$、$b_x=q(x)K(y\mid x)$，再对 $y$ 求和，得到

$$
\begin{aligned}
D(pK\Vert qK)
&=\sum_y\left(\sum_xp(x)K(y\mid x)\right)
\log\frac{\sum_xp(x)K(y\mid x)}{\sum_xq(x)K(y\mid x)}\\
&\le\sum_{x,y}p(x)K(y\mid x)\log\frac{p(x)}{q(x)}\\
&=D(p\Vert q).
\end{aligned}
$$

零或无穷情形由同一不等式的扩展约定处理。对有限正比值取上确界即得范围。证毕。

## 2. 互信息是可传播的因果标记

**定义 2.1（干预标签与互信息）。** 令 $U$ 是一个有限干预标签，$X$ 是通道输入，$U\to X\to Y$ 表示给定 $X$ 后 $Y$ 与 $U$ 条件独立，并由 $K$ 产生 $Y$。定义

$$
I(U;X)=\sum_u\Pr(U=u)D(p_{X\mid u}\Vert p_X).
$$

这把“干预端知道了什么”写成一份关于实际输入关系的量，而不是把抽象图上的边数当成信息量。

**定理 2.2（强数据处理预算）。** 在 $U\to X\xrightarrow K Y$ 下，

$$
\boxed{
I(U;Y)\le \eta_{\mathrm{KL}}(K)\,I(U;X).
}
$$

### 证明

记 $p_u=p_{X\mid U=u}$，$p_X=\sum_up(u)p_u$。由通道条件独立性，

$$
p_{Y\mid u}=p_uK,
\qquad
p_Y=p_XK.
$$

因此

$$
\begin{aligned}
I(U;Y)
&=\sum_up(u)D(p_uK\Vert p_XK)\\
&\le\eta_{\mathrm{KL}}(K)\sum_up(u)D(p_u\Vert p_X)\\
&=\eta_{\mathrm{KL}}(K)I(U;X).
\end{aligned}
$$

若某个项为零或无穷，按相对熵的扩展值逐项成立。证毕。

**推论 2.3（零预算的结构判据）。** 以下命题等价：

1. $\eta_{\mathrm{KL}}(K)=0$；
2. 对任意 $p,q$，有 $pK=qK$；
3. $K(\cdot\mid x)$ 与 $K(\cdot\mid x')$ 对所有 $x,x'$ 相同；
4. 对任意 $U\to X\to Y$，有 $I(U;Y)=0$。

### 证明

$3\Rightarrow2$ 与 $2\Rightarrow4$ 直接成立。若 $4$ 成立，取 $U$ 为二点标签并令 $X$ 在两个标签下分别集中于 $x,x'$；则 $I(U;Y)=0$ 要求两行通道相同，故 $4\Rightarrow3$。

若 $2$ 成立，分子恒为零，故 $1$ 成立。反过来若 $1$ 成立而存在 $x,x'$ 使两行不同，由通道推前的线性性，可在全支撑分布的内部取两个充分接近的分布 $p,q$，使 $pK\ne qK$。此时 $0<D(p\Vert q)<\infty$ 且 $D(pK\Vert qK)>0$，相对熵比为正，与 $\eta_{\mathrm{KL}}(K)=0$ 矛盾。故 $1\Rightarrow3$。证毕。

特别地，图上允许一条边并不保证边上有可见因果信息；恒定通道可以位于一条合法路径上，却具有零预算。

## 3. 串联路径的乘法预算

**定理 3.1（KL 收缩系数的串联次乘性）。** 若 $K:X\to Y$、$L:Y\to Z$，则

$$
\boxed{
\eta_{\mathrm{KL}}(L\circ K)
\le
\eta_{\mathrm{KL}}(L)\eta_{\mathrm{KL}}(K).
}
$$

### 证明

对任意有限相对熵的 $p,q$，先经过 $K$ 再经过 $L$，有

$$
\begin{aligned}
D(pKL\Vert qKL)
&\le \eta_{\mathrm{KL}}(L)D(pK\Vert qK)\\
&\le \eta_{\mathrm{KL}}(L)\eta_{\mathrm{KL}}(K)D(p\Vert q).
\end{aligned}
$$

取所有允许分布对的上确界即可。证毕。

**推论 3.2（因果链的信息锥）。** 对有限链

$$
U\to X_0\xrightarrow{K_1}X_1\xrightarrow{K_2}\cdots
\xrightarrow{K_m}X_m,
$$

有

$$
\boxed{
I(U;X_m)
\le
\left(\prod_{j=1}^{m}\eta_{\mathrm{KL}}(K_j)\right)I(U;X_0).
}
$$

### 证明

把定理 2.2 逐层应用，或先用定理 3.1 得到复合通道的收缩系数，再应用定理 2.2。证毕。

若某一层为零预算，所有下游输出都与 $U$ 独立；若每层至多为 $\eta<1$，则链长为 $m$ 时的信息至多按 $\eta^m$ 衰减。这是“路径存在”和“路径仍能传递多少可区分性”的严格分离。

## 4. 分支网络与瓶颈

**定义 4.1（带公开分支标签的混合通道）。** 设分支 $i\in I$ 的概率为 $\lambda_i$，每个分支有通道 $K_i:X\to Y_i$。把分支标签也作为输出的一部分，定义

$$
K_{\mathrm{br}}(i,y\mid x)=\lambda_iK_i(y\mid x).
$$

**定理 4.2（分支预算的加权上界）。** 有

$$
\boxed{
\eta_{\mathrm{KL}}(K_{\mathrm{br}})
\le
\sum_{i\in I}\lambda_i\eta_{\mathrm{KL}}(K_i).
}
$$

### 证明

由于不同 $i$ 的输出支持不交，

$$
D(pK_{\mathrm{br}}\Vert qK_{\mathrm{br}})
=
\sum_i\lambda_iD(pK_i\Vert qK_i).
$$

每一项至多为 $\lambda_i\eta_{\mathrm{KL}}(K_i)D(p\Vert q)$；求和并取上确界即得。证毕。

**推论 4.3（隐藏分支只会减少预算）。** 若不公开 $i$，只输出 $y$，得到

$$
\overline K=\sum_i\lambda_iK_i.
$$

则

$$
\boxed{
\eta_{\mathrm{KL}}(\overline K)
\le
\sum_i\lambda_i\eta_{\mathrm{KL}}(K_i).
}
$$

### 证明

隐藏分支是对公开输出 $(i,y)$ 的确定后处理 $(i,y)\mapsto y$。定理 1.4 给出后处理不会增加相对熵，结合定理 4.2 即得。证毕。

这说明“分支有机会到达目标”与“观察者能从目标读出哪条分支”是两个接口问题。公开标签的预算可以逐支相加；把标签抹去还会发生额外混合损失。

## 5. 预算的精确见证：擦除通道

**定义 5.1（二元擦除通道）。** 令 $X=\{0,1\}$，输出集为 $Y=\{0,1,\perp\}$。给定 $\varepsilon\in[0,1]$，通道 $E_\varepsilon$ 以概率 $1-\varepsilon$ 输出输入位，以概率 $\varepsilon$ 输出擦除符号 $\perp$。

**定理 5.2（擦除通道的精确预算）。**

$$
\boxed{
\eta_{\mathrm{KL}}(E_\varepsilon)=1-\varepsilon.
}
$$

并且对任意 $U\to X\to Y$，

$$
\boxed{
I(U;Y)=(1-\varepsilon)I(U;X).
}
$$

### 证明

输出擦除标记 $B=\mathbf 1\{Y\ne\perp\}$ 与 $X,U$ 独立，且 $B=1$ 时 $Y=X$。因此

$$
I(U;Y)=I(U;B,Y)=I(U;Y\mid B)
=(1-\varepsilon)I(U;X).
$$

对任意输入分布 $p,q$，输出的非擦除部分按相同权重 $1-\varepsilon$ 缩放，而擦除部分相同，故

$$
D(pE_\varepsilon\Vert qE_\varepsilon)
=(1-\varepsilon)D(p\Vert q).
$$

取比值即得相对熵收缩系数；当 $D(p\Vert q)>0$ 时比值正好恒为 $1-\varepsilon$。证毕。

擦除是一个达到乘法预算的明确反例族：每一次独立擦除都把剩余互信息乘以同一个因子，而不是只给一个松的数量级估计。

## 6. 从相对熵预算到位置事件读数

**引理 6.1（Pinsker 事件界）。** 对有限分布 $r,s$ 和任意事件 $E$，

$$
|r(E)-s(E)|
\le \operatorname{TV}(r,s)
\le \sqrt{\frac12D(r\Vert s)}.
$$

### 证明

事件指示映射是一个通道，故第一不等式来自总变差的定义。对分布合并到事件 $E$ 与补集 $E^c$ 后，log-sum 不等式给出二点分布的相对熵不增；对二点分布应用

$$
a\log\frac ab+(1-a)\log\frac{1-a}{1-b}
\ge 2(a-b)^2
$$

即可得到第二不等式。证毕。

**定理 6.2（路径的信息—事件预算）。** 设两个干预条件在路径输入处诱导分布 $p,q$，路径复合通道为

$$
K=K_m\circ\cdots\circ K_1.
$$

若 $D(p\Vert q)<\infty$，则任意目标位置、记录或局域事件 $E$ 满足

$$
\boxed{
\bigl|(pK)(E)-(qK)(E)\bigr|
\le
\sqrt{
\frac12
\left(\prod_{j=1}^{m}\eta_{\mathrm{KL}}(K_j)\right)
D(p\Vert q)
}.
}
$$

### 证明

由定理 3.1，

$$
D(pK\Vert qK)
\le
\left(\prod_j\eta_{\mathrm{KL}}(K_j)\right)D(p\Vert q).
$$

再用引理 6.1 即得。证毕。

该界只控制两个干预条件在同一事件接口上的差异。它不把非零事件概率强行变成确定结果，也不取代“事件被排除”的支撑条件：后一命题要求的是相应效果对当前状态给出严格零概率，而不是两个候选输入之间的差异很小。

## 7. 三个边界例子：路径、信息与事件的分离

**命题 7.1（拓扑路径不保证操作影响）。**

1. 恒定通道 $K(y_0\mid x)=1$ 对所有 $x$ 都有 $\eta_{\mathrm{KL}}(K)=0$；它可以作为一条允许路径的局部机制，却完全擦除输入差异。
2. 恒等通道的收缩系数为 $1$；它保存全部输入分布的相对熵。
3. 对擦除通道，系数为 $1-\varepsilon$；同一条拓扑边可以有连续的一族不同信息预算。

### 证明

第一项由推论 2.3，第二项由 $pK=p,qK=q$，第三项由定理 5.2。证毕。

**推论 7.2（因果接口的三层读法）。** 对一个声明的局部过程，应分别记录：

$$
\boxed{
\text{允许的局部替换}
\quad\longrightarrow\quad
\text{输入差异的产生}
\quad\longrightarrow\quad
\text{通道的相对熵预算}
\quad\longrightarrow\quad
\text{目标事件的读出差异}.
}
$$

任何一层被省略，都不能由剩余的图形关系自动补回。特别是“有路径”不等于“有可检测因果影响”，“事件概率变化”也不等于“某一次结果被确定”。

## 8. AHH：因果锥应携带可组合的信息账

对有限路径，定义其相对熵预算

$$
\mathsf B(K_1,\ldots,K_m)
=
\prod_{j=1}^{m}\eta_{\mathrm{KL}}(K_j).
$$

它具有串联下的乘法组合律，并在分支网络中受加权上界控制。相同的拓扑路径可以因为局部机制不同而拥有零预算、单位预算或中间预算；相同的终点事件又可能因读出效果不同而给出不同可见差异。

> **AHH：因果锥不是一组只标注“可达/不可达”的箭头，而是一份沿接口递减、在分支处按权重合并、最终由事件读出兑现的信息账。**

这份账仍然是模型相对的：它依赖可执行输入族、合法通道、共同随机来源以及被声明的读出接口。它量化的是可传播的区分性，不替代量子支撑条件、动力学不变子空间或一次记录的结果律。

## 追加锚（本行以下为增补区）
