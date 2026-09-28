# 因果可控—可观测商：最小边界不是全部状态

> **本卷的机器契约。** 本文是 \`docs/develop/theory/\` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

一个动力学系统可以有很多内部坐标，但干预者真正能够改变的方向，和未来观察者真正能够区分的方向，通常只占其中一部分。本卷给出一个有限维线性模型中的精确商空间：

$$
\boxed{
\text{因果边界}
=
\frac{\text{可由允许干预到达的状态}}
{\text{其中永远不能被未来读出区分的状态}}.
}
$$

这个商不是把状态空间任意压缩，而是由两个操作条件共同决定：

- **可控性**：某个方向是否能由允许的输入真正激活；
- **可观测性**：某个方向是否能在未来的合法读出中留下差异。

因此，一个方向只“存在于方程”还不足以成为因果内容。不可达方向没有被接口赋予作用机会；可达但永远不可观测的方向虽然会演化，却不会改变任何声明的因果记录。反过来，只有两者的交叠才需要进入最小的因果记忆。

## 1. AHH：因果状态是可达与可辨识的交集

令内部状态空间为有限维向量空间 $X$，允许干预空间为 $U$，读出空间为 $Y$。考虑零初态的离散过程：

$$
x_{t+1}=Ax_t+Bu_t,
\qquad
y_t=Cx_t,
\qquad
x_0=0,
$$

其中 $A:X\to X$ 是内部演化，$B:U\to X$ 是干预接口，$C:X\to Y$ 是读出接口。这里的「位置事件」可以作为 $C$ 的一个分量：例如把某区域的占据概率、点击概率或记录标签编码成读出坐标。

真正的最小因果状态不是 $x_t$ 的全部坐标，而是未来所有合法实验能区分的等价类。若两个当前状态在任何未来输入词下都给出同样的输出词，它们对该接口来说就是同一个因果状态。

$$
\boxed{
\text{内部维数}
\;\ge\;
\text{因果边界维数};
\qquad
\text{多出的维数是接口不可达或不可辨识的部分}.
}
$$

## 2. 可达子空间与不可观测子空间

**定义 2.1（可达子空间）。** 允许输入任意有限词，并从零初态开始。定义

$$
\mathcal R
=
\operatorname{span}\bigl(
\operatorname{im}B,\,
\operatorname{im}AB,\,
\operatorname{im}A^2B,\ldots
\bigr)
\subseteq X.
$$

$\mathcal R$ 是所有可由有限次干预产生的状态的线性包络。由于 $X$ 有限维，Cayley–Hamilton 定理给出

$$
\mathcal R
=
\operatorname{span}\bigl(
\operatorname{im}B,\ldots,\operatorname{im}A^{n-1}B
\bigr),
\qquad n=\dim X.
$$

**定义 2.2（不可观测子空间）。** 定义

$$
\mathcal N
=
\bigcap_{k\ge0}\ker(CA^k).
$$

若 $z\in\mathcal N$，则从状态差 $z$ 出发，在没有额外输入时的全部未来读出都为零：

$$
CA^kz=0
\qquad\forall k\ge0.
$$

同样由 Cayley–Hamilton 定理，

$$
\mathcal N
=
\bigcap_{0\le k<n}\ker(CA^k).
$$

**定义 2.3（操作等价）。** 对 $x,x'\in\mathcal R$，写

$$
x\sim_{\mathrm{op}}x'
$$

当且仅当对每个未来输入词 $(u_0,\ldots,u_{m-1})$ 和每个 $m\ge0$，从 $x$ 与 $x'$ 出发的未来读出词完全相同。

这个定义把「相同」限定在已经声明的干预与读出接口内。若增加一个新的探针，$\mathcal N$ 可能变小，因果边界也可能变大。

## 3. 可达—不可观测商的基本定理

**定理 3.1（操作等价的精确核）。** 对 $x,x'\in\mathcal R$，有

$$
\boxed{
x\sim_{\mathrm{op}}x'
\quad\Longleftrightarrow\quad
x-x'\in\mathcal N.
}
$$

### 证明

令 $z=x-x'$。从两个状态施加同一个未来输入词时，输入项完全抵消，差分状态满足

$$
z_{t+1}=Az_t,
\qquad z_t=A^tz.
$$

所以第 $t$ 个未来读出之差为

$$
CA^tz.
$$

若 $z\in\mathcal N$，上述差对所有 $t$ 都为零，故两个状态对任何共同输入词给出同样的输出。

反过来，若两个状态操作等价，取未来输入词为空，便得到

$$
CA^tz=0
\qquad\forall t\ge0.
$$

因此 $z\in\mathcal N$。证毕。

**推论 3.2（因果边界）。** 定义

$$
\mathcal Z
=
\mathcal R/(\mathcal R\cap\mathcal N),
\qquad
d_{\mathrm{causal}}=\dim\mathcal Z.
$$

则 $\mathcal Z$ 的元素恰好是可由允许干预产生、且能被某个未来合法读出区分的状态类。

$$
\boxed{
d_{\mathrm{causal}}
=
\dim\mathcal R-\dim(\mathcal R\cap\mathcal N).
}
$$

这给出一个只依赖接口的因果维数。它不等于 $\dim X$，也不等于单独的可控维数 $\dim\mathcal R$。

## 4. 商动力学仍然是一个合法因果模型

要使商空间成为真正的状态边界，而不是静态集合，需要验证动力学和接口能够下降到商上。

**引理 4.1（两个不变性）。**

$$
A\mathcal R\subseteq\mathcal R,
\qquad
A\mathcal N\subseteq\mathcal N.
$$

### 证明

第一式对生成元逐项成立：

$$
A(A^k\operatorname{im}B)=A^{k+1}\operatorname{im}B\subseteq\mathcal R.
$$

若 $z\in\mathcal N$，则对任意 $k\ge0$，

$$
CA^k(Az)=CA^{k+1}z=0,
$$

故 $Az\in\mathcal N$。证毕。

**定理 4.2（商模型的存在与精确复现）。** 在 $\mathcal Z$ 上定义

$$
\bar A[x]=[Ax],
\qquad
\bar B u=[Bu],
\qquad
\bar C[x]=Cx,
$$

其中 $[x]$ 表示 $x$ 在 $\mathcal Z$ 中的等价类。则这些定义良定，并且对任意允许输入词，商模型产生与原模型完全相同的读出词。

### 证明

若 $[x]=[x']$，则 $x-x'\in\mathcal R\cap\mathcal N$。由引理 4.1，

$$
A(x-x')\in\mathcal R\cap\mathcal N,
$$

所以 $\bar A$ 良定。$\bar B$ 的像落在 $\mathcal R$，故良定。

又因为 $\mathcal N\subseteq\ker C$，若 $x-x'\in\mathcal R\cap\mathcal N$，则

$$
Cx=Cx',
$$

故 $\bar C$ 良定。

原系统状态递推逐步取商，得到

$$
[x_{t+1}]
=
\bar A[x_t]+\bar B u_t,
\qquad
y_t=\bar C[x_t].
$$

归纳可知每一步读出相同。证毕。

这一定理说明「删掉因果沉默方向」不是近似，而是在声明的接口上保持全部响应的精确替换。

## 5. 最小性：任何线性因果摘要都必须容纳这个商

**定义 5.1（线性因果摘要）。** 设 $W$ 是有限维空间，线性映射

$$
\eta:\mathcal R\to W
$$

称为一个因果摘要，如果存在某个递推与读出机制，使得对所有 $x\in\mathcal R$，摘要 $\eta(x)$ 足以产生从 $x$ 出发的全部未来读出，并且不再访问 $x$ 的其余坐标。

仅需要一个必要性质：若 $\eta(x)=\eta(x')$，则所有未来读出必须相同。

**定理 5.2（因果维数下界）。** 任意线性因果摘要满足

$$
\boxed{
\dim W\ge d_{\mathrm{causal}}.
}
$$

等号由定理 4.2 的商模型取得，因此 $\mathcal Z$ 是线性意义下的最小因果边界。

### 证明

若 $\eta(x)=\eta(x')$，摘要无法区分两者，因而必须有 $x\sim_{\mathrm{op}}x'$。由定理 3.1，

$$
\ker\eta\subseteq\mathcal R\cap\mathcal N.
$$

由秩—零化度定理：

$$
\begin{aligned}
\dim W
&\ge \operatorname{rank}\eta\\
&=\dim\mathcal R-\dim\ker\eta\\
&\ge \dim\mathcal R-\dim(\mathcal R\cap\mathcal N)\\
&=d_{\mathrm{causal}}.
\end{aligned}
$$

商模型的摘要 $x\mapsto[x]$ 维数正好为 $d_{\mathrm{causal}}$，故下界可达。证毕。

这里的「最小」带有明确量词：它针对所有 $x\in\mathcal R$、所有允许未来输入词和所有声明的未来读出成立。若只要求某个固定初态或某个有限实验词集合，所得维数可以更小，但那是换了任务。

## 6. 响应 Hankel 矩阵读出同一个维数

定义脉冲响应块：

$$
M_k=CA^{k-1}B,
\qquad k\ge1.
$$

对正整数 $r,s$ 定义块 Hankel 矩阵：

$$
\mathsf H_{r,s}
=
\begin{bmatrix}
M_1&M_2&\cdots&M_s\\
M_2&M_3&\cdots&M_{s+1}\\
\vdots&\vdots&&\vdots\\
M_r&M_{r+1}&\cdots&M_{r+s-1}
\end{bmatrix}.
$$

它只记录输入脉冲如何经过过程影响未来读出，不直接暴露内部坐标。

**定理 6.1（稳定 Hankel 秩等于最小因果维数）。** 若 $d=d_{\mathrm{causal}}>0$，则对所有 $r,s\ge d$，

$$
\boxed{
\operatorname{rank}\mathsf H_{r,s}=d.
}
$$

### 证明

在商模型上定义长度为 $r$ 的可观测矩阵和长度为 $s$ 的可控矩阵：

$$
\mathsf O_r=
\begin{bmatrix}
\bar C\\
\bar C\bar A\\
\vdots\\
\bar C\bar A^{r-1}
\end{bmatrix},
\qquad
\mathsf C_s=
\begin{bmatrix}
\bar B&\bar A\bar B&\cdots&\bar A^{s-1}\bar B
\end{bmatrix}.
$$

逐块相乘得到

$$
\mathsf H_{r,s}=\mathsf O_r\mathsf C_s.
$$

商模型按定义既可达又可观测：$\operatorname{im}\mathsf C_d=\mathcal Z$，且

$$
\bigcap_{k=0}^{d-1}\ker(\bar C\bar A^k)=\{0\}.
$$

前者意味着 $\mathsf C_d$ 满行秩，后者意味着 $\mathsf O_d$ 满列秩。有限维线性代数给出

$$
\operatorname{rank}(\mathsf O_d\mathsf C_d)=d.
$$

当 $r,s\ge d$ 时，$\mathsf O_d$ 和 $\mathsf C_d$ 都是相应矩阵的子矩阵，故秩至少为 $d$；而乘积的中间空间维数为 $d$，秩至多为 $d$。因此秩恰为 $d$。证毕。

**推论 6.2（只看响应就能发现隐藏维数的上限）。** 当足够长的输入—输出脉冲实验可取得时，稳定的 Hankel 秩给出最小因果边界维数；任何额外内部坐标都不会增加该秩。

这个读数有一个清楚的范围：它识别的是零初态、线性、时不变接口下的输入—输出因果内容。非线性、时变或带隐藏初始来源的模型需要改写响应矩阵，不能直接套用本定理。

## 7. 有限观测窗造成的暂时沉默

现实实验常只允许观察 $T$ 个未来步。定义有限窗不可观测空间：

$$
\mathcal N_T
=
\bigcap_{0\le k<T}\ker(CA^k),
$$

以及有限窗因果维数：

$$
d_T
=
\dim\mathcal R-\dim(\mathcal R\cap\mathcal N_T).
$$

**定理 7.1（有限窗维数单调且最终稳定）。**

$$
d_T\le d_{T+1}\le d_{\mathrm{causal}},
\qquad
d_T=d_{\mathrm{causal}}\quad\text{当 }T\ge n.
$$

### 证明

增加一个交集项只能缩小空间：

$$
\mathcal N_{T+1}
=
\mathcal N_T\cap\ker(CA^T)
\subseteq\mathcal N_T.
$$

所以 $\dim(\mathcal R\cap\mathcal N_T)$ 不增，$d_T$ 不减；显然 $\mathcal N\subseteq\mathcal N_T$，故 $d_T\le d_{\mathrm{causal}}$。

Cayley–Hamilton 表明 $A^k$（$k\ge n$）是前 $n$ 个幂的线性组合，因此

$$
\bigcap_{0\le k<n}\ker(CA^k)
=
\bigcap_{k\ge0}\ker(CA^k)=\mathcal N.
$$

故 $T\ge n$ 时两者相同。证毕。

**反例 7.2（延迟链的未来可观测性）。** 令 $X=\mathbb R^n$，$B=e_1$，$C=e_n^{\mathsf T}$，并令

$$
Ae_i=e_{i+1}\quad(1\le i<n),
\qquad
Ae_n=0.
$$

一次输入脉冲沿链逐步移动。它在前 $n-1$ 个未来步对读出完全沉默，却在第 $n$ 步出现。因此

$$
d_T<d_{\mathrm{causal}}
\qquad(T<n)
$$

可以发生。有限窗口中的「没有因果影响」只说明当前窗口未分辨出该方向，不能升级成全时域禁止。

这与无限时域的因果沉默严格区分：

$$
\text{暂时看不见}
\ne
\text{对所有未来实验都看不见}.
$$

## 8. 两类隐藏方向与同响应模型

可把内部方向按接口作用分成三类：

1. **不可达方向**：不属于 $\mathcal R$。它们可能改变内部方程，却从零初态和允许输入出发永远不会被激活；
2. **可达但不可观测方向**：属于 $\mathcal R\cap\mathcal N$。它们能被干预激活，也可能在内部演化，但不改变任何未来读出；
3. **因果可见方向**：在商 $\mathcal Z$ 中有非零类。它们既能由允许输入触达，又能在某个未来读出中产生差异。

**命题 8.1（隐藏扩张不改变接口响应）。** 给定一个系统 $(A,B,C)$，在状态空间加入一个附加空间 $H$，构造块对角扩张

$$
A'=
\begin{bmatrix}
A&0\\
0&D
\end{bmatrix},
\qquad
B'=
\begin{bmatrix}
B\\
G
\end{bmatrix},
\qquad
C'=
\begin{bmatrix}
C&0
\end{bmatrix},
$$

其中 $D,G$ 任意。若附加块从零初态只进入 $H$ 且不耦合回原块，则所有输入—输出响应仍与原系统相同。

### 证明

由块三角递推，$A'$ 的上左块为 $A$，而 $C'$ 只取上方坐标。因此对任意输入词，输出满足原系统同样的递推，附加块完全被读出投影消去。证毕。

命题 8.1 说明「内部坐标更多」不能单独证明「因果内容更多」。只有它们在允许干预和合法读出之间留下不可消去的响应，才会增加商维数。

## 9. 对位置事件接口的解释

设某个局域位置事件由线性读出分量 $c_R^{\mathsf T}x_t$ 表示，或在一个线性化的概率响应模型中由若干行组成的矩阵 $C_R$ 表示。相应的局部不可观测空间为

$$
\mathcal N_R
=
\bigcap_{k\ge0}\ker(C_RA^k).
$$

对一个可达状态差 $z\in\mathcal R$：

- 若 $z\in\mathcal N_R$，任何未来输入下，区域 $R$ 的事件记录都不变；
- 若 $z\notin\mathcal N_R$，存在某个有限未来时刻使局域事件读出产生差异；
- 若 $z\notin\mathcal R$，允许接口根本不能把该差异从零初态激活出来。

所以「一个位置能否成为因果目标」至少要问两个问题：

$$
\boxed{
\text{输入能否把差异送到该位置？}
\quad\text{以及}\quad
\text{该位置的读出能否把差异送回记录？}
}
$$

这补上了单纯画一条空间邻接边的缺口。邻接只表示某种潜在耦合；因果接口还要求可达性、可观测性和允许的实验窗口。

## 10. 结论：最小因果边界是一个接口商

本卷的核心等式是：

$$
\boxed{
\mathcal Z
=
\frac{\mathcal R}{\mathcal R\cap\mathcal N}.
}
$$

它把三种常被混淆的陈述拆开：

- 内部方程中存在一个坐标；
- 允许干预能够激活这个坐标；
- 某个未来事件记录能够区分这个坐标。

只有第二与第三同时成立时，该方向才是接口上的因果内容。有限实验窗还会把真正可见方向暂时隐藏，稳定的 Hankel 秩则给出长期输入—输出关系所需的最小边界维数。

因此，关系几何里的「边界」可以有一个严格的操作性含义：

> **边界不是包住全部内部状态的壳，而是所有允许改变与未来记录之间必须经过的最小商空间。**

当这个商为空时，接口上没有可检测因果作用；当商非空时，其每个非零类都由某个可达干预和某个未来读出共同见证。这个结论只对已声明的模型、输入族、读出族和时间范围负责；改变接口，就可能改变边界。

## 追加锚（本行以下为增补区）
