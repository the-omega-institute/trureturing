# 干预与条件化的交换秩及后选择箭头

> **本卷的机器契约(逐条可查,落地后不改)。** 消化器 `generic-v1`;地址由本文件字节决定。本卷是 `docs/develop/theory/` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。

## 1. 定位、状态与产地

**参考输入,不是真源。** 上一卷 `CAUSAL_POSTSELECTION_GATE_INTERVENTION_CLOSURE.md` 给出两个模型在输入专属接口下的碰撞。本卷固定一个有限潜变量模型，研究另一条更细的关系：先对选择事件条件化再干预，和先干预再对选择事件条件化，何时给出同一后继状态。

**AHH 候选。**

$$
\boxed{
\text{后选择不产生“反向因果”这一说法，只有在选择似然对输入与潜变量可分离时才可安全使用；}
\\
\text{选择似然矩阵出现非零二阶行列式，干预与条件化便不交换，并能被一个读出接口显现。}
}
$$

这里的箭头是条件分布中的操作性箭头，不是时间倒流，也不是超光速作用。条件化事件必须被当作关系结构中的一个端口，而不能默认为透明的观察。

**产地。** 本卷沿用 `consensus-rnd:sshx` 研究方向；ChatGPT Pro 研究席返回了秩一交换与 Hilbert 投影容量候选，主循环独立重写并核对有限代数。codex 设计席因宿主负载门未发射，故不把其意见计入。本文的文献状态只申报碰撞选择、干预语义、条件独立性和投影距离界的已知成分，不申报本卷组合的原创性。

## 2. 有限潜变量与两个操作顺序

**定义 2.1（潜变量模型）。** 取有限集 $\mathcal U$、输入集 $\mathcal X$、输出集 $\mathcal Y$，以及满支撑先验 $\pi\in\Delta(\mathcal U)$。对每个 $x\in\mathcal X$ 与 $u\in\mathcal U$，给定输出核

$$
K_x(y\mid u),
\qquad
\sum_{y\in\mathcal Y}K_x(y\mid u)=1.
$$

潜变量先按 $\pi$ 生成，外部输入 $X$ 由实验者选择，输出 $Y$ 按 $K_X(\cdot\mid U)$ 生成。选择标签 $Z$ 只保留一个固定值 $z$ 供条件化；记

$$
s_x(u)=\Pr(Z=z\mid\operatorname{do}(X=x),U=u).
$$

本卷先假定 $s_x(u)>0$ 对所有 $x,u$ 成立，因此所有条件分母都正。允许零值时，只需把陈述限制到相关正支撑并逐项检查条件事件是否可达。

**定义 2.2（基线策略与选择后先验）。** 令 $q\in\Delta(\mathcal X)$ 为一个满支撑基线输入策略，并记

$$
\ell_q(u)=\sum_{x\in\mathcal X}q(x)s_x(u),
\qquad
L_q=\sum_u\pi(u)\ell_q(u),
\qquad
L_x=\sum_u\pi(u)s_x(u).
$$

选择事件发生后，基线策略下的潜变量后验为

$$
\pi_{q,z}(u)=\frac{\pi(u)\ell_q(u)}{L_q},
$$

而固定输入 $x$ 后的后验为

$$
\pi_{x,z}(u)=\frac{\pi(u)s_x(u)}{L_x}.
$$

**定义 2.3（两种顺序）。** 对一个固定输入 $x$，定义两种输出律：

$$
D_{\mathrm{select}\to\mathrm{do}}^{q,z,x}(y)
=\sum_u\pi_{q,z}(u)K_x(y\mid u),
$$

表示先在基线策略下看到 $Z=z$，再把下一次输入固定为 $x$；以及

$$
D_{\mathrm{do}\to\mathrm{select}}^{z,x}(y)
=\sum_u\pi_{x,z}(u)K_x(y\mid u),
$$

表示先固定输入 $x$，再在该轮对 $Z=z$ 条件化。前者把 $Z=z$ 当作已经交付的历史记录，后者把它当作当前轮的选择门。

若对所有允许的输出核 $K$ 两者相同，称选择与干预在潜变量接口上交换；若只对一个指定 $K$ 相同，称它们在该读出上交换。

## 3. 交换的精确秩判据

**定理 3.1（全读出交换当且仅当选择似然秩一）。** 假设 $s_x(u)>0$。以下条件等价：

1. 对任意满支撑先验 $\pi$、任意满支撑基线策略 $q$、任意 $x$，以及任意有限输出字母表和输出核族 $K_x(\cdot\mid u)$（特别包括取 $\mathcal Y=\mathcal U$ 的恒等读出），都有

$$
D_{\mathrm{select}\to\mathrm{do}}^{q,z,x}
=
D_{\mathrm{do}\to\mathrm{select}}^{z,x}.
$$

2. 对每个 $x$，存在正数 $\alpha_x$ 与同一个正函数 $\beta:\mathcal U\to(0,\infty)$，使

$$
\boxed{s_x(u)=\alpha_x\beta(u)\quad\text{对所有 }x,u.}
$$

3. 选择似然矩阵 $S=(s_x(u))_{x,u}$ 的所有二阶行列式为零：

$$
\boxed{
 s_x(u)s_{x'}(u')=s_x(u')s_{x'}(u)
 \quad\text{对所有 }x,x',u,u'.
}
$$

换言之，选择事件对输入和潜变量的依赖必须分离为一个输入因子与一个潜变量因子；这正是正矩阵的秩一条件。

**证明。**

**(2) 推出 (1)。** 若 $s_x(u)=\alpha_x\beta(u)$，则

$$
\ell_q(u)=\beta(u)\sum_xq(x)\alpha_x.
$$

代入定义，基线选择后的后验为

$$
\pi_{q,z}(u)=\frac{\pi(u)\beta(u)}{\sum_v\pi(v)\beta(v)},
$$

而固定 $x$ 后的后验同样为

$$
\pi_{x,z}(u)=\frac{\pi(u)\alpha_x\beta(u)}{\alpha_x\sum_v\pi(v)\beta(v)}
=\frac{\pi(u)\beta(u)}{\sum_v\pi(v)\beta(v)}.
$$

两个潜变量后验逐点相同，经过任意 $K_x$ 推出输出律相同。

**(2) 与 (3) 等价。** 正矩阵的任意一个非零行可以取作 $\beta$ 的标度基准；所有二阶行列式为零恰好说明每一行都与它成比例。反过来，外积 $\alpha\beta^{\mathsf T}$ 的二阶行列式显然全为零。

**(1) 推出 (2)。** 取输出字母表 $\mathcal Y=\mathcal U$，并令可选读出核为恒等核 $K_x(y\mid u)=\mathbf1_{y=u}$。条件 (1) 于是要求

$$
\pi_{q,z}=\pi_{x,z}
$$

对所有满支撑 $\pi,q,x$ 成立。固定任意一个满支撑 $\pi,q$，归一化等式给出每个行向量 $s_x(\cdot)$ 都与混合行向量 $\ell_q(\cdot)$ 成比例；因此任意两行成比例，得到 (2)。证毕。

**推论 3.2（固定读出下的较弱判据）。** 对一个指定输出核 $K$，秩一是交换的充分条件，但不必是必要条件。必要且充分的条件是

$$
\sum_u\bigl(\pi_{q,z}(u)-\pi_{x,z}(u)\bigr)K_x(y\mid u)=0
\quad\text{对所有 }y.
$$

因此，读出会把潜变量后验差异压入自己的核；“没有看见交换失败”只能说明该接口看不到那一部分差异。

**证明。** 直接把两种输出律相减。证毕。

## 4. 非秩一时必有可见后选择箭头

**定理 4.1（非零二阶行列式的最小见证）。** 若选择矩阵 $S$ 不是秩一，则存在 $x,x',u,u'$ 使

$$
\Delta=s_x(u)s_{x'}(u')-s_x(u')s_{x'}(u)\ne0.
$$

存在一个两元素潜变量子模型、一个满支撑先验、一个满支撑基线策略和一个有限输出读出，使选择与干预不交换；因此“选择事件制造后继输入差异”不是纯语言现象。

**证明。** 取该非零行列式涉及的两个输入和两个潜变量，限制到这四个坐标。若某个列或行在限制后不具正质量，可把先验和策略取为这两个坐标上的任意正权并归一化；正假设保证两个选择事件分母非零。取恒等读出 $Y=U$。若两种后验在这两个坐标上相同，则其坐标比相同，从而

$$
\frac{s_x(u)}{s_x(u')}=\frac{s_{x'}(u)}{s_{x'}(u')},
$$

与 $\Delta\ne0$ 矛盾。故输出分布不同。证毕。

**命题 4.2（交换缺口的精确距离）。** 对任意指定 $\pi,q,x,K$，定义

$$
\Gamma_{q,z,x}(K)
=\operatorname{TV}\left(D_{\mathrm{select}\to\mathrm{do}}^{q,z,x},
D_{\mathrm{do}\to\mathrm{select}}^{z,x}\right).
$$

则 $\Gamma_{q,z,x}(K)=0$ 当且仅当推论 3.2 的每个输出坐标等式成立；当 $K$ 是恒等读出时，

$$
\Gamma_{q,z,x}(K)=\operatorname{TV}(\pi_{q,z},\pi_{x,z}).
$$

这给出一个接口依赖的后选择箭头强度，而不是把“有无箭头”压成单一图形标签。

**证明。** 总变差定义给出第一句；恒等读出只是把潜变量分布原样输出。证毕。

## 5. 投影扩张与可见顺序效应的锐利容量

**定理 5.1（Hilbert 投影容量）。** 固定基线输入 $a$、目标输入 $x$ 和选择标签 $z$。令

$$
f(u)=s_x(u),
\qquad
g(u)=s_a(u),
\qquad
\nu=B_a^z\pi,
\qquad
r(u)=\frac{f(u)}{g(u)}.
$$

写 $\bar r=\mathbb E_\nu[r]$，并令

$$
m=\min_{u\in\operatorname{supp}\nu}r(u),
\qquad
M=\max_{u\in\operatorname{supp}\nu}r(u).
$$

则有精确换测度式

$$
B_x^z\pi(u)=\nu(u)\frac{r(u)}{\bar r},
$$

以及

$$
\operatorname{TV}(B_x^z\pi,B_a^z\pi)
=\frac{1}{2\bar r}\mathbb E_\nu|r-\bar r|
\le
\frac{\sqrt M-\sqrt m}{\sqrt M+\sqrt m}.
$$

定义选择似然两行的投影扩张

$$
\Delta_z(a,x)=\log\frac{M}{m}
=\max_u\log\frac{s_x(u)}{s_a(u)}
-\min_u\log\frac{s_x(u)}{s_a(u)}.
$$

则对任意终端读出核 $K_x$，顺序效应满足

$$
\boxed{
R_{a,x,z}(\pi,K)
\le
\operatorname{TV}(B_x^z\pi,B_a^z\pi)
\le
\tanh\!\left(\frac{\Delta_z(a,x)}4\right).
}
$$

对所有允许的先验与读出取上确界时，上界可达：

$$
\boxed{
\sup_{\pi,K}R_{a,x,z}(\pi,K)
=\tanh\!\left(\frac{\Delta_z(a,x)}4\right).
}
$$

**证明。** 由 Bayes 公式，$\nu(u)\propto\pi(u)g(u)$，故

$$
B_x^z\pi(u)=\frac{\pi(u)f(u)}{\sum_v\pi(v)f(v)}
=\nu(u)\frac{f(u)/g(u)}{\mathbb E_\nu[f/g]}.
$$

这给出等式。由于 $r\in[m,M]$，固定其均值 $\bar r$ 时，凸函数 $t\mapsto|t-\bar r|$ 的端点表示给出

$$
\mathbb E_\nu|r-\bar r|
\le
\frac{2(M-\bar r)(\bar r-m)}{M-m}.
$$

除以 $2\bar r$，再对 $\bar r\in[m,M]$ 最大化；最大点是 $\bar r=\sqrt{Mm}$，最大值为

$$
\frac{\sqrt M-\sqrt m}{\sqrt M+\sqrt m}
=\tanh\!\left(\frac14\log\frac Mm\right).
$$

任意随机读出核都收缩总变差，得到第一项不等式。为达到上确界，在两个取到 $m,M$ 的潜变量上令 $\nu$ 的质量分别为

$$
\nu(r=m)=\frac{\sqrt M}{\sqrt M+\sqrt m},
\qquad
\nu(r=M)=\frac{\sqrt m}{\sqrt M+\sqrt m},
$$

并取 $\pi(u)\propto\nu(u)/g(u)$。若坚持先验满支撑，可在其余点加入趋于零的正质量，故上确界不变。最后用二值 Hahn 读出 $Y=\mathbf1_A(U)$，其中 $A$ 是 $B_x^z\pi-B_a^z\pi$ 的正部；该读出达到潜变量总变差。证毕。

**推论 5.2（投影零曲率）。** 对正选择似然，以下条件等价：

$$
\Delta_z(a,x)=0
\iff
s_x(\cdot)\text{ 与 }s_a(\cdot)\text{ 成比例}
\iff
\text{该输入对该选择事件不产生归一化顺序效应}.
$$

因此定理 3.1 的秩一条件可以读为：所有输入行之间的投影扩张都为零；定理 5.1 则给出偏离秩一时的精确可见容量。

## 6. 二状态对称见证与锐利边界

**定义 6.1（二状态选择门）。** 令 $\mathcal U=\mathcal X=\mathcal Y=\{0,1\}$，取 $0\le\varepsilon\le1$，并令

$$
S_\varepsilon=
\begin{pmatrix}
1&\varepsilon\\
\varepsilon&1
\end{pmatrix},
\qquad
s_x(u)=(S_\varepsilon)_{x,u}.
$$

令 $\pi(0)=\pi(1)=1/2$、$q(0)=q(1)=1/2$，并令 $Y=U$。无条件时 $Y$ 与 $X$ 独立；选择事件 $Z=1$ 的概率由 $S_\varepsilon$ 给出。

**命题 6.2（对称门的交换缺口）。** 对 $0\le\varepsilon\le1$，基线策略下先条件化再固定 $X=0$ 给出

$$
\Pr(U=0\mid Z=1)=\frac12,
$$

而先固定 $X=0$ 再条件化给出

$$
\Pr(U=0\mid\operatorname{do}(X=0),Z=1)=\frac1{1+\varepsilon}.
$$

因此

$$
\boxed{
\Gamma_{q,z,0}(\operatorname{id})
=\frac{1-\varepsilon}{2(1+\varepsilon)}.
}
$$

对 $X=1$，偏差方向相反而距离相同。交换在且仅在 $\varepsilon=1$ 时成立；此时选择矩阵为秩一。$\varepsilon=0$ 给出最大缺口 $1/2$，但每个相关条件事件仍有正概率。

**命题 6.3（二值选择器的双结果边界）。** 设 $Z\in\{0,1\}$，并要求归一化交换同时对 $Z=1$ 与 $Z=0$ 成立。若至少有两个输入和两个潜变量取值，且两种结果都有正概率，则选择核必须满足下列两种形状之一：

$$
\boxed{s_x(u)=p(x)}
\qquad\text{或}\qquad
\boxed{s_x(u)=q(u)}.
$$

前者表示选择只依赖输入，后者表示选择只依赖潜变量。两者都不允许输入与潜变量形成真正的交互。

**证明。** 对 $Z=1$ 的切片，定理 3.1 给出 $s_x(u)=\alpha(x)\beta(u)$；对 $Z=0$ 的切片，$1-s_x(u)$ 也必须秩一。任取两行 $x,a$ 与两列 $u,v$，后者的二阶行列式为

$$
(\alpha(x)-\alpha(a))(\beta(v)-\beta(u)).
$$

它必须为零。若 $\alpha$ 在输入上不恒定，则 $\beta$ 在潜变量上恒定，得到第一种形状；若 $\alpha$ 恒定，则得到第二种形状。证毕。

**证明。** 基线混合对两个 $u$ 的选择似然都是 $(1+\varepsilon)/2$，所以基线后验保持均匀。固定 $X=0$ 后，两列质量为 $1$ 与 $\varepsilon$，归一化即得 $1/(1+\varepsilon)$ 与 $\varepsilon/(1+\varepsilon)$。二元分布与均匀分布的总变差距离是

$$
\left|\frac1{1+\varepsilon}-\frac12\right|
=\frac{1-\varepsilon}{2(1+\varepsilon)}.
$$

矩阵行列式为 $1-\varepsilon^2$，故在给定区间内秩一恰好对应 $\varepsilon=1$。证毕。

## 7. 与全局后选择门边界的关系

上一卷的门模型构造了两个不同的生成机制，它们在只允许操纵 $X$ 的基础合同下完全碰撞；本卷研究一个单一机制内部的两个操作顺序。两者的关系可以写成：

$$
\begin{array}{c}
\text{模型级不可区分}\
\text{(改变生成机制)}
\end{array}
\quad\Longrightarrow\quad
\text{需要打开 }S\text{ 才能分裂},
$$

而本卷给出更细的接口级判据：

$$
\begin{array}{c}
\text{机制固定}\
\text{(只改变操作顺序)}
\end{array}
\quad\Longrightarrow\quad
\text{秩一才允许条件化与干预交换}.
$$

秩一条件不是要求没有任何 $X$ 对可见记录的作用；它只要求选择对 $X$ 的改变可以被一个与潜变量独立的总体因子吸收。非秩一时，后选择会把输入的信息写入潜变量后验，随后任何能分辨该后验的输出接口都能看到差异。

## 8. 不能推广的边界与文献状态

**反例 8.1（条件分布中的箭头不是时间倒流）。** 命题 6.2 中 $Y=U$ 且无条件 $Y$ 与 $X$ 独立。先固定 $X$ 再选择 $Z=1$ 所得到的分布变化，来自选择后验的改变；它不构成从未来回到过去的动力学影响。

**反例 8.2（秩一不是固定读出的必要条件）。** 若 $K_x$ 把所有潜变量都映为同一个输出，则即便 $S$ 非秩一，推论 3.2 的输出差仍可为零。因而不能从一次粗粒化读数的交换推出潜变量接口已经交换。

**开放问题 8.3（带代价的部分开门）。** 本卷比较完全条件化和完全干预。若只能以有限样本、噪声选择器或部分软干预访问 $Z$，需要给出样本复杂度与可辨识距离的联合界；本文未给出统一统计估计定理。

**文献状态。** 碰撞器与选择偏差、干预与条件化的语义区分、以及条件独立的图模型判据都是成熟主题。本卷的秩一交换判据、二状态锐利见证和“固定读出可见性”分层，是这些成分的有限代数重组候选，不申报原创优先权。

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Berkson, 1946, *Limitations of the application of fourfold table analysis to hospital data*, `doi:10.1038/152309a0` | `literature-attested`:选择条件能够制造关联；不用于本卷的秩一充要式。 |
| Pearl, *Causality*, 2nd ed., UCLA 在线版 <https://bayes.cs.ucla.edu/BOOK-2K/> | `literature-attested`:观察、条件化与干预的语义差异及选择图；不用于本卷的有限见证优先权。 |
| Dawid, 1979, *Conditional independence in statistical theory*, `doi:10.1111/j.2517-6161.1979.tb01052.x` | `literature-attested`:条件独立的概率语义；不替代本卷的有限后验计算。 |
| Cohen and Fausti, *A sharp bound on the total variation distance between probability measures*, <https://arxiv.org/abs/2309.02413> | `literature-attested`:Hilbert 投影距离控制总变差的锐利双曲正切界；本卷把它代入有限 Bayes 选择行的似然比。 |
| — | `repo-derived`:定理 3.1、推论 3.2、定理 4.1、命题 4.2、定理 5.1、命题 6.2 与命题 6.3 的自包含推导。 |
| — | `candidate/recombination`:把选择似然矩阵的秩与干预—条件化交换接口相连；不构成原创性声明。 |

**核验边界。** 全部陈述均在有限集、正概率和显式归一化条件下。本文没有执行 Lean 编译，也没有把有限代数核验冒称为形式证明；零选择概率、无限轮、统计估计和现实世界选择机制需要额外假设。

## 追加锚（本行以下为增补区）
