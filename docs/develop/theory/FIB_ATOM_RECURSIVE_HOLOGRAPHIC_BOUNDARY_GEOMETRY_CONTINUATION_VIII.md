# FIB-ATOM 递归全息边界几何 VIII：原生守卫与静态坐标的动力学缺口

**约定 250.0（来源与任务）。** 本卷接续[卷 VII](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VII.md) §§239–249。原生窗口合同取自[关系延拓几何](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 定义 7.1，亦见[内生三轴与预测接口](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md) 定义 6.4；静态完整世界取自 [strict-real 支持卷 VII](https://github.com/the-omega-institute/trureturing/blob/50c4fcacf296ffa60e50806a835d49e383ae7b3d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md) 定义 1.1、§§21–24，以下记为 [SJ]。不同来源之间的对应均须显式给出。有限维递推和逆函数定理是经典中间工具；本卷的承重内容是它们与这两份来源合同的接合及失败见证，属 `repo-derived`，不作文献优先权主张。

## 250. 高到低守卫对可逆线性 null 表示的条件性障碍

**定义 250.1（固定的原生前缀与合法性目标）。** 令

$$
\Sigma=\{\mathrm{null},[2],[3],[25],[5]\}.
$$

窗口按高到低读入，每个印刷三位仍按低到高书写；单位位固定为零，允许高端补零，空词合法，没有 End 动作或最高窗非空检查。状态含接缝 $s\in\{0,1\}$ 与整数组成 $n\in\mathbb Z^2$，初态为 $(0,0)$。在合法边上

$$
n'=Sn+d_\sigma,\qquad
S=\begin{pmatrix}1&2\\2&3\end{pmatrix}.
\tag{250.1}
$$

全部接缝与位移为

| 字母 | 印刷三位 | $d_\sigma$ | 允许旧接缝 | 新接缝 |
| --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $000$ | $(0,0)$ | $0,1$ | $0$ |
| $[2]$ | $100$ | $(1,0)$ | $0,1$ | $1$ |
| $[3]$ | $010$ | $(0,1)$ | $0,1$ | $0$ |
| $[25]$ | $101$ | $(2,1)$ | $0$ | $1$ |
| $[5]$ | $001$ | $(1,1)$ | $0$ | $0$ |

令 $\mathcal P\subseteq\Sigma^*$ 为从初态出发的合法有限前缀，$s(w)$ 为其末接缝。固定目标

$$
G_5(w)=\mathbf 1_{\{w[5]\in\mathcal P\}}
       =1-s(w)\qquad(w\in\mathcal P).
\tag{250.2}
$$

它询问下一次 $[5]$ 是否允许，不要求真的执行失败动作，也不把错误结果删出比较。当前组成、方向读数和完整树是另外的任务。

**定义 250.2（待检验的表示合同）。** 所考察的表示由一个有限维实向量空间 $V$、映射 $v:\mathcal P\to V$、一个固定线性自同构 $A:V\to V$ 和一个固定线性泛函 $e:V\to\mathbb R$ 组成，要求

$$
v(w\mathrm{null})=Av(w),\qquad
e(v(w))=G_5(w)\qquad\text{对每个 }w\in\mathcal P.
\tag{250.3}
$$

这里不假设 $v$ 线性、连续或单射，不要求每个向量是可达状态，也不要求其余四个字母有线性实现。可逆性针对整个 $V$；固定的 $A,e$ 不能依前缀或未来测试长度更换。$\mathrm{null}$ 在原生合同中确实更新组成且重置接缝，未被解释为恒等。

**定理 250.3（原生接缝重置排除该表示合同）。** 定义 250.2 的表示不存在。更精确地，令 $H\ge0$ 为整数，只要求下列两条合法轨道的更新等式在 $0\le k<H$ 成立、目标等式在 $0\le k\le H$ 成立，则任何这样的可逆线性表示都须满足

$$
\dim V\ge H+1:
\qquad \mathrm{null}^k,\quad [2]\mathrm{null}^k.
\tag{250.4}
$$

证明。定义 250.1 的表逐项给出

$$
\begin{aligned}
G_5(\varepsilon)&=1,&G_5([2])&=0,\\
G_5(\mathrm{null}^k)&=1,&
G_5([2]\mathrm{null}^k)&=1\quad(k\ge1).
\end{aligned}
\tag{250.5}
$$

所有这些前缀均合法：$[2]$ 从初态合法，$\mathrm{null}$ 对两种接缝都允许，第一次 $\mathrm{null}$ 即将接缝置零。置 $x=v(\varepsilon)-v([2])$，由线性和更新等式得

$$
ex=1,\qquad eA^kx=0\quad(k\ge1).
\tag{250.6}
$$

设 $d=\dim V$。$d=0$ 已与 $ex=1$ 矛盾。对 $d\ge1$，写 $A$ 的特征多项式为

$$
\chi_A(t)=c_0+c_1t+\cdots+c_{d-1}t^{d-1}+t^d,
\qquad c_0=(-1)^d\det A\ne0.
$$

经典 Cayley–Hamilton 恒等式给

$$
0=e\chi_A(A)x
  =c_0ex+\sum_{j=1}^{d-1}c_jeA^jx+eA^dx=c_0,
\tag{250.7}
$$

矛盾。这个论证只使用 $k=0,\ldots,d$。故有限时域 $H$ 若允许 $d\le H$ 也矛盾，得到 (250.4)。所用中间机制是有限维线性表示的标量响应满足固定线性递推；其加权自动机背景见关系延拓几何 §6 所引 Berstel–Reutenauer，*Noncommutative Rational Series with Applications*，Chapter 2，以及 Balle–Panangaden–Precup，[*Singular Value Automata and Approximate Minimization*, arXiv:1711.05994v2](https://arxiv.org/abs/1711.05994v2)，§2、Theorem 2.1 的有限表示与 Hankel 秩对应。后者供应经典表示背景，不是本原生守卫障碍的逐字陈述。这里新增的是由原生两条轨道强制的 (250.6)，而非该经典递推工具。∎

**命题 250.4（有限时域与奇异表示的精确边界）。** 对任意 $H\ge0$，(250.4) 在它声明的两轨道测试族内可达到；若允许奇异的固定线性 $\mathrm{null}$ 更新，则全部原生前缀的守卫任务有二维表示。此外，固定可逆仿射 $\mathrm{null}$ 更新与固定仿射合法性读出也不能在有限维仿射空间上满足全部前缀合同。

证明。对有限时域取 $V=\mathbb R^{H+1}$，基为 $b_0,\ldots,b_H$，令 $A$ 作循环置换 $Ab_i=b_{i+1\bmod(H+1)}$，$e(b_i)=\mathbf1_{\{i=0\}}$。置

$$
u=\sum_{i=0}^H b_i,\qquad
v(\mathrm{null}^k)=A^ku=u,\qquad
v([2]\mathrm{null}^k)=A^k(u-b_0).
\tag{250.8}
$$

在 $0\le k\le H$ 恰得 (250.5)。到 $k=H+1$，第二轨道的目标读出返回零而原生目标为一；此构造只实现所声明的两轨道有限测试，不提供其余词的实现。

对全部守卫任务，将接缝零、一编码为 $b_0,b_1\in\mathbb R^2$。每个字母把允许的源基向量送到表中指定的新接缝基向量，把不允许的源基向量送到零；零保持零。初态为 $b_0$。合法前缀始终是对应的一个基向量，因而 $e=(1,0)$ 精确读出 (250.2)，而

$$
A_{\mathrm{null}}=
\begin{pmatrix}1&1\\0&0\end{pmatrix}
\tag{250.9}
$$

是奇异矩阵。归纳同时验证非法前缀吸收于零；如需区别已失败与合法接缝一，另用 $(1,1)$ 读出当前有效性。这个二维表示不承诺恢复组成。组成与合法性联合任务的既有六维表示见关系延拓几何定理 8.2；其 $\mathrm{null}$ 同样将两个接缝块汇入一个块。

最后，将有限维仿射空间选原点写成 $\mathbb R^d$。仿射更新 $z\mapsto Bz+c$ 与仿射读出 $\ell z+a$ 齐次化为

$$
\widehat A=\begin{pmatrix}B&c\\0&1\end{pmatrix},\qquad
\widehat e=(\ell,a),\qquad \widehat v(w)=(v(w),1).
$$

$B$ 可逆使 $\widehat A$ 可逆；全部前缀等式于是违反定理 250.3。这个结论不覆盖非线性合法性读出、依时更新或无限维表示，也不排除把环境、历史或额外记录作为表示的一部分；扩展后若仍声称有限维且满足 (250.3)，仍须接受同一检验。∎

## 251. augmented-J 的局部逆与未实例化的原生拉回

**定义 251.1（完整世界、基点和局部图）。** 取 [SJ] 的全部严格完整世界

$$
W=(P(r,b),g,d)\in\mathcal H,\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
$$

其中 $0<r<1$、$b>0$、$0\ne g\in\mathbb R[t]$、$\deg g\le3$、$d\in\mathbb R$，并保留该来源最初五个固定读数和原时钟。记

$$
\pi(W)=(p(W),v(W)),\qquad
\Gamma(W)=\Psi_J(W)=(p(W),v(W),a(W)).
\tag{251.1}
$$

$a$ 是同一完整世界的第七时钟 $J$ 响应；$g,d$ 不随目标更换。为避免与世界的 drift $d$ 混淆，本节不用 $d$ 表示维数。[SJ] 推论 24.2 供应

$$
p(W)\ge0\quad\Longrightarrow\quad
\operatorname{rank}d\Gamma_W=2
\tag{251.2}
$$

在完整二维解析 parent 上成立，包括奇异来源；它不是固定 drift 切片的秩断言。

**命题 251.2（局部来源恢复与原生守卫缺口同时存在）。** 固定任意 $W_0\in\mathcal H$ 且 $p(W_0)\ge0$。存在包含 $W_0$ 的 parent 邻域 $U$，使 $\Gamma|_U$ 单射，且每个确定性完整世界目标 $T:U\to Y$ 在 $\Gamma(U)$ 上唯一下降。然而，对同一个 $U$，存在保留原生合法前缀的来源扩张及其中两个合法状态，具有相同的基点和 augmented-J 边界，下一次 $[5]$ 的合法性却不同。这是静态局部逆不能自动供应原生拉回的失败见证。

证明。由 (251.2)，$p,v,a$ 中某两个分量 $(f,h)$ 在 $W_0$ 的二维 parent 坐标中有非零 Jacobian。经典逆函数定理给缩小后的 $U$，使

$$
\psi=(f,h):U\longrightarrow\Omega\subseteq\mathbb R^2
$$

为微分同胚。于是 $\Gamma|_U$ 单射，且在其实际像上

$$
L_U(q)=\psi^{-1}(\operatorname{pr}_{f,h}q),\qquad
\overline T(q)=T(L_U(q))
\tag{251.3}
$$

恢复来源和目标。基点由 $q$ 的前两个分量恢复。这个 $L_U$ 的类型是 $\Gamma(U)\to U$，不是原生历史到完整世界的映射；它只在该分支实际像上定义。上述局部逆推导亦是 [SJ] §24 明示的用途，不把它重新列为独立的新定理。

构造扩张

$$
\widehat U=U\times\mathcal P,\qquad
\widehat\pi(W,w)=\pi(W),\qquad
\widehat\Gamma(W,w)=\Gamma(W),\qquad
\widehat G_5(W,w)=G_5(w).
\tag{251.4}
$$

原生追加 $\widehat U_\sigma(W,w)=(W,w\sigma)$ 的定义域严格为

$$
\widehat D_\sigma
=\{(W,w):W\in U,\ w\in\mathcal P,\ w\sigma\in\mathcal P\}.
\tag{251.5}
$$

其中 $W$ 仍是一整个严格世界，未更换其 source、gain 或 drift，$w$ 则独立满足原生全部接缝守卫。取

$$
\widehat x_0=(W_0,\varepsilon),\qquad
\widehat x_1=(W_0,[2]).
$$

两点均在 $\widehat U$，且

$$
\widehat\Gamma(\widehat x_0)=\widehat\Gamma(\widehat x_1),\qquad
\widehat\pi(\widehat x_0)=\widehat\pi(\widehat x_1),\qquad
\widehat G_5(\widehat x_0)=1\ne0=\widehat G_5(\widehat x_1).
\tag{251.6}
$$

因此不存在 $\overline G_5:\widehat\Gamma(\widehat U)\to\{0,1\}$ 恢复该目标，也不存在边界子集 $D_5^B$ 使 $\widehat D_{[5]}=\widehat\Gamma^{-1}(D_5^B)$。若还要求具体的非空原世界来源，可取[支持卷 V](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md) 定理 1.2 的 $W_A$；它满足 $56\le p(W_A)\le58$，故 (251.2) 适用。

扩张 (251.4) 是两份已声明合同的数学直积反模型，不声称它已由原生 FIB 构造或物理协议实现，也不声称 $\Gamma$ 在 $\mathcal H$ 自身有此碰撞。它反驳的仅是“完整世界上的局部静态坐标逆必然恢复新增的原生守卫”。即便将追加后遗忘前缀的投影与 $U$ 上恒等映射作成交换图，(251.6) 的合法域差别仍在；该恒等映射本身也不是原 $J/M$ 时钟操作的识别。∎

**定义 251.3（原生拉回必须满足的方程）。** 要将卷 VII 命题 249.4 实例化，须另外指定一个原生来源域 $S_{\rm nat}$、基点 $\beta_{\rm nat}:S_{\rm nat}\to\pi(U)$、边界 $\gamma:S_{\rm nat}\to\Gamma(U)$、目标 $T_{\rm nat}$，以及映射 $L:S_{\rm nat}\to U$。对每个声明的原生部分操作 $u_\sigma:D_\sigma^{\rm nat}\to S_{\rm nat}$，还须指定同类型来源操作 $U_\sigma:D_\sigma^{\rm src}\to U$。所需等式是

$$
\begin{gathered}
\pi\circ L=\beta_{\rm nat},\qquad
\Gamma\circ L=\gamma,\qquad
T\circ L=T_{\rm nat},\\
D_\sigma^{\rm nat}=L^{-1}(D_\sigma^{\rm src}),\qquad
L(u_\sigma x)=U_\sigma(Lx)\quad(x\in D_\sigma^{\rm nat}).
\end{gathered}
\tag{251.7}
$$

若结论声称边界本身决定合法性，还要求 $D_\sigma^{\rm src}$ 在 $\Gamma$ 纤维上饱和；在单射分支 $U$ 内自动满足这一项。若操作离开 $U$，则必须给出目标分支及那里的边界和图，不能继续套用 $L_U$ 的定义域。完整来源恢复还须 $L$ 对声明的原生来源等价类单射。向原生来源传递某一逃逸对，须两个端点均在 $L$ 的像中，且对应历史可以同时合法提升；正向目标因子化本身不提供这些提升。

**命题 251.4（该来源桥的实际未定项）。** (251.2) 与 (251.3) 只供应 strict-real 分支内部的来源逆。原生高到低窗口与原 $J/M$ 时钟是不同操作合同；没有给出 (251.7) 中的 $S_{\rm nat},L,U_\sigma$ 及其等式时，不能从前者推出原生目标或合法域的拉回。特别地，若原生历史映射 $i:\mathcal P\to S_{\rm nat}$ 满足 $T_{\rm nat}\circ i=G_5$，且候选向量边界 $v=\gamma\circ i$ 服从固定可逆线性 $\mathrm{null}$ 更新，则不能再以固定线性效应 $e$ 恢复该目标。

证明。静态逆的定义域和陪域在 (251.3) 已固定，不能仅靠改名变成 $S_{\rm nat}\to U$。来源扩张 (251.4) 中的投影 $L(W,w)=W$ 保基点，且 $\Gamma L=\widehat\Gamma$，但 (251.6) 排除 $T L=\widehat G_5$ 及精确合法域反像等式。因此前两式不蕴含其余式。对最后一项，若另有 $e(v(w))=T_{\rm nat}(i(w))$，则它等于 $G_5(w)$，与固定可逆 $\mathrm{null}$ 更新共同给出 (250.3)，违反定理 250.3。这里失败的是这些联合假设，不是所有可能的原生拉回。∎

## 252. 对三维载体判据保留的联合义务

**命题 252.1（表示障碍不选择空间维数）。** 定理 250.3 对所有有限线性维数同样成立，因此它本身不能在三维与其他有限维物理配置载体之间作选择。命题 251.2 的 parent 维数二与三个实响应也不能取代卷 VII 定义 248.1 的三维配置—预测证书。

证明。定理 250.3 的量词是全部有限维 $V$；命题 250.4 又给出离开可逆性后确实存在的原生守卫表示。因而被排除的是“有限维、固定可逆更新、固定线性合法性读出、精确全前缀”这一联合合同。物理配置维数没有被这些假设识别为 $\dim V$，不能由此取得空间维数结论。

对于 [SJ]，三分量 $\Gamma$ 在二维 parent 上的局部秩为二，只给该来源的局部静态坐标。命题 251.2 已在保留它的局部逆时产生守卫逃逸，故还须先解决 (251.7) 的来源及操作对应。其后，occurrence 到配置载体的注入、统一分辨率与 packing 预算、实际运输与 holonomy、细化嵌入与极限紧致性，仍分别是卷 VII §§239–248 的独立输入。这里没有构造它们。

同样，[SJ] §24 的局部秩结论没有断言跨分支单射；卷 VII 定义 249.2 的 $D_J\cap D_M$ 仍保留同一完整 child 内的两组独立见证对。局部逆、直积反模型与本卷的守卫障碍均未给出该全局集合的存在或排除。任何把这些任务合并的结论都须在同一实际来源、允许历史和共同基点上同时满足它们，不能由各自分立的可达性拼成联合实现。∎

## 追加锚（本行以下为增补区）
