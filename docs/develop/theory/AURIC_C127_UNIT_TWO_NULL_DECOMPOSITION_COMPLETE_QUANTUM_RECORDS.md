# 单位不能拆成两个零

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC 量子关系研究

从一个内部单位到完整量子记录

C127

两段各自真正为零的历史，

不能合成一段完整的单位历史。

$$
Q(e)=1,\qquad
 \boxed{\nexists h:\ Q(h)=Q(e-h)=0.}
$$

由全部原记录的归一化取得单位；只禁止它被双零拼成。
在原完整 Hermitian 历史域内，这足以推出每个记录过程完全正，并导出各支效果的非负性与上界。
本轮只提出这一条候选，不再把任意端点的零差传递或逐支正效果当作新增前件。

固定源码：`7c2b901642e2`
提交时点：2026-11-04 06:16:14，Asia/Singapore
对应 2026-11-03 22:16:14 UTC

自包含工作稿：定义、证明、抛物面几何与有限证据

## 摘要

C126 要求所有零差都能传递，并从单事件的非负单位效果选择正取向。C127 回溯到一份完整原记录：只保留复线性、保伴随及 $\sum_j\Phi_j(I)=I$，不预设任何支效果为正。共同归一输入给单位历史 $e$，满足 $Q(e)=1$。唯一候选是 $e$ 不能写成两份自比较均为零的历史之和。

核心等价在任意维 Hermitian 空间上成立，不依赖辅助正内积或谱分解。若存在负方向 $n$，先扣除沿 $e$ 的分量，再缩放为 $Q(w)=-1/4$，则 $e/2+w$ 与 $e/2-w$ 均为零，却合成为单位。反之，正形式的零集合为线性根空间，不能双零合成单位。

对完整有限记录域，这给出

$$
\text{单位不可双零分解}
 \Longleftrightarrow Q_{\rm rec}\ge0
 \Longleftrightarrow C_j\ge0\ (\forall j)
 \Longleftrightarrow \Phi_j\text{ 全部 CP}.
$$

支效果 $0\le\Phi_j(I)\le I$、C126 的零差传递及全部比较替换性均成为推论。固定一个端点不等于只检查一个输入实验；完整记录基准和原相干历史域仍须保留。

固定单位后，一段历史 $z$ 与它的二元关系只剩三个实数：

$$
\Gamma(e,z)=x+iy,\qquad s=Q(z),\qquad
 \boxed{s\ge x^2+y^2.}
$$

这是旋转抛物面上方的区域，也是二阶正矩阵锥的单位截面；按迹归一后与 Bloch 球去南极对应。抛物面以下的任一点都能经同域改写与缩放，变成单位的双零分解。

候选还推出紧界

$$
Q(h)+Q(e-h)\ge\tfrac12.
$$

在固定系数半径 $R$ 内，这一不等式的最大亏损为 $D_R=2R^2b$，其中 $b$ 是完整记录关系矩阵的最大负谱幅度；不再需要 C126 的最大正特征值。精确双零见证的最小中心半径为 $1/(2\sqrt b)$，说明数学见证存在不意味着统一有界的实际成本。

本轮核读仓库新追加的原返回尺度与指定 Lorentz 比较群分类，以及一项确有 Lean 证明体的有限矩阵界。前者仍保留完整原尺度与其他重构前件，后者已使用迹概率定义；均不被误述为从本轮候选独自导出复数、Born 或标准模型。本稿完整重建所需有限量子规则，并明确效果概率、独立复合与时钟等接口。

**白话。**不必先保证整个世界里每一种“相同”都可传递。先拿完整原记录中已经确定的一份单位，要求它不能由两份真正的零拼成。只要关系中有负的余量，就能把它放到单位的一半两侧，让两边各自相消，合起来却仍是单位。排掉这件事，就会迫使完整关系为正，零差才可以可靠地合并，量子过程才与全部内部记录相容。

## 目录

- [1. 回溯的位置与本轮源码进展](#section-1)
- [2. 唯一候选：单位不可由两个零历史拼成](#section-2)
- [3. 一个单位参照的三维抛物面](#section-3)
- [4. 二读数的有限证据与见证半径](#section-4)
- [5. 由完整单位发展有限量子理论](#section-5)
- [6. 观察者、内部单位与整体关系](#section-6)
- [7. 本轮唯一完整候选](#section-7)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 回溯的位置与本轮源码进展

<a id="sec-c127-scope"></a>

### 1.1 少一个全端点要求，撤去逐支正效果前件

C126 已证明：不定 Hermitian 形式的每个向量都能写成两个零向量之和。因此本轮无需先检查所有零差链是否传递，只要阻止这一后果发生在一份固定的、已归一的单位历史上。
同时把单事件放回已经声明的完整原记录族，正取向便可由 $\sum_j\Phi_j(I)=I$ 供应；不用先分别要求 $0\le\Phi_j(I)\le I$。

| 项目 | C126 | C127 |
|---|---|---|
| 唯一新增要求 | 全端点的零差传递 | 一个单位端点不可双零分解 |
| 正向来源 | 各事件非负单位效果 | 全部原记录的单位归一化 |
| 逐支效果不等式 | 前件 | 结论 |
| 共同滤片 | 已撤去 | 不再引入 |
| 完整相干历史 | 保留 | 保留 |
| 核心证明 | 不定形式的零集合分类 | 单位与一个负方向的二维改写 |
| 三维截面 | 归一化二元 Gram 球 | 固定单位对角项的抛物面 |

这是在原完整记录已供应时的结构缩减。对一份未给补事件的孤立操作，本轮不能凭空补出真实失败装置；只给条件成功态也不能替代完整归一化。
单位基准保留全部记录，改变的历史仍含所有已声明输入方向。因而这里不声称实际实验成本处处降低，也不把等价刻画宣称为文献首发或已确认的新物理定律。

### 1.2 固定快照与真实新增量

本稿固定源码 `7c2b901642e29adbf2907b53d6a5f7db831e7df1`，提交时点为 2026-11-04 06:16:14（Asia/Singapore）。相对前轮 `460cf8b49a93`，比较接口的文件列表在 300 项截断；本轮改以不截断 Git 子树逐项核对。
在 `docs/develop/theory` 的 1225 份来源中，仅 C123/C124 文稿追加第 18–20 节；在 `D5/S3/Quantum` 中，仅新增一份 AF 矩阵界 Lean 文件。这个声明只覆盖上述两个完整子树，未宣称审计全仓。

### 1.3 原返回尺度决定的是哪一个更大结构

PR #26220 的新段先保留同源全未来响应、全部成功失败及原细标签，再给定四维 Lorentz 兼容锥、原旋转群闭包和全载体的具名正返回

$$
US=SU=qI,\qquad 0<q<1.
$$

它还要求 $S,U$ 在整个锥上质量不增，指定数学群为
$G=(\overline{\langle\mathcal R,S,U\rangle})^0$，闭包取于 $GL(V)$。
令 $c=(1,0)$、$u(t,w)=t$、

$$
\lambda=|\det_\mathbb R S|^{1/4},\qquad
 \chi=\operatorname{arcosh}\frac{u(Sc)}\lambda.
$$

新定理给出 $qe^\chi\le\lambda\le e^{-\chi}$，并在这些前件下准确刻画：指定群在整个锥内部传递，当且仅当

$$
Sc\notin\mathbb R_+c,
 \qquad \frac{\log\lambda}{\log q}\notin\mathbb Q.
$$

数学逆、闭包和连通参数没有因此成为实际可调用门；有限精度频率也不认证对数比无理 [1](#ref-repo-c127-native)。

这里 $\operatorname{Ad}_A(X):=AXA^*$。原文给了可重算的模型：$A=\operatorname{diag}(1,1/2)$，$S=\operatorname{Ad}_A$，
$B_q=\sqrt q\,\operatorname{diag}(1,2)$，$U_q=\operatorname{Ad}_{B_q}$，分别取 $q=1/4$ 与 $1/9$，且各自保留完整失败补支。
两份所选成功词的条件作用相同，原成功率和失败效果不同；$\lambda=1/2$、$\chi=\log2$，两份指定群分别为 $SO^+(1,3)$ 与 $\mathbb R_{>0}SO^+(1,3)$。
这说明被条件化丢掉的原尺度能改变更大结构。它没有独自补出复中心、Born、CP 或一般仪器组装；本轮将其用作“先保留原记录，再取商”的具体边界。

### 1.4 新增 Lean 证明与其概率前件

PR #26216 新增 `AbedNikolaevaNovikovAFDensityBound.lean`，包含实际的定理证明体。其矩阵结论是：$A\ge0$、$B=B^*$、维数为 $n$ 时，

$$
A\le n\,|A+iB|,
$$

并在 $n\ge1$、$A+iB\ne0$ 时，对每个严格正定 $\rho$ 给原迹商的上确界一个统一于 $\rho$ 的界 $n$；允许非零的 $A+iB$ 奇异 [2](#ref-repo-c127-af)。
直接依赖中的 `bornProbability` 已定义为 $\operatorname{Tr}(\rho P)$；因此该结果不是 Born 起源推导 [3](#ref-repo-c127-born)。
本轮阅读了源码证明，未运行新的 Lean 构建，也没有据此认证文献优先权或维数无关的界。

**白话。**仓库的新例子提醒我们：两次成功后的样子相同，完整经历仍可能不同，因为成功和失败的原分量还在。要把公理放回整体内部，先保留这份完整性。然后只问：整体自己已经确定的一份单位，能不能被两份真正的零拼出来？

<a id="section-2"></a>

## 2. 唯一候选：单位不可由两个零历史拼成

<a id="sec-c127-unit"></a>

本节把 C126 的全部端点传递性进一步压缩为一个固定单位端点的约束，同时从完整原记录的归一化恢复各支的正取向。比较仍为已声明的 Hermitian 二次结构；这里给出其直接等价证明，不提出文献优先性主张。

### 2.1 一个单位端点足够选择正关系

### 定义 2.1（C127：单位不可双零分解）

令 $V$ 为任意实或复向量空间，$\Gamma$ 分别为对称双线性或 Hermitian 半双线性形式；复情形首槽共轭。置 $Q(h)=\Gamma(h,h)$，给定 $Q(e)=1$ 的单位历史。唯一新增要求为

<a id="eq-c127-single-axiom"></a>

$$
\boxed{\nexists h\in V:\quad Q(h)=0\quad\text{且}\quad Q(e-h)=0.}
\tag{1}
$$

它约束同一比较域内的二元拆分 $(h,e-h)$，不先要求全部零差关系可传递。

### 定理 2.2（固定单位判据）

<a id="thm-c127-unit"></a>

在上述前件下，单位不可双零分解，当且仅当 $Q(h)\ge0$ 对全部 $h\in V$ 成立。此时

$$
\mathcal N:=\{h:Q(h)=0\}=\operatorname{rad}\Gamma
$$

为线性空间，故 $h\sim k\iff Q(h-k)=0$ 是可在全部比较中替换的等价关系。结论不要求有限维，也不使用辅助内积或谱分解。

**证明。**
若 $Q\ge0$ 且 $Q(h)=0$，则对任意 $k$ 与标量 $t$，

$$
Q(h+tk)=2\Re\bigl(t\Gamma(h,k)\bigr)+|t|^2Q(k)\ge0.
$$

选取适当相位、任意小的 $t$，可知 $\Gamma(h,k)=0$。实情形只需选取 $t$ 的符号。因此零集合恰为根空间，两个零历史的和仍为零，不可能等于 $Q(e)=1$ 的 $e$。

反之，若有 $Q(n)<0$，令

$$
w_0=n-\Gamma(e,n)e.
$$

则

$$
\Gamma(e,w_0)=0,\qquad
 Q(w_0)=Q(n)-|\Gamma(e,n)|^2<0.
$$

将 $w_0$ 实倍缩放成 $w$，使 $Q(w)=-1/4$。于是

<a id="eq-c127-two-null-witness"></a>

$$
h=\frac e2+w,\qquad e-h=\frac e2-w,
 \qquad Q(h)=Q(e-h)=\frac14+Q(w)=0,
\tag{2}
$$

违反候选。失败见证全部落在 $\operatorname{span}\{e,n\}$ 内。根空间的线性与全部比较替换性再给出所述等价关系。

所以本轮只要阻止一个已经归一化的对象被双零合并，就能恢复 C126 对全部端点的传递性。这里的零是完整历史的自比较零，不是某个终端端口的一次零读数。

**白话。**先固定一份确实读作一的整体。如果关系里有一个负方向，就能把这份整体拆成两份各自读作零的历史。只禁止这件事，已经足以排除全部负方向；此后，所有真正的零差自然都能连续替换。

### 2.2 完整原记录内生供应单位

### 定义 2.3（候选完整记录族）

取有限非空的原记录集 $J$，$m,d_j\ge1$，给定复线性、保伴随映射

<a id="eq-c127-record-normalization"></a>

$$
\Phi_j:M_{d_j}(\mathbb C)\longrightarrow M_m(\mathbb C),
 \qquad
 \sum_{j\in J}\Phi_j(I_{d_j})=I_m.
\tag{3}
$$

不预设各支正性、完全正性或 $0\le\Phi_j(I)\le I$。原记录包括被声明为完整测试组成部分的成功与失败；此时这些映射只是候选更新表，尚未获得合法概率支的资格。

令 $\mathfrak H_j=M_{d_j}\otimes\mathbb C^m$，并在历史 $h_j=\sum_r a_{jr}\otimes u_{jr}$、$k_j=\sum_s b_{js}\otimes v_{js}$ 上定义

$$
\Gamma_j(h_j,k_j)
 =\sum_{r,s}\langle u_{jr},\Phi_j(a_{jr}^*b_{js})v_{js}\rangle.
$$

完整记录的形式历史域及比较为

<a id="eq-c127-record-form"></a>

$$
\mathfrak H_{\rm rec}=\bigoplus_{j\in J}\mathfrak H_j,
 \qquad
 \Gamma_{\rm rec}(h,k)=\sum_j\Gamma_j(h_j,k_j),
 \qquad Q_{\rm rec}(h)=\Gamma_{\rm rec}(h,h).
\tag{4}
$$

不同原记录之间的交叉项为零。这里的直和表达互斥记录的未条件化读数相加，不添加跨原记录的相干干涉，不将环境的数学分解指标升级成原记录。
任取一个固定归一向量 $u_0\in\mathbb C^m$，令

<a id="eq-c127-canonical-unit"></a>

$$
e=e_{u_0}:=(I_{d_j}\otimes u_0)_j.
 \qquad
 Q_{\rm rec}(e)
 =\left\langle u_0,\sum_j\Phi_j(I_{d_j})u_0\right\rangle=1.
\tag{5}
$$

所以单位的正读数由完整性给出，不另挑一个已知正的分支。

### 定理 2.4（一个单位拆分判据恰好选择量子仪器）

<a id="thm-c127-instrument"></a>

对式 [(3)](#eq-c127-record-normalization)–[(4)](#eq-c127-record-form) 定义的候选族，以下等价：

1. 固定的 $e_{u_0}$ 满足 C127；

2. $Q_{\rm rec}\ge0$ 于完整历史域；

3. 每个未归一化 Choi 矩阵 $C_j=[\Phi_j(E_{rs})]_{r,s=1}^{d_j}$ 均正半定；

4. 每个 $\Phi_j$ 完全正。

成立后，各支效果自动满足

$$
E_j:=\Phi_j(I_{d_j})\ge0,\qquad
 I_m-E_j=\sum_{\ell\ne j}E_\ell\ge0.
$$

因此该族成为完整量子仪器的 Heisenberg 表示；不同输出维数及零分支均包含在内。

**证明。**
式 [(5)](#eq-c127-canonical-unit) 与定理 [2.2](#thm-c127-unit) 给 (1)$\Leftrightarrow$(2)。矩阵单位满足
$E_{pr}^*E_{qs}=\delta_{pq}E_{rs}$，故各支历史关系矩阵为 $I_{d_j}\otimes C_j$。完整矩阵是这些矩阵的直和，立即给 (2)$\Leftrightarrow$(3)。

若 $\Phi_j$ 完全正，历史块矩阵 $[a_r^*a_s]$ 为正，对其逐块作用 $\Phi_j$ 后，以向量族 $(u_r)_r$ 评价就得到 $Q_j\ge0$。
反过来，任取 $X=[X_{rs}]=T^*T\in M_n(M_{d_j})$ 为正，则对任意 $u_r\in\mathbb C^m$，

$$
\sum_{r,s}\langle u_r,\Phi_j(X_{rs})u_s\rangle
 =\sum_\ell Q_j\!\left(\sum_r T_{\ell r}\otimes u_r\right)\ge0.
$$

因为 $n$ 任意，全部有限放大 $\operatorname{id}_n\otimes\Phi_j$ 都保持正性，故 (2)$\Leftrightarrow$(4)。最后，各 $E_j\ge0$ 及完整性给出效果上界。

若 $E_j=0$，则 $C_j\ge0$ 且 $\operatorname{Tr} C_j=\operatorname{Tr} E_j=0$，所以 $C_j=0$、$\Phi_j=0$；零分支无需删除。实际条件输出仍只在该支概率为正时定义。

### 推论 2.5（前轮的同一性与共同左续接）

候选成立后，零差集合是 $\Gamma_{\rm rec}$ 的根空间。对 $a=(a_j)_j$ 定义逐原记录的形式左作用 $L_a(h_j)_j=(a_jh_j)_j$，则

$$
Q_{\rm rec}(L_ah)=\Gamma_{\rm rec}(h,L_{a^*a}h).
$$

因此零差在全部二元比较和共同左续接下保持；C126 与 C125 所需的零保持均为推论。实际调用的接续仍须由原菜单供应。

同一个完整记录族内，任何归一输入 $u$ 都给 $Q(e_u)=1$。所以选择哪一个单位端点不改变所选出的 CP 类；有负方向时，每个这样的端点都有失败拆分。这个结论不自动识别两个尚未对应的观察域。

### 2.3 每支一来源行的扰动已经足够

### 命题 2.6（保留单位背景的来源行检验）

<a id="prop-c127-row-test"></a>

在每个记录中固定任意一行 $p_j$，令

$$
\mathfrak H_{j,p_j}
 =\left\{\sum_rE_{p_jr}\otimes u_r:u_r\in\mathbb C^m\right\}
 \subset\mathfrak H_{\rm rec},
$$

其余记录分量取零。只要求对每个 $j$ 和每个 $z\in\mathfrak H_{j,p_j}$，下面两份读数不能同时为零，就与定理 [2.4](#thm-c127-instrument) 中的各条件等价：

<a id="eq-c127-row-unit-test"></a>

$$
Q_{\rm rec}(e/2+z),\qquad Q_{\rm rec}(e/2-z).
\tag{6}
$$

**证明。**
全部 CP 时，由主定理当然通过这些特殊拆分。反之，若某个 $C_j$ 非正，该来源行中有 $Q(z_0)<0$。乘一个单位复相位使 $\Re\Gamma(e,z_0)=0$，再作实倍缩放，使 $Q(z)=-1/4$。于是 [(6)](#eq-c127-row-unit-test) 两项均为 $1/4-1/4=0$，矛盾。

这里使用原复线性历史域的相位。固定的是单位背景与每支来源行；$u_r$ 仍遍历全部声明的输入方向。规范 $e$ 通常不在单来源行内，所以这不是一次未覆盖输入方向的单输入实验，也不供应新的实际相位门。

### 2.4 删除前件会漏过哪些坏模型

**把原记录拆开认证。**

取两支标量映射 $\Phi_1(\lambda)=-\lambda$、$\Phi_2(\lambda)=2\lambda$。它们的和保持单位，每支的零关系都是普通相等，但第一支为负。完整形式为

$$
Q(z_1,z_2)=-|z_1|^2+2|z_2|^2,\qquad e=(1,1).
$$

令 $h=((1+i)/2,1/2)$，则 $e-h=((1-i)/2,1/2)$，两者的 $Q$ 都为零。完整原记录的共同判据正好排除这个模型；分别检查每支零差不能替代它。

**删除保伴随性。**

取单记录 $\Phi:M_2\to\mathbb C$，
$\Phi(a)=(1/2+i)a_{11}+(1/2-i)a_{22}$。
它复线性、保持单位，却不保伴随，也不正。若把零仅解释为复数零，则其历史自比较满足
$\Re Q(a)=\operatorname{Tr}(a^*a)/2>0$ 对全部非零 $a$ 成立，因而单位不可双零分解自动通过。实自比较的 Hermitian 前件不能省去。

**把全输入域缩成一个输入。**

取转置 $\Phi(a)=a^T:M_2\to M_2$，它复线性、保伴随、正且保持单位。每个单纯张量都有
$Q(a\otimes u)=\langle u,(a^*a)^Tu\rangle\ge0$，所以固定一个输入方向的检验全部通过。
但 $C_\Phi$ 是交换矩阵，其反对称方向的特征值为 $-1$。
具体取 $e=I_2\otimes e_1$、
$n=(E_{11}\otimes e_2-E_{12}\otimes e_1)/\sqrt2$，则 $Q(n)=-1$、$\Gamma(e,n)=0$；$e/2\pm n/2$ 恰为双零拆分。候选因此真正排除了正而非完全正的过程。

**单位与二次结构仍有内容。**

若不要求 $Q(e)=1$，$Q(z)=-|z|^2$ 的非零端点同样不可双零分解，却全为负。
若撤去二次结构，$Q(x)=\|x\|_4^2$ 也没有非平凡零历史，却不满足内积的平行四边形恒等式。这些前件没有被一个更短的候选句子消除。

**白话。**完整原记录先告诉我们：这次整体读作一，不必预先宣布每个分支都为正。只要这份一不能被两份真正的零拼出来，所有分支就被共同约束成正的量子事件。起点可以换，失败的拆法也可以换；同一完整比较域中的合法过程类不会因此改变。

<a id="section-3"></a>

## 3. 一个单位参照的三维抛物面

<a id="sec-c127-geometry"></a>

本节只展开同一个候选的几何。固定完整单位历史 $e$，$Q(e)=1$；由前节取得 $\Gamma\succeq0$，记其零空间为 $\mathcal N$。对任意历史 $z$，二元关系只需三个实数：

$$
c=\Gamma(e,z)=x+iy,\qquad s=Q(z),\qquad
 G_{e,z}=\begin{pmatrix}1&c\\\bar c&s\end{pmatrix}.
$$

### 定理 3.1（固定单位的抛物面与球坐标）

<a id="thm-c127-paraboloid"></a>

二元关系表为正，当且仅当

<a id="eq-c127-paraboloid"></a>

$$
s\ge x^2+y^2.
\tag{7}
$$

其剩余量恰为 $Q(z-ce)=s-|c|^2$。取迹归一化后，

<a id="eq-c127-bloch-chart"></a>

$$
\frac{G_{e,z}}{1+s}=\frac{I+r\cdot\sigma}{2},\qquad
 r=\frac{(2x,-2y,1-s)}{1+s}
\tag{8}
$$

将整个区域 $\mathcal P=\{s\ge x^2+y^2\}$ 双射到闭 Bloch 球去掉南极 $(0,0,-1)$。
边界对应秩一，内部对应秩二。

**证明。**
第一主元为一，故二阶正性等价于 $\det G_{e,z}=s-|c|^2\ge0$。直接展开又给 $\Gamma(e,z-ce)=0$ 和所述剩余量。
Pauli 展开给式 [(8)](#eq-c127-bloch-chart)，且

$$
1-\|r\|^2=\frac{4(s-x^2-y^2)}{(1+s)^2}.
$$

闭球中除了南极都有 $r_z>-1$，逆映射为

$$
s=\frac{1-r_z}{1+r_z},\qquad
 x=\frac{r_x}{1+r_z},\qquad
 y=-\frac{r_y}{1+r_z}.
$$

代入得到 $s-x^2-y^2=(1-\|r\|^2)/(1+r_z)^2\ge0$，证明双射。行列式为零恰好给秩一，此时
$z-ce\in\mathcal N$，且 $\operatorname{ker} G_{e,z}=\operatorname{span}\{(-c,1)\}$。

这只抛物面是二阶正关系大锥的固定单位截面。令

$$
(T,X,Y,Z)=(1+s,2x,-2y,1-s),
$$

则 $G\succeq0$ 等价于 $T\ge\sqrt{X^2+Y^2+Z^2}$，而固定第一自比较为一给 $T+Z=2$。再除以 $T$ 才得到三维球。沿 $\mathcal P$ 趋向无穷时，$r$ 统一趋向南极；补入这一点便得到闭球，抛物面边界则补成球面。

锥的行列式 $4\det G=T^2-X^2-Y^2-Z^2$ 是矩阵坐标上的不定二次式，不是历史自比较 $Q$。前者为零表示秩一边界，后者为零表示历史属于根空间；两种零不能互换。

### 3.1 抛物面外的关系怎样变成单位双零分解

暂回到未经候选筛选的 Hermitian 关系。如果某份 $z$ 有 $s<|c|^2$，先扣去沿单位方向已确定的部分：

$$
w=z-ce,\qquad \Gamma(e,w)=0,\qquad Q(w)=s-|c|^2<0.
$$

将 $w$ 缩放到 $Q(w)=-1/4$，$e/2+w$ 与 $e/2-w$ 就都是零历史。
因此每个抛物面外点都能通过已有线性组合送到同一个被禁止的拆分。
一般地，写 $h=e/2+z$，有

$$
Q(h)=\tfrac14+s+x,\qquad
 Q(e-h)=\tfrac14+s-x.
$$

双零要求 $x=0,s=-1/4$，完全位于允许区域之下。这是同一个候选的几何见证，不是新增的曲面公理。

<a id="fig-c127-paraboloid"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \begin{scope}[x=1.65cm,y=1.30cm]
  \node at (0,1.96) {$y=0$ 的抛物面截面};
  \fill[teal!8] plot[domain=-1.15:1.15,samples=70] (\x,{\x*\x})
    --(1.15,1.65)--(-1.15,1.65)--cycle;
  \draw[gray!75,->] (-1.40,0)--(1.47,0) node[right] {$x$};
  \draw[gray!75,->] (0,-0.60)--(0,1.73) node[left] {$s$};
  \draw[teal!75!black,very thick,domain=-1.15:1.15,samples=70]
    plot (\x,{\x*\x});
  \node[teal!75!black,fill=white,inner sep=2pt] at (0.50,1.30) {$s\ge x^2$};
  \fill[red!75!black] (0,-0.25) circle (2pt);
  \node[red!75!black,anchor=west] at (0.13,-0.32) {双零所需点};
  \node[red!75!black,anchor=west] at (0.13,-0.57) {$(0,-1/4)$};
 \end{scope}
 \draw[gray!80,->,thick] (2.65,0.70)--(4.90,0.70)
   node[midway,above=3pt] {取迹归一化};
 \begin{scope}[xshift=7.55cm,x=1.40cm,y=1.40cm]
  \node at (0,1.82) {$r_y=0$ 的 Bloch 截面};
  \fill[teal!8] (0,0) circle (1);
  \draw[teal!75!black,thick] (0,0) circle (1);
  \draw[gray!75,->] (-1.23,0)--(1.33,0) node[right] {$r_x$};
  \draw[gray!75,->] (0,-1.16)--(0,1.32) node[left] {$r_z$};
  \node[teal!75!black] at (0.40,0.35) {秩二};
  \node[teal!75!black] at (-0.82,0.96) {秩一};
  \fill[white] (0,-1) circle (2.8pt);
  \draw[red!75!black,thick] (0,-1) circle (2.8pt);
  \node[red!75!black] at (0,-1.48) {南极是缺去的无穷远点};
 \end{scope}
\end{tikzpicture}
```

**图 1。**固定单位自比较后，关系坐标位于抛物面上方；单位双零拆分所需点落在其下方。取迹归一化给球的坐标图。图是历史关系空间的截面，不是物理时空。

这里的整个参数区域首先描述允许的 Gram 表。对一个固定过程，若商空间只有一维，就只实现抛物面边界；至少有两个独立商方向时，$z=ce+\sqrt{s-|c|^2}\,f$、$f\perp e$、$Q(f)=1$ 才能实现整个区域。数学组合存在与实际原门词可取得性仍须分别说明。实数关系只给 $y=0$ 的截面；本轮没有从该图推出复标量。

回到原二元式，实变量 $a,b$ 的 $a^2+\xi ab+b^2$ 对应关系表
$\left(\begin{smallmatrix}1&\xi/2\\\xi/2&1\end{smallmatrix}\right)$。
其正性为 $|\xi|\le2$。等值线为一时，$\xi=0$ 才是圆；$\xi=2$ 给 $(a+b)^2=1$，是两条平行直线。交叉项是双线性的，固定一元后才对另一元线性。可保留的直觉是：二元关系的线性配对与自比较的平方读数之间存在精确约束；本轮把它写成 $s\ge|c|^2$。

**白话。**把单位方向中已经看清的部分扣掉，剩下的自比较必须不负。这就画出一只最简单的抛物面：边界表示没有剩余方向，内部表示还有一份独立内容。任何落到曲面下方的关系，都能被移到同一条负轴上，再拼出“两个零合成一个单位”的矛盾。球与抛物面是同一正关系结构的两种归一化坐标。

<a id="section-4"></a>

## 4. 二读数的有限证据与见证半径

<a id="sec-c127-finite-evidence"></a>

仍固定同一个完整过程及 $Q(e)=1$。这里的 $e=h+(e-h)$ 是相干历史的代数分解，不能当作互斥事件的概率分支；若先强制两项正交，其自比较之和本来就等于一，便无法检验负关系。

### 命题 4.1（单位中点的紧下界）

候选成立后，任意历史 $h$ 满足

<a id="eq-c127-midpoint-floor"></a>

$$
Q(h)+Q(e-h)
 =\frac12+2Q\!\left(h-\frac e2\right)
 \ge\frac12.
\tag{9}
$$

等号当且仅当 $h-e/2\in\mathcal N$。

**证明。**
令 $z=h-e/2$。两份展开的交叉项互相抵消，常数项之和为 $Q(e)/2=1/2$。候选已给 $Q\ge0$，而正形式的零集合恰为 $\mathcal N$。

为了量化违反，以下也允许尚未通过候选的 Hermitian 关系。固定矩阵单位和标准输入基，取相应的欧氏系数范数 $\|\cdot\|_0$，写 $Q(z)=z^*Gz$，其中

$$
G=\bigoplus_j I_{d_j}\otimes C_j,
 \qquad b=\max\{0,-\lambda_{\min}(G)\}
       =\max_j\max\{0,-\lambda_{\min}(C_j)\}.
$$

辅助范数仅给比较系数的预算，不能用尚待认证为正的 $Q$ 替代它，也不自动等于实际门的成本。

### 定理 4.2（中点亏损恰好测量负谱）

<a id="thm-c127-defect"></a>

对 $R>0$，令 $(t)_+=\max\{t,0\}$，并定义

$$
D_R=\sup_{\|h-e/2\|_0\le R}
 \left(\frac12-Q(h)-Q(e-h)\right)_+.
$$

则

<a id="eq-c127-exact-defect"></a>

$$
\boxed{D_R=2R^2b.}
\tag{10}
$$

**证明。**
式 [(9)](#eq-c127-midpoint-floor) 的等式部分不依赖正性，所以
$D_R=\sup_{\|z\|_0\le R}(-2z^*Gz)_+$。
若 $b=0$，此量为零。若 $b>0$，Rayleigh 下界给它至多 $2R^2b$；取最负单位特征向量的 $R$ 倍即达到。

### 4.1 无需测出严格零的否定证书

设同一历史配对、同一实际过程及同一个置信事件给出

$$
Q(h)\le U_h,\qquad Q(e-h)\le U_{e-h}.
$$

单位已精确标定时，

<a id="eq-c127-finite-rejection"></a>

$$
U_h+U_{e-h}<\frac12
\tag{11}
$$

就是违反候选的有限证书。若单位标定也有误差，且 $Q(e)\ge L_e$，将右端换成 $L_e/2$ 即可；证明仍用对任意 $e$ 成立的展开式。
这些是未条件化读数的共同界，不能把各自条件化后的支、不同事件或不同实现混入同一个不等式。分别声称的边缘置信水平也不自动组成共同置信事件。
使用这份实验性证书还要求相关形式历史具有已标定的实际实现，并将制备或后选尺度恢复到同一原读数约定；形式组合的存在不自动保证装置能够执行。

一个历史对没有越界，并不控制上确界 $D_R$。若确有全域上界 $D_R\le\varepsilon$，才由定理得到 $b\le\varepsilon/(2R^2)$；这还是原关系矩阵的负谱控制，未自动构造保持全部原记录与归一化的修复仪器。

### 4.2 为什么有限预算内没有双零仍不等于完全正

### 命题 4.3（复历史中的最小双零半径）

<a id="prop-c127-radius"></a>

若 $b>0$，则

<a id="eq-c127-null-radius"></a>

$$
\inf_{\substack{Q(h)=0\\Q(e-h)=0}}
 \left\|h-\frac e2\right\|_0
 =\frac1{2\sqrt b}.
\tag{12}
$$

若 $b=0$，没有双零分解，约定该下确界为 $+\infty$。

**证明。**
双零给 $z=h-e/2$ 满足 $Q(z)=-1/4$。由 $Q(z)\ge-b\|z\|_0^2$ 得下界。
反过来，取最负单位特征向量 $v$，乘一个复相位，使 $\Re\Gamma(e,v)=0$；这不改变范数和 $Q(v)=-b$。令 $z=v/(2\sqrt b)$，则

$$
Q(e/2\pm z)=\tfrac14+Q(z)\pm\Re\Gamma(e,z)=0,
$$

达到所述半径。

因此，在中心半径 $R$ 的闭球内存在双零分解，恰好等价于 $b\ge1/(4R^2)$。例如

$$
Q(z_1,z_2)=|z_1|^2-\epsilon|z_2|^2,\qquad e=(1,0),\quad\epsilon>0,
$$

取 $z=(0,1/(2\sqrt\epsilon))$，便在最小半径上产生 $e/2\pm z$ 的双零。负方向越浅，精确拆分所需系数越大；有限半径内未见双零只能限制负谱，不能认证其为零。精确达到一般式 [(12)](#eq-c127-null-radius) 用到了复相位；实域不自动具有同一最优半径，但式 [(10)](#eq-c127-exact-defect) 仍成立。

**白话。**不必先证明两份读数真的为零。把它们的可信上界相加，如果这个和还低于单位中点应有的下界，就已经找到反例。反过来，少量测试没有发现问题，不等于所有关系都已检过；尤其很浅的负方向，需要很大的历史系数才会露出精确的双零拆分。

<a id="section-5"></a>

## 5. 由完整单位发展有限量子理论

<a id="sec-c127-quantum"></a>

本节在主定理已选择完全正记录族后，给出通常有限量子规则的自包含推导。所用 Choi、Kraus、Stinespring 与效果概率表示属于成熟数学；新增候选只承担前文的选择步骤 [7](#ref-watrous2018)、[6](#ref-choi1975)、[5](#ref-stinespring1955)、[8](#ref-busch2003)。

### 5.1 Hilbert 商与一个保留完整记录的等距表示

### 定理 5.1（完整记录表示）

<a id="thm-c127-record-dilation"></a>

令 $\mathfrak H_j=M_{d_j}\otimes\mathbb C^m$，$\mathcal N_j=\{h:Q_j(h)=0\}$。
候选成立后，$H_j=\mathfrak H_j/\mathcal N_j$ 带内积
$\langle[h],[k]\rangle=\Gamma_j(h,k)$。
若 $r_j=\operatorname{rank} C_j$，则存在 $d_j\times m$ 矩阵 $K_{j\alpha}$，使

<a id="eq-c127-kraus"></a>

$$
\Phi_j(a)=\sum_{\alpha=1}^{r_j}K_{j\alpha}^*aK_{j\alpha},
 \qquad
 \sum_{j,\alpha}K_{j\alpha}^*K_{j\alpha}=I_m.
\tag{13}
$$

对应一个等距

$$
V:\mathbb C^m\longrightarrow
 \bigoplus_j(\mathbb C^{d_j}\otimes\mathbb C^{r_j}),
 \qquad
 Vu=\bigoplus_j\sum_\alpha K_{j\alpha}u\otimes e_\alpha.
$$

各支态方向 $\mathcal T_j:M_m\to M_{d_j}$ 为
$\mathcal T_j(\rho)=\sum_\alpha K_{j\alpha}\rho K_{j\alpha}^*$。
完整输出为原记录直和 $\bigoplus_j\mathcal T_j(\rho)$，它完全正且保迹。

**证明。**
正形式的零集合是根空间，所以商内积不依赖代表。定义

$$
\pi_j(a)[h]=[L_ah],\qquad V_ju=[I_{d_j}\otimes u].
$$

伴随关系 $\Gamma_j(L_ah,k)=\Gamma_j(h,L_{a^*}k)$ 和根空间不变性给出良定义的保单位 $*$-表示。
取 $b=(\|a\|^2I-a^*a)^{1/2}$，则

$$
\|a\|^2Q_j(h)-Q_j(L_ah)=Q_j(L_bh)\ge0,
$$

故 $\pi_j$ 有界。直接评价给
$\Phi_j(a)=V_j^*\pi_j(a)V_j$ 及 $V_j^*V_j=E_j$。

行分解 $G_j=I_{d_j}\otimes C_j$ 给 $\dim H_j=d_jr_j$。
置 $Z_j=\pi_j(E_{11})H_j$。矩阵单位给各 $\pi_j(E_{ii})H_j$ 等维且正交直和为全空间；
$e_i\otimes z\mapsto\pi_j(E_{i1})z$
因此给 $H_j\cong\mathbb C^{d_j}\otimes Z_j$，其中 $\dim Z_j=r_j$，表示变为 $a\otimes I_{Z_j}$。
在 $Z_j$ 选基展开 $V_j$ 即得 Kraus 族。原完整性给 $V^*V=\sum_jE_j=I_m$。
态方向式由迹配对得到；其全迹为 $\operatorname{Tr}\rho$。$r_j=0$ 时用零空间与空和。

表示由 $\pi_j(a)V_ju$ 张成。令
$w_{j\alpha}=\sum_i e_i\otimes K_{j\alpha}^*e_i$，有
$C_j=\sum_\alpha w_{j\alpha}w_{j\alpha}^*$，所以任一 Kraus 族至少含 $r_j$ 项，而上述构造达到。
两个最小列因子 $A,B$ 满足 $AA^*=BB^*=C_j$，满列秩给 $B=AU$、$UU^*=I$，故最小数学记录只差环境酉坐标。
原标签 $j$ 与数学指标 $\alpha$ 不同；这个存在证明不自动供应可访问的环境端口。完整输出只评价原记录的块对角代数，扩张空间的跨记录非对角项不被自动认作原可观测量。

### 5.2 从效果读数得到密度矩阵与 Born 规则

### 定义 5.2（完整效果的概率评价）

在一个有限 $M_d(\mathbb C)$ 部门，效果为 $0\le a\le I$。同一赋值 $p(a)\in[0,1]$ 满足 $p(I)=1$，且在 $a+b\le I$ 时满足 $p(a+b)=p(a)+p(b)$。
同一效果的赋值不因所属完整测试而改变。

### 定理 5.3（有限效果的 Born 表示）

每个这样的 $p$ 唯一写成

$$
p(a)=\operatorname{Tr}(\rho a),\qquad \rho\ge0,\quad\operatorname{Tr}\rho=1.
$$

密度态的极点恰为秩一态。对归一 $\psi,\varphi$，纯态 $\lvert \psi\rangle \langle \psi\rvert $ 对单位秩一投影 $\lvert \varphi\rangle \langle \varphi\rvert $ 的读数为
$|\langle\varphi,\psi\rangle|^2$。

**证明。**
可加性给有理齐次性；非负性给单调性，用有理数上下夹逼得实齐次性。
对 $a\ge0$，取 $s>0$ 且 $s\ge\|a\|$，置 $f(a)=sp(a/s)$；齐次性使其不依赖 $s$，并使正锥加法成立。
若 $a-b=a'-b'$，则 $a+b'=a'+b$，所以 $f(a)-f(b)$ 唯一延伸到 Hermitian 空间。
有限迹配对给唯一 Hermitian $\rho$；对秩一正矩阵评价给 $\rho\ge0$，对单位评价给迹一。
秩至少二时可向两个正谱权作小幅相反移动，得到非平凡凸分解；秩一态的正分解只能支持同一射线，归一后相同。最后的平方律由矩阵相乘取迹得出。

这是全效果的有限 Gleason–Busch 形式，包括二维 [8](#ref-busch2003)。它使用上面的概率定义；这些评价条件尚未由 C127 单独推出，也不意味着全部数学效果已实际可访问。只有锐投影的正交可加性在二维不足。
复向量相干组合早已在对象接口中，本轮并未从一个抽象零关系单独选出复数或线性叠加。

### 5.3 仪器、条件态与投影更新

主定理导出的 $E_j\ge0$ 与 $\sum_jE_j=I$ 给

$$
p_j=\operatorname{Tr}(\rho E_j)=\operatorname{Tr}\mathcal T_j(\rho),\qquad
 \sum_jp_j=1.
$$

只有 $p_j>0$ 时才定义 $\rho_j=\mathcal T_j(\rho)/p_j$。保留所有支的未条件化输出，就保留原成功率与失败率。
数学上任意有限 POVM 都有 $K_j=\sqrt{E_j}$ 的实现及
$V\psi=\sum_j\sqrt{E_j}\psi\otimes\lvert j\rangle $；实际记录与联合控制的供应仍是独立问题。

### 命题 5.4（投影支的逐射线保持）

同空间 CP 事件若效果为投影 $P$，且保持 $\operatorname{Ran} P$ 内每条纯射线，则它为 $\rho\mapsto P\rho P$。

**证明。**
$P=0$ 时，$\sum K_\alpha^*K_\alpha=0$ 使每项为零。否则效果等式给 $K_\alpha(I-P)=0$。
射线保持给 $K_\alpha x\in\mathbb C x$，对基向量及两两和比较可知 $K_\alpha=c_\alpha P$；效果等式给 $\sum|c_\alpha|^2=1$。

仅要求结果可重复，还允许结果子空间内部旋转，不能独自选择 Lüders 支。

### 5.4 独立复合与合法接续

### 命题 5.5（复矩阵对象的独立联合）

若 $M_d$ 与 $M_m$ 保单位保星嵌入同一有限代数，两像交换且共同生成，则联合代数同构于 $M_{dm}$。

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满的保单位 $*$-同态。
张量矩阵单位使定义域为 $M_{dm}$。其任一非零双边理想，经左右矩阵单位乘法得到全部矩阵单位，故代数简单；核不能为全体，所以为零。

Kraus 族的串接为 $L_\beta K_\alpha$，并接为 $K_\alpha\otimes L_\beta$；故 CP 类对合法串并接闭合。
完整局部保迹过程满足

$$
\operatorname{Tr}_A[(\mathcal T_A\otimes\operatorname{id})(\rho_{AB})]=\operatorname{Tr}_A\rho_{AB},
$$

因为对任意另一侧效果 $f$，伴随作用给
$\mathcal T_A^*(I)\otimes f=I\otimes f$。
条件在某个结果上的边缘可以不同，其选择信息由相应记录承载。

### 5.5 完整可逆与给定时钟

### 定理 5.6（同维完全正可逆性）

若同维 CPTP 映射 $\mathcal T$ 有 CPTP 左逆 $\mathcal S$，则 $\mathcal T(\rho)=U\rho U^*$，$U$ 酉。

**证明。**
取两映射的 Kraus 族 $K_i,L_j$。恒等通道的 Choi 表秩一，故 $L_jK_i=c_{ji}I$。
对非零 $K_{i_0}$，$\sum_jL_j^*L_j=I$ 保证至少一个 $L_{j_0}K_{i_0}\ne0$，因而两矩阵可逆。
从 $L_{j_0}K_i=c_{j_0i}I$ 得全部 $K_i$ 共线，合并为一个 $K$；保迹给 $K^*K=I$，同维给酉性。

若另给连续一参数 CPTP 群，有限维中在单位附近取小矩阵对数，交换群律给局部连续可加性，故群为 $e^{tD}$。
酉共轭使其为 $*$-自同构，对乘法求导给保星导子。
令 $A=\sum_kD(E_{k1})E_{1k}$，由导子律得 $[A,E_{ij}]=D(E_{ij})$。
保星性使 $A+A^*$ 为中心元，故可换成反自伴部分。于是存在自伴 $H$，满足

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

选纯态相位代表后得 $i\hbar\dot\psi=H\psi$。
一般可微酉传播子也给 $H(t)=i\hbar\,\partial_tU(t,s)U(t,s)^*$，传播律使其与 $s$ 无关，且由 $UU^*=I$ 的导数可知自伴。
实际时钟、具体 $H$ 与 $\hbar$ 标定并非本轮候选选择。

| 通常规则 | 来源及仍保留的定义前件 |
|---|---|
| Hilbert 几何 | 相干 Hermitian 历史、内部单位与候选；正核取零差商。 |
| 完整量子仪器 | 候选给逐支 CP；原总归一化给正效果、不增迹与全保迹。 |
| Born 与纯态 | 全效果的归一可加评价；正锥极点及秩一迹配对。 |
| 张量与无信号 | 独立交换并共同生成的联合接口；完整局部过程保迹。 |
| 酉与时间方程 | 同维 CPTP 逆；连续群或可微传播及内部时钟。 |
| 复数与场内容 | 复矩阵接口仍继承；具体场、局域性与无限维算符域尚未选定。 |

**白话。**完整的一份单位先保证所有原记录能放回同一个整体；禁止它由双零拼成，使各支关系都为正。把真正零差合并，就有内积；把所有支与数学记录一起保留，就有量子过程。相容的完整效果读数给概率，完整可逆给酉作用，时钟再把作用写成时间方程。每一层都有自己的明确输入，当前省去的是逐支的正性命令与任意端点的传递要求。

<a id="section-6"></a>

## 6. 观察者、内部单位与整体关系

<a id="sec-c127-observers"></a>

### 6.1 起点可以变，比较域不能被悄悄换掉

对同一个完整记录族，每个归一输入 $u$ 都给单位 $e_u$。主定理说明，对其中任意一个单位施加候选，所选择的过程类相同。这解释了一个精确的“起点无关性”：判据不需要额外指定一个宇宙外的优先参照。
它不说明不同观察者的未知历史域已经对应，也不把一个单位端点等同于一条输入状态的实际测量。失败拆分仍可以使用完整域内的其他输入方向。

两个局部观察者是否有共同关系，须由内部可检查的对应、来源和记录来认证。交换一个带证明的共同子结构，足以认证这一部分确为共同结构；逻辑上不要求一方包含另一方的全部结构。若要断言这就是完整交集，还需双方完整的嵌入或成员判定。没有这样的证据时，不能从“都属于 $\Omega$”推出已知整个交集。
项目的共同来源与观察者序列文稿也保留完整来源、实际接续和编码语义的区别 [4](#ref-repo-c127-observers)。

### 命题 6.1（相容窗口的单位与正核拼接）

设内部历史窗口 $V_\alpha$ 通过指定的单射复线性映射形成有向系统，Hermitian 比较在嵌入下相容，各窗口含有同一个单位 $e$，满足 $Q(e)=1$ 与 C127。
则其代数直接极限上有良定义的正半定比较，各零差商等距嵌入同一个 Hilbert 完成空间。

**证明。**
有限多个历史总能进入一个共同更大窗口；在其中评价比较。相容性使数值不依赖窗口，而固定单位判据使每个自比较非负。
全局零空间与每个窗口的交恰为该窗口的零空间，故商映射等距。对代数并集的商取完成即得所述空间。

这个结论要求跨窗口的对应已经给出。只知道互相分离的边缘数据，不能恢复未供应的交叉比较。
若两个窗口序列覆盖同一个稠密域，它们得到同一完成空间；要说物理态沿时间收敛，还需另给态序列、共同表示、距离及收敛估计。
整体态的选择仍须另给相容的准备与足够分离的评价；几何拼接没有单独选出唯一 $\omega$，也没有证明它纯。

### 6.2 自指起点与输入的去向

固定归一 $\lvert o\rangle $，重置映射

$$
\mathcal R_o(\rho)=\operatorname{Tr}(\rho)\lvert o\rangle \langle o\rvert
$$

有 Kraus 族 $K_k=\lvert o\rangle \langle k\rvert $，因而完全正且保迹；等距表示
$V\psi=\lvert o\rangle \otimes\psi$ 把原输入保存到另一数学环境因子。若该扩张实际实现，环境仍在整体内部；表示的存在不自动供应可访问的原记录。
这能实现“局部输出总回到同一状态”，但不是同维封闭酉门把所有不同输入消掉：酉作用保持正交性。程序输出自身的门词还需指定编码和解释规则；内容与地址的对应不能由重置式单独证明。

本轮不把这种重置直接解释为粒子的生成、湮灭或标准模型中的某个场。那些识别还需要局域可观测代数、时空对称、粒子表示、统计及具体作用量等物理输入；当前证明只涉及有限复矩阵的完整量子过程。

### 6.3 “内生”在本轮的准确含义

单位由原完整记录的总归一化给出，比较与零由同域历史定义；候选约束的两个元 $h,e-h$ 也都在该域内。
因此可把候选写成这些内部定义之间的相容条件，而无需另加一个来自外部的特殊滤片或优先观察者。
不过，把它称为定义间约束，不会使其成为纯逻辑恒真式：前面的负分支反例同时满足线性、保伴随和总归一化，却违反该约束。
数学上它准确选择正关系类；物理上为何实际世界只实现这个类，仍须有操作语义或经验支持。

**白话。**观察者可以从不同地方开始，先保留自己有来源的完整记录。只要两人已经知道自己处于同一套比较关系中，他们选哪一份单位作起点，都不会改变什么过程合法；但不知道的交集仍然不知道。把越来越多有来源的窗口接起来，可以得到共同关系空间。它没有替观察者打开上帝视角，也没有偷偷把未知的整体态算出来。

<a id="section-7"></a>

## 7. 本轮唯一完整候选

<a id="sec-c127-conclusion"></a>

> 在同一内部来源、同一 Hermitian 相干历史域及同一完整未条件化记录约定中，由全部原记录的归一化取得一份单位历史。它不能拆成两份自比较均为零的历史。

在有限过程接口中，继承的前件是复矩阵历史、复线性保伴随的候选更新及
$\sum_j\Phi_j(I)=I$。这些前件已给 $Q(e)=1$；本轮新增内容只有

$$
\nexists h:\ Q(h)=Q(e-h)=0.
$$

它不预设各支非负效果、不预设完全正、不另加入全端点传递性。
证明给出完整闭环：

$$
\text{固定单位不可双零分解}
 \Longleftrightarrow Q_{\rm rec}\ge0
 \Longleftrightarrow\text{全部原分支完全正}.
$$

所有零差的传递与比较替换、各支效果 $0\le E_j\le I$ 和量子仪器表示随之导出。
几何压缩成 $s\ge|c|^2$，有限中点亏损压缩成 $D_R=2R^2b$。
这两式展开的是同一候选，不增加第二条公理。

复线性、伴随、全部输入方向、完整原记录与后续接口仍有实质内容；本稿未证明复 Hilbert 体系是无结构逻辑的唯一模型。本轮给出数学证明和反例，未执行 C127 的 Lean 形式化或物理实验，亦不主张文献优先性或已确认的新物理规律。

### 本轮完整白话

**白话。**观察者顺着内部历史读关系，不必先看完整个世界。先把一次完整经历的原记录都留下，包括成功和失败；它们合在一起已经是一份确定的单位。现在只锁住一件事：这份一不能由两份真正的零拼出来。如果关系里藏着负的余量，就能把单位的一半放在两侧，再把负余量一正一反放进去，让两边各自完全相消，合起来却仍是一。所以禁止这种拆法，就会排除全部负关系，各个分支也自动成为合法的量子事件。从一段历史中扣掉沿单位方向的部分，剩余量必须不负；允许关系就落在抛物面上或其上方。边界表示没有剩余方向，上方表示还有独立内容。把真正的零差合并，剩下的关系有了内积；保留所有原记录，就有完整量子过程；相容的效果读数给概率，完整可逆给酉演化，内部时钟再给时间方程。不同观察者可以选不同起点，但只有已经认证的共同关系才能互相比较。所有单位、记录和参照都在整体里，本轮只锁住：完整的一份一，不能是两个真正的零。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c127-native"></a>

### [1]

The Omega Institute, *AURIC Native Reciprocal Comparison and Finite Endpoint Quantum C123*（含原生 C124 部分），新追加第 18–20 节。
[固定源码全文](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)；
[PR #26220 合入](https://github.com/the-omega-institute/trureturing/commit/0e9b83a26e2e56dd870f32ae9a28296850b179a7)，2026-11-03 21:57:34 UTC。
本稿逐式核读新增 271 行及直接依赖段；保留同源完整响应、指定 Lorentz 锥、原旋转、全载体双向返回、原尺度和数学群定义。该新增分类在普通数学文稿中，没有被本稿改述为新 Lean 定理。

<a id="ref-repo-c127-af"></a>

### [2]

The Omega Institute, *AbedNikolaevaNovikovAFDensityBound*。
[固定提交的完整 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.lean)；
[PR #26216 合入](https://github.com/the-omega-institute/trureturing/commit/d22b3725457f8aadbfb02504b868028cdd790424)，2026-11-03 21:59:12 UTC。
核读新文件 247 行及直接概率定义：$A\le n|A+iB|$ 与严格正定密度参数下原迹商的上确界界。源码含实际证明体；本轮未运行新的 Lean 构建。

<a id="ref-repo-c127-born"></a>

### [3]

The Omega Institute, *FiniteDimensional*。
[固定提交的直接概率接口](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/D5/S3/Quantum/FiniteDimensional.lean)，
`bornProbability rho P := Matrix.trace (rho * P)`。
已给的 Born 迹定义与本稿的概率表示证明分别说明。

<a id="ref-repo-c127-observers"></a>

### [4]

The Omega Institute, *AURIC Common Source Self Reference and Observer Sequences C117*。
[同一固定快照全文](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。
本轮与前轮快照逐项比较，该文未改；共同来源、实际门词和编码语义不由边缘态相同自动供应。

<a id="ref-stinespring1955"></a>

### [5]

W. F. Stinespring, ``Positive functions on $C^*$-algebras'',
*Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955).
[doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。
正映射的扩张表示；本稿给出有限历史商、最小表示及完整记录等距的直接证明。

<a id="ref-choi1975"></a>

### [6]

M.-D. Choi, “Completely positive linear maps on complex matrices”,
*Linear Algebra and its Applications* **10**(3), 285–290 (1975).
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。
有限 Choi 判据的原始出处；本稿由历史行分解直接证明所需等价链，并与下一项作者公开原文核对。

<a id="ref-watrous2018"></a>

### [7]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开电子版第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 表示及其等价条件。

<a id="ref-busch2003"></a>

### [8]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)。
完整效果可加概率的 Born 表示，包括二维；与只对锐投影的条件区分。
