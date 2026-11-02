# 补向相容、共同量子场与内部学习

从两态的一阶关系到同一个生成元

**AURIC v86：一个完整候选及其理论接续**

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮承接 v85，将问题收束到一个共同结构：当前态、相对于它的补空间、由补空间给出的切向变化，以及这些局部方向怎样拼成同一个可执行量子场。在继承的有限复态空间和共同转移读口上，只新增一个候选 $C_{86}$：同一完整可逆操作所给的各态切向响应，使任意两态的转移关系在一阶共同保持。本文不预设这张方向表来自同一个矩阵。

通过有限秩一参照框、Hermitian 实空间上的反伴随延拓、Jordan 乘法相容性，给出自足代数证明：候选恰好迫出 $\mathcal X(P)=-i[H,P]/\hbar$，其中同一个自伴 $H$ 只差共同标量。这将单态切向留下的补空间自由，锁成一个全输入共同作用。射影场与实际相位提升分别处理，保留项目已有完整相干比较合同。

一对正交方向生成一个 Bloch 三维片；场是这些片之间相容的方向分配，并非一张三维图容纳任意高维系统。在已经认证的共同场类内，一点的方向及其全部方向的一阶变化确定生成元到标量；固定有限生成元的更高阶变化形成有限递推。程序内容、门调用和学习记录均在整体内部：给出精确程序的正交性证明、可逆学习更新、记录归并余量，以及能量分块 Gram 匹配的有限可实现性定理。这些结论说明计算新内容怎样接上新轨道，也说明计算本身不等同于净能量流入。最后逐项接回标准有限维量子规则，明确所继承的正核、概率标定、复合和原生菜单。

全部论证为解析证明，未运行数学程序、数值实验或候选枚举。

## 目录

- [1. 版本位置：把共同作用前移到切向定义](#section-1)
- [2. 补、切向与整体：同一个分解的不同位置](#section-2)
- [3. 二元关系怎样归一提升为有限三维片](#section-3)
- [4. 本轮唯一新候选：二态补向相容](#section-4)
- [5. 主定理：一阶二态约束迫出共同生成元](#section-5)
- [6. 从共同场到门：必须保留相位提升](#section-6)
- [7. 反着推：删掉相容条件，会出现什么](#section-7)
- [8. 变化的变化：一点的全方向响应确定整个场](#section-8)
- [9. 更高阶变化形成有限递推，新的方向来自组合](#section-9)
- [10. 更大结构：场、读数与二元关系的统一](#section-10)
- [11. 内容即地址：计算、程序与实际调用怎样接合](#section-11)
- [12. 有限可实现性：两两关系匹配才能共用一个门](#section-12)
- [13. 内部学习是一种可实现过程，计算不等于净借能量](#section-13)
- [14. 怎样推出现有量子规则：完整依赖与关键证明](#section-14)
- [15. 完整白话图景与本轮候选的最简表述](#section-15)
- [来源与版本关系](#references)

<a id="section-1"></a>

## 1. 版本位置：把共同作用前移到切向定义

本轮记为 v86，直接承接已交付 v85。项目固定核验基线为 `c63ab162315fddd0801cbe9f47dbf3eda6e13360`。本轮两次有界实时 HEAD 获取均失败，不能认证该提交之后的仓库差异。相关核读覆盖 V67、V74、V78 综合稿与 V80 的下列章节；关键词检索范围为本地固定快照已有的 16 个 Markdown 文件。这不构成全仓库查重或文献优先权声明。

| 来源 | 已建立的接口 | 本轮接续 |
| --- | --- | --- |
| V67 §§2、6 | 内容、执行、未来比较及不可丢失的内部余码 | 将学习程序与执行条件放回同一整体 |
| V74 §§3–7 | 单曲线生成元、补空间自由、几何场、二阶读出恢复 | 从未认证的方向表推出共同生成元 |
| V78 §16 | 已有光滑酉族到 Schrödinger 形式 | 明确场认证与相位提升的先后 |
| V80 §§2、3、5 | 同一实际协议、相干锚、全输入幅度刚性 | 保留实际相位和原生供应合同 |
| v84、v85 | 实际酉执行与内部能量参照闭合 | 接回可逆执行与分块资源相容性 |

V74 已证明：单条曲线可以有很多生成元；只保持球面与辛形式不够；在二能级中保持全部点积的连续运动为共同酉转动。本轮新增的项目接口，是任意有限维的**二态一阶相容式及其直接代数证明**。其更大数学结构是射影态空间的等距场与矩阵生成元的对应，已有几何量子力学文献 [6](#ref-ashtekar)–[7](#ref-pastorello)。不把经典对应重新宣布为新发现。

本轮继承共同复正核、概率强度标定、相干参考、复合端口和完整记录。$\Omega$ 表示整体；有限维 $\mathcal H$ 是当前声明的比较与执行载体，其复维数 $d\ge1$，不把整体本身断言为有限维。控制器、程序、内部时钟和会返回的记忆均属于完整接口。$C_{86}$ 约束的是同一时刻、同一设置下的**可逆纯态场**；有选择的测量支路及丢弃记录后的局部通道，通过原有仪器结构处理。

**白话图景。**这次把问题收束为一句话：每个位置都能画一根箭头，但这些箭头何时属于同一个门？新增的约束直接检查两根箭头与两态关系是否合得上。合得上，整个场才能由同一个作用产生。

<a id="section-2"></a>

## 2. 补、切向与整体：同一个分解的不同位置

约定内积第二变量线性。对归一 $\psi\in\mathcal H$，定义

$$
P=\ket\psi\bra\psi,
\qquad Q=I-P,
\qquad \mathcal H=\operatorname{ran}P\oplus\operatorname{ran}Q.
$$

$Q$ 是相对于当前态的正交补投影，$Q\mathcal H$ 是所有水平可变方向的空间。它不等于某一根已选择的切向量。

若在同一载体内，整体另有一个归一向量代表 $\omega$，则

$$
\boxed{\omega=P\omega+Q\omega
=\langle\psi,\omega\rangle\psi+Q\omega.}
$$

此处 $P\omega$ 一般不是完整归一态 $\psi$。若硬要求 $\omega=\psi+w$、$w\perp\psi$ 且二者归一，则 $1=1+\lVert w\rVert^2$，只能有 $w=0$。当 $\Omega$ 表示事件关系整体而非向量时，上式应理解为选定表示中的投影分解，不能把集合补与向量加法混用。系统与环境的张量分解 $\mathcal H_S\otimes\mathcal H_R$，也不是这项正交直和分解。

### 定义 2.1（水平变化与射影切向）

归一曲线 $\psi(t)$ 的水平变化为

$$
v=Q\dot\psi,
\qquad \langle\psi,v\rangle=0.
$$

其纯态投影的速度为

$$
\mathcal X(P)=\dot P=\ket v\bra\psi+\ket\psi\bra v.
$$

它满足

$$
\boxed{\mathcal X(P)^\dagger=\mathcal X(P),\qquad
P\mathcal X(P)+\mathcal X(P)P=\mathcal X(P).}
$$

这些条件也充分：在 $P\oplus Q$ 分块下，它们强制两个对角块为零；取 $v=\mathcal X(P)\psi$ 就恢复上述表达。因此切向本身是**当前方向与补方向之间的非对角关系**。

若分解随历史移动，$Q(t)=I-P(t)$，还得到

$$
\boxed{\dot Q=-\dot P,\qquad
\dot P=P\dot P Q+Q\dot P P.}
$$

这给“补与动”一个精确联系：同一分解两侧的变化彼此相反。当 $d>2$，$Q$ 的秩为 $d-1$，不能一概称为另一个纯态。

对任意给定的水平 $v$，

$$
H_P=i\hbar\bigl(\ket v\bra\psi-\ket\psi\bra v\bigr)
$$

自伴且满足 $-i[H_P,P]/\hbar=\mathcal X(P)$。不过在单点还可加任意与 $P$ 对易的块，不改变这一根箭头。这正是 V74 已有的单态生成元自由。

**白话图景。**“反”可以精确对应相对于当前态的补方向；“动”是当前态与补方向之间已经建立的作用。补说明还有哪些方向可走，切向说明这一步实际朝哪里走。整体中的另一部分不会仅因存在，就自动把当前态推过去；还要有一条内部作用把二者接上。

<a id="section-3"></a>

## 3. 二元关系怎样归一提升为有限三维片

设 $v\ne0$，取 $\eta=v/\lVert v\rVert$。则 $\psi\perp\eta$，选定的二元载体为 $\mathcal S=\operatorname{Span}_\mathbb C\{\psi,\eta\}$。其中任意归一态 $\chi=\alpha\psi+\beta\eta$，$|\alpha|^2+|\beta|^2=1$，具有三维 Bloch 坐标

$$
\boxed{r(\chi)=
\bigl(2\operatorname{Re}(\bar\alpha\beta),,2\operatorname{Im}(\bar\alpha\beta),
|\alpha|^2-|\beta|^2\bigr),\qquad |r|^2=1.}
$$

恒等式由 $4|\alpha\beta|^2+(|\alpha|^2-|\beta|^2)^2=1$ 直接得到。有限测地步 $\chi(s)=\cos s\,\psi+\sin s\,\eta$ 对应 $r(s)=(\sin2s,0,\cos2s)$。初始切向方向落在球面切平面内。

任意两归一端态都能放进一个至多二维复载体；相同射线时该载体可以退化为一维。上一轮的二向量 Gram 提升同样保留。对非零 $u,w$，令

$$
C=\operatorname{Re}\langle u,w\rangle,quad S=\operatorname{Im}\langle u,w\rangle,quad
D=\lVert u\rVert^2\lVert w\rVert^2-|\langle u,w\rangle|^2\ge0,
$$

则 $(C,S,\sqrt D)/(\lVert u\rVert\lVert w\rVert)$ 位于单位上半球。但对 $u=\psi$、$w=v\perp\psi$，这个三元组总是 $(0,0,1)$。**因此仅保留归一 Gram 三个数，会丢掉“补空间里的哪根方向”。**必须同时保留载体嵌入、参考方向及强度 $\lVert v\rVert$。

当 $d=\dim\mathcal H>2$，纯态空间实维为 $2d-2$，不能由单个 Bloch 球容纳全部自由度。这里的有限三维提升是逐二元片的表示；重叠片之间的相容关系才构成整体场。任意一片的表示也不保证实际轨迹始终留在该片内。

```text
             r3
              ↑
              ψ •────→ 切向
             / \    （二元球面片）
            /   \
           η     其他补向

p(P,R) = (1 + r_P · r_R)/2
```

**白话图景。**可以把一对当前方向与补方向画成一个球面片：当前态在这里，下一步沿着球面走。高维整体中有许多这样的片。场的内容不仅是每个片里那根箭头，还包括各片重叠时不能互相打架。

<a id="section-4"></a>

## 4. 本轮唯一新候选：二态补向相容

记 $\mathcal P_1$ 为 $\mathcal H$ 上所有秩一正交投影。共同转移比较为

$$
p(P,R)=\operatorname{tr}(PR)=|\langle\psi,\phi\rangle|^2,
\quad P=\ket\psi\bra\psi,\ R=\ket\phi\bra\phi.
$$

这是已经标定的关系读口，不重新把 Born 标定当成待证空白。

### 定义 4.1（候选 $C_{86}$：同一可逆场的二态相容）

为每个 $P\in\mathcal P_1$ 指定一项切向 $\mathcal X(P)$，满足第 2 节的 Hermitian 切向条件。同一完整可逆设置中的这张方向表，应满足

$$
\boxed{C_{86}:\quad
\operatorname{tr}\bigl(\mathcal X(P)R+P\mathcal X(R)\bigr)=0
\quad\text{对任意 }P,R\in\mathcal P_1.}
$$

它就是两个态同时沿该方向表变化时，$p(P,R)$ 的一阶变化为零。只移动一个态、把另一个固定为读口时，转移读数当然可以改变。此处不假设 $\mathcal X$ 已由线性算子产生，也不预设光滑性。主定理以整个 $\mathcal P_1$ 为数学声明域；若原生准备菜单只供应其中一个子集，未经覆盖或延拓证明，结论不能直接外推到全空间。

用水平向量表示，同一条件为

$$
\operatorname{Re}\left\{
\overline{\langle\psi,\phi\rangle}
\left(\langle v_\psi,\phi\rangle+\langle\psi,v_\phi\rangle\right)\right\}=0.
$$

这条式子把两个局部补向与它们之间原有的关系锁在一起。它适用于声明的全部可准备输入；程序或返回记忆改变时，必须连同它们比较完整输入，不能对每个输入暗换设置，仍声称使用同一张场表。

若此前已经给出共同酉流，$C_{86}$ 自动成立。本轮的用途，是在只提出局部方向表时，把它作为**能否属于同一量子门的定义相容条件**。“所有对象内生”本身并不排除不满足此式的其他关系模型；后面的删除反例将说明差别。

**白话图景。**两点一起被同一个完整门带着走，不能一边说它们仍使用同一比较规则，一边偷偷把它们彼此的可区分关系拉长或压短。每个态的箭头都受其他态的箭头约束。这就是本轮唯一新增的要求。

<a id="section-5"></a>

## 5. 主定理：一阶二态约束迫出共同生成元

### 定理 5.1（有限维共同场刚性）

在有限复 $\mathcal H$ 上，切向表 $\mathcal X$ 满足 $C_{86}$，当且仅当存在同一个自伴算子 $H$，使

$$
\boxed{\mathcal X(P)=-\frac{i}{\hbar}[H,P]
\quad\text{对全部 }P\in\mathcal P_1.}
$$

$H$ 在加共同实标量 $cI$ 的意义下唯一。无需额外假定场连续：结论自动给出光滑场。

下面给自足证明，不以 Wigner 定理或已知酉流作为证明前提。

#### 第一步：有限参照把任意方向表锁成线性延拓

给定正交基 $e_j$，以下 $d^2$ 个秩一投影构成 $\operatorname{Herm}(\mathcal H)$ 的实基：

$$
P_{e_j},\qquad
P_{(e_j+e_k)/\sqrt2},\qquad
P_{(e_j+i e_k)/\sqrt2}\quad(j<k).
$$

记作 $R_a$。减去对应两个对角投影的一半，即得到每对非对角矩阵元的实、虚方向，所以它们确实张成，数量又恰为 $d^2$。在实 Hilbert–Schmidt 内积 $(A,B)=\operatorname{tr}(AB)$ 下，定义唯一实线性 $L$，使 $L(R_a)=\mathcal X(R_a)$。

对参照两两应用 $C_{86}$，得到

$$
(LR_a,R_b)+(R_a,LR_b)=0,
$$

由双线性延拓，$L^*=-L$。再对任意纯态 $P$ 与每个 $R_a$ 使用候选：

$$
(\mathcal X(P),R_a)=-(P,LR_a)=(LP,R_a).
$$

参照张成全部 Hermitian 空间，因此

$$
\boxed{\mathcal X(P)=L(P)\quad\text{对全部纯态 }P.}
$$

切向条件给 $\operatorname{tr}\mathcal X(P)=0$；线性延拓及反伴随性于是给 $L(I)=0$。

这同时证明候选的一个压缩形式：只须第二个输入遍历上述有限参照，第一个输入仍遍历全部纯态。**它不是有限次实验对未知任意场的全域认证。**

#### 第二步：纯态与补空间相容迫出 Jordan 乘法约束

取任意正交秩一分解 $I=\sum_jP_j$。切向条件给

$$
L(P_j)=L(P_j)P_j+P_jL(P_j),
$$

因此 $L(P_j)$ 只有第 $j$ 行、列的非对角项。又因 $\sum_jL(P_j)=0$，任意 $j\ne k$ 的交叉项满足

$$
\boxed{
L(P_j)P_k+P_jL(P_k)+L(P_k)P_j+P_kL(P_j)=0.}
$$

四项只支持 $(j,k)$、$(k,j)$ 两个位置；其系数正是 $L(P_j)+L(P_k)$ 在该位置的值，而其他 $L(P_\ell)$ 对该位置贡献为零。

对任意 Hermitian $A=\sum_j a_jP_j$ 展开，对角项使用切向条件，非对角项使用上述抵消式，得到

$$
\boxed{L(A^2)=L(A)A+AL(A).}
$$

将 $A+B$ 代入并减去两个平方式，得到极化式

$$
L(AB+BA)=L(A)B+AL(B)+L(B)A+BL(A).
$$

这是 Hermitian 矩阵 Jordan 乘法的导子条件。它不是另加公理，而是二态相容与纯态切向关系推出的更大结构。将算子复线性延拓至所有矩阵后，极化式仍成立。

#### 第三步：这类导子只能是同一个矩阵的对易作用

固定第一步所用正交基，写 $P_j=\ket{e_j}\bra{e_j}$。定义矩阵 $K_0$：

$$
(K_0)_{kj}=\bra{e_k}L(P_j)\ket{e_j}\quad(k\ne j),
\qquad (K_0)_{jj}=0.
$$

由 $L(I)=0$ 及 Hermitian 性，有 $(K_0)_{jk}=-\overline{(K_0)_{kj}}$，故 $K_0^\dagger=-K_0$。直接检查各矩阵元，$[K_0,P_j]=L(P_j)$。

令 $M=L-[K_0,\,\cdot\,]$。则 $M$ 仍反伴随、满足 Jordan 导子式，且 $M(P_j)=0$。

记 $E_{jk}=\ket{e_j}\bra{e_k}$。对 $P_j$ 与任意 Hermitian $A$ 应用极化式，有

$$
M(P_jA+AP_j)=P_jM(A)+M(A)P_j.
$$

所以 $M$ 保持每个二维实平面

$$
\operatorname{Span}_\mathbb R\{E_{jk}+E_{kj},\ i(E_{jk}-E_{kj})\}.
$$

反伴随性使它在该平面只可能是无穷小旋转。复线性延拓后可写为

$$
M(E_{jk})=i\theta_{jk}E_{jk},
\qquad \theta_{jk}\in\mathbb R,
\qquad \theta_{kj}=-\theta_{jk}.
$$

当 $j,k,\ell$ 互异时，$E_{jk}E_{k\ell}+E_{k\ell}E_{jk}=E_{j\ell}$。极化式因而给

$$
\theta_{j\ell}=\theta_{jk}+\theta_{k\ell}.
$$

故存在实数 $d_j$，使 $\theta_{jk}=d_j-d_k$。当 $d\ge3$ 可固定一个基指标直接构造；当 $d=2$ 只需取 $d_1=0,d_2=-\theta_{12}$；当 $d=1$ 场恒零。于是

$$
M=[i\operatorname{diag}(d_j),\,\cdot\,],
\qquad L=[K,\,\cdot\,],
\qquad K=K_0+i\operatorname{diag}(d_j),
\qquad K^\dagger=-K.
$$

取 $H=i\hbar K$ 就得到主公式。

#### 第四步：反向与唯一性

若 $\mathcal X(P)=-i[H,P]/\hbar$，则切向条件直接成立，且

$$
\operatorname{tr}\bigl([H,P]R+P[H,R]\bigr)=\operatorname{tr}[H,PR]=0.
$$

所以 $C_{86}$ 成立。若 $H_1,H_2$ 给出同一张场，则 $H_1-H_2$ 与每个秩一投影对易。在基投影下它必须对角；再与 $P_{(e_j+e_k)/\sqrt2}$ 对易，迫使所有对角元相同。因此只差 $cI$。证毕。

**白话图景。**证明的关键不是先写一个 Hamiltonian 再解释它。我们先只收集每个态怎样朝补方向变化。有限参照把这张表锁成共同关系，正交分解又要求各项在重叠位置互相接合，最后才逼出同一个矩阵。这个矩阵就是整张场的简洁内容。

<a id="section-6"></a>

## 6. 从共同场到门：必须保留相位提升

由主定理，固定场的流是

$$
P(t)=U(t)P(0)U(t)^\dagger,
\qquad U(t)=e^{-itH/\hbar}.
$$

微分右端即可验证，有限线性常微分方程保证唯一。水平向量是

$$
\boxed{v_\psi=-\frac{i}{\hbar}
\bigl(H-\langle\psi,H\psi\rangle I\bigr)\psi.}
$$

注意：$P\mapsto\mathcal X(P)$ 是线性超算子的限制，选定完整提升 $\psi\mapsto-iH\psi/\hbar$ 复线性；**水平表达**因减掉当前态的相位速度，一般不是 $\psi$ 的复线性函数。

设实际指定的幅度速度为

$$
w_\psi=v_\psi-\frac{i}{\hbar}a(\psi)\psi,
\qquad a(\psi)\in\mathbb R.
$$

它与上述射影场相同。当且仅当

$$
\boxed{a(\psi)-\langle\psi,H\psi\rangle=c
\quad\text{与输入无关}}
$$

时，$w_\psi=-i(H+cI)\psi/\hbar$ 是同一个线性 Schrödinger 提升。允许时间依赖时，$c$ 可是同一时刻对所有输入相同的 $c(t)$。

射影候选本身看不见 $a(\psi)$ 的逐输入变化；项目 V80 已有的完整复核比较正是用来认证这个相位提升。例如 $F_t(\psi)=e^{it f(P_\psi)}\psi$ 在射影上恒等，但一般不是同一个线性幅度门。当一个分支相对于另一个分支的相位可以被内部参考读到时，它不是可任意丢弃的整体相位。

对时间依赖的方向表逐时满足候选，得到 $H(t)$；若方向表随时间连续，可取迹零规范使 $H(t)$ 连续，进而得到酉传播子。时间不变的场才给自治一参数群；任意程序切换不可冒充自治。

**白话图景。**球面上的箭头确定“往哪里走”，还没有确定所有支路怎样相互对相位。旧版本已经保留的相干参考在这里继续工作：它把同一轨道上的相位接起来，于是局部方向、完整量子门与可读出的干涉保持一致。

<a id="section-7"></a>

## 7. 反着推：删掉相容条件，会出现什么

### 7.1 只有归一、补向和保辛，仍可把两态关系扭坏

在 Bloch 球取

$$
F(r)=\kappa r_z\,e_z\times r,
\qquad \kappa\ne0.
$$

它处处切于球面，保持归一，且是一个二次球面函数的 Hamiltonian 场，保持辛形式，但各纬度的转速不同。取

$$
r=(1,0,0),
\qquad s=(0,\sqrt{1-a^2},a),
\qquad 0<a<1.
$$

有 $F(r)=0$、$F(s)=(-\kappa a\sqrt{1-a^2},0,0)$，所以

$$
\left.\frac{d}{dt}\frac{1+r(t)\cdot s(t)}2\right|_{t=0}
=-\frac{\kappa a\sqrt{1-a^2}}2\ne0.
$$

这直接违反 $C_{86}$。每个点都可另造一个局部自伴生成元，却不能由一个全输入共同量子门产生整张场。这是 V74 保辛反例的一阶二态检验形式。

### 7.2 只检查正交关系的一阶变化，条件甚至可能为空

若 $PR=0$，任意合法切向都有 $\operatorname{tr}(\mathcal X(P)R)=\operatorname{tr}(P\mathcal X(R))=0$。因此仅检查一阶的正交态对，会漏掉所有上述非正交关系扭曲。只检查 $P=R$ 同样只重复切向归一条件。

只检查有限参照彼此也不够。对 $d\ge2$，取非零共同场 $\mathcal X_H$，令

$$
f(P)=\prod_a\bigl(1-\operatorname{tr}(PR_a)\bigr),
\qquad \widetilde{\mathcal X}(P)=f(P)\mathcal X_H(P).
$$

它在所有参照上为零，故参照间测试全部通过，却在其他一些点非零。若它来自共同 $H'$，则 $H'$ 与全部参照对易，进而与它们张成的所有矩阵对易，只能为标量，迫使场处处零，矛盾。因此有限参照必须与每个声明输入比较。

### 7.3 少了完整输入接口，同一规则会变成按输入换规则

若控制记忆 $m$ 决定 $H_m$，比较 $P$ 与 $R$ 时分别偷偷选不同 $m$，就不是同一个闭合纯态场。正确方式是在完整 $P\otimes P_m$ 上比较同一处理器；忽略控制记录后，局部演化可以有噪声、条件性和混合态。它们可由原有量子仪器描述，并不反驳共同场定理。

### 7.4 三维局部图不替代共同正核

每对关系分别可画出来，不保证整个关系表为正。三阶矩阵对角元为 1、所有非对角元为 $-3/4$，每个二阶主块均正，但对 $\mathbf1=(1,1,1)$，

$$
\mathbf1^\dagger K\mathbf1=-3/2.
$$

因此共同复正核仍是继承背景；单靠“有正交分解”不能重新推出 Hilbert 空间。

| 拿掉什么 | 可以出现的后果 |
| --- | --- |
| 全输入二态相容 | 每个态各自绕圈，整体比较关系随时间扭曲 |
| 非正交态的比较 | 一阶正交测试全部通过，仍漏掉非量子方向表 |
| 完整相位参考 | 射影完全相同，实际跨支相位可以不同 |
| 共同设置与返回记忆 | 同一输入标签背后暗换控制，失去单一过程身份 |
| 公共复正核 | 两两可画，整体却没有共同 Hilbert 实现 |
| 实际调用菜单 | 矩阵存在，但尚无所需原生控制或资源 |

**白话图景。**反着推会发现，缺的不是“能不能给每一点画个圈”。那太容易了。真正的限制是：所有圈必须共用一张关系网，不能对不同输入各讲一套运动规则。这使候选成为可以被反例击穿的约束，而不只是一幅看起来合理的图。

<a id="section-8"></a>

## 8. 变化的变化：一点的全方向响应确定整个场

### 定理 8.1（共同场的一阶局部资料）

在已经由 $C_{86}$ 认证的场类内，一个点的场值及该场向所有邻近方向的一阶变化，唯一确定 $H$ 到共同标量。

**证明。**取射影坐标 $\psi(z)\sim(1,z)^{\mathsf T}$，$z\in\mathbb C^{d-1}$，写

$$
H=\begin{pmatrix}a&b^\dagger\\b&C\end{pmatrix},
\qquad M=C-aI.
$$

由两块 Schrödinger 方程对分量比 $z=\psi_\perp/\psi_0$ 求导，得到

$$
\boxed{i\hbar F(z)=b+Mz-z(b^\dagger z),\qquad F(z)=\dot z.}
$$

因此

$$
\boxed{b=i\hbar F(0),qquad
Mu=i\hbar\,DF(0)[u]\quad\text{对全部 }u.}
$$

这确定了 $b$ 及 Hermitian $M$，从而确定 $H-aI=\left(\begin{smallmatrix}0&b^\dagger\\b&M\end{smallmatrix}\right)$。独立实参数数目为 $2(d-1)+(d-1)^2=d^2-1$。当 $d=1$ 时无射影运动，结论退化为标量自由。

这与 V74 的“矩阵期望读数及其前两阶资料确定算符”一致：读数先微分为方向，所以场的一阶资料对应读数的二阶资料。新增候选先认证这张场确实属于矩阵类，随后才能使用有限资料恢复。

必须区分 $DF(0)$ 与一条轨迹的加速度。后者只给 $DF(0)[F(0)]$ 等沿实际方向的资料，不给全部横向响应。例如 $H_1=0$ 与 $H_2=\ket1\bra1$ 在初态 $\ket0$ 上都给固定射线，却对叠加态产生不同作用。再长的同一固定态记录，也补不全这个门。

非静止历史也可如此：

$$
H_\lambda=\begin{pmatrix}0&\kappa&0\\\kappa&0&0\\0&0&\lambda\end{pmatrix},
\qquad\kappa\ne0,
\qquad\psi(0)=e_0.
$$

所有 $\lambda$ 的整条实际轨迹及其全部时间导数都相同，因为它们留在前两个坐标内；第三方向的响应却不同。

在二能级，写 $H=cI+\frac{\hbar}{2}b\cdot\sigma$，则

$$
\boxed{\dot r=b\times r.}
$$

这个结论也可直接在三维证明：候选变成 $F(r)\cdot s+r\cdot F(s)=0$。取三个坐标轴参照，以 $F(e_j)$ 为列组成矩阵 $B$，得到 $F(r)=-B^{\mathsf T}r$；再代入参照得 $B=-B^{\mathsf T}$。三阶反对称矩阵恰为某个固定向量的叉乘作用。$b$ 对输入一致。$b\ne0$ 时，$r\cdot b$ 恒定，轨迹为绕 $b$ 轴的纬圈，极点固定；$b=0$ 时全部射线固定。一根箭头只确定 $b$ 的横向部分；周围箭头怎样变化补上纵向部分。这个二能级结论直接给出持续基础门圆轨道。更高维仍保留 v85 已证的多能隙、多频率边界。

**白话图景。**“变化的变化”确实能把门认出来。现在往哪走，是第一份资料；把当前态往周围轻轻换一个方向，箭头怎样跟着改变，是第二份资料。在相容的量子场里，这些资料已经够了。沿一条路一直看下去，未必知道旁边的路怎么走，所以单条历史与完整场仍有区别。

<a id="section-9"></a>

## 9. 更高阶变化形成有限递推，新的方向来自组合

固定 $H$ 时，定义

$$
\mathcal L_H(A)=-\frac{i}{\hbar}[H,A].
$$

反复微分给

$$
\boxed{P^{(n)}(t)=\mathcal L_H^n(P(t)).}
$$

$\mathcal L_H$ 是 $d^2$ 维矩阵空间上的线性算子，Cayley–Hamilton 恒等式因此把足够高阶导数写成有限个较低阶导数的固定线性组合。更具体地，在 $H$ 的本征基上，矩阵元的频率是 $(E_j-E_k)/\hbar$。只存在有限多个能隙频率；零频率及成对正负频率给一个实系数消去多项式。所以固定有限系统中的“变化、变化的变化、再变化”不必新增无穷多个独立对象。

不同共同场也可组合。在超算子对易约定下，

$$
[\mathcal L_A,\mathcal L_B]
=\mathcal L_{-i[A,B]/\hbar}.
$$

这由 $[\operatorname{ad}_A,\operatorname{ad}_B]=\operatorname{ad}_{[A,B]}$ 直接得到。为避免把二阶控制参数误作物理时间，另用无量纲反 Hermitian 控制矩阵 $K_1,K_2$ 写

$$
e^{sK_1}e^{sK_2}e^{-sK_1}e^{-sK_2}
=I+s^2[K_1,K_2]+O(s^3).
$$

乘开到二阶即可验证：一阶互消，留下顺序不交换产生的方向。它说明计算一个新门内容，可以是在已有关系的组合中找出新作用方向。

这个公式需要相应正、逆小步实际可调用。项目只允许完整正脉冲时，不能借公式偷偷加入分数脉冲或负时间控制。v84 已有的正历史精确周期逆门、或近似回返逆门，分别提供其声明范围内的替代。“生成元在代数中存在”“可近似到达”“某个有限原生词精确执行”须保持各自含义。

### 命题 9.1（全部过去导数也不决定任意未来控制）

令

$$
f(t)=\begin{cases}0,&t\le0,\\e^{-1/t^2},&t>0.\end{cases}
$$

$f$ 光滑且在零点全部导数为零。选非标量自伴 $V$，则 $H_1(t)=0$、$H_2(t)=f(t)V$ 在过去及零点全部时间导数相同，但对非本征输入给出不同未来轨迹。

**证明。**每阶导数是 $e^{-1/t^2}$ 乘 $1/t$ 的有限多项式，趋零。第二条传播子为

$$
\exp\left[-\frac{iV}{\hbar}\int_0^t f(s)\,ds\right],
$$

在足够小的正时间对非本征输入产生非平凡射线变化；第一条保持不动。

故内部预测必须包含真实控制规律、程序和可用资料。只说整体包含未来，不能替代一个可计算、可辨识的预测接口。

**白话图景。**固定的场可以用有限规则生成一层又一层变化；把已有作用按不同顺序组合，也能得到新的方向。这很接近“从内部结构算出新路线”。但若之后还会有新的内部程序切换，预测就得把那个程序一起算进去，不能仅凭过去的轨迹猜出尚未给定的控制。

<a id="section-10"></a>

## 10. 更大结构：场、读数与二元关系的统一

主定理给出 $H$ 后，定义其内部读数函数

$$
f_H(P)=\operatorname{tr}(HP).
$$

在继承的水平几何中，取

$$
g(u,v)=2\hbar\operatorname{Re}\langle u,v\rangle,
\qquad
\omega(u,v)=2\hbar\operatorname{Im}\langle u,v\rangle,
\qquad Ju=iu.
$$

对任意水平 $w$，

$$
df_H(w)=2\operatorname{Re}\langle(H-f_HI)\psi,w\rangle,
$$

因此

$$
\boxed{\omega(v_H,w)=df_H(w),\qquad
v_H=-J\operatorname{grad}f_H.}
$$

这里的场、生成元、读数及其变化是同一对象在不同接口上的表达。沿自己生成的流，$df_H(v_H)=\omega(v_H,v_H)=0$，所以读数可保持而轨迹仍在运动。

若该生成参数由内部时钟标定为时间，$H$ 就是对应的能量生成元；若尚未给时钟与尺度，它首先是相对于该参数的作用生成元。$\hbar$ 的物理数值不由归一化推出。同一平均读数也不决定方向：在 $\ket0$ 上，$H_x=\hbar\nu\sigma_x/2$、$H_y=\hbar\nu\sigma_y/2$ 均值都为零，却给不同切向。把生成元当作统一对象是可行的；把单一平均能量数当成全部场信息则不够。

对任意两个自伴 $A,B$，定义

$$
A\circ B=\frac{AB+BA}{2},
\qquad
\{A,B\}_{\rm q}=\frac{AB-BA}{i\hbar}.
$$

对称部分组织共同读数与二阶波动，反对称部分组织作用顺序与运动。主证明中的 Jordan 导子与这里的对易生成元相互对应。这就是候选所属的矩阵可观测量代数与射影几何结构，无需为“场”“变化的变化”各引入一套互不关联的基本实体。

全部相容场构成 $\operatorname{Herm}(\mathcal H)/\mathbb RI$ 的 $d^2-1$ 维实空间，相应反 Hermitian 生成元取商后为 $\mathfrak u(d)/(i\mathbb RI)\cong\mathfrak{su}(d)$。它们积分为共同射影酉作用；原生可调用场可以只占其中一部分。

本文的“场”严格指态空间上的方向场。电磁场等时空局域场还需要空间位置、局域耦合与传播结构；有限二元提升本身没有证明这些额外结构已经出现。

**白话图景。**同一个内部作用，摊开看是每个态上的箭头，压缩看是一个生成元，接上读口看是一个数及它的变化。这里确实可以少立很多孤立概念。“能量、场、激发”能否共用这张图，取决于内部时钟和参考怎样接上，而不是先把几个词宣布为完全同义。

<a id="section-11"></a>

## 11. 内容即地址：计算、程序与实际调用怎样接合

沿用 V67 的合同：内容身份、执行算子、当前末态与未来可比较行为不是同一个判据。内容可以是完整内部程序结构本身，无须假定另有一个脱离它的外部地址。但是，同一末态不决定完整门：$I$ 与 $\operatorname{diag}(1,-1)$ 都把 $\ket0$ 留在原处，却对其他输入不同。若实际历史或相干参考仍可读，等价关系必须保留它们。

给组成程序载体完整正交基的有限内部程序态 $\ket p$，一个明确的完整处理器可写为

$$
\boxed{W=\sum_p\ket p\bra p\otimes U_p.}
$$

若每个 $U_p$ 酉，直接计算 $W^\dagger W=I$。程序内容 $p$ 与可调用作用 $U_p$ 通过处理器内部的控制关系接在一起。若程序是叠加 $\sum_pc_p\ket p$，则

$$
W\left(\sum_pc_p\ket p\otimes\ket\psi\right)
=\sum_pc_p\ket p\otimes U_p\ket\psi,
$$

通常产生纠缠；忘掉程序后得到相应混合通道，不能把它直接叫作一个已选定的纯态门。

### 定理 11.1（精确确定程序必须区分不等价的完整酉作用）

设固定完整等距处理器 $W$ 对程序 $p,q$，能对**所有**未知数据输入精确实现酉门 $U,V$。若 $U^\dagger V$ 不是标量，则 $\langle p,q\rangle=0$。

**证明。**完整输出的数据部分为纯态，故对固定程序可写成 $U\psi\otimes r_{p,\psi}$。对基输入与其叠加使用线性性，迫使残余向量与输入无关，记为 $r_p$。于是任意 $\psi,\phi$ 的输入输出内积保持给

$$
\langle p,q\rangle\langle\psi,\phi\rangle
=\langle r_p,r_q\rangle\langle\psi,U^\dagger V\phi\rangle,
$$

即

$$
\boxed{\langle p,q\rangle I
=\langle r_p,r_q\rangle U^\dagger V.}
$$

若残余重叠非零，右式迫 $U^\dagger V$ 为标量；否则左式也为零。

这是 Nielsen–Chuang 精确可编程处理器定理的两输入证明 [8](#ref-nielsen)。所以 $m$ 维程序载体不能确定、精确地供应超过 $m$ 个两两不等价的酉通道。近似、概率成功和仅匹配一个已知输入不在该定理的同一范围。比较载体若包含相位控制支路，就须在那个更大载体上判断两门是否只差整体相位。

不断增长的程序串、可变长度执行及固定精度近似通用计算不被这项固定维数结论禁止。若目标门还改变运行时长、停止规则或控制设置，它们也属于实际程序内容。

**白话图景。**算出一条新路线，可以在内部留下一个可用的程序内容。这个内容真正带着系统走，还要经过已有处理器的耦合。如果两个不同门的程序根本无法区分，同一个确定处理器就不能对任意未知输入准确执行两者。“地址就是内容”因此也有物理容量与相容条件。

<a id="section-12"></a>

## 12. 有限可实现性：两两关系匹配才能共用一个门

下面的结论直接把“算出内容”与“存在共同执行”连接起来，并沿用 v85 已认证的总能量参照 $G$。不再新增公理。

### 定理 12.1（内部能量块上的 Gram 插值）

在同一个有限完整载体上，事先固定 $G=\sum_\lambda\lambda\Pi_\lambda$。给有限拟议输入、输出族 $z_a,w_a$。存在同一个完整酉 $U$，满足

$$
Uz_a=w_a\quad\forall a,
\qquad [U,G]=0,
$$

当且仅当

$$
\boxed{\langle z_a,\Pi_\lambda z_b\rangle
=\langle w_a,\Pi_\lambda w_b\rangle
\quad\text{对全部 }a,b,\lambda.}
$$

**证明。**必要性由 $U^\dagger\Pi_\lambda U=\Pi_\lambda$ 立即得到。反之，在每个能量块上定义

$$
T_\lambda\left(\sum_ac_a\Pi_\lambda z_a\right)
=\sum_ac_a\Pi_\lambda w_a.
$$

二元 Gram 相等使两边范数平方对任意系数 $c_a$ 一致，因而该映射良定义、等距、像空间维数相同。在同一个有限能量块内补齐正交基，把它延拓为酉 $U_\lambda$。令 $U=\bigoplus_\lambda U_\lambda$，则得到所需结论。

没有能量限制时，去掉分块即可得到通常的 Gram 插值条件。总能量守恒的背景来自 v85，而不是针对拟议门事后挑一个 $G$。这里 $z_a,w_a$ 使用共同相干参考固定的向量代表；若只规定输出射线，则条件应是存在各输出相位使相应 Gram 等式成立。

这项判据本身也有二元三维表达。对任意两项及某能量块，写

$$
\Gamma=\begin{pmatrix}p&c\\\bar c&q\end{pmatrix}\ge0,
\qquad s=p+q.
$$

当 $s>0$，令

$$
\boxed{r_\Gamma=\frac{(2\operatorname{Re}c,-2\operatorname{Im}c,p-q)}s,
\qquad |r_\Gamma|^2=1-\frac{4(pq-|c|^2)}{s^2}\le1.}
$$

按标准 Pauli 约定，$\Gamma/s=(I+r_\Gamma\cdot\sigma)/2$。因此每个二元能量块是一颗三维球内的点，加上它的权重 $s$；$s=0$ 时保留零块，不做除法。分块 Gram 匹配恰要求这些点与权重一并匹配。三维归一坐标不能取代被归一化之前的资源权重。

仅保每个态的能量分布还不够。取两个能量块，分别有正交基 $a_0,a_1$ 与 $b_0,b_1$，令

$$
\begin{aligned}
z_1&=(a_0+b_0)/\sqrt2,&z_2&=(a_1+b_1)/\sqrt2,\\
w_1&=z_1,&w_2&=(a_0-b_0)/\sqrt2.
\end{aligned}
$$

输入、输出各是正交归一对，每个态在两块的概率都为 $1/2$。但两个输入的分块交叉内积为零，输出的为 $1/2$ 与 $-1/2$。所以不存在一个守恒 $U$ 同时实现这些要求。

该定理保证**数学上存在**相容酉，未保证原生菜单能精确调用它。实际合成仍须遵守完整脉冲、资源、误差与历史条件。

**白话图景。**给每个输入各算出一个看起来可达的终点，还不等于算出了一个共同量子门。两个输入原来在每个内部块里怎样重叠，执行后仍须对得上。把这些二元关系一起配平，才得到一份不会互相矛盾的完整门内容。

<a id="section-13"></a>

## 13. 内部学习是一种可实现过程，计算不等于净借能量

给内部数据记录 $d$、当前程序 $p$、一个声明的误差读口或损失 $\ell(p,d)$，以及更新函数 $f(d,p)$。有限二进制寄存器上可定义

$$
\boxed{L_f:\ket{d,p,z}\longmapsto
\ket{d,p,z\oplus f(d,p)}.}
$$

它是基态置换，故酉。初始 $z=0$ 时，第三个寄存器得到新程序，旧输入仍保留。随后由第 11 节的受控处理器执行所选门；新读出回到记录，继续更新。数据、假设、误差与更新规则都可放在 $\Omega$ 内部。只有当这些接口真的供应时，才称为一个具体学习过程。量子演化本身不自动保证损失下降、预测正确或某种算法收敛。

这里可复制的是正交记录。任意未知量子内容不能被无条件复制：若完整等距满足 $\psi\otimes0\mapsto\psi\otimes\psi\otimes r_\psi$，两输入内积给

$$
c=c^2\langle r_\psi,r_\phi\rangle,
$$

在 $0<|c|<1$ 时取模即矛盾。所以内部学习也不获得对一份未知态全部坐标的无扰读取能力。

若更新需要把不同历史物理合并为同一内容，V67 的内部余码结论继续适用。设

$$
V\ket h=\ket{f(h)}\ket{r_h}
$$

是完整等距，输入历史正交、输出内容态归一，则

$$
\delta_{hk}=\langle f(h),f(k)\rangle\langle r_h,r_k\rangle.
$$

若内容采用正交记录编码，第一因子才可进一步写为 Kronecker 符号。同一内容下的不同历史必须由正交余码区分。因此有限确定归并需要

$$
\dim R\ge\max_c|f^{-1}(c)|.
$$

被学习器忽略的差别仍留在整体内部；工作地址相同不使完整历史消失。这也解释了为何增长的记录可使工作层呈现单向过程，而完整执行保持可逆结构。

### 命题 13.1（内容变化不迫使正的净能量流入）

事先固定完整示例载体 $\mathbb C^2_E\otimes\mathbb C^2_P$ 及自治能量生成元

$$
G=\ket1\bra1_E\otimes(3gI_P+g\sigma_x^P),
\qquad g>0.
$$

经过内部时间 $T=\pi\hbar/(2g)$，其传播子恰为

$$
U(T)=\ket0\bra0_E\otimes I_P+\ket1\bra1_E\otimes\sigma_x^P.
$$

它将 $\ket{1,0}$ 变为 $\ket{1,1}$，改变程序内容而保持全部能量分布。

**证明。**$E=0$ 块的演化恒等；$E=1$ 块为 $e^{-i3gt/\hbar}e^{-igt\sigma_x/\hbar}$。在 $t=T$，前因子为 $i$，后一因子为 $-i\sigma_x$，故乘积为 $\sigma_x$。初态在 $G$ 的两个能量 $2g,4g$ 上各占 $1/2$，整个演化保持这些概率，均值始终为 $3g$，方差为 $g^2$。

例子否定“有计算步骤或新地址，必有正净能量借入”的普遍推论。它使用事先给定的内部耦合及有能量方差的初态，不证明初态准备、硬件、时钟读出和存储无需资源；实际所用部件仍须在完整载体上结算。这里 $G$ 自身就是运行的自治生成元，也不是为某个先给出的门事后挑选的对数或零算子。

因此，用户所说的“借”最稳固的统一含义是：**把整体内部原先未在该工作接口上调用的结构，接成了新的可用作用。**它可能借用相位参照、程序容量、相关性、触发资源或能量转移。若把“借能量”专指能量读数转移，就应继续服从 v85 的完整守恒与分块匹配，不能从“算出了内容”直接推出。

**白话图景。**学习可以全部发生在整体里面：留下经验，比较结果，更新可调用的内容，再沿新路线执行。所谓“借”，可以理解为把整体里已经有的结构接过来使用。新地址不一定需要净借进一笔能量；但它需要真实的内容、记录、参照和执行关系。这些都不能因工作态看起来回到了原点而被删掉。

<a id="section-14"></a>

## 14. 怎样推出现有量子规则：完整依赖与关键证明

本轮是连续理论的一个增量。$C_{86}$ 精确解决“局部方向是否来自共同门”的问题，不把已经继承的复正核、概率和复合条件藏进结论。

| 标准规则 | 内部关系前件 | 得到的表达 |
| --- | --- | --- |
| 复 Hilbert 态空间 | 共同归一复正核；零关系商与张成 | $K(x,y)=\langle x,y\rangle$ |
| 可逆共同动力学 | v84 实际门认证；本轮切向相容 | $\mathcal X(P)=-i[H,P]/\hbar$ |
| Schrödinger 方程 | 共同场及既有相位提升；内部时间标定 | $i\hbar\dot\psi=H\psi$ |
| Born 效果读出 | 内部结果分支与已标定强度 | $p_e=\operatorname{tr}(\rho M_e^\dagger M_e)$ |
| 密度算子 | 正、归一、相容的效果读数泛函 | $\rho\ge0,\ \operatorname{tr}\rho=1$ |
| 复合系统 | 积核与产品参照张成 | $\mathcal H_{AB}\cong\mathcal H_A\otimes\mathcal H_B$ |
| 测量与一般通道 | 记录显化、分支选择或忽略记录 | $\rho\mapsto\sum_eM_e\rho M_e^\dagger$ |
| 理想投影更新 | 投影效果并固定其范围内全部纯态 | $\rho\mapsto P\rho P$ |
| 能量守恒 | v85 独立内部能量读口与有限均值闭合 | $[U,G]=0$ |
| 内部学习与程序调用 | 记录、误差、可逆更新及原生处理器 | 新程序内容及条件执行 |

### 共同正核到 Hilbert 空间

对有限形式和 $u=\sum_i c_i[x_i]$，定义

$$
\langle u,u\rangle=\sum_{i,j}\bar c_i c_jK(x_i,x_j)\ge0.
$$

正半定性使零范数向量与一切向量正交；商掉零空间便得内积空间。在有限秩切口内已是有限维 Hilbert 空间。复线性叠加是同一关系实现中的线性结构，并非从两个正交向量的存在单独推出。

### 共同场到酉门和 Schrödinger 方程

主定理直接得到 $H=H^\dagger$，相位比较固定实际提升。解 $\dot U=-iHU/\hbar$ 后，$\frac d{dt}(U^\dagger U)=0$，故初值 $U(0)=I$ 给酉门。固定 $H$ 为指数流；随内部程序变化的 $H(t)$ 给相应传播子。这与 v84 对实际有限门的认证相互兼容，适用前件不同。

### 显化内部记录得到效果和 Born 形式

对完整酉 $W$ 与内部记录初态 $\ket0$，在正交记录基 $\ket e$ 下定义

$$
M_e=(I\otimes\bra e)W(I\otimes\ket0).
$$

酉性给 $\sum_eM_e^\dagger M_e=I$。在既有“分支强度即概率”的标定下，

$$
p_e(\psi)=\lVert M_e\psi\rVert^2
=\langle\psi,E_e\psi\rangle,
\qquad E_e=M_e^\dagger M_e\ge0.
$$

结果条件态由 $M_e\psi$ 归一给出；零概率支路不定义归一条件态。这里明确使用已有概率标定，未假装 $C_{86}$ 独立推出随机读数语义。

### 相容效果读数得到密度矩阵

设 $f$ 定义在全部效果 $0\le E\le I$，正、归一，且当 $E+F\le I$ 时 $f(E+F)=f(E)+f(F)$。先由单调性和有理分割得到实齐次性；对正算子 $A$ 取正整数 $n\ge\lVert A\rVert$，定义 $F(A)=nf(A/n)$，该定义与 $n$ 无关且在正锥上可加。再以正负分解延拓为 Hermitian 空间上的实线性泛函。有限维迹配对给唯一 $\rho$，使 $F(A)=\operatorname{tr}(\rho A)$。正性给 $\rho\ge0$，归一给 $\operatorname{tr}\rho=1$。

### 积核得到张量积，忽略记录得到通道

若独立准备的共同核为

$$
K_{AB}((x,y),(x',y'))=K_A(x,x')K_B(y,y'),
$$

映射 $[x,y]\mapsto[x]\otimes[y]$ 保全部 Gram。产品准备张成声明的复合载体时，它延拓为酉同构。忽略完整记录给 $\Phi(\rho)=\sum_eM_e\rho M_e^\dagger$。反向，任何有限完整 Kraus 族给等距 $V\psi=\sum_eM_e\psi\otimes\ket e$，可在匹配总维度的载体中补齐为酉。若只有迹不增支路，须补失败算子。这样的数学扩张不自动满足独立指定的 $G$ 守恒或原生门供应。

### 理想投影还需要范围内不扰动

若某结果的效果为投影 $P$，其 Kraus 算子 $A_\alpha$ 满足 $\sum_\alpha A_\alpha^\dagger A_\alpha=P$。对 $\ker P$ 的向量求范数和可知 $A_\alpha=A_\alpha P$。当 $P\ne0$，若该结果还固定 $\operatorname{ran}P$ 内每个纯态，则每个 $A_\alpha\psi$ 都与 $\psi$ 共线；对两态及其叠加使用线性性，得到 $A_\alpha=c_\alpha P$，$\sum|c_\alpha|^2=1$。故该结果的未归一更新恰为 $P\rho P$。$P=0$ 时所有 Kraus 算子为零。

由此得到完整的有限维量子表示、可逆动力学、复合、效果与仪器结构。全数学过程类还需相应全菜单；具体项目的原生受限菜单给其可执行子理论。整体内生性使条件都由内部对象陈述，但不会单凭“都在整体中”就逻辑排除所有其他物理模型。

**白话图景。**已有量子规则可以接成一条完整链：共同关系决定态空间，两态变化相容决定共同运动，内部记录的分支决定测量，忽略记录得到局部混合，独立准备的积关系给出复合系统。新候选填的是“局部箭头怎样成为同一个门”这一环。把每一环的前件写明，才不会把想证明的量子规则偷偷放回定义里。

<a id="section-15"></a>

## 15. 完整白话图景与本轮候选的最简表述

把 $\Omega$ 看成包含准备、关系、程序、观察者和记录的整体。内部的一个观察者选出当前态，就同时选出了“沿当前态”和“相对于它的其他方向”这项分解。真正的变化，是当前方向与某个补方向之间已经建立的内部作用。当前态与一个选定补向可以画成一个三维球面片；整个场，是许多这样的片相互接合后的箭头图。

箭头不能任意画。同一完整可逆门带着两个态一起走时，它们之间的比较关系要保持。只要求这一条两态的一阶相容式，就能把各处零散箭头压成同一个自伴生成元。它在每个态上的投影是切向，接到读口上是一个可观察数，接到内部时钟上才获得能量的时间尺度含义。二能级时持续固定作用给圆轨道；高维时多个能隙共同决定轨迹。一点的箭头及周围箭头如何改变，足以识别这个共同场；单条历史则可能缺少横向资料。

整体中的一部分还可以保存经验、比较预测误差、计算新的程序内容。当这个内容通过内部处理器连接到工作态时，新的门才真正被调用，工作轨迹随之改变。这是一种可以完整放进量子理论的学习过程。更新旧内容所忽略的信息留在内部余码与记录里；新程序所需的容量、相位与资源也留在同一本账中。“借”可以指接入新的内部可用作用，但计算新地址不自动等于净借入正能量。

用户的“道是整体，反是补，动是切向”可用作这一结构的直观记忆：

$$
\boxed{\text{整体内的分解}
\ \longrightarrow\ \text{当前态与补向的作用}
\ \longrightarrow\ \text{二态相容的共同场}.}
$$

其数学骨架只有一个本轮候选：

$$
\boxed{\text{同一可逆场中，两态关系的一阶变化为零}}
$$

$$
\boxed{
\operatorname{tr}\bigl(\mathcal X(P)R+P\mathcal X(R)\bigr)=0
\quad\Longleftrightarrow\quad
\mathcal X(P)=-\frac{i}{\hbar}[H,P].}
$$

这不是从一句哲学表述直接证明自然规律，而是把直观图景压成一个作用于二元关系、可以证明其后果、可以删除检验、可以接回量子规则的内部约束。

<a id="references"></a>

## 来源与版本关系

<a id="ref-v67"></a>

1. 项目 V67，*History Scripts, Content Addressing, and Quantum Entanglement in One Ontic State*，固定快照，核读 §§2、6。 [项目原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md)。

<a id="ref-v74"></a>

2. 项目 V74，*Smooth Quantum Histories, Cotangent Dynamics, and Endogenous Motion*，固定快照，核读 §§3–7、12 中本轮所用接口。 [项目原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。

<a id="ref-v78"></a>

3. 项目 V78 综合稿，*Endogenous Relational Quantum Theory: Unified Relational Axioms*，§16。 [项目原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)。

<a id="ref-v80"></a>

4. 项目 V80，*All-Outcome Binary Difference Nonexpansion, Finite Oriented Anchors, and Endogenous Quantum Processes*，核读同一协议与相位提升合同。 [项目原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。

<a id="ref-v84v85"></a>

5. 本对话已交付 v84、v85：正历史回返与实际酉门；内部能量参照、轨道偏转与资源接力。本轮继承其完整执行、独立能量读口与原生菜单的适用范围。

<a id="ref-ashtekar"></a>

6. A. Ashtekar and T. A. Schilling, *Geometrical Formulation of Quantum Mechanics*, [arXiv:gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069)。核读 §II.C.1 的几何可观测量、Killing 场及一点二阶资料对应。

<a id="ref-pastorello"></a>

7. D. Pastorello, *A geometric approach to quantum control in projective Hilbert spaces*, [arXiv:1508.07209v3](https://arxiv.org/abs/1508.07209v3) (2016)。本轮仅使用 §3 Proposition 8、式 (17) 及 Theorem 9 的切向与共同场结构；不使用其余控制可达性定理。

<a id="ref-nielsen"></a>

8. M. A. Nielsen and I. L. Chuang, *Programmable Quantum Gate Arrays*, Phys. Rev. Lett. **79**, 321–324 (1997)， [doi:10.1103/PhysRevLett.79.321](https://doi.org/10.1103/PhysRevLett.79.321)；[作者稿](https://arxiv.org/abs/quant-ph/9703032)。核读确定、精确、全输入编程的程序正交性证明。
