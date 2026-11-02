# 反向内容完备与内部回返

地址即内容、单曲线、终态与酉性的关系

AURIC v83：一个完整候选及其有限量子理论

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮从用户的推理链出发：内容即地址，全部量子态能由一条无分叉曲线串联，
最终态为整体 $\Omega$，首尾切向对称，因而两门互逆且酉。
本文逐段说明其中可保留的定义、需要附加的条件和不成立的蕴含。
内容去重不消去不同续接，任意两态可连接不等于一条光滑曲线覆盖全部态，
可逆性不迫出最终汇点，根态回返与单点切向抵消也不等于全域门互逆。

新的候选定义完整相干续接 $F:S(H)\to S(H)$：
它不放大任意两个内容的相干弦差，且其输出像对共同参考下的反向幅度闭合。
共同复正核、单位强度球面及有限复方向校准沿用已有接口。
不预设 $F$ 线性、满射或可逆。证明先由球面直径迫出
$F(-x)=-F(x)$，再以正反二元关系夹成等距，最后推出唯一复线性酉延拓。
有限同维闭合在从等距到全域逆的一步起作用。
相应球面实等距刚性属于 Ding 2002 年的既有结果；本文给出所需有限情形的完整解析证明，
并将其作为本项目的内部续接候选，而不认领该数学定理的首次发现。

在此基础上，本文发展有共同根的可逆运输结构，精确计算正向、逆族和反向协议的切向，
给出三维球上的端点运输公式，证明终点复位必须把输入差别留在内部记录中，
并说明正历史时钟与可逆态商不能混同。
最后用已有核、效果、记录、组合与时钟条件重构有限维量子规则。
全部数学为解析推导；排版与文件检查不承担数学证明。

## 目录

- [1. 版本承接与本轮的准确问题](#section-1)
- [2. 内容地址消除重复名字 不消除不同续接](#section-2)
- [3. 单曲线 原子门与最终态之间缺少的蕴含](#section-3)
- [4. v83 候选 反向内容完备的二元续接](#section-4)
- [5. 主定理 从反向像闭合推出线性与酉逆](#section-5)
- [6. 逐条删除后的明确二元见证](#section-6)
- [7. 共同根产生可逆运输结构 而非唯一终点](#section-7)
- [8. 首尾切向的准确对称关系](#section-8)
- [9. 二元关系和首尾运输的有限三维提升](#section-9)
- [10. 终止汇点与内部记录](#section-10)
- [11. 有限门与 v82 切向场的互相接续](#section-11)
- [12. 门 测量与可恢复通道的关系](#section-12)
- [13. 从新候选完整接回有限维量子规则](#section-13)
- [14. 用一段白话连起本轮理论](#section-14)
- [15. 本轮结论的范围](#section-15)

<a id="section-1"></a>

## 1. 版本承接与本轮的准确问题

本轮递增为 v83，直接承接本对话 v82。
可核验的项目快照仍为

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`。

本轮恢复并重新读取该快照中与问题直接相关的主文、V67、V73、V74。
实时提交通道未返回可用的新 HEAD，故不声称覆盖未读取的新提交。

主文第 3--4 节已经区分正历史追加、算子可逆和时钟记录，并给出同整体中的互斥续接
[1](#ref-omega)。V67 第 2 节已经给内容地址、执行和未来充分商的不同定义
[2](#ref-v67)。V73 第 5 节已经在有限闭合 Gram 关系下重构酉门及数学逆
[3](#ref-v73)。V74 第 2 节证明有限历史可作平滑插值，但并未声称所有态被同一光滑曲线遍历
[4](#ref-v74)。这些结果本轮继续使用。

| 问题 | 已有接口 | v83 的推进 |
| --- | --- | --- |
| 地址即内容 | 精确内容商、固定未来接口 | 说明去重与不同续接可以并存 |
| 逆与酉 | 有限闭合关系可给数学逆 | 从更弱的反向像闭合和二元不扩张推出酉性 |
| 单条历史 | 有限历史平滑插值 | 区分可连接、实际轨道和全态空间遍历 |
| 首尾切向 | 单曲线仍有生成元自由度 | 给逆族微分及反向控制的准确公式 |
| 整体与终点 | 内部记录保留被局部读口遗漏的差别 | 证明全局终止汇点与可逆差分保持不相容 |

术语约定：$\Omega$ 表示用户所说的全部内部关系结构；
$\omega_0$ 表示某个声明表示中的归一来源。部分旧稿把后者也记为 $\Omega$，
此处只为避免把全体结构和其中一个向量直接代换。
程序、时钟、相干参考和记录均属于整体内部。

**白话图景。**我们继续用同一个整体，不增加外部本体。需要精确的是：
整体、某个根内容、沿途读出和完整历史分别承担什么关系。
只有类型清楚，才可以判断一个回路到底恢复了什么。

<a id="section-2"></a>

## 2. 内容地址消除重复名字 不消除不同续接

<a id="statement-2-1"></a>

#### 定义 2.1（相对于未来接口的内容）

给定合法历史集合及全部声明续接、读口、相干参考和相关记录。
两段历史在所有这些续接中不可区分时，记为 $h\sim k$。
内容地址是该等价类的身份。若相同续接 $w$ 合法，则要求
$h\sim k\Rightarrow hw\sim kw$，使续接在商上良定义。

若时钟或程序记录将来会被读取，就必须包含在此接口中。
若只取当前末态商，则只保留当前末态承担的信息。

<a id="statement-2-2"></a>

#### 命题 2.2（去重不迫使后继唯一）

即使相同内容只有一个地址，同一个内容 $x$ 仍可以有不同合法续接
$F(x)\ne G(x)$。

**证明。**

在量子比特上取 $x=|0\rangle$，$F=I$，$G=H_{\mathrm{Had}}$。
两个后继为 $|0\rangle$ 与 $|+\rangle =(|0\rangle +|1\rangle )/\sqrt2$。
它们可由已有读口区分，所以内容即地址要求它们具有不同地址。
等价节点合并不会把不等价节点合并。

□

给定包括内部控制记录在内的完整实际协议，可以得到一条确定的实际历史。
更换协议时的不同续接与这一确定性并不冲突。
在控制寄存器上可以统一写为
$\sum_c|c\rangle \langle c|\otimes U_c$；控制 $c$ 不同时完整输入已经不同。

<a id="statement-2-3"></a>

#### 命题 2.3（根态回返不足以认证逆门）

存在酉门 $U,G$，使 $GU\omega_0=\omega_0$，但 $GU\ne I$。

**证明。**

取 $\omega_0=|0\rangle$，$U=H_{\mathrm{Had}}$，$G=ZH_{\mathrm{Had}}$。
有 $GU=Z$，所以 $GU|0\rangle =|0\rangle$，但
$GU|+\rangle =|-\rangle \ne|+\rangle$。
根态回返只检验一个输入。

□

<a id="figure-1"></a>

**图 1。**

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[>=Stealth,every node/.style={font=\small},
 state/.style={draw=accent,rounded corners,fill=accent!5,minimum width=24mm,minimum height=9mm}]
\node[state] (o) at (0,1.8) {$\omega_0=\ket0$};
\node[state] (x) at (-2.6,0) {$\ket1$};
\node[state] (p) at (2.6,0) {$\ket+$};
\draw[->,thick,accent,bend left=16] (o) to node[left] {$X$} (x);
\draw[->,thick,accent,bend left=16] (x) to node[right] {$X$} (o);
\draw[->,thick,accent,bend left=16] (o) to node[right] {$H_{\mathrm{Had}}$} (p);
\draw[->,thick,accent,bend left=16] (p) to node[left] {$H_{\mathrm{Had}}$} (o);
\draw[->,thick,warm] (o) edge[loop above] node {$Z\omega_0=\omega_0$} (o);
\end{tikzpicture}
\caption{同一个根、不同续接与根上回路可以同时存在。根上回路 $Z$ 在其他输入上仍可被区分。}
\end{figure}
```

<a id="statement-2-4"></a>

#### 命题 2.4（算子回返不能恢复正历史计数）

历史 $g\bar g$ 与空历史可有相同执行 $I$，但其正长度分别为二和零。
所以长度不能通过该执行商成为良定义函数。

**证明。**

若存在 $\ell=\bar\ell\circ\operatorname{Exec}$，相同执行就必须给相同长度，
与二和零不同矛盾。

□

**白话图景。**地址去重把同一内容的重复名字合成一个节点。
它不把两份不同内容变成同一份，也不把所有通向一个节点的路线都变成同一段历史。
如果时钟记录还在，走出去再回来也仍可读出已经走过的路。

<a id="section-3"></a>

## 3. 单曲线 原子门与最终态之间缺少的蕴含

<a id="statement-3-1"></a>

#### 命题 3.1（任意两态可连接）

有限维空间的任意单位向量 $x,y$，存在酉算符 $U$ 使 $Ux=y$。

**证明。**

分别将 $x,y$ 补成正交单位基，按基一一映射即得。

□

这说明全酉控制类的齐性，不说明任意指定原生菜单都已供应这个门，
也不说明所有态位于同一个固定场的轨道。

<a id="statement-3-2"></a>

#### 定理 3.2（一条普通光滑曲线不能覆盖整个量子比特纯态球）

不存在覆盖 $S^2$ 的 $C^1$ 曲线 $\gamma:\mathbb R \to S^2$。
有限区间或可数分段 $C^1$ 的情形也不可能。

**证明。**

在紧区间 $[a,b]$ 上，导数有界，设 $\left\lVert \gamma'\right\rVert \le L$。
把参数区间等分为 $N$ 段，每段图像包含在以起点为中心、
欧氏弦半径 $r_N=L(b-a)/N$ 的球面帽中。
当 $r_N\le2$，该球面帽面积为 $\pi r_N^2$：
由弦长平方 $r_N^2=2(1-\cos\theta)$ 与帽面积 $2\pi(1-\cos\theta)$ 即得。
因此图像面积外估计至多
$\pi L^2(b-a)^2/N$，令 $N\to\infty$ 得零。
整条实参数曲线是可数个紧区间图像之并，仍为面积零集合，
不能等于面积为 $4\pi$ 的球面。

□

本结论使用普通切向正则性。仅连续的空间填充曲线不在此范围内；
稠密经过也不同于精确经过每一点。
例如 $H=(\hbar\omega/2)\sigma_z$ 的轨道保持 Bloch 球的纬度，
本身已经说明一个自主门不遍历全部纯态。

<a id="statement-3-3"></a>

#### 命题 3.3（连续门类没有内禀的最小非恒等步）

任意有限维非恒等酉门都可继续分解为更小参数的酉门。

**证明。**

写 $U=\sum_j e^{i\theta_j}P_j$，则
$V=\sum_j e^{i\theta_j/2}P_j$ 满足 $V^2=U$。
同样可作任意正整数次根。若 $U\ne I$，至少一个非零谱相位可取主值，
其对应开根仍非恒等，且参数更小。

□

原子门可以由原生语言、实验控制或内部时钟分辨率定义。
它不是从连续酉几何自动产生的不可再分有限变化。
固定有限或可数门字母表的有限字集可数，因而从固定来源有限字精确到达的态至多可数；
不可数的纯态球不能全部由这类有限字精确命名。允许连续门参数或无限极限时需另行说明。

<a id="statement-3-4"></a>

#### 命题 3.4（无分叉不保证最终态）

唯一前驱和唯一后继的可逆系统可以没有最后状态。

**证明。**

取整数上的 $n\mapsto n+1$。量子例子取
$U=\operatorname{diag}(1,e^{i\alpha})$，其中 $\alpha/(2\pi)$ 无理，起点为 $|+\rangle$。
第 $n$ 态为 $(|0\rangle +e^{in\alpha}|1\rangle )/\sqrt2$。
若两个射线相等，第一分量迫使共同相位为一，继而
$(n-m)\alpha\in2\pi\mathbb Z$，所以 $n=m$。
轨道有唯一的正反一步，却没有最终状态。

□

有限确定可逆系统则是置换，每条轨道成为循环；循环也不指定一个本征的最后节点。

**白话图景。**任意两点能连起来，是路线存在；所有点都在同一条实际路上，是另一回事。
连续门可以不断细分。即使每一步后继唯一，历史也可能一直延长，或者绕成循环，
并不会因此自动出现一个最后的内容。

<a id="section-4"></a>

## 4. v83 候选 反向内容完备的二元续接

<a id="statement-4-1"></a>

#### 定义 4.1（完整有限相干截口）

沿用共同复正核及实际相干接口，取有限维复 Hilbert 空间 $H$，
内积对第二变量线性。单位球 $S(H)$ 是本截口的完整声明输入域。
实际完整门是映射 $F:S(H)\to S(H)$，暂不假定线性、满射、可逆或可微。
输入输出为同一个有限载体，所有会返回的记录均已纳入。

单位球约束表示完整归一强度。它不应用于已经丢弃某结果、
再除以成功概率的条件化支路。共同参考使跨输入的相对相位有统一含义。

<a id="statement-4-2"></a>

#### 定义 4.2（有限复方向校准 J）

取复正交单位基 $a_1,\ldots,a_d$，保留已有约束

<a id="equation-J"></a>

$$
F(ia_j)=iF(a_j),\qquad j=1,\ldots,d.\tag{J}
$$

<a id="statement-4-3"></a>

#### 定义 4.3（唯一候选 C83）

完整相干续接满足以下同一组二元相容关系：

<a id="equation-N"></a>

$$
\begin{aligned}
\left\lVert F(x)-F(y)\right\rVert &\le\left\lVert x-y\right\rVert
&& (x,y\in S(H)),
\end{aligned}\tag{N}
$$

<a id="equation-A"></a>

$$
\begin{aligned}
\forall x\in S(H)\quad\exists y\in S(H):\quad
F(y)&=-F(x).
\end{aligned}\tag{A}
$$

N 是二元差分不扩张；A 是输出像对反向内容闭合，
等价于 $-F(S(H))\subseteq F(S(H))$。

A 没有预先指定 $y=-x$，也没有要求输出先覆盖整个单位球。
它只要求每个已输出内容的相干反向版本仍属于同一个完整门的输出像。
全域可逆或满射会供应 A，但 A 比这些前件弱。
相反幅度相对于内部参考定义；它们在无参考的射线商中相同，
因此不能先忘掉参考再原样使用 A 的弦差证明。

**白话图景。**不用先假定最后有一个 $\Omega$ 等着所有内容归并。
先要求完整门没有丢掉自己输出的反向相干版本，
并且同一门不能放大两份内容的差别。下面会证明：
这已经足以把反向输入、完整比较和逆门逐步锁出来。

<a id="section-5"></a>

## 5. 主定理 从反向像闭合推出线性与酉逆

<a id="statement-5-1"></a>

#### 定理 5.1（有限复球面刚性）

实际 $F:S(H)\to S(H)$ 满足 A、N、J，当且仅当存在唯一
$U\in U(H)$ 使 $F(x)=Ux$。
因此 $F$ 自动满射、可逆，并满足

$$
\langle F(x),F(y)\rangle =\langle x,y\rangle ,\qquad F^{-1}=U^*|_{S(H)}.
$$

**证明。**

**第一步，球面直径迫出反向输入。**
固定 $x$，A 给某个 $y$ 使 $F(y)=-F(x)$。由 N，

$$
2=\left\lVert F(x)-F(y)\right\rVert \le\left\lVert x-y\right\rVert \le2.
$$

单位 Hilbert 球面上，$\left\lVert x-y\right\rVert =2$ 当且仅当 $y=-x$：
因为 $\left\lVert x-y\right\rVert ^2=2-2\operatorname{Re} \langle x,y\rangle$，
取等给 $\left\lVert x+y\right\rVert ^2=0$。因此

<a id="equation-5-1"></a>

$$
\boxed{F(-x)=-F(x).}\tag{5.1}
$$

**第二步，正反二元不等式夹成等距。**
将 N 分别用于 $(x,y)$ 与 $(x,-y)$，得到

$$
\left\lVert F(x)-F(y)\right\rVert ^2\le\left\lVert x-y\right\rVert ^2,\qquad
\left\lVert F(x)+F(y)\right\rVert ^2\le\left\lVert x+y\right\rVert ^2.
$$

两边各自求和都等于四，故每一项分别取等。
于是 $F$ 保持全部弦距离，并有

<a id="equation-5-2"></a>

$$
g(F(x),F(y))=g(x,y),\qquad g=\operatorname{Re} \langle \cdot,\cdot\rangle .\tag{5.2}
$$

**第三步，全部实际坐标给实线性。**
取实正交单位基 $b_1,\ldots,b_{2d}=a_1,ia_1,\ldots,a_d,ia_d$。
令 $c_j=F(b_j)$。保实内积说明 $c_j$ 也是实正交单位基。
因此对任意单位 $x$，

$$
F(x)=\sum_j g(c_j,F(x))c_j
=\sum_j g(b_j,x)c_j.
$$

定义 $Ux=\sum_jg(b_j,x)c_j$，即得实际 $F$ 的唯一实线性正交延拓。

**第四步，J 给复线性。**
J 说明 $U(ia_j)=iU(a_j)$，故实线性给 $UJ=JU$。
所以 $U$ 复线性；实内积保持及对 $ix,y$ 的同一等式恢复虚部，
得到 $`U^*U=I`$。有限同维保证满射，故 $`U^{-1}=U^*`$。
反向，任意酉算符的球面限制显然满足 A、N、J。

□

主证明的实球面部分是 Ding 的球面等距延拓结果在本有限情形中的直接证明
[6](#ref-ding)。这里的新候选是将其前件解释为已有内部相干接口上的完整续接约束，
再分析其对地址、根态回返和切向的具体后果。

<a id="statement-5-2"></a>

#### 推论 5.2（内部可回返的充分版本）

若一个完整门已具有全域回程，则其满射性供应 A；
再加 N 与 J，即可推出酉性。
但从酉逆的数学存在到原生逆控制可执行，仍需声明菜单供应。

**证明。**

全域回程使每个 $-F(x)$ 都有前驱，故 A 成立。
其余由主定理。
若原生菜单仅含一个无有限阶酉 $U$ 的非负整数幂，
每个原生门都满足候选，却不存在非负整数 $n$ 使 $U^n=U^{-1}$。

□

<a id="statement-5-3"></a>

#### 说明 5.3（有限闭合的作用）

对较大的输出空间，同一论证给等距嵌入，不必满射。
无限维时，单边移位 $Se_n=e_{n+1}$ 具有反向闭合像、保距离并与 $i$ 相容，
但 $e_0$ 不在像中。因此不能把有限同维步骤默默推广到整个无限载体。

**白话图景。**一个输出能找到反向输出，距离又不能放大，那么产生这个反向输出的输入
就只能是原输入的反面。再同时比较一对内容及其中一个的反面，
两条不等式只能同时取等。所有实际坐标被共同比较锁住，复方向随后锁成酉门。
逆性由此成为结论，不需要一个最终汇点。

<a id="section-6"></a>

## 6. 逐条删除后的明确二元见证

<a id="statement-6-1"></a>

#### 命题 6.1（删去反向像闭合允许内容折叠）

在标准复坐标中定义

$$
F(z)_j=|\operatorname{Re}  z_j|+i|\operatorname{Im}  z_j|.
$$

则 $F:S(H)\to S(H)$ 满足 N 和全部有限 J，却不满足 A，也不酉。

**证明。**

逐实坐标取绝对值保持平方和，并由
$||a|-|b||\le|a-b|$ 得 N。
又 $F(e_j)=e_j$、$F(ie_j)=ie_j$，故 J 成立。
像落在实坐标均非负的球面部分，不含 $-e_1$。
两个明确受影响的内容 $e_1,-e_1$ 都被送到 $e_1$。

□

<a id="statement-6-2"></a>

#### 命题 6.2（删去二元不扩张 可逆也不酉）

设 $a>b>0$，$A=\operatorname{diag}(a,b)$，定义

$$
F_A(x)=\frac{Ax}{\left\lVert Ax\right\rVert }\quad(x\in S(\mathbb C ^2)).
$$

它是光滑、相位协变的球面双射，逆为归一 $A^{-1}$，满足 A 和 J，
却违反 N。

**证明。**

逆公式直接代入成立。取
$x=(e_1+e_2)/\sqrt2$、$y=(-e_1+e_2)/\sqrt2$，
原距离平方为二，而像距离平方为

$$
\left\lVert F_A(x)-F_A(y)\right\rVert ^2
=\frac{4a^2}{a^2+b^2}
=2+\frac{2(a^2-b^2)}{a^2+b^2}>2.
$$

这同时给出发生关系变形的两个元。

□

<a id="statement-6-3"></a>

#### 命题 6.3（删去 J 允许实正交而非复酉）

复共轭 $Cz=\bar z$ 保持球面距离，像反向闭合，却满足 $C(iz)=-iCz$。
因此 A、N 本身不能排除共轭。

**证明。**

逐坐标取共轭不改实距离，并且 $C^2=I$。
但 $C(i e_j)=-i e_j\ne iC(e_j)$，所以它不复线性。

□

若删除单位强度的定义，只在全幅度空间上考虑 $F(x)=c x$，
$0<c<1$，它有对称像、复方向及不扩张性，却缩小强度，当然不酉。
每个反例都是满足其他条件的自洽模型。
候选选择哪些完整续接属于量子相干门；它没有把反例说成逻辑上不存在。

**白话图景。**折叠会把反向内容压成同一个地址；拉伸再归一虽然可逆，却改变两份内容的关系；
共轭保实距离，却翻转共同复方向。每条条件排除的变化都有可指认的内容对。

<a id="section-7"></a>

## 7. 共同根产生可逆运输结构 而非唯一终点

<a id="statement-7-1"></a>

#### 定义 7.1（完整数学门类与运输箭头）

取全部满足候选的映射，由主定理得到 $U(d)$。
把单位内容作为对象，把 $(x,U,y)$、$Ux=y$ 作为运输箭头。
定义

$$
(y,V,z)\circ(x,U,y)=(x,VU,z),\qquad
(x,U,y)^{-1}=(y,U^*,x).
$$

每条箭头可逆，这种结构称为群胚。

若只取特定原生菜单，需先检查其逆控制闭包；
数学允许的群胚不自动等于该菜单的实际执行图。

<a id="statement-7-2"></a>

#### 定理 7.2（端点之间保留稳定子自由度）

固定单位 $x,y$，若 $U_0x=y$，则所有把 $x$ 送到 $y$ 的酉门恰为

$$
\boxed{\{U:Ux=y\}=U_0\operatorname{Stab} (x),\qquad
\operatorname{Stab} (x)=\{S:Sx=x\}\cong U(d-1).}
$$

**证明。**

$Ux=y$ 等价于 $`U_0^*Ux=x`$，故 $U=U_0S$、$S\in\operatorname{Stab} (x)$。
固定 $x$ 的酉算符在 $x^\perp$ 上仍可任意酉作用，反向也成立，
于是得到 $U(d-1)$。射线稳定子则允许在 $\mathbb C  x$ 上另有单位相位，
对应 $U(1)\times U(d-1)$。

□

<a id="statement-7-3"></a>

#### 推论 7.3（回根门的完整形式）

若 $U\omega_0=x$，则所有把 $x$ 送回 $\omega_0$ 的酉门为

$$
\boxed{G=SU^*,\qquad S\in\operatorname{Stab} (\omega_0).}
$$

只有其中 $S=I$ 给出所要求的整个算子逆 $`G=U^*`$。

**证明。**

$GU\omega_0=\omega_0$ 等价于 $GU\in\operatorname{Stab} (\omega_0)$。

□

这把「回到 $\Omega$」中的未定作用精确落在稳定子上。
它是端点关系之上仍须保留的一层关系，而不是额外的外部东西。

<a id="statement-7-4"></a>

#### 命题 7.4（把共同根规定为唯一终对象会消掉全部回路自由度）

若一个群胚具有终对象 $\omega$，即每个对象 $x$ 到 $\omega$ 都有唯一箭头
$u_x$，则任意 $x,y$ 之间也恰有一个箭头，所有稳定子平凡。

**证明。**

任意 $f:x\to y$ 满足 $u_yf=u_x$，所以
$f=u_y^{-1}u_x$。尤其 $x=y$ 时只有恒等。

□

有限量子幅度空间在 $d\ge2$ 时具有非平凡 $U(d-1)$ 稳定子，
所以这种终对象条件并非一般量子作用群胚的性质。
这里的范畴终对象也不同于时间上的最后事件，二者都不能由「存在共同根」推出。

**白话图景。**从根出发能到很多内容，从这些内容也能回根。
但回到同一个根时，门在其他方向上还可能做了不同事情。
这些差别形成稳定子和回路。整体可以把所有路线容纳在一起，
而无须把它们排成唯一一条线或指定一个最终终点。

<a id="section-8"></a>

## 8. 首尾切向的准确对称关系

<a id="statement-8-1"></a>

#### 命题 8.1（路径反向在同一个端点上取负）

给可微路径 $\gamma:[0,T]\to M$，定义
$\bar\gamma(t)=\gamma(T-t)$。则

$$
\boxed{\bar\gamma'(0)=-\gamma'(T),\qquad
\bar\gamma'(T)=-\gamma'(0).}
$$

**证明。**

对复合函数直接求导。

□

两个负号分别比较同一端点上的正反速度。
通常 $\gamma'(0)$ 与 $\gamma'(T)$ 属于不同切空间，
不能未经运输就宣称它们相反。
若 $\gamma$ 本身是一条接缝光滑的周期曲线，则正向首尾满足
$\gamma'(T)=\gamma'(0)$。仅有端点相等还不保证接缝导数相等。

<a id="statement-8-2"></a>

#### 定理 8.2（逆族的切向包含微分运输）

设 $F_t$ 是可微微分同胚族，实际 Euler 场为
$v_t=(\partial_tF_t)\circ F_t^{-1}$。
令 $G_t=F_t^{-1}$，则

<a id="equation-8-1"></a>

$$
\boxed{\partial_tG_t(y)=-D(F_t^{-1})_y\,v_t(y).}\tag{8.1}
$$

**证明。**

对 $F_t(G_t(y))=y$ 求导，得
$v_t(y)+D(F_t)_{G_t(y)}\,\partial_tG_t(y)=0$。
左乘逆微分即得。

□

若 $F_t=U(t)$，$\dot U(t)=K(t)U(t)$，则逆族 $`W(t)=U(t)^*`$ 的实际生成元为

<a id="equation-8-2"></a>

$$
\boxed{\widetilde K(t)=\dot W(t)W(t)^*
=-U(t)^*K(t)U(t).}\tag{8.2}
$$

一般时变场不能省去这个共轭。

<a id="statement-8-3"></a>

#### 定理 8.3（倒放整段门历史）

设 $U(0)=I$，定义从终态起步的反向协议

$$
R(s)=U(T-s)U(T)^*,\qquad0\le s\le T.
$$

则

$$
R(0)=I,\quad R(T)=U(T)^*,\quad
\boxed{\dot R(s)=-K(T-s)R(s).}
$$

**证明。**

直接微分 $U(T-s)$，用 $\dot U(t)=K(t)U(t)$。
作用于终态 $U(T)x$ 后，$R(s)U(T)x=U(T-s)x$，
恰好沿原路径反向走。

□

这与逐时刻取 $U(t)^{-1}$ 是两条不同的门曲线。
数学上的逆控制也不等同于物理学中另行定义的反酉时间反演对称性。

<a id="statement-8-4"></a>

#### 命题 8.4（单点反向箭头不认证整个逆门）

取 $\psi=|0\rangle$，

$$
K=i\sigma_x,\qquad
L=-i\sigma_x+i\lambda|1\rangle \langle 1|,\quad\lambda\in\mathbb R \setminus\{0\}.
$$

则 $L\psi=-K\psi$，但两族 $e^{tL}$、$e^{tK}$ 不在零点邻域互为完整逆族。

**证明。**

最后一项消去 $\psi$，故单点切向相反。
若两族互逆，微分矩阵等式 $e^{tL}e^{tK}=I$ 于零点，就必须有 $L=-K$，
与定义矛盾。
更具体地，二阶展开在该点给

$$
e^{tL}e^{tK}\psi
=\psi-\frac{\lambda t^2}{2}|1\rangle +O(t^3).
$$

一阶抵消并没有消去二阶偏离。

□

**白话图景。**倒着沿一条路走，在同一个位置，箭头确实反过来。
绕同一圈正向回到起点，首尾箭头则同向。
眼前两个箭头抵消，只说明眼前的一阶抵消；
完整逆门还必须在所有声明内容上恢复作用。

<a id="section-9"></a>

## 9. 二元关系和首尾运输的有限三维提升

### 9.1 二元比较球

对两个单位内容 $x,y$，令 $z=\langle x,y\rangle$，采用转置 Gram 的坐标约定

$$
R_{xy}=\frac12
\begin{pmatrix}1&\bar z\\z&1\end{pmatrix}
=\frac12(I+\mathbf r\cdot\boldsymbol\sigma),
\qquad
\mathbf r=(\operatorname{Re}  z,\operatorname{Im}  z,0).
$$

正核给 $|z|\le1$，因此 $\left\lVert \mathbf r\right\rVert \le1$。
候选 N 起初只约束
$2-2\operatorname{Re}  z' \le 2-2\operatorname{Re}  z$。
A 迫出真正的反向输入后，$(x,-y)$ 的同一约束给反向不等式，
所以实坐标被固定；J 及实际线性再固定虚坐标。
因此整个二元关系图保持。
许多这样的局部三维图仍须来自同一个共同正核，不能各自任意拼接。

### 9.2 当前态与当前切向的球图

对归一态 $\psi$，水平切向 $\xi\perp\psi$ 落在
$\operatorname{span} _{\mathbb C }\{\psi,\xi\}$ 中。若 $\xi=zu$、$u\perp\psi$ 单位，
则该二维载体上的 Bloch 坐标满足

$$
\mathbf r_\psi=(0,0,1),\qquad
\dot{\mathbf r}_\psi=(2\operatorname{Re}  z,2\operatorname{Im}  z,0).
$$

这是即时一阶的三维表示，不把全部高维态空间压成同一个三维球。

<a id="statement-9-1"></a>

#### 定理 9.1（球面端点切向的运输）

给 $\mathbf p,\mathbf q\in S^2$，非重合、非对跖，
记 $c=\mathbf p\cdot\mathbf q=\cos\theta$、$s=\sin\theta>0$。
从 $\mathbf p$ 到 $\mathbf q$ 的最短大圆初始切向为

$$
\mathbf u_0=\frac{\mathbf q-c\mathbf p}{s},
$$

正向抵达的切向为

$$
\mathbf u_T=\frac{c\mathbf q-\mathbf p}{s}.
$$

反向从终点出发的切向恰为

$$
\boxed{\mathbf u_{\mathrm{rev}}=
\frac{\mathbf p-c\mathbf q}{s}=-\mathbf u_T.}
$$

**证明。**

取弧长参数
$\gamma(a)=\cos a\,\mathbf p+\sin a\,\mathbf u_0$，
$0\le a\le\theta$。
求导并代入 $a=\theta$，得
$-s\mathbf p+c(\mathbf q-c\mathbf p)/s=(c\mathbf q-\mathbf p)/s$。
反向路径导数取负即得。

□

对跖点的最短弧不唯一，须另给历史切向；相同点则不能由端点数据指定非零圈数和路径。

### 9.3 圆和椭圆的既有历史条件

给起点 $\mathbf p$、历史单位切向 $\mathbf u$、目标 $\mathbf q\ne\mathbf p$，
令 $\mathbf b=\mathbf p\times\mathbf u$。
在明确的平面截球圆类中，圆平面由

$$
(\mathbf b+\kappa\mathbf p)\cdot\mathbf r=\kappa,
\qquad
\kappa=\frac{\mathbf b\cdot\mathbf q}{1-\mathbf p\cdot\mathbf q}
$$

确定。写 $\mathbf r=X\mathbf p+Y\mathbf u+Z\mathbf b$，
代入 $Z=\kappa(1-X)$ 得

$$
X^2+Y^2+\kappa^2(1-X)^2=1.
$$

所以球面圆在历史平面上的投影是圆或椭圆。
这是 v78--v82 的历史弧消费者；光滑性本身不强迫实际轨迹属于圆类。

**白话图景。**二元关系先被放进一个小关系球，正反比较锁住它的位置。
看一条球面弧时，起点和终点的箭头要沿弧运输后比较。
倒着走的箭头在终点取负；首尾是否同向、是否闭合、有没有椭圆投影，
各自由路径、方向和读出平面决定。

<a id="section-10"></a>

## 10. 终止汇点与内部记录

<a id="statement-10-1"></a>

#### 定理 10.1（共同可逆门没有多输入终止汇点）

若同一个单射 $T:X\to X$ 将所有输入送到 $\omega$，
则 $X$ 至多只有一个元素。
若 $T(\omega)=\omega$，任何其他输入都不能经有限次 $T$ 首次到达 $\omega$。

**证明。**

第一句由 $T(x)=T(y)$ 及单射性即得。
第二句由 $T^n(x)=\omega=T^n(\omega)$ 及 $T^n$ 单射得 $x=\omega$。

□

<a id="statement-10-2"></a>

#### 推论 10.2（共同酉演化不能把不同完整内容渐近合成同一点）

若 $x\ne y$，共同酉演化始终满足
$\left\lVert U(t)x-U(t)y\right\rVert =\left\lVert x-y\right\rVert >0$，
故两者不可能同时在范数意义趋向同一个单位向量。
若讨论射线，须改要求 $[x]\ne[y]$；此时
$d_{\mathrm{FS}}([U(t)x],[U(t)y])=d_{\mathrm{FS}}([x],[y])>0$，
故二者不能同时趋向同一射线。

<a id="statement-10-3"></a>

#### 命题 10.3（自主平衡态不能被非平衡轨迹有限时间撞入）

设自主场局部 Lipschitz 且 $v(\omega)=0$。
若某解在有限 $T$ 满足 $x(T)=\omega$，则它在共同连通定义区间上恒为 $\omega$。

**证明。**

常值解与该解在 $T$ 有相同初值。局部解唯一性向前、向后适用，
故两解在共同连通定义区间上相同。

□

若时变控制在到达指定目标后关掉，某条轨迹当然可以停止；
那是控制历史中的选择，不是所有完整态的本征最终汇点。

<a id="statement-10-4"></a>

#### 定理 10.4（局部统一终点必须由内部记录保留差别）

设完整复线性等距算符 $V:H\to H_S\otimes H_R$ 对所有单位 $\psi$ 满足

$$
V\psi=\omega_0\otimes\eta_\psi,\qquad\left\lVert \omega_0\right\rVert =1.
$$

则

$$
\boxed{\langle \eta_\psi,\eta_\phi\rangle =\langle \psi,\phi\rangle .}
$$

记录载体中存在输入空间的等距副本，特别地 $\dim H_R\ge\dim H$。

**证明。**

对两输出取内积，使用 $V$ 等距及 $\omega_0$ 归一即得。
任取输入正交单位基，其记录像也正交，所以维数结论成立。
线性记录映射可直接定义为
$(\langle \omega_0|\otimes I)V$。

□

SWAP 给最简单实现：

$$
\psi_S\otimes\omega_{0,R}
\longmapsto
\omega_{0,S}\otimes\psi_R.
$$

局部读口都看到 $\omega_0$，完整内容仍依赖输入。

<a id="statement-10-5"></a>

#### 命题 10.5（严格增长时钟不能同时成为可逆态的状态函数）

设至少存在一条连接不同内容的允许门 $x\to y$，$x\ne y$，其逆门也允许。
若每条此类允许门都要求目标的 $\tau$ 严格大于来源，
则不存在这样的 $\tau:X\to\mathbb R$。

**证明。**

逆门同时要求 $\tau(x)>\tau(y)$，矛盾。

□

时钟可以定义在正历史及其记录上。若只恢复局部态，时钟记录可以继续增长；
若全部相关记录也恢复到原来，就不能在同一个完整内容中还读出不同的历史序号。
同样，可达性在可逆分量上形成双向关系；若把它强行当作反对称偏序，
则所有互达对象被商成同一类，态间区分随之消失。

**白话图景。**局部内容可以回到共同根，输入差别则搬到内部记录。
如果要求整个内容都变成同一份，又要整个过程可逆，就相互冲突。
整体 $\Omega$ 可以容纳所有这些回返，而不必成为抹掉全部差别的最后一个点。

<a id="section-11"></a>

## 11. 有限门与 v82 切向场的互相接续

<a id="statement-11-1"></a>

#### 定理 11.1（v83 到 v82）

设 $F_t$ 满足本轮候选，且其有限基锚输出随 $t$ 可微。
则实际映射为可微酉族 $U(t)$。定义

$$
K(t)=\dot U(t)U(t)^*.
$$

有 $`K(t)^*=-K(t)`$，并且当前实际场为 $v_t(x)=K(t)x$。

**证明。**

主定理把矩阵列写成有限锚输出，所以矩阵可微。
微分 $`U(t)U(t)^*=I`$ 得 $`K+K^*=0`$。
对当前态 $x=U(t)x_0$，速度为
$\dot U(t)x_0=K(t)x$。

□

因此 v82 的球面切向、共同复方向及
$2\operatorname{Re} \langle x-y,v_t(x)-v_t(y)\rangle =0$ 全部成立。
定义 $H(t)=i\hbar K(t)$，便得到

$$
\boxed{i\hbar\dot\psi=H(t)\psi,\qquad H(t)^*=H(t).}
$$

时间单位和 $\hbar$ 的物理标定仍由内部时钟与既有读出接口供应。

<a id="statement-11-2"></a>

#### 定理 11.2（v82 到 v83）

v82 的实际反自伴场在所需时间正则性下积分为酉传播子，
其球面限制满足本轮 A、N、J。
任意一个有限 v83 门也至少存在某条平滑切向实现。

**证明。**

反自伴场积分后保持内积，故保距离、满射且保复方向，立即满足候选。
反向，对有限酉 $U=\sum_r e^{i\theta_r}P_r$，
取 $K=i\sum_r\theta_rP_r$，则 $U=e^K$，
曲线 $e^{tK}$ 给平滑实现。

□

对数分支和中间历史并不唯一，也不自动属于某个受限原生菜单。
有限门、无穷小门与实际历史由此接通，但仍保留各自的身份。

**白话图景。**上一轮从箭头推出共同生成元，这一轮从有限续接推出共同酉门。
可微时，两者互相接得上。某个有限门确实可以沿一条平滑曲线实现，
但这个事实并不把所有内容和所有历史都变成同一条曲线。

<a id="section-12"></a>

## 12. 门 测量与可恢复通道的关系

### 12.1 同一完整门给效果和后继

在内部记录准备 $|0\rangle$ 上，完整酉门 $U$ 给分支

$$
M_e=(I\otimes\langle e|)U(I\otimes|0\rangle ).
$$

记录基完备及酉性给

$$
\sum_eM_e^*M_e=I,\qquad E_e=M_e^*M_e.
$$

在此前同根强度与概率的标定下，

$$
p(e\mid\psi)=\left\lVert M_e\psi\right\rVert ^2=\langle \psi,E_e\psi\rangle .
$$

非零概率时的条件态为 $M_e\psi/\left\lVert M_e\psi\right\rVert$。
零概率不指定归一条件态。多个不读取的记录标签给
$`\mathcal I_e(\rho)=\sum_\alpha M_{e\alpha}\rho M_{e\alpha}^*`$。
这接回有限量子仪器的标准结构 [8](#ref-watrous)。

单独的酉门是效果为 $I$、后继为 $`U\rho U^*`$ 的单结果仪器。
效果 $I$ 本身不能保留所有不同门的后继差别。
测量作为取得可区分记录的过程，仍须实际产生这些记录。

<a id="statement-12-1"></a>

#### 定理 12.1（地址身份不等于可无扰读出的经典标签）

设完整复线性等距作用在每个未知纯态上给

$$
V\psi=U\psi\otimes r_\psi,
$$

其中同一个 $U$ 酉，$\left\lVert r_\psi\right\rVert =1$。
若这一式对全部单位态成立，则 $r_\psi$ 与输入无关。

**证明。**

保内积给

$$
\langle \psi,\phi\rangle
=\langle \psi,\phi\rangle \langle r_\psi,r_\phi\rangle .
$$

若 $\langle \psi,\phi\rangle \ne0$，则记录内积为一，故记录向量相同。
若两态正交，以 $(\psi+\phi)/\sqrt2$ 为桥，它与两者的内积都非零，
所以两记录仍相同。比例向量的情形也由同一式得到。

□

所以把完整内容当作地址，并不自动供应一个在所有未知纯态上无扰读取该地址的经典读口。
需要区分内容身份与实际可读取的记录。
若允许扰动或与记录纠缠，完整测量仍可成立。

### 12.2 同维物理回程的通道版本

下面是一个消费者，不是主定理的隐藏前件。
若由独立的静态全效果响应、混合相容及任意内部参考正性已经供应
线性、完全正、迹保持映射，则可以在通道层重述回返。
不能先以酉扩张定义可用操作，再把以下结论当作从零证明酉性。

<a id="statement-12-2"></a>

#### 定理 12.2（同维 CPTP 左逆迫出酉通道）

在同一有限维 $H$ 上，设 $\Phi,\Psi$ 均完全正、迹保持，
且 $\Psi\Phi=\mathrm{id}$。
则存在酉 $U$ 使

$$
\boxed{\Phi(X)=UXU^*.}
$$

**证明。**

写有限 Kraus 表示
$`\Phi(X)=\sum_iA_iXA_i^*`$、
$`\Psi(X)=\sum_jB_jXB_j^*`$。
对每个纯态，合成输出仍是同一秩一正算符；
正项不能相互抵消，因此每个 $B_jA_i x$ 必与 $x$ 共线。
一个线性算符保留每条向量直线，比较两独立向量及其和即知它是标量恒等。
故 $B_jA_i=c_{ji}I$。

至少某个 $c_{j_0i_0}\ne0$。同维方阵使 $B_{j_0}$ 与 $A_{i_0}$ 可逆，
所以
$A_k=(c_{j_0k}/c_{j_0i_0})A_{i_0}$。
于是 $`\Phi(X)=sA_{i_0}XA_{i_0}^*`$，其中 $s>0$。
迹保持给 $`sA_{i_0}^*A_{i_0}=I`$。
取 $U=\sqrt{s}A_{i_0}$，有限同维保证其酉。

□

这是已有可恢复量子操作理论的同维情形 [7](#ref-nayaksen)。
Kraus 表示可从完全正性的有限 Choi 矩阵谱分解得到，
不必将酉扩张作为该表示的证明前件。

删去完全正时，转置 $T(X)=X^{\mathsf T}$ 是正、迹保持且 $T^2=I$，
但非酉共轭。取
$|\Phi\rangle =(|00\rangle +|11\rangle )/\sqrt2$，
则 $(T\otimes\mathrm{id})(|\Phi\rangle \langle \Phi|)$ 是交换算符的一半，
在反对称态 $(|01\rangle -|10\rangle )/\sqrt2$ 上期望为 $-1/2$。
这正好把失败定位到系统与一个内部参考之间。

删去迹保持，可逆滤波 $`X\mapsto AXA^*`$ 及其逆均完全正，但 $A$ 不必酉。
只要求线性逆也不够：退极化
$\Phi_\lambda(\rho)=\lambda\rho+(1-\lambda)I/d$，
$0<\lambda<1$，在线性空间上可逆，但其逆将部分纯态送出正锥。
跨维时，等距嵌入可有完全正迹保持左逆，却不是原同载体上的酉自映射。

**白话图景。**有内部回程的完整门保住全部可比较内容。
如果只看局部、忽略记录或按结果归一，便会得到不同形式的操作。
通道层的物理可恢复性也能锁成酉，但前提必须同时约束它与所有内部参考的关系，
不能只看一个根或一个孤立输入。

<a id="section-13"></a>

## 13. 从新候选完整接回有限维量子规则

本节将已有接口和本轮增量逐项列清，避免把已供应结构重新当作空白，
也避免把它们全部藏进「内生」一词。

<a id="statement-13-1"></a>

#### 定理 13.1（共同正核的有限 Hilbert 表示）

给内容集合上的复核 $k$，假定每个有限 Gram 矩阵正半定。
在形式有限和上定义

$$
\left\langle\sum_ic_i\delta_{x_i},
\sum_jd_j\delta_{y_j}\right\rangle
=\sum_{i,j}\bar c_i k(x_i,y_j)d_j.
$$

商去零范数元后得到内积空间；若截口秩有限，得到有限维复 Hilbert 空间，
且 $k(x,y)=\langle \iota(x),\iota(y)\rangle$。

**证明。**

正性给半内积，复参数二次式的非负性给 Cauchy--Schwarz。
零范数元因而与全部向量正交，商内积良定义。
有限秩给有限维，有限维自动完备。

□

实际相干组合的可用性仍由声明的操作闭包供应；
表示空间中某个向量的数学存在不自动成为原生准备协议。

<a id="statement-13-2"></a>

#### 定理 13.2（全效果正响应的密度表示）

在全部效果 $0\le E\le I$ 上，设同一个响应 $f$ 非负、$f(I)=1$，
并对合法部分和可加。则存在唯一
$\rho\ge0$、$\operatorname{Tr} \rho=1$ 使 $f(E)=\operatorname{Tr} (\rho E)$。

**证明。**

有限可加给有理齐次，正性给单调性。
用有理数上下夹住 $t\in[0,1]$，得到 $f(tE)=tf(E)$，
无需预设连续。
对 $A\ge0$ 选整数 $n\ge\left\lVert A\right\rVert$，
定义 $\ell(A)=nf(A/n)$。共同细分说明与 $n$ 无关；
共同大分母给正锥可加性和实齐次。
按 $X=A-B$ 延拓到自伴空间；若另一分解 $A'-B'$ 相同，
则 $A+B'=A'+B$ 保证定义无关。
有限维迹配对给唯一自伴 $\rho$；
一维投影上的非负性给 $\rho\ge0$，归一性给迹一。

□

前件是全效果延拓及同效果相容，不能以有限菜单数值表替代。

<a id="statement-13-3"></a>

#### 定理 13.3（乘积核与张成闭包给张量积）

若独立准备满足

$$
k_{AB}((x,y),(x',y'))=k_A(x,x')k_B(y,y'),
$$

且乘积准备张成所声明的复合空间，则
$H_{AB}\cong H_A\otimes H_B$。

**证明。**

将 $\iota_{AB}(x,y)$ 送到 $\iota_A(x)\otimes\iota_B(y)$。
乘积核等式保证线性张成上的半内积相同，
故商去零元后得到等距。张成条件保证覆盖整个声明复合空间。

□

实际局部端口若为 $A\otimes I$ 与 $I\otimes B$，则相互对易。
对第二端的迹保持操作忽略结果，
由 $`\sum_eM_e^*M_e=I`$ 得第一端全部效果响应不变。
这供应相应局部操作的无信号性。

<a id="statement-13-4"></a>

#### 定理 13.4（投影效果与本征子空间无扰给通常更新）

设同空间结果操作有 Kraus 算符 $A_\alpha$，
$`\sum_\alpha A_\alpha^*A_\alpha=P`$ 为投影。
若每个 $\operatorname{ran}  P$ 中的单位纯态被该结果操作固定，则
$\mathcal I_P(\rho)=P\rho P$。

**证明。**

对 $\ker P$ 中向量，所有 $A_\alpha$ 的范数平方之和为零，
故 $A_\alpha=A_\alpha P$。
固定秩一输出迫使每个 $A_\alpha\psi$ 与 $\psi$ 共线；
比较子空间内向量及其和，得到 $A_\alpha=c_\alpha P$。
当 $P\ne0$，效果等式给 $\sum|c_\alpha|^2=1$；
当 $P=0$，全部 Kraus 算符为零。结论均成立。

□

效果 $P$ 单独仍允许范围内附加酉转动。
非零结果概率时再归一，才得 $P\rho P/\operatorname{Tr} (\rho P)$。

<a id="statement-13-5"></a>

#### 命题 13.5（不确定性是两个中心化方向的正关系）

令 $u=(A-\langle A\rangle)\psi$、
$w=(B-\langle B\rangle)\psi$，其中 $A,B$ 自伴、$\psi$ 归一。
则

$$
(\Delta A)^2(\Delta B)^2
\ge \operatorname{Cov}(A,B)^2+
\frac14|\langle[A,B]\rangle|^2.
$$

**证明。**

二元 Gram 正性给
$\left\lVert u\right\rVert ^2\left\lVert w\right\rVert ^2\ge|\langle u,w\rangle |^2$。
其实部为协方差，虚部为 $\langle[A,B]\rangle/(2i)$，
取模平方即得。

□

如需将两方向再归一为一个三维球，应先用内部尺度消去不同物理量纲。
零方差边界保留；本征态可以使某个读口完全确定。

| 标准量子规则 | 内部关系来源 | 明确保留的条件 |
| --- | --- | --- |
| 复 Hilbert 空间 | 共同复正核与零范数商 | 当前有限秩截口 |
| 叠加与射线 | 相干组合及整体相位商 | 会返回的内部参考不能提前丢弃 |
| 线性酉门 | 本轮 A、N、J 的球面刚性 | 完整单位强度、有限同载体 |
| 逆门 | 酉延拓的伴随 | 数学存在与原生控制供应分别说明 |
| 薛定谔方程 | 可微门族的反自伴切向 | 时间正则性、时钟与单位标定 |
| 效果及 Born 规则 | 完整门的记录分支、同根强度标定 | 实际 ready 记录与读口 |
| 混态 | 全效果正归一部分可加响应 | 同效果相容及全效果延拓 |
| 完全正仪器 | 内部记录粗粒化及参考相容 | 完整输出类型与分支域 |
| 投影更新 | 投影效果和范围内纯态无扰 | 非零概率条件化 |
| 张量积与纠缠 | 乘积核、张成和整体相干组合 | 实际局部端口与可用性 |
| 不确定性 | 二元中心化 Gram 正性 | 同一状态与单位尺度 |
| 周期与回路 | 特定门谱和相位闭合 | 多频率须满足共同回返条件 |

<a id="statement-13-6"></a>

#### 定理 13.6（有限过程的条件重构）

在上述共同核、相干组合、全效果、记录、组合和时钟接口下，
候选 C83 给标准有限维量子态、效果、酉门和完全正仪器的表示。
反向，任意有限维标准量子系统可供应这些接口并满足 C83。
若准备和控制菜单取相应的全部数学允许对象，得到完整的有限维量子过程类；
受限菜单则给其中的子理论。

**证明。**

核表示给共同空间；主定理给实际完整酉门；
记录分支给 $M_e$、效果、概率和完全正操作；
正响应表示给一般态，乘积核给复合。
反向标准有限系统直接满足每条等式。
对任意有限仪器 Kraus 族 $\{M_{e\alpha}\}$，
映射 $x\mapsto\bigoplus_{e,\alpha}M_{e\alpha}x$ 等距，
在准备子空间与输出子空间之间补齐正交基，可在更大的固定内部载体上延拓成酉门。
任意效果 $E$ 可用 $\sqrt E,\sqrt{I-E}$ 两分支实现；
任意密度态可由其谱分解准备，或由内部纯化后限制读出得到。
这些存在构造在完整控制类中实现全部有限过程；
它们不扩大一个事先受限的原生菜单。

□

**白话图景。**共同正核给关系的坐标，完整续接候选锁成酉门，
记录把门接成效果和条件后继，全效果响应给混态，
乘积比较给复合系统。已有量子规则可以沿这条链逐项出现，
每一步都能指出用了哪一个内部接口。

<a id="section-14"></a>

## 14. 用一段白话连起本轮理论

整个 $\Omega$ 容纳所有内容及其内部续接。内容即地址，使相同内容只有一个身份，
也使不同内容保留不同身份；它并不把所有不同续接都抹成一条路。
固定一个完整控制历史，就得到一条实际曲线。
完整相干门若能产生一份内容，也保有其相对于共同参考的反向版本；
再要求它不放大任意两份内容的差别，球面的正反关系就把两端比较锁成等式。
于是实际门必须是同一个复线性酉作用，逆门在有限闭合载体上随之存在。
回到共同根，只说明当前根内容恢复；其他方向上的作用由稳定子和回路继续保留。
反向走同一条曲线时，箭头在同一个端点反过来；
沿原方向绕一圈回来，首尾箭头则相接。
若局部内容最后统一成根态，过去的差别会进入内部记录；
若连记录也全部恢复，就不会同时留下一个不同的「最后一次」标签。
量子态、门、测量、时钟和回路都可以在这个整体里定义，
而酉性来自完整关系可保留的相容结构，不需要先假定全体态有一个终止汇点。

<a id="section-15"></a>

## 15. 本轮结论的范围

本轮给出一个完整的新候选及其有限量子重构用途，
没有把「一切属于 $\Omega$」这一成员关系单独当作推出全部物理规律的证明。
共同复正核、复方向、读出标定和控制域是沿用的明确接口，
新候选约束它们上的实际续接。
球面刚性、可恢复通道和量子仪器的标准数学归属分别列于文献。
整体关系结构、共同来源、给定实际历史和最终汇点的不同定义贯穿全文。

全部证明采用解析推导，没有进行数值搜索、数学程序验证或模拟。
本轮没有修改远端仓库，也没有认证未读取的新增提交。
无限维全域逆、具体相互作用和经验常数并非本有限重构定理的自动结论。

## 来源与版本关系

<a id="ref-omega"></a>

**[1]**
trureturing，[整体静态相容纤维理论固定原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，第 3--4 节。
本轮核读配置、严格增长时钟、互斥续接及执行商遗漏历史计数的正文。

<a id="ref-v67"></a>

**[2]**
trureturing，[V67 历史脚本、内容寻址与唯一来源固定原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md)，第 2 节。

<a id="ref-v73"></a>

**[3]**
trureturing，[V73 最小闭合关系体与酉重构固定原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_PREFIX_STATES_MINIMAL_CLOSED_RELATIONAL_BODY_AND_UNITARY_RECONSTRUCTION_V73.md)，定义 5.1、定理 5.2、推论 5.3。

<a id="ref-v74"></a>

**[4]**
trureturing，[V74 平滑历史与内生运动固定原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)，第 2 节。

<a id="ref-v82"></a>

**[5]**
本对话连续研究，[v82 切向二元相容与内生量子门理论](https://chatgpt.com/space/page_3e3918be4eec8191aef3239016dbff9c)，2026 年 11 月 2 日。

<a id="ref-ding"></a>

**[6]**
Guanggui Ding.
*The 1-Lipschitz mapping between the unit spheres of two Hilbert spaces
can be extended to a real linear isometry of the whole space*.
Science in China Series A: Mathematics, 45(4), 479--483, 2002.
[DOI: 10.1007/BF02872336](https://doi.org/10.1007/BF02872336).
出版者摘要明确给反向像闭合与非扩张的前件；本文独立写出所需有限情形的全部证明。

<a id="ref-nayaksen"></a>

**[7]**
Ashwin Nayak and Pranab Sen.
*Invertible Quantum Operations and Perfect Encryption of Quantum States*.
Quantum Information and Computation, 7(1--2), 103--110, 2007.
[arXiv:quant-ph/0605041](https://arxiv.org/abs/quant-ph/0605041)，定理 2.1 及同维讨论。

<a id="ref-watrous"></a>

**[8]**
John Watrous. *The Theory of Quantum Information*.
[第 2 章作者公开稿](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，
态、通道、Kraus 表示和测量仪器。

## 源稿前言与排版元数据

```latex
% !TEX program = xelatex
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace,tikz}
\usetikzlibrary{arrows.meta,positioning,calc}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\definecolor{warm}{HTML}{B75B39}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v83：反向内容完备、内部回返与量子起源}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v83 / 内容、回返与酉性}
\fancyhead[R]{\small 定义、定理、证明与白话}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\figurename}{图}
\renewcommand{\refname}{来源与版本关系}
\renewcommand{\proofname}{证明}
\numberwithin{equation}{section}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{lemma}[definition]{引理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Rea}{\operatorname{Re}}
\newcommand{\Ima}{\operatorname{Im}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\Stab}{\operatorname{Stab}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\Exec}{\operatorname{Exec}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/#1}{#2}}
\title{\color{ink}\bfseries 反向内容完备与内部回返\\[6pt]
\large 地址即内容、单曲线、终态与酉性的关系\\[4pt]
AURIC v83：一个完整候选及其有限量子理论}
\author{项目连续研究稿}
\date{2026 年 11 月 2 日}
```

```latex
\begin{document}
\maketitle
\clearpage
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{center}\small\texttt{c63ab162315fddd0801cbe9f47dbf3eda6e13360}。\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.24\textwidth}XX@{}}
\toprule
\\
\midrule
\\
\\
\\
\\
\\
\bottomrule
\end{tabularx}
\end{center}
\begin{center}\small
\begin{longtable}{@{}p{.23\textwidth}p{.36\textwidth}p{.34\textwidth}@{}}
\toprule
\\
\midrule
\endhead
\\
\\
\\
\\
\\
\\
\\
\\
\\
\\
\\
\\
\bottomrule
\end{longtable}
\end{center}
\begin{thebibliography}{99}
\end{thebibliography}
\end{document}
```
