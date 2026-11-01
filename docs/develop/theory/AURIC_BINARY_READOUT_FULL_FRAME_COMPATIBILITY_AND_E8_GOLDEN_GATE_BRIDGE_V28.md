<a id="auric-v28"></a>

# AURIC：二元读出、全框架相融与 E8 黄金门桥梁

**相对门序列、三轴几何、关系元数与条件量子重构**

**定义、定理与纸面证明**

**v28.0 · 2026 年 10 月 30 日 · Asia/Singapore**

> **转换说明（编者）。** 本文完整转写原作者提供的 v28.0 XeLaTeX 稿件。作者关于固定快照、来源核读、历史统计、纸面结果及项目进展的陈述仍归属于原作者，不构成本次转换的新认证。字体、页眉、页码、分页和目录排版由 Markdown 替代；数学宏按 TeX 参数规则展开为独立表达。陈述沿用各节共享计数器，小节保留 11.1–11.3；仅保留源稿显式公式标签 (F)、(E)，全部证明保留可见终止符。原始外部自引链接及先行研究归属照录。

<a id="sec-abstract"></a>

## 摘要

本文把“观察者与基底都是门序列，读出是相对关系”的直觉写成相对门公式，
并区分二结果概率、二态编码、三维 Bloch 坐标和测后状态。
两复振幅经归一化与共同相位取商得到 $\mathbb{C} P^1\simeq S^2$；
一组三轴上的两个均值加纯度一般仍有符号歧义。
但若把平方和约束加强为所有旋转框架上的同一连续、各向同性响应相容，
则可直接推出 $p=(1+\cos\theta)/2$。
更一般地，全效果的正性、归一化与可加相容给出密度算子形式。
本文给出有限候选射线来自同一 qubit 的 Gram 充要判据，
并证明 AURIC 五模式的三个原始占据读口不能直接等同于三个尖锐 Pauli 轴。

多元关系可经辅助见证二元化，但见证携带联合信息；
仅用布尔二元约束，即使加入布尔辅助变量，仍不能表达三元奇偶关系。
任意有限 POVM 可递归二叉化，原系统维数与测量权限却仍须保留。
在另一会话的 $A_4\oplus A_4$ 严格积分扩张模型中，
本文显式构造跨分级根 $SU(2)$ 双态码，证明 E8 五相位在该码上给出黄金门的平方，
而完整黄金门还需要平方根分支与相干混合。
八个简单根各供应一对黄金门时，十六个固定门的闭包为紧 E8。
该结果不把 E8 与项目原生 $PU(13)$ 或 $SU(248)$ 识别。

最后结合仓库新增的平方根稳定性锐性、有限核对固定间隙与十八模式上下文赋值奇偶定理，
明确全域相容与有限记录之间的逻辑差别。
本文得到一套可继续形式化的条件理论；复效果空间、复合规则、读口资源和积分扩张均被明列，
不把几何图像或有限标定当作这些前提的证明。

**方法与结论身份。**
数学部分全部为纸面符号论证；未运行数值实验、CAS、数学枚举、门字搜索或 Lean。
文件检索、来源比对、排版编译与页面检查仅服务于审阅和交付。
经典 Bloch 几何、效果版 Gleason 定理、二叉测量、根系与紧群理论均保留原有归属。
本文的贡献范围是本研究路线中的接口细化、直接证明与条件综合，不提出一般数学工具的原创优先权。

## 目录

1. [两份研究的实际接点与固定来源](#sec-sources)
2. [观察者、被测态与基底的相对门表示](#sec-relative)
3. [二态系统为何出现三个坐标](#sec-bloch)
4. [把三轴直觉加强为可以证明的相容原则](#sec-frames)
5. [概率相容与测后状态是两个义务](#sec-effects)
6. [五点与三读口：把关系相融变成精确判据](#sec-five)
7. [多元关系的二元化究竟保留了什么](#sec-binary)
8. [从另一会话的 E8 胶合到一个具体二态编码](#sec-e8code)
9. [五种相位的读出：二元递归不能无代价增加信息](#sec-phase)
10. [固定黄金门如何生成 E8，及其不能替代的控制](#sec-control)
11. [最新项目结果如何约束这套理论](#sec-latest)
12. [一套可继续发展的条件理论](#sec-synthesis)

[文献与固定项目来源](#sec-bibliography)

<a id="sec-sources"></a>

## 1. 两份研究的实际接点与固定来源

本轮固定仓库 `dev` 提交为
`6f7aa75a805fc506ba97bf40728c48da8d90fd56`。
其时间为 2026 年 10 月 30 日 20:05:34（新加坡；UTC 12:05:34），合并 PR #24193。
相对 v27 所用 `66259f03d60716f143cd59c7644dadcb67cc1b73` 前进 154 个提交。
两固定提交的完整树差分含 3055 个变更文件，其中 theory 目录恰有八个；
本稿只把实际阅读且与本题有关的增量用于推理。
这里固定一次快照，不把后续尚未检查的提交包含在“已核对”中。（[1](#ref-repohead)）

本轮完整读取另一会话已经交付的
*AURIC–E8 相容扩张与观察理论* LaTeX 源文稿；
该稿基于旧快照 `66259f0`。
它证明的是固定正交等尺度 $A_4^2$ 的严格积分扩张、五分级相位、
全局提升障碍、条件 E8 控制和黄金读出的稳定性。
本文直接承接这些明示条件，并给出二态编码与黄金门的新接口；
没有把另一会话的完整聊天记录视为已取得。（[8](#ref-selfe8)）

与本题直接相关的项目新进展包括：
相干重构续卷 II 第 96–97 节；
类型化残差余循环文本中的联合误差支撑判据；
以及新加入的十八模式玻色占据赋值 Lean 源文件。
黄金门 v15 的 Git blob 仍为
`34d292bc4447b98f96919745c31ff915824a67cc`。
新归档的旧研究稿不被计作独立验证。（[2](#ref-repoborn)、[6](#ref-repococycle)、[7](#ref-repoks)、[3](#ref-repov15)）

| 对象 | 载体与维数 | 本文允许的解释 |
| --- | --- | --- |
| AURIC 五模式 | $\mathcal{H}_F\simeq\mathbb{C}^5$ | 五种合法占据模式及其实际读口 |
| 原生量子扇区 | $\mathcal{H}_{13}\simeq\mathbb{C}^{13}$ | 七个原生门与完整终端律 |
| 二态编码 | $W\simeq\mathbb{C}^2$ | 明确选定且控制泄漏的子空间 |
| Bloch 表示 | $B^3\subset\mathbb{R}^3$ | 二维复密度矩阵的实坐标 |
| E8 关系格 | $\Gamma\subset\mathbb{R}^8$ | 整数配对和胶合关系 |
| E8 伴随载体 | $\mathfrak e_{8,\mathbb{C}}\simeq\mathbb{C}^{248}$ | 根双态码、五分级和群作用 |

统一采用

$$
\varphi=\frac{1+\sqrt5}{2},\qquad x=\varphi^{-1},\qquad
 \zeta=e^{3\pi i/5},\qquad \omega=e^{2\pi i/5}.
$$

于是 $x+x^2=1$、$\zeta^{10}=1$、$\zeta^5=-1$、$\zeta^2=\omega^3$。
本稿用 $\omega$ 表示 E8 五分级相位，避免与旧 E8 稿中的五次根记号混淆。
内积对第一变量共轭线性、对第二变量线性。

<a id="sec-relative"></a>

## 2. 观察者、被测态与基底的相对门表示

<a id="statement-2-1"></a>

#### 定义 2.1（相对制备与读出）

给定复希尔伯特空间 $\mathcal{H}$、单位种子 $\lvert 0 \rangle$、制备酉 $A$ 和基底酉 $B$，
令 $\lvert \psi \rangle =A\lvert 0 \rangle$、$\lvert b_i \rangle =B\lvert i \rangle$。
相对门为 $R=B^\dagger A$。在已供应 Born 读口的模型中，
第 $i$ 个结果的概率为

$$
p_i=\left| \langle b_i,\psi\rangle \right| ^2
     =\left| \langle i \rvert  B^\dagger A\lvert 0 \rangle  \right| ^2.
$$

“门”可以是有限字，也可以是另行供应的数学酉；
仅有稠密可达性时，不能把任意数学酉说成原菜单的精确有限字。

<a id="statement-2-2"></a>

#### 定理 2.2（共同换框消去）

对任意酉 $U$，同时将 $(A,B)$ 替换为 $(UA,UB)$，相对门及全部概率不变。
两对酉 $(A,B)$、$(A',B')$ 的相对门相同，当且仅当它们相差这种共同左作用。

**证明。**

$(UB)^\dagger(UA)=B^\dagger A$。反之，若 $B'^\dagger A'=B^\dagger A$，
令 $U=B'B^\dagger$，则 $UB=B'$ 且
$UA=B'B^\dagger A=B'(B'^\dagger A')=A'$。

∎

因此“把共同本体约去”有一个精确版本：对一对完整酉标架取共同左作用的商。
它不意味着未知物理本体已被证明不存在，也不意味着种子、内积或读口权重无需指定。

<a id="statement-2-3"></a>

#### 命题 2.3（两个制备程序未必给出正交基）

若 $\lvert b_0 \rangle =B_0\lvert 0 \rangle$、$\lvert b_1 \rangle =B_1\lvert 0 \rangle$，则它们正交恰当且仅当

$$
\langle 0 \rvert  B_0^\dagger B_1\lvert 0 \rangle =0.
$$

程序不同本身不蕴含正交。若正交，则存在数学酉 $B$ 以二者为前两列；
该补全的原生可实现性仍是独立问题。

**证明。**

第一式就是内积的定义。正交单位对可扩充为正交归一基，按列排列得到酉矩阵。
例如 $B_0=I$ 与作用在种子上仅给整体相位的非恒等 $B_1$，程序不同而射线相同。

∎

<a id="statement-2-4"></a>

#### 定理 2.4（二态读出的泄漏项）

设 $b_0,b_1$ 正交，$P_i=\lvert b_i \rangle \langle b_i \rvert$，$W=\operatorname{span}\{b_0,b_1\}$。
对任意密度态 $\rho$，

$$
p_0+p_1=\operatorname{Tr}(\rho\Pi_W),\qquad
 p_\perp=1-p_0-p_1=\operatorname{Tr}(\rho(I-\Pi_W)).
$$

二者之和为一，恰当且仅当 $\rho$ 的支撑包含于 $W$。
否则完整读出至少应保留补空间结果，或明确以 $W$ 中成功为条件做后选择。

**证明。**

$P_0+P_1=\Pi_W$，取迹得公式。
若 $\operatorname{Tr}(\rho(I-\Pi_W))=0$，则
$\left\lVert (I-\Pi_W)\sqrt\rho \right\rVert _{\mathrm{HS}}^2=0$，故支撑在 $W$；逆向显然。

∎

在原生 $\mathcal{H}_{13}$ 中补空间维数为 $11$；在 E8 伴随载体中则为 $246$。
丢掉泄漏结果再归一化，会改变研究的概率合同。

<a id="statement-2-5"></a>

#### 定义 2.5（观察者的操作性版本）

有限观察者模型由可执行制备和门、测量仪器族、可读记录代数、
以及依记录选择下一操作的策略组成。
其“预测”是在这些权限下给未来记录赋予条件律；
“增长”是把新的记录或控制节点加入模型。
这给出内生观察者的一种数学实现，不把该定义当作对意识或宇宙本体的唯一刻画。

<a id="sec-bloch"></a>

## 3. 二态系统为何出现三个坐标

本节的标准 Pauli 算子为

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
 \sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
 \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

<a id="statement-3-1"></a>

#### 定理 3.1（归一化、共同相位与 Bloch 球）

令 $\lvert \psi \rangle =a\lvert 0 \rangle +b\lvert 1 \rangle$，$|a|^2+|b|^2=1$，并按共同相位识别纯态。
定义

$$
r_x=2\Re(\overline a b),\qquad
 r_y=2\Im(\overline a b),\qquad
 r_z=|a|^2-|b|^2.
$$

则 $\left\lVert \mathbf r \right\rVert =1$，且得到双射

$$
\mathbb{C} P^1=S^3/U(1)\simeq S^2.
$$

一般二态密度矩阵恰为

$$
\rho=\frac12(I+r_x\sigma_x+r_y\sigma_y+r_z\sigma_z),
 \qquad \left\lVert \mathbf r \right\rVert \le1.
$$

**证明。**

直接展开，

$$
r_x^2+r_y^2+r_z^2
 =4|a|^2|b|^2+(|a|^2-|b|^2)^2
 =(|a|^2+|b|^2)^2=1.
$$

共同相位消去。反向，若 $r_z>-1$，可取

$$
a=\sqrt{\frac{1+r_z}{2}},\qquad
 b=\frac{r_x+i r_y}{\sqrt{2(1+r_z)}}；
$$

南极取 $(a,b)=(0,1)$。所得秩一投影为

$$
\lvert \psi \rangle \langle \psi \rvert =
 \frac12\begin{pmatrix}1+r_z&r_x-i r_y\\r_x+i r_y&1-r_z\end{pmatrix},
$$

故同一 $\mathbf r$ 恰给同一射线。
任意迹一 Hermitian $2\times2$ 矩阵可唯一如此展开。
由 $(\mathbf r\cdot\boldsymbol\sigma)^2=\left\lVert \mathbf r \right\rVert ^2I$，
其本征值为 $(1\pm\left\lVert \mathbf r \right\rVert )/2$，正性等价于球内条件。

∎

精确的自由度计数是：两个复振幅有四个实参数；
归一化去掉一个，共同相位再去掉一个，纯态剩两个实自由度。
这些自由度由嵌入 $\mathbb{R}^3$ 的球面表示。
因此不能把“一个复平面的两个实坐标加一个约束”直接数成三个自由度；
约束通常减少维数。三维来自迹一二阶复 Hermitian 矩阵的三个实分量。

<a id="statement-3-2"></a>

#### 命题 3.2（概率差与复相干的三个实分量）

写

$$
\rho=\begin{pmatrix}p&c\\\overline c&1-p\end{pmatrix}.
$$

则 $\rho\ge0$ 当且仅当 $0\le p\le1$ 且
$|c|^2\le p(1-p)$；纯态时取等号。
在本文约定下

$$
r_z=2p-1,\qquad r_x=2\Re c,\qquad r_y=-2\Im c.
$$

因此“一对结果之间的关系”可具体表现为复相干 $c$；
它含两个实量，通常不能由 $p$ 和 $1-p$ 恢复。

**证明。**

二阶 Hermitian 矩阵的正性由两个对角元非负和行列式非负判定；
纯迹一矩阵等价于行列式零。与上一矩阵逐项比较即可。

∎

<a id="statement-3-3"></a>

#### 定理 3.3（夹角读出及两坐标歧义）

对单位测量方向 $\mathbf n$，令
$P_{\mathbf n}=(I+\mathbf n\cdot\boldsymbol\sigma)/2$。
则

$$
p(+\mid\rho,\mathbf n)=\operatorname{Tr}(\rho P_{\mathbf n})
 =\frac{1+\mathbf r\cdot\mathbf n}{2}.
$$

纯态时若 $\theta_B$ 是 Bloch 向量夹角，
$\theta_{\rm FS}=\arccos|\langle b,\psi\rangle|$，
则

$$
p=\cos^2(\theta_B/2)=\cos^2\theta_{\rm FS},
 \qquad \theta_B=2\theta_{\rm FS}.
$$

已知纯态的 $r_x,r_z$，一般只得到
$r_y=\pm\sqrt{1-r_x^2-r_z^2}$。
混态则允许整个区间
$|r_y|\le\sqrt{1-r_x^2-r_z^2}$。

**证明。**

$\operatorname{Tr}\sigma_i=0$、$\operatorname{Tr}(\sigma_i\sigma_j)=2\delta_{ij}$ 给迹公式。
纯态转移概率等于两秩一投影乘积的迹，再用半角恒等式。
剩余坐标的结论由球面或球内约束直接得到。
例如 $(\lvert 0 \rangle +i\lvert 1 \rangle )/\sqrt2$ 与 $(\lvert 0 \rangle -i\lvert 1 \rangle )/\sqrt2$
具有相同 $r_x=r_z=0$，而 $r_y$ 符号相反。

∎

Hilbert 空间中的正交基态对应 Bloch 球的对踵点；
三条正交 Bloch 轴对应三个不对易的 Pauli 观测量。
这是两种不同的“正交”。在重复制备上估计三轴统计，
也不同于对一份未知态一次读出三个精确实数。

<a id="statement-3-4"></a>

#### 推论 3.4（三轴方差的平方约束）

在标准 Pauli 读出中，

$$
\sum_{j=x,y,z}\operatorname{Var}_\rho(\sigma_j)
 =3-\left\lVert \mathbf r \right\rVert ^2\ge2,
$$

纯态时等号成立；并且
$\Delta_\rho\sigma_x\,\Delta_\rho\sigma_y\ge|r_z|$。

**证明。**

$\sigma_j^2=I$ 给方差 $1-r_j^2$，求和即可。
又

$$
(1-r_x^2)(1-r_y^2)-r_z^2
 =1-\left\lVert \mathbf r \right\rVert ^2+r_x^2r_y^2\ge0,
$$

开平方给第二式。

∎

这是已给复二态结构与 Pauli 读口后的不确定性关系；
某一轴处于本征态时该轴方差可以为零，另外两轴承担方差。

<a id="sec-frames"></a>

## 4. 把三轴直觉加强为可以证明的相容原则

<a id="statement-4-1"></a>

#### 定义 4.1（全正交框架的中心化响应相容）

纯制备标签 $\mathbf m\in S^2$、二元问题方向 $\mathbf n\in S^2$。
令 $p_{\mathbf m}(\mathbf n)\in[0,1]$，并定义
$f_{\mathbf m}(\mathbf n)=2p_{\mathbf m}(\mathbf n)-1$。
本节明确要求：

1. 互补读出：$f_{\mathbf m}(-\mathbf n)=-f_{\mathbf m}(\mathbf n)$；

2. 共同旋转协变与连续性：
$f_{R\mathbf m}(R\mathbf n)=f_{\mathbf m}(\mathbf n)$，$R\in SO(3)$，
且响应连续；

3. 自身标定：$f_{\mathbf m}(\mathbf m)=1$；

4. 对每个正交归一三框架 $(\mathbf n_1,\mathbf n_2,\mathbf n_3)$，

$$
\sum_{j=1}^3 f_{\mathbf m}(\mathbf n_j)^2=1.
 \tag{F}
$$

(F) 约束的是同一制备在不同实验设置下的响应族，
并不声称三次不对易测量可在同一份样本上同时无扰动完成。

<a id="statement-4-2"></a>

#### 定理 4.2（全框架平方相容锁定 Born 角度律）

<a id="thm-frameborn"></a>

上述条件强制

$$
f_{\mathbf m}(\mathbf n)=\mathbf m\cdot\mathbf n,\qquad
 p_{\mathbf m}(\mathbf n)=\frac{1+\mathbf m\cdot\mathbf n}{2}.
$$

**证明。**

绕 $\mathbf m$ 的旋转把具有相同 $\mathbf m\cdot\mathbf n$ 的方向互相连接，
所以存在连续函数 $h:[-1,1]\to[-1,1]$，使
$f_{\mathbf m}(\mathbf n)=h(\mathbf m\cdot\mathbf n)$。
共同协变使 $h$ 不依赖 $\mathbf m$，互补性给 $h$ 奇，自身标定给 $h(1)=1$。
令 $g(t)=h(\sqrt t)^2$，$0\le t\le1$。
任意 $s,t,u\ge0$、$s+t+u=1$ 都可作为固定单位 $\mathbf m$
在某个正交框架中三个坐标的平方；故

$$
g(s)+g(t)+g(u)=1.
$$

先取 $(1,0,0)$ 得 $g(0)=0$。
再比较 $(s,t,1-s-t)$ 与 $(s+t,0,1-s-t)$，得到

$$
g(s+t)=g(s)+g(t)\qquad(s,t\ge0,\ s+t\le1).
$$

$g\ge0$ 使其单调；$g(1)=1$ 给有理点 $g(q)=q$，
由有理数上下逼近得所有实点 $g(t)=t$。
因此 $h(v)^2=v^2$。在 $(0,1]$ 上 $h$ 无零点，
连续性及 $h(1)=1$ 选择正支 $h(v)=v$；
奇性处理负半轴，$h(0)=0$。代回即可。

∎

这一结论直接回应“三轴加约束”的直觉：真正有强制力的是
**所有旋转框架共享同一个相容响应**。
三维方向空间、可标定概率、连续性以及 (F) 仍是输入条件；
此定理没有从五点形状独自生成它们。

<a id="statement-4-3"></a>

#### 命题 4.3（二元互补、标定与旋转相容本身不够）

对任意纯标签 $\mathbf m$，

$$
\widetilde p_{\mathbf m}(\mathbf n)
   =\frac{1+(\mathbf m\cdot\mathbf n)^3}{2}
$$

满足连续性、正性、互补归一化、自身标定和共同旋转协变，
但通常不是 Born 响应，也不满足 (F)。

**证明。**

所有前述性质由三次函数的奇性、单调性与区间范围直接得到。
取框架使 $\mathbf m$ 三坐标均为 $1/\sqrt3$，
则三个中心化响应的平方和为
$3(1/\sqrt3)^6=1/9$，不等于一。

∎

<a id="statement-4-4"></a>

#### 命题 4.4（二元问题不单独选择三维）

对每个整数 $d\ge2$，状态空间 $B^d=\{\mathbf r:\left\lVert \mathbf r \right\rVert \le1\}$、
方向 $\mathbf n\in S^{d-1}$ 和

$$
e_{\pm\mathbf n}(\mathbf r)=\frac{1\pm\mathbf n\cdot\mathbf r}{2}
$$

给出正的归一二元响应，允许全部 $SO(d)$ 旋转。
因此仅凭二元性、归一化及各向同性，无法选出 $d=3$。

**证明。**

Cauchy–Schwarz 给 $|\mathbf n\cdot\mathbf r|\le1$，
故两个响应非负且和为一。正交变换保持内积。
每个 $d$ 都成立，所以这些条件没有维数选择能力。

∎

<a id="statement-4-5"></a>

#### 定理 4.5（由可逆相互作用选择三维：外部重构定理的条件推论）

<a id="thm-krumm"></a>

额外采用 Krumm–Müller 的球比特复合框架：
单系统为 $B^d$、$d\ge2$；包含全部局部 $SO(d)$；
复合空间包含所有独立积态及其积二元效果；
复合系统满足无信号和局部层析，其状态由全部局部测量统计及联合相关确定；
全局可逆变换构成闭连通矩阵群，并保持所有合法概率。
若存在不能写成独立局部门乘积的可逆变换，则 $d=3$。

**证明。**

所引原文定理 1 在完全相同的框架下证明：
$d\ne3$ 时全局群等于局部群。取逆否命题即得。
这里完整分类证明归于该文，本文没有将其改称为 AURIC 五点的无条件推导。（[11](#ref-krumm)）

∎

“局部层析”包含所有阶数的联合相关，绝非只检查两两边缘。
该定理提供一条比“两个加一个等于三”更强的量子起源路线：
先明确复合与相容，再要求真正的可逆相互作用。

<a id="statement-4-6"></a>

#### 定理 4.6（反对易三操作产生相容复结构）

<a id="thm-clifford"></a>

设非零有限维实内积空间 $V$ 上有实自伴算子 $A,B,C$，满足

$$
A^2=B^2=C^2=I,\qquad AB=-BA,\quad BC=-CB,\quad CA=-AC.
$$

则 $J=ABC$ 是正交复结构：

$$
J^2=-I,\qquad J^{\mathsf T}=-J,\qquad
 JA=AJ,\quad JB=BJ,\quad JC=CJ.
$$

令 $i$ 作用为 $J$，可得 $V\simeq\mathbb{C}^2\otimes\mathbb{C}^m$，
且在合适酉坐标中

$$
A=\sigma_z\otimes I_m,\quad
 B=\sigma_x\otimes I_m,\quad
 C=\sigma_y\otimes I_m.
$$

特别地 $\dim_\mathbb{R} V=4m$；最小非零或不可约情形就是一个复二态系统。

**证明。**

移动三个算子时共有三次反交换，故
$J^2=-A^2B^2C^2=-I$、$J^{\mathsf T}=CBA=-J$，
从而 $J^{\mathsf T}J=I$。
每个生成元跨过另外两个生成元时符号消去，所以它们与 $J$ 对易。
实内积 $g$ 与 $J$ 给 Hermitian 内积
$\langle u,v\rangle_\mathbb{C}=g(u,v)-i\,g(u,Jv)$。
于是 $A,B,C$ 都为复线性自伴酉算子。
将 $V=V_+\oplus V_-$ 按 $A$ 的 $\pm1$ 本征空间分解；
$J$ 保持两空间，$B$ 将二者酉同构，所以二者复维数相等，记为 $m$。
选 $V_+$ 的正交复基 $u_1,\ldots,u_m$，以 $Bu_1,\ldots,Bu_m$ 为 $V_-$ 基，
便得所列 $A,B$ 矩阵。
又 $AB=JC=iC$，故 $C=-iAB=\sigma_y\otimes I_m$。
每对 $\operatorname{span}_\mathbb{C}\{u_k,Bu_k\}$ 都不变，因此不可约时 $m=1$。

∎

这是 Clifford 三生成元结构在本题中的直接表述，
相同复结构线索已出现于本轮入库的旧 v24 稿。（[5](#ref-repov24)）
它提供一条真正能够构造 $i$ 的条件路线：
**把三读出强化为三个反对易的归一化可逆操作。**
三个普通欧氏方向正交，以及三个对易占据读口，都没有自动满足这一算子关系。
故这里推出的是“反对易相容结构所要求的复二态”，而非从三点外形推出复数。

<a id="sec-effects"></a>

## 5. 概率相容与测后状态是两个义务

<a id="statement-5-1"></a>

#### 定义 5.1（全效果相容权重）

在已给定有限维复 $\mathcal{H}$ 上，效果为 $0\le E\le I$。
一个权重 $w$ 对全部效果定义，并满足

$$
w(E)\ge0,\qquad w(I)=1,\qquad
 w(E+F)=w(E)+w(F)\quad(E,F\ge0,\ E+F\le I).
 \tag{E}
$$

同一 $E$ 出现在不同分解中时使用同一个 $w(E)$；
这就是此处的上下文无关性及粗粒化相容。

<a id="statement-5-2"></a>

#### 定理 5.2（效果相容推出密度算子）

<a id="thm-effectborn"></a>

满足 (E) 的权重唯一写成

$$
w(E)=\operatorname{Tr}(\rho E),\qquad \rho\ge0,\quad\operatorname{Tr}\rho=1.
$$

在 $\dim\mathcal{H}=2$ 时结论同样成立。

**证明。**

可加性先给 $w(0)=0$；若 $E\le F$，则 $w(F)-w(E)=w(F-E)\ge0$。
拆成等份得有理齐次性 $w(qE)=qw(E)$，$0\le q\le1$；
用有理数上下夹逼及单调性，得到所有 $t\in[0,1]$ 的实齐次性。
对 $A\ge0$ 选 $s\ge\left\lVert A \right\rVert$、$s>0$，定义
$L(A)=s\,w(A/s)$；齐次性保证与 $s$ 无关。
把 $A,B,A+B$ 同时缩入效果区间，得到 $L(A+B)=L(A)+L(B)$。
对 Hermitian $H=A-B$ 定义 $L(H)=L(A)-L(B)$；
若另一分解 $A'-B'$ 相同，则 $A+B'=A'+B$，所以定义无歧义。
于是 $L$ 为正的实线性泛函。
有限维 Hermitian 空间的迹内积非退化，给唯一 Hermitian $\rho$ 使
$L(H)=\operatorname{Tr}(\rho H)$。作用于所有秩一投影得 $\rho\ge0$，
作用于 $I$ 得 $\operatorname{Tr}\rho=1$。

∎

这是 Busch 效果版 Gleason 定理的有限维形式。（[10](#ref-busch)）
输入已包含复效果空间和全效果可加性。
只对一个互补投影对要求归一化，比 (E) 弱得多；
定理不能被表述成“只要存在两个读出，就已经无前提推出 Born 规则”。

<a id="statement-5-3"></a>

#### 定义 5.3（仪器与效果）

量子仪器由完全正、迹不增映射 $\{\mathcal I_i\}$ 组成，
且 $\sum_i\mathcal I_i$ 保迹。效果 $E_i$ 满足
$\operatorname{Tr}\mathcal I_i(\rho)=\operatorname{Tr}(\rho E_i)$。
条件测后态为 $\mathcal I_i(\rho)/\operatorname{Tr}(\rho E_i)$，分母须为正。

<a id="statement-5-4"></a>

#### 定理 5.4（角度或效果不能唯一决定塌缩更新）

同一 PVM $\{P_0,P_1\}$ 可对应不同的合法测后状态规则，
而所有该次读出概率完全相同。

**证明。**

在 $\mathbb{C}^2$ 中取计算基投影。
Lüders 仪器为 $\mathcal I_i(\rho)=P_i\rho P_i$。
另取

$$
\mathcal J_i(\rho)=\operatorname{Tr}(\rho P_i)\lvert 0 \rangle \langle 0 \rvert .
$$

后一映射的 Kraus 算子是 $\lvert 0 \rangle \langle i \rvert$，因此完全正且两支和保迹。
两者效果均为 $P_i$。对输入 $\lvert 1 \rangle \langle 1 \rvert$，
结果 $1$ 的概率都为一，但条件输出分别为 $\lvert 1 \rangle \langle 1 \rvert$ 与 $\lvert 0 \rangle \langle 0 \rvert$。
因此一次读出夹角不能区分二者。

∎

<a id="statement-5-5"></a>

#### 命题 5.5（静态联合描述与条件分支）

对完备 PVM $\{P_i\}_{i=1}^r$，映射

$$
V\lvert \psi \rangle =\sum_i P_i\lvert \psi \rangle \otimes\lvert i \rangle
$$

为等距映射，可在引入固定初态记录寄存器后扩充为酉操作。
忽略记录给 $\sum_iP_i\rho P_i$；
按记录 $i$ 条件化给 Lüders 分支。

**证明。**

$V^\dagger V=\sum_iP_i^\dagger P_i=I$。
有限维等距映射把输入子空间的一组正交基送为正交组，
补全两端正交基得到酉扩张。
展开 $V\rho V^\dagger$ 后取记录偏迹或夹取 $\lvert i \rangle$ 即得两式。

∎

因此“全局关系可静态表示”与“局部观察者有条件更新”可以同时成立。
该构造本身没有解决为什么单次经验出现某一结果的解释问题；
概率、仪器和记录读口在此仍有明确数学角色。

<a id="statement-5-6"></a>

#### 定理 5.6（递归记录的相容性不要求额外的外部时钟）

设每个有限历史 $h$ 的下一步 Kraus 族满足
$\sum_iM_{i|h}^\dagger M_{i|h}=I$。
令 $K_\varnothing=I$、$K_{hi}=M_{i|h}K_h$，则

$$
p(h)=\operatorname{Tr}(K_h\rho K_h^\dagger),\qquad
 \sum_i p(hi)=p(h).
$$

所有有限记录可作为一棵静态树的相容权重表示。

**证明。**

将 $K_{hi}$ 代入，迹的循环性及 Kraus 完备性给

$$
\sum_i p(hi)
 =\operatorname{Tr}\!\left(K_h\rho K_h^\dagger
             \sum_iM_{i|h}^\dagger M_{i|h}\right)=p(h).
$$

根权重为一，逐层得到每个有限深度的完整归一。

∎

这里没有另选一个绝对物理时间，但组合次序仍由程序或因果依赖确定。
作用在独立张量因子上的操作可以交换；一般同一系统上的门不可以任意换序。
例如 $P_xP_z\lvert 0 \rangle =\lvert + \rangle /\sqrt2$，
而 $P_zP_x\lvert 0 \rangle =\lvert 0 \rangle /2$。
“静态相融”应保存这些组合关系，不能自动变成交换律。

<a id="sec-five"></a>

## 6. 五点与三读口：把关系相融变成精确判据

<a id="statement-6-1"></a>

#### 定理 6.1（候选转移概率来自同一 qubit 的充要条件）

<a id="thm-gram"></a>

给定 $N$ 个标签和实对称表 $q_{ij}$，$q_{ii}=1$。
存在纯二态射线 $\psi_1,\ldots,\psi_N$ 使

$$
q_{ij}=|\langle\psi_i,\psi_j\rangle|^2
$$

当且仅当矩阵

$$
G_{ij}=2q_{ij}-1
$$

半正定且 $\operatorname{rank} G\le3$。
这特别适用于 AURIC 的五个候选标签，但不自动把五个合法基模式压成二态。

**证明。**

若存在射线，其单位 Bloch 向量 $\mathbf r_i\in\mathbb{R}^3$ 满足
$q_{ij}=(1+\mathbf r_i\cdot\mathbf r_j)/2$，
所以 $G$ 是这些向量的 Gram 矩阵，半正定、秩至多三。
反之，正半定且秩至多三的 $G$ 可分解为实向量 Gram 矩阵；
对角元一保证向量均为单位向量。
用 Bloch 球双射为每个向量选一条射线，即得所有指定概率。

∎

<a id="statement-6-2"></a>

#### 命题 6.2（逐对可行不等于全局二态可行）

四标签表 $q_{ii}=1$、$q_{ij}=1/2$（$i\ne j$）的每一对都可由二态射线实现，
但四者不能同时来自同一个 qubit。

**证明。**

任意一对可取 Bloch 球上的正交单位向量。
整体表却给 $G=I_4$，秩为四，违反定理 [6.1](#thm-gram)。

∎

三维 Bloch Gram 数据通常还遗失一个定向选择。
v27 已证明

$$
\operatorname{Tr}(P_aP_bP_c)=\frac14\left(
 1+\mathbf a\cdot\mathbf b+\mathbf b\cdot\mathbf c+\mathbf c\cdot\mathbf a
 +i\,\mathbf a\cdot(\mathbf b\times\mathbf c)\right).
$$

两两概率确定点积及三重积的绝对值，未确定其符号；
复共轭保持所有两两概率而翻转该虚部。
所以复相位所保存的关系可以位于有向闭环中。（[9](#ref-selfv27)）
这与“关系在连线上”的直觉相接，但闭环相容不是孤立边权列表。

<a id="statement-6-3"></a>

#### 定义 6.3（项目五模式的三个占据读口）

在五模式的复线性实现中，沿用项目顺序

$$
(\lvert N \rangle ,\lvert 2 \rangle ,\lvert 3 \rangle ,\lvert 5 \rangle ,\lvert 25 \rangle )
 =(\lvert 000 \rangle ,\lvert 100 \rangle ,\lvert 010 \rangle ,\lvert 001 \rangle ,\lvert 101 \rangle ).
$$

三个占据算子为

$$
N_1=\operatorname{diag}(0,1,0,0,1),\quad
 N_2=\operatorname{diag}(0,0,1,0,0),\quad
 N_3=\operatorname{diag}(0,0,0,1,1).
$$

它们两两对易。令
$X=\operatorname{Tr}(\rho N_1)$、$Y=\operatorname{Tr}(\rho N_3)$、$Z=\operatorname{Tr}(\rho N_2)$。（[4](#ref-repofib)、[8](#ref-selfe8)）

<a id="statement-6-4"></a>

#### 命题 6.4（三个稳定占据均值仍有隐藏纤维）

对角概率向量的全部解为

$$
p=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
$$

其中

$$
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
$$

这里 $X,Y,Z$ 已来自态的占据均值；若改为任意候选实三元组，
还须另要求 $Z\ge0$，再以区间非空判定可行性。
对全部五维密度矩阵，在正定态附近固定三个均值留下实维数 $21$ 的仿射纤维。

**证明。**

令 $\kappa=p_{25}$，由三个占据和解得其余四项；
逐项非负给所列上下界。
五阶迹一 Hermitian 矩阵实维数为 $25-1=24$，
三个占据泛函在迹一空间上独立，故固定它们留下 $24-3=21$ 维。
正定集合开，局部维数不会被正性再压低。

∎

对角纤维在上下界严格分离时是一维区间，在端点重合时退化为单点。

<a id="statement-6-5"></a>

#### 定理 6.5（原始占据三读口不能直接成为尖锐 Pauli 三轴）

设 $J:\mathbb{C}^2\to\mathcal{H}_F$ 是任意等距编码。
三个压缩效果 $J^\dagger N_iJ$ 联合可测。
它们不可能同时等于三个不同正交轴的正结果 Pauli 投影。

**证明。**

原五模式 PVM 的压缩
$E_s=J^\dagger\lvert s \rangle \langle s \rvert J$ 非负且 $\sum_sE_s=I_2$。
每个 $J^\dagger N_iJ$ 都是相应模式 $E_s$ 的和，故同一 POVM 给出联合测量。
现在证明尖锐二元投影 $P$ 与任一联合可测效果 $Q$ 必须对易。
若联合效果为 $F_{ab}$，则 $0\le F_{1b}\le P$、
$0\le F_{0b}\le I-P$。
正性迫使前者支撑在 $\operatorname{ran}P$、后者在其正交补，
所以 $Q=F_{01}+F_{11}$ 对该分解块对角，$[P,Q]=0$。
不同正交 Pauli 轴的秩一投影不对易，矛盾。

∎

压缩后的效果本身可以不对易，但仍联合可测，不能据此得到全部尖锐 Pauli 读口。
要在 AURIC 上使用 Bloch 三轴，必须另给相干基底变换与对应读口，
或明确研究的是带噪的不尖锐效果。

<a id="statement-6-6"></a>

#### 定理 6.6（三个无偏正交读口的共同锐度界）

<a id="thm-sharpness"></a>

对 $0\le\eta_j\le1$，效果
$E_{j,\pm}=(I\pm\eta_j\sigma_j)/2$ 联合可测，
当且仅当

$$
\eta_x^2+\eta_y^2+\eta_z^2\le1.
$$

等强度时恰为 $\eta\le1/\sqrt3$。

**证明。**

记 $s\in\{\pm1\}^3$、$v_s=(s_x\eta_x,s_y\eta_y,s_z\eta_z)$。
若 $\left\lVert \boldsymbol\eta \right\rVert \le1$，则
$G_s=(I+v_s\cdot\boldsymbol\sigma)/8$ 非负、和为单位，
其三个二元边缘正是所需效果。
反之，任意联合 POVM 写成
$G_s=(a_sI+\mathbf b_s\cdot\boldsymbol\sigma)/2$。
正性给 $\left\lVert \mathbf b_s \right\rVert \le a_s$，
归一给 $\sum_sa_s=2$，边缘给
$\sum_s s_j\mathbf b_s=2\eta_j\mathbf e_j$。
因此

$$
2\left\lVert \boldsymbol\eta \right\rVert ^2
 =\sum_s v_s\cdot\mathbf b_s
 \le\left\lVert \boldsymbol\eta \right\rVert \sum_s\left\lVert \mathbf b_s \right\rVert 
 \le2\left\lVert \boldsymbol\eta \right\rVert .
$$

零向量情形直接成立；非零时约去范数即得结论。

∎

这是无偏正交三轴联合测量的标准条件，文献中的必要界见
Brougham–Andersson 附录式 (A4)。（[13](#ref-brougham)）
此处的平方约束针对效果的读口锐度，而 Bloch 球平方约束针对态；
两者作用于不同对象，不能直接相互替换。

<a id="sec-binary"></a>

## 7. 多元关系的二元化究竟保留了什么

<a id="statement-7-1"></a>

#### 定理 7.1（带联合见证域的二元编码）

<a id="thm-witness"></a>

对任意集合关系 $R\subset X_1\times\cdots\times X_N$，
存在辅助域 $W$ 和二元关系 $E_i\subset W\times X_i$，使

$$
R(x_1,\ldots,x_N)
 \ \Longleftrightarrow\
 \exists w\in W\ \bigwedge_{i=1}^N E_i(w,x_i).
$$

可取 $W=R$，$E_i(w,x_i)$ 定义为第 $i$ 个坐标投影等于 $x_i$。

**证明。**

若元组属于 $R$，以自身为见证即可。
反之，某个 $w\in R$ 同时具有这些坐标，故目标元组就是 $w$，属于 $R$。
空关系取空辅助域也成立。

∎

这是约束满足问题中隐藏变量编码的直接形式。（[14](#ref-samaras)）
有限情形辅助域可能具有与整个允许元组集相同的规模；
图变成二元 incidence 并不表示联合信息消失或自动压到三实维。

<a id="statement-7-2"></a>

#### 命题 7.2（所有两两投影可以丢失全部奇偶约束）

令
$R_{\rm even}=\{(a,b,c)\in\{0,1\}^3:a\oplus b\oplus c=0\}$。
它的每个两坐标投影都是 $\{0,1\}^2$，
但原关系只允许八个元组中的四个。

**证明。**

任意指定两个坐标，第三个可唯一选为它们的异或，使总奇偶为零。
因此每个二元投影都不排除任何二元取值，而原三元约束仍排除奇数奇偶。

∎

<a id="statement-7-3"></a>

#### 定理 7.3（只给布尔二元约束，加入布尔辅助变量仍不够）

<a id="thm-boolean"></a>

三元偶奇偶关系不能写成有限个布尔一元、二元关系的合取，
再对任意有限个布尔辅助变量作存在量化。

**证明。**

记 $\operatorname{maj}(a,b,c)$ 为三个布尔值的多数值，并逐坐标作用于元组。
任意布尔二元关系都对多数运算封闭：
对三个允许的二元组，每一坐标至少有两个输入行等于该坐标的多数值；
两个各至少含两行的子集在三行中必相交。
交中的一行恰等于所得多数二元组，所以它仍在该关系内。
一元关系也显然封闭。
封闭性被合取保留；存在量化也保留，因为对三个可行的自由变量元组，
取它们各自的辅助见证，再对全部自由变量与见证逐坐标取多数，
便得到新的共同见证。
然而偶奇偶关系含 $110,101,011$，三者的逐坐标多数为 $111$，
后者不在关系中。因此不可能有上述表达。

∎

定理 [7.1](#thm-witness) 没有矛盾：它允许四值或更大的联合见证域。
NAND 的“两个输入”也不等于关系只有二元；
其正确性关系 $z=\neg(a\land b)$ 涉及 $(a,b,z)$ 三个变量。

<a id="statement-7-4"></a>

#### 命题 7.4（两体边缘不决定整体量子关系）

对 $N\ge3$，

$$
\lvert \mathrm{GHZ}_\pm \rangle 
 =\frac{\lvert 0 \rangle ^{\otimes N}\pm\lvert 1 \rangle ^{\otimes N}}{\sqrt2}
$$

是正交态，但所有真子系统约化态都相同，因而所有两体边缘相同。

**证明。**

两态内积为零。对至少一个因子取偏迹时，
交叉项含 $\operatorname{Tr}(\lvert 0 \rangle \langle 1 \rvert )=0$，只留下两项对角混合，符号消失。

∎

所以“可用局部二体操作构成”与“由所有两体边缘决定”是不同命题。

<a id="statement-7-5"></a>

#### 定理 7.5（有限 POVM 的精确递归二叉化）

<a id="thm-tree"></a>

设 $E_1,\ldots,E_N\ge0$、$\sum_iE_i=I$ 作用于原 $d$ 维系统。
允许目标依赖的二结果仪器及记录反馈时，
存在有限二叉树，叶 $i$ 的完整操作恰为

$$
\rho\longmapsto \sqrt{E_i}\rho\sqrt{E_i}.
$$

平衡划分可使深度至多 $\lceil\log_2N\rceil$。

**证明。**

对树节点的叶集合 $S$ 定义 $E_S=\sum_{i\in S}E_i$，
根累计算子为 $\sqrt{E_S}=I$。
把 $S$ 分成非空 $T,U$，设 $\Pi_S$ 是 $E_S$ 的支撑投影，
$E_S^{+1/2}$ 是其平方根的 Moore–Penrose 逆。
定义

$$
L_T=\sqrt{E_T}\,E_S^{+1/2},\qquad
 L_U=\sqrt{E_U}\,E_S^{+1/2}.
$$

二者满足
$L_T^\dagger L_T+L_U^\dagger L_U=\Pi_S$。
将额外 Kraus 算子 $I-\Pi_S$ 归入任一结果，即得完整二结果仪器。
因 $0\le E_T,E_U\le E_S$，它们支撑包含于 $\Pi_S$，所以

$$
L_T\sqrt{E_S}=\sqrt{E_T}\Pi_S=\sqrt{E_T},
 \qquad (I-\Pi_S)\sqrt{E_S}=0.
$$

到达该节点时额外 Kraus 分支的概率严格为零。
递归归纳后，叶累计操作就是所需 Lüders 操作。
平衡分割的叶深度给对数上界。

∎

此构造与 Andersson–Oi 的二叉广义测量框架一致。（[12](#ref-andersson)）
二结果记录可以反复使用，原 $d$ 维系统和依节点改变的测量作用仍保留；
它没有把原系统编码成一个固定 qubit。

<a id="statement-7-6"></a>

#### 命题 7.6（可逆二态压缩的维数障碍）

若等距线性编码 $V:\mathbb{C}^d\to\mathbb{C}^2$ 存在，则 $d\le2$。

**证明。**

$V^\dagger V=I_d$ 使 $V$ 单射，故
$d=\operatorname{rank} V\le2$。

∎

据此必须区分二结果、二态、二元约束、二输入门和二体操作。
它们都出现数字二，却不具有同一个维数或信息合同。

<a id="sec-e8code"></a>

## 8. 从另一会话的 E8 胶合到一个具体二态编码

<a id="statement-8-1"></a>

#### 定义 8.1（承接的积分关系模型）

令

$$
V_0=\{u\in\mathbb{R}^5:\textstyle\sum_i u_i=0\},\qquad
 Q=V_0\cap\mathbb{Z}^5,\qquad L_0=Q\oplus Q,
$$

两因子取固定正交、等尺度标准内积。置

$$
\omega_k=e_1+\cdots+e_k-\frac{k}{5}\mathbf{1}.
$$

严格积分扩张指加法子群 $L$ 满足 $L_0\subsetneq L\subset V_0\oplus V_0$ 且
$\langle L,L\rangle\subset\mathbb{Z}$。

<a id="statement-8-2"></a>

#### 定理 8.2（既有 E8 选择结果及其假设）

固定上述标记时，严格积分扩张恰有

$$
\Gamma_+=L_0+\mathbb{Z}(\omega_1,\omega_2),\qquad
 \Gamma_-=L_0+\mathbb{Z}(\omega_1,\omega_3).
$$

二者均为 E8 根格，判别胶合线分别为

$$
C_s=\{(a,2s a):a\in\mathbb{F}_5\},\qquad s=\pm1.
$$

**证明。**

这是另一会话文稿的选择定理；重述其有限核心以固定依赖。（[8](#ref-selfe8)）
整数配对使 $L_0\subset L\subset L_0^*$。
$Q^*/Q\simeq\mathbb{F}_5$，判别配对为 $4aa'/5\bmod\mathbb{Z}$，
因此 $L/L_0$ 是 $\mathbb{F}_5^2$ 中对该配对全迷向的非零子空间。
非零 $(a,b)$ 必须满足 $a^2+b^2=0$，
所以 $a\ne0$ 且 $b/a=\pm2$。
两条直线均满足配对条件，二维全空间不满足，故只有所列两种。
指数为五，Gram 行列式为 $25/5^2=1$。
又 $5v\in L_0$ 为偶格且 $v^2$ 为整数，
故 $25v^2$ 偶迫使 $v^2$ 偶。
于是得到正定偶幺模秩八格；
调用经典秩八偶幺模格的唯一性，识别为 E8。
原稿亦给出根数及 ADE 识别的直接路线。

∎

这里的 $b=2sa$ 是两个五值变量之间的二元关系，
没有把其八维格载体变成三维，也没有仅凭五个模式选出 E8。

以下选 $\Gamma_+$，按标准根系构造取紧连通 E8 群 $G$、
$\mathfrak g=\mathfrak e_{8,\mathbb{C}}$ 和酉伴随载体 $\mathcal K=\mathfrak g$。
内积由紧实型的负 Killing 形式给出。
胶合类使

$$
\mathfrak g=\bigoplus_{j\in\mathbb{F}_5}\mathfrak g_j,\qquad
 \dim_\mathbb{C}(\mathfrak g_0,\ldots,\mathfrak g_4)=(48,50,50,50,50).
$$

局部子群与相位算子为

$$
H=\frac{\operatorname{SU}(5)\times\operatorname{SU}(5)}
          {\langle(\omega I,\omega^2I)\rangle},
 \qquad z=[(\omega I,I)]\in H,\qquad Z=\operatorname{Ad}(z),
$$

$$
Z|_{\mathfrak g_j}=\omega^jI,\qquad Z^5=I.
$$

这里 $z$ 属于 $H$ 的中心，E8 自身的中心仍平凡。
这些标准结构与 Yokota 的五分级构造一致。（[15](#ref-yokota)、[8](#ref-selfe8)）
以下根 $\operatorname{SU}(2)$ 与最大环面所用的标准紧群事实可参看作者讲义。（[16](#ref-conrad)）

<a id="statement-8-3"></a>

#### 定理 8.3（显式跨分级根双态码）

<a id="thm-rootcode"></a>

在 $\Gamma_+$ 中取

$$
\alpha=(\omega_1,\omega_2),\qquad
 \beta=(e_2-e_1,0).
$$

则

$$
W=\mathfrak g_\beta\oplus\mathfrak g_{\beta+\alpha}
 \subset\mathcal K
$$

是根子群 $j_\alpha:\operatorname{SU}(2)\hookrightarrow G$ 的标准二复维表示。
可选正交归一基 $e_0,e_1$，分别属于分级 $0,1$。

**证明。**

$\left\lVert \omega_1 \right\rVert ^2=4/5$、$\left\lVert \omega_2 \right\rVert ^2=6/5$，
故 $\alpha^2=\beta^2=2$，且
$(\alpha,\beta)=(\omega_1,e_2-e_1)=-1$。
所以 $\alpha+\beta\in\Gamma_+$ 且平方范数二，是根。
$\beta-\alpha$ 与 $\beta+2\alpha$ 的平方范数均为六，故不是根。
相应 $\alpha$ 根串只有 $\beta,\beta+\alpha$。
根 $\mathfrak{sl}_2$ 三元组在二者上的权为 $-1,+1$，
升降括号非零且不能继续，故为最高权一的不可约双态模。
紧实型使该表示酉；不同权空间正交，归一并调整相位得到标准 $\operatorname{SU}(2)$ 矩阵。
根子代数积分成群同态；$-I$ 在此双态模上作用为 $-I$，不是单位，
故其核平凡，得到嵌入。
最后 $\beta\in L_0$，$\beta+\alpha$ 属胶合类一，给出两荷。

∎

这一构造建立了局部 Bloch 三坐标与全局 E8 的明确连接。
根 $SU(2)$ 同样存在于其他半单 Lie 群；
E8 的选择仍由积分扩张条件承担。

<a id="statement-8-4"></a>

#### 定理 8.4（五相位给黄金平方门）

<a id="thm-squarebridge"></a>

在定理 [8.3](#thm-rootcode) 的码上，令 $P=\lvert e_1 \rangle \langle e_1 \rvert$，

$$
K_P=\zeta[(I-P)+\zeta P].
$$

则

$$
\boxed{\ Z^3|_W=\omega^2 K_P^2.\ }
$$

但 $Z$ 的任何幂在 $W$ 上都不与 $K_P$ 射影相等。

**证明。**

$Z|_W=\operatorname{diag}(1,\omega)$。
由 $\zeta^2=\omega^3$、$\zeta^4=\omega$，

$$
K_P^2=\operatorname{diag}(\omega^3,\omega),\qquad
 \omega^2K_P^2=\operatorname{diag}(1,\omega^3)=Z^3|_W.
$$

$K_P$ 两本征值之比为本原十次根 $\zeta$，
所以其射影阶为十；$Z^k|_W$ 的射影阶整除五。
射影相等将使阶数相等，矛盾。

∎

此等式只在指定码上成立，不能据此识别整个 $248$ 维算子。
$Z$ 的幂仍全部交换，没有自动供应第二相干投影或任意码态制备。

<a id="statement-8-5"></a>

#### 定理 8.5（编织相容锁定黄金重叠）

<a id="thm-braidangle"></a>

在复二维空间取不同秩一投影 $P,Q$，
$K_R=\zeta[I+(\zeta-1)R]$，$R=P,Q$。
则

$$
K_PK_QK_P=K_QK_PK_Q
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}(PQ)=\varphi^{-2}=x^2.
$$

取 $P=\operatorname{diag}(0,1)$，适当选择基矢相位后，

$$
Q=\begin{pmatrix}x&x\sqrt x\\x\sqrt x&x^2\end{pmatrix}.
$$

**证明。**

记 $s=\operatorname{Tr}(PQ)$。秩一性给 $PQP=sP$、$QPQ=sQ$，展开得

$$
K_PK_QK_P-K_QK_PK_Q
 =\zeta^3(\zeta-1)\bigl[\zeta+s(\zeta-1)^2\bigr](P-Q).
$$

$P\ne Q$ 且 $\zeta\ne1$，所以等式恰要求

$$
s=-\frac{\zeta}{(\zeta-1)^2}
  =\frac1{2-(\zeta+\zeta^{-1})}
  =\frac1{2+x}=x^2.
$$

其中 $\zeta+\zeta^{-1}=-x$、$(2+x)x^2=1$。
此时 $Q_{22}=x^2$、$Q_{11}=1-x^2=x$；
行列式零给非对角元模为 $x\sqrt x$，调基矢相位令其为正实数。

∎

这是项目 v15 编织展开的反向应用。（[3](#ref-repov15)）
条件链为：五分级确定平方门相位；选定十次相位分支并要求两门编织，
确定黄金混合角。后两个要求并未由格胶合自动提供。

<a id="sec-phase"></a>

## 9. 五种相位的读出：二元递归不能无代价增加信息

<a id="statement-9-1"></a>

#### 定理 9.1（同一二态码上的五相位单份极限）

<a id="thm-fivephase"></a>

在 $W$ 中取

$$
\lvert \psi_k \rangle =\frac{\lvert e_0 \rangle +\omega^k\lvert e_1 \rangle }{\sqrt2},
 \qquad k\in\mathbb{F}_5,
$$

未知 $k$ 等先验。
对一份输入，无论使用何种 POVM，正确识别五值的平均成功率至多 $2/5$，
且该上界可达。

**证明。**

对任意五结果 POVM $\{M_k\}$，
$\rho_k=\lvert \psi_k \rangle \langle \psi_k \rvert \le I_W$，故

$$
P_{\rm succ}=\frac15\sum_k\operatorname{Tr}(M_k\rho_k)
 \le\frac15\sum_k\operatorname{Tr} M_k=\frac{\dim W}{5}=\frac25.
$$

又 $\sum_{k=0}^4\omega^k=0$ 给
$\sum_k\rho_k=(5/2)I_W$。
因此 $M_k=(2/5)\rho_k$ 为 POVM，且每项正确概率为 $2/5$，
达到上界。

∎

<a id="statement-9-2"></a>

#### 推论 9.2（任意有限二元递归读出仍受同一上界约束）

对同一份未知输入，允许固定辅助态、任意反馈、任意有限层数的二元仪器，
仍不能超过定理 [9.1](#thm-fivephase) 的 $2/5$。

**证明。**

每个完整记录分支给出完全正映射 $\mathcal I_h$，
其效果为 $\mathcal I_h^*(I)$，对全部分支相加为单位。
按最终猜测值汇总这些效果，得到作用于原输入的五结果 POVM。
固定辅助态可吸收到该有效 POVM 中。
定理 [9.1](#thm-fivephase) 因而直接适用。

∎

若协议允许拒绝，必须将拒绝计入完整成功率；
只在成功子样本上重新归一化属于另一任务。
增加独立输入副本则确实改变来源资源，不属于上面“同一份输入”的结论。

在该码内，$Z$ 基读出对所有 $k$ 都为 $(1/2,1/2)$；
相位藏在

$$
r_x=\cos(2\pi k/5),\qquad r_y=\sin(2\pi k/5),\qquad r_z=0.
$$

合适的跨分级效果可以使不同相位的概率律不同，
但“概率律不同”不等于一次样本完美区分。
这正是复相干关系需要额外读口的具体实例。

<a id="statement-9-3"></a>

#### 命题 9.3（五维相干来源可以让二元递归读出五值）

若另从五个分级各供应一个正交单位向量 $u_j$，
并可制备

$$
\lvert \Phi_k \rangle =\frac1{\sqrt5}\sum_{j=0}^4\omega^{kj}\lvert u_j \rangle ,
$$

则五态正交，存在完美判别；
在其五维张成空间上的对应五结果 PVM，
可按定理 [7.5](#thm-tree) 编成深度至多三的二元测量树。

**证明。**

$\langle\Phi_\ell,\Phi_k\rangle  =\frac15\sum_j\omega^{(k-\ell)j}=\delta_{k\ell}$。
正交投影测量完美区分，二叉构造适用。

∎

在整个 $\mathcal K$ 上，可把正交补并入任一结果以补全测量；
所列探针在该补空间中质量为零。
这里二元的是每次记录，五维的是输入相干来源。
它把用户的递归读出图景落实为可行构造，同时保留必要的信息载体。
旧 E8 文稿已经给出更一般的带权最优式
$P_{\rm opt}=\frac15(\sum_j\sqrt{w_j})^2$；
本节的增量是把二态界与递归仪器编译放到同一操作合同中。（[8](#ref-selfe8)）

<a id="statement-9-4"></a>

#### 命题 9.4（静态面相容仍是全局约束）

在有限二维复形上，给定平坦的 $\operatorname{PU}(5)^2$ 边数据，
任选其 $H$ 提升 $h_e$，反向边取逆，
令每个有序面边界积为 $z^{\eta_f}$。
用中心边相位 $b_e\in\mathbb{F}_5$ 替换 $h_e\mapsto z^{b_e}h_e$ 后，

$$
\eta\longmapsto\eta+\delta b.
$$

全部面能同时闭合，恰当且仅当 $[\eta]=0\in H^2(B;\mathbb{F}_5)$。

**证明。**

新增相位属于中心，移至有序边界积前端时，
指数按边在面边界中的有符号出现次数相加，恰为 $\delta b$。
二维复形中二余链自动为余循环；
存在 $\delta b=-\eta$ 恰等价于上同调类为零。

∎

这是旧 E8 稿全局提升定理的保留形式。（[8](#ref-selfe8)）
它表明每条边都可提升，不保证所有面边界同时闭合；
面平坦性仍允许非收缩回路具有非平凡 holonomy。
相位缺陷的实际读取还取决于允许的探针和效果；
二态探针的一次读出并未自动取得旧稿的五维完美相位测量。

<a id="sec-control"></a>

## 10. 固定黄金门如何生成 E8，及其不能替代的控制

<a id="statement-10-1"></a>

#### 引理 10.1（一对黄金门的 SU(2) 密度）

<a id="lem-su2dense"></a>

对定理 [8.5](#thm-braidangle) 中的 $P,Q$，

$$
\widehat K_P=e^{-9\pi i/10}K_P,\qquad
 \widehat K_Q=e^{-9\pi i/10}K_Q
$$

属于 $\operatorname{SU}(2)$，二十次幂为单位，且

$$
\overline{\langle\widehat K_P,\widehat K_Q\rangle}=\operatorname{SU}(2).
$$

**证明。**

本征值为 $e^{-3\pi i/10},e^{3\pi i/10}$，故行列式一且二十次幂为单位。
给出项目 v15 密度结论的一条纸面论证。（[3](#ref-repov15)）
令 $R_P=2P-I=\mathbf a\cdot\boldsymbol\sigma$、
$R_Q=2Q-I=\mathbf b\cdot\boldsymbol\sigma$。
因 $0<\operatorname{Tr}(PQ)=x^2<1$，$\mathbf a,\mathbf b$ 不平行。
两个归一化门五次幂的乘积为 $-R_PR_Q$，其迹为

$$
2-4x^2=-4+2\sqrt5.
$$

若它有限阶，两个本征值是互逆单位根，
其迹的所有代数共轭都形如 $\lambda+\lambda^{-1}$，位于 $[-2,2]$。
但上述迹的共轭为 $-4-2\sqrt5<-2$，矛盾。
因此其幂在自身的圆子群中稠密；该圆的轴是 $\mathbf a\times\mathbf b$。
以 $\widehat K_P$ 共轭该圆，相当于绕 $\mathbf a$ 旋转角 $3\pi/5$
（方向约定可取其负），把此垂直轴送到不平行轴。
两个圆的 Lie 方向及其括号张成全部 $\mathfrak{su}(2)$。
生成闭群于是具有完整 Lie 代数，而 $\operatorname{SU}(2)$ 连通，故闭群为全部 $\operatorname{SU}(2)$。

∎

<a id="statement-10-2"></a>

#### 定理 10.2（十六个固定黄金门的条件 E8 普适性）

<a id="thm-e8univ"></a>

选 E8 的八个简单根及对应根嵌入
$j_i:\operatorname{SU}(2)\hookrightarrow G$，$1\le i\le8$。
若明确供应下列十六个可调用门，

$$
\mathcal S=\{j_i(\widehat K_P),j_i(\widehat K_Q):1\le i\le8\},
$$

则

$$
\boxed{\ \overline{\langle\mathcal S\rangle}=G=E_{8,c}.\ }
$$

只用正向字也有相同闭包。

**证明。**

生成闭群 $C$ 由引理 [10.1](#lem-su2dense) 包含每个根 $\operatorname{SU}(2)$。
因此 $\operatorname{Lie}(C)_\mathbb{C}$ 含全部简单根的 Chevalley 生成元 $E_i,F_i,H_i$，
它们按标准根系构造生成 $\mathfrak e_{8,\mathbb{C}}$。
故 $\operatorname{Lie}(C)=\operatorname{Lie}(G)$；$G$ 连通，得到 $C=G$。
每个生成元的逆等于十九次正向调用，所以正向菜单生成同一个子群。

∎

这里供应的是具体 $\operatorname{SU}(2)$ 提升及其 E8 像；
在一个二态码上的整体相位等价，不表示整个伴随载体上该相位可免费删除。

这是一种“固定黄金局部形状，加八个根地址和两种相干投影”的有限菜单。
未证明十六最小，也未给综合算法或误差成本。
单个固定矩阵重复调用只产生交换的循环闭包，
不能因此取得非交换 E8。
一个局部原语在不同地址的部署能力，正如 NAND 的不同布线，是通用性合同的一部分。

<a id="statement-10-3"></a>

#### 命题 10.3（离散近似生成不等于精确连续综合）

固定有限门菜单的全部有限字至多可数，因而不能精确覆盖不可数的 E8。

**证明。**

每个固定字长只有有限个字，对全部自然数字长取并仍可数。
非离散正维紧 Lie 群含坐标开集，不可数。

∎

旧 E8 稿的统一精确有限词长结论使用可调实参数连续菜单，
不由定理 [10.2](#thm-e8univ) 继承。
在 $\mathcal K$ 上，所得控制群实维数为 $248$；
它保存 E8 Lie 括号等结构，不是实维数 $248^2-1=61503$ 的 $\operatorname{SU}(248)$。

<a id="statement-10-4"></a>

#### 定理 10.4（原生 PU(13) 与紧 E8 的双向连续同态障碍）

<a id="thm-rankobstruction"></a>

任意连续群同态

$$
\operatorname{PU}(13)\longrightarrow E_{8,c},\qquad
 E_{8,c}\longrightarrow\operatorname{PU}(13)
$$

均平凡。

**证明。**

连续 Lie 群同态光滑，导数的核为 Lie 理想。
两端 Lie 代数均实单，非零导数必须单射。
第一方向会将 $\mathfrak{su}(13)$ 的十二维 Cartan 阿贝尔子代数嵌入紧 $\mathfrak e_8$。
紧 Lie 代数的阿贝尔子代数包含于某最大环面的 Lie 代数，后者维数至多八，矛盾。
第二方向则要求 $248$ 维 Lie 代数注入
$\dim\mathfrak{su}(13)=168$ 的空间，同样不可能。
两个源群连通，导数为零使整个像为单位。

∎

<a id="statement-10-5"></a>

#### 推论 10.5（固定无泄漏编码也不能绕过秩障碍）

在 E8 的任意有限维酉表示中，
若所供逻辑门全部来自 E8 并保持某个固定十三维码，
它们在该码上的射影闭包不能为完整 $\operatorname{PU}(13)$。

**证明。**

保持该码的控制闭包是紧子群 $H\subset E8$。
若其射影限制像稠密于 $\operatorname{PU}(13)$，紧性使像等于该群。
$H$ 的分支群有限；其单位分支的像是连通目标中的有限指数闭子群，
故仍为整个 $\operatorname{PU}(13)$，进而 $\operatorname{Lie}(H)$ 满射 $\mathfrak{su}(13)$。
在紧 Lie 代数中，用不变正定内积取该满射核的正交补，
得到与 $\mathfrak{su}(13)$ 同构的理想，因此把十二维 Cartan 嵌入紧 $\mathfrak e_8$，
再次矛盾。

∎

该结论不排除把 $\mathbb{C}^{13}$ 作为抽象线性子空间嵌入 $\mathbb{C}^{248}$，
也不排除换编码、加入测量资源或扩大控制群。
它精确排除同一个固定码上、纯 E8 控制下对完整原生 $\operatorname{PU}(13)$ 的无泄漏等同。

<a id="sec-latest"></a>

## 11. 最新项目结果如何约束这套理论

<a id="sec-11-1"></a>

### 11.1. 全域平方相容与有限标定之间有严格差别

沿用项目原生 $\mathcal{H}_{13}$、种子 $v=e_{00100}$、七个门 $K_j$、
全部有限正向字 $\mathsf W$ 与全部 $1024$ 个终端标签。
合法十三基坐标的平方记为 $q_w(\psi)$，非法标签取零。
固定 $u=e_{00000}$，$q_u,q_v$ 始终指这两个基探测器的坐标。
未知响应 $P_w$ 只先要求连续、共同相位不变、非负、完整归一、
基底点质量标定及当前射线的指定终端充分性。
记

$$
\mathcal D(P)=\sup_{\left\lVert \psi \right\rVert =1,w}|P_w(\psi)-q_w(\psi)|,
$$

$$
\mathcal R(P)=\sup_{p,f,w}
 \left|a_3+x^2a_1-a_0-x^2a_2\right|,
 \qquad a_t=P_w(K_fK_0^tK_pv).
$$

这里两种上确界都是全域量词，不是已检查样本集的最大值。

<a id="statement-11-1"></a>

#### 定理 11.1（项目新增平方根稳定性的锐性）

在上述同一响应类中，对每个 $0<\theta\le1$ 存在响应 $P^\theta$，满足

$$
\mathcal R(P^\theta)\le\frac{52}{243}\theta^2,\qquad
 \mathcal D(P^\theta)\ge\frac{\theta}{16}.
$$

因此不能有统一的 $o(\sqrt\varepsilon)$ 误差模量，
把 $\mathcal R(P)\le\varepsilon$ 推为更小阶的全域 Born 偏差。

**证明。**

这是续卷 II 定理 96.2 与推论 96.3；以下重述构造的关键估计。（[2](#ref-repoborn)）
令 $t=\theta/16$、$d=t^2/(1+t^2)$，
把 $u=e_{00000},v$ 两个探测器旋转为
$(u+tv)/\sqrt{1+t^2}$ 与 $(-tu+v)/\sqrt{1+t^2}$，其余不动。
令对应二次读数为 $Q_\beta$，并置

$$
P^\theta_\beta=
 \frac{(Q_\beta-d)_+}{\sum_\gamma(Q_\gamma-d)_+}.
$$

非法标签仍取零。分母至少 $1-13d\ge243/256$，
所以响应连续、非负且归一；阈值使所有原基点再次精确给点质量。
若 $A=\sum_\beta\min(Q_\beta,d)$，
则各坐标差满足
$|P^\theta_\beta-Q_\beta|\le A/(1-A)\le13\theta^2/243$。
原门具有两谱式 $K_0=\zeta[(I-\Pi)+\zeta\Pi]$，$\Pi$ 为投影。
因此去掉共同相位后，任意二次读数沿
$K_fK_0^tK_pv$ 是序列 $1,\zeta^t,\zeta^{-t}$ 的线性组合。
它们都被

$$
z^3-x^2z^2+x^2z-1=(z-1)(z-\zeta)(z-\zeta^{-1})
$$

消去，故二次 $Q$ 精确满足四时关系。系数绝对值和
$2+2x^2<4$，得到所列残差上界。
在 $(u+v)/\sqrt2$ 上，直接展开两个旋转坐标并归一化得到

$$
P^\theta_u=\frac12+\frac{t}{1-t^2},
$$

故偏差至少 $t=\theta/16$。
取 $\theta=\sqrt\varepsilon$，即可排除统一更小阶模量。

∎

这项新进展使“近似相融”的量级有了纸面界。
旋转探测器在此仅用于构造一个数学响应，
没有因此新增实际原生制备或仪器。

<a id="statement-11-2"></a>

#### 定理 11.2（项目新增有限完整律核对的固定间隙）

<a id="thm-finitechecks"></a>

对任意有限射线查询集及有限原生四时上下文集，
存在同一原源上的连续归一响应 $P$：
它在全部这些点的完整终端律上与 $q$ 相同，
精确保留基标定，并具有某个有限多项式次数与有限预测秩；
但在另一个实际有限原生上下文上满足

$$
\mathcal D(P)>\frac1{32},\qquad
 \mathcal R(P)>\frac1{32}.
$$

次数和见证字长可以依赖查询集，此类中没有共同上界。

**证明。**

这是续卷 II 定理 97.2 的终端部分；给出其有限分离论证。（[2](#ref-repoborn)）
原门公式给 $K_1v=\zeta(Av+Be_{10100})$，
$A=1+(\zeta-1)x$、$B=(\zeta-1)x\sqrt x$，
且 $|A|^2=x^2>0$、$|B|^2=x>0$。
$K_0$ 在这两个分量上的相位比为 $\zeta$，
故 $\eta_t=[K_0^tK_1v]$，$0\le t\le3$，两两不同。
把全部有限查询及其四时点并成有限集 $F$。
在数学酉群中，条件
$q_u(U\eta_3)q_v(U\eta_3)>1/8$ 给非空开集；
非空性可由把 $\eta_3$ 送到 $[(u+v)/\sqrt2]$ 得到，此时乘积为 $1/4$。
有限个条件 $U\eta_t\in F$ 各只有闭的空内点集合。
去掉它们仍有非空开集。
原生门在 $\operatorname{PU}(13)$ 中的密度因此给一个实际有限字 $f_*$，
使 $z_t=[K_{f_*}K_0^tK_1v]$ 全部避开 $F$，且所列乘积大于 $1/8$。
这里复用的是项目 §77.2 的原生密度，不是把闭包酉当作精确字。

令 $S=F\cup\{z_0,z_1,z_2\}$，为其射线选单位代表，定义

$$
g_m([\psi])=\prod_{\xi\in S}
 (1-|\langle\xi,\psi\rangle|^{2m}).
$$

它在 $S$ 上为零，在全域处于 $[0,1]$，
而因 $z_3\notin S$，有 $g_m(z_3)\to1$。
选有限 $m$ 使 $g_m(z_3)>1/2$，再令

$$
h=\tfrac12q_uq_vg_m,\qquad
 P_u=q_u+h,\quad P_v=q_v-h,\quad P_w=q_w\ (w\ne u,v).
$$

$0\le h\le q_uq_v/2$ 保证正性与严格支撑保持；
两个修正相消，故全 $1024$ 项归一不变。
基点上 $q_uq_v=0$，给精确标定；$F$ 上 $h=0$，给全部查询通过。
前三个四时点修正为零，第四个大于
$\frac12\cdot\frac18\cdot\frac12=1/32$。
$q$ 的四时差为零，因此该真实上下文上的残差和终端偏差都超过 $1/32$。

最后，$h$ 在单位球上可齐次化为双次数
$(k,k)$ 的多项式，$k=m|S|+2$。
酉拉回保持该有限维函数空间，
其复维数为 $\binom{12+k}{k}^2$，
因此由实际接续函数的张成得到有限预测秩。
所有响应仍只依赖当前射线，所以保留指定终端充分性。

∎

原文进一步保留旧四维码和 Alice 行边缘，
并给出分别满足不同记录接口的两个完整概率补全。
这些加强及其准确来源域见 §97；
不能把两个补全并成一个同时满足所有全域接口的模型。

这项结果不排除加入共同次数界、共同连续模或独立结构证明后的有限认证。
它说明本稿定理 [4.2](#thm-frameborn) 的“每个正交框架”，
以及定理 [5.2](#thm-effectborn) 的“全部效果”，
不能靠任意有限次成功核对自动取得。

<a id="sec-11-2"></a>

### 11.2. 关系的不确定性在联合支撑中

<a id="statement-11-3"></a>

#### 定理 11.3（相同通道边际范围，完全不同的恢复能力）

<a id="thm-jointnoise"></a>

令来源为非负整数对 $(m,n)\in\mathbb{N}^2$，此处 $\mathbb{N}=\{0,1,\ldots\}$，
$g=m+\sqrt2\,n$。
给定 $\varepsilon>0$，考虑联合读数

$$
Y_\parallel=(g,g)+\varepsilon(t,t),\qquad
 Y_\perp=(g,g)+\varepsilon(t,-t),\qquad |t|\le1.
$$

两种误差支撑同为一维，且每个坐标的误差范围相同。
垂直支撑时可以精确恢复全部来源；
平行支撑时，任何固定有限值的额外来源标签都不能保证全部来源的精确恢复。

**证明。**

垂直支撑中 $(Y_1+Y_2)/2=g$ 精确。
若 $m+\sqrt2n=m'+\sqrt2n'$，无理性给 $m=m',n=n'$。

平行支撑中两个读口给同一个带闭误差 $\varepsilon$ 的标量。
假定额外标签有 $M$ 个值且足以统一恢复。
则同标签下任意两个不同 $g$ 必须距离严格大于 $2\varepsilon$，
否则两个允许观测区间共享记录。
对 $0\le m,n\le L$，共有 $(L+1)^2$ 个不同来源，
但它们的 $g$ 全在长度 $(1+\sqrt2)L$ 的区间内。
每个标签至多容纳
$1+(1+\sqrt2)L/(2\varepsilon)$ 个这样的分离点，
故必须

$$
(L+1)^2\le
 M\left(1+\frac{(1+\sqrt2)L}{2\varepsilon}\right).
$$

固定 $M,\varepsilon$ 而令整数 $L$ 增大，左侧二次增长、右侧线性增长，矛盾。

∎

这抽取了项目类型化残差余循环文本 §14 的联合支撑机制；
原文把它放在实际三状态路径源和终点接口中。（[6](#ref-repococycle)）
它支持“关系也需要建模”的判断。
但这仍是经典精确获取与噪声合同的算术定理，
没有单独推出复数、Born 规则或三维物理空间。

<a id="sec-11-3"></a>

### 11.3. 二元 incidence 仍可能有全局赋值障碍

<a id="statement-11-4"></a>

#### 定理 11.4（奇数上下文与双重 incidence 的占据障碍）

设有有限模式集与奇数个上下文，每个模式恰属于两个不同上下文。
若每模式赋自然数 $v_e$，同一模式的值与上下文无关，
且每个上下文占据总和同为 $n$，则 $n$ 必为偶数。

**证明。**

设上下文个数为奇数 $r$。对全部上下文求和，每模式被数两次，故

$$
rn=2\sum_e v_e.
$$

右侧为偶数，而 $r$ 奇，得到 $n$ 偶。

∎

新源文件
`EighteenModeBosonicAssignmentParity.lean`
使用 Kurzyński 的十八模式、九上下文 incidence 表，
并给出赋值存在当且仅当 $n$ 偶的声明。（[7](#ref-repoks)、[17](#ref-kurzynski)）
必要性就是上述双计数。
其表中包含遍历全部九上下文的环

$$
1\longrightarrow2\longrightarrow8\longrightarrow4
 \longrightarrow7\longrightarrow3\longrightarrow9
 \longrightarrow5\longrightarrow6\longrightarrow1.
$$

当 $n=2m$ 时，只在该环的模式上赋值 $m$，其余赋零，
每上下文恰接两条环边，给充分性。
本轮核对的是源声明与纸面推理，没有重新运行 Lean。
该结果排除某种上下文无关的全局赋值，
不排除奇数粒子量子态存在。
它也没有说图用二元端点编码后就失去全局约束。

<a id="sec-synthesis"></a>

## 12. 一套可继续发展的条件理论

<a id="statement-12-1"></a>

#### 定义 12.1（本轮的 AURIC 观测单元）

一份二态观测单元的数据为

$$
\mathcal A=(W,P,Q,K_P,K_Q,\mathscr E,\mathscr I),
$$

其中 $W\simeq\mathbb{C}^2$，$P,Q$ 为不同秩一投影，
$\operatorname{Tr}(PQ)=x^2$，$K_R=\zeta[I+(\zeta-1)R]$；
$\mathscr E$ 是实际效果族，$\mathscr I$ 是可调用仪器族。
必须另写明可制备态、可部署地址、记录权限和泄漏处理。
这一定义保留黄金门的相容代数，没有默认全部效果或全部仪器均能从原门免费取得。

<a id="statement-12-2"></a>

#### 定理 12.2（条件相容模型的存在与联合结论）

<a id="thm-combined"></a>

以下数据可以在同一数学模型中同时成立：

1. 严格积分扩张 $\Gamma_+$ 及其紧 E8 伴随载体；

2. 定理 [8.3](#thm-rootcode) 的跨分级双态码，
在其底层实四维空间上取反对易三操作；

3. 该码上的正效果、满足 (E) 的权重以及指定量子仪器；

4. 黄金投影对和八个根地址上的十六门菜单；

5. 以门字和实际记录组成的静态相容观察网络。

在该模型中，局部复二态结构、Born 形式、相对门读出、
二叉测量递归、五相位平方门桥梁与紧 E8 近似控制同时成立。

**证明。**

先取 $\Gamma_+$ 的标准 E8 构造。
定理 [8.3](#thm-rootcode) 给具体 $W$。
在 $W$ 上选标准 Pauli 三操作并实化，
满足定理 [4.6](#thm-clifford)，复结构与已有编码一致。
取全部效果及任一密度矩阵的迹权重，满足 (E)，
相应 Lüders 仪器和固定记录扩张给出非空操作模型。
选定定理 [8.5](#thm-braidangle) 的 $P,Q$，
并把所列十六门明确列入权限。
此前各定理逐项适用：相对读出由共同换框，
递归测量由二叉树，
五相位关系由码上分级，
E8 控制由根子群生成。
任意有限自适应记录由第 [5](#sec-effects) 节形成相容树；
如使用有向边网络，必须保存有序组合和面相容条件。
这些构造没有要求一个固定二态码在全部 E8 控制下保持不变；
离码分支按前述泄漏规则完整保留。具体地，记编码等距为
$\iota:W\to\mathcal K$。对码上任意 POVM $\{E_i\}$，取全空间 Kraus 算子

$$
L_i=\iota\sqrt{E_i}\,\iota^\dagger,\qquad
 L_\perp=I-\iota\iota^\dagger.
$$

它们满足 $\sum_iL_i^\dagger L_i+L_\perp^\dagger L_\perp=I_{\mathcal K}$，
在原码上恢复同一 Lüders 操作，在离码后仍有定义并保留补空间结果。

∎

这给出的是**有模型、有映射、有反例边界的条件统一**。
它没有把所有资源都从一条形状公理中推出来。
特别是，原 FIB 的三个对易占据读口与反对易三操作之间，
仍缺一条来自原菜单、保留全部记录的物理或操作推导。

| 欲解释的结构 | 本稿给出的严格来源 | 尚不能省略的输入 |
| --- | --- | --- |
| 相对观察 | $B^\dagger A$ 的共同左作用商 | 同一内积、兼容读口、种子与权限 |
| 三轴 Bloch 坐标 | $\mathbb{C} P^1\simeq S^2$ | 二复维；与三物理空间维无自动等同 |
| 复结构 $i$ | $J=ABC$ | 实内积、三归一化操作的反对易 |
| 平方概率 | 全框架相容或全效果可加 | 全域量词、概率标定及效果空间 |
| 测后经典记录 | 仪器、等距扩张与条件化 | 具体记录读口及测后规则 |
| 多元关系二元化 | 联合见证或二叉仪器 | 辅助域、原维数、控制和记录资源 |
| 黄金门关系 | 固定十次相位及编织等式 | 第二相干投影与相位分支 |
| E8 选择与控制 | 严格积分胶合及根子群生成 | 格内积、整性、地址和实际调用 |
| 有限精度认证 | 全域误差界与来源限制 | 共同正则性或独立结构证明 |

下一步最有辨识力的数学任务是：
在原五模式或原十三维菜单中，明确构造一组保留来源与档案的读口转换，
证明它实际供应的是哪一类反对易或全效果相容结构；
随后再说明这些转换如何接到 E8 根编码。
若只能取得有限概率核对，应同时给共同次数、连续模或其他可证覆盖条件，
否则定理 [11.2](#thm-finitechecks) 的反模型仍适用。

因此本轮可成立的核心判断是：
*二元读出在全局相融约束下可以组织出复二态几何；
复二态单元可以作为 E8 内部的具体根编码；
递归组织保留并传递联合关系，却不会自动消除载体维数、相干资源与全域一致性的要求。*

<a id="sec-bibliography"></a>

## 文献与固定项目来源

<a id="ref-repohead"></a>

**[1]**

The Omega Institute.
*trureturing*，固定提交
`6f7aa75a805fc506ba97bf40728c48da8d90fd56`，
2026-10-30 20:05:34（Asia/Singapore），PR #24193。
[提交永久链接](https://github.com/the-omega-institute/trureturing/commit/6f7aa75a805fc506ba97bf40728c48da8d90fd56)。
本稿使用完整提交树差分及固定 blob 核对，不将来源文本等同于本轮内核认证。

<a id="ref-repoborn"></a>

**[2]**

The Omega Institute.
*AURIC FIB ATOM 与量子基本原则：原生预测秩与终端响应（续卷 II）*。
本轮重点为 §77.1–77.2、§96–97。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。
当前 blob：`5a1a0de6190046c87b496fcc481c62babbce07de`。

<a id="ref-repov15"></a>

**[3]**

The Omega Institute.
*AURIC 黄金门：NAND 式通用性与算术边界，v15*，
命题 3.2、定理 4.3 及其二维门模型。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)。
本轮该文件相对 v27 未变。

<a id="ref-repofib"></a>

**[4]**

The Omega Institute.
*FIB-ATOM 金字塔：基础公式、原子关系与同源接续总表*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
使用五合法模式及占据均值，不从模式计数预设量子物理。

<a id="ref-repov24"></a>

**[5]**

The Omega Institute.
*AURIC：两基态、三通道、相位手性与递归平方律，v24*。
[本轮快照中的旧稿归档](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
包含反对易三操作与复结构线索；归档不构成新的独立验证。

<a id="ref-repococycle"></a>

**[6]**

The Omega Institute.
*Recursive Relational Observation: Typed Residual Cocycle Reconstruction*，
§§12–21，特别是命题 14.1。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)。

<a id="ref-repoks"></a>

**[7]**

The Omega Institute.
*EighteenModeBosonicAssignmentParity.lean*。
[固定源文件](https://github.com/the-omega-institute/trureturing/blob/6f7aa75a805fc506ba97bf40728c48da8d90fd56/D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.lean)。
声明 `result : claim`，私有引理
`incidence_double_count`、`assignment_even` 与
`even_assignment`；本轮未运行 Lean。

<a id="ref-selfe8"></a>

**[8]**

此前另一会话研究稿。
*AURIC–E8 相容扩张与观察理论*，2026-10-30，
源文件 `auric_e8_formal_theory_zh.tex`，
固定项目快照 `66259f03d60716f143cd59c7644dadcb67cc1b73`。
[已交付源文稿](https://chatgpt.com/library?file_id=libfile_3b99ecbfb700819184b080371f6684fc&account_id=personal)。
本文完整读取其原文；它属于同一研究的先行推导，不是外部独立确认。

<a id="ref-selfv27"></a>

**[9]**

此前研究稿。
*AURIC：刚性镜像、复相位与原生黄金门*，v27.0，2026-10-30。
[已交付源文稿](https://chatgpt.com/library?file_id=libfile_f039d2ae37cc8191a1711625e27cca2c&account_id=personal)。
本轮承接其 Gram 闭环、Bargmann 手性与共同换框结果。

<a id="ref-busch"></a>

**[10]**

Paul Busch.
*Quantum states and generalized observables: a simple proof of Gleason's theorem*.
2003.
[arXiv:quant-ph/9909073v3](https://arxiv.org/html/quant-ph/9909073v3)。
全效果正权重及可加性刻画密度算子，包含二维情形。

<a id="ref-krumm"></a>

**[11]**

Marius Krumm and Markus P. Müller.
*Quantum computation is the unique reversible circuit model for which bits are balls*.
npj Quantum Information 5, 7 (2019).
[arXiv:1804.05736](https://arxiv.org/pdf/1804.05736)，§II 与定理 1。
本文只引用列明复合框架下的维数条件推论。

<a id="ref-andersson"></a>

**[12]**

Erika Andersson and Daniel K. L. Oi.
*Binary search trees for generalized measurement*.
[arXiv:0712.2665v1](https://arxiv.org/html/0712.2665v1)，§§III–IV。
有限 POVM 的递归二结果实现及测后操作自由度。

<a id="ref-brougham"></a>

**[13]**

Thomas Brougham and Erika Andersson.
*Estimating the expectation values of spin 1/2 observables with finite resources*.
Physical Review A 76, 052313 (2007).
[arXiv:0708.3375](https://arxiv.org/pdf/0708.3375)，§VI 与附录式 (A4)。

<a id="ref-samaras"></a>

**[14]**

Nikolaos Samaras and Kostas Stergiou.
*Binary Encodings of Non-binary Constraint Satisfaction Problems:
Algorithms and Experimental Results*. Journal of Artificial Intelligence Research, 2005.
[隐藏变量编码原文](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume24/samaras05a-html/node8.html)。

<a id="ref-yokota"></a>

**[15]**

Ichiro Yokota.
*Exceptional Lie groups*. 2009.
[arXiv:0902.0431v1](https://arxiv.org/html/0902.0431v1)。
§5.12，定理 5.12.1、5.12.5，给 E8 五分级和
$(SU(5)\times SU(5))/\mathbb{Z}_5$ 子群；§5.9 给中心平凡。

<a id="ref-conrad"></a>

**[16]**

Brian Conrad, lectures; Aaron Landesman, notes.
*Math 210C. Compact Lie Groups*. Stanford University, 2018.
[作者讲义](https://math.stanford.edu/~conrad/210CPage/handouts/lie_groups_notes.pdf)。
用于标准根 $SU(2)$、紧 Lie 代数、最大环面和秩的背景。
本文的根码与控制应用另给纸面证明。

<a id="ref-kurzynski"></a>

**[17]**

 Paweł Kurzyński.
*Contextuality of Identical Particles*.
Physical Review A 95, 012133 (2017).
[arXiv:1609.01250](https://arxiv.org/abs/1609.01250)。
十八模式上下文占据模型的原始来源；本稿的偶数充要声明按当前项目源文件定位。
