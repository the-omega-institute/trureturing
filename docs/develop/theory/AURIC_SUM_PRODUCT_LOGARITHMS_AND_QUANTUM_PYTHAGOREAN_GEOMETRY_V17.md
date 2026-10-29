<a id="auric-v17"></a>

# 加乘电路、对数与量子勾股

**AURIC 五模式的三角几何与黄金门**

**定义、定理与完整纸面证明**

**v17.0 · 2026 年 10 月 30 日 · Asia/Singapore**

> **转换说明（编者）。** 本文完整转换作者提供的同名 XeLaTeX 稿件；陈述沿用每节共享编号，公式保留全局编号 (1)–(3)，引文与固定项目链接均保留。正文的“本轮”“最新”、固定提交审计、历史及推进报告归属于原作者，本次转换不重新认证这些报告或主张数学首创。正文保留全部纸面证明及其前提；本次仅作内容与本地排版核对，不主张 Lean、数学数值、CAS、模拟、门搜索、硬件或原生托管 MathJax 认证。

<a id="sec-abstract"></a>

## 摘要

本文把“加法、乘法、指数、对数、三角形与量子门”的联系落实为同一五模式来源上的若干精确恒等式。对数把正权电路的乘法变成加法，把加法变成 log-sum-exp；五模式底面的唯一仿射回路产生隐藏关联参数，对数优势比是其 Fisher 对偶坐标。最大熵完成满足 KL 勾股恒等式，概率平方根实现 Fisher 球面几何，Gram 行列式把整体体积写成三角形或四面体体积平方之和。在明确给定的条件两比特纯态中，四角振幅比的复对数由经典关联与相位两部分组成，纠缠强度恰分解为双曲正弦平方与正弦平方之和。最后，从 Fibonacci 融合的加乘规则推得黄金归一三角，再通过相邻投影的编织相容性确定相对相位及门的转移权重。各项定理注明欧氏尺子、概率标定、Hilbert 与张量结构等前提；它们构成可继续研究的桥梁，不把不同层次的“正交”混为一谈。

**证明与来源身份。**本文给出经典工具在项目指定对象上的自足证明、已有项目结论的核对以及本轮的综合推论。不主张发明指数族、KL 投影、Fisher 几何、Cauchy--Binet、concurrence 或 Fibonacci 任意子理论。未运行 Lean 构建、数学数值程序、CAS、模拟或门序列搜索。

## 目录

1. [最新项目进展与本轮的证明目标](#sec-1)
2. [加法、乘法与对数电路](#sec-2)
3. [五个模式、唯一四角关系与十个三角形](#sec-3)
4. [三读出、隐藏关联与指数族](#sec-4)
5. [信息勾股：三个可见误差与一个隐藏关联](#sec-5)
6. [三个稳定读出的正交性究竟在哪里](#sec-6)
7. [三角面积平方为何会相加](#sec-7)
8. [从加乘到量子电路：直和、张量积与平方](#sec-8)
9. [核心定理：对数关联与相位的量子勾股](#sec-9)
10. [量子相对熵把三层缺失精确相加](#sec-10)
11. [递归观测如何在复对数中累加关系](#sec-11)
12. [黄金门：融合加乘、勾股三角与编织相位](#sec-12)
13. [指数门、谱与记录后的概率电路](#sec-13)
14. [本轮形成的理论与可检验的后续问题](#sec-14)

[文献与固定项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 最新项目进展与本轮的证明目标

本轮只读固定的 `dev` 提交为
`d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a`。
提交时间为 2026-10-30 01:43:03（Asia/Singapore），合并 #23783，主题为区分近似 Walsh 范数与合法取得。相对 v16 的 `f22ccafb…`，理论目录有六个路径变化，其中一新增、五修改；当前理论树含 1006 个文件。本轮核验了二十份当前源码与五份前版源码的 Git blob，按主题阅读有关章节。这是有范围的研究审计，不是对整个仓库的形式化认证。

真正最新且与本题直接相关的两项进展是：

1. [《真实切面恢复》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md)新增 §§18--20：指定实际一阶来源的近似 Walsh $\ell^1$ 范数可指数大，同时整个允许的一阶类仍有两条常量探测词的合法取得方法；已知目标公式还有 $O(H)$ 计数器求值。**一个谱表示的系数范数，不等于所有电路或实际取得协议的成本。**
2. [《统一联合律桥》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)新增 §2：给定完整实际过去的下一探针校准律，才能由塔式递归推出条件乘积律。相同单次边缘不提供独立乘法。它还区分完整概率律的可识别性与一份有限记录对隐藏来源的零误差识别。

本题的主要数学基础已经出现在未变更的《金字塔基础公式》、[《读口与记录三角形》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md)、[《关系三角形与反演精度》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_MOMENT_TRIANGLES_AND_INVERSE_PRECISION.md)及[《概率、相位运输与完整回路》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)中。前稿 v14、v15 的仓库转录是研究连续性，不是额外独立验证。本文进一步把这些材料组织成一条从加乘电路到复四角关系、再到黄金门的证明链。

<a id="statement-1-1"></a>

#### 定义 1.1（三层结构）

组合层给出合法模式、可组合关系与电路；统计层另给实际联合律、记录、条件化与误差尺度；相干层另给复 Hilbert 空间、张量分割、相位和测量仪器。本文在每层明确所用对象，再证明跨层映射保持哪些运算。

“静态”在此表示研究完整相容关系及其不同消元顺序。电路的依赖偏序、条件概率的完整历史以及非交换算子的次序仍须保留；它们不要求一个额外的绝对外部时钟。

<a id="sec-2"></a>

## 2. 加法、乘法与对数电路

<a id="statement-2-1"></a>

#### 定义 2.1（半环算术电路）

设 $S$ 是交换半环。有限算术电路是以常数、变量为输入，以 $+$、$\times$ 为内部节点的有向无环图。它的值由依赖关系递归确定。分配律把输出展开成多项式；共享子式可以节省工作而不改变该值。

<a id="statement-2-2"></a>

#### 命题 2.2（路径求和的适用形式）

若有限 DAG 的递归为

$$
f_v=b_v+\sum_{u\to v}w_{vu}f_u,
$$

则 $f_v$ 等于所有从某个源项 $b_s$ 到 $v$ 的有向路径的有序权重乘积之和。一般含两个非平凡输入的乘法门，需要解析树展开，不能都解释为原图上的单一路径。

<a id="proof-2-2"></a>

**证明。** 
按任一拓扑序归纳。代入每个前驱的已展开式，相当于把最后一条边接到该前驱的全部路径上；不同前驱区分最后一条边。长度零的路径给 $b_v$。有限性保证展开终止。一般乘法门同时取两个子电路的项，分配律给两者项集的笛卡尔积，故对应解析树。
 ∎

<a id="statement-2-3"></a>

#### 定理 2.3（对数半环同构）

在 $\mathbb{R}\cup\{-\infty\}$ 上定义

$$
a\oplus b=\log(e^a+e^b),\qquad a\otimes b=a+b,
$$

并约定 $e^{-\infty}=0$、$-\infty+a=-\infty$。则 $\log$ 是

$$
(\mathbb{R}_{\ge0},+,\times)\ \cong\
(\mathbb{R}\cup\{-\infty\},\oplus,\otimes)
$$

的同构，其逆为 $\exp$。原来的零、单位分别成为 $-\infty$、$0$。

<a id="proof-2-3"></a>

**证明。** 
$\log(ab)=\log a+\log b$，而 $\log(a+b)$ 恰是所定义的 $\oplus$。含零的情形由约定成立。两个双射互逆，故结合律、交换律和分配律全部随坐标变换转移。
 ∎

所以对数把乘法门变成普通加法门，把加法门变成 log-sum-exp 门。若 $a^2+b^2=c^2$ 且三者为正，同一勾股式在对数坐标中是

$$
2\log c=(2\log a)\oplus(2\log b).
$$

它提供精确坐标转换，而没有消去两种组合运算的区别。

<a id="statement-2-4"></a>

#### 命题 2.4（为何连续的乘加转换给出对数）

若连续函数 $L:(0,\infty)\to\mathbb{R}$ 满足 $L(ab)=L(a)+L(b)$，则 $L(a)=c\log a$。若再规定 $L(e)=1$，则 $c=1$。

<a id="proof-2-4"></a>

**证明。** 
令 $F(t)=L(e^t)$，则 $F(s+t)=F(s)+F(t)$。整数和有理数上的加法性给 $F(q)=qF(1)$，连续性延拓到全实数。取 $t=\log a$ 即得。
 ∎

概率的加法用于互斥事件；乘法的一般形式是条件链

$$
\Pr(o_1,\ldots,o_n)=\prod_{j=1}^n\Pr(o_j\mid o_1,\ldots,o_{j-1}).
$$

在正概率前缀上这是条件概率定义的递归；零质量分支可用已指定转移核描述。只有满足实际独立或条件独立，才可将条件项换成固定边缘。最新联合律桥正是在完整过去上验证这种替换。

<a id="statement-2-5"></a>

#### 说明 2.5（接回 v16 的变分）

给定有限路径权 $q_h>0$、代价 $c_h$ 与 $\tau>0$，

$$
\mathcal Z=\sum_hq_he^{-c_h/\tau}
$$

是加乘电路，$-\tau\log\mathcal Z$ 是其对数表示。若 $q$ 为参考概率律，则

$$
\mathbb{E}_Pc+\tau D\!\left(P\middle\Vert q\right) 
=-\tau\log\mathcal Z+\tau D\!\left(P\middle\Vert P^*\right) ,\quad
P_h^*=q_he^{-c_h/\tau}/\mathcal Z.
$$

展开对数即得。这是递归配分计算与 Gibbs 最小化的精确桥；代价、参考律和温度的选取仍是该问题的数据。

<a id="sec-3"></a>

## 3. 五个模式、唯一四角关系与十个三角形

<a id="statement-3-1"></a>

#### 定义 3.1（AURIC 五模式与坐标）

使用模式顺序

$$
\Sigma=(0,1,2,3,13)=(000,100,010,001,101).
$$

$x$ 为左端占位，$y$ 为右端占位，$z$ 为中位占位。印刷位串采用左、中、右顺序；几何坐标采用 $(x,y,z)$，故

$$
v_0=0,\quad v_1=e_x,\quad v_2=e_z,\quad
v_3=e_y,\quad v_{13}=e_x+e_y.
$$

它们对应项目数值标签 $(0,2,3,5,25)$。$0$ 模式表示空选择；相干层的 $|0\rangle$ 是单位基向量，不是零向量。

<a id="statement-3-2"></a>

#### 命题 3.2（五维函数代数）

五模式上的全部实值函数由 $\{1,x,y,z,xy\}$ 张成且线性独立，满足

$$
x^2=x,\quad y^2=y,\quad z^2=z,\quad xz=yz=0.
$$

五个事件指示函数分别是

$$
e_0=1-x-y-z+xy,\ e_1=x-xy,\ e_2=z,\ e_3=y-xy,\ e_{13}=xy.
$$

它们两两相乘为零，自身平方不变，且和为一。

<a id="proof-3-2"></a>

**证明。** 
逐个合法占位直接得到关系。所列 $e_s$ 在模式 $s$ 上为一、其余为零，因此任意函数 $f$ 等于 $\sum_sf(s)e_s$。五个原函数的线性组合若为零，依次在空模式、三个单点及共同端点上求值，全部系数均为零。
 ∎

<a id="statement-3-3"></a>

#### 定理 3.3（唯一仿射关系）

五个增广列 $(1,v_s)$ 的秩为四，核为

$$
\operatorname{span}\{h\},\qquad h=(1,-1,0,-1,1)^T.
$$

相应关系是

$$
\boxed{v_0+v_{13}=v_1+v_3.}
$$

<a id="proof-3-3"></a>

**证明。** 
$v_0,v_1,v_2,v_3$ 仿射独立，因此秩为四；直接代入 $h$ 得零。五列的零空间一维，故全部仿射依赖均为其倍数。底面的任意三个点不共线，故四角支撑还是最小依赖支撑。
 ∎

这是投影后坐标的关系；五个不同的原子事件仍然不同。三个均值无法看到的恰是该核方向。

<a id="statement-3-4"></a>

#### 定理 3.4（标准欧氏尺子下的三角分类）

采用项目定义 3.1 所选的标准欧氏内积，五点任取三点得到十个非退化三角形。其中九个是直角三角形，唯一例外为 $(v_1,v_2,v_3)$：它是边长 $\sqrt2$ 的等边三角形。

<a id="proof-3-4"></a>

**证明。** 
四个底面三角形均为单位正方形的一半，直角边长为 $1,1$。含顶点 $v_2$ 的六个三角形中，两个侧面的直角边为 $1,1$，另两个侧面的直角边为 $1,\sqrt2$；内部三角形 $(v_0,v_2,v_{13})$ 在 $v_0$ 处的直角边为 $1,\sqrt2$。余下 $(v_1,v_2,v_3)$ 的三条边平方都为二。
 ∎

因此，三个从原点出发的正交位置向量，其*端点*之间构成等边三角形。点、从共同原点出发的向量、事件指示函数是三个不同对象。只有在已经选定内积后，角度和勾股才有确定含义。

<a id="fig-1"></a>

**图 1 · 左面板：占位坐标的仿射投影示意**

```text
 v_2
   ●⡀
   ⡟⣮⠒⠤⡀
   ⡇⠘⡕⡄⠈⠑⠤⡀
   ⡇ ⠘⡌⢆  ⠈⠑⠢⣀
   ⡇  ⠱⡀⠣⡀    ⠑⠢⢄
   ⡇   ⠱⡀⠑⡄      ⠉⠢⢄
   ⡇    ⠱⡀⠈⢢        ⠉⠒⢄⡀
   ⡇     ⢣  ⠱⡀         ⠈⠒⢄⡀
   ⡇      ⢣  ⠘⢄           ⠈⠑⠤⡀
   ⡇       ⢣  ⠈⠢⡀            ⠈⠑⠤⣀
   ⡇        ⢇   ⠑⡄               ⠑⠢⣀
   ⡇        ⠈⢆   ⠈⢆                 ⠉⠢⢄
   ⡇        v_3    ⠣⡀                  ⠉⠢⢄⡀ v_13
   ⡇          ⢈●⠤⠤⠤⠤⠼⢤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠬⣶●
   ⡇         ⡠⠃ ⠁    ⠈⢢                ⠤⠒ ⡠⠃
   ⡇       ⢀⠔⠁    ⠐⠤⡀  ⠱⡀       ⣀  ⠒⠉   ⢀⠔⠁
   ⡇      ⡠⠃            ⠈⢆ ⣀⠤  ⠉       ⡠⠃
   ⡇    ⢀⠔⠁           ⠈⠦⡔ ⠣⡀         ⢀⠔⠁
   ⡇   ⡠⠃       ⢀  ⠔⠊      ⠑⡄       ⡠⠃
   ⡇ ⢀⠔⠁   ⢀⣀  ⠊⠁         ⠈⠢⠌⢆    ⢀⠔⠁
   ⡇⡠⠃ ⡠⠤  ⠁                  ⢱⡀ ⡠⠃
   ●⠷⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠽●⠁
 v_0                           v_1
```

> **图形排版说明（编者）。** `●` 仅标出五个顶点，线条交叉不新增顶点。实线为底面四边 $v_0v_1$、$v_1v_{13}$、$v_{13}v_3$、$v_3v_0$ 及四条顶点连线 $v_2v_0$、$v_2v_1$、$v_2v_3$、$v_2v_{13}$；点线为两条底面对角线 $v_0v_{13}$（源图蓝虚线）与 $v_1v_3$（源图红虚线）。源图浅蓝底面以这四条底边围定。文字示意保留关联，不用字符斜率量角。

**图 1 · 右面板：黄金通道的归一三角**

```text
                        ●
                       ╱│
                      ╱ │
                     ╱  │
                    ╱   │
                   ╱    │
                  ╱     │
                 ╱      │
              1 ╱       │  b = φ^(−1/2)
               ╱        │
              ╱         │
             ╱          │
            ╱           │
           ╱            │
          ╱             │
         ╱              │
        ╱               │
       ╱             ┌──┤
      ●──────────────┴──●
            a = φ^(−1)

             a² + b² = 1
```

右面板边标：$a=\varphi^{-1}$、$b=\varphi^{-1/2}$、斜边 $1$；右下角为直角，$a^2+b^2=1$。

**图 1.** 左图只表达五点及两条底面对角线的关联；纸面透视角度不作为欧氏量测。右图表达黄金通道的归一三角。两图使用不同的数学载体。

<a id="sec-4"></a>

## 4. 三读出、隐藏关联与指数族

令 $p_s\ge0$、$\sum_sp_s=1$，并记

$$
X=\mathbb{E}_px=p_1+p_{13},\quad Y=\mathbb{E}_py=p_3+p_{13},\quad
Z=\mathbb{E}_pz=p_2,\quad R=1-Z,\quad \kappa=p_{13}.
$$

<a id="statement-4-1"></a>

#### 定理 4.1（完整纤维与两种对角线）

固定 $(X,Y,Z)$ 的全部相容律恰为

<a id="eq-fiber"></a>

$$
\begin{aligned}
p(\kappa)&=(R-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\end{aligned}
\tag{1}
$$

$$
\begin{aligned}
\kappa_-&=\max(0,X+Y-R)\le\kappa\le\min(X,Y)=\kappa_+.
\end{aligned}
$$

底面对角线 $v_0v_{13}$ 的三角剖分，再与顶点 $v_2$ 取锥，其重心完成选择 $\kappa_+$；另一条对角线 $v_1v_3$ 选择 $\kappa_-$。

<a id="proof-4-1"></a>

**证明。** 
均值定义与归一化逐项解出 [(1)](#eq-fiber)；五项非负恰给所列区间。若 $X\le Y$，上端点令 $p_1=0$，来源落入 $\operatorname{conv}(v_0,v_2,v_3,v_{13})$；若 $Y\le X$，则令 $p_3=0$，落入另一四面体。下端点在 $X+Y\le R$ 时令 $p_{13}=0$，否则令 $p_0=0$，正好是另一剖分的两四面体。各四面体内的重心坐标唯一，公共面上表示相合。
 ∎

这把“对角线的位置是一种预测”落实为一个精确例子：选一种剖分，就选了一种相容完成。选择并不改变已经观测到的三个均值。例如 $X=Y=R/2$ 时，两端为 $0,R/2$，后述最大熵点为 $R/4$。

以下涉及对数和 Fisher 度量时，除特别声明外均取满支撑 $p_s>0$。

<a id="statement-4-2"></a>

#### 定义 4.2（完整四参数指数族）

设 $T=(x,y,z,xy)$，自然参数为 $\vartheta=(\theta_x,\theta_y,\theta_z,\eta)$，定义

$$
\begin{aligned}
\Psi(\vartheta)&=\log\left(1+e^{\theta_x}+e^{\theta_z}+e^{\theta_y}
  +e^{\theta_x+\theta_y+\eta}\right),
\end{aligned}
$$

$$
\begin{aligned}
p_\vartheta(s)&=\exp\{\vartheta\cdot T(s)-\Psi(\vartheta)\}.
\end{aligned}
$$

未归一化权重为 $(1,a,b,c,dac)$，其中 $a=e^{\theta_x}$、$b=e^{\theta_z}$、$c=e^{\theta_y}$、$d=e^\eta$。

<a id="statement-4-3"></a>

#### 定理 4.3（对数把唯一四角关系显式化）

每份正五模式律都有唯一上述参数，且

$$
\theta_x=\log\frac{p_1}{p_0},\quad
\theta_y=\log\frac{p_3}{p_0},\quad
\theta_z=\log\frac{p_2}{p_0},\quad
\boxed{\eta=\log\frac{p_0p_{13}}{p_1p_3}}.
$$

此外

$$
p_0p_{13}-p_1p_3=R\kappa-XY.
$$

故 $\eta=0$ 等价于在 $z=0$ 条件下两个端点独立。

<a id="proof-4-3"></a>

**证明。** 
以 $p_0$ 为基准取比值，依次恢复三个单位置参数及交互参数；反代再归一化恢复全部概率。行列式式由 [(1)](#eq-fiber) 展开。底面条件概率表为

$$
\frac1R\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix}.
$$

正二元表独立当且仅当秩一，也即行列式零。
 ∎

<a id="statement-4-4"></a>

#### 定理 4.4（配分函数的变分与对偶）

有

$$
\nabla\Psi=\mathbb{E}_pT=(X,Y,Z,\kappa),\qquad
\nabla^2\Psi=\operatorname{Cov}_p(T)>0.
$$

对正均值域中的完整四维均值 $m$ 及其唯一概率律 $p_m$，

$$
\Psi^*(m)=\sup_\vartheta\{\vartheta\cdot m-\Psi(\vartheta)\}
=\sum_sp_m(s)\log p_m(s)=-H(p_m).
$$

<a id="proof-4-4"></a>

**证明。** 
对有限指数和逐项求导得到均值与协方差。若 $c^T\operatorname{Cov}(T)c=0$，则 $c\cdot T$ 在全支撑上恒定。空模式使该常数为零；三个单模式依次使前三个系数为零，$13$ 模式使最后系数为零，故 Hessian 正定。最后展开

$$
D\!\left(p_m\middle\Vert p_\vartheta\right) 
=\sum_sp_m\log p_m-\vartheta\cdot m+\Psi(\vartheta)\ge0.
$$

匹配的唯一参数取得等号，给出共轭式。
 ∎

这就是上一稿“预测、递归、变分”在本题的一次具体会合：递归计算配分函数，求导得到读出，凸对偶得到熵目标。一般指数族的背景见 [2](#ref-wj)。

<a id="sec-5"></a>

## 5. 信息勾股：三个可见误差与一个隐藏关联

<a id="statement-5-1"></a>

#### 定理 5.1（唯一最大熵完成）

在 $R>0$、$0<X,Y<R$ 下，固定三均值的熵唯一最大于

$$
\kappa^*=\frac{XY}{R},\qquad
p^*=\left(\frac{(R-X)(R-Y)}R,\frac{X(R-Y)}R,Z,
\frac{Y(R-X)}R,\frac{XY}R\right).
$$

对同一纤维上的正律，令 $F(\kappa)=-H(p(\kappa))$，则

$$
F'(\kappa)=\eta,\qquad
F''(\kappa)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}>0.
$$

<a id="proof-5-1"></a>

**证明。** 
纤维导数是 $h=(1,-1,0,-1,1)$，且 $\sum h_s=0$，所以 $F'=\sum h_s\log p_s=\eta$，再求导得第二式。$\eta=0$ 等价于 $R\kappa=XY$，其解位于区间内部；严格凸性给唯一最小负熵。$Z=0$ 时对四底角相同证明，其他退化边界按条件表的退化边缘处理；$R=0$ 时仅剩顶点律。
 ∎

<a id="statement-5-2"></a>

#### 定义 5.2（零交互族）

令 $\mathcal E$ 为 $\eta=0$ 的满支撑三参数族。每个成员在底面是两个 Bernoulli 变量的乘积。记 $d(a\Vert b)$ 为二元 KL，$I_0(p)$ 为条件表 $p(x,y\mid z=0)$ 的互信息，$D\!\left(p\middle\Vert q\right) =\sum_sp_s\log(p_s/q_s)$。

<a id="statement-5-3"></a>

<a id="thm-kl"></a>

#### 定理 5.3（精确 KL 勾股与非正交修正）

若 $q\in\mathcal E$，则

$$
\boxed{ D\!\left(p\middle\Vert q\right) = D\!\left(p\middle\Vert p^*\right) + D\!\left(p^*\middle\Vert q\right) .}
$$

更一般地，对任意正 $q$，设其交互参数为 $\eta_q$，则

$$
\boxed{ D\!\left(p\middle\Vert q\right) = D\!\left(p\middle\Vert p^*\right) + D\!\left(p^*\middle\Vert q\right) 
 -\eta_q(\kappa-\kappa^*).}
$$

<a id="proof-5-3"></a>

**证明。** 
$\log q$ 为常数、$x,y,z,xy$ 的线性组合。$p$ 和 $p^*$ 的前三均值与总质量相同，故

$$
\sum_s(p_s-p_s^*)\log q_s=\eta_q(\kappa-\kappa^*).
$$

在正内点，相同论证对 $\log p^*$ 给零，因其交互参数为零，直接展开三个 KL 的差即可。
边界也可直接证明：当 $R>0$，$p^*$ 的底面是 $p$ 的条件边缘的乘积，故 $\operatorname{supp} p\subseteq\operatorname{supp} p^*$，按该条件表展开即得

$$
D\!\left(p\middle\Vert p^*\right) =H(p^*)-H(p)=R I_0(p).
$$

任意满支撑 $q$ 的对数线性形式仍给

$$
D\!\left(p\middle\Vert q\right) - D\!\left(p^*\middle\Vert q\right) 
=H(p^*)-H(p)-\eta_q(\kappa-\kappa^*),
$$

所以结论覆盖纤维端点、零边缘和 $Z=0$ 的底面。$R=0$ 时 $p=p^*=\delta_2$，两式亦成立。令 $\eta_q=0$ 得第一式。
 ∎

这是经典信息投影定理在本来源上的具体实例，理论背景见 [1](#ref-cs)。KL 通常不对称，故这里的“勾股”指有向散度的精确分解，不是把它当成普通欧氏距离。

<a id="statement-5-4"></a>

#### 定理 5.4（四项非负分解）

令 $u=X/R$、$v=Y/R$，把 $q\in\mathcal E$ 参数化为顶点质量 $Z'$、底面端点概率 $u',v'$。则

$$
\boxed{ D\!\left(p\middle\Vert q\right) =R I_0(p)+d(Z\Vert Z')
 +R d(u\Vert u')+R d(v\Vert v').}
$$

特别地，$D\!\left(p\middle\Vert p^*\right) =R I_0(p)=H(p^*)-H(p)$。

<a id="proof-5-4"></a>

**证明。** 
先按 $z$ 拆分 KL：顶点与底面质量贡献 $d(Z\Vert Z')$，顶点条件层只有一个状态。底面令 $r_{ij}=p_{ij}/R$，其边缘为 $a_i,b_j$，目标乘积边缘为 $a_i',b_j'$。分解

$$
\log\frac{r_{ij}}{a_i'b_j'}
=\log\frac{r_{ij}}{a_ib_j}+\log\frac{a_i}{a_i'}+\log\frac{b_j}{b_j'}.
$$

按 $r$ 求和即得互信息与两个边缘 KL，乘回 $R$。在 $q=p^*$ 时三个可见项皆零。熵差式由定理 [5.3](#statement-5-3) 的证明得到。
 ∎

此处标准条件互信息 $I_p(x;y\mid z)$ 已等于 $R I_0(p)$；若使用该记号，不可再乘一次 $R$。当 $R=0$ 时，三个底面项定义为零，公式退为顶点二元 KL。

<a id="statement-5-5"></a>

#### 命题 5.5（纤维 Bregman 关系）

对同一正纤维的 $p_\kappa,p_\lambda$，

$$
\begin{aligned}
D\!\left(p_\kappa\middle\Vert p_\lambda\right) 
 &=F(\kappa)-F(\lambda)-\eta(\lambda)(\kappa-\lambda),
\end{aligned}
$$

$$
\begin{aligned}
D\!\left(p_\kappa\middle\Vert p_\lambda\right) + D\!\left(p_\lambda\middle\Vert p_\kappa\right) 
 &=(\kappa-\lambda)(\eta(\kappa)-\eta(\lambda)).
\end{aligned}
$$

<a id="proof-5-5"></a>

**证明。** 
代入 $p_\kappa-p_\lambda=(\kappa-\lambda)h$，并用 $\sum h_s\log p_\lambda(s)=\eta(\lambda)$ 展开 KL。交换两点相加得到第二式。其非负性来自 $\eta$ 严格递增。
 ∎

<a id="sec-6"></a>

## 6. 三个稳定读出的正交性究竟在哪里

<a id="statement-6-1"></a>

#### 命题 6.1（原始读出通常不统计正交）

同一实际律下，三个中心化读出的 Gram 矩阵为

$$
\operatorname{Cov}(x,y,z)=
\begin{pmatrix}
X(1-X)&\kappa-XY&-XZ\\
\kappa-XY&Y(1-Y)&-YZ\\
-XZ&-YZ&Z(1-Z)
\end{pmatrix}.
$$

在 $p^*$ 上仍有 $\operatorname{Cov}(x,y)=XYZ/R$。当 $X,Y,Z>0$ 时，未中心化且单位归一的指示函数 Gram 为

$$
\begin{pmatrix}1&\kappa/\sqrt{XY}&0\\
\kappa/\sqrt{XY}&1&0\\0&0&1\end{pmatrix}.
$$

<a id="proof-6-1"></a>

**证明。** 
由 $x^2=x,y^2=y,z^2=z,xz=yz=0$ 及 $\mathbb{E} xy=\kappa$ 直接计算。最大熵情形代入 $\kappa=XY/R$。
 ∎

因此可以研究严格成立的*读出方向正交化*，而不必假定原始三随机变量已经正交。

<a id="statement-6-2"></a>

#### 定义 6.2（最大熵参考下的五元函数）

固定满支撑 $p^*$，令 $u=X/R,v=Y/R$，定义

$$
\begin{aligned}
t_z&=\frac{z-Z}{\sqrt{ZR}},&
t_x&=\frac{(1-z)(x-u)}{\sqrt{Ru(1-u)}},
\end{aligned}
$$

$$
\begin{aligned}
t_y&=\frac{(1-z)(y-v)}{\sqrt{Rv(1-v)}},&
t_h&=\frac{(1-z)(x-u)(y-v)}{\sqrt{Ru(1-u)v(1-v)}}.
\end{aligned}
$$

<a id="statement-6-3"></a>

#### 定理 6.3（五模式的完整勾股分解）

$\{1,t_z,t_x,t_y,t_h\}$ 是 $L^2(\Sigma,p^*)$ 的正交归一基。对任意复值函数 $f$，定义 $\operatorname{Var} f=\mathbb{E}|f-\mathbb{E} f|^2$，则

$$
\boxed{\operatorname{Var}_{p^*}f
= \left|\mathbb{E}(f t_z)\right| ^2+ \left|\mathbb{E}(f t_x)\right| ^2
 + \left|\mathbb{E}(f t_y)\right| ^2+ \left|\mathbb{E}(f t_h)\right| ^2.}
$$

前三个非平凡方向加常数张成 $\operatorname{span}\{1,x,y,z\}$，最后一个方向是唯一均值不可见的交互方向。

<a id="proof-6-3"></a>

**证明。** 
在 $p^*$ 下，$z$ 为 Bernoulli；给定 $z=0$，$x,y$ 是独立 Bernoulli。条件求期望表明四个 $t$ 均值零、二阶矩一。$t_z$ 在底面为常数，而其余三个的底面条件均值为零。$t_x,t_y$ 的交叉项因独立为零；$t_x,t_h$ 与 $t_y,t_h$ 的交叉项各含一个独立零均值因子。空间维数五，故五个正交单位函数构成基，Parseval 给等式。又合法性给 $(1-z)(x-u)=x-u+uz$，$y$ 同理，遂有可见空间的张成关系。
 ∎

<a id="statement-6-4"></a>

#### 推论 6.4（隐藏关系的精确 Pearson 平方）

令 $\delta=\kappa-\kappa^*$。同三均值的 $p$ 满足

$$
\frac p{p^*}=1+
\frac{\delta}{\sqrt{Ru(1-u)v(1-v)}}t_h,
\qquad
\boxed{\sum_s\frac{(p_s-p_s^*)^2}{p_s^*}
=\frac{\delta^2}{Ru(1-u)v(1-v)}.}
$$

<a id="proof-6-4"></a>

**证明。** 
密度差与常数及三个可见方向正交，只能沿 $t_h$；其系数为 $\mathbb{E}_pt_h$，展开分子得 $\delta/\sqrt{Ru(1-u)v(1-v)}$。再用 Parseval。
 ∎

<a id="statement-6-5"></a>

#### 定理 6.5（Fisher 正交与平方根几何）

定义 $g_F(a,b)=\sum_sa_sb_s/p_s$，其中概率切向满足质量和为零。则

$$
d\eta(a)=g_F(h,a),\qquad \partial_\kappa\eta=g_F(h,h)>0.
$$

在 $\delta=0$ 的点处，用坐标 $(Z,u,v,\delta)$ 表示的完整四维 Fisher 度量为

$$
\boxed{ds^2=\frac{dZ^2}{ZR}+R\frac{du^2}{u(1-u)}
 +R\frac{dv^2}{v(1-v)}+
\frac{d\delta^2}{Ru(1-u)v(1-v)}.}
$$

映射 $p\mapsto2(\sqrt{p_s})_s$ 把正单纯形等距嵌入半径二球面的正象限。

<a id="proof-6-5"></a>

**证明。** 
对 $\eta=\log p_0+\log p_{13}-\log p_1-\log p_3$ 求导得第一式。对 $p^*$ 的 $Z,u,v$ 参数求对数导数，分别得到上述三个归一函数的标量倍数；交叉期望为零。$\delta$ 切向为 $h$，其分数方向沿 $t_h$，长度平方为 $1/[Ru(1-u)v(1-v)]$。最后 $\sum_s(2\sqrt{p_s})^2=4$ 且 $d(2\sqrt{p_s})=dp_s/\sqrt{p_s}$，直接给度量拉回。
 ∎

前三个可见方向加一个隐藏关系方向，确实在这个明确参考下有勾股结构。上式在 $\delta=0$ 处的分块表达不能任意外推到全部关联律；概率运输卷已有 $d\eta=g_F(h,\cdot)$ 的全域形式。概率平方根的实球面实现本身也没有给出全部复相位。

<a id="sec-7"></a>

## 7. 三角面积平方为何会相加

<a id="statement-7-1"></a>

<a id="thm-volume"></a>

#### 定理 7.1（协方差体积的单纯形平方和）

设有限个向量 $v_i\in\mathbb{R}^d$ 具有非负权重 $p_i$，且 $\sum_i p_i=1$。
记其均值为 $\mu=\sum_i p_iv_i$，协方差为 $G=\sum_i p_i(v_i-\mu)(v_i-\mu)^T$。则

$$
\boxed{\det G=(d!)^2\!
\sum_{i_0<\cdots<i_d}
\left(\prod_{k=0}^{d}p_{i_k}\right)
\operatorname{Vol}_d(v_{i_0},\ldots,v_{i_d})^2.}
$$

特别在二维，

$$
\det G=4\sum_{i<j<k}p_ip_jp_k A_{ijk}^2.
$$

<a id="proof-7-1"></a>

**证明。** 
令 $M$ 的第 $i$ 行为 $\sqrt{p_i}(1,v_i^T)$。其 Gram 矩阵为

$$
M^TM=\begin{pmatrix}1&\mu^T\\\mu&\sum_i p_iv_iv_i^T\end{pmatrix}.
$$

减去首行、列的相应倍数，其行列式为 $\det G$。Cauchy--Binet 把它写成全部 $(d+1)$ 行子矩阵的行列式平方之和。每个子式等于 $\sqrt{\prod p_{i_k}}$ 乘增广顶点行列式，后者的绝对值为 $d!$ 倍单纯形体积，得到结论。
 ∎

这是一种真正的广义勾股：Gram 体积来自外幂空间中的范数，子式是其正交坐标。项目矩三角形卷已使用此经典恒等式：当 $v_i=(r_i,r_i^2)$ 时，三角面积由 Vandermonde 给出

$$
A(a,b,c)=\tfrac12(b-a)(c-a)(c-b),\quad a<b<c.
$$

面积很小意味着这些候选响应在该读出中接近退化；精确可逆与稳定可逆是两项不同要求。

<a id="statement-7-2"></a>

#### 推论 7.2（五模式的体积平方）

对本五个欧氏顶点，

$$
\det\operatorname{Cov}(x,y,z)
=Z\bigl(p_0p_1p_3+p_0p_1p_{13}
 +p_0p_3p_{13}+p_1p_3p_{13}\bigr).
$$

<a id="proof-7-2"></a>

**证明。** 
四个底面点共面，对应体积为零。其余四个四面体都包含顶点 $v_2$，由三个底角组成，体积均为 $1/6$。代入定理 [7.1](#statement-7-1)。
 ∎

<a id="statement-7-3"></a>

#### 定理 7.3（记录三角形的最小性）

在底面上，假设先验端点独立，每个正概率记录结果 $o$ 后的端点仍独立。令 $u_o=\mathbb{E}[x\mid o,z=0]$、$v_o=\mathbb{E}[y\mid o,z=0]$。若两个后验均值都随记录改变，至少要有三个记录结果。对三个结果及其底面条件权重 $q_0,q_1,q_2$，有

$$
\det\operatorname{Cov}_q(u_o,v_o)=4q_0q_1q_2 A_\triangle^2.
$$

<a id="proof-7-3"></a>

**证明。** 
总协方差公式给 $0=\operatorname{Cov}(x,y)=\operatorname{Cov}_q(u_o,v_o)$，因为每个后验内的协方差为零。若仅两个正概率结果，右侧为 $q_0q_1(u_1-u_0)(v_1-v_0)$，必有一项均值不变。三个结果的面积式是定理 [7.1](#statement-7-1) 的三点特例。
 ∎

三结果确实足够。取 $q_o=1/3$ 及

$$
(u_0,v_0)=(1/4,2/3),\quad
(u_1,v_1)=(1/2,1/6),\quad
(u_2,v_2)=(3/4,2/3).
$$

令每个条件后验为对应乘积 Bernoulli 表。其混合均值为 $(1/2,1/2)$、混合共同占位为 $1/4$，故混合先验仍为独立表。所有表项均正，以 $\Pr(o\mid x,y)=q_op(x,y\mid o)/p(x,y)$ 即构造出合法读口。该三角面积为 $1/8$，两坐标方差为 $1/24,1/18$，协方差为零。若补入任意 $0\le Z<1$ 的固定顶点质量，令每个完整后验顶点质量均为 $Z$，则得到五模式读口。这给出“两个非零正交信息变化需要三记录”的具体实现。

<a id="sec-8"></a>

## 8. 从加乘到量子电路：直和、张量积与平方

<a id="statement-8-1"></a>

#### 定理 8.1（范数平方保持两种组合）

在已给 Hilbert 结构中，令 $w(v)= \left\lVert v\right\rVert ^2$，则

$$
\boxed{w(u\oplus v)=w(u)+w(v),\qquad
w(u\otimes v)=w(u)w(v).}
$$

相干叠加则满足

$$
w(u+v)=w(u)+w(v)+2\operatorname{Re}\langle u,v\rangle.
$$

<a id="proof-8-1"></a>

**证明。** 
直和内积逐分量相加；简单张量的内积为两因子的内积之积。展开同一空间中 $u+v$ 的二次型，得到交叉项。
 ∎

正交记录实现可加分支，张量乘积实现已声明的系统复合。概率电路与量子电路的一个严格联系，就在于这个平方重量映射。

<a id="statement-8-2"></a>

#### 命题 8.2（全相位加性与真正正交）

对所有实数 $\theta$，

$$
\left\lVert u+e^{i\theta}v\right\rVert ^2= \left\lVert u\right\rVert ^2+ \left\lVert v\right\rVert ^2
$$

当且仅当 $\langle u,v\rangle=0$。只在一个相位成立，仅能推出相应实交叉项为零。

<a id="proof-8-2"></a>

**证明。** 
取 $\theta=0,\pi/2$，分别令内积的实部、虚部为零。反向直接展开。
 ∎

<a id="statement-8-3"></a>

#### 定理 8.3（在这些前提下平方权重被确定）

在维数至少二的 Hilbert 空间上，设 $W$ 定义于全部向量，取非负实值；它在酉变换下不变，对正交向量可加，且单位向量的权重为一。则 $W(v)= \left\lVert v\right\rVert ^2$。

<a id="proof-8-3"></a>

**证明。** 
酉不变性使 $W(v)=f( \left\lVert v\right\rVert ^2)$。任意 $a,b\ge0$ 可作为两正交向量的范数平方，因此 $f(a+b)=f(a)+f(b)$。非负性使 $f$ 单调，$f(1)=1$ 给有理点 $f(q)=q$，用上下有理逼近得全部非负实数上 $f(t)=t$。
 ∎

这是含明确输入的平方规则：已经有 Hilbert 内积、全部相关酉对称和正交可加性，再得到唯一校准重量。五个组合标签本身没有单独完成这些输入的推导。

<a id="statement-8-4"></a>

#### 定理 8.4（有限经典通道的量子扩张）

给定有限列随机矩阵 $T(y\mid x)$，定义

$$
V|x\rangle=\sum_y\sqrt{T(y\mid x)}\,|y\rangle|x,y\rangle_E.
$$

其中环境基两两正交。则 $V$ 是等距映射，且

$$
\operatorname{Tr}_E(V\rho V^\dagger)
=\sum_{x,y}T(y\mid x)\rho_{xx}|y\rangle\langle y|.
$$

有限扩充空间后可把 $V$ 延拓为酉操作。

<a id="proof-8-4"></a>

**证明。** 
不同输入的像因环境记录不同而正交；相同输入的像范数平方为 $\sum_yT(y\mid x)=1$。取环境偏迹消去所有不同 $(x,y)$ 的项，得到通道。把等距映射的正交列补为完整正交基，即得酉延拓。
 ∎

有限确定性函数也有可逆扩张 $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$。有限精度的指数、对数算法可按此方式编译；它并不使任意精确连续实数函数成为有限寄存器中的同维酉门。若只要求一个同维 $U$ 满足 $T_{yx}=|U_{yx}|^2$，则至少需要行和、列和都为一；把两个输入都擦除到同一输出的随机矩阵即不满足。实际辅助寄存器、初态和记录由扩张明确承担。

<a id="sec-9"></a>

## 9. 核心定理：对数关联与相位的量子勾股

<a id="statement-9-1"></a>

#### 定义 9.1（条件底面的纯态与四角复比）

现在明确给定 $\mathcal H_5\subset(\mathbb{C}^2)^{\otimes3}$、计算基、Born 标定以及中位为零分支的两端张量分割。令

$$
|\Psi\rangle=\alpha_0|000\rangle+\alpha_1|100\rangle
+\alpha_2|010\rangle+\alpha_3|001\rangle+\alpha_{13}|101\rangle,
\qquad \sum_s|\alpha_s|^2=1.
$$

令 $p_s=|\alpha_s|^2$、$R=1-p_2>0$，条件底面纯态的系数矩阵为 $M/\sqrt R$，其中

$$
M=\begin{pmatrix}\alpha_0&\alpha_3\\\alpha_1&\alpha_{13}\end{pmatrix}.
$$

当四底角非零时，定义

$$
\Omega=\frac{\alpha_0\alpha_{13}}{\alpha_1\alpha_3},\qquad
\eta=\log\frac{p_0p_{13}}{p_1p_3},\qquad
\Phi=\arg\Omega\pmod{2\pi}.
$$

于是 $\log\Omega=\eta/2+i\Phi\pmod{2\pi i}$。

<a id="statement-9-2"></a>

#### 定理 9.2（可分性需要模与相位同时相容）

条件底面纯态可分当且仅当 $\det M=0$。在四底角非零时，它等价于

$$
\boxed{\kappa=\frac{XY}{R}\quad\text{且}\quad\Phi=0\pmod{2\pi}.}
$$

<a id="proof-9-2"></a>

**证明。** 
两比特纯态可分恰指系数矩阵能写成两个向量的外积，即矩阵秩一；$M\ne0$，因此等价于行列式零。等式 $\alpha_0\alpha_{13}=\alpha_1\alpha_3$ 对非零复数要求模相等和相位相同。模平方相等是 $p_0p_{13}=p_1p_3$，前文已经证明它等价于 $R\kappa=XY$。
 ∎

<a id="statement-9-3"></a>

<a id="thm-main"></a>

#### 定理 9.3（对数关联与相位的双平方恒等式）

设四底角非零，记

$$
s=\sqrt{p_0p_{13}},\qquad t=\sqrt{p_1p_3}.
$$

则

<a id="eq-det-sum"></a>

$$
\begin{aligned}
\left|\det M\right| ^2
&=(s-t)^2+4st\sin^2(\Phi/2)
\end{aligned}
\tag{2}
$$

<a id="eq-sinh"></a>

$$
\begin{aligned}
&=4st\left[\sinh^2(\eta/4)+\sin^2(\Phi/2)\right].
\end{aligned}
\tag{3}
$$

定义条件纯态的 concurrence 为 $C=2|\det M|/R$，则

$$
\boxed{C^2=\frac{16\sqrt{p_0p_1p_3p_{13}}}{R^2}
\left[\sinh^2(\eta/4)+\sin^2(\Phi/2)\right].}
$$

<a id="proof-9-3"></a>

**证明。** 
$\det M$ 是模分别为 $s,t$、相位差为 $\Phi$ 的两个复数之差，因此余弦定理给

$$
\left|\det M\right| ^2=s^2+t^2-2st\cos\Phi.
$$

加减 $2st$ 并用 $1-\cos\Phi=2\sin^2(\Phi/2)$，得到 [(2)](#eq-det-sum)。又 $s/t=e^{\eta/2}$，所以

$$
s=\sqrt{st}\,e^{\eta/4},\quad
t=\sqrt{st}\,e^{-\eta/4},\quad
(s-t)^2=4st\sinh^2(\eta/4).
$$

代入并乘 $4/R^2$ 得最后一式。
 ∎

同一结果也来自

$$
\left|\sinh(a+ib)\right| ^2=\sinh^2a+\sin^2b,
\qquad a+ib=\tfrac12\log\Omega.
$$

复对数换支只使该双曲正弦改变符号，模平方保持不变。因此这个量在相位圆周上良定义。

这是本轮将用户直觉落实得最直接的公式：乘积关系经对数成为 $\eta$，同一振幅比的虚部成为相位 $\Phi$，两者在一个可计算的纠缠量中以非负平方贡献相加。该恒等式是所声明纯态模型内的精确关系；并不等同于断言 $(\eta,\Phi)$ 在全部 Fisher 几何中自动正交。

<a id="statement-9-4"></a>

#### 定理 9.4（纠缠与局部 Bloch 向量的勾股）

令 $\rho_A=MM^\dagger/R=(I+r\cdot\sigma)/2$ 为条件底面态的一端约化态，则

$$
\boxed{C^2+ \left\lVert r\right\rVert ^2=1.}
$$

<a id="proof-9-4"></a>

**证明。** 
$\operatorname{Tr}\rho_A=1$ 且 $\det\rho_A=|\det M|^2/R^2=C^2/4$。二阶矩阵的 Bloch 表示给 $\det\rho_A=(1- \left\lVert r\right\rVert ^2)/4$，相等即得。其两个非负本征值保证 $0\le C\le1$。
 ∎

纯态 concurrence 的一般理论见 [4](#ref-wootters)。这里没有调用混合态 concurrence 的凸包公式；若条件态混合，上述纯态等式不可直接使用。

<a id="statement-9-5"></a>

#### 命题 9.5（同五概率而从零纠缠到最大纠缠）

取

$$
|\Psi_\pm\rangle=\frac1{\sqrt5}
\bigl(|000\rangle+|100\rangle+|010\rangle+|001\rangle
\mathbin{\pm}|101\rangle\bigr).
$$

两态有完全相同的五个模式概率 $p_s=1/5$，同样的三读出 $X=Y=2/5,Z=1/5$，且 $\eta=0$。在中位为零条件下，$\Psi_+$ 的两端为乘积态，$C=0$；$\Psi_-$ 的两端为最大纠缠纯态，$C=1$。

<a id="proof-9-5"></a>

**证明。** 
两态仅差一项相位。$R=4/5$，条件底面矩阵分别为

$$
\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
\frac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

第一矩阵秩一；第二的任一单端约化态为 $I/2$。也可将 $\Phi=0,\pi$ 代入定理 [9.3](#statement-9-3)。
 ∎

这个例子展示抽象 Hilbert 完成的非唯一性。它不声称两个态能从计算基经有限个原生黄金门精确制备；v15 的算术障碍恰限制这种有理完整概率的精确实现。这里研究的是条件分支，也没有把它直接认作丢弃中位后的无条件纠缠。

<a id="statement-9-6"></a>

#### 命题 9.6（四角复比的指定规范意义）

在四个元素非零的二阶矩阵上，$\Omega=M_{00}M_{11}/(M_{10}M_{01})$ 是可逆对角行列缩放 $M\mapsto D_LMD_R$ 的完整不变量。

<a id="proof-9-6"></a>

**证明。** 
每行、每列的因子在分子分母中各出现一次，故抵消。反向，设目标为 $N$，先取左第一因子为一，右因子取 $N_{00}/M_{00}$ 与 $N_{01}/M_{01}$，再取左第二因子使 $(1,0)$ 元素匹配。前三个非零元素相等且复比相等，强制第四个相等。
 ∎

局部对角相位是该群的子群，所以 $\Phi$ 确为一种闭合相位关系。任意局部酉变换的范围更大；一般非酉缩放也会改变归一化 concurrence，不能把 $C$ 的数值说成此缩放群的不变量。零振幅处不用不存在的相位或对数，直接使用 $\det M$；$R=0$ 时条件底面态不存在。

<a id="sec-10"></a>

## 10. 量子相对熵把三层缺失精确相加

<a id="statement-10-1"></a>

#### 定义 10.1（记录去相干与量子散度）

在 $\mathcal H_5$ 的指定记录基上，$\Delta\rho$ 表示删除非对角项，$p=\operatorname{diag}\rho$。定义

$$
S(\rho)=-\operatorname{Tr}\rho\log\rho,\quad
 D_Q\!\left(\rho\middle\Vert \sigma\right) =\operatorname{Tr}\rho(\log\rho-\log\sigma),\quad
C_{\rm rel}(\rho)=H(p)-S(\rho).
$$

对数按支撑解释，参考态满支撑时散度有限。

<a id="statement-10-2"></a>

<a id="thm-qkl"></a>

#### 定理 10.2（相干、隐藏关联与可见失配的三项分解）

对任意五维密度矩阵 $\rho$，令 $p^*$ 为 $p=\operatorname{diag}\rho$ 的同三均值最大熵完成。对任意满支撑 $q\in\mathcal E$，令 $\sigma=\operatorname{diag} q$。则

$$
\boxed{ D_Q\!\left(\rho\middle\Vert \sigma\right) 
=\underbrace{C_{\rm rel}(\rho)}_{\text{记录基相干}}
+\underbrace{R I_0(p)}_{\text{隐藏经典关联}}
+\underbrace{ D\!\left(p^*\middle\Vert q\right) }_{\text{可见读出失配}}.}
$$

三项均非负。

<a id="proof-10-2"></a>

**证明。** 
因 $\log\sigma$ 对角，$\operatorname{Tr}\rho\log\sigma=\sum_sp_s\log q_s$，故

$$
D_Q\!\left(\rho\middle\Vert \sigma\right) =H(p)-S(\rho)+ D\!\left(p\middle\Vert q\right) .
$$

再用定理 [5.3](#statement-5-3) 及 $D\!\left(p\middle\Vert p^*\right) =R I_0(p)$。相干项等于 $D_Q\!\left(\rho\middle\Vert \Delta\rho\right) \ge0$。若某 $p_s=0$，正半定性给 $|\rho_{st}|^2\le\rho_{ss}\rho_{tt}=0$，该行列全零，因此 $\rho$ 的支撑仍包含于 $\Delta\rho$ 的支撑，散度解释有效。
 ∎

相干相对熵的标准分解见 [3](#ref-bcp)；本定理把它与 AURIC 的特定条件独立投影组合。将第 5 节的四项 KL 式代入，还能把最后一项拆成三个二元读出损失。

<a id="statement-10-3"></a>

#### 推论 10.3（固定三读出的最大量子熵态）

在 $\mathcal H_5$ 上固定三个占位算符的期望，唯一最大 von Neumann 熵态为 $\rho^*=\operatorname{diag} p^*$。

<a id="proof-10-3"></a>

**证明。** 
$S(\rho)\le H(\operatorname{diag}\rho)\le H(p^*)$。第一项等号强制无记录基相干，第二项等号强制条件表独立，故同时取等仅有 $\operatorname{diag} p^*$。
 ∎

最大熵态是一个明确评分下的预测完成。它与实际来源态的相等需要额外依据；例如上一节两个纯态有相同三个均值，却都保留相干关系。相干的总量也不单独确定相位回路，故不同缺失信息应由对应读出检验。

<a id="sec-11"></a>

## 11. 递归观测如何在复对数中累加关系

<a id="statement-11-1"></a>

#### 定理 11.1（经典四角关系的 Bayes 递归）

设 $p_0p_1p_3p_{13}>0$。对一条正似然 $\ell_s>0$，令后验 $p'_s=p_s\ell_s/\sum_tp_t\ell_t$。则

$$
\boxed{\eta'=\eta+\log\frac{\ell_0\ell_{13}}{\ell_1\ell_3}.}
$$

如果似然在底面因子化为一个左端因子乘一个右端因子，则交互增量为零。

<a id="proof-11-1"></a>

**证明。** 
将后验代入四角比，四个归一化因子在分子分母各出现两次，全部抵消；剩下先验四角比乘似然四角比。因子化似然的行、列因子亦相消。
 ∎

<a id="statement-11-2"></a>

#### 定理 11.2（对角量子分支的复关系递归）

设原纯态满足 $\alpha_0\alpha_1\alpha_3\alpha_{13}\ne0$。明确给定对角量子仪器 $M_o=\operatorname{diag}(m_{o,s})$，满足 $\sum_o|m_{o,s}|^2=1$。选一条正概率结果且四底角乘子非零，纯态分支为 $\alpha'_s=m_{o,s}\alpha_s/\sqrt{q_o}$。则

$$
\begin{aligned}
\Omega'&=\Omega\frac{m_{o,0}m_{o,13}}{m_{o,1}m_{o,3}},
\end{aligned}
$$

$$
\begin{aligned}
\eta'&=\eta+\log\left|\frac{m_{o,0}m_{o,13}}{m_{o,1}m_{o,3}}\right|^2,
\end{aligned}
$$

$$
\begin{aligned}
\Phi'&=\Phi+\arg\frac{m_{o,0}m_{o,13}}{m_{o,1}m_{o,3}}\pmod{2\pi}.
\end{aligned}
$$

因此 $\log\Omega$ 在模 $2\pi i$ 的意义下逐次相加。

<a id="proof-11-2"></a>

**证明。** 
直接代入 $\Omega$；两个分子与两个分母中的 $\sqrt{q_o}$ 相消。取模平方对数与相位，分别得到后两式。仪器完备性保证总分支概率为一，但不用于代数抵消。
 ∎

这把“预测过程仍有相同递归结构”变成可检验的更新律：真实似然或 Kraus 分支决定每次增量，完整记录决定采用哪条分支。因子化幅度的对角局部操作保持 $\Omega$；非因子化幅度能改变它。仅有似然因子化会保持 $\eta$，但仍可通过非因子化相位改变 $\Phi$。

对固定的一组对角操作，乘子可交换，复关系增量的和与排列无关。一般量子操作不对角，或者后续选择依赖已得记录时，不能省略其依赖与相容条件。这一节给出的是同一来源上的递归更新，不把任意重排都宣称为同一操作。

<a id="sec-12"></a>

## 12. 黄金门：融合加乘、勾股三角与编织相位

<a id="statement-12-1"></a>

#### 定义 12.1（明确供应的 Fibonacci 融合规则）

给定两个简单标签 $\mathbf1,\tau$，其融合满足

$$
\tau\otimes\tau=\mathbf1\oplus\tau.
$$

设正重量 $d$ 对 $\oplus$ 相加、对 $\otimes$ 相乘，且 $d(\mathbf1)=1$。

<a id="statement-12-2"></a>

#### 定理 12.2（融合加乘选出黄金归一三角）

记 $d=d(\tau)>0$，则

$$
d^2=1+d,\quad d=\varphi=\frac{1+\sqrt5}{2},\quad
\frac1{\varphi^2}+\frac1\varphi=1.
$$

将两个归一通道权重作为平方幅度，令

$$
a=\varphi^{-1},\qquad b=\varphi^{-1/2},
$$

则 $a^2+b^2=1$，并且

$$
F=\begin{pmatrix}a&b\\b&-a\end{pmatrix}
\quad\text{满足}\quad F^T=F,\quad F^2=I,\quad\det F=-1.
$$

<a id="proof-12-2"></a>

**证明。** 
对融合式施加重量映射，得到 $d^2=1+d$，唯一正根是 $\varphi$。除以 $d^2$ 得两个归一权重。将正平方根取作第一列，再以实正交补全得到第二列；直接矩阵乘法给所列性质。
 ∎

这里 $d$ 是融合的正量子维数或扩展重量，不是要求一个有限单粒子 Hilbert 空间有非整数个基向量。一般归一三角 $a^2+b^2=1$ 有连续多个解，具体融合递归或等价的 $b^2=a$ 自相似条件选出黄金值。项目中的 Fibonacci $F$ 块还带有其模型的结合相容数据；$F^2=I$ 单独不证明全部五边形与六边形相容方程。标准模型背景与该 $F$ 矩阵见 [5](#ref-hg)。

<a id="statement-12-3"></a>

#### 命题 12.3（算符形式的勾股）

用 Pauli 算符写 $F=a\sigma_z+b\sigma_x$。由于

$$
\sigma_z^2=\sigma_x^2=I,\qquad
\sigma_z\sigma_x+\sigma_x\sigma_z=0,
$$

所以 $F^2=(a^2+b^2)I$。这里的反对易算符关系属于所给二维相干块，原始三个可同时读取的占位算符则两两交换。

<a id="statement-12-4"></a>

<a id="thm-braid"></a>

#### 定理 12.4（投影相容决定相对编织相位）

设不同的非零自伴投影 $P,Q$ 满足

$$
PQP=\lambda P,\qquad QPQ=\lambda Q,
$$

令 $z\ne1$、$G_P=I+(z-1)P$、$G_Q=I+(z-1)Q$。则

$$
G_PG_QG_P=G_QG_PG_Q
\quad\Longleftrightarrow\quad z+\lambda(z-1)^2=0.
$$

若 $|z|=1$、$z=e^{i\theta}$，则等价于

$$
\boxed{4\lambda\sin^2(\theta/2)=1.}
$$

在 $0\le\lambda<1$ 的投影重叠范围内，存在非平凡酉相位解当且仅当 $\lambda\ge1/4$。

<a id="proof-12-4"></a>

**证明。** 
令 $u=z-1$。用投影等式展开两边，公共项抵消，差为

$$
(u+u^2+\lambda u^3)(P-Q).
$$

由于 $u\ne0$ 且 $P\ne Q$，等价于 $1+u+\lambda u^2=0$。除以 $z$ 并用 $z+z^{-1}=2\cos\theta$ 得 $1+\lambda(2\cos\theta-2)=0$。存在性由 $0\le\sin^2\le1$ 及反向选角得到。
 ∎

<a id="statement-12-5"></a>

#### 推论 12.5（黄金手性相位）

若 $\lambda=\varphi^{-2}$，则相对相位为

$$
z=e^{\pm3\pi i/5}.
$$

<a id="proof-12-5"></a>

**证明。** 
方程化为 $z^2+\varphi^{-1}z+1=0$；因 $2\cos(3\pi/5)=-\varphi^{-1}$，两单位根如上。共同乘在两个门上的标量相位不影响三重关系，因此这里只确定相对本征相位及其共轭手性。
 ∎

<a id="statement-12-6"></a>

#### 定理 12.6（相容相位把三角边平方变成转移权重）

取 $a=\sqrt\lambda$、$b=\sqrt{1-\lambda}$，

$$
P=|1\rangle\langle1|,\qquad
Q=\begin{pmatrix}b^2&ab\\ab&a^2\end{pmatrix}.
$$

若上述非平凡酉编织关系成立，则 $G_Q$ 对任一计算基输入的保持概率是 $\lambda$，翻转概率是 $1-\lambda$。黄金情形得到

$$
\boxed{T=\begin{pmatrix}\varphi^{-2}&\varphi^{-1}\\
\varphi^{-1}&\varphi^{-2}\end{pmatrix}.}
$$

<a id="proof-12-6"></a>

**证明。** 
向量 $(b,a)^T$ 为单位向量，故 $Q$ 为秩一投影，且与 $P$ 的重叠为 $a^2=\lambda$。定理 [12.4](#statement-12-4) 给 $|z-1|^2=1/\lambda$。非对角矩阵元为 $(z-1)ab$，其 Born 权重为

$$
|(z-1)ab|^2=\lambda^{-1}\lambda(1-\lambda)=1-\lambda.
$$

酉性使每列概率和为一，故保持权重为 $\lambda$。
 ∎

这条证明链同时使用了融合加乘、三角归一、投影重叠、相容相位和平方读出。项目路径投影的相邻编织关系在指定合法路径表示中成立；不能不加检验地推广到所有物理比特的任意子空间。$F$ 在这里也可以只是比较基底的矩阵，不因此被当成原生菜单里免费可调用的门。

<a id="sec-13"></a>

## 13. 指数门、谱与记录后的概率电路

<a id="statement-13-1"></a>

#### 命题 13.1（同一个黄金门的两种递归）

令 $n_L,n_R$ 为左右占位投影，$Q_C$ 为前节的黄金 $Q$ 作用于中位，所有算符在未注明的位置上张量恒等。项目投影与固定门为

$$
\mathcal P=n_Ln_R+(I-n_L)(I-n_R)Q_C,
\qquad K=\zeta[I+(\zeta-1)\mathcal P],\quad \zeta=e^{3\pi i/5}.
$$

其活跃二维块采用有序基 $(|000\rangle,|010\rangle)$。则

$$
K^m=\zeta^m(I-\mathcal P)+\zeta^{2m}\mathcal P,
\qquad K^{10}=I.
$$

在其活跃二维块，若每步后都完全去相干，概率按前节 $T$ 递归，且

$$
T^m=\frac12\begin{pmatrix}1+r^m&1-r^m\\1-r^m&1+r^m\end{pmatrix},
\qquad r=2-\sqrt5=-\varphi^{-3}.
$$

因此 $T^{10}\ne I$，而 $T^m$ 趋于两列均为均匀律的矩阵。

<a id="proof-13-1"></a>

**证明。** 
$\mathcal P$ 与 $I-\mathcal P$ 为互补谱投影，直接求幂。$\zeta^{10}=1$ 给十阶返回。$T$ 在对称方向的本征值为一，在反对称方向的本征值为 $2\varphi^{-2}-1=2-\sqrt5$；分解两本征方向得到幂公式，且 $|r|<1$。
 ∎

相干电路的每步先平方再按概率组合，会加入记录或去相干这一实际操作。由此得到的谱和递归应在相应模型内解释。固定门的有限阶返回与概率混合可以同时成立，因为它们是两个明确不同的实验安排。

<a id="statement-13-2"></a>

#### 定理 13.2（矩阵指数的范围）

每个有限维酉矩阵都可写为 $U=e^{iH}$，其中 $H$ 为 Hermitian；一般 $H$ 不唯一。若 $A,B$ 交换，则 $e^{A+B}=e^Ae^B$。若要求该等式对全部小参数同时成立，则

$$
e^{sA}e^{sB}-e^{s(A+B)}=\tfrac{s^2}{2}[A,B]+O(s^3)
$$

使 $[A,B]=0$ 成为必要条件。

<a id="proof-13-2"></a>

**证明。** 
对 $U$ 取正交谱分解 $U=\sum_je^{i\theta_j}P_j$，令 $H=\sum_j\theta_jP_j$。各 $\theta_j$ 加 $2\pi$ 的整数倍仍给同一 $U$。交换情形可用幂级数二项展开；一般情形逐项比较二阶系数即得差式。
 ∎

例如 $K=e^{i(3\pi/5)(I+\mathcal P)}$，但也可为其某条谱相位另选对数分支。一个静态门矩阵因此不唯一确定物理 Hamiltonian、作用时长或能量尺度。复数还有相消：$1+(-1)=0$，所以相干幅度不能通过正权半环的无损映射同时保存其加乘与非零支撑。

<a id="statement-13-3"></a>

#### 命题 13.3（三个态的相位三角约束）

对三个单位态 $u,v,w$，令 $a=\langle u,v\rangle$、$b=\langle v,w\rangle$、$c=\langle w,u\rangle$。它们的 Gram 正性要求

$$
\boxed{|a|^2+|b|^2+|c|^2\le1+2\operatorname{Re}(abc).}
$$

加上 $|a|,|b|,|c|\le1$，该条件也足以在某个复 Hilbert 空间实现这些重叠。若三态位于二维空间，则等号成立。

<a id="proof-13-3"></a>

**证明。** 
Gram 矩阵为

$$
G=\begin{pmatrix}1&a&\bar c\\\bar a&1&b\\c&\bar b&1\end{pmatrix}.
$$

行列式展开得到不等式；三个二阶主子式给模长条件。全部主子式非负等价于 Hermitian 矩阵正半定，取矩阵平方根实现为 Gram。二维空间中 $\operatorname{rank} G\le2$，所以行列式为零。
 ∎

环积 $abc$ 在各态重定相位下不变。这又是一种三角关系，但其边是态的重叠；若三态真正两两正交，则三边重叠全零，环相位没有定义。它与五模式占位坐标中的直角三角形应按各自载体使用。

<a id="sec-14"></a>

## 14. 本轮形成的理论与可检验的后续问题

现在可以把“它们都有关联”写成一组保持运算的映射：

$$
\begin{aligned}
\text{正权电路的加乘}
&\xrightarrow{\log}\text{log-sum-exp 与加法},
\end{aligned}
$$

$$
\begin{aligned}
\text{五模式四角乘积比}
&\xrightarrow{\log}\text{隐藏关联的对偶坐标 }\eta,
\end{aligned}
$$

$$
\begin{aligned}
\text{三读出相容纤维}
&\xrightarrow{\text{最大熵投影}}\text{KL 勾股分解},
\end{aligned}
$$

$$
\begin{aligned}
\text{正交直和与张量复合}
&\xrightarrow{ \left\lVert \cdot\right\rVert ^{2}}\text{可加与可乘的重量},
\end{aligned}
$$

$$
\begin{aligned}
\text{条件复振幅表 }M
&\longmapsto(\eta,\Phi;\,st/R^2)
\longmapsto\text{纠缠双平方和},
\end{aligned}
$$

$$
\begin{aligned}
\tau\otimes\tau=\mathbf1\oplus\tau
&\xrightarrow{d}\varphi^2=1+\varphi
\xrightarrow{\text{相容}}\text{黄金门的相位与转移权重}.
\end{aligned}
$$

<a id="table-1"></a>

| 层次 | 精确对象 | 勾股或相容结论 |
| --- | --- | --- |
| 欧氏占位几何 | 五点与指定标准内积 | 九直角一等边；两剖分对应纤维两端 |
| 概率信息几何 | 同一五律、最大熵参考 | KL 分解；Fisher 可见与隐藏切向正交 |
| 统计记录几何 | 同源后验均值及记录权重 | 三记录最小性；协方差等于面积平方加和 |
| 复振幅几何 | 条件两比特纯态和四角复比 | 双曲平方加相位平方；$C^2+\lvert r\rvert^2=1$ |
| 黄金相干块 | 融合规则、投影与编织关系 | 黄金归一三角及相对相位 $e^{\pm3\pi i/5}$ |

本轮的中心推进是定理 [9.3](#statement-9-3)、[10.2](#statement-10-2) 及复关系递归：它们把“关系也需要预测”变成明确的缺失参数与可检验恒等式。三个稳定读出控制可见部分；$\eta$ 度量底面概率关系；$\Phi$ 是这些概率不显示的一项相干关系。把实际观测过程写成 Kraus 分支后，其递归增量也有确定的复对数形式。

接下来的关键任务可以按实际读出提出。首先，给一个具体允许仪器菜单，说明怎样取得 $\kappa$ 与相位回路，而不仅是定义它们。其次，为该取得协议证明误差、样本、相干控制和门数成本；最新 Walsh 结果提醒我们不能用一个表示范数代替所有资源下界。再次，针对某项操作，验证它是否保持所用条件纯态、独立性或最大熵族；这些条件决定哪一种勾股式继续有效。

项目[《相干重构续卷》](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)§67.3 仍把复标量、Born 测量、系统组合和动力学的起源列为未闭合的桥。本文给出了在明确结构中通往这些问题的约束方程；如果要声称从更少公理重建量子理论，还须证明所需结构由那些公理唯一或操作等价地得到。黄金门的已有普适性也应继续按 v15 的编码、可用地址和近似闭包使用；有限精确实现与任意精度逼近仍有算术差别。

<a id="sec-bibliography"></a>

## 文献与固定项目来源

<a id="ref-cs"></a>

**[1]** I. Csiszár and P. C. Shields.
*Information Theory and Statistics: A Tutorial*.
Foundations and Trends in Communications and Information Theory 1(4), 2004,
尤其 §3 的信息投影与勾股恒等式。
[作者机构全文](https://www.renyi.hu/~csiszar/Publications/Information_Theory_and_Statistics:_A_Tutorial.pdf)。

<a id="ref-wj"></a>

**[2]** M. J. Wainwright and M. I. Jordan.
*Graphical Models, Exponential Families, and Variational Inference*.
Berkeley Technical Report 649, 2003。
[机构报告页面](https://statistics.berkeley.edu/tech-reports/649)。

<a id="ref-bcp"></a>

**[3]** T. Baumgratz, M. Cramer and M. B. Plenio.
*Quantifying Coherence*.
Physical Review Letters 113, 140401 (2014)，尤其式 (8)。
[arXiv:1311.0275](https://arxiv.org/abs/1311.0275)。

<a id="ref-wootters"></a>

**[4]** W. K. Wootters.
*Entanglement of Formation of an Arbitrary State of Two Qubits*.
Physical Review Letters 80, 2245--2248 (1998)。
[作者预印本](https://arxiv.org/abs/quant-ph/9709029)。

<a id="ref-hg"></a>

**[5]** L. Hadjiivanov and L. S. Georgiev.
*Braiding Fibonacci Anyons* (2024)，尤其 §3、式 (3.10)。
[arXiv:2404.01778](https://arxiv.org/abs/2404.01778)。

<a id="ref-found"></a>

**[6]** trureturing，固定提交 `d3c5bc77…`。
[AURIC 金字塔基础公式与关系](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，§§2--6、9、命题 15.3。

<a id="ref-record"></a>

**[7]** 同提交。
[读口完整分类与记录三角形](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md)，尤其 §§2--9。
该文为用户稿转录，其普通证明与旧实验自述的证据身份分开。

<a id="ref-moment"></a>

**[8]** 同提交。
[关系三角形与反演精度](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_MOMENT_TRIANGLES_AND_INVERSE_PRECISION.md)，§§3--4 及金字塔联系。

<a id="ref-phase"></a>

**[9]** 同提交。
[概率、相位运输与完整回路](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)，§§2.1--2.2。

<a id="ref-v14"></a>

**[10]** 同提交。
[存在量词、电路半环与量子记录 v14](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)。
前稿转录，作为研究连续性使用。

<a id="ref-v15"></a>

**[11]** 同提交。
[黄金门的 NAND 式普适性与精确算术边界 v15](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)，§§3--6、9。
前稿转录，保留编码、门菜单与近似／精确之区分。

<a id="ref-latest"></a>

**[12]** 同提交。
[真实切面恢复](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md)，本轮新增 §§18--20；
[统一联合律桥](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)，本轮新增 §2。

<a id="ref-quantum"></a>

**[13]** 同提交。
[量子原则与相干重构续卷](https://github.com/the-omega-institute/trureturing/blob/d3c5bc77408d91c0f11eb05bf86e8876a7cd7f4a/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，§§64--67。
本轮未变更；§67.3 的起源桥仍开放。
