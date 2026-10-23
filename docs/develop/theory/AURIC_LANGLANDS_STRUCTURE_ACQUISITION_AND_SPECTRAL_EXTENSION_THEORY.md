# AURIC–Langlands 结构取得与谱延拓理论

预测增长、二拷贝张量、关系球面与 Hecke 相容性的定义和证明。

> **范围。** 本卷是纯理论 Markdown 正文。它把新增结构写成有限维普通数学命题，
> 不增加 `.tex`、Lean、消化记录或实验材料。除明确标为外部输入的几何 Satake、
> Riemann–Hilbert 与几何朗兰兹结果外，定理均由文中给出的证明承担；本卷没有声称
> 整卷已经通过 Lean 编译。
>
> **固定快照。** 结构比较以提交 `af80fa178cd445406a7be55aeb4d9e9599a21b66`
> 为当前快照，以 `f38e7d6dad5d17bf396a26b6b03b2eed6a3728d4` 为基线。仓库已有的
> 《AURIC FIB 关系丛与预测闭包理论》作为前置数学背景；本卷只引用它已经明确的
> 合同，不把经典来源、量子态、控制门、内部记忆、局部系统和自守对象混成一个载体。

## 摘要

本卷研究结构取得何时真正增加预测能力，以及五模式关系丛怎样产生可检验的谱接口。
旧摘要封闭的内部反馈只能对旧摘要作随机后处理，不能分裂旧纤维。新增末端读口的全部
未来增量由旧盲空间上的残余可观测系统给出，并在至多有限个词长层后稳定。增长所得的
短正合列一般不按动力学分裂；固定读口目录的捕获函数次模，而控制菜单可以有互补协同。

在指定实结构、独立同分布制备和完整实联合效果的条件下，二拷贝统计把任意密度态确定到
复共轭轨道；一个校准的非实参考进一步消除该二元歧义。五模式的虚部二次张量有显式的
$SO(5)$ 等变满射

$$
\operatorname{Sym}^2(\mathfrak{so}_5)
\twoheadrightarrow \mathbf 1\oplus \operatorname{Sym}^2_0(\mathbb C^5)\oplus\mathbb C^5,
\qquad 55=1+14+5+35.
$$

该态射粘合为平行局部系统态射，并在几何 Satake 与 Hecke 本征结构中保持自然性。关系
球面上的非零 Chern 向量说明预量子线丛不能直接成为无奇点平坦谱局部系统；取最大可平坦
环面商只能消除丛的拓扑障碍，球面本身的无奇点平坦单值仍然平凡。另选四穿孔并给出三
个独立控制时可以构造稠密 $SO_5(\mathbb C)$ 单值，但无理角分歧不能用有限覆叠消去。

## 1. 本次理论增量与证明责任

### 1.1 固定快照与来源边界

本卷保留以下增量：关系丛理论中的正则关系球面、Chern 向量、预量子整性、预测闭包和
内部观察者；有限联合预测中的有限祖先签名与预算边界；以及本卷新增的残余系统、二拷贝
分类、张量分裂、Hecke 自然性和穿孔谱构造。

固定快照的比较接口可能截断文件列表，因此“前后提交差异”不被当作完整变更清单。对
`docs/develop/theory` 的文件 blob 逐项比较才用于目录级增量。本文引用的仓库理论文本
只承担所引用的既有定理；读过 `NativeTimeProfile.lean` 的源声明不等于重新编译整个
工程，也不把原生树复制定理当作量子复制定理。

### 1.2 三种复制必须分开

1. 原生有序对象的带标签并行复制，可产生整数剖面；
2. 来源允许重新独立制备，因而提供 $\rho^{\otimes k}$；
3. 从一份任意未知态制造另一份相同态。

后两项分别是来源合同和不可克隆问题。第一项不自动供应第二项，第二项也不允许把第三项
当作免费操作。

### 1.3 外部输入

本卷使用以下外部数学接口：向量丛的 clutching 分类和 Chern–Weil 公式；正则奇
Riemann–Hilbert 对应；Tannaka 重构；$Sp_4$ 与 $SO_5$ 的几何 Satake 等价；以及特征零
无分歧几何朗兰兹中的 Hecke 本征对象存在性。它们的适用条件在相应章节逐项写出。

## 2. 结构取得与残余预测增长

### 2.1 旧摘要封闭的内部协议

**定义 2.1（旧摘要封闭）。** 设来源为 $x\in X$，已有摘要为 $q:X\to Q$。一个
协议对 $q$ 封闭，是指初始记忆律、各步更新核、动作选择和停止规则只依赖 $q(x)$、
已经得到的记录以及与来源独立的随机性；协议不增加来源读口。记录空间取标准 Borel
空间，核和停止规则可测，允许有限步或几乎必然有限的停止时间。

**定理 2.2（内部重编码不能细化旧纤维）。** 对任一旧摘要封闭协议，输出律存在核
$K$ 使

$$
\mathcal L(R\mid x)=K(q(x),\,\cdot).
$$

因此 $q(x)=q(y)$ 时完整输出律相同。若输出几乎必然等于确定属性 $a(x)$，则存在
$\bar a$ 满足 $a=\bar a\circ q$。

**证明。** 初始记忆律只依赖 $q(x)$。若长度 $t$ 的记录律已经因子化，下一步更新
核仍只依赖摘要和旧记录；对旧记录积分后，长度 $t+1$ 的律仍因子化。有限时域输出
是记录前缀的后处理。若停止时间 $T<\infty$ 几乎必然，则对任意输出事件 $B$，

$$
\Pr_x(R\in B)=\sum_{t\ge0}\Pr_x(T=t,R\in B),
$$

每一项由有限前缀决定，故同样因子化。确定输出给出相等的 Dirac 测度，所以属性在
每条 $q$ 纤维上恒定。$□$

这允许在原菜单内进行反馈：若旧预测保存每个实际输出分支，同一摘要和同一记录选择
同一动作。读取来源相关标签、取得来源相关初始记忆或使用新的联合测量则改变合同，
不能被上述不分裂结论覆盖。

### 2.2 残余可观测系统

**定义 2.3（残余系统）。** 令 $V$ 为有限维实向量空间，$T_a:V\to V$ 为原有总定义
线性分支，$a\in\mathcal A$。旧全未来效果空间 $O\subset V^*$ 满足
$T_a^*O\subseteq O$，并令

$$
N=\{v\in V:\ell(v)=0\text{ 对所有 }\ell\in O\}.
$$

于是 $T_aN\subseteq N$。增加末端线性读口 $A:V\to\mathbb R^s$，保留旧分支并定义

$$
K_A=N\cap\bigcap_{w\in\mathcal A^*}\ker(AT_w),
$$

其中空词包含在内。置 $m=\dim N$、$r=\operatorname{rank}(A|_N)$，并在 $N^*$ 中
递推

$$
M_0=\operatorname{rowspan}(A|_N),\qquad
M_{k+1}=M_k+\sum_{a\in\mathcal A}(T_a|_N)^*M_k.
$$

**定理 2.4（残余增长公式）。** 新全未来盲空间恰为 $K_A$。它是包含于
$N\cap\ker A$ 的最大共同不变子空间，并存在与所有旧分支交换的短正合列

$$
0\longrightarrow N/K_A\longrightarrow V/K_A
\longrightarrow V/N\longrightarrow0.
$$

新增预测维数为

$$
\Delta_A=\dim N-\dim K_A=\dim M_\infty=\dim M_{m-r}.
$$

特别地，$A|_N=0$ 时 $\Delta_A=0$。

**证明。** 旧效果与所有 $AT_w$ 的分量张成新效果空间，其共同零化子正是 $K_A$。
若 $L\subset N\cap\ker A$ 共同不变，则 $T_wL\subseteq L$，故 $AT_wL=0$，从而
$L\subseteq K_A$；最大性成立。商映射 $[v]_{K_A}\mapsto[v]_N$ 满射，核为
$N/K_A$，而两层核都对每个 $T_a$ 不变，因此各箭头交换动力学。

归纳可得 $M_k$ 由长度不超过 $k$ 的 $AT_w|_N$ 的行张成，故
$K_A=M_\infty^\perp$。若 $M_{k+1}=M_k$，它已经对全部拉回不变，递推不再增长。
从初始维数 $r$ 到至多 $m$ 每次严格增长至少一维，至多 $m-r$ 轮稳定。$□$

该界只控制线性闭包轮数，不控制系数求取、数值精度、制备、采样或记录成本。密度态
版本还必须在迹一仿射超平面处理归一化方向。

### 2.3 不按动力学分裂的扩张

**定理 2.5（预测增长可以不分裂）。** 旧动力学即使是三个经典状态上的随机通道，
上述短正合列也未必有动力学相容的线性截面。

**证明。** 取列随机矩阵

$$
T=\begin{pmatrix}1&1/2&0\\0&1/2&1/2\\0&0&1/2\end{pmatrix},
\qquad \tau(p)=p_1+p_2+p_3,
\qquad f(p)=p_3.
$$

有 $\tau T=\tau$、$fT=f/2$，所以 $N=\mathbb R n$，其中 $n=e_1-e_2$。增加
$A(p)=p_2$ 得 $K_A=0$。令 $m=e_2-e_3$，则

$$
Tn=\tfrac12n,\qquad Tm=\tfrac12m+\tfrac12n.
$$

商中 $[m]$ 是非零的 $1/2$ 特征向量，而 $(T-\tfrac12I)v=0$ 的全部解为 $N$。
若存在动力学相容截面 $s$，则 $s([m])$ 必须是 $N$ 中的特征向量，故其商为零，
与 $s$ 为截面矛盾。$□$

## 3. 结构价值、目录选择与取得成本

### 3.1 固定读口的捕获函数

**定义 3.1。** 对有限来源集合 $X$，$|X|=n\ge2$，固定读口目录
$f_j:X\to Y_j$，置

$$
P=\{(x,y):x\ne y\},\qquad
D_j=\{(x,y)\in P:f_j(x)\ne f_j(y)\},
$$

并定义

$$
C(S)=\left|\bigcup_{j\in S}D_j\right|,qquad
 e(S)=1-\frac{C(S)}{n(n-1)}.
$$

目录项是具体出现的读口；相同函数若以不同标签出现仍保留两个索引。

**定理 3.2（固定目录次模性）。** $C$ 单调且次模。若 $S\subseteq T$、$j\notin T$，则

$$
C(S\cup\{j\})-C(S)\ge C(T\cup\{j\})-C(T).
$$

删除 $j\in S$ 的损失为

$$
C(S)-C(S\setminus\{j\})
=\left|D_j\setminus\bigcup_{i\in S\setminus\{j\}}D_i\right|.
$$

**证明。** 加入 $j$ 的边际收益是
$|D_j\setminus\bigcup_{i\in S}D_i|$；$S$ 增大只会扩大被减去的集合。删除式是同一
集合恒等式。$□$

**推论 3.3（等成本贪心界）。** 每项成本相同、预算为 $k\ge1$ 时，逐次选择边际
捕获最大的读口，所得 $S_k$ 满足

$$
C(S_k)\ge\left[1-(1-1/k)^k\right]\operatorname{OPT}
\ge(1-e^{-1})\operatorname{OPT}.
$$

证明是标准的次模贪心递推：最优集合相对于当前集合的边际收益总和至少为剩余差，
其中一项至少贡献 $1/k$，迭代即可。该保证支付不了评估所有目录项的实际成本。

### 3.2 控制协同不必次模

**定理 3.4（控制菜单的互补性）。** 取 $X=\{0,1,2,3\}$，末端读口
$f=\mathbf1_{\{3\}}$，排列控制 $a=(0\ 2)$、$b=(2\ 3)$。允许由所选控制组成的
有限词，则 $a$ 单独无收益，在已有 $b$ 时却有严格正收益。

**证明。** 四种菜单的全未来等价类和有序捕获数为

| 菜单 | 等价类 | 捕获数 |
|---|---|---:|
| $\varnothing$ | $\{0,1,2\},\{3\}$ | $6$ |
| $\{a\}$ | $\{0,1,2\},\{3\}$ | $6$ |
| $\{b\}$ | $\{0,1\},\{2\},\{3\}$ | $10$ |
| $\{a,b\}$ | $\{0\},\{1\},\{2\},\{3\}$ | $12$ |

因为 $f\circ a=f$、$f\circ b=\mathbf1_{\{2\}}$、$f\circ b\circ a=\mathbf1_{\{0\}}$，
表格成立。加入 $a$ 的边际收益由 $0$ 变为 $2$，违反次模性。效果空间维数
$2,2,3,4$ 也给出同一反例。$□$

### 3.3 低维精确分辨不保证低样本成本

**定理 3.5（指数样本下界）。** 对
$P_0=\operatorname{Bernoulli}(1/2)$ 与
$P_\eps=\operatorname{Bernoulli}(1/2+\eps)$，任一至多使用 $n$ 个独立样本、平均错误率
不超过 $1/3$ 的协议满足

$$
 n\ge \frac{\log(13/9)}{\log(1+4\eps^2)}
 \ge \frac{\log(13/9)}{4\eps^2}.
$$

当 $\eps=2^{-L}$ 时，需要 $\Omega(4^L)$ 个样本，尽管一个二元读口即可精确
区分两个概率律。

**证明。** $n$ 个样本的似然比 $\Lambda$ 满足
$\mathbb E_0\Lambda=1$、$\mathbb E_0\Lambda^2=(1+4\eps^2)^n$。因此

$$
\operatorname{TV}(P_0^{\otimes n},P_\eps^{\otimes n})
\le\tfrac12\sqrt{(1+4\eps^2)^n-1}.
$$

平均错误率至少为 $(1-\operatorname{TV})/2$。错误率 $\le1/3$ 要求总变差至少
$1/3$，于是 $(1+4\eps^2)^n\ge13/9$。取对数并使用
$\log(1+t)\le t$。提前停止的协议是完整样本的后处理，故同样受限。$□$

## 4. 二拷贝观察与复共轭商

### 4.1 实结构合同

**定义 4.1。** 固定 $H=\mathbb C^d$ 及指定实基。密度态唯一写为

$$
\rho=S+iA,qquad S^{\mathsf T}=S,\quad A^{\mathsf T}=-A,quad S,A\in M_d(\mathbb R).
$$

实效果是满足 $0\le E\le I$ 的实对称矩阵。二拷贝结果另要求来源能够独立重复制备
$\rho^{\otimes2}$，并且联合载体允许的实效果张成全部实对称矩阵。单系统实门菜单不
自动提供这两个条件。

单拷贝实效果只看 $S$：$\operatorname{tr}(E\rho)=\operatorname{tr}(ES)$。
在 $D$ 维联合载体上，设置

$$
P_i=|e_i\rangle\langle e_i|,qquad
P_{ij}=\tfrac12|e_i+e_j\rangle\langle e_i+e_j|
$$

可由 $R_{ii}=p(P_i)$、
$R_{ij}=p(P_{ij})-[p(P_i)+p(P_j)]/2$ 重构实对称部分。它们是多个测量设置，
不是一个正交测量的同时结果。

### 4.2 二拷贝完整分类

**定理 4.2（任意混态的二拷贝分类）。** 对密度态 $\rho,\rho'$，以下等价：

1. 全部实二拷贝效果给出相同统计；
2. $\rho'=\rho$ 或 $\rho'=\bar\rho$；
3. 对所有 $k\ge1$，全部实 $k$ 拷贝效果给出相同统计。

实际上每个固定 $k\ge2$ 的完整实联合统计都恰好确定一个复共轭轨道。

**证明。** 二拷贝实统计确定

$$
R_2(\rho)=\operatorname{Re}(\rho\otimes\rho)=S\otimes S-A\otimes A.
$$

对第二因子取部分迹得到 $S$，因为 $\operatorname{tr}S=1$、$\operatorname{tr}A=0$。相同
统计继而给出 $A\otimes A=A'\otimes A'$。实向量空间中
$a\otimes a=b\otimes b$ 蕴含 $b=\pm a$：若 $a\ne0$，用一个不在 $a$ 的核中的线性
泛函收缩即可；$a=0$ 时结论直接成立。因此 $A'=\pm A$，即 $\rho'=\rho$ 或
$\bar\rho$。反向显然，因为实效果的概率是实数。任意 $k\ge2$ 的完整统计包含
$E\otimes I^{\otimes(k-2)}$，故可以恢复二拷贝统计。$□$

在五模式中，单拷贝实摘要的归一化维数为 $14$。二拷贝在 $A\ne0$ 的开域中保留
实维 $24$ 的轨道商，但保留两个候选态；$A=0$ 是固定点层。这是非线性轨道商，
不是原 $25$ 维实态空间上的线性核商。

**命题 4.3（局部操作边界）。** 只供应独立副本、局部实操作和经典反馈时，任意
分支概率只依赖 $S$，因为

$$
\operatorname{tr}[(E_1\otimes\cdots\otimes E_k)\rho^{\otimes k}]
=\prod_j\operatorname{tr}(E_jS).
$$
若不保证 i.i.d.，联合实统计不能识别单一来源的隐藏虚部。

**证明。** 迹的张量乘法性给出第一式。对相关来源

$$
\Omega=\tfrac12\rho\otimes\rho+\tfrac12\bar\rho\otimes\bar\rho
=S\otimes S-A\otimes A,
$$

其边缘为 $S$，且对实联合效果与 $\rho^{\otimes2}$ 相同。因此独立制备条件不可省略。
$□$

### 4.3 稳定性与二次不变量

**命题 4.4。** 固定 $S$，令 $A$ 的坐标为 $a_1,\ldots,a_m$。在 $A\mapsto-A$ 下
不变的多项式环由所有二次乘积 $a_ia_j$ 生成。并置

$$
\delta(A,B)=\min(\|A-B\|_F,\|A+B\|_F),qquad
D(A,B)=\|A\otimes A-B\otimes B\|_F.
$$

则

$$
\delta(A,B)\le2^{1/4}D(A,B)^{1/2};
$$

若 $\|A\|_F,\|B\|_F\ge a_0>0$，还有
$\delta(A,B)\le D(A,B)/a_0$。

**证明。** 通过整体符号选择使 $c=\langle A,B\rangle_F\ge0$，记
$u=\|A\|_F,v=\|B\|_F$。则

$$
\delta^2=u^2+v^2-2c,qquad D^2=u^4+v^4-2c^2,
$$

并有

$$
2D^2-\delta^4=(u^2-v^2)^2+4c\delta^2\ge0,
$$

$$
D^2-\tfrac12(u^2+v^2)\delta^2
=\tfrac12(u^2-v^2)^2+c\delta^2\ge0.
$$

两式分别给出两项界。$□$

## 5. 校准相位参考与可调用操作

**定理 5.1（已校准参考的线性恢复）。** 已知参考态
$\sigma=T+iB$ 满足 $B\ne0$，系统和参考独立，且完整实联合效果可用时，

$$
R_\sigma(\rho)=\operatorname{Re}(\rho\otimes\sigma)=S\otimes T-A\otimes B
$$

唯一确定 $\rho$。对收缩
$\mathcal C_C(X\otimes Y)=X\langle C,Y\rangle_F$，有

$$
S=\frac{\mathcal C_T(R_\sigma)}{\|T\|_F^2},qquad
A=-\frac{\mathcal C_B(R_\sigma)}{\|B\|_F^2}.
$$

**证明。** 对称与反对称矩阵在 Frobenius 内积下正交，分别收缩即可；$T$ 的迹为一
所以 $T\ne0$，$B\ne0$ 是假设。$□$

两态差满足精确恒等式

$$
\|R_\sigma(\rho)-R_\sigma(\rho')\|_F^2
=\|S-S'\|_F^2\|T\|_F^2+\|A-A'\|_F^2\|B\|_F^2.
$$

合法参考满足 $\|B\|_F^2\le1/2$，纯量子位
$(1,i)^{\mathsf T}/\sqrt2$ 达到该界。若参考也只知道到复共轭，整体同时共轭仍无法
消除歧义。

**定理 5.2（实来源不能免费生成非实参考）。** 初态和辅助态都为实态、每个仪器分支
都有实 Kraus 算子时，有限自适应组合及正概率后选择的输出仍为实态。

**证明。** 每个未归一化分支为
$\sum_\alpha K_\alpha\rho K_\alpha^{\mathsf T}$，仍为实矩阵；归一化除以正实
概率不改变实性。张量、复合及依记录选择均保持性质，归纳完成。$□$

**定理 5.3（一个相位量子位的精确实化）。** 令

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
r=(1,i)^{\mathsf T}/\sqrt2,qquad Jr=ir.
$$

若 $U=X+iY\in U(d)$，定义

$$
\mathcal R(U)=X\otimes I_2+Y\otimes J,
$$

则 $\mathcal R(U)\in SO(2d)$，且
$\mathcal R(U)(\psi\otimes r)=U\psi\otimes r$。参考 $r$ 被原样返回。

**证明。** $U^\dagger U=I$ 给出
$X^{\mathsf T}X+Y^{\mathsf T}Y=I$ 和
$X^{\mathsf T}Y-Y^{\mathsf T}X=0$。结合 $J^{\mathsf T}=-J,J^2=-I$ 得
正交性。$\mathbb C r$ 和 $\mathbb C\bar r$ 上分别作用为 $U$ 与 $\bar U$，行列式
为 $\det U\det\bar U=1$。最后由 $Jr=ir$ 得作用式；张量线性保证对外部纠缠
也成立。$□$

该构造需要更大的联合控制菜单；不能把单系统 $SO(5)$ 菜单擅自替换为 $SO(10)$。

**例 5.4（五模式相位）。** 取 $J_{12}=E_{12}-E_{21}$，
$\rho_a=I_5/5+iaJ_{12}$，$|a|\le1/5$。单拷贝实统计与 $a$ 无关。令
$\Phi=(|1,1\rangle+|2,2\rangle)/\sqrt2$，则

$$
\operatorname{tr}(|\Phi\rangle\langle\Phi|\rho_a^{\otimes2})=1/25-a^2.
$$

已知 $\sigma_b=I_5/5+ibJ_{12}$ 时，同一设置给 $1/25-ab$，因而第二拷贝只给平方，
校准参考给出符号。

## 6. 隐藏二次关系的表示论分裂

令 $V_5=\mathbb R^5$ 带标准度量和定向，$\mathfrak g=\mathfrak{so}(5)\simeq\Lambda^2V_5$，
并记 $W_{14}=\operatorname{Sym}^2_0V_5$。反对称矩阵 $A$ 对应二形式
$a_A=\sum_{i<j}A_{ij}e_i\wedge e_j$。

**定义 6.1（三个二次协变映射）。** 对 $A\odot B=(A\otimes B+B\otimes A)/2$，置

$$
\sigma(A\odot B)=-\tfrac12\operatorname{tr}(AB),
$$

$$
\gamma(A\odot B)=-\tfrac12(AB+BA)+\frac{\operatorname{tr}(AB)}5I_5,
$$

$$
\beta(A\odot B)=*(a_A\wedge a_B).
$$

$\beta$ 对 $A,B$ 对称，因为二形式楔积交换。

**定理 6.2（五模式二次张量分裂）。** 映射

$$
\Psi=(\sigma,\gamma,\beta):\operatorname{Sym}^2\mathfrak{so}(5)
\longrightarrow \mathbb R\oplus W_{14}\oplus V_5
$$

是 $SO(5)$ 等变满射，核维数为 $35$，并有等变分裂

$$
\operatorname{Sym}^2\mathfrak{so}(5)
\simeq\mathbf1\oplus W_{14}\oplus V_5\oplus K_{35}.
$$

$K_{35}$ 是否不可约不是本定理的断言。复杂化后同样成立于 $SO_5(\mathbb C)$。

**证明。** 迹、矩阵乘法、楔积和 Hodge 星在 $SO(5)$ 作用下自然变换，故三映射等变，
且 $\gamma$ 对称无迹。取 $J_{ij}=E_{ij}-E_{ji}$。五个指标互异时

$$
\Psi(J_{ij}\odot J_{kl})=(0,0,\pm e_m),
$$

故 $V_5$ 可单独命中。对互异 $i,j,k$，
$J_{ik}J_{jk}=-E_{ij}$、$J_{jk}J_{ik}=-E_{ji}$，所以
$\gamma(J_{ik}\odot J_{jk})=(E_{ij}+E_{ji})/2$。又

$$
\gamma(J_{ij}^{\odot2})=E_{ii}+E_{jj}-\tfrac25I_5,
$$

这些元素生成全部 $W_{14}$。最后
$\Theta=\sum_{i<j}J_{ij}^{\odot2}$ 满足 $\Psi(\Theta)=(10,0,0)$，故满射。
定义域维数为 $10\cdot11/2=55$，目标为 $1+14+5=20$，核为 $35$。内积
$-\operatorname{tr}(AB)/2$ 在 $\mathfrak g$ 上正定且不变，核的正交补给出等变分裂。
复杂化由 $SO(5)$ 在 $SO_5(\mathbb C)$ 中的 Zariski 稠密性得到。$□$

二拷贝已确定 $A^{\odot2}$，从而确定
$\|A\|_F^2/2$、$-A^2+\operatorname{tr}(A^2)I/5$ 与
$*(a_A\wedge a_A)$。后者是五维 Pfaffian 型向量：若
$a_A=\lambda_1e_1\wedge e_2+\lambda_2e_3\wedge e_4$，则
$*(a_A\wedge a_A)=2\lambda_1\lambda_2e_5$。

**命题 6.3（有限联合效果取得二次坐标）。** 令 $Y_{ij}=iJ_{ij}$，则

$$
E_{ij,kl}=\tfrac12(I_{25}+Y_{ij}\otimes Y_{kl})
$$

是实联合效果，并满足

$$
\operatorname{tr}(E_{ij,kl}\rho^{\otimes2})=\tfrac12+2A_{ij}A_{kl}.
$$

若这些效果均可调用，至多 $55$ 个二元设置连同单拷贝实层析取得完整
$A^{\odot2}$；若只供应张成族，则可由线性组合计算期望，但实际设置数另计。

**证明。** $Y_{ij}$ 是范数不超过一的 Hermitian 矩阵，故 $E$ 在 $[0,I]$ 中。
又 $\operatorname{tr}(Y_{ij}\rho)=2A_{ij}$，迹的张量乘法性给公式。十个反对称
坐标的对称二次乘积共有 $55$ 项。$□$

## 7. 从张量态射到 Hecke 相容性

**假设 7.1（几何接口）。** $X$ 是光滑连通复曲线，$E$ 是平坦
$SO_5(\mathbb C)$ 局部系统。若调用无分歧几何朗兰兹的本征存在性，另要求 $X$ 射影、
$E$ 不可约并固定半典范归一化。记

$$
V_E=E_{\mathrm{std}},\qquad \mathfrak g_E=\operatorname{ad}E\simeq\Lambda^2V_E,
\qquad W_E=\operatorname{Sym}^2_0V_E.
$$

**定理 7.2（平行分裂）。** 定理 6.2 粘合为平行满射

$$
\Psi_E:\operatorname{Sym}^2(\operatorname{ad}E)	woheadrightarrow
\mathbf1_X\oplus W_E\oplus V_E
$$

和秩 $35$ 的核局部系统 $K_E$，并给出平行分裂

$$
\operatorname{Sym}^2(\operatorname{ad}E)
\simeq\mathbf1_X\oplus W_E\oplus V_E\oplus K_E.
$$

**证明。** 在局部平坦标架中逐纤维应用 $\Psi$。过渡函数在 $SO_5$ 中，而 $\Psi$ 等变，
所以局部映射粘合并与路径输运交换。正交补分裂同样粘合。$□$

**外部定理 7.3（Satake 与无分歧本征对象）。** 对 $G=Sp_4(\mathbb C)$、
$\check G=SO_5(\mathbb C)$，几何 Satake 给出对称张量等价

$$
\operatorname{Sat}:\operatorname{Rep}(\check G)
\simeq\operatorname{Perv}_{G(\mathcal O)}(\operatorname{Gr}_G).
$$

对满足假设 7.1 的不可约 $E$，无分歧几何朗兰兹提供非零 Hecke 本征对象
$\mathcal F_E$ 及对表示 $R$ 的同构

$$
\varepsilon_R:H_R(\mathcal F_E)\xrightarrow{\sim}E_R\boxtimes\mathcal F_E,
$$

并要求它对表示态射、单位、张量和多点融合相容。本卷将此作为外部输入，不重证深层存在性。

**定理 7.4（隐藏二次关系的 Hecke 自然性）。** 对 $\psi=\sigma,\gamma,\beta$ 或
总映射 $\Psi$，记目标表示为 $R'$。则

$$
\varepsilon_{R'}\circ H_\psi(\mathcal F_E)
=(\psi_E\boxtimes\operatorname{id}_{\mathcal F_E})\circ\varepsilon_R.
$$

特别地，$\beta$ 把二次伴随系数的 Hecke 操作映到标准五维系数的 Hecke 操作。

**证明。** $\psi$ 是 $\operatorname{Rep}(SO_5)$ 中的明确态射。Satake 把它送到卷积
对象间态射，Hecke 作用再送到函子间自然变换；本征同构对表示态射的自然性就是所列
交换式。若只有分别存在的本征同构，而没有态射和融合相容性，则不能推出此式。$□$

因此完整链条是

$$
\text{实二拷贝统计}\longrightarrow A^{\odot2}
\xrightarrow{\Psi}(1,14,5)\text{ 系数数据}
\longrightarrow\text{平行局部系统}\longrightarrow\text{Hecke 自然性}.
$$

它没有构造“实验仪器到层范畴”的实现函子；这里使用的是共同表示及其张量态射。

## 8. 关系球面、Chern 向量与最大可平坦环面商

五模式概率写作

$$
 p=(1-X-Y-Z+\kappa,\;X-\kappa,\;Z,\;Y-\kappa,\;\kappa),
$$

其中 $r=1-Z$、
$\kappa_- =\max(0,X+Y+Z-1)$、$\kappa_+=\min(X,Y)$，宽度
$w=\kappa_+-\kappa_-$。在
$0<Z<1$、$0<X,Y<r$、$X\ne Y$、$X+Y\ne r$ 时，固定 $b=(X,Y,Z)$ 的约化空间
$S_b$ 是光滑球面，正域是 $(\kappa_-,\kappa_+)\times S^1$，并有

$$
\omega_{\mathrm{rel}}=d\chi\wedge d\kappa,qquad
\int_{S_b}\omega_{\mathrm{rel}}=2\pi w.
$$

复坐标可取
$z=\psi_0\psi_{13}/(\psi_1\psi_3)$，两极封口给 $S_b\simeq\mathbb P^1$。

原主 $T^3$ 丛在四个参数区域的原始绕数向量为

| 区域 | $w$ | $c=-\nabla_b w$ | 一个商坐标 |
|---|---:|---|---|
| $X+Y<r,\ X<Y$ | $X$ | $(-1,0,0)$ | $(t_Y,t_Z)$ |
| $X+Y<r,\ Y<X$ | $Y$ | $(0,-1,0)$ | $(t_X,t_Z)$ |
| $X+Y>r,\ X<Y$ | $r-Y$ | $(0,1,1)$ | $(t_X,t_Y/t_Z)$ |
| $X+Y>r,\ Y<X$ | $r-X$ | $(1,0,1)$ | $(t_Y,t_X/t_Z)$ |

**定理 8.1（最大可平坦化环面商）。** 令 $c\in\mathbb Z^3$ 为表中的非零原始向量，
置

$$
\lambda_c:\mathbb G_m\to T=(\mathbb C^\times)^3,
\qquad u\mapsto(u^{c_1},u^{c_2},u^{c_3}),
$$

$$
T_{\mathrm{flat}}=T/\lambda_c(\mathbb G_m).
$$

则 $T_{\mathrm{flat}}$ 是二维环面，其字符格为

$$
X^*(T_{\mathrm{flat}})=\{q\in\mathbb Z^3:\langle q,c\rangle=0\}.
$$

对任意复环面同态 $f:T\to T'$，以下等价：

1. 推出丛 $f_*P_c$ 存在平坦联络；
2. 共字符 $f_*c$ 为零；
3. $f$ 唯一因子化通过 $T_{\mathrm{flat}}$。

**证明。** 原始性使 $c$ 可补成整数基，故 $\lambda_c$ 是闭嵌入，商为二维环面。字符在
子环面上平凡当且仅当与 $c$ 配对为零。若推出丛平坦，则每个字符关联线丛平坦，球面
上的 Chern 数必须为零，于是 $\langle\eta,f_*c\rangle=0$ 对所有字符 $\eta$ 成立，
故 $f_*c=0$。反之 $f_*c=0$ 时过渡 $z^c$ 被送到单位，推出丛平凡并有平坦联络。
$f_*c=0$ 等价于 $f\circ\lambda_c$ 平凡，正是因子化条件。$□$

**推论 8.2（对偶环面的接口）。** Langlands 对偶给出

$$
1\longrightarrow\check T_{\mathrm{flat}}
\longrightarrow\check T\xrightarrow{\ c\ }\mathbb G_m
\longrightarrow1.
$$

原共字符格正合列
$0\to\mathbb Zc\to X_*(T)\to X_*(T_{\mathrm{flat}})\to0$，对偶后核正是
$\mathbb Zc$。原始性保证右端满射和核连通。

**定理 8.3（球面上的平坦障碍）。**

1. 字符 $q$ 的关联线丛可平坦化，当且仅当 $\langle q,c\rangle=0$；
2. 若 $s>0$ 且 $n=sw\in\mathbb Z$，则曲率 $F=-is\omega_{\mathrm{rel}}$ 的预量子线丛
   次数为 $n>0$，不可能同时平坦；
3. 球面上任意无奇点平坦 $SO_5(\mathbb C)$ 局部系统的单值平凡。

**证明。** 第一项由过渡 $z^{\langle q,c\rangle}$ 或定理 8.1。第二项由

$$
\deg L=\frac{i}{2\pi}\int_{S_b}F=sw=n>0
$$

而平坦联络的 Chern 类为零。第三项由 $\pi_1(S^2)=1$，平坦运输可全局平凡化。$□$

**命题 8.4（最大环面仍不足以得到稠密谱参数）。** 选取 $c^\perp$ 的整数基
$\chi_1,\chi_2$，映射

$$
(t_1,t_2)\mapsto
\operatorname{diag}(\chi_1,\chi_1^{-1},\chi_2,\chi_2^{-1},1)
$$

给出最大环面嵌入，但所有经它因子化的单值都落在真 Borel 子群内，不能 Zariski 稠密于
$SO_5(\mathbb C)$。证明是标准旗标稳定性：该环面保持一条真各向同性旗标，故处于真
Borel 中。

## 9. 整数荷、留数补偿与穿孔谱实现

**定理 9.1（次数与留数补偿）。** 在 $\mathbb P^1$ 上以
$e_\infty=z^n e_0$ 粘合 $\mathcal O(n)$，令 $w=z^{-1}$。对 $a\in\mathbb C$，设置

$$
\nabla e_0=e_0\,a\frac{dz}{z},\qquad
\nabla e_\infty=-e_\infty(a+n)\frac{dw}{w}.
$$

这给出只在 $0,\infty$ 有对数极点的联络，且

$$
\deg L+\operatorname{Res}_0\nabla+\operatorname{Res}_\infty\nabla=0.
$$

在 $\mathbb C^\times$ 上它平坦，单值为 $e^{-2\pi ia}$。

**证明。** 框架变换要求
$A_\infty=A_0+d\log z^n=(a+n)dz/z=-(a+n)dw/w$。两个留数和为 $-n$，
而穿孔曲线上 $d(dz/z)=0$。水平解为 $z^{-a}$，绕原点得到单值。$□$

一般紧曲线上，若 $s$ 是线丛的非零亚纯截面且 $\nabla s=s\alpha$，则留数定理给

$$
\sum_p\operatorname{Res}_p\nabla+\deg L=0.
$$

所以不同整数延拓可以由奇点留数补偿；穿孔单值只记录指数，不记录延拓的整数部分。

### 9.1 三个独立控制的稠密性

**引理 9.2。** 用指标 $1,\ldots,5$，令

$$
A_1=J_{12}-J_{45},\qquad A_2=J_{13},\qquad A_3=J_{14}-J_{25}.
$$

这三个矩阵生成 $\mathfrak{so}(5)$。取 $\theta=\pi\sqrt2$、$U_j=\exp(\theta A_j)$，
则 $U_1,U_2,U_3$ 在 $SO(5)$ 中生成拓扑稠密子群，在 $SO_5(\mathbb C)$ 中 Zariski 稠密。

**证明。** 直接交换给

$$
[A_2,[A_2,A_1]]=-J_{12},\qquad
[A_2,[A_2,A_3]]=-J_{14}.
$$

从而取得 $J_{12},J_{13},J_{14},J_{45},J_{25}$；坐标平面连通图和
$[J_{ij},J_{jk}]=J_{ik}$ 生成全部十个 $J_{ij}$。每个单参数群周期为 $2\pi$，而
$\theta/(2\pi)$ 无理，所以整数幂稠密于对应圆群。三圆群的 Lie 代数为全部
$\mathfrak{so}(5)$，闭包为连通的 $SO(5)$。实紧形式在其复化中的 Zariski 闭包 Lie
代数为 $\mathfrak{so}_5(\mathbb C)$，故复群稠密。$□$

三个 $A_j$ 必须是分别可调用的控制；一个固定 Hamiltonian 的存在不供应独立定时。

**定理 9.3（四穿孔关系球面的稠密谱实现）。** 在 $S_b$ 上选四个不同点
$p_1,\ldots,p_4$，令

$$
\pi_1(S_b\setminus\{p_1,\ldots,p_4\})
=\langle\gamma_1,\ldots,\gamma_4\mid\gamma_1\gamma_2\gamma_3\gamma_4=1\rangle.
$$

置 $\rho(\gamma_j)=U_j$（$j\le3$），
$\rho(\gamma_4)=(U_1U_2U_3)^{-1}$。则得到 Zariski 稠密的
$SO_5(\mathbb C)$ 局部系统。

**证明。** 唯一群关系由第四个矩阵定义满足；前三个矩阵已经生成稠密子群。$□$

正则奇 Riemann–Hilbert 将其实现为穿孔曲线上的代数平坦联络并允许正则奇延拓。
四个标记点和闭路是额外数据，不由概率金字塔自动选出。

**定理 9.4（无理角分歧不能由有限覆叠消去）。** 上述前三个穿孔的任意有限分歧拉回，
都不能跨过其上方点延拓为无奇点平坦局部系统。

**证明。** 局部覆盖 $z=u^m$ 后小圆周单值为 $U_j^m$。$A_j$ 的特征值为
$0,i,-i$，因此 $U_j^m$ 的特征值含
$1,e^{im\pi\sqrt2},e^{-im\pi\sqrt2}$。无理性使后两者不等于一，所以
$U_j^m\ne I$ 且不是非平凡标量。若跨点无奇点延拓，小圆周可缩，单值必须为单位，矛盾。$□$

## 10. 保留无分歧接口的另一种基底

**命题 10.1。** 另取光滑射影属三复曲线 $X$，标记

$$
\pi_1(X)=\langle a_1,b_1,a_2,b_2,a_3,b_3:\prod_{j=1}^3[a_j,b_j]=1\rangle.
$$

令 $\rho(a_j)=U_j$、$\rho(b_j)=I$，得到稠密且不可约的
$SO_5(\mathbb C)$ 局部系统。

**证明。** 每个交换子为单位，群关系成立；像包含三个 $U_j$，故稠密。若存在真抛物
约化，则稠密像落在真 Zariski 闭子群中，矛盾。通过 Riemann–Hilbert 得到代数连接，
因此第 7 节的无分歧外部接口可用。$□$

这条属三构造与四穿孔构造不是同一个基底上的同一个谱参数。前者用于无分歧接口，
后者用于展示关系球面上增加奇点后的稠密单值。

## 11. 校准结构、谱群与中心歧义

**命题 11.1（结构增长方向）。** 增加门菜单使生成群闭包满足
$G_{\mathcal U}\subseteq G_{\mathcal U'}$；增加读出使预测盲空间反向包含；固定张量
$t$ 并要求保持它时，结构群变为稳定子
$G_t=\{g:g\cdot t=t\}\subseteq G$。

**证明。** 第一项是生成子群和闭包的单调性，第二项是对偶零化子的反向包含，第三项
是稳定子定义。三项发生在不同对象上，不能互相替代。$□$

获得十个新的状态坐标，不会自动把保持 $SO_5$ 的门群扩大为 $GL_5$ 的稠密群；
$W_{14}$ 已经是 $SO_5$ 的忠实表示，保存足够张量态射时可以重构该群。

**定理 11.2（全局水平校准障碍）。** 若
$\rho:\pi_1(X,x)\to SO_5(\mathbb C)$ Zariski 稠密，则基点反对称矩阵 $B$ 能延拓
为全局水平的 $\operatorname{ad}E$ 截面，当且仅当它与全部单值交换；此时 $B=0$。

**证明。** 路径独立的平行运输恰等价于 $B$ 与所有闭路单值交换。交换方程是多项式方程，
由稠密性推广到整个 $SO_5(\mathbb C)$。与所有成对符号翻转对角矩阵交换迫使非对角元
为零，再与每个 $J_{ij}$ 的指数交换迫使对角元相同，故 $B=\lambda I$。反对称条件
给 $\lambda=0$。$□$

**定理 11.3（规则相位校准的稳定子）。** 若
$B=aJ_{12}+bJ_{34}$、$ab\ne0$ 且 $a^2\ne b^2$，则

$$
Z_{SO_5(\mathbb C)}(B)\simeq(\mathbb C^\times)^2,qquad
Z_{SO(5)}(B)\simeq SO(2)\times SO(2).
$$

**证明。** $B$ 的特征值为 $ia,-ia,ib,-ib,0$，互异。交换矩阵保持五条特征线，
正交性将相反特征值配对，零特征线取值为一；所得矩阵由两对互逆参数给出二维复环面。
实正交条件给两个独立旋转。$□$

例如 $B=J_{12}+2J_{34}$ 时，
$\sigma=I_5/5+i\epsilon B$ 在 $0<|\epsilon|<1/10$ 时是正定态。该基点参考
可以合法存在，但若要求它成为所有路径共享的全局水平张量，仍受定理 11.2 限制。

**命题 11.4（通道中心盲性）。** 若未知门只以
$\operatorname{Ad}_U(\rho)=U\rho U^\dagger$ 形式调用，则任何参考、联合测量和反馈
都不能区分 $U$ 与 $e^{i\alpha}U$。

**证明。** 两者定义完全相同的通道，且与任意外部系统张量恒等后仍相同；有限复合和
条件分支的概率逐步相同。若另供相干受控未知门，则是不同合同。$□$

**命题 11.5（正交结构消除标量提升歧义）。** 给定
$\rho:\Gamma\to SO_5(\mathbb C)$。若
$q:GL_5\to PGL_5$ 且
$q\circ\widetilde\rho=q\circ\rho$，则唯一存在字符
$\chi:\Gamma\to\mathbb C^\times$ 使
$\widetilde\rho(\gamma)=\chi(\gamma)\rho(\gamma)$。若还保持同一二次型和体积形式，
则 $\chi=1$。

**证明。** 逐点射影相等给出唯一标量，表示乘法使其成为字符。保持二次型给
$\chi^2=1$，保持体积给 $\chi^5=1$，两指数互素，故 $\chi=1$。$□$

## 12. 综合定理与未供应接口

**定理 12.1（结构取得与谱延拓综合结论）。** 考虑五模式模型并假设：

1. 有明确输出分支与旧预测商；新增线性读口保持原分支合同；
2. 指定实结构，并在二拷贝任务中另供 i.i.d. 制备和充分实联合效果；
3. 三个独立可调用的实控制 $A_1,A_2,A_3$；
4. 使用朗兰兹接口时，另供带标记复曲线及平坦 $SO_5$ 单值。

则：

1. 旧摘要封闭的内部计算不能细化旧纤维，新增维数由 $M_\infty$ 给出；
2. 二阶实联合张量达到复共轭轨道商，校准非实参考可消除歧义，但成本不由维数控制；
3. 隐藏二次关系给出
   $\operatorname{Sym}^2\mathfrak{so}_5\twoheadrightarrow\mathbf1\oplus W_{14}\oplus V_5$，
   并在局部系统上成为平行分裂；
4. 属三曲线与稠密单值满足外部无分歧接口时，Hecke 本征对象保存
   $\sigma,\gamma,\beta$ 的态射相容性；
5. 原正则关系球面上无奇点稠密参数被拓扑排除；四穿孔可实现稠密单值，但无理角
   分歧不能由有限覆叠消除，非零预量子次数须由留数或其他额外结构补偿。

**证明。** 前两项分别由定理 2.2、2.4、4.2、5.1 和 3.5；第三项由定理 6.2、
7.2；第四项由引理 9.2、命题 10.1、外部定理 7.3 和定理 7.4；第五项由定理 8.3、
9.1、9.3、9.4。每项只使用其明示合同，没有把操作存在性替换为几何存在性。$□$

### 12.1 尚需构造的两个对象

第一，需要从实际仪器和参考操作生成到几何 Hecke 作用范畴的函子，并证明它保存选定
的合成、张量和等变态射。第 7 节只证明系数层态射的自然性，不自动构造这个实现函子。

第二，需要在四穿孔关系球面上选定局部单值条件、带分歧谱栈、自守范畴和 Hecke 作用，
再证明相应的本征存在性。定理 9.4 表明该问题不能通过有限覆叠直接化为无分歧情形。

### 12.2 可形式化的最小核心

适合优先进入证明助手的有限代数对象包括：残余核的最大不变性、三状态非分裂反例、
四状态控制协同反例、实二拷贝的 $\mathbb Z_2$ 分类、参考收缩公式，以及 $\Psi$ 的
显式满射。它们不需要先形式化整个几何朗兰兹证明；本卷不把建议形式化的声明写成
已编译事实。

## 13. 结论的量词与实现边界

本卷的核心结论分别属于不同层次：

- **可取得性：** 新读口是否切开旧盲空间由 $M_\infty$ 判定；
- **可识别性：** 完整二拷贝实统计只识别复共轭轨道；校准非实参考给单射；
- **几何拓扑：** $c$、Chern 数和球面基本群给出平坦障碍；
- **表示论：** $\Psi$ 是明确的等变满射，维数分裂是线性代数结论；
- **谱接口：** Hecke 自然性需要外部 Satake、本征对象和融合相容性；
- **资源成本：** 样本数、门调用数、参考制备和实验误差仍需另行计费。

因此“隐藏关系已经进入朗兰兹谱”只能在具备第 7 节外部接口的条件下理解为一个条件
态射结论；它不宣称原实验仪器本身就是层，也不把穿孔单值构造冒充无分歧几何朗兰兹
存在性。

## 14. 参考文献与固定来源

1. the-omega-institute，trureturing，固定提交比较：
   [f38e7d6dad5d 至 af80fa178cd44](https://github.com/the-omega-institute/trureturing/compare/f38e7d6dad5d17bf396a26b6b03b2eed6a3728d4...af80fa178cd445406a7be55aeb4d9e9599a21b66)。
2. trureturing，[AURIC FIB 关系丛与预测闭包理论](https://github.com/the-omega-institute/trureturing/blob/af80fa178cd445406a7be55aeb4d9e9599a21b66/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)。
3. trureturing，[FIB-ATOM boundary geometry: finite joint cycle and radial prediction](https://github.com/the-omega-institute/trureturing/blob/af80fa178cd445406a7be55aeb4d9e9599a21b66/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_FINITE_JOINT_PREDICTION.md)。
4. trureturing，[NativeTimeProfile.lean](https://github.com/the-omega-institute/trureturing/blob/af80fa178cd445406a7be55aeb4d9e9599a21b66/D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.lean)。本文只据其声明和证明项，不报告整库重编译。
5. A. Hickey and G. Gour，[Quantifying the Imaginarity of Quantum Mechanics](https://arxiv.org/abs/1801.05123), *J. Phys. A* 51 (2018), 414009。
6. K.-D. Wu et al.，[Operational Resource Theory of Imaginarity](https://arxiv.org/abs/2007.14847), *Phys. Rev. Lett.* 126 (2021), 090401。
7. A. Hatcher，[Vector Bundles and K-Theory](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf), version 2.2。
8. P. Deligne and J. S. Milne，[Tannakian Categories](https://jmilne.org/math/xnotes/tc2022.pdf)。
9. I. Mirković and K. Vilonen，[Geometric Langlands duality and representations of algebraic groups over commutative rings](https://arxiv.org/abs/math/0401222)。
10. P. Deligne，[Équations différentielles à points singuliers réguliers](https://publications.ias.edu/node/355), LNM 163 (1970)。
11. D. Gaitsgory and S. Raskin，[Proof of the geometric Langlands conjecture I: construction of the functor](https://arxiv.org/html/2405.03599v2)。
12. D. Gaitsgory and S. Raskin，[Proof of the geometric Langlands conjecture V: the multiplicity one theorem](https://arxiv.org/abs/2409.09856)。
13. trureturing，[Observer-Internal Three-Axis Geometry and Predictive Interface](https://github.com/the-omega-institute/trureturing/blob/af80fa178cd445406a7be55aeb4d9e9599a21b66/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。

## 附录 A：固定来源与目录核对

本续篇直接使用的新增理论输入包括：关系丛与预测闭包卷；有限联合预测卷；原生时间
剖面源；以及递归边界几何和严格实关联支持的后续卷。目录级比较只统计理论目录中
新增、修改和删除的文件，不能把源码、Blueprint 或运行登记中的变更混入理论目录清单。
本卷不把目录比较当作数学证明；它只用于说明来源范围。

## 附录 B：符号和量词核对

| 符号或断言 | 适用范围 |
|---|---|
| $N,K_A$ | 固定有限维线性来源、既有全部输出分支和新增末端读口；不暗含新控制。 |
| $A,B$ | 二拷贝中 $A$ 是未知态虚部，$B$ 是已知参考虚部；控制矩阵写作 $A_1,A_2,A_3$。 |
| $A^{\odot2}$ 与 $A^2$ | 前者为对称二次张量，后者为矩阵乘法。 |
| 完整实联合统计 | 足够多设置的概率律数据，不等于一次实验样本。 |
| $T_{\mathrm{flat}}$ | 使推出丛存在某个平坦联络的普遍商，不保证指定几何联络平坦。 |
| $1\oplus14\oplus5\oplus35$ | 等变线性分裂，不表示四份独立物理资源。 |
| 全局水平参考 | 要求单值不变的张量；基点制备的参考不必满足此条件。 |
| 无分歧/带分歧 | 属三曲线使用无分歧接口；四穿孔构造只给带奇点局部系统。 |

## 追加锚（本行以下为增补区）

## 15. 固定二次协变量不能普遍替代完整二次张量

### 15.1 同一坐标下的合法域与识别目标

沿用定义 4.1 和第 6 节，在 $H=\mathbb C^5$ 上固定同一指定实正交基
$e_1,\ldots,e_5$，实空间取标准度量及定向 $e_1\wedge\cdots\wedge e_5$。
记 $e_{ij}=e_i\wedge e_j$、$e_{1234}=e_1\wedge e_2\wedge e_3\wedge e_4$，
并仍取 $J_{ij}=E_{ij}-E_{ji}$。矩阵与二形式的对应严格使用
$a_A=\sum_{i<j}A_{ij}e_{ij}$，Hodge 星使用上述度量和定向。

识别问题的合法输入为实矩阵 $S,A,B$，满足

$$
S^{\mathsf T}=S,\qquad \operatorname{tr}S=1,\qquad
A^{\mathsf T}=-A,\qquad B^{\mathsf T}=-B,\qquad
S+iA\succeq0,\qquad S+iB\succeq0.
$$

这里两个态共享同一个 $S$，$B$ 表示另一个候选态的虚部，不是第 5 节的已知参考。
合法域包括重谱和半正定边界，不额外要求单谱或泛型条件。比较始终在固定坐标中进行，
所取等价关系只有整体符号 $B=\pm A$；它对应两个态相等或互为复共轭，
不把一般正交换基或酉共轭也商掉。

把定义 6.1 限制到对称秩一张量，记

$$
\begin{aligned}
q(A)&=\Psi(A^{\odot2})\\
&=\left(-\tfrac12\operatorname{tr}(A^2),\,
-A^2+\frac{\operatorname{tr}(A^2)}5I_5,\,
*(a_A\wedge a_A)\right).
\end{aligned}
$$

因 $q(-A)=q(A)$，它确实定义了整体符号商上的读数。待区分的是它能否识别这个商：
在上述全部合法输入上，$q(A)=q(B)$ 是否蕴含 $B=\pm A$？
定理 6.2 的满射与核维数只描述整个对称张量空间上的线性映射；
单有非零线性核并未给出两个合法秩一张量的差。下面直接给出这样的差。

### 15.2 严格正定态上的完整反例

**命题 15.1（固定协变量的非分离性）。** 取

$$
S=\frac15I_5,\qquad
A=\frac{J_{12}+J_{34}}{10},\qquad
B=\frac{J_{13}-J_{24}}{10}.
$$

则 $\rho_A=S+iA$ 和 $\rho_B=S+iB$ 均为严格正定、迹为一的合法态，且

$$
q(A)=q(B)=\left(
\frac1{50},\,
\frac{\operatorname{diag}(1,1,1,1,-4)}{500},\,
\frac{e_5}{50}\right),
\qquad B\notin\{A,-A\}.
$$

因而第 15.1 节的全称识别蕴含不成立。

**证明。** $S$ 实对称且迹为一，$A,B$ 实反对称，故两个态均为 Hermitian。
$A$ 的两个非零块分别在坐标平面 $(1,2)$、$(3,4)$ 上；$B$ 的非零块分别在
$(1,3)$、$(2,4)$ 上，后一块仅反转符号。在每个平面上，$iJ_{ij}/10$ 的
两个特征值为 $-1/10$ 和 $1/10$。因此两个态各自的特征值多重集都是

$$
\left\{\frac1{10},\frac1{10},\frac3{10},\frac3{10},\frac15\right\}.
$$

它们全为正且和为一。这同时验证了合法性；反例并不依赖半正定边界态。

令 $P=\operatorname{diag}(1,1,1,1,0)$。由于各自的两个坐标平面不相交，交叉矩阵乘积
为零，而 $J_{ij}^2=-E_{ii}-E_{jj}$，所以

$$
A^2=B^2=-\frac{P}{100},\qquad
\operatorname{tr}(A^2)=\operatorname{tr}(B^2)=-\frac1{25}.
$$

代入定义 6.1，两个标量分量和两个对称无迹分量分别相同，并且等于

$$
\sigma(A^{\odot2})=\sigma(B^{\odot2})=\frac1{50},\qquad
\gamma(A^{\odot2})=\gamma(B^{\odot2})
=\frac{P}{100}-\frac{I_5}{125}
=\frac{\operatorname{diag}(1,1,1,1,-4)}{500}.
$$

第三个分量也保留其定向符号。具体地，

$$
a_A=\frac{e_{12}+e_{34}}{10},\qquad
 a_B=\frac{e_{13}-e_{24}}{10}.
$$

每个可分解二形式的自楔积为零，两个二形式的楔积交换，而
$e_{13}\wedge e_{24}=-e_{1234}$。于是

$$
\begin{aligned}
a_A\wedge a_A
&=\frac{2e_{12}\wedge e_{34}}{100}
=\frac{e_{1234}}{50},\\
a_B\wedge a_B
&=-\frac{2e_{13}\wedge e_{24}}{100}
=\frac{e_{1234}}{50}.
\end{aligned}
$$

标准定向给 $*(e_{1234})=e_5$，故
$\beta(A^{\odot2})=\beta(B^{\odot2})=e_5/50$。至此三个分量逐一相同。
最后 $A_{12}=1/10$，而 $B_{12}=0$，故 $B$ 既不等于 $A$，也不等于 $-A$。
这两个合法输入满足全称蕴含的前件而不满足后件。$□$

### 15.3 对完整二拷贝识别的确切影响

命题 15.1 给出了定理 6.2 的核中的具体非零元素

$$
T=A^{\odot2}-B^{\odot2}\ne0,\qquad \Psi(T)=0,
$$

而且它的两个秩一项来自同一个 $S$ 下的严格正定态。非零性无需另作维数推断：
在 $J_{ij}$ 固定基的二次坐标中，$J_{12}^{\odot2}$ 的系数对
$A^{\odot2}$ 是 $1/100$，对 $B^{\odot2}$ 是零。
所以完整二次张量仍然区分这两个态的复共轭轨道；被合并的是它们在 $\Psi$ 下的像。

对第 4.2 节的实际识别目标，这说明即使已经给出同一个 $S$，也不能在全部合法态上
以 $(S,q(A))$ 替代 $(S,A^{\odot2})$。定理 4.2 以完整实二拷贝统计恢复
$A\otimes A$，命题 4.4 使用全部二次坐标乘积，命题 6.3 取得完整
$A^{\odot2}$；这些结论均保留。定义 6.1 的协变量只是完整张量的线性像，
本来并未宣称这个像足以识别原来的整体符号商。

因此，完整张量的识别定理与固定协变量的不充分性同时成立。
这里没有把两个态同谱当作等价，也没有以坐标变换取代整体符号条件。

### 15.4 来源与适用边界

本节是以定义 4.1、定义 6.1 为前提的仓内综合推导；其新增内容是命题 15.1 的
显式合法碰撞，以及它对第 4.2 节识别目标的后果。证明由所列矩阵、谱和楔积计算承担。
定理 6.2 的 $35$ 维核陈述没有单独供应这个合法秩一张量差，
而定理 4.2、命题 4.4 和命题 6.3 的完整张量结论也没有断言这种碰撞不存在。

一般二次测量的识别判据、泛型测量族的结论与这里已固定的 $q$ 有不同的适用范围。
本节不援引 Wang–Xu 的 [arXiv:1605.08034v3](https://arxiv.org/abs/1605.08034v3)
定理 2.1、4.1 或 Higham（1987）作为此固定映射反例的定理来源；
不以某一来源没有列出此例来推断文献新颖性，也不作全库或外部文献穷尽排重的断言。
仓内综合推导不等于全球原创性主张。

结论严格限于固定基、固定定向、上述合法域和整体符号等价下的全称充分性失败。
该见证含重谱；它不决定泛型充分性，也不提供一般纤维分类。
这里不新增测量设置、样本量、稳定性、物理实现或朗兰兹传递的断言，
亦不宣称 Lean 或 kernel 核验。第 7 节的条件态射接口不从本节反例取得新的传递结论。

## 追加锚（本行以下为增补区）
