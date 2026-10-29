<a id="auric-v12"></a>

# AURIC 有限分辨率与完整递归观测理论

**稳健重构、相干拒绝与实际取得的边界 · v12.0 · 2026-10-29**

> 本文是用户提供的 AURIC v12.0 XeLaTeX 续稿的独立纯 Markdown 转换版。数学表达使用标准 Markdown 数学块；本文不依赖 TeX 编译。原稿的标题页、章节结构、定理、定义、假设、例子、证明和书目均在此保留；显示编号只服务于阅读，不是项目源码的验证编号。
>
> 固定项目版本：`5517865965160e8d20e4122aafe4e6c468c6c41d`
>
> 提交时间：2026-10-29 14:45:40（Asia/Singapore）；快照元数据取得：2026-10-29 14:50:04（Asia/Singapore）。比较基线：`7307a34c8f47f70cd39fc47da78328fa3f3ffcde`。
>
> 本稿是独立续作；“本文定理”不表示已经写入项目或具有数学史上的首创性。
>
> 本稿的普通证明不以 Lean 检查、数学程序或硬件实验充当证明。项目源码事实与本文新证明分开标注；文献和仓库链接只支持所声明的范围。

**正文导航。** [1](#sec-1) · [2](#sec-2) · [3](#sec-3) · [4](#sec-4) · [5](#sec-5) · [6](#sec-6) · [7](#sec-7) · [8](#sec-8) · [9](#sec-9) · [10](#sec-10) · [11](#sec-11) · [12](#sec-12) · [证明地位](#sec-provenance) · [参考文献](#sec-bibliography)

<a id="sec-abstract"></a>

## 摘要

本稿把“观察者内生、量与关系都需要预测”的直觉推进为一组可检验的数学命题。关键对象是保留结果、后态和未来记忆的完整仪器；关键问题是有限读数何时控制任意合法续接，以及误差如何沿递归传播。

本文区分精确 law 商、静态完成和实际取得，并证明偏离模型像的有噪拟合界、有限历史表的后验重构界与闭合残差公式、完整仪器的自适应稳定性、稀有分支的条件误差界、含量具误差的层析桥、有限参考测试到保迹完全正修复的定理，以及静态切面交换和紧模型类实现定理。对项目新增的五模 Lüders 下界给出自足复证，并与同一菜单内精确二元效果作配对。

本文没有把递归、五个标签或正交读出直接当作复 Hilbert 空间与 Born 规则的证明。量子部分明确采用有限维复量子操作框架；定理说明这些条件如何协调、哪些信息可以保留以及哪些断言仍需要新增物理条件。

<a id="sec-1"></a>

## 1. 本轮进展与研究对象

<a id="sec-1-1"></a>

### 1.1 固定版本中的实质变化

本轮核对默认分支 `dev` 的固定提交。在 `docs/develop/theory` 范围内，相对 v11 基线，文件数从 971 增至 988；共 28 条路径变化，其中 17 条新增、11 条修改。核对了 24 份当前文本和 7 份基线文本的 Git blob；这些计数是理论目录的元数据事实，不表示已验证 988 份文件的每个证明。本文采用以下项目接口：

| 新进展 | 已有结论 | 使用边界 |
| --- | --- | --- |
| [预测波 VI §§116–121](#ref-1) | 固定源的有限原始概率稳定确定正常形式；非零保留参数允许恢复相关补全向量。 | 只比较同一模型族的精确 law；不自动给采样服务、任意噪声解码或完整补全酉矩阵。 |
| [预测波 VII §§142–145](#ref-2) | 阶三固定源的 117 行有限证书及有限范数下的非线性反射端点。 | 全历史范数端点问题仍未重算。 |
| [相干重构续卷 §§47–49](#ref-3) | 破坏性读出可抹去相位区别；相干拒绝可重新显出环积；五模完整仪器有正误差下界。 | 不同载体、制备和菜单须分别声明。 |
| [最小预测核心桥](#ref-4) | 完整经典转录 law 的商同构于实际来源像。 | 联合核是等价关系，不能误作复 PSD Gram 核；逆极限可含虚拟线程。 |
| [有限边界标本读出](#ref-7) | 有限量子标本与原精确 Read 服务存在可证明的取得缺口。 | 复空间、Born、标本制备与旁记录都是条件输入。 |

最新提交对应 VII 的阶三有限端点，而不是全历史端点问题的解决。量子停止 advice 编译 [文献 6](#ref-6) 的作用域是 $\mathbb C^3$，它只通过指定嵌入运输到五模中的三维支持扇区；其终端结果给效果，没有给一般后测仪器。本文不会把它与五维全域的 $3/7$ 下界拼成一个未经同域核对的上下界。

Selfcal V 的文件没有变化；上一稿的 $JJ$ 证书不算本轮新进展。新增的 V10 总论 [文献 8](#ref-8) 是此前稿件的入库转换，不能作为对本稿结论的独立验证。

裸递归不唯一指定量子语义：取 $Z=\mathbb N$、$\rho(n)=n+1$，令状态为经典概率分布、读出为确定函数，所有复合相容性都成立，但可观测代数交换且无需复数幅度。五个角色画成几何图形并不排除这个反模型。

**命题 1.1（裸递归不唯一指定量子语义）。** 只要求存在一个集合、一个递归操作 $\rho$ 和可重复复合的关系标签，不足以推出非交换量子操作或复数幅度。

**证明。** 取 $Z=\mathbb N$、$\rho(n)=n+1$，把角色解释为五个可重复使用的经典标签。状态可取 $Z$ 上的概率分布，读出可取确定函数，递归由推前分布实现。所有复合相容性都成立，但整个可观测代数可交换，概率无需复数幅度。若增加更多关系公理，必须逐条检验这个反模型是否被排除；仅把标签画成金字塔不会改变结论。

这个命题不否定项目的几何构造。它给后续研究一个精确任务：哪一条操作要求排除经典语义，哪些组合要求确定复结构，哪些实际记录校准 Born 权重。本文集中处理已经安装量子语义之后的递归相容与稳健性。

<a id="sec-1-2"></a>

### 1.2 三个层次不能合并

**定义 1.2（来源、预测与操作合同）。** 一个**来源模型**给出可能来源集合 $Z$；一个**观察合同**给出允许的制备、动作、续接、记录、参考和停止规则。对来源 $z$ 与合法协议 $\Pi$，记其完整结果律为 $P_z^\Pi$。完整表示包含合同中的失败、拒绝与 Stop，不得只保留成功样本后再称为原始 law。

两个来源的精确预测等价定义为

<a id="eq-1-u01"></a>

$$
z\sim_{\mathscr T}z'
\quad\Longleftrightarrow\quad
P_z^\Pi=P_{z'}^\Pi\quad(\Pi\in\mathscr T).
$$

若合同还允许保留量子末态并继续操作，预测对象必须包括后态与记忆的联合操作，而不仅是当前结果概率。语法层的角色

<a id="eq-1-u02"></a>

$$
F[\mathrm{null}],\quad F[1],\quad F[2],\quad F[3],\quad F[1,3]
$$
不单独提供数学语义；数学存在也不单独提供实际调用、读出和记录权限。

第一层是关系语法，例如 $\beta=\rho(\alpha)$ 和五个角色；第二层是给语法安装数学语义，例如经典转移系统、实或复向量空间、正核、仪器；第三层是实际取得，即给定观察者是否真的能够制备、调用、读出与记录这些对象。语法等式不单独提供第二层的唯一选择，数学存在也不单独提供第三层的执行权限。

即使观察者对量具和关系只能给出一个相容模型集合，仍可严格讨论这些模型的共同预测。本文的精确等号表达模型内的条件约束，不声称物理观察者已经精确知道所有参数；有限误差定理研究未知性保留后仍对全部允许模型成立的结论。

<a id="sec-1-3"></a>

### 1.3 观察者内生与无外部时钟

在有限观察截面，观察者由记忆载体 $M$、联合状态和控制更新规则表示。系统 $S$ 与 $M$ 可以相关或纠缠；观察行为是允许载体上的联合更新，并在需要时追加实际经典记录。

**定义 1.3（内生观察者）。** 在一个有限观察截面，观察者由记忆载体 $M$、其联合状态和控制更新规则表示。系统 $S$ 与 $M$ 可以相关或纠缠；控制程序可以存于 $M$ 中，不要求存在置于模型之外的观察者。

字 $w=a_1\cdots a_n$ 或调用层数 $n$ 只表示因果组合的记账次序，不是宇宙绝对时间。对同一有限因果偏序，不同线性扩张是否给出同一结果，必须在完整接口上证明；因果依赖、书写次序与外部时钟不可混同。

<a id="sec-2"></a>

## 2. 有限 law 商与偏离模型像的数据

<a id="sec-2-1"></a>

### 2.1 在精确预测商上工作

项目 VI §§118–119 的源特定结果提供了这里采用的正常形式与双 Lipschitz 夹逼；本文把它作为固定源合同下的应用前提，不重演其完整核计算（见[文献 1](#ref-1)）。

固定源码允许的源 $\mathfrak s$ 取 $0<d<1$、$\sin(2\theta)\ne0$、同一个已安装 mixing $N$、九个实际带权前缀和完整十维返回合同。配对参数为

<a id="eq-2-u01"></a>

$$
\Theta=\{(\gamma,h)\in\mathbb C\times\mathbb C^3:|\gamma|\le1,\ \|h\|\le1\}.
$$

源码正常形式为

<a id="eq-2-1"></a>

$$
\mathcal N(\gamma,h)
=\bigl(\gamma,\ hh^\dagger,\ \mathrm i(ht^\dagger-th^\dagger),\ \gamma h\bigr),
\qquad t\ne0.
\tag{2.1}
$$

这里 $t\ne0$ 是源固定向量。每个假设使用一个固定的完整补全，并贯穿该假设的所有历史；它不是每次观测后可重新选择的自由参数。令 $d_{\mathcal N}$ 为四个坐标差的范数之和：标量绝对值、两个矩阵的 Hilbert--Schmidt 范数和向量 Euclidean 范数，即

$$
\begin{aligned}
d_{\mathcal N}((\gamma,h),(\gamma',h'))={}&|\gamma-\gamma'|
+\|hh^\dagger-h'h'^{\dagger}\|_{\mathrm{HS}}\\
&+\|\mathrm i(ht^\dagger-th^\dagger-h't^\dagger+th'^{\dagger})\|_{\mathrm{HS}}
+\|\gamma h-\gamma'h'\|.
\end{aligned}
$$

对固定源，存在有限原始概率向量 $P_{\mathfrak s}$ 和正数 $c_{\mathfrak s},C_{\mathfrak s}$，满足

<a id="eq-2-2"></a>

$$
\frac{c_{\mathfrak s}}2d_{\mathcal N}
\le \Delta_f
\le \Delta_{\rm all}
\le 2C_{\mathfrak s}d_{\mathcal N}.
\tag{2.2}
$$

这里 $\Delta_f$ 是有限原始概率向量的最大坐标差，$\Delta_{\rm all}$ 是源码规定的所有原始历史终端概率坐标差的上确界。该式不是所有自适应协议的 TV，也不是完整仪器的 diamond 距离。

<a id="sec-2-2"></a>

### 2.2 紧模型像上的有噪拟合

<a id="thm-2-1"></a>

**定理 2.1（紧模型像上的有噪拟合）。** 设 $\Theta$ 为紧空间，$P:\Theta\to\mathbb R^M$ 连续。设 $d_*$ 为参数的预测伪距离并有

<a id="eq-2-u02"></a>

$$
\alpha d_*(\vartheta,\vartheta')
\le\|P(\vartheta)-P(\vartheta')\|_\infty,
\qquad \alpha>0.
$$

若数据 $y$ 满足真实参数 $\vartheta_*$ 的误差保证 $\|y-P(\vartheta_*)\|_\infty\le\varepsilon$，且 $\widehat\vartheta$ 满足

<a id="eq-2-u03"></a>

$$
\|P(\widehat\vartheta)-y\|_\infty
\le \inf_{\vartheta\in\Theta}\|P(\vartheta)-y\|_\infty+\eta,
$$

则

<a id="eq-2-3"></a>

$$
\begin{aligned}
\|P(\widehat\vartheta)-P(\vartheta_*)\|_\infty&\le2\varepsilon+\eta,\\
d_*(\widehat\vartheta,\vartheta_*)&\le(2\varepsilon+\eta)/\alpha.
\end{aligned}
\tag{2.3}
$$

若未来距离满足 $d_{\rm fut}\le\beta d_*$，还得 $d_{\rm fut}(\widehat\vartheta,\vartheta_*)\le\beta(2\varepsilon+\eta)/\alpha$。

**证明。** 连续残差函数在紧集上取到最小值；真实参数是候选，故最小残差不超过 $\varepsilon$，近似极小点残差不超过 $\varepsilon+\eta$。三角不等式给第一式，再应用度量下界和未来距离控制。

<a id="cor-2-2"></a>

**推论 2.2（原始返回 law 的非精确数据延拓）。** 在[式（2.2）](#eq-2-2)的固定源合同下，任意上述拟合满足

<a id="eq-2-4"></a>

$$
 d_{\mathcal N}(\widehat\vartheta,\vartheta_*)
 \le \frac{2(2\varepsilon+\eta)}{c_{\mathfrak s}},
 \qquad
 \Delta_{\rm all}(\widehat\vartheta,\vartheta_*)
 \le\frac{C_{\mathfrak s}}{c_{\mathfrak s}}(2\varepsilon+\eta).
\tag{2.4}
$$

若真实 $|\gamma_*|\ge\rho>0$，源码全域加权界还给出

<a id="eq-2-5"></a>

$$
\|\widehat h-h_*\|
\le\frac{2\varepsilon+\eta}{c_{\mathfrak s}\rho}.
\tag{2.5}
$$

**证明。** $\Theta$ 是有限维闭有界集，故紧；原始概率是参数的连续函数。应用定理 2.1 时取 $\alpha=c_{\mathfrak s}/2$ 得第一界。为取得第二界的较好常数，直接使用源码 VI（118.12）的

$$
c_{\mathfrak s}\mathcal D\le\Delta_f\le\Delta_{\rm all}\le C_{\mathfrak s}\mathcal D,
$$

其中

$$
\begin{aligned}
\mathcal D={}&|\gamma-\gamma'|+\|hh^\dagger-h'h'^\dagger\|_{\mathrm{HS}}\\
&+\|\mathrm i(ht^\dagger-th^\dagger-h't^\dagger+th'^{\dagger})\|_{\mathrm{HS}}\\
&+\max\{|\gamma|,|\gamma'|\}\,\|h-h'\|.
\end{aligned}
$$

最后使用源码 VI（119.2）

$$
|\gamma-\gamma'|+\max\{|\gamma|,|\gamma'|\}\|h-h'\|
\le c_{\mathfrak s}^{-1}\Delta_f,
$$

以及 $\max\{|\widehat\gamma|,|\gamma_*|\}\ge\rho$，得到（2.5）。这给出存在型有噪解码规则，不等于已经取得数据、解决全局优化或给出有效终止时间。

定义可行性残差

$$
r(y)=\operatorname{dist}_{\infty}(y,P(\Theta)).
$$

若 $r(y)>\varepsilon$，则该模型族中没有参数能在声明误差内解释 $y$；若 $r(y)\le\varepsilon$，只能说明未被这一检查排除，不能证明真实世界必在 $\Theta$ 中。若 $d,\theta,N$ 也视为未知，必须扩大参数域并重新证明统一稳定性。

<a id="sec-2-3"></a>

### 2.3 为什么稳定的是关系商，而不是每个坐标

当 $\gamma=0$ 时，$\gamma h$ 消失；源码给出反射二点纤维以及不同位置的不同逆连续模。因此可稳定的是 $\mathcal N$ 或 law 商，未必是每个隐参数。靠近 $\gamma=0$ 的截面出现 $1/\rho$ 条件数恶化；这不是自动得到新的力、隧穿概率或物理相变。

[预测波 VII](#ref-2) 对指定阶三源给出 $L_{\mathfrak s}=2$ 的 117 行证书及有限最大坐标范数下的非线性端点。等价范数通常不保持两个约束优化问题的精确差值或极小点类型，故本文不把有限端点升级为全历史端点。

> **说明（117 行证书的限度）。** 最新 VII 对一个指定阶三源给出 $L_{\mathfrak s}=2$ 的 117 行证书，并证明其**有限最大坐标范数**下的非线性最优差和端点类型。等价范数控制距离大小，通常不保持两个约束优化问题的精确差值或极小点类型。因此本文的有噪延拓不会把 VII 的有限端点结论升级为源码明确未解决的全历史端点结论。

<a id="sec-3"></a>

## 3. 有限历史表的稳健重构与隐藏残差

<a id="sec-3-1"></a>

### 3.1 两个坐标约定

**定义 3.1（线性预测表示）。** 设实线性载体 $V$ 有初态 $x_0$、终端泛函 $\ell$ 和动作 $T_a$。对字 $w=a_1\cdots a_n$，定义

<a id="eq-3-u01"></a>

$$
T_w=T_{a_n}\cdots T_{a_1},\qquad
p(w)=\ell T_wx_0,\qquad T_\epsilon=I.
$$

取 $r$ 个校准列 $C:\mathbb R^r\to V$ 和 $r$ 个观察行 $O:V\to\mathbb R^r$，置

<a id="eq-3-u02"></a>

$$
H=OC,\quad H^{(a)}=OT_aC,\quad b=Ox_0,\quad c=\ell C,
$$

并假设 $H$ 可逆。观察坐标与列系数坐标的更新分别为

<a id="eq-3-u03"></a>

$$
B_a=H^{(a)}H^{-1},\qquad
A_a=H^{-1}H^{(a)},\qquad
B_a=HA_aH^{-1},\qquad d=cH^{-1}.
$$

<a id="sec-3-2"></a>

### 3.2 闭合误差与测量误差必须分开

**假设 3.1（未来闭合）。** 对实际可达空间 $R=\operatorname{span}_{\mathbb R}\{T_wx_0\}$，要求

<a id="eq-3-1"></a>

$$
OT_ax=B_aOx,\qquad \ell x=dOx\qquad(x\in R),
\tag{3.1}
$$

例如，当 $C$ 的列构成整个可达空间的基时，该条件成立；更一般地，可以先在所有未来不可见的子空间取商后要求闭合。在此假设下

$$
p(w)=dB_wb=cA_wH^{-1}b.
$$

有限表的可逆性本身不证明未来闭合。

<a id="thm-3-1"></a>

**定理 3.1（可由近似表核证的逆与更新误差）。** 固定向量范数及其诱导算子范数，行泛函使用相应对偶范数。已知

<a id="eq-3-u04"></a>

$$
\widehat H=H+E,\quad
\widehat H^{(a)}=H^{(a)}+E_a,\quad
\widehat c=c+e_c,
$$

误差分别不超过 $\varepsilon_H,\varepsilon_a,\varepsilon_c$。若 $\widehat H$ 可逆且

<a id="eq-3-u05"></a>

$$
\rho=\|\widehat H^{-1}\|\varepsilon_H<1,
\qquad
h_\dagger=\frac{\|\widehat H^{-1}\|}{1-\rho},
$$

其中

$$
\widehat B_a=\widehat H^{(a)}\widehat H^{-1},
\qquad
\widehat d=\widehat c\widehat H^{-1}.
$$

则误差球中的 $H$ 一定可逆，并有

<a id="eq-3-2"></a>

$$
\begin{aligned}
\|H^{-1}\|&\le h_\dagger,\\
\|B_a-\widehat B_a\|&\le h_\dagger(\varepsilon_a+\|\widehat B_a\|\varepsilon_H),\\
\|d-\widehat d\|&\le h_\dagger(\varepsilon_c+\|\widehat d\|\varepsilon_H).
\end{aligned}
\tag{3.2}
$$

**证明。** $H=\widehat H(I-\widehat H^{-1}E)$，Neumann 级数给出逆的界。直接相乘得到

<a id="eq-3-u06"></a>

$$
B_a-\widehat B_a=(-E_a+\widehat B_aE)H^{-1},\qquad
d-\widehat d=(-e_c+\widehat dE)H^{-1}.
$$

应用次乘性即可。严格阈值不可删除：$\widehat H=[1]$、$\varepsilon_H=1$ 的误差球含有奇异 $H=[0]$。Euclidean 范数下，该判据等价于 $\sigma_{\min}(\widehat H)>\varepsilon_H$；这里的误差球是输入保证，不是从观察到一张表自动获得的置信区间。

<a id="thm-3-2"></a>

**定理 3.2（字乘积的稳定传播）。** 设精确闭合成立。若所有精确产品范数至多 $M$、估计产品范数至多 $\widehat M$，包括空产品，每步差不超过 $\delta$，且 $\|\widehat b-b\|\le\varepsilon_b$，则

<a id="eq-3-3"></a>

$$
\|\widehat B_w\widehat b-B_wb\|
\le\widehat M\varepsilon_b+n\widehat M M\delta\|b\|.
\tag{3.3}
$$

若 $\|\widehat d-d\|\le\varepsilon_d$，概率差满足

<a id="eq-3-4"></a>

$$
|\widehat p(w)-p(w)|
\le \|\widehat d\|
\bigl(\widehat M\varepsilon_b+n\widehat M M\delta\|b\|\bigr)
+\varepsilon_dM\|b\|.
\tag{3.4}
$$

**证明。** 逐次把估计乘积中的第 $j$ 个因子替换为精确因子，得到望远镜恒等式

$$
\widehat B_w-B_w
=\sum_{j=1}^n
\widehat B_{a_n}\cdots\widehat B_{a_{j+1}}
(\widehat B_{a_j}-B_{a_j})
B_{a_{j-1}}\cdots B_{a_1}.
$$

对每项应用 $\widehat M,M,\delta$ 的界，再把 $\widehat b-b$ 和 $\widehat d-d$ 分开，即得（3.3）和（3.4）。共同收缩范数且 $\|b\|,\|\widehat d\|\le1$ 时，界化简为 $\varepsilon_b+n\delta+\varepsilon_d$。相似变换

<a id="eq-3-u07"></a>

$$
B'=\begin{pmatrix}0&t\\t^{-1}&0\end{pmatrix},\quad t>1,
\qquad (B')^2=I
$$

说明不能无条件把单步范数反复取幂：虽然 $\|B'\|_2=t>1$，所有产品仍至多为 $t$。
规范变换必须同时输运噪声单位；若真实读数被削弱而噪声未变，条件数恶化具有实际意义。

<a id="prop-3-3"></a>

**命题 3.3（有界可达域与概率坐标的产品界）。** 若有限维可达集合 $\mathcal K=\{B_wb\}$ 有界且张成 $\mathbb R^r$，则

<a id="eq-3-u08"></a>

$$
Q=\overline{\operatorname{conv}}(\mathcal K\cup-\mathcal K)
$$

是一个范数的单位球，每个 $B_a$ 在该范数下收缩。若校准列是真实可达次归一化状态、观察行为是概率效果、闭合成立，且对全部合法续接 $w$，$T_wC$ 的各列仍为合法次归一化状态，则

<a id="eq-3-5"></a>

$$
\sup_w\|B_w\|_\infty
\le\|H^{-1}\|_{\infty\to1}
\le r\|H^{-1}\|_{\infty\to\infty}.
\tag{3.5}
$$

**证明。** $Q$ 闭、有界、凸、中心对称；张成性保证它含原点邻域，所以 Minkowski 泛函是范数。由于 $B_a\mathcal K\subseteq\mathcal K$，有 $B_aQ\subseteq Q$。第二式由 $B_wH=OT_wC=:M_w$ 得到；$M_w$ 的每个元素均在 $[0,1]$ 内，所以 $\|M_wv\|_\infty\le\|v\|_1$，从而 $\|B_wu\|_\infty\le\|H^{-1}u\|_1$，最后用 $\|v\|_1\le r\|v\|_\infty$。该结论需要全部可达域有界；估计模型不会仅凭真实模型的收缩范数自动保持这一性质。

<a id="sec-3-3"></a>

### 3.3 隐藏方向的精确残差

<a id="thm-3-4"></a>

**定理 3.4（隐藏方向的精确残差式）。** 不假设未来闭合，令

<a id="eq-3-u09"></a>

$$
J=CH^{-1},\qquad P=JO,
$$

以及

<a id="eq-3-u10"></a>

$$
 r_a(x)=OT_a(I-P)x,\qquad \tau(x)=\ell(I-P)x.
$$

若 $y_j=Ox_j$、$x_{j+1}=T_{a_{j+1}}x_j$，则恒有

<a id="eq-3-6"></a>

$$
 y_{j+1}=B_{a_{j+1}}y_j+r_{a_{j+1}}(x_j),
 \qquad
 \ell x_j=dy_j+\tau(x_j).
\tag{3.6}
$$

在全部校准列上 $r_a(Cu)=0$。**证明。** $OJ=I$，所以 $P^2=P$ 且 $PC=C$。分解 $x=Px+(I-P)x$，把 $Px=JOx$ 代回即可；在 $x=Cu$ 时余项直接消失。

若估计产品一致有界于 $\widehat M$，逐步插入上式还得到

$$
\|\widehat y_n-y_n\|
\le\widehat M\varepsilon_b+\widehat M\sum_{j=1}^n
\bigl(\delta_j\|y_{j-1}\|+\|r_{a_j}(x_{j-1})\|\bigr).
$$

这把测量噪声与真正未建模的隐藏方向残差分开；降噪减少 $\delta_j$，不会自动消除 $r_{a_j}$。

<a id="ex-3-5"></a>

**例 3.5（条件数为一而未来仍失败）。** 过程 A 永远输出 $0$；过程 B 保留 $L+1$ 个计数状态，前 $L$ 次输出 $0$、之后输出 $1$。对所有长度不超过 $L$ 的输出字，两者完全一致，可取

<a id="eq-3-u11"></a>

$$
H=[1],\quad H^{(0)}=[1],\quad H^{(1)}=[0],\quad b=c=[1],
$$

但 $0^{L+1}$ 的概率分别为 $1$ 与 $0$。这说明在没有维数上界或未来闭合保证时，任何固定有限深度的成功都不能证明全部未来相同。

<a id="sec-4"></a>

## 4. 基本原子必须规定完整仪器

<a id="sec-4-1"></a>

### 4.1 结果、后态与记录的相关性

**定义 4.1（完整记录仪器）。** 在有限维复载体上，完整记录仪器是完全正映射族
$\Phi=\{\Phi_a:\mathcal L(A)\to\mathcal L(B_a)\}$，满足

<a id="eq-4-u01"></a>

$$
\sum_a\operatorname{Tr}\Phi_a(X)=\operatorname{Tr}X,
\qquad E_a=\Phi_a^*(I).
$$

完整记录提升为

<a id="eq-4-u02"></a>

$$
\operatorname{Inst}_\Phi(X)=\bigoplus_a\Phi_a(X),
$$

不同分支的载体须事先给定共同识别。若记录未来还可以相干重组，它应留在量子载体内，而不能预先当作直和中的经典标签；同一经典仪器也不唯一指定一个相干控制实现。

并定义

<a id="eq-4-u03"></a>

$$
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1,
\qquad
\delta(\Phi,\Psi)=\tfrac12\|\operatorname{Inst}_\Phi-\operatorname{Inst}_\Psi\|_\diamond.
$$

<a id="lem-4-1"></a>

**引理 4.1（完整记录控制各类读出）。** 对共同输入 $\rho_{AR}$，

<a id="eq-4-u04"></a>

$$
D((\operatorname{Inst}_\Phi\otimes\operatorname{id})(\rho),
  (\operatorname{Inst}_\Psi\otimes\operatorname{id})(\rho))
=\frac12\sum_a\|((\Phi_a-\Psi_a)\otimes\operatorname{id})(\rho)\|_1.
$$

它同时上界当前结果分布 TV、忘记记录后的后态距离和任何共同后续测量的分布差。**证明。** 块对角矩阵的迹范数等于各块迹范数之和；每块用 $|\operatorname{Tr}X|\le\|X\|_1$ 得结果 TV。忘记记录或作共同后续 CPTP 后处理时，Hermitian 差的迹范数不增；写成 $X=X_+-X_-$ 后由正性、三角不等式和保迹性立即得到。

<a id="ex-4-2"></a>

**例 4.2（同效果、同平均通道，完整仪器仍完全不同）。** qubit 上令

<a id="eq-4-u05"></a>

$$
\Phi_0(X)=X/2,\quad\Phi_1(X)=ZXZ/2,
\qquad
\Psi_0(X)=ZXZ/2,\quad\Psi_1(X)=X/2.
$$

两者效果都是 $(I/2,I/2)$，平均通道也相同；输入 $|+\rangle$ 时记录块后态正交，故完整仪器距离为一。分别知道当前概率和平均后态，仍可能不知道结果与后态的相关性。

<a id="sec-4-2"></a>

### 4.2 相干拒绝如何读出三点环积

<a id="thm-4-3"></a>

**定理 4.3（三射线的完整四记录式）。** 设 $v_0,v_1,v_2$ 为单位向量，$K_{ij}=\langle v_i,v_j\rangle$、$P_i=|v_i\rangle\langle v_i|$。从 $v_0$ 出发，先实施 $P_1$ 与 $Q_1=I-P_1$ 两分支，再测试 $P_2$。置

<a id="eq-4-u06"></a>

$$
 x=|K_{10}|^2,\quad y=|K_{21}|^2,\quad z=|K_{20}|^2,\quad B=K_{01}K_{12}K_{20}.
$$

按 $(++,+-,-+,-- )$ 排列，完整记录概率为

<a id="eq-4-1"></a>

$$
\boxed{(xy,\ x(1-y),\ z+xy-2\Re B,\ 1-x-z-xy+2\Re B)}.
\tag{4.1}
$$

其中 $B$ 在各向量独立相位变换下不变，因而是关系环积；该实验只读取 $\Re B$，整体复共轭不改变这些概率，也不排除更大实载体的实化模型。

证明：负后正质量是
$\|P_2Q_1v_0\|^2=|K_{20}-K_{21}K_{10}|^2$，展开即得；最后一项由负分支总质量 $1-x$ 相减。

**命题 4.2（破坏性负支可以抹去这个区别）。** 若每次查询正分支都重置到所查射线，负分支重置到共同 fail 并立即 Stop，则从对应单一源射线开始，任意有限自适应完整记录概率只依赖各 $|K_{ij}|^2$。随机种子、依种子的协议选择与记录后处理均要求可测。

**证明。** 固定无关随机种子后，协议是一棵有限树。每条继续路径的后态是最近一次成功查询的射线，其转移概率是两个射线的平方重叠；第一次拒绝贡献 $1-|K_{ij}|^2$ 并停止。因此每个叶概率是这些因子的乘积；对共同种子分布积分仍然相等。允许相干初始叠加、保留拒绝后态或更换参考合同都可能改变结论。

<a id="sec-4-3"></a>

### 4.3 五模菜单：准确效果与相干后继之间的定量差距

**假设 4.3（原生菜单的输出比较）。** 载体为 $\mathbb C^d$，协议允许系统酉操作、完整秩一投影读出、经典反馈、输入无关随机种子和 Stop。Stop 不改变当前系统态并结束量子操作。没有量子旁路、额外量子辅助载体或 reset。每个固定种子的实际协议树有限终止，允许不同种子有不同有限深度；种子分布、树选择、控制及终端后处理均可测。完整原始记录作为协议历史保留，最后经共同经典后处理粗化为两个旗标，并保留系统输出。

比较的通道输出类型统一为 $\mathbb C^d\otimes\mathbb C^2$。若要求把更精细的原始记录也放入最终距离，目标必须另给同类型记录扩展；下列结论对该粗化输出成立，因而也是任一这种扩展的下界。任意系统酉操作构成原五模等待操作的扩大类；在扩大类成立的下界也适用于原菜单。

令 $P$ 为非零真投影、$Q=I-P$、$r=\operatorname{rank}Q\ge2$。目标 Lüders 旗标通道为

<a id="eq-4-u07"></a>

$$
\Lambda(X)=PXP\otimes|+\rangle\langle+|
+QXQ\otimes|-\rangle\langle-|.
$$

<a id="thm-4-4"></a>

**定理 4.4（原菜单的统一完整仪器下界）。** 在只允许系统酉、完整秩一投影、经典反馈、输入无关随机种子和有限终止协议，且无量子旁路、额外量子辅助或 reset 的菜单下，任意实现通道 $\Gamma$ 满足

<a id="eq-4-2"></a>

$$
\frac12\|\Gamma-\Lambda\|_\diamond
\ge\frac{r-1}{2r-1}.
\tag{4.2}
$$

原五模单模式 $P$ 有 $r=4$，因此下界为 $3/7$。

**证明。** 令 $w$ 为最终输出负旗标、且此前从未量子读出的协议路径的总种子概率。第一次读出之前没有输入相关的经典信息，所以 $w$ 与量子输入无关。负分支映射可分成

$$
M_-=N_-+E_- ,\qquad N_-^*(I)=wI,qquad E_-^*(I)\le(1-w)I.
$$

$N_-$ 是总权重 $w$ 的酉通道混合。每条包含一次秩一读出的路径，其 Kraus 乘积的秩至多一，因此 $E_-$ 作用于任意带参考输入都给可分正算子。每个固定种子的读出负支是完全正、迹不增映射，其归一化 Choi 正且迹至多一；可测性和有限维性保证对种子积分存在。可分正锥在迹有界截面上闭，积分仍可分。

先取支撑在 $P$ 中的输入。目标负概率为零，实际负概率至少为 $w$，所以距离至少 $w$。再取 $Q$ 与一个 $r$ 维数学参考间的最大纠缠态

$$
|\Omega_Q\rangle=r^{-1/2}\sum_{j=1}^r|q_j\rangle|j\rangle.
$$

目标在负旗标中完整保留该纯态。$N_-$ 对这个测试的重叠不超过 $w$。对任意可分正算子 $\sigma$，Cauchy--Schwarz 对纯乘积给
$\langle\Omega_Q|\sigma|\Omega_Q\rangle\le\operatorname{Tr}(\sigma)/r$，再用凸性扩展；故 $E_-$ 的重叠至多 $(1-w)/r$。于是读取效果 $|\Omega_Q\rangle\langle\Omega_Q|\otimes|-\rangle\langle-|$ 给距离至少 $(1-w)(1-1/r)$。因此

<a id="eq-4-u08"></a>

$$
\frac12\|\Gamma-\Lambda\|_\diamond
\ge\max\{w,(1-w)(r-1)/r\}
\ge\frac{r-1}{2r-1}.
$$

**来源与地位。** 这是对项目续卷 Theorem 49.1 的自足复证（见[文献 3](#ref-3)）。该参考仅用于定义和下界测试，不表示原装置已获准制备纠缠输入；本定理没有声称一般 $3/7$ 下界可以达到。

<a id="thm-4-5"></a>

**定理 4.5（效果约束下的相干误差与尖锐值）。** 若负效果满足

<a id="eq-4-u09"></a>

$$
\|M_-^*(I)-Q\|_{\operatorname{op}}\le\eta,\qquad 0\le\eta\le1,
$$

则

<a id="eq-4-3"></a>

$$
\frac12\|\Gamma-\Lambda\|_\diamond
\ge\max\left\{\frac{r-1}{2r-1},(1-\eta)\left(1-\frac1r\right)\right\}.
\tag{4.3}
$$

**证明（效果约束）。** 对 $P$ 中任意归一化输入，实际负概率不超过 $\eta$，又至少为 $w$，所以 $w\le\eta$。前一证明的第二个见证给 $(1-w)(1-1/r)\ge(1-\eta)(1-1/r)$，同时保留统一下界。

若效果完全正确，先作原完整基测量后合并 $Q$ 标签，得到

$$
\Gamma_{\rm fine}(X)=PXP\otimes|+\rangle\langle+|
 +\sum_{j=1}^{r}P_jXP_j\otimes|-\rangle\langle-|,
\qquad Q=\sum_{j=1}^{r}P_j .
$$

令 $\mathcal D_Q$ 为 $Q$ 子空间的完全去相干通道。取
$Z_Q=\sum_{j=1}^{r}e^{2\pi\mathrm i(j-1)/r}|q_j\rangle\langle q_j|$，则

$$
\mathcal D_Q=\frac1r\sum_{k=0}^{r-1}\operatorname{Ad}_{Z_Q^k}
=\frac1r\operatorname{id}_Q+\left(1-\frac1r\right)\mathcal R
$$

其中 $\mathcal R$ 是其余相位酉的平均通道。因此
$\tfrac12\|\operatorname{id}_Q-\mathcal D_Q\|_\diamond\le1-1/r$，先作 $QXQ$ 过滤不增这个界。另一方面，在 $|\Omega_Q\rangle$ 上目标是纯态，实际是 $r^{-1}\sum_j|q_j,j\rangle\langle q_j,j|$；其半迹范数恰为 $1-1/r$。上下界一致，得到精确效果约束下的尖锐值 $1-1/r$，原五模为 $3/4$。有误差 $\eta>0$ 的整条下界曲线尚未证明尖锐。

这里的 $3/4$ 只是在**精确二元效果约束**下的尖锐值；有误差 $\eta>0$ 时，上式给出下界，但尚未证明整条曲线尖锐。正确的概率输出也不自动提供拒绝子空间的相干后继；该后继必须作为单独的仪器能力提供和检验。

<a id="sec-5"></a>

## 5. 完整递归的误差与内生策略

策略距离的相关背景见[文献 11](#ref-11)；下面直接证明有限调用预算。

<a id="thm-5-1"></a>

**定理 5.1（共同自适应续接的误差预算）。** 对每个深度 $k-1$ 的实际经典历史 $h$，两模型仪器满足

<a id="eq-5-u01"></a>

$$
\tfrac12\|\operatorname{Inst}_{\Phi_{k,h}}-\operatorname{Inst}_{\Psi_{k,h}}\|_\diamond
\le\varepsilon_{k,h},
\qquad\varepsilon_k=\sup_h\varepsilon_{k,h}.
$$

将会再次参与的记忆与环境纳入共同载体，使用同一因果控制程序，协议至多调用 $N$ 次，停止节点用共同吸收填充。若初始联合状态距离为 $d_0$，则

<a id="eq-5-1"></a>

$$
D(\Omega_N^\Phi,\Omega_N^\Psi)
\le\min\left\{1,d_0+\sum_{k=1}^N\varepsilon_k\right\}.
\tag{5.1}
$$

共同初态时，最终通道的 half-diamond 距离也受同一和控制。

**证明。** 将每轮共同预处理、历史控制、仪器调用、记录追加和共同后处理合为 $F_k^\Phi,F_k^\Psi$。轮前联合态写成经典历史直和 $\omega=\bigoplus_h\omega_h$，块范数相加给出每轮差不超过 $\varepsilon_k$；插入 $F_k^\Phi(\Omega_{k-1}^\Psi)$，用共同 CPTP 收缩并归纳即可。任意未操作参考可贯穿全过程。

这个证明没有假设独立重复样本。核心条件是每轮误差界对实际可能出现的参考、记忆和控制上下文成立。若黑箱含隐藏的可复用记忆，单轮约化通道未必满足该条件；此时应比较完整多轮策略，或把相应记忆显式纳入共同载体。

<a id="cor-5-2"></a>

**推论 5.2（访问概率而非最坏深度）。** 若 $q_{k-1}^{\Psi}(h)$ 是到达节点 $h$ 的概率，则

<a id="eq-5-2"></a>

$$
D(\Omega_N^\Phi,\Omega_N^\Psi)
\le d_0+\sum_{k=1}^N\sum_hq_{k-1}^\Psi(h)\varepsilon_{k,h}.
\tag{5.2}
$$

交换 $\Phi,\Psi$ 后的访问概率界也成立。若全部活动调用误差不超过 $\varepsilon$，$T$ 是实际调用次数，则

$$
D(\Omega_N^\Phi,\Omega_N^\Psi)
\le\min\left\{1,\ d_0+
\varepsilon\min\{\mathbb E_\Phi\min(T,N),\mathbb E_\Psi\min(T,N)\}\right\}.
$$

**证明。** 在主定理的逐轮估计中保留 $\sum_hq_h\varepsilon_{k,h}$，不用最坏上界；活动层的概率总和等于截断调用次数的期望。交换两模型后再取两者较小者，并与距离上界一取最小。

**例 5.2（局部近似不等于全部未来近似）。** 过程 $\Phi$ 每次必记 continue；$\Psi$ 每次活动调用以概率 $0<\varepsilon\le1$ 记 Stop，否则 continue。单次距离是 $\varepsilon$，但前 $N$ 次完整记录的 TV 为

$$
1-(1-\varepsilon)^N\longrightarrow1.
$$

这是合法的有限经典仪器例子，同时使访问概率界精确饱和。

相干误差也可线性累积。令 $U_\theta=e^{-\mathrm i\theta Z}$，$0<\theta$、$N\theta\le\pi/2$。恒等通道与 $\operatorname{Ad}_{U_\theta}$ 的单次 half-diamond 为 $\sin\theta$：带参考纯输入的两输出重叠是 $\operatorname{Tr}(\rho U_\theta)=\cos\theta-\mathrm i\sin\theta\operatorname{Tr}(\rho Z)$，模至少 $\cos\theta$，$|+\rangle$ 达到等号。执行 $N$ 次，从 $|+\rangle$ 得距离 $\sin(N\theta)$，且 $\sin(N\theta)/(N\sin\theta)\to1$。因此统一加法界中的系数一不能改小，也不能普遍换成独立经典失配的乘积公式。

<a id="prop-5-3"></a>

**命题 5.3（策略本身变化的误差）。** 在一个节点，控制器按 $\pi(a)$、$\widetilde\pi(a)$ 选择动作并记录标签；同一动作距离为 $\varepsilon_a$，则总 half-diamond 距离不超过

<a id="eq-5-3"></a>

$$
\operatorname{TV}(\pi,\widetilde\pi)
+\sum_a\min\{\pi(a),\widetilde\pi(a)\}\varepsilon_a.
\tag{5.3}
$$

**证明。** 令 $m_a=\min\{\pi(a),\widetilde\pi(a)\}$。在动作块中先配对共同质量 $m_a$，再把剩余质量留给单方通道。共同质量贡献至多 $m_a\varepsilon_a$；剩余质量的半迹范数求和为 $\operatorname{TV}(\pi,\widetilde\pi)$。对输入和参考取上确界即得。

评分微小变化不保证最大值选择稳定。例如评分 $(0,\eta)$ 与 $(\eta,0)$ 的逐项差只有 $\eta$，确定性最大值选择却完全相反。若评分误差至多 $\eta$，且最佳动作与其余动作的间隔严格大于 $2\eta$，则最优动作保持不变，因为两端评分各最多移动 $\eta$。这使“预测成为观察者自身增长”进入整体因果原子的误差预算。

<a id="sec-6"></a>

## 6. 有限分辨率、后选择与镜像稳定

<a id="sec-6-1"></a>

### 6.1 保留失败质量才能正确条件化

对次归一化正算子 $A,B$，令 $p=\operatorname{Tr}A$、$q=\operatorname{Tr}B$，并置

<a id="eq-6-u01"></a>

$$
\overline D(A,B)=\tfrac12\|A-B\|_1+\tfrac12|p-q|.
$$

<a id="thm-6-1"></a>

**定理 6.1（后选择的精确放大界）。** 若共同事件筛选得到成功块 $A,B$ 且 $p,q>0$，完整成功／失败输出距离不超过 $\delta$，则

<a id="eq-6-1"></a>

$$
|p-q|\le\delta,\qquad
D(A/p,B/q)
\le\min\left\{1,\frac{\overline D(A,B)}{\max(p,q)}\right\}
\le\min\left\{1,\frac{\delta}{\max(p,q)}\right\}.
\tag{6.1}
$$

**证明。** 失败块的迹差给出 $|p-q|$。若 $p\ge q$，则

<a id="eq-6-u02"></a>

$$
 pD(A/p,B/q)\le\tfrac12\|A-B\|_1+\tfrac12(p-q)=\overline D(A,B),
$$

另一种次序交换两者。归一化态的距离至多一，故得（6.1）。

**例 6.1（误差在稀有分支上完全显现）。** 取 $0<r\le1$、$0\le t\le1$。两制备仪器都以概率 $r$ 成功，失败态相同；成功态分别为 $|0\rangle\langle0|$ 与 $(1-t)|0\rangle\langle0|+t|1\rangle\langle1|$。完整距离是 $rt$，条件距离是 $t$，精确达到 $\delta/r$。取 $t=1,r=\delta$，任意小整体误差都可在该稀有分支上成为距离一。若只知真实成功概率 $p\ge p_0>0$，还须 $\delta<p_0$ 才能保证另一模型的 $q>0$；若 $q=0$，另一模型的条件态没有定义。

<a id="sec-6-2"></a>

### 6.2 近似关系不是等价关系

**定义 6.2（分辨率下的预测距离）。** 对声明未来协议族 $\mathscr T$ 定义

<a id="eq-6-u03"></a>

$$
 d_{\mathscr T}(z,z')=\sup_{\Pi\in\mathscr T}\operatorname{TV}(P_z^\Pi,P_{z'}^\Pi).
$$

它是伪距离；$d_{\mathscr T}=0$ 定义精确商。固定 $\varepsilon>0$ 的“距离不超过 $\varepsilon$”一般不定义商。在可直接读出的二元概率线段上距离就是 $|p-q|$；在线段 $0,\varepsilon,2\varepsilon$ 上相邻两对均近邻而首尾不近邻。任意两点可以用步长不超过 $\varepsilon$ 的有限链连接，因此近邻关系的传递闭包把整条线段合并，包括完全可区分的端点 $0,1$。

**证明。** 三点距离直接由 $|p-q|$ 给出；对任意区间作等分即可构造有限链。

**命题 6.2（近邻传递闭包可能丢失全部区别）。** 在可直接读出的二元概率线段上，距离就是 $|p-q|$。$0,\varepsilon,2\varepsilon$（$0<\varepsilon\le1/2$）的相邻两对均近邻而首尾却不是。任意两点可以用步长不超过 $\varepsilon$ 的有限链连接，故近邻关系的传递闭包把整条线段合并，包括完全可区分的端点 $0,1$。

**证明。** 直接计算三点距离；对任意区间作等分即可构造有限链。

<a id="sec-6-3"></a>

### 6.3 镜子何时会稳定

<a id="thm-6-2"></a>

**定理 6.2（有限网与递归误差）。** 固定 $d$ 维密度态集，对每个 $\eta>0$ 存在有限迹距离 $\eta$ 网，基数可取

<a id="eq-6-u04"></a>

$$
M\le(1+2/\eta)^{d^2-1}.
$$

若 $D(Q_k\omega,\omega)\le\eta_k$，真实与估计 CPTP 更新 half-diamond 距离不超过 $\varepsilon_k$，则

$$
\rho_{k+1}=T_k(\rho_k),
\qquad
\widehat\rho_{k+1}=Q_{k+1}(\widetilde T_k(\widehat\rho_k)).
$$

<a id="eq-6-2"></a>

$$
D(\rho_N,\widehat\rho_N)
\le D(\rho_0,\widehat\rho_0)+
\sum_{k=0}^{N-1}(\varepsilon_k+\eta_{k+1}).
\tag{6.2}
$$

**证明。** 迹一 Hermitian 仿射空间的实维数为 $d^2-1$；状态集位于以 $I/d$ 为中心、迹距离半径一的球内。取极大的 $\eta$ 分离集，半径 $\eta/2$ 的开球互不相交且落在半径 $1+\eta/2$ 的球内，体积比给出 $M\le(1+2/\eta)^{d^2-1}$，极大性给出覆盖。递归式中依次插入 $T_k(\widehat\rho_k)$ 和 $\widetilde T_k(\widehat\rho_k)$，应用 CPTP 收缩、更新误差和代表误差，再归纳得到（6.2）。

**命题 6.3（完整旧记录排除全域严格收缩）。** 若更新完整保留旧经典记录，且存在两个不同的允许记录扇区，则不可能对全部联合状态有统一 $\kappa<1$ 使 $D(T\rho,T\sigma)\le\kappa D(\rho,\sigma)$。

**证明。** 取分别支撑在两个记录扇区中的状态。初始距离为一；更新后读取旧记录仍能完全区分，距离仍为一。

若某个**预测摘要**的更新另有证明的收缩常数 $\kappa<1$，则

<a id="eq-6-3"></a>

$$
 e_N\le\kappa^Ne_0+
 \sum_{k=0}^{N-1}\kappa^{N-1-k}(\varepsilon_k+\eta_{k+1}),
 \qquad
 \limsup_{N\to\infty}e_N\le\frac{\varepsilon+\eta}{1-\kappa}
\tag{6.3}
$$

其中末式取统一误差上界；证明只是反复代入并求几何和。因此“镜像最终稳定”可以是摘要的收敛定理，但需要明确摘要、距离、收缩和分辨率，不能从所有递归或完整历史自动推出。

<a id="sec-7"></a>

## 7. 量与尺子同时不准时，怎样得到操作误差

<a id="sec-7-1"></a>

### 7.1 归一化 Choi 约定

[Choi 文献](#ref-9)与[Watrous 第三章](#ref-10)提供本节标准操作框架的背景。

对 $\Phi:\mathcal L(\mathbb C^d)\to\mathcal L(\mathbb C^m)$，令

<a id="eq-7-u01"></a>

$$
|\Omega_d\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle,
\qquad
J_\Phi=(\Phi\otimes\operatorname{id})(|\Omega_d\rangle\langle\Omega_d|).
$$

输出因子在前、输入参考在后；保迹等价于 $\operatorname{Tr}_{\rm out}J_\Phi=I_d/d$，完全正等价于 $J_\Phi\succeq0$。若 $J_\Phi=\sum_\ell|v_\ell\rangle\langle v_\ell|$，则 $\operatorname{vec}(K_\ell)=\sqrt d\,v_\ell$ 给出 Kraus 表示；反向由 Kraus 展开直接得到正性。在这个约定中，单个 Kraus 的输出偏迹带转置，但对目标 $I_d/d$ 不改变保迹条件。

<a id="lem-7-1"></a>

**引理 7.1（Choi 与完整操作范数）。** 任意复线性映射差 $\Delta$ 满足

<a id="eq-7-1"></a>

$$
\|J_\Delta\|_1\le\|\Delta\|_\diamond\le d\|J_\Delta\|_1.
\tag{7.1}
$$

证明：左边取最大纠缠输入；右边将任意参考向量写成 $u=\sum_j|j\rangle|u_j\rangle$ 并定义 $K_u|j\rangle=\sqrt d|u_j\rangle$，从而

<a id="eq-7-u02"></a>

$$
(\Delta\otimes\operatorname{id})(|u\rangle\langle v|)
=(I_m\otimes K_u)J_\Delta(I_m\otimes K_v^\dagger).
$$

**证明。** 左边取 $|\Omega_d\rangle$ 作为 diamond 范数的一个输入。右边取任意参考及单位向量 $u=\sum_j|j\rangle|u_j\rangle$、$v=\sum_j|j\rangle|v_j\rangle$，定义 $K_u|j\rangle=\sqrt d|u_j\rangle$、$K_v|j\rangle=\sqrt d|v_j\rangle$。二者算子范数至多 $\sqrt d$，直接展开给出

$$
(\Delta\otimes\operatorname{id})(|u\rangle\langle v|)
=(I_m\otimes K_u)J_\Delta(I_m\otimes K_v^\dagger).
$$

迹范数至多 $d\|J_\Delta\|_1$。任意输入算子作奇异值分解 $X=\sum_\ell s_\ell|u_\ell\rangle\langle v_\ell|$，使用 $\sum_\ell s_\ell=\|X\|_1$ 及三角不等式，最后取上确界即得（7.1）。

<a id="sec-7-2"></a>

### 7.2 有限框架的精确误差证书

**定义 7.1（输入与输出双基）。** 取 $d^2$ 个密度态 $\rho_j$ 构成 $\operatorname{Herm}_d$ 的实基，取 $m^2$ 个合法效果 $0\le E_i\le I$ 构成 $\operatorname{Herm}_m$ 的实基。取 Hermitian 对偶基 $D_j,F_i$，满足

$$
\operatorname{Tr}(D_j\rho_k)=\delta_{jk},
\qquad \operatorname{Tr}(E_iF_\ell)=\delta_{i\ell}.
$$

双基通常不是正算子；它们用于数学重构，不自动是可执行操作。

<a id="thm-7-2"></a>

**定理 7.2（概率框架到完整仪器误差）。** 对 Hermitian 保持映射差 $\Delta$，令 $\delta p_{ij}=\operatorname{Tr}(E_i\Delta(\rho_j))$，则

<a id="eq-7-2"></a>

$$
J_\Delta=\frac1d\sum_{ij}\delta p_{ij}F_i\otimes D_j^{\mathsf T},
\qquad
\|\Delta\|_\diamond
\le\sum_{ij}|\delta p_{ij}|\|F_i\|_1\|D_j\|_1.
\tag{7.2}
$$

**证明。** 双基给出 $X=\sum_j\operatorname{Tr}(D_jX)\rho_j$ 和 $\Delta(\rho_j)=\sum_i\delta p_{ij}F_i$。先在 Hermitian 空间成立，再作复线性延拓。映射 $X\mapsto F_i\operatorname{Tr}(D_jX)$ 的归一化 Choi 为 $F_i\otimes D_j^{\mathsf T}/d$，应用引理 7.1、张量迹范数乘法性与三角不等式得到第一项和第二项。完整记录的 Choi 矩阵是分块直和；各块迹范数相加，再除以二即得仪器界。

对带结果仪器，各分支使用自己的输出双基；若联合概率误差至多 $\zeta_{aij}$，则

<a id="eq-7-3"></a>

$$
\delta(\Phi,\Psi)\le
\frac12\sum_{aij}\zeta_{aij}\|F_{a,i}\|_1\|D_j\|_1.
\tag{7.3}
$$

<a id="cor-7-3"></a>

**推论 7.3（输入、量具和概率读数同时有误差）。** 若

<a id="eq-7-u03"></a>

$$
D(\rho_j,\widetilde\rho_j)\le\alpha_j,
\qquad
\|E_{a,i}-\widetilde E_{a,i}\|_{\operatorname{op}}\le\beta_{a,i},
$$

且实际读数误差至多 $\xi_{aij}$，则

<a id="eq-7-4"></a>

$$
\frac12\|\operatorname{Inst}_{\widehat\Phi}-\operatorname{Inst}_\Phi\|_\diamond
\le\frac12\sum_{aij}(\xi_{aij}+\alpha_j+\beta_{a,i})
\|F_{a,i}\|_1\|D_j\|_1.
\tag{7.4}
$$

**证明。** 输入差项可写成 $\operatorname{Tr}(\Phi_a^*(\widetilde E_{a,i})(\rho_j-\widetilde\rho_j))$。因为 $0\le\Phi_a^*(\widetilde E_{a,i})\le I$ 且输入差迹为零，其绝对值至多 $\alpha_j$；效果差项至多 $\beta_{a,i}\operatorname{Tr}\Phi_a(\rho_j)\le\beta_{a,i}$。再加入读数误差 $\xi_{aij}$，应用定理 7.2 即得（7.4）。这里若 $\widehat\Phi$ 尚非合法仪器，不把它称为两个物理过程之间的概率距离；稀有分支归一化另需定理 6.1。

<a id="sec-7-3"></a>

### 7.3 尺子退化使小坐标差失去意义

qubit 效果基

<a id="eq-7-u04"></a>

$$
I/2,\quad(I+\epsilon X)/2,\quad(I+\epsilon Y)/2,\quad(I+\epsilon Z)/2,
\qquad 0<\epsilon\le1
$$

始终张成 $\operatorname{Herm}_2$，但 $|0\rangle$ 与 $|1\rangle$ 的所有测试概率差至多 $\epsilon$。对偶基相应放大，因此不能删除框架条件数。

这给出“关系也测不准”的操作含义：不确定的不只是状态坐标，还包括解释它的框架。若框架只有未固定的 $GL$ 规范而无物理标定，首先得到的是该规范下的预测模型，不是已核证的 Hilbert 迹距离或 diamond 距离。

**例 7.3（尺子退化使小坐标差失去意义）。** 在 qubit 上取效果基

$$
I/2,\quad (I+\epsilon X)/2,\quad
(I+\epsilon Y)/2,\quad(I+\epsilon Z)/2,
\qquad 0<\epsilon\le1.
$$

它始终张成 $\operatorname{Herm}_2$。但态 $|0\rangle\langle0|$、$|1\rangle\langle1|$ 的迹距离为一，而所有测试概率差至多 $\epsilon$。对偶基必相应放大，不能删除定理 7.2 中的双基范数。

<a id="sec-8"></a>

## 8. 有限参考测试与保迹完全正修复

<a id="sec-8-1"></a>

### 8.1 有限测试只给带余量的正性

<a id="thm-8-1"></a>

**定理 8.1（有限联合方向网的正性证书）。** 令 $q=md$，$J=J^\dagger$、$\|J\|_{\operatorname{op}}\le M$。若秩一投影族 $\{Q_s\}$ 是全部秩一投影的迹范数 $\eta$ 网，且 $\operatorname{Tr}(Q_sJ)\ge-\delta$，则

<a id="eq-8-1"></a>

$$
J\succeq-\nu I_q,
\qquad\nu=\delta+M\eta.
\tag{8.1}
$$

证明：任意秩一 $Q$ 与某个 $Q_s$ 距离至多 $\eta$，故 $\operatorname{Tr}(QJ)\ge-\delta-M\eta$。

乘积方向不足以证明完全正性。转置映射 $T(X)=X^{\mathsf T}$ 的 Choi 矩阵为交换算子除以 $d$；乘积向量上期望非负，但反对称子空间有本征值 $-1/d$。有限网也只能给余量：取未测试方向 $u$，令

<a id="eq-8-u01"></a>

$$
J=\frac{I-a|u\rangle\langle u|}{q-a}
$$

即可在有限测试上非负、在 $u$ 上为负。

**例 8.1（没有联合参考方向时，正性不足）。** 取 $m=d\ge2$。转置映射 $T(X)=X^{\mathsf T}$ 保持单系统正性与迹，但 $J_T=S/d$，其中 $S$ 是交换算子。在任意乘积向量上

$$
\langle a,b|J_T|a,b\rangle=|\langle a,b\rangle|^2/d\ge0,
$$

而反对称子空间却有本征值 $-1/d$。因此即使检查全部乘积方向，也不等于检查完全正性。

有限联合网也不能精确排除所有负方向。以 $d=1,q=m\ge2$ 为例，对任意有限测试向量取一条未与它们共线的 $u$，令 $c=\max_s|\langle u,v_s\rangle|^2<1$。选择 $1<a<\min(q,1/c)$，则

$$
J=\frac{I-a|u\rangle\langle u|}{q-a}
$$

迹一，在全部有限测试上为正，在 $u$ 上却为负；$c=0$ 时略去 $1/c$ 限制。故网格余量确有必要。

<a id="sec-8-2"></a>

### 8.2 保留归一化的统一修复

<a id="thm-8-2"></a>

**定理 8.2（近似正性到 CPTP 模型）。** 若 $J=J_\Phi$ Hermitian、$\operatorname{Tr}_{\rm out}J=I_d/d$ 且 $J\succeq-\nu I_{md}$，令

<a id="eq-8-u02"></a>

$$
 t=md\nu,\qquad
\mathcal D(X)=\operatorname{Tr}(X)I_m/m,\qquad
\Phi^{\rm cp}=\frac{\Phi+t\mathcal D}{1+t},
$$

则 $\Phi^{\rm cp}$ CPTP 且

<a id="eq-8-2"></a>

$$
\frac12\|\Phi^{\rm cp}-\Phi\|_\diamond\le md^2\nu.
\tag{8.2}
$$

**证明。** $J_{\mathcal D}=I_{md}/(md)$，故 $J^{\rm cp}=(J+\nu I)/(1+t)\succeq0$；偏迹仍为 $I_d/d$。若 $s=\operatorname{Tr}J_-$，则 $s\le md\nu=t$、$\operatorname{Tr}J=1$ 给 $\|J\|_1=1+2s$。因此

<a id="eq-8-u03"></a>

$$
\|J^{\rm cp}-J\|_1
\le\frac{2t(1+s)}{1+t}\le2t,
$$

再用[式（7.1）](#eq-7-1)并除以二。

若估计 Choi 矩阵不保迹，置

<a id="eq-8-u04"></a>

$$
B=\operatorname{Tr}_{\rm out}\widehat J-I_d/d,
\qquad
Y=\widehat J-(I_m/m)\otimes B,
$$

先修正为 $Y$ 再应用定理 8.2，得到

<a id="eq-8-3"></a>

$$
\frac12\|\Phi^{\rm cp}-\widehat\Phi\|_\diamond
\le\frac d2\|B\|_1+md^2\left(\nu+\frac{\|B\|_{\operatorname{op}}}m\right).
\tag{8.3}
$$

完整仪器的各分支必须共同除以 $1+t$，否则会破坏总概率归一化。该修复只产生邻近抽象 CPTP 模型，不证明它属于原五模菜单。

**推论 8.2（保迹残差与分支归一化）。** 若 $\widehat J$ Hermitian 但未必保迹，令

$$
B=\operatorname{Tr}_{\rm out}\widehat J-I_d/d,
\qquad
Y=\widehat J-(I_m/m)\otimes B.
$$

若 $\widehat J\succeq-\nu I$，则 $Y$ 保迹且
$Y\succeq-(\nu+\|B\|_{\operatorname{op}}/m)I$。先修正为 $Y$，再使用定理 8.2，得到 CPTP 映射与原估计映射的距离上界

$$
\frac12\|\Phi^{\rm cp}-\widehat\Phi\|_\diamond
\le\frac d2\|B\|_1+
md^2\left(\nu+\frac{\|B\|_{\operatorname{op}}}m\right).
$$

**证明。** 对 $Y$ 取输出偏迹立即消去 $B$；修正项的迹范数为 $\|B\|_1$、算子范数为 $\|B\|_{\operatorname{op}}/m$。先用引理 7.1 估计保迹修正代价，再用定理 8.2 和三角不等式。

完整仪器须整体保迹。更细地，若各分支 Choi $J_a$ 满足
$\sum_a\operatorname{Tr}_{\rm out}J_a=I_d/d$、$J_a\succeq-\nu_aI_{m_ad}$，令

$$
t_a=m_ad\nu_a,\qquad t=\sum_at_a,\qquad
J_a^{\rm cp}=\frac{J_a+t_aI_{m_ad}/(m_ad)}{1+t}.
$$

所有分支都正，总偏迹仍为 $I_d/d$；在直和上重复负质量证明得到完整仪器修复的 half-diamond 上界 $dt$。分母必须共同，逐支分别除以 $1+t_a$ 一般会破坏总概率归一化。

上述有限网可以只是已重构模型的数学检查；若解释为物理参考测试，必须确实提供联合制备与读出。修复得到邻近的抽象 CPTP 模型，不证明它属于原五模菜单；定理 4.5 正说明即使目标完全正且保迹，原菜单仍可能有无法越过的实现误差。

<a id="sec-9"></a>

## 9. 静态切面的可交换性必须在完整输出上检验

<a id="sec-9-1"></a>

### 9.1 有限测试的充分性

本节的核心结论是未来效果的线性充分判据。

<a id="thm-9-1"></a>

**定理 9.1（未来效果的线性充分判据）。** 在固定 $d$ 维 Hilbert 空间，已测效果为 $E_1,\ldots,E_s$，令

<a id="eq-9-u01"></a>

$$
W=\operatorname{span}_{\mathbb R}\{I,E_1,\ldots,E_s\}.
$$

全部测试概率对所有密度态唯一确定未来效果 $F$ 的期望，当且仅当 $F\in W$。

**证明。** 若 $F=\alpha_0I+\sum_j\alpha_jE_j$，其期望由同一线性组合给出。若 $F\notin W$，以 Hilbert--Schmidt 投影定义 $\Delta=F-P_WF\ne0$。则 $\operatorname{Tr}\Delta=0$、$\operatorname{Tr}(E_j\Delta)=0$，但 $\operatorname{Tr}(F\Delta)=\|\Delta\|_{\mathrm{HS}}^2>0$。取 $0<s_0<1/(d\|\Delta\|_{\operatorname{op}})$，则 $\rho_\pm=I/d\pm s_0\Delta$ 都正定、迹一；它们已测概率相同而未来期望不同。

<a id="sec-9-2"></a>

### 9.2 交换差表

<a id="thm-9-2"></a>

**定理 9.2（有限读数对预测交换子的证书）。** 在真正 $r$ 维闭合预测载体或最小预测商上，令 $C:\mathbb R^r\to V$ 为同构，$H=OC$ 可逆，

<a id="eq-9-u02"></a>

$$
D_{ab}=O(T_bT_a-T_aT_b)C,\qquad A_a=C^{-1}T_aC.
$$

则

<a id="eq-9-u03"></a>

$$
[A_b,A_a]=H^{-1}D_{ab}.
$$

若每个 $D_{ab}$ 元素绝对值不超过 $\delta$，且 $\|\widehat H-H\|_2\le e<\sigma_{\min}(\widehat H)$，则

<a id="eq-9-1"></a>

$$
\|[A_b,A_a]\|_2
\le\frac{r\delta}{\sigma_{\min}(\widehat H)-e}.
\tag{9.1}
$$

**证明。** $O=HC^{-1}$，故

$$
D_{ab}=H[A_b,A_a].
$$

逐元素界给 $\|D_{ab}\|_2\le\|D_{ab}\|_{\mathrm{HS}}\le r\delta$。对单位向量 $x$，
$\|Hx\|\ge\|\widehat Hx\|-e\ge\sigma_{\min}(\widehat H)-e$，所以
$\|H^{-1}\|_2\le[\sigma_{\min}(\widehat H)-e]^{-1}$，相乘即得（9.1）。这里必须先证明闭合并移到有效载体；原大载体中的矩形 $C$ 一般没有逆，Euclidean 坐标界也不能直接冒充 diamond 界。

<a id="sec-9-3"></a>

### 9.3 有限 DAG 的稳健切面不变性

<a id="thm-9-3"></a>

**定理 9.3（有限 DAG 的稳健切面不变性）。** 设有限事件偏序的每个事件对应共同载体上的 CPTP 映射 $\mathcal E_e$，含结果寄存器和观察者记忆；不可比事件满足

<a id="eq-9-u04"></a>

$$
\tfrac12\|\mathcal E_e\mathcal E_f-\mathcal E_f\mathcal E_e\|_\diamond
\le\kappa_{ef}.
$$

若两个线性扩张由 $K$ 次相邻不可比事件交换连接，则完整组合通道距离满足

<a id="eq-9-2"></a>

$$
\tfrac12\|\mathcal C_\sigma-\mathcal C_\tau\|_\diamond
\le\sum_{\text{交换路径}}\kappa_{ef}
\le K\kappa.
\tag{9.2}
$$

**证明。** 先证明两个线性扩张可由相邻不可比事件交换连接：取目标次序的首事件，把它在当前次序中向前移动；它前面的事件都与它不可比，否则某个次序违反偏序。逐个相邻交换后固定该事件，再对剩余事件归纳。单次交换的整个组合差是

$$
\mathcal S\circ(\mathcal E_e\mathcal E_f-\mathcal E_f\mathcal E_e)\circ\mathcal P,
$$

其中前、后缀是 CPTP，故不放大 diamond 缺陷；对全部交换应用三角不等式得到（9.2）。若记录分别追加 $A$ 与 $B$，即使系统端恒等，完整输出也可能因 $AB$ 与 $BA$ 不同而距离一。

<a id="sec-10"></a>

## 10. 从静态完成到实际模型：紧性提供什么

<a id="sec-10-1"></a>

### 10.1 相容线程与实际来源像

相容线程与实际来源像的区别见[文献 5](#ref-5)。

<a id="thm-10-1"></a>

**定理 10.1（闭纤维紧性实现）。**

设 $X$ 为非空紧空间，观测 $q_n:X\to X_n=q_n(X)$ 满足 $q_n=b_nq_{n+1}$。若每条纤维 $q_n^{-1}(\{x_n\})$ 都闭，则每个相容线程 $b_n(x_{n+1})=x_n$ 都由某个 $x\in X$ 实现。

**证明。** 对给定线程置 $F_n=q_n^{-1}(\{x_n\})$。相容性使每个 $F_n$ 非空；它们闭且嵌套。紧空间中这组闭集有有限交性质，故 $\bigcap_nF_n\ne\varnothing$，其中任一点就是所求来源。∎

<a id="ex-10-1"></a>

**例 10.1（每层可实现而没有共同来源）。** 取 $X=\mathbb N_{\ge1}$、$q_n(x)=\min(x,n)$。线程 $x_n=n$ 相容，每个有限初段可由充分大的整数实现；但没有一个有限整数同时满足全部 $q_n(x)=n$。因此“每一层都有”与“同一个来源拥有全部层”之间需要紧性等额外条件。

<a id="sec-10-2"></a>

### 10.2 固定量子资源类的实现与有限证伪

**定义 10.1（固定量子参数类）。** 固定载体维数 $D$、有限动作菜单和有限非空结果集；所有会复用的装置记忆均计入 $D$。参数由初态密度矩阵和各动作完整仪器的 Choi 块组成：

<a id="eq-10-u01"></a>

$$
\rho\succeq0,\quad\operatorname{Tr}\rho=1,\qquad
J_{a,o}\succeq0,\quad
\sum_o\operatorname{Tr}_{\rm out}J_{a,o}=I_D/D.
$$

同一仪器在全部层复用；若控制器也未知，应把它的有限参数和记忆一起固定，而不能每增加一个约束就悄悄扩大资源。记此非空参数集为 $\Theta_D$。

<a id="thm-10-2"></a>

**定理 10.2（固定资源类中的相容实现）。** 参数集 $\Theta_D$ 是紧集；每个有限原始字概率连续。若每个有限闭概率约束子族在同一 $\Theta_D$ 内可实现，则全部约束有共同模型。若 $\vartheta_n$ 对所有 $|w|\le n$ 的误差趋于零，则收敛子列给出对全部有限字精确实现的 $\vartheta_*$。

**证明。** 初态集合闭有界。每个 Choi 块正且迹不超过一，所有块的归一化条件是闭线性约束，所以有限个块组成闭有界有限维集合，即为紧。由 Choi 到线性映射是线性变换，有限复合及末端取迹是参数的多项式，故每个有限字概率连续。闭概率约束对应紧空间的闭子集，有限交性质给出共同点。近似情形取 $\vartheta_n$ 的收敛子列；对任一固定字，从充分大的子列项起误差趋零，由连续性得到极限精确满足该字，这个同一极限适用于每个固定字。

<a id="cor-10-3"></a>

**推论 10.3（紧模型类失败必有有限正间隔见证）。** 若目标全部字概率在 $\Theta_D$ 中没有实现，则存在有限字集 $F$ 和 $\epsilon_0>0$，使

<a id="eq-10-u02"></a>

$$
\inf_{\vartheta\in\Theta_D}\max_{w\in F}|p_\vartheta(w)-p_*(w)|=\epsilon_0>0.
$$

这不给出找到 $F$ 的有效算法、长度上界或实际采样能力。

**例 10.2（允许维数随精度增长会失去固定实现）。** 取一个非最终周期的确定二进制序列。每个有限前缀都能由有限经典计数器逐次输出，因此也能由有限维量子仪器实现；维数可以随前缀增长。但不存在一个固定有限维、同一仪器反复调用的模型精确产生整个序列。

**证明。** 假设有这样的模型，记第 $n$ 个前缀后的归一化态为 $\rho_n$。非最终周期性保证任意两个不同位置的无限后缀不同，因此对任意 $n\ne m$，某个有限未来输出字的效果在 $\rho_n,\rho_m$ 上分别给概率 $1$ 与 $0$。对 $0\le E\le I$，这迫使两个态的支撑分别位于 $E$ 的本征值 $1$ 和 $0$ 空间，因而正交。于是有限维空间含无限多个非零两两正交支撑，矛盾。该例排除的是统一有限维实现；允许无限记忆或新增外部时变控制会改变模型类。


<a id="sec-11"></a>

## 11. 存在一个谱，不等于取得完整 Read 服务

<a id="thm-11-1"></a>

**定理 11.1（有限纯态标本的不可区分代价）。** 两个已知纯态等先验、重叠模 $0<c<1$，提供有限 $m\ge1$ 份标本及共同源无关辅助态。任意联合 POVM 的最小平均错误率为

<a id="eq-11-1"></a>

$$
 p_m^{\rm err}=\frac{1-\sqrt{1-c^{2m}}}{2}.
\tag{11.1}
$$

若每个来源错误率不超过 $0<\epsilon<1/2$，必要条件为

<a id="eq-11-2"></a>

$$
 m\ge\frac{\log(1/[4\epsilon(1-\epsilon)])}{-2\log c}.
\tag{11.2}
$$

**证明。** 对等先验 $\rho,\sigma$，取二元效果 $E$，成功率为 $\frac12+\frac12\operatorname{Tr}(E(\rho-\sigma))$。在 $0\le E\le I$ 上，最大值由 $\rho-\sigma$ 的正本征空间投影达到，为 $\frac12+\frac14\|\rho-\sigma\|_1$。两纯态差在其二维张成空间中的本征值为 $\pm\sqrt{1-c^2}$；$m$ 份纯态的重叠是 $c^m$，故得到（11.1）。共同源无关辅助态张量因子的迹范数为一，不改变差的迹范数。逐来源错误率不超过 $\epsilon$ 蕴含平均错误率不超过 $\epsilon$；整理 $c^{2m}\le4\epsilon(1-\epsilon)$ 即得（11.2）。这是标准二态区分结论（见[Watrous 第三章定理 3.4](#ref-10)），此处的自足证明用于固定归一化，不把它声称为 AURIC 语法的新量子公理。

[项目有限标本卷](#ref-7) §§2–4 给出真实同尺度树对 $U_n,V_n$ 的 $c_n=1-\delta/w_n$、$\delta=(\sqrt\varphi-1)^2$、$w_n=2(n+\varphi^2)$。固定 $m$ 时错误率趋于 $1/2$；利用 $-\log(1-x)\le x/(1-x)$ 得

<a id="eq-11-3"></a>

$$
 m\ge\frac{w_n-\delta}{2\delta}\log\frac1{4\epsilon(1-\epsilon)}.
\tag{11.3}
$$

这说明原精确 Read 服务与有限量子标本属于不同输入合同，并非量子理论内部矛盾。

<a id="prop-11-2"></a>

**命题 11.2（精确标签需要正交旁记录）。** 若主标本纯态 $\psi_u$ 两两非正交，旁记录态为 $\eta_u$，有限协议能从
$|\psi_u\rangle^{\otimes m}\otimes\eta_u$ 精确输出标签 $u$，则不同 $\eta_u$ 的支撑两两正交，故

<a id="eq-11-u01"></a>

$$
\dim E\ge\#\{u\}.
$$

**证明。** 精确输出标签意味着不同输入支撑可由某个效果以 $1$ 与 $0$ 区分，正性迫使这些支撑正交。主纯态的内积为 $\langle\psi_u|\psi_v\rangle^m\ne0$，所以张量积支撑的正交性只能来自旁记录态支撑的正交性。每个来源至少需要一个非零正交维度，故 $\dim E\ge\#\{u\}$。∎

<a id="sec-12"></a>

## 12. 相干记录的条件实现与量子公理的准确位置

<a id="sec-12-1"></a>

### 12.1 一比特相干记录如何补上缺失能力

<a id="thm-12-1"></a>

**定理 12.1（Lüders 原子的条件实现）。** 设 $P$ 为非零真投影、$Q=I-P$。另供一比特辅助载体 $A$、初态 $|0\rangle_A$、联合酉

<a id="eq-12-u01"></a>

$$
U=P\otimes X_A+Q\otimes I_A.
$$

读取 $A$ 的结果 $1,0$ 分别实现 $X\mapsto PXP$、$X\mapsto QXQ$。忘记旗标后的通道
$\mathcal L(X)=PXP+QXQ$ 在“固定纯辅助态、联合酉、最后丢弃辅助系统”的实现类中最小环境维数恰为二。

**证明。** $P,Q$ 正交且和为 $I$，故 $U$ 酉。对任意参考，

<a id="eq-12-u02"></a>

$$
|\psi\rangle|0\rangle_A\mapsto
(P\otimes I_R)|\psi\rangle|1\rangle_A+
(Q\otimes I_R)|\psi\rangle|0\rangle_A.
$$

读出辅助比特即得两个未归一化分支。归一化 Choi 是 $\operatorname{vec}(P)$ 与 $\operatorname{vec}(Q)$ 的两个正交秩一项，Choi 秩为二；任意纯环境实现的维数至少为 Choi 秩，上面的实现达到二。

<a id="sec-12-2"></a>

### 12.2 公理、条件定理与尚待选择的结构

| 问题 | 本稿已经得到 | 仍需的输入或证明 |
| --- | --- | --- |
| 观察者是什么 | 可作为联合系统中的记忆、状态和控制程序；误差计入同一递归。 | 具体记忆载体及实际允许操作。 |
| 预测原子是什么 | 结果、后态、记录相关性和续接共同组成完整仪器。 | 由五个几何角色到该仪器的明确实现。 |
| 有限分辨率是否足够 | 固定紧模型族内有噪拟合可稳健；完整递归有误差预算。 | 真实模型归属、读数误差证书、未来闭合或维数约束。 |
| 镜像是否收敛 | 摘要若严格收缩，得到几何误差界；全记录一般不严格收缩。 | 摘要定义、收缩常数及罕见分支概率控制。 |
| 为什么完全正 | 保留参考并要求联合正性对应 Choi 正性；有限网给近似证书。 | 张量参考结构与复线性语义已安装。 |
| 为什么平方权重 | 环积公式、标本区分和 Born 权重在所用框架内相容。 | 未从裸递归或五点图唯一推出 Born 规则。 |
| 为什么复数与连续性 | 复模型中的相位环积和稳定法形可读。 | 排除其他概率理论、固定复结构及连续模型选择原则。 |
| 静态完成是否真实 | 固定紧资源类的闭约束有共同实现与有限证伪见证。 | 实际制备、算法取得和资源成本不由紧性提供。 |

<a id="sec-12-3"></a>

### 12.3 可递归观测原子与最小性

**定义 12.1（可递归观测原子与最小性的合同）。** 相对于固定操作合同，一个可递归观测原子给出输入／输出载体、完整仪器或保相干实现、结果记录及所有允许续接的共同类型。所谓“最小”，必须相对于明确成本偏序定义，例如量子辅助维数、原生控制种类、读出次数和记忆规模；不同成本不能仅凭图的顶点数合并。

NAND 普适性依赖固定布尔语义、编码、张量组合、可实现门族与逼近成本。本文 $3/4$ 尖锐值和一比特条件实现只针对相干拒绝任务，不证明 AURIC 金字塔对全部量子计算普适。

<a id="sec-12-4"></a>

### 12.4 接下来最有判别力的三个问题

1. 在原五模菜单下，完整 Lüders 仪器的无约束最优误差是多少？本文复证的 $3/7$ 是统一下界，精确效果受限类的 $3/4$ 已尖锐，二者之间的一般折中仍待证明。
2. 能否在原始控制和原始带权记录中，为完整仪器而非仅指定终端 law 建立实际可取得的有限标定？框架定理给出充分条件，但制备、参考和重复机会必须由原合同供应。
3. 如何把 VII 的有限范数端点推进到其单独定义的全历史范数？有限行稳定性不会保存所有不同目标范数的最优值和极小点类型。

<a id="sec-provenance"></a>

## 来源、阅读范围与证明地位

### 本稿使用的四种证据

有效 advice 与实际取得的区别另见[文献 6](#ref-6)，v10 前稿见[文献 8](#ref-8)。

源码事实使用固定项目提交 `5517865965160e8d20e4122aafe4e6c468c6c41d` 与比较基线 `7307a34c8f47f70cd39fc47da78328fa3f3ffcde`。Git 对象和文件 blob 核验用于确认文本身份，不证明文本中的全部数学结论。

本文逐式给出主要新增组合结果：离像拟合、效果约束的精确尖锐代价、量具误差桥、有限余量 CPTP 修复、交换差表、固定资源相容实现、有限标本区分和一比特 Lüders 条件实现。这些名称表示本文的组织和证明，不主张基本数学方法首创。

特别保留以下区别：

- 复相干 Gram 核与经典联合 law 等价关系；
- 原始概率的最大坐标差、完整转录 TV 与 diamond 距离；
- 数学参考测试与实际参考权限；
- 完整读出后合并效果与保留拒绝相干性的仪器；
- 有限维参数紧性、有效算法、实际采样与原生控制实现；
- 本文普通推导、源码原有结论和已有量子信息定理。

标准量子框架、Choi 判据、迹距离及策略距离属于既有理论，分别注明原始文献或作者著作。最新 VII 的 34 阶子式、117 行证书和相关有理界在本轮按源码阅读，没有运行数值或符号程序独立重算，因而不以其大规模算术证书作为本文新普通证明的未说明步骤。

### 项目文本阅读范围

完整阅读或完整新增段阅读覆盖：最小预测核心桥、有限标本读出、量子停止 advice、相干重构续卷 §§42--50，以及相关单参考、自校准和取得卷的新段。选择性深读覆盖：Waves VI §§112--121 的合同、主定理和主要证明；Waves VII §§142--145 的合同、证书结构和精确范围；联合核线程实现的定义与实现条件。其余相关文本用于接口核对，不声称已经逐项验证全部证明。

本轮未修改项目源码，未运行 Lean 或数学实验；文档检查只验证交付文件的数学渲染、交叉引用、链接和版面相关静态证据。

<a id="sec-bibliography"></a>

## 参考文献

以下项目条目的文件路径与本稿固定提交一致；每项链接直接指向该提交的 blob。

<a id="ref-1"></a>

**[1]** AURIC 项目，*[Compatible Predictive Waves and Relational Spectra VI](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md)*。§§114–121，尤其定义 118.1、定理 118.3、推论 118.4、定理 119.1。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-2"></a>

**[2]** AURIC 项目，*[Compatible Predictive Waves and Relational Spectra VII](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VII.md)*。§§142–145；117 行有限最大坐标范数及其非线性端点，不含全历史端点的重算。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-3"></a>

**[3]** AURIC 项目，*[FIB-ATOM Quantum Principles and Coherent Reconstruction: Continuation](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)*。§§47–50，尤其定理 49.1 的有限协议分解、参考见证与 3/7 下界。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-4"></a>

**[4]** AURIC 项目，*[Recursive Relational Observation: Joint Kernel Minimal Predictive Core Bridge](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md)*。完整未来 law 商、实际来源像及最小预测表示。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-5"></a>

**[5]** AURIC 项目，*[Recursive Relational Observation: Joint Kernel Thread Realization](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_THREAD_REALIZATION.md)*。类型化相容塔、实际来源像与虚拟线程的边界。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-6"></a>

**[6]** AURIC 项目，*[Recursive Relational Observation: Quantum Stopping Advice Compilation](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_STOPPING_ADVICE_COMPILATION.md)*。Theorem 3.2、Proposition 6.1；已供应可计算校准名字及承诺输入上的有效有限 advice，不是未知源取得定理。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-7"></a>

**[7]** AURIC 项目，*[FIB-ATOM Original-Boundary Finite-Specimen Readout](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/FIB_ATOM_ORIGINAL_BOUNDARY_FINITE_SPECIMEN_READOUT.md)*。§§1、3–5；有限标本、原始 Read、精确旁记录与共同辅助态的合同。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-8"></a>

**[8]** AURIC 项目，*[Coherent Relations and Recursive Observation Theory V10](https://github.com/the-omega-institute/trureturing/blob/5517865965160e8d20e4122aafe4e6c468c6c41d/docs/develop/theory/AURIC_COHERENT_RELATIONS_AND_RECURSIVE_OBSERVATION_THEORY_V10.md)*。用户前稿的转换收录版；本次没有修改。 固定提交：5517865965160e8d20e4122aafe4e6c468c6c41d。

<a id="ref-9"></a>

**[9]** Man-Duen Choi, “Completely positive linear maps on complex matrices,”
*Linear Algebra and its Applications* **10**(3), 285–290 (1975).
[DOI: 10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

<a id="ref-10"></a>

**[10]** John Watrous, *The Theory of Quantum Information*,
Cambridge University Press (2018), Chapter 3.
[第三章作者公开 PDF](https://cs.uwaterloo.ca/~watrous/TQI/TQI.double.3.pdf)。
本稿用到二元态判别、迹范数与通道距离的标准归一化。

<a id="ref-11"></a>

**[11]** Gus Gutoski, “On a measure of distance for quantum strategies,”
*Journal of Mathematical Physics* **53**, 032202 (2012).
[arXiv:1008.4636，v4](https://arxiv.org/html/1008.4636v4)。
策略距离的背景引用不把本稿有限调用的望远镜证明升级为无限协议定理。
