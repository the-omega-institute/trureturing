# 原局部纯极限与共同正提升

## 132. 有限源测试的正提升障碍与返回球维数

**定义 132.1（原域、局部标签与源误差）。** 保留[131.1][Q132SR]的整个有限维实空间 $V$、闭尖生成锥 $C$、严格正单位 $u$，以及全部 $K=C\cap\{u=1\}$、$P=\operatorname{ext}K$、$\mathcal E=[0,u]_{C^*}$ 和完整原排除集 $D_r$。全局假设仍为 $\mathrm{EB}_{\ge1}$：每个 $D_r$ 是正维、允许变维的整个仿射欧氏闭球。固定一个原纯点 $p$，置 $F=D_p$、$k=\dim\operatorname{aff}F$；$F$ 的相对球面为 $S(F)=P\cap F$。记

$$
\begin{aligned}
I(F)&=\{s\in P:D_s=F\},\\
\mathcal A_a&=\{h\in\mathcal E:h(a)=1,\ h|_{D_a}=0\},\\
N_t&=\{b\in C^*:b(t)=0\},\\
\|b\|_K&=\max_{x\in K}|b(x)|,\qquad
\|b\|_F=\max_{x\in F}|b(x)|,\\
R_F(t,h)&=\inf_{b\in N_t}\|b-h\|_F.
\end{aligned}
\tag{Q132.1}
$$

$\|\cdot\|_F$ 可以是半范数；$R_F$ 只测固定原整球上的误差。$N_t$ 包含全部原锥正泛函，没有上界 $b\le u$。每个候选 $b$ 必须同时在整个 $C$ 上非负、精确零于同一个 $t$，并在整个 $F$ 上承担(Q132.1)的误差；不允许逐输入更换延拓。以下固定 $V$ 的任一范数及其对偶范数。由 $K$ 线性张成 $V$，存在 $A>0$ 使

$$
\|b\|_*\le A\|b\|_K\qquad(b\in V^*).
\tag{Q132.2}
$$

**命题 132.2（移动正零泛函的原单位控制）。** 不要求 $I(F)$ 单点。对 $t\in P$，置

$$
\alpha_p(t)=\max_{x\in D_t}\operatorname{dist}(x,F).
\tag{Q132.3}
$$

则 $t\to p$ 于原 $P$ 时 $\alpha_p(t)\to0$。当 $A\alpha_p(t)<1$ 时，每个 $b\in N_t$ 满足

$$
\max_K b\le
\frac{\max_F b}{1-A\alpha_p(t)}.
\tag{Q132.4}
$$

特别地，若 $t_n\to p$、$b_n\in N_{t_n}$，且 $b_n|_F$ 一致趋于某个 $\ell:F\to[0,1]$，则置

$$
B_n=\max_K b_n,\qquad
f_n=\frac{b_n}{\max\{1,B_n\}},
\tag{Q132.5}
$$

有 $f_n\in\mathcal E$、$f_n(t_n)=0$、$f_n|_F\to\ell$ 一致，且 $\|f_n-b_n\|_K\to0$。若 $\max_F\ell=1$，还有 $B_n\to1$。

证明。纯极限标签处的整球上关联直接复用[IX118.3的(IX118.4)][Q132IX]，其证明不消费Inj或固定球维数。若(Q132.3)不趋零，选 $t_n\to p$ 及 $x_n\in D_{t_n}$，使 $x_n$ 到 $F$ 的距离有正下界；紧 $K$ 中的收敛子列及该上关联给极限在 $F$，矛盾。

对非零 $b\in N_t$，复用原正零泛函的最大值结论[positive_annihilator_maximum][Q132SN]：$B:=\max_Kb=\max_{D_t}b>0$。对每个 $x\in D_t$，取 $z\in F$ 达到到 $F$ 的距离；同一个 $b$ 满足

$$
b(x)\le b(z)+\|b\|_*\|x-z\|
\le\max_Fb+AB\alpha_p(t).
\tag{Q132.6}
$$

取 $D_t$ 上最大值得(Q132.4)。$b=0$ 时同式直接成立。这里最大值原理与(Q132.2)只作既有前置使用；新增控制是对趋近 $p$ 的全部正零泛函统一的(Q132.4)，并未要求它们预先有单位上界。

现在 $m_n:=\max_Fb_n\to\max_F\ell\le1$，且 $0\le m_n\le B_n$。式(Q132.4)给 $\limsup B_n\le1$。原锥上的非负性与 $\max_Kf_n\le1$ 经同一个 $u$ 齐次化给 $0\le f_n\le u$ 于全部 $C$。又有

$$
\|f_n-b_n\|_K=(B_n-1)_+\longrightarrow0.
\tag{Q132.7}
$$

这同时给整个 $F$ 上的收敛；$\max_F\ell=1$ 时由 $m_n\le B_n$ 得 $B_n\to1$。证毕。

**引理 132.3（单标签球内的混极限迫使整球缩向标签）。** 另设 $I(F)=\{p\}$。若 $y\in\operatorname{ri}F$、$r_n\in P$、$r_n\to y$，则

$$
\max_{x\in D_{r_n}}\|x-p\|\longrightarrow0.
\tag{Q132.8}
$$

证明。每个球面邻点 $a\in S(F)$ 的排除球亦单标签，直接复用[single_label_neighbor][Q132SN]，包括 $k=1$ 的线段情形。任取 $x_n\in D_{r_n}$ 的收敛子列 $x_n\to x$，并从完整 $\mathcal A_{r_n}$ 取同一效应子列 $e_n\to e\in\mathcal E$。有 $e(y)=1$、$e(x)=0$。因 $u-e\ge0$ 于 $K$ 且 $y\in\operatorname{ri}F$，有 $e|_F=1$，故 $x\in D_a$ 对每个 $a\in S(F)$ 成立。

选两个不同 $a,a'\in S(F)$。它们的单标签性给 $D_a\ne D_{a'}$；原零对称又给 $p\in D_a\cap D_{a'}$。[原真面分类及整球交点性质][Q132BF]使该交集恰为 $\{p\}$，所以 $x=p$。紧性反证把所有选择的这一聚点结论升级为(Q132.8)。没有对混极限 $y$ 使用需要全局Inj的标签判据。证毕。

**定理 132.4（有限共同源测试的正锥距离下界或维数上升）。** 在定义132.1的原域中，设 $I(F)=\{p\}$ 并固定 $y\in\operatorname{ri}F$。存在有限多个原纯点 $a_1,\ldots,a_m\in S(F)$、固定原完整零确认 $h_i\in\mathcal A_{a_i}$ 及 $\varepsilon,\delta>0$，使对每个

$$
r\in P,\quad \|r-y\|<\varepsilon,\qquad
t\in P\cap D_r
\tag{Q132.9}
$$

至少一项成立：

$$
\dim\operatorname{aff}D_t\ge k+1,
\qquad\text{或}\qquad
\max_{1\le i\le m}R_F(t,h_i)\ge\delta.
\tag{Q132.10}
$$

这些 $a_i,h_i,\varepsilon,\delta$ 先于所有 $r,t$ 选择。还对每个 $\tau>0$ 存在 $\varepsilon_\tau>0$，使(Q132.9)中的 $\varepsilon$ 换成 $\varepsilon_\tau$ 后，全部 $h_i(t)\le\tau$ 同时成立。因此，若存在趋近 $y$ 的原纯列并沿第二分支选取返回标签，原输入上的全部读数趋零，而任意大小的正延拓在固定原整球上的误差仍有共同正下界；本条不先断言这种纯列存在。

证明。先在 $S(F)$ 选一个有限集，使

$$
y\in\operatorname{ri}\operatorname{conv}\{a_1,\ldots,a_m\},\qquad
\operatorname{aff}\{a_1,\ldots,a_m\}=\operatorname{aff}F.
\tag{Q132.11}
$$

存在性只用球几何：在固定球图中取以球心指向 $y$ 为第一轴的正交轴及其正负端点；球心时任选第一轴。$y$ 的轴坐标绝对值严格小于一，故在这些端点凸包的相对内部。各 $D_{a_i}$ 单标签，由引理132.3引用的邻点传播取得。选任意 $h_i\in\mathcal A_{a_i}$。其整个原一值面恰为 $\{a_i\}$：任一纯一值点 $v$ 给 $D_{a_i}\subseteq D_v$，极大性给相等，局部单标签性迫 $v=a_i$；紧一值面由其极点凸生成，故也不含其他混态。原零对称给 $p\in D_{a_i}$，所以 $h_i(p)=0$。

反设没有(Q132.10)的统一 $\varepsilon,\delta$。可选同一列 $r_n\to y$、$t_n\in P\cap D_{r_n}$，使

$$
\dim\operatorname{aff}D_{t_n}\le k,\qquad
\max_iR_F(t_n,h_i)<1/n.
\tag{Q132.12}
$$

对每个 $i,n$ 从下确界选 $b_{i,n}\in N_{t_n}$，使 $\|b_{i,n}-h_i\|_F<2/n$；不要求下确界达到。引理132.3给 $t_n\to p$。命题132.2在同一个 $F$、同一个 $t_n$ 上将全部这些正泛函归一为 $f_{i,n}\in\mathcal E$，并给

$$
B_{i,n}:=\max_K b_{i,n}\to1,\qquad
f_{i,n}|_F\longrightarrow h_i|_F.
\tag{Q132.13}
$$

对充分大的 $n$，选原纯最大点 $x_{i,n}\in D_{t_n}$，使 $b_{i,n}(x_{i,n})=B_{i,n}$；存在性复用[positive_annihilator_maximum][Q132SN]。上关联使这些点的聚点在 $F$。(Q132.13)、全效应的统一有界性及 $f_{i,n}(x_{i,n})\to1$，使每个这样的聚点满足 $h_i(x)=1$，因而为 $a_i$。所以 $x_{i,n}\to a_i$，所有有限测试共享同一个返回球序列 $D_{t_n}$。

由(Q132.12)取一个子列使 $d:=\dim\operatorname{aff}D_{t_n}$ 恒定，$1\le d\le k$。在辅助欧氏尺中写 $D_{t_n}=c_n+L_n\overline B^d$，其中 $L_n$ 的列为正交半轴向量。紧 $K$ 使这些中心、半轴一致有界；再取同一个子列使 $c_n\to c$、$L_n\to L$。于是

$$
D_{t_n}\longrightarrow H=c+L\overline B^d\subseteq F.
\tag{Q132.14}
$$

包含关系只用纯标签 $t_n\to p$ 的上关联。各 $x_{i,n}\to a_i$ 使 $a_i\in H$，(Q132.11)遂给 $\dim\operatorname{aff}H=k$。因 $\operatorname{rank}L\le d\le k$，必有 $d=k$ 且 $L$ 单射。

原零对称给 $r_n\in P\cap D_{t_n}$，即 $r_n=c_n+L_nv_n$、$\|v_n\|=1$。在该子列再取 $v_n\to v$，得 $\|v\|=1$、$y=c+Lv\in\partial_{\rm rel}H$。另一方面(Q132.11)及 $\operatorname{conv}\{a_i\}\subseteq H\subseteq F$ 给 $y\in\operatorname{ri}H$，矛盾。这里单射性是在维数比较后取得；没有把降秩图的球面极限误作像球的相对球面。

最后，若 $r_n\to y$、$t_n\in P\cap D_{r_n}$，引理132.3给 $t_n\to p$，故有限族的全部 $h_i(t_n)\to0$。若所述 $\varepsilon_\tau$ 不存在，选违反它的 $1/n$ 邻近序列便矛盾。这证明全部量词的统一性。证毕。

**约定 132.5（与指定坏见证的局部纯极限问题对应）。** 对[131.1][Q132SR]任意指定的坏对径 $q,\bar q$ 及 $y=(3q+\bar q)/4$，本章未断言 $\mathsf{LP}_{p,y}$。若 $I(F)=\{p\}$ 且有反向的原纯列，定理132.4给同一原返回关系上的精确义务：排除实际高维返回球，并排除固定有限族在全部正锥延拓中的源误差下界。所有原球维数都是正整数且不超过 $\dim\ker u$，故最大维数存在；只有当指定 $F$ 本身达到该值时，(Q132.10)的维数上升分支才被去掉，源误差下界仍未由EB消除。这里没有把任意指定 $F$ 换成最大维数球。重复球分支亦未由本章结算。不得将这些缺项作为已经支付的前提。

沿此有限测试路线，一个足够的共同选择目标是：从假想 $r_n\to y$ 选同一列 $t_n\in P\cap D_{r_n}$，同时有 $\dim\operatorname{aff}D_{t_n}\le k$ 及 $\max_iR_F(t_n,h_i)\to0$。定理132.4排除这组共同条件；从EB产生它们尚未证明。每个测试分别在不同返回标签上可修复，不供应这个同标签目标；此目标也未被声明为LP的必要条件或等价表述。

命题132.2在定理132.4的活推导中支付的是共同原单位：若所需正提升精确零于同一个移动标签，且在固定整个 $F$ 上有给定的有界读数，那么无须再另求一项渐近单位预算。全锥正提升的存在性仍未证明。仅有逐点小读数、无正性延拓、不同来源的局部最大值或抽象球图，均不满足这一前件。本章没有证明原域局部混合映射开放，也没有给完整EB反模型。

本章数学归属为 `repo-derived`：原面分类、单标签传播、正零泛函最大值及纯标签上关联均按下面的原声明复用；新增组合是移动标签的统一单位控制，以及在同一返回球上、预先固定有限族、以整个固定源球半范数衡量且允许无界正泛函的统一障碍。没有全球原创或历史优先权断言。固定三球加全局Inj的[fixed_zero_distance_obstruction][Q132FZ]保留其原假设与结论；它的整个 $K$ 效应距离结论未被当作本章较弱原域、较强正锥源距离结论的前置。

[Q132SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "131.1—131.3：全部原态、效应、变维EB与指定坏见证；131.2的闭包等价保持原样。"
[Q132IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "116.2：重复块与单标签二分；118.3的(IX118.4)：不需Inj的纯标签上关联。"
[Q132SN]: ../../../D5/S3/Quantum/Foundation/SingleLabelNormalBody.lean "single_label_neighbor；positive_annihilator_maximum；既有固定标签 normal_body_bound 不包含移动标签的(Q132.4)。"
[Q132BF]: ../../../D5/S3/Quantum/Foundation/ExclusionBallFaces.lean "exclusion_ball_faces：仅EB的全部原真面分类；不同完整球的交点性质亦见 SingleLabelNormalBody.equal_of_two_points。"
[Q132FZ]: ../../../D5/S3/Quantum/Foundation/FixedZeroObstruction.lean "fixed_zero_distance_bound 只比较整个K上的完整效应误差；fixed_tests_of_proper_limit 与 fixed_zero_distance_obstruction 的Inj、固定维数前件不用于本章。"

## 追加锚（本行以下为增补区）

## 133. 同一返回球的正法向扇区与消失轴质量

**定义 133.1（原返回、源方向与漏出量）。** 沿用定义132.1的全部原域及 $\mathrm{EB}_{\ge1}$，固定任意 $F=D_p$、$k=\dim\operatorname{aff}F\ge1$ 和 $y\in\operatorname{ri}F$。在 $V$ 上固定辅助欧氏内积，所有距离、算子范数和奇异值均相对于它及参数空间的标准欧氏内积。固定一个单射球图

$$
F=c_F+T_F\overline B^k,\qquad
y=c_F+T_F\xi,\qquad \|\xi\|<1.
\tag{Q133.1}
$$

选单位向量 $v_0,\ldots,v_k\in\mathbb R^k$，使 $a_i=c_F+T_Fv_i$ 仿射无关且 $y$ 在其单纯形的相对内部。这样的选择总存在：取球心在零的正则单纯形；当 $\xi\ne0$ 时将一个顶点旋转至 $\xi/\|\xi\|$，则 $\xi$ 在从零至该顶点的开线段中；$\xi=0$ 时不需旋转。$k=1$ 时使用两个端点。这些 $a_i$ 是固定源球的接触点，不要求它们同属一个原可区别框架。

对每个 $b\in C^*\setminus\{0\}$，记

$$
M(b)=\max_K b>0,\qquad
b(c_F+T_Fz)=b(c_F)+\langle g_b,z\rangle
\quad(z\in\mathbb R^k).
\tag{Q133.2}
$$

仅在 $g_b\ne0$ 时定义 $w_b=g_b/\|g_b\|$。对一个实际原返回

$$
r\in P,\qquad t\in P\cap D_r,
\qquad E_t=D_t,
\tag{Q133.3}
$$

置

$$
\alpha_F(t)=\max_{x\in E_t}\operatorname{dist}(x,F).
\tag{Q133.4}
$$

全部候选 $b\in N_t$ 均在同一个整个原锥 $C$ 上非负，且精确满足 $b(t)=0$。特别地，$b$ 并非仅在 $F$ 上非负的仿射函数。$M(b)$ 不预先有单位上界；$\|g_b\|/M(b)$ 是不依赖正倍数的源对比度。以下只使用原零对称、完整零确认、极大真面及球面纯性这些[既有原面接口][Q133BF]，不假设标签单点、Inj、闭 $P$、Pair或共同球维数。

**定理 133.2（低维返回的统一方向扇区界）。** 对定义133.1的固定数据，存在 $\varepsilon,\theta,H>0$，先于所有 $r,t,b$ 选择，使每个满足(Q133.3)及 $\|r-y\|<\varepsilon$ 的实际返回，若

$$
\dim\operatorname{aff}E_t\le k,
\tag{Q133.5}
$$

则存在一个 $i\in\{0,\ldots,k\}$，使对所有 $b\in N_t\setminus\{0\}$ 同时有

$$
g_b\ne0,\quad \|w_b-v_i\|<\theta
\quad\Longrightarrow\quad
\|g_b\|\le H M(b)\alpha_F(t).
\tag{Q133.6}
$$

指标 $i$ 可以依赖 $r,t$，但不能再依赖该扇区内所测试的 $b$。

证明。先给所有实际返回共用的单侧收敛：

$$
\lim_{\rho\downarrow0}
\sup_{\substack{r\in P,\ \|r-y\|<\rho\\t\in P\cap D_r}}
\alpha_F(t)=0,
\tag{Q133.7}
$$

其中空集的上确界取零。若不成立，取 $r_n\to y$、$t_n\in P\cap D_{r_n}$ 及 $x_n\in D_{t_n}$，使 $\operatorname{dist}(x_n,F)$ 有统一正下界。选 $e_n\in\mathcal A_{t_n}$。原零对称给 $r_n\in D_{t_n}$，所以

$$
e_n(r_n)=e_n(x_n)=0,\qquad e_n(t_n)=1.
$$

紧 $K,\mathcal E$ 给共同收敛子列 $x_n\to x$、$t_n\to t$、$e_n\to e$，满足 $e(y)=e(x)=0$、$e(t)=1$。$e$ 的零面是真面；它包含 $y\in\operatorname{ri}F$，因而包含整个 $F$。$F$ 是极大真面，故该零面恰为 $F$，于是 $x\in F$，矛盾。这是[126.8][Q133SR]同面紧性机制在任意源球及变维实际返回上的应用；它不辨认 $t$ 的极限标签，也不要求该极限纯。命题132.2的原单位估计因此亦适用于这里的全部返回，但以下直接使用同一最大值前置。

取(Q132.2)在当前欧氏尺中的 $A>0$。固定非零 $b\in N_t$ 且 $g_b\ne0$，写 $s=\|g_b\|$、$w=w_b$、$B=M(b)$、$\alpha=\alpha_F(t)$。[positive_annihilator_maximum][Q133SN]供应同一 $E_t$ 中的原纯最大点 $x$，满足 $b(x)=B$。取最近 $z=c_F+T_Fq\in F$，$\|q\|\le1$。因为 $F\subseteq K$，有 $\max_Fb=b(c_F)+s\le B$，从而

$$
\begin{aligned}
s(1-\langle w,q\rangle)
&\le B-b(z)=b(x-z)\le AB\alpha,\\
\|q-w\|^2
&\le2(1-\langle w,q\rangle).
\end{aligned}
\tag{Q133.8}
$$

记 $T_0=\|T_F\|>0$，得到每个源方向的接触估计

$$
\|x-a_i\|
\le\alpha+T_0\left(\sqrt{\frac{2AB\alpha}{s}}+\|w-v_i\|\right).
\tag{Q133.9}
$$

这个估计对 $b$ 正齐次；没有把原正泛函替换成局部函数。

固定足够小的 $\delta>0$，使下列两项单纯形稳定性同时成立。若 $x_i$ 距 $a_i$ 小于 $\delta$、$r$ 距 $y$ 小于 $\delta$，且 $x_0,\ldots,x_k,r$ 同在某个维数至多 $k$ 的仿射空间，则 $x_i$ 仿射无关、张成该空间，且 $r$ 是其单纯形的严格正重心组合。另存在固定 $\beta>0$，使只要 $x_i\in\operatorname{aff}F$ 且 $\|x_i-a_i\|\le\delta$，就有

$$
\overline B_{\operatorname{aff}F}(y,\beta)
\subseteq\operatorname{conv}\{x_0,\ldots,x_k\}.
\tag{Q133.10}
$$

两项都由非退化单纯形的稳定性取得：令以 $a_i-a_0$ 为列的矩阵为 $D$，它的最小奇异值严格正；扰动后的列矩阵仍满列秩，其左逆连续。在第一项中，$r$ 属于同一仿射空间，所以用该左逆计算的重心坐标确实重构 $r$，并仍为正。第二项先取一个以 $y$ 为中心、闭包包含于原单纯形内部的小球，再将扰动取到使该紧球上的所有重心坐标仍严格正。收小 $\delta$ 即同时保证两项。

选 $\theta,H>0$ 使

$$
T_0\theta<\delta/4,\qquad
T_0\sqrt{2A/H}<\delta/4.
\tag{Q133.11}
$$

再由(Q133.7)选 $0<\varepsilon<\delta$，使全部 $\varepsilon$-邻近实际返回的 $\alpha<\delta/4$。若(Q133.6)在每个扇区都失败，就能对同一个 $r,t$ 为每个 $i$ 选取一个 $b_i\in N_t\setminus\{0\}$，满足

$$
\|w_{b_i}-v_i\|<\theta,\qquad
\|g_{b_i}\|>H M(b_i)\alpha.
\tag{Q133.12}
$$

由(Q133.9)选得同一 $E_t$ 中的纯最大点 $x_i$，均距 $a_i$ 小于 $3\delta/4$。若 $\alpha=0$，(Q133.8)直接给 $q=w$，同一估计仍成立。由(Q133.5)和单纯形稳定性，$r$ 是这些仿射无关 $x_i$ 的严格正组合。因为 $k\ge1$，这与 $r$ 为 $K$ 的极点矛盾。证毕。

**定理 133.3（越过全部扇区界的返回必须在消失轴上带质量）。** 保留定理133.2所选的固定方向及常数。设

$$
r_n\in P,\quad r_n\to y,\qquad
t_n\in P\cap D_{r_n},\qquad
E_n=D_{t_n},\quad \alpha_n=\alpha_F(t_n).
\tag{Q133.13}
$$

另假设对充分大的每个 $n$ 和每个 $0\le i\le k$，存在 $b_{i,n}\in N_{t_n}\setminus\{0\}$，满足

$$
g_{b_{i,n}}\ne0,\qquad
\|w_{b_{i,n}}-v_i\|<\theta,\qquad
\|g_{b_{i,n}}\|>H M(b_{i,n})\alpha_n.
\tag{Q133.14}
$$

所有 $i$ 共享同一个实际返回标签 $t_n$。不要求这些正泛函趋于预先给定的非恒定源函数；其归一化源对比度允许趋零。

写任一单射球图为

$$
E_n=c_n+L_n\overline B^{d_n},\qquad
r_n=c_n+L_nz_n,\quad \|z_n\|=1,
\tag{Q133.15}
$$

其中单位球面参数的存在由原零对称及 $S(E_n)=P\cap E_n$ 给出。将奇异值按降序排列。则 $\alpha_n\to0$，且最终 $d_n\ge k+1$；存在只依赖固定源数据和 $K$ 的 $s_*>0$、$\eta>0$，使

$$
\liminf_n\sigma_k(L_n)\ge s_* ,\qquad
\sigma_{k+1}(L_n)\le\alpha_n
\quad\text{于充分大的 }n.
\tag{Q133.16}
$$

令 $W_n\subset\mathbb R^{d_n}$ 为后 $d_n-k$ 个右奇异方向张成的空间，则还有

$$
\liminf_n\|\operatorname{proj}_{W_n}z_n\|^2\ge\eta.
\tag{Q133.17}
$$

证明。(Q133.7)给 $\alpha_n\to0$，定理133.2排除充分大 $n$ 的 $d_n\le k$。(Q133.9)—(Q133.14)给同一个 $E_n$ 内的接触点 $x_{i,n}$，满足 $\|x_{i,n}-a_i\|<3\delta/4$。

设 $R=\operatorname{diam}K/2>0$。每个中心 $c_n\in K$，且 $\|L_n\|\le R$，因为任一对径端点 $c_n\pm L_nv$ 都在 $K$。实际正整数 $d_n\le\dim\ker u$，故从任何子列都可再取 $d_n=d$ 恒定的子列；再由有界性取

$$
c_n\to c,\quad L_n\to L,\quad z_n\to z,\qquad
E_n\longrightarrow H_0=c+L\overline B^d.
\tag{Q133.18}
$$

这里 $\|z\|=1$、$Lz=y-c$，而 $\alpha_n\to0$ 给 $H_0\subseteq F$。同时取有限族 $x_{i,n}\to x_i\in H_0$，由(Q133.10)有

$$
\overline B_{\operatorname{aff}F}(y,\beta)\subseteq H_0\subseteq F.
\tag{Q133.19}
$$

所以 $\operatorname{rank}L=k$。还可取 $\sigma_k(L)\ge\beta$：在 $\operatorname{aff}F$ 的每个单位方向上，(Q133.19)给 $H_0$ 的宽度至少 $2\beta$；该椭球在方向 $v$ 上的宽度等于 $2\|L^*v\|$。奇异值连续性及“任意子列再取子列”遂给 $\liminf\sigma_k(L_n)\ge\beta$，可取 $s_*=\beta$。这个论证保留变维，只在有限维环境允许的子列上固定实际维数。

记 $Q$ 为到 $\operatorname{span}(F-F)^\perp$ 的正交投影。对每个单位参数 $v$，两个端点距 $\operatorname{aff}F$ 均不超过 $\alpha_n$，即

$$
\|Q(c_n-c_F\pm L_nv)\|\le\alpha_n.
$$

相减得 $\|QL_n\|\le\alpha_n$，而 $(I-Q)L_n$ 的秩至多 $k$。取 $L_n$ 的前 $k+1$ 个右奇异方向所张成的空间，该空间中有单位 $v$ 满足 $(I-Q)L_nv=0$；于是

$$
\sigma_{k+1}(L_n)\le\|L_nv\|=\|QL_nv\|\le\alpha_n.
\tag{Q133.20}
$$

这只是标准[SVD][Q133BV]的维数论应用，作为实际返回的估计步骤使用。

最后收小 $\beta$ 使 $0<\beta<R$，此时(Q133.19)仍成立。对(Q133.18)的任一共同极限，令 $w\in(\ker L)^\perp$ 是 $Lw=y-c$ 的最小范数解。由 $y\in H_0$ 有 $a:=\|w\|\le1$。若 $a>0$，则 $c+L(w/a)$ 在 $H_0$ 的相对边界，且

$$
\beta\le\|c+L(w/a)-y\|
=(1-a)\|L(w/a)\|\le R(1-a).
\tag{Q133.21}
$$

故 $\|w\|\le1-\beta/R$；$a=0$ 时同一上界成立。又 $z-w\in\ker L$ 且 $w\perp\ker L$，所以

$$
\|\operatorname{proj}_{\ker L}z\|^2
=1-\|w\|^2
\ge1-(1-\beta/R)^2=:\eta>0.
\tag{Q133.22}
$$

为把这个极限结论传回 $W_n$，在当前定维子列上为 $L_n^*L_n$ 选正交特征标架并再取收敛子列。前 $k$ 个特征值有统一正下界，后 $d-k$ 个趋零；极限的后 $d-k$ 个特征向量因而恰张成 $\ker L$，对应正交投影收敛。(Q133.22)遂给该子列上(Q133.17)的下界。若原列的下极限更小，取违反下界的子列再作上述提取便矛盾。证毕。

**定义 133.4（方向条件与局部纯极限的区分）。** (Q133.14)称为沿给定实际返回列的共同方向条件；它是额外前件，不是 $\mathrm{EB}_{\ge1}$ 的已得结论。定理133.2无此额外前件，量化的是一个扇区内的全部原正零泛函。定理133.3在该前件下限制实际高维返回的内禀坐标，未把高维返回删去。特别地，物理轴长趋零不能推出它的单位球参数趋零。

两定理均允许重复标签纤维 $I(F)$，并适用于[131.1][Q133SR]的指定坏对径内点 $y$；没有从这些条件推出 $\mathsf{LP}_{p,y}$、共同正提升的存在性或完整原域反模型。源点在 $\overline P$ 之外也不是前件或结论。固定源测试的共同提升与本章共同方向条件之间，不附加等价断言。

[Q133BF]: ../../../D5/S3/Quantum/Foundation/ExclusionBallFaces.lean "exclusion_ball_faces 的前两项：完整暴露真面与全部真面分类；极大性及球面纯性亦见 IX116.1。"
[Q133SN]: ../../../D5/S3/Quantum/Foundation/SingleLabelNormalBody.lean "positive_annihilator_maximum：对整个原锥正泛函给同一 D_t 内的原纯全局最大点，不需 SingleLabel 或 EB。"
[Q133SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "126.8：裸EB3重复球内点附近的整球单侧收敛；126.11—126.12：零于靠近源内点的原效应之平坦化与最大面集中；131.1—131.3：原坏见证及仍待证的局部纯极限。"
[Q133BV]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf "Boyd and Vandenberghe, Convex Optimization, Appendix A.5.4, pp.648–649：SVD、右奇异方向及最小范数逆；这些标准线性代数仅为证明中间步骤。"

## 追加锚（本行以下为增补区）
