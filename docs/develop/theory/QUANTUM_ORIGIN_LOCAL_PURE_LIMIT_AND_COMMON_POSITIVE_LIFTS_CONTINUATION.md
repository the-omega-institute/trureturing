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
