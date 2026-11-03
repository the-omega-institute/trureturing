# AURIC：复合比较有限带噪报告的 V96 续篇

## 1. 原有限报告的合同与参数对应

**定义 1.1（原卷与同一实际报告域）。** 称[《复合比较的有限变化见证、共同标定与量子生成》V96](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md)为原卷。本卷续接其 C98 实际报告的定量问题；无“原卷”限定的编号属于本卷。两个局部场、实际运算及有限报告均取同一个实现，具体对应为：

| 本卷使用的对象或标签 | 原卷定义与对应 |
| --- | --- |
| $J_A,J_B,S_J,g_J,1_J,D^J,B_J$ | [原卷定义 8.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#8-一般正比较场与不含外部标尺的候选)：有限非零实空间、交换含幺正 Frobenius 比较及非零实线性比较导子指派，$B_J(a,c)=D^J_ac$；不预设交替、Jacobi 或 $D_1=0$。 |
| $M,T,\kappa,\beta$ 与报告范数 | [原卷定义 14.1、原卷命题 14.2 及式 (14.1)–(14.3)](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#14-从局部关系通道到实际联合运算)：同一实际四通道运算、两个单位嵌入及其唯一实际系数；联合内积明确取 $g_A\otimes g_B$。 |
| $e_i,\mathcal P_J,(b,d),\Pi_J^{\rm self},\Pi_J^{\rm mix}$ | [原卷定义 8.3 与式 (8.2)](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#8-一般正比较场与不含外部标尺的候选)：原完整有序正交单位基、基向量与归一两两和、固定有序活动参照 $B(b,d)\ne0$，自身标签交换参照槽，混合标签为 $i<j,k$。 |
| $R,S_p,R_{ijk},\Theta$ | [原卷定义 16.2、原卷引理 16.3 及式 (16.2)–(16.4)](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#16-实际有限残差选择联合模板)：$S_p,R_{ijk}$ 分别是上列原自身、混合标签处的实际 $R$；$\Theta$ 按 $\Pi_A\sqcup\Pi_B$ 的全部标签出现次数求平方和，第二方仅作张量翻转，保留同一 $M,T,\kappa,\beta$。 |
| 自身收缩与已交替估计的区别 | [原卷式 (16.6)](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#16-实际有限残差选择联合模板)及[原卷定理 17.2–17.3](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#17-局部盲核联合诊断与条件误差界)：复用前者的精确收缩及原卷定理 17.2 的逐点界；原卷定理 17.3 的双方已交替前件不属于本卷输入。 |

本卷不要求零条件 C98。$n_J$ 包括单位方向，标签的基顺序和参照方向均保留；不从 $B(b,d)\ne0$ 推出 $B(d,b)\ne0$。正的活动、系数和结构范数界均只按下文逐条明列的条件使用。原卷定义 8.4 的投影报告向量 $Q$ 与本卷定义 2.1 的非负标量 $Q$ 不同。

## 2. 交替前的有限实际报告与条件定量证书

**定义 2.1（原报告、单位读出与条件量）。** 保留原卷定义 8.1、8.3、14.1、16.2 的全部前件、实际运算 $M,T$ 和同一个带标签有限族，不要求 C98、局部交替、$D_1=0$ 或 Jacobi。对其中一方 $J$，记 $n=\dim J$，使用原来的完整正交单位基 $e_1,\ldots,e_n$、原来的归一两两和族 $\mathcal P_J$，以及另一方的原有序参照 $(b,d)$。以下量均属于这同一实际实现：

$$
\begin{aligned}
v&=B(b,d),& w&=B(d,b),& r&=\|v\|>0,& u&=\|1_J\|>0,\\
z_{ij}&=B(e_i,e_j),&K_{ij}&=[L_{e_i},L_{e_j}],&
C_z(c)&=B(c,z)\qquad(i<j).
\end{aligned}
\tag{2.1}
$$

$B$ 在参照槽中属于伙伴场，在 $z_{ij},C_z$ 中属于 $J$。两方的系数始终是原卷命题 14.2 中同一对实际 $\kappa,\beta$。特别地，不把 $w$ 替换成 $-v$，不把 $C_z$ 替换成 $-D_z$。记实际报告及其未平均范数为

$$
\begin{aligned}
R_{ijk}&=R(e_i\otimes b,e_k\otimes d,e_j\otimes1),\\
S_p&=R(p\otimes d,p\otimes b,p\otimes1),\\
m^2&=\sum_{i<j,k}\|R_{ijk}\|^2,&
\varepsilon_{\rm self}&=\max_{p\in\mathcal P_J}\|S_p\|,\\
Z^2&=\sum_{i<j}\|z_{ij}\|^2,&
A^2&=\sum_{i<j}\|K_{ij}\|_{\rm HS}^2,\\
h^2&=\sum_{i<j}\|L_{z_{ij}}\|_{\rm HS}^2,&
Q&=\|w\|\left(\sum_{i<j}\|C_{z_{ij}}\|_{\rm HS}^2\right)^{1/2}.
\end{aligned}
\tag{2.2}
$$

Hilbert–Schmidt 范数使用 $g_J$，报告范数使用原来的乘积内积。$m,Z,A,h,Q$ 均取非负平方根；此处 $Q$ 是标量条件量，不是原卷定义 8.4 的报告向量。$C_z$ 一般不是斜伴算子。单位中间输入的读出定义为

$$
U_{ij}=\sum_{k=1}^n g_J(1_J,e_k)R_{ijk}
=R(e_i\otimes b,1_J\otimes d,e_j\otimes1).
\tag{2.3}
$$

等号只使用残差的三线性；$U_{ij}$ 是已有混合报告的线性读出，不添加探针，也不改变原有限族。

报告在这里是给定 $M,T$ 的实际残差；其误差大小指这些向量非零。若另给观测向量 $\widehat R_{ijk},\widehat S_p$ 及确定的误差包络

$$
\|R_{ijk}-\widehat R_{ijk}\|\le\eta_{ijk},\qquad
\|S_p-\widehat S_p\|\le\xi_p,
\qquad \eta_{ijk},\xi_p\ge0,
$$

可使用

$$
\overline m=
\left(\sum_{i<j,k}\|\widehat R_{ijk}\|^2\right)^{1/2}
+\left(\sum_{i<j,k}\eta_{ijk}^2\right)^{1/2},
\qquad
\overline\varepsilon_{\rm self}
=\max_{p\in\mathcal P_J}(\|\widehat S_p\|+\xi_p)
\tag{2.4}
$$

作为 $m,\varepsilon_{\rm self}$ 的上界。也允许任意其他已证上界；无观测误差时取上界等于实际量。下列式子的 $r,u,Z,A,h,Q$ 仍是 (2.1)–(2.2) 的结构量；若这些量本身也只有区间信息，数值代入须分别使用所需方向的有效界，不能从残差小自动取得结构量的下界。

**定理 2.2（交替前的单位矩与非零系数证书）。** 在定义 2.1 下，有精确恒等式

$$
\boxed{\sum_{i<j}\langle U_{ij},z_{ij}\otimes v\rangle
=\beta r^2Z^2,}
\tag{2.5}
$$

以及精确正交分解和有限报告上界

$$
\boxed{\sum_{i<j}\|U_{ij}\|^2
=\beta^2r^2Z^2
+\kappa^2\|w\|^2\sum_{i<j}\|D_1z_{ij}\|^2
\le u^2m^2.}
\tag{2.6}
$$

所以当 $Z>0$ 时，同一实际系数满足

$$
\boxed{|\beta|\le\frac{u m}{rZ}.}
\tag{2.7}
$$

完整混合族还给出

$$
\boxed{m+|\kappa|Q\ge r\sqrt{A^2+\beta^2h^2}\ge rA.}
\tag{2.8}
$$

若 $A>0$ 且 $m<rA$，则 $Q>0,Z>0,\kappa\ne0$，并有

$$
\boxed{|\kappa|\ge\frac{rA-m}{Q}>0.}
\tag{2.9}
$$

特别地，若已证上界 $\overline m<rA$，则

$$
\mu_{\rm cert}=\frac{rA-\overline m}{Q}
\quad\text{满足}\quad 0<\mu_{\rm cert}\le|\kappa|.
\tag{2.10}
$$

这是充分阈值；未通过该阈值不判定 $\kappa=0$，也不否定其他条件证书。

证明。只复用原卷定义 8.1 所具有的斜伴随性，即[比较曲率 V95，定理 2.1 第一项](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md)。特别地，$D_1$ 斜伴；这不等于 $D_1=0$。原卷引理 16.3 在全部当前输入上给

$$
R_{ijk}=(K_{ij}+\beta L_{z_{ij}})e_k\otimes v
-\kappa C_{z_{ij}}e_k\otimes w.
\tag{2.11}
$$

由于 $L_a1=a$ 及 $S$ 交换，$K_{ij}1=0$；又 $L_z1=z$、$C_z1=B(1,z)=D_1z$。因此

$$
U_{ij}=\beta z_{ij}\otimes v-\kappa D_1z_{ij}\otimes w.
\tag{2.12}
$$

斜伴随性使 $g_J(z_{ij},D_1z_{ij})=0$，即使 $v,w$ 不正交，(2.12) 的两项仍正交。与 $z_{ij}\otimes v$ 配对并求和得到 (2.5)，取范数平方并求和得到 (2.6) 的等式。对 (2.3) 逐对使用 Cauchy–Schwarz 不等式，得到

$$
\|U_{ij}\|^2\le
\left(\sum_k g_J(1,e_k)^2\right)\sum_k\|R_{ijk}\|^2
=u^2\sum_k\|R_{ijk}\|^2.
$$

求和得到 (2.6) 的不等式；$Z>0$ 时可以除以 $rZ$，得到 (2.7)。这一步没有用 $B$ 的交替性。

在以 $(i,j,k)$ 为标签的正交直和中，把 (2.11) 的第一项族记为 $E$，把 $C_{z_{ij}}e_k\otimes w$ 的族记为 $F$。于是 $R_{\rm mix}=E-\kappa F$ 且 $\|F\|=Q$。Frobenius 性使每个 $L_z$ 自伴，$K_{ij}$ 是两个自伴算子的交换子，因而斜伴。实自伴与实斜伴算子在 Hilbert–Schmidt 内积下正交，所以

$$
\|E\|^2=r^2\sum_{i<j}\|K_{ij}+\beta L_{z_{ij}}\|_{\rm HS}^2
=r^2(A^2+\beta^2h^2).
$$

三角不等式 $\|E\|\le\|R_{\rm mix}\|+|\kappa|\|F\|$ 给出 (2.8)。若 $m<rA$，则 $|\kappa|Q\ge rA-m>0$，故 $\kappa\ne0,Q>0$。由 $Q>0$ 可知某个 $C_{z_{ij}}\ne0$，从而某个 $z_{ij}\ne0$，所以 $Z>0$。现在除以正的 $Q$ 得 (2.9)；再用 $m\le\overline m$ 得 (2.10)。式 (2.4) 的上界分别来自直和中的三角不等式和逐报告三角不等式。∎

**定理 2.3（原有限自身样本控制全局对称缺陷）。** 在定义 2.1 下，给任意已经证成的数 $\mu$ 满足 $0<\mu\le|\kappa|$。它可以是 (2.10)，也可以来自其他独立的系数条件。令

$$
d_0=\sqrt{\frac{\overline\varepsilon_{\rm self}}{\mu r}},
\qquad \Delta=(2n-1)d_0.
\tag{2.13}
$$

则对全部 $x,a,c\in J$，

$$
\boxed{\|D_xx\|\le\Delta\|x\|^2,\qquad
\|B(a,c)+B(c,a)\|\le2\Delta\|a\|\|c\|.}
\tag{2.14}
$$

特别地，$\sup_{\|x\|=1}\|D_xx\|\le\Delta$，并有 $\|D_1\|_{\rm op}\le2u\Delta$。若使用混合报告阈值 $\overline m<rA$，这些结论可直接取

$$
\boxed{\Delta=(2n-1)
\sqrt{\frac{\overline\varepsilon_{\rm self}Q}
{r(rA-\overline m)}}.}
\tag{2.15}
$$

这里 $\overline\varepsilon_{\rm self}$ 是残差范数的上界，不是残差范数平方。若只给 C98 的总平方和上界 $\Theta(M,T)\le\theta$，则 $m\le\sqrt\theta$、$\varepsilon_{\rm self}\le\sqrt\theta$；在另已证 $0<\mu\le|\kappa|$ 时，可取 $\Delta=(2n-1)\theta^{1/4}/\sqrt{\mu r}$。两方各自满足所需条件时，分别以其自身的维数和伙伴活动量应用本定理。

证明。令 $q(x)=B(x,x)$。原卷式 (16.6) 由立方零矩消去 $\beta$，在残差不为零时仍给

$$
(g_J(p,\cdot)\otimes I)S_p
=\kappa\|q(p)\|^2v.
$$

每个规定的 $p\in\mathcal P_J$ 都是单位向量，故收缩算子范数为一，并有

$$
|\kappa|r\|q(p)\|^2\le\|S_p\|
\le\overline\varepsilon_{\rm self},
\qquad \|q(p)\|\le d_0.
\tag{2.16}
$$

这只是原卷定理 17.2 的逐点估计；全局结论还需使用原有限族的极化信息。对 $p_{ij}=(e_i+e_j)/\sqrt2$，双线性给

$$
B(e_i,e_j)+B(e_j,e_i)=2q(p_{ij})-q(e_i)-q(e_j),
$$

所以其范数至多为 $4d_0$。写 $x=\sum_i x_ie_i$，逐项展开而不假设交替，得到

$$
\begin{aligned}
\|q(x)\|
&\le d_0\sum_i x_i^2+4d_0\sum_{i<j}|x_ix_j|\\
&\le d_0\bigl(1+2(n-1)\bigr)\sum_i x_i^2
=\Delta\|x\|^2.
\end{aligned}
$$

第二个不等式由 $2|x_ix_j|\le x_i^2+x_j^2$ 对全部无序对求和得到。对单位向量 $a,c$，精确极化式及平行四边形恒等式给

$$
\begin{aligned}
\|B(a,c)+B(c,a)\|
&=\tfrac12\|q(a+c)-q(a-c)\|\\
&\le\tfrac\Delta2(\|a+c\|^2+\|a-c\|^2)=2\Delta.
\end{aligned}
$$

对非零 $a,c$ 分别归一化，再用双线性得到 (2.14)；任一为零时结论也成立。最后 $B(a,1)=0$ 是原单位导子律，因此 $D_1a=B(1,a)+B(a,1)$，取 $a$ 为单位向量得 $\|D_1\|_{\rm op}\le2u\Delta$。代入 (2.10) 得 (2.15)。总平方和界对其每个子族和每个分量给上述上界，完成证明。这里不主张常数 $2n-1$ 的最优性。∎

**定理 2.4（实际额外通道及零分母的范围）。** 对两方原完整基，定义双线性映射的 Hilbert–Schmidt 量

$$
f_J^2=\sum_{i,j=1}^{n_J}\|B_J(e_i,e_j)\|^2,
\qquad
\mathcal E_\beta=\beta B_A\otimes B_B.
\tag{2.17}
$$

$\mathcal E_\beta$ 是实际 $T$ 的额外双线性通道，而 $\beta$ 只是其系数。在原卷定义 14.1 的乘积内积下，

$$
\boxed{\|\mathcal E_\beta\|_{\rm HS}=|\beta|f_Af_B,\qquad
\|\mathcal E_\beta(H,X)\|
\le|\beta|f_Af_B\|H\|\|X\|.}
\tag{2.18}
$$

这里双线性映射的 Hilbert–Schmidt 范数指其在两个输入空间的 Hilbert 张量积上线性化后的范数。若任一方 $J$ 的 $Z_J>0$，则全部联合输入还满足

$$
\boxed{\|\mathcal E_\beta(H,X)\|
\le\frac{u_Jm_Jf_Af_B}{r_JZ_J}\|H\|\|X\|.}
\tag{2.19}
$$

两方均有正分母时可取两个系数上界的较小者。使用 $\overline m_J$ 仍给有效上界。因此从系数控制取得通道的统一小量还需要控制 $f_Af_B$ 及活动分母，不能把系数和通道的范数认作同一数量。

下列退化均保留在原定义的范围内：若 $Z=0$，则 $Q=h=0$，混合报告满足 $m=rA$，(2.5) 为零矩，不能除以 $Z$；若 $Q=0$，则精确地 $m=r\sqrt{A^2+\beta^2h^2}$，所以严格阈值 $m<rA$ 不可能成立。若 $A=0$，该严格阈值同样不成立。若 $Q>0$ 但 $\overline m\ge rA$，式 (2.10) 不提供正的 $\mu$；若 $\kappa=0$，不得使用 (2.13) 除以它。若 $\overline\varepsilon_{\rm self}=0$ 且已有正的 $\mu$，(2.14) 则确实推出全局交替。$r=0$ 不属于原参照对的允许范围；在删去活动前件的扩大范围内，以上需除以 $r$ 的结论均不适用。充分阈值失效的这些情形不被排除，也不自动具有相反结论。

证明。把两个联合输入的因子重排，$\mathcal E_\beta$ 的线性化就是 $\beta\widetilde B_A\otimes\widetilde B_B$，其中 $\widetilde B_J:J\otimes J\to J$ 是 $B_J$ 的线性化；重排是正交映射。对正交张量基求像的范数平方，得到 $\|\mathcal E_\beta\|_{\rm HS}^2=\beta^2f_A^2f_B^2$。算子范数不超过 Hilbert–Schmidt 范数，且 $\|H\otimes X\|=\|H\|\|X\|$，故 (2.18) 对任意联合输入成立，未把它们限制为简单张量。代入 (2.7) 得 (2.19)。

若 $Z=0$，所有 $z_{ij}=0$，所以 $C_{z_{ij}}=L_{z_{ij}}=0$，由 (2.11) 得 $m=rA$。若 $Q=0$，则 (2.11) 的最后一项族为零，证明 (2.8) 时计算的 $\|E\|$ 就等于 $m$。其余结论分别由非负性、正分母要求及定理 2.3 直接得到。∎

## 3. 同一有限族的可实现退化

**命题 3.1（非交替的单位生成元、零上三角与保持非零的额外通道）。** 存在满足原卷定义 8.1、14.1 的一参数实际系统族，两方均非交替、活动参照均非零，原有限报告的总平方和趋零，而实际额外通道不趋零。具体地，取 $t>0$，两方都使用

$$
J=\mathbb R1\oplus\mathbb R^2,
\qquad
S((\alpha,a),(\gamma,c))=(\alpha\gamma+\langle a,c\rangle,\alpha c+\gamma a)
\tag{3.1}
$$

及标准正内积。令 $x,y$ 是向量部分的正交单位基，$J_0x=y,J_0y=-x$，并定义

$$
D^t_{(\alpha,a)}(\gamma,c)=(0,t\alpha J_0c),
\qquad B_t(a,c)=D^t_ac.
\tag{3.2}
$$

固定完整基的顺序为 $e_1=x,e_2=y,e_3=1$，保留由此产生的全部基向量、归一两两和及 $i<j,k$ 混合标签；两方的固定参照均取 $b=1,d=x$。实际运算取原卷命题 14.2 的原卷式 (14.3)，其中 $\kappa=0$，$\beta$ 任意。则在每一方，

$$
\begin{gathered}
u=1,\qquad v=ty,\qquad w=0,\qquad r=t,\\
Z=Q=h=0,\qquad A^2=2,\qquad
m^2=2t^2,\qquad \varepsilon_{\rm self}=0,\\
\sup_{\|a\|=1}\|D^t_aa\|=t/2>0,
\qquad f_J^2=2t^2.
\end{gathered}
\tag{3.3}
$$

两方原有限报告的总量为 $\Theta(M,T)=4t^2$，且这些报告完全不依赖 $\beta$。若取 $\beta=t^{-2}$，则

$$
\|\mathcal E_\beta\|_{\rm HS}=2,
\qquad
\|\mathcal E_\beta(1\otimes1,x\otimes x)\|=1.
\tag{3.4}
$$

因此，仅凭这些有限报告的绝对小量，在全部原允许的未交替实现上，不能得到实际额外通道趋零的无条件结论；即使自身报告全部为零，也不能在 $\kappa=0$ 时推出交替。该族满足 $m=rA$，正好不通过定理 2.2 的严格充分阈值。

证明。式 (3.1) 交换、含幺，其 Frobenius 三线性形式在三个变量中对称，标准内积正定。算子 $\delta(\gamma,c)=(0,J_0c)$ 是 $S$ 的导子：导子律的标量分量为 $\langle J_0a,c\rangle+\langle a,J_0c\rangle=0$，向量分量为 $\alpha J_0c+\gamma J_0a$。故每个 $D^t_{(\alpha,a)}=t\alpha\delta$ 都是比较导子，指派实线性且非零。$B_t(1,x)=ty$、$B_t(x,1)=0$，所以场确实未交替，$D^t_1$ 也不为零；所有局部前件都成立。原卷命题 14.2 保证所取实际 $M,T$ 满足四通道闭包和两个单位嵌入。

在已固定的基顺序下，全部 $i<j$ 都有 $z_{ij}=0$：前两个基元的标量分量为零，而 $B_t(a,1)=0$。所以 $Z=Q=h=0$。又 $L_1=I$，仅 $K_{12}$ 非零，且

$$
K_{12}1=0,\qquad K_{12}x=-y,\qquad K_{12}y=x.
$$

于是 $A^2=2$，(2.11) 使混合平方和为 $r^2A^2=2t^2$，与 $\beta$ 无关。自身报告由原卷式 (16.4) 为零，因为 $\kappa=0,w=0$；这对完整原自身族中的每个 $p$ 都成立。翻转两方后同样如此，因此 $\Theta=2m^2=4t^2$。

对单位 $a=(\alpha,a_0)$，有

$$
\|D^t_aa\|=t|\alpha|\|a_0\|
\le\tfrac t2(\alpha^2+\|a_0\|^2)=t/2,
$$

等号在 $a=(1+x)/\sqrt2$ 达到。双线性映射在基输入上的非零像只有 $B_t(1,x)=ty$ 和 $B_t(1,y)=-tx$，故 $f_J^2=2t^2$。(2.18) 给 $\|\mathcal E_\beta\|_{\rm HS}=2|\beta|t^2$；在指定单位联合输入上的像为 $\beta t^2y\otimes y$。令 $\beta=t^{-2}$ 即得 (3.4)。每个 $t>0$ 的活动都非零；$t=0$ 的极限失去活动，不被当作满足原定义的新端点。固定任意 $t>0$ 而改变 $\beta$ 时，同一批实际报告也保持完全相同，额外通道却可任意增大。∎

## 4. 定量结论的数学归属与适用范围

**定义 4.1（精确复合性、有限条件估计与解释边界）。** 本节沿用如下文献对应与结论范围。[Moldoveanu，*Quantum mechanics from invariance principles*，arXiv:1303.3935，式 (6)–(9)](https://arxiv.org/html/1303.3935)的局部不变性对所列运算族施加 Leibniz，包含有向运算自身，并在式 (6) 后明确输入 $1\alpha f=0$；式 (7)–(8) 列一般四通道，式 (9) 是精确复合产品。[Kapustin，*Is there life beyond Quantum Mechanics?*，arXiv:1303.6917v4，Axioms 4–7、Proposition 3.1、Theorem 3.1](https://arxiv.org/html/1303.6917v4)从 Lie 观测量、中心常量和精确组合条件研究公共参数及三种结合代数分支；其有限维量子选择还使用 Axioms 8–9 的谱条件及 Corollary 4.3 等结论。这些是精确 Jordan–Lie 复合性及表示路线的文献先例，不被认作本节的有限噪声结论。

定理 2.2–2.4 与命题 3.1 的数学归属为 `repo-derived`：承重内容是在原 C98 带标签族中，用单位线性读出及 $D_1$ 的斜伴随性取得交替前的精确 $\beta$ 矩，以混合族的伴随分解排除条件性的零系数区间，再把原有限自身样本传至全局对称缺陷，并给出同一族的可实现退化。斜伴随性复用 V95 定理 2.1 第一项；自身收缩复用原卷式 (16.6) 与原卷定理 17.2；Cauchy–Schwarz、Hilbert–Schmidt 正交、三角不等式和极化是其中的标准中间工具。原卷定理 17.3 的双方交替前件没有被用于上述估计，也没有被静默删除后沿用其公式。此归属不主张全局文献原创优先权。

这些定量结论的对象是明确的有限维正 Frobenius 场、给定四通道实际运算和其原有限报告。正的系数下界、活动量下界及局部通道范数控制各按定理中的显式充分条件承担；它们不是一般噪声报告的自动后果。定理 2.2 只给 $|\kappa|$ 的下界，不给噪声情形的 $\kappa$ 符号；定理 2.3 只给交替缺陷，不给 Jacobi 稳定性、邻近复 $C^*$ 代数或完整近似重构。一般联合量子表示和状态、效果、过程的物理解释仍按原卷定理 16.4、19.1 的精确前件及操作供应条件承担；这些条件估计不构成完整物理理论，也不主张最优常数。

[原卷定义 20.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#20-保留条件取值的实际关系延伸)与[原卷定理 21.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#21-不给通道闭包也能反推出局部量子结构)使用保值条件作用和全输入的精确实际联合导子律；C99 对原实际整体的认证及状态—过程接续分别由原卷定理 23.1、25.2、26.1 承担。[原卷定义 27.1、原卷定理 27.3](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#27-任意实际正比较下的同一整体延伸)把这条精确局部重构链推广到不必因子化的正 Frobenius 联合内积；[原卷定理 30.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#30-活动第三方认证乘法不强迫中心权独立)以 C100 的实际活动延伸认证原整体，保留任意严格正中心权。[原卷定义 33.1–33.2、原卷定理 33.3](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#33-允许静态对象的活动伙伴候选)进一步允许静态对象，以每个同一实际对象的活动伙伴条件 C101 给出静态—活动分类；[原卷定理 34.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#34-经典与量子实际复合的完整分类)认证三类实际张量关系。这些精确推广不以原 C98 有限报告的非零小量替代其全输入恒等式或伙伴存在量词，也不给出本卷的交替前带噪误差界。

定义 2.1 只使用原卷定义 14.1 的实际四通道闭包、乘积内积和原有限报告，不附加 C99、C100、C101 的精确合同，也不从这些候选推出乘积内积或四通道闭包。命题 3.1 是原报告域内的非交替退化，不是满足上述精确合同全部条件的反例。

[有限内部约束 V97，定理 9.2](AURIC_FINITE_INTERNAL_CONSTRAINTS_UNIQUE_WHOLE_SOURCE_AND_STABLE_QUANTUM_READOUT_V97.md#thm-c97-low-defect)、[V97 定理 10.1](AURIC_FINITE_INTERNAL_CONSTRAINTS_UNIQUE_WHOLE_SOURCE_AND_STABLE_QUANTUM_READOUT_V97.md#thm-c97-inner-certificate)及[V97 §16](AURIC_FINITE_INTERNAL_CONSTRAINTS_UNIQUE_WHOLE_SOURCE_AND_STABLE_QUANTUM_READOUT_V97.md#sec-c97-reconstruction)的稳定性对象是既有共同复 $C^*$ 代数中的态与正约束，其固定内层证书使用有限缺额隙及零约束态的局域直径。该约束缺额与本节的实际运算残差不是同一数量；在尚无保持正性、误差包络和实际运算对应的桥梁时，(2.14) 不给出该态的迹距离控制，也不给出参考稳定的近似恢复或近似复 $C^*$ 重构。共同源的唯一性同样不供应实际耦合、控制菜单或时钟标定。

## 追加锚（本行以下为增补区）

## 5. 无通道闭包的实际全三线性残差合同

**定义 5.1（从原 C99 二元边重新指定前件）。** 本节起另取[原卷定义 20.1](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#20-保留条件取值的实际关系延伸)的二元实际边。第 1–4 节的四通道闭包、$\kappa,\beta$、有序活动参照和 $\Theta$ 均不是本节前件或报告。局部 $J_A,J_B$ 是非零有限维实空间，分别有正定内积 $g_J$、交换含幺 Frobenius 双线性乘法 $S_J$，以及非零实线性指派 $D^J:J_J\to\operatorname{Der}(J_J,S_J)$。记 $L^J_ac=S_J(a,c)$、$B_J(a,c)=D^J_ac$。不预设交替、Jacobi 或 $D^J_{1_J}=0$。

同一实际联合空间和内积为 $V=J_A\otimes_{\mathbb R}J_B$、$g_V=g_A\otimes g_B$。$M:V\times V\to V$ 是任意交换含幺 Frobenius 双线性乘法，单位恰为 $1_A\otimes1_B$；$\Gamma:V\to\operatorname{End}_{\mathbb R}(V)$ 任意实线性。原卷 (20.1)、(20.2) 原样对全部输入成立，即

$$
\begin{aligned}
M(a\otimes1_B,c\otimes d)&=S_A(a,c)\otimes d,\\
M(1_A\otimes b,c\otimes d)&=c\otimes S_B(b,d),\\
\Gamma_{a\otimes b}(c\otimes1_B)&=D^A_ac\otimes b,\\
\Gamma_{a\otimes b}(1_A\otimes d)&=a\otimes D^B_bd.
\end{aligned}
\tag{5.1}
$$

仅将原卷 (20.3) 的零恒等式替换为同一实际运算的三线性残差

$$
E(H,X,Y)=\Gamma_HM(X,Y)
       -M(\Gamma_HX,Y)-M(X,\Gamma_HY).
\tag{5.2}
$$

不另要求 $\Gamma_H$ 是导子、斜伴随或满足 Jacobi，也不将 $M$ 投影到任何四通道空间。这里研究的是 C99 所用二元边的局部交替桥；原卷定义 20.2 对原整体再作活动延伸的存在量词，不由小残差自动供应。

**定义 5.2（完整报告、单位和有限条件参数）。** 固定两方的完整正交单位基 $(e_i)_{i=1}^{n_A}$、$(f_j)_{j=1}^{n_B}$，维数包括单位方向，但不要求单位本身是基向量。记其乘积正交单位基为 $(v_\mu)_{\mu=1}^N$，$N=n_An_B$。报告是每个有序三元标签的实际输出，误差量为未作平均的平方和：

$$
\epsilon^2=
\sum_{\mu,\nu,\lambda=1}^N
 \|E(v_\mu,v_\nu,v_\lambda)\|^2.
\tag{5.3}
$$

$\epsilon$ 是此三线性张量的 Hilbert–Schmidt 范数，与所选完整正交单位基无关，且

$$
\|E(H,X,Y)\|\le\epsilon\|H\|\|X\|\|Y\|.
\tag{5.4}
$$

若报告的是每个三元标签的均方根输出 $\eta$，则 $\epsilon=N^{3/2}\eta$，不是 $\eta$ 本身。若输出再拆成标量坐标，(5.3) 已含输出坐标的平方和，不再除以输出维数。

对 $J=A,B$，取同一实现上的有限非负上界 $\ell_J,d_J$，并定义有限曲率读数 $k_J$：

$$
\begin{aligned}
u_J&=\|1_J\|>0,\\
\|S_J(a,c)\|&\le\ell_J\|a\|\|c\|,\qquad
\|D^J_ac\|\le d_J\|a\|\|c\|,\\
k_A&=\max_{i,j,r}
       \|[L^A_{e_i},L^A_{e_j}]e_r\|,\qquad
k_B=\max_{i,j,r}
       \|[L^B_{f_i},L^B_{f_j}]f_r\|.
\end{aligned}
\tag{5.5}
$$

这些是附加可给定的充分参数，不是由 $\epsilon$ 单独反演出的数。它们可完全从局部有限表取得：例如 $\ell_J,d_J$ 可分别取 $\bigl(\sum_{i,j}\|S_J(e_i,e_j)\|^2\bigr)^{1/2}$、$\bigl(\sum_{i,j}\|D^J_{e_i}e_j\|^2\bigr)^{1/2}$，对 $B$ 方以 $f$ 代 $e$。允许使用更紧的实际双线性运算范数上界。$k_J$ 是指定基上的最大值，不冒充整个单位球上的最大曲率；改变基时可重算它。单位长度不被默认为 $1$，且 $\ell_Ju_J\ge1$。

本合同中的活动性保证每个 $k_J>0$，但不给任何统一正下界。事实上若完整曲率表为零，双线性使全部左乘对易；交换性再给 $L_{S(a,c)}=L_aL_c$，所以乘法结合。有限正含幺交换结合 Frobenius 代数由共同自伴谱分解同构于有限实直积，其导子全为零，和活动性矛盾。这正是原卷定理 21.1 所用的定性论证。下文仍逐项保留 $k_J=0$ 的公式分支，明确零分母时能得什么；活动合同排除该分支，并不授权在一个变化族上把 $k_J$ 换成未给出的统一常数。

## 6. 完整实际残差的曲率条件二次根证书

**定理 6.1（自缺陷、完整对称缺陷及单位生成元）。** 在定义 5.1–5.2 的同一实现上，置

$$
c_A=u_B(1+2u_A\ell_A),\qquad
c_B=u_A(1+2u_B\ell_B).
\tag{6.1}
$$

若 $k_B>0$，定义

$$
r_A=
\frac{\epsilon c_B+
 \sqrt{\epsilon^2c_B^2+4k_B\epsilon c_A d_B}}{2k_B},
\qquad
\delta_A=\min\{d_A,r_A\};
\tag{6.2}
$$

若 $k_B=0$，定义 $\delta_A=d_A$，不对 (6.2) 作 $0/0$ 解释。交换 $A,B$ 定义 $r_B,\delta_B$；其中 $r_B$ 只在 $k_A>0$ 时使用。则两方均有

$$
\begin{aligned}
\sup_{\|a\|=1}\|D^J_aa\|&\le\delta_J,\\
\|D^J_ac+D^J_ca\|&\le2\delta_J\|a\|\|c\|,\\
\|D^J_{1_J}\|_{\rm op}
 &\le u_J\min\{d_J,2\delta_J\}.
\end{aligned}
\tag{6.3}
$$

$\delta_J\le d_J$ 是与残差证书独立的平凡截顶。未除以曲率的结论也对零曲率分支成立：对每个单位 $a\in J_A$，

$$
k_B\|D^A_aa\|^2
 \le\epsilon\bigl(c_A d_B+c_B\|D^A_aa\|\bigr),
\tag{6.4}
$$

另有交换双方的式子。因此不借任何正活动下界就有逐实现的条件证书；只有在给出相应条件控制后，它才是一个族上的消失模量。

证明。局部每个导子都消去单位，并由[比较曲率 V95 定理 2.1 第一项及其证明](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md#2-有限正比较下自守与复乘法成为结论)对局部内积斜伴随。该项只用有限维、交换含幺正 Frobenius 乘法与导子律，不用 C95、局部交替或双曲率抵消。下列斜伴随步骤仅施于局部 $D^J_a$，不施于实际 $\Gamma_H$。

先定义线性算子族 $Q$ 和实际差 $R$：

$$
Q_{a\otimes b}=D^A_a\otimes L^B_b+L^A_a\otimes D^B_b,
\qquad R_H=\Gamma_H-Q_H.
\tag{6.5}
$$

$Q$ 由张量泛性质线性延拓，尚不被断言为实际 $\Gamma$。由 (5.1)，$M(c\otimes1_B,1_A\otimes d)=c\otimes d$。将这两个输入代入 (5.2)，两个输出项各用一次模作用，得到对全部 $H,c,d$ 的精确等式

$$
R_H(c\otimes d)
 =E(H,c\otimes1_B,1_A\otimes d).
\tag{6.6}
$$

完整报告在此提供了比逐个简单张量估计更直接的界。将 $R$ 视为线性映射 $V\otimes V\to V$，其系数平方和为

$$
\sum_{\mu,i,j}
 \|E(v_\mu,e_i\otimes1_B,1_A\otimes f_j)\|^2
 \le u_A^2u_B^2\epsilon^2.
\tag{6.7}
$$

因为 $(e_i\otimes1_B/u_B)_i$ 和 $(1_A/u_A\otimes f_j)_j$ 分别是 $V$ 内的正交单位族，可以各自补成正交单位基；(6.7) 左端除去单位因子后只是 $E$ 在三个输入槽上的 Hilbert–Schmidt 平方和的一部分。因此包括任意纠缠输入 $Y$，均有

$$
\|R_HY\|\le\rho\|H\|\|Y\|,
\qquad \rho=\epsilon u_Au_B.
\tag{6.8}
$$

这里没有把简单张量的范数界不经证明地延拓到任意张量，也没有隐去维数因子；完整平方和本身承担了延拓。

记实际左乘为 $\mathbb L_XY=M(X,Y)$，并置

$$
F(X,Y)=M(X,Y)-(S_A\otimes S_B)(X,Y),\qquad
K^J_{ac}=[L^J_a,L^J_c].
\tag{6.9}
$$

$F$ 交换，但不要求其属于任何通道空间。残差定义的算子形式是

$$
[\Gamma_H,\mathbb L_X]-\mathbb L_{\Gamma_HX}
       =E(H,X,\,\cdot\,).
\tag{6.10}
$$

在此依次取 $H=a\otimes b$、$X=c\otimes1_B$ 与 $X=1_A\otimes d$。用 (5.1)、(6.5)，以及局部导子恒等式 $[D_a,L_c]=L_{D_ac}$，得到

$$
\begin{aligned}
\mathbb L_{D^A_ac\otimes b}
 &=L^A_{D^A_ac}\otimes L^B_b
        +K^A_{ac}\otimes D^B_b+\mathcal A_{a,b,c},\\
\mathcal A_{a,b,c}
 &=[R_{a\otimes b},L^A_c\otimes I]
                 -E(a\otimes b,c\otimes1_B,\,\cdot\,),\\
\mathbb L_{a\otimes D^B_bd}
 &=L^A_a\otimes L^B_{D^B_bd}
        +D^A_a\otimes K^B_{bd}+\mathcal B_{a,b,d},\\
\mathcal B_{a,b,d}
 &=[R_{a\otimes b},I\otimes L^B_d]
                 -E(a\otimes b,1_A\otimes d,\,\cdot\,).
\end{aligned}
\tag{6.11}
$$

特别地，没有在展开中使用 $D_1=0$。由 (5.4)、(6.8) 和 $\|[T,U]\|\le2\|T\|\|U\|$，

$$
\begin{aligned}
\|\mathcal A_{a,b,c}\|_{\rm op}
 &\le\epsilon c_A\|a\|\|b\|\|c\|,\\
\|\mathcal B_{a,b,d}\|_{\rm op}
 &\le\epsilon c_B\|a\|\|b\|\|d\|.
\end{aligned}
\tag{6.12}
$$

现在固定任意 $a\in J_A$，令 $z=D^A_aa$。第一条 (6.11) 取 $c=a$，因 $K^A_{aa}=0$，

$$
F(z\otimes b,Y)=\mathcal A_{a,b,a}Y.
\tag{6.13}
$$

另取 $f,g,b\in J_B$、$c\in J_A$，记 $w=D^B_fg$。第二条 (6.11) 作用于 $z\otimes b$，再用 $F$ 的交换性和 (6.13)，得

$$
\begin{aligned}
D^A_cz\otimes K^B_{fg}b
 &=F(c\otimes w,z\otimes b)
                    -\mathcal B_{c,f,g}(z\otimes b)\\
 &=\mathcal A_{a,b,a}(c\otimes w)
                    -\mathcal B_{c,f,g}(z\otimes b).
\end{aligned}
\tag{6.14}
$$

所以

$$
\|D^A_cz\|\|K^B_{fg}b\|
 \le\epsilon\|b\|\|c\|\|f\|\|g\|
          \bigl(c_A d_B\|a\|^2+c_B\|z\|\bigr).
\tag{6.15}
$$

若 $k_B>0$，从定义 5.2 的有限表选单位基向量 $f,g,b$ 达到该最大值。再取 $\|a\|=1$、$c=a$。局部斜伴随性给

$$
\|z\|^2
 =g_A(D^A_aa,z)=-g_A(a,D^A_az)
 \le\|D^A_az\|.
\tag{6.16}
$$

(6.15) 因而推出 (6.4)。$k_B=0$ 时 (6.4) 两侧仍满足所示非负不等式，但不提供除法。对 $k_B>0$，不等式
$k_Bs^2-\epsilon c_Bs-\epsilon c_A d_B\le0$
在 $s\ge0$ 中的解区域正是 $0\le s\le r_A$，包括 $\epsilon=0$、$d_B=0$ 或常数项为零的情形。另由 (5.5) 有 $\|z\|\le d_A$，得到第一条 (6.3)。交换双方得另一方。

为证明完整双线性结论，置 $q_J(a)=D^J_aa$。实线性给 $q_J(ta)=t^2q_J(a)$，故 $\|q_J(a)\|\le\delta_J\|a\|^2$ 对全部 $a$ 成立。极化恒等式为

$$
D^J_ac+D^J_ca
 =\tfrac12\bigl(q_J(a+c)-q_J(a-c)\bigr).
\tag{6.17}
$$

当 $a,c$ 均为单位时，平行四边形恒等式给右端范数不超过 $2\delta_J$。双线性缩放覆盖任意非零 $a,c$，零输入时两侧均为零。最后 $D^J_a1_J=0$，故取 $c=1_J$ 得 $\|D^J_{1_J}a\|\le2u_J\delta_J\|a\|$；(5.5) 又独立给 $u_Jd_J$ 的上界。这证明全部 (6.3)。∎

**推论 6.2（精确端点、固定条件消失及维数依赖）。** 定义 5.1 的活动合同下，$\epsilon=0$ 恢复两方局部交替和 $D^J_{1_J}=0$，并由 (6.8) 恢复同一实际 $\Gamma=Q$。对一族满足该合同的实际实现，若给出

$$
k_A,k_B\ge k_0>0,\qquad
c_A,c_B\le C,\qquad d_A,d_B\le D_0<\infty,
\tag{6.18}
$$

则

$$
\delta_J\le
 \frac{\epsilon C}{k_0}
       +\sqrt{\frac{\epsilon C D_0}{k_0}}
 \longrightarrow0\qquad(\epsilon\longrightarrow0).
\tag{6.19}
$$

若还要求单位生成元范数在该族上一致趋零，$u_A,u_B$ 的统一上界是一个充分输入。对报告均方根 $\eta$，(6.19) 的右端应写为

$$
\frac{N^{3/2}\eta C}{k_0}
 +\sqrt{\frac{N^{3/2}\eta C D_0}{k_0}}.
\tag{6.20}
$$

因此维数变化时，仅 $\eta\to0$ 不是这里的充分消失条件。更一般地，控制 (6.2) 中两个实际比值 $\epsilon c_B/k_B$、$\epsilon c_A d_B/k_B$ 趋零便足以控制 $A$ 方，另一方交换指标；这不要求每个原始参数分别有界。

证明。活动性使两个曲率分母为正，故 $\epsilon=0$ 时 (6.2)、(6.3)、(6.8) 给精确结论。非负数满足 $\sqrt{x^2+4y}\le x+2\sqrt y$，用于 (6.2) 即给 $r_A\le\epsilon c_B/k_B+\sqrt{\epsilon c_A d_B/k_B}$；代入 (6.18) 得 (6.19)。单位生成元的结论由 (6.3) 给出，(6.20) 则由 (5.3) 的归一化换算给出。所有界均为充分界，不断言最优常数或必要条件。

若改变共同时间单位，将两方 $D$ 和实际 $\Gamma$ 同乘 $\tau\ne0$，则 (5.1) 保持，$E$ 同乘 $\tau$，$\epsilon,d_J,\delta_J$ 可相应同乘 $|\tau|$，而 $u_J,\ell_J,k_J,c_J$ 不变；(6.2) 正好按此齐次缩放。$\tau=0$ 是静态极限，不是活动合同中的另一个实现。∎

## 7. 完整残差趋零而自缺陷不消失的实际尺度障碍

**命题 7.1（固定九维联合载体上的全报告反例族）。** 存在每个 $t>0$ 都满足 (5.1) 以及全部局部活动、正性、含幺、Frobenius 和导子前件的实际实现，其联合维数恒为 $9$，且

$$
\epsilon_t^2=48t^6\longrightarrow0,\qquad
\sup_{\|a\|=1}\|D^J_aa\|=\tfrac12
\quad(J=A,B).
\tag{7.1}
$$

这里 $E_t$ 是完整实际 (5.2)，不是四通道报告的子族。每个 $t>0$ 的 $E_t$ 非零。这一族排除不带任何额外尺度或条件控制、只由完整 $\epsilon$ 给出且趋于零的局部交替界。

证明。两方均取同一个欧氏空间 $J=\mathbb R\oplus\mathbb R^2$，正交单位基为 $e_0,x,y$。先定义

$$
\begin{aligned}
S_0((\alpha,u),(\beta,v))
   &=(\alpha\beta+\langle u,v\rangle,\alpha v+\beta u),\\
Ke_0&=0,\qquad Kx=y,\qquad Ky=-x,\\
D_{(\alpha,u)}&=\alpha K.
\end{aligned}
\tag{7.2}
$$

$S_0$ 交换、单位为 $e_0$；其欧氏三次型
$\alpha\beta\gamma+\gamma\langle u,v\rangle+
\alpha\langle v,w\rangle+\beta\langle u,w\rangle$
全对称，故为正 Frobenius 比较。$K$ 在空间部分斜伴，$\langle Ku,v\rangle+\langle u,Kv\rangle=0$，直接代入 (7.2) 给
$KS_0(a,c)=S_0(Ka,c)+S_0(a,Kc)$。
因此每个 $D_a$ 是导子，指派实线性且 $D_{e_0}=K\ne0$。

对 $t>0$ 定义实际局部产品和单位

$$
S_t=tS_0,\qquad 1_t=t^{-1}e_0,
\tag{7.3}
$$

保持原欧氏内积和 $D$ 不变。导子律、交换性及 Frobenius 性随产品同次缩放保持，单位由 (7.3) 直接给出。局部自缺陷为

$$
D_aa=(0,\alpha Ku),\qquad
\|D_aa\|=|\alpha|\|u\|
 \le\tfrac12(\alpha^2+\|u\|^2).
\tag{7.4}
$$

$a=(e_0+x)/\sqrt2$ 取等号，所以 (7.1) 的第二项成立。$D_{1_t}=t^{-1}K$ 并不为零；这里没有暗加单位标签生成元为零。

在同一个实际 $V=J\otimes J$ 上取欧氏乘积内积，令 $L^0_a=S_0(a,\,\cdot\,)$，并给出完整联合运算

$$
\begin{aligned}
M_0(a\otimes b,c\otimes d)&=S_0(a,c)\otimes S_0(b,d),\\
Q^0_{a\otimes b}&=D_a\otimes L^0_b+L^0_a\otimes D_b,\\
M_t&=t^2M_0,\qquad \Gamma^t_H=tQ^0_H .
\end{aligned}
\tag{7.5}
$$

线性延拓定义全部 $H$ 上的 $\Gamma^t$。$M_t$ 交换、对乘积正内积 Frobenius，单位恰为 $1_t\otimes1_t$。对简单张量逐项有

$$
\begin{aligned}
M_t(a\otimes1_t,c\otimes d)&=S_t(a,c)\otimes d,\\
M_t(1_t\otimes b,c\otimes d)&=c\otimes S_t(b,d),\\
\Gamma^t_{a\otimes b}(c\otimes1_t)
 &=t\bigl(D_ac\otimes L^0_b(t^{-1}e_0)
          +L^0_ac\otimes D_b(t^{-1}e_0)\bigr)
   =D_ac\otimes b,\\
\Gamma^t_{a\otimes b}(1_t\otimes d)&=a\otimes D_bd.
\end{aligned}
\tag{7.6}
$$

其中 $D_be_0=0$；所有身份由多线性覆盖全部要求的输入。这检查了保留的两类模作用和两类保值条件作用。实际联合残差由 (7.5) 在三项中同次给出

$$
E_t=t^3E_0,
\tag{7.7}
$$

其中 $E_0$ 使用 $M_0,Q^0$。一个具体完整基标签已给出非零见证：

$$
E_t(e_0\otimes x,\ e_0\otimes y,\ x\otimes y)
      =t^3y\otimes x.
\tag{7.8}
$$

事实上 $M_0(e_0\otimes y,x\otimes y)=x\otimes e_0$，$Q^0_{e_0\otimes x}=K\otimes L^0_x$ 将它送到 $y\otimes x$，而此 $Q^0$ 对两个原输入的像均为零。

为取得完整而非抽样的平方和，固定第一输入 $H$，对另外两个完整基槽求和。$H$ 的两个因子都在 $\{x,y\}$ 时 $Q^0_H=0$；$H=e_0\otimes e_0$ 时 $Q^0_H=K\otimes I+I\otimes K$ 是 $M_0$ 的导子。这五个标签的残差全为零。对其余四个标签，可按下列有限张量计数计算。设

$$
\begin{aligned}
P(c,e)&=S_0(Kc,e),& Q(c,e)&=S_0(c,Ke),\\
U_b(d,f)&=L^0_bS_0(d,f)-S_0(L^0_bd,f),&
V_b(d,f)&=L^0_bS_0(d,f)-S_0(d,L^0_bf).
\end{aligned}
\tag{7.9}
$$

当 $b=x$ 或 $y$ 时，局部导子律给

$$
E_0(e_0\otimes b,c\otimes d,e\otimes f)
 =P(c,e)\otimes U_b(d,f)+Q(c,e)\otimes V_b(d,f).
\tag{7.10}
$$

这些双线性张量均使用固定三维正交单位基。由 (7.2) 的乘法表
$e_0a=a$、$x^2=y^2=e_0$、$xy=0$ 取得

$$
\begin{aligned}
\|P\|_{\rm HS}^2=\|Q\|_{\rm HS}^2&=4,
 &\langle P,Q\rangle_{\rm HS}&=-2,\\
\|U_b\|_{\rm HS}^2=\|V_b\|_{\rm HS}^2&=2,
 &\langle U_b,V_b\rangle_{\rm HS}&=1.
\end{aligned}
\tag{7.11}
$$

例如 $P$ 的四个非零输入是 $(x,e_0),(x,y),(y,e_0),(y,x)$，输出分别为 $y,e_0,-x,-e_0$；$Q(c,e)=P(e,c)$。$V_x$ 仅在 $(y,x),(y,y)$ 非零，输出为 $-y,x$，$U_x(d,f)=V_x(f,d)$。将 $x,y$ 同时旋转给 $b=y$ 的相同内积读数。(7.10) 的平方和因而为 $4\cdot2+4\cdot2+2(-2)\cdot1=12$。翻转双方给另外两个标签的同样数值。因此

$$
\begin{array}{c|c|c}
H\text{ 的类型}&\text{标签数}&
 \displaystyle\sum_{\nu,\lambda}
 \|E_0(H,v_\nu,v_\lambda)\|^2\\ \hline
e_0\otimes x,\ e_0\otimes y,\ x\otimes e_0,\ y\otimes e_0
 &4&12\text{（每个标签）}\\
e_0\otimes e_0,\ \{x,y\}\otimes\{x,y\}
 &5&0
\end{array}
\tag{7.12}
$$

九个第一输入和全部 $9^2$ 个其余输入已被计入，得到 $\epsilon_0^2=48$，由 (7.7) 得 (7.1)。

同一模型的实际参数也可明确对应到证书：

$$
n_A=n_B=3,\quad N=9,\quad
u_A=u_B=t^{-1},\quad
d_A=d_B=1,\quad
\ell_A=\ell_B=\sqrt2\,t,\quad
k_A=k_B=t^2.
\tag{7.13}
$$

$d=1$ 由 $D_ac=\alpha Kv$ 达到。对单位 $a=(\alpha,u),c=(\beta,v)$，令 $r=\|u\|,s=\|v\|$，则
$\|S_0(a,c)\|^2\le(|\alpha\beta|+rs)^2+(|\alpha|s+|\beta|r)^2
=1+4|\alpha\beta|rs\le2$，
同向取 $a=c=(e_0+x)/\sqrt2$ 达到上界。完整曲率表中仅空间基向量对可能非零，$[L^0_x,L^0_y]y=x$、$[L^0_x,L^0_y]x=-y$，故 $k=t^2$。因此

$$
c_A=c_B=\frac{1+2\sqrt2}{t},\qquad
\frac{\epsilon_t c_A}{k_A}
 =4\sqrt3(1+2\sqrt2),
\tag{7.14}
$$

另一侧同样。残差虽趋零，证书的条件比值并不趋零；(6.2) 的平凡截顶也仍可使用。这里的活动始终非零，但单位长度发散、曲率读数趋零。$t=0$ 时产品不再含幺，故不是合同内的精确零残差端点；这与推论 6.2 没有矛盾。反例断言的是必须排除某种实际退化或添加额外观察，不断言 (6.18) 的每一项分别必要，也不排除其他充分证书。∎

## 8. 实际参数桥的数学来源与未延伸边界

**定义 8.1（承重推导、成熟输入与范围）。** 定理 6.1 及命题 7.1 的承重内容属于本仓推导（repo-derived）：从原卷 (20.1)、(20.2) 和同一实际完整三线性残差，取得 (6.6) 的模板差、(6.14) 的曲率耦合误差，再由局部斜伴随性得到二次根模量；并以满足同一残差合同的完整实际尺度族检查其条件边界。V95 定理 2.1 第一项的局部导子斜伴随性、原卷定理 21.1 的精确条件作用与曲率论证是复用的中间结果；Hilbert–Schmidt 收缩、Cauchy–Schwarz、交换子范数界、极化和二次方程解法是成熟工具，不另认领为新理论。

[Kapustin，arXiv:1303.6917v4，Axioms 4–7、Theorem 3.1](https://arxiv.org/html/1303.6917v4)从 Lie 观测量及精确组合前件出发；[Moldoveanu，arXiv:1303.3935，式 (6)–(9)](https://arxiv.org/html/1303.3935)使用精确运算复合和额外单位条件；[Barnum–Wilce，arXiv:1202.4513v2，引言 Hanche-Olsen 定理及 Proposition 1](https://arxiv.org/html/1202.4513v2)使用既有 Jordan／量子比特结构；[Niestegge，arXiv:1402.0158v2，§5 Definition 1](https://arxiv.org/html/1402.0158v2)的动力对应已包含 $D_aa=0$。这些文献供应精确复合性和表示路线的背景，不在本节中供应一个交替前、任意实际 $M,\Gamma$ 的完整残差估计。本节的本仓推导归属不主张文献原创优先权。

第 1–4 节的 C98 证书作用于另一带标签报告域；$\Theta$ 与这里的 $\epsilon$ 没有被等同。原卷 C99–C102 的精确重构、活动伙伴和过程结论，以及 C103 的接续标尺、C104 的谱滤波标定，分别使用其自身全输入恒等式、对象存在或实际过程前件；它们不给出未证明的带噪推论。[四路径全记录恢复界续卷 I 第 34、36 节](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md#34-the-exact-small-distance-envelope-and-all-original-minimizing-pairs)的初始包络及固定反馈比较则作用于已经给定的归一化效果与同一个实际 $U$，不是 (5.2) 的代数残差；未给出从这些效果和概率读数到 (5.1)–(5.3) 的实际对应时，不能将其界代入 (6.2)。

本节对 $\epsilon>0$ 只控制局部自缺陷、对称双线性缺陷、单位标签生成元及 (6.8) 的实际模板差。它不推出 Jacobi 稳定性、共同标尺稳定性、近邻复 $C^*$ 重构，也不把小残差的整体自动当成一个精确导子对象继续套用第三方重构。有限维、精确局部导子、乘积正内积及全部模作用与保值条件作用仍是明列前件；任意非因子化联合内积需要另一个估计。测量不确定度、完整操作供应、具体动力学、无限维极限和物理实现均没有由本证书补齐。本文陈述与解析证明不作 Lean／kernel 验证或最优性主张。

## 追加锚（本行以下为增补区）
