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
