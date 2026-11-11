# 任意标记的五点正性桥梁与仿射复几何

## 1. 原始关系与有限正性判据

**定义 1.1（未固定单位的比较来源）。**设 $M$ 带二元运算 $\cdot$ 和双侧单位 $1$，不要求结合、交换、消去或逆元。给定完全任意的 $U:M\to M$，以及处处有限的 $c:M^2\to[0,\infty)$，满足 $c(a,a)=0$。原始配方的次序、括号、来源和记录均保留。考虑全四变量关系

$$
\sum_{k=0}^2c(a\cdot U^ku,b\cdot U^kv)=3c(a,b)+3c(u,v).
\tag{R}
$$

不将 $U1=1$、对称性、距离、拓扑或 Hilbert 几何包含在这个定义中。

**定义 1.2（五点负型）。**条件 $\mathrm{N}_5$ 指 $c$ 对称，且对任意 $m\le5$、标签 $x_1,\ldots,x_m\in M$ 和实系数 $\alpha_i$，都有

$$
\sum_i\alpha_i=0\quad\Longrightarrow\quad
\sum_{i,j}\alpha_i\alpha_jc(x_i,x_j)\le0.
\tag{1.1}
$$

标签可重复；这是所有至多五点配置的普遍条件，不是选定有限样本上的检查。条件 $\mathrm{N}_{\rm fin}$ 指同一条件对每个有限 $m$ 成立。

**定理 1.3（局部到整体的完整等价）。**定义 1.1 与 (R) 下，以下四项等价：

1. $\mathrm{N}_5$；
2. 第 2 节定义的每个乘法四点缺陷均属于双侧根空间；
3. 存在复 Hilbert 空间 $H$ 和 $F:M\to H$，满足

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad
F(Ua)=\omega Fa+t,\quad t=F(U1),\qquad
c(a,b)=\|Fa-Fb\|^2,
\quad \omega=-\tfrac12+i\tfrac{\sqrt3}{2};
\tag{1.2}
$$

4. $\mathrm{N}_{\rm fin}$。

最小表示 $H=\overline{\operatorname{span}_{\mathbb C}F(M)}$ 唯一到唯一的保标签酉同构。定理不声称 (R) 单独推出 $\mathrm{N}_5$。

## 2. 在不定号自由空间中定位缺陷

**引理 2.1（无固定锚的恒等式）。**令 $p_k=U^k1$、$q(a)=c(a,1)$、$r(a)=c(1,a)$。在自由实差空间 $E=\operatorname{span}_{\mathbb R}\{e_a=\delta_a-\delta_1\}$ 上置

$$
B(e_a,e_b)=\frac{q(a)+r(b)-c(a,b)}2,\qquad
\mathcal N=\{z:B(z,E)=B(E,z)=0\}.
\tag{2.1}
$$

此刻 $B$ 可非对称、不定号。映射 $Se_a=e_{Ua}-e_{p_1}$ 保持 $B$。定义

$$
X_k(a,u)=e_{a\cdot U^ku}-e_{p_k},\qquad
D_k(a,u)=e_{a\cdot U^ku}-e_{a\cdot p_k}-e_{U^ku}+e_{p_k}.
\tag{2.2}
$$

则

$$
\sum_k B(X_k(a,u),X_k(b,v))=3B(e_a,e_b)+3B(e_u,e_v),
\tag{2.3}
$$

$$
\sum_k B(D_k(a,u),D_k(b,v))=0.
\tag{2.4}
$$

**证明。**令 $s_n=c(U^nu,U^nv)$。(R) 的背景取 $(1,1)$ 得 $s_{n+1}+s_{n+2}=2s_n$。解为 $A+B_0(-2)^n$；全部整数 $n\ge0$ 上的有限非负性迫 $B_0=0$，故 $c(Uu,Uv)=c(u,v)$。四点极化公式

$$
2B(e_x-e_s,e_y-e_t)=-c(x,y)+c(x,t)+c(s,y)-c(s,t)
\tag{2.5}
$$

随后给 $B(Sx,Sy)=B(x,y)$。对 (2.5) 取 $x=a\cdot U^ku,s=p_k,y=b\cdot U^kv,t=p_k$ 并求和，依次使用 (R) 的输入 $(a,b,u,v)$、$(a,1,u,1)$、$(1,b,1,v)$ 及 $(1,1,1,1)$，得 (2.3)。对其两端分别在输入矩形 $(a,u),(a,1),(1,u),(1,1)$ 上取交替和，所有只依赖单个输入轴的项消失，得 (2.4)。全程未重括号。

**定义 2.2（乘法四点缺陷与完整行列等价）。**置

$$
D(a,u)=D_0(a,u)=e_{a\cdot u}-e_a-e_u.
$$

记 $\mathrm{BR}$ 为 $D(a,u)\in\mathcal N$ 对全部 $a,u$ 成立。记 $x\approx y$ 为对每个 $z$ 都同时有 $c(x,z)=c(y,z)$、$c(z,x)=c(z,y)$。

**引理 2.3（根空间恰好编码完整行列）。**$x\approx y$ 当且仅当 $e_x-e_y\in\mathcal N$。

**证明。**正向代入 (2.1)。反向令 $w=e_x-e_y\in\mathcal N$，则 $0=B(w,w)=(c(x,y)+c(y,x))/2$。非负性给两个比较均为零。由 $B(w,e_y)=B(e_y,w)=0$ 得 $q(x)=q(y),r(x)=r(y)$，再与任意 $e_z$ 双向配对，给完整行列相等。这里不使用未经证明的零比较传递性。

**命题 2.4（五点条件消去全部乘法缺陷）。**$\mathrm{N}_5$ 蕴涵 $\mathrm{BR}$。

**证明。**对称性使 $B$ 对称。总质量为零、支撑至多五点的自由向量 $w=\sum_i\alpha_i\delta_{x_i}$ 满足

$$
B(w,w)=-\frac12\sum_{i,j}\alpha_i\alpha_jc(x_i,x_j)\ge0.
$$

每个 $D_k(a,u)$ 支撑至多四点，故 (2.4) 取相同矩形后为三个非负数之和等于零，特别 $B(D(a,u),D(a,u))=0$。对任意标签 $z$ 和实数 $\lambda$，向量 $D(a,u)+\lambda e_z$ 支撑于 $\{a\cdot u,a,u,1,z\}$，故

$$
0\le B(D+\lambda e_z,D+\lambda e_z)
=2\lambda B(D,e_z)+\lambda^2B(e_z,e_z).
\tag{2.6}
$$

有限系数的一次项若不为零，取符号相反且足够小的 $\lambda$ 即矛盾。因此 $B(D,e_z)=0$；对称性给反向配对也为零。任意 $z$ 张成 $E$，所以 $D\in\mathcal N$。此证明不主张五是最小点数。

## 3. 先证明根稳定性，再取得仿射三相作用

**命题 3.1（乘法根性迫出中心化三相和）。**在 (R) 下，$\mathrm{BR}$ 蕴涵 $(I+S+S^2)E\subseteq\mathcal N$。

**证明。**由 $S^ke_u=e_{U^ku}-e_{p_k}$，有 $X_k(a,u)-e_a-S^ke_u=D(a,U^ku)\in\mathcal N$。代入 (2.3)，用 $S$ 保持 $B$ 消去纯背景项和纯增量项，得到

$$
B(e_a,(I+S+S^2)e_v)+B((I+S+S^2)e_u,e_b)=0.
$$

分别令 $u=1$、$a=1$，两种配对都为零，结论成立。此时尚未在商上使用 $S$。

**命题 3.2（完整三次周期与合法商算子）。**若 $(I+S+S^2)E\subseteq\mathcal N$，则 $U^3a\approx a$ 对全部 $a$ 成立，且 $S\mathcal N\subseteq\mathcal N$。商 $V=E/\mathcal N$ 上的诱导算子 $R_0$ 满足

$$
R_0^2+R_0+I=0,\quad R_0^3=I,\quad
B(R_0x,R_0y)=B(x,y).
\tag{3.1}
$$

**证明。**记 $L_a=(I+S+S^2)e_a=e_a+e_{Ua}+e_{U^2a}-e_{p_1}-e_{p_2}$。则 $L_{p_1}=e_{p_3}$，且 $L_{Ua}-L_a=e_{U^3a}-e_a$，所以这些向量均在 $\mathcal N$。引理 2.3 给完整行列周期，且 $S^3x-x\in\mathcal N$ 对所有 $x$ 成立。对 $n\in\mathcal N,y\in E$，

$$
B(Sn,y)=B(Sn,S^3y)=B(n,S^2y)=0,
$$

反向配对同理。根稳定性因此成立，$S$ 才能下降。中心化三相和给 (3.1)，不要求原始 $U$ 满射或三周期。

## 4. 可见群、平移不变性与完整表示

**证明定理 1.3 的 $2\Rightarrow3$。**记 $\beta(a)=[e_a]\in V$，$A=\beta(M)$，$t=\beta(p_1)$。由 $\mathrm{BR}$ 与命题 3.2，

$$
\beta(a\cdot b)=\beta(a)+\beta(b),\qquad
\beta(Ua)=R_0\beta(a)+t.
\tag{4.1}
$$

此时 $A$ 初看只是加法幺半群。取实际有限纠偏配方

$$
V_U(a)=U(a\cdot U^21).
\tag{4.2}
$$

因 $\beta(U^21)=(I+R_0)t$，有 $\beta(V_Ua)=R_0\beta(a)$。再由 $R_0+R_0^2=-I$，

$$
\beta(V_Ua\cdot V_U^2a)=-\beta(a).
\tag{4.3}
$$

所以 $A$ 是实向量空间中的加法群，$R_0$ 是其三周期自同构。原始配方的逆元、结合和交换均未被假设或由此宣告。

引理 2.3 使整个有向核下降为 $A$ 上的 $C$。固定 $x,y\in A$，令 $h(z)=C(x+z,y+z)$、$m=\inf_Ah\ge0$。(R) 对同一增量 $w$ 的两端给

$$
\sum_{k=0}^2h(z+R_0^kw+t_k)=3h(z),\quad
t_0=0,\ t_1=t,\ t_2=(I+R_0)t.
$$

每项至少为 $m$，故 $h(z+w)-m\le3(h(z)-m)$。对任意目标 $\zeta$ 取 $w=\zeta-z$，再取 $h(z)\downarrow m$，得 $h(\zeta)=m$。因此 $C$ 共同平移不变，且

$$
C(x,y)=f(x-y),\quad f\ge0,\quad f(0)=0,\quad
f(R_0x)=f(x),\quad
\sum_kf(x+R_0^ky)=3f(x)+3f(y).
\tag{4.4}
$$

此时可直接应用《无结合律的双端三相比较：可见代数与复几何共同生成》第 4 节的群上推导：奇部的 $8^n$ 缩放被偶部的 $4^n$ 上界排除；$L=R_0-R_0^2$ 使平行四边形缺陷同时按 $9$ 与 $3$ 缩放，故该缺陷为零。交换群上的经典极化给对称双可加型；有限 Gram 正性、实标量扩张、零空间商和完成给实 Hilbert 表示。$J=(2R_0+I)/\sqrt3$ 给复结构，得到 (1.2)。这里仅在群结构已经合法取得后复用该推导。

**证明定理 1.3 的其余蕴涵与唯一性。**$1\Rightarrow2$ 为命题 2.4。若有 (1.2)，对实系数 $\sum_i\alpha_i=0$，

$$
\sum_{i,j}\alpha_i\alpha_jc(x_i,x_j)
=-2\left\|\sum_i\alpha_iF(x_i)\right\|^2\le0,
$$

且 $c$ 对称，故 $3\Rightarrow4\Rightarrow1$。反向表示推出 (R)，直接展开 $\sum_k\|X+\omega^kY\|^2$。在任意表示中，(4.2) 满足 $F(V_Ua)=\omega Fa$，因此第一变量线性的全部复 Gram 由原比较恢复为

$$
\langle Fa,Fb\rangle
=\frac{q(a)+q(b)-c(a,b)}2
+\frac{i}{2\sqrt3}\bigl(c(V_Ua,b)-c(a,V_Ub)\bigr).
\tag{4.5}
$$

相同 Gram 给最小闭复张成空间之间唯一的保标签酉同构。证毕。

## 5. 有限正提升与两种原点

**命题 5.1（不动可见单位的有限纠偏）。**在定理 1.3 的等价条件下，$a\sim b\iff c(a,b)=0$ 是兼容乘法和标记的等价关系，$M/{\sim}\cong F(M)$ 是无挠的 $\mathbb Z[\omega]$-模。原标记是 $x\mapsto\omega x+t$；纠偏配方 $V_U$ 是 $x\mapsto\omega x$。特别 $U^3a\sim a$，但不要求原始对象 $U^31=1$。

**证明。**平方距离使零比较恰为相同向量；乘法与标记分别由加法和仿射映射表示。式 (4.2)–(4.3) 给取负与 $\omega$ 封闭。Hilbert 加法群无挠。

**命题 5.2（有限三历史正提升）。**对有限标签 $a_i$ 与整数 $z_{i,k}$，令 $m_i=\max(0,-z_{i,0},-z_{i,1},-z_{i,2})$。把各 $V_U^ka_i$ 重复 $z_{i,k}+m_i$ 次，按指定次序和括号聚合，所得 $h$ 满足

$$
F(h)=\sum_{i,k}z_{i,k}\omega^kF(a_i).
$$

**证明。**每次聚合给向量相加，增加的三个方向和为零。原始树不被识别或删除。这只供应有限 Eisenstein 整数系数；任意复缩放与完成中的极限不由此成为实际配方。

**命题 5.3（聚合零点与旋转中心）。**令 $o=t/(1-\omega)$，则 $c(Ua,a)=3\|Fa-o\|^2$，且 $c(U1,1)=0$ 当且仅当 $t=0$。中心 $o$ 未必在实际像 $F(M)$ 中。把坐标平移到 $o$ 后，标记成为纯旋转，但聚合公式变为 $G(a\cdot b)=Ga+Gb+o$，其中 $G=F-o$。

**证明。**$F(Ua)-Fa=(\omega-1)(Fa-o)$，而 $|\omega-1|^2=3$。取 $a=1$ 得单位比较为 $\|t\|^2$。例取 $F(M)=\mathbb Z[\omega],t=1$，则 $o=(2+\omega)/3\notin\mathbb Z[\omega]$。平移后的聚合式直接由加法计算。

**命题 5.4（保留原始树的非零来源）。**取三个叶标签生成的所有有限非空有序满二叉树并添加单位。两非空树的乘法为左右嫁接，单位按双侧单位规则处理。叶权为 $1,\omega,\omega^2$，$F$ 为叶权和，$F1=0$；$\sigma$ 循环叶标签并令 $\sigma1=1$。置 $Ua=\sigma(a)\cdot x_0$、$c(a,b)=|Fa-Fb|^2$。则 (R) 和 $\mathrm{N}_5$ 成立，读数非零无界；原始乘法非结合、非交换，$U1\ne1$ 且 $U^3\ne I$。

**证明。**$F(ab)=Fa+Fb,FUa=\omega Fa+1$，直接由表示恒等式取得结论。每次 $U$ 增加一叶，故原始三次标记不为恒等；不同左右树与括号仍不同。$n$ 个 $x_0$ 的任意指定括号聚合给单位比较 $n^2$。若改为 $Ua=\sigma(a)\cdot((x_0\cdot x_1)\cdot x_2)$，则原始 $U1\ne1$ 仍成立，但 $c(U1,1)=0$，显示该关系条件严格弱于对象等式。

## 6. 三历史事件与实际量子接口

**命题 6.1（全部八事件的强正几何）。**取三个实际历史的像 $v_i=F(h_i)$。对全部 $E\subseteq\{0,1,2\}$ 置 $A(E)=\sum_{i\in E}v_i$、$D(E,F)=\langle A(E),A(F)\rangle$、$\mu(E)=\|A(E)\|^2$。令 $L$ 为八事件对三标签的零一关联矩阵，$G_{ij}=\langle v_i,v_j\rangle$，则 $D_8=LGL^{\mathsf T}\succeq0$，且无三阶干涉。

**证明。**这些都是同一组事件向量的 Gram。平方展开只含单历史项和两历史交叉项。命题 5.4 的树来源实际供应 $v=(1,\omega,2)$；按空集、三个单点、三对、全集排列，质量为 $0,1,1,4,1,9,3,7$。除以总质量 $7$ 仍有事件强度 $9/7$，所以事件强度与同一完整测试中的概率须区分。三方向在振幅平面构成等边结构，不限定物理空间维数。

**定理 6.2（已具表示的完整测试与细过程）。**实际完整有限测试的总核 $c_*$ 和事件核 $c_e$ 各满足定理 1.3 的等价条件，且 $\sum_ec_e=c_*$。则在总核最小空间上有唯一效果 $E_e\ge0$，满足 $\sum_eE_e=I$ 及

$$
c_e(a,b)=\langle Fa-Fb,E_e(Fa-Fb)\rangle.
$$

非零输入差 $x$ 的归一读数为 $\langle x,E_ex\rangle/\|x\|^2$。

另外，输入、输出来源各取定理 1.3 的最小表示，即 $H_{\rm in}=\overline{\operatorname{span}_{\mathbb C}F_{\rm in}(M_{\rm in})}$，输出同理。实际有限细分支 $T_j$ 保持单位，满足全部成对校准 $\sum_jc_{\rm out}(T_ja,T_jb)=c_{\rm in}(a,b)$、逐记录对应，以及纠偏相位条件

$$
c_{\rm out}(T_jV_{U,\rm in}a,V_{U,\rm out}T_ja)=0.
\tag{6.1}
$$

则有唯一复线性 $K_j$，使 $K_jF_{\rm in}a=F_{\rm out}(T_ja)$、$\sum_jK_j^*K_j=I$，并按实际事件分组得到 Kraus 仪器。

**证明。**由 $iFa=(2F(V_Ua)+Fa)/\sqrt3$，可见像的实线性张成与复线性张成相同，因而在最小空间中稠密。$c_e\le c_*$ 使 $Fa\mapsto F_ea$ 在可见像上良定义、可加且范数收缩。清分母与有界延拓给实线性收缩 $L_e$；共同的实际配方 $V_U$ 使其与 $\omega$ 相容，故复线性，取 $E_e=L_e^*L_e$。极化给唯一性与完整性。细过程的直和映射 $a\mapsto\bigoplus_jF_{\rm out}(T_ja)$ 保单位零值及全部距离，实 Gram 延拓给等距；(6.1) 使它复线性。坐标即 $K_j$，等距给归一，任意辅助空间上的 $K_j\otimes I$ 给完全正扩张。这里只构造与细记录相容的数学扩张；实际参考上的过程与之相同仍需参考接口。总核的五点正性在本定理中不替代各事件核所需的表示条件。

**对应 6.3（保留的供应条件）。**聚合加法不等于联合张量。实际联合的可见双可加性、复相位平衡及乘积质量给复张量嵌入，乘积像稠密才给整个联合空间。全效果域上一致、非负、归一、可加的评价在有限维给密度态，无限维还需正规性或相应可数可加。实际可逆、保单位、保全部成对比较并保纠偏相位的过程给酉表示；连续时间和生成元需实际时间接口。历史幅度不是脱离参考的纯射线：$Fa$ 与 $\omega Fa$ 同射线，仍可有 $c(V_Ua,a)=3\|Fa\|^2$。实际非零准备、参考、全效果、联合与时间各有来源；$F1=0$ 不供应非零参考态。这些接口沿用前述续卷第 6 节的条件，仿射场合以 (4.2) 校准相位。

## 7. 原始候选的精确剩余问题

**问题 7.1（非负配平是否自动供应有限正性）。**定义 1.1 与 (R) 是否单独推出 $\mathrm{N}_5$，等价地是否单独推出 $\mathrm{BR}$ 或 (1.2)？本卷的条件等价不回答这一蕴涵。仅要求 $c(U1,1)=0$ 的一般 magma 是否已足以恢复严格相位表示，也不由本卷无条件解决。

**命题 7.2（三个较弱推论不足以替代完整关系）。**同时标记等距、同步三次滑移和界 $c(a\cdot u,b\cdot v)\le3(c(a,b)+c(u,v))$，单独不能推出 $U^31\approx1$。

**证明。**在 $M=\mathbb N$ 的加法来源中，单位为 $0$，取 $Un=n+1,c(n,m)=(n-m)^2$。三个较弱条件分别由平移、同步滑移及 $(x+y)^2\le2(x^2+y^2)$ 成立，而 $c(U^30,0)=9$。它不满足完整 (R)：数值 $a=u=1,b=v=0$ 给左侧 $12$、右侧 $6$。这只排除丢弃完整关系后的推理，不是问题 7.1 的反例。

**对应 7.3（工具与承重范围）。**有限负型的锚核、Gram 商、Hilbert 完成及二次函数极化是经典工具。本卷的承重关系是 (R) 下五点条件与乘法四点缺陷根性、整体负型及仿射表示的等价。群上极化的文献条件与引用沿用前述续卷对应 7.1：Aczél 的交换群结论见 de Place Friis–Stetkær，*On the quadratic functional equation on groups*，DOI 10.5486/pmd.2006.3270，Theorem 1.2；这里只在第 4 节已经得到交换群后使用。没有将局部正性归为原关系的已知后果，也不作文献优先权主张。

## 追加锚（本行以下为增补区）

## 8. 单位轨道根性与完整乘法根性的条件等价

**定义 8.1（单位轨道条件与双向读数）。**沿用定义 1.1、引理 2.1 和定义 2.2 的全部对象与量词。特别，$M$ 仍为任意有双侧单位的 magma，$U$ 任意，$c$ 处处有限、非负且零对角，(R) 对全部 $a,b,u,v$ 成立。置

$$
A_j(a)=D(a,p_j)=e_{a\cdot p_j}-e_a-e_{p_j},\qquad p_j=U^j1.
$$

单位轨道条件 $\mathrm{UC}$ 指

$$
A_j(a)\in\mathcal N\qquad(a\in M,\ j=1,2).
\tag{8.1}
$$

这里的根空间是原自由差空间中完整的双侧根空间。对任意有向核 $d$ 置

$$
\begin{aligned}
H_d(a,u;z)={}&d(a\cdot u,z)-d(a,z)-d(u,z)+d(1,z)\\
&-d(a\cdot u,1)+d(a,1)+d(u,1),
\end{aligned}
\tag{8.2}
$$

并令 $c^{\mathsf T}(x,y)=c(y,x)$。因此 (8.1) 要求每个 $a$、两个 $j$ 及每个读出标签 $z$ 上的两个配对次序，而非某组有限读数或仅自配对。

**定理 8.2（单位轨道根性归约）。**在定义 1.1 与完整关系 (R) 下，

$$
\mathrm{UC}\ \Longleftrightarrow\ \mathrm{BR}
\ \Longleftrightarrow\ \mathrm N_5
\ \Longleftrightarrow\ \mathrm N_{\rm fin}
\ \Longleftrightarrow\ \text{存在满足 (1.2) 的仿射复 Hilbert 表示}.
\tag{8.3}
$$

其中 $\mathrm{UC}$ 也等价于

$$
H_c(a,p_j;z)=H_{c^{\mathsf T}}(a,p_j;z)=0
\qquad(a,z\in M,\ j=1,2).
\tag{8.4}
$$

**证明。**$\mathrm{BR}\Rightarrow\mathrm{UC}$ 是定义 2.2 在 $u=p_1,p_2$ 的特化。(8.4) 与 (8.1) 的等价由定理 8.3 的读数恒等式给出。反向 $\mathrm{UC}\Rightarrow\mathrm{BR}$ 的证明依次为定理 8.3 的合法相位下降、第 9 节的仿射字符分解、第 10 节的成对历史与完整核下降，以及第 11 节在既有群上结论处的应用。其余等价直接使用定理 1.3。这里没有从 (R) 单独断言 (8.1)。

**定理 8.3（双向读数与相位下降的确切前件）。**在定义 1.1 与 (R) 下，令 $L=I+S+S^2$，则

$$
\begin{aligned}
H_c(a,u;z)&=-2B(D(a,u),e_z),\\
H_{c^{\mathsf T}}(a,u;z)&=-2B(e_z,D(a,u)),
\end{aligned}
\tag{8.5}
$$

且

$$
\begin{aligned}
B(Le_u,e_z)&=-\sum_{k=0}^2B(S^ke_u,A_k(z)),\\
B(e_z,Le_u)&=-\sum_{k=0}^2B(A_k(z),S^ke_u).
\end{aligned}
\tag{8.6}
$$

这里 $A_0(z)=D(z,1)=0$。特别，$\mathrm{UC}$ 蕴涵 $LE\subseteq\mathcal N$，从而命题 3.2 的全部结论成立。

**证明。**展开 (2.1) 中的 $B(D(a,u),e_z)$，与 $r(z)$ 相乘的系数为 $1-1-1=-1$，所得正是 (8.5) 的第一式。转置核仍满足 (R)：把其四变量依次换为 $b,a,v,u$ 即得原式；其锚定双线性型为 $B^{\mathsf T}$，故第二式同样成立。由于 $e_z$ 张成 $E$，(8.5) 给 (8.4) 与 (8.1) 的双向等价。

在自由空间中直接有

$$
X_k(1,u)=S^ke_u,\qquad X_k(z,1)=e_z+A_k(z).
\tag{8.7}
$$

将这两个输入代入 (2.3)，右侧为零；交换两个输入再代入一次，得到 (8.6)。更一般地，在 (2.3) 的一个输入上取矩形 $(a,u)-(a,1)-(1,u)+(1,1)$ 的交替和，得到

$$
\begin{aligned}
\sum_{k=0}^2 B(D_k(a,u),X_k(b,v))&=0,\\
\sum_{k=0}^2 B(X_k(b,v),D_k(a,u))&=0
\end{aligned}
\tag{8.8}
$$

对全部 $a,u,b,v$ 成立。交替和中的左侧向量恰为 (2.2) 的 $D_k$，右侧两个只依赖单轴的项各自抵消。

若有 $\mathrm{UC}$，(8.6) 的每一项均因双侧根性为零。因此 $LE\subseteq\mathcal N$。现在才应用命题 3.2，得到 $S\mathcal N\subseteq\mathcal N$，并在 $V=E/\mathcal N$ 上取得可逆算子 $R$，满足

$$
R^2+R+I=0,\qquad R^3=I,\qquad B(Rx,Ry)=B(x,y).
\tag{8.9}
$$

此后仍以 $B$ 表示商上的双线性型。它只在两个次序共同意义下非退化：若 $B(x,\beta(z))=B(\beta(z),x)=0$ 对全部 $z$ 成立，则 $x=0$，其中 $\beta(a)=[e_a]$。在此下降之前未在商上使用 $S$，也未对原始 $U$ 要求满射或对象层面的三周期。

## 9. 保留仿射偏移的三字符分解

**定理 9.1（仿射分解与等向缺陷）。**在定理 8.2 的前件和 $\mathrm{UC}$ 下，令 $t_k=\beta(p_k)$、$t=t_1$，并置

$$
T(a,u)=\beta(a\cdot u)-\beta(a)-\beta(u),\qquad
W=\operatorname{span}_{\mathbb R}\{T(a,u):a,u\in M\}.
$$

则 $t_0=0$、$t_2=(I+R)t$，且

$$
\beta(a\cdot U^ku)
=\beta(a)+R^k\beta(u)+t_k+R^{-k}T(a,u)
\qquad(k=0,1,2).
\tag{9.1}
$$

此外，

$$
B(W,W)=0,\qquad T(a,Uu)=R^2T(a,u),\qquad RW=W.
\tag{9.2}
$$

**证明。**由 $S$ 的定义和合法下降，

$$
\beta(Ua)=R\beta(a)+t,\qquad
\beta(U^ka)=R^k\beta(a)+t_k\quad(k=0,1,2).
\tag{9.3}
$$

$\mathrm{UC}$ 给 $\beta(a\cdot p_k)=\beta(a)+t_k$，也包括 $k=0$。记

$$
\xi_k(a,u)=[X_k(a,u)]=\beta(a\cdot U^ku)-t_k.
$$

于是 $\xi_k(b,1)=\beta(b)$、$\xi_k(1,v)=R^k\beta(v)$。(2.3) 先与输入 $(b,1)$ 配对，再反向配对，两式共同给

$$
\sum_{k=0}^2\xi_k(a,u)=3\beta(a).
\tag{9.4}
$$

这里使用的是商上共同非退化性，并未使用单侧非退化性。再与 $(1,v)$ 按两个次序配对，并用 (8.9) 把 $R^k$ 转到另一变量，得到

$$
\sum_{k=0}^2R^{-k}\xi_k(a,u)=3\beta(u).
\tag{9.5}
$$

这正是《无结合律的双端三相比较：可见代数与复几何共同生成》[第 2 节](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#2-在非对称非正定空间中保留全部缺陷)式 (2.8)–(2.10) 所用的三字符系统，但此处未知量为中心化的 $\xi_k$，不是未减去仿射偏移的 $\beta(a\cdot U^ku)$。具体地，令

$$
d_k=\xi_k(a,u)-\beta(a)-R^k\beta(u).
$$

则 $d_0=T(a,u)$，且 (9.4)–(9.5) 给

$$
d_0+d_1+d_2=0,\qquad d_0+R^2d_1+Rd_2=0.
$$

消去 $d_2$ 后，$(R^2-R)d_1=(R-I)d_0$；由 $(R^2-R)^2=-3I$，该算子可逆，而 $d_1=R^2d_0$ 满足此式。因此 $d_2=Rd_0$，即 (9.1)。

把 $\xi_k(a,u)=\beta(a)+R^k\beta(u)+R^{-k}T(a,u)$ 代回 (2.3)。纯背景项为 $3B(\beta(a),\beta(b))$，纯增量项为 $3B(\beta(u),\beta(v))$；所有不同字符的交叉项为零。例如

$$
\sum_k B(R^k\beta(u),R^{-k}T(b,v))
=B\left(\beta(u),\sum_kR^{-2k}T(b,v)\right)=0.
$$

其他交叉项同样由 $I+R+R^2=0$ 消去。剩余式为

$$
3B(T(a,u),T(b,v))=0\qquad(a,u,b,v\in M).
$$

所有有序缺陷对均在量词内，故 $B(W,W)=0$。取 (9.1) 的 $k=1$ 并减去 $\beta(a)+\beta(Uu)$，得 $T(a,Uu)=R^2T(a,u)$，所以 $R^2W\subseteq W$。再作用 $R^2$ 得 $RW\subseteq W$；结合 $R^3=I$ 即得 $RW=W$。这个结论只是 $W$ 的等向性，尚不蕴涵 $W$ 为根空间。

**定理 9.2（纠偏配方生成商像中的负元）。**在定理 9.1 的条件下，令 $\gamma(a)=\beta(a)\bmod W$，$A=\gamma(M)\subseteq V/W$，$\rho$ 为 $R$ 诱导的算子，$\tau=\gamma(p_1)$。则 $A$ 为加法群，$\rho$ 限制为 $A$ 的自同构，且

$$
\gamma(a\cdot b)=\gamma(a)+\gamma(b),\qquad
\gamma(Ua)=\rho\gamma(a)+\tau,\qquad I+\rho+\rho^2=0.
\tag{9.6}
$$

**证明。**$RW=W$ 使 $\rho$ 合法；$T$ 的定义使乘法像为加法，故 $A$ 初为加法幺半群，零元为 $\gamma(1)$。沿用 (4.2) 的原始括号，置

$$
V_U(a)=U(a\cdot p_2),\qquad V_U^2(a)=V_U(V_U(a)).
\tag{9.7}
$$

因 $\gamma(p_2)=(I+\rho)\tau$，有

$$
\gamma(V_U(a))
=\rho\bigl(\gamma(a)+(I+\rho)\tau\bigr)+\tau
=\rho\gamma(a).
$$

因此指定的二元项

$$
d_a=V_U(a)\cdot V_U^2(a)
\tag{9.8}
$$

满足 $\gamma(d_a)=(\rho+\rho^2)\gamma(a)=-\gamma(a)$。每个像元素的负元都在 $A$ 中，故 $A$ 为加法群。$V_U$ 及其二次迭代又分别实现 $\rho$ 和 $\rho^2=\rho^{-1}$，所以 $\rho A=A$。这里只在向量商的像中取得群；未改变 $M$ 的任何次序、括号或运算律。

## 10. 成对有限历史与完整有向核的下降

**定理 10.1（同纤维的统一双向界）。**在定理 9.2 的条件下，置

$$
K=\{(a,b)\in M^2:\gamma(a)=\gamma(b)\},\qquad
N_0=\{u\in M:\gamma(u)=0\}.
$$

对每个 $(a,b)\in K$，令 $w=\beta(a)-\beta(b)$。则 $c(a,b)=c(b,a)=0$，且对每个 $z\in M$，

$$
|B(w,\beta(z))|\le\frac32r(z),\qquad
|B(\beta(z),w)|\le\frac32q(z).
\tag{10.1}
$$

**证明。**$w\in W$，而由 (2.1)

$$
0=B(w,w)=\frac{c(a,b)+c(b,a)}2.
$$

两个实际比较非负，故都为零。这里没有从 $B(w,w)=0$ 推出根性。$c(a,b)=0$ 与 (2.1) 给 $q(a)-q(b)=2B(w,\beta(b))$；同理由 $c(b,a)=0$ 得 $r(a)-r(b)=2B(\beta(b),w)$。于是

$$
\begin{aligned}
c(a,b\cdot z)-c(b,b\cdot z)
&=-2B(w,\beta(z)),\\
c(b\cdot z,a)-c(b\cdot z,b)
&=-2B(\beta(z),w).
\end{aligned}
\tag{10.2}
$$

计算中使用 $\beta(b\cdot z)=\beta(b)+\beta(z)+T(b,z)$，而 $B(w,T(b,z))=B(T(b,z),w)=0$ 由 (9.2) 给出。

(R) 的 $k=0$ 项与非负性对全部四变量给

$$
0\le c(x\cdot u,y\cdot v)\le3\bigl(c(x,y)+c(u,v)\bigr).
\tag{10.3}
$$

以 $(x,y,u,v)=(a,b,1,z)$ 和 $(b,b,1,z)$ 代入，(10.2) 第一行的两个读数均在 $[0,3r(z)]$。以 $(b,a,z,1)$ 和 $(b,b,z,1)$ 代入，第二行的两个读数均在 $[0,3q(z)]$。这给 (10.1)，并且界不依赖于同纤维对 $(a,b)$。它是前述续卷第 3 节式 (3.2) 的同一实际比较界，适用于此处仍带仿射偏移的纤维。

**定理 10.2（成对历史消去零纤维残余）。**在上述条件下，$u\in N_0$ 蕴涵 $\beta(u)=0$。

**证明。**固定任意 $z\in M$，分别考虑实线性泛函和对应常数

$$
\begin{aligned}
\alpha(x)=B(x,\beta(z)),&\qquad C=\tfrac32r(z),\\
\alpha(x)=B(\beta(z),x),&\qquad C=\tfrac32q(z).
\end{aligned}
\tag{10.4}
$$

以下论证对两种选择各作一次。令

$$
J=\frac{2R+I}{\sqrt3},\qquad
\ell=\alpha-i\alpha J,\qquad
\omega=-\frac12+i\frac{\sqrt3}{2}.
$$

由 (8.9)，$J^2=-I$ 且 $\ell R=\omega\ell$。这只是代数复结构，不要求 $B$ 为正或对称。若 $(a,b)\in K$，则 $(Ua,Ub)\in K$，且

$$
R(\beta(a)-\beta(b))=\beta(Ua)-\beta(Ub).
$$

因此 (10.1) 同时界住 $|\alpha(w)|$ 和 $|\alpha(Rw)|$，均不超过 $C$。从而

$$
|\ell(w)|^2
=\alpha(w)^2+\frac{(2\alpha(Rw)+\alpha(w))^2}{3}
\le4C^2\qquad((a,b)\in K).
\tag{10.5}
$$

特别，此界并未要求单条零纤维历史在 $U$ 下保持零纤维；仿射项 $\tau$ 可以非零。

固定 $u\in N_0$。对每个整数 $n\ge0$，以 $\mathcal I_n=\{0,1,2\}^n$ 为有限指标集。每个词 $(k_1,\ldots,k_n)$ 索引两条指定的左括号递推：

$$
\begin{aligned}
x_0=y_0&=1,\\
x_j&=x_{j-1}\cdot U^{k_j}u,\\
y_j&=y_{j-1}\cdot p_{k_j}\qquad(1\le j\le n).
\end{aligned}
\tag{10.6}
$$

两条递推分别保留；不将 $x_j$ 与 $y_j$ 认作同一原始对象。由 $\gamma(u)=0$ 和 (9.6)，$\gamma(U^ku)=\gamma(p_k)$，故每一步都有 $\gamma(x_j)=\gamma(y_j)$。因此这些成对项全属于 $K$。

设某节点的对为 $(x,y)$，差为 $w=\beta(x)-\beta(y)$。由 (9.1) 与 $\mathrm{UC}$，其 $k$ 子节点的差恰为

$$
\begin{aligned}
&\beta(x\cdot U^ku)-\beta(y\cdot p_k)\\
&\quad=w+R^k\beta(u)+R^{-k}T(x,u).
\end{aligned}
\tag{10.7}
$$

这里两个 $t_k$ 相减消失，未将任何单条历史的仿射偏移设为零。令 $Z=\ell(w)$、$A_u=\ell(\beta(u))$、$D_x=\ell(T(x,u))$；三个子值为

$$
Z+\omega^kA_u+\omega^{-k}D_x\qquad(k=0,1,2).
$$

有限三字符正交给出确切恒等式

$$
\frac13\sum_{k=0}^2|Z+\omega^kA_u+\omega^{-k}D_x|^2
=|Z|^2+|A_u|^2+|D_x|^2.
\tag{10.8}
$$

这是前述续卷第 3 节式 (3.4) 的标量平方恒等式；此处它作用于成对差 (10.7)。以深度 $n$ 的全部词作有限平均，记

$$
E_n=3^{-n}\sum_{\mathcal I_n}|\ell(\beta(x_n)-\beta(y_n))|^2.
$$

根节点差为零，且 (10.8) 逐层给 $E_{n+1}\ge E_n+|A_u|^2$。于是

$$
n|A_u|^2\le E_n\le4C^2\qquad(n\ge0),
\tag{10.9}
$$

右侧由每个词上的 (10.5) 得到。任意深度的有限恒等式已经迫使 $A_u=0$。取实部得 $\alpha(\beta(u))=0$；对 (10.4) 的两种配对和任意 $z$ 重复，商上共同非退化性给 $\beta(u)=0$。

$\mathcal I_n$ 只是有限 magma 项的证明索引；论证没有引入概率律、无限随机历史或任何对原事件空间的替换。

**定理 10.3（整个纤维与整个有向核下降）。**在上述条件下，

$$
\gamma(a)=\gamma(b)\quad\Longrightarrow\quad\beta(a)=\beta(b)
\quad\Longrightarrow\quad a\approx b.
\tag{10.10}
$$

因此有唯一的 $C:A^2\to[0,\infty)$，满足 $c(a,b)=C(\gamma(a),\gamma(b))$；它处处有限、零对角，并在加法群 $A$ 上保留完整 (R)，标记为 $x\mapsto\rho x+\tau$。

**证明。**固定 $z$ 和 (10.4) 的任一实泛函。对 $(a,b)\in K$，令

$$
h(a,b)=\alpha(\beta(a)-\beta(b)),\qquad
M_\alpha=\sup_{(a,b)\in K}|h(a,b)|.
$$

由 (10.1)，$0\le M_\alpha\le C<\infty$。因 $\beta(a\cdot U^kd)=\xi_k(a,d)+t_k$，(9.4) 给

$$
\sum_{k=0}^2 h(a\cdot U^kd,b\cdot U^kd)=3h(a,b).
\tag{10.11}
$$

这只在两个背景相减后使用；两边共有的 $\sum_kt_k$ 恰好抵消。所有子对仍在 $K$，因为其 $\gamma$ 差等于 $\gamma(a)-\gamma(b)$。

对给定 $(a,b)\in K$ 选定 (9.8) 的实际括号项 $d=d_a$。由 $\gamma(d)=-\gamma(a)=-\gamma(b)$，$a\cdot d$ 与 $b\cdot d$ 均在 $N_0$。定理 10.2 使 (10.11) 的 $k=0$ 项为零，故

$$
|h(a,b)|\le\frac23M_\alpha.
$$

在整个 $K$ 上取上确界，得到 $M_\alpha\le2M_\alpha/3$，因其有限，必为零。两个配对次序对每个 $z$ 都为零，共同非退化性给 $\beta(a)=\beta(b)$。这等价于 $e_a-e_b\in\mathcal N$，引理 2.3 随即给全部行、全部列的相等，而非只给 $c(a,b)=0$。

定义 $C(\gamma(a),\gamma(b))=c(a,b)$；完整行列相等使其与两个代表元的选择无关。$\gamma$ 满到 $A$，故任意四个群元素都可由原四标签代表。由 (9.6) 及 $\gamma(U^ku)=\rho^k\gamma(u)+\tau_k$，其中

$$
\tau_0=0,\quad\tau_1=\tau,\quad\tau_2=(I+\rho)\tau,
$$

原 (R) 正好下降为

$$
\sum_{k=0}^2 C(x+\rho^ks+\tau_k,y+\rho^kt+\tau_k)
=3C(x,y)+3C(s,t)\qquad(x,y,s,t\in A).
\tag{10.12}
$$

没有把核预先对称化，也没有只下降其零对角或某个标量投影。

## 11. 在既有群上结论处闭合条件归约

**证明定理 8.2 的 $\mathrm{UC}\Rightarrow\mathrm{BR}$。**第 8–10 节已取得加法群 $A$、其自同构 $\rho$、$I+\rho+\rho^2=0$，以及处处有限非负、零对角的完整有向核 $C$，满足 (10.12)。这正是本卷第 4 节共同平移不变性论证的群入口：该论证只使用这些群上条件，不再要求原始标签满足结合律或 $U1=1$。具体对应为第 4 节的群 $A$、算子 $R_0$、偏移 $t_k$ 和核 $C$ 分别取此处的 $A,\rho,\tau_k,C$。因此直接复用该节的下确界论证，得到共同平移不变性，并写成

$$
\begin{aligned}
C(x,y)&=f(x-y),& f&:A\to[0,\infty),& f(0)&=0,\\
f(\rho x)&=f(x),&&&
\sum_{k=0}^2f(x+\rho^ky)&=3f(x)+3f(y).
\end{aligned}
\tag{11.1}
$$

这里相位不变性的前件也满足：引理 2.1 给原核同时标记等距，下降后即 $C(\rho x+\tau,\rho y+\tau)=C(x,y)$；共同平移不变性消去 $\tau$。

随后直接应用《无结合律的双端三相比较：可见代数与复几何共同生成》[第 4 节](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#4-三相缺陷恒等式直接给出平方几何)式 (4.1) 之后的群上推导。其输入是交换加法群、满足 $I+\rho+\rho^2=0$ 的自同构、以及满足 (11.1) 的有限非负函数；这些输入已经逐一取得。该推导提供偶性、平行四边形律、对称双可加极化、有限 Gram 正性、实标量扩张、零空间商和 Hilbert 完成，因而有可加映射 $F_0:A\to H$，满足

$$
f(x)=\|F_0x\|^2,\qquad F_0(\rho x)=\omega F_0x.
$$

所用交换群极化结论的精确文献前件为：定义域 $G$ 是交换群，值群 $H_0$ 是交换群且每个 $h\in H_0$ 的方程 $2x=h$ 有唯一解，函数满足

$$
f(xy)+f(xy^{-1})=2f(x)+2f(y).
\tag{11.2}
$$

这是 Peter de Place Friis、Henrik Stetkær，*On the quadratic functional equation on groups*，Publ. Math. Debrecen 69/1–2，65–93，[DOI 10.5486/pmd.2006.3270](https://doi.org/10.5486/pmd.2006.3270)，第 65–67 页 Theorem 1.2（归于 Aczél）的条件；亦见前述续卷对应 7.1 和本卷对应 7.3。此处 $G=(A,+)$ 已为交换群，$H_0=(\mathbb R,+)$ 满足唯一二可除性，(11.2) 为上述既有群上推导所得的平行四边形律，$xy^{-1}$ 对应 $x-y$。它没有被用于原始 magma，也不把非负性单独当作极化的前件。极化、Gram 与完成均沿用该既有推导。

令 $F=F_0\gamma$。由 (9.6)、(10.12) 和 (11.1)，

$$
F1=0,\quad F(a\cdot b)=Fa+Fb,\quad
F(Ua)=\omega Fa+F(p_1),\quad c(a,b)=\|Fa-Fb\|^2.
$$

所以取得定理 1.3 的第三项，即原来的仿射表示 (1.2)。定理 1.3 给 $\mathrm N_5$ 与 $\mathrm{BR}$，完成 $\mathrm{UC}\Rightarrow\mathrm{BR}$，从而完成 (8.3) 的证明。这里复用的群上极化为上述文献所载结论（literature-attested），其余群上二次函数、Gram 与完成步骤沿用所引第 4 节。本归约为本仓推导的条件命题（repo-derived）：单位轨道的完整双侧根性已足以推出全部乘法缺陷的根性，尤其包含带仿射偏移的成对历史传递；不主张文献优先权。

**问题 11.1（归约后的普遍迫出问题）。**在定义 1.1 与 (R) 下，是否对每个 $a,z\in M$ 和 $j=1,2$ 都有 (8.4)？由定理 8.2，此问题与问题 7.1 的 $\mathrm{BR}$、$\mathrm N_5$ 和仿射表示迫出问题等价，仍未由上述条件归约回答。

由 (8.6)，更先行的相位合法性条件 $LE\subseteq\mathcal N$ 恰等价于下列两个混合和对全部 $u,z$ 消失：

$$
\sum_{k=1}^2B(S^ke_u,A_k(z))=0,\qquad
\sum_{k=1}^2B(A_k(z),S^ke_u)=0.
\tag{11.3}
$$

(11.3) 只给命题 3.2 的下降前件；这里未证明它足以推出 $\mathrm{UC}$。上述成对历史证明还使用 $\beta(y\cdot p_k)=\beta(y)+t_k$，即 $\mathrm{UC}$ 所给的逐个单位轨道缺陷根性，不能用混合和的消失替换。也未由 (R) 单独消去 (11.3) 的任何一个普遍读数和。

**假设 11.2（原事件与接口的保留范围）。**原事件空间 $\Omega$、固定事件核 $D$、装置、菜单、程序、带原括号的历史、原始质量、概率、失败、停止、记录和返回系数均沿用其原定义。式 (10.6) 的配对项与有限指标集只在上述数学证明中使用，不增补这些对象的定义或操作。定理 8.2 的条件等价不供应实际非零准备、参考、复制、重置、辅助系统、张量联合、仪器或时间接口；第 6 节的各项来源条件仍为各自前件。完整关系单独迫出 $\mathrm{UC}$ 的问题和量子来源问题均未由此解决。

## 追加锚（本行以下为增补区）

## 12. 自由有单位项上的归一化反模型归约

**定义 12.1（保留次序与括号的自由项）。**令 $\mathcal T$ 为由不同符号 $1,A,Z$、一元构造子 $V$ 和有序二元构造子生成的有限正规项集。具体地，$1,A,Z\in\mathcal T$；若 $s\in\mathcal T$，则 $V(s)\in\mathcal T$；若 $s,t\in\mathcal T\setminus\{1\}$，则有新的有序项 $\langle s,t\rangle\in\mathcal T$。不同构造子的输出及不同输入的构造项彼此不同。定义总二元运算

$$
s\cdot t=
\begin{cases}
t,&s=1,\\
s,&t=1,\\
\langle s,t\rangle,&s\ne1,\ t\ne1.
\end{cases}
\tag{12.1}
$$

两条单位规则在 $(1,1)$ 处一致。于是 $\mathcal T$ 是带任意一元运算的自由有双侧单位 magma；除 $1\cdot s=s=s\cdot1$ 及其在项中的代换外，没有施加其他恒等式，特别没有 $V1=1$、结合律、交换律或标记周期。

每个项可编码为有限字母表上的有限字符串，故 $\mathcal T$ 至多可数；各 $V^n1$ 彼此不同，故它可数无限。对任意有双侧单位的 magma $M$、任意 $W:M\to M$ 以及 $a,z\in M$，结构递归唯一给出总求值映射 $\phi:\mathcal T\to M$，满足

$$
\phi(1)=1,\quad\phi(A)=a,\quad\phi(Z)=z,\quad
\phi(s\cdot t)=\phi(s)\cdot\phi(t),\quad
\phi(Vs)=W\phi(s).
\tag{12.2}
$$

单位情形由 $M$ 的双侧单位律保证；非单位乘积与一元构造子情形由递归定义保证。此求值不要求单射，也不要求满到整个 $M$。

对任意处处有限实值有向核 $d$，仍用 (8.2) 的七项式定义 $H_d$，不要求 $d$ 非负。对 $\mathcal T$ 上的核定义

$$
h(d)=H_d(A,V1;Z).
\tag{12.3}
$$

本节中的归一化系统要求 $C:\mathcal T^2\to[0,\infty)$ 处处有限、$C(s,s)=0$，并对每个有序四元组满足

$$
\sum_{k=0}^2 C(a\cdot V^ku,b\cdot V^kv)
=3C(a,b)+3C(u,v).
\tag{12.4}
$$

重复标签、单位标签及每个项的原括号都包括在量词中。

**定理 12.2（原普遍蕴涵的归一化反模型等价）。**在定义 1.1 的整个原模型类中，存在满足 (R) 而不满足 $\mathrm{UC}$ 的模型，当且仅当对至少一个 $\sigma\in\{+1,-1\}$，定义 12.1 的同一个 $\mathcal T$ 上存在满足 (12.4) 的处处有限非负零对角核 $C$，且

$$
h(C)=\sigma.
\tag{12.5}
$$

由定理 8.2，这也等价于原普遍蕴涵 $(R)\Rightarrow\mathrm{BR}$ 或 $(R)\Rightarrow\mathrm N_5$ 的失败。它是整个模型类上的反模型存在性归约，不是在某个固定原模型中用一个读数代替全部 $\mathrm{UC}$ 读数。

**证明。**先说明所用标记替换的合法性。引理 2.1 已给同时标记等距；其适用条件正是原模型的有限非负性与完整 (R)。具体地，$s_n=c(U^nu,U^nv)$ 满足 $s_{n+1}+s_{n+2}=2s_n$，其解 $\alpha+\beta(-2)^n$ 在所有 $n\ge0$ 上非负迫使 $\beta=0$，所以 $c(Uu,Uv)=c(u,v)$。这是既有结论的直接应用，不要求 $U$ 满射或 $U1=1$。

固定原标签 $a,b,u,v$，令

$$
t_n=c(a\cdot U^nu,b\cdot U^nv)\qquad(n\ge0).
$$

对增量 $(U^nu,U^nv)$ 应用原 (R)，同时标记等距使右侧与 $n$ 无关：

$$
t_n+t_{n+1}+t_{n+2}=3c(a,b)+3c(u,v).
\tag{12.6}
$$

相邻两式相减得 $t_{n+3}=t_n$。因此若取 $W=U^2$，其三项依次为 $t_0,t_2,t_4$，而 $t_4=t_1$；故 $W$ 也满足同一个完整 (R)。这只是实际比较序列的周期性，没有断言 $U^3x=x$、完整行列周期、根稳定性或任何商算子的下降。取 $W=U$ 则无需替换。

再令 $c^{\mathsf T}(x,y)=c(y,x)$。原 (R) 在四元组 $(b,a,v,u)$ 的实例正好说明 $c^{\mathsf T}$ 满足同一个关系；它也处处有限、非负、零对角。

若原模型不满足 $\mathrm{UC}$，由定理 8.2 的确切读数刻画，存在实际 $a,z\in M$、$j\in\{1,2\}$ 及 $d\in\{c,c^{\mathsf T}\}$，使

$$
\eta=H_d(a,U^j1;z)\ne0.
$$

这里保留了两个读出次序及全部 $a,z,j$ 的存在性见证。取 $W=U^j$，由上述论证 $d$ 与 $W$ 仍满足完整关系。用 (12.2) 求值，并置

$$
C(s,t)=\frac{d(\phi(s),\phi(t))}{|\eta|}.
\tag{12.7}
$$

由于 $\phi$ 是总求值，每个项四元组的 (12.4) 都是原关系的一个实际实例再除以正数 $|\eta|$。全部单位约化、重复标签与原括号均被尊重；额外的求值重合不影响任何等式。有限性、非负性和零对角同样被保留。七项式的线性及 $\phi(V1)=U^j1$ 给 $h(C)=\eta/|\eta|\in\{+1,-1\}$。

反之，若有这样的 $C$，则 $(\mathcal T,\cdot,1,V,C)$ 本身就是定义 1.1 所允许的原模型。其第一单位轨道、一个指定次序的读数 $H_C(A,V1;Z)$ 非零，故违反 $\mathrm{UC}$ 的普遍要求。最后直接应用定理 8.2 的条件等价即得其余表述。没有把 $\mathrm{UC}$ 放入任何声称由 (R) 单独成立的前提。证毕。

## 13. 固定逐坐标有限盒中的总性判据

**定理 13.1（处处有限归一化核的共同盒判据）。**固定 $\sigma\in\{+1,-1\}$。定义 12.1 的 $\mathcal T$ 上存在满足 (12.4)–(12.5) 的处处有限非负零对角核，当且仅当存在预先固定的实数族

$$
0<B_{s,t}<\infty\qquad((s,t)\in\mathcal T^2),
\tag{13.1}
$$

使零对角等式、所有 (12.4) 实例及 (12.5) 的每个有限子集，都能在同一个盒

$$
\prod_{(s,t)\in\mathcal T^2}[0,B_{s,t}]
\tag{13.2}
$$

中同时满足。$B_{s,t}$ 可以随有序坐标而无界，但不能随所选有限约束集改变；不要求全局统一上界。

**证明。**若已有总核 $C$，取 $B_{s,t}=1+C(s,t)$，则 $C$ 同时满足整个系统及全部盒约束，因而满足每个有限子集。

反向，$\mathcal T^2$ 可数，全部四元组也可数。将有序坐标枚举为 $i=1,2,\ldots$，将上述等式枚举为 $E_1,E_2,\ldots$。每条等式都是只涉及有限多个坐标的实线性等式。对每个 $n$，在同一盒中选取满足 $E_1,\ldots,E_n$ 的点 $C^{(n)}$；若有限可行解只指定了约束涉及的坐标，未使用的坐标补零即可。

第一坐标落在固定紧区间 $[0,B_1]$ 中，故可取使第一坐标收敛的无限子序列；从该子序列再取使第二坐标收敛的无限子序列，依次进行。在这些嵌套子序列中选取原指标严格递增的对角子序列 $C^{(n_\ell)}$，可令 $n_\ell\ge\ell$。每个固定坐标都收敛到某个 $C_i\in[0,B_i]$。

对固定等式 $E_r$，当 $\ell\ge r$ 时，$n_\ell\ge r$，所以该子序列的点都满足 $E_r$。其有限多个坐标各自收敛，有限线性组合因而通过极限；故 $C$ 也满足 $E_r$。所有 $r$ 都如此，得到完整 (12.4)、全部零对角和 $h(C)=\sigma$。每个 $B_i$ 有限，所以得到的是处处有限的实值核。这里使用的是逐坐标 Bolzano–Weierstrass 与对角抽取，不把有限可行性本身当作总性。证毕。

**命题 13.2（无共同有限坐标界时的逃逸）。**对非负实变量 $x_0,x_1,\ldots$，系统

$$
x_0-x_n=n\qquad(n\ge1)
\tag{13.3}
$$

的每个有限子系统都可行，但它没有所有坐标均为有限实数的总解。

**证明。**对一个有限的指标集 $I\subseteq\mathbb N_{\ge1}$，令 $N=\max(I\cup\{0\})$，取 $x_0=N$、$x_n=N-n$ 对 $n\in I$，其他 $x_n$ 取零。这给非负有限解。若整个系统有非负总解，则 $x_0=n+x_n\ge n$ 对每个正整数 $n$ 成立，与 $x_0$ 有限矛盾。特别，任何固定有限的 $B_0$ 都会被某个单独等式与非负性排除；这说明定理 13.1 中同一个逐坐标有限盒的量词不能删去。证毕。

## 14. 仿射单位轨道上的归一化有号三次核

**定义 14.1（全项求值与有号核）。**取

$$
\omega=-\frac12+i\frac{\sqrt3}{2},\qquad
1+\omega+\omega^2=0,\qquad\omega^3=1.
$$

在全部 $\mathcal T$ 上以结构递归定义数学求值 $F:\mathcal T\to\mathbb C$：

$$
F1=0,\qquad F(A)=F(Z)=1,\qquad
F(s\cdot t)=Fs+Ft,\qquad F(Vs)=\omega Fs+1.
\tag{14.1}
$$

单位规则与 $F1=0$ 相容，所以求值处处有定义且有限。不同原项可以有相同求值；不因此识别原项。特别 $F(V1)=1$，而不是零。对 $\sigma\in\{+1,-1\}$ 定义

$$
\begin{aligned}
r(s,t)&=\operatorname{Re}((Fs-Ft)^3),\\
d_\sigma(s,t)&=-\frac{\sigma}{6}r(s,t),\\
Q(s,t)&=|Fs-Ft|^2.
\end{aligned}
\tag{14.2}
$$

有号核允许正、负实值；这种允许不改变原问题对 $C$ 的非负要求。

**定理 14.2（全部四元组的等式相容性与七项读数）。**$r,d_\sigma,Q$ 均为处处有限、零对角的实值核，并满足全部 (12.4)。$r$ 和 $d_\sigma$ 反对称，$Q$ 对称且非负。对任意 $a,p,z\in\mathcal T$，

$$
H_r(a,p;z)=-6\operatorname{Re}(Fa\,Fp\,Fz),\qquad
H_{d_\sigma}(a,p;z)=\sigma\operatorname{Re}(Fa\,Fp\,Fz),\qquad
H_Q(a,p;z)=0.
\tag{14.3}
$$

因而 $h(d_\sigma)=\sigma$、$h(Q)=0$。三次有号机制沿用《无结合律的双端三相比较：可见代数与复几何共同生成》[命题 5.4](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#5-保留括号的非零模型与完整三历史提升)；此处给出保留仿射偏移、并在自由项的单位轨道上取得指定非零读数的适配。

**证明。**由 (14.1)，

$$
F(V^ks)=\omega^kFs+\tau_k,\qquad
\tau_0=0,\quad\tau_1=1,\quad\tau_2=1+\omega
\qquad(k=0,1,2).
\tag{14.4}
$$

对任意实际项四元组置 $x=Fa-Fb$、$y=Fu-Fv$，则共同的仿射项严格相消：

$$
F(a\cdot V^ku)-F(b\cdot V^kv)=x+\omega^ky.
\tag{14.5}
$$

立方展开给

$$
\begin{aligned}
\sum_{k=0}^2(x+\omega^ky)^3
&=3x^3+3x^2y\sum_{k=0}^2\omega^k
  +3xy^2\sum_{k=0}^2\omega^{2k}
  +y^3\sum_{k=0}^2\omega^{3k}\\
&=3x^3+3y^3.
\end{aligned}
\tag{14.6}
$$

取实部，再乘 $-\sigma/6$，分别得到 $r$ 和 $d_\sigma$ 的完整关系。另一方面，$|\omega|=1$，所以

$$
\begin{aligned}
\sum_{k=0}^2|x+\omega^ky|^2
&=3|x|^2+3|y|^2
 +2\operatorname{Re}\left(\overline{x}y\sum_{k=0}^2\omega^k\right)\\
&=3|x|^2+3|y|^2,
\end{aligned}
\tag{14.7}
$$

得到 $Q$ 的完整关系。此核验对每个四元组同时有效，包括标签重合、单位的两种乘法位置、不同标记表达式及原括号；未在任一重合情形另假定一致性。有限性和零对角直接来自 (14.2)；交换两变量使立方变号、平方范数不变，给出其余性质。

为完整计算七项式，记 $\alpha=Fa$、$\pi=Fp$、$\zeta=Fz$。由 $F(a\cdot p)=\alpha+\pi$ 及 $F1=0$，

$$
\begin{aligned}
H_r(a,p;z)=\operatorname{Re}\bigl(&
(\alpha+\pi-\zeta)^3-(\alpha-\zeta)^3-(\pi-\zeta)^3
+(-\zeta)^3\\
&-(\alpha+\pi)^3+\alpha^3+\pi^3\bigr).
\end{aligned}
\tag{14.8}
$$

前三个立方的差为

$$
3\alpha\pi(\alpha+\pi)-6\alpha\pi\zeta+\zeta^3.
$$

加上 $(-\zeta)^3$ 消去末项；余下三个立方消去 $3\alpha\pi(\alpha+\pi)$。于是只剩 $-6\operatorname{Re}(\alpha\pi\zeta)$，得到 (14.3) 的第一、第二式。相应的平方范数式为

$$
\begin{aligned}
H_Q(a,p;z)={}&|\alpha+\pi-\zeta|^2-|\alpha-\zeta|^2
-|\pi-\zeta|^2+|\zeta|^2\\
&-|\alpha+\pi|^2+|\alpha|^2+|\pi|^2=0.
\end{aligned}
\tag{14.9}
$$

第一行展开为 $2\operatorname{Re}(\alpha\overline{\pi})$，第二行恰为其负值。最后取 $a=A,p=V1,z=Z$，三个求值全为 $1$，即得两个归一化读数。证毕。

**定理 14.3（纯等式关系商中的非零读数）。**令 $L=\mathbb R^{(\mathcal T^2)}$ 为有序项对上的有限支撑自由实向量空间，基向量记为 $\varepsilon_{s,t}$。令 $J\subseteq L$ 为下列所有向量的实线性张成：

$$
\varepsilon_{s,s},\qquad
\sum_{k=0}^2\varepsilon_{a\cdot V^ku,b\cdot V^kv}
-3\varepsilon_{a,b}-3\varepsilon_{u,v}
\qquad(s,a,b,u,v\in\mathcal T).
\tag{14.10}
$$

定义与七项读数对应的向量

$$
\begin{aligned}
\mathbf h={}&\varepsilon_{A\cdot V1,Z}-\varepsilon_{A,Z}
-\varepsilon_{V1,Z}+\varepsilon_{1,Z}\\
&-\varepsilon_{A\cdot V1,1}+\varepsilon_{A,1}+\varepsilon_{V1,1}.
\end{aligned}
\tag{14.11}
$$

则 $\mathbf h+J\ne0$ 于 $L/J$。特别，零对角与全部完整关系的有限实线性组合不能单独推出 $h=0$。

**证明。**对固定 $\sigma$，以

$$
\Lambda_\sigma\left(\sum_{s,t}\lambda_{s,t}\varepsilon_{s,t}\right)
=\sum_{s,t}\lambda_{s,t}d_\sigma(s,t)
$$

定义实线性泛函。向量有限支撑，故不要求 $d_\sigma$ 有界，也无收敛问题。定理 14.2 说明 $\Lambda_\sigma$ 消去 $J$ 的每个生成元，因此消去 $J$；但 $\Lambda_\sigma(\mathbf h)=\sigma\ne0$。所以 $\mathbf h\notin J$。这是纯线性等式关系商的结论，没有引入序锥、正分离或非负扩张定理，也没有推出非负核存在。证毕。

## 15. 原始倍增界与全部对称修补的障碍

**命题 15.1（固定二次修补的精确失败）。**对任意有限 $K\ge0$，置 $C_K=KQ+d_\sigma$。它处处有限、零对角，满足全部 (12.4) 且 $h(C_K)=\sigma$，并满足逐有序坐标的有限绝对值界

$$
|C_K(s,t)|\le B_K(s,t)
:=1+K|Fs-Ft|^2+\frac{|Fs-Ft|^3}{6}.
\tag{15.1}
$$

但 $C_K$ 不是非负核，对两个 $\sigma$ 均如此。

**证明。**等式与读数由定理 14.2 的线性组合得到；绝对值界由 $|\operatorname{Re}(w^3)|\le|w|^3$ 得到。定义实际的平衡项

$$
b_0=A,\qquad b_{n+1}=b_n\cdot b_n.
\tag{15.2}
$$

这里保留这一递归规定的全部括号。由 (14.1) 归纳得 $F(b_n)=2^n$，于是

$$
\begin{aligned}
C_K(b_n,1)&=K4^n-\frac{\sigma}{6}8^n,\\
C_K(1,b_n)&=K4^n+\frac{\sigma}{6}8^n.
\end{aligned}
\tag{15.3}
$$

当 $2^n>6K$，$\sigma=+1$ 时第一项为负，$\sigma=-1$ 时第二项为负。这排除每个固定有限 $K$，即使允许 (15.1) 的界随坐标增长也不改变结论。这里的绝对值盒不等于定理 13.1 的非负盒。证毕。

**定理 15.2（任意原模型的原始平衡倍增界）。**对定义 1.1 的任意非负核 $c$，只要满足完整 (R)，就对每个有序 $x,y\in M$ 有

$$
\begin{aligned}
&c(x\cdot x,y\cdot y)
+c(x\cdot Ux,y\cdot Uy)
+c(x\cdot U^2x,y\cdot U^2y)\\
&\hspace{3em}=6c(x,y).
\end{aligned}
\tag{15.4}
$$

令 $s_0(x)=x$、$s_{n+1}(x)=s_n(x)\cdot s_n(x)$，则对所有 $n\ge0$，

$$
0\le c(s_n(x),s_n(y))\le6^n c(x,y),
\tag{15.5}
$$

以及

$$
\begin{aligned}
&|c(s_n(x),s_n(y))-c(s_n(y),s_n(x))|\\
&\hspace{3em}\le6^n\max\{c(x,y),c(y,x)\}.
\end{aligned}
\tag{15.6}
$$

这些结论不需要 $\mathrm{UC}$、对称性、可见群或 Hilbert 表示。

**证明。**在原 (R) 中精确代入 $(a,b,u,v)=(x,y,x,y)$，右侧就是 $3c(x,y)+3c(x,y)$，得到 (15.4)。左侧三项的每一项都非负，舍去 $k=1,2$ 项即得 $c(x\cdot x,y\cdot y)\le6c(x,y)$。从 $n=0$ 开始沿指定平衡项归纳，得到 (15.5)。把原有序对换为 $(y,x)$ 再作同一归纳，得到反向界。对两个非负实数 $r,s$ 有 $|r-s|\le\max(r,s)$，因此两种次序的界共同给 (15.6)。全程没有重括号或对原始 $U$ 作任何额外假设。证毕。

**定理 15.3（指定三次反对称轮廓排除每个对称修补）。**固定任一 $\sigma\in\{+1,-1\}$。不存在处处有限非负、零对角且满足全部 (12.4) 的核 $C$，使

$$
\frac{C-C^{\mathsf T}}2=d_\sigma.
\tag{15.7}
$$

因而不存在任何处处有限实值对称核 $S$，使 $S+d_\sigma$ 成为这样的非负完整关系核。这个排除允许 $S$ 依赖原项、不能通过 $F$ 分解、没有全局界，甚至允许 $S$ 自身取负值；若另要求 $S$ 满足完整关系并有 $h(S)=0$ 以保留归一化，它仍被排除。

**证明。**若有这样的 $C$，置

$$
M=\max\{C(A,1),C(1,A)\}<\infty.
$$

自由单位规则给 $s_n(1)=1$，而 $s_n(A)=b_n$。由 (15.7)、(14.2) 及 $F(b_n)=2^n$，

$$
C(b_n,1)-C(1,b_n)
=2d_\sigma(b_n,1)=-\frac{\sigma}{3}8^n.
\tag{15.8}
$$

另一方面，(15.6) 给其绝对值至多为 $6^nM$。因此每个 $n\ge0$ 都必须满足

$$
\frac{8^n}{3}\le6^nM,
\qquad\text{即}\qquad
\left(\frac43\right)^n\le3M.
\tag{15.9}
$$

左侧随 $n$ 无界，与 $M$ 有限矛盾。若 $C=S+d_\sigma$ 且 $S$ 对称，则 $d_\sigma$ 反对称直接给 (15.7)，故同样排除。证明同时覆盖两个符号，且不使用 $S$ 的任何其他性质。证毕。

**命题 15.4（固定盒内仅对附加轮廓的有限矛盾）。**预先给定任意逐坐标有限界 $B_{s,t}$。在 (12.4)、非负性及 $C(s,t)\le B_{s,t}$ 之外，再附加 (15.7) 的三次反对称轮廓，则其中一个有限子系统已经不可行。不附加轮廓时，不能由此断言原归一化系统不可行。

**证明。**置 $B_* =\max\{B_{A,1},B_{1,A}\}$，选取有限整数 $n$，使 $(4/3)^n>3B_*$。对 $m=0,\ldots,n-1$，只取 (12.4) 在 $(b_m,1,b_m,1)$ 和 $(1,b_m,1,b_m)$ 的实例，以及其中三项的非负约束。它们沿平衡递归给两个方向的 (15.5)。再取两个初始坐标的非负性、上界及 (15.7) 在 $(b_n,1)$ 的实例，便得 $8^n/3\le6^nB_*$，与所选 $n$ 矛盾。若 $n=0$，仅初始坐标的非负性、上界与轮廓实例已足够。所取等式和坐标均有限。三次轮廓是额外构造方程，归一化 $h(C)=\sigma$ 只指定一个七项读数；这里没有从原归一化系统推出该轮廓，所以这个有限矛盾只属于指定构造族，不是对定理 12.2 原归一化系统的不可行性证书。证毕。

## 16. 非对称修正的必要条件与未决范围

**定理 16.1（保留归一化的修正必须改变三次反对称分量）。**若存在满足 (12.4)–(12.5) 的处处有限非负零对角核 $C$，则对相应的 $d_\sigma$，核 $e=C-d_\sigma$ 是处处有限实值零对角完整关系核，满足 $h(e)=0$；并且对所有 $n\ge0$，

$$
\left|e(b_n,1)-e(1,b_n)-\frac{\sigma}{3}8^n\right|
\le6^nM,\qquad
M=\max\{C(A,1),C(1,A)\}<\infty.
\tag{16.1}
$$

这样的修正必非对称。式 (16.1) 只是必要条件，不保证全四变量相容性或全部坐标的非负性。

**证明。**完整关系、零对角及七项读数均为核的线性条件，所以 $e=C-d_\sigma$ 保留前两者，并有 $h(e)=h(C)-h(d_\sigma)=0$。沿 (15.2) 的同一个原项递归，

$$
\begin{aligned}
C(b_n,1)-C(1,b_n)
&=e(b_n,1)-e(1,b_n)+2d_\sigma(b_n,1)\\
&=e(b_n,1)-e(1,b_n)-\frac{\sigma}{3}8^n.
\end{aligned}
$$

对左侧应用定理 15.2 即得 (16.1)。若 $e$ 对称，便落入定理 15.3 排除的情形，故它必须改变指定的反对称轮廓。反向并未成立：这条单条平衡射线上的界没有检查其他有序项对或任一其他四元组的完整关系。证毕。

**问题 16.2（对称有号种子的确切读数问题）。**在同一个 $\mathcal T$ 上，是否存在处处有限实值、对称、零对角并满足全部 (12.4) 的核 $E$，使 $H_E(A,V1;Z)=1$？或者，加入全部对称关系 $\varepsilon_{s,t}-\varepsilon_{t,s}$ 后，向量 $\mathbf h$ 是否属于 (14.10) 与这些对称关系生成的实线性空间？前者要求一个全项公式，后者要求一个有限实线性关系表示；这里两者均未取得。任一有号结论仍须另行处理非负性与处处有限总性，才能触及原反模型问题。

**对应 16.3（复用范围与数学来源）。**定理 8.2 的 $\mathrm{UC}\Leftrightarrow\mathrm{BR}$、本卷第 4 节与所引续卷第 4 节的群上二次函数及 Hilbert 推导，均在原来确切前件下复用。引理 2.1 的同时标记等距、续卷命题 5.4 的有号三次机制及有限或全局有界非负核为零的结论，也不在此计作新的迫出结果。定理 12.2 的归一化接口、仿射单位轨道非零读数、纯等式商见证，以及原始 $6^n$ 界对指定 $8^n$ 反对称轮廓的障碍，是本仓推导（repo-derived）；定理 13.1 使用经典的逐坐标紧性抽取，不作紧性方法或文献优先权主张。

交换群二次方程的文献结论仍是 Peter de Place Friis、Henrik Stetkær，*On the quadratic functional equation on groups*，Publ. Math. Debrecen 69/1–2，65–93，[DOI 10.5486/pmd.2006.3270](https://doi.org/10.5486/pmd.2006.3270)，第 65–67 页 Theorem 1.2；[原始论文](https://publi.math.unideb.hu/paper/1111/download/)要求交换定义域群、唯一二可除的交换值群，以及群二次方程。这是已有群入口处的 literature-attested 前置，不是任意 magma 或任意仿射标记下的迫出定理；本节各原始项上的新结论不以它补足尚未取得的群结构。

**问题 16.4（原目标与实际来源的保留边界）。**完整 (R) 单独是否迫出全部 $a,z\in M$、两个 $j=1,2$ 及两个读出次序上的 (8.4)，即是否迫出 $\mathrm{UC}/\mathrm N_5/\mathrm{BR}$，仍未解决。这里没有构造处处有限非负的总反模型。定理 14.3 只排除纯等式关系消去 $h$；定理 15.3 只排除指定三次反对称轮廓的所有对称修补；定理 13.1 仍要求同一个逐坐标有限盒中的全部有限子集可行。混合和 (11.3) 消失只供应已陈述的相位下降前件，不替代完整 $\mathrm{UC}$。

原事件空间 $\Omega$、固定原事件核 $D$、所有原装置、程序、菜单、历史、原始概率与质量，包括零值、失败、停止、记录及返回系数，均保持其原定义。自由项、复数求值及关系商只承担数学论证，不供应实际重置、复制、辅助系统、量子位、角操作、张量联合、充分参考执行、仪器、时间接口或完全正映射的实际来源。可表示性、正性、实际供应与对既定原事件核及过程的识别仍是不同义务；静态定向和实际资源缺口不由这些抽象结果闭合。

## 追加锚（本行以下为增补区）

## 17. 对称有号种子与两个单位读数

**定义 17.1（复二维空间上的对称有号全项模型）。**令

$$
\omega=-\frac12+i\frac{\sqrt3}{2},\qquad
1+\omega+\omega^2=0,\qquad \omega^3=1.
$$

取 $M=\mathbb C^2$，单位 $0=(0,0)$，乘法为向量加法，且

$$
Ux=\omega x+(1,1),\qquad p(t)=(t,t)\quad(t\in\mathbb C).
$$

在任意 $x,y\in M$ 上置

$$
E(x,y)=-\frac12\operatorname{Re}\bigl((x_1-y_1)(x_2-y_2)(x_1-x_2+y_1-y_2)\bigr).
\tag{17.1}
$$

这是处处有限的实值核；它允许有号取值，因而暂不属于原问题的非负核类。

**定理 17.2（全四变量关系与七项式读数）。**定义 17.1 的 $E$ 对称、零对角，并且对任意 $a,b,u,v\in\mathbb C^2$ 满足完整四变量关系 (R)

$$
\sum_{k=0}^2E(a+U^ku,b+U^kv)=3E(a,b)+3E(u,v).
\tag{17.2}
$$

此外，对任意 $a=(a_1,a_2)$、$z=(z_1,z_2)$ 和 $t\in\mathbb C$，沿用 (8.2) 的七项式有

$$
H_E(a,p(t);z)=\operatorname{Re}\bigl(t(a_1z_2-a_2z_1)\bigr).
\tag{17.3}
$$

特别地，若 $A=(1,0)$、$Z=(0,1)$，则

$$
H_E(A,p(1);Z)=1,\qquad H_E(A,p(1+\omega);Z)=\frac12.
\tag{17.4}
$$

**证明。**由递推直接得到

$$
U^kx=\omega^kx+\tau_k(1,1),\qquad
\tau_0=0,\quad\tau_1=1,\quad\tau_2=1+\omega.
\tag{17.5}
$$

置

$$
\begin{aligned}
X_0&=a_1-b_1,&X_1&=u_1-v_1,\\
Y_0&=a_2-b_2,&Y_1&=u_2-v_2,\\
Z_0&=a_1-a_2+b_1-b_2,&Z_1&=u_1-u_2+v_1-v_2.
\end{aligned}
$$

公因子 $\tau_k(1,1)$ 在三个差因子中分别消去，故

$$
\begin{aligned}
&(a+U^ku)_1-(b+U^kv)_1=X_0+\omega^kX_1,\\
&(a+U^ku)_2-(b+U^kv)_2=Y_0+\omega^kY_1,\\
&(a+U^ku)_1-(a+U^ku)_2+(b+U^kv)_1-(b+U^kv)_2
 =Z_0+\omega^kZ_1.
\end{aligned}
$$

因为 $\sum_k\omega^k=\sum_k\omega^{2k}=0$ 且 $\sum_k\omega^{3k}=3$，三次展开给出

$$
\sum_{k=0}^2(X_0+\omega^kX_1)(Y_0+\omega^kY_1)(Z_0+\omega^kZ_1)
=3X_0Y_0Z_0+3X_1Y_1Z_1.
$$

取实部并乘以 $-1/2$ 即得 (17.2)。交换 $x,y$ 时前两个差因子变号而第三个不变，所以 $E(y,x)=E(x,y)$；置 $x=y$ 则三因子乘积为零。

为计算 (17.3)，令

$$
S=a_1-a_2,\qquad T=z_1-z_2,\qquad P=a_1+a_2,\qquad Q=z_1+z_2.
$$

将 (8.2) 的七项逐项代入 (17.1)，不把 $t$ 限制为实数，复数多项式部分化为

$$
\begin{aligned}
&[t(P-Q)+t^2](S+T)-[t^2-tQ]T-[tP+t^2]S\\
&\qquad=t(PT-QS).
\end{aligned}
$$

而 $PT-QS=-2(a_1z_2-a_2z_1)$，故

$$
H_E(a,p(t);z)=-\frac12\operatorname{Re}\bigl(t(PT-QS)\bigr)
=\operatorname{Re}\bigl(t(a_1z_2-a_2z_1)\bigr).
$$

取 $a=A,z=Z$，有 $a_1z_2-a_2z_1=1$，且 $\operatorname{Re}(1+\omega)=1/2$，得到 (17.4)。证毕。

**定理 17.3（自由项拉回与对称关系商中的两个非成员）。**在定义 12.1 的同一个自由有单位 magma $\mathcal T$ 上，定义结构递归映射

$$
\eta(1)=0,\qquad \eta(A)=(1,0),\qquad \eta(Z)=(0,1),\qquad
\eta(s\cdot t)=\eta(s)+\eta(t),\qquad \eta(Vs)=U\eta(s),
\tag{17.6}
$$

并置 $E_{\mathcal T}(s,t)=E(\eta(s),\eta(t))$。则 $E_{\mathcal T}$ 是处处有限、对称、零对角并满足全部 (12.4) 的有号核，而且

$$
E_{\mathcal T}(A\cdot V1,1)=-1,\qquad
E_{\mathcal T}(Z\cdot V1,1)=1.
\tag{17.7}
$$

令 $J_{\mathrm{sym}}$ 为 (14.10) 的 $J$ 与全部交换向量的和：

$$
J_{\mathrm{sym}}=J+\operatorname{span}_{\mathbb R}
\{\varepsilon_{s,t}-\varepsilon_{t,s}:s,t\in\mathcal T\}.
\tag{17.8}
$$

除 (14.11) 的 $\mathbf h_1=\mathbf h$ 外，定义

$$
\begin{aligned}
\mathbf h_2={}&\varepsilon_{A\cdot V^2 1,Z}-\varepsilon_{A,Z}
-\varepsilon_{V^2 1,Z}+\varepsilon_{1,Z}\\
&-\varepsilon_{A\cdot V^2 1,1}+\varepsilon_{A,1}+\varepsilon_{V^2 1,1}.
\end{aligned}
\tag{17.9}
$$

则

$$
\mathbf h_1\notin J_{\mathrm{sym}},\qquad
\mathbf h_2\notin J_{\mathrm{sym}}.
\tag{17.10}
$$

这两个结论分别成立，不断言二者或其混合组合的线性独立性。本定理回答了 §16.2 的有号问题。

**证明。**结构递归 (17.6) 总定义，每个有限原始项的求值均有限，且尊重真正的双侧单位规则。源 $\mathcal T$ 的约化仍只有这些单位规则；$\eta$ 不必单射，求值相同不使原始项相等，也不向 $\mathcal T$ 增添结合律、交换律或 $V$ 的周期关系。由乘法与 $V$ 的递归式，(17.2) 逐项拉回为 (12.4)，对称性与零对角也随即保留。由 $\eta(V1)=(1,1)$，

$$
\eta(A\cdot V1)=(2,1),\qquad \eta(Z\cdot V1)=(1,2),
$$

代入 (17.1) 得 (17.7)。

对有限支撑向量 $q=\sum\lambda_{s,t}\varepsilon_{s,t}$ 定义

$$
\Lambda(q)=\sum\lambda_{s,t}E_{\mathcal T}(s,t).
$$

零对角、(12.4) 和 $E_{\mathcal T}(s,t)=E_{\mathcal T}(t,s)$ 分别说明 $\Lambda$ 消灭 $J$、交换生成元以及 $J_{\mathrm{sym}}$。另一方面，(17.3) 与

$$
\eta(V1)=p(1),\qquad \eta(V^2 1)=p(1+\omega)
$$

给出

$$
\Lambda(\mathbf h_1)=1,\qquad \Lambda(\mathbf h_2)=\frac12.
$$

若任一 $\mathbf h_j$ 属于 $J_{\mathrm{sym}}$，则其 $\Lambda$ 值应为零，矛盾；故 (17.10) 成立。证毕。

**对应 17.4（相位、原问题边界与物理来源）。**式 (17.1) 的交换对称性来自交换端点时两个差因子同时变号、第三个差因子保持不变；它是无序比较读数的候选定义，不是对既有有向模型的所有交换次序的定理，也不是顺序测量的交换性。三次单位根的相消给出全四变量 (R) 的有号解，但负值读数 (17.7) 说明它不满足原问题的非负性，因此不提供原几何蕴涵的非负总反模型，也不决定非负对称完整(R)是否迫出UC/BR/几何。原有 §8.2 的条件等价、$H$、$T$、$L$、$J$ 及非负 $\mathrm{UC}\Longleftrightarrow\mathrm{BR}$ 范围均保持；[续卷 W 定理 20.1（正幂三点分类）](./AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md) 在完整 (R) 下所用的任意统一 $\alpha>0$ 的 $c^\alpha$ 三角条件仍是另行的接口前件。

这里使用的三次单位根相消和有限支撑赋值是经典中间工具；本节新增的承重内容是处处有限的对称有号全项种子、两个单位读数 $1$ 与 $1/2$，以及 (17.10) 的关系张成分离。该种子没有给出非负性、实际事件或过程的来源，也没有补足原事件空间、组成、时间和完整量子接口；完整量子起源候选仍需在这些边界内另行验证。

## 追加锚（本行以下为增补区）

## 18. 第三标记返回下的单标记标定

**定义 18.1（完整返回与保留单位贡献的标定）。**沿用定义 1.1 的整个原模型类：$M$ 仅有二元运算和真实双侧单位 $1$，$U:M\to M$ 任意，$c:M^2\to[0,\infty)$ 处处有限且零对角，完整 (R) 对全部原标签 $a,b,u,v$ 成立。仍记 $p_j=U^j1$、$P_ja=a\cdot p_j$，以及定义 8.1 的 $A_j(a)$、$H_d$ 和引理 2.1 的 $E,B,\mathcal N$。条件 $\mathrm C_3$ 为

$$
c(P_3a,b)=c(a,b),\qquad c(a,P_3b)=c(a,b)
\qquad(a,b\in M).
\tag{18.1}
$$

对 $j=1,2$，条件 $\mathrm C_j$ 为一个标记的完整双向标定族

$$
H_c(a,p_j;z)=H_{c^{\mathsf T}}(a,p_j;z)=0
\qquad(a,z\in M).
\tag{18.2}
$$

由 (8.5)，$\mathrm C_j$ 恰为 $A_j(a)\in\mathcal N$ 对全部 $a$ 成立，因而 $\mathrm{UC}=\mathrm C_1\land\mathrm C_2$。这里 $\mathrm C_3$ 专指 (18.1) 的返回，不指 $j=3$ 的七项式标定。所有量词保留重复标签、两个读数次序和原乘积的括号；$P_3$ 不与 $P_1$ 的三次复合相认。

**引理 18.2（四个原标签返回等价与合法三阶商作用）。**在定义 18.1 的原类及完整 (R) 下，以下四个普遍条件等价：

$$
\begin{aligned}
&c(P_3a,b)=c(a,b) &&(a,b\in M),\\
&c(a,P_3b)=c(a,b) &&(a,b\in M),\\
&c(U^3a,b)=c(a,b) &&(a,b\in M),\\
&c(a,U^3b)=c(a,b) &&(a,b\in M).
\end{aligned}
\tag{18.3}
$$

任一个条件都等价于 $\mathrm C_3$，也等价于下列任一个完整行列普遍条件：

$$
a\cdot(U^3u)\approx a\cdot u,\qquad
 a\cdot p_{j+3}\approx a\cdot p_j
\qquad(a,u\in M,\ j\ge0),
\tag{18.4}
$$

其中 $\approx$ 是定义 2.2 的全部原行列相等。此时 $Se_a=e_{Ua}-e_{p_1}$ 保持 $\mathcal N$，故在 $V=E/\mathcal N$ 上诱导算子 $T$，满足

$$
T^3=I,\qquad B(Tx,Ty)=B(x,y).
\tag{18.5}
$$

**证明。**为与自由空间上的 $S$ 区分，暂记原对象操作 $G=U^3$、$P=P_3$。直接复用[续卷 W 引理 17.1](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#17-实际单位碰撞与全部探针上的标记消去)的交叉等距：

$$
c(Ga,Gb)=c(Ga,Pb)=c(Pa,Gb)=c(Pa,Pb)=c(a,b).
\tag{18.6}
$$

第一端点的 $P$ 返回与第二端点的 $G$ 返回等价：前者给 $c(a,Gb)=c(Pa,Gb)=c(a,b)$，后者给 $c(Pa,b)=c(Pa,Gb)=c(a,b)$。同样，第二端点的 $P$ 返回与第一端点的 $G$ 返回等价。两个 $G$ 返回也等价：在 $c(Ga,Gb)=c(a,b)$ 中用所给返回消去其中一端，即取得另一端。每次代入均使用普遍量词，未要求 $G$ 或 $P$ 满射。于是 (18.3) 四项等价。

引理 2.1 已给同步 $U$ 等距。完整 (R) 对 $(a,b,U^nu,U^nv)$ 的相邻实例相减，给

$$
c\bigl(a\cdot(U^3u),b\cdot(U^3v)\bigr)=c(a\cdot u,b\cdot v).
\tag{18.7}
$$

取 $v=1$，用第二端点的 $P_3$ 返回，得到 $c(a\cdot(U^3u),b)=c(a\cdot u,b)$；取 $u=1$，另用第一端点返回，得到 $c(a,b\cdot(U^3v))=c(a,b\cdot v)$。这两式分别给 (18.4) 的完整行与完整列；再取 $u=p_j$ 得其第二式。反向，在 (18.4) 的第一项取 $u=1$，或在第二项取 $j=0$，均给 $P_3a\approx a$，也即 $\mathrm C_3$。这里只消去该指定右输入中的三次标记，没有建立 $\approx$ 对任意乘法环境的相容性。

特别 $U^3a\approx a$、$p_3\approx1$。引理 2.3 因而给

$$
e_{U^3a}-e_a\in\mathcal N,\qquad e_{p_3}\in\mathcal N,\qquad
(S^3-I)E\subseteq\mathcal N,
\tag{18.8}
$$

末式使用 $S^3e_a=e_{U^3a}-e_{p_3}$。在定义任何商标记之前，对 $n\in\mathcal N,y\in E$ 分别计算

$$
\begin{aligned}
B(Sn,y)&=B(Sn,S^3y)=B(n,S^2y)=0,\\
B(y,Sn)&=B(S^3y,Sn)=B(S^2y,n)=0.
\end{aligned}
\tag{18.9}
$$

首个等号使用 (18.8) 的双侧根性，第二个等号使用引理 2.1 的自由空间等距。所以 $S\mathcal N\subseteq\mathcal N$，$T$ 才能下降，(18.8) 给 $T^3=I$，逆算子为 $T^2$。$B$ 因 $\mathcal N$ 在两个槽均为根而下降；商上的确切非退化性只是

$$
\bigl[B(w,x)=B(x,w)=0\ \text{对每个 }x\in V\bigr]\ \Longrightarrow\ w=0.
\tag{18.10}
$$

并未假设任一个单侧根空间为零，也未假设 $B$ 对称或正定。证毕。

**定理 18.3（两个缺陷的耦合与单标记条件判据）。**在完整原类及 $\mathrm C_3$ 下，置

$$
\beta(a)=[e_a],\qquad \alpha_j(a)=[A_j(a)],\qquad
L=I+T+T^2,\qquad Q=L/3.
\tag{18.11}
$$

则 $Q$ 是像为 $\ker(T-I)$ 的幂等算子，满足 $B(Qx,y)=B(x,Qy)$。对每个原标签 $a$，两个单位缺陷满足精确关系

$$
\begin{aligned}
L\beta(a)+T^2\alpha_1(a)+T\alpha_2(a)&=0,\\
\alpha_2(a)&=-T\alpha_1(a)-L\beta(a),\\
Q\alpha_1(a)+Q\alpha_2(a)&=-3Q\beta(a),\\
(I-Q)\alpha_2(a)&=-T(I-Q)\alpha_1(a).
\end{aligned}
\tag{18.12}
$$

在定义 1.1 的完整 (R) 类中，有条件等价

$$
\begin{aligned}
\mathrm C_3\land\mathrm C_1
\quad\Longleftrightarrow\quad
\mathrm C_3\land\mathrm C_2
\quad\Longleftrightarrow\quad
\mathrm{UC}
\quad\Longleftrightarrow\quad
\text{存在满足 (1.2) 的完整仿射复 Hilbert 表示}.
\end{aligned}
\tag{18.13}
$$

因此额外返回条件只需 (18.3) 中任一端点的一条普遍条件；标定则仍要求同一个 $j$ 的全部原标签、全部探针与两个读数次序。表示中的漂移 $t=F(U1)$ 不受零值限制。

**证明。**引理 18.2 已先支付商算子的合法性。由 $T^3=I$ 及等距性，两个槽分别有

$$
B(Tx,y)=B(x,T^2y),\qquad B(x,Ty)=B(T^2x,y).
\tag{18.14}
$$

故 $L$ 可移至另一槽而不变，且 $L^2=3L$、$TL=LT=L$。于是 $Q^2=Q$；$TQ=Q$，而 $Tx=x$ 时 $Qx=x$，给出其像。分解 $V=\operatorname{im}Q\oplus\ker Q$ 的两个部分在 $B$ 的两个配对次序下均互相正交；这只是双线性意义下的固定部分与非平凡三相部分，不是已经取得的正内积。

直接将 (8.6) 的两条原轴恒等式降到这个合法商。对任意原标签 $u,a$，令 $x=\beta(u),y=\beta(a)$，则

$$
\begin{aligned}
B(Lx,y)&=-B(Tx,\alpha_1(a))-B(T^2x,\alpha_2(a)),\\
B(y,Lx)&=-B(\alpha_1(a),Tx)-B(\alpha_2(a),T^2x).
\end{aligned}
\tag{18.15}
$$

分别用 (18.14) 移动算子，得到

$$
\begin{aligned}
B\bigl(x,Ly+T^2\alpha_1(a)+T\alpha_2(a)\bigr)&=0,\\
B\bigl(Ly+T^2\alpha_1(a)+T\alpha_2(a),x\bigr)&=0.
\end{aligned}
\tag{18.16}
$$

$\beta(M)$ 张成 $V$，所以 (18.10) 给 (18.12) 第一式；作用 $T^2$ 得第二式，再分别作用 $Q$ 与 $I-Q$ 得余下两式。这里 $\alpha_j(a)$ 始终按原标签索引，未把它当成 $\beta(a)$ 上已经良定义的函数或线性算子，也未令 $P_j$ 先行下降。

若给 $\mathrm C_1$，则 $\alpha_1(a)=0$，耦合式给 $\alpha_2(a)=-L\beta(a)$；若给 $\mathrm C_2$，则 $\alpha_2(a)=0$，同式给 $\alpha_1(a)=-T^2L\beta(a)=-L\beta(a)$。两种情形均在原恒等式 (2.3) 取 $u=v=1$：由 $X_k(a,1)=e_a+A_k(a)$ 及 $A_0=0$，有

$$
\sum_{k=0}^2 B\bigl(\beta(a)+\alpha_k(a),\beta(b)+\alpha_k(b)\bigr)
=3B(\beta(a),\beta(b)).
\tag{18.17}
$$

三个向量由两份 $\beta(a)$ 与一份 $(I-L)\beta(a)$ 组成，只在 $k=1,2$ 的位置上有别。因此由双线性及张成性，对全部 $x,y\in V$ 有

$$
B((I-L)x,(I-L)y)=B(x,y).
\tag{18.18}
$$

但移槽与 $L^2=3L$ 又给

$$
B((I-L)x,(I-L)y)
=B(x,y)-2B(Lx,y)+B(L^2x,y)
=B(x,y)+B(Lx,y).
\tag{18.19}
$$

所以 $B(Lx,y)=0$ 对全部 $x,y$ 成立；另一方向也有 $B(y,Lx)=B(Ly,x)=0$。完整双侧非退化性 (18.10) 迫 $Lx=0$ 对全部 $x$ 成立。耦合式随即消去另一标记的全部缺陷，取得原自由空间中完整的 $\mathrm{UC}$。几何上，$I-L=I-3Q$ 在固定部分乘以 $-2$，在 $\ker Q$ 上为恒等；它同时保持 $B$ 迫使固定部分在两个方向都落入根，而非仅有零自配对。

现在直接应用定理 8.2：其 $M,U,c$ 正是本节原对象，根空间也是同一个 $\mathcal N$，全部 $a,z$ 与 $j=1,2$ 的前件已经取得。故得到 (1.2)，连同该定理已有的 $\mathrm{BR}$、对称性、全部有限负型与最小表示唯一性；不另作群化或 Hilbert 分类。反向，$\mathrm{UC}$ 经定理 8.2 给表示，因而两个 $\mathrm C_j$ 都成立，且

$$
F(p_3)=(1+\omega+\omega^2)t=0,\qquad
F(P_3a)=Fa,
\tag{18.20}
$$

给 $\mathrm C_3$。这证明 (18.13)。

单标记标定保留 $e_{p_j}$：其内容是 $e_{a\cdot p_j}-e_a-e_{p_j}\in\mathcal N$，不是 $e_{a\cdot p_j}-e_a\in\mathcal N$。在表示中它允许 $F(P_1a)=Fa+t$；第一标记完整行列不可见才会要求 $t=0$。例如取加法 magma $M=\mathbb C$，单位记作 $0$，任取 $t\ne0$，置 $Uz=\omega z+t$、$c(z,w)=|z-w|^2$、$Fz=z$。两端共同仿射项相消及 $\sum_k\omega^k=0$ 直接给完整 (R)；$p_3=0$，两个标定族由其表示取得。但 $c(P_1 0,0)=|t|^2>0=c(0,0)$。这是 (1.2) 的非零漂移实例，也与命题 5.4 的原始树实现相容，不另计为新的分类。证毕。

**对应 18.4（来源、有号种子与保留接口）。**引理 18.2 的交叉等距复用续卷 W 引理 17.1；自由差空间等距、完整行列与根空间的对应、两个轴配对次序及完成分类，分别复用引理 2.1、2.3、式 (8.6) 与定理 8.2。三阶商的根稳定性及算子移槽也用于续卷 W 定理 40.1；该定理以输入的纯相位 Hilbert 映射和受支配反对称残差取得端点均值。本节不使用那个均值前件，新增的 repo-derived 承重关系是原类在返回条件下的 (18.12)，以及由一个双向标定族通过 (18.17)–(18.19) 消去固定部分的判据。有限循环平均与幂等算子代数是推导内的经典工具；完整几何及既有度量、增长入口不作为新增结果重述，不主张文献优先权。

为划清非负性边界，直接检验定义 17.1 的同一个对称有号种子 $E$。其中 $U^3x=x$、$p_3=0$，故两个第三标记返回都在原对象上成立。定理 17.2 已给完整 (R) 以及

$$
H_E((1,0),p_1;(0,1))=1,\qquad
H_E((1,0),p_2;(0,1))=\tfrac12.
\tag{18.21}
$$

它仍不满足任一个标定族，且由 (17.1) 有 $E((2,1),0)=-1$，亦即定理 17.3 的原项负值。这个负值把种子排除在定义 1.1 的非负总模型类之外；它只说明完整等式、对称性与第三返回在有号扩展中不足以推出标定，不能用来否定非负完整 (R) 或非负完整 (R) 加第三返回的几何充分性。

本节没有从完整 (R) 推出 (18.3) 的任一返回，也没有从完整 (R) 加 $\mathrm C_3$ 推出 $\mathrm C_1$。这两个仍未解决的普遍蕴涵分别是返回接口和单标记标定接口；(18.13) 仅说明后者一旦供应就足以复用全部比较几何。它不改变问题 16.4 的原类量词。

在唯一整体态 $\Omega$ 的建模前提下，$\beta(a)$、$Q$ 和 Hilbert 完成均不是自动可执行的门或准备操作。观察者、参考、记录与读出仍须由同一 $\Omega$ 内的实际有限历史实现；非零准备、事件与完整测试的概率归一、共同联合与条件历史、仪器及其参考实现、物理过程的组合和物理时间，仍保留第 6 节与 §11.2 所列的独立接口。三相指标、三标签测试、复 Hilbert 维数与物理或 Bloch 三维没有在本判据中被认同；这里取得的是条件比较几何，不是完整量子起源。

## 追加锚（本行以下为增补区）
## 19. 真群上的任意标记与对称非负全关系

本节把原始对象的乘法进一步限制为真群，只为关闭一个明确的桥，不把所得结论外推到一般有单位 magma。比较端点互换不改读数的对称性在这里仍是明确定义输入；它不要求群乘法交换，也不宣称既有有向模型具有这一对称性或序贯测量操作可交换。

**定义 19.1（真群任意标记模型）。**令 $G$ 为任意真群，单位为 $1$；不要求交换、可数、拓扑、增长或有限生成。令 $U:G\to G$ 为任意总映射，不要求 $U1=1$、满射、乘法性或周期性。令

$$
c:G^2\longrightarrow[0,\infty)
$$

处处有限、对称且 $c(g,g)=0$。假设对全部 $a,b,u,v\in G$ 都有完整四变量关系

$$
\sum_{k=0}^2c\bigl(aU^ku,bU^kv\bigr)=3c(a,b)+3c(u,v).
\tag{19.1}
$$

这里所有乘法、逆元、括号和 $U$ 的迭代都是给定对象上的实际总运算。

**引理 19.2（右移不变性与零子群的双侧不可见性）。**在定义 19.1 的前件下，存在有限函数 $f:G\to[0,\infty)$，满足

$$
c(a,b)=f(ab^{-1}),\qquad f(1)=0,\qquad f(x^{-1})=f(x),
\tag{19.2}
$$

并且 $Z=\{z:f(z)=0\}$ 是正规子群。对任意 $z,w\in Z$ 和 $a,b\in G$，有

$$
c(az,bw)=c(a,b).
\tag{19.3}
$$

同步标记保持零纤维：$aZ=bZ$ 蕴涵 $UaZ=UbZ$。因而 $c$、$U$ 以及 (19.1) 都下降到真群 $G/Z$，且

$$
c(a,b)=0\quad\Longleftrightarrow\quad aZ=bZ.
\tag{19.4}
$$

**证明。**固定 $a,b$，置 $h(x)=c(ax,bx)$，$m=\inf_{x\in G}h(x)\ge0$。在 (19.1) 中取背景 $ax,bx$ 与增量 $u,u$，得

$$
\sum_{k=0}^2h(xU^ku)=3h(x).
$$

任一项不小于 $m$。给定目标 $y$，取实际群元 $u=x^{-1}y$，第零项给

$$
h(y)-m\le3(h(x)-m).
$$

对 $x$ 取下确界即 $h(y)=m$；取 $x=1$ 得 $h(y)=h(1)$，即

$$
c(ax,bx)=c(a,b).
\tag{19.5}
$$

故 $f(g)=c(g,1)$ 给出 (19.2)。将 (19.1) 的第零项与背景 $x,1$、增量 $y,1$ 比较，得到实际有限项不等式

$$
f(xy)\le3\bigl(f(x)+f(y)\bigr).
\tag{19.6}
$$

对称性和 (19.5) 给 $f(x^{-1})=f(x)$，所以 $Z$ 对乘法和逆元封闭。再在 (19.1) 中取背景 $a,a$、增量 $z,1$；其第零项为 $f(aza^{-1})$，而右侧为零，故 $Z$ 正规。

置 $p_j=U^j1$、$T_j(x)=U^jx\,p_j^{-1}$。先前同步等距结论（本卷引理 2.1）给

$$
f(T_jx)=c(U^jx,p_j)=c(x,1)=f(x),
\tag{19.7}
$$

所以 $T_jZ\subseteq Z$。固定 $x$，令 $m_x=\inf_{z\in Z}f(xz)$。对 $z,w\in Z$，在 (19.1) 中取背景 $xz,1$、增量 $w,1$，由 (19.7) 得

$$
\sum_{j=0}^2 f\bigl(xzT_jw\bigr)=3f(xz).
\tag{19.8}
$$

三个参数都在同一右陪集 $xZ$，故每项不小于 $m_x$。给定 $z_0\in Z$，取实际 $w=z^{-1}z_0$，第零项给

$$
f(xz_0)-m_x\le3(f(xz)-m_x).
$$

对 $z$ 取下确界，得到 $f(xz_0)=m_x$；再取 $z_0=1$，即

$$
f(xz)=f(x)\qquad(x\in G,z\in Z).
\tag{19.9}
$$

正规性把 $a zw^{-1}b^{-1}$ 写成 $(ab^{-1})z'$（其中 $z'\in Z$），于是 (19.3) 成立。式 (19.4) 由 (19.2)、(19.9) 及 $Z$ 的定义得到。最后，同步等距给 $c(Ua,Ub)=c(a,b)$；因此相同右陪集仍映到相同右陪集，$U$ 在 $G/Z$ 上下降。独立改变两个代表元的 (19.3) 也保证下降后的核良定义，四元关系逐代表元保留。证毕。

**引理 19.3（保群的有限矩阵零漂移实现）。**给定定义 19.1 的一个模型和有限标签集 $A\subseteq G$，存在可数真群 $S$、总映射 $U_*$ 及处处有限、对称、非负、零对角的核 $c_\infty$，满足完整 (19.1)，并有真实单位 $1_S$ 使

$$
c_\infty(U_*1_S,1_S)=0,\qquad
c_\infty(x_a,x_b)=c(a,b)\quad(a,b\in A),
\tag{19.10}
$$

其中 $x_a\in S$ 是指定的来源。$S$ 的群律、逆元和 $U_*$ 的总性在取极限前已经成立；$a\mapsto x_a$ 不被宣称为保乘法或保标记的映射。

**证明。**沿用[续卷 W 定理 9.2–9.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#9-精确保留比较矩阵的右梳复制)的实际右梳。令 $\Sigma_N=\{0,1,2\}^N$，$G_N=G^{\Sigma_N}$ 逐坐标取真群运算，$U_N$ 逐坐标作用，真实单位为常数组 $\mathbf1$，并置

$$
c_N(X,Y)=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}c(X_\sigma,Y_\sigma).
\tag{19.11}
$$

对 $\sigma=(\sigma_1,\ldots,\sigma_N)$，右梳 $H_N^\sigma(a;1)$ 严格按 W 定义的括号递推；记

$$
\Gamma_N(a)(\sigma)=H_N^\sigma(a;1).
$$

W 的精确右梳恒等式给

$$
c_N(\Gamma_N(a),\Gamma_N(b))=c(a,b),
\tag{19.12}
$$

且以

$$
\Omega=q(p_1)+q(p_2)+r(p_1)+r(p_2),\qquad q(g)=c(g,1),\quad r(g)=c(1,g)
$$

记单位轨道预算，有

$$
c_N(\Gamma_N(1),\mathbf1)+c_N(\mathbf1,\Gamma_N(1))\le\frac{\Omega}{N},\qquad
c_N(\mathbf p_j,\mathbf1)+c_N(\mathbf1,\mathbf p_j)\le\frac{\Omega}{N}.
\tag{19.13}
$$

这里逐坐标求和仍给 $G_N$ 上的完整 (19.1)；(19.12) 只保持比较矩阵，从不把 $\Gamma_N$ 当作同态。

现在取直积群 $P=\prod_{N\ge1}G_N$，逐坐标定义 $U_*$，并令 $x_a=(\Gamma_N(a))_{N\ge1}\in P$。从这些 $x_a$ 出发，递归令 $S_0$ 为其生成子群，$S_{n+1}$ 为由 $S_n\cup U_*(S_n)$ 生成的子群，置

$$
S=\bigcup_{n\ge0}S_n.
$$

每个 $S_n$ 可数，故 $S$ 是可数真子群，含真实单位并对 $U_*$ 封闭。重要的是，这个群载体的逆元和结合律是每个坐标中已经成立的对象等式。

对 $S$ 中由有限个 $x_a$、单位、乘法、逆元和 $U_*$ 写出的表达式 $e$，先由 (19.6)、对称性和 (19.13) 递归给出与 $N$ 无关的有限预算。例如可取

$$
B(1)=0,\qquad B(x_a)=3q(a)+3\Omega,\qquad
B(e^{-1})=B(e),
\tag{19.14}
$$

以及

$$
B(ef)=3(B(e)+B(f)),\qquad B(U_*e)=3B(e)+3\Omega.
\tag{19.15}
$$

数组模型中每个表达式的 $q_N$ 不超过其预算，而

$$
c_N(e_N,f_N)\le3\bigl(B(e)+B(f)\bigr).
\tag{19.16}
$$

逆元预算使用 $q_N(e_N^{-1})=q_N(e_N)$；标记节点使用同步等距和第一个单位轨道项；乘法节点使用 (19.6)。这些估计只涉及实际有限项，不引入度量或三角前件。

枚举 $S$ 的全部有序对，依次对标量序列

$$
c_N\bigl(\pi_Ns,\pi_Nt\bigr)
$$

取收敛子列，再取一个共同的对角子列 $N_\ell\to\infty$；这里 $\pi_N$ 是第 $N$ 个坐标投影。这一步只复用[续卷 W 定理 23.2](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#23-任意有限比较矩阵的零漂移实现)的逐项对角方法；其自由含幺 magma 载体在本节被实际直积群 $S$ 替换，不能把 W 的载体直接称为真群。由 (19.16)，每个极限有限，定义

$$
c_\infty(s,t)=\lim_{\ell\to\infty}c_{N_\ell}(\pi_{N_\ell}s,\pi_{N_\ell}t).
\tag{19.17}
$$

非负性、对称性和零对角通过有限标量极限保留。对任意固定 $a,b,u,v\in S$，投影保留乘法、逆元、单位和 $U_*$；同一个对角子列中左侧三个核值及右侧两个核值同时收敛，所以完整 (19.1) 也保留。由 (19.13)，

$$
c_\infty(U_*1_S,1_S)=\lim_{\ell\to\infty}\frac{q(p_1)}{N_\ell}=0.
$$

而 (19.12) 给出 (19.10) 的比较矩阵保留。故这是处处定义的总真群模型，而非有限窗口或相互独立的边界序列。证毕。

**定理 19.4（真群任意标记的完整仿射复几何等价）。**在定义 19.1 的模型类中，完整关系 (19.1) 等价于存在复 Hilbert 空间 $H$ 和映射 $F:G\to H$，使

$$
\begin{gathered}
F1=0,\qquad F(gh)=F(g)+F(h),\\
F(Ug)=\omega F(g)+t,\qquad t=F(U1),\\
c(g,h)=\|F(g)-F(h)\|^2,\qquad
\omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\end{gathered}
\tag{19.18}
$$

最小表示 $H=\overline{\operatorname{span}_{\mathbb C}F(G)}$ 按本卷定理 1.3 的保标签唯一性唯一到酉同构。零核 $c\equiv0$ 包含在此结论中；$t$ 不被要求为零。

**证明。**先证 (19.1) 蕴涵 (19.18)。任取至多五个原标签 $a_1,\ldots,a_m$（允许重复），令 $A$ 为其有限集合，应用引理 19.3 得到 $(S,U_*,c_\infty)$。在整个真群 $S$ 上应用引理 19.2；其零集 $Z_\infty$ 是正规子群，独立代表元的完整行列相等，且 $U_*$ 在陪集上下降。因为

$$
c_\infty(U_*1_S,1_S)=0,
$$

下降后的实际单位被下降的标记固定：$\overline U[1_S]=[1_S]$。因此真群商 $S/Z_\infty$ 连同下降后的有限非负零对角核满足[续卷 V 定理 1.3](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#1-原始配方与唯一配平关系)的全部前件。该定理给出其平方距离的复 Hilbert 表示，故对任意实系数 $\alpha_i$ 且 $\sum_i\alpha_i=0$，有

$$
\sum_{i,j}\alpha_i\alpha_jc_\infty([x_{a_i}],[x_{a_j}])
=-2\left\|\sum_i\alpha_iF_\infty([x_{a_i}])\right\|^2\le0.
\tag{19.19}
$$

用 (19.10) 拉回，得到原 $c$ 的五点负型 $\mathrm N_5$。这里不同的有限标签集可以使用不同的辅助群和不同的对角子列；(19.19) 只涉及被保留的原比较矩阵，不要求这些辅助表示彼此相容。

现在回到原始 $G,U,c$，直接应用本卷定理 1.3 的 $\mathrm N_5\Rightarrow$ 表示方向，得到 (19.18)。乘法和 $U$ 都由该定理在原对象上恢复；它们没有从 $\Gamma_N$、$S$ 或任何极限嵌入拉回。定理 1.3 同时给出最小表示唯一性。

反向设 (19.18) 成立。记 $t_0=0$、$t_1=t$、$t_2=(1+\omega)t$，则

$$
F(U^ku)=\omega^kF(u)+t_k.
$$

两端共同的 $t_k$ 相消；令 $X=F(a)-F(b)$、$Y=F(u)-F(v)$，左侧成为

$$
\sum_{k=0}^2\|X+\omega^kY\|^2
=3\|X\|^2+3\|Y\|^2,
$$

正是 (19.1)。证毕。

**对应 19.5（新桥的边界与可见作用）。**定理 19.4 在真群分支内移除了预先给定的归一化三相同态、右差形式、零行列合同、负型和 Hilbert 前件；它保留真群的结合与实际逆元、对称性、处处有限非负零对角核和全部四变量关系。原始 $U$ 或 $g\mapsto Ug(U1)^{-1}$ 在 $G$ 上不被宣称为同态。由 (19.18)，只有在可见商 $G/\ker F$ 上，归一化词才诱导

$$
[g]\longmapsto[Ug][U1]^{-1},
$$

其像作用为乘以 $\omega$，因而是立方为恒等的自同构；这是商上的推论，不是原标签上的运算等式。对每个 $j=1,2$，本卷式 (8.2) 的双向单位缺陷在 (19.18) 中直接展开为零，所以两个完整代表元方向都闭合。

这里实际复用的数学来源是 W 定理 9.2–9.3 的精确右梳核保持、W 定理 23.2 的对角极限方法、V 定理 1.3 的单位固定分类和本卷定理 1.3 的原始 $\mathrm N_5$ 应用；这些来源的适用条件分别已在本节的真群、总标记、全四变量和有限非负前件中逐项保留。没有新增准备、参考、效果、事件、联合、仪器、过程、组合或物理时间的实际来源；第 6 节与 §11.2 的接口条件仍须分别供应。辅助直积、群生成、逆元、对角极限、商和 Hilbert 完成都只是比较数学构造，不是可执行的物理复制、逆门或时间演化。定理 19.4 不解决一般任意有单位 magma，也不完成完整量子起源问题；它只关闭真群、任意总标记这一有界桥。固定相位正性分类仍由续卷 V 覆盖，本节不重复该结果。

## 追加锚（本行以下为增补区）

## 20. 受总核支配事件的固定模型与精确穷尽

### 20.1 原事件问题及其返回接口

**定义 20.1（给定仿射总几何的普遍事件断言）。**沿用定义 1.1 的实际签名：$M$ 是带真实双侧单位 $1$ 的任意 magma，$U:M\to M$ 任意；不要求结合、交换、逆元、消去、拓扑或商下降。固定 $\omega=\exp(2\pi i/3)$。给定复 Hilbert 空间 $H$、映射 $F:M\to H$ 和任意漂移 $t\in H$，满足

$$
\begin{gathered}
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad F(Ua)=\omega Fa+t,\\
H=\overline{\operatorname{span}_{\mathbb C}F(M)},\qquad
K(a,b)=\|Fa-Fb\|^2.
\end{gathered}
\tag{20.1}
$$

实际给定的完整有限测试用有限索引集 $J$ 及核族 $(d_j)_{j\in J}$ 表示；各 $d_j:M^2\to[0,\infty)$ 处处有限，对全部有序原标签及所示括号满足

$$
\sum_{k=0}^2d_j(a\cdot U^ku,b\cdot U^kv)
=3d_j(a,b)+3d_j(u,v),\qquad
\sum_{j\in J}d_j(a,b)=K(a,b).
\tag{20.2}
$$

因此 $0\le d_j\le K$，各事件零对角，但不预设事件对称、负型、第三标记返回或 Hilbert 表示。两个索引即使给出同一函数也仍是两个事件标签。

记 $\mathsf{Eff}$ 为以下普遍断言：对每个满足 (20.1) 的 $(M,1,\cdot,U,H,F,t)$ 及每个满足 (20.2) 的完整带索引有限测试，在这个给定总核的同一个最小复空间 $H$ 上存在唯一复正收缩 $(E_j)_{j\in J}$，使

$$
0\le E_j\le I_H,\qquad
\sum_{j\in J}E_j=I_H,\qquad
d_j(a,b)=\langle Fa-Fb,E_j(Fa-Fb)\rangle
\quad(a,b\in M).
\tag{20.3}
$$

这里的普遍量词指满足所列公理的全部数学模型及其给定测试；它不宣称任意新构造的数学测试在物理中可用。总 Hilbert 几何是本问题的输入，不是由本节推导的量子起源。

**命题 20.2（同一总空间上的事件效果恰等价于两个普遍返回）。**固定 (20.1)，令 $d:M^2\to[0,\infty)$ 处处有限、满足完整 (R) 且 $d\le K$。记 $p_3=U^31$。在给定 $H$ 上存在表示 $d$ 的复正收缩，当且仅当

$$
d(a\cdot p_3,b)=d(a,b),\qquad
d(a,b\cdot p_3)=d(a,b)
\qquad(a,b\in M).
\tag{20.4}
$$

对 (20.2) 的原完整测试，所有事件都有 (20.4) 时，效果在同一个给定最小总空间上唯一，且和为 $I_H$。

**证明。**由仿射规则及 $1+\omega+\omega^2=0$，有

$$
F(p_3)=(1+\omega+\omega^2)t=0,\qquad
F(a\cdot p_3)=Fa.
\tag{20.5}
$$

故效果表示给出两个返回。反向，$d$ 非负、零对角、满足完整 (R) 和 (20.4)；[续卷 W 定理 43.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#43-原核的有界轴刚性与第三标记返回下的完整仿射几何)在这个同一个 $M,U,d$ 上给出完整仿射复 Hilbert 表示。总核 $K$ 满足完整 (R) 及两个返回，因而 $K-d$ 也非负、零对角、满足完整 (R) 及两个返回。再次应用 W 定理 43.3，得到补核的表示。于是本卷定理 1.3 的表示条件对带索引二元测试

$$
J=\{0,1\},\qquad d_0=d,\qquad d_1=K-d
\tag{20.6}
$$

逐一成立，定理 6.2 给出所需效果及唯一性。即使 $d=K-d$，(20.6) 也保留两个索引。对原完整有限测试，分别将 W 定理 43.3 用于每个 $d_j$，再将定理 6.2 用于该原测试，即得唯一性与效果和。这里没有从逐点费用支配推出极化核的正定性或 Loewner 支配。

此应用同时明确 §18.4 所列条件接口的数学范围：在定义 1.1 的完整非负有向类中，W 定理 43.3 已给出

$$
(R)+\mathrm C_3\ \Longrightarrow\ \mathrm C_1,\ \mathrm{UC}
\ \Longrightarrow\ \text{完整仿射复 Hilbert 表示}.
\tag{20.7}
$$

因此 §18.4 中“$(R)+\mathrm C_3$ 到 $\mathrm C_1$ 尚缺”的条件缺口由该定理支付；本节复用这个条件结论。单独 $(R)\Rightarrow\mathrm C_3$ 仍未在一般原始类中推出。§19 的真群定理 19.4 保留实际结合律、逆元与核对称性，不能用于当前任意 magma 和初始有向事件来代付这些前件。证毕。

### 20.2 一个固定仿射总核与一个返回坐标

**定义 20.3（自由两来源仿射候选类）。**令 $T_2$ 为由不同符号 $1,x,y$、一元构造子 $U$ 和有序二元构造子生成的自由真含幺 $U$-magma，只施加双侧单位律。采用 §12 的单位约简正规项：$1,x,y,Us$ 均为正规项，两个非单位正规项的有序二元节点也是正规项；乘积中的单位因子先约简，其他括号与次序全部保留。特别，$U1$、$U^31$ 和 $1$ 是不同原项。$T_2$ 可数且无限。

在 $\mathbb C^3$ 的标准正交基 $e_1,e_2,e_3$ 中定义

$$
\begin{gathered}
\psi(1)=0,\quad \psi(x)=e_1,\quad \psi(y)=e_2,\\
\psi(s\cdot z)=\psi(s)+\psi(z),\qquad
\psi(Us)=\omega\psi(s)+e_3,\\
\kappa(s,z)=\|\psi(s)-\psi(z)\|^2.
\end{gathered}
\tag{20.8}
$$

单位约简与这些递归相容。总漂移实际为 $e_3$，最小总空间是 $\mathbb C^3$，因为 $\psi(U1)=e_3$。

令 $\mathcal A$ 为全部函数 $q:T_2^2\to\mathbb R$ 的以下类：对每个有序项对有 $0\le q(s,z)\le\kappa(s,z)$，对全部有序项四元组有完整原关系

$$
\sum_{k=0}^2q(a\cdot U^ku,b\cdot U^kv)
=3q(a,b)+3q(u,v).
\tag{20.9}
$$

不加对称、负型、返回、表示或纤维下降。零对角由支配自动成立。固定

$$
P=x\cdot(U^31),\qquad
\Delta(q)=q(P,y)-q(x,y).
\tag{20.10}
$$

$P$ 不与 $x$ 合并；$\psi(P)=\psi(x)=e_1$，故 $\kappa(P,y)=\kappa(x,y)=2$。

**定理 20.4（原普遍事件断言的单坐标固定模型归约）。**定义 20.1 的整个模型与完整有限测试类中，以下断言等价：

1. $\mathsf{Eff}$ 成立。
2. 对每一个 $q\in\mathcal A$，都有 $\Delta(q)=0$。
3. $\max_{q\in\mathcal A}\Delta(q)=0$。

最大值存在，并且

$$
0\le\max_{q\in\mathcal A}\Delta(q)
=\max_{q\in\mathcal A}|\Delta(q)|\le2.
\tag{20.11}
$$

若有 $q\in\mathcal A$ 使 $\Delta(q)>0$，则在同一个整个 $T_2$、实际自由构造子 $U$ 及总映射 $\psi$ 上，带索引测试 $d_0=q,d_1=\kappa-q$ 是 $\mathsf{Eff}$ 的总反模型。这不是仅在有限标签或有限关系窗中的反例。

**证明。**先核对固定总核。对任意有序 $a,b,u,v\in T_2$，令 $A=\psi(a)-\psi(b)$、$B=\psi(u)-\psi(v)$。第 $k$ 项两个端点共有的仿射漂移相消，故总核左侧为

$$
\sum_{k=0}^2\|A+\omega^kB\|^2
=3\|A\|^2+3\|B\|^2.
\tag{20.12}
$$

因此 $\kappa$ 满足完整 (20.9)；$q\mapsto\kappa-q$ 保持 $\mathcal A$。由于两个指定总费用均为 $2$，该补变换把 $\Delta$ 变为 $-\Delta$。零核说明此类非空，每个补核都在同一个整个项代数上非负且满足完整关系。

现在设某个原模型中的受支配事件 $d$ 违反 (20.4)。若只有第二端点返回失败，取 $d^{\mathsf T}(s,z)=d(z,s)$，并把来源对 $(a,b)$ 换为 $(b,a)$。原关系在 $(a,b,u,v)$ 换成 $(b,a,v,u)$ 后正给转置核的完整关系；$K$ 对称，仍支配该核。因此可设第一端点有失败

$$
\delta=d(a\cdot p_3,b)-d(a,b)\ne0.
\tag{20.13}
$$

取自由求值 $\phi:T_2\to M$，送 $x\mapsto a,y\mapsto b,1\mapsto1$，并按原来的二元与一元运算递归。它尊重且只需尊重两条单位律，不重括号。置

$$
S=\|Fa\|^2+\|Fb\|^2+\|t\|^2,\qquad
V(z_1,z_2,z_3)=z_1Fa+z_2Fb+z_3t.
\tag{20.14}
$$

对单位正规项归纳得

$$
F(\phi(s))=V\psi(s)\quad(s\in T_2),\qquad
\|Vz\|^2\le S\|z\|^2\quad(z\in\mathbb C^3).
\tag{20.15}
$$

一元步骤恰是 $F(U\phi(s))=\omega F(\phi(s))+t$，没有舍去漂移。范数界是对三个源向量应用 Cauchy–Schwarz，不要求 $V$ 单射或来源正交。若 $Fa=Fb$，则 (20.5) 使 (20.13) 中两个费用都被零总费用支配，违背 $\delta\ne0$。故 $Fa\ne Fb$，从而 $S>0$。现在才定义

$$
q(s,z)=\frac{d(\phi(s),\phi(z))}{S}.
\tag{20.16}
$$

对每个有序项对，由 (20.15) 有

$$
0\le q(s,z)\le S^{-1}\|V(\psi(s)-\psi(z))\|^2
\le\kappa(s,z).
\tag{20.17}
$$

自由求值保持每个实际构造子，因而所有有序四元组的完整 (R) 连同原括号同时拉回。于是 $q\in\mathcal A$，且 $\Delta(q)=\delta/S\ne0$。若此值为负，换成 $\kappa-q$ 即得正值。零漂移、某个来源像为零、来源标签等于原单位、线性比较映射 $V$ 奇异均不影响这一步；来源生成元即使求值等于原单位，也不在自由语法中与新单位合并。

若第 2 项成立，上述构造排除每个原模型中每个受支配事件的任一返回失败。命题 20.2 遂给每个原完整带索引测试在给定最小总空间上的唯一效果及和为恒等。反过来，$\mathsf{Eff}$ 应用于任一 $q\in\mathcal A$ 的测试 $d_0=q,d_1=\kappa-q$，效果表示及 $\psi(P)=\psi(x)$ 给 $\Delta(q)=0$。这证明前两项的等价及正值反模型结论。

最后，$\mathcal A$ 是坐标盒

$$
\prod_{(s,z)\in T_2^2}[0,\kappa(s,z)]
\tag{20.18}
$$

的闭子集：每条 (20.9) 只含有限坐标。可数坐标的逐项对角子列论证给出其紧性，$\Delta$ 是有限坐标连续函数，故最大值可取到。补变换的符号对称性和两个 $[0,2]$ 界给 (20.11)，也给第 2、3 项等价。证毕。

这里要求所有 $q\in\mathcal A$ 通过同一个指定坐标测试；单个 $q$ 的 $\Delta(q)=0$ 不在本定理中被断言足以给该 $q$ 效果。最大值究竟为零还是正值，仍未确定。

### 20.3 保留共同支配的去漂移与固定三来源三角

**定义 20.5（自由三来源纯相位候选类）。**令 $T_3$ 为对应的自由真含幺 $U$-magma，生成元为 $x_1,x_2,x_3$，只作单位约简。在同一个标准 $\mathbb C^3$ 中置

$$
\begin{gathered}
f_0(1)=0,\qquad f_0(x_i)=e_i\quad(1\le i\le3),\\
f_0(s\cdot z)=f_0(s)+f_0(z),\qquad f_0(Us)=\omega f_0(s),\\
K_0(s,z)=\|f_0(s)-f_0(z)\|^2.
\end{gathered}
\tag{20.19}
$$

令 $\mathcal B$ 为所有在整个 $T_3^2$ 上满足完整原 (R) 及 $0\le q\le K_0$ 的函数；不预设其余事件性质。总漂移为零，最小空间为 $\mathbb C^3$，但原项 $U1$ 仍不同于 $1$；$U^31$ 也不约简。载体仍是可数无限项集。

**定理 20.6（共同总核支配下的纯相位固定三角归约）。**原普遍断言 $\mathsf{Eff}$ 等价于

$$
\forall q\in\mathcal B:\qquad
\sqrt{q(x_1,x_3)}\le
\sqrt{q(x_1,x_2)}+\sqrt{q(x_2,x_3)}.
\tag{20.20}
$$

若 $\mathsf{Eff}$ 不成立，则有一个 $q\in\mathcal B$ 严格违反此有向生成元三角；带索引测试 $d_0=q,d_1=K_0-q$ 在这个固定纯相位总模型上就是总反模型。因此，对所有纯相位总几何证明事件断言足以推出任意漂移的原断言。仅某一个 $q$ 满足 (20.20) 的三角式，不被断言足以给该 $q$ 表示。

**证明。**若原断言失败，由命题 20.2 存在一个原受支配事件 $d$ 没有效果。它不能有完整仿射复 Hilbert 表示，否则该表示给两个返回；$K-d$ 也有返回，再由 W 定理 43.3 和本卷定理 6.2 得到效果。将 [W 定理 14.1](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#14-保留有限核的极限给出完整三点几何桥) 的有向三角分类逆否应用于 $d$ 自身，得到原标签 $a_1,a_2,a_3$，使

$$
g:=\sqrt{d(a_1,a_3)}-\sqrt{d(a_1,a_2)}
-\sqrt{d(a_2,a_3)}>0.
\tag{20.21}
$$

该应用只用 $d$ 非负、处处有限、零对角及完整 (R)，不添加对称性或返回。

对 $N\ge1$ 及 $\sigma\in\Sigma_N=\{0,1,2\}^N$，取 [W 引理 23.1](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#23-任意有限比较矩阵的零漂移实现) 的同一个实际右梳

$$
H_0(a;1)=1,\qquad
H_N^\sigma(a;1)=a\cdot U^{\sigma_1}
H_{N-1}^{(\sigma_2,\ldots,\sigma_N)}(a;1).
\tag{20.22}
$$

记 $s_r=\sigma_1+\cdots+\sigma_r$、$s_0=0$，选唯一 $e_\sigma\in\{0,1,2\}$ 使 $s_N+e_\sigma\equiv0\pmod3$，并置

$$
\Gamma_Na(\sigma)=U^{e_\sigma}H_N^\sigma(a;1).
\tag{20.23}
$$

在实际数组 magma $M^{\Sigma_N}$ 上，乘法和 $U_N$ 逐坐标采用原运算，真实单位为常值数组 $\mathbf1$。定义

$$
\begin{aligned}
d_N(X,Y)&=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}d(X_\sigma,Y_\sigma),\\
H_N^{\rm arr}&=\ell^2(\Sigma_N;H),\\
F_N(X)&=\left(\frac{F(X_\sigma)}{\sqrt{N3^N}}\right)_\sigma,\qquad
t_N=\left(\frac{t}{\sqrt{N3^N}}\right)_\sigma.
\end{aligned}
\tag{20.24}
$$

有限平均保持完整 (R)；本卷引理 2.1 的非负递推给 $d(Ua,Ub)=d(a,b)$。W 引理 23.1 的右梳平均恰为 $Nd(a_i,a_j)$，末端同步标记又等距，所以

$$
d_N(\Gamma_Na_i,\Gamma_Na_j)=d(a_i,a_j)
\quad(1\le i,j\le3).
\tag{20.25}
$$

所有九个有向源费用在同一个模型中精确保留，不需任何返回前件。与此同时，保留的是一个共同总映射，而不是分别复制各事件后再拼接：

$$
\begin{gathered}
F_N\mathbf1=0,\qquad F_N(XY)=F_NX+F_NY,\\
F_N(U_NX)=\omega F_NX+t_N,\qquad
\|t_N\|=\|t\|/\sqrt N,\\
0\le d_N(X,Y)\le\|F_NX-F_NY\|^2
\quad(X,Y\in M^{\Sigma_N}).
\end{gathered}
\tag{20.26}
$$

为识别这个同一总核的源向量，复用 W 式 (41.5)–(41.15) 中右梳、相位校准和共同等距的代数。具体置

$$
m=\frac{t}{1-\omega},\qquad
A_N(\sigma)=\sum_{r=0}^{N-1}\omega^{s_r},\qquad
I_Nv=\left(\frac{\omega^{e_\sigma}A_N(\sigma)v}{\sqrt{N3^N}}\right)_\sigma.
\tag{20.27}
$$

按 (20.22) 的实际括号展开，得到

$$
\begin{aligned}
F(H_N^\sigma(a;1))
&=A_N(\sigma)Fa+(1-\omega^{s_N})m,\\
F(U^{e_\sigma}H_N^\sigma(a;1))
&=\omega^{e_\sigma}A_N(\sigma)Fa
 +(1-\omega^{s_N+e_\sigma})m\\
&=\omega^{e_\sigma}A_N(\sigma)Fa.
\end{aligned}
\tag{20.28}
$$

若 $r>l$，$\mathbb E_\sigma\omega^{s_r-s_l}=0$，因为其中一个独立相位的均值是 $(1+\omega+\omega^2)/3=0$。因此

$$
\mathbb E_\sigma|A_N(\sigma)|^2=N,\qquad
\|I_Nv\|^2=\|v\|^2,\qquad
F_N(\Gamma_Na_i)=I_NFa_i.
\tag{20.29}
$$

$I_N$ 是对所有来源共同的复线性等距。上述式子包含 $N=1$：此时 $A_1=1$，平均范数仍为 $1$，末端漂移相消仍逐项成立。这里只使用这些有限代数恒等式，不调用 W 定理 41.1 的残差消失结论，也不将其返回前件转借给 $d$。

将同一个 $T_3$ 求值到每个数组模型，令 $\operatorname{ev}_N(x_i)=\Gamma_Na_i$、$\operatorname{ev}_N(1)=\mathbf1$，两构造子采用实际运算。在 $T_3$ 上递归定义

$$
\begin{aligned}
f(1)&=0,& f(x_i)&=Fa_i,& f(sz)&=f(s)+f(z),& f(Us)&=\omega f(s),\\
\lambda_1&=0,& \lambda_{x_i}&=0,& \lambda_{sz}&=\lambda_s+\lambda_z,&
\lambda_{Us}&=\omega\lambda_s+1.
\end{aligned}
\tag{20.30}
$$

单位约简保持两递归。由 (20.26)–(20.29) 对项归纳，有

$$
F_N(\operatorname{ev}_Ns)=I_Nf(s)+\lambda_s t_N
\qquad(s\in T_3).
\tag{20.31}
$$

因此对每个固定有序项对 $(s,z)$，

$$
\begin{aligned}
\|F_N(\operatorname{ev}_Ns)-F_N(\operatorname{ev}_Nz)\|^2
&\longrightarrow\|f(s)-f(z)\|^2,\\
0\le d_N(\operatorname{ev}_Ns,\operatorname{ev}_Nz)
&\le\bigl(\|f(s)-f(z)\|
+|\lambda_s-\lambda_z|\,\|t\|\bigr)^2.
\end{aligned}
\tag{20.32}
$$

此处右端是每对坐标各自有限且不依赖 $N\ge1$ 的共同界，不要求一个常数控制全部项。枚举所有有序项对，对事件费用取一条共同的对角子列 $N_\ell\to\infty$，得到整个 $T_3^2$ 上的有限非负总核 $d_\infty$。每条原 (R) 只含有限坐标，求值又保持原构造子，故全部关系在同一极限中成立；(20.26)、(20.32) 还给

$$
0\le d_\infty(s,z)\le\|f(s)-f(z)\|^2,\qquad
d_\infty(x_i,x_j)=d(a_i,a_j)\quad(1\le i,j\le3).
\tag{20.33}
$$

故 (20.21) 的严格差值 $g$ 精确保留，而不是由一个非严格极限不等式推断其严格性。未添加返回、表示或同纤维行列下降。

最后置

$$
S_0=\sum_{i=1}^3\|Fa_i\|^2,\qquad
V_0(z_1,z_2,z_3)=\sum_{i=1}^3z_iFa_i.
\tag{20.34}
$$

若 $S_0=0$，三个源像都为零，支配使全部源对费用为零，与 (20.21) 矛盾。因此 $S_0>0$。由自由递归与 Cauchy–Schwarz，

$$
f=V_0f_0,\qquad \|V_0z\|^2\le S_0\|z\|^2.
\tag{20.35}
$$

定义 $q=d_\infty/S_0$ 后，(20.33)–(20.35) 给整个 $T_3$ 上的 $0\le q\le K_0$ 及完整 (R)，而生成元三角的严格超额为 $g/\sqrt{S_0}>0$。总核 $K_0$ 满足完整 (R)，故 $K_0-q$ 也非负且满足完整关系，给出带索引总二元反模型。

反向，若 $\mathsf{Eff}$ 成立，它给任一 $q\in\mathcal B$ 的带索引测试 $(q,K_0-q)$ 一个效果 $E$。于是 $\sqrt{q(s,z)}=\|E^{1/2}(f_0(s)-f_0(z))\|$ 是 Hilbert 半范数距离，满足指定生成元三角，得到 (20.20)。证毕。

零漂移、零或重复源像、奇异 $V_0$ 及原标签 $a_i=1$ 都允许；只在严格三角失败已确保 $S_0>0$ 后才除以它。没有除以准备费用、某个距离或 $\|t\|$。单独应用 W 定理 23.2 分别复制事件核并不给出 (20.26)–(20.33) 的共同支配，本证明保留同一 $F_N$、同一 $I_N$ 与同一条对角子列。

### 20.4 同一仿射项模型上的有限有理穷尽

**推论 20.7（返回最大值的精确有限系统）。**在定义 20.3 的 $T_2$ 上，对单位正规项置

$$
|1|=|x|=|y|=1,\qquad |Us|=1+|s|,\qquad
|s\cdot z|=1+|s|+|z|\quad(s,z\ne1),
\tag{20.36}
$$

一般乘积先作单位约简。对 $N\ge1$ 令

$$
\begin{aligned}
T_N&=\{s\in T_2:|s|\le N\},\\
E_N&=T_N\ \cup\ \{a\cdot U^ku:a,u\in T_N,\ 0\le k\le2\}
\ \cup\ \{P\},\qquad P=x\cdot(U^31).
\end{aligned}
\tag{20.37}
$$

在唯一一组共享实变量 $z_{s,r}$、$(s,r)\in E_N^2$ 上，定义有限系统 $\mathcal P_N$：

$$
\begin{gathered}
0\le z_{s,r}\le\kappa(s,r)\quad(s,r\in E_N),\\
\sum_{k=0}^2z_{a\cdot U^ku,b\cdot U^kv}
=3z_{a,b}+3z_{u,v}\quad(a,b,u,v\in T_N).
\end{gathered}
\tag{20.38}
$$

不加对称性、任何 $\mathrm C_3$ 行、负型或商识别；所有关系与界使用这同一变量族。置

$$
m_N=\max_{z\in\mathcal P_N}(z_{P,y}-z_{x,y}).
\tag{20.39}
$$

这些系统是非空有界有理多面体，最大值是有理数，并有精确关系

$$
0\le m_{N+1}\le m_N\le2,\qquad
\max_{q\in\mathcal A}\Delta(q)=\inf_{N\ge1}m_N.
\tag{20.40}
$$

因此 $\mathsf{Eff}$ 恰等价于 $\inf_Nm_N=0$；其失败恰等价于

$$
\exists\varepsilon\in\mathbb Q_{>0}\ \forall N\ge1\quad
\exists z^{(N)}\in\mathcal P_N\cap\mathbb Q^{E_N^2}:\qquad
z^{(N)}_{P,y}-z^{(N)}_{x,y}\ge\varepsilon.
\tag{20.41}
$$

其中同一个正有理阈值在所有 $N$ 上固定，不能改成依赖窗口的正阈值。

**证明。**这是 [W 定理 38.4](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#38-纯相位支配残差的固定两来源归约与有理穷尽) 的紧有理穷尽在当前事件类中的应用，保留共享变量，去掉该残差类的反对称与返回附加行，并使用当前仿射总核与指定差坐标。具体地，(20.8) 的每个复坐标都在 $\mathbb Z[\omega]$ 中。若差坐标为 $m+n\omega$，$m,n\in\mathbb Z$，则

$$
|m+n\omega|^2=m^2-mn+n^2.
\tag{20.42}
$$

所以每个 $\kappa(s,r)$ 都是非负整数，所有有限行数据有理。零总费用保留为单点界 $z_{s,r}=0$，不合并不同项。零变量族可行；有界有理多面体的线性目标可在有理顶点取到最大值，适用于退化面和零维情形。目标中的两个变量都在 $[0,2]$，故 $0\le m_N\le2$。$E_N\subseteq E_{N+1}$ 且大系统限制后满足小系统，给单调性。

每个总候选 $q\in\mathcal A$ 都限制为所有 $\mathcal P_N$ 的可行点，所以 $\max\Delta\le\inf_Nm_N$。反向，逐个取有限最大点，在未出现的坐标上填零，视为固定盒 (20.18) 中的点。枚举全部有序项对，取一条共同对角子列。每条总界与每条完整 (20.9) 都最终进入某一有限系统，故极限 $q$ 属于 $\mathcal A$。指定差坐标的极限为单调数列的下确界，给 $\Delta(q)=\inf_Nm_N$，从而得 (20.40)。

若该值为正，选一个严格小于它的正有理数 $\varepsilon$，每个窗口的有理最大点满足 (20.41)。反向，若同一正有理阈值对所有窗口可行，在同一固定盒中作上述对角提取，得到 $\Delta(q)\ge\varepsilon>0$ 的总候选；也可由 $m_N\ge\varepsilon$ 及 (20.40) 直接得到。证毕。

此推论没有给出任何 $m_N$ 的值；有限多个窗口的正最大值不能替代总反模型。既未断言某个有限窗就迫出零，也未给出收敛率或有效判定算法。

### 20.5 来源对应与数学范围

**对应 20.8（目标特定的归约增量及保留前件）。**本节的承重内容是受支配事件问题的两个精确普遍归约：任意 magma、任意总空间维数、任意来源 Gram 与任意漂移，归到固定 $T_2,\psi$ 的一个返回差坐标；通过保留共同总核的数组极限，再归到固定 $T_3,f_0$ 的一个生成元有向三角。前者给显式紧盒中的最大值问题及有理有限系统，后者证明纯相位子类对原任意漂移事件问题具有反模型完备性。它们是已有方法对未付事件接口的综合与应用，不主张自由代数、紧性、算子效果的一般新方法或历史优先权。

本节使用的 W、V、IV 结果以版本 `13d69713c20f58174d6bbfd07a12be95802faed7` 中相应条目为来源；本卷 §19 使用其真群前件。具体对应如下。

- 本卷定义 1.1、定理 1.3、引理 2.1、命题 5.3 和定理 6.2，分别给原任意标记签名、表示条件的接口、同步标记等距、一般漂移与旋转中心的区别，以及已经取得事件表示后的效果唯一性与完整性。本卷 §§12–13 给保留次序与括号的自由求值及共同有限坐标盒的总性方法；没有把零距离直接提升为完整行列相同。
- W 定理 14.1 给 (20.21) 的严格有向三角见证；W 引理 23.1 及 §§23.2–23.4 给右梳复制与有限矩阵归约的来源，当前证明另保留 (20.26) 的同一总核。W 定理 38.2 的自由求值与范数支配用于 (20.14)–(20.17)、(20.34)–(20.35)，W 定义 38.3、定理 38.4 的紧有理穷尽用于推论 20.7。W38 本身针对假定纯相位与返回的反对称残差，不是当前事件类的现成结论。
- W 式 (41.5)–(41.15) 的右梳展开、共同复线性等距和消失漂移用于 (20.22)–(20.33)；W 定理 41.1 和 W40 的返回依赖结论均不作为无返回事件定理使用。W 定理 43.3 在命题 20.2 中按原核自己的完整非负前件使用，支付两个返回到表示的条件桥。
- [续卷 V 定义 1.1、定理 1.3 与 6.1](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md) 保留实际 $U1=1$；[续卷 IV 定义 1.1 与定理 5.1](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_IV.md) 还保留交换幺半群与实际 $U0=0$。这些实际恒等式没有在本节自由模型中成立，故不以那些事件定理跳过任意标记接口。§19 的真群、实际逆元与对称性也没有在此获得。

正定核的 Radon–Nikodym 型表示以正定核及其差仍正定的核序为前件；当前逐点费用界 $0\le d\le K$ 未供应这些前件。该类结果不承担本节的证明，也不将事件极化的 Loewner 支配作为输入。

**命题 20.9（退化情形、漂移与未付接口）。**定义 20.1 的零总空间及空测试不产生归一化准备；固定三维模型不产生物理三维结论，也不自动实现其数学事件和数组运算。具体地：若 $H=0$，则 $K=0$，每个事件都为零，唯一算子为零且也是该空间的 $I_H$；空完整测试强制 $K=0$，因最小性也有 $H=0$。单事件完整测试只有总事件，其效果是 $I_H$；零事件和全事件分别有 $0$ 和 $I_H$。非零漂移不被完整 (R) 与事件支配排除，零漂移也不强迫实际 $U1=1$。

**证明。**前三个结论直接由非负完整性、最小性和恒等算子的定义得到。为核对非零漂移边界，取 $M=(\mathbb C,+)$、真实单位 $0$、$Uz=\omega z+t$、$Fz=z$，事件 $d(z,w)=|z-w|^2/2$，另一带索引事件为 $K-d=d$。按 (20.12) 有完整 (R)，且

$$
d(U0,0)=|t|^2/2.
\tag{20.43}
$$

所以不能要求所有事件的单位标记费用在非零漂移时消失。(20.8) 的固定总模型本身也有漂移 $e_3$。另一方面，(20.19) 的零总漂移来自向量递归，但自由语法仍保留不同项 $U1,1$，故不推出实际单位固定。

$T_2,T_3$ 都有无限多不同的 $U^n1$，所以三个复坐标仅是总几何的搜索界，载体不是有限集合。三相 $k=0,1,2$、三个来源或三标签测试、复 Hilbert 维数、物理空间维数和 Bloch 维数各由不同对象定义；没有在这些构造中提供相互识别的映射。零对费用只能给该坐标事件值为零；(20.16)、(20.33) 从未以此推出完整行列纤维下降。证毕。

本节仍须二选一地解决 $\max_{q\in\mathcal A}\Delta(q)=0$ 或构造一个总 $q\in\mathcal A$ 使 $\Delta(q)>0$；等价的纯相位普遍生成元三角也未在此证成或由总反例推翻。更大的无 Hilbert 输入问题中，原始完整 $(R)\Rightarrow\mathrm C_3$ 及原始总几何入口仍未由这些归约解决。

若唯一整体态 $\Omega$ 为建模前提，原给定菜单仍是给定菜单，新自由菜单与数组操作只是数学模型。它们不供应实际非零准备、全效果可取得性、预测与实际内部读出的对应、观察者与参考、联合及条件历史、张量组成、经校准仪器、门和过程的实际组合、物理时间或生成元。定理 6.2 及 §11.2 的相应接口仍须分别供应；本节不由静态比较归约声称完整量子起源。

## 追加锚（本行以下为增补区）

## 21. 真群上有向非负全关系自动恢复对称性

### 21.1 同一个原群与有向零纤维

**定义 21.1（不输入对称性的真群模型）。**令 $G$ 为任意实际群，单位为 $1$，$U:G\to G$ 为任意总映射。令 $d:G^2\to[0,\infty)$ 处处有限且 $d(g,g)=0$，对全部有序原标签要求

$$
\sum_{k=0}^2 d(aU^ku,bU^kv)=3d(a,b)+3d(u,v)
\qquad(a,b,u,v\in G).
\tag{21.1}
$$

不输入 $d$ 的对称性、负型、返回或表示，不要求 $G$ 交换，不要求 $U$ 保单位、保乘法、满射、连续或三周期。结合律和实际逆元属于给定 $G$ 的输入。记

$$
p_j=U^j1,\qquad T_jz=(U^jz)p_j^{-1},\qquad
f(x)=d(x,1).
\tag{21.2}
$$

**引理 21.2（有向核沿正规零子群的双端下降）。**在定义 21.1 下，共同右移不变性成立：

$$
d(ax,bx)=d(a,b),\qquad d(a,b)=f(ab^{-1}).
\tag{21.3}
$$

再设 $Z\lhd G$ 是一个给定的正规子群，满足

$$
f(z)=0,\qquad T_jz\in Z
\quad(z\in Z,\ j=0,1,2).
\tag{21.4}
$$

则原来的同一个有向核在两个端点独立下降到 $G/Z$：

$$
f(xz)=f(x),\qquad d(az,bw)=d(a,b)
\quad(x,a,b\in G,\ z,w\in Z).
\tag{21.5}
$$

这里不要求 $Z$ 等于 $f$ 的整个零集，也不以 $d(1,z)=0$ 或完整行列不可见性为额外前件。本引理只断言核的下降；一般给定 $Z$ 下，尚不据此断言 $U$ 在陪集上良定义。

**证明。**共同右移部分直接采用引理 19.2 证明中通向 (19.5) 的论证；该部分没有使用对称性。具体地，固定 $a,b$，令 $h(x)=d(ax,bx)$。群非空及处处有限性使

$$
0\le m:=\inf_{x\in G}h(x)\le h(1)<\infty.
$$

将 (21.1) 用于背景 $ax,bx$ 和增量 $u,u$，由实际结合律得

$$
\sum_{k=0}^2h(xU^ku)=3h(x).
$$

任一项至少为 $m$。给定目标 $y\in G$，对每个 $x$ 取实际群元 $u=x^{-1}y$，第零项于是给

$$
0\le h(y)-m\le3(h(x)-m).
$$

右端对 $x$ 的下确界为零，所以 $h(y)=m=h(1)$。这不要求下确界取到，也不使用 $U$ 的逆。共同右移取 $x=b^{-1}$ 即得 (21.3)。此时没有推出 $f(x^{-1})=f(x)$。

现固定 $x\in G$，令

$$
m_x=\inf_{z\in Z}f(xz),\qquad 0\le m_x\le f(x)<\infty.
$$

对任意 $z,w\in Z$，把 (21.1) 用于背景 $xz,1$ 和增量 $w,1$；(21.3) 与 $f(w)=0$ 给

$$
\begin{aligned}
\sum_{j=0}^2 f(xzT_jw)
&=\sum_{j=0}^2 d(xzU^jw,p_j)\\
&=3f(xz)+3f(w)=3f(xz).
\end{aligned}
\tag{21.6}
$$

由 (21.4)，三个参数都在同一个右陪集 $xZ$ 中，每项至少为 $m_x$。给定目标 $z_0\in Z$，对每个 $z\in Z$ 取实际 $w=z^{-1}z_0\in Z$。因为 $p_0=1$、$T_0w=w$，第零项正是 $f(xz_0)$，故

$$
0\le f(xz_0)-m_x\le3\bigl(f(xz)-m_x\bigr).
\tag{21.7}
$$

对 $z$ 取下确界，得 $f(xz_0)=m_x$；再取 $z_0=1$，得 $m_x=f(x)$。这证明 (21.5) 的第一式。最后，实际群运算与正规性给

$$
\begin{aligned}
d(az,bw)
&=f(azw^{-1}b^{-1})\\
&=f\bigl((ab^{-1})(bzw^{-1}b^{-1})\bigr)
=f(ab^{-1})=d(a,b),
\end{aligned}
\tag{21.8}
$$

因为 $bzw^{-1}b^{-1}\in Z$。两个端点都保留原 $d$ 的次序，并未用转置核替代其中一行。$Z$ 是子群已经保证 $z^{-1}\in Z$；不需另加关于逆元的费用条件。证毕。

### 21.2 不带对称性前件的真群分类

**定理 21.3（有向全关系在真群上迫出完整仿射复几何）。**给定任意实际群 $G$、任意总映射 $U$ 及处处有限、非负、零对角的原有向核 $d$，完整 (21.1) 等价于存在完备复 Hilbert 空间 $H_d$ 及映射 $F_d:G\to H_d$，使

$$
\begin{gathered}
F_d1=0,\qquad F_d(gh)=F_dg+F_dh,\\
F_d(Ug)=\omega F_dg+t_d,\qquad t_d=F_d(U1),\\
d(g,h)=\|F_dg-F_dh\|^2,\qquad
\omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\end{gathered}
\tag{21.9}
$$

因而 $d$ 的对称性、全部有限负型及两个普遍第三标记返回都是结论：

$$
d(ap_3,b)=d(a,b),\qquad d(a,bp_3)=d(a,b)
\quad(a,b\in G).
\tag{21.10}
$$

最小表示 $H_d=\overline{\operatorname{span}_{\mathbb C}F_d(G)}$ 唯一到唯一的保标签酉同构。不要求漂移为零；零核也在本定理范围内，其最小空间为零。

**证明。**只在同一个原 $G,U$ 上定义辅助总核

$$
K(a,b)=d(a,b)+d(b,a).
\tag{21.11}
$$

交换 (21.1) 的两个背景标签及两个增量标签，正给 $d^{\mathsf T}$ 的完整关系。因此 $K$ 满足完整关系，且处处有限、非负、对称、零对角。将定理 19.4 的 $c$ 精确取为此 $K$；其实际群及任意总标记前件均由原 $G,U$ 供应，得到可取最小的完备复空间 $H$ 及映射 $F$，满足

$$
F1=0,\quad F(gh)=Fg+Fh,\quad
F(Ug)=\omega Fg+t,\quad t=F(U1),\quad
K(a,b)=\|Fa-Fb\|^2.
\tag{21.12}
$$

这份 Hilbert 几何是对辅助对称核应用既有定理所得，不是原 $d$ 的输入。

令 $Z=\ker F$。由于 $F$ 是从实际群到 Hilbert 加法群的同态，$Z$ 是实际正规子群；特别，交换子的不可见性是这个同态的后果。由 $0\le d\le K$，对 $z\in Z$ 有

$$
0\le d(z,1)\le K(z,1)=\|Fz\|^2=0.
$$

令 $t_0=0,t_1=t,t_2=(1+\omega)t$。由仿射递推及群同态，

$$
F(T_jz)=F(U^jz)-F(p_j)=\omega^jFz
\quad(j=0,1,2),\qquad
F(p_3)=(1+\omega+\omega^2)t=0.
\tag{21.13}
$$

所以 $T_jZ\subseteq Z$ 且 $p_3\in Z$。现在把引理 21.2 应用于原来的同一个有向 $d$ 和这个 $Z$，先得两个端点的完整纤维下降，再在 (21.5) 分别取 $(z,w)=(p_3,1),(1,p_3)$，得到 (21.10)。这里没有仅凭 $K$ 的零费用就识别原 $d$ 的行列。

至此，原 $G,U,d$ 已具有全部有序标签上的完整非负 (R)、零对角和两个普遍返回。[续卷 W 定理 43.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#43-原核的有界轴刚性与第三标记返回下的完整仿射几何)可在这同一个原对象上直接使用，给原 $d$ 的完整仿射表示，因而给对称性与全部有限负型。W43.3 的返回前件在此之前已经支付。

于是 (21.11) 成为 $K=2d$，故也可在 (21.12) 的同一个完备最小空间 $H$ 上直接取

$$
F_d=F/\sqrt2,\qquad t_d=t/\sqrt2.
\tag{21.14}
$$

其平方距离恰为原 $d$，群加法、仿射漂移和最小闭张成均保留。最小表示唯一性直接复用定理 1.3；不重新证明分类或 Gram 唯一性。

反向，若有 (21.9)，则两个端点的第 $k$ 次漂移相消。令 $X=F_da-F_db$、$Y=F_du-F_dv$，定理 19.4 反向证明中的恒等式

$$
\sum_{k=0}^2\|X+\omega^kY\|^2=3\|X\|^2+3\|Y\|^2
$$

直接给 (21.1)。证毕。

定理 21.3 对真群分支接续定理 19.4：只删除其核对称性输入，保留原实际群、全部有序标签、任意总标记、有限非负零对角及完整四变量关系。它没有要求 $U$ 在原群上是同态。表示取得后，$G/\ker F_d$ 才通过 $[g]\mapsto F_dg$ 识别为可见加法群；归一化词 $g\mapsto(Ug)(U1)^{-1}$ 在该商上诱导乘以 $\omega$ 的自同构。原 $U$ 在可见像上仍是带 $t_d$ 的仿射作用，实际标签上的 $U^3g=g$ 不由此宣告。

### 21.3 给定总空间上的原事件效果

**推论 21.4（真群受支配事件不另需对称或返回）。**令 $G$ 是实际群，$U:G\to G$ 任意。给定满足 (20.1) 的同一个最小复 Hilbert 空间 $H$、可加 $F$ 和任意漂移 $t$，记 $K(a,b)=\|Fa-Fb\|^2$。若一个处处有限、非负的原有向核 $d$ 满足完整 (21.1) 且 $d\le K$，则在这个给定的 $H$ 上存在唯一复正收缩 $E$，满足

$$
0\le E\le I_H,\qquad
d(a,b)=\langle Fa-Fb,E(Fa-Fb)\rangle
\quad(a,b\in G).
\tag{21.15}
$$

若实际给定的完整有限索引测试 $(d_j)_{j\in J}$ 各满足完整 (21.1)、处处有限非负，且 $\sum_{j\in J}d_j=K$，则各事件在这个同一个给定最小 $H$ 上有唯一效果 $E_j$，并有

$$
\sum_{j\in J}E_j=I_H.
\tag{21.16}
$$

各原事件的对称性、负型和第三标记返回都不作为输入。

**证明。**支配先给 $d(a,a)=0$。在这个给定 $F$ 下取实际正规子群 $Z=\ker F$。式 (21.13) 仍成立，且 $d(z,1)=0$ 由支配取得，所以引理 21.2 直接给原 $d$ 的两个普遍返回。将命题 20.2 中的 $M,U,H,F,K,d$ 逐一取为当前同名对象；该命题的全部前件已经成立，直接得到 (21.15) 和唯一性。其证明所需补核是同一原 $G$ 上的 $K-d$，不假定费用的逐点支配等于极化核的 Loewner 支配。

对原有限索引测试，非负完整和逐项给 $d_j\le K$；上段为每个原 $d_j$ 支付两个返回，再直接应用命题 20.2 的完整测试结论，得到 (21.16) 与各效果唯一性。效果构造、复线性延拓和完整性均复用定理 6.2 与命题 20.2，不另计为新的效果表示证明。证毕。

重复或零事件保留原索引：两个相同的事件核给两个相同但分别计入完整和的效果，零事件给零效果，单事件完整测试给 $I_H$。若 $K=0$，则全部事件为零，最小性给 $H=0$，唯一算子为零且也是 $I_H$；空完整测试同样只在这个退化情形出现。没有要求实际各支等质量，也不删除原零质量或不等质量；实际概率的归一化仍只在严格正的原总质量处进行。对于非零输入差 $x=Fa-Fb$，表示给数学比值 $\langle x,E_jx\rangle/\|x\|^2$；它接到哪一份实际准备和完整菜单，仍由原事件来源条件决定。

### 21.4 承重增量、原来源与完整剩余问题

本节的仓内条件推导是：在实际真群上，从原有向非负全关系本身恢复对称性及第三标记返回，不再为真群原核或真群各事件单独输入它们。承重步骤是引理 21.2 对给定正规零子群的有向双端下降，以及将该步骤用于 $d+d^{\mathsf T}$ 的 Hilbert 零纤维。引理 19.2 的共同右移及下确界方法、定理 19.4 的对称真群分类、W43.3 的返回到完整仿射几何、定理 1.3 的唯一性、定理 6.2 与命题 20.2 的效果结论全部按原前件复用；这些已有分类、极化、完成和效果构造不重复计为新增结果。W 的对应条目沿用 §20.5 所列来源身份。

群二次方程与极化的文献条件沿本卷 §11、对应 19.5 及 W 对应 41.4 所载边界理解：de Place Friis–Stetkær 的 [DOI 10.5486/pmd.2006.3270](https://doi.org/10.5486/pmd.2006.3270) 与 Akkaoui–Fadli 的 [DOI 10.2478/amsil-2024-0023](https://doi.org/10.2478/amsil-2024-0023) 不被作为任意总 $U$、完整有向四变量定理的现成来源。本节只给相对上述仓内结果的推导，不主张文献检索穷尽或历史原创性。

完整物理来源继续逐字义采用[环境耦合卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#6-完整原问题与七项物理合同的精确身份)及[两角正性证书卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md#49-不缩减的全文来源与七项量子消费者)的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，包括各自逐层钉版、递归纳入全文及七项消费者的全部原量词。本节的群核 $d,K$ 与这些原接口中的同名字母不自动相认。准备、原事件及菜单、全质量、parent/ready、共同参考、副本与相关联合、typed 全输出、全部合法历史／未来、真实返回、记录、拒绝／失败／停止／销毁、时钟及过程合同均按该精确来源继续承担，不由本节的核商或数学逆元供给。特别，实际 analyzer 的指定接受关联、CountRead 的同一接受完整活动输出和读后 ready、全输入／全合法未来 Return 都没有在此构造。

一般有单位 magma 不具备本证明两次使用的实际群除法：$x^{-1}y$ 与 $z^{-1}z_0$ 不能仅由原二元组合或尚未下降的 $U$ 形式制造。因此一般原始 $(R)\Rightarrow\mathrm C_3$、无 Hilbert 输入的原始总几何，以及定义 20.1 对任意 magma 的整个 $\mathsf{Eff}$ 断言仍未在此解决；固定自由模型上的返回差最大值也没有由真群结论变成零。实际群前件没有从同一 $\Omega$ 的原始组合关系推出。完整量子起源目标保持原范围并且未完成。

### 21.5 中文直观说明

先比较两条实际历史接上同一条尾巴后的读数。真群里的除法使我们从任何尾巴出发，都能把某个实际增量选成通往任意目标尾巴的那一步。完整关系说三个非负读数的平均固定；每项都不低于同一个下确界，于是把出发读数压近下确界，就迫使目标读数也等于它。这说明共同尾巴不改变原有向比较，全程不用先交换两个比较端点。

接着只对辅助总核 $d+d^{\mathsf T}$ 使用已经成立的对称真群定理。它给出的 Hilbert 表示把某个正规子群看成零。原有向读数虽还没有被证明对称，却被这个总核支配，因而在该子群上的单位费用也为零。沿同一个零陪集再作刚才的下确界论证，就能证明原读数在两个端点都无法分辨代表元。第三次标记后的单位恰落在这个零子群中，所以它的两端返回是推出来的，不再是另加的输入。既有返回分类随后给出同一个原读数的复 Hilbert 平方几何和等边三相作用；实际漂移可以非零。

少掉的只是实际真群分支的对称性与独立返回前件。原始组合未必是群，纸面群逆元也不是物理逆操作；复 Hilbert 完成不制造可取得准备、全菜单、真实相关联合或读后返回装置。原三相指标、复空间维数与物理空间维数仍是不同对象；同一 $\Omega$ 的全部来源和七项消费者合同继续逐项保留，完整量子供给仍须另行完成。

## 追加锚（本行以下为增补区）
## 22. 实际产品右输入的三相运输与自由正规障碍

本节把 W 续卷的平稳总模型直接用于实际乘积作为右输入的情形，并给出一个独立的可数载体、处处有限值的总自由正规模型。所用的仓内关系是 [W 引理 17.1](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#17-实际单位碰撞与全部探针上的标记消去) 的同层滑移、[W 定理 44.2 与推论 44.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#44-保全实际第三标记返回的平稳扩张与双向来源链) 的平稳扩张和 [W 定理 45.2–推论 45.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#45-共同平移核的实际乘积平分与三相背景运输) 的共同背景运输；新增部分是这些已付关系在实际乘积右输入、二坐标预算和自由正规模型中的应用。这里不把来源集合对乘法封闭作为前提。

### 22.1 实际乘积右输入的四块运输

**命题 22.1（四块实际乘积运输）。**取 W 定理 44.2 的同一个总模型 $(N,\star,e,V,d)$、保乘法和单位的自同构 $A$，其中 $AV=VA$、$d(As,At)=d(s,t)$。对 $m\in\mathbb Z$ 置

$$
F_m(s,t)=d(A^ms,t),\qquad T=V^3.
$$

每个 $F_m$ 都是处处有限、非负的完整 $(R)$ 核，且同步 $V$ 等距；仅 $F_0=d$ 本身被要求零对角。以下定义对所有实际输入成立：

$$
I_0(a,u)=T(a\star u),\qquad I_1(a,u)=a\star T(u)
\qquad(a,u\in N),
$$

以及

$$
J=\{a\star T(u):a,u\in N\}.
$$

则对任意 $a,b,u,v\in N$，四个有序块同时对所有 $m$ 成立：

$$
F_m\bigl(I_\epsilon(a,u),I_\eta(b,v)\bigr)=F_m(a\star u,b\star v)
\qquad(\epsilon,\eta\in\{0,1\}).
\tag{22.1}
$$

这里 $a\star u$、$b\star v$ 是实际右输入；不要求它们属于任何来源集合，也不把来源等式延伸到乘积。

**证明。**固定 $a,b,u,v\in N$，对 $n\ge0$ 置

$$
h_n=F_m(a\star V^nu,b\star V^nv).
$$

把完整 $(R)$ 用于实际四元组 $(a,b,V^nu,V^nv)$。同步 $V$ 等距给
$F_m(V^nu,V^nv)=F_m(u,v)$，所以对每个 $n\ge0$，

$$
h_n+h_{n+1}+h_{n+2}=3F_m(a,b)+3F_m(u,v),
$$

右端与 $n$ 无关。相邻两式相减得到 $h_{n+3}=h_n$，特别是 $h_3=h_0$。取原四元组 $(a,b,u,v)$，这正给出 $(1,1)$ 块：

$$
F_m(a\star T(u),b\star T(v))=F_m(a\star u,b\star v).
$$

$(0,0)$ 块只用同步 $V^3$ 等距：

$$
F_m(T(a\star u),T(b\star v))=F_m(a\star u,b\star v).
$$

对 $(1,0)$ 块，在同一个滑动恒等式中取背景 $(a,e)$、右输入 $(u,b\star v)$。其第零项和第三项分别是

$$
h_0=F_m(a\star u,e\star(b\star v))=F_m(a\star u,b\star v),
$$

$$
h_3=F_m(a\star T(u),e\star T(b\star v))
   =F_m(I_1(a,u),I_0(b,v)).
$$

对 $(0,1)$ 块，取背景 $(e,b)$、右输入 $(a\star u,v)$。同样，

$$
h_0=F_m(e\star(a\star u),b\star v)=F_m(a\star u,b\star v),
$$

$$
h_3=F_m(T(a\star u),b\star T(v))
   =F_m(I_0(a,u),I_1(b,v)).
$$

所有四元组都是真实标签，始终保留原乘法括号；没有使用来源对乘法封闭，也没有把 $V$ 当作乘法自同态或重括号。证毕。

取 $b=a$、$v=u$ 并令 $m=0$，(22.1) 给出

$$
 d\bigl(T(a\star u),a\star T(u)\bigr)=0,\qquad
 d\bigl(a\star T(u),T(a\star u)\bigr)=0.
\tag{22.2}
$$

这是两端的零比较，不是实际标签等式。其在 $J$ 上能推出的行列事实可以精确写成：对任意 $a,u\in N$ 及 $z=b\star T(v)\in J$，

$$
d\bigl(I_0(a,u),z\bigr)
 =d(a\star u,b\star v)
 =d\bigl(I_1(a,u),z\bigr),
$$

$$
d\bigl(z,I_0(a,u)\bigr)
 =d(z,I_1(a,u)).
$$

前一式用 $(0,1)$、$(1,1)$ 两块，后一式用相同两块交换有序输入；它们只说明对集合 $J$ 的这些行、列读数相同。另若 $d(x,y)=d(y,x)=0$，则把 $x,y$ 放进同一个由 $V$ 与 $\star$、固定实际参数组成的有限项上下文 $C[-]$，仍有

$$
d(C[x],C[y])=d(C[y],C[x])=0.
$$

这是对上下文深度的结构归纳：$V$ 步用同步等距；二元步在另一输入相同的情况下，把完整 $(R)$ 用于该二元步的两个标签，右端为零，三项非负性遂使其中的 $k=0$ 项为零，反向次序同理。这个结论只保留共同上下文中的双向零比较，不给出任意行不变性、任意列不变性、零关系的传递性或全域同余。

### 22.2 二坐标的精确背景预算

**命题 22.2（两坐标四块预算）。**在 $N^2$ 上作完整的逐坐标定义

$$
e_{[2]}=(e,e),\\
z\star_{[2]}w=(z_1\star w_1,z_2\star w_2),\\
V_{[2]}z=(Vz_1,Vz_2),\\
A_{[2]}z=(Az_1,Az_2).
$$

于是 $e_{[2]}$ 是真实双侧单位，$V_{[2]}A_{[2]}=A_{[2]}V_{[2]}$。置

$$
 d^{[2]}(z,w)=\frac12\sum_{j=1}^2d(z_j,w_j),\qquad
 F_m^{[2]}(z,w)=\frac12\sum_{j=1}^2F_m(z_j,w_j).
$$

逐坐标的完整 $(R)$ 在整个 $N^2$ 上由有限平均继承：对任意四个 $N^2$ 标签，逐坐标写出完整关系后相加并除以 $2$ 即得 $F_m^{[2]}$ 的完整关系。以下只复用这一有限平均。令

$$
K=\{a\in N:Aa=a\},\qquad S=\{u\in N:Vu=Au\}.
$$

对 $a,b\in K$、$u,v\in S$ 定义实际数组

$$
 X(a,u)=\bigl(V(a\star u),V^2(a\star u)\bigr),\qquad
 Y(a,u)=\bigl(a\star Vu,a\star V^2u\bigr),
$$

以及有序背景费用

$$
 q(a)=d(a,e),\qquad r(b)=d(e,b),\qquad
 Q(a,b)=\frac{3q(a)+3r(b)-d(a,b)}2\ge0.
$$

对 $u\in S$，两种数组在共同实际锚点上相等：

$$
X(e,u)=Y(e,u)=(Vu,V^2u).
$$

这个锚点不必是实际单位 $e_{[2]}$；这里不作 $e\in S$ 的假设。

则对所有 $m$ 同时有四块恒等式

$$
\begin{aligned}
 F_m^{[2]}(X(a,u),X(b,v))
 &=F_m^{[2]}(Y(a,u),Y(b,v))
 =d(a,b)+F_m(u,v),\\
 F_m^{[2]}(X(a,u),Y(b,v))
 &=F_m^{[2]}(Y(a,u),X(b,v))
 =Q(a,b)+F_m(u,v).
\end{aligned}
\tag{22.3}
$$

$Q$ 保留有序角色，不假定对称或零对角。其非负性只用原单项界 $d(a,b)\le3(q(a)+r(b))$。

**证明。**同类的两个等式分别由同步 $V$ 等距和 W 推论 45.3 的固定背景平分。对 $XY$ 块，在同一实际模型的 $(R)$ 中代入背景 $(e,b)$、右输入 $(a\star u,v)$。右端为

$$
3r(b)+3F_m(a\star u,v)
=3r(b)+3q(a)+3F_m(u,v),
$$

而 $k=0$ 项为 $F_m(a\star u,b\star v)=d(a,b)+F_m(u,v)$。余下的 $k=1,2$ 两项正是两坐标和，故相减第零项后除以二得到第一混合式。背景 $(a,e)$、右输入 $(u,b\star v)$ 给出另一混合式，且保留 $q$、$r$ 的有序位置。证毕。

令 $z=a\star u$、$b=a$、$v=u$，则 $A^kz=a\star V^ku$。从 (22.3) 的 $m=0$ 混合块得到精确的两步预算

$$
\begin{aligned}
\sum_{k=1}^2d\bigl(V^kz,A^kz\bigr)
&=\sum_{k=1}^2d\bigl(A^kz,V^kz\bigr)\\
&=3\,[q(a)+r(a)].
\end{aligned}
\tag{22.4}
$$

(22.4) 与 (22.2) 比较的是两种不同阶段：前者给实际乘积输入的两坐标背景费用，后者给同一总模型中的互相零比较；它们不把零费用升级为实际相等，也不供应来源闭包。令 $H_m=F_m-F_0$，并令 $E,G$ 各自独立取 $X$ 或 $Y$，则四块统一满足

$$
 H_m^{[2]}(E(a,u),G(b,v))=H_m(u,v).
\tag{22.5}
$$

因此四个 $H_m$ 块都保留同一个 $H_m(u,v)$；特别地，对 W 定理 44.2 的来源 $x_0,y_0$ 和 $\delta=H_3(x_0,y_0)$，取 $m=3,u=x_0,v=y_0$ 时四个块都保留 $\delta$。这里没有把 $F_0$ 证明成 Fourier 常数模，也没有得到关于 $m$ 的调和性；数组仍只是坐标构造，不是物理副本。

### 22.3 全域自由正规模型与有限置换障碍

下面给出一个独立的可数载体、处处有限值的总正规模型。它只使用单位规则、源原子和正规形构造，不输入结合律、交换律或额外乘法等式。

**构造 22.3（自由正规模型）。**取两族彼此不同的源原子 $x_i,y_i\ (i\in\mathbb Z)$。令 $N$ 的正规形由

$$
e,\qquad x_i,y_i\ (i\in\mathbb Z),\qquad \nu(s),\qquad \langle s,t\rangle
$$

递归生成，其中 $\nu(s)$ 只在 $s$ 不是源原子时可用，$\langle s,t\rangle$ 只在 $s,t\ne e$ 时可用；所有正规形按构造子和参数严格区分。有限字符串树由可数源原子生成，故载体 $N$ 可数。定义真实单位乘法

$$
e\star s=s\star e=s,\qquad s\star t=\langle s,t\rangle\quad(s,t\ne e).
$$

定义总标记

$$
Vx_i=x_{i+1},\qquad Vy_i=y_{i+1},\qquad Vs=\nu(s)
\qquad(s\text{ 为任意非源正规形，包括 }e).
$$

再令

$$
Ae=e,\qquad Ax_i=x_{i+1},\qquad Ay_i=y_{i+1},\qquad
A\nu(s)=\nu(As),\qquad A\langle s,t\rangle=\langle As,At\rangle.
$$

则 $A^{-1}$ 将源指标减一，$A$ 是真实自同构，$AV=VA$；由单位、标记和乘法从 $e$ 生成的子代数逐点被 $A$ 固定。这里没有给非结合二元词增加任何结合或交换关系。

取

$$
\zeta=e^{2\pi i/3},\qquad h=(1-\zeta)^{-1},\qquad \tau=(0,1)\in\mathbb C^2,
$$

并递归定义 $F:N\to\mathbb C^2$：

$$
F(e)=0,\qquad F(x_i)=(\zeta^i,h),\qquad F(y_i)=(0,h),
$$

$$
F(\langle s,t\rangle)=F(s)+F(t),\qquad
F(\nu(s))=\zeta F(s)+\tau.
\tag{22.6}
$$

因 $\zeta h+1=h$，所有实际标记都满足

$$
F(Vs)=\zeta F(s)+\tau.
$$

由此三次迭代给出

$$
F(V^3s)=F(s)\qquad(s\in N).
$$

令 $p_3=V^3e=\nu^3(e)$。则

$$
F(p_3)=F(V^3e)=F(e)=0,
$$

并且对任意 $a\in N$，

$$
F(a\star p_3)=F(a)+F(p_3)=F(a),\qquad
F(p_3\star a)=F(p_3)+F(a)=F(a).
$$

所以对任意 $a,b\in N$，

$$
d(a\star p_3,b)=d(a,b),\qquad
d(a,b\star p_3)=d(a,b),
$$

两端的实际 $\mathrm C_3$ 返回都成立；这些是核读数等式，不是对象等式，且 $p_3=\nu^3(e)\ne e$。

若 $D(z_1,z_2)=(\zeta z_1,z_2)$，则正规形归纳给 $F(As)=DF(s)$；$D$ 是酉的。令

$$
d(s,t)=\lVert F(s)-F(t)\rVert^2.
$$

这是一个可数载体上的处处有限值、非负且零对角的总关系模型。事实上对任意四个实际输入，令 $X=F(a)-F(b)$、$Y=F(u)-F(v)$。单位因子被实际乘法删除但其 $F$ 值为零，且标记漂移在差中抵消，所以

$$
F(a\star V^ku)-F(b\star V^kv)=X+\zeta^kY.
$$

于是有限 Fourier 恒等式

$$
\sum_{k=0}^2\lVert X+\zeta^kY\rVert^2
=3\lVert X\rVert^2+3\lVert Y\rVert^2
$$

给出完整 $(R)$；同时 $d(As,At)=d(s,t)$。这里 $p_1=Ve=\nu(e)$、$p_2=V^2e$ 都有范数平方 $1$，故原单位预算

$$
B_0=\sum_{j=1}^2[d(p_j,e)+d(e,p_j)]=4,
$$

而 $F(Ve)=\tau\ne0$，所以漂移非零。另一方面 $F(V^3s)=F(s)$，因此该模型满足全局第三标记返回，返回缺陷 $\delta=0$；这不识别正规形标签，因为 $p_3=\nu^3(e)\ne e$，一般非源正规形的 $V^3s$ 也不等于 $s$。

**命题 22.4（有限坐标置换不能保留非源语法）。**对非源正规形定义外层连续标记数

$$
\ell(e)=0,\qquad \ell(\langle s,t\rangle)=0,\qquad
\ell(\nu(s))=1+\ell(s).
$$

$A$ 保持 $\ell$，而 $V$ 作用于任意非源正规形时使 $\ell$ 增一并仍为非源。因此对每个非源 $s$ 和每个正整数 $r$，都有

$$
V^rs\ne A^rs.
\tag{22.7}
$$

实际来源集合恰为

$$
S=\{s:Vs=As\}=\{x_i,y_i:i\in\mathbb Z\}.
\tag{22.8}
$$

对任意正整数 $n$，在总坐标 $N^n$ 上令 $V_{[n]}$、$A_{[n]}$ 逐坐标作用。任意坐标置换 $\sigma\in\mathfrak S_n$ 都与这两个逐坐标作用相容。若

$$
V_{[n]}z=\sigma A_{[n]}z,
$$

则对 $\sigma$ 的每一个长度为 $r$ 的循环，迭代该等式 $r$ 次；因 $\sigma$ 与 $V_{[n]}、A_{[n]}$ 交换，循环中的每一坐标 $i$ 都满足

$$
V^rz_i=A^rz_i.
$$

由 (22.7)，所有坐标都必须是源原子。故任何保留一个非源坐标的有限置换提升都不可能满足这条实际来源等式；特别，未约简的实际二元积也不能被这样的置换修复。这个障碍只针对路线 $V_{[n]}=\sigma A_{[n]}$，不延伸为对所有有限构造、可观测提升或来源存在性的不可行性定理。

一个非空的饱和实例是 $p_1=\nu(e)$、$a=p_1\in K$、$u=x_0\in S$。令 $z=p_1\star x_0$，它是非源二元正规形；$q(p_1)=r(p_1)=1$，所以 (22.4) 给出

$$
\sum_{k=1}^2d(V^kz,A^kz)=6,
$$

而 (22.2) 给出 $d(Tz,p_1\star T(x_0))=d(p_1\star T(x_0),Tz)=0$。这同时显示两步背景预算可以非零而第三阶段比较为零。

### 22.4 范围与未解边界

22.1 是把已付滑移和共同背景运输应用到实际乘积右输入；22.2 是与来源变量无关的精确两坐标预算；22.3 是一个可数载体、处处有限值的总正规模型及其有限坐标置换障碍。它们都不证明来源闭包，不证明一般原始完整 $(R)\Rightarrow\mathrm C_3$，也不提供 $\delta\ne0$ 的总反模型；上面的自由模型满足全局第三标记返回且返回缺陷为 $\delta=0$。一般原始 $(R)\Rightarrow\mathrm C_3$ 仍是开放边界。

本节的自由乘积、有限 Fourier 反演和正规形归纳是经典工具在本仓对象上的构造与应用，不主张历史原创性或穷尽检索。它不增加实际 $\Omega$、准备、效果、质量、参考、联合和条件历史、复制、全菜单、固定支撑、中间截断、记录、拒绝／失败／停止、时钟、未来合同或物理过程；这些原量词与接口继续由本卷既有来源逐项承担，也不从该抽象模型推出物理量子来源。§21 已在实际群分支删除独立的对称性输入；本节在一般原始类给出有限提升路线的精确控制和限制，未添加群假设，也未声称新的全局最小几何完成。

## 追加锚（本行以下为增补区）

## 23. 实际右群作用把群内零纤维传播到全部原标签

### 23.1 原载体上的充分结构

**定义 23.1（实际群尾巴与整载体右作用）。**令 $M$ 为带实际二元运算 $\cdot$ 和真实双侧单位 $e$ 的集合；$e$ 即前文的 $1$。令 $U:M\to M$ 为任意总映射。给定处处有限、非负、零对角的原有向核 $d$，对全部有序原标签及下式实际括号要求

$$
\sum_{j=0}^2d(a\cdot U^ju,b\cdot U^jv)
=3d(a,b)+3d(u,v)
\qquad(a,b,u,v\in M).
\tag{23.1}
$$

充分结构是存在 $G\subseteq M$，满足：$e\in G$，继承的同一个实际乘法使 $G$ 成为群，群逆元也是 $G$ 中的实际标签；$U(G)\subseteq G$；并且

$$
(a\cdot g)\cdot h=a\cdot(g\cdot h)
\qquad(a\in M,\ g,h\in G).
\tag{23.2}
$$

式 (23.2) 是原右乘本身在整个 $M$ 上的结合右 $G$-作用，单位作用由原双侧单位律给出；没有换成另造的抽象作用。不要求作用忠实或在 $M$ 上传递。$G$ 外的乘积不要求结合、可逆、消去或交换。$U$ 不要求保单位、保乘法、满射、周期或连续；不输入 $d$ 的对称性、三角、负型或 Hilbert 表示。记

$$
p_j=U^je\in G,\qquad P_j(a)=a\cdot p_j.
\tag{23.3}
$$

$p_j$ 按实际标记轨道定义，不以 $p_1$ 的重复乘积定义；两者不被预先等同。

### 23.2 两次下确界给出的整载体传播

**定理 23.2（共同群尾巴与独立零尾巴都不改变原比较）。**在定义 23.1 下，对全部原 $a,b\in M$ 和 $g\in G$，有

$$
d(a\cdot g,b\cdot g)=d(a,b).
\tag{23.4}
$$

将定理 21.3 精确用于限制 $G,U|_G,d|_{G^2}$，记所得最小表示为 $F_G:G\to H_G$，漂移为 $t_G=F_G(Ue)$，并令 $Z=\ker F_G$。则在全部原标签上有两个端点的独立不变性：

$$
d(a\cdot z,b\cdot w)=d(a,b)
\qquad(a,b\in M,\ z,w\in Z).
\tag{23.5}
$$

特别 $p_3\in Z$，所以两个普遍第三标记返回成立：

$$
d(P_3a,b)=d(a,b),\qquad d(a,P_3b)=d(a,b)
\qquad(a,b\in M).
\tag{23.6}
$$

**证明。**第一步固定任意原 $a,b\in M$，只在实际群尾巴上定义

$$
h(x)=d(a\cdot x,b\cdot x),\qquad
m=\inf_{x\in G}h(x),\qquad 0\le m\le h(e)<\infty.
$$

对任意 $x,u\in G$，将 (23.1) 用于实际背景 $a\cdot x,b\cdot x$ 和增量 $u,u$。由于 $U^ju\in G$，(23.2) 精确给出

$$
\sum_{j=0}^2h(x\cdot U^ju)=3h(x).
\tag{23.7}
$$

给定目标 $y\in G$，对每个 $x\in G$ 取实际增量 $u=x^{-1}\cdot y$。第零项是 $h(y)$，另外两项至少为 $m$，故

$$
0\le h(y)-m\le3\bigl(h(x)-m\bigr).
\tag{23.8}
$$

对 $x$ 取下确界，得 $h(y)=m$；取 $y=e$ 得 $m=d(a,b)$。这证明 (23.4)，不要求下确界取到，也不要求 $h$ 有统一上界。

第二步只在 $G$ 内复用定理 21.3。继承群、$U$-稳定、有限非负零对角及完整限制关系已逐项满足其前件，因此

$$
\begin{gathered}
F_G(gh)=F_Gg+F_Gh,\qquad F_G(Ug)=\omega F_Gg+t_G,\\
d(g,h)=\|F_Gg-F_Gh\|^2\quad(g,h\in G),\qquad
\omega=\exp(2\pi i/3).
\end{gathered}
\tag{23.9}
$$

于是 $Z$ 是 $G$ 的正规子群，$d(u,v)=0$ 对全部 $u,v\in Z$ 成立。这里只取得群内表示，没有把它预先延到 $M$。定义归一化的实际群标签

$$
T_ju=(U^ju)\cdot p_j^{-1}\quad(j=0,1,2).
$$

仿射递推给 $F_G(U^ju)=\omega^jF_Gu+\sum_{r=0}^{j-1}\omega^rt_G$，空和为零，故

$$
F_G(T_ju)=\omega^jF_Gu,\qquad T_j(Z)\subseteq Z,\qquad
F_G(p_3)=(1+\omega+\omega^2)t_G=0.
\tag{23.10}
$$

这里不需要 $U(Z)\subseteq Z$；非零漂移恰由实际 $p_j^{-1}$ 消去。

仍固定任意原 $a,b\in M$，现在在两份独立零尾巴上定义

$$
k(z,w)=d(a\cdot z,b\cdot w),\qquad
\mu=\inf_{(z,w)\in Z^2}k(z,w),\qquad
0\le\mu\le k(e,e)<\infty.
$$

对 $z,w,u,v\in Z$，将 (23.1) 用于背景 $a\cdot z,b\cdot w$ 和增量 $u,v$。每个第 $j$ 项先由 (23.4) 同时右乘 $p_j^{-1}$，再只用 (23.2) 与 $G$ 内结合律，得到

$$
\begin{aligned}
&d\bigl((a\cdot z)\cdot U^ju,(b\cdot w)\cdot U^jv\bigr)\\
&\quad=d\bigl(((a\cdot z)\cdot U^ju)\cdot p_j^{-1},
                 ((b\cdot w)\cdot U^jv)\cdot p_j^{-1}\bigr)\\
&\quad=d\bigl(a\cdot(z\cdot T_ju),b\cdot(w\cdot T_jv)\bigr)
=k(z\cdot T_ju,w\cdot T_jv).
\end{aligned}
$$

由 $d(u,v)=0$，完整关系因此成为

$$
\sum_{j=0}^2k(z\cdot T_ju,w\cdot T_jv)=3k(z,w).
\tag{23.11}
$$

给定任意目标 $(z_0,w_0)\in Z^2$，对每个 $(z,w)\in Z^2$ 取实际群增量

$$
u=z^{-1}\cdot z_0,\qquad v=w^{-1}\cdot w_0.
$$

因 $T_0u=u$、$T_0v=v$，(23.11) 的第零项是 $k(z_0,w_0)$；其余参数仍在 $Z^2$，所以

$$
0\le k(z_0,w_0)-\mu\le3\bigl(k(z,w)-\mu\bigr).
\tag{23.12}
$$

对 $(z,w)$ 取下确界，得 $k(z_0,w_0)=\mu$。再取目标 $(e,e)$，得 $\mu=d(a,b)$，即 (23.5)。由 (23.10) 的 $p_3\in Z$，分别取 $(z,w)=(p_3,e),(e,p_3)$，便是 (23.6)。整个证明既没有使用原 $a,b$ 的逆元，也没有交换比较端点；零费用到完整行列不变的桥梁是 (23.11)–(23.12)，而非对零距离的预先识别。证毕。

### 23.3 同一个原核的完整几何

**推论 23.3（整载体的最小仿射复 Hilbert 几何）。**在定义 23.1 下，存在完备复 Hilbert 空间 $H_d$ 与 $F_d:M\to H_d$，满足

$$
\begin{gathered}
F_de=0,\qquad F_d(a\cdot b)=F_da+F_db,\\
F_d(Ua)=\omega F_da+t_d,\qquad t_d=F_d(Ue),\\
d(a,b)=\|F_da-F_db\|^2,\qquad
H_d=\overline{\operatorname{span}_{\mathbb C}F_d(M)}.
\end{gathered}
\tag{23.13}
$$

最小表示唯一到唯一的保原标签酉同构；原 $d$ 的对称性、全部有限负型及 $\sqrt d$ 的全部三角不等式随之成立。漂移不限为零，有向输入、非忠实或全零比较均保留。

**证明。**定理 23.2 已在同一个原 $M,U,d$ 上供应两个普遍返回 (23.6)。将[续卷 W 定理 43.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#43-原核的有界轴刚性与第三标记返回下的完整仿射几何)的 $c$ 精确取为此 $d$，其全部原始前件均已满足，直接得到 (23.13) 及上述核性质。最小闭张成与唯一性复用本卷定理 1.3。这里没有以 $d+d^{\mathsf T}$、群内核或极限核替代原 $d$；不重证分类、极化、Gram 正性或 Hilbert 完成。证毕。

### 23.4 已给定同一总空间上的全部原事件

**推论 23.4（右群作用分支的受支配事件自动具有返回与效果）。**在定义 23.1 的同一实际 $M,U,G$ 上，另已给定定义 20.1 的同一个最小总表示 $H,F,t,K$：

$$
Fe=0,\quad F(a\cdot b)=Fa+Fb,\quad F(Ua)=\omega Fa+t,
\quad K(a,b)=\|Fa-Fb\|^2,\quad
H=\overline{\operatorname{span}_{\mathbb C}F(M)}.
$$

若原事件 $q:M^2\to[0,\infty)$ 处处有限、满足全部有序 (23.1) 且 $q\le K$，则 $q$ 自动具有 (23.6)，并在这个已给定的 $H$ 上有唯一复正收缩 $E_q$，使

$$
0\le E_q\le I_H,\qquad
q(a,b)=\langle Fa-Fb,E_q(Fa-Fb)\rangle
\quad(a,b\in M).
\tag{23.14}
$$

实际已给定的完整有限索引菜单 $(q_\ell)_{\ell\in J}$，若每项非负有限、满足同一全关系且 $\sum_{\ell\in J}q_\ell=K$，则保留每个原索引并有

$$
\sum_{\ell\in J}E_{q_\ell}=I_H.
\tag{23.15}
$$

**证明。**支配给 $q(a,a)=0$；将定理 23.2 的核直接取为这个 $q$，便在全部原标签上取得两个返回。随后命题 20.2 精确用于已给定的 $H,F,K$ 和当前 $q$，得到 (23.14) 与唯一性。各事件自己的群内或整载体最小空间均不与 $H$ 静默相认。效果证明及所需补核 $K-q$ 的处理全部复用命题 20.2／定理 6.2；没有从核的逐点支配推断极化型的 Loewner 次序。

对原完整菜单，非负完整和逐项给 $q_\ell\le K$，所以上段逐项支付返回，再直接应用命题 20.2 的原索引完整测试结论，得到 (23.15)。重复事件仍保留不同索引，零事件给零效果；不要求质量相等。若 $K=0$，支配给所有事件为零，最小性给 $H=0$，其零算子也是 $I_H$；空完整菜单也只在此退化情形出现。没有从本推论制造任何未实际给定的菜单。证毕。

### 23.5 非结合、非可逆原载体上的非零严格弱化例子

**例 23.5（树值可见、记录不删、漂移非零）。**令 $B=\mathbb Z[\omega]\subset\mathbb C$，$G_0=B\times\mathbb Z$ 取加法。令 $T$ 是三个叶标签 $x_0,x_1,x_2$ 上的自由含幺二元 magma：正规项是 $e_T$、三个叶子及两个非单位正规项的有序二元节点；乘法 $s*t$ 先约去单位因子，其余保留实际二元节点与括号。定义

$$
\begin{gathered}
f(e_T)=0,\qquad f(x_r)=\omega^r\quad(r=0,1,2),\qquad
f(s*t)=f(s)+f(t),\\
\sigma(e_T)=e_T,\qquad \sigma(x_r)=x_{r+1\bmod3},\qquad
\sigma(s*t)=\sigma(s)*\sigma(t).
\end{gathered}
$$

结构递归给 $f(\sigma s)=\omega f(s)$，$\sigma^3s=s$。置

$$
\begin{aligned}
M&=G_0\times T,\qquad e=((0,0),e_T),\\
((g,n),s)\cdot((h,m),t)&=((g+h,n+m),s*t),\\
U((g,n),s)&=((\omega g+1,n+1),\sigma s),\\
d\bigl(((g,n),s),((h,m),t)\bigr)
&=|g-h|^2+|f(s)-f(t)|^2,\\
G&=G_0\times\{e_T\}\subset M.
\end{aligned}
\tag{23.16}
$$

这些定义在全部原标签上总定义。$e$ 是实际双侧单位；$G$ 的继承乘法是群加法，逆为 $((g,n),e_T)^{-1}=((-g,-n),e_T)$，且 $U(G)\subseteq G$。右乘 $((h,m),e_T)$ 只平移前两个坐标而保留树 $s$，所以 (23.2) 对每个原 $a\in M$ 成立。

令

$$
F((g,n),s)=(g,f(s))\in\mathbb C^2,\qquad t_0=(1,0).
$$

直接由定义有 $Fe=0$、$F(ab)=Fa+Fb$、$F(Ua)=\omega Fa+t_0$ 和 $d(a,b)=\|Fa-Fb\|^2$。对任何原 $a,b,u,v$，置 $A=Fa-Fb$、$B'=Fu-Fv$，两个端点的同相漂移相消，给出完整手算恒等式

$$
\begin{aligned}
\sum_{j=0}^2d(a\cdot U^ju,b\cdot U^jv)
&=\sum_{j=0}^2\|A+\omega^jB'\|^2\\
&=3\|A\|^2+3\|B'\|^2.
\end{aligned}
\tag{23.17}
$$

故全部有序原关系成立，值处处有限、非负、零对角。像中有 $(1,0)$ 和 $(0,1)$，最小总空间正是 $\mathbb C^2$，漂移 $t_0\ne0$。对 $\alpha_r=((0,0),x_r)$，有 $d(\alpha_0,e)=1$、$d(\alpha_0,\alpha_1)=3$：非单位树的可见值并未全被抹掉。

原载体确实不是群。$(\alpha_0\cdot\alpha_1)\cdot\alpha_2$ 与 $\alpha_0\cdot(\alpha_1\cdot\alpha_2)$ 是不同的实际正规树，故全局结合律失败。叶数 $L(e_T)=0$、$L(x_r)=1$、$L(s*t)=L(s)+L(t)$ 为非负整数；若 $s\ne e_T$，则任意乘积含 $s$ 的树叶数为正，不可能等于 $e_T$。因此 $M\setminus G$ 的每个标签都没有左逆或右逆。

同时

$$
p_1=((1,1),e_T),\qquad p_2=((1+\omega,2),e_T),\qquad
p_3=((0,3),e_T)\ne e,\qquad
U^3((g,n),s)=((g,n+3),s).
\tag{23.18}
$$

所以 $U^3$ 在原载体上没有固定点；而 $(p_1\cdot p_1)\cdot p_1=((3,3),e_T)\ne p_3$。群内表示可取 $F_G((g,n),e_T)=g$，从而 $Z=\{((0,n),e_T):n\in\mathbb Z\}$，$p_3\in Z$。本比较满足两个普遍 $P_3$ 返回，却有 $d(p_1,e)=1$，没有把非零漂移改成零费用标记。

树、整数和全部实际标签仍保留在 $M$；此 $d$ 看不见的记录并未因此删除。若另有原读数能区分这些记录，本例没有替那些读数证明 (23.1)，更没有断言全部合法观察都必须塌缩为 $F$。这只是充分结构严格弱于“整个 $M$ 是群”的数学见证，不是原 $\Omega$ 的物理供给器。

### 23.6 承重增量、成熟工具与不缩减的来源

本节相对 §21 的实质增量是 (23.4)–(23.5) 的整载体传播：可用除法只在实际 $G$ 内，而两个背景端点始终遍历全部原 $M$。第二次取下确界作用于独立的 $Z\times Z$ 尾巴，归一化后每一相仍在同一轨道，因而不需群外正规性或群外逆元。这不同于仅在群 $G$ 内套用引理 21.2，也不由原 V 卷要求 $Ue=e$ 的分类或原 IV 卷的交换幺半群分类支付；非零漂移及非结合原载体由例 23.5 同时保留。

非负平均的下确界刚性、群作用的轨道参数化和自由含幺二元正规形都是成熟工具。群内分类 21.3、[W43.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#43-原核的有界轴刚性与第三标记返回下的完整仿射几何)、本卷 1.3、20.2／6.2、极化、Gram 正性与完成均为已付复用。本节只主张相对这些仓内结果的充分结构推导，不主张穷尽检索、历史原创性、外部开放问题解决或形式化核验。

完整原来源继续严格采用[环境耦合卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#6-完整原问题与七项物理合同的精确身份)及[两角正性证书卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md#49-不缩减的全文来源与七项量子消费者)的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：逐层钉版、递归纳入的全文与七项消费者同时保留，不以这里的短说明替代原合同。本节的 $d,F,G$ 不自动成为那些原接口中的同名对象。

同一个原 $\Omega$ 的全部准备、事件、过程、参考、副本及相关联合，零／不等／次归一质量、全菜单、固定支持、每个已量化中间切口，控制、物理钟、单位、ready、旗标，全部程序、记录、拒绝／失败／停止／销毁、完整输出、两侧及逆向 Return 和每个合法未来均保留。共同全词 $K/J$、指定分析器的准确接受关联、CountRead 的同一接受完整活动输出及实际读后 ready、第一合法消费者和全输入／全合法未来真实返回，仍须由同一原来源供应；C13950–73 和 C128385–392 的已成结论按其准确前件复用，不重新列缺。

(23.6) 只是这一个比较核对实际右标记的普遍返回，不是原完整输出或全部未来的物理 Return。数学群逆元不制造物理逆过程，仿射加法不制造相干控制、复制或顺序门复合；效果表示不制造准备、菜单、张量、CP／Kraus、条件更新或 Hamiltonian 所需的原过程、参考及时间前件。这里没有从原 $\Omega$ 构造 $G$ 或证明 (23.2)，没有证明所有 magma 都具有此结构，也没有解决一般原始 $(R)\Rightarrow\mathrm C_3$ 或任意 magma 的整个 $\mathsf{Eff}$。例 23.5 只证明数学前件确实放宽，不能据此宣称全来源公理更少或物理资源最小。完整原 Omega 目标保持不变且未完成。

### 23.7 完整中文直观说明

把 $G$ 想成允许接到任何原标签后面的实际“尾巴库”。尾巴之间有群内除法，尾巴接续在任何原背景上都遵守同一结合右作用，但原背景彼此怎样组合仍可非结合、不可逆。固定两个原背景，看同时接同一尾巴的比较。完整关系把三个非负尾巴读数的和钉为起点读数的三倍；从任何尾巴出发，群内除法都能把第零相送到指定目标。把起点读数压近全轨道下确界，目标也只能等于这个下确界，所以共同尾巴根本不改变比较。

只在群内使用已有分类后，得到一组群内看不见的零尾巴。现在允许两个端点各接不同的零尾巴。标记会带来共同漂移，因此不能假定标记直接保持零尾巴；先用第一步把共同的第 $j$ 标记尾巴从两端撤去，剩下的归一化尾巴才仍在零群内。于是两个独立尾巴也满足同样的非负平均关系，再取一次下确界，就证明全部原背景的比较都不受它们影响。第三标记尾巴正属这个零群，两个端点的返回因此成为结论。

此后全部复 Hilbert 平方几何由已成立的返回分类直接给出。若总空间已经给定，每个受它支配的原事件也先获得自己的返回，再由既有事件定理进入同一总空间；不会把不同事件空间硬当成同一个空间。原完整菜单中的重复、零或不等质量事件都保留各自索引。

树例子说明结论没有偷把整个世界改成群：树的括号真的不同，非单位树真的没有逆元，树值又真的能产生非零比较；整数记录让第三次实际标记永不回到原标签。这个比较看不见第三次标记的差别，与原记录消失、所有观察都看不见或物理装置真正返回，是三件不同的事。这里完成的是上述充分结构的几何桥，完整量子来源仍须原来源和七项消费者共同完成。

## 追加锚（本行以下为增补区）

## 24. 无实际逆元的交换幺半群尾巴迫出整载体返回

### 24.1 原对象与共同尾巴

**定义 24.1（实际交换幺半群的整载体右作用）。**保留定义 23.1 的原 $M,e,\cdot,U,d$ 及对全部有序 $a,b,u,v\in M$ 的完整 (23.1)：

$$
\sum_{j=0}^2d(a\cdot U^ju,b\cdot U^jv)
=3d(a,b)+3d(u,v).
\tag{24.1}
$$

$M$ 只是真实双侧含幺的二元 magma，$U$ 是任意总映射，$d:M^2\to[0,\infty)$ 处处有限且零对角，允许初始有向。充分结构改为一个实际子集 $S\subseteq M$：它包含 $e$，继承的同一个实际乘法使它成为交换幺半群，$U(S)\subseteq S$，并且

$$
(a\cdot s)\cdot r=a\cdot(s\cdot r)
\qquad(a\in M,\ s,r\in S).
\tag{24.2}
$$

$S$ 不要求消去或有逆元；其外部乘积不要求结合、交换、消去或有逆元。$U$ 不要求保单位、满射、保乘法或周期。记 $p_j=U^je\in S$、$P_3(a)=a\cdot p_3$；$p_j$ 不是预先规定的 $p_1$ 的乘法幂。这里的 $S$ 是实际尾巴集合，不是 §24.6 原物理合同中的 Jordan 响应符号。

**定理 24.2（无逆元的整载体传播）。**在定义 24.1 下，有

$$
\begin{aligned}
d(a\cdot s,b\cdot s)&=d(a,b)
&& (a,b\in M,\ s\in S),\\
d(a\cdot z,b\cdot w)&=d(a,b)
&& (a,b\in M,\ z,w\in Z),
\end{aligned}
\tag{24.3}
$$

其中 $Z=\{s\in S:F_Ss=0\}$，$F_S$ 是下面证明中在同一限制核 $d|_{S^2}$ 上取得的可加仿射复 Hilbert 表示。该构造满足 $p_3\in Z$，从而在全部原载体上有

$$
\boxed{d(P_3a,b)=d(a,b)=d(a,P_3b)\quad(a,b\in M).}
\tag{24.4}
$$

**证明：共同尾巴。**固定原 $a,b\in M$，在 $S$ 上置 $h(x)=d(a\cdot x,b\cdot x)$。对 (24.1) 取增量 $x,x$，其第零项及非负性给

$$
0\le h(x)\le3d(a,b)\quad(x\in S).
\tag{24.5}
$$

对每个固定 $s\in S$，再取背景 $a\cdot x,b\cdot x$ 和增量 $s,s$，由 (24.2) 得

$$
\sum_{j=0}^2h(x\cdot U^js)=3h(x)\qquad(x\in S).
\tag{24.6}
$$

$U^js\in S$，这三个右平移在交换幺半群 $S$ 上交换。[IV 引理 2.1](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_IV.md#2-两个既有调和工具的有限版本)适用于有界实函数 $h$，给每个平移各自保持 $h$。特别第零平移给 $h(x\cdot s)=h(x)$；在 $x=e$ 取值，得到 (24.3) 第一式。此处既未解方程 $xu=y$，也未使用 $Ue=e$。

### 24.2 IV 的未锚定仿射适配

继续证明定理 24.2。下面只在 $S$ 内使用限制核，不先将群化、线性空间或表示赋给整个 $M$。[IV 定义 1.1 与定理 1.3](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_IV.md#1-来源与候选关系)有 $Ue=e$ 前件，在这里不能直接调用；可复用的是该卷 §3 在处理标记之前的证明。其不依赖固定锚的准确适配如下。

令 $G$ 为交换幺半群 $S$ 的 Grothendieck 群，$\iota:S\to G$ 为自然映射，置

$$
q(\iota u-\iota v)=d(u,v).
\tag{24.7}
$$

共同尾巴不变性已支付良定义性：若两个差相等，存在 $r\in S$ 使 $u\cdot v'\cdot r=u'\cdot v\cdot r$；分别给两端接相同尾巴即可比较这两个读数。$\iota$ 无须单射，未对原 $S$ 作消去。于是 $q\ge0$、$q(0)=0$。对原 $u,v\in S$ 记 $h_j=\iota(U^ju)-\iota(U^jv)$，完整关系成为

$$
\sum_{j=0}^2q(x+h_j)=3q(x)+3q(h_0)\qquad(x\in G).
\tag{24.8}
$$

这里没有在 $G$ 上定义 $U$。每个群元可作某一原对的 $h_0$，非负性给 $q(x+y)\le3(q(x)+q(y))$。对任意有限多原对 $(u_i,v_i)$，将 $q$ 拉回自由格 $\mathbb Z^{3r}$：

$$
Q(n)=q\left(\sum_{i,j}n_{i,j}h_{i,j}\right),\qquad
\Delta_0Q=3\sum_i\bigl(q(h_{i,0})+q(-h_{i,0})\bigr).
\tag{24.9}
$$

常数 Poisson 式来自对各原对与交换后的原对求和，重复或有整数关系的方向照样保留。盒上最大值的二分界为 $A(2R)\le6A(R)$，所以增长指数为 $\log_2 6<3$。IV 引理 2.2 因而适用；IV §3 的差分、非负性和 Gram 构造给

$$
q(x)=B(x,x)+\ell(x),\qquad
B\text{ 对称双可加},\quad\ell\text{ 可加}.
\tag{24.10}
$$

一次项的消失也不使用固定锚。对每个原对置 $s_*=h_0+h_1+h_2$，在 (24.8) 减去 $x=0$ 的式子，给 $B(x,s_*)=0$。于是 $B(s_*,s_*)=0$，$q(s_*),q(-s_*)\ge0$ 迫使 $\ell(s_*)=0$；再把 $x=0$ 的原对与交换原对两式相减，给 $\ell(s_*)=3\ell(h_0)$。所有群元都可作 $h_0$，故 $\ell=0$。

按 IV §3 的整数 Gram、清分母和有限实极限步骤，$B$ 的实线性延拓半正定；商去零空间并完成得到实 Hilbert 空间 $H_{\mathbb R}$ 及可加 $F_S:S\to H_{\mathbb R}$，满足

$$
F_Se=0,\qquad d(u,v)=\|F_Su-F_Sv\|^2,
\qquad H_{\mathbb R}=\overline{\operatorname{span}_{\mathbb R}F_S(S)}.
\tag{24.11}
$$

这些步骤及常数 Poisson 工具均是 IV 的已付推导；其方程只涉及成对标记差，未设 $p_1=e$。现在显式补上该证明原来使用固定锚的标记步骤。

在背景 $e,e$ 上反复用 (24.1)，对 $r_n=d(U^nu,U^nv)$ 得 $r_{n+1}+r_{n+2}=2r_n$。解 $r_n=\alpha+\beta(-2)^n$ 的全部非负性迫使 $\beta=0$，故 $U$ 保持成对距离。令 $t=F_Sp_1$、$G_u=F_S(Uu)-t$。由于 $G_e=0$，距离极化给

$$
(G_u,G_v)_{\mathbb R}=(F_Su,F_Sv)_{\mathbb R}.
\tag{24.12}
$$

故 $F_Su\mapsto G_u$ 在实线性包上良定义：任何有限实线性关系的像，其范数平方按 (24.12) 与原关系相同，必为零。它延伸为整个 $H_{\mathbb R}$ 上的实线性等距算子 $T$，并有

$$
F_S(Uu)=TF_Su+t,\qquad
F_S(U^2u)=T^2F_Su+Tt+t.
\tag{24.13}
$$

前面的 $B(x,s_*)=0$ 在 Gram 商中给真正的向量等式

$$
\sum_{j=0}^2\bigl(F_S(U^ju)-F_S(U^jv)\bigr)=0.
\tag{24.14}
$$

用 (24.13) 并取 $v=e$，漂移逐项相消，得到 $(I+T+T^2)F_Su=0$。实线性稠密性遂给 $I+T+T^2=0$，因而 $T^3=I$；特别 $T$ 此时才知为满射。令 $J=(I+2T)/\sqrt3$，则 $J^2=-I$、$J^*=-J$。按 IV 的约定以 $J$ 作为乘以 $i$ 的作用，得到同一实空间上的复 Hilbert 空间 $H_S$，$T$ 成为乘以 $\omega=\exp(2\pi i/3)$，且

$$
\begin{gathered}
F_S(u\cdot v)=F_Su+F_Sv,\qquad
F_S(Uu)=\omega F_Su+t,\\
d(u,v)=\|F_Su-F_Sv\|^2\quad(u,v\in S),\qquad
H_S=\overline{\operatorname{span}_{\mathbb C}F_S(S)}.
\end{gathered}
\tag{24.15}
$$

这里保留任意 $t$，没有以旋转中心替换实际聚合单位，也没有调用前件未满足的锚定分类。

### 24.3 实际正词补偿与独立零尾巴

在 (24.15) 中，$F_Sp_1=t$、$F_Sp_2=(1+\omega)t$、$F_Sp_3=0$。定义以下全部属于实际 $S$ 的有限正词：

$$
q_0=e,\qquad q_1=U(p_2\cdot p_2),\qquad
q_2=(q_1\cdot q_1)\cdot U(q_1).
\tag{24.16}
$$

它们的值由可加仿射公式逐项给出：

$$
\begin{aligned}
F_Sq_1&=2\omega(1+\omega)t+t=-t,\\
F_S(Uq_1)&=(1-\omega)t,\\
F_Sq_2&=-2t+(1-\omega)t=-(1+\omega)t.
\end{aligned}
\tag{24.17}
$$

所以 $F_Sq_j=-F_Sp_j$ 对 $j=0,1,2$ 成立。没有断言 $p_j\cdot q_j=e$；补偿只发生在这个表示的值上。$Z=\ker F_S$ 是实际交换子幺半群，包含 $e,p_3$；对所有 $u,v\in Z$ 有 $d(u,v)=0$。置

$$
T_ju=(U^ju)\cdot q_j\quad(u\in Z,\ j=0,1,2).
\tag{24.18}
$$

由 (24.15)–(24.17)，$F_S(T_ju)=\omega^jF_Su=0$，所以 $T_j(Z)\subseteq Z$，且 $T_0u=u$。不要求 $U(Z)\subseteq Z$，也不要求这些实际映射可逆或保乘法。

固定任意原 $a,b\in M$，在交换幺半群 $Z\times Z$ 上定义

$$
k(z,w)=d(a\cdot z,b\cdot w).
$$

对 (24.1) 用背景 $a,b$ 和增量 $z,w$，由 $d(z,w)=0$ 及第零项非负得 $0\le k(z,w)\le3d(a,b)$。再对背景 $a\cdot z,b\cdot w$ 及增量 $u,v\in Z$ 用 (24.1)。每个第 $j$ 项可以由已经证明的共同尾巴不变性同时右乘实际 $q_j$；(24.2) 精确给

$$
\begin{aligned}
&d\bigl((a\cdot z)\cdot U^ju,(b\cdot w)\cdot U^jv\bigr)\\
&\quad=d\bigl(((a\cdot z)\cdot U^ju)\cdot q_j,
               ((b\cdot w)\cdot U^jv)\cdot q_j\bigr)\\
&\quad=k(z\cdot T_ju,w\cdot T_jv).
\end{aligned}
\tag{24.19}
$$

于是对每个固定 $u,v\in Z$，

$$
\sum_{j=0}^2 k(z\cdot T_ju,w\cdot T_jv)=3k(z,w)
\qquad(z,w\in Z).
\tag{24.20}
$$

这是 $Z\times Z$ 上三个交换的普通平移对有界实函数 $k$ 的平均关系；不需要映射 $T_j$ 彼此交换。再次应用 IV 引理 2.1，第零平移给 $k(z\cdot u,w\cdot v)=k(z,w)$。在 $(z,w)=(e,e)$ 取值，得到 (24.3) 第二式。再分别取 $(u,v)=(p_3,e),(e,p_3)$，即 (24.4)。两个独立尾巴始终作用于原 $a,b$，没有将其先投影到 $S$ 或交换有向端点。定理 24.2 证毕。

### 24.4 同一原核与给定总空间上的事件

**推论 24.3（原核的完整仿射几何及同一总空间事件）。**在定义 24.1 下，原 $d$ 在全部 $M$ 上有最小完备复 Hilbert 表示

$$
\begin{gathered}
F_de=0,\qquad F_d(a\cdot b)=F_da+F_db,\\
F_d(Ua)=\omega F_da+t_d,\qquad t_d=F_d(Ue),\\
d(a,b)=\|F_da-F_db\|^2,\qquad
H_d=\overline{\operatorname{span}_{\mathbb C}F_d(M)}.
\end{gathered}
\tag{24.21}
$$

它唯一到唯一的保原标签酉同构；原核对称性、全部有限负型及 $\sqrt d$ 的三角不等式都是结论。

另在相同实际 $M,U,S$ 上，若已给定定义 20.1 的同一个最小总空间 $H,F,t,K$，且原事件 $q$ 有限非负、满足完整 (24.1) 并满足 $q\le K$，则在这个给定 $H$ 上有唯一复正收缩 $E_q$，使

$$
q(a,b)=\langle Fa-Fb,E_q(Fa-Fb)\rangle\quad(a,b\in M).
\tag{24.22}
$$

对实际已给定的任一完整有限带索引菜单 $(q_\ell)_{\ell\in I}$，若各项满足上述全关系且 $\sum_{\ell\in I}q_\ell=K$，则同一 $H$ 上 $\sum_{\ell\in I}E_{q_\ell}=I_H$，保留全部原事件索引。

**证明。**定理 24.2 已在原 $M,U,d$ 上供应两个普遍返回，故 [W43.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#43-原核的有界轴刚性与第三标记返回下的完整仿射几何)精确适用，给 (24.21) 与核性质；最小性及唯一性复用本卷定理 1.3。整载体分类是该既有结论的消费，不是另一项新分类。

对给定总空间事件，$q\le K$ 先给 $q(a,a)=0$。将定理 24.2 的核取为 $q$ 本身，其同一个实际交换幺半群及右作用前件不变，故该事件取得自己的两个普遍返回。现在才将命题 20.2 应用于原来给定的 $H,F,K$ 和这个 $q$，得到 (24.22) 与唯一性。事件自己的辅助 $H_S$ 或 $H_q$ 不被认作给定的 $H$。补事件 $K-q$ 的表示、极化及 Loewner 正性全部沿命题 20.2／定理 6.2 的证明，不从逐点 $q\le K$ 直接推算子次序。

对原完整菜单，完整和逐项给 $q_\ell\le K$；对每个原事件支付返回后，命题 20.2 的原索引结论给效果和。重复事件保持不同索引，零事件给零效果，质量不要求相等；严格正实际总质量才允许概率归一。若 $K=0$，最小性给 $H=0$，所有事件及效果为零，而零算子也是 $I_H$。空完整菜单只在这个退化情形成立。不制造任何尚未实际给定的菜单。证毕。

### 24.5 没有任何稳定实际子群的非零总模型

**命题 24.4（正坐标与非结合树的严格范围见证）。**令 $S_0=\mathbb N^3$，取

$$
\rho(n_0,n_1,n_2)=(n_2,n_0,n_1),\qquad
\phi(n)=n_0+\omega n_1+\omega^2n_2,\qquad e_0=(1,0,0).
$$

令 $\mathcal T$ 为三种叶标签 $x_0,x_1,x_2$ 的自由含幺有序二元 magma：添加单位 $e_{\mathcal T}$，乘法 $*$ 遇到单位时约简，否则是新的有序树节点。不同括号、次序和叶标签仍不同。定义

$$
\begin{gathered}
f(e_{\mathcal T})=0,\qquad f(x_r)=\omega^r,\qquad
f(s*t)=f(s)+f(t),\\
\sigma(e_{\mathcal T})=e_{\mathcal T},\qquad
\sigma x_r=x_{r+1\ ({\rm mod}\ 3)},\qquad
\sigma(s*t)=(\sigma s)* (\sigma t).
\end{gathered}
$$

在全部原标签上置

$$
\begin{aligned}
M&=S_0\times\mathcal T,\qquad e=(0,e_{\mathcal T}),\\
(n,s)\cdot(m,r)&=(n+m,s*r),\\
U(n,s)&=(\rho n+e_0,\sigma s),\\
d((n,s),(m,r))&=|\phi(n)-\phi(m)|^2+|f(s)-f(r)|^2,\\
S&=S_0\times\{e_{\mathcal T}\}.
\end{aligned}
\tag{24.23}
$$

则定义 24.1 的全部前件成立，最小总空间为 $\mathbb C^2$，漂移非零；$M$ 非结合且非交换，只有 $e$ 可逆，没有任何包含 $e$ 的 $U$-稳定实际子群。因此本模型满足定理 24.2 的结构而不满足 §23 的结构。

**证明。**$S$ 的继承乘法是 $\mathbb N^3$ 加法，且 $U(S)\subseteq S$。右乘 $S$ 中标签只平移正坐标、不改变树，故 (24.2) 对全部原 $a\in M$ 成立。结构递归给 $\phi(\rho n)=\omega\phi(n)$、$f(\sigma s)=\omega f(s)$、$\sigma^3s=s$。置

$$
F(n,s)=(\phi(n),f(s)),\qquad t=(1,0).
$$

于是 $Fe=0$、$F(ab)=Fa+Fb$、$F(Ua)=\omega Fa+t$、$d(a,b)=\|Fa-Fb\|^2$。对任意原有序四元组，令 $A=Fa-Fb$、$B'=Fu-Fv$；同相漂移在差中相消，直接平方展开给

$$
\sum_{j=0}^2d(a\cdot U^ju,b\cdot U^jv)
=\sum_{j=0}^2\|A+\omega^jB'\|^2
=3\|A\|^2+3\|B'\|^2.
\tag{24.24}
$$

所以完整原始关系成立，核有限、非负、零对角。像中包含 $(1,0)$ 和 $(0,1)$，最小复空间确为 $\mathbb C^2$。对外部树标签 $\alpha_r=(0,x_r)$，有 $d(\alpha_0,e)=1$、$d(\alpha_0,\alpha_1)=3$，非尾巴部分没有被全部压成零读数。

树的两个括号 $(x_0*x_1)*x_2$、$x_0*(x_1*x_2)$ 不同，交换叶次序也不同，故原全局结合与交换律失败。若 $(n,s)$ 有任一侧的逆，非负坐标和必须为零，迫 $n=0$；树叶数在乘法下相加，且非单位树叶数正，又迫 $s=e_{\mathcal T}$。所以实际可逆元只有 $e$。任何以原 $e$ 为单位的实际子群只能是 $\{e\}$，但 $Ue=(e_0,e_{\mathcal T})\ne e$，它不稳定。

此外，

$$
\begin{gathered}
p_1=(e_0,e_{\mathcal T}),\quad
p_2=((1,1,0),e_{\mathcal T}),\quad
p_3=((1,1,1),e_{\mathcal T})\ne e,\\
U^3(n,s)=(n+(1,1,1),s).
\end{gathered}
\tag{24.25}
$$

$U$ 每次使正坐标总数增加一，故没有实际周期点；特别 $U^3$ 没有实际固定点。$F(p_3)=0$ 而 $d(p_1,e)=1$，两端核返回与非零漂移同时保留。所有正坐标和树仍是原标签，不因这个核看不见其某些区别就删除。证毕。

### 24.6 承重来源、完整物理合同与中文解释

**来源与边界 24.5。**本节的 repo-derived 承重增量是：在定义 24.1 的实际交换幺半群右作用下，以两次有界交换平均刚性、未锚定仿射适配及实际正词 (24.16) 支付整载体的 (24.3)–(24.4)。相对 §23 撤去实际逆元，同时加入尾巴交换律，两个结构并非全面互相包含；命题 24.4 证明这里确实覆盖 §23 未覆盖的原模型。没有把整载体分类或同一总空间效果另算新成果。

有界交换平均刚性复用 IV 引理 2.1 的有限原子证明，其成熟来源为 Bebe Prunaru，*A short proof of a Choquet–Deny theorem for abelian topological semigroups*，Theorem 1 与 pp.1–2，[作者机构原文](https://imar.ro/~dtimotin/idei/choquet-deny5.pdf)。常数 Poisson／次三次格点刚性复用 IV 引理 2.2；相关平方差分方法见 Gabor Lippner、Dan Mangoubi，*Harmonic functions on the lattice: Absolute monotonicity and propagation of smallness*，[arXiv:1312.4550v3](https://arxiv.org/html/1312.4550v3)，Theorem 2.1、Claim 2.2、Remark 2.3、Corollary 1.9，DOI 10.1215/00127094-3164790。这些是中间工具的文献归属，不是对本节原签名传播结论的文献优先权主张。这里不输入拓扑半群、物理概率过程或物理随机游走。

Grothendieck 群化、有限差分、Gram 商与完成、距离极化、仿射等距的中心化以及自由含幺树均是成熟工具。IV §3 在固定锚之前的平方几何推导、本卷 §4 的有限正纠偏思想、W43.3 的返回分类及本卷 20.2／6.2 的同一总空间效果全部按准确前件复用。§24.2 明列原 IV 最后标记步骤所需的仿射替换，不将原锚定定理的前件默认为成立。附近 C133 诸卷的上述结果不提供本节的无逆元整载体传播；本节只作相对所引结果的仓内推导，不主张外部检索穷尽、历史原创性或形式化核验。

完整原物理来源逐字采用[环境耦合卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#6-完整原问题与七项物理合同的精确身份)与[两角正性证书卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md#49-不缩减的全文来源与七项量子消费者)的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，逐层固定身份及全部递归上游不变；本节尾巴 $S$ 不替换其中的原响应 $S$。以下七项与这些全文同时保留，不作删减合同：

1. 实际相干准备、原同源标签、parent/ready、合法控制、共同全词与有限旧复 Gram 的完整供应，才接复 Hilbert 与可观测量消费者；数学向量与正词不供应可取得准备。
2. 原态、效果、Born、原事件绑定与准确接受端、全部完整菜单及零／不等／次归一／非正常质量、固定支持全质量均保留；仅严格正实际质量可归一。
3. 原相关联合、实际参考与副本、共同来源、同向交换腿、共同全词 $K/J$、生成分离和重数，才接张量与复合；边缘相同不代付联合实现。
4. 每条 typed CP／Kraus 分支的未归一上下文、整个系统及递归参考、所有输出与每个合法未来、真支持与补元、精确根及累计支持运输均保留；正性不自动成为 CP，正常性和表示域也不删除。
5. 原完整仪器、完整 typed 菜单、TP 单位分区、成功／失败／细记录／port／post-port 输出、真实分组与条件化、更新及 Lüders 的射线和完整输出校准均保留。
6. 全部原顺序、自适应、并行历史，记录、拒绝、失败、停止、销毁、泄漏、真遗忘、两侧及逆向真实 Return，与每个仍合法未来同时保留。
7. 原动力、实际连续可逆流及逆、物理钟与单位、能量解释、强连续实现、一般生成元域、共同仪器及同一个正 $\hbar$ 保持各自准确前件。

指定分析器仍须给字面旧 $\tau;T_P$ 的指定接受族提供准备无关的准确接受关联：域遍历全部原准备、中间切口、参考／副本、允许的词和树、原坐标、完整菜单与固定支持全质量，保持原支持和未归一标尺，到同一原实际菜单及接受端。此要求不是整仪器或全部历史恒等；矩阵相等、存在菜单、纯校准、操作逆字或矩阵综合均不构造该关联。CountRead 仍须同一接受叶的完整活动输出、实际读后活动 ready、第一合法消费者，以及读后同一完整活动输入对所有合法未来的真实 Return。

C13950–73、C128385–392 的既有下降、参考、恢复与相应明确前件下的成果继续作为复用，不重新列缺。Native XI／C139 保留其原来源、Return 与地址前件；OTF8 的实际 CP ports 仍是前件，Native GP／RG2 的不同启动装置不供应 AURIC 原来源身份。传入 R5 §20 的共同见证／稳定部分及维数碰撞和 OTF8 §17 的有限混合酉旋转障碍，保留各自原范围，不支付这里的实际来源或全部消费者。

本节没有从原 $\Omega$ 构造定义 24.1 的实际 $S$ 或证明其右作用，也没有由本条件分支推出任意 magma 的原始 $(R)\Rightarrow\mathrm C_3$。式 (24.4) 只返回这一个比较核的值，不是完整活动输出或全未来真实 Return；实际正补偿词不制造物理逆准备、负准备、复制或相干控制。本节没有完成实际分析器、CountRead 或完整量子来源，原 Omega 全目标保持不变且未完成。

**直观解释 24.6。**把 $S$ 看成一库能接到任何原对象后面的实际正尾巴。它们之间可交换、可合并，却不必能撤销。固定两个原对象，同接一个尾巴所得读数都被完整关系压在同一个有限上界内。三条交换平移的平均又总等于原值；有界交换平均刚性迫使每条平移单独都不能改变这个读数，所以共同尾巴可以在比较中消去，尽管实际对象没有被撤销。

只在尾巴库内部，已有 IV 方法先恢复平方距离。标记不必固定空尾巴，所以它在这些向量上应当是旋转加漂移。先减去标记空尾巴的向量，成对距离才给真正的线性等距；三相差之和为零再迫其旋转一百二十度。这样保留了漂移，没有偷偷把原空尾巴换成另一个旋转中心。

随后用正尾巴造出补偿：把第二标记尾巴合并两次再标记，向量恰为第一漂移的负值；再用三个正因子合成第二漂移的负值。它们在实际库里都不是逆元，只是这个比较读数的补偿词。对两个端点各接不同的零向量尾巴，先同时接同一个补偿词，标记后的尾巴便又落入零尾巴库。两份独立零尾巴上的读数仍有界，仍满足交换平移平均关系；再用一次刚性，就得到全部原对象上的独立零尾巴不变性。第三标记空尾巴的向量正为零，两个端点的第三返回因此同时成立。

此后整载体 Hilbert 分类与给定总空间上的效果由已有定理接上。树模型说明原对象的括号、正坐标及实际记录可以始终不同，第三标记甚至没有任何实际固定点，比较却已返回。这个数值返回既不抹掉原记录，也不证明装置、完整输出和所有合法未来真正回到原处；完整物理来源与七项消费者仍须在同一原实现中共同成立。

## 追加锚（本行以下为增补区）

## 25. 原生有限项、静态事件与同一参考态的顺序读出

### 25.1 原乘法项的实际作用与标量障碍

**定义 25.1（受限原生项签名与锚定复核）。**固定 §4、定义 20.1 所用的同一个实际 $M,e,\cdot,U$ 及其最小表示；在满足各节全部前件时，该表示可由 §23 的实际群右作用或 §24 的实际交换幺半群右作用这两类充分结构取得。这些结构不由原 $\Omega$ 自动供应，后一结构也不消除一般 magma 的几何／事件缺口或创造新的实际运算。以下用 $\zeta$ 表示前文的三次相位根，另将 $\omega$ 留给态泛函：

$$
Fe=0,\qquad F(a\cdot b)=Fa+Fb,\qquad
F(Ua)=\zeta Fa+t,\qquad
\zeta^2+\zeta+1=0,\quad \operatorname{Im}\zeta>0,
\qquad t=F(Ue).
\tag{25.1}
$$

受限原生一元项由一个变量 $x$、任意固定原标签常元、二元运算 $\cdot$ 和标记 $U$ 作有限次构造；允许变量重复，保留每次实际乘法的次序和括号。常元不随输入变化。比较值、坐标、事件索引和核值都是关系数据，不因此成为新的取坐标、按核选择、准备或控制运算。这里限制的是所研究的生成签名，不断言完整原 $\Omega$ 只有这些运算。令

$$
\mathcal O=\mathbb Z[\zeta],\qquad
\kappa(a,b)=(Fa)^\dagger Fb.
\tag{25.2}
$$

$\kappa$ 取第一变量共轭线性的约定；应用本卷第一变量线性的式 (4.5) 时取共轭。所谓完整锚定分支守恒，是对全部原 $a,b$ 要求有限族 $w_j$ 满足

$$
\sum_j\kappa(w_j(a),w_j(b))=\kappa(a,b).
\tag{25.3}
$$

这保留共同锚 $e$，不把左侧另行减去各分支的 $F(w_j(e))$。

**命题 25.2（受限原项不能生成非标量坐标分支）。**每个定义 25.1 的项 $w$ 有

$$
F(w(a))=\lambda_wFa+b_w,\qquad
\lambda_w\in\mathcal O,\qquad b_w=F(w(e)).
\tag{25.4}
$$

若 $F(M)\ne\{0\}$，有限项族满足 (25.3)，则恰有一个分支在表示中为 $\lambda I$，其中

$$
\lambda\in\mu_6=\{\pm1,\pm\zeta,\pm\zeta^2\};
\tag{25.5}
$$

其余分支在表示中全为零。特别，在 $\dim_{\mathbb C}H\ge2$ 时不能由这些项得到非零、非全空间的正交坐标投影。即使另准许任意复标量缩放，但仍只准许标量仿射分支，(25.3) 所给的分支效果仍全是 $|\lambda_j|^2 I$，不能成为依赖输入方向的坐标探针。

证明。结构归纳的系数规则为

$$
\begin{array}{c|c}
\text{项}&(\lambda,b)\\ \hline
x&(1,0)\\
c\text{，固定常元}&(0,Fc)\\
w\cdot v&(\lambda_w+\lambda_v,b_w+b_v)\\
Uw&(\zeta\lambda_w,\zeta b_w+t).
\end{array}
\tag{25.6}
$$

故全部有限项，包括重复使用输入的项，均满足 (25.4)。这沿用 §4–5 的 Eisenstein 配方结构；结构归纳只是该受限签名的逐项计算。若还施行实际一元映射的复合，则

$$
(\lambda_f,b_f)\circ(\lambda_g,b_g)
=(\lambda_f\lambda_g,\lambda_fb_g+b_f).
\tag{25.7}
$$

式 (25.7) 的映射复合与原二元乘法的 (25.6) 是两种运算；原二元乘法始终表示向量加法，没有被替换成矩阵乘法。

在 (25.3) 取 $a=b=e$，得 $\sum_j\|b_j\|^2=0$，所以每个 $b_j=0$。再取 $Fa\ne0$，得

$$
\sum_j|\lambda_j|^2=1,\qquad
|m+n\zeta|^2=m^2-mn+n^2\in\mathbb Z_{\ge0}.
\tag{25.8}
$$

故恰有一个范数为一，其余为零。由
$4(m^2-mn+n^2)=(2m-n)^2+3n^2$，范数一只有 $(m,n)=(\pm1,0),(0,\pm1),(1,1),(-1,-1)$，正是 (25.5)。范数非负整数这一步与 [C139 §16，命题 16.3](AURIC_C139_MUTUAL_PROBES_AND_INTRINSIC_RECOVERY_OF_SQUARE_GEOMETRY.md#16三路算术读口的实际供给与稠密边界)的算术障碍共用成熟的 Eisenstein 范数，不另主张算术分类。

若某项满足 $F(w(a))=PFa$，取 $a=e$ 先给 $b=0$，在 $F(M)$ 的复线性张成上又有 $P=\lambda I$，与投影同时有非零像和非零核矛盾。准许一般标量后，整数论结论可失效，但相同的锚定计算仍杀掉偏置，且每支的 $M_j^\dagger M_j=|\lambda_j|^2I$。所以标量分支的方向障碍不依赖整数范数。证毕。

### 25.2 全部原比较与一个三标签事件见证

**命题 25.3（忠实的完整平方几何仍不供应坐标接续）。**取

$$
M=\mathcal O^2,\qquad e=0,\qquad a\cdot b=a+b,\qquad
U(a)=\zeta a+e_0,\qquad e_0=(1,0),\quad e_1=(0,1),
\tag{25.9}
$$

以 $G=M$ 的实际加法群和右作用满足定义 23.1，取 $F$ 为到 $H=\mathbb C^2$ 的恒等嵌入。对每一对原标签都给出

$$
\begin{gathered}
K(a,b)=\|a-b\|^2,\qquad
q_j(a,b)=|a_j-b_j|^2\quad(j=0,1),\\
\kappa(a,b)=a^\dagger b,\qquad
\kappa_j(a,b)=\overline{a_j}b_j,\qquad
\kappa=\kappa_0+\kappa_1.
\end{gathered}
\tag{25.10}
$$

这些是所有交叉标签的完整函数，不只给出 Born 对角。每个 $K,q_j$ 都满足完整有序四变量 (R)，并有 $q_0+q_1=K$。总表示忠实，$t=e_0\ne0$，而定义 25.1 的任何项 $w$ 都不能同时满足

$$
\|F(w(a))-F(w(e))\|^2=q_0(a,e)
\quad(a=e_0,e_1).
\tag{25.11}
$$

因此这个同一来源具有坐标事件效果，而其受限原生项不能生成相应的未归一化坐标分支。

证明。$e_0,e_1$ 属于 $M$ 并复张成 $H$，$F$ 不丢失标签。对任意原 $a,b,u,v$，置 $A=a-b$、$B=u-v$。$U^k$ 两端的共同漂移相消，所以

$$
\begin{aligned}
\sum_{k=0}^2K(a\cdot U^ku,b\cdot U^kv)
&=\sum_{k=0}^2\|A+\zeta^kB\|^2\\
&=3\|A\|^2+3\|B\|^2.
\end{aligned}
\tag{25.12}
$$

对每个坐标作同一计算，即为 $q_j$ 的全部 (R)。交叉项之和因 $1+\zeta+\zeta^2=0$ 而为零；这就是 §4 及例 23.5 所用的完整恒等式，不依赖抽取有限样本。由 §20、推论 23.4，原菜单的效果是同一 $H$ 上的 $P_j=|j\rangle\langle j|$；也可直接将 (25.10) 代入其表示与唯一性结论。完整极化核由相应距离和本卷式 (4.5) 的共轭约定恢复，原标签上的纠偏项对两个事件也表示乘以 $\zeta$。

具体地，

$$
Ue=e_0,\qquad U^2e=(1+\zeta)e_0,\qquad U^3=I_M,
\qquad V_U(a)=U(a\cdot U^2e)=\zeta a.
\tag{25.13}
$$

原 $U$ 的非零漂移未被删除；$U$ 本身不是保零的量子酉算子，纠偏后的 $V_U$ 才表示 $\zeta I$。

命题 25.2 给出

$$
\|F(w(e_0))-F(w(0))\|^2
=|\lambda_w|^2
=\|F(w(e_1))-F(w(0))\|^2,
\tag{25.14}
$$

而 $q_0(e_0,0)=1$、$q_0(e_1,0)=0$，故 (25.11) 不可能。此处用同一项、同一锚和三个原标签即得矛盾；偏置不能通过换锚掩盖。数学投影 $P_j$ 确实存在，但取坐标没有包含在原项语法中。也未声称两种不同表示具有相同的完整原数据，或较丰富的 $\Omega$ 不能实现投影。证毕。

### 25.3 由实际接续与共同参考补足有限接口

**假设 25.4（同源接续、正交记录与分析器）。**在命题 25.3 的同一个来源上，增加实际总接续 $r_0,r_1:M\to M$，要求所有原 $a,c$ 的共同参考混合配对满足

$$
\kappa(c,r_j(a))=\kappa_j(c,a).
\tag{25.15}
$$

若还要求相干保留结果，则增加一个共同输出载体 $N$、实际映射 $i_j:M\to N$、$R:M\to N$ 及强正复核 $L$。这里强正指每个有限 Gram 矩阵半正定，约定第一变量共轭线性。要求

$$
\begin{gathered}
L(i_j(c),i_k(b))=\delta_{jk}\kappa(c,b),\\
L(i_j(c),R(a))=\kappa_j(c,a),\qquad
L(R(a),R(a))=\kappa(a,a).
\end{gathered}
\tag{25.16}
$$

$i_j$ 给各结果的同载体参考；$R$ 是带完整记录的共同接续。若要相干混合这些记录，还须另给在该共同输出上实际合法且相对于这些参考校准的分析器。式 (25.15)–(25.16) 本身不供应分析器、控制、准备或复合权限。

**命题 25.5（静态效果到实际坐标分支的有条件桥）。**在命题 25.3 与假设 25.4 下，全部原输入满足

$$
F(r_j(a))=P_jFa.
\tag{25.17}
$$

特别 $r_0(a)=(a_0,0)$、$r_1(a)=(0,a_1)$ 是这一忠实来源上唯一满足 (25.15) 的接续，且它们是新增运算而非受限原生项。对该接续，预测波定理 7.2 的精确对应为

$$
H_n=H_{n+1}=\mathbb C^2,\qquad
\mathcal K_n=\mathcal K_{n+1}=\kappa,\qquad O=\{0,1\},\qquad M_j=P_j.
\tag{25.18}
$$

若再有 (25.16)，则在 $L$ 的 Hilbert 表示中，$R$ 的像恰为固定共同参考下的记录等距

$$
V_{\rm rec}\psi=P_0\psi\otimes|0\rangle+P_1\psi\otimes|1\rangle.
\tag{25.19}
$$

这里的相位由混合参考配对固定，不仅由同结果守恒固定。

证明。(25.15) 给

$$
(Fc)^\dagger\bigl(F(r_j(a))-P_jFa\bigr)=0\qquad(c\in M).
$$

$F(M)$ 复张成 $\mathbb C^2$，故括号为零。其值仍在 $\mathcal O^2$，所以显示的坐标接续确为总定义；$F$ 忠实又给原标签唯一性。命题 25.3 排除了它们是原项的可能。于是

$$
\kappa(r_j(a),r_j(b))=\kappa_j(a,b),\qquad
\sum_j\kappa(r_j(a),r_j(b))=\kappa(a,b).
\tag{25.20}
$$

这正好是[《相融预测波与关系谱》定义 7.1、定理 7.2](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#7-预测波怎样给出概率与观察者的记录增长)的式 (7.1)，合法描述在本例张成全部 $\mathbb C^2$。直接复用该定理，得到 $M_j=P_j$、$\sum_jM_j^\dagger M_j=I$、分支 $\rho\mapsto P_j\rho P_j$ 及数学记录等距；不另输入 CP 假设。完全正、Kraus 分支和记录等距的这部分是既有结论的应用。其一般有限维先例见 Watrous，*The Theory of Quantum Information*，[第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22、Corollary 2.27；这些先例不构造本来源的实际 $r_j$ 或 $R$。

为识别实际 $R$，令 $G:N\to H_L$ 为强正核的最小 Gram 表示。(25.16) 第一式给正交等距 $T_j:H\to H_L$，满足 $T_jFc=G(i_j(c))$。将

$$
s_a=\sum_jT_jP_jFa
$$

与每个 $T_jFc$ 配对，(25.16) 第二式给 $G(R(a))-s_a$ 正交于两个参考子空间。又有

$$
\|s_a\|^2=\sum_j\|P_jFa\|^2=\|Fa\|^2=\|G(R(a))\|^2.
\tag{25.21}
$$

由正交分解，残差范数为零。因此 $G(R(a))=s_a$，在 $T_j\psi\leftrightarrow\psi\otimes|j\rangle$ 的固定识别下就是 (25.19)。这还从显示配对推出全部 $L(R(a),R(b))$，没有遗留未定的额外记录分量。若只保留 (25.20)，每支重相位 $P_j\mapsto e^{i\gamma_j}P_j$ 仍守恒，故不足以给出 (25.16) 的参考相位。

原漂移仍须逐项保留：

$$
\begin{aligned}
F(r_j(Ua))&=\zeta P_jFa+P_jt,\\
F(U(r_j(a)))&=\zeta P_jFa+t,\\
F(r_j(V_Ua))&=\zeta F(r_j(a)).
\end{aligned}
\tag{25.22}
$$

在 $t=e_0,j=1$ 时前两行不同；不能以 $r_j$ 与原 $U$ 交换代替正确的纠偏协变性。证毕。

### 25.4 固定全局纯参考与正成功域上的历史

**定义 25.6（共同参考及其额外资源）。**将上述 $H=\mathbb C^2$ 作为目标系统 $S$ 的幅度空间。另给两个二维系统 $C,E$ 和两个二维记录 $R_1,R_2$，固定同一个全局纯参考

$$
\begin{gathered}
\mathcal H=H_C\otimes H_S\otimes H_E\otimes H_{R_1}\otimes H_{R_2},\\
|\Psi_0\rangle=|+\rangle_C\otimes|\Phi^+\rangle_{SE}
                    \otimes|00\rangle_{R_1R_2},\\
|+\rangle=(|0\rangle+|1\rangle)/\sqrt2,\qquad
|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,\\
\omega(X)=\langle\Psi_0|X|\Psi_0\rangle,\qquad
\omega_S(B)=\omega(I_C\otimes B\otimes I_{ER_1R_2})
             =\operatorname{Tr}(B)/2.
\end{gathered}
\tag{25.23}
$$

$\omega_S$ 忠实于 $M_2(\mathbb C)$，$\omega$ 不忠实于完整 $M_{32}(\mathbb C)$。全局纯参考、这些复合系统、独立 ready 控制、ready 记录、目标门 $X=|0\rangle\langle1|+|1\rangle\langle0|$、从 $S$ 到各记录的 CNOT 记录操作，以及所用的合法复合，均作为额外资源前件。它们不由原乘法和 $U$ 的项生成定理供应。

对任意实际给定的全局分支算子 $D$，定义

$$
w_D=\omega(D^\dagger D)\ge0,\qquad
\omega_D(B)=\frac{\omega(D^\dagger BD)}{w_D}\quad\text{仅当 }w_D>0.
\tag{25.24}
$$

若 $D$ 是收缩，则 $w_D\le1$。称其为成功概率时，另要求实际给出带成功旗标的完整操作，失败结果也保留；单凭收缩矩阵的存在不授予这项实际权限。若 $w_D=0$，保留未归一化零分支，不定义条件泛函。

对一个实际给定的目标收缩 $A$，其全局提升取其余因子上的单位，简记

$$
w_A=\omega_S(A^\dagger A),\qquad
\omega_{S,A}(B)=\frac{\omega_S(A^\dagger BA)}{w_A}\quad(w_A>0).
\tag{25.25}
$$

这些是同一个参考的标准过滤评价。$A=0$ 给 $w_A=0$；只有在本目标代数的忠实性下，才能由 $A\ne0$ 推出 $w_A>0$。对一般非忠实参考，非零算子也可有零权。例如 $D=|-\rangle\langle-|_C\otimes I$ 非零而 $D|\Psi_0\rangle=0$。任意有界 $B$ 在零权时满足 $\omega(D^\dagger BD)=0$，因为 $D|\Psi_0\rangle=0$；这不使分母成为正数。

对实际给定的任意有限分支词 $K_h$，同样置

$$
p_h=\omega(K_h^\dagger K_h),\qquad
\omega_h(B)=\frac{\omega(K_h^\dagger BK_h)}{p_h}\quad(p_h>0).
\tag{25.26}
$$

词内的乘法是已给算子按实际时间次序的复合，独立于 (25.1) 的原二元聚合。完整有限分支树的归一化由预测波定理 7.2 的逐层守恒复用；其标准有限归纳不构造新的记录系统或任意长度程序权限。零历史始终保留未归一化零量，不除以零。

**命题 25.7（同一全局参考、定常目标边缘与不同历史相关）。**在命题 25.5 的投影接续与定义 25.6 的资源下，两种程序 $Z$–$I$–$Z$ 和 $Z$–$X$–$Z$ 共用 (25.23) 的同一个 $\omega$。其第一次、第二次结果的联合表分别为

$$
\bigl(p_I(i,j)\bigr)_{i,j=0}^1
=\begin{pmatrix}1/2&0\\0&1/2\end{pmatrix},\qquad
\bigl(p_X(i,j)\bigr)_{i,j=0}^1
=\begin{pmatrix}0&1/2\\1/2&0\end{pmatrix}.
\tag{25.27}
$$

两次读数的边缘均匀，忽略记录的目标态始终为 $I/2$；完整全局态及记录则不要求在程序作用下不变。若额外坚持同一个全局泛函对这些 ready 记录操作也不变，便与本例的非平凡记录概率矛盾。

证明。令 $C_k$ 为实际给定的 $\mathrm{CNOT}_{S\to R_k}$，其余系统上作用单位，并令

$$
T_U=C_2U_SC_1,\qquad U\in\{I,X\},\qquad
\Pi_i^{R_k}=|i\rangle\langle i|_{R_k}.
$$

记录在 ready 输入上的作用就是 (25.19) 的本例提升，故同一个参考上的联合评价为

$$
\begin{aligned}
p_U(i,j)
&=\omega\bigl(T_U^\dagger\Pi_i^{R_1}\Pi_j^{R_2}T_U\bigr)\\
&=\omega_S(P_iU^\dagger P_jUP_i)
=\omega_S(K_{ji}^\dagger K_{ji}),\qquad K_{ji}=P_jUP_i.
\end{aligned}
\tag{25.28}
$$

$P_jIP_i=\delta_{ji}P_i$，而 $XP_i=P_{1-i}X$；$\omega_S(P_i)=1/2$，即得 (25.27)。每个显示的正历史权重为 $1/2$。等价地，按 $S,E,R_1,R_2$ 的次序写出记录部分，两个全局输出向量分别是

$$
\begin{aligned}
T_I|\Psi_0\rangle
 &=|+\rangle_C\otimes
   \bigl(|0,0,0,0\rangle+|1,1,1,1\rangle\bigr)/\sqrt2,\\
T_X|\Psi_0\rangle
 &=|+\rangle_C\otimes
   \bigl(|1,0,0,1\rangle+|0,1,1,0\rangle\bigr)/\sqrt2.
\end{aligned}
\tag{25.29}
$$

迹掉 $E,R_1,R_2$ 得 $I/2$。在每一中间阶段也有

$$
\sum_iP_i(I/2)P_i=I/2,\qquad U(I/2)U^\dagger=I/2,
\tag{25.30}
$$

所以目标非选择态定常，不妨碍记录相关改变。另一方面，ready 初态有 $\omega(\Pi_1^{R_1})=0$，记录后有
$\omega(T_U^\dagger\Pi_1^{R_1}T_U)=1/2$，排除了对这一全局操作的不变性。固定参考泛函与对所有复合操作不变是不同条件。

静态效果不决定后继的数学先例已见预测波 §7 及[同效果而二步联合律不同的命题](../../../D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.lean)；本命题使用其有限分支计算，将同一忠实目标参考、纯全局参考和 ready 记录同时放入 (25.9) 的有条件扩充。$X$ 与记录操作已明列为新增资源，没有把两张不同程序表说成相同完整原操作数据的两种实现。证毕。

### 25.5 过滤后的相干校准与门提升

**假设 25.8（同参考的受控门与校准分析器）。**在定义 25.6 的固定参考上，给一个实际可用的目标酉门提升 $W$。除目标过滤的成功分支 $A$ 外，另给实际受控门

$$
\mathrm C(W)=|0\rangle\langle0|_C\otimes I_S
             +|1\rangle\langle1|_C\otimes W,
\tag{25.31}
$$

在 $E,R_1,R_2$ 上取单位；并给相对于 ready $|+\rangle_C$ 和 (25.31) 共同校准的 $+$ 分析器。过滤不作用控制；受控门之前，控制独立于过滤后的目标及成功旗标，且处于 ready $+$。这里指定的是门提升及其相位参考，不能只给目标通道 $B\mapsto WBW^\dagger$。

**命题 25.9（同一参考对分支和相干门提升的联合约束）。**在假设 25.8 下，完整程序的成功且 $+$ 的未归一化联合概率为

$$
p(\mathrm{success},+)
=\frac{w_A+\operatorname{Re}\omega_S(A^\dagger WA)}2.
\tag{25.32}
$$

仅在 $w_A>0$ 时，条件概率为该式除以 $w_A$。取 $A=I$，则

$$
p_+(W)=\frac{1+\operatorname{Re}\omega_S(W)}2,
\qquad p_+(I)=1,\qquad p_+(-I)=0.
\tag{25.33}
$$

$I$ 与 $-I$ 的无控制目标通道相同，但在固定共同参考的受控程序中不同。这不构成对完整原核不可识别性的反例：命题 25.3 的完整数据已经区分其目标输出标签。

证明。过滤成功后的目标与环境向量为 $(A\otimes I_E)|\Phi^+\rangle$，平方范数为 $w_A$；仍与 $|+\rangle_C$ 独立。再施 (25.31) 并取 $+$，未归一化向量为

$$
\frac12\bigl((I+W)A\otimes I_E\bigr)|\Phi^+\rangle.
$$

由 $W^\dagger W=I$，其平方范数为

$$
\frac14\omega_S\bigl(A^\dagger(2I+W+W^\dagger)A\bigr)
=\frac12\bigl(w_A+\operatorname{Re}\omega_S(A^\dagger WA)\bigr).
\tag{25.34}
$$

这复用标准受控干涉计算及[混合控制块的偏迹恒等式](../../../D5/S3/Quantum/Dynamics/PositivePauliClockOrder.lean)的同类迹配对，亦与预测波 §7 的跨记录相位边界一致。Cauchy–Schwarz 给
$|\omega_S(A^\dagger WA)|\le w_A$，故联合权重属于 $[0,w_A]$；$w_A=0$ 时该式为零，不产生条件概率。取 $A=I$ 即得 (25.33)。目标通道只用 $WBW^\dagger$，整体负号相消，而受控门的负号相对于控制零支变成相对相位。

这一全局／相对相位区别的文献先例见 Araújo、Feix、Costa、Brukner，*Quantum circuits cannot control unknown operations*，[原文](https://arxiv.org/html/1309.7976v2)。该文的未知黑箱电路前件不能排除本假设已供应的校准原生受控门；反之，无控制通道数据也不能自动供应 (25.31)。

在忠实原来源中，$-e_0$ 是实际标签，并且

$$
K(e_0,-e_0)=4,\qquad K(e_0,e_0)=0.
\tag{25.35}
$$

故完整原数据从未将两个标量提升识别为同一输出。式 (25.15)–(25.16) 的共同参考配对同样固定分支作用与相位，不能在保留这些数值时任意重相位。

还有一个不依赖逐门相位校准的受限比较：固定实际门标签字母表，给每个标签重相位 $W_g\mapsto e^{i\theta_g}W_g$。若字 $w$ 中标签 $g$ 出现 $n_g(w)$ 次，则

$$
W_w\longmapsto e^{i\Theta(w)}W_w,\qquad
\Theta(w)=\sum_g n_g(w)\theta_g,
\tag{25.36}
$$

因标量位于中心。两字 $w,v$ 若每个标签次数都相等，则交叉参考值
$\omega_S(W_v^\dagger W_w)$ 的重相位因子为一。这个逐标签平衡条件足以使中央相位抵消，即使门的次序不同；它不供应相干比较两字的装置。逆门若作为不同标签供应，就分别计数，除非另有相位绑定合同。无此平衡条件且无共同参考，普通概率或分别的同结果核不足以固定相干提升；若实际历史、跨历史／参考配对及终端分析器全部给定，其有限预测便由这些共同数据固定。证毕。

### 25.6 原来源、几何类型与充分接口的边界

**命题 25.10（受限生成障碍不选择唯一态或三维本体）。**命题 25.2–25.9 的组合给出以下有条件关系：在 (25.9) 的完整静态来源中，原项不能实现坐标分支；加入 (25.15) 的实际接续，便能按 (25.18) 复用既有仪器表示；再给 (25.16)、ready 复合资源及 (25.31) 的共同相位参考和分析器，(25.27)、(25.32) 就由同一个 (25.23) 计算。这个充分接口不推出其资源的全局最小性，也不从受限签名选出唯一 $\omega$。

证明。前述命题已逐项证明这条有条件链。为见选择态的边界，对每个 $0<r<1$，

$$
\sigma_r=\operatorname{diag}(r,1-r),\qquad
\omega_r(B)=\operatorname{Tr}(\sigma_rB)
\tag{25.37}
$$

都是忠实归一化目标态，均在全部原生标量酉门的共轭下不变。故原生标量不变性不能选择 $r=1/2$；而加入的坐标探针给 $\omega_r(P_0)=r$，区分这些态。(25.23) 选择一个共同参考足以作条件计算，但不证明它是唯一物理来源。即使另给固定矩阵代数上全部酉共轭不变性，标准迹唯一性也只选择该代数上的迹态，不确定其全局纯化、ready 资源或物理取得性。

各几何对象的类型同时保留。$\zeta\in\mathbb C$ 是三次标量相位；在 $H$ 的实化上，$R_0$ 表示 $\zeta I$，而

$$
J=\frac{2R_0+I}{\sqrt3},\qquad J^2=-I
\tag{25.38}
$$

是 §4 的实复结构，作用于本例四维实幅度空间。qubit 的密度矩阵另有 Pauli 表示

$$
\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2,\qquad
\mathbf r\in\mathbb R^3,\quad\|\mathbf r\|\le1.
\tag{25.39}
$$

这是已选 $H=\mathbb C^2$ 后的 Bloch 三维，不能与实幅度四维相认。$\zeta I$ 的共轭在所有密度矩阵上为恒等，因此它本身不产生非平凡 Bloch 转动；$\omega$ 则是算子代数上的正线性泛函，不是相位数或 $J$。

[C139 定义 16.1](AURIC_C139_MUTUAL_PROBES_AND_INTRINSIC_RECOVERY_OF_SQUARE_GEOMETRY.md#16三路算术读口的实际供给与稠密边界)明确加入相干三等分、非标量端口与 Fourier 操作，故其扩充菜单不受旧受限签名的标量结论限制。[环境耦合卷 §§19–21](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#19-平衡零模族的原零探针刚性)的有限探针也以完整矩阵乘法、正泛函及 Hermitian 角探针背景为前件；其中的矩阵探针不能不经来源桥梁就充当本节的原标签项。相应的 [spin-factor／Pauli 完整分类](../../../D5/S3/Quantum/SpinFactor/OriginalClassification.lean)以 $E=\mathbb R\times\mathbb R^3$ 及 P2、PB 关系为输入，不从这里的受限签名推导维数。

因而，将这条链用于 §23.6 所保留的同一个完整原 $\Omega$，仍须从该原来源证明 §23 的实际群右作用或 §24 的实际交换幺半群右作用等充分结构，或另付一般 magma 的几何／事件前件，构造非标量接续及其混合参考律，并给非零准备、概率标尺、保留记录、合法联合、相干分析器与所用控制。对任意长度程序、物理时钟、时空维数、全部未来 Return 和唯一本体来源的结论，均不能只由这里的有限条件链推出。这里的组合是针对原签名及其显示扩充的数学推导；结构归纳、整数范数、过滤、有限历史和受控干涉都是上述引文范围内的标准中间工具，不据此提出历史优先权或新增数学公理的唯一性主张。证毕。

## 追加锚（本行以下为增补区）

## 26. 可见像上的三相方程与二次支配奇部消去

以下在定义 21.1 的同一个原群上，给出定理 21.3 的可见像直接证明。记该定义的原有向核为 $c=d$；辅助对称核取平均 $k=(d+d^{\mathsf T})/2$，而非 (21.11) 的总和 $K=d+d^{\mathsf T}$。因此下文的 $F$ 可由 (21.12) 的表示除以 $\sqrt2$ 取得，其正规核不变。直接证明先建立 $\phi:F(G)\to[0,\infty)$，再用奇部的倍增与二次支配推出对称性。

**定义 26.1（真群有向全关系模型）。**令 $G$ 为任意真群，单位为 $1$；不要求交换、可数、拓扑、增长或有限生成。令 $U:G\to G$ 为任意总映射，不要求 $U1=1$、满射、乘法性或周期性。令

$$
c:G^2\longrightarrow[0,\infty)
$$

处处有限且 $c(g,g)=0$，不预设 $c(g,h)=c(h,g)$。对全部有序 $a,b,u,v\in G$ 假设

$$
\sum_{j=0}^2c\bigl(aU^ju,bU^jv\bigr)=3c(a,b)+3c(u,v).
\tag{26.1}
$$

乘法、逆元、括号及 $U$ 的迭代均是给定真群上的实际运算。

**定理 26.2（真群有向全关系的直接商像证明）。**定义 26.1 的 (26.1) 等价于存在复 Hilbert 空间 $H$ 及映射 $F:G\to H$，满足

$$
\begin{gathered}
F1=0,\qquad F(gh)=F(g)+F(h),\\
F(Ug)=\omega F(g)+t,\qquad t=F(U1),\\
c(g,h)=\|F(g)-F(h)\|^2,
\qquad \omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\end{gathered}
\tag{26.2}
$$

最小空间 $\overline{\operatorname{span}_{\mathbb C}F(G)}$ 按本卷定理 1.3 的保标签唯一性唯一到酉同构；零核和奇异核均包含在结论中，且 $t$ 不被要求为零。

**证明（六步）。**

**第一步：对称化只用于调用既有真群分类。**置 $c^{\mathsf T}(a,b)=c(b,a)$。将 (26.1) 的四元组换成 $(b,a,v,u)$，可见 $c^{\mathsf T}$ 也满足同一关系。于是

$$
k=\frac{c+c^{\mathsf T}}2
$$

是对称、处处有限、非负、零对角并满足 (19.1) 的核。对 $k$ 应用已有定理 19.4，得到某个 $F:G\to H$ 和 $t=F(U1)$，使

$$
F1=0,\quad F(gh)=Fg+Fh,\quad F(Ug)=\omega Fg+t,
\quad k(a,b)=\|Fa-Fb\|^2.
\tag{26.3}
$$

由于 $c^{\mathsf T}\ge0$，逐点有

$$
0\le c(a,b)\le 2k(a,b)=2\|Fa-Fb\|^2.
\tag{26.4}
$$

这里尚未把 $c$ 识别为 $k$；(26.3) 只是为有向核提供同一比较几何和支配界。

**第二步：不使用对称性的右平移不变性。**固定 $a,b$，置

$$
h(x)=c(ax,bx),\qquad m=\inf_{x\in G}h(x)\ge0.
$$

在 (26.1) 中取背景 $(ax,bx)$ 和增量 $(u,u)$，得到

$$
\sum_{j=0}^2h(xU^ju)=3h(x).
\tag{26.5}
$$

给定目标 $y$，取实际群元 $u=x^{-1}y$。其第零项为 $h(y)$，其余各项不小于 $m$，故

$$
h(y)-m\le3\bigl(h(x)-m\bigr).
\tag{26.6}
$$

对 $x$ 取下确界即得 $h(y)=m$。取 $x=1$，得到

$$
c(ax,bx)=c(a,b),\qquad c(a,b)=f(ab^{-1}),\qquad f(g):=c(g,1).
\tag{26.7}
$$

这一步只使用真实右逆元求解 $xu=y$，不交换任何群因子，也不要求下确界被取到。

**第三步：先支付有向核的完整陪集下降。**令

$$
N=\ker F,\qquad p_j=U^j1,\qquad T_jw=U^jw\,p_j^{-1}.
$$

由 (26.3) 的仿射递推，存在 $t_j=F(p_j)$ 使

$$
F(U^jw)=\omega^jFw+t_j,\qquad F(T_jw)=\omega^jFw.
\tag{26.8}
$$

$N$ 是实际群同态 $F$ 的正规子群。若 $w\in N$，则 (26.4) 给 $f(w)=0$；同步标记等距（本卷引理 2.1，适用条件正是处处有限非负性与完整 (R)）给

$$
f(T_jw)=c(U^jw,p_j)=c(w,1)=0,
\qquad T_jN\subseteq N.
\tag{26.9}
$$

固定 $x\in G$，令

$$
m_x=\inf_{z\in N}f(xz).
$$

对 $z,w\in N$，在 (26.1) 中取背景 $(xz,1)$ 和增量 $(w,1)$；用 (26.7) 和 (26.9) 化简三个项，得到

$$
\sum_{j=0}^2f(xzT_jw)=3f(xz).
\tag{26.10}
$$

三个参数 $xzT_jw$ 都在同一陪集 $xN$。给定 $z_0\in N$，取实际 $w=z^{-1}z_0$，则 $T_0w=w$，所以第零项是 $f(xz_0)$，从而

$$
f(xz_0)-m_x\le3\bigl(f(xz)-m_x\bigr).
\tag{26.11}
$$

对 $z$ 取下确界，得 $f(xz_0)=m_x$；取 $z_0=1$ 后

$$
f(xz)=f(x)\qquad(x\in G,z\in N).
\tag{26.12}
$$

令 $S=F(G)$。它是加法子群。定义 $\phi:S\to[0,\infty)$ 为 $\phi(Fg)=f(g)$。这是良定义的：若 $Fg=Fh$，则 $gh^{-1}\in N$；正规性把左侧的 $N$ 因子移到右侧，具体为

$$
g=(gh^{-1})h=h\,(h^{-1}(gh^{-1})h),
$$

其中括号内的元素属于 $N$，故由 (26.12) 有 $f(g)=f(h)$。于是

$$
c(a,b)=\phi(Fa-Fb),\qquad 0\le\phi(x)\le2\|x\|^2\quad(x\in S).
\tag{26.13}
$$

这里的 $N$ 可以很大，甚至 $N=G$；没有把零距离纤维误当作原标签相等。

**第四步：在可见商上取得完整三相关系。**先由 (26.8) 看出 $S$ 对 $\omega$ 稳定：$t=F(U1)\in S$，且

$$
\omega Fg=F(Ug)-t\in S.
\tag{26.14}
$$

对任意 $a,b$，引理 2.1 给出原有向核的同步等距 $c(Ua,Ub)=c(a,b)$。若 $x=Fa-Fb$，则

$$
\phi(\omega x)=\phi(x).
\tag{26.15}
$$

任取 $x=Fa-Fb$、$y=Fu-Fv$，把 (26.1) 用 (26.13) 改写，得到 $S$ 上的完整方程

$$
\sum_{j=0}^2\phi(x+\omega^jy)=3\phi(x)+3\phi(y).
\tag{26.16}
$$

仿射漂移在两端的差中逐项消失；此处没有假设 $U$ 是同态、满射或周期映射。

**第五步：二次支配消灭奇部。**在 (26.16) 中取 $y=x$，并用 $1+\omega=-\omega^2$、(26.15)，得到

$$
\phi(2x)+2\phi(-x)=6\phi(x).
\tag{26.17}
$$

定义 $h(x)=\phi(x)-\phi(-x)$。将 (26.17) 对 $-x$ 使用并相减，得

$$
h(2x)=8h(x).
\tag{26.18}
$$

另一方面由 (26.13)，对每个 $n\ge0$ 有

$$
|h(2^nx)|\le\phi(2^nx)+\phi(-2^nx)
\le4\,4^n\|x\|^2.
\tag{26.19}
$$

结合 (26.18) 即

$$
8^n|h(x)|\le4\,4^n\|x\|^2,
$$

令 $n\to\infty$，得到 $h(x)=0$。故 $\phi$ 偶，且由 (26.13)

$$
c(a,b)=\phi(Fa-Fb)=\phi(Fb-Fa)=c(b,a).
\tag{26.20}
$$

于是 $c=k$，(26.3) 已经给出 (26.2) 的表示。

**第六步：反向及最小性。**反设 (26.2) 成立。置 $t_0=0$、$t_1=t$、$t_2=(1+\omega)t$，则

$$
F(U^ju)=\omega^jFu+t_j.
$$

令 $X=Fa-Fb$、$Y=Fu-Fv$。两端共同的 $t_j$ 相消，且

$$
\begin{aligned}
\sum_{j=0}^2c(aU^ju,bU^jv)
&=\sum_{j=0}^2\|X+\omega^jY\|^2\\
&=3\|X\|^2+3\|Y\|^2
=3c(a,b)+3c(u,v).
\end{aligned}
\tag{26.21}
$$

这证明 (26.1)。最小表示的酉唯一性沿用本卷定理 1.3；整个证明没有把辅助商、陪集或 Hilbert 表示中的相等提升为原群标签相等。证毕。

**推论 26.3（第 19 节对称输入的消除）。**在真群、任意总 $U$、处处有限非负零对角和完整四变量关系的分支内，端点互换对称性是定理 26.2 的结论而非独立前件。因此定理 26.2 去除了第 19 节定义 19.1 与定理 19.4 的对称输入；第 19 节的分类可作为本证明第一步调用的既有结果，新增的实质关系是对原有向 $c$ 的全陪集下降和奇部消去。

**命题 26.4（实际群结构、奇异核和漂移的边界）。**定理 26.2 不使 $G$ 交换，也不使 $U$ 成为同态、满射或周期映射。$F$ 只把实际群送入加法群，因而杀掉实际交换子：

$$
F([g,h])=F(ghg^{-1}h^{-1})=0,
$$

但 $[g,h]=1$ 未由此推出。$N=\ker F$ 是可见比较几何的不可见正规子群；$N=G$ 时 (26.4) 立即给 $c\equiv0$，并取 $H=0,F=0,t=0$。非零漂移仍可出现，例如

$$
G=(\mathbb C,+),\qquad U z=\omega z+t,\qquad Fz=z,
\qquad c(z,w)=|z-w|^2,
\tag{26.22}
$$

其中 $t\in\mathbb C$ 任意，(26.1) 仍成立。可见商上的相位作用是比较几何；它不是原群标签上的门同态、可逆过程或物理时间演化。

**命题 26.5（直接推导的结构前件与适用范围）。**定理 26.2 的前件仍为实际真群、任意总 $U$、处处有限非负零对角和完整有向关系；一般有单位 magma 的结论及实际物理供给不在此结论内。

**证明。**第 19.2 的下确界机制和第 19.4 的对称真群分类在上述前件下适用；真实逆元、正规核和 (26.10)–(26.12) 先给完整原始有向核的陪集下降，(26.13)–(26.20) 再直接消去奇部，没有把 W41.1 或 W41.2 的 $\mathrm C_3$ 前件提前借入，也不需要调用 W43.3 的返回分类。辅助群、直积、核商、Hilbert 完备化和三相求和只是经典比较数学工具，不给物理复制、逆门或内部历史的实现；这些工具的使用不构成历史优先权主张。

因此，本节不解决一般有单位 magma 上的原始 $(R)\Rightarrow\mathrm C_3$，不决定第 20 节自由 $T_2$ 事件最大值，也不提供有限菜单的非零准备、可达效果、联合历史、仪器、门/过程组合、物理时间或唯一整体态 $\Omega$ 内实际读出的桥。若这些接口另有完整前件，可再调用本卷定理 6.2；本节本身只给“实际真群、任意总标记、完整有向关系”这一数学分支的结论。证毕。

## 追加锚（本行以下为增补区）
