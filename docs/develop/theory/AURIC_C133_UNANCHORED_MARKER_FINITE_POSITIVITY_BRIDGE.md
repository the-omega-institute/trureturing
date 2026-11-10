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

本节把原始对象的乘法进一步限制为真群，只为关闭一个明确的桥，不把所得结论外推到一般有单位 magma。交换性在这里仍是比较读数的明确定义输入；它不等同于既有有向模型的交换，也不等同于序贯测量操作可交换。

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
c(a,b)=f(ab^{-1}),\qquad f(1)=0,qquad f(x^{-1})=f(x),
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
c_\infty(U_*1_S,1_S)=0,qquad
c_\infty(x_a,x_b)=c(a,b)\quad(a,b\in A),
\tag{19.10}
$$

其中 $x_a\in S$ 是指定的来源。$S$ 的群律、逆元和 $U_*$ 的总性在取极限前已经成立；$a\mapsto x_a$ 不被宣称为保乘法或保标记的映射。

**证明。**沿用[续卷 W 定理 9.2–9.3](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#9-精确保留比较矩阵的右梳)的实际右梳。令 $\Sigma_N=\{0,1,2\}^N$，$G_N=G^{\Sigma_N}$ 逐坐标取真群运算，$U_N$ 逐坐标作用，真实单位为常数组 $\mathbf1$，并置

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
c_N(\Gamma_N(1),\mathbf1)+c_N(\mathbf1,\Gamma_N(1))\le\frac{\Omega}{N},qquad
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
B(1)=0,\qquad B(x_a)=3q(a)+3\Omega,qquad
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

取收敛子列，再取一个共同的对角子列 $N_\ell\to\infty$；这里 $\pi_N$ 是第 $N$ 个坐标投影。由 (19.16)，每个极限有限，定义

$$
c_\infty(s,t)=\lim_{\ell\to\infty}c_{N_\ell}(\pi_{N_\ell}s,\pi_{N_\ell}t).
\tag{19.17}
$$

非负性、对称性和零对角通过有限标量极限保留。对任意固定 $a,b,u,v\in S$，投影保留乘法、逆元、单位和 $U_*$；同一个对角子列中的六个相关标量同时收敛，所以完整 (19.1) 也保留。由 (19.13)，

$$
c_\infty(U_*1_S,1_S)=\lim_{\ell\to\infty}\frac{q(p_1)}{N_\ell}=0.
$$

而 (19.12) 给出 (19.10) 的比较矩阵保留。故这是处处定义的总真群模型，而非有限窗口或相互独立的边界序列。证毕。

**定理 19.4（真群任意标记的完整仿射复几何等价）。**在定义 19.1 的模型类中，完整关系 (19.1) 等价于存在复 Hilbert 空间 $H$ 和映射 $F:G\to H$，使

$$
\begin{gathered}
F1=0,\qquad F(gh)=F(g)+F(h),\\
F(Ug)=\omega F(g)+t,qquad t=F(U1),\\
c(g,h)=\|F(g)-F(h)\|^2,qquad
\omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\end{gathered}
\tag{19.18}
$$

最小表示 $H=\overline{\operatorname{span}_{\mathbb C}F(G)}$ 按本卷定理 1.3 的保标签唯一性唯一到酉同构。零核 $c\equiv0$ 包含在此结论中；$t$ 不被要求为零。

**证明。**先证 (19.1) 蕴涵 (19.18)。任取至多五个原标签 $a_1,\ldots,a_m$（允许重复），令 $A$ 为其有限集合，应用引理 19.3 得到 $(S,U_*,c_\infty)$。在整个真群 $S$ 上应用引理 19.2；其零集 $Z_\infty$ 是正规子群，独立代表元的完整行列相等，且 $U_*$ 在陪集上下降。因为

$$
c_\infty(U_*1_S,1_S)=0,
$$

下降后的实际单位被下降的标记固定：$\overline U[1_S]=[1_S]$。因此真群商 $S/Z_\infty$ 连同下降后的有限非负零对角核满足[续卷 V 定理 1.3](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#1-原始关系与有限正性判据)的全部前件。该定理给出其平方距离的复 Hilbert 表示，故对任意实系数 $\alpha_i$ 且 $\sum_i\alpha_i=0$，有

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

其像作用为乘以 $\omega$，因而为三阶自同构；这是商上的推论，不是原标签上的运算等式。对每个 $j=1,2$，本卷式 (8.2) 的双向单位缺陷在 (19.18) 中直接展开为零，所以两个完整代表元方向都闭合。

这里没有新增准备、参考、效果、事件、联合、仪器、过程、组合或物理时间的实际来源；第 6 节与 §11.2 的接口条件仍须分别供应。辅助直积、群生成、逆元、对角极限、商和 Hilbert 完成都只是比较数学构造，不是可执行的物理复制、逆门或时间演化。定理 19.4 不解决一般任意有单位 magma，也不完成完整量子起源问题；它只关闭真群、任意总标记这一有界桥。固定相位正性分类仍由续卷 V 覆盖，本节不重复该结果。

## 追加锚（本行以下为增补区）
