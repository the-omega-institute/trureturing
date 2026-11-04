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
