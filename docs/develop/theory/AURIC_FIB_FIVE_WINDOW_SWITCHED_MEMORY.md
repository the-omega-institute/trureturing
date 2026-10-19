# AURIC FIB 五窗口切换记忆

> 本卷是独立的后继数学参考卷，采用普通 `generic-v1` 结构。已有正文及编号保持固定；后续增补从文末追加锚开始，勘误明确指出被替代的陈述。本卷研究预先指定的切换通道，所用固定通道结果归于相应前卷。

## 1. 模型、全输入接口与范数

**定义 1.1（预定义切换模型）。** 保留系统为一个 $H=\mathbb C^5$，有序正交基为 $e_0,\ldots,e_4$，对应五个标签 $(000,100,010,001,101)$。固定一个 $0<\eta<1$，记 $r=1-\eta$，并令

$$
Q=Q_\eta=\begin{pmatrix}
r&0&0&\eta&0\\r&0&0&\eta&0\\0&r&0&0&\eta\\
0&0&1&0&0\\0&0&1&0&0
\end{pmatrix}.
\tag{1.1}
$$

每个允许通道 $\Phi_t:M_5(\mathbb C)\to M_5(\mathbb C)$ 都是复线性 CPTP 映射，并满足

$$
\operatorname{diag}\Phi_t(X)=Q^{\mathsf T}\operatorname{diag}X
\qquad\text{对每个复矩阵 }X.
\tag{1.2}
$$

这里 $Q_{ij}$ 从输入 $i$ 到输出 $j$；条件包括两个有序非厄米矩阵单位，不能只在五个基态上检验。序列 $\Phi_1,\Phi_2,\ldots$ 在选择输入之前公开指定，与输入及任何结果无关。记

$$
T_{b:a}=\Phi_b\circ\cdots\circ\Phi_a\quad(b\ge a),\qquad
T_n=T_{n:1},\qquad T_{a-1:a}=\operatorname{id},\qquad T_0=\operatorname{id}.
\tag{1.3}
$$

每次应用使用新的环境并立即丢弃；两次应用之间不保留环境、测量结果、纠错综合征、输入相关历史或第二份数据。没有反馈、途中读出或途中恢复。终端恢复若出现，是最后一次通道之后作用于 $H$ 的 CPTP 映射。有限参考系统 $\mathcal K$ 完全不受通道作用，仅用于数学检验，不计作可用的操作记忆。证明中的逻辑与规范因子只是 $H$ 子空间的坐标。

周期 $\ell$ 指 $\Phi_{t+\ell}=\Phi_t$。知道起始相位及终端所处相位是额外的公开控制权；它与输入标签无关，须单独计费。固定通道的“混合”指其幂对所有复输入趋于同一个重置 $\mathcal R_\sigma(X)=\sigma\operatorname{Tr}X$。切换序列不预设具有固定的极限密度。

**约定 1.2（来源与证据范围）。** [半参数卷][HG] 为源一，[量子记忆卷][QM] 为源二。下文只引用这两份给定文本中明确提供的数学结果；其中链接的文献和其他卷均作为不透明的来源标识，不主张独立认证其版本或优先权。源二 §3 的选定有限活动 Perron–Markov 接口为

$$
\lambda=\frac{\eta}{(1-\eta)^2},\qquad
p=\frac{(r^2,\eta r,\eta,\eta r,\eta^2)^{\mathsf T}}{1+\eta}.
\tag{1.4}
$$

它不从经典分布推出 CPTP 实现。这里额外选择了全输入通道模型与公开控制序列；没有物理、实验机器学习或本征窗口操作的实现桥梁。所有证明是有限维复线性代数中的条件性数学论证，不主张 Lean 内核认证。

**引理 1.3（完整范数与参考放大）。** 使用不除以二的迹范数与

$$
\|L\|_\diamond=\sup_{m\ge1,\ Z\ne0}
\frac{\|(L\otimes\operatorname{id}_m)(Z)\|_1}{\|Z\|_1},
\tag{1.5}
$$

其中 $Z$ 可以是任意复矩阵。CPTP 映射的该范数为一，单位酉前、后复合保持该范数。对任意 $L:M_5\to M_5$，还有

$$
\|L\|_\diamond\le5\max_{i,j}\|L(|e_i\rangle\langle e_j|)\|_1.
\tag{1.6}
$$

证明。在每个放大维数，CPTP 映射的伴随 $\Theta$ 是保持单位元的 CP 映射。对正块矩阵

$$
\begin{pmatrix}Y^\dagger Y&Y^\dagger\\Y&I\end{pmatrix}
$$

应用二阶放大并取 Schur 补，得到

$$
\Theta(Y)^\dagger\Theta(Y)\le\Theta(Y^\dagger Y)
\le\|Y\|_\infty^2I.
$$

故放大伴随收缩算子范数；迹范数对偶给出任意复输入上的完全收缩。密度输入达到范数一。单位酉复合及其逆都完全收缩，因而保持范数。

为证 (1.6)，写 $Z=\sum_{ij}|e_i\rangle\langle e_j|\otimes Z_{ij}$。对其奇异值分解的一项 $|a\rangle\langle b|$，按系统指标分块 $a=(a_i)$、$b=(b_j)$，各块范数之和为

$$
\sum_{ij}\|a_i\|\|b_j\|
\le5\Bigl(\sum_i\|a_i\|^2\Bigr)^{1/2}
       \Bigl(\sum_j\|b_j\|^2\Bigr)^{1/2}=5\|a\|\|b\|.
$$

按奇异值求和便得 $\sum_{ij}\|Z_{ij}\|_1\le5\|Z\|_1$。再用三角不等式和张量积迹范数乘法性即得 (1.6)，常数与参考维数无关。$\square$

**引理 1.4（每个实际连续块的共同人口律）。** 对任意允许序列、每个复 $X$ 及每个连续子序列，

$$
\operatorname{diag}T_{b:a}(X)
=(Q^{\mathsf T})^{b-a+1}\operatorname{diag}X.
\tag{1.7}
$$

记 $E_j=|e_j\rangle\langle e_j|$，并置

$$
\mathsf A=\operatorname{span}\{e_0,e_1\},\quad
\mathsf B=\mathbb Ce_2,\quad
\mathsf D=\operatorname{span}\{e_3,e_4\},\quad
\mathsf L=\mathsf A\oplus\mathsf B,\quad z=e_2.
$$

每个单步通道都满足

$$
\begin{aligned}
\Phi_t^\dagger(E_0)&=rP_{\mathsf A},&
\Phi_t^\dagger(E_1)&=rP_{\mathsf B},&
\Phi_t^\dagger(E_2)&=P_{\mathsf D},\\
\Phi_t^\dagger(E_3)&=\eta P_{\mathsf A},&
\Phi_t^\dagger(E_4)&=\eta P_{\mathsf B},&
\Phi_t(X)&=\operatorname{Tr}(X)E_2\quad(X\in\mathcal B(\mathsf D)).
\end{aligned}
\tag{1.8}
$$

长度二的人口矩阵的前三行和后两行分别为

$$
a_Q=(r^2,0,\eta,r\eta,0),\qquad b_Q=(0,r,0,0,\eta).
\tag{1.9}
$$

因而任意二、三步前缀都有

$$
T_2^\dagger(E_0)=r^2P_{\mathsf L},\quad
T_2^\dagger(E_1)=rP_{\mathsf D},\quad
T_3^\dagger(E_2)=\eta(rP_{\mathsf L}+P_{\mathsf D})>0.
\tag{1.10}
$$

证明。将 (1.2) 再用于实际的中间复矩阵，逐步归纳得到 (1.7)，起点可以是任何 $a$。对所有 $X$ 用迹配对即得伴随公式。正输入若支持于 $\mathsf D$，其输出人口只在坐标二非零；正性迫使其余行列全为零，因此输出为其迹乘 $E_2$。正矩阵复线性张成全代数，故重置结论适用于整个 $\mathcal B(\mathsf D)$。(1.9) 由 (1.1) 的两次路径分解得到，再应用一次对角伴随便得 (1.10)。最后一个式子的特征值为 $\eta r$ 与 $\eta$，均严格为正。这些是拉回的效应，不是向前演化的密度。$\square$

## 2. 半参数的三个完整通道及其实际 Gram

**定义 2.1（给定典范与两个更新）。** 本节至第六节固定 $\eta=r=1/2$，令

$$
q=2^{-1/2},\quad u=q(e_0+e_3),\quad v=q(e_1+e_4),\quad
R=\operatorname{span}\{u,v,z\},\quad s=(u+v+z)/\sqrt3.
$$

源二定义 17.2 的典范通道记为 $C$，其完整 Kraus 对是

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|+|z\rangle\langle e_3|,\\
C(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger.
\end{aligned}
\tag{2.1}
$$

取显式符号矩阵

$$
S=\operatorname{diag}(1,-1,1,1,1),\qquad
\mathcal U=\operatorname{Ad}_S,\qquad v_-=Sv=q(-e_1+e_4),\qquad R_-=SR.
\tag{2.2}
$$

于是 $S=S^\dagger=S^{-1}$、$\mathcal U^2=\operatorname{id}$。定义

$$
A=\mathcal U\circ C,\qquad B=C\circ\mathcal U.
\tag{2.3}
$$

它们在全部五维输入上的 Kraus 算子为

$$
\begin{aligned}
A_0=SK_0&=|u\rangle\langle e_0|+q|v_-\rangle\langle e_2|+|z\rangle\langle e_4|,\\
A_1=SK_1&=|u\rangle\langle e_1|+q|v_-\rangle\langle e_2|+|z\rangle\langle e_3|,\\
B_0=K_0S&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
B_1=K_1S&=-|u\rangle\langle e_1|+q|v\rangle\langle e_2|+|z\rangle\langle e_3|.
\end{aligned}
\tag{2.4}
$$

未写出的矩阵项均为零。这里分别是输出后复合和输入前复合；“对角共轭”另指同时在两端复合互逆的相位映射。

**命题 2.2（CP、TP、全复输入律及完整 Gram）。** $C,A,B$ 都是允许通道，均有 Choi 秩二。采用源一的精确顺序

$$
\begin{aligned}
f&=(\alpha_0,\alpha_1,\beta_0,\beta_1,\gamma_0,\gamma_1,\delta_0,\delta_1),\\
\mathcal E&=((0,0),(0,1),(3,0),(3,1),(1,2),(4,2),(2,3),(2,4)),\\
w&=(q,q,q,q,q,q,1,1),\qquad G_{ab}=\langle f_a,f_b\rangle,
\end{aligned}
\tag{2.5}
$$

内积对第一变量共轭线性。对每个通道取同一个正交环境对 $f_0,f_1$，令 $c=q(f_0+f_1)$。三个实际向量列为

$$
\begin{aligned}
f^C&=(f_0,f_1,f_0,f_1,c,c,f_1,f_0),\\
f^A&=(f_0,f_1,f_0,f_1,-c,c,f_1,f_0),\\
f^B&=(f_0,-f_1,f_0,-f_1,c,c,f_1,f_0).
\end{aligned}
\tag{2.6}
$$

它们在这个共同环境基下的列因子为

$$
F_C=\begin{pmatrix}1&0&1&0&q&q&0&1\\0&1&0&1&q&q&1&0\end{pmatrix},\quad
F_A=\begin{pmatrix}1&0&1&0&-q&q&0&1\\0&1&0&1&-q&q&1&0\end{pmatrix},\quad
F_B=\begin{pmatrix}1&0&1&0&q&q&0&1\\0&-1&0&-1&q&q&1&0\end{pmatrix}.
\tag{2.7}
$$

完整实际 Gram 为 $G_D=F_D^\dagger F_D$，$D=C,A,B$，明确展开为

$$
G_C=\begin{pmatrix}
1&0&1&0&q&q&0&1\\0&1&0&1&q&q&1&0\\
1&0&1&0&q&q&0&1\\0&1&0&1&q&q&1&0\\
q&q&q&q&1&1&q&q\\q&q&q&q&1&1&q&q\\
0&1&0&1&q&q&1&0\\1&0&1&0&q&q&0&1
\end{pmatrix},
\tag{2.8}
$$

$$
G_A=\begin{pmatrix}
1&0&1&0&-q&q&0&1\\0&1&0&1&-q&q&1&0\\
1&0&1&0&-q&q&0&1\\0&1&0&1&-q&q&1&0\\
-q&-q&-q&-q&1&-1&-q&-q\\q&q&q&q&-1&1&q&q\\
0&1&0&1&-q&q&1&0\\1&0&1&0&-q&q&0&1
\end{pmatrix},
\tag{2.9}
$$

$$
G_B=\begin{pmatrix}
1&0&1&0&q&q&0&1\\0&1&0&1&-q&-q&-1&0\\
1&0&1&0&q&q&0&1\\0&1&0&1&-q&-q&-1&0\\
q&-q&q&-q&1&1&q&q\\q&-q&q&-q&1&1&q&q\\
0&-1&0&-1&q&q&1&0\\1&0&1&0&q&q&0&1
\end{pmatrix}.
\tag{2.10}
$$

证明。Kraus 表达式直接给出 CP。正交的 $u,v,z$ 给出

$$
K_0^\dagger K_0=E_0+E_2/2+E_4,\qquad
K_1^\dagger K_1=E_1+E_2/2+E_3.
$$

其和是 $I$。$A$ 的同类和仍是 $I$，$B$ 的同类和为 $SIS=I$，故三者 TP。对任意复矩阵，

$$
\operatorname{diag}C(X)=
\bigl((X_{00}+X_{11})/2,\ X_{22}/2,\ X_{33}+X_{44},\
(X_{00}+X_{11})/2,\ X_{22}/2\bigr)^{\mathsf T}.
\tag{2.11}
$$

这是因为三个相互不交的坐标支持 $u,v,z$ 的自身系数依次为 $X_{00}+X_{11}$、$X_{22}$、$X_{33}+X_{44}$；它们之间的交叉算子计算基对角为零。对角相位共轭不改变任何输入或输出对角，故 (2.3) 给出 $A,B$ 的同一全输入律。

(2.6) 的每一列都来自 (2.4) 的实际环境系数；不是独立指定的两两重叠。因子 (2.7) 证明同时 PSD、单位对角、$G_{12}=G_{34}=G_{78}=0$。其前两列已张成两维，所以秩恰为二。采用未归一化、输出在前的 Choi 矩阵

$$
J_\Phi=\sum_{ii'}\Phi(|e_i\rangle\langle e_{i'}|)\otimes|e_i\rangle\langle e_{i'}|,
$$

其活动块为 $\operatorname{diag}(w)\overline G\operatorname{diag}(w)$，因为边 $a,b$ 的环境迹是 $\langle f_b,f_a\rangle$；其余行列为零。权重严格为正，故 Choi 秩与 Gram 秩相同。这里各 Gram 为实矩阵，仍保留该共轭约定。源二边序 (4.3) 与本节边序相差源一 (2.4) 的置换 $(1,2,6,7,3,8,4,5)$；没有改换内积方向。最小环境维数因此为二。$\square$

## 3. 两个更新各自重复时都完全混合

**定理 3.1（个体混合与全输入瞬态）。** 单独重复 $A$ 或 $B$ 时，分别有

$$
A^n\longrightarrow\mathcal R_{P_{R_-}/3},\qquad
B^n\longrightarrow\mathcal R_{P_R/3}
\quad\text{于 diamond 范数}.
\tag{3.1}
$$

证明。$A$ 的全部输出支持于 $R_-$。在有序基 $(u,v_-,z)$ 上，其限制 Kraus 是 $qU_0,qV_1$，其中

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
V_1=\begin{pmatrix}0&-1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{3.2}
$$

具体地，$A_0(u,v_-,z)=q(u,z,v_-)$，$A_1(u,v_-,z)=q(z,-u,v_-)$。两个矩阵均为酉矩阵，且 $U_0^2=I$、$V_1^3=-I$。

令 $F_A=(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{V_1})/2$。若 $F_A(X)=\xi X$、$|\xi|=1$、$X\ne0$，则等长向量平均的 Hilbert–Schmidt 范数取等迫使

$$
U_0XU_0^\dagger=V_1XV_1^\dagger=\xi X.
$$

例如等式由 $\|(Y_0+Y_1)/2\|_2^2=(\|Y_0\|_2^2+\|Y_1\|_2^2)/2-\|Y_0-Y_1\|_2^2/4$ 直接得到。两种共轭的阶分别整除二和三，所以 $\xi^2=\xi^3=1$，即 $\xi=1$。

固定的 $X$ 必与 $U_0,V_1$ 对易。令

$$
J=U_0V_1=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&1\end{pmatrix}.
$$

则 $J^2=\operatorname{diag}(-1,-1,1)$，而 $V_1J^2V_1^\dagger=\operatorname{diag}(-1,1,-1)$。这两个对角矩阵在三条坐标线上的联合特征值各异；与它们都对易迫使 $X$ 对角。再与循环的带符号置换 $V_1$ 对易，迫使三个对角元相等。因此固定空间恰为 $\mathbb CI_{R_-}$。

$F_A$ 是 Hilbert–Schmidt 收缩，其幂有界，故单位圆上的 Jordan 块不可能大于一。上述证明留下单重的周边特征值一，其余块严格衰减；保迹给出极限 $Y\mapsto I_{R_-}\operatorname{Tr}(Y)/3$。对任意完整输入 $X$，$A(X)$ 已在 $\mathcal B(R_-)$，且迹仍为 $\operatorname{Tr}X$，所以 $A^n(X)=F_A^{n-1}(A(X))$ 有 (3.1) 的极限。这一步包括初始支持外的输入及所有交叉项。引理 1.3 将全矩阵单位的收敛升级为任意有限参考上的 diamond 收敛。

最后 $B=\mathcal U\circ A\circ\mathcal U$，故 $B^n=\mathcal U\circ A^n\circ\mathcal U$；其极限为第二个重置。这里 $A,B$ 彼此对角共轭，并未将它们认作 $C$ 的对角共轭。$\square$

**命题 3.2（整个 Gram 的忠实分类核对）。** 源一的半参数分类与定理 3.1 相容；$G_A,G_B$ 都不在典范 $G_C$ 的四相位轨道。

证明。按源一定义 2.3，若 $t_j$ 是单位相位，该轨道要求整个矩阵满足

$$
G_{ab}=\overline{\chi_a}\chi_b(G_C)_{ab},\quad
\chi=(1,t_0\overline t_1,t_3\overline t_0,t_3\overline t_1,
 t_1\overline t_2,t_4\overline t_2,t_2\overline t_3,t_2\overline t_4).
\tag{3.3}
$$

假设 $G_A$ 满足它。其 $G_{13}=1$ 强制 $t_3/t_0=1$；$G_{15}=-q$ 强制 $t_1/t_2=-1$；$G_{25}=-q$ 再强制 $t_0/t_1=1$；$G_{27}=1$ 强制 $t_2/t_3=1$。后三个等同关系与 $t_1/t_2=-1$ 矛盾。$B$ 是 $A$ 的对角共轭；若 $B$ 在典范轨道，则 $A$ 也在，仍矛盾。源一定理 5.1 正是对这个实际完整 Gram、此边序与此共轭方向的分类，故也判两者混合。这只是直接证明的交叉核对；秩二本身不判定混合。$\square$

## 4. 实际交替词与所有时刻的经典标签

**定理 4.1（两种起始相位的完整映射）。** 令 $T_n^A$ 对应 $(A,B,A,B,\ldots)$，$T_n^B$ 对应 $(B,A,B,A,\ldots)$。对每个 $m\ge0$，

$$
\begin{aligned}
T_{2m}^A&=C^{2m},&T_{2m+1}^A&=\mathcal U\circ C^{2m+1},\\
T_{2m}^B&=\mathcal U\circ C^{2m}\circ\mathcal U,&
T_{2m+1}^B&=C^{2m+1}\circ\mathcal U.
\end{aligned}
\tag{4.1}
$$

证明。实际两步 Kraus 词满足

$$
B_jA_i=K_jK_i=:W_{ji},\qquad A_jB_i=SW_{ji}S,
\tag{4.2}
$$

其中全部五维算子为

$$
\begin{aligned}
W_{00}&=q|u\rangle\langle e_0|+q^2|z\rangle\langle e_2|+q|v\rangle\langle e_4|,\\
W_{01}&=q|u\rangle\langle e_1|+q^2|z\rangle\langle e_2|+q|v\rangle\langle e_3|,\\
W_{10}&=q|z\rangle\langle e_0|+q^2|u\rangle\langle e_2|+q|v\rangle\langle e_4|,\\
W_{11}&=q|z\rangle\langle e_1|+q^2|u\rangle\langle e_2|+q|v\rangle\langle e_3|.
\end{aligned}
\tag{4.3}
$$

这些等式直接来自 (2.1)、(2.4) 与 $S^2=I$，故 $B\circ A=C^2$、$A\circ B=\mathcal U\circ C^2\circ\mathcal U$。对实际两步块取幂，再前置下一次更新，得到 (4.1)。$m=0$ 时两个偶数式均为恒等映射，故也包含时间零。等式在整个复代数上成立，张量任意恒等参考仍成立。$\square$

**命题 4.2（零误差的一位经典记忆）。** 置

$$
P=|s\rangle\langle s|,\qquad M=(P_R-P)/2,\qquad
w_0=(u-2v+z)/\sqrt6.
\tag{4.4}
$$

$P,M$ 是正交支持的密度，且 $C(P)=P$、$C(M)=M$。它们的人口都为 $p=(1,1,2,1,1)^{\mathsf T}/6$，相应选定源接口的活动为 $\lambda=2$。下表给出编码、每个时刻的输出及终端投影读出：

| 起始相位 | 编码零、编码一 | 偶数时刻输出 | 奇数时刻输出 | 偶数读出 | 奇数读出 |
| --- | --- | --- | --- | --- | --- |
| $A$ 先 | $P,M$ | $P,M$ | $SPS,SMS$ | $\{P,I-P\}$ | $\{SPS,I-SPS\}$ |
| $B$ 先 | $SPS,SMS$ | $SPS,SMS$ | $P,M$ | $\{SPS,I-SPS\}$ | $\{P,I-P\}$ |

每一行也可以把编码一换成 $|w_0\rangle\langle w_0|$ 或其 $S$ 共轭，得到两个正交纯输入；同一个终端读出仍然零误差。

证明。在 $(u,v,z)$ 上 $C$ 的 Kraus 是 $qU_0,qU_1$，其中

$$
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{4.5}
$$

两个置换都固定 $s$、保持 $R\cap s^\perp$，从而固定 $P$ 与该二维支持上的均匀密度 $M$。$\operatorname{diag}P=p$、$\operatorname{diag}P_R=3p$ 也给出 $M$ 的人口。应用 (4.1) 得表中每个输出；支持一直正交。$w_0$ 是该二维支持中的单位向量，其纯态经过 $C^n$ 后仍在该支持内，未要求它一直为纯态。终端第一投影对应零、第二投影对应一，即得到一位永久标签。此标签所在的两扇区随公开相位移动，逻辑零、一无需互换。

读出若写成经典输出通道，为 $Y\mapsto |0\rangle\langle0|\operatorname{Tr}(P_{\rm ph}Y)+|1\rangle\langle1|\operatorname{Tr}((I-P_{\rm ph})Y)$，只在最后执行。$\square$

## 5. 完整输入的相位极限、瞬态效应与重置距离

**定理 5.1（典范供应结果的精确对应）。** 定义

$$
d=(e_0-e_1-e_3+e_4)/2,\qquad E=P+\tfrac23|d\rangle\langle d|,
\qquad \mathcal T=(C^2+2C^3)/3.
\tag{5.1}
$$

则 $d$ 是 $R^\perp$ 中的单位向量，$E$ 是谱为 $1,2/3,0,0,0$ 的效应。对所有复 $X$，

$$
\begin{aligned}
C^\dagger(P)&=E,& C^\dagger(E)&=E,\\
\mathcal T(X)&=P\operatorname{Tr}(EX)+M\operatorname{Tr}((I-E)X),\\
C^n-\mathcal T&=(-1/2)^{n-2}(C^2-\mathcal T)\quad(n\ge2),\\
\|C^n-\mathcal T\|_\diamond&\le\tfrac43\,2^{-(n-2)}\quad(n\ge2).
\end{aligned}
\tag{5.2}
$$

证明及来源对应。本节的 $e_j,u,v,z,K_0,K_1,C$ 分别就是源二定义 17.2 的 $|j\rangle,u,v,z,K_0^\circ,K_1^\circ,\Phi_\circ$，参数严格为 $\eta=1/2$，没有换输入编码或换 Kraus 通道。源二定理 19.1 的全 $25$ 维复超算子结论为

$$
\det(tI-C)=t^{20}(t-1)^2(t+1/2)^3,\qquad
C^2(C-\operatorname{id})(C+\tfrac12\operatorname{id})=0.
\tag{5.3}
$$

该结果包含整个输入瞬态；不是只对 $\mathcal B(R)$ 的多项式。其证明在 $(u,v,z)$ 的对角、对称非对角、反对称非对角三个复子空间上给出矩阵

$$
D_0=\begin{pmatrix}1/2&1/2&0\\0&0&1\\1/2&1/2&0\end{pmatrix},\quad
S_0=\begin{pmatrix}0&1/2&1/2\\1&0&0\\0&1/2&1/2\end{pmatrix},\quad
A_0=\begin{pmatrix}0&1/2&1/2\\0&0&0\\0&-1/2&-1/2\end{pmatrix}.
$$

前两者的特征多项式为 $t(t-1)(t+1/2)$，第三者满足 $A_0^2=-A_0/2$；因此限制映射 $F$ 满足 $F(F-\operatorname{id})(F+\operatorname{id}/2)=0$。因 $C(M_5)\subseteq\mathcal B(R)$，在完整代数上多一个 $C$ 因子，正是 (5.3) 的瞬态项。这是对给定全输入定理的对应复述，非切换的新固定通道成果。

为识别效应，实际伴随像为

$$
K_0^\dagger s=(e_0+e_4)/\sqrt3+e_2/\sqrt6,\qquad
K_1^\dagger s=(e_1+e_3)/\sqrt3+e_2/\sqrt6.
$$

它们的外积和即为 $E$，且其在 $R$ 的压缩为 $P$；全部输出在 $R$，故 $C^\dagger E=C^\dagger P=E$。两个置换 $U_0,U_1$ 生成 $S_3$，相同平均范数取等论证表明固定空间就是其对易子，即 $\operatorname{span}\{P,M\}$：对易矩阵的对角位置共有一个值，有序非对角位置共有一个值。

(5.3) 等价于 $2C^4=C^3+C^2$，给出 $C\mathcal T=\mathcal TC=\mathcal T$。$\mathcal T$ 是通道的凸组合，固定空间上的恒等，故为 CPTP 投影。守恒的 $E$ 确定其 $P$ 系数，保迹确定另一系数，得到 (5.2) 的完整输入公式。又 $C(C^2-\mathcal T)=-(C^2-\mathcal T)/2$，归纳得到精确递推；$C^2-\mathcal T=(2/3)(C^2-C^3)$ 与引理 1.3 给出范数界。这也逐项对应源二定理 18.3、19.2 与源一推论 6.1。$\square$

**推论 5.2（四个相位极限及参考）。** 对两种起始相位、两个奇偶子序列，相位极限依次为

$$
L^A_{\rm even}=\mathcal T,\quad L^A_{\rm odd}=\mathcal U\circ\mathcal T,
\quad L^B_{\rm even}=\mathcal U\circ\mathcal T\circ\mathcal U,
\quad L^B_{\rm odd}=\mathcal T\circ\mathcal U.
\tag{5.4}
$$

令 $L_n^{A/B}$ 为对应奇偶极限，则每个 $n\ge2$ 都有

$$
\|T_n^{A/B}-L_n^{A/B}\|_\diamond\le\epsilon_n,
\qquad \epsilon_n=\tfrac43\,2^{-(n-2)}.
\tag{5.5}
$$

对任意有限参考及任意复 $Z$，第一个极限的完整作用为

$$
(\mathcal T\otimes\operatorname{id}_{\mathcal K})(Z)
=P\otimes\operatorname{Tr}_H[(E\otimes I)Z]
+M\otimes\operatorname{Tr}_H[((I-E)\otimes I)Z].
\tag{5.6}
$$

其余三个极限分别在输出端、输入与输出两端、输入端应用 $S$，等价于相应替换准备态或效应。每个参考误差不超过 $\epsilon_n\|Z\|_1$。

证明。将 (5.2) 代入整个映射恒等式 (4.1)，用单位酉前后复合的 diamond 等距性即可。张量化 (5.2) 的显式作用得到 (5.6)，未删掉任何初始矩阵块。$\square$

**命题 5.3（完整输入的终端概率与瞬态注入）。** 对任意初始密度，$A$ 先时的零读出概率在所有 $n\ge1$ 都是 $\operatorname{Tr}(E\rho)$，$B$ 先时为 $\operatorname{Tr}(SES\rho)$。时间零的效应分别为 $P,SPS$。

证明。用表中读出消去输出相位，再用 $(C^\dagger)^n(P)=E$，得到两个公式。特别地，$A$ 先时初始 $|d\rangle\langle d|$ 位于 $R^\perp$，却向 $P$ 极限扇区注入 $2/3$ 的权重；$B$ 先时对应输入为 $S|d\rangle\langle d|S$。故不能把全输入效应 $E$ 换成常返支持内的投影 $P$。$\square$

**定理 5.4（每个优化重置的正距离）。** 对任一种交替、每个 $n\ge0$ 与每个密度 $\sigma$，

$$
\|T_n^{A/B}-\mathcal R_\sigma\|_\diamond\ge1.
\tag{5.7}
$$

四个相位极限都与重置集合的最短距离恰为一；有限时刻的最短距离趋于一，并且对 $n\ge2$，

$$
1\le\inf_\sigma\|T_n^{A/B}-\mathcal R_\sigma\|_\diamond\le1+\epsilon_n.
\tag{5.8}
$$

证明。表中两种输入的每个时刻输出 $\omega_0,\omega_1$ 始终正交，迹范数距离为二。故

$$
2\le\|\omega_0-\sigma\|_1+\|\omega_1-\sigma\|_1
\le2\|T_n^{A/B}-\mathcal R_\sigma\|_\diamond.
$$

极限也有同一正交输出对。对 $\rho_t=tP+(1-t)M$，有

$$
(\mathcal T-\mathcal R_{\rho_t})(X)
=(P-M)\operatorname{Tr}((E-tI)X),\qquad
\|\mathcal T-\mathcal R_{\rho_t}\|_\diamond=2\max\{t,1-t\}.
\tag{5.9}
$$

为核对完全范数，映射 $X\mapsto A\operatorname{Tr}(BX)$（$B$ 厄米）的范数是 $\|A\|_1\|B\|_\infty$：放大泛函的伴随为 $Y\mapsto B\otimes Y$，迹范数对偶给出上界，取 $B$ 的最大绝对特征值单位特征向量达到下界。这里 $\|P-M\|_1=2$，$E$ 的谱含零、一，故得到 (5.9)。$t=1/2$ 达到一。单位酉前后复合将重置集合双射到自身，故四个极限的最短距离相同。到固定集合的距离是 1-Lipschitz，结合 (5.5) 得 (5.8)。允许每个时刻重新优化 $\sigma$ 仍不能消除该距离。$\square$

## 6. 经典标签、有限 NPT 与精确量子码是三件事

**命题 6.1（显式相干衰减与 NPT 见证）。** 令

$$
|\Omega\rangle=(|0\rangle_{\rm ref}s+|1\rangle_{\rm ref}w_0)/\sqrt2.
\tag{6.1}
$$

$A$ 先使用此输入，$B$ 先使用 $(I\otimes S)|\Omega\rangle$。两种交替在每个有限 $n\ge0$ 都产生 NPT 输出；其相应非对角矩阵单位的幅度为 $(-1/2)^n$。每个相位极限则为测量后准备通道，因而是纠缠破坏的。

证明。由 (3.2)、(4.5)，$(U_0+U_1)w_0/2=-w_0/2$，而两个置换都固定 $s$。故

$$
C(|s\rangle\langle w_0|)=-\tfrac12|s\rangle\langle w_0|.
$$

对 $C^n$，输出的参考块为

$$
\frac12\begin{pmatrix}
P&c_n|s\rangle\langle w_0|\\
c_n|w_0\rangle\langle s|&D_n
\end{pmatrix},\qquad c_n=(-1/2)^n,\quad
D_n=C^n(|w_0\rangle\langle w_0|).
\tag{6.2}
$$

$D_n$ 支持于 $R\cap s^\perp$。参考部分转置后，压缩到有序对 $(|1\rangle_{\rm ref}s,|0\rangle_{\rm ref}w_0)$ 得到

$$
\begin{pmatrix}0&c_n/2\\c_n/2&0\end{pmatrix},\qquad
\det=-4^{-n}/4<0,
\tag{6.3}
$$

负特征值为 $-2^{-n-1}$。正算子的压缩必正，故全部分转置非正。分离态在参考转置下为正，因而这证明 NPT。对交替，用 (4.1) 把输入相位消去，输出只余一个已知系统酉相位；它保持 NPT。对 $A$ 先，还明确有

$$
T_n^A(|s\rangle\langle w_0|)
=(-1/2)^nS^{n\bmod2}|s\rangle\langle w_0|S^{n\bmod2}.
$$

$B$ 先有相应的输入、输出相位版本。两个标量扇区之间的相干因此衰减；$M$ 扇区内的无迹信息也由 (5.2) 消失。相位极限 (5.6) 的 POVM 为 $\{E,I-E\}$ 或其共轭，准备态为正交密度及其共轭，所以是测量后准备。这里沿用源二定理 20.2 的典范见证，新增的是完整切换恒等式的传递。它不证明精确恢复一个复量子位；后面的三步定理给出独立的否定结论。$\square$

## 7. 可逆前缀的完整支持与不同下一通道

**引理 7.1（有支持的综合征形式及恢复的 CPTP 补全）。** 若通道限制 $F:\mathcal B(\mathcal C)\to M_5$ 有终端 CPTP 左逆，$\dim\mathcal C=k$，则存在 $s\ge1$、$\tau>0$（定义在 $G=\mathbb C^s$ 上、迹为一）及等距嵌入 $W:\mathcal C\otimes G\to H$，使

$$
F(X)=W(X\otimes\tau)W^\dagger,\qquad ks\le5.
\tag{7.1}
$$

所有纯输入的输出秩都为 $s$。对任何实际 Stinespring 补通道，输出恒为 $\operatorname{Tr}X$ 乘一个秩为 $s$ 的密度。对任意 $v\in H$，置 $y=W^\dagger v$，则

$$
F^\dagger(|v\rangle\langle v|)
=\operatorname{Tr}_{G}\!\left[(I\otimes\sqrt\tau)|y\rangle\langle y|(I\otimes\sqrt\tau)\right].
\tag{7.2}
$$

其秩等于 $y$ 的 Schmidt 秩，至多为 $s$，零向量的秩取零。反之 (7.1) 具有全输出空间上的 CPTP 左逆。

证明。设限制的 Kraus 为 $L_i:\mathcal C\to H$，左逆的 Kraus 为 $D_a$。对每个单位 $x\in\mathcal C$，$\sum_{ai}|D_aL_ix\rangle\langle D_aL_ix|=|x\rangle\langle x|$。各正项只能落在 $\mathbb Cx$，所以每个线性算子 $D_aL_i$ 保持每条复直线。对基向量和两两之和应用此性质，得 $D_aL_i=c_{ai}I_{\mathcal C}$，右边视作回到原代码的嵌入。恢复保迹给出 Knill–Laflamme 条件

$$
L_i^\dagger L_j=\alpha_{ij}I_{\mathcal C},\qquad
\alpha_{ij}=\sum_a\overline{c_{ai}}c_{aj},\qquad
\alpha\ge0,\quad\operatorname{Tr}\alpha=1.
\tag{7.3}
$$

酉旋转 Kraus 指标对角化 $\alpha$，舍去零特征值后有 $L_b=\sqrt{p_b}U_b$，$p_b>0$、$\sum_b p_b=1$、$U_b^\dagger U_c=\delta_{bc}I_{\mathcal C}$。令 $W(x\otimes b)=U_bx$、$\tau=\operatorname{diag}(p_b)$，便得 (7.1)。输出秩及支持维数随之成立。在原 Kraus 环境基中补输出是 $\alpha^{\mathsf T}\operatorname{Tr}X$；其他实际环境只把其支持等距嵌入，秩不变。

迹配对给出 (7.2)；它是向量 $(I\otimes\sqrt\tau)y$ 的约化密度。$\sqrt\tau$ 在其支持可逆，故不改变 Schmidt 秩。这个证明不要求 $v$ 已在 $\operatorname{ran}W$。

最后任取支持于 $\mathcal C$ 的固定密度 $\rho_{\mathcal C}$，

$$
\mathcal D(Y)=\operatorname{Tr}_{G}(W^\dagger YW)
+\operatorname{Tr}((I-WW^\dagger)Y)\rho_{\mathcal C}
\tag{7.4}
$$

是 CP 的，两个项的迹分别为 $\operatorname{Tr}(WW^\dagger Y)$ 和其补数，故 TP；且 $\mathcal DF(X)=X$。第一项的输出自然嵌回原代码。这是标准 Knill–Laflamme 的具体有限维形式，对应源二定理 5.1。$\square$

**引理 7.2（每个单步的等距维数上界）。** 任意允许单步的等距限制维数至多三，任意正确码的维数也至多三。若三维代码 $\mathcal C$ 正确，则

$$
\mathcal C=\operatorname{span}\{a,z,d_0\},\qquad
 a\in\mathsf A,\ d_0\in\mathsf D,\quad\|a\|=\|d_0\|=1.
\tag{7.5}
$$

证明。等距限制把秩一输出效应拉回成至多秩一。对 (1.8) 的 $E_0,E_1,E_2$，因 $r>0$，得到 $P_{\mathcal C}P_{\mathsf A}P_{\mathcal C}$、$P_{\mathcal C}P_{\mathsf B}P_{\mathcal C}$、$P_{\mathcal C}P_{\mathsf D}P_{\mathcal C}$ 各至多秩一，且三者之和为 $I_{\mathcal C}$，故维数至多三。若 $k\ge3$ 仅知正确，$ks\le5$ 强制 $s=1$，仍是等距。$k=3$ 时三个投影像的维数各至多一，其正交直和包含三维 $\mathcal C$，所以恰为 $\mathcal C$；中间非零像为 $\mathbb Cz$，得到 (7.5)。结论逐一适用于每个通道，不要求各步相同。$\square$

**引理 7.3（不同下一通道的全范围传递）。** 设同一逻辑量子位 $\mathcal C$ 的连续可逆前缀为

$$
F_t(X)=W_t(X\otimes\tau_t)W_t^\dagger,\qquad
F_{t+1}(X)=W_{t+1}(X\otimes\tau_{t+1})W_{t+1}^\dagger,
$$

并满足 $F_{t+1}=\Phi_{t+1}F_t$；两种 $\tau$ 均在自己的规范空间上严格正。记 $R_t=\operatorname{ran}W_t$。下一通道的每个 Kraus 都把整个 $R_t$ 送入 $R_{t+1}$；在 $W$ 坐标中，其对整个输入代数的限制为

$$
\widetilde\Phi_{t+1}=\operatorname{id}_{M_2}\otimes\Gamma,
\qquad \Gamma(\tau_t)=\tau_{t+1},
\tag{7.6}
$$

$\Gamma$ 是 CPTP。这里没有 $\Phi_t=\Phi_{t+1}$ 的前提。

证明。$F_t(I_{\mathcal C})$ 在 $R_t$ 上严格正，其下一像支持于 $R_{t+1}$。若 $y\perp R_{t+1}$，下一通道 Kraus $K_\mu$ 满足

$$
0=\sum_\mu\|F_t(I_{\mathcal C})^{1/2}K_\mu^\dagger y\|^2.
$$

故每个 $K_\mu R_t\subseteq R_{t+1}$，不是仅对某个选定态的支持关系。坐标算子 $L_\mu=W_{t+1}^\dagger K_\mu W_t$ 因而满足 $\sum_\mu L_\mu^\dagger L_\mu=I_{\mathcal C\otimes G_t}$，并将 $X\otimes\tau_t$ 映成 $X\otimes\tau_{t+1}$。

对角化 $\tau_t=\sum_a p_a|a\rangle\langle a|$，其中每个 $p_a>0$。对每个复逻辑向量 $\ell$，

$$
\sum_{\mu,a}p_a|L_\mu(\ell\otimes a)\rangle\langle L_\mu(\ell\otimes a)|
=|\ell\rangle\langle\ell|\otimes\tau_{t+1}.
$$

每个正项都必须位于 $\mathbb C\ell\otimes G_{t+1}$。因所有权重正且 $a$ 张成输入规范空间，每个 $L_\mu$ 在整个输入空间保持所有逻辑直线。对逻辑基的两条直线，它是两个规范块；再对两基向量之和应用该性质，两个规范块必须相等。因此 $L_\mu=I_{\mathcal C}\otimes B_\mu$。其完备性给出 $\sum_\mu B_\mu^\dagger B_\mu=I$，得到整个代数上的 (7.6)。只保留 $X\otimes\tau_t$ 上的等式不足以代替这一步。$\square$

**引理 7.4（满 Schmidt 秩纯像强迫规范酉性）。** 若引理 7.3 中两个规范空间均为二维，且

$$
(\operatorname{id}\otimes\Gamma)(|\xi\rangle\langle\xi|)=|y\rangle\langle y|,
\tag{7.7}
$$

其中 $\xi,y$ 单位且 $y$ 的 Schmidt 秩为二，则 $\Gamma=\operatorname{Ad}_V$，$V$ 是二维酉矩阵；原下一通道在四维 $R_t$ 上等距。

证明。纯像使每个 $ (I\otimes B_\mu)\xi=c_\mu y$。至少一个 $c_\mu\ne0$。令 $X_\xi,Y_y$ 是两个 ket 的 $2\times2$ 系数矩阵，方程就是

$$
X_\xi B_\mu^{\mathsf T}=c_\mu Y_y.
$$

$Y_y$ 可逆且至少一个系数非零，故 $X_\xi$ 可逆，所有 $B_\mu$ 正比于同一个矩阵；若 $c_\mu=0$，该 $B_\mu$ 必为零。保迹迫使公共矩阵的平方模是正标量乘 $I$，归一化后为方阵酉矩阵 $V$，于是得到结论。这里是 ket 系数的普通转置，不是伴随或部分转置；原通道的等距为 $W_{t+1}(I\otimes V)W_t^\dagger$ 在 $R_t$ 上的限制。$\square$

## 8. 任意预定义序列的三步精确量子位阻碍

**定理 8.1（固定内部参数上的全部切换序列）。** 固定任意 $0<\eta<1$。对于任意预定义允许序列，在每个 $n\ge3$，若要求终端 CPTP 恢复在一个复子空间的整个算子代数上精确恒等，则最大代码维数恰为一。

证明。只须排除三步量子位。设 $\mathcal C$ 是二维代码，$\mathcal R_3T_3(X)=X$ 对全部 $X\in\mathcal B(\mathcal C)$ 成立。每个前缀 $F_t=T_t|_{\mathcal B(\mathcal C)}$ 都可逆，因为 $\mathcal R_3\circ T_{3:t+1}$ 是其 CPTP 左逆；这只是必要性的证明，不在真实序列中插入恢复。由引理 7.1，规范秩 $s_t\in\{1,2\}$。

先由 (1.10) 得 $F_3^\dagger(E_2)$ 在 $\mathcal C$ 上严格正，秩为二。(7.2) 因此迫使 $s_3=2$ 且 $W_3^\dagger z$ 的 Schmidt 秩为二。若 $s_2=2$，则 $\dim R_2=\dim R_3=4$，而

$$
\dim(R_2\cap\mathsf D)\ge4+2-5=1.
$$

取该交中的单位 $x$。第三个实际通道由 (1.8) 把 $|x\rangle\langle x|$ 送到 $|z\rangle\langle z|$，而引理 7.3 的范围包含使 $z\in R_3$。故 $\xi=W_2^\dagger x$、$y=W_3^\dagger z$ 都单位，且满足 (7.7)。引理 7.4 迫使 $\Phi_3$ 在整个四维 $R_2$ 等距，违反引理 7.2。因此 $s_2=1$。

第二前缀现在等距。拉回 $E_0,E_1$ 并用 (1.10)，两个正压缩 $P_{\mathcal C}P_{\mathsf L}P_{\mathcal C}$ 与 $P_{\mathcal C}P_{\mathsf D}P_{\mathcal C}$ 各至多秩一，且和为 $I_{\mathcal C}$。二维正收缩及其补的秩都至多一，迫使其特征值为 $1,0$。其特征值一的单位向量 $x$ 满足 $\|P_{\mathsf L}x\|=1$，故 $x\in\mathsf L$；另一个单位向量 $y\in\mathsf D$。因而

$$
\mathcal C=\operatorname{span}\{x,y\},\qquad x\in\mathsf L,\quad y\in\mathsf D,\quad x\perp y.
\tag{8.1}
$$

第一通道将 $|y\rangle\langle y|$ 重置为纯态 $E_2$；可逆第一前缀的所有纯像秩相同，故 $s_1=1$。唯一可能的模式是

$$
(s_1,s_2,s_3)=(1,1,2).
\tag{8.2}
$$

第二前缀等距地将 $x,y$ 送到正交纯向量 $h',w'$。共同的人口律 (1.9) 给出其支持和绝对坐标，分别为

$$
(r,0,\sqrt\eta,\sqrt{r\eta},0),\qquad
(0,\sqrt r,0,0,\sqrt\eta).
$$

两个支持不相交，合起来覆盖五个坐标。取一个对角酉 $D_{\rm ph}$，同时使这五个非零坐标为正。对所有步骤统一定义

$$
\Psi_t=\operatorname{Ad}_{D_{\rm ph}}\circ\Phi_t\circ
\operatorname{Ad}_{D_{\rm ph}^\dagger}.
\tag{8.3}
$$

单位酉前后复合保持 CP 与 TP；对每个复 $X$，$\operatorname{diag}(D_{\rm ph}^\dagger XD_{\rm ph})=\operatorname{diag}X$ 且输出共轭也保持对角，将它们代入 (1.2) 即证每个 $\Psi_t$ 仍允许。每个前缀都严格望远镜消去为

$$
\Psi_t\circ\cdots\circ\Psi_1
=\operatorname{Ad}_{D_{\rm ph}}\circ T_t\circ
\operatorname{Ad}_{D_{\rm ph}^\dagger}.
\tag{8.4}
$$

这是全序列共用的一次坐标变换，不是每步免费实施相位纠正。代码与恢复也共同共轭。第二像为固定平面

$$
\mathsf T=\operatorname{span}\{h,w\},\qquad
h=r e_0+\sqrt\eta\,e_2+\sqrt{r\eta}\,e_3,\qquad
w=\sqrt r\,e_1+\sqrt\eta\,e_4.
\tag{8.5}
$$

两向量正交，平方范数分别为 $r^2+\eta+r\eta=1$ 与 $r+\eta=1$。

为证明真正的终端代码传递，记共轭后代码为 $\mathcal C'$，第二前缀等距为 $U_2:\mathcal C'\to\mathsf T$，三步恢复为 $\mathcal R'_3$。在整个 $H$ 上定义

$$
\mathcal J_2(Y)=U_2P_{\mathcal C'}YP_{\mathcal C'}U_2^\dagger
+\operatorname{Tr}((I-P_{\mathcal C'})Y)|h\rangle\langle h|.
\tag{8.6}
$$

两项均 CP，迹和为 $\operatorname{Tr}Y$，故 $\mathcal J_2$ 是 CPTP。对每个复 $Y\in\mathcal B(\mathsf T)$，以 $X=U_2^\dagger YU_2$ 代入三步恢复等式，便得

$$
(\mathcal J_2\circ\mathcal R'_3)\Psi_3(Y)=Y.
\tag{8.7}
$$

所以一个与前两步不同的允许最终通道也必须能纠正整个 $\mathsf T$。以下引理排除它，完成三步的反证。大于二维的代码包含量子位子码；若 $n>3$ 时有恢复，把它与实际后缀 $T_{n:4}$ 复合就会恢复三步前缀。故所有 $n\ge3$ 都至多一维。一维代码总能用终端重置恢复，最大维数于是恰为一。$\square$

**引理 8.2（最终通道的完整复强迫平面矛盾）。** 对每个内部参数，(8.5) 的平面 $\mathsf T$ 不能被任何允许单步通道精确纠正，不限制其实际 Gram 的复相位、秩或环境维数。

证明。使用源二定理 4.1 的必要且充分单通道参数化。在同一个实际复环境内，有八个单位向量，满足 $\alpha_0\perp\alpha_1$、$\beta_0\perp\beta_1$、$\delta_0\perp\delta_1$，并且

$$
\begin{aligned}
Ve_i&=\sqrt r\,e_0\otimes\alpha_i+\sqrt\eta\,e_3\otimes\beta_i\quad(i=0,1),\\
Ve_2&=\sqrt r\,e_1\otimes\gamma_0+\sqrt\eta\,e_4\otimes\gamma_1,\\
Ve_3&=z\otimes\delta_0,\qquad Ve_4=z\otimes\delta_1.
\end{aligned}
\tag{8.8}
$$

这里没有跨步骤的共同环境假设，只有这个最终通道自身的共同环境。为说明使用的接口，任一允许通道的 dilation 写成 $Ve_i=\sum_j e_j\otimes e_{ji}$，(1.2) 在全部矩阵单位上的系数恰要求 $\langle e_{ji'},e_{ji}\rangle=\delta_{ii'}Q_{ij}$。零边消失，非零边除以正权重即为 (8.8) 及上述三个正交对；反之这些约束使 $V$ 等距并满足全输入律。其余重叠只受一个共同 PSD Gram 约束，特别不假设两个 $\gamma$ 正交。

设 $\widehat\Phi(X)=\operatorname{Tr}_H(VXV^\dagger)$。可纠正性由 (7.3) 迫使

$$
\widehat\Phi(|h\rangle\langle h|)=\widehat\Phi(|w\rangle\langle w|)=\omega,
\qquad
\widehat\Phi(|h\rangle\langle w|)=\widehat\Phi(|w\rangle\langle h|)=0,
\tag{8.9}
$$

其中 $\omega$ 是秩 $s\le2$ 的密度，因为 $2s\le5$。迹掉系统坐标，在两个对角输入上得到

$$
\begin{aligned}
\omega={}&r^3|\alpha_0\rangle\langle\alpha_0|
+r^2\eta|\beta_0\rangle\langle\beta_0|
+r\eta|\delta_0\rangle\langle\delta_0|\\
&+r\eta|\gamma_0\rangle\langle\gamma_0|
+\eta^2|\gamma_1\rangle\langle\gamma_1|,\\
\omega={}&r^2|\alpha_1\rangle\langle\alpha_1|
+r\eta|\beta_1\rangle\langle\beta_1|
+\eta|\delta_1\rangle\langle\delta_1|.
\end{aligned}
\tag{8.10}
$$

第一式的五个向量在 $Vh$ 的不同系统坐标 $0,3,2,1,4$ 上，第二式的三个在 $Vw$ 的 $0,3,2$ 上，故没有省略干涉项。所有系数严格正。正秩一和的像等于其向量的张成空间，这是因为其核是所有向量正交补的交。因此八个向量全在 $E_*:=\operatorname{ran}\omega$ 内。正交的 $\alpha$ 对已使其维数至少二，故 $\dim E_*=2$。三组 $\alpha,\beta,\delta$ 对于是都是同一个 $E_*$ 的有序正交基。

在 $E_*$ 上置

$$
\begin{aligned}
S_0&=r^2|\alpha_0\rangle\langle\alpha_0|
+r\eta|\beta_0\rangle\langle\beta_0|+\eta|\delta_0\rangle\langle\delta_0|,\\
S_1&=r^2|\alpha_1\rangle\langle\alpha_1|
+r\eta|\beta_1\rangle\langle\beta_1|+\eta|\delta_1\rangle\langle\delta_1|,\\
\rho_g&=r|\gamma_0\rangle\langle\gamma_0|+\eta|\gamma_1\rangle\langle\gamma_1|.
\end{aligned}
\tag{8.11}
$$

三组正交基分解与 $r^2+r\eta+\eta=1$ 给出 $S_0+S_1=I$，(8.10) 则给出 $rS_0+\eta\rho_g=S_1$。因此

$$
S_0=\frac{I-\eta\rho_g}{1+r},\qquad
S_1=\frac{rI+\eta\rho_g}{1+r},\qquad
S_0,S_1\ge\frac r{1+r}I>0,
\tag{8.12}
$$

最后的不等式只用了 $\rho_g$ 是密度，故 $0\le\rho_g\le I$。

另一个必需条件是全部复交叉算子为零。其确切式子为

$$
\widehat\Phi(|h\rangle\langle w|)
=\sqrt r\left(r^2|\alpha_0\rangle\langle\alpha_1|
+r\eta|\beta_0\rangle\langle\beta_1|
+\eta|\delta_0\rangle\langle\delta_1|\right)=0,
\tag{8.13}
$$

另一个有序交叉输入的输出为此式的伴随，亦为零。例如三个系数分别来自系统坐标零、三、二的 ket 幅度乘以另一 ket 幅度的共轭，即 $r^{5/2},r^{3/2}\eta,\sqrt r\eta$。这里保留复 bra 的共轭；仅有实部或迹为零无法代替 (8.13)。

令 $U_\alpha,U_\beta,U_\delta:\mathbb C^2\to E_*$ 送标准有序基到三组实际有序正交基，构造只用于证明的辅助通道

$$
\mathcal M(Y)=r^2U_\alpha YU_\alpha^\dagger
+r\eta U_\beta YU_\beta^\dagger+\eta U_\delta YU_\delta^\dagger.
\tag{8.14}
$$

它只有三个 Kraus 算子 $rU_\alpha,\sqrt{r\eta}U_\beta,\sqrt\eta U_\delta$，其 Choi 矩阵为三个向量化 Kraus 外积之和，秩至多三。然而 (8.11)、(8.13) 已规定全部四个复矩阵单位的像：

$$
\mathcal M(E_{00})=S_0,\quad \mathcal M(E_{11})=S_1,\quad
\mathcal M(E_{01})=\mathcal M(E_{10})=0.
$$

于是输入在前的未归一化 Choi 矩阵为

$$
J^{\rm in}_{\mathcal M}=\begin{pmatrix}S_0&0\\0&S_1\end{pmatrix},
\tag{8.15}
$$

由 (8.12) 秩恰为四，矛盾。输出在前的版本是 $\mathsf{Swap}J^{\rm in}_{\mathcal M}\mathsf{Swap}^\dagger$，只同时置换行列而保持秩；不是部分转置。该辅助通道没有引入任何可执行恢复或保留系统。本引理复用了源二定理 9.1 的强迫平面代数；定理 8.1 新增的是对不同通道逐一证明的前缀、全范围、共享相位与终端代码接口。$\square$

## 9. 切换类的尖锐精确码维数与合法见证

**定理 9.1（类最优序列）。** 在每个固定内部参数，令 $k_n$ 是某个预定义序列在时间 $n$ 的最大终端正确子空间维数，令 $K_n^{\rm sw}(\eta)$ 是对所有这种序列的最大值。则

$$
(K_0^{\rm sw},K_1^{\rm sw},K_2^{\rm sw},K_3^{\rm sw},\ldots)
=(5,3,2,1,1,\ldots).
\tag{9.1}
$$

证明。时间零为五，一步上界为引理 7.2，三步及以后为定理 8.1。若三维代码能经过两个不同通道而正确，两种前缀由 $3s\le5$ 都必须等距。第一代码由 (7.5) 为 $\operatorname{span}\{a,z,d_0\}$。其三个正交纯输出 $f_A,f_B,f_D$ 的支持依次是 $\operatorname{span}\{e_0,e_3\}$、$\operatorname{span}\{e_1,e_4\}$、$\mathbb Cz$；前两个的非零绝对幅度都是 $\sqrt r,\sqrt\eta$。第一像 $\mathcal C_1$ 的 $\mathsf A$ 投影因此同时包含非零的 $e_0,e_1$ 方向，秩至少二。第二通道在整个 $\mathcal C_1$ 上必等距（由两个前缀等距的复合等式），违反引理 7.2 证明中的 $\mathsf A$ 投影秩至多一。故二步上界为二。

下界采用源二定义 10.1 的 oldest-bit 通道，不要求任何途中操作。记

$$
u_\eta=\sqrt r\,e_0+\sqrt\eta\,e_3,\qquad
v_\eta=\sqrt r\,e_1+\sqrt\eta\,e_4,
$$

并在每步重复以下两个完整 Kraus 算子定义的通道：

$$
L_0=|u_\eta\rangle\langle e_0|+|v_\eta\rangle\langle e_2|+|z\rangle\langle e_3|,
\qquad L_1=|u_\eta\rangle\langle e_1|+|z\rangle\langle e_4|.
\tag{9.2}
$$

其平方和是 $I$；按 (2.5) 的环境向量顺序，列表为 $(f_0,f_1,f_0,f_1,f_0,f_0,f_0,f_1)$，使用参数 $\sqrt r,\sqrt\eta$ 的边权重。这是一个实际共同 PSD Gram，满足全部规定正交性，因此具有每个复输入的 (1.2)。三维代码 $\operatorname{span}\{e_0,e_2,e_3\}$ 被 $L_1$ 消去，被 $L_0$ 等距送到 $\operatorname{span}\{u_\eta,v_\eta,z\}$；其终端恢复是逆等距加补空间重置，见 (7.4)。

二步代码为 $\mathcal C_2=\operatorname{span}\{e_0,e_3\}$，完整两步词为

$$
\begin{aligned}
L_0L_0&=|h\rangle\langle e_0|+|w\rangle\langle e_3|,\\
L_0L_1&=|h\rangle\langle e_1|+|w\rangle\langle e_4|,\\
L_1L_0&=|h\rangle\langle e_2|,\qquad L_1L_1=0,
\end{aligned}
\tag{9.3}
$$

其中 $h,w$ 为 (8.5)。后三个词消去 $\mathcal C_2$，第一个限制为等距 $U_2:\mathcal C_2\to\mathsf T$。合法的完整终端解码是

$$
\mathcal R_2(Y)=U_2^\dagger YU_2+
\operatorname{Tr}((I-P_{\mathsf T})Y)E_0.
\tag{9.4}
$$

Kraus 可取 $U_2^\dagger$ 及 $|e_0\rangle\langle e_j|(I-P_{\mathsf T})$，$j=0,\ldots,4$，其平方和为 $P_{\mathsf T}+(I-P_{\mathsf T})^2=I$，并恢复全部复代码矩阵单位。三维和二维见证分别支付一次、两次实际通道应用及一次终端恢复，使用新鲜二维环境，未把证明中的左逆插入中途。同一固定通道已达到全部类上界，故也是允许切换类的下界。$\square$

**推论 9.2（交替例子的精确码序列）。** 对第 4 节的两个实际交替序列，个体代码序列也都为 $(5,3,2,1,1,\ldots)$。

证明。为给出半参数 $C$ 的具体下界，旋转其 Kraus 指标，令 $J=(K_0+K_1)/\sqrt2$、$D=(K_0-K_1)/\sqrt2$。在

$$
H_+=\operatorname{span}\{q(e_0+e_1),z,q(e_3+e_4)\}
$$

上，$D$ 为零，$J$ 将显示的正交基等距送到 $(u,v,z)$。$A$ 加一个输出酉、$B$ 加一个输入酉，均保留三维下界。在 $R$ 内令 $a=(u-v)/\sqrt2$，$P_a=|a\rangle\langle a|$。实际限制的旋转 Kraus 满足

$$
(U_0-U_1)/2=U_0P_a,\qquad
(U_0+U_1)/2=U_0(I_R-P_a).
$$

故 $a^\perp\cap R$ 是 $C$ 的一步等距平面。将其用 $J|_{H_+}$ 拉回，得到 $C^2$ 的二步等距代码，终端逆等距用 (7.4) 补全。$A$ 先的两步映射就是 $C^2$；$B$ 先的映射为 $\mathcal U C^2\mathcal U$，将代码及恢复相应共轭即可。类上界给出等号。三步后精确量子位消失，与永久经典标签和每个有限时刻的 NPT 同时成立。$\square$

## 10. 秩一重人口帽的完整混态几何

**引理 10.1（保持人口的纯态分解）。** 对任意有限维密度 $\rho$ 和秩一投影 $P_j=|j\rangle\langle j|$，存在有限纯态凸分解，其中每一项的 $P_j$ 人口恰为 $\operatorname{Tr}(P_j\rho)$。

证明。按 $\rho$ 的秩 $s$ 归纳。秩一显然。若 $s\ge2$，其支持上厄米矩阵的实维数是 $s^2>2$，故存在非零支持内厄米 $H$ 同时满足 $\operatorname{Tr}H=\operatorname{Tr}(P_jH)=0$。$\rho$ 在该支持上严格正，所以 $\rho+tH\ge0$ 的实参数区间包含零的邻域。非零无迹厄米矩阵兼有正、负特征值，沿其特征向量的二次型将区间两端界为有限的 $t_-<0<t_+$。端点处秩必下降，否则支持内严格正性可将区间延长。两个端点仍是密度，且保持所需人口，而

$$
\rho=\frac{t_+}{t_+-t_-}(\rho+t_-H)
+\frac{-t_-}{t_+-t_-}(\rho+t_+H).
\tag{10.1}
$$

对两端归纳即可；每条分支秩都下降，故分解有限。任意谱分解不自动具有这个性质。本引理为源二引理 27.2 的通用成分。$\square$

**定理 10.2（重人口帽直径与阈值反例）。** 维数至少二时，令

$$
\mathcal C_a=\{\rho\ge0:\operatorname{Tr}\rho=1,\ \operatorname{Tr}(P_j\rho)\ge a\}.
$$

若 $1/2<a\le1$，其不减半迹范数直径恰为 $4\sqrt{a(1-a)}$。若 $0\le a\le1/2$，直径为二。高于一维的投影即使人口要求为一，也可具有直径二。

证明。对两个纯项，调全局相位使 $j$ 坐标非负，写 $u=\sqrt p\,j+u_\perp$、$v=\sqrt q\,j+v_\perp$，其中 $p,q\ge a>1/2$。反三角不等式及 Cauchy–Schwarz 给出

$$
|\langle u,v\rangle|\ge\sqrt{pq}-\sqrt{(1-p)(1-q)}\ge2a-1.
$$

$P_u-P_v$ 无迹且秩至多二，平方 Hilbert–Schmidt 范数为 $2(1-|\langle u,v\rangle|^2)$，故其非零特征值为 $\pm\sqrt{1-|\langle u,v\rangle|^2}$。因此

$$
\|P_u-P_v\|_1=2\sqrt{1-|\langle u,v\rangle|^2}\le4\sqrt{a(1-a)}.
\tag{10.2}
$$

对帽中的两个混态用引理 10.1 分解，所有纯项仍在帽中；以两个凸分解权重的乘积配对，三角不等式将 (10.2) 推到全部混态。取单位 $k\perp j$，两个向量 $\sqrt a\,j\pm\sqrt{1-a}\,k$ 达到等号。$a=1$ 时帽仅含 $P_j$。

若 $a\le1/2$，$(j+k)/\sqrt2$ 与 $(j-k)/\sqrt2$ 是帽内正交向量，距离二已是所有密度的最大值。高秩投影的范围中直接取两个正交向量即可。还可给出阈值处收缩结论失效的实际通道：对量子位在 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$ 基中去相干，总有 $|0\rangle$ 人口 $1/2$，却固定两个正交纯态。若投影 $P$ 秩至少二，取其范围中的 $e_1,e_2$，通道

$$
X\longmapsto PXP+\operatorname{Tr}((I-P)X)|e_1\rangle\langle e_1|
\tag{10.3}
$$

的 Kraus 为 $P$ 与 $|e_1\rangle\langle f_a|$（$f_a$ 是补空间的正交基），平方和为 $I$。它始终具有 $P$ 人口一，仍固定 $e_1,e_2$ 的两个纯态。这些是一般人口判据的边界反例，不是五窗口切换类的完整分类。$\square$

## 11. 小参数上对实际切换块的一致完全遗忘

**定理 11.1（充分区间上的统一切换收缩）。** 设

$$
0<\eta<\alpha:=\frac{5-\sqrt{17}}4,\qquad
p_0=\frac{r^2}{1+\eta},\qquad \delta=1-\frac1{2p_0}.
$$

取任意整数 $k\ge1$ 满足 $\eta^{2k}<\delta$，例如取严格的选择

$$
k=\left\lfloor\frac{\log\delta}{2\log\eta}\right\rfloor+1,
\quad N=2k+1,\quad a=p_0(1-\eta^{2k})>1/2,
\quad \kappa=2\sqrt{a(1-a)}<1.
\tag{11.1}
$$

对该参数的每个预定义允许序列、每个种子密度 $\rho_{\rm seed}$，令 $\sigma_n=T_n(\rho_{\rm seed})$。则对任意有限参考、任意复 $Z\in\mathcal B(H\otimes\mathcal K)$ 及 $n\ge0$，

$$
\begin{aligned}
\|(T_n\otimes\operatorname{id})(Z)-\sigma_n\otimes\operatorname{Tr}_H Z\|_1
&\le\min\{2,10\kappa^{\lfloor n/N\rfloor}\}\,\|Z\|_1,\\
\|T_n-\mathcal R_{\sigma_n}\|_\diamond
&\le\min\{2,10\kappa^{\lfloor n/N\rfloor}\}.
\end{aligned}
\tag{11.2}
$$

常数在选择通道序列及输入之前已由 $\eta,k$ 决定；允许 $\sigma_n$ 随时间变化。

证明。先确定共同的人口块。沿用 (1.9) 的两行，有

$$
a_QQ=ra_Q+\eta b_Q,\qquad b_QQ=a_Q,\qquad
p^{\mathsf T}=\frac{a_Q+\eta b_Q}{1+\eta}.
$$

于是 $p^{\mathsf T}Q=p^{\mathsf T}$；记 $\Pi=\mathbf1p^{\mathsf T}$，得到

$$
(Q^2-\Pi)Q=-\eta(Q^2-\Pi),\qquad
Q^n=\Pi+(-\eta)^{n-2}(Q^2-\Pi)\quad(n\ge2).
\tag{11.3}
$$

前式分别在 $Q^2$ 的两种行上由上一行恒等式得到，后式从 $n=2$ 逐次右乘 $Q$ 归纳。这是源二定理 29.1 的相同矩阵、参数及行约定。由 $Q^2$ 的第零列 $r^2,r^2,r^2,0,0$，对 $N=2k+1$ 得

$$
(Q^N)_{i0}=\begin{cases}
p_0(1-\eta^{2k}),&i=0,1,2,\\
p_0(1+\eta^{2k-1}),&i=3,4,
\end{cases}
\qquad\min_i(Q^N)_{i0}=a.
\tag{11.4}
$$

而 $p_0>1/2$ 等价于 $2\eta^2-5\eta+1>0$，在内部参数中恰给 $\eta<\alpha$；另一个根大于一。于是 $0<\delta<1$。因 $\log\eta<0$，条件 $\eta^{2k}<\delta$ 等价于 $k>\log\delta/(2\log\eta)$，(11.1) 即使在该比值为整数时也严格有效。因此 $1/2<a<p_0<1$。

现在取序列中任意一个实际连续 $N$ 步块 $\Gamma$。引理 1.4 给出它的人口矩阵确实是 $Q^N$，即使这 $N$ 个通道全部不同。每个密度的输出于是都有

$$
\operatorname{Tr}(E_0\Gamma(\rho))
=\sum_i(Q^N)_{i0}\rho_{ii}\ge a.
\tag{11.5}
$$

对任意非零无迹厄米 $Y$，归一化其 Jordan 部分写成

$$
Y=t(\rho_+-\rho_-),\qquad t=\|Y\|_1/2.
$$

两个实际输出在定理 10.2 的秩一帽中，故

$$
\|\Gamma(Y)\|_1\le4t\sqrt{a(1-a)}=\kappa\|Y\|_1.
\tag{11.6}
$$

这里由 Jordan 归一化获得相对于输入范数的 Lipschitz 收缩；单有输出绝对直径不够。把实际 $T_n$ 按时间顺序拆成 $\lfloor n/N\rfloor$ 个完整块及不足 $N$ 步的余块。正保迹映射对厄米矩阵收缩迹范数：将其正负部分分别送出后用三角不等式及保迹即可。各块仍保持无迹性，因此逐块得到

$$
\|T_n(Y)\|_1\le c_n\|Y\|_1\quad(Y=Y^\dagger,\ \operatorname{Tr}Y=0),
\qquad c_n=\kappa^{\lfloor n/N\rfloor}.
\tag{11.7}
$$

最后证明完整复参考估计，而不从状态收缩直接猜测。置

$$
L_n=T_n-\mathcal R_{\sigma_n}
=T_n\circ(\operatorname{id}-\mathcal R_{\rho_{\rm seed}}).
$$

对对角单位 $E_{ii}$，$L_n(E_{ii})=T_n(E_{ii}-\rho_{\rm seed})$，括号是无迹厄米且范数至多二，故范数至多 $2c_n$。对 $i\ne j$，

$$
E_{ij}=(E_{ij}+E_{ji})/2+i(E_{ij}-E_{ji})/(2i).
$$

两个厄米项均无迹且范数一，重置都消去它们，(11.7) 仍给 $\|L_n(E_{ij})\|_1\le2c_n$。引理 1.3 的任意复矩阵 SVD 分块证明于是给出 $\|(L_n\otimes\operatorname{id})(Z)\|_1\le10c_n\|Z\|_1$，不含参考维数因子。$T_n$ 与 $\mathcal R_{\sigma_n}$ 又都为 CPTP，故独立有 diamond 差范数至多二，取最小即得 (11.2)。重置的放大恰为 $\sigma_n\otimes\operatorname{Tr}_H Z$，而 TP 使该参考边缘保持原值。

这个证明逐个控制实际混合词块；没有相乘各通道的谱隙，也没有把源二定理 37.1 的同一通道幂的紧致界拿来控制不同通道的词。$\square$

**推论 11.2（周期序列的唯一吸引密度轨道）。** 在定理 11.1 的充分区间，任意预定义周期 $\ell$ 的序列有唯一的周期密度轨道 $\sigma_0,\ldots,\sigma_\ell=\sigma_0$，满足 $\sigma_j=\Phi_j(\sigma_{j-1})$。对所有输入及有限参考，(11.2) 可取 $\sigma_n=\sigma_{n\bmod\ell}$。周期轨道允许基本周期严格小于 $\ell$，各相位的对角都为 (1.4) 的人口列 $p$。

证明。周期乘积 $F=\Phi_\ell\cdots\Phi_1$ 是 CPTP。对任一种子，Cesàro 平均 $m^{-1}\sum_{a=0}^{m-1}F^a(\rho)$ 在紧致密度空间中有收敛子列，其在 $F$ 下的差范数至多 $2/m$，极限 $\sigma_0$ 因而是固定密度。若有两个这样的密度，其无迹差被 $F^m=T_{m\ell}$ 保持，同时由 (11.7) 收缩至零，所以两者相同。定义 $\sigma_j=T_j(\sigma_0)$ 即得闭合轨道，任何另一个周期轨道在相位零也给出 $F$ 固定密度，故唯一。取定理 11.1 的种子为 $\sigma_0$，周期性给出所有相位的完整吸引估计。由 (11.3) 可知 $Q^{\ell m}\to\Pi$，故 $Q^\ell$ 的唯一固定概率是 $p$，这使 $\operatorname{diag}\sigma_0=p$，其余相位亦然。这没有在保留数据系统内增加时钟或历史寄存器。$\square$

**命题 11.3（充分判据的确切边界）。** 该区间与 (11.1) 是充分条件，未断言尖锐。对 $\eta\ge\alpha$ 的内部参数，任何时刻都不能使 $\min_i(Q^n)_{i0}>1/2$；这不否定别的切换遗忘机制。

证明。平稳加权平均给出

$$
\min_i(Q^n)_{i0}\le\sum_i p_i(Q^n)_{i0}=p_0\le1/2.
$$

等号参数处，每个有限 $k$ 的 (11.4) 最小值还严格小于 $1/2$。帽判据在阈值处与高秩观察下的失效已有定理 10.2 的反例。第 4 节的反例参数 $1/2$ 在本充分区间外，其永久标签与本节无矛盾。$\square$

## 12. 控制权与数学操作成本

**约定 12.1（逐项计费）。** 第 4 节构造改变了固定通道模型的控制合同：允许从两个预先固定更新中按公开的二周期选择，输入相关的数据仍只留在一个五维系统。所需资源为：

| 项目 | 本卷实际使用的数学资源 |
| --- | --- |
| 保留数据系统 | 一个 $\mathbb C^5$；没有并行副本、第二份输入相关数据或中途综合征寄存器。 |
| 固定更新 | 两个固定 CPTP 通道 $A,B$，各两个完整 Kraus 算子；各自的实际 Gram、Choi 秩与最小环境维数均为二。 |
| 新鲜环境 | 每次通道应用使用一个新的二维最小环境并丢弃；$n$ 步使用 $n$ 次这种新鲜环境交互，不累计保留它们。一般允许类的最小单步环境维数在二至八之间。 |
| 实际更新次数 | 时间 $n$ 就是 $n$ 次完整通道应用；一个二周期支付两次应用，有四个显示的两步 Kraus 词。Kraus 分支不是可供访问的测量结果。 |
| 公开相位控制 | 两种调度相位，即一个二值公开相位；起始相位、终端奇偶及相位选择权均独立于标签，并作为额外控制给出，不计入保留数据系统。 |
| 相位算子 | 若按 (2.3) 分解，每个 $A$ 支付一次 $C$ 后的 $S$，每个 $B$ 支付一次 $C$ 前的 $S$；这些是完整更新的一部分。相邻因子消去是映射恒等式，不授权免费中途纠错。 |
| 终端经典读出 | 一次两结果投影 POVM，从 $\{P,I-P\}$、$\{SPS,I-SPS\}$ 中按公开相位选取。若统一使用前一个读出，可额外支付至多一次终端 $S$。 |
| 终端量子恢复 | 仅在有限正确码陈述中使用一次合法 CPTP 恢复；其逆等距与补空间重置已明确给出，不作为维持经典标签的中途步骤。 |
| 外部参考 | 只在完全范数或 NPT 命题中作为不受作用的数学检验系统，不给操作方增加保留记忆。 |

上述操作计数不换算为本征完整窗口次数、硬件门数、物理时间、实验运行、全部工作量或总存储成本，也不构成容量或实现效率结论。公开控制的二值相位不承载所编码的标签；撤去相位知识是不同的读出合同，本卷没有替它证明同一读出结论。

## 13. 结果归属与未解决边界

**约定 13.1（精确复用与新增桥梁）。** 本卷对给定来源的使用与新增内容对应如下。这里的“新增”只指这份后继卷所处理的切换推导，不表示经过全球文献查新的原创结论。

| 给定来源或标准框架 | 精确对应与归属 |
| --- | --- |
| 源一：半参数卷定义 2.1–2.3、定理 5.1 | 允许半参数全复输入模型、实际八向量顺序、反向 Gram 的 Choi 约定，以及完整四相位对角共轭轨道。第 2 节保留其顺序；命题 3.2 以全部 Gram 轨道条件核对实际构造。 |
| 源一：推论 6.1、7.1 | 典范完整效应、极限及有限记忆事实在分类轨道上的传递。这里 $A,B$ 在轨道外，其个体混合由第 3 节直接证明，未借同秩推断。 |
| 源二：定义 2.2、定理 4.1–4.2 | 固定参数允许类、一个通道自身的共同复环境及重置扇区。引理 1.4 对不同通道及每个连续子序列重证全输入组成关系。 |
| 源二：定理 5.1、6.1–6.2、7.1、8.1、9.1–9.2 | 原有综合征、单步维数、固定通道全范围及强迫平面材料。第 7 节和定理 8.1 逐项证明不同下一通道的全范围传递、满秩规范纯像后果、模式 $(1,1,2)$、同一个相位共轭对全部前缀的望远镜消去，以及完整终端解码补全。强迫平面本身的复共同环境矛盾在引理 8.2 复述；不是用“幂改成乘积”的记号替换冒充新接口。 |
| 源二：定义 10.1、定理 10.2 | oldest-bit 固定通道与合法终端下界码；第 9 节在允许切换类中复用它们达到尖锐类最优值，并证明不同二步通道的上界。 |
| 源二：定义 17.2、定理 17.3、18.1、18.3、19.1–19.2、20.1–20.2、21.2 | $C=\Phi_\circ$ 的典范完整 Kraus、$P,M,E$、包括瞬态的多项式和完全收敛率、重置距离、有限 NPT、支持内代码。第 5 节给出精确参数、基、Kraus 及 Choi 对应；第 4–6 节新增实际交替词、两种起始相位与四个相位极限的全输入传递。 |
| 源二：引理 27.2、定理 27.3、28.1–28.2、29.1、30.1 | 秩一帽几何、保持人口的混态分解、无迹收缩、复参考放大、人口幂及充分阈值。第 10–11 节给出这些成分的完整有限维证明，并将每个实际切换块的人口 $Q^N$ 接入，得到随时间变化的重置轨道和周期吸引结论。 |
| 源二：定理 36.1、37.1 及源一的半参数分类 | 都是固定通道结果；不提供任意混合词的一般谱半径或乘积收缩界。这里没有把其同质紧致界用于混合词。 |
| 标准 Stinespring、Choi、Knill–Laflamme、测量后准备框架 | 归于给定两卷列出的标准来源。共同环境 dilation、Choi 正性与 Kraus 秩、标量压缩及纠缠破坏的有限维用法在正文展开。Hilbert–Schmidt 等号、厄米 Jordan 分解、谱/Jordan 收敛与 SVD 分块是普通有限维线性代数。 |

**约定 13.2（结论的量词与未解问题）。** 两个个体混合却能交替保留经典标签的显式例子只在 $\eta=1/2$ 给出；完整输入的映射和读出恒等式包括时间零；完全范数收敛率按 (5.5) 适用于 $n\ge2$。三步精确复量子位阻碍则对每一个固定内部参数及每一个预定义输入无关序列成立，不要求周期，也不要求各步等同。小参数的统一完全遗忘只在第 11 节给出的充分区间证明；非周期序列跟随 $T_n(\rho_{\rm seed})$，周期序列有唯一吸引周期密度轨道。

尚未解决的是内部参数上任意或周期切换能否保留经典标签的尖锐分类、其他相位选择的完整分类、充分区间之外的普遍混合词界，以及最佳切换收敛率和常数。单个通道都混合不推出其交替混合，第 4 节就是反例；相同五人口也不决定标签、纠缠或代码，$P,M$ 的相同人口与正交支持给出具体区别。全参数精确量子位命题不在这些未解边界之列。

变参数 $\eta_t$、反馈、环境或结果访问、中途主动恢复、保留输入相关历史、更大保留系统以及端点参数均不在三步定理的合同内。有限 NPT 不推出精确量子位或正的渐近量子容量；经典零误差标签也不推出非交换矩阵代数的可逆保留。相位极限为纠缠破坏与每个有限乘积非纠缠破坏可以并存。源二的经典活动对应只提供选定源的概率接口；不提供从同一局部边缘到任意实际源、从源到 CPTP、从时间指标到本征窗口操作、Hamiltonian、物理场论或实验机器学习的桥梁。全输入数学结果、文献标识与控制计数均不构成上述经验、物理、总资源、形式内核或全球新颖性认证。

[HG]: AURIC_FIB_FIVE_WINDOW_HALF_GRAM_CLASSIFICATION.md
[QM]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md

## 追加锚（本行以下为增补区）
