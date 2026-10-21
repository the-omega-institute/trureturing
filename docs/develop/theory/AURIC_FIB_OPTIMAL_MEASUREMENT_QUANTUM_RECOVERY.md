# AURIC FIB：共同保真等号测量与保留量子输出的精确恢复

## 1. 对象、实际输出与恢复目标

本文讨论有限维复量子系统中的一个精确问题：测量在一组态的每一对上都达到根保真度等号时，保留下来的量子输出连同实际测量记录，是否足以由同一个信道恢复这些态？对于正定有限态族，答案恰由原态是否两两对易决定。证明先从实际 Kraus 算子推出条件量子输出的族内因子化，再以联合正传输块上的有限随机矩阵证明必要性。量子输出并未被预先删除。

全文是可错的、未经执行的普通条件符号数学，不是形式核认证或实验结果。源卷记为 S，经典恢复伴卷记为 C；其固定内容身份与文献归属列于 §11。标准纠错、Choi 参数化与乘法域方法按既有工具使用，本文不主张它们的发明权或文献优先权。原来的普适近似资源桥梁仍为 OPEN，见 §10。

**定义 1.1（共同根保真缺陷）。** 记输入空间为 $A=\mathbb C^d$，$M(A)$ 为其完整复算子代数。密度矩阵半正定、迹为一；忠实指正定。信道指复线性、完全正、保迹映射（CPTP）。本文主定理固定 $d\ge2,r\ge3$ 和忠实态 $\rho_0,\ldots,\rho_{r-1}$。记 $[U,V]=UV-VU$，$\|U\|_F^2=\operatorname{Tr}(U^\dagger U)$，另用迹范数 $\|\cdot\|_1$ 与算子范数 $\|\cdot\|_{\mathrm{op}}$。令 $q=\binom r2$，对同一个任意有限 POVM $E=(E_x)_{x=1}^m$ 定义

$$
\begin{aligned}
&E_x\succeq0,\qquad \sum_xE_x=I_A,\\
&p_i(x)=\operatorname{Tr}(E_x\rho_i),\qquad
 F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1,\\
&C_{ij}(E)=\sum_x\sqrt{p_i(x)p_j(x)},\qquad
 \delta_{ij}(E)=C_{ij}(E)-F(\rho_i,\rho_j),\\
&F_U(\boldsymbol\rho)=q^{-1}\sum_{i<j}F(\rho_i,\rho_j),\\
&F_M(\boldsymbol\rho)=\inf_{\substack{m\ge1\text{ 有限},\ E_x\succeq0\\
\sum_xE_x=I_A}}q^{-1}\sum_{i<j}C_{ij}(E),\\
&\Delta(\boldsymbol\rho)=F_M(\boldsymbol\rho)-F_U(\boldsymbol\rho),\qquad
 G_{\boldsymbol\rho}(E)=q^{-1}\sum_{i<j}\delta_{ij}(E).
\end{aligned}
\tag{1.1}
$$

根保真度的有限测量表示及数据处理采用 S §1 所给的 NMLW 接口：包括奇异态在内，$F(\rho,\sigma)$ 是全部有限 POVM 的经典根保真度下确界，并在 CPTP 映射下不减。因此每个 $\delta_{ij}\ge0$，且 $\Delta=\inf_EG(E)\ge0$。不同态对分别选取的测量不构成 (1.1) 的共同测量。本文将“实际等号测量”严格限定为 $G(E_{\rm actual})=0$，即这一个测量在每一对上等号成立；仅仅是 $F_M$ 的某个最小化测量并不足够，除非还知道 $\Delta=0$。

**定义 1.2（固定仪器的实际联合输入）。** 令 $B$ 是任意正的有限维保留输出空间，$C_{\rm rec}=\mathbb C^m$ 为记录空间。实际有限仪器由 CP 映射

$$
\mathcal I_x(X)=\sum_aK_{xa}XK_{xa}^\dagger,\qquad
K_{xa}:A\longrightarrow B,\qquad
E_x=\sum_aK_{xa}^\dagger K_{xa},\qquad \sum_xE_x=I_A
\tag{1.2}
$$

给出。解码器真正收到的是

$$
\mathcal N(X)=\sum_x|x\rangle\langle x|\otimes\mathcal I_x(X).
\tag{1.3}
$$

未记录的 $a$ 和已丢弃环境均不可读。有限态族恢复是存在一个在整个 $M(C_{\rm rec}\otimes B)$ 上 CPTP 的 $\mathcal R$，满足 $\mathcal R\mathcal N(\rho_i)=\rho_i$ 对所有 $i$ 同时成立。解码器不能依赖未知的输入族成员；等式是在实际分支平均之后成立，不能成功后选择。更强的全输入目标是 $\mathcal R\mathcal N=\operatorname{id}_{M(A)}$；它等价于所有输入与所有未触有限参考的恢复，证明见 §6。

**引理 1.3（正泛函制备、旗标拼接与嵌入回缩）。** 对 $F\succeq0$ 和密度矩阵 $\eta$，映射 $Y\mapsto\operatorname{Tr}(FY)\eta$ 完全正。若每个 $\mathcal R_x:M(B)\to M(A)$ 均 CPTP，则

$$
\mathcal R(Y)=\sum_x\mathcal R_x(Y_{xx}),\qquad
Y_{xx}=(\langle x|\otimes I_B)Y(|x\rangle\otimes I_B)
\tag{1.4}
$$

是全联合代数上的 CPTP 映射。若 $b:A\to H$ 是等距嵌入，$P=bb^\dagger$，$\iota(X)=bXb^\dagger$，则任选输入密度矩阵 $\omega$，

$$
\mathcal T_b(Y)=b^\dagger Yb+\operatorname{Tr}((I_H-P)Y)\omega
\tag{1.5}
$$

是 CPTP，且 $\mathcal T_b\iota=\operatorname{id}_{M(A)}$。

证明。取 $F=\sum_\ell f_\ell|u_\ell\rangle\langle u_\ell|$、$\eta=\sum_j s_j|v_j\rangle\langle v_j|$。算子 $\sqrt{f_\ell s_j}|v_j\rangle\langle u_\ell|$ 的 Kraus 和恰为正泛函制备，其伴随乘积和为 $F$。若 $L_{xj}$ 是 $\mathcal R_x$ 的 Kraus 算子，则 (1.4) 的 Kraus 算子为 $L_{xj}(\langle x|\otimes I_B)$，伴随乘积和为 $I_{C_{\rm rec}}\otimes I_B$。最后，(1.5) 第一项的 Kraus 伴随乘积为 $P$，第二项由前述构造贡献 $I_H-P$，故全空间上 CP 且保迹；代入 $bXb^\dagger$ 得回缩恒等式。所有等式都是复算子恒等式，张量任意参考恒等后仍成立。因此恢复至 $A$ 与恢复至指定嵌入目标 $\iota$ 可以互相转化，但并不把任意未知的全空间 $H$ 输入也加入恢复目标。$\square$

## 2. 忠实正传输与共同等号效应

**引理 2.1（正传输和精确残差；S 定义 1.3、定理 2.1 的接口）。** 对忠实 $\rho_0,\rho_i$，唯一正定解 $T_i\rho_0T_i=\rho_i$ 为

$$
T_i=\rho_0^{-1/2}(\rho_0^{1/2}\rho_i\rho_0^{1/2})^{1/2}\rho_0^{-1/2},
\qquad T_0=I_A,
\qquad \operatorname{Tr}(\rho_0T_i)=F(\rho_0,\rho_i).
\tag{2.1}
$$

对非零效应令 $t_{ix}=\sqrt{p_i(x)/p_0(x)}>0$，则

$$
\delta_{0i}(E)=\sum_x
\frac{\|\sqrt{E_x}(T_i-t_{ix}I_A)\sqrt{\rho_0}\|_F^2}{2t_{ix}}.
\tag{2.2}
$$

故 $\delta_{0i}(E)=0$ 当且仅当对每个非零效应都有

$$
\sqrt{E_x}T_i=t_{ix}\sqrt{E_x},\qquad
T_i\sqrt{E_x}=t_{ix}\sqrt{E_x}.
\tag{2.3}
$$

证明。以 $\sqrt{\rho_0}$ 合同变换传输方程，$\sqrt{\rho_0}T_i\sqrt{\rho_0}$ 必为 $\sqrt{\rho_0}\rho_i\sqrt{\rho_0}$ 的唯一正平方根，得存在性、唯一性和根保真迹式。忠实性使非零正效应上的所有概率正。令 $A_x=\sqrt{E_x}\sqrt{\rho_0}$、$B_{ix}=\sqrt{E_x}T_i\sqrt{\rho_0}$，则两者的 Frobenius 范数平方分别为 $p_0(x),p_i(x)$。展开得到

$$
\frac{\|B_{ix}-t_{ix}A_x\|_F^2}{2t_{ix}}
=\sqrt{p_0(x)p_i(x)}-\operatorname{Re}\operatorname{Tr}(A_x^\dagger B_{ix}).
$$

最后一项求和等于 $\operatorname{Tr}(\rho_0\sum_xE_xT_i)=F(\rho_0,\rho_i)$，证明 (2.2)。非负项之和为零恰使每项为零；消去右侧可逆的 $\sqrt{\rho_0}$ 并取伴随即得 (2.3)。这是 Fuchs–Caves 成对等号条件在所定传输方向上的残差表达。$\square$

**命题 2.2（有限达到、传输对易和全部等号效应；S 定理 2.2、3.1）。** (1.1) 的下确界达到，某个最小化 POVM 至多含 $d^2$ 个非零秩一效应。对忠实族，下列条件等价：$\Delta=0$；存在一个有限共同等号 POVM；所有 $T_i$ 两两对易。成立时，令 $P_\alpha$ 为按不同联合特征值元组标记的非零联合谱投影，

$$
T_iP_\alpha=\lambda_{i\alpha}P_\alpha,\qquad
\lambda_{i\alpha}>0,\qquad \lambda_{0\alpha}=1.
\tag{2.4}
$$

一个 POVM 等号成立，当且仅当其每个非零效应满足

$$
E_x=P_{\alpha(x)}E_xP_{\alpha(x)},\qquad
\sum_{x:\alpha(x)=\alpha}E_x=P_\alpha.
\tag{2.5}
$$

证明。对正分解 $E=\sum_kE_k$，Cauchy–Schwarz 给出

$$
\sum_k\sqrt{\operatorname{Tr}(E_k\rho_i)\operatorname{Tr}(E_k\rho_j)}
\le\sqrt{\operatorname{Tr}(E\rho_i)\operatorname{Tr}(E\rho_j)}.
$$

因此谱细化不增任何成对目标。把秩一效应写成 $w_xQ_x$，其中 $Q_x$ 是迹一秩一投影、$w_x>0$；约束为 $\sum_xw_xQ_x=I_A$，目标为 $\sum_xw_xh(Q_x)$，$h(Q)=q^{-1}\sum_{i<j}\sqrt{\operatorname{Tr}(Q\rho_i)\operatorname{Tr}(Q\rho_j)}$。若正权重超过 $d^2$ 个，Hermitian 空间的实线性相关给出非零实数列 $a_x$，满足 $\sum_xa_xQ_x=0$。取迹有 $\sum_xa_x=0$，故两种符号均出现。选择其整体符号使 $\sum_xa_xh(Q_x)\le0$，再把权重换成

$$
w_x+s a_x,\qquad s=\min_{a_x<0}\frac{w_x}{-a_x}>0.
$$

这保持非负性和约束，至少删去一个正权重，且不增目标。有限重复后至多剩 $d^2$ 项。补零至 $d^2$ 个槽，正、秩至多一、和为恒等的元组构成非空紧集：各槽在 $0\preceq E_x\preceq I_A$ 中，约束均闭；目标在零效应处也连续。因此该紧集上有最小值，且与全部有限 POVM 的下确界相同。这里必须容许秩为零的边界。

若 $\Delta=0$，达到性和每对缺陷非负使达到测量在所有态对上同时等号成立。(2.3) 给出 $[T_i,T_j]\sqrt{E_x}=0$，右乘 $\sqrt{E_x}$ 后求和得 $[T_i,T_j]=0$。反向，若传输对易，则

$$
S_{ij}=T_jT_i^{-1}>0,\qquad
S_{ij}\rho_iS_{ij}=(T_jT_i^{-1})(T_i\rho_0T_i)(T_i^{-1}T_j)=\rho_j.
$$

由唯一性这是态对 $i,j$ 的正传输；在每个 $P_\alpha$ 上它是标量 $\lambda_{j\alpha}/\lambda_{i\alpha}$。若效应满足 (2.5)，该比值平方即为 $p_j(x)/p_i(x)$，故引理 2.1 用于每一对时残差均零，特别联合谱 PVM 本身可行。必要性亦由 (2.3) 得到：每个 $\sqrt{E_x}$ 的像空间只含同一联合特征值元组的向量，故支撑在一块；将完备性压缩至该块即得块内求和式。

不同元组是块的身份；不能任意把同一元组的简并块再标成不同元组。块内效应可以是任意满足和约束的正算子，无需为投影，也无需彼此对易。$\square$

## 3. 实际等号仪器的尖锐有限态族恢复定理

**定理 3.1（每一种实际实现都恰由态对易决定）。** 固定定义 1.2 的任意实际有限仪器，并假设其实际记录效应满足 $G_{\boldsymbol\rho}(E)=0$。按命题 2.2 取联合块，令

$$
A_\alpha=P_\alpha\rho_0P_\alpha,\qquad
\pi_i(\alpha)=\operatorname{Tr}(P_\alpha\rho_i)
=\lambda_{i\alpha}^2\pi_0(\alpha),\qquad \pi_0(\alpha)>0.
\tag{3.1}
$$

则下列四项等价：存在一个共同 CPTP 解码器恢复全部 $\rho_i$；$\rho_0=\sum_\alpha A_\alpha$；$[\rho_0,T_i]=0$ 对全部 $i$ 成立；$[\rho_i,\rho_j]=0$ 对全部 $i,j$ 成立。

量词是：对于每个忠实有限态族、每个共同等号 POVM、每个实现该 POVM 的有限维实际仪器，上述等价均成立。输出空间可以有任意允许的正有限维数，块可以任意简并，量子输出可以奇异。对于不对易族，没有一种等号效应的实现能恢复它；对于对易族，以下同一形式的块制备解码器对每一种实现均可用。

证明。先删零效应；由 $\sum_aK_{xa}^\dagger K_{xa}=0$ 可知其每个 Kraus 算子均零，故不损失实际分支。固定非零效应所属块 $\alpha=\alpha(x)$。若 $v\in\ker P_\alpha$，则

$$
\sum_a\|K_{xa}v\|^2=\langle v,E_xv\rangle=0.
$$

每项非负，故实际的每个 $K_{xa}=K_{xa}P_\alpha$。另一方面，尽管 $\rho_0$ 可以有跨块相干，仍有 $P_\alpha\rho_iP_\alpha=\lambda_{i\alpha}^2A_\alpha$。因而

$$
\mathcal I_x(\rho_i)=\lambda_{i\alpha}^2\mathcal I_x(A_\alpha),\qquad
\operatorname{Tr}\mathcal I_x(A_\alpha)=p_0(x)>0.
$$

定义 $\tau_x=\mathcal I_x(A_\alpha)/p_0(x)$，得到实际族内的因子化

$$
\mathcal I_x(\rho_i)=p_i(x)\tau_x,\qquad
p_i(x)=\lambda_{i\alpha}^2p_0(x),\qquad
\mathcal N(\rho_i)=\sum_xp_i(x)|x\rangle\langle x|\otimes\tau_x.
\tag{3.2}
$$

每个 $\tau_x$ 是与 $i$ 无关的密度矩阵。这是由实际仪器推出的条件量子输出结论，并非对所有输入预设测量制备因子化。

若有共同解码器，令 $\eta_x=\mathcal R(|x\rangle\langle x|\otimes\tau_x)$，则它是与 $i$ 无关的密度矩阵，且 $\rho_i=\sum_xp_i(x)\eta_x$。由块内效应之和为 $P_\alpha$，可聚合为

$$
\eta_\alpha=\frac{\sum_{x:\alpha(x)=\alpha}p_0(x)\eta_x}{\pi_0(\alpha)},\qquad
\rho_i=\sum_\alpha\pi_i(\alpha)\eta_\alpha.
\tag{3.3}
$$

各 $\eta_\alpha$ 正且迹一。定义列随机矩阵 $M_{\beta\alpha}=\operatorname{Tr}(P_\beta\eta_\alpha)$。对 (3.3) 再测量联合块，得到 $M\pi_i=\pi_i$，特别有严格正的平稳列向量 $\pi_0$。记

$$
v_{i\alpha}=\frac{\pi_i(\alpha)}{\pi_0(\alpha)}=\lambda_{i\alpha}^2,
\qquad W_{\beta\alpha}=M_{\beta\alpha}\pi_0(\alpha).
$$

其行和、列和及加权关系分别为

$$
\sum_\alpha W_{\beta\alpha}=\pi_0(\beta),\qquad
\sum_\beta W_{\beta\alpha}=\pi_0(\alpha),\qquad
\sum_\alpha W_{\beta\alpha}v_{i\alpha}=\pi_0(\beta)v_{i\beta}.
$$

完整展开非负平方和，得

$$
\begin{aligned}
\sum_{\beta,\alpha}W_{\beta\alpha}(v_{i\alpha}-v_{i\beta})^2
&=\sum_\alpha\pi_0(\alpha)v_{i\alpha}^2
 +\sum_\beta\pi_0(\beta)v_{i\beta}^2
 -2\sum_\beta\pi_0(\beta)v_{i\beta}^2\\
&=0.
\end{aligned}
\tag{3.4}
$$

故 $M_{\beta\alpha}>0$ 强制全部 $i$ 都有 $\lambda_{i\alpha}^2=\lambda_{i\beta}^2$。特征值正，平方无符号歧义；联合元组不同，遂强制 $\alpha=\beta$。由列和为一得到 $M=I$。这里没有使用可逆性、详细平衡、不可约性或概率向量之间的线性独立性。

于是 $\operatorname{Tr}((I-P_\alpha)\eta_\alpha)=0$。此数等于 $\|(I-P_\alpha)\sqrt{\eta_\alpha}\|_F^2$，由正性可知 $\eta_\alpha=P_\alpha\eta_\alpha P_\alpha$，连跨块项也全为零。(3.3) 在 $i=0$ 时即证明 $\rho_0$ 块对角。这一步覆盖任意块内简并。

反向，若 $\rho_0=\sum_\alpha A_\alpha$，令 $\sigma_\alpha=A_\alpha/\pi_0(\alpha)$，在整个联合代数上定义

$$
\mathcal R(Y)=\sum_x\operatorname{Tr}(Y_{xx})\sigma_{\alpha(x)}.
\tag{3.5}
$$

引理 1.3 证明它完全正且保迹；零效应可任取制备态。它读取 $x$，可以忽略 $B$，且

$$
\mathcal R\mathcal N(\rho_i)
=\sum_xp_i(x)\sigma_{\alpha(x)}
=\sum_\alpha\lambda_{i\alpha}^2A_\alpha=\rho_i.
$$

再核对其余等价方向。$[\rho_0,T_i]$ 的 $\alpha,\beta$ 块为 $(\lambda_{i\beta}-\lambda_{i\alpha})P_\alpha\rho_0P_\beta$；不同联合元组总有某一分量不同，所以所有这些交换子为零恰等于跨块全零。在块对角情形，所有 $\rho_i$ 的 $\alpha$ 块为同一个 $A_\alpha$ 的正标量倍数，故两两对易。反过来，若忠实态两两对易，它们可同时对角化；唯一正传输在同一基中对角元为 $\sqrt{\rho_{i,k}/\rho_{0,k}}$，故与 $\rho_0$ 对易。四项等价证毕。

若只有一个联合块，每个 $T_i$ 为正标量乘恒等，态迹归一使该标量为一，故所有态相同，(3.5) 仍适用。由此，退化族与高秩联合块都没有遗漏。$\square$

**推论 3.2（保真完全等号仍不是恢复判据）。** 在定理 3.1 的任意实际实现上，每对联合输出满足

$$
F(\mathcal N(\rho_i),\mathcal N(\rho_j))=F(\rho_i,\rho_j),\qquad
\Delta(\mathcal N(\boldsymbol\rho))=0.
\tag{3.6}
$$

证明。真实链 $\rho_i\to\mathcal N(\rho_i)\to p_i$ 的两步数据处理给出

$$
F(\rho_i,\rho_j)\le F(\mathcal N(\rho_i),\mathcal N(\rho_j))
\le C_{ij}(E)=F(\rho_i,\rho_j).
$$

在输出上读记录是一个共同有限 POVM，其每对经典根保真都恰等于相应输出根保真。因此输出的 $F_M\le F_U$，结合普遍反向界得等号。这里无需对可能奇异的联合输出使用忠实传输分类。§4 的不对易例满足 (3.6) 却不能恢复，因而这些等号不是充分恢复条件。$\square$

## 4. 实际共同等号仪器上的量子比特反例

**命题 4.1（全部成对根保真保留，而联合输出严格收缩）。** 任取实数 $0<k<1$、$0<a<b<1$。对 $s\in\{0,a,b\}$ 定义

$$
\rho_s=\frac12\begin{pmatrix}
1+s&k\sqrt{1-s^2}\\
k\sqrt{1-s^2}&1-s
\end{pmatrix}.
\tag{4.1}
$$

取 $A=B=\mathbb C^2$，$P_j=|j\rangle\langle j|$，固定实际 Kraus 算子 $K_0=P_0,K_1=P_1$，保留两结果记录和量子输出：

$$
\mathcal N(X)=|0\rangle\langle0|\otimes P_0XP_0
 +|1\rangle\langle1|\otimes P_1XP_1.
\tag{4.2}
$$

该三态忠实且不同，$\Delta(\boldsymbol\rho)=G(E_{\rm actual})=0$，每一对根保真均由 (4.2) 保留，输出缺陷亦为零；但不存在恢复全部三态的共同 CPTP 解码器。

证明。每态迹一、对角元正，且 $\det\rho_s=(1-k^2)(1-s^2)/4>0$。相对于 $s=0$ 的唯一正传输是 $T_s=\operatorname{diag}(\sqrt{1+s},\sqrt{1-s})$，因为合同乘积 $T_s\rho_0T_s=\rho_s$。它们对易，且实际效应就是共同联合谱 PVM。命题 2.2 给出 $\Delta=G=0$；$P_0+P_1=I_2$ 亦证明实际仪器 CP 且保迹。

可逐对显式核对根保真。对于任意两个量子比特态，正矩阵 $\sqrt\rho\sigma\sqrt\rho$ 的两个特征值给出

$$
F(\rho,\sigma)^2=\operatorname{Tr}(\rho\sigma)+2\sqrt{\det\rho\det\sigma}.
$$

这是两个非负特征值平方根之和的平方，故包括奇异情形。在 (4.1) 中令 $R_{st}=\sqrt{(1-s^2)(1-t^2)}$，则

$$
\operatorname{Tr}(\rho_s\rho_t)=\frac{1+st+k^2R_{st}}2,\qquad
2\sqrt{\det\rho_s\det\rho_t}=\frac{(1-k^2)R_{st}}2.
$$

因此 $F(\rho_s,\rho_t)^2=(1+st+R_{st})/2$。实际坐标分布的经典根保真为

$$
C_{st}=\frac{\sqrt{(1+s)(1+t)}+\sqrt{(1-s)(1-t)}}2,
$$

其平方正是同一个表达式，且两者非负，故 $F=C_{st}$。实际联合输出是

$$
\mathcal N(\rho_s)=\frac{1+s}2|0,0\rangle\langle0,0|
 +\frac{1-s}2|1,1\rangle\langle1,1|,
$$

所以联合根保真也等于 $C_{st}$。记录读出见证其输出缺陷为零。

然而，$a,0$ 两态的联合输出差非零特征值为 $\pm a/2$，于是

$$
\frac12\|\mathcal N(\rho_a)-\mathcal N(\rho_0)\|_1=\frac a2.
$$

输入差为 $\tfrac12\begin{pmatrix}a&k(\sqrt{1-a^2}-1)\\k(\sqrt{1-a^2}-1)&-a\end{pmatrix}$。迹零 Hermitian 二阶矩阵 $\begin{pmatrix}z&c\\\overline c&-z\end{pmatrix}$ 的平方为 $(z^2+|c|^2)I$，故

$$
\frac12\|\rho_a-\rho_0\|_1
=\frac12\sqrt{a^2+k^2(1-\sqrt{1-a^2})^2}>\frac a2.
\tag{4.3}
$$

任意 CPTP 映射在 Hermitian 输入上收缩迹范数：写 $H=H_+-H_-$，由正性、保迹和三角不等式，$\|\mathcal R(H)\|_1\le\operatorname{Tr}H_++\operatorname{Tr}H_-=\|H\|_1$。若同一 $\mathcal R$ 恢复 $\rho_a,\rho_0$，便与 (4.3) 矛盾。第三态不会消除这个矛盾。另有 $[\rho_0,\rho_a]=\begin{pmatrix}0&-ka/2\\ka/2&0\end{pmatrix}\ne0$，与定理 3.1 一致。这里收缩的是实际量子输出与实际记录的完整联合态，不是一个被擅自缩小的经典解码器类别。$\square$

**推论 4.2（最小性的限定）。** 不同态的输入维数至少为二，源约定 $r\ge3$ 下至少有三态；(4.1) 达到这两点。如果放宽该元组约定，(4.3) 已由两个态给出分离。一个忠实不同态对的等号测量至少有两个非零结果，(4.2) 也达到该数。

证明。一维仅有一个密度矩阵。若仅有一个非零效应，它必须为 $I_A$；引理 2.1 的零残差强制 $T=tI_A$，态迹归一再强制 $t=1$，两个态因而相同。故不同态对不可能有单结果等号测量。这里不声称保留输出维数的最小性或全部仪器类别的其他最小性。$\square$

## 5. 固定仪器、选择实现与有限态族的 Choi 条件

**命题 5.1（实际有限态族恢复的 Choi 可行性）。** 对任意固定有限仪器和有限态族，允许输入奇异，令 $S_{ix}=\mathcal I_x(\rho_i)$，保留其实际未归一化权重。固定 $B$ 的一个正交基。共同恢复存在当且仅当存在 $B\otimes A$ 上的矩阵 $J_x$ 满足

$$
J_x\succeq0,\qquad \operatorname{Tr}_A J_x=I_B,\qquad
\sum_x\operatorname{Tr}_B[(S_{ix}^{\mathsf T}\otimes I_A)J_x]=\rho_i
\quad\text{对每个 }i.
\tag{5.1}
$$

转置只在已指定的 $B$ 基中。它是标准 Choi 参数化对实际联合解码器的应用，是有限半正定约束规格，不是已执行的可行性求解。

证明。若 $\mathcal R$ 存在，则 $\mathcal R_x(Y)=\mathcal R(|x\rangle\langle x|\otimes Y)$ 为 CP 且保迹。其 Choi 矩阵

$$
J_x=\sum_{u,v}|u\rangle\langle v|\otimes\mathcal R_x(|u\rangle\langle v|)
$$

正，且 $\operatorname{Tr}_A J_x=I_B$。矩阵单位展开给出 $\mathcal R_x(Y)=\operatorname{Tr}_B[(Y^{\mathsf T}\otimes I_A)J_x]$，代入实际 $S_{ix}$ 即得必要式。

反向，把每个正 $J_x$ 谱分解为向量外积，逐一重排为 $|L_{xj}\rangle\rangle=\sum_u|u\rangle\otimes L_{xj}|u\rangle$，得到 CP 映射 $\mathcal R_x(Y)=\sum_jL_{xj}YL_{xj}^\dagger$ 和上述重建公式。在这一向量化约定下，$\operatorname{Tr}_A J_x=(\sum_jL_{xj}^\dagger L_{xj})^{\mathsf T}$，所以单位矩阵约束恰等价于保迹。引理 1.3 的旗标拼接在全联合代数上给出 CPTP 解码器，(5.1) 使其恢复全族。证明中没有除以分支概率；零概率和奇异分支不成问题，完全未使用的分支也可以任取 CPTP 限制。每个态必须满足同一组 $J_x$，不能分别求出不同解码器后拼作共同解。$\square$

**命题 5.2（平方根实现的支配与维数边界）。** 若允许保留输入大小的量子空间 $A$，则

$$
\mathcal N_E(X)=\sum_x|x\rangle\langle x|\otimes\sqrt{E_x}X\sqrt{E_x}
\tag{5.2}
$$

经 CPTP 后处理能产生实现相同效应的每一种仪器输出。因此，允许该保留空间时，“存在某种可恢复实现”等价于“平方根实现可恢复”。这不允许把已指定的小输出空间 $B$ 替换为 $A$。

证明。令 $Q_x=\operatorname{supp}E_x$，$E_x^{-1/2}$ 只在支撑上求逆，核上为零。效应支撑论证给出 $K_{xa}=K_{xa}Q_x$。置 $L_{xa}=K_{xa}E_x^{-1/2}$，则 $\sum_aL_{xa}^\dagger L_{xa}=Q_x$。任选输出密度矩阵 $\omega_x$，定义

$$
\Phi_x(Y)=\sum_aL_{xa}YL_{xa}^\dagger
 +\operatorname{Tr}((I_A-Q_x)Y)\omega_x.
$$

引理 1.3 的补空间制备使其全空间上 CP，伴随乘积和为 $Q_x+(I_A-Q_x)=I_A$，故保迹。又 $E_x^{-1/2}\sqrt{E_x}=Q_x$，且补空间项在 $\sqrt{E_x}X\sqrt{E_x}$ 上为零，故

$$
\Phi_x(\sqrt{E_x}X\sqrt{E_x})=\mathcal I_x(X).
$$

读取并保留 $x$、条件应用 $\Phi_x$ 得到全联合 CPTP 后处理 $\Phi$，使 $\mathcal N=\Phi\mathcal N_E$。若 $\mathcal R$ 解码 $\mathcal N$，则 $\mathcal R\Phi$ 解码 $\mathcal N_E$；反向存在性由 (5.2) 本身就是允许实现得到。零效应给出 $Q_x=0$、全部 $K_{xa}=0$，可用任意制备补全，亦无例外。$\square$

在定理 3.1 的等号效应条件下，选择实现不会改变族恢复答案。离开这一条件，效应通常不足以判断一个固定实现。若连效应和仪器都不规定，可以选恒等信道加独立虚记录恢复任意族；这是另一存在性问题，不能回答固定实际仪器的恢复问题，也不是 §4 或 §7 反例的构造。

## 6. 全输入与全部参考的复 Kraus 判据

**定理 6.1（带实际旗标的全码纠错）。** 对固定有限仪器，全输入恢复等价于每个可见 $x$ 内全部复交叉项满足

$$
K_{xa}^\dagger K_{xb}=\gamma_{x,ab}I_A\qquad\text{对所有 }a,b.
\tag{6.1}
$$

不同记录的旗标正交，所以不再有跨 $x$ 的附加条件。这是 S §7 所引 Knill–Laflamme、Gregoratti–Werner 标准全码纠错接口；以下证明包括矩形等距算子和全输出补全，不将它作为新的通用纠错定理。

证明。若 $\mathcal R\mathcal N=\operatorname{id}$，取解码器 Kraus 算子 $R_j$，复合信道的 Kraus 算子为 $T_{jxa}=R_j(|x\rangle\otimes K_{xa})$。恒等信道的 Choi 矩阵是秩一正矩阵 $|I_A\rangle\rangle\langle\langle I_A|$。正外积和等于该矩阵，意味着每个向量 $|T_{jxa}\rangle\rangle$ 都在其一维支撑内：对任意正交向量取二次型，所得非负平方和为零，各项都零。因此 $T_{jxa}=c_{jxa}I_A$。令 $R_{jx}=R_j(|x\rangle\otimes I_B)$，保迹性给出 $\sum_jR_{jx}^\dagger R_{jx}=I_B$，从而

$$
K_{xa}^\dagger K_{xb}
=\sum_j(R_{jx}K_{xa})^\dagger(R_{jx}K_{xb})
=\left(\sum_j\overline{c_{jxa}}c_{jxb}\right)I_A.
$$

这保留了虚部，不是只检查对角项或实交叉项。

反向，$\Gamma_x=(\gamma_{x,ab})$ 为 Hermitian 半正定矩阵，因为对任意复 $z$，

$$
\left(\sum_a z_aK_{xa}\right)^\dagger\left(\sum_b z_bK_{xb}\right)
=(z^\dagger\Gamma_xz)I_A\succeq0.
$$

取酉矩阵 $U$ 使 $U^\dagger\Gamma_xU=\operatorname{diag}(\lambda_{xk})$，并令 $L_{xk}=\sum_aU_{ak}K_{xa}$。酉 Kraus 旋转不改变 $\mathcal I_x$，且 $L_{xk}^\dagger L_{x\ell}=\lambda_{xk}\delta_{k\ell}I_A$。零特征值的 Kraus 算子为零；其余写成 $\sqrt{\lambda_{xk}}V_{xk}$，得到 $V_{xk}^\dagger V_{x\ell}=\delta_{k\ell}I_A$，即同一 $x$ 内的等距算子像空间彼此正交。令 $P_x=\sum_kV_{xk}V_{xk}^\dagger\preceq I_B$，定义

$$
\mathcal R_x(Y)=\sum_kV_{xk}^\dagger YV_{xk}
 +\operatorname{Tr}((I_B-P_x)Y)\omega,
\tag{6.2}
$$

$\omega$ 为任意输入密度矩阵。引理 1.3 使其全空间上 CPTP，并由正交性得 $\mathcal R_x\mathcal I_x(X)=(\sum_k\lambda_{xk})X$。无非零 Kraus 的记录可任取 CPTP 解码。总仪器保迹强制 $\sum_{x,k}\lambda_{xk}=1$，因此旗标拼接得到 $\mathcal R\mathcal N(X)=X$。

最后，复算子恒等式张量任意有限参考恒等仍成立。反过来，只要求所有参考自由输入密度矩阵的恢复，也已通过正矩阵的缩放、Hermitian 正负部分和复线性张成固定全部 $M(A)$。所以全输入恒等、全部输入态恢复、全部输入及全部未触有限参考恢复在此等价。$\square$

**推论 6.2（标量效应的必要性与固定实现反例）。** 全输入恢复强制 $E_x=p_xI_A$，但这些效应对固定实现并不充分。如果允许选择实现且 $\dim B\ge\dim A$，它们又足以实现全输入恢复。

证明。(6.1) 的对角项求和给出 $p_x=\sum_k\lambda_{xk}$。固定的抹除仪器 $\mathcal I_x(X)=p_x\operatorname{Tr}(X)\omega_B$ 有同一效应，却在所有密度矩阵上输出相同；当 $\dim A>1$ 时不能恢复两个不同态。若允许选择一个等距 $V:A\to B$，取 $K_x=\sqrt{p_x}V$，由引理 1.3 的像空间回缩即可恢复所有输入。若规定 $\dim B<\dim A$，定理 6.1 的任意非零分支所需等距算子都不存在，不能把较大空间的实现引入原任务。有限态族恢复无须满足 (6.1)；§8 才给出何时可将族目标提升为全代数目标。$\square$

## 7. 指定五维仪器、压缩反例与精确记录应用

**定义 7.1（保留 S 的实际坐标与权限）。** 取 $H=\mathbb C^5$ 的正交基 $e_0,\ldots,e_4$，令

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad b(q_0,q_1,q_2)=q_0u+q_1v+q_2z.
\tag{7.1}
$$

$b:\mathbb C^3\to H$ 等距，$P_R=bb^\dagger$，$\iota(X)=bXb^\dagger$。S 中该嵌入的符号为 $B$，本文使用小写 $b$，避免与任意保留输出空间 $B$ 混淆。实际全空间 Kraus 算子为

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_3|.
\end{aligned}
\tag{7.2}
$$

它们的伴随乘积分别为 $\operatorname{diag}(1,0,1/2,0,1)$、$\operatorname{diag}(0,1,1/2,1,0)$，和为 $I_5$。取

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\quad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\quad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}.
\tag{7.3}
$$

作用于 $u,v,z$ 得到 $K_jb=bU_j/\sqrt2$，$U_1=U_0W$，$W=W^\dagger$ 且 $W^2=I_3$。另一实际环境测量基产生

$$
A_0=cK_0+isK_1,\qquad A_1=isK_0+cK_1,
\qquad c=\cos\theta,\quad s=\sin\theta.
\tag{7.4}
$$

两种选择为 $\theta=0,\pi/6$。系数矩阵 $\begin{pmatrix}c&is\\is&c\end{pmatrix}$ 酉，故它们在整个 $M_5$ 上有同一平均信道。码上的限制为 $A_jb=bV_j/\sqrt2$，其中 $V_0=U_0(cI+isW)$、$V_1=V_0W$ 均酉。以下 $Q_j$ 表示实际所选仪器的 $U_j$ 或 $V_j$。

恢复权限依 S §§7–10 固定：每步新环境、相同交互、相同已选环境基测量、取得实际标签后丢弃环境；只由这些标签更新经典记录。没有中间量子反馈、自适应仪器、参考读取、保留量子环境、额外量子摘要、依赖输入的量子旁信息或成功后选择。终端解码器收到实际 $H$ 与完整被计数视图。目标是所有 qutrit 码输入及任意未触有限参考经 $\iota$ 嵌入，非任意未知五维输入。码上每个标签的效应为 $I_3/2$，所以对全部码输入和参考公平；(7.2) 明确显示这不等于全 $H$ 输入公平。

**命题 7.2（在指定仪器中，输入零缺陷本身不充分）。** 保持 $\theta=0$ 的实际仪器，取已知时长 $n=1$，并把两个取得的标签压缩成同一个视图 $y$。存在三个忠实、对易、输入缺陷为零的 qutrit 态，却无法由实际 $H$ 和该一值记录恢复。

证明。取 $D=\operatorname{diag}(1,-1,0)$，$0<t<1/3$，令 $\rho_0=I_3/3$、$\rho_\pm=I_3/3\pm tD$。它们正定、迹一、不同且对角；共同坐标测量已达到各对根保真，故 $\Delta=0$。实际输入无关压缩满足 $r(y\mid0)=r(y\mid1)=1$，所以完整保留输出为单一旗标乘以下量子态：

$$
\mathcal N_y(X)=\tfrac12b(U_0XU_0^\dagger+U_1XU_1^\dagger)b^\dagger
=bU_0\frac{X+WXW}{2}U_0^\dagger b^\dagger.
\tag{7.5}
$$

由于 $WDW=-D$，三个量子输出都等于 $b(I_3/3)b^\dagger$，记录也完全相同；同一个线性解码器不能将一个联合输入送至三个不同目标。两分支均按规定权重求和，没有选取成功事件。

这里实际细标签效应为 $I_3/2$，压缩后效应为 $I_3$，它们对任意密度矩阵给出相同记录分布，所以 $C_{ij}=1$。而

$$
F(\rho_0,\rho_\pm)=\frac{\sqrt{1+3t}+\sqrt{1-3t}+1}{3}<1,
\qquad F(\rho_+,\rho_-)=2\sqrt{1/9-t^2}+1/3<1.
$$

第一个严格性来自平方根严格凹与 $t>0$，第二个来自 $t^2>0$。故这些实际效应的 $G>0$，不满足定理 3.1 的实际等号前提。这正区分输入 $\Delta=0$ 和实际 $G=0$；保留细标签则可按下一命题恢复全部码输入。$\square$

**命题 7.3（实际压缩的全输入判据）。** 在固定仪器、固定已知 $n\ge0$ 和固定有限输入无关压缩核 $r(y\mid h)$ 下，令时间顺序为 $h=(h_1,\ldots,h_n)$，

$$
Q_h=Q_{h_n}\cdots Q_{h_1},\quad Q_\varnothing=I_3,\qquad
r(y\mid h)\ge0,\quad\sum_y r(y\mid h)=1.
$$

实际解码前信道为

$$
\mathcal N_r(X)=2^{-n}\sum_{h,y}r(y\mid h)|y\rangle\langle y|
 \otimes bQ_hXQ_h^\dagger b^\dagger.
\tag{7.6}
$$

存在一个接收记录与实际 $H$ 的全联合 CPTP 解码器，能精确恢复全部码输入与参考，当且仅当对每个正视图 $y$，其全部正权重历史只有一个射影词类，即

$$
r(y\mid h)r(y\mid k)>0\quad\Longrightarrow\quad
Q_h^\dagger Q_k\in\mathbb CI_3.
\tag{7.7}
$$

证明。由码不变性和实际所选算子 $L_jb=bQ_j/\sqrt2$ 的限制（$L_j$ 为 $K_j$ 或 $A_j$），逐次组合得到历史 Kraus $2^{-n/2}bQ_h$，每个历史概率为 $2^{-n}$，包括所有未触参考。最新因子在最左，不能倒转词序。压缩后 $y$ 内的 Kraus 为 $K_{yh}=2^{-n/2}\sqrt{r(y\mid h)}bQ_h$，总伴随乘积和由压缩行和为一得 $I_3$。它们的复交叉项为

$$
K_{yh}^\dagger K_{yk}=2^{-n}\sqrt{r(y\mid h)r(y\mid k)}Q_h^\dagger Q_k.
$$

全 $H$ 解码器达到 $\iota$ 后，接上引理 1.3 的回缩就是字面 qutrit 解码器，故定理 6.1 的必要性适用，给出 (7.7)。相对酉为标量时其模必为一，即同一射影词类。

反向，对每个正视图选一个正权重代表 $h_y$，定义全 $H$ 酉

$$
D_y=bQ_{h_y}^\dagger b^\dagger+(I_H-P_R).
$$

其在码与正交补上分别是逆酉和恒等。若 $Q_h=e^{i\phi_h}Q_{h_y}$，便有 $D_ybQ_h=e^{i\phi_h}b$；相位在密度算子中消去。由引理 1.3 拼接的 $Y\mapsto\sum_yD_yY_{yy}D_y^\dagger$ 是全联合代数上 CPTP，求和所有实际 $2^{-n}r(y\mid h)$ 权重后恰得 $\iota(X)$。它不读取已被压缩掉的细历史。零概率视图可任取解码。复算子等式保证全部参考。$\square$

特别保留 $y=h$ 时，上述 $D_h$ 给出细标签联合信道的精确逆；接上 $\mathcal T_b$ 得字面左逆。有限终端视图至少需要 $m_n=|\{[Q_h]\}|$ 个值：每个历史有正概率，不同类不能共享一个正视图；记录射影类本身达到这个终端数，包括随机压缩也不能降低必要值。关于在线前缀寄存器的实现不由这段终端论证推出。

## 8. 有限族、加权代数和参考的准确迁移

**命题 8.1（复线性空间上的完整迁移）。** 固定一个族解码器，置 $\Lambda=\mathcal R\mathcal N$、$L=\operatorname{span}_{\mathbb C}\{\rho_i\}$。则 $\Lambda$ 在 $L$ 上恒等。对于任意有限参考 $Z$，每个参考矩阵块属于 $L$ 的算子均由 $\Lambda\otimes\operatorname{id}_Z$ 固定。

证明。第一项直接由复线性。取参考正交基展开 $Y=\sum_{u,v}Y_{uv}\otimes|u\rangle\langle v|$，逐块应用 $\Lambda(Y_{uv})=Y_{uv}$ 即得第二项。这包括满足块限制的密度矩阵，并不包括任意联合密度矩阵。反向，$L$ 上恒等当然包含每个族方程。$\square$

**定理 8.2（忠实归一化的生成代数迁移）。** 若 $\rho_0>0$，令

$$
\widehat A_i=\rho_0^{-1/2}\rho_i\rho_0^{-1/2},\qquad
\mathfrak A=C^*(I_A,\widehat A_1,\ldots,\widehat A_{r-1}),\qquad
\mathcal W=\rho_0^{1/2}\mathfrak A\rho_0^{1/2}.
\tag{8.1}
$$

这里 $C^*$ 表示有限维生成的含幺复星代数。每一个恢复该有限族的固定 $\Lambda=\mathcal R\mathcal N$ 都在 $\mathcal W$ 和它的全部有限参考矩阵放大上恒等。若 $\mathfrak A=M(A)$，则同一解码器恢复全部输入和全部未触有限参考。此为标准忠实不变泛函、Schwarz 等号及乘法域方法的应用。

证明。定义

$$
\Phi(X)=\rho_0^{-1/2}\Lambda(\rho_0^{1/2}X\rho_0^{1/2})\rho_0^{-1/2},
\qquad \varphi(X)=\operatorname{Tr}(\rho_0X).
$$

合同映射与 $\Lambda$ 均 CP，故 $\Phi$ CP；$\Lambda(\rho_0)=\rho_0$ 使 $\Phi(I)=I$。保迹性使

$$
\varphi(\Phi(X))=\operatorname{Tr}\Lambda(\rho_0^{1/2}X\rho_0^{1/2})
=\varphi(X).
$$

$\varphi$ 忠实：若 $D\succeq0$ 且 $\varphi(D)=0$，取 $\rho_0\succeq\mu I$、$\mu>0$，便有 $0\ge\mu\operatorname{Tr}D$，故 $D=0$。每个 Hermitian $\widehat A_i$ 均由 $\Phi$ 固定。

从有限 Kraus 形式堆叠得到 $\Phi(X)=V^\dagger(X\otimes I)V$，且含幺性使 $V^\dagger V=I$。对任意满足 $\Phi(D)=D$ 的 Hermitian $D$，

$$
\Phi(D^2)-D^2
=V^\dagger(D\otimes I)(I-VV^\dagger)(D\otimes I)V\succeq0.
\tag{8.2}
$$

不变性使此正矩阵的 $\varphi$ 值为零，忠实性使它为零。右侧是 $T^\dagger T$，其中 $T=(I-VV^\dagger)(D\otimes I)V$，故 $T=0$。因而 $(D\otimes I)V=V\Phi(D)=VD$，取伴随亦有 $V^\dagger(D\otimes I)=DV^\dagger$。对任意 $X$ 得

$$
\Phi(DX)=D\Phi(X),\qquad \Phi(XD)=\Phi(X)D.
$$

对固定生成元反复应用该式，所有词及其复线性组合均固定；由有限维连续性其范数闭包 $\mathfrak A$ 也固定。逆转合同归一化便得到 $\Lambda$ 在 $\mathcal W$ 上恒等。命题 8.1 的矩阵块证明同样适用于 $\mathcal W$；若生成代数是全矩阵代数，可逆合同映射将它满射到 $M(A)$，全输入及参考结论遂成立。$\square$

$\widehat A_i$ 与 §2 的正传输 $T_i$ 是不同对象，不能互换。$\mathcal W$ 是加权线性空间，通常既不是原坐标中的含幺代数，也不必包含 $I_A$。不经忠实归一化就对 $C^*(\rho_i)$ 宣称相同迁移，没有上述证明依据。

**命题 8.3（普通含幺算子系统的实际反例）。** 令 $S_0=\operatorname{span}_{\mathbb C}\{I_A,\rho_i\}$。有限族恢复不自动包含 $S_0$ 上恒等；存在实际信道，使每个族解码器都无法同时恢复 $I_A/d$。

证明。取 $A=\mathbb C^2\oplus\mathbb C$，$\tau>0$ 是不同于 $I_2/2$ 的 qubit 密度矩阵。令 $P$ 是二维块投影，$f$ 是一维补空间的单位向量，置 $A_0=\tau\oplus0$、$B_0=0_2\oplus1$。取三个不同的 $t_j\in(0,1)$，$\rho_j=t_jA_0+(1-t_j)B_0$，这些态忠实且对易。固定实际信道

$$
\mathcal N(X)=\operatorname{Tr}(PX)A_0+\langle f|X|f\rangle B_0.
\tag{8.3}
$$

它保留三维量子输出，可配单值记录。引理 1.3 证明其 CP，两个效应之和为 $I_3$ 故保迹；其固定每个 $\rho_j$，所以恒等解码可恢复该族。

对任意其他族解码器 $\mathcal R$，两种不同 $t_j$ 的方程

$$
t_j\mathcal R(A_0)+(1-t_j)\mathcal R(B_0)=t_jA_0+(1-t_j)B_0
$$

的二阶系数矩阵可逆，遂强制 $\mathcal R(A_0)=A_0$、$\mathcal R(B_0)=B_0$。但 $\mathcal N(I_3)=2A_0+B_0$，故 $\mathcal R\mathcal N(I_3)=2A_0+B_0\ne I_3$，因为 $\tau\ne I_2/2$。所以每个族解码器都不能恢复 $S_0$ 中的 $I_3/3$。

这不违反定理 8.2。取锚 $\rho_0=t_0\tau\oplus(1-t_0)$，则 $\widehat A_j=(t_j/t_0)I_2\oplus((1-t_j)/(1-t_0))$。不同 $t_j$ 使生成代数恰为两个块上的标量代数，故 $\mathcal W=\operatorname{span}_{\mathbb C}\{A_0,B_0\}$。它不含 $I_3$，因为 $\tau$ 不标量；而所有族解码器的复合确实在该加权空间上恒等。一般而言，固定解码器在 $S_0$ 上恒等，恰是族方程再加 $\Lambda(I_A)=I_A$（若此式尚未由族线性张成给出）；保迹不能代替含幺。$\square$

## 9. 独立种子：精确平均与近似平均的不同边界

**命题 9.1（精确平均的纯 Choi 转移）。** 在 §7 的权限下，令 $s$ 是显式免费的独立共享种子，具有标准 Borel 概率律 $\nu$。每个条件完整解码信道 $\mathcal C_s:M_3\to M(H)$ 均 CPTP 且可测。若

$$
\int\mathcal C_s\,d\nu(s)=\iota
\tag{9.1}
$$

在全部码算子上精确成立，则在同一个满测度集合上 $\mathcal C_s=\iota$，同时对所有码输入及所有未触有限参考成立。

证明。令 $|\Omega_3\rangle=3^{-1/2}\sum_{j=0}^2|j\rangle\otimes|j\rangle$，$|\Omega_b\rangle=(b\otimes I)|\Omega_3\rangle$。归一化 Choi 态 $J_s=(\mathcal C_s\otimes\operatorname{id})(|\Omega_3\rangle\langle\Omega_3|)$ 正且迹一，平均为秩一投影 $P_b=|\Omega_b\rangle\langle\Omega_b|$。非负可测函数 $\operatorname{Tr}((I-P_b)J_s)$ 积分为零，故几乎处处为零。正性给出 $J_s=P_bJ_sP_b$，迹一再给出 $J_s=P_b$。Choi 矩阵的矩阵单位展开是单射，因而 $\mathcal C_s=\iota$ 在这个共同满测度集成立，不需交无穷多个输入相关例外集。命题 7.3 遂逐种子适用。$\square$

有限视图是前述矩阵判据的直接范围。若使用 S 所规定的可测解码器与标准 Borel 一般视图，有限个历史还允许以下精确表达：压缩测度为 $r_h(dy)$，令 $\mu(dy)=2^{-n}\sum_hr_h(dy)$，$w_h(y)=2^{-n}dr_h/d\mu$，则 $\sum_hw_h=1$ 几乎处处。条件混合信道 $X\mapsto\sum_hw_h(y)bQ_hXQ_h^\dagger b^\dagger$ CPTP；接上 $\mathcal D_y$ 后仍 CPTP。精确积分为 $\iota$ 时，同一纯 Choi 证明使条件完整信道几乎处处为 $\iota$；对有限历史 Kraus $\sqrt{w_h(y)}bQ_h$ 应用定理 6.1，即得后验正权重历史几乎处处只含一个射影类。这依赖已声明的可测接口，不把非原子视图的零概率单点当作有限字母表，也不推出新的在线构造。

**命题 9.2（近似平均不强制同误差逐种子成立）。** 即使完全遵守 §7 的权限，积分信道的全部输入与参考半迹误差为 $\delta\in(0,1)$，也不保证条件误差几乎处处至多 $\delta$。

证明。保留全部细标签，取独立二值种子。概率 $1-\delta$ 时用精确逆；概率 $\delta$ 时由终端 CPTP 解码器不顾输入而制备固定纯码态 $b|0\rangle$。积分信道为 $(1-\delta)\iota+\delta\mathcal P$，其中 $\mathcal P(X)=\operatorname{Tr}(X)b|0\rangle\langle0|b^\dagger$。任意输入与参考的两个输出态的半迹距离至多一，故积分误差至多 $\delta$；取与 $|0\rangle$ 正交的纯码输入，即达到 $\delta$。坏种子上的误差则恰为一，且其概率 $\delta>0$。所以同误差的几乎处处结论失败。此例只分离精确与近似种子推理，不是新的近似存储下界。$\square$

历史相关且可见的种子属于完整被计数视图，不能改名为独立免费种子。依赖历史而可见的程序、控制选择、时钟变化、存档和缓冲也须一并计数；被丢弃的私有随机性在压缩核中平均。

## 10. 保留的原目标、资源与证据边界

**定义 10.1（OPEN：普适近似协议到共同测量的资源桥梁）。** 固定实际仪器与已知时长 $n$，允许的有限视图协议为

$$
\mathcal C(X)=\int 2^{-n}\sum_{h,y}r_s(y\mid h)
\mathcal D_{s,y}(bQ_hXQ_h^\dagger b^\dagger)\,d\nu(s),
\tag{10.1}
$$

$\mathcal D_{s,y}:M(H)\to M(H)$ 是实际可测 CPTP 解码器，仍接收量子 $H$。$y$ 表示完整被计数视图，规模记为 $W$；无免费种子时取单点种子空间。若选定例如

$$
\operatorname{err}(\mathcal C)=
\sup_{\substack{Z\text{ 有限}\\ \xi\text{ 是 }\mathbb C^3\otimes Z\text{ 上密度矩阵}}}
\frac12\|((\mathcal C-\iota)\otimes\operatorname{id}_Z)(\xi)\|_1,
\tag{10.2}
$$

则原目标仍要求：对每一个符合全部实际权限且 $\operatorname{err}(\mathcal C)\le\varepsilon$ 的协议，构造一个合法有限共同 POVM $E_{\mathcal C}$ 和一个明确实际态族 $\boldsymbol\eta_{\mathcal C}$，证明

$$
0\le\Delta(\boldsymbol\eta_{\mathcal C})
\le G_{\boldsymbol\eta_{\mathcal C}}(E_{\mathcal C})
\le g(W,n,\varepsilon).
\tag{10.3}
$$

共同实现映射、所有常数及足以沿所需方向结合正缺陷下界的资源依赖都必须给出。本文未建立这个普适构造或函数 $g$。定理 3.1 是精确、忠实、实际等号测量下的族恢复定理，不能替代 (10.3) 的量词。分别最优的成对测量、独立边缘、替换实际仪器、删除量子 $H$、成功后选择或从积分近似界假定逐种子同界，都不满足该义务。

两个源卷中的纯经典结论保持其原范围。C 定理 2.1 的三态精确极小极大值和定理 3.1 的传输线性响应证书均针对一个真实有限测量后接同一个制备的链；S 定理 6.2 的 $\varepsilon\ge\Delta^2/8$ 也需要该因子化与最大半迹误差。本文的 (3.2) 只在实际等号前提下导出了族内因子化，没有为任意协议 (10.1) 导出它。

这种区别可由保留纠缠直接检验：任意纯经典测量制备 qutrit 信道 $X\mapsto\sum_x\operatorname{Tr}(E_xX)\omega_x$ 在最大纠缠态的一半作用后输出 $\tfrac13\sum_x\omega_x\otimes E_x^{\mathsf T}$，是正乘积项之和，故可分；细标签精确逆的目标 $|\Omega_b\rangle$ 则 Schmidt 秩为三且纠缠。因而实际细标签恢复不可能被这样的全输入纯经典因子化替代。

源卷 S 定理 8.1–8.2 的标量边界亦可直接说明。细标签联合信道有 §7 给出的 CPTP 左逆，而标签单独的边缘为 $2^{-n}I_{2^n}\operatorname{Tr}X$。后者在密度矩阵上常值，故 $F_U=F_M=1$、$\Delta=0$；若一并保留参考，它还含原参考边缘，不应把该边缘也称为常值。对任意信道，输出 POVM 可由伴随拉回成输入 POVM并保持概率，故 $F_M$ 不减；成对根保真数据处理亦使 $F_U$ 不减。把这两个不等式分别用于细标签联合信道及其字面左逆，便得联合 $F_U,F_M,\Delta$ 都等于输入值，包括奇异输出。S §8 所给的正缺陷 qutrit 族也因此能被精确恢复，说明输入零缺陷并非一般保留量子恢复的必要条件。

同一固定输入族在两角度具有相同的标签缺陷、相同的细标签联合缺陷；(7.4) 又证明其平均全信道相同。S §9.1 通过所引 REC 提供的既有记录数如下；它们在此仅按源接口引用，不把其全长词计数与在线前缀构造当作本文证明。

| 实际角度 | $n=0$ | $n=1$ | $n=2$ | $n\ge3$ |
| --- | --- | --- | --- | --- |
| $\theta=0$ | $1$ | $2$ | $4$ | $6$ |
| $\theta=\pi/6$ | $1$ | $2$ | $4$ | $2^n$ |

在这些既有结论的权限内，上述三个相同标量数据无法区分不同的精确保留记录需求。这只排除了三种指定替代，并非所有未来协议敏感保真桥梁的不可能性证明。§7 给出了终端类数判据的完整应用证明，没有重新给出表中全部词计数、前缀实现或新的记录下界。

记录值数不等于总成本。标签取得、环境准备、测量通信、校准、固定表、已知确定性时钟、逆控制合成、精度和运行时间是其他资源。固定描述可以依赖 $n$，但不能暗藏额外运行相关历史。本文不作物理实现、总成本、经验机器学习增益或更大目标已完成的断言。

忠实性、有限族、有限维和实际 $G=0$ 是主分类的条件。一般 Choi 与全输入 Kraus 判据允许奇异态，但并不自动给出奇异输入的传输分类。一般或 Pauli $F_M$ 精确值、全部正缺陷最优测量、最优常数与指数、一般族的最小恢复误差、全部经典最优解码器分类和普适近似记录桥梁，均不由本文解决。有限族的参考迁移严格限于已证明的复线性空间或忠实加权代数；没有任意含幺系统、任意未加权代数或任意联合态的额外迁移。

## 11. 固定来源身份与方法归属

S 指《AURIC FIB common-measurement compatibility, defect and recovery separation》，固定 UTF-8 内容的 SHA256 为 `220c4122d70761d158e7683572e937e62b0487127c53d950fb850f47c51cdcfe`。本文引用其定义 1.2–1.3、定理 2.1–3.1 的根保真与忠实等号接口，以及 §§7–10 的实际仪器、记录权限、既有精确事实和未决近似义务。

C 指《AURIC FIB：零保真缺陷下的严格正经典恢复间隙》，固定 UTF-8 内容的 SHA256 为 `d072e0b54577a2d44e107b43c006f190e4f2bfde690b4bc0dfee09e162271a7f`。其三态经典最小值与传输响应证书是独立的既有输入，不因本文扩大解码器输入类型而扩大适用范围。

原文献的以下身份与定位仅按 S 的引用使用，不附加外部真实性或文献查全认证：Nuradha、Mishra、Leditzky、Wilde，*Multivariate Fidelities*，arXiv:2404.16101v3，Proposition 3.1、Definition 5.40、Proposition 5.44，承担根保真测量表示与共同测量比较；Fuchs、Caves，*Mathematical Techniques for Quantum Communication Theory*，arXiv:quant-ph/9604001v1，§2、式 (7)、(18)–(24)，承担成对最优测量及效应本征空间接口；Gregoratti、Werner，*Quantum Lost and Found*，arXiv:quant-ph/0209025v1，Proposition 2、式 (7)，以及 Knill、Laflamme，*A Theory of Quantum Error-Correcting Codes*，arXiv:quant-ph/9604034v1，Theorem 3.2、式 (19)–(20)，承担标准纠错归属。S 所引 REC 是固定修订 `9ebc22c28bd51d31eafacb9320f91e96df4e6275` 中的 `docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md`；本文关于表中词计数与前缀寄存器事实的来源止于 S 对它的明确转述。

Choi 参数化、Kraus 与 Stinespring 表示、Schwarz 等号、乘法域与忠实不变泛函、纯 Choi 极端性、迹范数收缩均为标准工具。定理 3.1 的实际支撑和条件输出推导、传输块上的平方和证明、实际联合态反例及各目标空间的精确接合，是相对于上述源接口的综合推导；不能据此将一般无广播、统计充分性或通用纠错事实称为新发现。所有证明保持普通条件数学的证据层级，不是形式核、执行、外部来源认证或世界优先权证书。

## 追加锚（本行以下为增补区）
