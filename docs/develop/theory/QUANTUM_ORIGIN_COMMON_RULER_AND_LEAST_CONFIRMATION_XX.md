# 量子起源 XX：共同圆尺与最小确认

## 270. 支撑内三标签、实际矩形与任意原维数的共同圆尺

**定义 270.1（完整强背景中的一个关系条件）。** 本节完整保留250.1：原 $V$ 是任意有限实空间，$\dim_{\mathbb R}V>1$；每个有限 $N\ge0$ 的整个载体为 $W_N=V^{\otimes_{\mathbb R}N}$，有闭尖生成锥 $C_N$、严格正乘积单位 $u_N$、整个紧底 $K_N$、全部原纯点 $P_N$、完整正对偶与效应区间 $[0,u_N]$ 和全部有限单位分解。零层为标量正锥，原乘积配对分离全部联合空间，规范重括号为恒等，全部位置置换及其逆、单位丢弃均正；每个有限分块 $a|b$ 均满足(250.1)的完整最小／最大界，包括任意原相关输入。记 $H_d=\operatorname{Herm}_d(\mathbb C)$；$P_v=vv^*/\|v\|^2$，$\mathcal D(S)$、$\operatorname{PSD}(S)$ 分别为复支持 $S$ 上的整个密度体与正锥。

唯一附加关系条件记为 $\mathsf R_3$：在**整个原 $K_3$** 上，存在一个正定实对称型 $g_3$ 于 $\ker u_3$，使每对不同 $p,q\in P_3$ 的整个最小实际面满足

$$
B_3(p,q)=c_{pq}+\{v\in D_{pq}:g_3(v,v)\le r_{pq}^2\},\qquad
\dim D_{pq}=3,\quad r_{pq}>0,
\tag{270.1}
$$

且 $P_3\cap B_3(p,q)$ 恰为其整个球面。这就是实际 L2 加存在一把共同圆尺 $\mathsf A_2$；量词包括全部纠缠纯点，中心和半径可逐球改变。不另加 TC、TF9、NC、ZP、FI、谱性、正面投影、标准 $C_1,C_2$、共同半径、物理旋转或任意面效应的全局正延拓。几何只在原三物理复制上要求，附加正资源则使用未截断的全有限背景。

下文240、250、253编号均指[XVIII][F270]，260编号均指[XIX260][S270]。本节的普通条件供应为260.2的完整 qubit 层级、260.5—260.6的整个实际 $2\times b$ 分类、240.2与240.5的实际面接口、XIII160.4的 TC 商、XIII161.3中分类后的产品正规形，以及XIII164.11的精确全有限尾部；各供应只按其明示前件使用。260.2的原局部维数四限制保留：它只应用于下面诱导出的四维实际二元支持，不应用于整个未知 $V$。这里扩展的是260以外的任意原维数，不改动260的限定命题，也不把253的 CB、ZP、FI 当作本候选的输入。

**引理 270.2（实际支持、内禀双界与局部 qubit 资源）。** $\mathsf R_3$ 下，原 $K_1,K_2$ 继承实际 L2 和正定共同尺。每个原实际二点面 $B\subset K_1$ 的 $S_B=\operatorname{span}_{\mathbb R}\operatorname{cone}B$ 为四维；令

$$
C_N^B=C_N\cap S_B^{\otimes N},\qquad u_N^B=u_N|_{S_B^{\otimes N}}.
\tag{270.2}
$$

这些整个支持锥组成满足260.1的完整强全有限四维层级，故260.2给其同一局部 qubit 坐标下的全部有限 PSD。更一般地，已经识别的任意两个实际支持块继承其**内禀**最小／最大界；总物理复制数不超过三时也继承原共同尺与 L2。

证明。由最大界及闭锥双极性，对 $z\in C_{a+b}$、$f\in C_a^*$，条件态 $(f\otimes\operatorname{id})z\in C_b$。若 $z\in K_{a+b}$ 的第二边缘为纯 $p$，则每个 $0\le f\le u_a$ 的条件态满足 $0\le(f\otimes\operatorname{id})z\le p$，因而是 $p$ 的非负倍数。完整效应张成 $W_a^*$，产品配对分离，遂有 $z=x\otimes p$。极边缘的逆像是实际面；反向由最小界给出。因此 $K_a\otimes p$ 是整个实际纯旁观面，产品纯点是原纯点。沿这一个面嵌入拉回 $g_3$，依次得到正定 $g_2,g_1$；面内生成面就是原生成面，故 L2 与圆度下降。

对 $z\in C_N$，要求每条单腿边缘位于 $\operatorname{cone}B$。以其余腿的任意 proper 效应条件化，该腿条件态被其边缘支配，故仍在这个面锥。其余腿的正泛函张成完整对偶，遂使 $z$ 在该腿上属于 $S_B$；对各腿重复得 $z\in S_B^{\otimes N}$。反向，载体已在该张量支撑内的正态，其正边缘属于 $C_1\cap S_B=\operatorname{cone}B$。所以(270.2)恰是这些实际边缘面的共同逆像，是整个实际面锥。纯产品实张成载体，故它生成；闭尖性、严格正单位、置换及丢弃全部限制下来。

在任意支持载体 $L$ 上，有限维双极性给

$$
(C\cap L)^*_{L}=\overline{\operatorname{res}_{L}C^*}.
\tag{270.3}
$$

原正简单张量给内禀最小界；对两块内禀正泛函，分别用(270.3)中的原正限制序列逼近，在支持输入上取配对极限，给内禀最大界。这里不要求逼近序列保持同一个 proper 预算，也不声称每个面效应有同预算全局延拓。支持层级的三复制底是原 $K_3$ 的实际面，故继承全部实际二点球和正定限制尺。$B$ 为三球，$\dim S_B=4$，恰好支付260.2的原维数前件。两个不同支持或不等物理块的边缘面用同一条件态支配与对偶闭包论证即可；只有其总复制数不超过三时才调用原几何。$\square$

**引理 270.3（只在已知支持测试的 Bell 压缩）。** 设标签块占 $k$ 个原物理复制，$D$ 是该块中的标准实际面，$E\subset D$ 是复二维支持。假设整个实际 $D\otimes E$ 与 $E\otimes E$ 支持面在相容坐标中标准。对任意 $r$ 复制的旁观块 $R$ 和任意 $Z\in C_{r+k}$，只要标签边缘 $\rho_D$ 支持于 $D$，则标签上的代数压缩

$$
\mathcal Q_E:\ X\longmapsto P_EXP_E
\tag{270.4}
$$

连同恒等旁观者，输出原正态，且质量满足

$$
u_{r+k}(\operatorname{id}_R\otimes\mathcal Q_E)Z
=\operatorname{Tr}(P_E\rho_D)\le\operatorname{Tr}\rho_D=u_{r+k}(Z).
\tag{270.5}
$$

任意支持内 $0\preceq A\preceq I_D$ 的标签单腿读出，也在该支持限制域上给正、迹不增的原旁观输出；所有这些陈述包含任意额外相关原旁观者。

证明。附加 $E_aE_b$ 上的归一 Bell 态 $P_\Omega$，$\Omega=(|00\rangle+|11\rangle)/\sqrt2$；只在已知实际支持 $D E_a$ 上取 Bell 投影 $H=P_\Omega$，在 $D\ominus E$ 块为零。这里 $H$ 是该支持上的 proper 效应，不给它任何环境延拓。

令 $R'=R E_b$ 为**整个保留旁观者**，包括保留 Bell 半边，取任意 $0\le f\le u_{R'}$ 的原效应。全有限原最大界给被收缩块 $D E_a$ 上的条件态 $\sigma_f$，并给原序中的支配

$$
0\le\sigma_f\le (u_{R'}\otimes\operatorname{id}_{D E_a})(Z\otimes P_\Omega)
=\rho_D\otimes I_E/2.
\tag{270.6}
$$

其边缘被支持边缘支配，故引理270.2把它放进**整个**实际 $D\otimes E$ 面；该面已知标准，所以 $0\le\operatorname{Tr}(H\sigma_f)$。对每个正原泛函，先以严格正单位缩放进 proper 区间即可使用此结论。完整 $C_{R'}^*$ 的测试及双极性因此将收缩输出放进原 $C_{r+k}$，不是仅把它放进产品最大锥。

在参考、输出 Bell 同一基的线性张量坐标中，直接收缩矩阵单位给

$$
(\operatorname{id}_{R E_b}\otimes H)(Z\otimes P_\Omega)
=\tfrac14(\operatorname{id}_R\otimes\mathcal Q_E)Z.
\tag{270.7}
$$

未乘四的 Bell 分支质量为 $\tfrac14\operatorname{Tr}(P_E\rho_D)\le u_{r+k}(Z)/4$；其补读出 $I-H$ 同样在支持内为正。乘四只用于锥正性；最终压缩的迹由其原边缘直接计算为(270.5)，故确为 TNI。没有把 Bell 分支乘四后的事件成功率假定为原事件；结论是支持域上代数压缩的正性和单位预算。单腿标签读出则对每个原旁观泛函先取 $D$ 上正条件态，再与 $A,I_D-A$ 配对，分别给输出和补输出的正性。

当 $D$ 取自一个局部 qubit 的两复制支持时，$k=2$，$D\otimes E$ 和 Bell 资源由引理270.2的完整 qubit 层级供应。对一复制目标 $r=1$，几何域为 $r+k=3$，但上述同时附加两标签半边的正资源可暂占 $r+3k=7$ 个物理复制；这只使用全有限正性，未对 $K_7$ 或 $K_4$ 加几何。未来 $r=2,k=1$ 的应用须先取得一复制实际 qutrit 及其 $D\otimes E$ 标准性。$\square$

**引理 270.4（最小平均面、三个标签与九维计数）。** 设目标块占 $r$ 份，标签块占 $k$ 份，$r+k\le3$。设 $D$ 含三个正交标签 $e_i=P_{|i\rangle}$，$i=1,2,3$，并满足引理270.3对每个二维标签支持的资源前件。对任意目标外三角，即不同纯点 $p_1,p_2,p_3$ 并非同处一个实际二点球，令

$$
z_i=p_i\otimes e_i,\qquad F=F_{r+k}(z_1,z_2,z_3),\qquad
\sigma=\tfrac13(z_1+z_2+z_3).
\tag{270.8}
$$

则 $\sigma\in\operatorname{ri}F$，每个 $X\in\operatorname{cone}F$ 被某个 $t\sum_i z_i$ 支配；$F$ 的齐次实维数恰为九，且 $F$ 本身为完整 qutrit 面。

证明。包含 $\sigma$ 的任意实际面，由三个严格正权重必须包含每个 $z_i$；反之含三点的面含平均。因此 $F=F(\sigma)$。有限维点的最小面可显式写成

$$
F(\sigma)=\{y\in K:\ \sigma=\lambda y+(1-\lambda)w
\text{ 对某 }w\in K,\ 0<\lambda<1\}.
\tag{270.9}
$$

右端是含 $\sigma$ 的面：凸性通过减小各自正系数取得共同系数；若其中一点在一条开线段上，代入表示即把两端也收入该集合。取其仿射张成中的有限仿射基点，分别反向延长至仍在 $K$ 的点；这些有限线段的凸包在 $\sigma$ 周围含一个相对邻域。因此 $\sigma\in\operatorname{ri}F$。任意 $y\in F$ 由反向延长得 $\sigma+\varepsilon(\sigma-y)\in F$，于是 $y\le(1+\varepsilon)\sigma/\varepsilon$；齐次化给所述支配。这不是任意大面中平均的相对内部主张。

标签边缘支持在 $\operatorname{span}_{\mathbb C}\{|1\rangle,|2\rangle,|3\rangle\}$，由条件支配，整个 $X$ 的载体在 $W_r\otimes H_3$。对标签 $E_{ij}=\operatorname{span}_{\mathbb C}\{|i\rangle,|j\rangle\}$ 作(270.4)，给

$$
0\le X^{ij}:=(\operatorname{id}\otimes\mathcal Q_{E_{ij}})X
\le t(z_i+z_j),\qquad X^{ij}\in\operatorname{cone}B(z_i,z_j).
\tag{270.10}
$$

后一个结论是实际面的序遗传性。单标签读出同样使 $X_{ii}$ 为 $p_i$ 的非负倍数。每个四维齐次球支撑 $\operatorname{span}B(z_i,z_j)$ 包含两个独立对角方向 $z_i,z_j$；投到其交叉块的像至多二维。因此 $X$ 的三个对角块总共至多三维，每条边的交叉块至多二维，给

$$
\dim_{\mathbb R}\operatorname{span}F\le3+2+2+2=9.
\tag{270.11}
$$

计数先对正 $X$ 作出，再由正锥张成延拓；没有把非正交叉块误称为一个正态。

还需三个 $z_i$ 的实际外部性。$\mathcal D(E_{12})$ 是标准标签 $D$ 的实际面，面传递性使它也是整个原标签底的实际面。标签边缘正映射的该面逆像包含 $z_1,z_2$ 却不含 $z_3$，所以最小实际 $B(z_1,z_2)$ 排除 $z_3$。任何含三点的二点球若含 $B(z_1,z_2)$，因三球严格凸而必须就是它，亦不可能。这个论证只用一个**实际面逆像**，不延拓标签效应。

现在仅把 $F$ 自身视作240.1的原域，单位及完整效应取其内禀值。它是紧实际面，继承所有实际 L2；在其九维齐次载体中任意三点面当然满足全称 TF9。240.2先给这个外三角仿射维数至少八，(270.11)给至多八；240.5遂给整个 $F$ 的保迹序同构

$$
\Phi:H_3\overset\sim\longrightarrow\operatorname{span}F,
\qquad \Phi(\mathcal D_3)=F.
\tag{270.12}
$$

不对环境目标或原 $K_3$ 断言 TF9。$\square$

**引理 270.5（三标签去标的边忠实性与严格正质量）。** 在270.4中，可选择(270.12)使 $\Phi(P_i)=z_i$。取标签 $|+\rangle=(|1\rangle+|2\rangle+|3\rangle)/\sqrt3$ 的支持内读出，定义

$$
h=(\operatorname{id}\otimes\langle+|\,\cdot\,|+\rangle)\Phi:H_3\to W_r,
\qquad T=h^*u_r.
\tag{270.13}
$$

则 $h\ge0$、$h(P_i)=p_i/3$，每个坐标二维支持的像锥恰为整个 $\operatorname{cone}B_r(p_i,p_j)$，限制为线性序同构；并且 $T\succ0$。

证明。标签对角读出在 $F$ 上是内禀 proper 效应 $m_i$，$\sum_i m_i=u_F$。在(270.12)下，三个 $z_j$ 的纯提升 $w_j$ 满足 $w_j^*(\Phi^*m_i)w_j=\delta_{ij}$。正收缩的期望为一或零分别迫使 $(\Phi^*m_i)w_i=w_i$、$(\Phi^*m_i)w_j=0$；自伴性使 $w_i\perp w_j$。它们构成 qutrit 正交基，故可取 $w_i=|i\rangle$。这里先由内禀 POVM 证明正交性，才称其为坐标轴。

$\Phi\mathcal D(E_{ij})=B(z_i,z_j)$。目标实际二元支持 $B_r(p_i,p_j)$ 与标签二元支持 $E_{ij}$ 的整个联合边缘面占至多三物理份；引理270.2给内禀 min/max 和圆度，260.5分类它为标准或单因子部分转置。标准分支中 $z_i,z_j$ 对应 $v_i\otimes|i\rangle,v_j\otimes|j\rangle$，两个目标向量 $v_i,v_j$ 独立。去标把其跨度合同地送到 $v_i/\sqrt3,v_j/\sqrt3$，所以给到整个目标实际二元锥的序同构。部分转置分支可选在标签因子；标签基与 $|+\rangle$ 均实，故其读出相同，结论仍成立。没有假定这些各边的 qubit 坐标已全局同步。

$h\ge0$ 给 $T\succeq0$。对每个完整原 $0\le f\le u_r$，有 $0\preceq h^*f\preceq T$，所以 $\ker T\subseteq\ker(h^*f)$。proper 效应实张成 $W_r^*$，于是对所有 $X\in H_3$，

$$
h(X)=h(P_TXP_T),\qquad P_T=\text{支持 }T\text{ 的正交投影}.
\tag{270.14}
$$

令 $\bar h$ 为 $h$ 在 $\operatorname{Herm}(\operatorname{supp}T)$ 上的限制。边像四维排除 $\operatorname{rank}T\le1$。若 $\operatorname{rank}T=2$，对每个坐标边令 $A_{ij}=P_T|_{E_{ij}}$。若 $\operatorname{rank}A_{ij}\le1$，则 $h(H(E_{ij}))=\bar h(A_{ij}H(E_{ij})A_{ij}^*)$ 至多一维，与边忠实性矛盾。所以 $A_{ij}$ 是二维间的可逆映射，进而

$$
h(\operatorname{PSD}_3)=\bar h(\operatorname{PSD}(\operatorname{supp}T))
=h(\operatorname{PSD}(E_{ij}))=\operatorname{cone}B_r(p_i,p_j).
\tag{270.15}
$$

第三点 $p_k$ 也在左侧，违反目标外三角。故 $\operatorname{rank}T=3$，即 $T\succ0$。$\square$

**命题 270.6（全部纯像、任意直线与目标 TC）。** 270.5的

$$
G(X)=h(T^{-1/2}XT^{-1/2})
\tag{270.16}
$$

为正、迹保持且线性单射；全部源秩一态映为原纯点，任意源复二维支持忠实地满到对应的整个实际二元球。因此目标块满足每个外三角的 TC；不要求 $G(\mathcal D_3)$ 等于目标外三角的整个实际面。

证明。先对 $h$ 证明秩一非零纯像。质量为 $\psi^*T\psi>0$。源向量只有一或两个非零坐标时由270.5的轴与边直接成立；三坐标皆非零时，令 $\chi_{ij}=\psi_i|i\rangle+\psi_j|j\rangle$，令 $q_{ij}$ 为 $h(\chi_{ij}\chi_{ij}^*)$ 的归一化纯像。每个 $q_{ij}\in B_r(p_i,p_j)$，与外部 $p_k$ 不同；由 $\psi=\chi_{ij}+\psi_k|k\rangle$ 得某个有限 $c>0$ 的源序支配

$$
\psi\psi^*\preceq c(\chi_{ij}\chi_{ij}^*+P_k).
\tag{270.17}
$$

所以归一像 $x$ 同时属于三个实际球 $B_r(q_{12},p_3)$、$B_r(q_{13},p_2)$、$B_r(q_{23},p_1)$。若 $x$ 混合，它是每颗严格凸三球的相对内部点；实际面的相对内部相交就意味着面相同。这一颗共同球便含全部 $p_i$，矛盾。于是 $x$ 纯。正定合同置换全部源秩一射线，故 $G$ 也具有全部纯像。

考察任意源二维支持 $S$。若两个纯像 $p,q$ 不同，其源秩一矩阵之和在 $S$ 上严格正，支配 $\operatorname{PSD}(S)$ 中每个元素；正性与实际面性质使 $G\mathcal D(S)\subseteq B_r(p,q)$。在两边标准仿射球坐标中写 $s\mapsto b+As$。整个单位球面的像是原纯点，故

$$
\|b+As\|^2=1\quad(\|s\|=1),\qquad
A^{\mathsf T}b=0,\quad A^{\mathsf T}A=\lambda I_3.
\tag{270.18}
$$

非恒定给 $\lambda>0$、$\operatorname{rank}A=3$，故 $b=0,\lambda=1$；因此此支持是忠实且满的。这里非恒定性先于纯标签单射得到，未循环使用后者。

若某二维支持 $S$ 的全部纯像恒为 $p$，取 $v\notin S$ 且像为 $q\ne p$；存在这种 $q$，因为三个轴经过合同后的像仍包含外三角。对每个 $y\in S$ 的非零向量，源线 $\operatorname{span}_{\mathbb C}\{v,y\}$ 非恒定，故其像都在同一个 $B_r(p,q)$。每个源向量写成 $a v+y$，于是全部纯像都在该球，仍违反外三角。因此没有塌缩线；任意两个不同源纯射线在其共同源线上，纯标签遂全局单射。

若 $0\ne X\in\ker G$，迹保持给 $\operatorname{Tr}X=0$。源矩阵谱分解 $X=X_+-X_-$，两者迹相同且正、支持正交；三维源中至少一侧秩一。该侧的归一像是原纯点，另一侧的谱混合只能由这个同一个纯像组成；纯标签单射与正负支持正交矛盾。因此 $G$ 线性单射。这使用源矩阵谱分解，不预设原目标谱性。

$G$ 中 $p_i$ 的提升射线为 $[T^{1/2}|i\rangle]$，三者独立但一般不正交。对外三角重新记这三条提升为 $[v],[a],[b]$，取 $v$ 单位。任意 $y\in P_r\cap B_r(p_2,p_3)$ 的唯一源提升在 $\operatorname{span}_{\mathbb C}\{a,b\}$，写作 $y'=\alpha a+\beta b$。源线壳在 $P_v$ 的切方向为

$$
\{zv^*+vz^*:z\in\mathbb C(I-P_v)y'\},\qquad
(I-P_v)y'=\alpha(I-P_v)a+\beta(I-P_v)b.
\tag{270.19}
$$

因 $G$ 对每条源线都是到整个实际球的仿射同构，其线性微分把这些方向恰送到实际球切方向。因此 $\tau_{r,p_1}(y)\subseteq\tau_{r,p_1}(p_2)+\tau_{r,p_1}(p_3)$。若无外三角，TC 全称式为空；若存在，则上述证明对每个外三角独立成立。坐标为零、源任意两点像相等的潜在分支、以及非正交提升均已处理。$\square$

**推论 270.7（TC1 与端点重叠的精确范围）。** $\mathsf R_3$ 蕴含整个原 $K_1$ 的 TC。每颗共同尺圆球自身还有对称的内禀重叠：不同纯点 $p,q$ 的实际球记为 $B$，中心 $c_B$、半径 $r_B$，定义

$$
\omega_B(p,q)=\tfrac12\left(1+\frac{g(p-c_B,q-c_B)}{r_B^2}\right).
\tag{270.20}
$$

则 $\omega_B(p,q)=\omega_B(q,p)$，且 $0\le\omega_B\le1$；相等端点的值定义为一。这是同一面内交换端点的 reciprocity，排核前不把它等同于全原菜单的 minimum。

证明。取任一原实际 qubit 支持 $B$；其存在由 $\dim V>1$ 及 L2 给出。270.2在它的两复制标准 $\operatorname{PSD}_4$ 中提供三维标签支持 $D$，其全部 $D\otimes E$ 与 Bell 资源也在这个已知的完整 qubit 层级。令目标 $r=1$、标签 $k=2$，270.3—270.6遂对每个目标外三角支付 TC1；几何始终只用三份。内禀重叠的对称性与界直接来自对称内积和 Cauchy–Schwarz，不涉及任何仪器。

仅有端点 reciprocity 不足以重建：经典全有限层级 $C_N=\mathbb R_+^{d^N}$、乘积求和单位及完整菜单，$d\ge2$，其纯目标 minimum 在纯点间为 Kronecker delta，双向相等；但二点面是线段而非三球。仪器次序也不由 reciprocity 固定：对 qubit 的 $P=P_0,Q=P_+$，Lüders yes 分支满足 $\operatorname{Tr}(PQ)=1/2$，而在输入 $P$ 上 $\operatorname{Tr}(Q(PPP)Q)=1/2$、$\operatorname{Tr}(P(QPQ)P)=1/4$。这是两段不同历史，不能从交换端点推成两个仪器复合可交换。$\square$

**命题 270.8（全局商以前的实际矩形标准性）。** TC1 后精确应用XIII160.4，得到 $n\ge2$ 及同一个实线性满射

$$
\pi:H_n\to V,\quad \pi(\operatorname{PSD}_n)=C_1,\quad u\pi=\operatorname{Tr},
\tag{270.21}
$$

全部复射影纯标签与全部原纯点双射，且每个二维支持限制为到整个实际二元球的序同构。此时不假定 $\pi$ 全局单射，也不引入 $C_2$ 的矩阵商。对任意复二维 $S,T\subset\mathbb C^n$，原 $K_2$ 中两边缘分别在 $\pi\mathcal D(S)$、$\pi\mathcal D(T)$ 的整个实际面，恰为

$$
(\pi\otimes\pi)\mathcal D(S\otimes T).
\tag{270.22}
$$

证明。270.2的条件支配使该面载体恰为 $\pi(H(S))\otimes\pi(H(T))$，十六维；$\pi$ 在每个因子四维支持上单射，故此处张量坐标忠实。它继承内禀 min/max、全部实际 L2 和 $g_2$，260.5给整个面为标准或单因子部分转置 PSD4。

两个候选的定义与局部正交基无关：换基的局部酉可在全 PSD 候选内吸收；在转置候选中用共轭酉吸收。它们随 $(S,T)\in\operatorname{Gr}_2(\mathbb C^n)^2$ 连续。用固定环境转置 $t_n$ 写转置候选时准确为 $(\pi\otimes\pi)(t_n\otimes\operatorname{id})\mathcal D(\bar S\otimes T)$，所以输出仍在同一原 $S,T$ 支持内。两个候选在闭 $K_2$ 中的包含集为闭集，且覆盖这个连通参数空间。若二者同时被包含，整个实际面的二选一分类迫使一者包含另一者；十六维忠实坐标中的 Bell 部分转置负特征值 $-1/2$ 排除它。故闭覆盖不交，一个方向处处固定。

对自支持 $S=T$，诱导实际 qubit 层级由260.2标准。其 qubit 坐标与 $\pi|_{H(S)}$ 相差一个保迹序自同构，即酉或酉后全转置；同一个变换作用两份，保持标准 PSD4。因此自矩形在(270.21)的同一坐标中就是标准，连通性迫使所有矩形标准。此处没有使用全局 $\Gamma_2$、产品 Wigner 正规形或预设标准 $C_2$。$\square$

**命题 270.9（只用有限实际矩形的任意核排除）。** (270.21)必为单射。因此 $\theta=\pi^{-1}$ 在整个原一复制载体上给 $\theta(C_1)=\operatorname{PSD}_n$、$u=\operatorname{Tr}\theta$。

证明。在 $\mathcal W=H_{n^2,0}$ 上直接用**原**张量映射 $\pi\otimes\pi$ 拉回 $g_2$，定义

$$
b(X,Y)=g_2((\pi\otimes\pi)X,(\pi\otimes\pi)Y),\quad
q(X)=b(X,X)\ge0,\quad
\operatorname{rad}b=\{X:b(X,Y)=0\ (Y\in\mathcal W)\}.
\tag{270.23}
$$

若 $0\ne H\in\ker\pi$，则 $\operatorname{Tr}H=0$，且 $H\otimes H_n+H_n\otimes H\subseteq\operatorname{rad}b$。同时在每个**已知标准实际矩形内**的二维支持 $U$ 上，实际面传递性和 $\mathsf A_2(g_2)$ 给 $q(X)=\lambda_U\operatorname{Tr}(X^2)$，$X\in H_0(U)$，$\lambda_U>0$。不同支持的比例不必相等。

取 $H$ 特征基，写 $H=H_+-H_-$、$I_+=\{i:h_i>0\}$、$I_-=\{j:h_j<0\}$，$p=|I_+|,q_-=|I_-|$。换基只是把同一个 $\pi$ 预合成酉合同；270.8对全部支持成立，故保持全部已付实际矩形。令 $b_{\mathbb C}$ 为 $b$ 到 $\mathfrak{sl}_{n^2}(\mathbb C)$ 的复双线性延拓，定义真正非负的半范数

$$
\|Z\|_b^2=b_{\mathbb C}(Z,Z^*)
=q(\operatorname{Re}Z)+q(\operatorname{Im}Z)\ge0,
\quad \operatorname{Re}Z=(Z+Z^*)/2,\quad
\operatorname{Im}Z=(Z-Z^*)/(2i).
\tag{270.24}
$$

这里不把 $b_{\mathbb C}(Z,Z)$ 说成非负。取 $i,k\in I_+$、$j,l\in I_-$，置 $a=(i,k),b_0=(i,l),c_0=(j,k),d=(j,l)$，$E_{xy}=|e_x\rangle\langle e_y|$，并明确取

$$
\begin{aligned}
M_{ij}^{kl}&=b_{\mathbb C}(E_{ab_0},E_{dc_0}),&
N_{kl}^{ij}&=b_{\mathbb C}(E_{ac_0},E_{db_0}),\\
J_{ts}&=|e_a+t e_d\rangle\langle e_{b_0}+s e_{c_0}|\\
&=E_{ab_0}+sE_{ac_0}+tE_{db_0}+stE_{dc_0},&s,t&\in\{1,-1\}.
\end{aligned}
\tag{270.25}
$$

左右向量正交，均有平方范数二；其二维支持 $U_{ts}$ 在实际矩形 $\operatorname{span}\{e_i,e_j\}\otimes\operatorname{span}\{e_k,e_l\}$ 内。故其两根 Hermitian Pauli 方向 $\operatorname{Re}J_{ts},\operatorname{Im}J_{ts}$ 等长且正交，给 $b_{\mathbb C}(J_{ts},J_{ts})=0$。精确消费XVIII(220.22)—(220.24)的有限计算：

$$
\sum_{s,t=\pm1}st\,b_{\mathbb C}(J_{ts},J_{ts})
=8(M_{ij}^{kl}+N_{kl}^{ij})=0.
\tag{270.26}
$$

四次展开仅消去每个支持自身的比例，没有调用(220.19)对所有环境二维支持的前件。令 $w_{ij}=h_i|h_j|>0$。由于 $H\otimes E_{lk}$、$E_{ji}\otimes H$ 在复化根空间，两侧分别允许把配对第二项的 $H_+$ 换为 $H_-$，于是同一有限关系给

$$
\begin{aligned}
\|H_+\otimes E_{kl}\|_b^2&=\sum_{i\in I_+,j\in I_-}w_{ij}M_{ij}^{kl},\\
\|E_{ij}\otimes H_+\|_b^2&=\sum_{k\in I_+,l\in I_-}w_{kl}N_{kl}^{ij},\\
0&=\sum_{k\in I_+,l\in I_-}w_{kl}\|H_+\otimes E_{kl}\|_b^2
 +\sum_{i\in I_+,j\in I_-}w_{ij}\|E_{ij}\otimes H_+\|_b^2.
\end{aligned}
\tag{270.27}
$$

所有配对矩阵均迹零，包括含 $H_+$ 的非对角张量；零谱指标从不进入权重。所有半范数非负、权重严格正，故其每个实部与虚部都在 $\operatorname{rad}b$。这只用至多 $4(pq_-)^2$ 个明确的实际二维支持，未要求 $\ker\pi$ 一维。

特别地对 $k\in I_+,l\in I_-$，令 $S_{kl}=E_{kl}+E_{lk}$，有 $H_+\otimes S_{kl}\in\operatorname{rad}b$。但其原像

$$
(\pi\otimes\pi)(H_+\otimes S_{kl})=\pi(H_+)\otimes\pi(S_{kl})\ne0
\tag{270.28}
$$

是原 $\ker u_2$ 中非零方向：$u\pi(H_+)=\operatorname{Tr}H_+>0$，而 $\pi(S_{kl})\ne0$ 由该二维支持忠实性给出。$g_2$ 正定与根空间结论矛盾。故不存在非零 $H$，$\pi$ 单射。$\square$

**命题 270.10（先得一复制 qutrit，再得 TC2）。** 若270.9给出的 $n=2$，260.2已直接给整个原全有限结论。若 $n\ge3$，整个原 $K_2$ 满足 TC，且不需要四物理复制的几何。

证明。现在才有整个一复制 $C_1$ 的矩阵序同构，可在其中取一个标准实际 qutrit 支持 $D$。任意 $E\subset D$ 的二维支持与 $D$ 的整个实际两块面，由270.2继承 min/max 与两复制几何；260.6以 $b=3$ 分类它为标准或单因子部分转置。其 $E\otimes E$ 子矩形由270.8标准，Bell 负特征值排除转置，故 $D\otimes E$ 在同一一复制坐标中标准。

因而270.3—270.6可取 $r=2,k=1$：目标是未知的整个 $K_2$，标签是一复制 $D$；每条目标实际二元支持与一条标签边总共三份，260.5支付其边读出所需标准／PT二选一。Bell 正性调用已标准的 $D\otimes E$ 及 $E\otimes E$，任意附加资源只用全有限正性。于是每个两复制目标外三角都有 TC2。若原 $V$ 尚未排核，不能预先取这个一复制 $D$；这一步的顺序是实质前件。$\square$

**命题 270.11（全部纯产品提升、秩穷尽与完整 C2）。** 在 $n\ge3$ 分支，TC2 与XIII160.4给

$$
\Pi:H_d\twoheadrightarrow W_2,\qquad
\Pi(\operatorname{PSD}_d)=C_2,\quad u_2\Pi=\operatorname{Tr},
\tag{270.29}
$$

全部源纯标签双射到全部原纯点，每个二维支持忠实地满到实际二元球。实际上 $d=n^2$、$\Pi$ 双射，且原来的同一个 $\theta=\pi^{-1}$ 已满足

$$
\theta^{\otimes2}(C_2)=\operatorname{PSD}_{n^2}.
\tag{270.30}
$$

证明。记 $p_x=\pi(P_x)$。提升产品正交基点 $p_{e_i}\otimes p_{e_j}$ 为单位向量 $v_{ij}\in\mathbb C^d$ 的纯标签。原一复制已完整矩阵化。任意局部 proper $e,f$ 的产品由最大界为正，且 $u_2-e\otimes f=(u-e)\otimes u+e\otimes(u-f)\ge0$，所以产品基效应 $e_i\otimes e_j$ 为原 proper 效应；其 $\Pi$ 拉回是 $0\preceq A_{ij}\preceq I_d$，在相应提升上值一，其余上值零。因而 $A_{ij}v_{ij}=v_{ij}$、$A_{ij}v_{kl}=0$ 对 $(i,j)\ne(k,l)$，自伴性给 $v_{ij}\perp v_{kl}$。置

$$
L=\operatorname{span}_{\mathbb C}\{v_{ij}:0\le i,j<n\},\qquad \dim_{\mathbb C}L=n^2.
\tag{270.31}
$$

证明**全部**纯产品提升在 $L$ 内，无须选相位。固定 $j$，若 $x$ 只有一个基分量，提升已在 $\operatorname{span}_i v_{ij}$；按非零分量个数归纳，写 $x=x'+a e_i$。一复制 $p_x$ 属于实际 $B(p_{x'},p_{e_i})$，纯旁观嵌入把它送到两端产品的整个实际二元面。$\Pi$ 的二维支持忠实性和纯标签双射于是使其提升在两端提升的复线性跨度中。这归纳给全部 $p_x\otimes p_{e_j}$ 的提升在 $L$；固定任意这样的 $x$，对第二因子同样归纳，给全部 $p_x\otimes p_y$ 的提升在 $L$。用的是实际纯旁观二元面，未用乘积相位正规形。

任取两因子的局部正交基，其 $n^2$ 个产品提升都在 $L$，并由对应产品效应的同一 $0/1$ 论证构成 $L$ 的正交基。任意秩一产品效应可纳入这样一个基菜单；其拉回在该基上恰有一个值一、其余为零，正性及补正性迫使它在 $L$ 上就是该一维投影，因而约化 $L$。秩一投影实张成各局部 Hermitian 对偶，全部产品效应遂实张成整个 $W_2^*$，所以每个原泛函的 $\Pi$ 拉回都约化 $L$。

若有 $0\ne w\in L^\perp$，取 $0\ne z\in L$。$[z+w]$、$[z-w]$ 不同，且两者范数相同；所有约化 $L$ 的 Hermitian 算子对其归一秩一投影读数相同。因此所有原泛函都给相同的 $\Pi$ 像，违反全部纯标签单射。故 $L^\perp=0$，$d=n^2$；$\dim W_2=(\dim V)^2=n^4=d^2$ 与满射性遂给 $\Pi$ 双射。

此后才调用XIII161.3中(161.15)之后的**产品正规形供应**，而不调用其更强的三复制几何入口。代入类型 $(n,n;n^2)$，状态产品为 $M=\Pi^{-1}(\pi\otimes\pi)$，效应产品在逆对偶迹坐标中为 $N$。原 min/max 给两者对全部正局部输入的正性；原配对、单位给

$$
\operatorname{Tr}(M(X,Y)N(A,B))=\operatorname{Tr}(XA)\operatorname{Tr}(YB),
\qquad N(I,I)=I.
\tag{270.32}
$$

原张量坐标给单射、分离和全部实空间张成，完整局部／目标矩阵锥及维数均已支付。该条件正规形给一个固定输出酉和两个固定输入转置位；输出酉可吸收进整个目标 PSD，所以在原 $\theta\otimes\theta$ 坐标中

$$
\theta^{\otimes2}C_2=(t_n^{\epsilon_1}\otimes t_n^{\epsilon_2})\operatorname{PSD}_{n^2}.
\tag{270.33}
$$

270.8的标准自 qubit 矩形排除 $\epsilon_1\ne\epsilon_2$；相同两位是恒等或整个矩阵转置，均保 PSD，得(270.30)。这一供应源为161.3所引的 Xu–Zheng–Fošner 产品保持定理及其原配对桥，不把它算作新的分类定理。$\square$

**定理 270.12（任意原维数的完整双向候选）。** 在270.1的强全有限背景，并相对于该定义明列的普通条件供应，有

$$
\mathsf R_3\quad\Longleftrightarrow\quad
\exists n\ge2\ \exists\theta:V\overset\sim\longrightarrow H_n:
\quad \theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\quad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(\forall N\ge0).
\tag{270.34}
$$

右侧是同一原局部坐标的整个有限锥，不是逐层另选坐标或仅识别纯产品。无需把整个 $K_3$ 的 TC 另作输入。

证明。270.2—270.9先给一复制完整 PSD。$n=2$ 时引理270.2的整个原空间已为四维，直接用260.2完成。$n\ge3$ 时270.10—270.11给同一个 $\theta$ 的完整 $C_1,C_2$。

现在对原 $2|1$ 切分固定第三腿的一个标准二维支持 $E$，第一块用**整个**已分类 $C_2=\operatorname{PSD}_{n^2}$。该边缘支持面是实际面，载体恰为 $H_{n^2}\otimes H(E)$，有内禀完整 min/max、迹单位、三复制 L2 和共同尺。260.6代入 $b=n^2$（以原正置换交换两块），给整个面为标准 PSD 或 qubit 因子部分转置 PSD。固定第一条数据腿为纯态，第二数据腿和第三腿的 $E\otimes E$ 自矩形由(270.30)标准；转置分支会使该矩形为 PT，Bell 负特征值排除它。因此这个**整个不等块支持面**标准。

取第三腿 $E=\operatorname{span}\{|0\rangle,|1\rangle\}$。同一 $\theta^{\otimes3}$ 坐标中的该面含归一实际 dyad

$$
\frac{\tau_n\tau_n^*}{n+1},\qquad
\tau_n=\sum_{i=0}^{n-1}|ii0\rangle+|011\rangle
=|I_n\rangle\!\rangle|0\rangle+|E_{10}\rangle\!\rangle|1\rangle,
\quad \|\tau_n\|^2=n+1.
\tag{270.35}
$$

这里精确沿用164.2的 $|A\rangle\!\rangle=\sum_i|i\rangle\otimes A|i\rangle$，故 $E_{10}=|1\rangle\langle0|$ 的向量化是 $|01\rangle$；不存在一次额外的转置约定。锥齐次性给未归一 $\tau_n\tau_n^*\in\theta^{\otimes3}C_3$。

精确匹配XIII164.1：其 $V=H_n$ 是现有 $\theta V$，各 $W_N$ 是这个同一原实张量坐标，单位为迹，$C_1,C_2$ 标准；闭尖生成性、严格正单位、完整所有层菜单、全部有限分块 min/max、正置换与正逆及规范重括号，都原样来自270.1而随同一个 $\theta$ 运输。尚未预付任何更高层 PSD、CP 或全局控制。于是(270.35)恰为164.11第3项，直接消费其 $(3\Rightarrow4)$，得全部有限层等式。所用尾部是164.10的六种子／十八腿有限预算、164.9与VII102.10的原全旁观有限字归纳及 [H260] 的精确异维普适性；没有对这些辅助高层锥加几何，也不重证或替换它们的长证明。

反向在标准层级中取 $g_3(x,y)=\operatorname{Tr}(\theta^{\otimes3}x\,\theta^{\otimes3}y)$ 于迹零空间。两不同纯射线生成其复二维支持上的整个 $\mathcal D_2$；中心 $P_S/2$、HS 半径 $1/\sqrt2$，原纯点恰为整个球面，所以满足270.1。只断言存在此尺，不断言给定的任意正定尺都可用。$\square$

**推论 270.13（同一坐标中的完整静态与条件过程字典）。** 在270.12任一等价条件下，记 $\Theta_N=\theta^{\otimes N}$、$D_N=n^N$。以下字典是250.4、260.8及XIII161.6—161.10在参数 $d=n^a,e=n^b$ 下的整锥后应用；操作行各自保留所列前件。

| 原对象或另给前件 | 同一坐标中的完整对应 |
| --- | --- |
| 全部原归一态、纯态、凸混合 | 全部 $\rho\succeq0,\operatorname{Tr}\rho=1$；全部秩一 $P_v$、纯域 $\mathbb {CP}^{D_N-1}$；原混合就是凸混合，矩阵谱分解成为原态的正交纯态分解 |
| 全部原效应、配对、有限单位分解 | 全部 $0\preceq E\preceq I$；$e_E(x)=\operatorname{Tr}(E\Theta_Nx)$；所有有限 POVM $\{E_j\}$，$\sum_jE_j=I$；PVM 为正交投影的单位分解；$p_j=\operatorname{Tr}(E_j\rho)$ |
| 全部纯目标确认者及对任意混输入的 minimum | $E=P_v+B$，$B=(I-P_v)B(I-P_v)$、$0\preceq B\preceq I-P_v$；最小确认效应 $P_v$，$T_{N,p_v}(x)=\operatorname{Tr}(P_v\Theta_Nx)$；零邻面为 $\mathcal D(v^\perp)$ |
| 实际面和纯几何 | 支持面 $\mathcal D(S)$；二支持球与三支持 qutrit；$|v^*w|^2$ 为重叠，HS 距离平方 $2(1-|v^*w|^2)$，通常 Fubini–Study 距离 $\arccos|v^*w|$ |
| 原产品、所有有限联合态、置换、重括号与丢弃 | 标准复 Hilbert 张量积上的整个联合 PSD；迹配对、交换和偏迹；纯纠缠为给定切分的 Schmidt 秩大于一，混态可分体为产品密度体凸包 |
| 实线性 $L:W_a\to W_b$，另要求每个有限 $M\ge0$ 上的整个原输入满足 $L\otimes\operatorname{id}_{W_M}\ge0$ | $\Phi=\Theta_bL\Theta_a^{-1}$ 的唯一复线性延拓为 CP，等价于 $J(\Phi)\succeq0$ 及有限矩形 Kraus 和 $\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*$ |
| 上行再要求所有正输入上 $u_bL\le u_a$ 或等号 | 分别为 TNI 或 TP，$\sum_\alpha K_\alpha^*K_\alpha\preceq I$ 或 $=I$；这是整输入预算，不是 Choi 总迹预算 |
| 有限分支 $L_j$ 各全旁观正，另有总预算 $u_b\sum_jL_j=u_a$ | 数学仪器；$\rho_j=\Phi_j(\rho)$、$p_j=\operatorname{Tr}\rho_j$，仅 $p_j>0$ 时条件态为 $\rho_j/p_j$；各支 TNI 不能替代总和预算 |
| 同层正分支具有投影效应 $A$，且在整个 certain-yes 支持的每个纯态逐点中性 | 唯一锐更新 $\Phi(X)=AXA$；投影效应或可重复性本身不代付逐点中性 |
| 另给同层连续可逆、保锥保单位实一参数群 | 酉共轭动力学 $\dot\rho=-i[H_{\rm gen},\rho]$，纯态择相位后 $i\dot\psi=H_{\rm gen}\psi$；生成元可加标量 |
| 数学菜单的实际设备实现、物理时间或无限／近似极限 | 事件饱和、记录、接线和仪器实现另给；实际钟、能量及 $H_{\rm phys}=\hbar H_{\rm gen}$ 另标定；无限系统的连接映射、相容态、完备化和 normal 延拓，以及近似稳定性、范数、误差和资源界均须自己的前件 |

证明。整锥和单位的双射，其逆对偶给完整原菜单，故 Born 式是原配对的精确坐标式。正收缩在 $v$ 上期望一迫使 $Ev=v$，给确认者分块；取 $B=0$ 同时达到所有混输入的 minimum，NC 与完整正交零邻在此成为结论。静态条目不使用任意面效应的环境延拓。

过程条目使用XIII161.7、161.7.1、161.9—161.10的整锥后证明，参数恰为 $d=n^a,e=n^b$；$n\ge2$ 的辅助幂可容纳任意有限辅助维数，标准嵌入及压缩给通常 CP，反向由 Kraus 和保全部 PSD 输入。单系统正性不足以支付这个量词。相关旁观输入的分支为 $(\operatorname{id}\otimes\Phi_j)(Z)$，仍以整个输出迹给概率；正输出迹零就为零，不指定其归一态。总仪器预算为 $\sum_{j,\alpha}K_{j,\alpha}^*K_{j,\alpha}=I$。逐点锐中性才调用161.7.1；指定连续群才调用161.10，静态尺不选实际 Hamiltonian 或时间单位。数学正映射、原全旁观正性和设备可实现性保持各自的量词。$\square$

**命题 270.14（普通条件综合的来源、范围与图景）。** 270.3—270.6的支持内三标签拼接，以及270.8—270.12在实际矩形和全有限尾部间的综合，是此处的 repo-derived 普通推导。有限维最小面与相对内部、闭锥双极性、正矩阵零块、Grassmannian 连通性和谱分解是成熟工具。小面分类精确消费[240.2、240.5][F270]及[XIX260][S270]；TC 到统一商消费[XIII160.4][T270]及其中 [SV160, Theorem 2.4] 的 Hermitian Veronesean cap 分类，未独立宣称新的 cap 分类。四矩形只消费[F270的(220.22)—(220.24)][F270]，其实际拥有卷为XVIII。分类后的产品正规形来自XIII161.3所引用的 [P270]，精确有限传播来自XIII164.11及其原列文献；[H260] 的 Harrow 推论2属于成熟文献工具。这些纸面供应均保留条件含义，本节的结论始终是相对于所列供应的普通条件数学，不申领全球文献优先性或形式化认证。

证明与图景。先在一个真实两态面中取得完整 qubit 资源，把三种目标准备各挂一盏正交标签灯。所有 Bell 测试只照已知实际标签支撑，并对连保留 Bell 半边在内的整个旁观者测试，所以擦掉标签时不会借用不存在的全局正效应。三盏灯的对角块只有三维，三条边各只有两个相干方向，最小面因此只有 qutrit 的九个齐次方向。去标后的一个混合像若同时躲进三颗实际球的内部，会迫使三颗球成为同一个面并吞掉外部第三点；这使全部纯线保持纯且忠实，支付切方向闭合。

矩形随后把未知大空间的核变成一个非零 Pauli 方向的零长度：四个带符号式给系数八，正权半范数和只能逐项为零，而原共同尺不容许非零方向零长。先排一复制核，才取得一复制 qutrit 作两复制目标的标签；再用全部纯产品提升和全部产品效应穷尽整个两复制体。最后只在三份内取得明确相干线 $\tau_n$，把它交给已有的精确全有限传播；共同的原局部坐标遂贯穿所有有限复制。

因此本节将260的原维数四范围扩展到任意有限原维数 $>1$，但始终继承250.1的强全有限背景，并相对于明确列出的普通条件供应。它不以ZP证明TC，不以253的维数选择替代矩形排核，不宣称全局最少公理或无条件物理实现。端点交换只是同一关系的对称；两个有序仪器的状态更新仍有各自前件。$\square$

[S270]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "XIX260：原四维局部系统的共同圆尺与乘积零面重建。"
[H260]: https://arxiv.org/abs/0806.0631v1 "Harrow, Exact universality from any entangling gate without inverses, Corollary 2：含不等分组维数的精确有限生成，非仅稠密。"
[F270]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "XVIII240.1—240.5、250.1与250.4；220.22—220.24的有限四矩形关系。"
[T270]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "XIII160.4的TC商；161.3分类后的产品正规形；164.1、164.10—164.11；161.6—161.10的条件字典。"
[P270]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/Library/QuantumStates/barnumhilgert2019spectral.md "Conditional normal-form theorem and proof：Xu–Zheng–Fošner 产品保持供应；此处仅在整层矩阵分类后使用。"

## 追加锚（本行以下为增补区）

## 271. 原 proper 最小确认的迹二桥与整个 qubit 分支

**定义 271.1（原菜单中的最小确认与实际二元球）。** 设 $A$ 为有限维实空间，$C\subset A$ 为闭、尖、生成凸锥，$u$ 在 $C\setminus\{0\}$ 严格正。始终使用整个紧底 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$、完整正对偶 $C^*$ 和完整 proper 区间 $\mathcal E=[0,u]_{C^*}$。两个效应的大小指其差属于这个**原正对偶**。条件 $\mathsf M$ 是：每个 $p\in P$ 有

$$
e_p\in\mathcal E,\qquad e_p(p)=1,\qquad
 e_p\le f\quad(f\in\mathcal E,\ f(p)=1).
\tag{271.1}
$$

等价地，对每个原纯目标 $p$，

$$
T_p(x)=\inf\{f(x):f\in\mathcal E,\ f(p)=1\}
\tag{271.2}
$$

在**全部原归一混合**上仿射。这里的 infimum 只在完整原 proper 菜单中取，不改成全部非负仿射函数，也不限制为某个选定子菜单。这个等价是 [M271]“An intrinsic binary comparison and its consistency condition”的接口：least 效应实现整个 infimum；反向，仿射的 $T_p$ 取值于 $[0,1]$，在 $p$ 取一，齐次延拓就是低于每个确认者的 proper 效应。不要求 $e_p$ 只在 $p$ 取一，也不输入数值互易。

实际 L2 指每对不同原纯点 $p,q$ 的**整个最小实际面** $B(p,q)=F_K(p,q)$ 仿射同构于非退化闭三球，且 $P\cap B(p,q)$ 恰为其整个球面，含义同 [XVIII240.1][G271]。没有共同尺、共同半径、一般暴露性、正面回缩或一般面效应延拓的附加前提。

矩阵部分以实迹配对 $\langle X,Y\rangle=\operatorname{Tr}(XY)$ 识别 $H_d=\operatorname{Herm}_d(\mathbb C)$ 与其对偶。$\|X\|_2=\sqrt{\operatorname{Tr}(X^2)}$ 始终为 Hilbert–Schmidt 范数；$P_v=vv^*/\|v\|^2$。$\operatorname{Sep}(m|n)$ 是全部正产品矩阵的凸锥，$\operatorname{BP}(m|n)=\operatorname{Sep}(m|n)^*$；其元素的每个产品向量期望非负，不预设为 PSD。$T_1$ 是固定第一因子基下的部分转置。原效应矩阵 $E$ 的读数写成 $E(X)=\operatorname{Tr}(EX)$，故矩阵单位为 $I$。

**定理 271.2（任意有限 $2\times b$ 的整锥分类）。** 对每个整数 $b\ge2$，设整个原载体就是

$$
A=H_2\otimes_{\mathbb R}H_b
 =\operatorname{Herm}(\mathbb C^2\otimes\mathbb C^b),
\qquad u=\operatorname{Tr},
\qquad
\operatorname{Sep}(2|b)\subseteq C\subseteq\operatorname{BP}(2|b).
\tag{271.3}
$$

$C$ 闭、尖、生成，原菜单为271.1的完整菜单。若整个原 $K$ 满足 $\mathsf M$ 和实际 L2，则在这个原坐标中

$$
\boxed{\ C=C^*=\operatorname{PSD}_{2b}
\quad\text{或}\quad
C=C^*=T_1\operatorname{PSD}_{2b}.\ }
\tag{271.4}
$$

两种整锥都满足这些前提。特别地，这不是对一个选定态族、某个压缩体或仅 Schmidt 秩二资源的分类；结论穷尽全部原态、纯点和原效应。证明不使用共同尺，也不使用260或270的分类作为前提。

证明。先在本证明内注明所消费的成熟供应。[M271]“Positive dual generation and one common complete frame”只用 proper leastness 导出正对偶剥离和完整 frame 扩张；数值互易用于该笔记后面的其他结论，此处不消费。实际 L2 的外三角齐次维数至少九，取 [XVIII240.2][G271]，不取带共同尺的低维分类。外部矩阵预算取 [GB271, Theorem 1]。以下分别给出这些供应在原菜单中的确切用法，以及新的迹二接合。

（一）原暴露面的 least 最大测试。由上述 M-only frame 供应，对任何 $f\in\mathcal E$，可在一个实际完整 frame 上写成

$$
f=\sum_i\lambda_i e_{p_i},\qquad
 e_{p_i}(p_j)=\delta_{ij},\qquad
 \sum_i e_{p_i}=u,\qquad 0\le\lambda_i\le1.
\tag{271.5}
$$

最后的系数界由 $\lambda_i=f(p_i)$ 得到。此处的 frame 是一个共同单位分解，不是分别选择的两两测试。为明确所用前件，leastness 先给 reciprocal zeros：$e_p(q)=0$ 时 $u-e_p$ 确认 $q$，故 $e_q\le u-e_p$，于是 $e_q(p)=0$；反向同理。对非零正泛函，取纯最大点，按最大值倍数减去其 least 效应，得到仍为正的残余。各次新纯点与此前纯点双向为零，故线性独立，有限维性使剥离终止。把所得正交族补全时，非零残余 $u-\sum_i e_{p_i}$ 的纯最大点与旧点正交，在该点残余恰取一；再减去其 least 效应。有限终止给(271.5)。这正是 [M271] 的剥离／补全证明，并未增加 $e_p(q)=e_q(p)$ 的非零读数条件。

设 $H=\{x\in K:f(x)=1\}\ne\varnothing$ 为一个原暴露面。置

$$
h_H=\sum_{\lambda_i=1}e_{p_i}.
\tag{271.6}
$$

所有 frame 读数非负且和为一，所以 $f(x)=1$ 当且仅当每个 $\lambda_i<1$ 的项在 $x$ 上为零，也当且仅当 $h_H(x)=1$。若 $g\in\mathcal E$ 在 $H$ 上恒为一，则它确认所有 $\lambda_i=1$ 的 $p_i$。按这些下标逐个减去 $e_{p_i}$：leastness 保证差为正；差不超过 $g\le u$，且因交叉读数为零仍确认下一个 $p_i$。所以

$$
\{h_H=1\}=H,\qquad h_H\le g
 \quad(g\in\mathcal E,\ g|_H=1).
\tag{271.7}
$$

这同时证明 $h_H$ 与所选展开无关。它还是 $\mathcal E$ 的极点：若 $h_H=(g_1+g_2)/2$，两个 proper 效应在 $H$ 上都取一，由(271.7)均不小于 $h_H$，故均等于它。

对每个原纯 $p\in H$，$e_p\le h_H$，因此 $d=h_H-e_p$ proper。它也是 $\mathcal E$ 的极点。事实上，若 $d=(d_1+d_2)/2$ 且 $d_i$ proper，则 $d_i(p)=0$；$u-d_i$ 确认 $p$，于是 $e_p\le u-d_i$。所以 $e_p+d_i$ 都 proper，其平均为极端 $h_H$，迫使 $d_1=d_2=d$。这里极端效应减法的论证保留了原全域上下预算，没有把面内效应当成全域效应。

（二）两份原锥的 HS／迹预算与产品端点。对(271.3)取对偶得

$$
\operatorname{Sep}(2|b)\subseteq C^*\subseteq\operatorname{BP}(2|b).
\tag{271.8}
$$

[GB271, Theorem 1] 在任意有限复 $m\times n$ 二体系统断言：Hermitian $\Delta$ 满足 $\|\Delta\|_2\le1$ 时，$I+\Delta$ 可分，包含等号。对非零 $W\in\operatorname{BP}(m|n)$，令 $\Delta=-W/\|W\|_2$，与 $W$ 配对得

$$
0\le\operatorname{Tr}\!\left[W\left(I-\frac W{\|W\|_2}\right)\right]
=\operatorname{Tr}W-\|W\|_2,
\qquad
\boxed{\ \|W\|_2\le\operatorname{Tr}W.\ }
\tag{271.9}
$$

零矩阵也满足此式。原态与原正效应都属于 BP，所以此预算对两者同时成立；正元素迹为零必为零。这是 HS 范数对普通迹的界，绝不是块正矩阵的核迹范数界。GB 的归一化可分球半径 $1/\sqrt{D(D-1)}$、$D=mn$，与此处单位矩阵周围的未归一半径一是不同表述。

对任意原纯 $x$ 及其 $e_x$，有 $\operatorname{Tr}x=1$，因此

$$
1=\operatorname{Tr}(e_xx)
 \le\|e_x\|_2\|x\|_2
 \le\operatorname{Tr}e_x.
\tag{271.10}
$$

若 $\operatorname{Tr}e_x=1$，Cauchy–Schwarz 及(271.9)全取等号；两者迹都为一，故

$$
e_x=x,\qquad \|x\|_2=1.
\tag{271.11}
$$

这里是条件推论，尚未假定未知原纯态为 PSD。

每个单位产品投影 $p=P_a\otimes P_b$ 都属于 $C$，且 $\operatorname{Tr}p=\|p\|_2=1$。整个 $K$ 由(271.9)包含于 HS 单位球；严格凸性使 $p$ 成为原纯点：若它是两个 $K$ 中点的非平凡凸平均，HS 范数等号迫使两点都等于 $p$。此外 $p$ 和 $I-p$ 都可分，后者可用含 $a,b$ 的产品正交基展开。所以 $p$ 是原 proper 效应。M 给 $e_p\le p$；由(271.9)的正差预算与(271.10)，

$$
1\le\operatorname{Tr}e_p\le\operatorname{Tr}p=1,
\qquad e_p=p.
\tag{271.12}
$$

同理，下文的产品投影 $R_i$、局部支持投影 $I_2\otimes Q$ 及其补都在原 proper 区间中；它们的合法性来自可分正展开，而不是未知锥对局部酉变换封闭。

（三）一般位置产品对的整个实际面。取单位产品端点

$$
p=P_{a\otimes b},\qquad q=P_{c\otimes d},\qquad
0<\alpha=|\langle a,c\rangle|<1,\quad
0<\beta=|\langle b,d\rangle|<1.
\tag{271.13}
$$

令 $S=\operatorname{span}_{\mathbb C}\{b,d\}$、$Q=P_S$，并置

$$
Q_0=I_2\otimes(I_b-Q),\qquad
R_1=P_{a^\perp}\otimes P_{d_S^\perp},\qquad
R_2=P_{c^\perp}\otimes P_{b_S^\perp}.
\tag{271.14}
$$

第二因子正交补取在 $S$ 内，第一因子正交补取在 $\mathbb C^2$ 内。$b=2$ 时 $Q_0=0$，后面论证仍成立。定义原暴露面

$$
Z=\{X\in K:\operatorname{Tr}(Q_0X)
=\operatorname{Tr}(R_1X)=\operatorname{Tr}(R_2X)=0\}.
\tag{271.15}
$$

暴露它的原 proper 效应可取 $I-(Q_0+R_1+R_2)/3$：三个效应非负且各不超过 $I$，平均也 proper，其一面恰是三个非负零条件的交。$p,q\in Z$，故 $B(p,q)\subseteq Z$。

先支付支持限制。若 $X\in\operatorname{BP}(2|b)$ 且 $\operatorname{Tr}(Q_0X)=0$，则

$$
X=(I_2\otimes Q)X(I_2\otimes Q).
\tag{271.16}
$$

证明这个块正零边缘事实时，不使用 $X\succeq0$。在 $S^\perp$ 上对第二腿求迹所得第一腿矩阵 $Y$ 为 PSD，因为其每个向量期望是若干非负产品期望之和。$\operatorname{Tr}Y=0$，所以 $Y=0$。对任意第一腿向量 $v$，条件切片 $X_v=(\langle v|\otimes I)X(|v\rangle\otimes I)$ 为 PSD，且在 $S^\perp$ 上迹为零。因此 $X_v$ 消去 $S^\perp$，包括它与 $S$ 的交叉块。对 $v$ 用复极化，所有第一腿矩阵元也消去这些块，得到(271.16)。这同时可用于 $C$ 中的态和 $C^*$ 中的效应。

选相位使 $\langle a,c\rangle=\alpha$、$\langle b,d\rangle=\beta$ 为正实数。在已证的支持 $\mathbb C^2\otimes S$ 中，

$$
T=[a\ c]\otimes[b\ d]:\mathbb C^2\otimes\mathbb C^2
 \overset{\sim}{\longrightarrow}\mathbb C^2\otimes S
\tag{271.17}
$$

可逆。这只是一张支持内的代数坐标图；$b>2$ 时 $T^{-1}$ 是此四复维支持到 $\mathbb C^4$ 的逆，绝不指整个 $\mathbb C^{2b}$ 上的逆，也不指一个原可操作的正回缩。

对 $Z$ 中矩阵作 $X\mapsto T^{-1}XT^{-*}$。局部可逆合同在代数上保持产品期望非负。$T^*R_1T$、$T^*R_2T$ 分别是 $P_{10}$、$P_{01}$ 的严格正倍数，故其两个对角元为零。固定任一局部基向量所得条件切片 PSD；PSD 中零对角元对应的整行整列为零，因而消掉 $00$ 与 $01,10$ 的相邻元、以及 $11$ 与 $01,10$ 的相邻元。唯一可能留下的形状是

$$
\begin{pmatrix}
 A&0&0&z\\
 0&0&w&0\\
 0&\bar w&0&0\\
 \bar z&0&0&D
\end{pmatrix},
\qquad A,D\in\mathbb R,\quad z,w\in\mathbb C.
\tag{271.18}
$$

所以 $\dim_{\mathbb R}\operatorname{span}Z\le6$。若 $Z$ 含有 $B(p,q)$ 外的原纯点 $r$，则实际面 $F_K(p,q,r)\subseteq Z$。实际 L2 下 [XVIII240.2][G271] 给这个外三角仿射维数至少八，故齐次维数至少九，矛盾。最后 $Z$ 是紧面，每点有有限原纯点分解，各分量仍在 $Z$；它们既全在 $B(p,q)$，就有

$$
\boxed{\ Z=B(p,q).\ }
\tag{271.19}
$$

这里没有要求整个原纯点集闭，也没有从局部三球先推出所有面暴露。只对这些一般位置产品对，已经证明其整个实际球就是一个原暴露面。

（四）least 面测试的**原迹**精确为二。取(271.7)供应的 $h=h_{B(p,q)}$。由产品 least 公式，

$$
h\ge_{C^*}p,\ q,\qquad h(p)=h(q)=1.
\tag{271.20}
$$

$ I_2\otimes Q$、$I-R_1$、$I-R_2$ 都在整个 $Z=B(p,q)$ 上取一，所以 leastness 在原完整效应菜单中给

$$
h\le_{C^*} I_2\otimes Q,\quad
h\le_{C^*} I-R_1,\quad
h\le_{C^*} I-R_2.
\tag{271.21}
$$

在原产品态 $R_i$ 上评价后两式，得到 $0\le h(R_i)\le0$。$Q_0$ 是非负可分矩阵，故属于 $C$；第一式给

$$
0\le\operatorname{Tr}(Q_0h)
\le\operatorname{Tr}[Q_0(I_2\otimes Q)]=0.
$$

对 $h\in C^*\subseteq\operatorname{BP}$ 应用(271.16)，也把它的支持限制在同一四复维空间。没有任何面效应的全局正延拓被调用。

在(271.17)中令 $\widetilde h=T^{-1}hT^{-*}$。它为(271.18)的稀疏形状，且(271.20)给

$$
\widetilde h-P_{00},\quad \widetilde h-P_{11}
 \in\operatorname{BP}(2|2).
\tag{271.22}
$$

该稀疏形状块正当且仅当

$$
A,D\ge0,\qquad |z|+|w|\le\sqrt{AD}.
\tag{271.23}
$$

为核对必要性和充分性，对产品向量 $u\otimes v$ 置 $x=|u_0v_0|$、$y=|u_1v_1|$。两条相干项的绝对值因子都是 $xy$；两个局部相位的和与差可以独立指定模 $2\pi$，故最小期望恰为

$$
Ax^2+Dy^2-2(|z|+|w|)xy.
$$

所有 $x,y\ge0$ 都可实现，此二次式非负恰是(271.23)，包含 $A=0$ 或 $D=0$ 的端点。将它分别用于(271.22)，得到

$$
A,D\ge1,\qquad
|z|+|w|\le
 \min\{\sqrt{(A-1)D},\sqrt{A(D-1)}\}.
\tag{271.24}
$$

记 $g=\alpha\beta\in(0,1)$。原确认方程必须在原产品向量上计算；$T^*(a\otimes b)=(1,\beta,\alpha,g)^t$、$T^*(c\otimes d)=(g,\alpha,\beta,1)^t$，所以

$$
\begin{split}
 A+Dg^2+2g\operatorname{Re}(z+w)&=1,\\
 Ag^2+D+2g\operatorname{Re}(z+w)&=1.
\end{split}
\tag{271.25}
$$

相减给 $(A-D)(1-g^2)=0$，即 $A=D$。于是

$$
\begin{aligned}
1
&=A(1+g^2)+2g\operatorname{Re}(z+w)\\
&\ge A(1+g^2)-2g\sqrt{A(A-1)}\\
&=1+\bigl(\sqrt{A-1}-g\sqrt A\bigr)^2
\ge1.
\end{aligned}
\tag{271.26}
$$

第一不等式包含 $\operatorname{Re}(z+w)\ge-(|z|+|w|)$ 及(271.24)。全部取等，因而

$$
A=D=\frac1{1-g^2},\qquad
z,w\in\mathbb R_{\le0},\qquad
z+w=-\frac g{1-g^2}.
\tag{271.27}
$$

$T$ 的各列是单位产品向量；$T^*T$ 在两个保留相干通道的元都是 $g$。因此原迹为

$$
\boxed{
\operatorname{Tr}h
=\operatorname{Tr}(T^*T\widetilde h)
=A+D+2g\operatorname{Re}(z+w)=2.
}
\tag{271.28}
$$

它不是 $\operatorname{Tr}\widetilde h=2/(1-g^2)$。这里精确付出了原坐标的迹预算，也是 leastness 与实际产品零面之间的新接合。

（五）实际残余纯态与两候选。置 $d=h-p$。由（一）和(271.12)，$d$ 是原 proper 区间的极点；(271.28)给 $\operatorname{Tr}d=1$，故 $d\ne0$。令 $m=\max_K d$。若 $m<1$，则 $m>0$，而

$$
d=m(d/m)+(1-m)0
$$

把它非平凡地分解成两个不同 proper 效应，矛盾。因此 $m=1$。紧的最大面有原纯点 $x$，满足 $d(x)=1$。M 给 $e_x\le d$，于是

$$
1\le\operatorname{Tr}e_x\le\operatorname{Tr}d=1.
$$

正差 $d-e_x\in C^*\subseteq\operatorname{BP}$ 的迹为零，由(271.9)差为零；再由(271.11)，

$$
\boxed{\ d=h-p=e_x=x\in K\cap\mathcal E,
\qquad x\in P,\qquad \|x\|_2=1.\ }
\tag{271.29}
$$

所以残余不只是一个代数上方便的矩阵，确是同一个原纯态与它的原最小效应。

(271.27)把所有可能的 $h$ 限制在一个线段：

$$
h=tH_0+(1-t)H_1,\qquad 0\le t\le1,
\tag{271.30}
$$

其中

$$
\begin{split}
H_0&=P_{\operatorname{span}_{\mathbb C}\{a\otimes b,c\otimes d\}},\\
H_1&=T_1P_{\operatorname{span}_{\mathbb C}\{\bar a\otimes b,\bar c\otimes d\}}.
\end{split}
\tag{271.31}
$$

这里 $P_S$ 对子空间表示正交投影。验证(271.31)只须把秩二投影的 Gram 逆写回 $T$ 坐标：$H_0$ 对应 $A=D=1/(1-g^2)$、$z=-g/(1-g^2),w=0$；在共轭第一腿上作同一计算后部分转置，$H_1$ 对应 $z=0,w=-g/(1-g^2)$。所以它们恰是(271.27)的两个端点，而非额外假设的原效应。

其残余分别为

$$
H_0-p=P_{\psi_0},\qquad
H_1-p=T_1P_{\psi_1},\qquad
\psi_0=\frac{c\otimes d-g\,a\otimes b}{\sqrt{1-g^2}},\quad
\psi_1=\frac{\bar c\otimes d-g\,\bar a\otimes b}{\sqrt{1-g^2}}.
\tag{271.32}
$$

两个向量归一且分别正交于被减去的产品向量。部分转置是 HS 正交对合，故两个残余的 HS 范数都为一。它们不同：$g>0$，稀疏坐标的两个通道不同，$T$ 在支持内可逆。严格凸性明确给

$$
\|t(H_0-p)+(1-t)(H_1-p)\|_2^2
=1-t(1-t)\|H_0-H_1\|_2^2<1
\quad(0<t<1).
$$

这与(271.29)矛盾，故对每个一般位置产品对，

$$
h=H_0\quad\text{或}\quad h=H_1.
\tag{271.33}
$$

所选端点 proper，其残余已经是实际原纯态兼效应。此时没有宣称未选端点也是原合法效应。

（六）共同连通域上的闭、互斥方向。所有有序一般位置产品投影对由连通空间

$$
\Xi=U(2)\times U(b)\times(0,1)^2
\tag{271.34}
$$

连续覆盖。例如取 $a=Ue_0$、$c=U(\alpha e_0+\sqrt{1-\alpha^2}e_1)$，$b=Ve_0$、$d=V(\beta e_0+\sqrt{1-\beta^2}e_1)$。任意一对可先择局部向量相位，再选择局部正交基取得这个形式。这里酉矩阵只参数化原本就全部存在的产品端点，未被当作未知 $C$ 的正变换。

$H_i(\xi)$ 在 $\Xi$ 上连续。定义

$$
A_i=\{\xi\in\Xi:H_i(\xi)\in[0,I]_{C^*}\},\qquad i=0,1.
\tag{271.35}
$$

原 proper 区间闭，故 $A_i$ 闭；(271.33)使它们覆盖 $\Xi$。它们互不相交。若两个候选同时 proper，它们都在 $p,q$ 上取一，一面包含整个最小实际面 $B(p,q)$，故由(271.7)

$$
h\le_{C^*}H_0,\ H_1.
$$

$h,H_0,H_1$ 的原迹都是二；两个正差迹零，(271.9)迫使 $h=H_0=H_1$，与候选不同矛盾。连通空间不能由两个非空、不交闭集覆盖，所以恰有一个 $A_i=\Xi$，另一个为空。方向因而全局固定。

这个论证只用候选公式的连续性、原效应区间的闭性和逐对 leastness；没有假设 $h$、$p\mapsto e_p$、实际球族或整个纯点集连续／闭。

（七）全部 Schmidt 秩二的实际覆盖与整锥夹逼。先设全局方向为 $H_0$。任意 Schmidt 秩二且非最大纠缠的单位向量，可在某个数学 Schmidt 基中写成

$$
\psi=\sqrt\lambda\,|00\rangle+\sqrt\mu\,|11\rangle,
\qquad \lambda,\mu>0,\quad\lambda+\mu=1,\quad\lambda\ne\mu.
\tag{271.36}
$$

Schmidt 基只是选取向量，不要求相关局部旋转已是原操作。定义单位产品向量和实数

$$
v=\frac{|0\rangle+|1\rangle}{\sqrt2}
 \otimes(\sqrt\mu\,|0\rangle-\sqrt\lambda\,|1\rangle),
\quad
s=\frac{\lambda-\mu}{\sqrt{2\lambda\mu}}\ne0,
\quad
w=\frac{v+s\psi}{\sqrt{1+s^2}}.
\tag{271.37}
$$

直接有 $\langle v,\psi\rangle=0$。$v+s\psi$ 的 $2\times2$ 系数矩阵为

$$
\begin{pmatrix}
 \sqrt\mu/\sqrt2+s\sqrt\lambda&-\sqrt\lambda/\sqrt2\\
 \sqrt\mu/\sqrt2&-\sqrt\lambda/\sqrt2+s\sqrt\mu
\end{pmatrix},
$$

其行列式恰为

$$
s\frac{\mu-\lambda}{\sqrt2}+s^2\sqrt{\lambda\mu}=0.
\tag{271.38}
$$

所以 $w$ 为归一产品向量，且 $|\langle v,w\rangle|=1/\sqrt{1+s^2}\in(0,1)$。这个全局重叠是两个局部重叠的乘积，故二者都非零。若一个局部重叠等于一，$v,w$ 共享该局部因子，$\psi$ 作为它们的线性组合也将是产品向量，矛盾。因此二者都严格小于一，$(P_v,P_w)$ 属于已支付的一般位置域，并且

$$
H_0(P_v,P_w)-P_v=P_\psi.
\tag{271.39}
$$

由(271.29)及全局方向，$P_\psi$ 同时属于原 $C$ 和原 $C^*$，并为原纯态兼 least 效应。

最大纠缠向量由固定 Schmidt 基中的 $\lambda\ne\mu$ 序列趋向 $\lambda=\mu=1/2$；$C,C^*$ 均闭，故对应投影也属于两锥。产品向量已由(271.12)包含。任何 $\mathbb C^2\otimes\mathbb C^b$ 向量的 Schmidt 秩至多二，故全部秩一投影都已覆盖，谱分解给

$$
\operatorname{PSD}_{2b}\subseteq C,\qquad
\operatorname{PSD}_{2b}\subseteq C^*.
\tag{271.40}
$$

取第二式的对偶，PSD 自对偶性给 $C\subseteq\operatorname{PSD}_{2b}$，于是 $C=C^*=\operatorname{PSD}_{2b}$。

若全局方向为 $H_1$，对任意目标 $\psi$ 仍构造(271.37)的两个产品向量，再将它们第一因子逐个共轭。一般位置和两个局部重叠大小不变，(271.32)的 $H_1$ 残余正是 $T_1P_\psi$。同样包含最大纠缠极限和产品端点，得到

$$
T_1\operatorname{PSD}_{2b}\subseteq C,\qquad
T_1\operatorname{PSD}_{2b}\subseteq C^*.
\tag{271.41}
$$

$T_1$ 为迹配对的正交对合，故 $(T_1\operatorname{PSD})^*=T_1\operatorname{PSD}$；再次夹逼得另一整锥等式。没有遗漏高 Schmidt 秩态的可能，因为第一因子维数二已经使这类向量不存在；也没有先把未知原纯点认作 PSD，再来证明穷尽。

（八）反向、退化产品对和原纯／效应穷尽。标准 PSD 锥中，对单位秩一 $p$，$0\preceq E\preceq I$ 且 $\operatorname{Tr}(Ep)=1$ 迫使 $Ep=p$，因而

$$
E=p+B,\qquad B=(I-p)B(I-p),\qquad
0\preceq B\preceq I-p.
\tag{271.42}
$$

所以 $p$ 是完整 proper 菜单中、同时对所有原混输入成立的 least 确认效应。任意两个不同纯点生成其复二维支持上的整个密度体，这正是三球；纯点为全部秩一投影。$T_1$ 是保迹实线性序同构，从 PSD 锥运输到 $T_1\operatorname{PSD}$，其逆对偶仍为 $T_1$，所以保留完整效应、配对、M、实际面和 L2。两种锥都含 Sep 且属于 BP，因为产品投影在 $T_1$ 下仍是产品投影。由此反向成立。

整锥等式同时给出全部原纯点：分别为 $P_\psi$ 或 $T_1P_\psi$；全部 proper 效应分别为 $0\preceq E\preceq I$ 或其 $T_1$ 像。不存在除此之外的原纯态或原正效应。

一般位置外的产品对不被略去。若 $p\ne q$，设 $L=\operatorname{span}\{a\otimes b,c\otimes d\}$。已证分类后，实际球和 least 最大测试分别为

$$
\begin{array}{c|c|c}
 &B(p,q)&h_{B(p,q)}\\ \hline
C=\operatorname{PSD}&\mathcal D(L)&P_L\\
C=T_1\operatorname{PSD}&
 T_1\mathcal D(\operatorname{span}\{\bar a\otimes b,\bar c\otimes d\})&
 T_1P_{\operatorname{span}\{\bar a\otimes b,\bar c\otimes d\}}
\end{array}
\tag{271.43}
$$

两行的 $h$ 原迹均为二，$h-p$ 仍是实际纯态兼 least 效应。若一个局部重叠为零，则两候选同为 $p+q$；若一个局部重叠为一而 $p\ne q$，则两候选同为固定局部秩一因子乘另一个局部二维支持投影。这些覆盖 $\alpha,\beta$ 的零／一退化端点，可直接由支持式计算，也与不同端点的极限一致。若 $p=q$，最小面为单点，least 测试为 $p$，原迹为一；不把此重合情形混入 L2 或迹二断言，也不要求趋于重合时支持平面有唯一极限。$\square$

**定理 271.3（原实维数四的同坐标全有限层级）。** 完整保留 [XVIII250.1][G271] 的强全有限背景：$W_N=V^{\otimes_{\mathbb R}N}$，闭尖生成的整个 $C_N$，严格正乘积单位 $u_N=u^{\otimes N}$，整个紧底、全部原纯点、完整效应和全部有限单位分解；标量零层、分离全部联合空间的原产品配对、规范重括号、正位置置换及其正逆、正单位丢弃；对全部有限 $a,b\ge0$，包括任意原相关输入，保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b.
\tag{271.44}
$$

在**同一原局域实维数 $\dim_{\mathbb R}V=4$** 下，下列等价：整个原 $K_3$ 满足271.1的 $\mathsf M$ 和实际 L2；存在一个固定保单位实线性同构 $\theta:V\to H_2$，使

$$
\boxed{
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{2^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\quad\text{对每个有限 }N\ge0.
}
\tag{271.45}
$$

$N=0$ 取恒等标量同构。本等价仅结算原维数四分支。

证明。（一）原纯旁观面与 M／L2 下降。对每个原纯旁观态 $r\in P_b$，全有限背景给

$$
\{z\in K_{a+b}:(u_a\otimes\operatorname{id})z=r\}
 =\{x\otimes r:x\in K_a\}.
\tag{271.46}
$$

这是 [XIII161.1][T271] 的实际纯旁观面供应，其证明只用 min/max、原单位配对和 tomography。具体地，每个 $0\le f\le u_a$ 条件态均被纯边缘 $r$ 支配，故为 $r$ 的非负倍数；完整效应张成对偶，产品配对分离，迫使 $z=x\otimes r$。纯边缘逆像为实际面；最小界给反向包含。产品纯点也是原纯点。

M 的下降须保留原菜单，不能仅引用面内几何。固定低层纯 $p$；$p\otimes r$ 是高层原纯点。若高层 least 效应为 $e_{p\otimes r}$，则

$$
g_p(x)=e_{p\otimes r}(x\otimes r)
\tag{271.47}
$$

是低层 proper 效应并确认 $p$。对任意低层原 proper $f$ 确认 $p$，$f\otimes u_b$ 是高层 proper 效应：最大界给它和 $(u_a-f)\otimes u_b$ 的非负性，总和是高层单位。它确认 $p\otimes r$，所以高层 leastness 限制为 $g_p\le f$。故 $g_p$ 就是低层完整菜单中的 least 确认者。这是明确的产品效应延拓，没有使用任意面效应延拓。

实际面内生成面与原生成面相同，(271.46)是整面序同构，所以实际 L2 同样下降。从整个 $K_3$ 先固定一份纯旁观得到 $K_2$，再固定一份得到 $K_1$；或者直接用两份纯产品作旁观。于是两个低层都继承 M 与实际 L2。

$K_1$ 的仿射维数为三，因为 $C_1$ 生成四维 $V$。任选两个不同原纯点，其实际三球也是三仿射维的面。满仿射维的面只能是整个 $K_1$：其相对内部含 $K_1$ 的内点，而含内点的面等于整个紧底。因此 $K_1$ 是一个完整三球。固定一个仿射球同构到 Bloch 球，按迹单位齐次延拓，得到

$$
\theta:V\overset\sim\longrightarrow H_2,
\qquad \theta(C_1)=\operatorname{PSD}_2,
\qquad u=\operatorname{Tr}\circ\theta.
\tag{271.48}
$$

后面始终使用这个同一个 $\theta$，不逐层另选矩阵坐标。这个下降没有用共同尺或260的整锥分类。

（二）同坐标分类整个 $C_2$，再分类整个 $C_3$。暂以 $C_N$ 表示 $\theta^{\otimes N}$ 下的像。(271.44)在 $1|1$ 上给 Sep／BP 夹逼；M、实际 L2 均已下降。271.2给

$$
C_2=T_1^\delta\operatorname{PSD}_4,
\qquad \delta\in\{0,1\}.
\tag{271.49}
$$

考虑 $1|23$ 分块，仅为第二块选择保迹序坐标 $T_2^\delta$，即令

$$
C'_3=T_2^\delta C_3.
\tag{271.50}
$$

在该分块，第二块原 $C_2$ 由(271.49)恰送到整个 $\operatorname{PSD}_4$，第一块仍为整个 $\operatorname{PSD}_2$。保迹序同构运输整锥及逆对偶完整菜单；最小界显然运输，最大界因全部正泛函随逆对偶一一对应而运输。M 是菜单序中的 least 性，实际 L2 是整个实际面的仿射性质，也都保持。因此整个 $C'_3$ 满足271.2的 $2\times4$ 前件，得

$$
C'_3=T_1^\eta\operatorname{PSD}_8,\qquad
C_3=T_1^\eta T_2^\delta\operatorname{PSD}_8,
\qquad\eta\in\{0,1\}.
\tag{271.51}
$$

$T_2^\delta$ 在此只是第二块的序坐标变换，不宣称它是原 $C_3$ 上可实现或正的局部操作，也没有预付原三份 PSD。

（三）三个原边缘的同一性排除相对转置。任意两位置边缘映射把原 $C_3$ **满射**到对应的原 $C_2$：正丢弃给包含；对任意原二份正向量附加一份归一原正态，最小界给反向满射。原正置换及其逆使三条有序边都为同一个 $C_2$。偏迹与转置交换，且一个完整二体的全转置保持 PSD。故(271.51)在 $12,13,23$ 三条边的像依次具有转置奇偶

$$
\eta\mathbin{\oplus}\delta,\qquad \eta,\qquad\delta.
\tag{271.52}
$$

标准二份锥与其单腿转置锥确实不同：$\Omega=(|00\rangle+|11\rangle)/\sqrt2$ 的 $T_1P_\Omega$ 在 $(|01\rangle-|10\rangle)/\sqrt2$ 上有本征值 $-1/2$。所以三条边与(271.49)相等，强制

$$
\eta\mathbin{\oplus}\delta=\delta,\qquad \eta=\delta,
\qquad\text{从而 }\eta=\delta=0.
\tag{271.53}
$$

因此在最初固定的 $\theta$ 中，完整 $C_1,C_2,C_3$ 已同时标准。这是三边奇偶接合的成熟论证，在此只消费新分类支付的整锥输入；不拿共同尺候选支付任何边。

（四）精确匹配 XIII161.4 的全有限尾部。此时 [XIII, Proposition 161.4][T271] 的前件逐项满足：其固定局部 $\theta$ 就是(271.48)，其同坐标(161.14)就是刚取得的标准 $C_1,C_2,C_3$；原全有限 min/max、单位、配对、正置换、规范重括号就是(271.44)及本定理的完整背景。因此该命题给**同一个** $\theta^{\otimes N}$ 下的(271.45)。这里直接调用它的精确结论，不调用 XIII 的旧几何分类入口。

所调用尾部的数学范围也固定：XIII161.4精确引用 [F271] 的 Lemmas 102.6—102.10 及(102.30)后的两条整锥包含。标准 $C_2$ 给正确归一的 Bell 杯帽；面对任意原相关输入，原最大界的正切片先给原 Choi 等价，不先假定高层 PSD。标准 $C_3$ 提供两种秩一三腿资源；其乘积由原最小界属于整个原 $C_6$，正 Bell 收缩产生原 $C_4$ 中的纠缠门 Choi 元。该尾部再导出全部数学局部酉群及一个 imprimitive 门，才使用 [H271, Corollary 2] 的精确有限普适性，包括不等分组维数；对每个有限 $N$ 的整个原态和整个原正效应做双向夹逼。这里物理局部旋转不是输入，Harrow 所需的数学映射则由尾部供应。六腿等中间资源确实使用未截断的全有限背景，不能用仅有三层的假设替代它。

零层本来为标量正锥，$\theta^{\otimes0}$ 保单位；其余单位等式由原 $u^{\otimes N}$ 和(271.48)给出。反向，(271.45)下，标准 PSD 的完整确认者分块(271.42)给 M，任意两纯点的整个复二维支持密度体给实际 L2；特别对整个 $K_3$ 成立。$\square$

**推论 271.4（同维比较、完整条件字典及原问题边界）。** 在271.3的固定250.1背景和同一原 $\dim_{\mathbb R}V=4$ 分支内，M 加实际 L2 已蕴含共同圆尺、自对偶、纯目标的唯一饱和 least 确认、实际二元面的暴露性、数值互易及正交分解性质。完整静态量子字典成立；过程、仪器、时间与实现只在各自额外前件下取得下述字典。原局域维数未指定的 M 加实际 L2 分类不由271.2—271.3结算，也不被它们反驳。

证明与对应。记 $\Theta_N=\theta^{\otimes N}$、$D_N=2^N$。对原 $x\in W_N$ 写 $\rho=\Theta_Nx$；对原效应 $f$ 写 $E=(\Theta_N^{-1})^*f$。整锥等式及其逆对偶给全部 $\rho\succeq0$ 和全部正效应矩阵，单位配对为 $f(x)=\operatorname{Tr}(E\rho)$，没有产品菜单截断。以下是271.3的整锥后应用，成熟静态及过程接口分别归于 [XVIII250.4][G271]、[XIII161.6—161.10][T271]，不把这些标准结论另计作新的分类定理。

| 原对象或明确另给的前件 | 同一原局部坐标中的完整对应 |
| --- | --- |
| 全部归一态、纯点与凸混合 | 全部密度矩阵 $\rho\succeq0,\operatorname{Tr}\rho=1$；全部秩一 $P_v$、纯域 $\mathbb{CP}^{D_N-1}$；凸混合与矩阵凸混合完全对应，谱分解成为实际正交纯态分解 |
| 全部 proper 效应与全部有限单位分解 | 全部 $0\preceq E\preceq I$ 与全部有限 POVM $\{E_j\},\sum_jE_j=I$；原概率为 Born 配对 $p_j=\operatorname{Tr}(E_j\rho)$，PVM 为正交投影的单位分解 |
| 纯目标 $p$ 的所有确认者与对全部原混输入的最小确认 | 若 $\Theta_Np=P_v$，确认者恰为 $P_v+B$，$B=(I-P_v)B(I-P_v)$、$0\preceq B\preceq I-P_v$；least 为 $P_v$，$T_p(x)=\operatorname{Tr}(P_v\Theta_Nx)$ |
| 全部实际面、二元球与零邻面 | 全部支持面 $\mathcal D(S)$；二元面为复二维支持的整个三球，least 最大测试为 $P_S$；纯 $P_v$ 的零邻面为 $\mathcal D(v^\perp)$ |
| 全部原复合、产品、置换、重括号及丢弃 | 标准复 Hilbert 张量积上的整个 PSD、产品密度矩阵、交换和偏迹；纯纠缠由相应切分 Schmidt 秩大于一判别，混态可分体为全部产品态的凸包 |
| 实线性 $L:W_a\to W_b$，另要求对每个有限原旁观 $M\ge0$，$L\otimes\operatorname{id}_{W_M}$ 保持整个原正锥 | $\Phi=\Theta_bL\Theta_a^{-1}$ 的唯一复线性延拓为 CP；等价于 Choi 矩阵正及有限矩形 Kraus 和 $\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*$ |
| 上行另要求在所有正输入上 $u_bL\le u_a$ 或等号 | 分别为 TNI 或 TP，即 $\sum_\alpha K_\alpha^*K_\alpha\preceq I$ 或 $=I$；预算针对整个输入，不是仅 Choi 总迹 |
| 有限分支 $L_j$ 各全旁观正，另给总预算 $u_b\sum_jL_j=u_a$ | 数学仪器：$\rho_j=\Phi_j(\rho)$、$p_j=\operatorname{Tr}\rho_j$；仅 $p_j>0$ 时条件态为 $\rho_j/p_j$；总 Kraus 预算为 $\sum_{j,\alpha}K_{j,\alpha}^*K_{j,\alpha}=I$ |
| 同层全旁观正分支的效应为投影 $A$，且在整个 certain-yes 支持的每个纯态上逐点中性 | 唯一锐更新 $\Phi(X)=AXA$；仅给投影效应或可重复性，不能替代逐点中性 |
| 另给同层连续、可逆、保锥保单位的实一参数群 | 酉共轭群及 $\dot\rho=-i[H_{\rm gen},\rho]$；对纯态择相位后 $i\dot\psi=H_{\rm gen}\psi$，生成元可加实标量 |
| 数学菜单的设备实现、物理时间、无限或近似极限 | 设备事件饱和、记录、接线与仪器实现另给；物理钟、能量与 $H_{\rm phys}=\hbar H_{\rm gen}$ 另标定；无限系统须指定连接映射、相容态、完备化与 normal 延拓，近似结论须另给范数、误差和资源界 |

静态各行由整锥、单位及迹配对直接取得；(271.42)还说明 least $P_v$ 只在该纯点上取一，任意原混态同时达到(271.2)的 minimum。数值互易为 $\operatorname{Tr}(P_vP_w)=|v^*w|^2$，HS 距离平方为 $2(1-|v^*w|^2)$。取迹零空间上的 $g_N(X,Y)=\operatorname{Tr}(\Theta_NX\,\Theta_NY)$，每个实际二元球中心为 $P_S/2$、HS 半径为 $1/\sqrt2$，故得到共同圆尺；这是结论，不是271.2的输入。

AD 沿用 XIII162.2 的原含义：每颗实际二元球内的每对内禀对径纯点可由一个原 proper 效应完全区分。标准支持球中，这两个秩一投影相加为支持投影，因而正交；其中一个投影就是原区分效应，故全部 AD 成立。另外，$r\perp p,q$ 时，$r$ 的向量正交于两向量的整个复线性张成，故 $r\perp s$ 对全部纯 $s\in B(p,q)$ 成立。正交补、投影暴露和正交纯分解均在整个支持面上成立。这些分类后性质不被逆向插入前面未知锥的证明。

过程各行须逐项消费自己的前件。全部原辅助幂 $2^M$ 可以容纳任意给定有限辅助维数；标准嵌入和压缩把全旁观正性化为通常完全正性，反向由 Kraus 和保持全部 PSD，精确是 XIII161.7 的矩形参数接口 $d=2^a,e=2^b$。单系统正性不够。总质量条件独立于全旁观正性，且各支分别 TNI 不能替代总仪器预算。有相关旁观输入 $Z$ 时，分支是 $(\operatorname{id}\otimes\Phi_j)(Z)$，仍按整个输出迹取概率；零概率正输出为零，不指定它的归一条件态。锐更新使用 XIII161.7.1 的全支持逐点中性，连续群使用 XIII161.10；静态分类不指定某个实际 Hamiltonian、物理时间或设备可实现性。

作为两个原坐标中的具体后应用，在已付出的标准 $C_2$ 中，Bell 支持球及其 least 测试为

$$
B(p_{00},p_{11})
=\mathcal D(\operatorname{span}\{|00\rangle,|11\rangle\}),
\qquad h=p_{00}+p_{11}.
\tag{271.54}
$$

任意非产品壳点 $p=P_\psi$，$\psi=\sqrt t\,|00\rangle+e^{i\phi}\sqrt{1-t}\,|11\rangle$，$0<t<1$，其原 least 效应就是 $p$。在原球中心 $h/2$ 上，

$$
p(h/2)=\tfrac12,\qquad h(h/2)=1,
\qquad e_p=p\ne h.
\tag{271.55}
$$

$t=1/2$ 的最大纠缠也包含在内；它的原态和效应合法性已经由闭锥覆盖支付。另一方面，三个产品点生成的**整个**实际面为

$$
F_K(p_{00},p_{01},p_{10})
=\mathcal D(\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}),
\qquad
\dim_{\mathbb R}\operatorname{span}F_K(p_{00},p_{01},p_{10})=9.
\tag{271.56}
$$

理由是 PSD 支持面的最小性及 $\dim_{\mathbb R}\operatorname{Herm}_3=9$。它不曾被作为共同尺之外尚未支付的三角输入。

同维比较的确切范围如下。在固定250.1背景和原实维数四下，260.2的“实际 L2 加存在共同尺”和271.3的“实际 L2 加原 proper M”都等价于(271.45)。所以可用 M 作为这个 qubit 分支的另一入口，并由它导出共同尺；新证明消除了**输入一把共同尺**的需要。这里不声称两个入口在更弱背景中有严格蕴含关系，不声称独立公理数严格减少，也不把270任意维数共同尺定理移作任意维数 M 定理。271.2用整个 $H_2\otimes H_b$ 及全部向量 Schmidt 秩至多二，271.3用原 $\dim_{\mathbb R}V=4$ 固定 $H_2$；这些承重点没有给未知一般局域系统供应同样入口。任意原维数的 M 加实际 L2 目标仍为未解决问题。

本推导的承重综合是：一般位置产品对的原 least 面测试有原迹二；极端残余因而成为实际原纯态兼 least 效应；闭且互斥的候选在共同连通域上统一方向，再由全 Schmidt 秩二覆盖锁定两个整个锥。M-only 剥离／补全、极端效应减法、GB 球及其对偶预算、产品零支持、稀疏块正代数、严格凸性、连通选择、Schmidt 分解和三边奇偶各保留成熟或所列仓内供应的归属；XIII161.4保留全有限尾部的归属。相对于所列供应及所检查的 [M271]、[G271]、[T271]、[GB271]、[AS271]、[N1-271]—[N3-271] 范围，这是 repo-derived composition，不作全球文献优先性或最少独立公理主张。

相关文献的条件也不能被这次综合省略。[AS271] 的 Main Theorem／Theorem 7.2 使用 Hilbert-ball 几何、atomic／non-atomic 分拆、每个 norm-exposed 面的 projectivity 及相应正交正部结构；M-only 的效应 frame 展开没有直接提供这些结构。[N1-271, §3] 与 [N2-271, Theorem 1] 的 $(**)$ 在**全部非负仿射函数**、于指定点归一为一的集合上取 infimum，并另要求唯一饱和；本节的原 proper 菜单域与它不同，且不输入唯一饱和。前者的自对偶路线另需对称跃迁概率，后者另需 bit symmetry。[N3-271, Theorem 2] 所调用的 Wang 分类要求紧的两点齐性度量空间及 convex metric，实际二元三球没有免费提供全局两点齐性。这些结果因此不替代271.2的未知锥证明。[GB271] 的 Theorem 1 确实适用于任意有限复二体而非仅等维因子；[H271] 的精确有限生成确实要求全体数学局部酉和 imprimitive 门，只有在已匹配的传播尾部才使用。

白话图景仍是上述证明的同一条件结论。在原维数四的分支，两颗一般位置、不正交的产品准备，先共同圈出一颗**真实存在的完整二元球**。要求整颗球都被确认的最省原测试，既不能少于两颗产品准备各自的确认测试，又不能在那些已知产品零方向上花预算；这把它的原总迹恰好钉成二。减掉一颗已知产品准备，余下的一份预算被极端性逼成另一颗真实原纯态，而且它同时就是自己的合法确认测试。这样的产品对可以连续换遍，两个候选方向不能在中间混合，也不能同时合法，于是全局只剩一个方向。第一腿只有二复维，所有纠缠向量的 Schmidt 秩最多二，这批残余就足以补齐整个态锥和效应锥；原三份的三条边再排掉相对转置。只有到这时，固定同一局部坐标的既有全有限传播才启动。因而得到原维数四的完整有限量子层级，同时保留一般维数入口、设备实现和物理时间各自未付出的条件。$\square$

[M271]: https://github.com/the-omega-institute/trureturing/blob/eba96d281b55801fac95eef637e144ea56caad12/Library/QuantumStates/mullerududec2012selfduality.md "Proper least confirmation：完整原菜单、全混合 infimum、M-only positive-dual peeling 与共同完整 frame；不消费其后需数值互易的结论。"
[G271]: https://github.com/the-omega-institute/trureturing/blob/eba96d281b55801fac95eef637e144ea56caad12/docs/develop/theory/QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "240.1—240.2 的实际 L2 与外三角下界；250.1 的完整强全有限背景；250.4 的整锥后字典。"
[T271]: https://github.com/the-omega-institute/trureturing/blob/eba96d281b55801fac95eef637e144ea56caad12/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "161.1 的实际纯旁观面；Proposition 161.4 的同坐标全有限尾部；161.6—161.10 的完整条件过程字典。"
[F271]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "XIII161.4 精确引用的版本：102.6—102.10 及(102.30)后全有限整锥夹逼。"
[GB271]: https://arxiv.org/abs/quant-ph/0204159v2 "Gurvits–Barnum, Largest separable balls around the maximally mixed bipartite quantum state, Section III, Theorem 1, p. 4；任意有限复二体的未归一 HS 半径一。"
[AS271]: https://doi.org/10.1007/BF02392307 "Alfsen–Shultz, State spaces of Jordan algebras (1978), Main Theorem 与 Theorem 7.2；保留 projectivity 及正交正部等前件。"
[N1-271]: https://arxiv.org/abs/2312.13213v2 "Niestegge, §3 性质(**)：全部非负仿射函数的 infimum 与唯一饱和；自对偶路线另需对称跃迁概率。"
[N2-271]: https://arxiv.org/abs/2411.18589v2 "Niestegge, Theorem 1：性质(**)与 bit symmetry；proper 菜单域不能替换其全部非负仿射函数域。"
[N3-271]: https://arxiv.org/abs/2601.01936v1 "Niestegge, Theorem 2：所用 Wang 分类需要 compact two-point-homogeneous metric space 与 convex metric。"
[H271]: https://arxiv.org/abs/0806.0631v1 "Harrow, Exact universality from any entangling gate without inverses, Corollary 2：全体局部酉和 imprimitive 门，含不等分组维数的精确有限生成。"

## 追加锚（本行以下为增补区）

## 272. 局域 M 与单一产品目标的整联合最小确认

**定义 272.1（完整菜单、整锥产品与指定目标）。** 对 $X=A,B,D$，取非零有限维实空间、闭尖生成锥 $C_X$、在非零正向量上严格正的单位 $u_X$、整个紧底 $K_X=C_X\cap\{u_X=1\}$、全部纯点 $P_X=\operatorname{ext}K_X$、完整正对偶及 proper 菜单 $\mathcal E_X=[0,u_X]_{C_X^*}$；全部有限单位分解均为菜单。局域 $\mathsf M_X$ 取271.1的完整量词：每个 $p\in P_X$ 有确认 $p$、并低于每个原 proper 确认者的 $e_p^X$。不要求数值互易 $e_p^X(q)=e_q^X(p)$ 或唯一取一。对原联合系统要求

$$
D=A\otimes_{\mathbb R}B,\qquad u_D=u_A\otimes u_B,\qquad
C_A\otimes_{\min}C_B\subseteq C_D
 \subseteq C_A\otimes_{\max}C_B.
\tag{272.1}
$$

最小锥由全部正产品生成，最大锥由两块全部正泛函的产品非负性定义；配对为原张量配对，分离整个 $D$。不缩小原相关锥或原效应区间。对指定 $p\in P_A,q\in P_B$，仅在该产品目标假设存在实际 least proper 确认者

$$
E\in\mathcal E_D,\qquad E(p\otimes q)=1,\qquad
E\le F\quad(F\in\mathcal E_D,\ F(p\otimes q)=1).
\tag{272.2}
$$

此处 least 是原对偶序中的最小元，非仅极小元。$\mathsf M_A,\mathsf M_B$ 是各自全部纯目标上的条件；(272.2)不对别的联合目标作要求。

**定理 272.2（局域完整 frame 支付单目标整载体因子化）。** 在272.1及局域 $\mathsf M_A,\mathsf M_B$ 下，$p\otimes q$ 是原联合纯点，且(272.2)强制

$$
\boxed{\ E=e_p^A\otimes e_q^B\quad\text{作为整个 }D\text{ 上的泛函。}\ }
\tag{272.3}
$$

因此对每个原 $z\in K_D$，包括任意相关输入，完整 proper 菜单中的确认 infimum 由同一个产品效应达到：

$$
\inf_{\substack{F\in\mathcal E_D\\F(p\otimes q)=1}}F(z)
 =(e_p^A\otimes e_q^B)(z).
\tag{272.4}
$$

若(272.2)逐个提供给全部纯产品目标，则(272.3)—(272.4)逐个成立，仍不需要其他联合纯目标的 M。

证明。（一）原菜单与纯性。最大界使正产品泛函在整个 $C_D$ 上非负。若 $f\in\mathcal E_A,g\in\mathcal E_B$，则

$$
u_D-f\otimes g
 =(u_A-f)\otimes u_B+f\otimes(u_B-g)\in C_D^*;
\tag{272.5}
$$

所以 $f\otimes g$ 是原 proper 效应。原边缘属于相应紧底。若 $z\in K_D$ 的 $B$ 边缘为纯 $q$，对每个 $f\in\mathcal E_A$ 的条件切片满足 $0\le(f\otimes\operatorname{id})z\le q$。纯射线迫使它为 $\lambda_fq$，取 $u_B$ 得 $\lambda_f=f(z_A)$。完整 proper 效应张成局域对偶：任意实泛函在紧底上有界，平移并缩放后进入 $[0,u_X]$。原产品配对分离遂给 $z=z_A\otimes q$；最小界给反向包含。故纯边缘逆像是实际面，并与整个 $K_A$ 仿射序同构。对 $p\otimes q$ 的任何凸分解，各分量的两个边缘都必须是 $p,q$，故各分量相同，产品纯性成立。这是 [B272]“A pure marginal fixes every conditional state”和 [XVIII250.2(i)][G272] 的 min/max 接口，不使用 M、共同尺或一般面效应延拓。

（二）含指定纯点的**整个单位完整 frame**。这里直接使用 [M272]“Positive dual generation and one common complete frame”的 M-only 零互易与补全；为固定所需接口，写出其在本推导中的用法。由 $e_s(t)=0$，$u-e_s$ 确认 $t$，leastness 给 $e_t\le u-e_s$，故 $e_t(s)=0$；交换即得零值双向等价。这仅是零互易。对有限纯族 $e_{s_i}(s_j)=\delta_{ij}$，归纳地用余下 proper 效应确认下一点，得 $\sum_i e_{s_i}\le u$。从指定点开始；若 $h=u-\sum_i e_{s_i}\ne0$，在纯点 $t$ 达到 $m=\max_Kh>0$。$h/m$ 是 proper 确认者，故 $e_t\le h/m$。它在旧点为零，零互易使每个 $e_{s_i}(t)=0$，所以 $m=h(t)=1$，可继续减去 $e_t$。各态由上述 Kronecker 读数线性独立，至多 $\dim X$ 项即终止。由此分别选到

$$
p_1=p,\quad q_1=q,\qquad
e_{p_i}^A(p_k)=\delta_{ik},\quad
e_{q_j}^B(q_\ell)=\delta_{j\ell},\qquad
\sum_i e_{p_i}^A=u_A,\quad\sum_j e_{q_j}^B=u_B.
\tag{272.6}
$$

这些是真正的单位分解菜单，非分别选择的两两区分测试。[N272] 的 Lemmas 3(i),(iv),5 是零关系、最大值减法及联合预算的成熟参照；此处消费的是 [M272] 已给出的 proper-M 版本，不输入该文另外的饱和公理。

置 $c_A=\sum_i p_i,c_B=\sum_jq_j$。证明 $c_X\in\operatorname{int}C_X$，这里的内部取**整个** $X$。若 $0\ne f\in C_X^*$ 且 $f(c_X)=0$，每个 frame 点上 $f(s_i)=0$。在纯 $t$ 取到正最大值 $m=\max_Kf$，则 $e_t\le f/m$，故 $e_t(s_i)=0$。零互易再给 $e_{s_i}(t)=0$，与 $\sum_i e_{s_i}(t)=u(t)=1$ 矛盾。因此每个非零正泛函在 $c_X$ 上严格正；有限维闭生成锥的对偶内部判据给所需内部性。

这一接口也使 $c_A\otimes c_B$ 位于整个最小锥、从而整个 $C_D$ 的内部。确切地，对任何在正产品上非负的双线性泛函 $H$，若 $H(c_A\otimes c_B)=0$，内部性使每个 $x\in C_A,y\in C_B$ 各满足 $x\le s c_A,y\le t c_B$，其中 $s,t\ge0$。于是

$$
0\le H(x\otimes y)\le stH(c_A\otimes c_B)=0.
\tag{272.7}
$$

两局域锥生成各自空间，实产品张成整个 $D$，故 $H=0$。有限维最小锥是紧归一产品底的凸包所生成的闭生成锥；再用对偶内部判据即得断言。这里的“正泛函消去受支配产品，再由张成消去整个载体”的接口也见 [B272]“Faithfulness and the exceptional-inclusive support bridge”“Ternary support and the common frame”及(58)后的内部性论证；这里用普通对偶序，未借用那些 Jordan 模型的自对偶尺或谱支持。

（三）只在所选目标调用一次联合 leastness。由(272.5)—(272.6)，各 $h_{ij}=e_{p_i}^A\otimes e_{q_j}^B$ 是 proper 效应且 $\sum_{ij}h_{ij}=u_D$，故产品家族确为原联合菜单。特别地，$h=h_{11}$ 确认 $p\otimes q$，故

$$
H=h-E\in C_D^*,\qquad H(p\otimes q)=0.
\tag{272.8}
$$

对其余 $(i,j)\ne(1,1)$，$h(p_i\otimes q_j)=0$；$0\le E\le h$ 迫使 $E$ 和 $H$ 都在这些产品点上为零。因此 $H(c_A\otimes c_B)=0$，(272.7)给 $H=0$，得到(272.3)和(272.4)。没有调用任何别的 $e^D_{p_i\otimes q_j}$。若所有纯产品目标各有 least，则逐个重复此推导；此时产品 frame 的 least 效应也确实合为 $u_D$，但本结论不要求联合全部纯点上的 M。

白话图景就是这个正差证明。每一边先从指定准备出发，补齐一套真正共用的完整测试菜单；这些准备加起来，在整个局域正锥中没有遗漏任何正方向。把两边的菜单配对，得到原联合菜单中的产品测试。指定产品准备已有一个最省联合确认测试，它只能比对应产品测试更小。两者之差仍是非负测试：在目标上差为零，在菜单的其他每个产品准备上也为零。完整菜单的产品总准备处于整个联合锥的内部，非负测试若在那里读零，就只能处处为零。于是两个测试对所有原联合输入相同，相关态也在其中；并非先丢弃相关性，再用边缘替代输入。

特别地，产品输入 $x\otimes y$ 的(272.4)为 $e_p^A(x)e_q^B(y)$，相关 $z$ 的读数仍是 $(e_p^A\otimes e_q^B)(z)$，一般不等于 $e_p^A(z_A)e_q^B(z_B)$。例如(272.6)两边各有第二项时，原最小界保证 $z=(p_1\otimes q_1+p_2\otimes q_2)/2$ 合法；前者为 $1/2$，两个边缘读数的乘积为 $1/4$。这是同一个原锥中的相关输入。

上述内部性只针对满足 $\sum_i e_{s_i}=u_X$ 的**整个单位完整 frame**；其态和可以依赖所选 frame。不曾证明任意子面有内禀完整菜单、任意态有正交谱、不同 frame 等长、存在规范共同态和、数值互易或共同尺。任意子面的未付谱／内部性不能代替(272.6)。$\square$

**推论 272.3（原 M3 的精确低份数应用与相容性）。** 完整保留 [XVIII250.1][G272]：任意非平凡有限实 $V$；每个有限 $N\ge0$ 的整个 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个紧底、全部原纯点、完整正对偶、全部 proper 效应及有限单位分解；标量零层、分离全载体的原产品配对、规范重括号、全部正位置置换及其正逆、正单位丢弃；全部有限分块的原 min/max 界包括全部相关输入。仅另假设整个 $K_3$ 的 $\mathsf M_3$，不预付共同尺或任何重建。则对非负整数 $a,b$ 满足 $a+b\le3$，每个 $p\in P_a,q\in P_b$ 有

$$
e^{a+b}_{p\otimes q}=e_p^a\otimes e_q^b
\quad\text{于整个 }W_{a+b},\qquad
T^{a+b}_{p\otimes q}(z)=(e_p^a\otimes e_q^b)(z)
\quad(z\in K_{a+b}).
\tag{272.9}
$$

$T$ 仍是271.1的完整 proper 菜单 infimum。$P_0=\{1\}$，$e_1^0=u_0=1$。尤其 $2|1$ 和 $1|2$ 中的二份块目标可以是其整个原 $K_2$ 的任意相关纯态，并非仅两颗单份纯态的产品。

证明。对 $n=1,2$，任选实际纯旁观 $r\in P_{3-n}$；这类旁观存在，可由归一紧底取极点，或用（一）的产品纯性选纯产品。原 min/max 给实际整面

$$
\{z\in K_3:z_{3-n}=r\}
 =\{x\otimes r:x\in K_n\}.
\tag{272.10}
$$

对每个 $p\in P_n$，$p\otimes r$ 是原三份纯态。令 $g_p(x)=e^3_{p\otimes r}(x\otimes r)$；由正产品嵌入，$g_p\in\mathcal E_n$ 且 $g_p(p)=1$。对任何原 $f\in\mathcal E_n$ 确认 $p$，指定延拓

$$
\widetilde f=f\otimes u_{3-n},\qquad
u_3-\widetilde f=(u_n-f)\otimes u_{3-n}
\tag{272.11}
$$

二者均在原 $C_3^*$ 中，故 $\widetilde f$ 是确认 $p\otimes r$ 的三份 proper 效应。M3 给 $e^3_{p\otimes r}\le\widetilde f$，限制得 $g_p\le f$。因此 $g_p=e_p^n$ 是**完整低层菜单**中的 least，唯一性还使它与旁观选择无关。这是271.3（一）已用的具体菜单下降，不是任意面效应延拓。$\mathsf M_1,\mathsf M_2$ 均已支付；对 $1|1,1|2,2|1$ 依次将两个局域 M 与相应联合 M 的产品目标代入272.2，得(272.9)。零层切分由标量单位直接成立。

重括号与位置相容性也在这同一个原空间中成立。对三个单份纯点，

$$
e^3_{(p\otimes q)\otimes r}
 =e^2_{p\otimes q}\otimes e_r^1
 =e_p^1\otimes e_q^1\otimes e_r^1
 =e_p^1\otimes e^2_{q\otimes r}
 =e^3_{p\otimes(q\otimes r)}.
\tag{272.12}
$$

这是整个 $W_3$ 上的泛函等式，允许任意原相关输入。任意原位置置换 $\sigma$ 是保单位序同构，其逆对偶双射完整 proper 菜单并保持确认及 leastness，故 $e^n_{\sigma p}=e_p^n\circ\sigma^{-1}$，$n\le3$；与(272.9)一致。对块内相关纯 $p\in P_2$，结论只将 $e_p^2$ 作为整个二份块的效应，不再拆成两个边缘效应。

若另给三份的实际 L2，(272.10)的整面序同构使面内生成面与原生成面相同，故实际 L2 同样下降；这是 [XVIII240.1、250.2(i)][G272] 的精确接口，不需要一般面投影。272.9本身不使用 L2。原背景虽为全有限，M 的输入只在三份，故上述推导在重建前仅供应 $a+b\le3$；不据此推广到更高份数的 M。任意原维数的 M 加实际 L2 重建仍未由本推论结算。

文献与新内容的范围随推导固定。[B272]“Least comparisons factor without an extra product axiom”的(5)已经给出同一产品恒等式，但在 $S=M+R$ 及其共同自对偶尺、规范 frame 态和的桥梁下；本节所增加的是局域完整 M 加**所选单一产品目标**联合 leastness 的前提弱化，以及上述原低份数接合，不将恒等式本身申领为新发现。[BW272] 的 Lemma 8 在 Jordan 模型复合中证明迹形式因子化，其 §2.3 的 Jordan frame、Definition 6 的产品测试与联合 Jordan 条件仍属其前件，不能被裸 full-menu 背景代付。[N272] 的 Lemmas 3,5 以 Axioms 1–2 和性质 $(*)$ 工作，Axiom 1 要求最小极端效应有唯一饱和态；其 §3 的 $(**)$ 更在全部非负仿射函数中取 infimum 并要求唯一取一，均不替换本节的 proper 菜单。本节相对于这些具名来源及仓内供应属于 repo-derived composition，不主张全球优先性、严格逻辑独立性或最少公理；亦不从此提供数值互易、一般面效应／投影、CP 或任何物理操作。$\square$

[M272]: ../../../Library/QuantumStates/mullerududec2012selfduality.md "Positive dual generation and one common complete frame：M-only 零互易、含指定纯点的完整单位 frame；不消费后续需数值互易的 signed spectrality。"
[B272]: ../../../Library/QuantumStates/barnumhilgert2019spectral.md "Ordered carriers and the shared composite contract 至 Least comparisons factor without an extra product axiom；其后具名三处正产品支配／整载体内部性接口。"
[G272]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "240.1 的实际 L2、250.1 的完整强全有限背景及250.2(i)的实际纯旁观整面。"
[BW272]: https://arxiv.org/abs/1202.4513v2 "Barnum–Wilce, Local tomography and the Jordan structure of quantum theory，§2.3、Definitions 6–7、Lemma 8；Jordan 模型与产品测试条件下的迹形式因子化。"
[N272]: https://arxiv.org/abs/2312.13213v2 "Niestegge, Quantum transition probability，Axioms 1–2、性质(*)、Lemmas 3、5及§3的(**)；保留其唯一饱和与不同 infimum 域的边界。"

## 追加锚（本行以下为增补区）


## 273. 四点两种换位与原二态球的共同刻度

**定义 273.1（原实际球上的有限换位条件）。** 单系统先采用271.1的非零有限实载体、闭尖生成原锥、严格正原单位、整个紧底 $K$、全部纯点 $P$ 和完整 proper 效应区间。取 $\dim V>1$；实际 L2 将给出所需的三维面。对整个 $K$ 的仿射自同构群记为 $\operatorname{Aut}_{\rm aff}(K)$：每个元素及其逆均把整个 $K$ 映到自身，并保持全部原凸准备关系。这是由原 $K$ 定义的数学群，不是另供的物理操作菜单。

实际 L2 保留271.1的完整含义：每对不同原纯点的整个最小实际面 $B=F_K(p,q)$ 是仿射闭三球，原纯点在其中恰为整个球面。对每个这样的**不同实际面** $B$，条件 $\mathsf{X}_4$ 要求存在四个不同的原纯点 $r_1,r_2,r_3,r_4\in B$，以及两张整个原体的仿射自同构 $S_B,T_B$，满足

$$
\begin{aligned}
S_Br_1=r_2,\quad S_Br_2=r_3,\quad S_Br_3=r_1,\quad S_Br_4=r_4,\\
T_Br_1=r_2,\quad T_Br_2=r_1,\quad T_Br_3=r_4,\quad T_Br_4=r_3.
\end{aligned}
\tag{273.1}
$$

不先要求四点仿射独立或构成正四面体，不给共同尺、半径或全轴半转。$S_B,T_B$ 在面外的阶数与作用不作额外规定；不同面可以选不同四点及不同自同构。条件要求的是整个原体上的映射存在，不能以仅在四点或面内合法的置换代替。

沿[XVIII200.1及(200.6)][C273]，在整个 $K$ 上取归一相对体积，记重心为 $c_K$、在 $L=\operatorname{lin}(K-K)$ 上的协方差为 $A_K$，定义

$$
g_K(v,w)=(A_K^{-1}v)(w),\qquad v,w\in L.
\tag{273.2}
$$

该既有供应给出 $g_K$ 正定及其对全部 $\operatorname{Aut}_{\rm aff}(K)$ 的不变性。此处的数学体积不要求均匀准备装置；也不将 $g_K$ 先解释为自对偶锥配对。

**定理 273.2（四点关系把每张原球接到同一整体尺）。** 在273.1的原域中，实际 L2 加 $\mathsf{X}_4$ 蕴含：对每个实际二态球 $B$，其球心为

$$
c_B=\frac{r_1+r_2+r_3+r_4}{4},
\tag{273.3}
$$

四点在该球的内禀椭球度量下自动构成正四面体；整个 $B$ 在**同一个** $g_K$ 下为圆球。确切地，存在 $R_B>0$ 使

$$
\begin{aligned}
L_B&=\operatorname{lin}(B-B),\qquad \dim L_B=3,\\
B&=\{c_B+v:v\in L_B,\ g_K(v,v)\le R_B^2\},\\
P\cap B&=\{c_B+v:v\in L_B,\ g_K(v,v)=R_B^2\}.
\end{aligned}
\tag{273.4}
$$

$R_B$ 可随面变化。只需273.1所列的两张全体映射，不需要把四面体的全部置换另作输入，也不要求它们在整个 $K$ 上满足有限群的全部关系。

证明。先固定任一实际 $B$。严格凸球内两个不同纯点所生成的原最小面就是整个 $B$：它们开弦上的点属于 $\operatorname{ri}B$，包含它们的原面必须包含 $B$。仿射自同构将最小实际面送到像端点的最小实际面。因此 $S_B$ 和 $T_B$ 都保持整个 $B$，而不只是置换四点。

在四个不同锚点上，$s=(123)$ 与 $t=(12)(34)$ 所生成的置换群是 $A_4$：$t$ 的三个循环共轭给全部三个非平凡双换位，与 $s$ 一起组成 $V_4\rtimes C_3$ 的十二个偶置换。特别地，顶点集和六条无序边各为一个轨道。先取把整个 $B$ 写成单位球的内禀方向二次型 $h_B$。保持 $B$ 的自同构保持其球心与 $h_B$；六边传递性使六条边的 $h_B$ 长度同为 $\ell>0$。对任意 $\sum_i\lambda_i=0$，平方距离的零和恒等式给

$$
h_B\!\left(\sum_i\lambda_i r_i,\sum_i\lambda_i r_i\right)
=\frac{\ell^2}{2}\sum_i\lambda_i^2.
\tag{273.2a}
$$

因此四点自动仿射独立。它们现在才唯一决定 $\operatorname{aff}B$ 上的映射，有限群关系也只在这个限制上成立；不向面外传递。

整个仿射球的中心唯一，故被每个保持 $B$ 的自同构固定。将 $c_B$ 写成四点的唯一仿射坐标，顶点传递性使四个系数相同，系数和为一即得(273.3)。置 $v_i=r_i-c_B$，则 $\sum_i v_i=0$。将同一个内禀球二次型 $h_B$ 归一成

$$
B=\{c_B+v:h_B(v,v)\le1\}.
\tag{273.5}
$$

保持整个球的仿射映射固定其中心，线性部分保持 $h_B$；这直接来自球的 Minkowski 泛函。因全部 $r_i$ 纯，$h_B(v_i,v_i)=1$。六边传递使非对角 $h_B(v_i,v_j)$ 为同一数 $a$。与 $\sum_i v_i=0$ 配对得 $1+3a=0$，所以 $a=-1/3$，四点自动为内禀正四面体。

同样，整个原体的 $S_B,T_B$ 保持273.2的同一个 $g_K$。顶点与六边传递性分别使

$$
g_K(v_i,v_i)=\rho^2,\qquad g_K(v_i,v_j)=b\quad(i\ne j).
\tag{273.6}
$$

$\rho^2>0$，因为 $v_i\ne0$。零和关系给 $b=-\rho^2/3$。四点仿射独立使前三个 $v_i$ 线性独立：若前三个有非零关系，用 $v_4=-v_1-v_2-v_3$ 即得到四点的非零零和仿射关系。因而它们构成 $L_B$ 的基，(273.6)与 $h_B$ 的相同 Gram 表给

$$
 g_K|_{L_B}=\rho^2 h_B.
\tag{273.7}
$$

取 $R_B=\rho$，(273.5)及原 L2 的全部纯边界给(273.4)。对每张实际球分别作此推导，使用的始终是同一个全体协方差尺 $g_K$。证明没有先用全域确认、数值互易、一般面效应延拓或纯态传递性。$\square$

**推论 273.3（原三复制上的完整有限复量子候选）。** 完整保留[XVIII250.1][F273]及270.1的强全有限背景：同一个非平凡有限实 $V$、每个 $N\ge0$ 的整个 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成原锥 $C_N$、严格正 $u_N=u^{\otimes N}$、整个归一紧底、全部原纯点、完整正对偶、全部 proper 效应及全部有限单位分解；标量零层、分离整个载体的原张量配对、规范重括号、全部正位置置换及其正逆、正单位丢弃；对全部有限分块和全部相关输入保留 min/max 界。仅在整个 $K_3$ 要求实际 L2 和 $\mathsf{X}_4$。

相对于270.2—270.12所列的普通条件供应，这个入口与存在整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$ 满足

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\qquad(N\ge0)
\tag{273.8}
$$

等价。此处未把 $\mathsf M_3$ 或原数值互易作为输入；它们在获得整锥对应后成为结论。

证明。273.2用于原三复制的整个 $K_3$，恰好供应270.1所需的一个正定共同圆尺及所有实际二纯三球；半径可变与270.1的量词一致。全部原背景未变，因此直接调用270.12，得到(273.8)。不重证该节的三标签接合、矩形排核、共同局部坐标及全有限传播，不以四点置换代付其任何背景或文献前件。

反向，在标准全有限复矩阵层级中，任何实际二纯面是复二维支持上的整个 qubit 密度体。取其中 Bloch 球的四个正四面体纯点。$(123)$ 固定第四点，是正四面体的 $2\pi/3$ 旋转；$(12)(34)$ 为 $\pi$ 旋转。每个都是 $\mathrm{SO}(3)$ 元素，可由二维支持上的一个酉矩阵共轭实现；将该酉矩阵在支持正交补上补成恒等，得到整个 $K_3$ 的仿射自同构，并实现(273.1)。这是数学自同构的存在，不要求该块酉为实际可调用的装置。实际 L2 同时由整个复二维支持成立，故反向完成。$\square$

**命题 273.4（两个有限换位的判据边界）。** 273.2中的两类置换各自单独都不能迫使一个不变正定二次型与内禀球型成比例；四点上的这些置换也不能替代实际 L2 或它们向整个原体的延伸。

证明。在正四面体的三维标准表示中，$s=(123)$ 的固定轴为第四个顶点方向 $a$。取欧氏单位轴 $a$ 和 $0\ne\varepsilon>-1$，则

$$
Q_s=I+\varepsilon aa^{\mathsf T}
\tag{273.9}
$$

正定、保持 $s$，却不为标量型。对 $t=(12)(34)$，取其 $\pi$ 旋转轴为第一坐标，$t=\operatorname{diag}(1,-1,-1)$；$Q_t=\operatorname{diag}(2,1,1)$ 同样正定、不变且非标量。二者只是否定“只靠一种置换就锁定任意不变尺”的线性代数主张，不是删掉273.1一半后整个原全有限层级的反模型，也不证明原公理的逻辑独立性或最少生成元数。

再取同一个正四面体四顶点的凸包 $\Delta$，与其外接整球 $B$ 比较。两者都容许(273.1)的两种全体仿射自同构，并且所列四点及置换表完全相同；$\Delta$ 的两纯最小面却是线段，$B$ 的则是整个三球。因此有限四点换位表没有独自恢复原最小面或球内连续状态。最后，对任一仿射球，其面内正四面体均有这两种旋转；若不要求它们延伸到整个 $K$，它们就未必保持整体 $g_K$，从而不能使用(273.6)。这后一项定位的是证明所需的环境相容性，不声称构造了违反原全有限结论的模型。$\square$

**推论 273.5（现有量子公理的对应与候选的准确含义）。** 在273.3的完整前提及普通条件供应下，同一个 $\Theta_N=\theta^{\otimes N}$ 给出以下对应；它们直接消费270.13的整锥后字典。

| 原定义或另给条件 | 对应 |
| --- | --- |
| 全部归一态、纯态与混合 | 全部密度矩阵、秩一投影与凸混合；纯标签为 $\mathbb{CP}^{n^N-1}$，谱分解成为原态的正交纯态分解 |
| 完整 proper 效应、配对与全部有限单位分解 | $0\preceq E\preceq I$，$p_j=\operatorname{Tr}(E_j\rho)$，$\sum_jE_j=I$；得到全部数学 POVM 与其 PVM 特例 |
| 原全菜单最小确认 | $e_{p_v}(x)=\operatorname{Tr}(P_v\Theta_Nx)$；纯端点读数 $|\langle v,w\rangle|^2$ 双向相同，全部混输入由同一个效应实现 minimum |
| 原所有有限联合态、产品与丢弃 | 同一局部复 Hilbert 坐标的张量积、全部联合 PSD、纠缠与偏迹 |
| 另给实线性分支在全部有限相关旁观输入上保持正性，并给原全正输入上的质量预算 | CP 与矩形 Kraus 表示；质量不增为 TNI、保质量为 TP；仪器另须各支总和的单位预算 |
| 另给同层正实线性分支 $L:W_N\to W_N$，其效应 $u_N\circ L=e_P$ 对应投影 $P$，并在整个 certain-yes 支持的每个纯态上满足 $Lp=p$ | 唯一锐更新 $X\mapsto PXP$ |
| 另给连续可逆保锥保单位的一参数群 | 酉共轭及 Hamilton 生成元形式；物理钟、能量与 $\hbar$ 的标定仍另给 |

证明与范围。273.3已经供应270.13的整个实际矩阵锥、单位、配对和张量坐标，故逐项代入该既有字典；各过程行只在同一行所列的额外前提下成立。无限维、无限张量极限、近似稳定性、设备实现和资源成本仍无新增结论。数值互易只交换同一比较的两个纯端点，不改变两个有序仪器的状态更新；270.7已有非正交 qubit 测量的不同先后概率反例。

本节新增的 repo-derived 接合是从每张实际球的四个原纯锚与两种**全体**换位，恢复内禀正四面体及同一全体协方差尺下的逐面圆性，再接到270的任意原维数全有限供应。有限置换群 $A_4$、不变二次型的有限维刚性、仿射球的中心与体积换元、Bloch 旋转的酉提升都是成熟中间工具；不将它们另领为新一般定理。关于对称与量子重建的成熟先例，[Müller—Ududec，Theorem 1及其bit symmetry定义][M273]使用有序可区分纯对的群传递性；本节未调用该定理，也未从两张映射直接申领它的自对偶结论。关于共同尺和完整重建的实际供应分别是[C273]与270.12—270.13，不将有限置换替换整个全域合同。不主张本入口相对 $\mathsf M_3+\mathrm{L2}$ 更弱、严格独立、全球最少或具有文献优先权；$\mathsf M_3+\mathrm{L2}$ 能否在任意原维数自行供应共同尺，仍未由本节解决。

白话说，每两个不同的纯准备真正撑起一整颗三维球。在每颗球上，只挑四个不同的纯准备：前三个轮换、第四个不动；再让两对准备同时互换。要求这两种换位都能放回整个系统，所有原混合关系仍成立。四点于是自动变成不共面的正四面体，各颗球也被同一把从整体定义的尺量圆，不必先输入这把尺或逐方向输入连续旋转。保持原来全部有限复合和完整测试背景，已有重建才把它接成全部密度态、Born 读数、张量积与纠缠；实际更新、仪器和物理时间仍各有自己的条件。$\square$

[C273]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "200.1、(200.5)—(200.6)：整个原体的协方差尺及仿射自然性。"
[F273]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "250.1的强全有限原域；273.3完整保留其条件。"
[M273]: ../../../Library/QuantumStates/mullerududec2012selfduality.md "Müller—Ududec，The structure of reversible computation determines the self-duality of quantum theory，Theorem 1；有序可区分纯对的bit symmetry及其条件边界。"

## 追加锚（本行以下为增补区）

## 274. 双复制互易、统一秩二覆盖与全部有限量子层级

**定义 274.1（互易只输入到原双复制）。** 完整保留273.3及[XVIII250.1][F274]的强全有限原背景，记为 $\mathsf F$：非平凡有限实 $V$，每个有限 $N\ge0$ 的整个原 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成锥 $C_N$、严格正乘积单位 $u_N=u^{\otimes N}$、整个归一紧底 $K_N$、全部原纯点 $P_N$、完整正对偶和 proper 区间、全部有限单位分解；标量零层、分离整个载体的原张量配对、规范重括号、正位置置换及其正逆、正单位丢弃；对每个有限分块及所有原相关输入保留 min/max 界。取 $\dim_{\mathbb R}V>1$。

只在整个 $K_3$ 要求271.1的 $\mathsf M_3$ 和实际 $\mathrm{L2}_3$。前者为每个原纯目标提供低于所有原 proper 确认者的 least 效应；后者要求每对不同原纯点生成的整个最小实际面是完整仿射闭三球，其整个球面恰为原纯点。271.3及272.9已经给出 $\mathsf M_1,\mathsf M_2,\mathrm{L2}_1,\mathrm{L2}_2$ 的下降，以及总份数至多三的纯块产品确认因子化。

本节额外要求的数值互易只在整个双复制：

$$
\mathsf R_2:\qquad e_p^2(q)=e_q^2(p)
\quad\text{对所有 }p,q\in P_2.
\tag{274.1}
$$

这里 $p,q$ 可以各自在两份内部纠缠，不是仅比较产品准备。所有 $e_p^j$ 都由各层完整原 proper 菜单及 $\mathsf M_j$ 唯一定义；不另供比较表。等价地，在 $\mathsf M_3$ 下，274.1可写为对每个原纯 $p$、每个有限原纯族 $q_i\in P_2$ 和概率权重 $\lambda_i$，

$$
T_p^2\!\left(\sum_i\lambda_iq_i\right)
=\sum_i\lambda_iT_{q_i}^2(p),\qquad
T_p^2(x)=\inf_{\substack{f\in[0,u_2]\\f(p)=1}}f(x).
\tag{274.2}
$$

等价只用 least 效应的仿射性及单项概率族，不算新的混合定理。没有输入 $\mathsf R_3$、共同尺、一般面效应延拓、矩阵类型或可调用物理变换。

**定理 274.2（任意矩阵尺寸中的统一 Schmidt 秩二覆盖）。** 设 $m,n\ge2$，整个原实载体为 $H_m\otimes_{\mathbb R}H_n$，单位为普通迹，其中 $H_d=\operatorname{Herm}_d(\mathbb C)$；原闭尖生成锥满足

$$
\operatorname{Sep}(m|n)\subseteq C\subseteq\operatorname{BP}(m|n).
\tag{274.3}
$$

使用整个迹一紧底、全部原纯点和完整 proper 菜单，并在整个紧底要求 $\mathsf M$ 和实际 L2。令

$$
\mathcal S_2(m|n)=\operatorname{cone}\{P_\psi:
\operatorname{SR}_{m|n}(\psi)\le2\}.
$$

则存在一个共同的 $\delta\in\{0,1\}$，使

$$
\boxed{\quad T_A^\delta\mathcal S_2(m|n)\subseteq C\cap C^*.\quad}
\tag{274.4}
$$

$T_A$ 是第一整个矩阵因子的固定基部分转置，对偶取普通迹配对。本结论不将 $m,n>2$ 时未覆盖的高 Schmidt 秩方向判成 PSD，也不声称一般 $m\times n$ 整锥分类。

证明。先精确复用271.2中不依赖第一因子维数二的供应。由(274.3)及对偶关系，$C,C^*\subseteq\operatorname{BP}(m|n)$。[GB271, Theorem 1]的单位矩阵周围未归一 HS 半径一可分球给271.9的 $\|X\|_2\le\operatorname{Tr}X$，同时适用于这两个锥。故271.10—271.12原样给：任意原纯 $x$ 有 $\operatorname{Tr}e_x\ge1$；若等号成立，则 $e_x=x$、$\|x\|_2=1$；每个单位产品投影 $P$ 是原纯点且 $e_P=P$。271.5—271.7的 M-only 剥离／补全与原暴露面 least 最大测试也适用于当前整个原菜单，不增加数值互易。

取一般位置单位产品端点

$$
P=P_{a\otimes b},\quad Q=P_{c\otimes d},\qquad
0<\alpha=|\langle a,c\rangle|<1,\quad
0<\beta=|\langle b,d\rangle|<1.
$$

置 $S=\operatorname{span}_{\mathbb C}\{a,c\}$、$T=\operatorname{span}_{\mathbb C}\{b,d\}$，并取四个整个原 proper 效应

$$
Q_A=(I-P_S)\otimes I,\quad Q_B=I\otimes(I-P_T),\quad
R_1=P_{a_S^\perp}\otimes P_{d_T^\perp},\quad
R_2=P_{c_S^\perp}\otimes P_{b_T^\perp}.
\tag{274.5}
$$

正交补向量均在所标记的复二维支持中取。四个投影及其补都是可分正矩阵，故原 proper 性来自(274.3)，不来自未知锥的滤波封闭。令 $Z$ 为它们的共同零面；$I-(Q_A+Q_B+R_1+R_2)/4$ 是暴露它的原 proper 效应。

271.16的块正零边缘论证可在两腿分别使用，给每个 $X\in Z$ 的真正支持限制

$$
X=(P_S\otimes P_T)X(P_S\otimes P_T).
\tag{274.6}
$$

具体说，条件切片在被消去的局域正交补上迹为零，故作为 PSD 切片消去该补及全部交叉块；再对另一腿极化。这个论证只要求块正，可用于原态和原正效应，不把 $X$ 先认作 PSD。现在支持内的可逆图 $D=[a\ c]\otimes[b\ d]$ 确为复四维图。两个 $R_i$ 零条件给271.18的六实维稀疏形状。因此 $\dim\operatorname{span}Z\le6$。若 $Z$ 有实际二态球 $B(P,Q)$ 外的原纯点，实际 L2 的[XVIII240.2][F274]使对应外三角齐次维数至少九，矛盾。紧面的有限原纯分解遂给 $Z=B(P,Q)$。

令 $h$ 为271.7给出的这个原暴露面的 least 最大测试。除了 $h\ge_{C^*}P,Q$ 和两条确认方程，还必须同时保留

$$
h\le_{C^*}P_S\otimes I,\qquad
h\le_{C^*}I\otimes P_T,\qquad
h\le_{C^*}I-R_1,I-R_2.
\tag{274.7}
$$

这些都是在整个 $Z$ 取一的原 proper 效应。前两式分别与原可分正态 $Q_A,Q_B$ 配对，给 $\operatorname{Tr}(Q_Ah)=\operatorname{Tr}(Q_Bh)=0$；后两式给 $h(R_i)=0$。于是同一个块正零边缘论证也把 **$h$ 本身** 限制到(274.6)的同一支持。没有将一个面内 least 效应冒作原全域效应。

现在可以直接应用271.22—271.33的四维支持内证明，参数对应为原 $a,c,b,d$、$g=\alpha\beta$、$\widetilde h=D^{-1}hD^{-*}$。该证明所用的所有输入都已在当前原菜单支付；它不需要整个第一因子只有二维。其稀疏系数满足

$$
A=D_0=\frac1{1-g^2},\qquad z,w\le0,\qquad
z+w=-\frac g{1-g^2},\qquad
\operatorname{Tr}h=A+D_0+2g\operatorname{Re}(z+w)=2.
\tag{274.8}
$$

这里 $D_0$ 是稀疏矩阵右下系数，与坐标图 $D$ 不同。最后一个迹是原矩阵迹，非 $\operatorname{Tr}\widetilde h$。原 proper 极端残余 $h-P$ 由271.29成为同一个原纯态兼 least 效应，HS 范数为一。271.30—271.33的严格凸性于是将 $h$ 限制为两端点之一：

$$
H_0=P_{\operatorname{span}\{a\otimes b,c\otimes d\}},\qquad
H_1=T_AP_{\operatorname{span}\{\bar a\otimes b,\bar c\otimes d\}}.
\tag{274.9}
$$

这两式是在整个原矩阵载体上的矩阵；$H_1$ 中先共轭支持，再作固定基的整个第一腿转置。

方向的共同性同样不能逐对任取。将271.34的域改为连通的 $U(m)\times U(n)\times(0,1)^2$，它连续覆盖全部一般位置产品投影对。两个候选随参数连续，其原 proper 性集合闭且覆盖；若同时 proper，leastness 给 $h\le H_0,H_1$，原迹均为二的正差只能为零，迫使两个不同候选相等，矛盾。因此两个闭集不交，连通性使同一个方向在全部参数上固定。这只参数化已存在的产品端点，不假设这些酉矩阵是原正操作。

最后直接使用271.36—271.39的显式残余构造，参数为任意选定的局域复二维 Schmidt 支持。它对每个非最大纠缠 Schmidt 秩二向量给一般位置产品 $v,w$，使选定方向的残余恰为 $P_\psi$ 或 $T_AP_\psi$，并同时属于 $C,C^*$。最大纠缠点由两锥闭性补上，产品点已支付。锥生成给(274.4)。这一尾步只覆盖 Schmidt 秩至多二；271.40在此仅当某个因子维数二时才升级为整个 PSD 锥。$\square$

**定理 274.3（原双复制互易足够）。** 在274.1的完整原域中，相对于[M274]的完整 M 加互易到规范迹 Jordan 几何纸面桥、[N274]的产品保持正规形及[T274]的全有限传播供应，下列等价：

$$
\mathsf M_3+\mathrm{L2}_3+\mathsf R_2\quad\Longleftrightarrow\quad
\exists n\ge2,\ \theta:V\overset\sim\longrightarrow H_n:\quad
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\quad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{274.10}
$$

同一个局域 $\theta$ 用于所有实际份数；零层为标量恒等。共同圆尺和整个三复制的数值互易是结论，不是本入口的附加假设。

证明。（一）先取得低二层的整个矩阵类型。固定任一原一复制纯旁观 $t$。由272.9的产品最小确认，274.1下降为

$$
e_p^1(q)=e_{p\otimes t}^2(q\otimes t)
=e_{q\otimes t}^2(p\otimes t)=e_q^1(p).
\tag{274.11}
$$

因此整个一、二复制分别有 M 加互易。对这两层分别调用[M274]的完整纸面桥，取得规范迹 Euclidean Jordan 表示；自对偶、谱性、projectivity 和纯过滤在该桥内导出，不从裸 M 或 L2 提前调用。实际 L2 排除非平凡直和，因为跨直和扇区的两纯最小面是线段。简单 Jordan 分类中，秩至少三的实、复、四元数及 Albert 型二支持面分别是实二维、三维、五维及九维球；rank-two spin factor 的整个球也只能为三维。故两层都为完整复矩阵类型。先固定一层保单位坐标 $\theta:V\to H_n$，$n\ge2$；二层实维数是 $(\dim V)^2=n^4$，所以它的矩阵尺寸为 $n^2$。

在这些已取得的整层坐标中，原产品准备和原产品效应具有[N274]所需的正产品性、精确迹配对、单位效应和完整载体维数。该笔记“Conditional normal-form theorem and proof”应用 Xu—Zheng—Fošner 的 Main Theorem，将产品映射化为固定酉合同及各腿固定转置。两腿同时转置保持整个 PSD 锥，故在最初固定的 $\theta$ 下，暂以 $C_j$ 表示其像，有

$$
C_1=\operatorname{PSD}_n,\qquad
C_2=T_1^\varepsilon\operatorname{PSD}_{n^2},\qquad
\varepsilon\in\{0,1\}.
\tag{274.12}
$$

这一步只运输矩阵坐标，不预设原整个张量线性化对纠缠 PSD 输入为正；正规形供应明确不要求后者。到这里尚未获得原 $C_3$ 的矩阵类型或 $\mathsf R_3$。

（二）仅给三层支付秩二资源。在实际分块 $(12)|3$ 中作坐标运输

$$
C'_3=T_1^\varepsilon C_3.
$$

该块的两个完整局域锥现为 $\operatorname{PSD}_{n^2}$ 和 $\operatorname{PSD}_n$。原 min/max 界、单位、完整菜单、M 及实际 L2 随保迹序坐标及其逆对偶运输，故274.2适用于整个 $C'_3$。第一块的整个转置 $T_{12}$ 与第三腿转置 $T_3$ 在 $\mathcal S_2((12)|3)$ 上给相同集合，因为二者的复合是保持 Schmidt 秩的全转置。因此存在一个共同 $\delta\in\{0,1\}$，使

$$
T_1^\varepsilon T_3^\delta\mathcal S_2((12)|3)
\subseteq C_3.
\tag{274.13}
$$

$T_1^\varepsilon$ 不是被宣布为原三层正操作；它只把该分块的原二层锥送到已知 PSD 块，供正确运输后的定理使用。

（三）真实 Bell 边缘排除三个错误方向。记 $B_{ij}$ 为原两个计算指标 $0,1$ 上的归一实 Bell 投影，并在未使用腿附加 $P_0$。以下每个投影在 $(12)|3$ 上的 Schmidt 秩均至多二，故均落在274.13的来源域中：

| $(\varepsilon,\delta)$ | 选取的来源投影 | 运输后丢弃旁观腿的原二层输出 |
| --- | --- | --- |
| $(1,0)$ | $P_0^{(1)}\otimes B_{23}$ | $B_{23}$ |
| $(1,1)$ | $B_{13}\otimes P_0^{(2)}$ | $B_{13}$，因为 $T_1T_3$ 是该 Bell 对的全转置 |
| $(0,1)$ | $B_{13}\otimes P_0^{(2)}$ | $T_3B_{13}$ |

原正丢弃和原正位置置换要求这些输出属于同一个274.12的 $C_2$。前两行要求标准 Bell 投影属于单腿转置 PSD 锥；第三行要求部分转置 Bell 投影属于标准 PSD。三者都不可能，因为 Bell 的部分转置在反对称向量上有本征值 $-1/2$。故 $\varepsilon=\delta=0$。于是 $C_2=\operatorname{PSD}_{n^2}$，且 $\mathcal S_2((12)|3)\subseteq C_3$。这里仅用明确的原三层态及其正边缘，不把各条边分别可选的方向当成同一联合实现。

（四）一只明确三腿种子已经足够。取[T274,164.10]的

$$
\tau_n=\sum_{i=0}^{n-1}|ii0\rangle+|011\rangle
=\left(\sum_i|ii\rangle\right)|0\rangle+|01\rangle|1\rangle.
\tag{274.14}
$$

右边在 $(12)|3$ 上恰有两个独立 Schmidt 方向，所以274.13的已定标准方向给 $\tau_n\tau_n^*\in C_3$；原迹质量为 $n+1$。固定同一个 $\theta$，274.12现给[T274,164.1]要求的标准低二层，274.14恰是164.11的条件3，其余每个有限层的 min/max、单位和正置换就是未缩减的 $\mathsf F$。直接调用164.11的 $3\Rightarrow4$，得到全部有限份的274.10，不必先证明整个 $C_3$ 是 PSD。

这个供应确实消费全有限背景：164.10用六份种子、十八条实际腿支付纠缠门资源，随后164.9消费正确的 Bell 杯帽、全部相关旁观输入及精确有限普适性。不能把只在三层输入 M 和 L2 误写成只需定义三层锥。

反向，标准全有限复矩阵层级中，271.42给完整 proper 菜单中的 least 确认，复二维支持给每对不同纯态的整个三球，迹配对给 $e_p(q)=\operatorname{Tr}(pq)=e_q(p)$。故特别满足 $\mathsf M_3,\mathrm{L2}_3,\mathsf R_2$；零层及乘积单位保持。$\square$

**命题 274.4（两层的同读数备择与第三层的作用范围）。** 对任意 $n\ge2$，固定同一局域 PSD 锥与产品迹配对，二层的 $C_2^{(0)}=\operatorname{PSD}_{n^2}$ 和 $C_2^{(1)}=T_1\operatorname{PSD}_{n^2}$ 都有完整菜单中的 M、纯端点互易及实际 L2，且全部产品准备与产品效应读数相同；它们对原标准 Bell 投影的准入不同。因此这些二层条件不能单独选择274.12的相对方向。本命题没有给任一非标准备择补出满足274.1的整个全有限层级，也不反驳274.3。

证明。部分转置是保迹、迹配对正交的实线性对合，将 PSD 序运输到 $T_1\operatorname{PSD}$，故运输完整菜单、M、互易和整个实际面；两锥的 Sep/BP 界由产品投影在 $T_1$ 下仍为产品投影得到。对两个模型中相同的原产品矩阵，读数始终是 $\operatorname{Tr}[(A\otimes B)(E\otimes F)]=\operatorname{Tr}(AE)\operatorname{Tr}(BF)$。Bell 投影属于前者，不属于后者，因为其部分转置有负本征值。若把原产品位置交换也列入二层合同，后者同样保持：交换把 $T_1\operatorname{PSD}$ 变为 $T_2\operatorname{PSD}=T_1\operatorname{PSD}$。本例只定位二层读数保留的区别，274.3的三层相容性才排掉第二种方向。$\square$

**推论 274.5（几何、量子公理字典及仍未支付的桥）。** 在274.3的完整前提和普通条件供应下，令 $\Theta_N=\theta^{\otimes N}$，则所有有限层的原纯准备为 $\mathbb{CP}^{n^N-1}$；每张实际二纯面是复二维支持的整个密度球。取同一个整层迹尺 $g_N(x,y)=\operatorname{Tr}(\Theta_Nx\,\Theta_Ny)$，在迹零方向上其球心为支持投影的一半、半径为 $1/\sqrt2$。这个尺从已得整锥坐标读取，不是274.1的输入。所有原高层最小确认和数值互易，特别 $\mathsf R_3$，同样成为结论。

| 原对象或同一行另外给出的条件 | 精确对应 |
| --- | --- |
| 全部原归一态、纯态、混合及完整 proper 效应 | 全部密度矩阵、秩一投影、凸混合及 $0\preceq E\preceq I$；原配对为 $\operatorname{Tr}(E\rho)$ |
| 全部有限单位分解与纯目标 least 确认 | 全部数学 POVM 及 PVM 特例；$e_{P_v}(x)=\operatorname{Tr}(P_v\Theta_Nx)$，纯端点比较为 $|\langle v,w\rangle|^2$ |
| 原所有有限联合锥、产品、重括号、置换和丢弃 | 同一复 Hilbert 局域坐标的张量积、全部纠缠态与偏迹 |
| 另给实线性分支在每个有限相关旁观输入上为正，并给整个正输入上的不增质量／守质量预算 | 矩形 CP 的 Kraus 形式及 TNI／TP；仪器还须所有分支之和的总单位预算 |
| 另给同层正实线性 $L$，$u_N\circ L=e_P$ 对应投影 $P$，且对每个 certain-yes 原纯态 $p$ 有 $Lp=p$ | 唯一理想锐更新 $X\mapsto PXP$ |
| 另给连续可逆保锥保单位的一参数群 | 酉共轭及 Hamilton 生成元形式；物理时钟、能量与 $\hbar$ 标定仍独立 |

证明。这些行逐项消费已得整锥、单位和原张量配对，以及273.5／270.13的完整条件过程字典；特别保留锐更新供应的正实线性、效应恒等式和整个 yes 支持逐点中性。不从静态互易推出设备、仪器可用性或先后更新可交换，也不增加无限维、近似稳定性或资源最优性的结论。

本节新增的 repo-derived 接合是：把271的迹二方法扩到任意两个矩阵因子的局域二维支持，取得一个全域统一的秩二方向；再以真实三层 Bell 边缘消去低二层的相对转置，并仅提取164.11所需的单只三腿种子。这使需要显式输入的数值互易停在整个 $K_2$，不用先供整个 $K_3$ 的互易。相对于保持不变的 $\mathsf F+\mathsf M_3+\mathrm{L2}_3$，$\mathsf R_3$ 由272下降到 $\mathsf R_2$，而274.3给反向后果；因此这里证明的是入口冗余可消去，不宣称严格逻辑更弱或最少独立公理。

正对偶剥离、GB 球及其 HS／迹预算、块正零边缘、严格凸性、连通选择、Schmidt 分解、Jordan 分类、产品保持分类和全有限传播均保留所列成熟或仓内供应的归属。274.2并不消费或改称 Barnum—Wilce 的 Jordan 复合定理；其局域矩阵类型只在274.3的第一步取得后使用。对称 spectral／Jordan 文献也不能在尚无互易时提前代付[M274]的完整桥。本节不申领全球优先性、相对273的严格弱化或物理实现。

更大的原问题仍保留：$\mathsf F+\mathsf M_3+\mathrm{L2}_3$ 是否自行给 $\mathsf R_2$，以及只再给 $\mathsf R_1$ 是否足够，均未由本节证明或反驳。四点有限交换条件273也未由这些较弱前件导出。

白话说，先让每种纯准备都有一只对所有混合输入都一致的最小确认测试，并保留“两种纯准备真正撑起整颗三维球”。交换比较对象后读数不变，这一条只需先要求在两份系统的全部纯准备之间成立；两份内部可以纠缠。第三份系统的作用，是要求三条边确实来自同一个整体，排掉各边单独看都合法、拼在一起却不相容的转置方向。随后一只明确的三腿相干准备就接上已有全有限重建，所有更高份的量子态、Born 读数和互易随之确定。这里仍没有把最小确认本身当作互易的证明。$\square$

[F274]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "240.1—240.2的实际L2及外三角下界；250.1的强全有限原背景。"
[M274]: ../../../Library/QuantumStates/mullerududec2012selfduality.md "Complete conditional candidate and its scope：完整proper最小确认加数值互易到规范迹Jordan几何的纸面桥；精确消费Barnum—Müller—Ududec Theorem16的导出前件。"
[N274]: ../../../Library/QuantumStates/barnumhilgert2019spectral.md "The matrix carrier and exact product contract；Conditional normal-form theorem and proof；Xu—Zheng—Fošner，Main Theorem，p.409，(1.1)—(1.2)，固定合同与输入转置。"
[T274]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "164.1的已对齐低二层全有限原域；164.10的明确tau_n及六副本十八腿；164.11的3⇒4；164.12的字典与过程边界。"

## 追加锚（本行以下为增补区）

## 275. 对角支撑的秩三接合、四接触补全与单复制互易

**定义 275.1（互易只输入到单复制）。** 完整保留274.1的全有限原背景 $\mathsf F$、整个 $K_3$ 上的 $\mathsf M_3$ 与实际 $\mathrm{L2}_3$，不缩减原载体、原纯点、完整 proper 菜单、全部有限单位分解或任意相关输入上的各分块 min/max 界。额外的数值条件只为

$$
\mathsf R_1:\qquad e_p^1(q)=e_q^1(p)\qquad(p,q\in P_1).
\tag{275.1}
$$

较高层的互易、矩阵类型、共同尺、正面压缩及面效应延拓均不作为输入。以下在274.2的统一 Schmidt 秩二覆盖之外，使用[XVIII240.5][Q275]的纯几何纸面供应：实际 L2 加全称三点面齐次维数至多九，给每个非共球三点的整个实际 qutrit 面。该九维上界将在明确构造的原暴露面内支付，不加到整个未知原锥。

**定理 275.2（任意矩阵尺寸的整锥补全）。** 在整个原实载体 $H_m\otimes_{\mathbb R}H_n$、普通迹单位、完整 proper 菜单和整个迹一紧底上，设 $m,n\ge2$、$\operatorname{Sep}(m|n)\subseteq C\subseteq\operatorname{BP}(m|n)$，并要求 M 与实际 L2。相对于274.2及[Q275]的上述供应，有

$$
\boxed{\quad C=C^*=\operatorname{PSD}_{mn}\quad\text{或}\quad
C=C^*=T_A\operatorname{PSD}_{mn}.\quad}
\tag{275.2}
$$

对偶取普通迹配对，$T_A$ 为固定第一因子基的部分转置。这里不输入数值互易。

证明。（一）固定共同方向并支付支撑。令 $P_\psi=\psi\psi^*/\|\psi\|^2$，$\mathcal S_k$ 为所有 Schmidt 秩至多 $k$ 的 $P_\psi$ 生成的锥。274.2给一个共同 $\delta$，使 $T_A^\delta\mathcal S_2\subseteq C\cap C^*$。对整个锥和逆对偶菜单作保迹正交坐标运输，置 $D=T_A^\delta C$。于是

$$
\mathcal S_2\subseteq D\cap D^*,\qquad
D,D^*\subseteq\mathcal S_2^*.
\tag{275.3}
$$

M、实际面、L2和 Sep/BP 夹逼均随这个序坐标运输；并未把部分转置宣布为原正操作。

任选局域正交归一族 $a_1,\ldots,a_r$、$b_1,\ldots,b_r$，$r\le\min(m,n)$。置

$$
v_i=a_i\otimes b_i,\quad W_r=\operatorname{span}_{\mathbb C}\{v_i\}_{i=1}^r,
\quad P_W=\sum_iP_{v_i},\quad Q_W=I-P_W,\quad
Z_r=\{X\in K_D:\operatorname{Tr}(Q_WX)=0\}.
\tag{275.4}
$$

将两族补为局域正交基，$P_W,Q_W$ 都是产品基投影之和，因而是整个原菜单中的互补 proper 效应。$Z_r$ 是原暴露面，且

$$
Z_r\subseteq\mathcal D(W_r).
\tag{275.5}
$$

为证275.5，$Q_W$ 的所有产品对角读数非负，零和使每个未选产品基向量的对角元为零。任意两个产品基向量的线性组合 Schmidt 秩至多二，275.3使其二阶主矩阵 PSD；零对角元遂消去整个对应行列。故 $X=P_WXP_W$。对任意 $\xi=\sum_i\xi_i v_i$，产品向量 $z=(\sum_i\xi_i a_i)\otimes(\sum_i b_i)$ 满足 $P_Wz=\xi$，所以块正性给 $\langle\xi,X\xi\rangle=\langle z,Xz\rangle\ge0$。这才证明支持内 PSD；不假定原压缩映射为正。

（二）新增秩一态的原全域确认。若单位 $\psi\in W_r$ 已有 $P_\psi\in D$，则它位于 $Z_r$，由275.5是该面的极点，因而是整个 $K_D$ 的原纯点。原 proper 效应 $P_W$ 确认它，M 给 $0\le_{D^*}e_{P_\psi}\le_{D^*}P_W$。在未选产品基态上评价，所得零对角元结合275.3的二阶主矩阵正性，将这个**原全域**效应也限制到 $W_r$。同（一）的产品向量论证给支持内 $e_{P_\psi}\succeq0$。

对任一只占至多两个 $v_i$ 坐标、且 $s\perp\psi$ 的单位向量，

$$
g_s=P_W-P_s\in[0,I]_{D^*}.
\tag{275.6}
$$

事实上，在这两个坐标里 $P_W-P_s$ 的对应项是另一只 Schmidt 秩至多二投影，其余项是产品投影；其补 $I-g_s=Q_W+P_s$ 也为已知原正效应之和。故 proper 性支付在整个原菜单。$g_s(P_\psi)=1$，leastness 与已知原态 $P_s\in D$ 给

$$
0\le\langle s,e_{P_\psi}s\rangle\le\langle s,g_ss\rangle=0.
\tag{275.7}
$$

写 $\psi=\sum_i c_iv_i$ 并选 $c_k\ne0$，向量 $\overline{c_i}v_k-\overline{c_k}v_i$（$i\ne k$）是 $r-1$ 个独立的此类正交方向，张满 $\psi^\perp\cap W_r$。支持内 PSD 使 $e_{P_\psi}$ 消去它们；确认值一遂给

$$
\boxed{\quad e_{P_\psi}=P_\psi\in D^*.\quad}
\tag{275.8}
$$

这个步骤在每次补出新态之后供应其原全域效应，不借用面内效应延拓。

（三）在真实九维面内补齐秩三。若 $\min(m,n)\ge3$，取 $r=3$。由275.3，每个坐标二支持的整个普通密度球 $\mathcal D(\operatorname{span}\{v_i,v_j\})$ 都在 $Z_3$。三颗球共同张满九实维 $\operatorname{Herm}(W_3)$，故 $\dim_{\mathbb R}\operatorname{span}Z_3=9$。它们也是这些坐标纯点的实际二点面：与普通 PSD 支持面的交给 $Z_3$ 的一个实际面，恰为该整球；整球内任意两个不同纯点的最小面就是整球。

设 $G$ 是三个 $P_{v_i}$ 的最小原实际面。$G\subseteq Z_3$，又含每对中点，因此由面性质含那对的整颗球。故 $G$ 张满九维，是 $Z_3$ 的满维面，只能等于 $Z_3$。特别地三个点不共处一个实际二点球。

现在仅把这个原实际面作为辅助凸几何载体。它的所有实际面仍是原实际面，继承实际 L2；它自身齐次维数九，故其中所有实际三点面自动满足 TF9。精确调用[Q275,240.5]，得 $Z_3$ 仿射同构于整个 qutrit 密度体。这里使用该供应的几何结论，不将面内完整几何对偶当成原全域可用效应。

还须对齐当前矩阵坐标。将该仿射同构齐次延拓为保迹线性同构 $L:H_3\to\operatorname{Herm}(W_3)$，有 $L(\mathcal D_3)=Z_3\subseteq\mathcal D(W_3)$。原效应族 $P_{v_1},P_{v_2},P_{v_3},Q_W$ 的前三项在 $Z_3$ 上和为一，并完全区分三个坐标纯点。拉回至标准 qutrit，三个纯原像因完全可区分而构成正交基；在源端选一个酉坐标后，可设 $L(P_i)=P_{v_i}$。

$L$ 因而把每个标准坐标二支持密度球满射到上述同名实际球，并固定其两极。球的仿射自同构固定中心且在 Bloch 方向上正交；固定纵轴后，其二维非对角实空间上为 $O(2)$。三个对角方向固定，三个非对角二维空间在 HS 配对下互相正交，所以 $L$ 在整个 $H_3$ 上为 HS 正交映射。因此 $L(\operatorname{PSD}_3)$ 对当前迹配对自对偶。对包含关系取对偶给

$$
L(\operatorname{PSD}_3)\subseteq\operatorname{PSD}(W_3)
\quad\Longrightarrow\quad
\operatorname{PSD}(W_3)\subseteq L(\operatorname{PSD}_3)^*
=L(\operatorname{PSD}_3).
\tag{275.9}
$$

故 $Z_3=\mathcal D(W_3)$。任意 Schmidt 秩三向量可置入这样的一对局域 Schmidt 基；结合（二），得到 $\mathcal S_3\subseteq D\cap D^*$。

（四）四个接触点补齐更高秩。先使用如下欧氏椭球事实，其证明附于本步以明确接触条件：若满维椭球 $E\subseteq\overline{\mathbb B}^3$ 有四个仿射无关的外球面接触点，则 $E=\overline{\mathbb B}^3$。写 $E=c+A\overline{\mathbb B}^3$，$A$ 可逆，$Q=A^TA$、$b=A^Tc$。接触点的逆像 $s_i$ 为单位球面上 $q(s)=s^TQs+2b^Ts+\|c\|^2$ 的全局最大点，值一。在 $s_0$ 用乘子 $Qs_0+b=\lambda s_0$。对 $s_0\cdot v\ne0$，令 $t=-2s_0\cdot v/\|v\|^2$，则 $s_0+tv$ 也在单位球面，且

$$
0\le q(s_0)-q(s_0+tv)=t^2v^T(\lambda I-Q)v.
\tag{275.10}
$$

由稠密性，$\lambda I-Q\succeq0$。其他接触点给 $(s_i-s_0)^T(\lambda I-Q)(s_i-s_0)=0$。三个差向量独立，故 $Q=\lambda I$、$b=0$、$c=0$，最后由最大值一得 $\lambda=1$。

对 $r\ge4$，归纳假定 $\mathcal S_{r-1}\subseteq D\cap D^*$。取目标 $\psi=\sum_{j=1}^r c_jv_j$，$c_j\ne0$；选互异非零复数 $t_j$，前四个为 $1,-1,\mathrm i,2\mathrm i$，并置 $\eta=-\sum_j(c_j/t_j)v_j$。每个 $\psi+t_j\eta$ 恰消去第 $j$ 个 Schmidt 项，其余项非零，故归一投影 $p_j$ 是已知 Schmidt 秩 $r-1$ 原纯态。纯性可由（二），或由271.9的 HS 单位球严格凸性取得。

令 $L_0=\operatorname{span}_{\mathbb C}\{\psi,\eta\}$、$F=Z_r\cap\mathcal D(L_0)$。275.5使 $F$ 为 $Z_r$ 的实际面，继而是整个 $K_D$ 的实际面；不要求 $P_{L_0}$ 为原 proper 效应。实际 L2 给

$$
B(p_1,p_2)\subseteq F\subseteq\mathcal D(L_0).
\tag{275.11}
$$

两端均为仿射三维，所以左端是 $F$ 的满维面，等于 $F$，并包含所有 $p_j$。前四个是外层普通密度球球面上的仿射无关点：源向量 $(1,t_j)$ 的 dyad 在实坐标 $(1,\operatorname{Re}t,\operatorname{Im}t,|t|^2)$ 下形成矩阵

$$
\begin{pmatrix}1&1&0&1\\1&-1&0&1\\1&0&1&1\\1&0&2&4\end{pmatrix},\qquad\det=-6.
\tag{275.12}
$$

映到 $L_0$ 的可逆合同及各项正归一化保留齐次线性独立，亦即四个迹一投影仿射独立。四接触点事实于是给 $B(p_1,p_2)=\mathcal D(L_0)$，特别 $P_\psi\in D$；（二）再给 $e_{P_\psi}=P_\psi\in D^*$。归纳到 $r=\min(m,n)$ 完成。若该最小维数为二，275.3已经覆盖所有秩一投影，无需（三）—（四）。

全部秩一投影现均属于 $D\cap D^*$。谱分解及普通 PSD 自对偶性给 $\operatorname{PSD}_{mn}\subseteq D,D^*$，因而 $D=D^*=\operatorname{PSD}_{mn}$。运输回共同方向即275.2。$\square$

**定理 275.3（单复制互易足够）。** 在275.1的完整原域，相对于[M274]的单层完整 M 加互易到规范迹 Jordan 几何纸面桥、[Q275]的几何供应以及[T274]的全有限传播，下列等价：

$$
\mathsf M_3+\mathrm{L2}_3+\mathsf R_1
\quad\Longleftrightarrow\quad
\exists n\ge2,\ \theta:V\overset\sim\longrightarrow H_n:\quad
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\quad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{275.13}
$$

证明。M 和实际 L2 由272下降到一、二层。只对单体调用[M274]的完整 M 加已输入 $\mathsf R_1$ 的桥；实际三球排除其他 Jordan 类型及非平凡直和，如274.3第一步，得到同一个保单位局域坐标 $\theta:V\to H_n$，$C_1=\operatorname{PSD}_n$、$n\ge2$。尚不分类 $C_2$。

在固定的原张量坐标中，整个 $C_2$ 满足275.2，参数为 $n|n$，所以 $C_2=T_1^\varepsilon\operatorname{PSD}_{n^2}$。在实际分块 $(12)|3$ 中运输 $C'_3=T_1^\varepsilon C_3$；两个完整局域锥现为 PSD，整个 M、L2、菜单和 min/max 原样运输。再用275.2，得一个共同 $\delta$，使

$$
C_3=T_1^\varepsilon T_3^\delta\operatorname{PSD}_{n^3}.
\tag{275.14}
$$

这里 $T_{12}$ 与 $T_3$ 在整个 PSD 锥上的像相同，因为其复合为全转置。三种错误方向的真实 Bell 边缘已由274.3（三）的三个明确来源投影逐项排除：$(1,0)$ 用 $P_0^{(1)}\otimes B_{23}$，$(1,1)$ 和 $(0,1)$ 用 $B_{13}\otimes P_0^{(2)}$；原正丢弃与原正置换要求输出落入同一个 $C_2$，而 Bell 部分转置的反对称本征值为 $-1/2$。因此 $\varepsilon=\delta=0$，$C_2,C_3$ 已为同一 $\theta$ 下的标准 PSD。

于是 $\tau_n=\sum_{i=0}^{n-1}|ii0\rangle+|011\rangle$ 的 dyad 属于原 $C_3$，迹质量 $n+1$。这精确给[T274,164.11]的条件3，且其标准低二层、全部有限 min/max 与相关输入等前件均已支付。直接消费 $3\Rightarrow4$，得到275.13的全有限结论。此路线只对单体使用 Jordan 桥；不再靠一个已分类的双体及产品保持正规形来取得 $C_2$。

反向标准复层级的完整菜单有投影 least 确认、复二维支持三球和单体迹互易，故满足左边。$\square$

**推论 275.4（几何、量子字典及剩余的内生桥）。** 在所列完整前提和纸面供应下，原纯准备为 $\mathbb{CP}^{n^N-1}$，实际二纯面为整个复二维密度球，整层共同尺为 $\operatorname{Tr}(XY)$。全部原归一态、proper 效应、有限单位分解及配对分别给密度矩阵、$0\preceq E\preceq I$、全部数学 POVM 和 $\operatorname{Tr}(E\rho)$；原全有限产品、相关输入及丢弃给同一复 Hilbert 坐标下的完整张量积与偏迹。

较高层的完整 least 确认和全部数值互易均成为结论。结合272的下降，在保持不变的 $\mathsf F+\mathsf M_3+\mathrm{L2}_3$ 及所列供应下，$\mathsf R_1\Longleftrightarrow\mathsf R_2\Longleftrightarrow\mathsf R_3$；这是互易输入层数的冗余消除，不是严格逻辑弱化或最少独立公理数的证明。275.2的整锥结论现有明确的秩三接合和高秩归纳；不能把它回填为274.2单独已给的一般整锥分类。

CP、TNI／TP、仪器、锐更新及 Hamilton 形式逐项保留274.5的额外过程条件：所有有限相关旁观输入的分支正性、整个正输入及分支之和的预算；同层正实线性更新的确切效应和所有 certain-yes 纯态的逐点中性；另给连续可逆保单位群。静态起点不供应这些设备，也不标定物理时钟、能量与 $\hbar$，不推出先后仪器可交换。

新增的仓内接合是：统一秩二方向给明确可分效应暴露的对角支撑面；该面内自动支付九维几何供应，且将抽象 qutrit 坐标对齐原矩阵坐标；四个已知低秩接触点再补齐任意有限 Schmidt 秩。每次新增态的全域效应由275.6—275.8支付。GB 球、M-only 剥离、既有秩二构造、Hermitian Veronesean 分类和240.5、欧氏二次型、Schmidt／谱分解以及有限传播各保留其成熟或仓内归属；本节不申领这些工具的新意、全球优先性、Lean／kernel 认证或物理实现。

完全删去单体互易仍未完成。只知道 $e_p(q)=0\Longleftrightarrow e_q(p)=0$，并不保证某张实际球的内禀对跖点可以由原全域 proper 效应读成一与零；若这个对跖分离条件能从其余原前件导出，既有球内半球比较桥才给 $\mathsf R_1$，继而应用275.3。这里没有把该条件列成新公理，也没有给满足全部原域的反模型。

白话说，先只在一份系统里要求两边交换比较对象后读数不变。两份系统已有的二方向相干准备，先围出一块真正九维的三方向小世界；原来的整球关系把它补成完整 qutrit。更大的相干准备，再由四个已知低秩准备把同一颗实际球撑满，每一步的确认测试都在原完整菜单里付清。这样联合互易不用另给，三份整体的真实边缘统一方向后，就接回全部有限量子层级。仍要追的最后这类缺口，是球内几何上相反的两个纯准备，为什么一定有一只原全域测试把它们完全分开。$\square$

[Q275]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "240.1—240.5：实际 L2、外三角九维下界、TF9 到 TC、纯扇穷尽及实际 qutrit 面；240.5 的几何供应经 XIII160.4 使用 Schillewaert—Van Maldeghem 的 Hermitian Veronesean Caps, Theorem2.4。"

## 追加锚（本行以下为增补区）

## 276. 产品提升锁定共同确认、无复合球的整锥补全

**定义 276.1（原二元共同确认与单体几何候选）。** 完整保留274.1的非平凡强全有限背景 $\mathsf F$：所有原有限张量载体及整个闭尖生成锥、严格正乘积单位、整个归一紧底和全部原纯点、完整正对偶及 proper 区间、全部有限单位分解、正位置置换及其正逆、正丢弃，以及包括任意相关输入的全部有限分块 min/max 界。对整个三份纯域定义二元关系约束，包含重复目标：

$$
\begin{aligned}
\mathcal E_3(p,q)&=\{f\in[0,u_3]_{C_3^*}:f(p)=f(q)=1\},\\
\mathsf J_3:\qquad
\forall p,q\in P_3\quad&\exists h_{p,q}\in\mathcal E_3(p,q):\quad
h_{p,q}\le_{C_3^*}f\quad(\forall f\in\mathcal E_3(p,q)).
\end{aligned}
\tag{276.1}
$$

重复目标给 $e_p^3=h_{p,p}$，即整个 $\mathsf M_3$。反向，有限维共同确认包的暴露性及271.7给 $\mathsf M_3\Rightarrow\mathsf J_3$，见[Q276S,274.13—274.14]。这只是同一最小确认信息的二元表示，不作为另一项输入计数。由271.46—271.47的纯旁观限制，M下降到一、二层，不消费实际L2。

仅在原单体保留实际 $\mathrm{L2}_1$：每对不同原纯点生成的最小实际面为整个实三维闭球的仿射像；并保留数值互易 $\mathsf R_1:e_p^1(q)=e_q^1(p)$。候选写为

$$
\boxed{\quad\mathsf Q_{\mathrm{one}}:=\mathsf J_3+\mathrm{L2}_1+\mathsf R_1
\quad\Longleftrightarrow\quad\mathsf M_3+\mathrm{L2}_1+\mathsf R_1.\quad}
\tag{276.2}
$$

二、三份实际球、较高层互易、容量界、qutrit分类及产品保持正规形均不输入。互易只交换被比较的两个端点，不断言先后仪器可交换。

**定理 276.2（M-only任意矩阵尺寸整锥分类）。** 在整个原 $H_m\otimes_{\mathbb R}H_n$ 上取普通迹单位，$m,n\ge2$，闭尖生成锥满足 $\operatorname{Sep}(m|n)\subseteq C\subseteq\operatorname{BP}(m|n)$，使用整个迹一紧底及完整 proper 菜单。仅要求整个原纯域上的M。相对于[Q276S,274.3]的M-only统一秩二供应，有

$$
\boxed{\quad C=C^*=\operatorname{PSD}_{mn}\quad\text{或}\quad
C=C^*=T_A\operatorname{PSD}_{mn}.\quad}
\tag{276.3}
$$

不要求实际L2或数值互易。这里的对偶为普通迹配对，$T_A$ 是固定第一因子基的部分转置。

证明。（一）原预算与对角支撑。精确复用[Q276S,274.3]，取得同一个 $\delta\in\{0,1\}$，使 $T_A^\delta\mathcal S_2\subseteq C\cap C^*$。令 $D=T_A^\delta C$；整个锥、逆对偶菜单及普通迹随保迹正交坐标运输，M保持。此处不将 $T_A$ 当成原物理正操作。于是

$$
\mathcal S_2\subseteq D\cap D^*,\qquad
D,D^*\subseteq\mathcal S_2^*\subseteq\operatorname{BP}(m|n),\qquad
\|X\|_2\le\operatorname{Tr}X\quad(X\in D\ \text{或}\ D^*).
\tag{276.4}
$$

最后一式是271.9的Gurvits—Barnum预算；特别正元素迹零即零。整个迹一原底包含在HS单位球内，故其中HS范数一的点必为原纯点。原暴露面的least最大确认、其在整个 proper 区间的极端性，以及 $h_H-e_p$ 的极端性，只用271.5—271.7的M-only剥离。

固定局域正交归一族，沿用275.4的 $v_i=a_i\otimes b_i$、$W_r=\operatorname{span}_{\mathbb C}\{v_i\}$、$P_W=\sum_iP_{v_i}$、$Q_W=I-P_W$ 及 $Z_r$。275.2（一）证明的 $Z_r\subseteq\mathcal D(W_r)$ 只消费276.4：未选产品对角元为零，任意两产品基向量的二阶主矩阵正性消去对应行列，产品提升再给支持内PSD。它不消费L2。

同一论证还给以下原效应版本：若 $0\le_{D^*}h\le_{D^*}P_W$，则

$$
h=P_WhP_W,\qquad 0\preceq h|_{W_r}\preceq I_{W_r}.
\tag{276.5}
$$

确实，$h$ 和 $P_W-h$ 都在 $\mathcal S_2^*$。未选产品对角读数均非负且和为零，二阶主矩阵消去行列；任意 $\xi=\sum_i\xi_i v_i$ 是产品向量 $(\sum_i\xi_i a_i)\otimes(\sum_i b_i)$ 在 $W_r$ 上的投影，所以块正性同时给两者在 $W_r$ 内PSD。这里证明的是这些已给原效应的矩阵支持，不假定原压缩映射保正或任意面效应可延拓。

若 $P_\alpha\in D$ 且 $\alpha\in W_r$ 为单位向量，则它的HS范数一，故原纯性已付。275.2（二）的两稀疏正交测试同样不消费L2，逐字给 $e_{P_\alpha}=P_\alpha\in D^*$。特别已知全部Schmidt秩至多二的投影均有这一原全域least确认。

（二）产品提升将共同确认锁成二支持投影。取两个线性独立单位向量 $\alpha,\beta\in W_r$，其投影已属于原 $D$。由[Q276S,274.13—274.14]的共同确认包，取得原全域共同least效应 $h$；它是原暴露包的least最大确认，且为整个 proper 区间的极点。因为 $P_W$ 共同确认两端，有 $h\le_{D^*}P_W$。276.5于是给支持内PSD收缩。确认值一使 $h\alpha=\alpha$、$h\beta=\beta$；写 $L=\operatorname{span}_{\mathbb C}\{\alpha,\beta\}$，则 $h$ 在 $L$ 上恒等。

对每个非零 $\eta=\sum_i\eta_i v_i\in W_r\cap L^\perp$，取

$$
z_\eta=\left(\sum_i\eta_i a_i\right)\otimes\left(\sum_i b_i\right),
\qquad P_Wz_\eta=\eta,\qquad s_\eta=z_\eta/\|z_\eta\|.
\tag{276.6}
$$

归一产品投影 $P_{s_\eta}$ 与其补均可分，故为整个原菜单的 proper 效应；$P_{s_\eta}$ 同时是原产品态。因为 $z_\eta$ 与 $\alpha,\beta$ 正交，$I-P_{s_\eta}$ 是原全域共同确认者。leastness遂给

$$
0\le\operatorname{Tr}(hP_{s_\eta})
\le\operatorname{Tr}((I-P_{s_\eta})P_{s_\eta})=0,
\qquad
\langle\eta,h\eta\rangle=\|z_\eta\|^2\operatorname{Tr}(hP_{s_\eta})=0.
\tag{276.7}
$$

支持内PSD使 $h\eta=0$。全部 $W_r\cap L^\perp$ 都被消去，支持外也已为零，因此

$$
\boxed{\quad h=P_L\quad\text{作为整个原载体上的效应}.\quad}
\tag{276.8}
$$

这一步的见证来自真正的全域产品测试。$P_L$ 的原proper性是least确认结论，不能在此前由普通矩阵PSD冒领。

（三）一只正交二稀疏方向完成全部秩归纳。Schmidt秩至多二的投影已有276.4。设全部秩至多 $r-1$ 的投影已在 $D\cap D^*$，并有原least确认，$3\le r\le\min(m,n)$。取任意秩 $r$ 的向量，写其Schmidt展开 $\psi=\sum_{j=1}^r c_jv_j$，每个 $c_j\ne0$；投影始终按 $P_x=xx^*/\|x\|^2$ 归一。令

$$
u=\overline{c_2}v_1-\overline{c_1}v_2,\qquad
\lambda=-c_1/\overline{c_2},\qquad
w=\psi+\lambda u.
\tag{276.9}
$$

则 $\langle\psi,u\rangle=0$，$u$ 有Schmidt秩二，$w$ 的第一坐标为零，第二坐标为 $(|c_1|^2+|c_2|^2)/\overline{c_2}\ne0$，其余坐标不变，故秩恰为 $r-1$。$u,w$ 独立且 $\operatorname{span}\{u,w\}=\operatorname{span}\{u,\psi\}$。归一两者后，原纯性与各自least确认均由归纳前件及（一）支付。

对这两端用（二），得原共同least $h=P_L$。因为 $P_u$ 在共同暴露包内，271.7的极端残余给

$$
d=h-e_{P_u}=P_L-P_u=P_\psi\in[0,I]_{D^*},
\qquad d\in\operatorname{ext}[0,I]_{D^*},\qquad\operatorname{Tr}d=1.
\tag{276.10}
$$

还须证明这个原效应确实是原态，不能从它的普通PSD形式直接推出。精确使用[Q276S,276.2（三）]的迹一极端效应论证：令 $t=\max_{x\in K_D}\operatorname{Tr}(dx)$。原生成性使 $t>0$，proper性给 $t\le1$；若 $t<1$，则 $d=t(d/t)+(1-t)0$ 是非平凡 proper 分解，违背极端性。因此 $t=1$，取一个原最大点 $x$，276.4给

$$
1=\operatorname{Tr}(dx)\le\|d\|_2\|x\|_2
\le\operatorname{Tr}d\operatorname{Tr}x=1.
\tag{276.11}
$$

Cauchy—Schwarz全取等号及两者迹一使 $d=x$、$\|x\|_2=1$。故 $P_\psi=d$ 确属原纯态，再由（一）取得原least确认 $e_{P_\psi}=P_\psi$，归纳闭合。这里无需对尚未证明为原态的残余预先调用M。

全部有限Schmidt秩因而都补齐。普通谱分解给 $\operatorname{PSD}_{mn}\subseteq D\cap D^*$；普通PSD自对偶性又使两锥都包含于PSD，所以 $D=D^*=\operatorname{PSD}_{mn}$。运输回原坐标得276.3。整个证明没有调用三点面、九维上界、抽象qutrit坐标对齐或四接触椭球结论。$\square$

**定理 276.3（实际球只需输入到单体）。** 在276.1的完整 $\mathsf F$ 下，相对于[M274]的完整M加数值互易到规范迹Jordan几何纸面桥、[Q276S,274.3]及[T274,164.11]的全有限传播，有

$$
\mathsf Q_{\mathrm{one}}\quad\Longleftrightarrow\quad
\exists n\ge2,\ \theta:V\overset\sim\longrightarrow H_n:\qquad
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\quad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{276.12}
$$

证明。M由纯旁观限制下降，故只对单体调用完整 $\mathsf M_1+\mathsf R_1$ 到Jordan几何的具名桥。$\mathrm{L2}_1$ 排除直和及非复简单类型，具体支付与274.3（一）、275.3首步相同：跨扇区二纯面是线段，实、复、四元数、Albert的二支持球实维数分别二、三、五、九，spin factor也只能保三球。得到同一个保单位局域坐标 $\theta:V\to H_n$、$C_1=\operatorname{PSD}_n$，$n\ge2$。

整个 $C_2$ 的 $n|n$ 分块现满足276.2；其M从三份下降，不需要 $\mathrm{L2}_2$。故 $C_2=T_1^\varepsilon\operatorname{PSD}_{n^2}$。在真实 $(12)|3$ 分块令 $C'_3=T_1^\varepsilon C_3$；局域整块变成 $\operatorname{PSD}_{n^2}$、$\operatorname{PSD}_n$，完整锥、菜单、单位及min/max随逆对偶一起运输。276.2再次给整个

$$
C_3=T_1^\varepsilon T_3^\delta\operatorname{PSD}_{n^3}.
\tag{276.13}
$$

第一块转置 $T_{12}$ 与 $T_3$ 对整个PSD给相同像；这里仍只是坐标运输。准确使用274.3（三）的同一实现Bell边缘表：$(1,0)$ 用来源 $P_0^{(1)}\otimes B_{23}$；$(1,1)$、$(0,1)$ 用来源 $B_{13}\otimes P_0^{(2)}$。正丢弃及正位置置换要求其边缘属于同一个 $C_2$，而前两项给标准Bell落入转置PSD、第三项给部分转置Bell落入PSD；反对称本征值 $-1/2$ 逐项排除。因此 $\varepsilon=\delta=0$。

于是明确 $\tau_n=(\sum_i|ii\rangle)|0\rangle+|01\rangle|1\rangle$ 的dyad属于原 $C_3$，质量 $n+1$。同一个 $\theta$ 下标准低二层、这只准确种子及未缩减的 $\mathsf F$，支付[T274,164.11]条件3到条件4，给全部有限层276.12。六份种子、十八条实际腿及所有相关旁观输入仍属于此供应；三层上只给M不等于只定义三层锥。

反向，在标准复PSD模型，每对原纯射线的共同least确认为其张成支持的投影，包含重复端点；实际二纯面为完整三球，单体Born迹配对互易，故满足276.2。$\square$

**推论 276.4（生成的几何、量子字典及仍未删除的条件）。** 在276.3的完整条件与具名纸面供应下，原共同least确认成为复子空间的支持join；对角支撑内的产品提升见证把其正交补逐点消去。这些支持投影的join、投影补及正交锐单位分解共同嵌入同一有限复投影格，原纯域为 $\mathbb{CP}^{n^N-1}$，所有层的实际二纯三球、完整least确认与数值互易都成为输出。

证明与对应。276.12中 $h_{P_v,P_w}=P_{\operatorname{span}\{v,w\}}$，$e_{P_v}=P_v$；面为支持内全部密度矩阵，互易为 $\operatorname{Tr}(P_vP_w)=\operatorname{Tr}(P_wP_v)$。所有归一态、完整proper菜单、有限单位分解及原配对依次给密度矩阵、$0\preceq E\preceq I$、全部数学POVM／PVM及Born概率 $\operatorname{Tr}(E\rho)$；原全有限产品、置换、丢弃给同一局域坐标的复张量与偏迹。

过程字典精确保留274.5的独立前件：分支在所有有限相关旁观输入上保正才得CP；原整个正输入及各分支总预算才给TNI／TP与仪器；锐效应及所有certain-yes纯态逐点中性才给Lüders；另给连续可逆保单位群才读数学酉动力学与Hamilton形式。静态理论不提供设备、物理时钟、能量或 $\hbar$ 标定，也不据端点互易推仪器顺序无关。

相对于275.3，这个候选去掉二、三份实际L2前件及qutrit几何供应，仅单体三球用于复数类型选择；同一剩余背景中二者均刻画复量子模型，故不声称严格不同的模型类、最少独立公理数或完全由定义唯一选出物理规律。仅有J而删除类型条件时，经典全有限正锥层级仍满足J：共同least是两原坐标的指示效应，却有线段二纯面，不能通过 $\mathrm{L2}_1$。这说明共同门本身没有选出三球。

删除 $\mathsf R_1$ 仍未完成。精确的未付接口是：在原单体每张实际球上，每对内禀对跖纯点是否必有原**全域**proper效应读成一与零。M已有的零读数互易不自动给这个效应；若由剩余前件付清该接口，既有半球比较桥才推出完整数值互易。这里不把接口补成输入，也不给满足整个 $\mathsf F+\mathsf M_3+\mathrm{L2}_1$ 的反模型。

新增repo-derived接合是276.6—276.11：原产品提升将两个已知相干端点的共同least锁成准确二维投影，再用一个正交二稀疏方向和一次坐标消去，把任意高秩投影实现为迹一极端残余。它超出[Q276S,276.2]只对产品目标付least、只给统一秩二资源的结论；此处消费的是全纯域M给任意两个已知原纯点的共同least，未把产品目标条件擅自扩域。GB预算、剥离／补全、共同确认包、极端残余等号、Schmidt／谱分解、Jordan分类与全有限传播各保留成熟或既有仓内归属，不申领其发明、全球优先性、形式内核认证或物理实现。

白话：每颗准备都有一只只认必要对象的最小门；两颗准备也有一只不比任何共同确认者多认一点的共同门。现在把更大的准备写进同一张对角支撑图：每个应当被共同门挡住的方向，都能从一颗真的产品准备投影出来，它的补测试便迫共同门关闭那个方向。共同门因此恰好留下两颗准备撑开的平面。取一颗只占两个坐标、又与目标正交的准备，再把目标的一个坐标抵消，就得到一颗已知的较低秩准备；从两者的共同门扣掉第一颗的门，余下的只能是目标本身。这样全部高秩方向逐级长出，不再逐层规定联合世界必须是什么球。单体的三球和交换比较端点不改读数仍明确保留；三份真实边缘统一镜像方向后，既有全有限传播接出整套有限复量子结构。$\square$

[Q276S]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "274.3的M-only共同确认包与统一Schmidt秩二供应，含274.13—274.14；276.2（三）的迹一极端proper效应与双HS／迹预算等号。"

## 追加锚（本行以下为增补区）

## 277. 可筛出的二纯球：由第二张球排除确认塌缩

**定义 277.1（原全域暴露的二元几何候选）。** 完整保留276.1的非平凡强全有限背景 $\mathsf F$、全部原纯点、完整proper菜单、全部有限单位分解及所有相关输入上的分块min/max界。单体 $K=K_1$、$P=P_1$、$\mathcal E=[0,u]_{C_1^*}$。对不同 $p,q\in P$，仍令 $B(p,q)=F_K(p,q)$ 为整个最小实际面。定义

$$
\mathrm{L2}^{\mathrm{exp}}_1:\quad
\forall p\ne q\in P,\quad
B(p,q)\text{ 仿射同构于完整非退化实三维闭球，且 }
\exists f_{p,q}\in\mathcal E:\ \{x\in K:f_{p,q}(x)=1\}=B(p,q).
\tag{277.1}
$$

全体 $K$ 由 $u$ 暴露；真球的测试必须属于原全域菜单，不能只定义在球内。候选为

$$
\boxed{\quad \mathsf Q_{\mathrm{exp}}:=\mathsf M_3+\mathrm{L2}^{\mathrm{exp}}_1
\quad\Longleftrightarrow\quad
\mathsf J_3+\mathrm{L2}^{\mathrm{exp}}_1.\quad}
\tag{277.2}
$$

J与M的互换只用276.1的同一全纯域成对确认包，包含重复目标。本定义不输入数值互易、端点唯一饱和、一般正面回缩或任意局部效应延拓。暴露性仍是明确的几何条件，尚未由裸 $\mathsf F+\mathsf M_3+\mathrm{L2}_1$ 推出；也不把整个态空间断言为球。

**定理 277.2（暴露球上的确认二择）。** 设有限维整个紧底 $K$ 满足M，$B$ 是其原暴露实际三球，$p\in P\cap B$。取球坐标 $\iota:\overline{\mathbb B}^{3}\to B$、$p=\iota(a)$、$\|a\|=1$，写 $\bar p=\iota(-a)$。则恰有以下两种情形：

$$
e_p=h_B,
\qquad\text{或}\qquad
e_p(\iota(x))=\frac{1+a\cdot x}{2},\quad
e_p(\bar p)=0,\quad h_B=e_p+e_{\bar p}.
\tag{277.3}
$$

这里 $h_B$ 是271.7的原暴露面least最大测试。对 $B=K$，第一种情形不发生。

证明。精确复用271.5—271.7的M-only剥离与极端残余，不消费非零数值互易：$h_B$ 为整个proper区间的极点，$e_p\le h_B$，$d=h_B-e_p$ 也是其中的极点。若 $d=0$，得第一种情形。否则令 $m=\max_Kd$。正性、原生成性及proper预算给 $0<m\le1$；若 $m<1$，则 $d=m(d/m)+(1-m)0$ 是两个不同proper效应的非平凡凸组合，违背极端性。因此 $m=1$。在原纯最大点 $r$ 上，

$$
1=d(r)=h_B(r)-e_p(r)\le1-e_p(r)\le1,
\qquad r\in B,\quad e_p(r)=0.
\tag{277.4}
$$

球内的 $[0,1]$ 值仿射确认者具有形式 $e_p(\iota(x))=1-\beta+\beta a\cdot x$，$0\le\beta\le1/2$：其线性部分因在 $a$ 取最大值而沿 $a$，球上最小值非负给上界。式(277.4)迫 $\beta=1/2$、$r=\bar p$。$d$ 确认 $\bar p$，故 $e_{\bar p}\le d$。于是 $s=e_p+e_{\bar p}\le h_B\le u$，并在 $p,\bar p$ 取一。$s$ 的一面包含这两点生成的整个实际球，所以 $s$ 确认整个 $B$；$h_B$ 的leastness再给 $h_B\le s$，得到等号。第二种情形的球内零读数排除第一种。

若 $B=K$，球内半球函数本身是原全域proper确认者，故 $e_p$ 不可能等于 $h_K=u$。整个证明只在已存在的全域效应上取差，没有先为球内半球函数假设延拓。$\square$

**定理 277.3（第二张暴露球排除塌缩，互易成为输出）。** 在有限维整个紧底、完整菜单、M及实际L2下，若每张二纯实际球都为原暴露面，则任意 $p\ne q$ 所在同一实际球中的least确认均为标准半球函数。因此

$$
e_p(q)=\frac{1+a\cdot b}{2}=e_q(p),
\qquad p=\iota(a),\ q=\iota(b).
\tag{277.5}
$$

特别地，不必另假设不同端点严格可分，或 $e_p$ 在每张球上非恒定。

证明。固定 $B=B(p,q)$ 和球面点 $p$。若 $B=K$，用277.2。若 $B$ 为真面，存在原纯点 $r\notin B$，否则有限维极点分解会给 $K\subseteq B$。令 $B'=F_K(p,r)$；按前件它也是原暴露三球。假设277.2的塌缩分支 $e_p=h_B$。$h_{B'}$ 确认 $p$，leastness于是给

$$
h_B=e_p\le h_{B'},\qquad B\subseteq B'.
\tag{277.6}
$$

$B$ 是 $K$ 的面，所以也为 $B'$ 的面；两者都具有仿射维数三，面包含迫 $B=B'$，这与 $r\in B'\setminus B$ 矛盾。因此每个球面端点都落在277.3的半球分支。在同一球中分别用于 $p,q$，内积对称给(277.5)。这是端点读数互易，不是先后仪器交换。$\square$

**定理 277.4（几何候选的全有限量子对应）。** 在未缩减的 $\mathsf F$ 及276.3的同一具名纸面供应下，以下等价：$\mathsf Q_{\mathrm{exp}}$；$\mathsf M_3+\mathrm{L2}_1+\mathsf R_1$；存在 $n\ge2$ 和同一保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{277.7}
$$

证明。M从三份按271.46—271.47的原纯旁观限制下降到单份；277.3给 $\mathsf R_1$，故276.3完整适用。它先用具名M+R Jordan桥及单体L2选复类型，再用276.2的M-only整锥分类、同一实现Bell边缘及准确 $\tau_n$ 种子接164.11。无需复合实际L2、额外端点严格性或projectivity。反向，在(277.7)中两纯态生成面是二维复支持上的完整密度体，支持投影为原全域proper效应，且其一面恰为该实际三球；投影least确认给M3，满足277.2。

量子公理对应精确复用276.4：完整归一态、纯态、proper菜单、有限单位分解与原配对，给密度矩阵、复射线、全部数学POVM／PVM及Born迹概率；全部原有限产品、置换及丢弃给同一复张量与偏迹。所有有限相关旁观输入上的分支保正、整个正输入的质量预算和各分支总预算，仍分别用于CP、TNI／TP与仪器；锐效应及整个yes支持逐点中性用于Lüders，指定连续可逆保锥保单位群用于数学酉动力学。设备、物理时间、能量与 $\hbar$ 标定及无限／近似极限各保留独立前件。

277.2与276.2在同一剩余背景及供应下刻画同一模型类。这里将独立写出的数值互易转为可筛出二元球的几何约束，不声称严格更弱、最少独立公理或由定义唯一选出物理规律。$\square$

**推论 277.5（维数至九时不输入互易或暴露性）。** 完整保留 $\mathsf F+\mathsf M_3+\mathrm{L2}_1$，并相对于[XVIII240.2][G277]的外三角维数供应及277.4的同一供应。若 $\dim_{\mathbb R}V\le9$，则(277.7)成立，且 $n\in\{2,3\}$。所有有限层仍完整保留，维数条件只作用于单体。

证明。固定原二纯球 $B$。若 $B\ne K$，取它的相对内部点并选原支撑超平面。其暴露真面 $H$ 包含 $B$；支撑仿射函数按全局最大、最小值归一，故 $H$ 由原proper效应暴露。若 $H\ne B$，紧面中的有限纯点分解给原纯点 $r\in H\setminus B$。[XVIII240.2][G277]对原外三角 $p,q,r$ 给

$$
9\le\dim\operatorname{span}F_K(p,q,r)
\le\dim\operatorname{span}H
\le\dim V-1\le8,
\tag{277.8}
$$

矛盾。因此所有原二纯球均暴露，277.3支付 $\mathsf R_1$，再用277.4。重建后 $\dim_{\mathbb R}V=n^2\le9$、$n\ge2$，恰得 $n=2$ 或 $3$。反向，标准qubit及qutrit的整个有限复层级满足这些前件。这是原一般目标的受限结论，没有推出裸前件自动限制原维数。$\square$

**命题 277.6（一般缺口、来源和完整图景）。** 对未限制单体维数的 $\mathsf F+\mathsf M_3+\mathrm{L2}_1$，本节尚未推出 $\mathsf R_1$；若该互易失败，则至少一张原二纯实际球不是原暴露面，且 $\dim_{\mathbb R}V\ge10$。对这样的球，令 $H_B$ 为包含它的最小暴露面，则

$$
B\subsetneq H_B\subsetneq K.
\tag{277.9}
$$

证明与范围。互易失败的几何和维数位置由277.3、277.5的逆否命题得到，不给反模型存在性。真面包含于某暴露真面；有限维严格面链把所有这类暴露面的交化为有限交，平均其原proper确认效应便暴露该交，所以 $H_B$ 存在且仍为真面。对 $p\in P\cap B$，$h_{H_B}-e_p$ 是原极端proper残余；非零时满值点只保证属于 $H_B$，尚未保证属于 $B$。由于 $h_{H_B}=1$ 于 $B$，在指定球内取得满值点恰等价于 $e_p$ 在该球内取得零点，不把这个定位条件申领为严格更弱的公理。

[XIX278.3][D277]在M-only下给正对偶 $C_1^*$ 的全部实际面暴露及其规范单位支持，但该结论的承载对象是正对偶，不能据此将原 $C_1$ 的全部面认作暴露面；278.2用于唯一饱和的额外换点条件也没有加入本候选。一般维数尚缺从现有前件到原球暴露性、球内零点或数值互易的一条充分桥梁。

本节的repo-derived接合是：用第二张经过同一端点的原暴露球排除277.3的塌缩分支，从而将277.4的数值输入换成明示二元暴露几何，并用外三角维数供应闭合277.5的完整有限子类。暴露面least、极端减法及frame剥离复用271.5—271.7与[Q276S]；外三角维数复用[XVIII240.2][G277]；Jordan及全有限分类复用276的具名供应。有限维支撑、球上仿射函数和面维数工具保留成熟归属，不申领其发明、全球优先性或形式内核认证。Hilbert-ball与projective面在[AS271]所引刻画中的额外条件仍按271.4的边界保留；本节没有援引其分类来免费支付原球暴露性。

白话：两颗纯准备撑开一颗实心球，还要求整个世界里有一只合法测试能单独筛出这颗球。从筛球的门减去某端点自己的最小门，若还有剩余，这只不可再拆的残余测试就必须在某处完全打开；筛球门把这个位置压在球内，球的几何再迫它恰好是端点的正对面。因此端点自己的门从正面读一、反面读零，整颗球上的刻度都被锁定。如果两只门恰好相同，端点的门就会把整球都认作自己；但再拿一颗球外准备与该端点撑开第二张可筛出的球，最小性会逼第一颗球装进第二颗同维球，产生矛盾。这样，读数互易由可筛出的二元球和最小门共同长出；仍未完成的是一般维数下，能否连“球可以单独筛出”也从原关系中推出。$\square$

[G277]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "240.1—240.2：仅实际L2的原外三角仿射维数至少八、齐次维数至少九。"
[D277]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "278.3：M-only正对偶实际面及其规范单位支持；不等于原锥实际面的暴露性。"

## 追加锚（本行以下为增补区）

## 278. 独立块的共同收紧与单体可筛球：不向三份纠缠点逐一配门

**定义 278.1（只在真实独立块目标上要求共同确认）。** 完整保留276.1的非平凡强全有限背景 $\mathsf F$，包括全部原有限实张量载体和整个闭尖生成锥、严格正乘积单位、整个归一紧底与全部原纯点、完整正对偶及proper菜单、全部有限单位分解、标量零层、原产品与重括号、正置换及其正逆、正丢弃，以及含任意相关输入的全部有限分块min/max界。不限制单体维数，不删任何联合纯点。在原三份的固定真实分块 $(12)|3$ 上，令

$$
\mathcal B_3=\{a\otimes b:a\in P_2,\ b\in P_1\}\subseteq P_3,\qquad
\mathcal E_3=[0,u_3]_{C_3^*}.
\tag{278.1}
$$

二份块 $a$ 可以有块内纠缠；独立只指它与第三份的原产品。精确采用[XIX276.1][J278]的 $\mathsf J_3^{\mathrm{prod}}$：每对 $P,Q\in\mathcal B_3$（含重复）在整个 $\mathcal E_3$ 中有共同least确认。序比较同时作用于全部原相关三份输入，不改成仅产品读数。

单体采用277.1的 $\mathrm{L2}^{\mathrm{exp}}_1$：每对不同原纯点生成的整个最小实际面，与完整非退化实三维闭球仿射同构，且恰为某原全域proper效应的一面。候选为

$$
\boxed{\quad \mathsf Q_{\mathrm{prod,exp}}
:=\mathsf J_3^{\mathrm{prod}}+\mathrm{L2}^{\mathrm{exp}}_1.\quad}
\tag{278.2}
$$

完整背景始终在框外共同保留。此处不输入 $\mathsf M_3$、二或三份实际L2、数值互易、换点公理或任意面效应延拓。只缩小最小确认条件的目标域，不缩小态、菜单或比较域；暴露性仍是明示几何输入。

**定理 278.2（产品对确认加单体可筛球重建全部有限层）。** 在278.1的完整背景下，相对于[M274]的M加数值互易到规范迹Jordan几何供应、276.2的M-only矩阵整锥供应、[XIX276.2（二）—（五）][J278]的产品对秩二供应及[T274,164.11]的准确全有限传播，下列条件等价：$\mathsf Q_{\mathrm{prod,exp}}$；277.2的 $\mathsf Q_{\mathrm{exp}}$；存在 $n\ge2$ 和同一保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(\forall N\ge0).
\tag{278.3}
$$

证明。（一）低层确认与几何。固定原纯旁观者 $b\in P_1$。对每个 $a\in P_2$，重复产品目标 $a\otimes b$ 的least确认限制到 $x\mapsto x\otimes b$，得原双份proper确认。任意原双份确认者 $f$ 可提升为 $f\otimes u_1$，三份leastness限制后给它低于所有这样的 $f$，故取得完整 $\mathsf M_2$。同一纯旁观下降给 $\mathsf M_1$，不需取得 $\mathsf M_3$。

现在277.2—277.3的实际证明只消费单体M、完整菜单及原暴露实际球，因而给 $\mathsf R_1$。具体地，取确认整球的least效应 $h_B$，极端残余 $h_B-e_p$ 非零时在该球内取得一，锁定对跖零点与半球刻度；塌缩时，第二张经过同一端点且含球外原纯点的暴露实际三球给同维面包含矛盾。整底为球的情形用原全域半球效应。于是单体完整M、数值互易与实际L2支付276.3第一步的具名Jordan桥和复类型选择，得到同一个保单位 $\theta$、$C_1=\operatorname{PSD}_n$、$n\ge2$。

（二）整个双份锥。原 $1|1$ 的min/max在此坐标成为Sep/BP界，单位为普通迹。整个双份的M已由（一）支付，故276.2给

$$
C_2=T_1^\varepsilon\operatorname{PSD}_{n^2},\qquad\varepsilon\in\{0,1\}.
\tag{278.4}
$$

这一步不用双份实际L2或互易；其全纯域M不能仅由双份产品目标least代替，这正是（一）保留全部 $a\in P_2$ 的原因。

（三）三份只取真实秩二资源。在 $(12)|3$ 上令 $D_3=T_1^\varepsilon C_3$。整个二份局域块现为 $\operatorname{PSD}_{n^2}$，第三块为 $\operatorname{PSD}_n$。原锥、完整逆对偶菜单、迹单位和分块min/max一起运输。该保迹正交线性坐标将 $\mathcal B_3$ 双射为这两个整个矩阵块的全部秩一产品投影，故产品对least也随之运输；不把部分转置当原物理正操作。

准确使用[XIX276.2（二）—（四）][J278]，取 $m=n^2$、第二参数为 $n$，得到

$$
\exists\delta\in\{0,1\}:\quad
T_{12}^{\delta}\mathcal S_2((12)|3)\subseteq D_3\cap D_3^*.
\tag{278.5}
$$

这里 $\mathcal S_2$ 是由该切分Schmidt秩至多二向量的dyad生成的锥。该供应只用重复产品least确定产品门、非重复产品共同least确定极端残余、双HS／迹预算识别迹一残余为原纯态，以及原产品补测试的稀疏迹二计算和连通选择；不消费双份换点、三份实际球或全部三份纯点的M。它对残余取得原纯性后也不另假设残余的least确认。

整个矩阵转置保留 $\mathcal S_2$，所以 $T_{12}^{\delta}\mathcal S_2=T_3^\delta\mathcal S_2$。运输回同一局域坐标，(278.5)给

$$
T_1^\varepsilon T_3^\delta\mathcal S_2((12)|3)\subseteq C_3.
\tag{278.6}
$$

按[XIX275.2（六）、276.2（五）][J278]的同一实现Bell边缘，在每腿固定同一 $|0\rangle,|1\rangle$ 支持。错误位 $(1,0)$ 用来源 $P_0^{(1)}\otimes B_{23}$，错误位 $(1,1)$、$(0,1)$ 用来源 $B_{13}\otimes P_0^{(2)}$。它们全在同一切分的秩二域；原正丢弃与原正置换迫其边缘属于(278.4)的同一个 $C_2$。前两项给标准Bell不能属于转置PSD，第三项给部分转置Bell不能属于PSD，均由反对称本征值 $-1/2$ 排除。因此 $\varepsilon=\delta=0$，整个 $C_2$ 标准且 $\mathcal S_2((12)|3)\subseteq C_3$。

取准确向量

$$
\tau_n=\left(\sum_{i=0}^{n-1}|ii\rangle\right)|0\rangle+|01\rangle|1\rangle,
\qquad \operatorname{Tr}(\tau_n\tau_n^*)=n+1.
\tag{278.7}
$$

它在该真实切分上有两个独立Schmidt方向，故其dyad属于原 $C_3$。同坐标标准 $C_1,C_2$、这只准确种子及完整原 $\mathsf F$，恰为[T274,164.11]第3项；直接消费 $3\Rightarrow4$ 得(278.3)。六份种子、十八条实际腿和全部有限相关旁观输入仍在该供应中，没有先分类整个 $C_3$，也没有将背景截断为三层。

反向，(278.3)中任意两纯射线的共同least是其张成支持投影，故特别对整个 $\mathcal B_3$ 成立；单体二纯实际面为复二维支持密度体，支持投影使其为原全域暴露三球。277.4又给 $\mathsf Q_{\mathrm{exp}}$ 与(278.3)等价。$\square$

**推论 278.3（不预选门的二元收紧版本）。** 在278.2的同一完整前提和供应下，候选也可写为

$$
\boxed{\quad\mathsf R_B+\mathrm{L2}^{\mathrm{exp}}_1,\qquad
\mathsf R_B:\ \forall f,g\in\mathcal E_3\ \exists h\in\mathcal E_3:\quad
h\le f,g,\quad c_B(h)=c_B(f)\cap c_B(g),\quad}
\tag{278.8}
$$

其中 $c_B(f)=\{P\in\mathcal B_3:f(P)=1\}$。这条规则只说两只原测试可共同收紧且不丢共同确认的独立块纯准备；不要求最大下界、联合仪器或先后操作交换。

证明。精确复用[XIX277.2][R278]的紧确认纤维引理：$\mathsf R_B$ 使每对目标（含重复）的非空紧确认纤维向下有向，内部原态评价严格检测非零正差，故纤维有唯一least。于是取得 $\mathsf J_3^{\mathrm{prod}}$，278.2适用。这一方向不调用XIX277.3所保留的旧双份换点。反向，在(278.3)中对任意 $0\preceq f,g\preceq I$，取 $h$ 为 $\ker(I-f)\cap\ker(I-g)$ 的正交投影；它低于两门并恰保留共同确认的射线，所以满足(278.8)。这里通过整锥结论建立反向，不在未知模型中将全部效应区间预称为格。$\square$

**推论 278.4（维数至九时只输入实际球）。** 完整保留 $\mathsf F+\mathsf J_3^{\mathrm{prod}}+\mathrm{L2}_1$，其中实际球明确为非退化三球仿射同构。相对于278.2及[XVIII240.2][G277]的外三角维数供应，若 $\dim_{\mathbb R}V\le9$，则(278.3)成立且 $n\in\{2,3\}$。等价地可用 $\mathsf R_B$ 代替产品对J；不另输入互易或暴露性，所有有限副本仍完整保留。

证明。278.2（一）的下降已给M1。277.5的几何部分只用实际球和维数：真球 $B$ 包含于原暴露真面 $H$；若 $H\ne B$，原外三角给 $9\le\dim\operatorname{span}H\le\dim V-1\le8$，矛盾。因此所有二纯球暴露。277.2—277.3由M1给互易，再用278.2。重建后 $\dim V=n^2\le9$ 且 $n\ge2$，故恰有两种尺寸。$\mathsf R_B$ 到J只消费278.3的紧纤维方向。维数条件仅限制单体，不是有限副本数的上限，也不声称由裸前件自动推出该维数界。$\square$

**命题 278.5（几何、量子公理对应与未付边界）。** 在278.2或278.3的完整前提及供应下，全三份M、所有层的实际二纯三球和数值互易均为输出。产品目标域在复模型中真小于全三份纯域，但新旧候选在同一剩余背景与供应下刻画相同模型类；不据目标域缩小声称严格逻辑弱化或最少独立公理。

证明与对应。278.3给每个原独立块目标集的规范确认闭包；重建后，确认门为这些射线的复张成支持投影，join为张成，补为正交补，整个有限复投影格随整锥一起读出。向量 $|000\rangle+|101\rangle$ 在 $(12)|3$ 上Schmidt秩二，故其纯态不在 $\mathcal B_3$；但它及其他所有联合纯点的least门由(278.3)成为结论。完整归一态、纯态、proper菜单、有限单位分解和原配对分别给密度矩阵、复射线、全部数学POVM／PVM和Born迹概率；全部有限产品、置换和丢弃给同一复张量与偏迹，具体字典复用276.4。

过程对应仍逐项保留276.4的独立条件：全部有限相关旁观输入上的分支保正给CP，整个正输入的质量预算及分支总预算给TNI／TP和仪器，锐效应及整个yes支持逐点中性给Lüders，指定连续可逆保锥保单位群给数学酉动力学。数学菜单不单独提供设备、物理钟、能量或 $\hbar$ 标定、无限或近似极限；端点互易不等于有序仪器交换。

裸 $\mathsf F+\mathsf J_3^{\mathrm{prod}}+\mathrm{L2}_1$ 在一般单体维数下是否已迫暴露性或 $\mathsf R_1$，本节仍未解决，也未给完整反模型。若互易失败，278.2（一）的M1及277.3的逆否命题迫至少一颗原实际球非暴露；278.4的同一外三角供应再迫 $\dim V\ge10$。XIX278.3关于正对偶面暴露的结论不替代原球暴露，额外换点也未加入本候选。278.4是完整有限子类，未替代此一般目标。

本节新增repo-derived接合是：由产品对J下降完整M2，以单体可筛球支付R1和复类型，再在双份使用M-only整锥补全、三份仅使用产品对秩二供应，准确回接全有限种子。因此既不需要旧双份换点及其射影—Gleason入口，也不向全三份纠缠点预配least门。单体二球非塌缩、矩阵整锥补全、产品对迹二计算、紧有向纤维、Jordan分类、Bell与全有限传播均保留各自已有或成熟归属，不将这些工具或重复证明申领为新成果；不主张全球优先性、内核认证或物理实现。

白话：把两份世界作为一块，再独立放入第三份。两只测试若都认出某些这样的独立准备，就能一起收紧而不丢这些共同对象；在完整紧菜单里，每对准备自己的最小共同门便自动存在。同一准备问两次，门就沿纯旁观者下降到单体。单体两颗纯准备撑开的球能被合法测试单独筛出，先取确认整球的最小门，再扣掉端点的最小门：非零残余锁定球内正对面，第二张球排除整球塌缩，于是正反比较共用同一刻度。双份由这把尺和最小门补全；三份只让独立块之间的共同门生成真实秩二纠缠资源，三条真实边排尽镜像，一颗明确种子把同一结构延到全部有限份数。几何上只输入单体可筛出的实心球，不预设联合世界的每颗球或每扇纠缠门；一般维数下能否连单体筛球要求也删掉，仍待证明。$\square$

[J278]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "276.1及276.2（二）—（五）：真实独立块目标、产品对least、极端迹一残余与统一Schmidt秩二供应；275.2（六）的Bell和准确种子。"
[R278]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "277.2的紧有向确认纤维及277.4的内生确认闭包；不直接消费277.3的旧X2入口。"

## 追加锚（本行以下为增补区）

## 279. 同准备的双份共同门：九点决定、正回缩与单读数判据

**定义 279.1（完整原域与球面对角确认）。** 保留278.1的整个非平凡强全有限背景 $\mathsf F$，包括全部有限原锥、整个归一紧底和全部原纯点、完整正对偶与proper菜单、全部有限单位分解、正置换及其正逆、正丢弃和含全部相关输入的每个有限分块min/max界。令 $\mathsf A_B$ 仅要求真实 $(12)|3$ 上每个 $a\otimes b\in P_2\otimes P_1$ 有原全域proper单点least；$P_2$ 包括块内纠缠。它不为两个不同三份目标预配共同门。单体实际L2仍指每对不同原纯点生成的整个最小实际面与完整非退化实三维闭球仿射同构。

$\mathsf A_B$ 沿原纯旁观面限制给整个M2，再给M1，证明精确复用278.2（一）及[XIX282.2][Q279One]的单点下降部分，不使用换点或数值互易。任意满足M的有限层，对非空纯目标集 $S$ 取包含它的最小原暴露面 $H_S$，令 $h_S=h_{H_S}$；空集令 $h_\varnothing=0$。最小暴露包存在：从任意暴露包出发，每次若仍有更小包便作交；真包含降低面维数，有限次达到对所有包的交。有限交由各确认效应的平均暴露。271.7的least最大测试于是给

$$
h_S\le f\quad\Longleftrightarrow\quad f(s)=1\ (s\in S),
\qquad f\in\mathcal E.
\tag{279.1}
$$

这没有使用裸背景中尚未证明的 $\mathsf J_3^{\rm prod}\Rightarrow\mathsf R_B$。以下新推导只需已支付的M1、M2；$\mathsf J_3^{\rm prod}$ 或 $\mathsf R_B$ 都是 $\mathsf A_B$ 的充分来源。

固定单体实际球 $B=\iota(\overline{\mathbb B}^3)$，记球心 $c_B=\iota(0)$、最小原暴露包 $H_B$、$h=h_{H_B}$。在整个双份菜单中定义

$$
\Delta_B=\{\iota(a)\otimes\iota(a):a\in S^2\},\qquad
k_B=h_{\Delta_B},\qquad t_B=h\otimes h-k_B.
\tag{279.2}
$$

全部球面点为原纯点，原产品纯性使 $\Delta_B\subset P_2$。原产品与完整菜单保证 $h\otimes h$ proper，故 $t_B\ge0$。单体球在此尚未假定暴露。

**定理 279.2（矩形确认的全域张量化）。** 在上述完整域与低两层M下，对任意 $A,T\subseteq P_1$，

$$
h_{A\otimes T}=h_A\otimes h_T
\quad\text{作为整个 }W_2\text{ 上的泛函。}
\tag{279.3}
$$

特别地，$h_{(P_1\cap B)\otimes(P_1\cap B)}=h\otimes h$，且 $e_{p\otimes q}=e_p\otimes e_q$；后一单点结论已有272.2。

证明。空集直接成立。非空时，令 $g=h_{A\otimes T}\le h_A\otimes h_T$。固定 $t\in T$，$g(\cdot\otimes t)$ proper、确认全部 $A$ 且不大于 $h_A$，由(279.1)等于 $h_A$。固定 $a\in A$ 同理得 $g(a\otimes\cdot)=h_T$。任取原归一 $y$；若 $h_T(y)>0$，则 $g(\cdot\otimes y)/h_T(y)$ proper、不大于 $h_A$，并确认 $A$，故等于 $h_A$。若 $h_T(y)=0$，正性和乘积上界使该切片为零。因此两边在全部正产品输入相同；两原锥生成原载体，原产品张成整个 $W_2$，给全域等式。$h_{P_1\cap B}=h$ 是最小暴露包的定义及(279.1)。$\square$

**定理 279.3（九点决定的对角参数与半球预算）。** 存在唯一内生参数 $\gamma_B$，满足

$$
\begin{aligned}
&k_B(\iota(x)\otimes\iota(y))=1-\gamma_B(1-x\cdot y),
&&\|x\|,\|y\|\le1,\\
&0\le\gamma_B\le\tfrac14,
&&\gamma_B=1-k_B(c_B\otimes c_B),\\
&\gamma_B=0\quad\Longleftrightarrow\quad k_B=h\otimes h.
\end{aligned}
\tag{279.4}
$$

对 $p=\iota(a)$、$\|a\|=1$，唯一写成

$$
e_p(\iota(x))=1-\beta_B(p)(1-a\cdot x),\qquad
2\gamma_B\le\beta_B(p)\le\tfrac12.
\tag{279.5}
$$

取任一正交球坐标基 $v_1,v_2,v_3$，下列九个 $a$ 的对角产品目标与整个 $\Delta_B$ 有完全相同的原确认纤维，因而有同一个 $k_B$：

$$
\pm v_1,\ \pm v_2,\ \pm v_3,\quad
(v_1+v_2)/\sqrt2,\ (v_1+v_3)/\sqrt2,\ (v_2+v_3)/\sqrt2.
\tag{279.6}
$$

证明。原交换正同构保持整个 $\Delta_B$，least唯一性使 $k_B$ 交换对称。球积限制为 $c+v\cdot(x+y)+x^{\mathsf T}My$、$M=M^{\mathsf T}$；对每个单位 $a$，在 $(a,a)$ 上取一。以 $a,-a$ 比较得 $v=0$，再由球面二次型恒定得 $M=(1-c)I$。令 $\gamma_B=1-c$；产品proper预算先给 $0\le\gamma_B\le1/2$。任一原 $e_p$ 在球内介于零一并在端点取一，其非恒定部分必须沿 $a$，给(279.5)的表示及 $0\le\beta_B(p)\le1/2$。

由单点产品least，$e_p\otimes e_p\le k_B$。取单位 $v\perp a$，置 $x=\cos t\,a+\sin t\,v$、$y=\cos t\,a-\sin t\,v$、$s=1-\cos t>0$，则

$$
(1-\beta_B(p)s)^2\le1-\gamma_B(4s-2s^2).
\tag{279.7}
$$

除以 $s$ 后令 $s\downarrow0$，得 $\beta_B(p)\ge2\gamma_B$，再得 $\gamma_B\le1/4$。若 $\gamma_B=0$，$k_B$ 确认整个球积；279.2给 $h\otimes h\le k_B$，反向已知。反之，$h\otimes h$ 在球积恒一，迫 $\gamma_B=0$。

最后，对任意原双份效应，其球面对角限制是次数至多二的实多项式。设它在(279.6)九点都取一。三个正负对先使线性部分为零，并使三个对角系数同为 $1-c$；三个混合点再使所有对称非对角系数为零。斜对称部分在对角恒零。因此它在整个 $S^2$ 上恒一，得到完全相同的确认纤维，不要求这些效应交换对称。这项有限决定性不缩减任何原菜单、原纯域或相关输入。$\square$

**定理 279.4（对角不塌缩给正回缩与真实纠缠资源）。** 若 $\gamma_B>0$，则存在正线性回缩

$$
\Pi_B:V\to\operatorname{span}C_B,\qquad
\Pi_B(C)=C_B,\quad \Pi_B|_{\operatorname{span}C_B}=\mathrm{id},\qquad
\gamma_B\,u_B\circ\Pi_B\le h\le u,
\tag{279.8}
$$

其中 $C_B=\operatorname{cone}B$、$u_B=u|_{\operatorname{span}C_B}$。同时存在原双份纯点 $r\in P_2$ 及 $\lambda>0$，使

$$
\begin{aligned}
&e_r(\iota(x)\otimes\iota(y))=\lambda(1-x\cdot y),\\
&(e_p\otimes e_q)(r)=0\quad\Longleftrightarrow\quad p=q
\qquad(p,q\in P_1\cap B).
\end{aligned}
\tag{279.9}
$$

$r$ 不是原 $1|1$ 产品纯点，其两个原边缘均在 $H_B$。

证明。用球的齐次Lorentz坐标 $C_B=\{(s,x):s\ge\|x\|\}$。对任意 $v\in V$ 唯一写

$$
t_B(v,\iota(y))=\gamma_B\bigl(w(v)-z(v)\cdot y\bigr).
\tag{279.10}
$$

$w,z$ 线性；原正 $v$ 使左边在整个球非负，故 $w(v)\ge\|z(v)\|$。定义 $\Pi_B(v)=(w(v),z(v))$。279.3使它在 $\operatorname{span}C_B$ 为恒等；$t_B\le h\otimes h$ 又给 $\gamma_B(w(v)+\|z(v)\|)\le h(v)$，得到(279.8)。

任意least共同确认 $g$ 都是整个proper区间的极点：其平均分解的两项仍确认全部目标，因leastness均不小于 $g$，只能相同。若 $g\le f$ 是两个这样的门，$d=f-g$ 也极端。事实上，$d=(d_1+d_2)/2$ 迫 $d_i$ 在 $g$ 的全部目标上为零；$u-d_i$ 确认它们，故 $g+d_i$ proper，其平均为极端 $f$。因此 $t_B$ 非零且极端。M2的完整frame展开中，若某系数严格介于零一，可单独上下扰动它，违背极端性。所以

$$
t_B=\sum_i e_{r_i},\qquad r_i\in P_2.
\tag{279.11}
$$

每一项在全部球面对角为零。一个在球积非负、且在全部 $(a,a)$、$\|a\|=1$ 取零的仿射双线性函数必为 $\lambda(1-x\cdot y)$、$\lambda\ge0$：写成 $c+v\cdot x+w\cdot y+x^{\mathsf T}My$，对角恒零给 $w=-v$、$\operatorname{sym}M=-cI$；对每个固定单位 $a$，关于 $y$ 的非负仿射函数在 $y=a$ 取零，其线性系数必须与 $-a$ 同向。比较 $a,-a$ 先消去 $\operatorname{skew}M$，再消去 $v$，剩余 $c\ge0$。应用于(279.11)，各系数 $\lambda_i\ge0$ 且和为 $\gamma_B$，可选 $\lambda_i>0$ 的一项为 $e_r$。

若 $r=a\otimes b$，272.2给 $e_r=e_a\otimes e_b$。其球积限制作为四维齐次双线性表的秩至多一，然而 $\lambda(1-x\cdot y)$ 的秩为四，矛盾。M2的零互易及产品least因子化给(279.9)。又 $e_r\le t_B\le h\otimes h$，在 $r$ 上评价得 $h\otimes h(r)=1$；由 $h\otimes h\le h\otimes u,u\otimes h$，两个边缘均在 $\{h=1\}=H_B$。$\square$

**定义 279.5（单读数条件与一对种子门）。** 定义

$$
\mathsf C_\Delta:\quad
k_B(c_B\otimes c_B)=\tfrac34
\quad\text{对每张原单体实际二纯球 }B.
\tag{279.12}
$$

这里 $c_B,k_B$ 全由原凸准备、完整双份菜单和(279.1)—(279.2)定义，未预选外来效应；等式 $3/4$ 仍是明确的额外关系约束，不宣称由裸背景自动成立。

令 $\mathcal R$ 精确采用[XIX282.2][Q279One]的同坐标集合：$n\ge2$，$\theta:V\to H_n$ 保单位实线性双射，$\theta C_1=\operatorname{PSD}_n$、$\theta^{\otimes2}C_2=T_1^\varepsilon\operatorname{PSD}_{n^2}$，$\varepsilon\in\{0,1\}$。性质 $\mathsf E_\tau$ 要求存在该集合中的一组坐标，使[XIX282.3，式(282.3)—(282.4)][Q279One]指定的那一对不同原产品源 $p,q\in P_2\otimes P_1$ 有原全域proper共同least。该式使用准确向量 $\tau_n=(\sum_i|ii\rangle)|0\rangle+|01\rangle|1\rangle$ 指定两只产品向量，尚不假定其dyad属于三份锥。候选为

$$
\boxed{\qquad
\mathsf Q_\Delta:=\mathsf A_B+\mathrm{L2}_1+\mathsf C_\Delta+\mathsf E_\tau.
\qquad}
\tag{279.13}
$$

$\mathcal R$ 的非空将在下一定理中先由前三项推出；不是以存在量词额外输入低两层量子类型。

**定理 279.6（单读数候选的完整有限量子对应）。** 保留完整 $\mathsf F$，相对于278.2明列的M加数值互易到Jordan桥、276.2的M-only矩阵整锥供应，以及[XIX282.4—282.5][Q279One]的固定一对产品源残余和XIII164.11准确全有限传播，$\mathsf Q_\Delta$ 等价于存在同一 $n\ge2$ 与同一保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\qquad(N\ge0).
\tag{279.14}
$$

证明。$\mathsf A_B$ 先给完整M2、M1。$\mathsf C_\Delta$ 使每颗球的 $\gamma_B=1/4$；式(279.5)的预算迫每个端点 $\beta_B(p)=1/2$，所以同球端点有

$$
e_p(q)=\frac{1+a\cdot b}{2}=e_q(p),
\qquad p=\iota(a),\ q=\iota(b).
\tag{279.15}
$$

这给整个单体数值互易。准确复用278.2（一）的具名M加互易Jordan桥及实际L2的复类型选择，取得 $C_1$ 的标准复矩阵表示；278.2（二）由M2及276.2给 $C_2$ 的PSD或相对转置坐标。因此 $\mathcal R\ne\varnothing$，没有输入球暴露性、双份换点或复合层实际L2。

$\mathsf E_\tau$ 现在只支付[XIX282.4][Q279One]所选的一对共同门。该供应的局部稀疏计算、迹二共同门及迹一极端残余，给准确 $\tau_n$ 的dyad或其第三腿镜像；[XIX282.5，式(282.13)—(282.16)][Q279One]在同一种子的两个交叠边缘排尽两个转置位，取得同坐标标准 $C_1,C_2$ 与准确种子。它们精确支付XIII164.11的 $3\Rightarrow4$，得(279.14)。不需全体非重复产品对J、全三份M或整个三份锥的预先分类。

反向，在(279.14)中 $\mathsf A_B$ 与 $\mathsf E_\tau$ 由秩一和共同支持投影实现，单体二纯面为二维复支持 $U$ 上的完整三球。$\{v\otimes v:v\in U\}$ 张成 $\operatorname{Sym}^2U$：在一组基 $v,w$ 中，$v^2,w^2,(v+w)^2$ 已张成三个对称基方向。因此 $k_B$ 是该三维复子空间的支持投影，球心为 $I_U/2$，有

$$
k_B(c_B\otimes c_B)
=\operatorname{Tr}\!\left(P_{\operatorname{Sym}^2U}\frac{I_U\otimes I_U}{4}\right)
=\tfrac34.
\tag{279.16}
$$

这正是成熟交换／对称子空间概率 $\operatorname{Tr}(P_{\rm sym}\rho\otimes\sigma)=(1+\operatorname{Tr}\rho\sigma)/2$ 在qubit整球上的特例，参见[Q279Swap]式(2)及图2；这里只用矩阵恒等式，不输入其设备实现。于是 $\mathsf C_\Delta$ 成立。$\square$

**定理 279.7（非暴露包的支持亏损与全有限放大）。** 仅用M1及[XIX278.3][D277]的正对偶实际面支持。对非空原暴露面 $H$，置

$$
D_H=\operatorname{face}_{C^*}(h_H),\quad L_H=\operatorname{span}D_H,\quad
d_H=\dim L_H,\quad s_H=\dim\operatorname{span}\operatorname{cone}H.
\tag{279.17}
$$

限制 $L_H\to\operatorname{Aff}(H)$ 是保单位序嵌入，因而 $d_H\le s_H$。若某实际面 $B\subsetneq H_B$，则 $d_{H_B}<s_{H_B}$。在整个 $\mathsf F$ 下，对每个有限 $N\ge1$，

$$
\begin{aligned}
\operatorname{span}\operatorname{face}_{C_N^*}(h_H^{\otimes N})&=L_H^{\otimes N},\\
\dim\operatorname{face}_{C_N^*}(h_H^{\otimes N})&=d_H^N,\\
\dim\operatorname{span}\operatorname{cone}\{z\in K_N:h_H^{\otimes N}(z)=1\}&\ge s_H^N.
\end{aligned}
\tag{279.18}
$$

证明。给定 $a\in L_H$，取大 $t>0$ 使 $f=a+t h_H\in\operatorname{ri}D_H$。M-only完整frame展开为 $f=\sum_i\lambda_i e_{q_i}$、$\lambda_i>0$，其正项支持之和由XIX278.3的规范支持唯一性等于 $h_H$，且每个 $q_i\in H$。因此

$$
a=\sum_i(\lambda_i-t)e_{q_i},\qquad a(q_i)=\lambda_i-t.
\tag{279.19}
$$

若 $a|_H\ge0$，所有系数非负，故 $a\in C^*$；反向显然。若限制为零，则 $a,-a\in C^*$，尖性迫 $a=0$。这给序嵌入和维数上界。

若 $d_H=s_H$，限制成为保单位序同构。对 $x\in\operatorname{ri}B$、$B\subsetneq H=H_B$，相对支撑给非恒零 $0\le\ell\le1$ 于 $H$、$\ell(x)=0$。满射及正性反映把它提升为 $a\in[0,h_H]$。$a\ge0$ 且在 $B$ 的相对内部取零，故在整个 $B$ 取零。原proper效应 $u-a$ 确认 $B$ 却不确认整个 $H_B$，与最小暴露包矛盾。

最后，有限维正锥中 $\operatorname{face}(z)=\{a\ge0:\exists t>0,\ a\le tz\}$。若 $0\le a\le t h_H^{\otimes N}$，固定除任一腿外的全部正输入，其正切片不大于 $h_H$ 的正倍数，所以在 $D_H$。正输入张成各腿，对每腿同时应用得 $a\in L_H^{\otimes N}$。反向，对任意 $f_i\in D_H$，各有 $0\le f_i\le t_i h_H$；原正对偶产品及张量序的望远镜分解给 $0\le\bigotimes_i f_i\le(\prod_i t_i)h_H^{\otimes N}$。这些产品张成 $L_H^{\otimes N}$。原态产品 $x_1\otimes\cdots\otimes x_N$、$x_i\in H$ 均在(279.18)的取一面，且张成维数 $s_H^N$ 的空间，完成证明。未对高层暗加M。$\square$

**命题 279.8（几何、量子字典与剩余条件）。** 279.6把原球暴露性换成原双份共同门的单读数条件；三份仅保留产品单点族及准确种子的一对额外共同门。它与278及XIX282在同一背景和各具名供应下给相同完整复模型类，不据此声称严格逻辑弱化或最少独立公理。$3/4$ 条件尚未由裸实际球、单点门或全部产品对J自动推出。

证明与边界。若某球内端点有 $m_p=e_p(\iota(-a))>0$，279.5给

$$
\gamma_B\le(1-m_p)/4<1/4,\qquad
|e_p(q)-e_q(p)|\le1-4\gamma_B.
\tag{279.20}
$$

第二式由 $\beta_B(p),\beta_B(q)\in[2\gamma_B,1/2]$ 及 $0\le1-a\cdot b\le2$ 得到。若每球 $\gamma_B>0$，则279.5使 $e_p(q)<1$ 对所有不同原纯点成立，给单点唯一饱和；但这还不是 $\gamma_B=1/4$。279.4的正回缩只满足带 $\gamma_B$ 的质量预算，不供给 $u_B\circ\Pi_B\le u$、全旁观正性或Alfsen—Shultz的compression。其纠缠资源的边缘只定位在 $H_B$，不能改报在 $B$。279.7的指数亏损也不是矛盾或反模型存在性证明。

(279.14)后，完整态、纯点、proper菜单、全部有限单位分解及配对分别成为密度矩阵、复射线、全部数学POVM／PVM及Born迹概率；原有限产品、置换、重括号及丢弃成为同一复张量和偏迹。CP、TNI／TP、仪器、Lüders和连续动力学仍分别保留276.4及XIX282.7的全旁观保正、整个正输入及分支总预算、锐效应与yes支持中性、指定连续可逆保锥保单位群等独立条件；数值互易没有推出仪器先后交换。设备、物理钟、能量与 $\hbar$、无限及近似极限没有由静态字典单独供应。

本节repo-derived承重内容为：原球面对角确认的规范参数及九点决定性、以单点产品least给出的 $1/4$ 预算、对角非塌缩的正回缩与真实双份纠缠资源、支持限制的序嵌入与全有限亏损公式，以及单读数条件接XIX282单对种子的完整有限重建。M-only剥离和面支持、纯旁观下降、产品单点因子化、Jordan／矩阵分类及一对种子尾部均保留所引已有归属。球上二次多项式、Lorentz对偶、有限维面与主面、矩阵对称投影及交换概率是成熟中间工具；[Q279Swap]给的是量子模型中的交换读数，不给未知原锥的重建。[Q279Nice]的面延伸／闭性判据也未被用于免费推原球暴露。不申领这些工具、全球优先性、Lean核验或物理实现。

白话：先把一颗球上的“同一准备放两份”全部送进共同最小门。虽然准备有无穷多个，九个选定方向就能决定同一扇门。把这扇门与允许球内任意两份准备的门相比：若两门相同，确认关系完全看不出“相同”与“任意配对”的差别；若有差，差值已经能产生正回缩和真实纠缠资源。进一步要求这扇同准备门对“两份球心”的读数为四分之三，所有端点的正反刻度便被球几何和最小性一起锁定。低两层于是恢复复数结构，再用最新的一对产品源及同一颗种子的交叠边缘长出全部有限量子层级。这里把未付的要求集中成了一个明示读数，没有证明它已自动内生；继续回溯必须从原关系推出这个读数，或给满足完整背景的反模型。$\square$

[Q279One]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "282.2—282.5：产品单点下降、低二层坐标、准确tau种子指定的一对产品源、局部共同门残余、同一种子的两个交叠NPT边缘及XIII164.11全有限传播；282.6保留单体可筛球替代入口。"
[Q279Swap]: https://arxiv.org/abs/quant-ph/0203016 "Ekert、Alves、Oi、Horodecki、Horodecki与Kwek，Direct estimations of linear and non-linear functionals of a quantum state；式(2)及图2的交换期望Tr(rho sigma)与P0=(1+Tr(rho sigma))/2；量子模型的成熟中间恒等式。"
[Q279Nice]: https://arxiv.org/abs/1202.4043 "Pataki，On the connection of facially exposed and nice cones，Theorem2及Remark1的面正延伸／锥和闭性等价；未把对偶面暴露误代入原锥的niceness。"

## 追加锚（本行以下为增补区）

## 280. 原球内的双份零接触：刻度由同一关联准备的归一化锁定

**定义 280.1（固定旁观纤维与原球内零面）。** 完整保留279.1的非平凡强全有限背景 $\mathsf F$、全部原有限层及相关输入、整个原proper菜单和全部有限单位分解。固定原纯旁观者 $b_*\in P_1$，仅要求

$$
\mathsf A_{b_*}:\quad
\forall a\in P_2,\quad
a\otimes b_*\text{ 在整个 }\mathcal E_3\text{ 有单点least确认}.
\tag{280.1}
$$

前两腿仍遍历包括块内纠缠的整个 $P_2$。纯旁观下降精确复用278.2（一）及[XIX283.1][Q280Tail]，取得完整M2、M1；不向其他旁观者的产品单点或所有三份纯点预配门。以下先只使用这两个低层M及原 $1|1$ min/max。

对一张原单体实际球 $B$，原丢弃记为 $\pi_1=\mathrm{id}\otimes u$、$\pi_2=u\otimes\mathrm{id}$，并定义

$$
\begin{aligned}
\mathcal F_{BB}
&=\{r\in K_2:\pi_1r\in B,\ \pi_2r\in B\},\\
k_B&=h_{\{p\otimes p:p\in P_1\cap B\}},\\
\mathsf Z_B
&:\quad\mathcal F_{BB}\cap\{r:k_B(r)=0\}\ne\varnothing.
\end{aligned}
\tag{280.2}
$$

$k_B$ 仍是279.1中整个原菜单的共同least，确认整个同纯准备对角族，不是逐点各选一扇门。$\mathcal F_{BB}$ 是原态侧的实际面；零面由原全域效应给出。$\mathsf Z_B$ 要求两张原面的交非空，没有缩小原系统，也没有假定局部效应任意延伸、原球暴露或保单位压缩。定义了交集不等于证明它非空；$\mathsf Z_B$ 是明示新增的关系条件。

**定理 280.2（零接触的维数预算、唯一纯态与内生刻度）。** 在上述完整低两层结构及M1、M2中，先允许所固定实际面为 $B=\iota(\overline{\mathbb B}^d)$，$d\ge2$，不要求其他实际面也有该维数。若 $\mathsf Z_B$ 成立，则

$$
\begin{aligned}
&e_{\iota(a)}(\iota(x))=\frac{1+a\cdot x}{2}
&&(\|a\|=1,\ \|x\|\le1),\\
&\gamma_B=\frac1{d+1},\qquad d\ge3,\\
&\mathcal F_{BB}\cap\{k_B=0\}=\{r_B\},\\
&r_B=c_B\otimes c_B-\sum_{j=1}^d b_j\otimes b_j,
&&b_j=\iota(v_j)-c_B,
\end{aligned}
\tag{280.3}
$$

其中 $(v_j)$ 是任意正交球坐标基。$r_B$ 是原 $K_2$ 的纠缠纯点，两张边缘都恰为 $c_B$。在整个 $\operatorname{span}C_B\otimes\operatorname{span}C_B$ 上，$r_B$ 的原最小确认效应满足

$$
e_{r_B}(\iota(x)\otimes\iota(y))
=\frac{1-x\cdot y}{d+1}.
\tag{280.4}
$$

证明。（一）实际面和载体定位。$B$ 是原实际面，正丢弃保归一，故两张原边缘逆像及其交 $\mathcal F_{BB}$ 都是 $K_2$ 的紧实际面。若 $r\in\mathcal F_{BB}$，任取原proper效应 $f$，则

$$
(\mathrm{id}\otimes f)r,\quad
(\mathrm{id}\otimes(u-f))r\in C,\qquad
(\mathrm{id}\otimes f)r+(\mathrm{id}\otimes(u-f))r=\pi_1r\in C_B.
\tag{280.5}
$$

锥面性质迫两项都在 $C_B$；交换两腿同理。完整正菜单张成各腿的全对偶，因此逐腿切片给

$$
r\in\operatorname{span}C_B\otimes\operatorname{span}C_B.
\tag{280.6}
$$

这项定位由同一个原态的两张边缘及互补测试得到，不是由两个分别可达的边缘拼出原态。

（二）零接触迫半球刻度。279.3的球面积分、交换唯一性和小角二阶比较，在任意 $d\ge2$ 的正交切向方向中原样成立；其维数无关的中间结果为

$$
\begin{aligned}
k_B(\iota(x)\otimes\iota(y))&=1-\gamma_B(1-x\cdot y),
&0\le\gamma_B\le\tfrac14,\\
e_p(\iota(x))&=1-\beta_p(1-a\cdot x),
&0\le\beta_p\le\tfrac12,\qquad p=\iota(a).
\end{aligned}
\tag{280.7}
$$

这里 $d\ge2$ 保证小角证明有非零正交切向方向；不将该论证用于只有两个端点的一维线段。取(280.2)中的同一 $r$。产品单点least的279.2给 $e_p\otimes e_p\le k_B$，所以 $(e_p\otimes e_p)(r)=0$。令 $m_p=\min_Be_p=1-2\beta_p\ge0$，$z_p=(\mathrm{id}\otimes e_p)r$。由（一），$z_p\in C_B$，从而

$$
0=e_p(z_p)\ge m_pu(z_p)
=m_p e_p(\pi_2r)\ge m_p^2.
\tag{280.8}
$$

故 $m_p=0$，每个端点都满足 $\beta_p=1/2$。不需要先取得数值互易、全局面效应延伸或 $r$ 的纯性。

（三）同一原态的张量刚性。在基 $(c_B,b_1,\ldots,b_d)$ 中，(280.6)及归一化将 $r$ 唯一写成系数 $(1,x,y,R)$。半球刻度使原产品测试读数为

$$
(e_{\iota(a)}\otimes e_{\iota(b)})(r)
=\frac14\left(1+a\cdot x+b\cdot y+a^{\mathsf T}Rb\right)\ge0.
\tag{280.9}
$$

全部单位对角 $a=b$ 上该值为零。279.4所用的非负仿射双线性零对角计算同样适用于 $d\ge2$：对角等式先给 $y=-x$、$\operatorname{sym}R=-I$。固定单位 $a$，关于 $b$ 的非负仿射函数在 $b=a$ 为零，其线性系数必须反向平行于 $a$；令 $R=-I+A$、$A^{\mathsf T}=-A$，得到

$$
x+Aa=(x\cdot a)a.
\tag{280.10}
$$

比较 $a,-a$ 给 $Aa=0$，再对所有方向给 $x=0$。故 $x=y=0,R=-I$，得到(280.3)的唯一张量。该表达在正交换基下不变，两个原边缘均为球心。

（四）归一化锁定尺度。令 $h=h_{H_B}$、$t_B=h\otimes h-k_B$。由 $h|_B=1$ 及(280.6)，$h\otimes h(r)=1$，所以 $t_B(r)=1$。另一方面，(280.7)在整个球积的限制给

$$
t_B(c_B\otimes c_B)=\gamma_B,\qquad
t_B(b_i\otimes b_j)=-\gamma_B\delta_{ij}.
\tag{280.11}
$$

将（三）的同一实际 $r$ 代入，得到

$$
1=t_B(r)=(d+1)\gamma_B.
\tag{280.12}
$$

因此 $\gamma_B=1/(d+1)$；结合 $\gamma_B\le1/4$ 得 $d\ge3$。这一步用原态的归一化预算，绝不是从 $\beta_p=1/2$ 和 $\beta_p\ge2\gamma_B$ 将上界改报等号。

（五）纯性、纠缠与最小确认。上述计算对交面内任意原态成立，故交面只有一个点。它是 $K_2$ 的非空实际面，单点即原纯点。若该态可分，将其写成有限个归一产品的凸组合；两边缘属于实际面 $B$ 迫每个非零项的两个因子都在 $B$。但在球内任意产品上，

$$
k_B(\iota(x)\otimes\iota(y))
\ge1-2\gamma_B=\frac{d-1}{d+1}>0,
\tag{280.13}
$$

与 $k_B(r_B)=0$ 矛盾。因此 $r_B$ 是原纠缠纯点。又 $t_B(r_B)=1$，所以 $e_{r_B}\le t_B$；其球面对角为零。非负双线性零对角刚性使其球积限制为 $\lambda(1-x\cdot y)$。在同一个(280.3)上评价 $e_{r_B}(r_B)=1$，迫 $\lambda=1/(d+1)$，得(280.4)。$\square$

**推论 280.3（三球校准的无数值替代及其边界）。** 在原实际三球上，$\mathsf Z_B$ 给

$$
k_B(c_B\otimes c_B)=\tfrac34,\qquad
(e_{\iota(a)}\otimes e_{\iota(b)})(r_B)=\frac{1-a\cdot b}{4}.
\tag{280.14}
$$

因此对每张原实际二纯三球要求 $\mathsf Z_B$，即给279.5的整个 $\mathsf C_\Delta$，并给整个单体数值互易。若同时复用278.2明列的M加互易Jordan桥、实际L2的复类型选择及276.2的M-only双份矩阵供应，则全体 $\mathsf Z_B$ 与全体 $\mathsf C_\Delta$ 等价。

证明。正向是280.2取 $d=3$。反向，$\mathsf C_\Delta$ 先由279.5锁定全部半球刻度和 $\mathsf R_1$，具名低层供应给同一 $C_1=\operatorname{PSD}_n$、$C_2=T_1^\varepsilon\operatorname{PSD}_{n^2}$。若 $\varepsilon=1$，对任一二维复支持 $U$ 的实际球，原对角纯产品在正PSD坐标中为 $\bar v\otimes v$。这些向量张成整个 $\bar U\otimes U$：在一组二维基中，$v=|0\rangle,|1\rangle,|0\rangle+|1\rangle,|0\rangle+i|1\rangle$ 已给四个复线性独立向量。因此其共同least支持是整个四维支持，球心读数为一，与 $\mathsf C_\Delta$ 矛盾。这里张成的是四维向量空间，不是声称四个投影张成十六维算子空间。

故 $\varepsilon=0$。在标准双份PSD中，二维复支持上的反对称秩一态给(280.3)，其两个边缘是 $I_U/2$，且对称子空间least $k_B$ 在它上取零。这证明 $\mathsf Z_B$，并未要求三份种子或全三份M。

本等价保留具名低层供应；没有证明固定一张球仅由端点刻度就足以校准，也没有从裸M或裸实际L2证明零交面存在。280.2在一般 $d$ 下只推出 $d\ge3$，不排除 $d>3$，不能把最小维数改报唯一维数。$\square$

**定义 280.4（原球零接触与一条关系线的完整候选）。** 单体保持原完整 $\mathrm{L2}_1$。令 $\mathsf Z_1$ 表示全部原实际二纯球上的 $\mathsf Z_B$。低二层坐标集合 $\mathcal R$ 精确沿用279.5；取[XIX283.3][Q280Tail]的 $b_n$ 和对齐子集 $\mathcal R_{b_*}$。令

$$
\begin{aligned}
\mathsf E_{\rm rel}(b_*):\quad
\exists(n,\theta,\varepsilon)\in\mathcal R_{b_*}\quad
\exists M\in\Sigma_n:\quad
\{p_M,q_M\}\text{ 在整个 }\mathcal E_3\text{ 有共同least},\\
\boxed{\quad
\mathsf Q_Z(b_*):=
\mathsf A_{b_*}+\mathrm{L2}_1+\mathsf Z_1+\mathsf E_{\rm rel}(b_*).
\quad}
\end{aligned}
\tag{280.15}
$$

$\Sigma_n$、准确向量化以及 $p_M,q_M$ 原样采用[XIX284.1，式(284.1)—(284.2)][Q280Tail]：$\operatorname{Tr}M=0$、$\|M\|_{\rm HS}=1$、$MM^*-M^*M\ne0$，并使用实际原锥的逆运输。低二层非空及 $b_*$ 的对齐先由前三项和下述具名供应取得；不是预设复坐标。第一点 $p_M$ 落在已付的固定纤维，第二点不另要求自己的单点least。不把 $M$ 的伴随、两颗源的描述坐标或种子原态性预置于原概率表。

**定理 280.5（固定纤维、球内零接触和单对关系线恢复全部有限层）。** 在完整 $\mathsf F$ 中，相对于278.2的M加互易Jordan及复类型选择、276.2的M-only矩阵整锥供应、[XIX283.2—283.4及284.2][Q280Tail]的单边Gram、极端残余与准确非正规种子，以及XIII164.11第2项到第4项的全有限传播，对任意固定 $b_*\in P_1$，候选 $\mathsf Q_Z(b_*)$ 等价于存在同一 $n\ge2$ 和同一保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\qquad(N\ge0).
\tag{280.16}
$$

证明。固定纤维先下降完整M2、M1。每张原球的零接触由280.2同时给端点半球刻度、唯一原球心边缘纯态及 $\gamma_B=1/4$，故取得全 $\mathsf R_1$ 和 $\mathsf C_\Delta$。具名Jordan和复类型供应、M-only双份分类于是给 $\mathcal R\ne\varnothing$；280.3还排除双份相对转置位。按XIX283.3的同局域酉坐标换基对齐 $b_*$，不把它当作未知高层的物理可实施操作。

现在仅消费 $\mathsf E_{\rm rel}$ 指定的那一对源。第一点在原固定纤维，故其单点least已付；共同least给其上的单边支配。准确复用XIX283.2的两条确认方程与单边Gram饱和、283.4的极端残余及双HS／迹预算，再用284.2（一）的复产品端点公式，得到同一个原三腿态的两个可能残余方向。284.2（二）的同一 $K_M=MM^*-M^*M$ 在两张交叠边缘的Schur补中反号出现，原正丢弃排尽残余镜像；其中双份方向已由零接触固定，不需重新输入。

所得准确原种子为 $r_Mr_M^*$，$r_M=|I_n\rangle\!\rangle|0\rangle+|M\rangle\!\rangle|1\rangle$。其第一截面满秩、第二截面非标量，精确支付XIII164.11第2项，得到(280.16)。一般 $M$ 保留该尾部依赖于 $M$ 的有限字预算，不冒称固定矩阵单位种子特有的统一六副本、十八腿构造。

反向，在整个有限复PSD模型中，固定纤维的各单点和任意所选双目标都有支持投影least；每个原二纯面是二维复支持上的完整三球，反对称秩一态给 $\mathsf Z_B$。按XIX283.3对齐任意 $b_*$，再取 $M=E_{10}\in\Sigma_n$，即给(280.15)的最后一项。$\square$

**命题 280.6（几何简化、量子字典与未付条件）。** 280.15将279的固定 $3/4$ 读数输入换成两张原实际面的非空交条件：同准备共同门有一个原零点，且同一个零点的两张原边缘仍在所生成的球内。刻度、球心边缘和唯一纠缠纯点由280.2的条件态与归一化推导；零面接触的存在性仍是新增要求，没有被“定义内生”一词消去。

证明与范围。280.8先由同一个原零点锁定半球刻度，280.9—280.12再利用它的张量系数和原归一化预算确定 $1/(d+1)$。这分开支付单体刻度与双份刻度，不使用“半球刻度已标准，故对角参数取最大值”的无效逆推。280.15的固定旁观纤维、单边Gram和非正规关系线复用XIX283—284；本节没有将它们重新申领为新内容。简化是以不含预定概率常数的面接触性质替代读数校准，并复用已经缩小的源族和关系线尾部；不是独立条件数减少、严格逻辑弱化或最少公理结论。

(280.16)后的静态字典精确复用279.8及XIX284.3：$\mathcal H_N=(\mathbb C^n)^{\otimes N}$，原态和纯点为全部密度矩阵和复射线，完整proper菜单与有限单位分解为全部数学POVM／PVM，原配对成为 $\operatorname{Tr}(E\rho)$，原产品、置换、重括号和丢弃成为同一复张量和偏迹。过程字典仍保留各自的全相关旁观保正、整个正输入和总质量预算、锐效应与yes支持中性、指定连续可逆群等前件，才分别得到CP、TNI／TP、仪器、Lüders和数学酉动力学。数值互易不表示仪器先后交换；物理钟、能量、$\hbar$、设备与无限极限不由本静态候选单独给出。

若删除 $\mathsf Z_1$，279的 $\gamma_B=0$ 和 $0<\gamma_B<1/4$ 分支仍未排除。仅有279.4的纠缠纯残余，其边缘只在 $H_B$，没有本节(280.5)在 $B$ 内的条件态定位；仅有正回缩也没有它的保单位或全旁观正性。一般原 $\mathsf F+\mathsf J_3^{\rm prod}+\mathrm{L2}_1$ 是否强迫这些零交面非空，仍未由本节解决，也没有因此给出其全有限反模型。

本节repo-derived承重内容是：以原球边缘面上的一个零接触，先内生全部半球刻度，再由同一归一原态推出唯一反向关联张量、$1/(d+1)$ 预算、$d\ge3$ 和原三球的 $3/4$，并接固定纤维与关系线的完整有限候选。实际面、条件态、非负双线性接触、Lorentz坐标和矩阵反对称态都是成熟工具；其中双线性刚性直接复用279.4，不申领singlet、球几何或关联态思想的发明。280.3的双份类型与280.5的完整传播均保留明列供应，不把条件兼容性当作物理实现或全球优先性。

关联态重建自对偶性的成熟先例见[Q280Conj]：Definition 1 (bis)的weak conjugate要求一张态沿指定系统同构，在全部基本结果上给完美均匀关联；Theorem 1 (bis)另用sharpness及其完整conjugate条件，Theorem 2的Jordan刻画还保留可逆filters或相应制备条件。本节的 $\mathsf Z_B$ 则在同一个原实际双份系统中只要求两张实际面的零接触，由(280.8)—(280.12)推出球上的反向关联与刻度，不输入上述filters，也不据此替代280.5所列的Jordan供应。该文§3的Remark与Appendix A.3还区分：正归一双线性形式在最大张量积中存在，不保证它属于所指定的实际复合。本节同样要求 $r_B\in K_2$；不能把Lorentz双线性公式或抽象conjugate的存在当成 $\mathsf Z_B$ 已成立。

白话：把一颗原球里的同一个纯准备各放两份，给整族准备找一扇共同最低门。再问：这扇门能否完全漏掉一种联合准备，而它的左右两张影子仍留在原来的球里？若能，单点自己的门在球内就必须真正碰到零，否则任何这样的联合准备都会留下正读数。各端点的刻度因此先被锁定；同一个漏网准备的左右相关性随后也只剩一种，两个影子恰是球心。它是一只归一准备，于是四个齐次方向的预算直接算出四分之一，最低门在两份球心处便读四分之三。这里新增的是“原球内确有这样的零接触”，没有把这个存在要求藏进定义。低两层尺子成立后，固定旁观纤维和一条非正规关系线的同一残余接上全部有限量子层级；原一般存在问题继续保留。$\square$

[Q280Tail]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "283.1的固定纯旁观纤维下降；283.2—283.4的单边Gram和极端残余；284.1—284.2的准确非正规关系线、复产品端点、同一K_M的两张交叠Schur补及XIII164.11第2项全有限入口；284.3保留静态和过程字典。"

[Q280Conj]: https://arxiv.org/abs/1206.2897v8 "Alexander Wilce，Conjugates, Filters and Quantum Mechanics；§3 Definition 1 (bis)、Remark及Theorem 1 (bis)，§4 Theorem 2，Appendix A.3；关联态、自对偶与Jordan重建的成熟先例，指定实际复合与最大张量积的区别。"

## 追加锚（本行以下为增补区）

## 281. 四个局部零读数：有限接触恢复整球共同门与实际回缩网络

**定义 281.1（同一原态上的有限平衡接触）。** 完整保留280.1的强全有限背景 $\mathsf F$、全部原锥与相关输入、完整proper菜单和全部有限单位分解。固定 $b_*\in P_1$，仍由 $\mathsf A_{b_*}$ 下降完整M2、M1。先固定任意原实际面 $B=\iota(\overline{\mathbb B}^d)$，$d\ge2$，记 $c=c_B$、$W_B=\operatorname{span}C_B$；$\mathcal F_{BB}$、$k_B$、$\mathsf Z_B$ 及 $h=h_{H_B}$ 精确沿用280.1。选有限球面方向及权重

$$
\mathcal A=(a_i,w_i)_{i=1}^m,\qquad
\|a_i\|=1,\quad w_i>0,\quad
\sum_iw_i=1,\quad \sum_iw_i a_i=0,\quad
\operatorname{span}_{\mathbb R}\{a_i\}=\mathbb R^d.
\tag{281.1}
$$

置 $p_i=\iota(a_i)$、$e_i=e_{p_i}$，只要求原有限零面交非空：

$$
\mathsf Z_B^{\mathcal A}:\quad
\exists r\in\mathcal F_{BB}\quad
(e_i\otimes e_i)(r)=0\quad(1\le i\le m).
\tag{281.2}
$$

所有读数来自同一个原 $r\in K_2$，两个原丢弃边缘仍在 $B$。方向只选原球端点，$e_i$ 是原全域单点least，不输入半球刻度、任意局部效应延伸、球暴露或保单位压缩。三球可取正四面体，$m=4$、$w_i=1/4$、$a_i\cdot a_j=-1/3$（$i\ne j$）；令 $\mathsf Z^{\rm tet}_1$ 表示每张原实际二纯三球都存在这样的四方向及同一个态。定义了这些交面不证明其非空。

**定理 281.2（有限局部零与整个对角门零等价）。** 在上述低两层完整背景中，对每一组满足(281.1)的固定方向，

$$
\mathsf Z_B^{\mathcal A}\quad\Longleftrightarrow\quad\mathsf Z_B.
\tag{281.3}
$$

成立时，(281.2)的全部见证恰为280.3的同一个原纠缠纯态 $r_B$；其边缘、全部端点刻度、$\gamma_B=1/(d+1)$ 及 $d\ge3$ 均由280.2给出。尤其三球的四个局部零已迫 $k_B(c\otimes c)=3/4$，不另输入这项概率常数。

证明。（一）先只校准选中的端点。280.2（一）的互补条件态定位对每个 $r\in\mathcal F_{BB}$ 成立，故 $r\in W_B\otimes W_B$。记 $m_i=\min_B e_i\ge0$。原正切片 $z_i=(\mathrm{id}\otimes e_i)r$ 在 $C_B$，所以

$$
0=e_i(z_i)\ge m_i u(z_i)
=m_i e_i(\pi_2r)\ge m_i^2.
\tag{281.4}
$$

因此 $m_i=0$。由280.7的端点表示，选中的 $\beta_{p_i}=1/2$，且 $e_i(\iota(x))=(1+a_i\cdot x)/2$。此时没有使用未选端点的半球测试。

（二）用有限条件态确定同一原态。按280.2的球齐次基将 $r$ 写成 $(1,x,y,R)$，其中 $x,y\in\mathbb R^d$、$R\in M_d(\mathbb R)$。$C_B$ 的Lorentz坐标及（一）使 $\ker e_i\cap C_B=\mathbb R_+\iota(-a_i)$。将两个原条件态分别压到这条零射线，得

$$
\begin{aligned}
x+Ra_i&=-(1+a_i\cdot y)a_i,\\
y+R^{\mathsf T}a_i&=-(1+a_i\cdot x)a_i.
\end{aligned}
\tag{281.5}
$$

令 $Q=\sum_iw_i a_i a_i^{\mathsf T}$。张成性给 $Q>0$，单位方向给 $\operatorname{Tr}Q=1$；$d\ge2$ 使 $\|Q\|_{\rm op}<1$。以正权对(281.5)求和，平衡性消去 $Ra_i$ 的平均与常数方向，给

$$
x=-Qy,\qquad y=-Qx.
\tag{281.6}
$$

于是 $x=Q^2x$ 迫 $x=y=0$；再由 $Ra_i=-a_i$ 和张成性，得 $R=-I$。因此整个有限交面至多一个点，存在性使它恰为 $\{r_B\}$。$\mathcal F_{BB}$ 是原实际面，各原正效应零面也是实际面，故其非空单点交是原 $K_2$ 的纯点。这一步只使用有限个原效应的条件态，没有把尚未支付的全方向半球泛函当作全域proper效应。

（三）从有限态读数到全方向帽读数。279.2的全域产品least因子化给 $e_{p_i\otimes p_i}=e_i\otimes e_i$。M2使 $r_B$ 有原least $e_{r_B}$；由(281.2)，$u_2-e_{p_i\otimes p_i}$ 确认 $r_B$，leastness迫 $e_{r_B}\le u_2-e_{p_i\otimes p_i}$，在 $p_i\otimes p_i$ 上评价即得

$$
e_{r_B}(p_i\otimes p_i)=0.
\tag{281.7}
$$

这里是零互易，不预付一般数值互易。现在才使用原proper帽在整个球积上的正性。将其限制写成

$$
g(a,b)=\lambda+v\cdot a+w\cdot b+a^{\mathsf T}Mb\ge0
\qquad(\|a\|,\|b\|\le1).
\tag{281.8}
$$

对每个 $i$，$g(a_i,a_i)=0$。固定一腿，另一腿是球上非负、在 $a_i$ 取零的仿射函数，其线性系数等于常数项乘 $-a_i$，故

$$
\begin{aligned}
w+M^{\mathsf T}a_i&=-(\lambda+v\cdot a_i)a_i,\\
v+Ma_i&=-(\lambda+w\cdot a_i)a_i.
\end{aligned}
\tag{281.9}
$$

同一组权重给 $w=-Qv$、$v=-Qw$，所以 $v=w=0$；张成性再给 $M=-\lambda I$。于是 $g(a,b)=\lambda(1-a\cdot b)$。在（二）已确定的同一归一态上评价，

$$
1=e_{r_B}(r_B)=(d+1)\lambda.
\tag{281.10}
$$

因此帽在整个球面对角取零。原proper效应 $u_2-e_{r_B}$ 确认整个 $\Delta_B$，共同least给 $k_B\le u_2-e_{r_B}$，故 $k_B(r_B)=0$，得到 $\mathsf Z_B$。反向，由 $e_i\otimes e_i\le k_B$，任一 $\mathsf Z_B$ 见证同时使所有(281.2)为零。280.2遂支付其余结论。有限决定性来自两次非负边界接触及同一严格收缩矩阵 $Q$；不是四点对任意二次多项式的插值。$\square$

**定理 281.3（有限接触确定全域帽及全相关旁观回缩）。** 若(281.2)成立，则原两个效应满足全域等式

$$
e_{r_B}=t_B:=h\otimes h-k_B
\qquad\text{于整个 }V\otimes V.
\tag{281.11}
$$

令 $\gamma=1/(d+1)$，用同一原态和原帽定义线性网络

$$
L_B(v)=(\mathrm{id}\otimes e_{r_B})(r_B\otimes v),\qquad
P_B=\gamma^{-1}L_B;
\tag{281.12}
$$

帽收缩第二、第三腿。则 $P_B$ 精确等于279.4的规范 $\Pi_B$，且

$$
\begin{aligned}
&P_B(V)=W_B,\quad P_B(C)=C_B,\quad
P_B|_{W_B}=\mathrm{id},\quad P_B^2=P_B,\\
&(P_B\otimes\mathrm{id}_m)(C_{m+1})\subseteq C_{m+1}\qquad(m\ge0).
\end{aligned}
\tag{281.13}
$$

未缩放 $L_B$ 在全部原相关旁观正输入上不增总质量；不由此宣称 $P_B$ 不增质量、保单位或原球暴露。

证明。280.2给 $t_B(r_B)=1$、$e_{r_B}\le t_B$，并给两者在整个球积相同的限制。置 $s=t_B-e_{r_B}\ge0$。原效应

$$
g=h\otimes h-s=k_B+e_{r_B}
\tag{281.14}
$$

满足 $0\le g\le h\otimes h\le u_2$，并确认全部球内纯产品。279.2的矩形共同least恰为 $h\otimes h$，所以 $h\otimes h\le g$，迫 $s=0$。这把球积限制的相等提升成原整个菜单中的同一效应，没有假设限制映射单射。

对任意原 $z\in C_{m+1}$，原 $2|(m+1)$ 最小界给 $r_B\otimes z\in C_{m+3}$。正置换、重括号将帽的两腿合成一块；原 $(m+1)|2$ 最大界以完整 $e_{r_B}\in C_2^*$ 正切片，给 $(L_B\otimes\mathrm{id}_m)z\in C_{m+1}$。相同论证用于补帽 $u_2-e_{r_B}$；两分支相加的输出为

$$
c\otimes(u\otimes\mathrm{id}_m)z,
\tag{281.15}
$$

其总质量等于 $u_{m+1}(z)$，故成功分支不增质量。该论证针对整个相关 $z$，没有只检查产品输入。

对 $v=\alpha c+\sum_jx_jb_j\in W_B$，280.4给 $e_{r_B}(c,v)=\gamma\alpha$、$e_{r_B}(b_j,v)=-\gamma x_j$，代入原杯 $r_B=c\otimes c-\sum_jb_j\otimes b_j$ 得 $L_B(v)=\gamma v$。输出恒在 $W_B$，且实际面满足 $C\cap W_B=C_B$：若 $v=a-b\in C$、$a,b\in C_B$，则 $v+b=a$ 的面性质迫 $v\in C_B$。因此(281.13)成立。最后，(281.11)及 $t_B$ 的交换对称性使

$$
P_B(v)=\gamma^{-1}\left[c\,t_B(v,c)-\sum_jb_j\,t_B(v,b_j)\right]
=\Pi_B(v),
\tag{281.16}
$$

正是279.10的同一规范回缩。仍只有既有预算 $\gamma\,u_B\Pi_B\le h\le u$；乘以 $\gamma^{-1}$ 保留全部旁观正性，却不能保留未缩放分支的单位预算。

原态与效应的收缩等于两张正映射复合，是[Q281Remote]§3 Lemma2的成熟remote evaluation；其Theorem2讨论regular composite中的实际态、效应及正幂等compression。该文的compression仅指正幂等，不自动包含本项目更强的单位预算或中性条件；在最大张量积中定义一个正双线性形式也不保证它属于指定实际复合。本节的承重接合是281.2取得原 $r_B$ 后，矩形least迫全域(281.11)，从而把既有 $\Pi_B$ 识别成同一原态／帽网络，并支付全部原相关旁观输入。$\square$

**定义 281.4（四方向接触与正则残余的完整候选）。** 单体保持原完整 $\mathrm{L2}_1$，低二层坐标集合 $\mathcal R$ 精确沿用279.5。对其中 $(n,\theta,\varepsilon)$，取单位 $b$ 表示 $\theta b_*=P_b$；$a,a'\in\mathbb C^n\otimes\mathbb C^n$、$d\in\mathbb C^n$ 遍历全部单位向量，定义

$$
\begin{aligned}
v&=a\otimes b,\qquad w=a'\otimes d,\qquad r_{v,w}=(I-P_v)w,\\
p&=(\theta^{\otimes3})^{-1}T_1^\varepsilon P_v,\qquad
q=(\theta^{\otimes3})^{-1}T_1^\varepsilon P_w.
\end{aligned}
\tag{281.17}
$$

$\mathsf{Reg}(r)$ 准确采用[XIX287.1][Q281Tail]：按XIII164.2的向量化，控制切片像 $\mathcal L_r=\operatorname{span}_{\mathbb C}\{R_k\}$ 维数二，且含可逆矩阵。令 $\mathsf E_\perp(b_*)$ 表示存在上述一组坐标与向量，使 $\mathsf{Reg}(r_{v,w})$ 成立且原 $\{p,q\}$ 在整个 $\mathcal E_3$ 有共同least。候选为

$$
\boxed{\qquad
\mathsf Q_{\rm fin}(b_*)=
\mathsf A_{b_*}+\mathrm{L2}_1+\mathsf Z^{\rm tet}_1+\mathsf E_\perp(b_*).
\qquad}
\tag{281.18}
$$

低层 $\mathcal R\ne\varnothing$ 由前三项与下述具名供应先取得。第一源的单点门来自固定纤维，第二源不另配自己的单点门；不输入 $r_{v,w}r_{v,w}^*\in C_3$，不预选第三腿坐标或特殊Schmidt配方。

**定理 281.5（有限接触候选恢复全部有限复量子层级）。** 在完整 $\mathsf F$ 中，相对于278.2的M加数值互易Jordan桥及实际L2复类型选择、276.2的M-only双份整锥供应、[XIX283.1—283.4、285.2—285.3、286.2及287.2—287.3][Q281Tail]的单边Gram与同一正则残余，以及XIII164.11第1项到第4项的全有限传播，对任意固定 $b_*\in P_1$，(281.18)等价于存在同一 $n\ge2$ 与同一保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\qquad(N\ge0).
\tag{281.19}
$$

证明。固定纤维先给完整M2、M1。281.2逐球给 $\mathsf Z_1$，280.2—280.3给全部半球刻度、单体数值互易和 $\mathsf C_\Delta$。具名Jordan／复类型桥与M-only整锥供应给 $\mathcal R\ne\varnothing$，280.3排除双份相对转置位。281.3同时给规范帽及全旁观正回缩，但其单位预算不充当低层分类的额外前件。

随后精确复用XIX287.3的低层替代入口。按XIX281.2，任取内部参照 $c_3\in\operatorname{ri}K_3$，完整原least条件逐源等价于其全原纯端点星形条件，因此 $\mathsf A_{b_*}$ 支付该入口的固定纤维，而 $\mathsf E_\perp$ 只支付287所需的一对共同门。正则性已包含一般位置和满秩截面；单边Gram及同一极端残余给两个可能镜像。第三腿辅助酉仅同时运输态、锥和菜单，不假定未知原锥在它下不变。两张交叠整块条件读数排尽镜像，逆运输回原同一个 $\theta$ 后，准确原正则种子支付XIII164.11第1项，得(281.19)。不额外要求 $\mathsf X_{T,2}$、全三份M、所有产品对共同门或特殊第三腿方向。

反向，标准全有限PSD模型的支持投影给固定纤维及所有所需共同least。任一二维复支持的完整三球含反对称秩一态，其边缘是球心，对全部同向纯产品取零，因而任选四面体均给(281.2)。正则产品对按287.2的反向构造取得：任意固定 $b$ 取 $d=(b+e)/\sqrt2$、$e\perp b$，数据切片采用286.11的独立矩阵对，其中一矩阵满秩。故 $\mathsf E_\perp$ 成立。$\square$

**命题 281.6（二元比较的几何、量子字典与存在边界）。** 本候选把280的整族共同门零条件等价换成同一个原态上的四个局部重复确认零读数；三球正四面体只是方便配置，任意满足(281.1)的有限正平衡张成族给同一见证、同一全域帽和同一规范网络。不将这项有限表述称为严格逻辑弱化、最少方向、最少公理或全球原创。

证明与范围。正四面体有 $Q=I/3$；一般配置只用 $0<Q<I$，不需等角、等权或原全域物理旋转。281.5的静态字典是 $\mathcal H_N=(\mathbb C^n)^{\otimes N}$、原实载体 $W_N\cong\operatorname{Herm}(\mathcal H_N)$、全部密度矩阵与复射线、完整数学POVM／PVM、Born迹配对，以及原产品、重排、重括号和丢弃对应的复张量与偏迹。过程结论仍逐项保留XIX287.4的全相关旁观保正、整个正输入及总分支预算、锐效应与yes支持中性、指定连续可逆保锥保单位群，才分别取得CP、TNI／TP与仪器、Lüders及数学酉动力学。281.3的网络只支付它自身的正性和未缩放预算，不供应全部物理设备；物理钟、能量、$\hbar$ 与无限极限仍另需前件。

“比较结果不依赖顺序”在这里对应同一配对的数值互易 $e_p(q)=e_q(p)$，并非先后实施两个仪器所得联合分布相同。经典比较也可互易，所以该短语单独不承担281.18的原实际三球、同一联合态存在和正则残余条件。新的几何约束是：四个包住球心的端点，使同一个联合态同时落在四张原产品零面；条件态各沿唯一反向射线，平衡消去两个漂移，原非负帽再把有限接触扩展为整球关系。

删除(281.2)的同一态要求，分别可达的四个零不能代替非空共同交；删除两边缘在 $B$ 的要求，279.4已有残余只把边缘放在暴露包 $H_B$，式(281.4)的球内下界与式(281.5)的Lorentz零射线均失去前件。279.4在 $\gamma_B>0$ 已给全对角零原纯态，却未给这项边缘回落；其正 $\Pi_B$ 也不能在281.3的前件支付之前直接用于任意原相关输入。$\gamma_B=0$ 时 $t_B=0$，不能从它的分解选出非零资源。上述是未付的具体桥，不是裸强背景的反模型。原 $\mathsf F+\mathsf J_3^{\rm prod}+\mathrm{L2}_1$ 是否自动给每张球的这些零交面，仍未由本节解决。

本节repo-derived承重接合是：未知刻度下有限原产品零，先确定原唯一纯态，再经零互易和有限非负双线性刚性取得整球帽；矩形least将其提升为全域帽，继而识别既有规范回缩的实际全旁观网络。四面体、Lorentz严格凸性、平衡矩和remote evaluation都是成熟工具，不单独申领新内容。[Q281SIC]的“Qubit SIC-POVM／Noiseless self-test”也使用四面体，但其prepare-and-measure模型先有Hilbert维数界，在量子态和POVM域内认证；它不支付本节未知原复合锥中的同一态存在及least偏序。上述文献对应与所引供应均限于各自前件；本节为条件数学纸面推导，不声称Lean核验或物理实现。

白话：在原来那颗球上挑四个包住球心的方向，只问有没有同一种双份准备，让四处“左右都说是”同时完全不发生，而左右影子仍留在这颗球里。若有，每个选中方向的门都必须真能碰到零，左右条件准备于是只能沿反方向；四个方向合起来，把所有偏心和多余扭曲都消掉，只剩一种球心对球心的反向关联。它自己的最低门也在这四处为零，而非负性迫这件事沿整张球成立。整族同准备门的零点因此不用另问；原态与原门接成的网络还恰好给原来的球回缩。再接固定旁观纤维和已有的一条正则残余关系，得到全部有限量子结构。简化的是入口：从整族共同门换成四个局部零；“这样的同一个原准备确实存在”仍明列，比较互易也没有变成仪器先后可交换。$\square$

[Q281Tail]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "281.2的逐源least／全原星形等价；283.1—283.4固定纤维、单边Gram和极端残余；285.2—285.3及286.2的条件谱与正则平面；287.1—287.3的正交残余、同时运输、回原尺子及XIII164.11第1到第4项。"

[Q281Remote]: https://arxiv.org/abs/0805.3553v1 "Barnum、Barrett、Leifer与Wilce，Teleportation in General Probabilistic Theories；§3 Lemma2的未归一远程评价，Theorem2的regular composite、实际态／效应与正幂等compression；不以最大张量积中的形式正性代替实际成员。"

[Q281SIC]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7164945/ "Tavakoli、Smania、Vértesi、Brunner与Bourennane，Self-testing nonprojective quantum measurements in prepare-and-measure experiments，Science Advances 6, eaaw6664；Results及Qubit SIC-POVM／Noiseless self-test，预定Hilbert维数界下的量子POVM认证。"

## 追加锚（本行以下为增补区）

## 282. 四点不共面就够：交叉读数替代球心平衡

**定义 282.1（原球的仿射张成接触）。** 保留280.1的完整强全有限背景 $\mathsf F$、全部原态与纯点、整个proper菜单、全部有限单位分解以及所有相关输入上的原min/max。固定原实际面 $B=\iota(\overline{\mathbb B}^d)$，$d\ge2$，沿用 $\mathcal F_{BB},k_B,\mathsf Z_B$。选有限互异单位方向 $a_1,\ldots,a_m$，要求

$$
\operatorname{aff}_{\mathbb R}\{a_1,\ldots,a_m\}=\mathbb R^d.
\tag{282.1}
$$

不另选权重，也不要求球心属于这些点的凸包。置 $p_i=\iota(a_i)$、$e_i=e_{p_i}$，定义

$$
\mathsf Z_B^{\rm aff}(a_1,\ldots,a_m):\quad
\exists r\in\mathcal F_{BB}\quad
(e_i\otimes e_i)(r)=0\quad(1\le i\le m).
\tag{282.2}
$$

这些有限原读数仍来自同一个原归一态；两张原边缘仍在同一实际球中。三球可以只选四个不共面的球面点。令 $\mathsf Z_1^{\rm aff}$ 表示每张原实际二纯三球都有这样的四点及同一个原见证。不将内禀球泛函预定为可延伸的原proper效应。

**定理 282.2（无平衡权的原有限接触等价）。** 在完整低两层原结构及M1、M2中，对每组满足(282.1)的固定方向，

$$
\mathsf Z_B^{\rm aff}(a_1,\ldots,a_m)
\quad\Longleftrightarrow\quad \mathsf Z_B.
\tag{282.3}
$$

成立时，(282.2)的原见证恰为280.3的同一个球心边缘纠缠纯态 $r_B$。全部原端点刻度、$\gamma_B=1/(d+1)$、$d\ge3$、全域帽等式及281.3的全部相关旁观网络结论均成立。

证明。先把有限接触所需的内禀正性与原proper预算分开。280.2（一）的原互补切片论证给每个 $r\in\mathcal F_{BB}$ 的支撑 $r\in W_B\otimes W_B$，其中 $W_B=\operatorname{span}C_B$。实际面满足 $C\cap W_B=C_B$：若 $v=a-b\in C$、$a,b\in C_B$，则 $v+b=a$ 的面性质给 $v\in C_B$。有限维双极性因而给

$$
(C_B)^*_{W_B}
=\overline{\operatorname{res}_{W_B}(C^*)}.
\tag{282.4}
$$

这是270.2所用的对偶限制闭包，不要求限制映射的像闭。任意两个内禀正泛函可分别用原正泛函限制逼近；原产品正性及 $r$ 的支撑使极限产品读数仍非负。因此在球齐次基中，将归一态写为 $(1,x,y,R)$ 后，其内禀双线性式

$$
G(a,b)=1+x\cdot a+y\cdot b+a^{\mathsf T}Rb
\quad(\|a\|,\|b\|\le1)
\tag{282.5}
$$

在整个球积非负。这一步只使用原正锥与极限，没有给内禀泛函共同的proper延伸预算。

若(282.2)成立，281.2（一）的原条件态下界先对选中端点给 $\min_Be_i=0$，所以它们的原限制确为 $(1+a_i\cdot a)/2$。故同一个(282.5)满足 $G(a_i,a_i)=0$。下面直接比较两个不同接触点，不再引入平衡矩阵。

所需的成熟球边界事实及其接合如下。设任一球积非负仿射双线性式为

$$
g(a,b)=\lambda+v\cdot a+w\cdot b+a^{\mathsf T}Mb.
\tag{282.6}
$$

若 $g(a_i,a_i)=0$，固定第一腿所得非负仿射函数在单位端点 $a_i$ 取零，其线性项只能反向平行于该端点。因此

$$
\begin{aligned}
g(a_i,b)&=A_i(1-a_i\cdot b),& A_i&=\lambda+v\cdot a_i\ge0,\\
g(a,a_j)&=B_j(1-a\cdot a_j),& B_j&=\lambda+w\cdot a_j\ge0.
\end{aligned}
\tag{282.7}
$$

在交叉点 $(a_i,a_j)$ 评价，两式相同。互异性给 $1-a_i\cdot a_j>0$，所以 $A_i=B_j$（$i\ne j$）。至少三个互异点已使所有 $A_i,B_i$ 等于同一常数：对任意两个指标，总能用第三个指标比较。于是 $v\cdot a_i=w\cdot a_i$ 都与 $i$ 无关。(282.1)使差向量 $a_i-a_1$ 张成 $\mathbb R^d$，故 $v=w=0$。再由(282.7)的线性系数得 $Ma_i=-\lambda a_i$；这些方向线性张成，故

$$
g(a,b)=\lambda(1-a\cdot b).
\tag{282.8}
$$

将这个中间计算用于同一个原态的(282.5)，得 $x=y=0,R=-I$。原有限零面与实际边缘面的交因而是单点；它是原 $K_2$ 的非空实际面，所以 $r=r_B$ 是原纯点。此时才使用M2给它的原least $e_{r_B}$。279.2的原产品单点least因子化及补门leastness给零互易：

$$
(e_i\otimes e_i)(r_B)=0
\quad\Longrightarrow\quad
e_{r_B}(p_i\otimes p_i)=0.
\tag{282.9}
$$

原 $e_{r_B}$ 在整个球积非负，故再用(282.6)—(282.8)得其限制为 $\lambda(1-a\cdot b)$。同一实际态的归一确认给 $1=e_{r_B}(r_B)=(d+1)\lambda$。因此原proper补帽 $u_2-e_{r_B}$ 确认整个同纯产品族，原共同least迫 $k_B\le u_2-e_{r_B}$，遂有 $k_B(r_B)=0$。反向，$e_i\otimes e_i\le k_B$ 直接给全部有限零。

现在才复用280.2和281.3，取得所有端点半球刻度、维数预算、全域 $e_{r_B}=h\otimes h-k_B$ 及同一原杯帽的全相关旁观正回缩。仍只有未缩放分支的质量预算，不将缩放后的规范回缩宣布为不增质量、保单位或实际设备。交叉等式是同一个正形式在两个接触点的两种读法相同；没有先假定任意纯态间的数值互易。$\square$

**命题 282.3（三个接触留下的圆与四点配置的范围）。** 三个线性独立单位方向在三维球中，仅凭(282.5)的内禀产品正性及三个对角零，不能确定 $x=y=0,R=-I$。全部满足这些读数的归一内禀最大张量锥元素恰为下列一参数族。令 $n\in\mathbb R^3$ 由 $n\cdot a_i=1$（$i=1,2,3$）唯一确定，置 $L=\|n\|^2>1$，则

$$
\begin{aligned}
x=y&=-s n,\qquad R=-(1-s)I+snn^{\mathsf T},\\
0\le s&\le\frac{2}{L+1},\\
G_s(a,a)&=s(n\cdot a-1)^2\qquad(\|a\|=1).
\end{aligned}
\tag{282.10}
$$

这是内禀正性方法的精确余量，不是完整原 $\mathsf F+$M 的反模型。反之，三球四个不共面的接触可以全在同一开半球，仍适用282.2。

证明。(282.7)的交叉比较在三个互异接触已经给 $x\cdot a_i=y\cdot a_i=t$。线性独立使 $x=y=t n$。零点的球边界系数给 $Ra_i=-tn-(1+t)a_i$，所以 $R=-(1+t)I-tnn^{\mathsf T}$；令 $s=-t$ 即得(282.10)首行。三个单位点不可能都在球面与某个切平面的唯一交点，故 $L>1$。球面对角的非负性给 $s\ge0$。

对任意单位 $a$，令 $k=n\cdot a$。固定第一腿后，关于第二腿的常数项为 $1-sk$，线性项为 $-sn-(1-s)a+skn$，且

$$
(1-sk)^2-\|-sn-(1-s)a+skn\|^2
=s\,[2-s(L+1)](k-1)^2.
\tag{282.11}
$$

非负仿射球函数的常数项须不小于线性项的范数。存在 $k\ne1$，故必要地 $s\le2/(L+1)$；反过来，这个区间使(282.11)非负，且

$$
1-sk\ge1-\frac{2\sqrt L}{L+1}>0.
\tag{282.12}
$$

于是对全部球面两腿非负，分腿仿射性将其延到整个实心球积。边缘向量满足 $\|sn\|\le2\sqrt L/(L+1)<1$，所以它们也在球内。$s>0$ 时对角零集恰为球面与 $n\cdot a=1$ 的圆；$s=0$ 时才是整个球面。三个正交方向给 $n=(1,1,1)$、$0\le s\le1/2$，不是任意二次插值的模糊自由度。

原(282.2)的三方向见证若存在，必须落在这一族中；但完整原菜单、M及更高层兼容性是否排掉 $s>0$，或者是否另迫原 $s=0$ 见证存在，均未由本命题结算。内禀最大锥成员不自动属于指定实际 $C_2$，也不供应原least帽。

四点的非平衡例可取 $0<\epsilon<1$ 及

$$
(\epsilon,0,\sqrt{1-\epsilon^2}),\quad
(-\epsilon,0,\sqrt{1-\epsilon^2}),\quad
(0,\epsilon,\sqrt{1-\epsilon^2}),\quad (0,0,1).
\tag{282.13}
$$

前三点张成一张水平仿射平面，第四点在其外；四点皆在北半球，故没有正权球心平衡，却满足(282.1)。这表明282.2允许的配置超出281.1，不表示两种完整候选的模型类严格包含，也没有给含噪近似稳定性或所有原约束下的最少方向定理。$\square$

**定义 282.4（仿射接触与同一门差三面的完整候选）。** 固定原 $b_*\in P_1$ 和任意原 $o\in\operatorname{ri}K_1$。保持原完整实际 $\mathrm{L2}_1$ 及280.1的固定纤维 $\mathsf A_{b_*}$。只要求另有原 $a_0,a_1\in P_2,d\in P_1$，令

$$
\begin{aligned}
p&=a_0\otimes b_*,\quad q=a_1\otimes d,\quad z=(p+q)/2,\\
R&=h_{\{p,q\}}-e_p,\\
\ell_1(x)&=R(x\otimes o\otimes o),\quad
\ell_2(x)=R(o\otimes x\otimes o),\quad
\ell_3(x)=R(o\otimes o\otimes x),\\
F_i&=\operatorname{face}_{C_1^*}(\ell_i).
\end{aligned}
\tag{282.14}
$$

这里要求原 $\{p,q\}$ 在整个 $\mathcal E_3$ 有共同least；$e_p$ 由固定纤维已付。$h_{\{p,q\}}$ 也就是确认 $z$ 的least。定义 $\mathsf E_{\rm Sh}(b_*;o)$ 为这对原源存在且满足

$$
\dim F_i>1\quad(i=1,2,3),\qquad
F_j=C_1^*\quad\text{对某个 }j.
\tag{282.15}
$$

它只读同一个原正门差的三张影子面，不另读概率重叠、非独立性、边缘覆盖、正则矩阵线或第三腿方向。完整候选为

$$
\boxed{\quad
\mathsf Q_{\rm aff}(b_*;o)=
\mathsf A_{b_*}+\mathrm{L2}_1+\mathsf Z_1^{\rm aff}
+\mathsf E_{\rm Sh}(b_*;o).
\quad}
\tag{282.16}
$$

**定理 282.5（仿射接触与三面关系恢复全部有限复量子层级）。** 在完整原 $\mathsf F$ 中，相对于278.2明列的M加数值互易Jordan桥及实际L2复类型选择、276.2的M-only双份整锥供应、[Q282Tail]的原单边Gram与同一门差三面桥，以及XIII165.9第1项到第4项的全有限传播，(282.16)等价于存在同一 $n\ge2$ 与同一保单位实线性序同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\qquad(N\ge0).
\tag{282.17}
$$

证明。固定纤维下降完整M2、M1。282.2逐球给 $\mathsf Z_1$，280.2—280.3给全部半球刻度、单体数值互易及 $\mathsf C_\Delta$；保留上述具名供应，取得同一单体复矩阵表示及标准双份整锥，不预付这些坐标。281.3的全域帽和实际网络随之取得，但不用它循环制造零接触见证。

任取原内部 $c_3\in\operatorname{ri}K_3$。XIX281.2的逐源least／全原纯端点星形等价，将 $\mathsf A_{b_*}$ 送到XIX290.1的 $\mathsf D_{b_*}(c_3)$，将所选共同least送到同一 $\mathsf S_z(c_3)$。原 $R\ge0$ 及三张影子正性由原least序直接给出，正是XIX290的同一个 $R$。XIX290.2自动排除局域相同与正交退化；290.3将三张原影子面对应到同一余项的三腿支撑，而非不同实例各自可达的秩。290.4遂给两条数据腿秩至少二且一条满维；其同一余项的两侧条件负方向排尽镜像，回原同一个 $\theta$ 后接XIII165.9，得(282.17)。无需原矩阵线有可逆切片，也无需全三份M或所有产品对共同least。

反向，标准完整PSD族以支持投影给固定纤维及所需共同least。每个二维复支持的三球内，反对称秩一态对全部同向纯产品取零，故任选四个不共面方向给(282.2)。最后一对原源直接复用XIX290.4反向的 $A_0=I_n/\sqrt n,A_1=E_{00}$ 与 $d=(b+e)/\sqrt2$；同一正交余项的腿秩为 $(n,n,2)$，故三面条件对每个原内部 $o$ 成立。XIX290.3的原序倍支配也说明参照 $o$ 的选择不改这些最小面。$\square$

**命题 282.6（关系几何、量子字典及未付存在性）。** 本候选的有限几何入口是四个不共面的原球端点，而非围住球心的四面体；高层入口是两只原确认门之差的三张面。其比较一致性与仪器实施顺序分别承担不同的命题。

证明与范围。式(282.7)的交叉读数先把所有选中接触的两种尺度锁成一个值；仿射张成再把两个漂移都消掉。这使281的正权平衡、球心凸包条件及严格收缩矩阵不再作为本入口的前件或证明步骤。282.3同时给出在少一个方向时当前内禀正性方法所看不见的整条圆自由；没有把方法余量当作原理论反例。

由(282.17)，数学态、纯点、完整proper效应及全部有限单位分解分别成为密度矩阵、复射线、$0\preceq E\preceq I$ 的全部效应及全部数学POVM；原配对成为Born迹配对，原产品、置换、重括号、丢弃成为复张量、腿重排及偏迹，锐效应成为投影。过程仍精确保留XIX289.5／290.5的独立前件：全相关旁观保正给CP／Kraus，整个输入及合计分支质量预算给TNI／TP和数学仪器，事件可用性、锐效应与整个yes支持中性给相应事件及Lüders，指定连续可逆保锥保单位群给数学酉动力学。物理钟、能量、$\hbar$、无穷维及近似极限均不由(282.17)独自支付。

数值互易 $e_p(q)=e_q(p)$ 交换的是一次比较的两个对象，不自动交换两次仪器的执行次序；经典模型也能有这种互易。这里量子结构的附加约束明确落在原实际球、同一联合准备的有限零面和同一门差的三面兼容上，未把“可以两两比较”本身当作全部量子公理。缺少同一态，分别为零的四个读数不能拼成原面交；缺少球内边缘，当前条件态和内禀球支撑论证均缺前件。279.4的既有残余仍只先给暴露包 $H_B$ 中的边缘，$\gamma_B=0$ 时残余又为零；本节没有消除这项原存在性缺口。裸 $\mathsf F+\mathsf J_3^{\rm prod}+\mathrm{L2}_1$ 是否已迫原 $\mathsf Z_B$，以及更少局部零在全部原M／高层约束下是否足够，仍是未解决的具体问题。

本节新增承重是：未知原端点刻度下，以仿射张成的有限原零面先取得唯一原纯态，再由其原least帽的同一交叉接触和归一预算得到整球共同门零；这适用于不具正权平衡的配置。非负球仿射函数的边界法线、对偶限制闭包和Lorentz范数判据为成熟中间工具，不单独申领新理论；XIX290的三面桥与全有限传播直接复用，不重复申领。三球四面体与已有量子POVM认证文献[Q281SIC]的对应仍限于其预定Hilbert维数及量子域；原态／帽网络的成熟remote evaluation见[Q281Remote]§3 Lemma2和Theorem2，不替代未知实际复合中的成员存在。本节是保留所列前件的条件纸面理论，不声称最少方向、最少独立公理、严格逻辑弱化、全球原创、Lean核验或物理实现。

白话：在原来那颗球上，只挑四个不在同一平面的方向；它们可以挤在同一边，不必围着球心。问有没有同一种双份准备，让四个方向的“左右都说是”同时不发生，而且左右影子仍在原球里。每个零把一侧条件准备钉在反方向；再把两个零点交叉着读，同一个读数从左边算、从右边算必须相同，于是四处共用一把尺。四点不共面，便没有地方藏偏心和额外扭曲，只剩球心对球心的反向关联。它自己的最低门再做同样的比较，就把四处的零扩成整球的零。随后只看另两只最低门相减所留下的三张影子：都不能缩成单线，至少一张要铺满。连上原有传播关系，便得到完整有限量子结构。三点留下的一条圆还不能删；这样的同一个原准备是否必然存在，也仍要证明。$\square$

[Q282Tail]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "281.2的逐源least／全原星形等价；287.2的同一正交残余与单边Gram；289.3及290.1—290.5的原正门差、三张影子面、退化排除、支撑对应和XIII165.9奇异线全有限传播。"

## 追加锚（本行以下为增补区）

## 295. 一步分岔只须能够重合：从原门关系的局部汇合回到量子子空间

**定义 295.1（同一确认目标的一步关系）。** 沿用本卷282的完整强全有限背景 $\mathsf F$：非平凡有限维原 $V$、全部有限 $W_N=V^{\otimes N}$、闭尖生成原锥与严格正乘积单位、整个紧底及纯点、全部proper效应和有限单位分解、全部相关输入上的原min/max、正置换、重括号与丢弃。低二层入口及具名Jordan／复类型／M-only、双HS／迹、同一实际余项和XIII165.9整奇异线传播供应均按[XIX291—294][Q295Prev]保留。固定原 $b_*\in P_1$，取原 $a_0,a_1\in P_2,d\in P_1$，置 $p=a_0\otimes b_*,q=a_1\otimes d$。仍只支付稀疏族 $\mathcal F_{b_*;p,q}=\{\{a\otimes b_*\}:a\in P_2\}\cup\{\{p,q\}\}$，并记 $\mathcal E=[0,u_3]_{C_3^*}$、$\mathcal E(S)=\{f\in\mathcal E:f(s)=1\ (s\in S)\}$、$\mathcal A(S)=\operatorname{ext}\mathcal E\cap\mathcal E(S)$。比较仍在整个原 $K_3$ 上。对 $e,g\in\mathcal A(S)$ 定义覆盖下降

$$
g\mathrel{\searrow_S}e
\quad\Longleftrightarrow\quad
e<g\ \land\ \nexists h\in\mathcal A(S):e<h<g.
\tag{295.1}
$$

这里“一步”只指原端点序中间没有另一端点，不指拓扑邻近、已知维数差一、可枚举选项或一次物理操作。定义局部分岔条件

$$
\mathsf{Fork}(\mathcal F):\quad
\forall S\in\mathcal F\ \forall g,e,f\in\mathcal A(S),\quad
(g\searrow_S e\ \land\ g\searrow_S f)
\Longrightarrow\exists k\in\mathcal A(S):k\le e,\ k\le f.
\tag{295.2}
$$

允许 $e=f$；此时取 $k=e$。对不同分支，不要求 $k$ 紧接在两者下方，也不预选终点。下面先由该规则内生取得各纤维的唯一least $e_S$，然后才定义 $R=e_{\{p,q\}}-e_{\{p\}}$。原三盲面仍为 $Z_i(R)=\{x\in K_1:R(y_1\otimes y_2\otimes y_3)=0\text{ 对所有其余两腿原 }y_j\in K_1,\ y_i=x\}$；$\mathsf{Blind}(R)$ 要求每个 $Z_i$ 可严格插入一个原真面 $G_i$，即 $Z_i\subsetneq G_i\subsetneq K_1$，且至少一个 $Z_j=\varnothing$。空面属于原面格。完整候选为

$$
\boxed{\quad
\mathsf Q_{\rm fork}(b_*):=
\mathsf X_{T,2}+\exists a_0,a_1\in P_2\ \exists d\in P_1:
\mathsf{Fork}(\mathcal F_{b_*;p,q})\land\mathsf{Blind}(R).
\quad}
\tag{295.3}
$$

**引理 295.2（有限面高度把任意下降拆为覆盖步）。** 在XIX294.2的原区间背景中，对任意 $S\subseteq K$ 及 $e<g$ 于 $\mathcal A(S)$，存在从 $g$ 到 $e$ 的有限覆盖下降链，步数至多 $\dim C^*$。端点集合及每个点的覆盖分支均可无限；不要求其闭或紧。

证明。XIX294.2给原极端效应的严格下降每步严格降低原对偶锥最小面的维数。考察从 $g$ 到 $e$ 的所有有限严格链，其长度是一个非空有界整数集，故有最大值和达到它的链。若相邻两项之间另有 $h\in\mathcal A(S)$，插入它便增加长度，矛盾；故该链逐步为覆盖。任一严格步都下降整数面维数，故得步数界。这不把覆盖与面维差一等同，也不从非闭极端集抽取极限。$\square$

**定理 295.3（只闭合一步分岔已足够）。** 在同一原背景中，对任意 $S\subseteq K$，(295.2)的单纤维条件当且仅当XIX294.1的该纤维至多一个终点，亦当且仅当XIX293.1的任意两极端确认门有极端共同下界。成立时，三种关系选出的 $e_S$ 是整个 $\mathcal E(S)$ 的同一唯一least。

证明。XIX294.2—294.3已经保证每个端点下方都有终点：在其下方取最小整数面维的端点即可，不输入终点存在性。按 $\dim\operatorname{face}_{C^*}(g)$ 归纳，证明任意 $g\in\mathcal A(S)$ 下方至多一个终点。若 $g$ 自己是终点，其下只能是它；否则给任意两个终点 $a,b\le g$，引理295.2提供从 $g$ 到它们的覆盖链，首步记为 $e,f$。同一首步时用归纳；不同首步时(295.2)给 $k\le e,f$，再取一个 $k$ 下方的终点 $t$。$e,f$ 的面维都严格低于 $g$，所以归纳分别给 $a=t$ 和 $b=t$。因此 $g$ 下终点唯一。原单位门 $u$ 在每个 $\mathcal A(S)$ 中且支配全部端点：若 $u=(f+h)/2$，则 $u-f,u-h\in C^*$ 之和为零，尖性迫 $f=h=u$，所以 $u$ 确为原菜单极端点，且确认所有归一准备。故整个纤维终点唯一。反向若终点唯一，每个 $e,f$ 下方的终点就是同一个 $k$，给(295.2)。最后直接复用XIX294.3的极端收紧、有限凸表示及least等价；不重证一般紧有向纤维论证。空 $S$ 的唯一终点为零门；无限 $S$ 的确认者仍构成含单位门的紧面，论证不变。$\square$

这正是终止关系的局部汇合到整体汇合原则在原凸端点序中的应用：295.2使 $k\le e,f$ 等价于两支可经有限覆盖步汇到 $k$；终止性由原最小面高度承担，共同顶由原单位承担。有限高度不意味着分支有限或全图有限。“没有中间端点”的定义仍读取全原端点序，因此局部化不自动给识别覆盖、寻找汇合点或最低门的算法及成本界。

**推论 295.4（同一原见证与全部有限量子层级）。** 在295.1的整个背景和具名供应下，对每个固定原 $b_*$，(295.3)与XIX294.1的完整候选等价，也等价于存在同一个 $n\ge2$ 及同一保单位实线性序同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使所有有限 $N\ge0$ 同时满足

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{295.4}
$$

证明。295.3逐个已支付纤维给同一least，故固定同一 $b_*,a_0,a_1,d$ 时，$e_{\{p\}}$、$e_{\{p,q\}}$、原正差 $R$ 和全部 $Z_i(R)$ 与XIX294严格相同。随后直接应用XIX294.4：先用已付低单体PSD面分类和三盲面排退化，再以同一Gram余项、原max两侧排转置，回原同一坐标后接XIII165.9整奇异线传播。这里不先假高层PSD，也不要求原矩阵线已有可逆切片。反向由完整PSD层级的支持投影给每个目标的least，再由295.3回读局部分岔条件；三盲面见证复用XIX290.4的同一个原源。

替代入口也完整保留：可将 $\mathsf X_{T,2}$ 换成原实际 $\mathrm{L2}_1+\mathsf Z_1^{\rm aff}$，其中每个原二纯三球的四个不共面方向必须在同一实际双份态上同向取零，且其双边缘仍在原球中。295.3先给固定纤维M1／M2，再按本卷282.2、280.2—280.3及具名Jordan、复类型和M-only供应取得标准低二层；此后同一 $R$ 链保持。实际交面非空、全相关旁观输入和放大回缩预算未被定义消掉。$\square$

**命题 295.5（重建后的每个分岔实际补成一个子空间方块）。** 在(295.4)已成立后，令 $\mathcal H=\mathbb C^{n^3}$、$L_S=\operatorname{span}_{\mathbb C}\{\operatorname{ran}\rho:\rho\in S\}$。$\mathcal A(S)$ 准确对应所有满足 $L_S\subseteq L\subseteq\mathcal H$ 的正交投影 $P_L$；覆盖下降准确对应 $L\subsetneq G$ 且 $\dim_{\mathbb C}G-\dim_{\mathbb C}L=1$。若 $P_G$ 有两个不同的下覆盖 $P_L,P_M$，则 $P_{L\cap M}$ 同时是两者的下覆盖。

证明。XIX293.4的谱扰动给 $\operatorname{ext}[0,I]$ 恰为全部投影，含零与单位。对密度态 $\rho$，$\operatorname{Tr}(P_L\rho)=1$ 当且仅当 $\operatorname{Tr}((I-P_L)\rho)=0$，即 $(I-P_L)\rho^{1/2}=0$，恰为 $\operatorname{ran}\rho\subseteq L$；因此空及无限 $S$ 都给所列支持区间。投影的Löwner序当且仅当其范围包含：若 $P_L\preceq P_G$，在 $L$ 的单位向量上评价，正差与投影范数界迫该向量属于 $G$；反向嵌套投影相乘等于小投影，差是正投影。若维差至少二，可在两者间添一个复方向得到中间投影；维差一则没有中间子空间，证明覆盖刻画。两张不同余维一子空间满足 $L+M=G$，故维数公式给 $\dim(L\cap M)=\dim G-2$；其交仍含 $L_S$，于是其投影同时下覆盖两支。$\square$

所以简洁几何可以画成原确认图里“一个上点分两路、两路可以重新重合”；重建后才取得更强的四边形，每条边准确少一复维，最低点为 $P_{L_S}$。子空间交与张成给投影子序的格，不给整个非交换效应区间的Löwner meet；XIX277.5的边界仍在。原候选未输入子空间、复维、格、固定步数菱形或任意目标集的least；重建后才把这些结构回读出来。

**命题 295.6（反事实、来源与量子公理字典）。** 终止、共同顶和分岔闭合在本证明中各有准确位置。仅有局部汇合而没有终止，严格下降的无限链可以没有终点；只有终止和局部汇合而没有共同顶，两个孤立点各有终点；有共同顶及有限高度但不闭合其分岔，三点V形序留下两个终点。这些是序方法边界，不冒充完整原锥层级反模型。若将顶点扩成全部混合效应，同一确认纤维中任意 $e<g$ 之间都有中点 $(e+g)/2$，故根本没有覆盖边，(295.2)反而空洞成立；原混合门 $2^{-m}u$ 还给无限严格下降链。因此不能以全部混合效应的覆盖规则替代本候选。经典完整层级的坐标投影也会汇合，故局部汇合单独不选择复量子类型；低层入口、同一门差三盲面和全部具名供应仍承担选择。

由295.4，态与纯态分别是全部密度矩阵和复射线，proper效应是全部 $0\preceq E\preceq I$，有限单位分解是POVM，投影分解是PVM，原配对是 $\operatorname{Tr}(\rho E)$，原乘积与丢弃给复张量及偏迹。CP／Kraus仍要求全相关旁观保正；TNI／TP和仪器要求全输入及总分支预算；可用事件保留事件供应；Lüders保留锐效应及整个yes支持中性；数学酉动力学保留指定连续可逆、保单位且全相关旁观保正的一参数群。物理钟、能量、$\hbar$、无穷维和近似极限未由静态重建单独支付。零一确认也未替代原全部仿射概率表。

本章repo-derived成果是：原确认端点序的有限面高度，将只作用在同一上门的一步分岔规则，接成逐源相同的最低门、正差与三盲面，再回读为复子空间覆盖方块。终止关系的局部汇合原则、有限维面理论、子空间维数公式与投影格是成熟数学，正文给出所需应用的完整纸面证明，不申领其发明或外部优先性；量子重建直接复用具名供应。本候选省去对终点的全局唯一性陈述，也不再逐对检查所有端点，只比较同一门的两个下覆盖；覆盖定义仍量化原序，不据此声称独立逻辑信息、量词数、计算成本、公理数减少或严格弱化。产地为Codex理论综合与ChatGPT研究线索；这是条件纸面理论，未做Lean核验、消化或物理实现。

白话：把同一目标的确认门画成一张向下的图，只看不能混合拆开的门。两只门之间如果再也插不进第三只端点门，就连一条向下边。现在只问一件局部的事：从同一只门往下走一步，若有两条路，它们以后还能不能重新碰头？原来的有限维凸几何保证每次真下降都缩小一张面，路不会无限走下去；每只门又都在单位门下面，所以每个局部分岔能碰头，就迫整张图落到同一个终点。最低门不必提前宣布。挑出的两种准备得到的共同终点，减去第一种准备的终点，留下同一份正差；它三条腿漏掉哪些准备，仍按三盲面的包含关系接上原低层和有限传播。得到量子表示后，这张图才显出熟悉形状：点是复子空间，边是少一个复方向，两条岔路正好能补成一个方块，终点是目标共同占据的最小子空间。原候选只要求局部分岔能重合；实际零态、概率刻度、过程和时间仍各自保留前件。$\square$

[Q295Prev]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "291.1的原三盲面；292.1的稀疏确认纤维；293.2—293.4的端点凸表示、least及投影分类；294.1—294.4的原最小面有限高度、终点存在、唯一性和全有限量子对应。"

## 追加锚（本行以下为增补区）

## 296. 不必先找一步边：每只门严格下方的可比图不裂开

**定义 296.1（只由原二元序画出的下方图）。** 完整保留295.1的强全有限背景、原全部准备与相关输入、整个proper菜单、全部有限单位分解和具名低层／双HS／迹／XIII165.9供应。仍固定原 $b_*\in P_1$，取原 $a_0,a_1\in P_2,d\in P_1$，置 $p=a_0\otimes b_*,q=a_1\otimes d$，并精确保留295.1的稀疏族 $\mathcal F_{b_*;p,q}$、$\mathcal E(S)$、$\mathcal A(S)$ 和整个原 $K_3$ 上的效应序。对 $g\in\mathcal A(S)$，置

$$
B_S(g)=\{e\in\mathcal A(S):e<g\},\qquad
e\sim f\ \Longleftrightarrow\ e\ne f\ \land\ (e\le f\ \lor\ f\le e).
\tag{296.1}
$$

$\sim$ 是 $B_S(g)$ 上的无向连边，不是等价关系。定义 $\mathsf{Link}(\mathcal F)$：对每个 $S\in\mathcal F$、每个 $g\in\mathcal A(S)$，$B_S(g)$ 为空，或其可比图连通；即任意两点之间有一条全部顶点留在 $B_S(g)$ 内的有限可比折线。允许单点图和零长度路径，不要求图有限、局部有限、路径单调或在原空间中连续。上点 $g$ 不属于图，否则任意两点都能经 $g$ 连通，条件将失去约束。候选不再定义覆盖边，也不要求某两门交出共同第三门。由下述定理先内生提取各已付纤维的同一least $e_S$，再置 $R=e_{\{p,q\}}-e_{\{p\}}$，三盲面 $\mathsf{Blind}(R)$ 完整沿用295.1，得到

$$
\boxed{\quad
\mathsf Q_{\rm link}(b_*):=
\mathsf X_{T,2}+\exists a_0,a_1\in P_2\ \exists d\in P_1:
\mathsf{Link}(\mathcal F_{b_*;p,q})\land\mathsf{Blind}(R).
\quad}
\tag{296.2}
$$

**定理 296.2（下方连通准确恢复同一终点）。** 在原有限维闭尖锥完整区间及归一确认纤维中，对任意 $S\subseteq K$，296.1的单纤维条件当且仅当XIX294.1的终点至多一个，也当且仅当295.2的局部分岔条件。成立时全部 $e_S,R,Z_i(R)$ 与295逐同源相同。

证明。XIX294.2—294.3已经支付两个事实：原极端效应严格下降使最小锥面维数严格下降；每个原端点下方至少有一个终点。现按 $r(g)=\dim\operatorname{face}_{C^*}(g)$ 归纳，证明每个 $g\in\mathcal A(S)$ 下方终点唯一。若 $B_S(g)=\varnothing$，则 $g$ 自己是终点。否则，对每个 $x\in B_S(g)$，归纳给它下方的唯一终点 $t_x$。若相邻两点满足 $x\le y$，则 $t_x\le x\le y$，且 $t_x$ 仍是整个原纤维的终点；$y$ 下的唯一性迫 $t_x=t_y$。反向可比同理。沿296.1的有限折线，所有 $t_x$ 因而相同。$g$ 的任何终点严格位于 $B_S(g)$，并作为自身下方的唯一终点等于上述共同值，故唯一。295.3已经以尖性证明原单位 $u$ 是全部 $\mathcal A(S)$ 的极端共同顶；在 $u$ 下运用归纳即得全纤维终点唯一。

反向，若该纤维终点唯一，记为 $t$。任意端点下方已有终点，所以 $t$ 低于全部端点。对每个 $g$，若 $g=t$ 则 $B_S(g)$ 为空；否则 $t\in B_S(g)$ 且与其中每个其他顶点可比。任何两点因而可经 $t$ 用至多两条边相连。与295.2的等价及全纤维least直接复用295.3和XIX294.3；其有限凸表示仍使用完整混合菜单，不因图只取端点而删除。空 $S$ 的终点为零门，无限 $S$ 仍由原非空紧确认面承担。$\square$

此处连通性只是原二元可比关系的有限路径闭包；它不取原极端集的拓扑闭包，不假极端集闭，不以图的有限高度推顶点或分支有限。整数面维数仍仅在证明里使用。相对295，最后候选删去了“中间再无原端点”的覆盖关系；代价是连通性本身量化有限路径，不将其说成量词数、独立逻辑信息、复杂度或成本下降。

**推论 296.3（更大结构是带内生锥顶的旗复形）。** 对满足296.1的任意纤维，固定 $g\ne e_S$，$B_S(g)$ 的可比图直径至多二。以 $B_S(g)$ 的有限严格链为单纯形所得序复形，是以 $e_S$ 为锥顶的单纯锥；其通常几何实现可缩。$B_S(e_S)$ 为空，本推论不称空图或空实现可缩。

证明。296.2给 $e_S<g$ 且 $e_S\le e$ 对全部 $e\in B_S(g)$。所以每个有限链都能加入 $e_S$ 仍成链，这正是抽象单纯复形为锥的判据；在每个含该顶点的单纯形上把重心坐标线性移向它，给相容的收缩。图中任意两点也可经它相连。该论证允许无限顶点；每个单纯形仍有限。可比图的有限团恰是有限全序链，因此这也是该图的旗复形。锥顶作为唯一least是定理输出，没有预先放进候选。图本身可以有回路，不是树；“锥”也不是额外的原凸态锥等式。$\square$

**推论 296.4（同一三份见证恢复完整有限量子理论）。** 在295.1完整背景和具名供应下，对每个固定原 $b_*$，(296.2)与(295.3)、XIX294.1及295.4的全部有限复PSD层级等价。

证明。296.2在重建前、对同一固定 $b_*,a_0,a_1,d$ 给逐个相同的原least，故同一正门差与普遍三盲面不变；直接复用295.4。顺序保持：低单体面分类、三盲面排退化、同一Gram余项及原max两侧排镜像，回原同一 $\theta$ 后接XIII165.9，不假高层PSD，也不要求矩阵线中已有可逆点。所有有限 $N\ge0$ 共享同一 $n\ge2$ 与同一局域坐标，而非仅某个有限前缀或仅 $2^N$。反向标准PSD全部目标的支持投影给least，再用296.2回读所有下方图；三盲面复用同一标准源。

XX282的实际替代入口原样保留：单体实际 $\mathrm{L2}_1$，每张原二纯三球内的同一实际双份态四个不共面方向同向取零、双边缘仍在原球。先由296.2的固定纤维least下降M1／M2，随后282.2、280.2—280.3及具名Jordan、复类型、M-only供应支付标准低二层，再接本章同源链。实际交面存在、全相关输入及放大回缩质量预算不因图连通而免费取得。$\square$

**命题 296.5（量子表示后的锥形与不能误删的最低点）。** 在295.4的同一复表示中，沿295.5记 $L_S$ 为全部目标支持的复张成。若 $g=P_G\ne P_{L_S}$，则

$$
B_S(P_G)=\{P_L:L_S\subseteq L\subsetneq G\}.
\tag{296.3}
$$

左端必须允许 $L=L_S$。其序复形正是这些包含关系的有限旗所成的锥，锥顶是 $P_{L_S}$。若再把最低点删去，连通性可以立即失效：当 $\dim_{\mathbb C}(G/L_S)=2$，余下顶点对应这个二维商的全部复直线；任意两条不同直线不可比，图是多点离散图。

证明。295.5的投影—范围对应直接给(296.3)。去掉 $L_S$ 后，严格中间子空间通过商映射对应 $G/L_S$ 的非零真子空间。商维数为二时只能是一维，互异者无包含，所以没有连边。连通性论证不能以“只看非平凡中间点”为名排掉原最低点；候选只去掉上点。复直线族在其通常Grassmann拓扑下又是连通的 $\mathbb{CP}^1$，而这里的可比图离散，明确说明图连通与原欧氏或Grassmann拓扑连通不是同一谓词。$\square$

**命题 296.6（必须逐门检验的反事实与量子字典）。** 只检查整个 $\mathcal A(S)$ 的可比图没有约束，因为所有顶点都与单位门相连。即使只检查去掉单位的图也不足：取有限序 $a,b<g<u$、$a<h<u$，除此及传递边外不再添加比较，$g,h$ 不可比，$a,b$ 不可比，$b,h$ 不可比。$u$ 严格下方的图由路径 $b-g-a-h$ 连通，但 $g$ 严格下方仅有两个不连通点 $a,b$，也是两个不同终点。因此296.1须检查每个原 $g$，不能只查单位。

去掉有限高度也失败：在反序自然数链 $x_0>x_1>\cdots$ 上再加共同顶 $u>x_0$，每只点严格下方的图都是非空可比链而连通，却没有任何终点。去掉共同顶，两个孤立点的严格下方都空，各自仍是终点。它们只界定序方法，不冒充全部强全有限原锥背景反模型。经典完整层级同样通过下方连通，仍失败量子换点；原三盲面与低层入口不能删除。完整概率效应和整个状态序仍承重，零一确认或产品域比较不能替代它们。

静态量子公理对应完整沿295.4及295.6：所有有限层的态／纯点、效应／单位分解、原配对及复合分别给密度矩阵／复射线、PSD效应／POVM与PVM、Born迹配对及复张量／偏迹。过程仍分别消费全相关旁观保正、全输入及合计分支预算、事件供应、锐效应与整个yes支持中性、指定连续可逆保单位且全相关旁观保正的一参数群，才给CP／Kraus、TNI／TP与仪器、可用事件、Lüders及数学酉动力学。物理钟、能量、$\hbar$、无限和近似极限照旧。

本章repo-derived接合是把局部覆盖分岔换成严格下方原可比图的连通性，并以面高度归纳保持同一原least、门差和三盲面；图的有限路径闭包、序复形、旗复形和有最小点即为锥的事实是成熟工具；[Wachs，§1.1][Q296Wachs]给出有限序复形及上下端点的锥形说明，本章允许无限顶点的部分由296.3逐有限链添同一锥顶直接证明，不从其有限域约定越界借用；量子重建复用具名供应。不申领更少独立公理、严格弱化、成本下降、全球原创或全部存在前提自动内生。正文是条件数学纸证，非Lean核验；图连边不是可实施转换，锥形收缩不是物理制备过程。

白话：不再先判断哪两只门之间恰好只有一步。把原来不能混合拆开的门当成点，只要两门在整个原状态域上能比大小，就连一条线。对同一个确认目标，拿起任意一只门，只看严格压在它下面的那些点；它们可以一个也没有，但有点时不能裂成彼此走不到的几片。为什么这足够？每次真下降都会缩小原正锥里的一张面，有限维使下降必然停住；低处相连的两点又必须认同同一个停点，沿线传下去，整个下方只剩一个终点。单位门压在全部门上，于是整张确认图共用同一只最低门，连混合门也在它上面。两种指定准备的共同最低门减去第一只最低门，仍留下同一份正差；三条腿漏掉什么，仍由同样的盲面关系接回低层和全部有限量子结构。重建以后，点才显成复子空间；每只上门下方的全部旗形都围着目标最小支持缩成一只锥。只去掉上门，不能连最低点也一起去掉。候选留下的是原二元大小关系的“下方不裂开”；实际联合准备、完整概率、仪器与时间仍明说前件。$\square$

[Q296Wachs]: https://arxiv.org/abs/math/0602226v2 "Michelle L. Wachs, Poset Topology: Tools and Applications, v2, §1.1：有限序的序复形、上下端点及锥形可缩性；不承担本章原锥有限高度、图连通到least或量子重建。"

## 追加锚（本行以下为增补区）

## 297. 大圆三次零比较：纯端点预算只留反关联与法向反射

**定义 297.1（同一大圆的原三零面与不塌缩关系）。** 完整保留279.1的非平凡强全有限背景 $\mathsf F$：所有有限原锥、全部原态与纯点、整个正对偶和proper菜单、全部有限单位分解、正置换及其正逆、重括号、正丢弃，以及包含所有相关输入的任意有限分块min/max。以下局部结论先只要求已经支付M1、M2。固定原实际三球 $B=\iota(\overline{\mathbb B}^3)$，沿用 $\mathcal F_{BB},W_B,c_B,h,k_B,t_B$。选过球心的二维线性平面 $P\subset\mathbb R^3$ 和其单位法向 $n$，在其大圆上取三个互异方向 $a_1,a_2,a_3$。三点自动仿射张成 $P$；不要求等角、球心凸包或任何平衡权重。置 $p_i=\iota(a_i)$、$e_i=e_{p_i}$，定义原实际面

$$
\begin{aligned}
\mathcal D_B(a_1,a_2,a_3)
&=\mathcal F_{BB}\cap\bigcap_{i=1}^3\{r:(e_i\otimes e_i)(r)=0\},\\
\mathsf{NC}_B&:\quad
k_B\ne h\otimes h,\\
\mathsf{GC}_B(a_1,a_2,a_3)&:\quad
\mathcal D_B(a_1,a_2,a_3)\ne\varnothing\ \land\ \mathsf{NC}_B.
\end{aligned}
\tag{297.1}
$$

由279.2，$h\otimes h$ 正是整个球内纯产品矩形的原共同least，$k_B$ 是同向纯产品对角族的原共同least。因此 $\mathsf{NC}_B$ 比较的是两个原确认族内生选出的门，不另指定概率常数。由279.3，它等价于 $\gamma_B>0$，并等价于存在一对球内准备，使某个确认全部同向纯产品的原proper效应不确认该准备对。最后一个等价由 $k_B|_{B\times B}=1-\gamma_B(1-x\cdot y)$ 及leastness给出。定义297.1没有把原面交的非空或两门的不同当作自动成立。

**定理 297.2（原三零面的精确端点二分）。** 若 $\mathcal D_B(a_1,a_2,a_3)$ 非空，则在球齐次基 $(c_B,b_1,b_2,b_3)$ 中，其全部归一态都是

$$
H_\kappa=J+\kappa vv^{\mathsf T},\qquad
J=\operatorname{diag}(1,-I_3),\quad v=(0,n),\quad
0\le\kappa\le2.
\tag{297.2}
$$

矩阵的首行和首列是质量及边缘系数，故两张原边缘都恰为 $c_B$。记该系数张量为 $r_\kappa$；只有已经属于原 $K_2$ 的参数才是原态，不预付整条内禀正线的成员资格。原三零面恰有以下三种可能：

$$
\mathcal D_B=\{r_0\},\qquad
\mathcal D_B=\{r_2\},\qquad
\mathcal D_B=[r_0,r_2].
\tag{297.3}
$$

出现的端点都是原 $K_2$ 纯点。其原least帽在整个球积上的限制分别为 $J/4$、$H_2/4$。尤其 $r_0$ 出现就给 $\mathsf Z_B$。这里没有声称三种局部形状都能延伸成满足完整 $\mathsf F$ 的模型。

证明。（一）先支付原支撑与内禀正性。$\mathcal F_{BB}$ 是原 $K_2$ 的紧实际面；280.2（一）的互补原条件态给每个见证的支撑 $W_B\otimes W_B$。282.4的对偶限制闭包把原正产品读数延到全部内禀正球泛函，故其归一式 $1+x\cdot a+y\cdot b+a^{\mathsf T}Rb$ 在整个球积非负。这没有给内禀半球泛函原proper延伸。281.4的同一条件态下界又使三个选中 $e_i$ 的球内限制恰为 $(1+a_i\cdot a)/2$；故三个原零确实给同一内禀式的三个对角零。

（二）三点的双仿射刚性。对任何在整个球积非负的 $g(a,b)=\lambda+\xi\cdot a+\eta\cdot b+a^{\mathsf T}Mb$，若三个 $g(a_i,a_i)=0$，282.7的球边界法线给

$$
g(a_i,b)=A_i(1-a_i\cdot b),\qquad
g(a,a_j)=B_j(1-a\cdot a_j).
\tag{297.4}
$$

交叉点的同一读数使 $A_i=B_j$ 对 $i\ne j$ 成立；三个互异点使全部尺度相同。三点仿射张成 $P$，所以 $\xi,\eta$ 的平面分量为零，且共同尺度为 $\lambda$。两侧线性系数给

$$
\eta+M^{\mathsf T}a_i=-\lambda a_i,\qquad
\xi+Ma_i=-\lambda a_i.
\tag{297.5}
$$

相减并用差向量张成 $P$，得 $(M+\lambda I)|_P=(M^{\mathsf T}+\lambda I)|_P=0$。故两方向的平面—法向交叉块都为零；再代回任一 $a_i\in P$ 得 $\xi=\eta=0$。仅剩法向—法向分量：

$$
g(a,b)=\lambda(1-a\cdot b)+\mu(n\cdot a)(n\cdot b),
\qquad \lambda\ge0,\quad 0\le\mu\le2\lambda.
\tag{297.6}
$$

必要性分别在 $(n,n)$、$(n,-n)$ 及平面内的异向对上读取。充分性由双线性矩阵的算子范数给出：其空间块在 $P$ 上为 $-\lambda I$，法向上为 $-\lambda+\mu$，所以范数不超过 $\lambda$，从而在整个实心球积非负。用于（一）的归一态时 $\lambda=1$，给(297.2)及完整参数界。此界消费了整个球积正性，不是仅凭三个已选方向的条件态得到。

（三）原纯端点的帽预算。三零原面是紧凸集，系数映射将其一一对应到某个非空闭区间 $I\subseteq[0,2]$。该区间的端点是三零面的极端点，而三零面是 $K_2$ 的实际面，故它们是原纯点。对一个这样的 $r_\kappa$，原产品least因子化与补门leastness给

$$
e_{r_\kappa}\le u_2-e_i\otimes e_i,
\qquad e_{r_\kappa}(p_i\otimes p_i)=0.
\tag{297.7}
$$

因此原帽的球积限制可用（二）写成 $G=\alpha J+\beta vv^{\mathsf T}$，其中 $\alpha\ge0$、$0\le\beta\le2\alpha$。还必须保留(297.7)的原proper上界。选平面内单位 $z\perp a_i$，令 $b_\pm=\cos\epsilon\,a_i\pm\sin\epsilon\,z$。同一上界在原产品 $\iota(b_+)\otimes\iota(b_-)$ 上给

$$
2\alpha\sin^2\epsilon
\le 1-\left(\frac{1+\cos\epsilon}{2}\right)^2,
\qquad \alpha\le\frac14.
\tag{297.8}
$$

后一式由除以 $\sin^2\epsilon$ 后令 $\epsilon\to0$ 得到。它不把内禀帽的正性上界当作原least上界，实际使用的是同一原 $e_i$ 和原 $e_{r_\kappa}$。

在同一个原态上归一确认，逐系数配对得

$$
1=e_{r_\kappa}(r_\kappa)
=(4-\kappa)\alpha+(\kappa-1)\beta.
\tag{297.9}
$$

若 $0<\kappa\le1$，右边不超过 $(4-\kappa)\alpha\le(4-\kappa)/4<1$。若 $1<\kappa<2$，由 $\beta\le2\alpha$，右边不超过 $(2+\kappa)\alpha\le(2+\kappa)/4<1$。均矛盾，故原纯端点只能是 $\kappa=0$ 或 $2$。闭区间 $I$ 遂只有(297.3)的三种可能。$\kappa=0$ 时等号迫 $\alpha=1/4,\beta=0$；$\kappa=2$ 时迫 $\alpha=1/4,\beta=1/2$，给所述原帽限制。

（四）若 $r_0$ 出现，$e_{r_0}|_{B\times B}=J/4$ 在整个同向球面对角取零。原proper补帽 $u_2-e_{r_0}$ 确认全部 $\Delta_B$，共同least给 $k_B\le u_2-e_{r_0}$，故 $k_B(r_0)=0$。这才取得 $\mathsf Z_B$，继而可复用280.2和281.3；没有以这些后续结论循环构造 $r_0$。$\square$

**定理 297.3（三个大圆零加原门不塌缩准确等价整球零接触）。** 对每组固定的大圆三方向，在上述完整原背景及M1、M2中，

$$
\mathsf{GC}_B(a_1,a_2,a_3)
\quad\Longleftrightarrow\quad \mathsf Z_B.
\tag{297.10}
$$

因此原 $\gamma_B=1/4$、全部端点半球刻度、原唯一球心边缘反关联纯态、全域帽 $e_{r_0}=t_B$ 及281.3的全部相关旁观网络均为后果，不再输入概率校准值。没有删去 $\mathsf{NC}_B$。

证明。正向，若三零面已有 $r_0$，297.2（四）即给结论。否则297.3迫它为 $\{r_2\}$，故 $r_2$ 是原实际态。由 $\mathsf{NC}_B$ 和279.3，原proper效应 $t_B=h\otimes h-k_B$ 的球积限制为 $\gamma_BJ$，其中 $\gamma_B>0$。

原 $2|2$ 最小界先给 $r_2\otimes r_2\in C_4$。将中间两腿合成一块，以同一个原 $t_B\in C_2^*$ 切片；原置换及含相关输入的 $2|2$ 最大界给实际输出

$$
s=(\mathrm{id}\otimes t_B\otimes\mathrm{id})(r_2\otimes r_2)\in C_2.
\tag{297.11}
$$

两份资源都支撑于 $W_B\otimes W_B$，所以输出在同一 $W_B\otimes W_B$。在球齐次系数中，$H_2$ 与 $J$ 都为对称对角矩阵，$H_2^2=J^2=I_4$，且 $H_2JH_2=J$，故

$$
H_s=\gamma_BH_2JH_2=\gamma_BJ,\qquad
u_2(s)=\gamma_B>0.
\tag{297.12}
$$

于是 $s/\gamma_B$ 是原归一态，两个边缘恰为 $c_B$，系数恰为 $r_0$；其三个原产品读数都为零。它确属同一个原三零面，297.2（四）给 $\mathsf Z_B$。这也排除了在 $\mathsf{NC}_B$ 下只有反射单点的情形。网络实际使用两份原杯和一只原双份帽，没有把内禀正张量直接声明为原态。

反向，原 $\mathsf Z_B$ 见证使所有 $e_i\otimes e_i\le k_B$ 同时取零。280.2给 $\gamma_B=1/4$，279.3即给 $k_B\ne h\otimes h$。故同一见证满足297.1。$\square$

**命题 297.4（剩余反射分支仍须接受全有限网络约束）。** 即使没有 $\mathsf{NC}_B$，297.2中实际出现的 $r_2$ 及其原帽也给一个全相关旁观保正的线性回缩。令

$$
L(v)=(\mathrm{id}\otimes e_{r_2})(r_2\otimes v),\qquad P_B^{\rm ref}=4L.
\tag{297.13}
$$

则 $P_B^{\rm ref}(V)=W_B$、$P_B^{\rm ref}(C)=C_B$、$P_B^{\rm ref}|_{W_B}=\mathrm{id}$、$(P_B^{\rm ref})^2=P_B^{\rm ref}$，且 $(P_B^{\rm ref}\otimes\mathrm{id}_m)C_{m+1}\subseteq C_{m+1}$ 对全部有限原相关旁观输入成立。未缩放 $L$ 不增总质量；没有由此证明放大后的 $P_B^{\rm ref}$ 不增质量、保单位、球暴露或设备可用性。

证明。$r_2$ 的第一腿支撑给 $L(V)\subseteq W_B$。原 $2|(m+1)$ 最小界及重排后的 $(m+1)|2$ 最大界，以实际帽 $e_{r_2}$ 切片，给全部原相关输入的正性。局域正输出落在 $C\cap W_B=C_B$。297.2的帽限制 $H_2/4$ 使 $L|_{W_B}=H_2(H_2/4)=I_4/4$，故放大后恰为所述回缩，且像锥等于 $C_B$。补帽 $u_2-e_{r_2}$ 的同一正性给两分支输出之和为 $c_B\otimes(\pi_m z)$，其总质量等于原输入质量，故 $L$ 分支不增质量。放大四倍后没有相同预算结论。这是281.3成熟杯帽计算在另一个原端点上的应用，不将它另计作新回缩原理。$\square$

**定义 297.5（大圆三零与下方连通的完整候选）。** 原单体实际 $\mathrm{L2}_1$ 仍要求任意两不同原纯点所生成的整个最小实际面是完整非退化三球。令 $\mathsf{GC}_1$ 要求每张这样的球存在一组297.1的大圆三方向，使 $\mathsf{GC}_B$ 成立。固定原 $b_*\in P_1$，沿用[XIX292—293][Q297Tail]的稀疏目标族

$$
\begin{aligned}
p&=a_0\otimes b_*,\qquad q=a_1\otimes d,\\
\mathcal F_{b_*;p,q}
&=\{\{a\otimes b_*\}:a\in P_2\}\cup\{\{p,q\}\},\\
\mathcal A(S)&=\operatorname{ext}[0,u_3]_{C_3^*}\cap
\{f:f(s)=1\ (s\in S)\}.
\end{aligned}
\tag{297.14}
$$

采用本卷296.1的 $\mathsf{Link}(\mathcal F)$：对每个 $S\in\mathcal F$ 及每只原端点门 $g\in\mathcal A(S)$，严格下方集合 $B_S(g)=\{e\in\mathcal A(S):e<g\}$ 为空，或在不同顶点可比即连边的无向图中连通。连通只指全部顶点留在 $B_S(g)$ 内的有限可比折线；不把上点 $g$ 放回图，不要求原拓扑连通、图有限或先识别覆盖步。本卷296.2先由原面有限高度及下方连通推出每个纤维的同一唯一least $e_S$，并证明其等价于295的 $\mathsf{Fork}$ 及XIX293的 $\mathsf{ETight}$；此后才提取同一个原正门差 $R_{\mathcal F}=e_{\{p,q\}}-e_{\{p\}}$。原 $\mathsf{Blind}(R)$ 指对三张普遍零面

$$
Z_i(R)=\{x\in K_1:R(y_1\otimes y_2\otimes y_3)=0
\text{ 对所有其他两腿 }y_j\in K_1,\ y_i=x\}
\tag{297.15}
$$

分别存在原面 $Z_i(R)\subsetneq G_i\subsetneq K_1$，且至少一个 $Z_j(R)=\varnothing$。候选为

$$
\boxed{\quad
\mathsf Q_{\rm gc}(b_*)=
\mathrm{L2}_1+\mathsf{GC}_1+
\exists a_0,a_1\in P_2\ \exists d\in P_1:
\mathsf{Link}(\mathcal F_{b_*;p,q})\land\mathsf{Blind}(R_{\mathcal F}).
\quad}
\tag{297.16}
$$

球上的共同门在同一候选中由后项下降的M1、M2供应；不另外添加一份固定纤维公理。所有 $P_2$ 仍包括块内纠缠，全部原混合效应及任意原相关输入仍保留。极端门指凸菜单端点，尚未宣称是实际锐仪器。

**定理 297.6（大圆端点预算接回完整有限复量子理论）。** 在完整原 $\mathsf F$ 中，相对于278.2明列的M加数值互易Jordan桥、实际L2复类型选择、276.2的M-only双份整锥供应、[Q297Tail]的原纤维下方连通内生least与同一门差三盲面桥，以及XIII165.9第1项到第4项的全有限传播，(297.16)等价于存在同一 $n\ge2$ 与同一保单位实线性序同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\quad(N\ge0).
\tag{297.17}
$$

证明。本卷296.2先从每只上门严格下方的可比图连通取得终点唯一，再复用XIX293.2的有限凸分解与紧确认纤维，取得稀疏族的全部原least；其中固定 $b_*$ 的全部单点纤维就是280.1的 $\mathsf A_{b_*}$。原纯旁观下降给M2、M1，因此297.1的球门定义及297.2—297.3均已具备前件。逐球得到 $\mathsf Z_B$，280.2—280.3给全部半球刻度、单体数值互易和 $\mathsf C_\Delta$。具名Jordan、复类型与M-only整锥供应取得同一低二层坐标，280.3排除双份相对转置位。这些坐标是所得，不是从反射分支的名称预定。

所选 $a_0,a_1,d$ 的共同least及原 $R_{\mathcal F}$ 与XIX292.2—293.3逐个相同。其三张盲面按291.2—291.3对应同一余项的三张影子支持；290.2排退化，290.3识别同一Gram余项，290.4由两侧原完整max排掉剩余镜像。回到同一原坐标后，一腿满支持及其余腿非一维的同一余项准确支付XIII165.9的整奇异线传播，得到(297.17)。这直接复用已有供应，不以尾部重述计作新增数学。

反向，完整有限PSD族中每个所需确认纤维的支持投影既是least也是原proper区间极端元，由296.2的反向给 $\mathsf{Link}$。每张二纯三球的反对称秩一态使整球同向产品为零，280.2给 $\gamma_B=1/4$，因此任意选定大圆三方向都给 $\mathsf{GC}_B$。最后的同一源对与三盲面见证复用XIX290.4、291.3及293.3的反向，给(297.16)。$\square$

**命题 297.7（简洁性、反事实、量子字典及未解决的端点）。** 本入口用同一大圆上三个原零和两个共同门不同，替代四个不共面原零；三零面中的连续自由由原纯端点的确认预算压到两个端点，再由原非零门差的实际四腿收缩选出反关联。它减少一个显式零读数，却重新显列了整个对角族与矩形族的非塌缩关系，不声称独立信息减少、严格逻辑弱化、最少方向或寻找成本降低。

证明与范围。若删掉端点原帽的least上界，(297.2)整条内禀正线都满足三个零，(297.8)的尺度预算便无来源。若只删去 $\mathsf{NC}_B$，297.2留下 $\{r_2\}$；此时若没有 $r_0$，必有 $\gamma_B=0$，297.11的原残余帽收缩就是零输出，而297.13的原自帽回缩仍成立。没有由该零分支构造完整强全有限反模型，也没有证明它能或不能延伸；必须继续用所有原分块、原菜单和更高层兼容性判定。二层部分转置像锥应称为co-positive／转置像锥，不等于PSD与其部分转置像的PPT交锥；单独二层例子不能结算全有限问题。一般正锥的自对偶张量存在结果[Q297Tensor]也不自动指定给定二层锥或支付结合性及全部分块。

由(297.17)，原完整态、纯点和proper菜单分别为全部密度矩阵、复射线及 $0\preceq E\preceq I$，所有原有限单位分解成为全部数学POVM，锐效应成为投影及PVM；同一原配对成为Born迹概率。原产品、置换、重括号、丢弃成为同一复张量、腿重排和偏迹。过程仍逐项保留XIX289.5及本卷296.6的独立条件：全部相关旁观保正才给CP／Kraus，整个输入和总分支质量预算才给TNI／TP及数学仪器，事件供应、锐效应及整个yes支持中性才给相应事件和Lüders，指定连续可逆保锥保单位群才给数学酉动力学。物理钟、能量、$\hbar$、无穷维与近似极限均不由静态锥等式独自支付。

一次比较交换两个对象的数值互易，与两次仪器交换执行次序分别承担不同条件。“两两可比较、从哪端算都相同”提供交叉等尺度的图景，但量子结构还消费同一原联合准备、实际球、原least预算、非塌缩关系及同一三腿门差的盲面兼容；没有从一般对称二元关系直接推出量子论。定义和原序可内生选出最低门，存在这些关系的原系统仍是明列模型前件。

文献归属：球边界法线、仿射张成、闭区间端点、算子范数和小角预算是成熟工具；Lorentz正映射分类可参照[Q297Lorentz]，这里不以整个最大正映射锥的极射线替代原实际零面的纯端点。原杯帽收缩的成熟remote evaluation沿用[Q281Remote]§3 Lemma2；它给收缩关系，不赠送未知原成员或单位预算。279—282的原支撑、对偶限制闭包、共同门、零互易及归一化，及XIX291—294、本卷295—296的原序连通尾部均保持原归属。本节repo-derived新增承重是：在未知原复合中以原端点least预算得大圆三零面的精确二分，再用原非塌缩共同门差将实际反射端点送回原反关联端点的等价桥。结论是保留上述前件的纸面条件理论，不声称全球原创、Lean核验或物理实现。

白话：先在球上画一条过球心的大圆，只挑三个不同方向。找同一种双份准备，让三个方向的“左右同时说是”都不发生，且左右影子仍在原球里。三个零还会留下一根可滑动的杆；但杆的端点必须是原纯准备，它自己的最低确认门既要认出自己，又不能超过三个补门的预算，于是杆头只能留在“各向都反着”或“只有法向翻回来”两处。再要求原关系确实分得开“相同准备配对”和“任意准备配对”：两只最低门有非零差。把两份法向反射准备的中间两端接到这只差门，外面两端就得到各向反关联，三个局部零因此扩成整球零。最后只要求每只门严格下方的可比图不裂开，内生选出最低门，再检查同一门差的三张漏读面如何包含，接回完整有限量子结构。更少的零已经做到；两类配对必须可区分这件事仍是明说的条件，不能藏进“内生”二字。$\square$

[Q297Tail]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "291.1—291.3的普遍原准备零域、原盲面与同一影子对应；292.1—292.3的稀疏确认纤维内生least及同一门差；293.1—293.4的原极端门收紧与完整菜单凸补全；290.2—290.4及XIII165.9的同一余项定向与全有限传播。"
[Q297Lorentz]: https://arxiv.org/abs/quant-ph/0503194v1 "Hildebrand，Cones of ball-ball separable elements；Lemma6、Definition1和Theorem1的Lorentz正映射极射线分类；整个正映射锥的分类不支付指定原实际复合的成员存在。"
[Q297Tensor]: https://arxiv.org/abs/2408.07389v1 "Netzer，Self-Dual Cone Systems and Tensor Products；Theorem2.2的完整S-system及G包含于其对偶的前提，Corollary3.3的某个binary functorial自对偶张量；不将其改报为指定二层、结合且满足全部原分块的层级延伸。"

## 追加锚（本行以下为增补区）

## 298. 不再为两点输入最低门：只分开一对实际混合准备

**定义 298.1（由共同产品零方向生成的另一只准备）。** 完整保留296.1的强全有限背景 $\mathsf F$：非平凡有限实载体、每个有限份数的整个闭尖生成锥及严格正乘积单位、全部原准备和纯点、完整正对偶与proper区间、全部有限单位分解、实际产品、正置换及其逆、重括号、丢弃，以及对所有原相关输入和全部有限分块的min/max。固定 $b_*\in P_1$，只对单点族

$$
\mathcal F^1_{b_*}=\{\{a\otimes b_*\}:a\in P_2\}
\tag{298.1}
$$

要求296.1的 $\mathsf{Link}$，不再把所选两点的共同确认纤维放进该规则。由296.2已给这条固定纤维的least，沿283.1下降给整个M2、M1。低层采用XX282的 $\mathrm{L2}_1+\mathsf Z_1^{\rm aff}$：每张原实际二纯三球中，同一个实际双份态使四个不共面方向的同向产品确认读数为零，两张边缘仍在该球内。完整保留XX282.2、280.2—280.3所列的互易Jordan、复类型及M-only整锥供应；它们先给同一个 $n\ge2,\theta$ 下的标准 $C_1,C_2$。双HS／迹预算和XIII165.9的全有限传播供应均保留。这里的实际零交面存在仍是前提。

在这些已付低层关系中，$T_j(x,y)=e_x(y)$，$j=1,2$；取原 $a_0,a_1\in P_2,d\in P_1$，置 $p=a_0\otimes b_*,q=a_1\otimes d,z=(p+q)/2$。原共同产品零集及其凸包为

$$
\begin{aligned}
\mathcal Z_{p,q}^{\rm prod}
&=\{s\otimes t:s\in P_2,t\in P_1,
\ T_2(a_0,s)T_1(b_*,t)=T_2(a_1,s)T_1(d,t)=0\},\\
\mathcal C_{p,q}&=\operatorname{conv}\mathcal Z_{p,q}^{\rm prod}.
\end{aligned}
\tag{298.2}
$$

凸包只混合实际独立准备，不补入未知纠缠态。仍用289.1的 $\Delta(z)=z-m\otimes t_0$，其中 $m=(a_0+a_1)/2,t_0=(b_*+d)/2$；$\mathsf{Cov}(a_0,a_1)$ 精确取288.1—288.2的同一平均数据准备两张原边缘，一侧在 $\operatorname{ri}K_1$、另一侧非纯。要求

$$
T_3(p,q)=e_p(q)>0,\qquad \Delta(z)\ne0,\qquad
\mathsf{Cov}(a_0,a_1),
\tag{298.3}
$$

首点 $e_p$ 已由(298.1)支付。最后只要求：对某个 $\zeta\in\operatorname{ri}\mathcal C_{p,q}$，有一只原 $f\in\mathcal E_3=[0,u_3]$ 满足

$$
f(z)=1,\qquad f(\zeta)=0.
\tag{298.4}
$$

记此条件为 $z\perp_{\mathcal E_3}\zeta$；它是二元完美可区分关系，测试为同一单位分解 $(f,u_3-f)$。$f$ 不要求极端、最低或低于其他门。定义完整候选

$$
\boxed{\quad
\mathsf Q_{\rm sep}(b_*):=
\mathsf{Link}(\mathcal F^1_{b_*})+\mathrm{L2}_1+\mathsf Z_1^{\rm aff}
+\exists a_0,a_1,d:\ (298.3)\ \land\
\exists\zeta\in\operatorname{ri}\mathcal C_{p,q}:\ z\perp_{\mathcal E_3}\zeta.
\quad}
\tag{298.5}
$$

定义按照上述次序使用已生成的低层比较，不把未支付的高层矩阵类型写入原候选。

**定理 298.2（一次二元区分给出极端迹二门与同一原残余）。** 在(298.1)—(298.3)及具名供应下，$\mathcal Z_{p,q}^{\rm prod}$ 非空紧，$\mathcal C_{p,q}$ 是原 $K_3$ 中的非空紧凸集。(298.4)与同一 $f$ 确认 $p,q$ 且在整个 $\mathcal Z_{p,q}^{\rm prod}$ 为零等价，与所选相对内部 $\zeta$ 无关。若成立，可以选取满足这些读数的整个原区间极点 $h$；$D=h-e_p$ 是迹一非零极端proper效应，且在下述同一低层迹坐标的态—效应对应中为一个原纯准备、HS范数为一。没有先为 $p,q$ 输入共同least。

证明。先用原固定纤维和低层入口取得同一个 $\theta$，只在本证明写其坐标。设 $a_0=P_a,a_1=P_{a'},b_*=P_b,d=P_{b'}$，其中 $a,a'\in\mathbb C^{n^2}$，$b,b'\in\mathbb C^n$ 为单位向量，$v=a\otimes b,w=a'\otimes b'$。283.4（一）的单点预算只用首点least，给 $e_p=P_v=:P$；289.2的定向前乘法桥使(298.3)前两项恰好给两个局域重叠的模都在 $(0,1)$。整个原三份锥 $C$ 及其对偶都夹在该 $(12)|3$ 的Sep/BP之间，未假设 $C=\operatorname{PSD}_{n^3}$。

此时(298.2)准确变成所有与 $v,w$ 同时正交的单位产品投影。取单位 $s\perp a$ 及 $t\perp b'$，即给其中一点；单位球紧、零方程闭，故该集紧。有限维凸包紧且有非空相对内部，全部点仍为原实际准备。对任意 $\zeta\in\operatorname{ri}\mathcal C_{p,q}$ 和 $y\in\mathcal C_{p,q}$，相对内部性质给 $\zeta=\lambda y+(1-\lambda)y'$，其中 $0<\lambda<1,y'\in\mathcal C_{p,q}$。原正 $f$ 在 $\zeta$ 为零遂迫 $f(y)=0$；反向由凸性直接成立。又因proper $f$ 的读数在 $[0,1]$，$f(z)=1$ 等价于 $f(p)=f(q)=1$。相对内部只用于包住全部共同零方向，不是额外原制备操作；有限维凸表示使 $\zeta$ 可由有限个实际产品准备混合取得。

满足(298.4)的全部门是原紧区间中线性泛函 $g\mapsto g(z)-g(\zeta)$ 的最大值一所成非空暴露面。取其极点 $h$，面性质使它也是整个区间极点；不对原极端集假闭或紧。首点least给 $D=h-P\ge_{C^*}0$，且 $D\le I-P\le I$、$D(P)=0$。若 $D=(D_1+D_2)/2$ 是proper平均分解，则正性给 $D_i(P)=0$，所以 $I-D_i$ 确认 $P$。只用 $e_p=P$ 得 $P\le I-D_i$，故 $P+D_i$ 都proper。它们以极端 $h$ 为平均，迫 $D_1=D_2=D$。这复用283.4（二）的单边减法，所需只是 $h$ 极端，不是 $h$ 已有leastness。

再取274.15的四个可分正矩阵 $Q_A,Q_B,R_1,R_2$。两个块支持补各可分解成共同产品零方向的非负和；$R_1,R_2$ 本身就在该零集。因此本章直接有 $h(Q_A)=h(Q_B)=h(R_1)=h(R_2)=0$。这里不将这些零读数冒充 $h\le I-Q_A,I-Q_B,I-R_1,I-R_2$ 的原序上界。283.2证明中四上界承担的正是这些零读数；其后只用块正性作零边缘和交叉块消去。因此同一可逆产品图下仍得283.3的六实维稀疏形。令局域相位使两重叠为正，$g=\langle a,a'\rangle\langle b,b'\rangle\in(0,1)$。$h-P\in C^*\subseteq\operatorname{BP}$ 给283.4的 $A\ge1,D_0\ge0,|z_0|+|w_0|\le\sqrt{(A-1)D_0}$，两确认方程给 $A=D_0$ 及

$$
1=A(1+g^2)+2g\operatorname{Re}(z_0+w_0)
\ge1+(\sqrt{A-1}-g\sqrt A)^2\ge1.
\tag{298.6}
$$

逐项取等正是283.7—283.8，故 $h\in\operatorname{conv}\{H_0,H_1\}$ 且原 $\operatorname{Tr}h=2$，不是变换后矩阵的迹。于是 $\operatorname{Tr}D=1$。276.2（三）对迹一极端proper效应的双HS／迹等号链，直接给 $D\in\operatorname{ext}K_3\cap C\cap C^*$、$\|D\|_2=1$。该步骤不为残余另给least，也未在此把它当作普通PSD。两个Gram残余端点范数都一且不同，严格凸性遂迫它恰为其中一个。$\square$

**定理 298.3（把共同least变成输出的完整量子候选）。** 在298.1明列的完整背景及供应下，对每个原 $b_*$，(298.5)当且仅当存在同一 $n\ge2$ 和同一个保单位实线性序同构 $\theta:V\to H_n$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\qquad(\forall N\ge0).
\tag{298.7}
$$

证明。298.2给的原残余仍是同一产品割线的正交余项 $r=(I-P_v)w$ 的归一dyad或其第三腿镜像；辅助第三腿酉须同时运输态、锥和菜单，准确沿287.2（二）—（三），不先断言未知原锥在它下不变。(298.3)的边缘覆盖由288.7—288.9支付该同一余项的数据展平秩 $(n,r_0)$ 或 $(r_0,n)$，$r_0\ge2$，控制秩为二。289.3的两个实际交叠max约束及条件部分转置负方向因此适用，排掉镜像；低二层在本入口已经同向标准。逆辅助运输后取得原同一 $\theta$ 中的实际一侧满支撑二元GME种子，再精确应用XIII165.9第1到第4项，得(298.7)。允许其整条矩阵线奇异，不额外要求可逆切片。所有有限相关旁观输入、实际杯帽、交换Gram接合及严格正成功质量沿原供应保留，不把几种分别成功的准备相加当成一颗相干态。

反向，标准PSD模型的全部支持投影least给(298.1)的单点Link；二维支持中的反对称态给XX282的同向全零及球内边缘。选289.3同一反向源：$a_0=P_{|I_n\rangle\!\rangle/\sqrt n},a_1=P_{|E_{00}\rangle\!\rangle}$，$b$ 表示原 $b_*$，$b'=(b+e)/\sqrt2$、$e\perp b$。则 $T_3(p,q)=1/(2n)>0$、$\Delta(z)\ne0$，两张平均数据边缘均为 $(I_n/n+E_{00})/2\succ0$。令 $L=\operatorname{span}\{v,w\}$，普通支持投影 $P_L$ 同时确认 $p,q$ 且在整个共同产品零集为零，故对任意相对内部 $\zeta$ 都满足(298.4)。这是标准模型的反向，不是正向中预付 $P_L$ 的原成员关系。

只有在(298.7)取得以后，原 $\{p,q\}$ 的整个确认纤维才由支持投影有least；所有其他纤维的least和Link也随之回读。新候选与296刻画同一完整模型类，但没有把任意裸纤维的“存在一只区分门”说成leastness的普遍等价条件。$\square$

**命题 298.4（更短的几何是两张暴露面的分开）。** (298.4)等价于存在同一原单位分解 $(f,u_3-f)$，使两点中点 $z$ 和共同零方向的任一相对内部混合 $\zeta$ 被完全分开；等价地，原状态体有两张由同一proper效应给出的不交暴露面 $\{f=1\},\{f=0\}$，前者包含 $p,q$，后者包含整个 $\mathcal C_{p,q}$。给定这样的两张面后，极端门的存在由原紧区间承担，不需为两点另付端点收紧、覆盖汇合或下方连通。

证明。所有等价由298.2的相对内部与饱和面论证。所求几何不是把两个产品点的线段叫成量子二纯面：$z$ 与 $\zeta$ 都是原可分混合；纯三腿资源出现在 $h-e_p$ 的极端预算之后。重建后，$\{f=1\}$ 与 $\{f=0\}$ 是两个正交支持面，取 $f=P_L$ 时前者为整个 $L$ 上的密度体，后者为整个 $L^\perp$ 上的密度体。无需先证共同产品零的凸包已经填满后者；它只负责用相对内部的一点代表其全部零读数。

二元完美可区分及效应单位分解是成熟概率理论概念，[Wilce，Appendix B.1][Q298Wilce]明确列出其效应定义；这里不借其conjugate、filter或重建定理代付成员关系。非空紧凸集有极点、暴露面极点为整体极点及相对内部的正段性质亦是成熟中间工具。本章repo-derived承重接合是：将指定产品对的共同least替换为共同产品零混合与目标中点的一次区分，以极端饱和面和首点least支付同一个迹二门／迹一原残余，再接原两侧定向及全部有限传播。单边Gram、双预算、实际种子和传播不重报为新工具；不主张全球优先性、独立公理最少或严格逻辑弱化。$\square$

**命题 298.5（反事实与现有量子公理的对应）。** 紧凸性只在(298.4)非空以后选出极端门，不自动使它非空；单点least仍只由(298.1)支付。删除零读数，单位门便确认任意 $p,q$，无法限制共同支持；删除确认读数，零门便满足全部零。允许针对每个零方向另换一只门，也不能给同一饱和面的非空。残余的HS等号链在本证明中由选取极端门支付。上述分别由单位／零门及298.2的证明依赖给出，不冒充完整强背景的非量子反模型。

证明与边界。极端门的减法只用首点least；若不保留它，$h-e_p$ 的原正性和极端性均无本章依据。对未选极端的门，当前等号链尚缺极端性，证明先在非空饱和面中选极点。源的一般位置、共同改变和一侧满维不能被“可以区分”省掉：正交产品对在标准PSD中也有支持区分门，但其正交余项本身仍为块产品；局部相同的289.4例亦缺控制秩二；小支撑例仍不能支付满维传播。它们只反驳删除条件后这同一见证必给合格种子的推断。共同产品零集保留整个双份纯块，包括块内纠缠，不能缩成三条腿分别产品零测试；$\operatorname{ri}\mathcal C_{p,q}$ 也不能替换成任意一点，否则正效应在那一点为零不保证在其余共同零方向为零。

| 原对象或过程前件 | 在(298.7)后的量子结构 |
| --- | --- |
| 所有有限原锥、归一底、纯点与凸混合 | 同一 $\mathcal H_N=(\mathbb C^n)^{\otimes N}$ 上的全部密度矩阵、复射线及其混合 |
| 完整proper菜单、单位分解与原配对 | 全部PSD效应、数学POVM及PVM；Born概率 $\operatorname{Tr}(E\rho)$；全部目标的支持投影least |
| 原产品、重括号、正置换及丢弃 | 同一复张量积及偏迹 |
| 分支对每个有限相关旁观输入保正，另给全输入及合计分支质量预算 | CP／Kraus、TNI／TP及数学仪器；可用事件仍需实际供应 |
| 锐效应及整个yes支持中性；指定连续可逆保单位且全旁观保正的一参数群 | 分别给Lüders及数学酉动力学；物理钟、能量、$\hbar$、无限和近似极限仍需各自前件 |

简化的准确范围是：两点共同确认不再输入对其他门的普遍序比较，最后只输入两种实际混合准备的一次二元区分；共同零族、相对内部、源覆盖及完整背景仍承担真实约束，不宣称总量词、成本或独立逻辑信息减少。正文是条件数学纸证，非Lean核验；定义间约束没有把实际非空与物理供应变成无条件事实。

白话：固定第三颗珠子，让前两颗的整条纯准备纤维仍各有自己的最低门，低层的球和同一种联合准备的四处零把共同尺子交出来。随后挑两种有重叠、又在两块共同改变的产品准备，各取一半放成第一只混合准备；再把它们共同看不见的所有产品方向混合成第二只，混得足以代表整个共同零集合。现在只问：有没有同一只合法门，百分之百接住第一只、完全挡住第二只？不先要求它最低。若有，所有保持这两个读数的门形成一张真实饱和面，原紧菜单必能从中挑出一只不能再混合拆开的门。扣掉第一点已有的最低门，同一份正残余便被零方向和预算钉成纯三腿资源；两张交叠影子排掉镜像，一侧铺满的关系接上全部有限量子结构。最后所有共同最低门才作为结果长出来。几何从“整张门图怎样收紧”退到“两团实际准备能否被同一对平行支撑面分开”；这一下分开确实存在、整个概率表和时间过程的条件仍明说。$\square$

[Q298Wilce]: https://arxiv.org/abs/1206.2897v8 "Alexander Wilce, Conjugates, Filters and Quantum Mechanics, Appendix B.1：效应单位分解与完美可区分定义；不承担本章原饱和面非空、共同产品零接合或全有限重建。"

## 追加锚（本行以下为增补区）

## 299. 先锁刻度再定方向：三个大圆零不再另加非塌缩

**定义 299.1（只留原三零交面）。** 完整保留297.1的非平凡强全有限背景 $\mathsf F$：全部有限原锥、整个原归一底与纯域、完整正对偶及proper菜单、全部有限单位分解、正置换及其正逆、重括号、正丢弃，以及全部原相关输入上每个有限分块的min/max界。固定原实际三球 $B$，沿用297.1的 $\mathcal F_{BB}$ 和原三零面。对过球心的平面 $P$ 上三个互异单位方向 $a_1,a_2,a_3$，只要求

$$
\mathsf G_{3,B}(a_1,a_2,a_3):\quad
\mathcal D_B(a_1,a_2,a_3)\ne\varnothing.
\tag{299.1}
$$

$\mathsf G_{3,1}$ 指每张由两个不同原单体纯点生成的整个实际三球，都存在这样一组方向使(299.1)成立。它不要求 $k_B\ne h\otimes h$，不先支付整球反关联态。原交面非空仍是实际成员的存在条件，不以整个内禀最大张量锥中的正形式代替。

**定理 299.2（两种纯端点都支付整球半球刻度）。** 在完整 $\mathsf F$ 及原M1、M2中，固定实际三球满足(299.1)，则对每个单位 $a$，原单点least帽的整个球内限制为

$$
e_{\iota(a)}(\iota(x))=\frac{1+a\cdot x}{2}
\qquad(\|x\|\le1).
\tag{299.2}
$$

此结论不要求原 $\gamma_B>0$，也不声称此时已经取得 $\mathsf Z_B$。

证明。297.2先给原三零面的完整端点二分。选其中任一个端点 $r$；它是原 $K_2$ 纯点、两边缘恰为 $c_B$，在 $W_B\otimes W_B$ 的态和原帽限制分别为

$$
H=\operatorname{diag}(1,R),\qquad G=H/4,
\qquad
R=-I_3\quad\text{或}\quad R=-I_3+2nn^{\mathsf T}.
\tag{299.3}
$$

这里 $n$ 是297.1的单位法向，$RR^{\mathsf T}=I_3$。两种情形都是真实出现的端点才使用，不把另一端的内禀正性升级为原成员。

先重申所需的原零互易。任意同层原纯点 $s,t$ 若 $e_s(t)=0$，则原proper补门 $u-e_s$ 确认 $t$；leastness给 $e_t\le u-e_s$，在 $s$ 上评价得 $e_t(s)=0$。交换两点给反向。这只是既有M的补门论证，数值互易尚未用到。

任选单位 $a$，置 $b=-R^{\mathsf T}a$，$p_a=\iota(a)$、$p_b=\iota(b)$。它们是同一球的原纯点，产品也是原纯点。由(299.3)的原帽限制直接读出

$$
e_r(p_a\otimes p_b)
=\frac{1+a^{\mathsf T}Rb}{4}=0.
\tag{299.4}
$$

在原双份纯域使用上述零互易，再用279.2的原产品least因子化，得到

$$
0=e_{p_a\otimes p_b}(r)
=(e_{p_a}\otimes e_{p_b})(r).
\tag{299.5}
$$

279.3在尚未校准的球上已经给

$$
e_{p_a}(\iota(x))=1-\beta_a+\beta_a a\cdot x,
\qquad 0\le\beta_a\le\frac12,
\tag{299.6}
$$

并对 $b$ 给同式。把它们代入同一个原态 $r$：边缘向量为零，相关块为同一个 $R$，故

$$
\begin{aligned}
0&=(1-\beta_a)(1-\beta_b)
+\beta_a\beta_b a^{\mathsf T}Rb\\
&=1-\beta_a-\beta_b.
\end{aligned}
\tag{299.7}
$$

两项分别不超过 $1/2$，所以均等于 $1/2$。$a$ 任意，得(299.2)。证明使用的是原纯端点自己的原帽，以及两个原纯产品的原least；没有为任意内禀半球泛函另作原proper延伸，也没有调用 $t_B$ 或除以 $\gamma_B$。$\square$

**推论 299.3（三零逐球给低二层尺子，暂不选转置方向）。** 在完整 $\mathsf F$、原M1、M2及实际 $\mathrm{L2}_1$ 中，$\mathsf G_{3,1}$ 给整个单体数值互易 $e_p(q)=e_q(p)$。相对于278.2明列的M加数值互易Jordan桥、实际L2的复类型选择及276.2的M-only双份整锥供应，得到非空坐标集

$$
\mathcal R=\left\{(n,\theta,\varepsilon):
\begin{array}{l}
n\ge2,\quad \theta C_1=\operatorname{PSD}_n,\quad
u_1=\operatorname{Tr}\circ\theta,\\
\theta^{\otimes2}C_2=T_1^\varepsilon\operatorname{PSD}_{n^2},
\quad \varepsilon\in\{0,1\}
\end{array}\right\}.
\tag{299.8}
$$

$\theta$ 是同一实线性双射；完整原菜单、原配对和单位一并运输。此时仍允许 $\varepsilon=1$，不提前将原反射分支判为不可能。

证明。任意两个不同原纯点都位于它们生成的实际三球；299.2在该球的同一仿射坐标中使两向读数都为 $(1+a\cdot b)/2$。同点读数为一，因此全域数值互易成立。随后精确复用276.3首段及278.2的具名Jordan和复类型步骤，只在单体取得同一 $\theta$；再用原M2和276.2，得到(299.8)。不使用276.3里需要整个三份M的后续分类。

也可在此支付[XIX279.2][Q299Tail]的原 $\mathsf X_{T,2}$，而不是把它重新加进候选。确实，保迹正交坐标 $T_1^\varepsilon\theta^{\otimes2}$ 将整个原双份锥与逆对偶菜单一起送到标准PSD；其原least是秩一支持投影，原 $T_2(p,x)=e_p(x)$ 成为Born配对。对不同射线 $p,q$，在同一复二维张成中，若两者不正交，就选与 $p$ 正交的射线 $g$；若两者正交，就选二者的非平凡叠加 $g$。两次都保留 $\operatorname{span}\{p,q\}=\operatorname{span}\{p,g\}$，从而保留全部原共同零参照，同时翻转零比较。运输回同一原双份即为所需换点。部分转置始终是坐标运输，没有宣称它是未知高层原物理正操作。$\square$

**定义 299.4（不另列非塌缩的完整候选）。** 固定原 $b_*\in P_1$，对原 $a_0,a_1\in P_2,d\in P_1$，沿用297.5的同一 $p=a_0\otimes b_*$、$q=a_1\otimes d$ 和稀疏目标族

$$
\mathcal F_{b_*;p,q}
=\{\{a\otimes b_*\}:a\in P_2\}\cup\{\{p,q\}\}.
\tag{299.9}
$$

$\mathsf{Link}$ 精确沿用296.1：对每个已付 $S$、每只极端确认上门 $g$，其严格下方原极端门的可比图为空或连通；最低门仍保留，上门 $g$ 排除，每条路径有限而图不必有限。由296.2先内生提取同一least，再置原正差 $R_{\mathcal F}=e_{\{p,q\}}-e_{\{p\}}$。$\mathsf{Blind}(R)$ 要求三张普遍原准备零面

$$
Z_i(R)=\{x\in K_1:R(y_1\otimes y_2\otimes y_3)=0
\text{ 对所有其余两腿原 }y_j,\ y_i=x\}
\tag{299.10}
$$

各有 $Z_i(R)\subsetneq G_i\subsetneq K_1$ 的原面插入，并且至少一个 $Z_j(R)=\varnothing$。候选为

$$
\boxed{\quad
\mathsf Q_{3}(b_*)=
\mathrm{L2}_1+\mathsf G_{3,1}+
\exists a_0,a_1\in P_2\ \exists d\in P_1:
\mathsf{Link}(\mathcal F_{b_*;p,q})\land\mathsf{Blind}(R_{\mathcal F}).
\quad}
\tag{299.11}
$$

球门及三零面使用的原M1、M2，由同一候选后项的固定纤维下降取得；这规定了定义的依赖顺序，不另添加低层M公理。所有块内纠缠纯点、原混合门、完整有限菜单、任意相关输入及全部有限分块仍在域内。

**定理 299.5（方向由同一三腿余项支付，整族非塌缩成为后果）。** 在完整原 $\mathsf F$ 中，相对于299.3的具名Jordan／复类型／M-only供应、[XIX289.3、290.2—290.4、291—294][Q299Tail]的双HS／迹、同一Gram余项与两侧原max定向，以及XIII165.9第1项到第4项的整奇异线和全有限传播，(299.11)等价于存在同一 $n\ge2$ 和同一保单位实线性序同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\quad(N\ge0).
\tag{299.12}
$$

在这一完整候选中，每张球的 $\mathsf Z_B$、$\gamma_B=1/4$ 和 $k_B\ne h\otimes h$ 都为后果；没有将此结论外推为裸三零局部定理。

证明。（一）先在原序中选门。296.2给稀疏族的同一全部least，其中固定 $b_*$ 的所有单点纤维，按280.1原纯旁观限制下降M2、M1。于是299.1和299.2的所有球门已有定义和leastness。逐球用299.2，随后299.3给(299.8)及原 $\mathsf X_{T,2}$。这里只取得带未定 $\varepsilon$ 的低二层，不需预先给标准方向或任何 $\mathsf Z_B$。

（二）同一尾部定向。现在296.1的原 $\mathsf Q_{\rm link}(b_*)$ 已逐项支付，可直接用296.4。展开该既有应用，其原least、同一 $R_{\mathcal F}$ 和三张 $Z_i(R)$ 在整条接合中不变；XIX291.2把原盲面准确对应同一余项的正影子支持。XIX290.2在解扭坐标 $D_3=T_1^\varepsilon\theta^{\otimes3}C_3$ 中排退化，本来就允许(299.8)的两种低层方向。290.3给同一Gram余项的三个展平支撑；290.4接289.3，先以一侧完整原max排第三腿镜像，再以另一侧排低二层相对转置位。两侧测试作用于同一原余项，不拼接不同实现的最优值。回原同一 $\theta$ 后，才由XIII165.9接整奇异矩阵线和全部有限层，得(299.12)。原高层锥在这一步之前未假定PSD，未将坐标转置或辅助酉当成原设备。

（三）后果与反向。在(299.12)中，每张原二纯三球对应同一复二维支持，反对称秩一准备属于同一原双份，整球同向产品读数为零。故得 $\mathsf Z_B$，280.2给 $\gamma_B=1/4$ 和非塌缩。反向从(299.12)，同一反对称准备使任意大圆三个原零同时成立；全部所需least由支持投影给出，296.2反向给 $\mathsf{Link}$。三盲面取XIX290.4及293.3的同一标准源，遂给(299.11)。完整候选因此与297.16在同一剩余背景和供应下刻画相同模型类。$\square$

**命题 299.6（回溯的简洁性、局部边界与量子字典）。** 相对297.16，本候选明删 $\mathsf{NC}_1$，不新增读数或另一条局部筛选关系。新承重是299.2的端点帽零互易：反关联端点与反射端点都能校准同一球上的全部原单点门；方向交由完整候选原有三盲面尾部统一支付。这是利用既有联合约束消除一条显列前件，不声称完整候选严格弱化、独立假设最少或全球原创。

证明与范围。若先只看一张原球并暂不使用完整尾部，297.2仍留下反射单点 $\{r_2\}$；299.2仅证明它也校准全部半球。没有从裸 $\mathsf F+$M1/M2及单球三零证明 $\mathsf Z_B$，也没有构造该局部分支的完整全有限延伸或不可能性。299.5是在全体原二纯球三零、实际L2、同一稀疏 $\mathsf{Link}$ 和同一 $\mathsf{Blind}$ 一起成立时，才排除相对转置并得到整族非塌缩；不能把后果提前用作299.2的前提。原三零面的实际非空、实际球和全部具名供应仍明列，不被“内生”二字取消。

简洁几何是两阶段：大圆三接触经原纯端点帽预算，只剩两种正交相关端点；二者都把每个球方向配到一个实际纯产品零点，所以原帽零互易把所有刻度一次锁定。此时先不挑方向，再让同一三腿门差的三张盲面接到同一余项，使用两侧原联合约束择向。门序的下方可比图及其内生锥顶仍按296.2—296.3；不另输入格、复射线或矩阵乘法。

由(299.12)，原归一态、纯点和整个proper菜单分别成为全部密度矩阵、复射线和 $0\preceq E\preceq I$；所有原有限单位分解成为数学POVM，锐分解成为PVM，原配对成为 $\operatorname{Tr}(\rho E)$，原复合、置换、重括号与丢弃成为同一复张量、腿重排和偏迹。过程仍保留297.7及XIX289.5的独立条件：全部相关旁观保正支付CP／Kraus；全输入和合计分支质量预算支付TNI／TP及数学仪器；事件供应、锐效应及整个yes支持中性支付相应事件和Lüders；指定连续可逆、保单位且全相关保正群支付数学酉动力学。物理钟、能量、$\hbar$、无穷维和近似极限不由静态锥等式单独支付。

数值互易比较的是一次二元读数从哪端计算；它不要求两次仪器交换执行次序。这里的半球刻度仍建立在完整原仿射概率表、least及实际联合准备上，不从任意对称可比较关系直接推出量子论。原零互易、产品least、Jordan／复类型、M-only整锥及三盲面传播保持既有归属；本章repo-derived新增是原两种端点共同校准整球的桥，以及由此让原尾部承担方向选择、在完整候选中消去显列非塌缩的接合。全文为条件纸面理论，不声称Lean核验或物理实现。

白话：在球上画一条大圆，只挑三个不同方向，让同一种双份准备在这三处都不能左右同时说“是”，左右影子仍留在原球里。最低确认门的预算先把可能的纯端点压成两种：各向反着，或只有法向翻回来。先别急着删第二种；这两种端点的门都能给球上每一个方向找出一个实际的零搭档。零关系从哪端看都一样，便迫每个方向使用同一把半球尺子。尺子定好以后，再看原来就要求的同一三腿门差：它三条腿漏掉的准备能否按三盲面关系拼在一起。两侧联合测试这时排掉镜像，接回完整有限量子结构。因此不用再额外要求“相同准备配对”和“任意准备配对”的最低门不同，这件事在完整候选中成为后果。三个零单独能否做到这一点仍未解决；这轮删条件靠的是整体已有关系的配合，设备和时间仍各有前件。$\square$

[Q299Tail]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "279.2的原共同零参照换点；282.2及283.1的带相对转置位低二层坐标；289.3、290.2—290.4的同一余项及两侧原max排方向；291.1—291.3的三盲面；292.1—294.4的稀疏least及完整候选接合。"

## 追加锚（本行以下为增补区）

## 300. 两端各取一张零面：交叉混合直接给出区分对象

**定义 300.1（零面的内部准备交叉配对）。** 完整保留298.1—298.5的强全有限背景、固定 $b_*$ 的整个单点族Link、单体实际三球、同一实际双份态四个不共面零及球内边缘，以及全部具名低层、双HS／迹和XIII165.9供应。仍取原 $a_0,a_1\in P_2$、$b_0=b_*,b_1=d\in P_1$，令 $p=a_0\otimes b_0,q=a_1\otimes b_1,z=(p+q)/2$，并保留(298.3)的正比较、非独立性及原数据边缘覆盖。低层least已付，定义其原零面

$$
A_i=\{s\in K_2:e_{a_i}(s)=0\},\qquad
B_i=\{t\in K_1:e_{b_i}(t)=0\},\qquad i=0,1.
\tag{300.1}
$$

任取 $x_i\in\operatorname{ri}A_i,y_i\in\operatorname{ri}B_i$，置同一个原归一准备

$$
\zeta_\times=\frac12(x_0\otimes y_1+x_1\otimes y_0).
\tag{300.2}
$$

相对内部取各零面的仿射包；这些面非空由下述低层结构给出。新候选 $\mathsf Q_\times(b_*)$ 与(298.5)相同，只将最后的 $\zeta\in\operatorname{ri}\mathcal C_{p,q}$ 替为(300.2)，并要求同一原proper门 $f$ 满足 $f(z)=1,f(\zeta_\times)=0$。候选不再先生成共同产品零集或对其凸包取相对内部。

**定理 300.2（两次交叉补足全部共同产品零）。** 在300.1的相同前提下，四张零面非空，且对任意原正泛函 $f\in C_3^*$ 及任意上述内部准备的选择，

$$
f(\zeta_\times)=0
\quad\Longleftrightarrow\quad
f(s\otimes t)=0\quad\bigl(s\otimes t\in\mathcal Z_{p,q}^{\rm prod}\bigr).
\tag{300.3}
$$

因而这个零读数与内部准备的具体选择无关；它不是将(300.2)未经证明地宣称为 $\operatorname{ri}\mathcal C_{p,q}$ 的一个点。

证明。低层已在同一个 $\theta$ 下成为完整PSD；$A_i$ 是 $a_i$ 的射线正交补上的整个密度体，$B_i$ 同理。双份复尺寸 $n^2\ge4$、单份尺寸 $n\ge2$，故面均非空；其相对内部恰是相应支持上正定的归一矩阵。原 $\Delta(z)\ne0$ 由289.2给 $a_0\ne a_1,b_0\ne b_1$。两个不同射线的正交补张成整个局域Hilbert空间，所以

$$
\frac{x_0+x_1}{2}\in\operatorname{ri}K_2,
\qquad
\frac{y_0+y_1}{2}\in\operatorname{ri}K_1.
\tag{300.4}
$$

这里只使用已付低层的PSD支持面；没有对原三份锥假设PSD。式(300.2)由原产品与凸混合取得，且每个分量可有限分解为 $A_0\otimes B_1$ 或 $A_1\otimes B_0$ 的原纯产品点，故都在共同产品零凸包中，反向直接成立。

正向，正性使两项 $f(x_0\otimes y_1),f(x_1\otimes y_0)$ 均为零。固定 $y_1$，原正切片 $s\mapsto f(s\otimes y_1)$ 在 $\operatorname{ri}A_0$ 的一点为零，298.2的正段论证使其在整个 $A_0$ 为零；再固定 $s\in A_0$，对 $y_1\in\operatorname{ri}B_1$ 使用同一论证，得到 $f(A_0\otimes B_1)=0$。另一交叉块同理。

任取(298.2)的纯共同产品零 $s\otimes t$。两条乘积为零共有四种析取情形。若 $s\in A_0,t\in B_1$ 或 $s\in A_1,t\in B_0$，已经为零。若 $s\in A_0\cap A_1$，其正切片在 $B_0,B_1$ 都为零，因而在(300.4)的内部平均为零，正段论证使它在整个 $K_1$ 为零。若 $t\in B_0\cap B_1$，交换两块，用 $K_2$ 的内部平均同理。四种情形穷尽，得到(300.3)。整个证明始终用同一个原 $f$，不把分别可达的零读数拼起来。$\square$

**定理 300.3（交叉零面候选完整发展同一有限量子理论）。** 在298.1的完整背景和供应下，$\mathsf Q_\times(b_*)$ 与(298.5)等价，故当且仅当同一个 $n\ge2,\theta$ 对所有有限 $N\ge0$ 满足

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{300.5}
$$

证明。300.2与298.2将两种最后零读数逐原源、逐同一 $f$ 等价，确认 $f(z)=1$ 未改，其余前件相同；直接应用298.3。给定候选中某组内部准备通过，所有其他组也由定理300.2的(300.3)通过。选取极端饱和门、首点least的正减法、单边Gram、双预算、同一实际残余、两侧原max定向及XIII165.9均不重证。标准PSD反向仍取298.3的同一源，$P_{\operatorname{span}\{v,w\}}$ 在两个交叉零块全零，因此给任意(300.2)的区分门。

这个等价保持同一源和区分效应，不只保持闭合存在量词后的模型类；但没有要求两种混合准备数值相等，也未证明原整个确认纤维在重建前有least。最小门仍由整锥重建回读。$\square$

**命题 300.4（反事实、量子字典与完整白话）。** 新的几何只用四张原零面，两次交叉产品和一次平均；它删去候选中对全部共同产品零的显式遍历及其凸包相对内部选择，保留每张局域零面内部的真实覆盖。相对内部不能换成任意边界点，也不能只保留一次交叉。

证明与边界。低层PSD中，相对内部准备的核正是已知纯射线，所以不同源的两张零面内部准备之和严格正；若任取边界准备，两者可以仍有共同核，(300.4)就不成立。具体在标准 $n=2$ 中取 $a_0=P_{00},a_1=P_{(00+11)/\sqrt2},b_0=P_0,b_1=P_+$。数据两边缘的平均都是 $\operatorname{diag}(3/4,1/4)$，源仍满足(298.3)。若违规取 $x_0=x_1=P_{01}$，而 $y_0=P_1,y_1=P_-$ 仍是各自零面的内部准备，则 $f=P_{\operatorname{span}\{00,11\}}\otimes I_2$ 确认 $p,q$ 并挡住这只边界交叉混合，却在共同产品零 $P_{11}\otimes P_-$ 取一。(300.3)因此不能如此推广。若只留一次交叉，在相同源取 $f'=I_8-(I_4-P_{00})\otimes P_-$，它仍proper、确认 $p,q$ 且在整个 $A_0\otimes B_1$ 为零，却在另一交叉共同零 $P_{(00-11)/\sqrt2}\otimes P_1$ 取 $3/4$。两个例子否定删条件后的同一 $f$ 零读数等价；它们都是量子模型，不是完整强前件的非量子反模型。两端不同由原非独立性支付，未从“取补面”自动取得。

由(300.5)，原归一态、纯点、完整效应、单位分解和配对仍给密度矩阵、复射线、全部数学POVM及PVM和Born迹概率；原产品、重排、丢弃给复张量与偏迹。CP／Kraus、TNI／TP、仪器、事件供应、Lüders及数学酉动力学，分别保留298.5所列的全相关旁观保正、全输入和合计预算、锐效应与整个yes支持中性、指定连续群等前件；物理钟、能量、$\hbar$、无限和近似极限仍独立。证明中新接合是(300.3)：两个局域内部零面的交叉配对，在同一个原正泛函下补足全部共同产品零；相对内部正段性质、PSD支持面和核的交关系是成熟中间工具。正效应由一个生成态向其整面传播饱和读数的成熟论证见[Q300CDP]Lemma19；同一二结果效应区分两集合的定义见[Q300JP]Definition4。这些结果不供应此处两个交叉块补足其余共同零的接合，不替代指定原区分门非空；298的重建不另计新成果。简化不申领独立公理最少、严格弱化、成本下降、全球原创或原非空自动内生；正文是条件纸证，非Lean核验。

白话：两种产品准备，先各看它的前两颗珠子能完全漏掉什么、第三颗珠子能完全漏掉什么。四张零面各取一只内部混合，保证没有漏掉那张面里任何可被正门看见的方向。再交叉搭配：第一种准备的数据零面配第二种的旁观零面，第二种的数据零面配第一种的旁观零面，两份平均成另一只实际准备。最后仍只问，同一扇门能否完全接住原来两种准备的平均，又完全挡住这只交叉混合。若能，正性会把这两个交叉零补成全部共同产品零，不必先把所有零方向列出来。后面的极端门、同一纯三腿余项和全部有限量子结构沿已证链长出。少掉的是整族共同零的遍历；四张零面的内部覆盖、实际区分存在和完整背景仍明说。$\square$

[Q300CDP]: https://arxiv.org/abs/1011.6451v3 "Chiribella、D’Ariano、Perinotti，Informational derivation of Quantum Theory，Lemma19：正效应的零／最大读数在生成面的传播；不借其重建前件供应本章指定区分关系。"
[Q300JP]: https://arxiv.org/abs/1703.09447v1 "Jenčová、Plávala，Conditions on the existence of maximally incompatible two-outcome measurements in General Probabilistic Theory，§VI Definition4：同一二结果效应在两个集合分别恒为零、一；不供应指定集合的区分门存在。"

## 追加锚（本行以下为增补区）

## 301. 三处接触与两次交叉：刻度先定，方向交给同一余项

**定义 301.1（三零与交叉区分的同一候选）。** 保留298.1的完整强全有限背景 $\mathsf F$、全部原准备与纯域、完整正对偶、proper菜单和有限单位分解、实际产品、正置换及逆、重括号、丢弃，以及全部有限分块在所有相关输入上的min/max。固定 $b_*\in P_1$，仅对(298.1)的单点族要求296.1的 $\mathsf{Link}$；它先给固定纤维least及完整M2、M1。低层入口改用单体实际 $\mathrm{L2}_1$ 和299.1的 $\mathsf G_{3,1}$：每张实际二纯三球上，存在同一实际双份准备及球内两张边缘，使某个大圆的三个互异方向同时给同向产品零。保留299.3的具名互易Jordan、复类型及M-only整锥供应，不另要求 $\mathsf{NC}_1$ 或四个不共面零。

沿用298.1的原 $p=a_0\otimes b_*,q=a_1\otimes d,z=(p+q)/2$、原非独立差 $\Delta(z)$ 和同一数据边缘覆盖 $\mathsf{Cov}(a_0,a_1)$，保留

$$
e_p(q)>0,\qquad \Delta(z)\ne0,\qquad \mathsf{Cov}(a_0,a_1).
\tag{301.1}
$$

以已得低层least定义300.1的四张原零面 $A_i,B_i$，取 $x_i\in\operatorname{ri}A_i,y_i\in\operatorname{ri}B_i$，令 $\zeta_\times=(x_0\otimes y_1+x_1\otimes y_0)/2$。要求两只实际混合由同一原单位分解完美区分：

$$
\boxed{\quad
\mathsf Q_{3\times}(b_*):=
\mathsf{Link}(\mathcal F^1_{b_*})+\mathrm{L2}_1+\mathsf G_{3,1}
+\exists a_0,a_1,d,x_0,x_1,y_0,y_1:\
(301.1)\ \land\ z\perp_{\mathcal E_3}\zeta_\times.
\quad}
\tag{301.2}
$$

存在量词中的内部点必须在上述对应零面内；$z\perp\zeta_\times$ 仍准确指存在同一原proper $f$ 满足 $f(z)=1,f(\zeta_\times)=0$。双HS／迹、单边Gram和XIII165.9的全部有限传播供应保留。候选没有所选两点共同least或原三盲面条件；非空区分仍是输入。

**定理 301.2（交叉零压缩不必先定低二层方向）。** 在301.1的相同背景和具名低层供应下，299.2—299.3先给同一 $\theta$ 及某个 $\varepsilon\in\{0,1\}$，使

$$
\theta C_1=\operatorname{PSD}_n,\qquad
\theta^{\otimes2}C_2=T_1^\varepsilon\operatorname{PSD}_{n^2},\qquad n\ge2.
\tag{301.3}
$$

即使此时 $\varepsilon$ 未定，300.2的同一正泛函零读数等价仍成立；若(301.2)的区分关系成立，可取得同一原纯准备，其在原 $\theta$ 坐标经第三腿辅助酉后的表达为

$$
\widehat x=T_1^\varepsilon T_3^\delta\widehat\Gamma
\in\widehat{\mathcal C}_3,\qquad \delta\in\{0,1\},
\tag{301.4}
$$

其中 $\Gamma=P_{(I-P_v)w}$、$v=a\otimes b,w=a'\otimes d'$ 表示同一原源，$P_{(I-P_v)w}$ 表示非零向量的归一dyad。生成 $\Gamma$ 的向量之三腿展平秩为 $(n,r,2)$ 或 $(r,n,2)$，$2\le r\le n$；尚未定向的 $\widehat x$ 不在此被认作普通PSD的dyad。第三腿辅助酉只运输同一对象、锥与整个菜单，不宣称是未知原锥的控制。

证明。固定纤维先下降M2、M1，故299.2的纯端点帽零互易已经可用；它对实际三零面的反关联端点与反射端点同样给完整半球刻度，不消费 $\gamma_B>0$。299.3随后给(301.3)，并给原双份比较与Born配对的对应；没有预先选择 $\varepsilon=0$。

置 $\mathcal C_3=\theta^{\otimes3}C_3$，仅在局部证明中用 $S_2=T_1^\varepsilon$、$S_3=T_1^\varepsilon$，后者作用于三腿的第一腿。$S_2$ 将整个双份块及其完整菜单送到标准PSD，单体块不变；$S_3\mathcal C_3$ 在 $(12)|3$ 上仍夹于标准Sep与BP之间。原效应按逆对偶同时运输；这些部分转置保迹、保HS且自伴随，因此迹配对与原序完整保留。没有断言 $S_3$ 是原正操作或新全有限一致坐标。

四张原零面在 $S_2$ 与单体坐标下，正是四个已知射线正交补的密度面；相对内部、正切片、实际产品和凸混合都随这些序同构运输。289.2的乘法桥在(301.3)的两种方向均成立，(301.1)遂给两局域重叠严格介于零和一。300.2证明的两个交叉块、两端内部平均和四种零析取因而逐项适用，保持同一原 $f$，没有先使用三份PSD。故它在 $\zeta_\times$ 的一个零读数准确给全部共同产品零。

满足确认与零读数的原proper效应组成整个菜单的非空暴露面；取其极点 $h$。在原序中，首点least给 $D=h-e_p\ge0$，298.2的单边减法给 $D$ 极端proper。运输到 $S_3\mathcal C_3$ 后，首门是 $P_v$；共同产品零给支持消去和Gram稀疏形所需四零。298.2从此处到(298.6)的局部证明只消费该 $(12)|3$ 的Sep/BP、首门least、同一极端 $h$、两确认及双HS／迹，故在这个运输锥逐项成立：原迹 $\operatorname{Tr}h=2$、$\operatorname{Tr}D=1$，同一 $D$ 成为原纯准备且HS范数一，两个Gram端点中必取一个。此处应用的是298.2的局部接合，不将整个运输锥冒充其标准全有限前件。

只按287.2（二）用第三腿酉将 $b,d'$ 同时变实，两个端点在解扭坐标中恰为 $\widehat\Gamma$ 与 $T_3\widehat\Gamma$；运输回原方向给(301.4)。288.7—288.9在两种 $\varepsilon$ 下均把同一原数据平均边缘的支撑对应到同一余项；转置不改变正定性或秩。(301.1)因此给上述三秩，允许整个控制矩阵线奇异。$\square$

**定理 301.3（三零交叉候选重建全部有限量子结构）。** 在301.1具名的完整背景与供应下，(301.2)当且仅当存在同一 $n\ge2$ 和保单位实线性序同构 $\theta$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{301.5}
$$

证明。301.2先给同一 $\widehat x$。原两个交叠分块的完整max条件，准确沿287.10，在同一辅助坐标给

$$
T_1^\varepsilon\widehat x\in\operatorname{BP}_{2|(13)},\qquad
T_2^\varepsilon\widehat x\in\operatorname{BP}_{1|(23)}.
\tag{301.6}
$$

第三腿辅助酉在每个分块中都只作用于已知双份PSD块的内部，故不需未知运输锥置换不变。301.2的三秩均至少二；288.2（三）的条件切片和负部分转置谱给同一 $\widehat\Gamma$ 两侧的负方向。第一式代入(301.4)即测试 $T_3^\delta\widehat\Gamma$，迫 $\delta=0$。第二式于是测试 $(T_1T_2)^\varepsilon\widehat\Gamma$；全转置保持BP，且 $T_1T_2=\mathsf T T_3$，迫 $\varepsilon=0$。两次都作用于同一原余项，不拼接不同态或不同最优值。

现在回原同一个 $\theta$，低二层已标准且 $\Gamma\in\mathcal C_3$。一侧满支撑和控制秩二准确支付XIII165.9的原dyad入口；其第1项到第4项给(301.5)，原杯帽、全部相关旁观输入、整奇异矩阵线及严格正成功质量均保留。原所选两点和其他目标的共同least此后由支持投影回读。

反向，在标准PSD模型仍取298.3的 $a_0=P_{|I_n\rangle\!\rangle/\sqrt n},a_1=P_{|E_{00}\rangle\!\rangle}$，令 $d=P_{(b+e)/\sqrt2}$、$e\perp b$。原正比较为 $1/(2n)$，非独立差非零，平均两张数据边缘均正定。支持投影 $P_{\operatorname{span}\{v,w\}}$ 确认 $z$ 并在两交叉零块全零，故给全部合法内部准备的区分。支持投影least给固定纤维Link；每张二维支持中的反对称准备给同一大圆任意三个同向零和球内边缘，实际L2成立。故(301.2)成立。$\square$

**命题 301.4（简洁几何、反事实和完整量子字典）。** 相对300.1，本候选把低层四个不共面同向零改为一条大圆上的三个互异零，不另加非塌缩；交叉零面的两次产品和一次二元区分不变。方向在同一高层余项的两个原联合约束中才确定。

证明与边界。299.2支付的是两种纯端点共同校准刻度，不是裸三零直接排反射。因此若在(301.3)便写 $\varepsilon=0$，本证明会循环；(301.4)—(301.6)明确承担尚欠的方向。删除交叠max，局部Gram仍留下镜像；删除局域内部覆盖或一次交叉，300.4的标准量子反例仍适用。删除实际区分非空，零门或单位门各只能满足一端读数，紧性没有把两者合为同一门。固定纤维Link、实际三球和三零面存在、Jordan／复类型／M-only、源一般位置和数据边缘覆盖、双预算及传播仍为明列前件，不能由定义消除。

由(301.5)，完整原归一底、纯点、proper菜单、单位分解和配对分别给全部密度矩阵、复射线、PSD效应、数学POVM／PVM及Born迹概率；原产品、置换、重括号、丢弃给复张量和偏迹。CP／Kraus仍需所有有限相关旁观输入保正；TNI／TP和仪器仍需整个输入及合计质量预算；可用事件另需供应，Lüders另需锐效应和整个yes支持中性，数学酉动力学另需指定连续可逆保单位且全旁观保正群。物理钟、能量、$\hbar$、无限及近似极限各保留独立前件。

299.2—299.3的端点共同刻度、300.2的交叉补足、298.2的极端饱和面与单边残余、288的同一支撑及两侧定向和XIII165.9传播均保留原归属。本章repo-derived新接合是在低二层转置位尚未选定时运输整个交叉零面区分，产生同一原极端余项，再让它同时支付两位方向；既删四零入口的一个读数，也不恢复所选pairleast或非塌缩输入。不申领最少独立公理、严格弱化、成本下降或全球原创；这是保留具名条件的纸面理论，不是Lean核验。

白话：球上只留一条大圆的三个接触。它们先把每个方向的刻度锁成同一把尺，允许尺子暂时有正反两种方向，不急着挑。随后还是取两种有重叠、两端共同改变且数据影子铺得够开的产品准备；把它们各自漏掉的两端零面交叉搭配，平均成另一只实际准备。问同一扇门能否总接住原中点、完全挡住交叉混合。若能，原菜单里一张饱和面会给出极端门；扣去首点已有最低门，得到同一份纯三腿余项。它同时受两张交叠联合影子的正性约束，任何残留镜像都会在其中读出负数，于是两种方向一起锁定，接上全部有限量子结构。少掉一个球上零读数，也没有把共同最低门塞回来；这只区分门确实存在和整套供应仍须明说。$\square$

## 追加锚（本行以下为增补区）

## 302. 只留固定单点族：跨分割正交补全自行长出区分门

**定义 302.1（三零与固定纤维的候选）。** 保留301.1的完整强全有限背景 $\mathsf F$：整个有限维原载体及每个有限份数的闭尖生成锥、严格正乘积单位、整个归一底与纯域、完整正对偶及proper区间、全部有限单位分解、实际产品、正置换及逆、规范重括号、正丢弃和全部相关输入上每个有限分块的min/max。固定 $b_*\in P_1$，只要求

$$
\boxed{\quad
\mathsf Q_0(b_*)=
\mathsf{Link}(\mathcal F^1_{b_*})+\mathrm{L2}_1+\mathsf G_{3,1}.
\quad}
\tag{302.1}
$$

$\mathcal F^1_{b_*}$、$\mathsf{Link}$ 和实际三零关系精确沿298.1、296.1和299.1；仍保留299.3的具名互易Jordan、复类型及M-only整锥、双HS／迹与XIII165.9传播供应。没有所选非正交产品对、$\Delta$、$\mathsf{Cov}$、交叉零面内部选择或完美区分存在条件。固定纤维先内生给原least，再下降M2、M1，299.2—299.3给同一 $\theta$ 和某个 $\varepsilon\in\{0,1\}$：

$$
\theta C_1=\operatorname{PSD}_n,\qquad
\theta^{\otimes2}C_2=T_1^\varepsilon\operatorname{PSD}_{n^2},\qquad n\ge2.
\tag{302.2}
$$

以下证明运输整个原态、菜单、配对及单位到同一 $\theta$，写 $u_N=\operatorname{Tr}$，$P_v=vv^*/\|v\|^2$。未定向时不预付高层PSD或普通Bell杯。

**定理 302.2（两种二层方向都给一体运输和二可分单点门）。** 在(302.2)的任一方向，任意一体合同 $\operatorname{Ad}_H$ 在全部有限原旁观者上正；酉合同及其逆是原保单位序自同构。固定纤维least因此给每个二可分原纯点的全原单点least；在 $ij|k$ 分割，该点与其least的同一迹密度为

$$
X=T_i^\varepsilon P_{a\otimes c},\qquad
a\in\mathbb C^n\otimes\mathbb C^n,\quad c\in\mathbb C^n,
\tag{302.3}
$$

其中 $T_i$ 只转置该双份块的一腿，第三腿保持；交换双份块两腿不改变所得整族。

证明。标准方向用XIII165.3。转置方向另证，不能引用该引理的标准前件。令 $\Omega=\sum_{ij}E_{ij}\otimes E_{ij}$，$F=T_1\Omega=\sum_{ij}E_{ij}\otimes E_{ji}$。原 $C_2=T_1\operatorname{PSD}$，其完整迹对偶也是自身，故 $F/n$ 是原归一杯及proper帽：$T_1(I-F/n)=I-\Omega/n\succeq0$。对任意 $H$，

$$
J_H=(\mathrm{id}\otimes\operatorname{Ad}_H)F
=\sum_{ij}E_{ij}\otimes HE_{ji}H^*\in C_2.
\tag{302.4}
$$

这个成员关系直接由 $T_1J_H=(\mathrm{id}\otimes\operatorname{Ad}_H)\Omega\succeq0$ 给出，不先调用原 $\operatorname{Ad}_H$ 正性。对原输入及任意相关旁观者，先用原min张量 $J_H$，再以原帽 $F/n$ 收缩输入和参考腿，原max及闭锥双极性保证整块切片为正。矩阵单位在简单张量上给

$$
(\operatorname{Tr}_{12}\otimes\mathrm{id})
\bigl[(F_{12}\otimes I)(x_1\otimes J_{H,23})\bigr]
=\sum_{ij}\operatorname{Tr}(xE_{ij})HE_{ji}H^*=HxH^*.
\tag{302.5}
$$

归一杯帽只添严格正尺度；实张量张成将等式推广到同一任意原相关输入，所以得到全部旁观正性。酉和逆均可用，且保迹。一般合同的数学不增质量预算可在 $H^*H\preceq I$ 时由单体正差与旁观单位的原max给出；未将它们宣称为设备事件。

在固定纤维中，$X$ 与 $I-X$ 都是原proper，$\|X\|_2=\operatorname{Tr}X=1$。设其least为 $e$，则 $e\le X$；双HS／迹给 $1=\operatorname{Tr}(eX)\le\|e\|_2\le\operatorname{Tr}e\le1$，故 $e=X$。一体酉运输孤立腿的固定 $b_*$ 至任意纯 $c$，原置换及逆运输任意分割，同时运输全确认纤维及原序，得(302.3)。不要求任意双体酉是未知高层的原对称。$\square$

**定理 302.3（跨三分割的七点补全排除转置方向）。** 在302.1的相同条件下，(302.2)必有 $\varepsilon=0$。

证明。先复用298.2的两条局部事实。若原proper区间极点 $H$ 确认已知least为 $X$ 的原点，则 $H-X$ 正且仍为整个区间极点：对其proper平均分解，零读数使两个补效应都确认该点，leastness使加回 $X$ 的两项proper，再用 $H$ 极端。若一个非零极端proper效应迹一，整个原归一底上的最大读数必为一，否则可与零门作非平凡凸分解；双HS／迹等号链使它同时为同一原纯准备、HS范数一。这些事实不预付普通PSD。

在实坐标二维角取

$$
\begin{aligned}
w&=(100+010+001)/\sqrt3,\\
u_1&=(000+010-001)/\sqrt3,\quad
u_2=(000-100+001)/\sqrt3,\quad
u_3=(000+100-010)/\sqrt3,\\
u_4&=011,\quad u_5=101,\quad u_6=110,\quad u_7=111.
\end{aligned}
\tag{302.6}
$$

字符串表示计算基向量；$w,u_1,u_2,u_3$ 在 $000,100,010,001$ 基中的未归一行分别为 $(0,1,1,1),(1,0,1,-1),(1,-1,0,1),(1,1,-1,0)$，内积直接给正交单位基。$u_1,u_2,u_3$ 分别孤立第一、第二、第三腿，其余是全产品。若 $\varepsilon=1$，(302.3)支付同一原态和least

$$
X_1=T_2P_{u_1},\quad X_2=T_1P_{u_2},\quad X_3=T_1P_{u_3},\quad
X_j=P_{u_j}\ (4\le j\le7).
\tag{302.7}
$$

对 $n>2$，再加入二维角外全部计算基投影；它们也是二可分单点门。前三个孤立腿都为实 $0$，矩阵单位展开给 $\operatorname{Tr}(X_iX_j)=\delta_{ij}$：交叉比较可先压到两条孤立腿的 $0$，其余为(302.6)同一零内积；后三个及角外基点直接由对角支撑读出。每只 $X_i$ 迹一、HS范数一。

单位门极端；按此原零表逐个扣除 $n^3-1$ 只单点least，当前余门仍确认下一点，故每一步保正且极端。最终原极端proper迹一门 $D=I-\sum X_i$，由上述双预算事实同时属于 $C_3$。其矩阵恰为

$$
D=\frac13\bigl(P_{100}+P_{010}+P_{001}
+|000\rangle\langle011+101+110|
+|011+101+110\rangle\langle000|\bigr).
\tag{302.8}
$$

但取 $a=(0+i1)/\sqrt2$、$\eta=(00+i01-i10)/\sqrt3$，则 $E=P_a\otimes T_2P_\eta$ 是原 $1|(23)$ 产品proper效应。原max要求 $\operatorname{Tr}(DE)\ge0$，而同一迹配对给

$$
\operatorname{Tr}(DE)=\langle a\otimes\eta,T_2D(a\otimes\eta)\rangle
=\frac16-\frac19-\frac19-\frac19=-\frac16.
\tag{302.9}
$$

三项负数分别来自 $T_2D$ 的 $010\leftrightarrow001$、$000\leftrightarrow101$、$010\leftrightarrow100$。这是原态与原proper效应的负读数，矛盾。故 $\varepsilon=0$；没有把不同分割的部分转置当成同一全局操作。$\square$

**定理 302.4（两次单点减法逐维长出满支撑种子）。** 在302.1的背景下，标准方向的固定单点族足以给同一全部有限原锥 $C_N=\operatorname{PSD}_{n^N}$；不消费301.1中的任何源对区分条件。

证明。现在302.2支付所有分割的二可分点 $P_s$ 的least。仍取(302.6)的七点及角外基点，直接用普通投影逐个从单位扣除；同一极端减法得 $P_w$ 为原迹一极端proper，同时为原纯准备。此时才得到 $W$，不是将一个普通GME向量预置为原态。

令 $S_k=\operatorname{span}\{0,\ldots,k-1\}$、$\Pi_{k,N}=\operatorname{Ad}_{P_{S_k}}^{\otimes N}$。XIII166.5的完整角继承和proper延拓已由302.2的一体合同支付：$D_N^{(k)}=C_N\cap\operatorname{Herm}(S_k^{\otimes N})=\Pi_{k,N}(C_N)$，形成尺寸 $k$ 的完整全有限模型；每只角内proper $f$ 由 $f\circ\Pi_{k,N}$ 延为原proper。包含整个内在对偶，不是只保留受限测试。$w$ 的三展平秩均二，在完整二维角准确用XIII165.9得 $D_N^{(2)}=\operatorname{PSD}_{2^N}$，对所有有限 $N$ 成立。

设完整 $k$ 角已支付，$2\le k<n$。固定XIII165的向量化 $|A\rangle\!\rangle=\sum_i|i\rangle_{\rm r}\otimes A|i\rangle_{\rm o}$，在原 $n\times n$ 矩阵中置

$$
\begin{aligned}
I_k&=\sum_{i<k}E_{ii},\qquad
\psi_k=|I_k\rangle\!\rangle|0\rangle+|E_{00}\rangle\!\rangle|1\rangle,\\
R_k&=kE_{00}+E_{0k},\quad Q_k=R_k-I_k,\quad
q_k=|Q_k\rangle\!\rangle|0\rangle,\quad u_k=\psi_k+q_k,\\
a_k&=\|\psi_k\|^2=k+1,\qquad b_k=\|q_k\|^2=k^2-k+1.
\end{aligned}
\tag{302.10}
$$

$P_{\psi_k}$ 是已完成角中的原态；角内效应零延拓使同一矩阵也是原proper。双预算使这种迹一原态／proper矩阵为整个原区间极点：若 $P_{\psi_k}=(F+G)/2$，在自身原态上评价，两项饱和及双HS／迹迫 $F=G=P_{\psi_k}$。未将角内极端性冒作全原极端性。

直接有 $\langle\psi_k,q_k\rangle=\operatorname{Tr}(I_kQ_k)=0$。$q_k$ 固定控制腿，$u_k=|R_k\rangle\!\rangle|0\rangle+|E_{00}\rangle\!\rangle|1\rangle$ 固定输出腿为 $0$，二者在不同割二可分，单点least均已付。极端 $I-P_{\psi_k}$ 确认 $P_{q_k}$；扣去其least再取补，得到原极端proper $H=P_{\psi_k}+P_{q_k}$，不是事先输入二点共同least。$H$ 确认 $P_{u_k}$，第二次扣去其单点least，得到

$$
H-P_{u_k}=P_{v_k},\qquad v_k=b_k\psi_k-a_kq_k,
\quad \langle u_k,v_k\rangle=0,\quad
\|v_k\|^2=a_kb_k(a_k+b_k)>0.
\tag{302.11}
$$

这是迹一原极端proper，故同一 $P_{v_k}\in C_3$。它的两个控制切片为

$$
A_k=(k^2+2)I_k-(k+1)(kE_{00}+E_{0k}),\qquad
B_k=(k^2-k+1)E_{00}.
\tag{302.12}
$$

$A_k$ 第零行为 $(2-k)e_0^{\mathsf T}-(k+1)e_k^{\mathsf T}$，其余 $i=1,\ldots,k-1$ 行为 $(k^2+2)e_i^{\mathsf T}$。像之和维数 $k$；$B_k$ 的非零第零行与 $A_k$ 的该行共同给新增 $e_k^{\mathsf T}$，叠矩阵秩 $k+1$。两切片独立，故生成向量的三秩准确为 $(k+1,k,2)$；$k=2$ 的 $2-k=0$ 不影响该结论。

全部支持在 $S_{k+1}^{\otimes3}$，交换两条数据腿后给完整 $k+1$ 角的一侧满支撑二元种子。XIII165.9现在对该完整角给全部有限 $D_N^{(k+1)}=\operatorname{PSD}_{(k+1)^N}$。有限局域维数归纳 $2\to3\to\cdots\to n$ 完成；每步先支付全部有限份数，再进入下一局域维数，不把有限前缀补全冒作全有限结论。$\square$

**定理 302.5（删去末尾存在性的完整量子候选）。** 在302.1明列背景和供应下，对每个原 $b_*$，(302.1)当且仅当存在同一保单位实线性序同构 $\theta$ 及 $n\ge2$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{302.13}
$$

301.1的合格源对、其交叉零面混合与同一原区分门、全部共同least和非塌缩均成为后果。

证明。正向由302.2—302.4。反向标准PSD支持投影least给固定纤维Link，每张二维支持的反对称准备给大圆三零和球内双边缘，实际L2成立。重建后取298.3的 $a_0=P_{|I_n\rangle\!\rangle/\sqrt n},a_1=P_{|E_{00}\rangle\!\rangle},d=P_{(b+e)/\sqrt2}$，$e\perp b$；同一原产品中点的比较为 $1/(2n)$、非独立差非零，两个数据平均边缘均为 $(I_n/n+E_{00})/2\succ0$。现在才用原支持投影 $f=P_{\operatorname{span}\{v,w\}}$，它确认 $z$ 并挡住任意合法交叉混合。区分门非空由此前不消费它的原序构造支付，不循环。$\square$

**命题 302.6（更大结构、反事实与量子字典）。** 相比301.2，本候选删除整个末尾源对存在条件；几何只留固定单点族和每张球上的三处接触，其他非正交共同门从跨分割的原零关系组合长出。

证明与范围。新增接合不是把单点least改名为全部M：正交族逐点扣除是成熟的既有剥离步骤；这里它先用于跨三个分割的七点，在未定方向时产生(302.8)的同一原矩阵并由复相位读数排转置。标准方向中，七点留下原 $W$，随后两次不同分割的单点least减法和完整角维数归纳产生 $(k+1,k,2)$ 原种子，才使非正交源区分存在成为后果。所有least比较都针对整个原菜单，后续角使用全部内在对偶及proper原延拓，不能缩为局部测试。

跨割是实质条件。若被扣除的整组向量都在同一个双块割为产品，且普通补投影秩一，则该补投影经该割部分转置仍正：部分共轭的正交产品族仍正交。纯态的PPT判据遂使补向量仍在该割为产品；这种单割补全不能制造跨该割纠缠的纯余项。(302.9)还消费实际复相位，不能只检实向量。若不保留一体全旁观运输、全菜单极端性或完整角延拓，对固定纤维扩域、逐次减法及维数归纳各出现具体未付接口；本证明已由302.2、双预算和XIII166.5支付，不将它们省成定义。

原零面传播、极端减法和迹一等号链保留298及276的归属；完整角和传播保留XIII165—166。跨割二可分正交集与其纠缠补空间在成熟量子文献中已有研究，例如[Q302UBB]给三比特五态UBB及三维GME补空间；它处于已给量子Hilbert模型，不供应未知原层级的least或本章升维。这里不单列七点线性代数或PPT为新理论。repo-derived新承重是(302.7)—(302.12)的全原序接合、方向反证与两次减法逐维传播；不主张全球原创、最少独立公理、严格逻辑弱化或无前提内生。

由(302.13)，原全部归一态、纯点、完整proper效应、有限单位分解及配对给密度矩阵、复射线、全部数学POVM／PVM和Born迹概率；实际产品、置换、重括号、丢弃给同一复张量和偏迹。CP／Kraus仍需全有限相关旁观保正，TNI／TP和仪器仍需全输入和合计预算，可用事件另需供应，Lüders另需锐效应及整个yes支持中性，数学酉动力学另需指定连续可逆保单位且全旁观保正群。物理钟、能量、$\hbar$、无限与近似极限仍各有独立条件。正文是条件纸面理论，不是Lean核验。

白话：固定一颗旁观者，让前两份所有纯准备在它旁边都有自己的最低门；球上仍只用三个接触把尺子交出来。接着把准备分割的方式换着看：七种互相漏读、但各自只在某一个分割上分开的准备，恰好占满一个小角里除一条方向外的地方。最低门允许在原序中逐只扣除；剩下那条方向必须也是原合法纯准备。若低层尺子取了镜像方向，同一份余项会让一个带复相位的合法联合门读出负数，于是镜像自行排除。正向尺子里，余项就是小角的W态。小角完成后，每次只拿两种有单点最低门的准备换一个方向，两次相减就多铺开一维；原传播关系把这个较大角全部完成，再往下一维走，有限次覆盖原空间。因此不必再另外要求那两只混合准备能被同一门分开，它们的区分门最后作为结果出现。固定单点族、实际三零和整套具名背景仍明说，没有把全部存在条件抹成空话。$\square$

[Q302UBB]: https://arxiv.org/abs/2604.06412v1 "Bera等，Strong nonlocality with more imaginarity and less entanglement，式(5)、Propositions1—2的五态三比特UBB和GME补空间；仅为跨割二可分正交几何的相关先例，不供应本章未知原层级的least或升维结论。"

## 追加锚（本行以下为增补区）

## 303. 不必挑哪只区分门：同一二元区分先迫出唯一门

**定义 303.1（只到三层的局部菜单与一只单点最低门）。** 本条直接给一个已选定的低层坐标，不再要求302.1的全有限背景、固定单点族Link、实际三零、Jordan／复类型／M-only或传播供应。取 $n\ge2$，载体为 $V_N=\operatorname{Herm}((\mathbb C^n)^{\otimes N})$，$N=1,2,3$，单位为迹，态—效应配对为 $\langle E,X\rangle=\operatorname{Tr}(EX)$；固定同一个 $\varepsilon\in\{0,1\}$，给

$$
C_1=\operatorname{PSD}_n,\qquad
C_2=T_1^\varepsilon\operatorname{PSD}_{n^2}.
\tag{303.1}
$$

$C_3$ 为闭尖生成锥、迹严格正，记 $K_j=\{X\in C_j:\operatorname{Tr}X=1\}$、$P_j=\operatorname{ext}K_j$，$j=1,2,3$。使用整个迹对偶 $C_3^*$、proper区间 $\mathcal E_3=[0,I]_{C_3^*}$；三个 $ij|k$ 分割对同一 $C_3$ 均有原 $C_2,C_1$ 的min/max，包含实际产品，保留正置换及正偏迹。双HS／迹预算精确指

$$
\|X\|_2\le\operatorname{Tr}X\quad(X\in C_3),
\qquad
\|E\|_2\le\operatorname{Tr}E\quad(E\in C_3^*).
\tag{303.2}
$$

不输入整个三份PSD、一体物理控制或第四层。取单位向量 $a,a'\in(\mathbb C^n)^{\otimes2}$、$b,d\in\mathbb C^n$，两个块内重叠的模都严格介于零和一，置 $a_0=T_1^\varepsilon P_a,a_1=T_1^\varepsilon P_{a'}$、$b_0=P_b,b_1=P_d$、$v=a\otimes b,w=a'\otimes d$、$p=a_0\otimes b_0,q=a_1\otimes b_1,z=(p+q)/2$。由min和(303.2)的严格凸取等，$p,q$ 都是原纯点。只要求 $p$ 在整个原菜单中有一只单点least $e_p$；不预给其矩阵、不要求 $q$ 或其他点有least。另要求同一 $m=(a_0+a_1)/2$ 的两张数据边缘非纯，即

$$
\mu_1=\operatorname{Tr}_2m\notin P_1,
\qquad \mu_2=\operatorname{Tr}_1m\notin P_1.
\tag{303.3}
$$

不要求边缘满维。定义原低层零面 $A_i=\{x\in K_2:\operatorname{Tr}(a_ix)=0\}$、$B_i=\{y\in K_1:\operatorname{Tr}(b_iy)=0\}$；这些是原实际态面，因为(303.1)的低层锥均迹自对偶。任选 $x_i\in\operatorname{ri}A_i,y_i\in\operatorname{ri}B_i$，置 $\zeta_\times=(x_0\otimes y_1+x_1\otimes y_0)/2$，定义

$$
\mathcal S_{p,q}
=\{f\in\mathcal E_3:f(z)=1,\ f(\zeta_\times)=0\}.
\tag{303.4}
$$

$\mathcal S_{p,q}\ne\varnothing$ 仍是同一实际二元区分的存在前件，不以紧凸性代付。定理将证明该面不依赖四个内部点。局部前件只把低层尺子作为已知接口，不宣称从一般对称二元关系得到(303.1)。

**定理 303.2（传播前的唯一门与每只区分门的同一纯差）。** 在定义303.1的条件下，若 $\mathcal S_{p,q}\ne\varnothing$，则它恰为单点 $\{h_{p,q}\}$；该门是整个原proper区间的极点，$h_{p,q}-e_p$ 对应同一实际原纯准备。低二层方向已由同一余项定向，不必先有一侧满支撑或整个三份PSD。在定向后的原同一低层坐标中，写 $v,w$ 为同一产品源的单位向量、$L=\operatorname{span}_{\mathbb C}\{v,w\}$，则原门的迹密度和原差的态坐标分别为

$$
H_{p,q}=P_L,
\qquad
(h_{p,q}-e_p)^{\sharp}=P_\psi,
\qquad
\psi=\frac{w-\langle v,w\rangle v}{\sqrt{1-|\langle v,w\rangle|^2}}.
\tag{303.5}
$$

$R^\sharp$ 在此仅记低层迹配对将原效应 $R$ 对应到的原态；不先把原态与效应空间混同。特别地 $H_{p,q}^2=H_{p,q}$、$\operatorname{Tr}H_{p,q}=2$；所有合格区分门都极端，各自的差均为同一原纯准备，不需另挑一只。未在本局部结论中断言 $h_{p,q}$ 是不带共同零要求的全部确认者的least。

证明。（一）同一面不依赖内部点。记 $\mathcal Z_{p,q}^{\rm prod}$ 为原低层纯产品中与 $p,q$ 同时迹正交的集合。301.2中对300.2的延伸只消费两个源在各块不同、已付低层零面、正切片和内部平均，不消费满支撑。它给任意同一原正泛函

$$
f(\zeta_\times)=0
\quad\Longleftrightarrow\quad
f|_{\mathcal Z_{p,q}^{\rm prod}}=0.
\tag{303.6}
$$

右侧与内部准备无关，故(303.4)定义同一面。此面是原紧区间中 $f\mapsto f(z)-f(\zeta_\times)$ 的最大值一所成非空暴露面，有限维紧凸性给极点；面极点亦为整个区间极点。这些是成熟凸几何中间工具，未据它们假定面只有一个点。

（二）先识别首门，再在固定坐标中遍历全部面极点。置 $S_3=T_1^\varepsilon$，同时运输 $C_3$、对偶及菜单；$S_3$ 保迹、保HS和迹配对，故(303.2)保持。原产品proper效应 $a_0\otimes b_0=S_3P_v$ 确认 $p$：其proper性由原max的正乘积效应及单位产品分解给出，未假设 $C_3$ 自对偶。leastness给 $0\le e_p\le S_3P_v$。在 $p$ 处评价及双预算给

$$
1=\operatorname{Tr}(e_pp)\le\|e_p\|_2\|p\|_2
\le\operatorname{Tr}e_p\le1.
\tag{303.7}
$$

取等迫 $e_p=p=S_3P_v$，所以不必把首门矩阵再作输入。$S_3C_3$ 在 $(12)|3$ 上夹于标准Sep与BP；这只运输同一三层对象，不把 $S_3$ 当作原正操作。第三腿辅助酉按XIX287.2（二）只依赖 $b,d$，在遍历 $h\in\operatorname{ext}\mathcal S_{p,q}$ 之前固定。对任意这样的 $h$，首点least单边减法、四个共同产品零测试、Gram迹二及双HS／迹等号链，逐项沿301.2的局部证明适用。这里使用的是其已展开的局部前件，不是以本条弱局部背景调用301.2的整个全有限陈述。该部分只需源一般位置、同一极端 $h$、首点least、共同零、Sep/BP和双预算，未消费数据边缘满支撑。因此同一个原差 $R_h=h-e_p$ 是实际纯准备，且

$$
\widehat x_h=T_1^\varepsilon T_3^{\delta_h}\widehat\Gamma,
\qquad \delta_h\in\{0,1\}.
\tag{303.8}
$$

$\Gamma=P_\psi$ 只由固定的 $p,q$ 及固定坐标决定，并不随 $h$ 改变；允许改变的只有尚未排除的 $\delta_h$。这同时解释为何不能从“至少有一个极点给合格种子”未经本步全称化就宣布门唯一。

（三）双侧非纯已经足够逐极点择向。XIX288.7—288.9对应同一源的平均边缘与同一 $\psi$ 的展平支撑；(303.3)使三秩为 $(r_1,r_2,2)$，其中 $r_1,r_2\ge2$，不需其中之一等于 $n$。XIII166.6的共同因子判据与Schmidt秩二纯态部分转置负谱，遂按XIX288.2（三）给同一 $\Gamma$ 的两侧条件负方向。每个 $\widehat x_h$ 都是同一原锥的实际成员，所以两个原交叠max分别要求

$$
T_1^\varepsilon\widehat x_h\in\operatorname{BP}_{2|(13)},
\qquad
T_2^\varepsilon\widehat x_h\in\operatorname{BP}_{1|(23)}.
\tag{303.9}
$$

第一侧排 $\delta_h=1$；第二侧再用全转置保持BP及 $T_1T_2=\mathsf T T_3$ 排 $\varepsilon=1$。这精确复用301.3的两侧局部排位，尚不调用其满支撑传播。选任一极点已使固定低层位为零；对其余全部极点再用同一原测试，皆得 $\widehat x_h=\widehat\Gamma$。由于残余的态—效应对应也由同一配对固定，逆辅助运输后每个极点的门都相同，密度为 $P_v+P_\psi=P_L$。

（四）从全部极点相同到整个面唯一。有限维非空紧凸集是其极点的凸包，所以全部面极点只为同一个 $h_{p,q}$ 时，整个 $\mathcal S_{p,q}$ 就是该单点。它作为面极点也是原区间极点；每个区分门均等于它，原差均为刚才的同一纯准备。两源不同且重叠模小于一，故 $v,\psi$ 正交归一，$P_L^2=P_L$ 且迹为二。证明在全有限传播前完成，没有将共同least或整个三份PSD回填进局部前提。$\square$

**命题 303.3（局部刚性与完整候选的分工）。** 完整量子候选直接复用302.1的 $\mathsf Q_0(b_*)$，不增加区分门唯一、极端或纯差条件。由302.5得到全部有限PSD后，每一组合格源都满足303.1；更强的局部结论是，303.2的证明只消费三层、一个首点least和实际区分，不需先完成302的整族构造。

证明与边界。定义303.1已将源严格重叠直接列出；全部零面和正配对由(303.1)给出。首点least的矩阵由(303.7)取得；共同零压缩仅用两块零面内部点和正切片；Gram仅用首门、共同零及同一 $(12)|3$ 的Sep/BP；残余原纯性仅用整个菜单极端性、紧归一底及(303.2)。同一三腿秩及两个交叠max随后完成局部方向和唯一性，没有消费任何第四层、其他单点least或全有限传播。这里的原态—效应对应只对取等后的同一余项成立，不假设 $C_3=C_3^*$。

在标准 $n=3$ 模型取数据向量 $a=|00\rangle$、$a'=(|00\rangle+|11\rangle)/\sqrt2$，第三腿取 $b=|0\rangle$、$d=(|0\rangle+|1\rangle)/\sqrt2$。两个块平方重叠均为 $1/2$，两张平均数据边缘均为 $\operatorname{diag}(3/4,1/4,0)$；同一 $\psi$ 三秩为 $(2,2,2)$，支持门给实际区分。因此局部唯一门成立，但这个给定源没有支付XIII165.2的一侧满维种子。此例区分两种证明接口，不是完整强全有限候选的非量子反模型。

更换四张零面内部点不改变(303.6)，因而门和原纯差不变。在给定低层坐标中，该门是二维复支持的正交投影，补门为 $I-P_L$；局部论证并不由此断言整个原三份锥是PSD，也未将它称为不带共同零要求的全部确认门的least。302.2—302.5另以固定单点族和三零，在完整全有限供应中主动制造跨割资源、升维和全部区分门；303的条件刚性不替代其存在与传播证明。故完整候选继续保持302的简洁形式，不恢复已删的源对存在条件。

文献归属。有限维紧凸集的极点凸包、HS严格凸性和Cauchy–Schwarz取等，以及纯态PPT负谱都是成熟中间工具；后者沿XIX[Q285J]的Johnston Theorem1。四零Gram和原迹一纯性分别复用本卷298.2、XIX276.2（三），两侧支撑及条件负方向复用XIX288.2（三）、288.7—288.9。repo-derived新增接合是从全有限候选抽出上述三层单首门接口，再将同源排位全称化到每个饱和面极点，迫原面唯一及每只门的同一实际纯差；不将标准PSD内的投影唯一性、全局最少独立公理或全球原创作为新结论。本文为条件纸面理论，不是Lean核验。

完整量子字典继续沿302.6：全部密度矩阵、复射线、Born迹概率、数学POVM／PVM、复张量和偏迹来自全有限重建。CP／Kraus、TNI／TP与仪器、Lüders、数学酉动力学分别保留全相关旁观保正、全输入及合计预算、事件供应和整个yes支持中性、指定连续可逆群等各自前件；物理钟、能量、$\hbar$、无限与近似极限各有独立条件。

白话：完整起点已经沿302缩成固定单点族和球上三处接触，其他存在关系让它自己长出来。这里再把其中一块拆小看：只给低两层的比较尺子、同一三层的联合约束和第一点的一只最低门；若原中点与交叉零面混合确实能被同一门完全分开，就不必再挑哪只门。把所有候选门的极端方向都看一遍，它们扣出的余项都来自同一对源，两侧联合测试会排掉每一个镜像，最后全指向同一只门，差也都是同一颗实际纯准备。两张数据影子只须都非纯，不必铺满整张单体；这只保证局部锁门，不代替整套存在和升维。比较从哪端计算相同，仍不等于仪器执行次序可以交换。$\square$

## 追加锚（本行以下为增补区）

## 304. 只向边缘未铺满的准备借门：最后一次补全不再预付满秩确认

**定义 304.1（按原边缘选出的固定纤维）。** 保留302.1的完整强全有限背景 $\mathsf F$：全部有限原实张量载体、闭尖生成锥及严格正乘积单位、整个归一底和纯域、完整正对偶及proper区间、全部有限单位分解、实际产品、正置换及逆、规范重括号、正丢弃，以及全部原相关输入上每个有限分块的min/max。仍保留299.3的互易Jordan／复类型桥、276.2的任意矩形M-only整锥分类、双HS／迹及XIII165.9的全有限传播供应；完整角继承沿XIII166.5按其前件使用。对原单体最小实际面 $B_1(p,q)$，定义

$$
\begin{aligned}
\mathsf{Bin}(K_1)&:\quad\exists p\ne q\in P_1:\ B_1(p,q)=K_1,\\
\pi_1&=\mathrm{id}\otimes u_1:K_2\longrightarrow K_1,\\
\Sigma_\partial&=\{a\in P_2:\pi_1(a)\in\partial_{\rm rel}K_1\ \lor\ \mathsf{Bin}(K_1)\},\\
\mathcal F^\partial_{b_*}&=\{\{a\otimes b_*\}:a\in\Sigma_\partial\},\qquad b_*\in P_1.
\end{aligned}
\tag{304.1}
$$

相对边界取整个原归一底的仿射包；$\mathsf{Bin}$ 只在原单体自身就是一张实际二点面时保留全部族，不用尚未取得的Hilbert维数或Schmidt秩选源。候选为

$$
\boxed{\quad
\mathsf Q_\partial(b_*)=
\mathsf{Link}(\mathcal F^\partial_{b_*})+\mathrm{L2}_1+\mathsf G_{3,1}.
\quad}
\tag{304.2}
$$

$\mathsf{Link}$ 精确沿296.1，只检查所选目标的每只原极端确认上门严格下方可比图为空或连通，排除上门但保留最低点，路径有限、图可无限。整个原菜单、全部原状态上的序和测试端未缩小。先从该规则提取已有的单体least，$\mathsf G_{3,1}$ 再使用这些原帽；每张实际二纯三球仍要求同一原双份准备给某大圆三个互异同向产品零，两张原边缘都在该球。没有把M2、任意面过滤或满边缘源的三份least重新加入前件。

**定理 304.2（缩小族仍支付单体刻度）。** 在304.1的同一背景中，(304.2)先给完整M1、每个所选 $a\in\Sigma_\partial$ 的双份全菜单least、全部纯产品点的least因子化，以及299.2的每张球全部半球刻度。因而具名Jordan／复类型供应给同一 $n\ge2,\theta$ 下的 $C_1=\operatorname{PSD}_n,u_1=\operatorname{Tr}$。这一步不消费未选双份纯点的least或完整M2。

证明。296.2逐个所选目标给原三份least $E_{a,b_*}$。限制到 $x\mapsto x\otimes b_*$，并与所有确认 $a$ 的原 $f\otimes u_1$ 比较，得 $e_a\le f$；这正是283.1的菜单下降，只将量词限制到已选族。每个 $p\otimes q$ 都被选中，因为第一边缘是原单体纯边界点；再下降得完整M1。272.2的准确前件只需两个局域完整M和这个产品目标自身的联合least，所以

$$
e_{p\otimes q}=e_p\otimes e_q\qquad(p,q\in P_1)
\tag{304.3}
$$

于整个原双份载体成立。

固定一张实际二点三球 $B$。两边缘在 $B$ 的整个原双份准备构成实际面；其与三只原产品效应零面的交仍是非空紧实际面。若 $B\ne K_1$，它是原真面，其边缘在 $\partial_{\rm rel}K_1$；若 $B=K_1$，$\mathsf{Bin}$ 成立。因此三零面的每个纯端点自身都属于 $\Sigma_\partial$，有原全域least。297.2—299.2的局部计算实际只用这类端点least、(304.3)和单体M1：原条件态下界先校准选中三个帽；球积正性给 $H_\kappa=J+\kappa vv^{\mathsf T}$、$0\le\kappa\le2$；端点的原帽及proper上界给

$$
0\le\alpha\le\tfrac14,\quad 0\le\beta\le2\alpha,
\qquad1=(4-\kappa)\alpha+(\kappa-1)\beta.
\tag{304.4}
$$

于是原纯端点只能为 $\kappa=0$ 或 $2$，态系数为 $H=\operatorname{diag}(1,R)$、帽限制为 $H/4$，$RR^{\mathsf T}=I_3$。此处未用球对角共同least $k_B$、球暴露性或非塌缩。

对任意球面单位 $a$ 取 $b=-R^{\mathsf T}a$，端点帽在原产品 $p_a\otimes p_b$ 取零。只对这两个已有least的原纯点用补门零互易，再用(304.3)，得 $0=(e_{p_a}\otimes e_{p_b})(r)=1-\beta_a-\beta_b$。单体proper给 $0\le\beta_a,\beta_b\le1/2$，故全为半球刻度。任意原单体纯点对都在其实际球内，因而数值互易成立；此时才按299.3的单体步骤用具名Jordan及复类型桥。没有直接调用299.3尚需完整M2的双份步骤。$\square$

**定理 304.3（三零端点内生二维压缩及完整矩形角）。** 在304.2所得单体坐标中，任意二维复支持 $S\subseteq\mathbb C^n$ 的 $\operatorname{Ad}_{P_S}$ 在全部有限原相关旁观者上正且不增迹。若 $n>2$，相应整个 $2\times n$ 原支持面拥有完整内在菜单和完整M，故276.2给其标准PSD或第二腿部分转置PSD；这些方向在所有 $S$ 上统一。

证明。记 $P=P_S$、$B=\mathcal D(S)$，取304.2已经支付的同一原三零纯端点 $r_B$ 及其least $e_{r_B}$。原边缘面论证使 $r_B$ 支撑在 $S\otimes S$。单体产品效应 $P\otimes P$ 原proper且确认它，故

$$
0\le_{C_2^*}e_{r_B}\le_{C_2^*}P\otimes P.
\tag{304.5}
$$

若Hermitian矩阵 $E$ 满足 $0\le_{\rm BP}E\le_{\rm BP}P\otimes P$，固定第二腿 $y$ 的条件矩阵即满足 $0\preceq E_y\preceq\langle y,Py\rangle P$。所以第一腿在 $S^\perp$ 上的行列全零；对 $y$ 极化、再交换两腿，得 $E=(P\otimes P)E(P\otimes P)$。原 $C_2$ 包含可分锥，故(304.5)适用这个支撑论证。帽的球积限制 $H/4$ 因此确定其整个原矩阵，未把限制等式冒作全域等式。

用该原杯帽构造 $L_B(x)=(\mathrm{id}\otimes e_{r_B})(r_B\otimes x)$。原min、重排后的max及双极性给全部相关旁观输入上的正性。准确支持及 $H^2=I_4$ 给

$$
4L_B(x)=PxP\qquad(x\in\operatorname{Herm}_n).
\tag{304.6}
$$

这是297.4成熟收缩的全域支持版本；正尺度放大先只保正。不增迹另由已得单体PSD给 $\operatorname{Tr}(Px)\le\operatorname{Tr}x$，相关输入的预算对其同一单腿正边缘评价；没有把放大四倍的预算从未放大分支直接搬来，也未宣称设备可用。

令 $R_S=\operatorname{Ad}_P\otimes\mathrm{id}$。原 $1|1$ 最大界使每个正输入的单腿条件矩阵PSD；若第一边缘在 $\mathcal D(S)$，在 $S^\perp$ 的条件矩阵正且迹零，故全零，极化得整个输入支持在 $S\otimes\mathbb C^n$。于是

$$
D_S=C_2\cap\operatorname{Herm}(S\otimes\mathbb C^n)
=R_S(C_2)
\tag{304.7}
$$

是第一边缘位于该实际面的整个原面锥。闭尖生成、普通迹单位及Sep/BP夹逼均继承。任意内在proper $f$ 由 $f\circ R_S$ 延为原proper，且其矩阵是零延拓，故内在菜单完整。该面纯点都是原纯点；$n>2$ 时第一边缘在真面，全部被选中。它们的原least限制到面内，利用全部 $f\circ R_S$ 比较，给整个内在菜单的M。现在才对 $m=2$、第二参数 $n$ 用276.2：

$$
D_S=\operatorname{PSD}(S\otimes\mathbb C^n)
\quad\text{或}\quad
D_S=T_2\operatorname{PSD}(S\otimes\mathbb C^n).
\tag{304.8}
$$

固定 $S_0$，用 $U\in U(n)$ 参数化 $S=US_0$；$T_2$ 取第二整腿，所以与第一腿坐标酉交换。两个候选锥经 $\operatorname{Ad}_U\otimes\mathrm{id}$ 嵌入 $C_2$ 的参数集均闭，按(304.8)覆盖 $U(n)$，且不交：同一二维Bell投影及其部分转置已区分两种整个面锥。$U(n)$ 连通使一个统一 $\varepsilon$ 在所有支持上成立。这里的 $U$ 只是连续坐标参数，尚未作为原过程使用。内在对偶零延拓还给

$$
T_2^\varepsilon\mathcal S_2\subseteq C_2\cap C_2^*,
\tag{304.9}
$$

其中 $\mathcal S_2$ 是全部Schmidt秩至多二投影生成的锥。这些投影同时proper：角内补效应零延拓，再加 $(I-P)\otimes I$ 就是全原补效应。$\square$

**引理 304.4（任意高秩射线的正交补可由少一阶的方向铺满）。** 若单位双体向量 $\psi\in\mathbb C^m\otimes\mathbb C^n$ 的Schmidt秩为 $r\ge3$，则 $\psi^\perp$ 有正交归一基，其每个向量Schmidt秩至多 $r-1$。

证明。选Schmidt坐标，置 $\psi=\alpha E_{11}+\beta E_{22}+\gamma D$，$\alpha,\beta,\gamma>0$、$\alpha^2+\beta^2+\gamma^2=1$，其中 $D$ 是余下 $r-2$ 个Schmidt项的归一和，支撑在底部 $(r-2)\times(r-2)$ 块。矩阵按向量化及HS内积识别。$E_{11},E_{22},D,E_{12}$ 正交归一，而

$$
\begin{aligned}
v_1&=-\beta E_{11}+\alpha E_{22}-\gamma E_{12},\\
v_2&=-\gamma E_{11}+\alpha D+\beta E_{12},\\
v_3&=\gamma E_{22}-\beta D+\alpha E_{12}
\end{aligned}
\tag{304.10}
$$

与 $\psi$ 正交且彼此正交归一。$v_1$ 只占左上二维块，秩至多二；$v_2,v_3$ 的顶部块各秩一，底部 $D$ 秩 $r-2$，故秩至多 $r-1$。底部矩阵块中补入 $D^\perp$ 的任意正交归一基，每项秩至多 $r-2$；再补入上述四维空间和底部块以外的全部矩阵单位，每项秩一。这是正交直和，恰铺满 $\psi^\perp$。一般Gram–Schmidt不保秩，证明只在底部块中使用它。$\square$

**定理 304.5（最后一次补全导出整个M2）。** 在(304.2)下，存在同一 $\theta$ 和 $\varepsilon\in\{0,1\}$，使 $C_2=T_2^\varepsilon\operatorname{PSD}_{n^2}$；完整双份M由此成为后果。满边缘源的三份least仍未在这一步取得。

证明。若 $n=2$，单体自身为实际二点三球，$\mathsf{Bin}$ 使 $\Sigma_\partial=P_2$；由原菜单下降给完整M2，直接用276.2。以下取 $n>2$，置 $D=T_2^\varepsilon C_2$，锥、菜单及配对一起运输。部分转置保迹及HS、保持Sep/BP夹逼；既有Gurvits—Barnum双预算给

$$
\|X\|_2\le\operatorname{Tr}X\qquad(X\in D\ \text{或}\ D^*).
\tag{304.11}
$$

(304.9)给所有秩至多二投影为原态兼proper。HS单位球严格凸性给其原纯性；这些源的第一边缘秩小于 $n$，所以其least已由选择族支付。该least低于自身投影，(304.11)的等号链 $1=\operatorname{Tr}(eP)\le\|e\|_2\le\operatorname{Tr}e\le1$ 使它恰为 $P$。

假设所有秩至多 $r-1$ 投影已在 $D\cap D^*$，$3\le r\le n$。对任意秩 $r$ 的 $\psi$，304.4给 $\psi^\perp$ 的正交归一基 $\xi_1,\ldots,\xi_{n^2-1}$，每项秩至多 $r-1<n$，原态及全菜单least均已付。从极端单位门逐只扣除 $P_{\xi_j}$：原正交读数使当前余门确认下一点，302.3所用的单点极端减法保持每步正、proper、极端。最终

$$
d=I-\sum_jP_{\xi_j}=P_\psi
\tag{304.12}
$$

是迹一原极端proper。302.3的最大读数与双HS／迹等号链使 $d$ 本身为同一原纯态。若 $r<n$，新源仍被选中，其least由输入给出并由同一等号链识别；若 $r=n$，这是最后一步，后续不再向这个目标借least。全部秩一PSD投影因此进入 $D\cap D^*$；谱分解及PSD自对偶给 $D=D^*=\operatorname{PSD}$。完整M2现在才回读。没有凭满秩源稠密或极限将其least补入。$\square$

**定理 304.6（边界族的完整量子候选）。** 在304.1明列背景及供应下，(304.2)、302.1的 $\mathsf Q_0(b_*)$ 及全部有限复PSD重建等价：存在同一保单位实线性序同构 $\theta$、$n\ge2$，使 $\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N}$、$u_N=\operatorname{Tr}\circ\theta^{\otimes N}$ 对所有有限 $N\ge0$ 成立。最终全部least和源对区分门均成为后果。

证明。304.2和304.5先给标准单体及可能带转置的完整双份。302.2的一体合同杯帽证明只消费这两层及原min/max，故仍给全部有限相关旁观者上的正性；酉和逆运输已选来源的固定旁观least。不能用一般非酉合同免费运输proper least。

302.3的七点中三个非全产品来源的双份块Schmidt秩为二，其余及角外基点为一：$n>2$ 时全部第一边缘未满，$n=2$ 时 $\mathsf{Bin}$ 保留全族。它们的全三份least因此均已付，同一原余项和复相位 $-1/6$ 证书排 $\varepsilon=1$。标准方向仍得原 $W$。其后302.4逐角升维，只有 $q_k=|Q_k\rangle\!\rangle|0\rangle$ 和 $u_k$ 需要单点least；前者双份块秩为 $k<n$，后者在孤立输出腿的另一个分割中块秩为二。它们也都属于已选边界族经置换、酉运输所得目标。已完成角内的 $P_{\psi_k}$ 只用原态、proper和整个原区间极端性，不调用它的least。XIII166.5的完整角及proper延拓、两次减法、三秩 $(k+1,k,2)$ 和XIII165.9因此按原前件接续；每步完成全部有限份数后才升 $k$。最终得到全部有限整锥。

反向，完整PSD中支持投影给所选族Link，单体实际L2及反对称准备给同一三零。$\mathsf Q_0$ 限制目标族即给 $\mathsf Q_\partial$，故三者等价。$\square$

**命题 304.7（简化范围、几何及量子字典）。** 当最终 $n\ge3$ 时，(304.1)恰选全部Schmidt秩小于 $n$ 的双份纯点；$n=2$ 时仍选全部纯点。固定纤维的输入只在高于二能级的分支实质缩小，所有原态、效应和比较域均保持完整。

证明与边界。$n\ge3$ 的二纯最小面是真二维支持，不能等于 $K_1$；边缘在相对边界恰为秩不足 $n$。被删的满秩双体纯点是行列式不零的开稠密部分，但这项稠密性只描述删去哪部分，不承担least延拓。几何结构是：同一纯旁观纤维上，只先固定投到单体边界的源；实际三零端点给二维压缩，把每个小支持连到整个原菜单。更高秩方向由低一阶方向的正交补留下，最后一步只要合法态／效应，完整门结构才整体回读。没有把低层M2作为替代输入，也没有将选择族统一截成秩二；302.4仍消费各个 $k<n$ 的来源。

删除 $\mathsf{Bin}$ 的二能级回退，本证明在整球三零端点least及七点二秩来源处缺前件；这只标本证明未付接口，不声称给出完整反模型。若所有被扣方向仅在同一产品分割可分，302.6的纯PPT边界仍阻止跨割纠缠余项。若省去二维压缩及完整内在菜单，不能从原面上选中纯点的least直接宣称拥有内在全M，再调用矩形分类。

Gurvits—Barnum[GB271]§III Theorem1给任意有限复二体的未归一可分HS半径一，正是(304.11)所复用的预算。固定Schmidt数正交基的相关研究[Q304UEB]§II要求列出向量的秩恰为 $k$，正交补不含秩恰为 $k$ 的向量；它没有给任意预指定高秩 $\psi$ 的整个正交补基，也没有给原未知锥的全域least。304.4的显式四方向计算在此承担必要接口，不由该文代付，也不申领线性代数工具的全球原创。repo-derived承重是边界原选择、三零least前件收缩、二维原压缩、逐秩原序补全及302最小消费清单的接合。局域frame、极端减法、GB预算、矩形分类、连通定向及全有限传播保留既有归属；正文是条件纸面理论，非Lean核验，不主张最少独立公理、严格逻辑弱化或无前提内生。

重建后，全部归一态、纯点、完整proper菜单及有限单位分解、原配对分别给密度矩阵、复射线、全部数学效应／POVM与PVM、Born迹概率；实际产品、置换、重括号、丢弃给同一复张量和偏迹。CP／Kraus仍要求全部有限相关旁观保正，TNI／TP及数学仪器仍要求全输入和合计分支预算，事件可用性另需供应，Lüders另需锐效应与整个yes支持中性，数学酉动力学另需指定连续可逆保单位且全旁观保正群。物理钟、能量、$\hbar$、无限与近似极限独立。

白话：原来前两份每一种纯准备都要向固定旁观者借一只最低门。现在先跳过那些影子已经铺满整个单体的准备；只有单体本身就是最小三球时，暂时保留原来的全部要求。三零关系先交出小球的尺和真正的二维压缩，使小支持里的门仍能拿到整个世界里比较。要留下一个更高秩方向，可以把它周围全部正交方向排成一套，其中每颗都少占一阶；逐只扣去它们的最低门，最后剩下的方向就必须也是合法准备。只要还未铺满，它还在已要求有门的边界族中，可以继续向上；最后一次铺满时，只需留下合法态和测试，不必再预付它的门来启动下一步。原来跨三个分割的七点和逐维构造恰好只借这些未满边缘的门，所以仍能完成全部有限量子结构。完整背景、实际三零和具名供应始终保留；二能级分支这一步尚未缩减。$\square$

[Q304UEB]: https://arxiv.org/abs/1407.4362v3 "Yu Guo、Shengjun Wu，Unextendible entangled bases with fixed Schmidt number，Phys. Rev. A90,054304；§II定义的固定秩UEBk，不供应本章任意给定高秩射线的正交补基或原未知锥的least。"

## 追加锚（本行以下为增补区）

## 305. 三个零不必共大圆：只比较一张边缘对一对对径点的读数

**定义 305.1（原对径读数比较）。** 完整保留304.1的强全有限背景、边界选择族 $\Sigma_\partial$、固定纯旁观者 $b_*$、$\mathcal F^\partial_{b_*}$、$\mathsf{Link}$、实际 $\mathrm{L2}_1$ 及全部具名供应。304.2中从Link下降到完整M1、选中双份源least及产品least因子化的第一步不消费三零，故仍先执行这一步。对实际二纯三球 $B=\iota(\overline{\mathbb B}^3)$，记 $p_a=\iota(a)$，$\bar p_a=\iota(-a)$；原帽 $e_p$ 均指整个原菜单中的单点least。令 $\mathsf G^{\rm cmp}_{3,1}$ 要求每张这样的 $B$ 都有三个互异单位方向 $a_1,a_2,a_3$ 及同一个原 $\omega\in K_2$，满足

$$
\begin{aligned}
\pi_1\omega,\pi_2\omega&\in B,\\
(e_{p_{a_i}}\otimes e_{p_{a_i}})(\omega)&=0\qquad(i=1,2,3),\\
\exists i\in\{1,2,3\}:\quad
 e_{p_{a_i}}(\pi_1\omega)&\ge e_{\bar p_{a_i}}(\pi_1\omega).
\end{aligned}
\tag{305.1}
$$

候选为

$$
\boxed{\quad
\mathsf Q^{\rm cmp}_\partial(b_*)=
\mathsf{Link}(\mathcal F^\partial_{b_*})+
\mathrm{L2}_1+\mathsf G^{\rm cmp}_{3,1}.
\quad}
\tag{305.2}
$$

原帽的存在先由同一Link给出；没有把未知帽的球内刻度作为定义。这条比较只涉及同一原边缘与一对原对径纯点的两次读数，不预设数值二分之一。球坐标只确定实际对径点，换正交坐标不改变条件，也不作为原过程。三个方向不要求共大圆、等角或球心凸包；整个原态、菜单和比较域仍保留。

**定理 305.2（三零使三张边缘比较相等且非正）。** 在305.1的先行Link及实际球条件中，任意满足前三个原零及球内双边缘的 $\omega$，其所选三个帽和三个对径帽在 $B$ 上都已是半球刻度。三个方向唯一确定一张平面 $n\cdot a=h$，其中 $\|n\|=1$、$|h|<1$。存在 $\kappa\ge0$，使同一原态的球张量系数及两张边缘坐标分别为

$$
\begin{aligned}
H_\kappa&=(1-\kappa h^2)J+\kappa vv^{\mathsf T},
&J&=\operatorname{diag}(1,-I_3),&v&=(-h,n),\\
r_1&=r_2=-\kappa h n,\\
e_{p_{a_i}}(\pi_1\omega)-e_{\bar p_{a_i}}(\pi_1\omega)
&=-\kappa h^2\qquad(i=1,2,3).
\end{aligned}
\tag{305.3}
$$

这里 $H_\kappa$ 是已有原态的系数，不宣称所有允许系数都是原成员。

证明。280.2（一）的互补原条件态给 $\omega\in W_B\otimes W_B$；282.4的正对偶限制闭包使其归一系数式在整个球积非负，不赠送任意内在proper的原延拓。对每个单体原纯点，279.3的局部法线形式为 $e_{p_a}(\iota(x))=1-\beta_a+\beta_a a\cdot x$，$0\le\beta_a\le1/2$。若一个已选 $\beta_{a_i}<1/2$，该帽在整个 $B$ 上有正下界 $m_i=1-2\beta_{a_i}$。同一原条件态仍在球面锥，280.8的两次下界遂给原零读数至少为 $m_i^2>0$，矛盾。因此三个已选帽均有 $\beta_{a_i}=1/2$。它在对径点为零；M1的补门least论证给 $e_{\bar p_{a_i}}(p_{a_i})=0$，故三个对径帽也有同一刻度。这一步未用双份任意纯点least。

三个互异球面点不共线，故其仿射平面唯一且 $|h|<1$。对整个球积非负、在这三个对角点为零的双仿射形式 $g$，297.2的边界法线步骤不依赖 $h=0$：

$$
g(a_i,b)=A_i(1-a_i\cdot b),\qquad
g(a,a_j)=B_j(1-a\cdot a_j).
\tag{305.4}
$$

在 $i\ne j$ 的交叉点比较给 $A_i=B_j$；三个互异点使全部尺度同为 $\alpha\ge0$。减去 $\alpha(1-a\cdot b)$ 后，形式在任一腿属于上述平面时恒零，因此唯一写成

$$
g(a,b)=\alpha(1-a\cdot b)+\beta(n\cdot a-h)(n\cdot b-h).
\tag{305.5}
$$

在球面对角上评价给 $\beta\ge0$。用于原归一态时常数项为一，故 $\alpha+\beta h^2=1$；置 $\kappa=\beta$，即得(305.3)的系数与边缘。已选两只对径帽已校准，其读数差恰为 $a_i\cdot r_1=-\kappa h^2$。没有从一般球积正性推原纯性，也未将帽与态预先识别。$\square$

**定理 305.3（一张原边缘的比较足以回到大圆三零）。** 在305.1的同一先行Link及实际L2背景下，每张球的(305.1)与299.1的大圆三零存在性等价。若(305.1)的三点不共大圆，同一原见证已有系数 $H_0=J$，并且它的整个球面同向原产品读数均为零。

证明。305.2先使比较成为 $-\kappa h^2\ge0$。因 $\kappa\ge0$，有 $\kappa h^2=0$。若 $h=0$，原来的三点与原见证直接给旧大圆入口。以下取 $h\ne0$，则同一原 $\omega$ 自身为 $r_0$，不是另将内在端点加入原锥。

还须把系数中的全对角零还原为尚未校准的原帽读数。令 $\mathcal D$ 为球内双边缘与这三只原产品零相交的整个原紧实际面。305.2将其各点唯一写成某个 $\kappa\ge0$；若 $r_0$ 是两点的非平凡凸平均，两点参数均非负而平均为零，只能均为零，故两点都等于 $r_0$。因此 $r_0$ 是该实际面的极点，进而是整个原 $K_2$ 的纯点。若 $B\ne K_1$，其第一边缘 $c_B$ 在原单体真面中；若 $B=K_1$，Bin回退适用。两种情形均使 $r_0\in\Sigma_\partial$，它在整个原双份菜单中的least $e_0$ 已由Link下降支付。

每个已选产品的least为 $e_{p_{a_i}}\otimes e_{p_{a_i}}$。在 $r_0$ 处为零，原补门及least比较两次给

$$
0\le e_0\le u_2-e_{p_{a_i}}\otimes e_{p_{a_i}},
\qquad e_0(p_{a_i}\otimes p_{a_i})=0.
\tag{305.6}
$$

它的球积限制由(305.5)写成 $G=\alpha J+\beta vv^{\mathsf T}$，$\alpha,\beta\ge0$；这里帽的常数项不归一为一。取单位 $z\perp n,a_i$，令 $b_\pm=\cos\epsilon\,a_i\pm\sin\epsilon\,z$。在同一个原proper上界评价，得到

$$
2\alpha\sin^2\epsilon+
\beta h^2(\cos\epsilon-1)^2
\le1-\left(\frac{1+\cos\epsilon}{2}\right)^2,
\qquad \alpha\le\frac14.
\tag{305.7}
$$

后一式是除以 $\epsilon^2$ 的极限。用同一原态 $H_0=J$ 归一确认，系数配对给

$$
1=e_0(r_0)=4\alpha-(1-h^2)\beta
\le4\alpha\le1.
\tag{305.8}
$$

$|h|<1$ 使等号迫 $\alpha=1/4,\beta=0$。因此原帽的整个球积限制为 $J/4$。对任意单位 $a$，该原帽在原纯产品 $p_a\otimes p_a$ 为零；这类产品已有原least及产品因子化。299.2的两点原零互易于是给

$$
0=(e_{p_a}\otimes e_{p_a})(r_0)=1-2\beta_a.
\tag{305.9}
$$

故任意原球面帽都校准，并且同一 $r_0$ 对全部同向原产品读数为零。现在才从实际球中任选三个互异大圆方向，交出旧入口。整个步骤只使用选中端点least及纯产品least，没有预付完整M2。

反向，旧大圆见证在305.2中有 $h=0$，故第一边缘为 $c_B$，三个比较均为零，原三点直接满足(305.1)。反向不要求旧见证是纯点，也不排除299.2的另一端点。$\square$

**定理 305.4（对径比较的完整量子候选）。** 在304.1明列的完整背景及具名供应下，对每个固定原 $b_*$，$\mathsf Q^{\rm cmp}_\partial(b_*)$、$\mathsf Q_\partial(b_*)$、$\mathsf Q_0(b_*)$ 与全部有限复PSD重建等价：存在同一 $n\ge2$、保单位实线性序同构 $\theta$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{305.10}
$$

证明。Link的先行下降和产品因子化不消费三零；305.3因此按已付前件取得实际大圆三零。此时才完整调用304.2—304.6：单体刻度、三零杯帽的全域二维压缩、proper延拓给完整矩形角菜单、统一二层方向、低一阶正交补与原序逐秩补全，给完整M2。302.2的全部相关旁观一体运输、302.3七点跨割方向反证、302.4两次减法逐维传播及XIII166.5完整角、XIII165.9全有限供应继续按原范围使用。所有 $q_k$ 的秩 $k<n$、换割 $u_k$ 的秩二及二能级Bin回退仍与304.6一致；本条未缩小该尾部消费族，也未以303的局部门唯一替代区分存在性。

反向由304.6的完整PSD反向和305.3。还可在每张二维支持取反对称准备，其双边缘是球心、全部同向原产品为零，故任意三个互异方向及对径比较都成立。$\square$

**命题 305.5（放宽的几何、保留的边界与量子字典）。** (305.1)放宽的是见证三点的摆放限制：大圆精确等式改为原边缘与一对原对径帽的弱读数比较。它允许旧入口不接受的非共大圆三点，但在保留背景中两者的存在断言等价。

证明与范围。在标准二能级球取反对称准备和 $a_1=e_1,a_2=e_2,a_3=e_3$，三点平面为 $(1,1,1)\cdot a=1$，不经过球心；边缘为球心，三个读数差均为零。故这些给定见证可用于(305.1)，不能以同一三点用于旧大圆定义。这不表示完整模型类严格扩大，也不声称独立公理数减少。新几何只以原二元帽—边缘读数比较选择半空间，三元有限提升的三零刚性把三个差锁成同一个非正值；同一原序的帽预算将未校准的球积限制回接为全部原产品零。

删除读数比较时，(305.3)仍容许 $h\ne0,\kappa>0$ 的系数分支；本条不能把它压到零。这指出当前证明未付的接口，不声称已有满足整个原菜单、选中least及全有限背景的非量子反模型。仅有 $H_0$ 的坐标对角零不足以宣布原帽读数全零，(305.6)—(305.9)正是必要桥梁。球坐标、对径映射和选择大圆均未作为可用设备或正控制。完整有限背景、边界Link、实际L2、三次原零、球内双边缘、Jordan／复类型、矩形M-only、双HS／迹与传播供应全部保留。

球面支撑法线、仿射平面因子化和二阶预算是成熟有限维工具；原支撑与正对偶限制、条件态下界、产品least和零互易分别复用280.2、282.4、272.2与299.2。Lorentz最大正映射锥的极射线分类沿[Q297Lorentz]Lemma6、Theorem1；该分类不将指定原子锥的纯点变成最大锥极点，也不供应未知原成员、正逆或Lorentz滤波。本条新增承重是原对径比较、三张同值边缘差、实际 $r_0$ 的选中纯性及原帽预算与304完整候选的接合，不申领上述成熟工具、全有限传播或全球原创。结论是条件纸面理论，非Lean核验。

重建后的归一态、纯点、完整proper菜单、有限单位分解与原配对给全部密度矩阵、复射线、数学效应／POVM与PVM、Born迹概率；原产品、置换、重括号与丢弃给同一复张量和偏迹。CP／Kraus仍要求全部有限相关旁观保正，TNI／TP与数学仪器仍要求全输入及合计分支预算，实际事件另需供应，Lüders另需锐效应和整个yes支持中性，数学酉动力学另需指定连续可逆保单位且全旁观保正群。物理钟、能量、$\hbar$、无限与近似极限仍独立。

白话：仍找同一种双份准备，让三个不同方向的“左右同时说是”都不发生，但不再要求三个方向刚好排在大圆上。只看这份准备的一张原影子：至少有一个已选方向，它的最低门读数不低于对面那只最低门。三个零会把这三次正反比较锁成同一个非正数；若三点真的偏离球心，比较只能把这个数压到零，同一原准备便留下各向反关联的系数。还不能把坐标上的零直接当成原门的零；它自己的最低门既要认出它，又受三只补门限制，预算恰把门固定下来，于是所有同向原读数都为零，可以重新选出大圆见证。随后二维小角、逐秩补全和跨割升维按既有证明完成全部有限量子结构。三点的精确摆放放宽成一条原读数比较，边界门族与完整背景仍明说；没有附加比较的任意三点尚未由本条解决。$\square$

## 追加锚（本行以下为增补区）

## 306. 整体已经是球时不再索取三零：把接触条件留给嵌入真面

**定义 306.1（仅作用于真二点面的接触关系）。** 保留304.1的完整强全有限背景、原边界选择族 $\Sigma_\partial$、固定原纯旁观者 $b_*$、$\mathcal F^\partial_{b_*}$ 及其原 $\mathsf{Link}$。实际 $\mathrm{L2}_1$ 仍作用于全部原单体二纯最小面。299.3的互易Jordan／复类型、276.2及其所引XIX274.3的M-only供应、双HS／迹和XIII165.9的全有限传播供应继续明列；需要完整角时仍按XIII166.5的原前件使用。不预置单体Hilbert维数。

先沿304.2的第一段从Link取得M1、选中双份least和纯产品least因子化；该段不消费三零。定义 $\mathsf G^{\rm cmp,prop}_{3,1}$：只对满足 $B=B_1(p,q)\ne K_1$ 的实际二纯球，要求305.1的完整关系。具体说，在某球坐标 $B=\iota(\overline{\mathbb B}^3)$ 中，有三个互异单位方向 $a_1,a_2,a_3$ 和同一个原 $\omega\in K_2$，使

$$
\begin{aligned}
\pi_1\omega,\pi_2\omega&\in B,\\
(e_{p_{a_i}}\otimes e_{p_{a_i}})(\omega)&=0\quad(i=1,2,3),\\
e_{p_{a_j}}(\pi_1\omega)&\ge e_{p_{-a_j}}(\pi_1\omega)
\quad\text{对某个 }j\in\{1,2,3\},\qquad p_a=\iota(a).
\end{aligned}
\tag{306.1}
$$

所有 $e_p$ 仍是整个原单体菜单中的least；测试端和原序不限制到面内。候选为

$$
\boxed{\quad
\mathsf Q^{\rm prop}_\partial(b_*)=
\mathsf{Link}(\mathcal F^\partial_{b_*})+
\mathrm{L2}_1+\mathsf G^{\rm cmp,prop}_{3,1}.
\quad}
\tag{306.2}
$$

与305.1相比，只删去 $B=K_1$ 分支上的全部三零、球内边缘及比较见证，不改变边界族的 $\mathsf{Bin}$ 回退。真面分支的三个零仍必须来自同一原双份准备。

**定理 306.2（整球分支由固定单点关系直接完成）。** 在306.1明列的背景及M-only、双HS／迹和传播供应中，若 $\mathsf{Bin}(K_1)$、$\mathrm{L2}_1$ 及 $\mathsf{Link}(\mathcal F^\partial_{b_*})$ 成立，则存在同一个保单位实线性序同构 $\theta:V\to H_2$，对所有有限 $N\ge0$ 有

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{2^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{306.3}
$$

本分支不消费任何三零或读数比较，也不消费互易Jordan／复类型桥。

证明。（一）整个单体先给二能级坐标。Bin给某对不同原纯点的最小实际面就是 $K_1$，L2于是使整个 $K_1$ 为三维闭球。取球心 $c$，写球同构为 $\iota(a)=c+Ta$，其中 $T:\mathbb R^3\to\ker u_1$ 为线性同构。整个原锥生成 $V$，故每个原向量唯一写为 $tc+Tx$。取三只标准Pauli矩阵 $\sigma_j$，令

$$
\theta(tc+Tx)=\frac12\left(tI_2+\sum_{j=1}^3x_j\sigma_j\right).
\tag{306.4}
$$

右边特征值为 $(t\pm\|x\|)/2$，其迹为 $t$；原锥恰由 $t\ge\|x\|$ 描述，遂给整个 $C_1=\operatorname{PSD}_2$ 及普通迹单位。完整菜单随逆对偶运输为 $[0,I_2]$，单体原least因而就是对应的纯投影。这是271.48所用的成熟球坐标齐次化，不从未知球帽预借刻度、数值互易或Jordan表示；球坐标选择也不宣称原设备可实现任意旋转。

（二）完整M2直接分类整个双份。Bin使 $\Sigma_\partial=P_2$。296.2给每个 $a\otimes b_*$ 的原三份least，再用304.2第一段的完整菜单限制及 $f\otimes u_1$ 比较，给整个原纯域上的M2。在同一个 $\theta^{\otimes2}$ 坐标中，原min/max成为整个 $H_2\otimes_{\mathbb R}H_2$ 上的Sep/BP夹逼。276.2的 $m=n=2$ 前件现在全部已付，故

$$
C_2=T_1^\varepsilon\operatorname{PSD}_4,\qquad
C_2^*=C_2,\qquad \varepsilon\in\{0,1\}.
\tag{306.5}
$$

此处M-only确实不要求实际双份球、数值互易或三零。也可直接用XIX274.3的统一秩二供应，因为 $2\times2$ 的全部向量Schmidt秩至多二，已得方向的秩二投影包含整个PSD锥；对偶包含给反向。部分转置在此仅是整锥坐标分类，未作为原物理操作。

（三）从低二层支付三份帽，再排镜像。抽取302.2已经展开的局部证明，而不按302.1含三零的完整候选前件调用其结论。该证明的实际输入只是(306.4)—(306.5)、全部有限相关输入的原min/max、固定纤维least及双HS／迹预算：标准方向以Bell杯帽，镜像方向以(302.4)—(302.5)的交换杯帽，支付全部有限相关旁观者上一体合同的正性。酉及逆保单位，所以原固定旁观者 $b_*$ 可运输到每个单体纯点，位置置换及逆再运输分割。

对固定纤维目标 $X=T_i^\varepsilon P_{a\otimes b_*}$，原min/max给 $X$ 和 $I-X$ proper；三份原least $e_X\le X$ 的确认与双预算给

$$
1=\operatorname{Tr}(e_XX)\le\|e_X\|_2\|X\|_2
=\|e_X\|_2\le\operatorname{Tr}e_X\le\operatorname{Tr}X=1.
\tag{306.6}
$$

因而 $e_X=X$。这是原三份完整菜单中的帽识别，不能只凭二层矩阵形式跳过。酉和置换运输给每个二可分三份原纯点的同一矩阵least。三份双预算在(306.5)任一方向均沿302的原 $1|23$ 分块供应，部分转置保迹和HS；未要求全M3或预置 $C_3$ 的PSD。

现在(302.6)—(302.9)的七点原序证明逐项可用：三个非全产品来源的双份块全在本分支保留的 $P_2$ 中，其余是全产品。若 $\varepsilon=1$，从原极端单位门逐只扣除七只正交单点least，得同一迹一极端proper余门 $D$；最大确认与双预算使 $D$ 同时为原态。原 $1|(23)$ 产品proper效应 $P_{(0+i1)/\sqrt2}\otimes T_2P_{(00+i01-i10)/\sqrt3}$ 对它的读数为 $-1/6$，与原max矛盾。故 $\varepsilon=0$。这一步用全部三个实际分割及复相位，不把各分割的转置拼成原全局操作。

（四）一个七点余项直接覆盖全部有限层。标准方向对同一七点逐只扣去普通投影，302.4首段的原极端减法和迹一等号链给

$$
P_w\in C_3\cap[0,I]_{C_3^*},\qquad
w=(100+010+001)/\sqrt3.
\tag{306.7}
$$

此处才取得实际原 $W$，不是预先把普通纠缠向量宣布为原准备。按XIII165.2的向量化，可忽略非零公共归一因子而写

$$
\sqrt3w=|A\rangle\!\rangle|0\rangle+|B\rangle\!\rangle|1\rangle,
\qquad A=E_{01}+E_{10},\quad B=E_{00}.
\tag{306.8}
$$

$A$ 可逆且与 $B$ 线性独立，像之和为整个 $\mathbb C^2$，共同核为零，三展平秩为 $(2,2,2)$。现在 $C_1=\operatorname{PSD}_2,C_2=\operatorname{PSD}_4$、整个原菜单和全有限min/max均准确满足XIII165.1，(306.8)满足165.2。165.9直接给(306.3)，无需完整角继承、另补qutrit或逐维升阶。所有有限 $N$ 的结论来自该具名全有限传播供应，不来自有限前缀或可生成子锥。$\square$

**定理 306.3（只向真面借接触的完整量子候选）。** 在306.1的同一完整背景及全部具名供应下，对每个固定原 $b_*$，$\mathsf Q^{\rm prop}_\partial(b_*)$ 与305.1的 $\mathsf Q^{\rm cmp}_\partial(b_*)$、304.1的 $\mathsf Q_\partial(b_*)$、302.1的 $\mathsf Q_0(b_*)$ 及全部有限复PSD重建等价：存在同一 $n\ge2$ 和保单位实线性序同构 $\theta$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{306.9}
$$

且 $\mathsf{Bin}(K_1)$ 当且仅当重建维数 $n=2$。

证明。按原几何是否Bin二分。Bin时由306.2直接得到 $n=2$ 的全部有限重建；标准反对称准备此时才成为原态，球心边缘和全部同向原产品零为后果。非Bin时，每张实际二纯面都不等于整个 $K_1$，故(306.1)恰覆盖305.1的全部球，305.4按完整原前件给(306.9)。该分支并未缩小原三零存在族，也未删除其比较。

反向，全部有限复PSD的支持投影least给同一固定边界族的Link。任意不同纯点的最小实际面是其复二维支持上的完整球；真面中取反对称准备，双边缘为该球中心，任意三个互异方向的同向原产品读数为零、对径比较取等，故满足(306.1)。在PSD中，二纯最小面只承载复二维支持；它等于整个单体当且仅当 $n=2$，给最后的维数识别。其余候选等价复用305.4。本证明没有用305.4去证明尚未支付三零的Bin分支。$\square$

**命题 306.4（嵌入几何、反事实及量子公理对应）。** 新候选将接触要求集中到二点球作为更大单体真面的嵌入关系；整个单体已经是球时，该要求的量词域为空，三零准备成为固定单点关系和三份跨割补全的结论。

证明与范围。整球分支直接给四维Lorentz锥与 $\operatorname{PSD}_2$ 的保单位表示；真面分支仍用305的三零—对径比较消去偏心自由度，再沿304支付二维压缩、完整矩形角和逐秩补全。两路汇合到同一低二层之后，三份的不同分割共同约束同一个原余项。最小几何图景因此是“原确认关系在球及球的嵌入上相容”，不是另为最小球预设一个反关联资源。

删除Bin分支三零不留缺口，由306.2主动造出该资源；删除真面分支三零或比较，当前证明仍缺非Bin时的球刻度和原二维压缩，305.5的小圆分支边界不变。若把Bin的边界族回退也删掉，未满边缘选择不能给全部M2或七点所需的三份非产品帽，306.2第二、三步便失去依据；这指出本证明的未付接口，不声称已构造完整非量子反模型。仅有球面外形而没有整个原菜单、全旁观min/max和跨分割同一性，也不能把任意一体坐标映射当作原正操作。

本条减少的是几何见证的索取范围：二能级整体不再提交任何三零准备，三能级及以上维持305的全部真面要求。它没有证明完整模型类严格扩大、独立公理数全局最小或无前提内生；在明列背景中这些存在断言仍等价。Jordan／复类型在非Bin分支保留，M-only、双预算及传播供应继续保留；Bin分支已明确不消费前一桥。有限维球的Pauli表示、HS取等及正交投影运算都是成熟中间工具，分别沿271.48、276及302的已有归属。新增repo-derived接合是原Bin二分、固定边界族的整球回退与302已展开低层证明及XIII165.9之间的连接，删除整个最小分支的三零前件；不将成熟表示、七点证书或传播另领为新一般定理，不申领全球原创。结论为条件纸面理论，非Lean核验。

重建后的公理对应沿同一个 $\theta$，不逐层换坐标：

| 量子力学中的结构 | 本候选中的推导与条件 |
| --- | --- |
| 有限复Hilbert空间、纯射线和密度矩阵 | (306.9)识别全部有限PSD锥；整个归一底与其极点分别给密度矩阵和纯射线 |
| Born概率、数学效应、POVM及PVM | 完整逆对偶成为 $0\preceq E\preceq I$，原配对为 $\operatorname{Tr}(\rho E)$；全部有限单位分解给POVM，投影分解为其中PVM |
| 复张量复合和部分迹 | 同一 $\theta^{\otimes N}$、原乘积配对和单位丢弃识别复张量与矩阵偏迹 |
| CP／Kraus与数学仪器 | 仍需指定映射对全部有限相关旁观者保正；TNI／TP及仪器另需全输入及合计分支预算，实际设备事件另需供应 |
| Lüders更新和数学酉动力学 | 前者仍需锐效应及整个yes支持中性；后者仍需指定连续、可逆、保单位且全旁观保正的群，物理钟、能量和 $\hbar$ 不由本条给出 |

白话：先看这只球是不是整个世界。如果整个单体就是一只二能级球，就不再额外索取一份“三个方向同时不响”的准备；同一固定旁观者下的最低确认关系已经能定出双份结构。把七个可分准备放到三个不同切口下比较，依次扣掉它们的最低门，剩下的一份必须同时是合法门和合法准备；镜像方案会给负概率，被排除，正确方案留下三边都连着的 $W$，由已明列的传播定理完成全部有限份数。如果球只是嵌在更大单体里的一个小面，才向这个嵌入索取原三零和一次对径比较，沿既有证明补齐整体。最小球自己的反关联不再先送进去，而是在同一确认关系的三份拼接中长出来；真面上的接触、完整菜单及传播条件仍全部明说。$\square$

## 追加锚（本行以下为增补区）

## 307. 两个原零交换边缘读数：由跨方向比较补出第三零

**定义 307.1（两个同向零与跨方向比较）。** 保留306.1的完整强全有限背景、原边界族及固定纯旁观者 $b_*$、$\mathsf{Link}(\mathcal F^\partial_{b_*})$、实际 $\mathrm{L2}_1$ 和全部具名供应。仍先由不消费几何见证的Link下降取得M1及纯产品least。定义 $\mathsf G^{\times,\rm prop}_{2,1}$：每张实际二纯真面球 $B=B_1(p,q)\ne K_1$ 都有球坐标 $p_x=\iota(x)$、两个单位方向 $a\ne b,a\ne-b$ 及同一个原 $\omega\in K_2$，满足

$$
\begin{aligned}
m_1=\pi_1\omega,\quad m_2=\pi_2\omega&\in B,\\
(e_a\otimes e_a)(\omega)&=(e_b\otimes e_b)(\omega)=0,\\
e_a(m_1)&\ge e_{-b}(m_1),\qquad e_x=e_{p_x}.
\end{aligned}
\tag{307.1}
$$

$e_x$ 是整个原单体菜单中的least，不是面内新选的帽。比较作用于同一张原边缘，却比较一个方向与另一个方向的对径；它取代305的同向对径比较。候选为

$$
\boxed{\quad
\mathsf Q^{\times}_\partial(b_*)=
\mathsf{Link}(\mathcal F^\partial_{b_*})+
\mathrm{L2}_1+\mathsf G^{\times,\rm prop}_{2,1}.
\quad}
\tag{307.2}
$$

Bin分支仍不索取几何见证；非Bin分支显列的同向双体零从三项变为两项，同时改变单体比较。没有新增任意控制、滤波、更新或设备事件。

**定理 307.2（原两零的交叉换位与补读数恒等式）。** 只取原双份min/max、完整原proper菜单及M1。设 $B$ 是实际二纯球，$\omega$ 的两个原边缘都在 $B$，且 $a\ne b$ 的两个同向原产品零成立；本条暂不要求跨方向比较，也不要求 $a\ne-b$。则

$$
\begin{aligned}
e_a(m_1)&=e_b(m_2),&e_b(m_1)&=e_a(m_2),\\
(e_{-a}\otimes e_{-a})(\omega)
&=(e_{-b}\otimes e_{-b})(\omega)
=e_{-b}(m_1)-e_a(m_1)\ge0.
\end{aligned}
\tag{307.3}
$$

本条不消费完整M2、$\omega$ 自己的least或任何高层PSD。

证明。（一）所有原proper条件向量留在实际面内。对 $0\le f\le u_1$ 取

$$
X_f=(f\otimes\mathrm{id})\omega,\qquad
Y_f=(\mathrm{id}\otimes f)\omega.
\tag{307.4}
$$

原max与完整正对偶使两者原正，且 $X_f+X_{u_1-f}=m_2$、$Y_f+Y_{u_1-f}=m_1$。$\operatorname{cone}B$ 为原实际面锥，所以全部 $X_f,Y_f\in\operatorname{cone}B$；其质量分别为 $f(m_1),f(m_2)$。这里只作明确张量收缩，不引入测量后的过程。

（二）一个零先校准对应帽及对径帽。原proper帽 $e_a$ 在 $p_a$ 取一，球上仿射极值给

$$
e_a(p_x)=\delta_a+(1-\delta_a)\frac{1+a\cdot x}{2},
\qquad \delta_a=e_a(p_{-a})\in[0,1].
\tag{307.5}
$$

于是 $e_a\ge\delta_a u_1$ 于 $\operatorname{cone}B$。同向零与(307.4)给

$$
0=e_a(Y_{e_a})\ge\delta_a u_1(Y_{e_a})
=\delta_a e_a(m_2)\ge\delta_a^2.
\tag{307.6}
$$

故 $\delta_a=0$，$e_a|_B=(1+a\cdot x)/2$。原proper $u_1-e_a$ 确认 $p_{-a}$；M1的全原least比较给 $e_{-a}\le u_1-e_a$。在 $p_a$ 求值得 $e_{-a}(p_a)=0$，球上仿射几何遂给 $e_{-a}|_B=(1-a\cdot x)/2$。因此

$$
r_a=u_1-e_a-e_{-a}\in C_1^*,\qquad
0\le r_a\le u_1,\qquad r_a|_B=0.
\tag{307.7}
$$

$b$ 完全同理。这里保留原正余门，未将球内互补冒作整个原载体上的 $e_{-a}=u_1-e_a$。

（三）同一交叉产品从两边计算。设 $A_j=e_a(m_j)$、$B_j=e_b(m_j)$。球内 $e_a$ 的零面恰为 $p_{-a}$，故(307.4)及同向零给

$$
X_{e_a}=A_1p_{-a},\qquad Y_{e_a}=A_2p_{-a},\qquad
X_{e_b}=B_1p_{-b},\qquad Y_{e_b}=B_2p_{-b}.
\tag{307.8}
$$

这些未归一等式在质量为零时也成立。于是

$$
(e_a\otimes e_b)(\omega)
=A_1e_b(p_{-a})=B_2e_a(p_{-b}),\qquad
e_b(p_{-a})=e_a(p_{-b})=\frac{1-a\cdot b}{2}>0.
\tag{307.9}
$$

仅除以这个严格正交叠，得 $A_1=B_2$；交换 $a,b$ 得 $B_1=A_2$。没有除以任何条件态质量。

（四）原余门在这份准备上消失。任取原proper $g$，原产品正性给

$$
0\le(r_a\otimes g)(\omega)
\le(r_a\otimes u_1)(\omega)=r_a(m_1)=0.
\tag{307.10}
$$

另一腿及 $r_b$ 同样。因而只在同一 $\omega$ 的相关产品读数中，可用 $u_1-e_a$ 替换 $e_{-a}$。展开并使用(307.9)，得

$$
\begin{aligned}
(e_{-a}\otimes e_{-a})(\omega)
&=((u_1-e_a)\otimes(u_1-e_a))(\omega)\\
&=1-A_1-A_2=1-A_1-B_1\\
&=e_{-b}(m_1)-e_a(m_1).
\end{aligned}
\tag{307.11}
$$

$b$ 的补对角读数同样是 $1-B_1-B_2=1-A_1-B_1$。两者原正，给(307.3)。$\square$

**定理 307.3（一次低阶比较产生同一准备的大圆三零）。** 若再满足307.1的比较及 $a\ne-b$，则同一个原 $\omega$ 具有 $a,b,-a,-b$ 四个同向产品零，且 $m_1=m_2=c_B$；因而它直接满足304.1所需的大圆三零。

证明。比较使(307.3)右端非正，原正性使其非负，故两只补对角读数同时为零。$a,b,-a$ 三点互异，均在 $S^2\cap\operatorname{span}\{a,b\}$，这是实际大圆；两个边缘仍在原球，见证没有更换。

球心结论也是后果。由(307.7)的原单位分解 $e_a+e_{-a}+r_a=u_1$、余门消失及新增补零，

$$
m_2=A_1p_{-a}+(1-A_1)p_a
=B_1p_{-b}+(1-B_1)p_b.
\tag{307.12}
$$

其球坐标给 $(1-2A_1)a=(1-2B_1)b$；$a\ne\pm b$ 使两向量线性独立，故 $A_1=B_1=1/2$、$m_2=c_B$。另一腿同理。该局部结论不宣称 $\omega$ 纯，也未把尚未校准的其他方向原产品读数预认成零。$\square$

**定理 307.4（两个原零的完整量子候选）。** 在307.1明列的同一完整背景和具名供应下，对每个固定原 $b_*$，$\mathsf Q^{\times}_\partial(b_*)$ 与306.1、305.1、304.1、302.1的完整候选及全部有限复PSD重建等价：存在同一保单位实线性序同构 $\theta$ 及 $n\ge2$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{307.13}
$$

证明。Bin时直接用306.2，不消费(307.1)。非Bin时全部实际二纯球都是真面；307.3对每张球输出原大圆三零，且同一第一边缘是球心，故305的比较也取等。由此306.3的全部前件已付。其非Bin路线继续使用304的球帽校准、全旁观二维压缩、完整矩形角菜单及M-only、低秩正交补逐秩补全，再用302的跨割七点、$q_k/u_k$ 两次减法、XIII166.5完整角及165.9的全有限传播。边界族仍准确支付这些来源：$q_k$ 双份块秩 $k<n$，$u_k$ 换割秩二，Bin保留全部 $P_2$；未删除或扩域任何原least消费。

反向，完整复PSD的支持投影least和全部原单位分解给原固定边界族Link，实际L2由二维复支持球成立。在每张真面球的二维支持上取反对称准备，两边缘为球心；任取 $a\ne\pm b$，两个原同向产品零成立，且 $e_a(m_1)=e_{-b}(m_1)=1/2$。无需制备该静态态的额外过程假设。与其余候选的等价由306.3。$\square$

**命题 307.5（旧比较不能在删去第三零后原样保留）。** 在标准 $n\ge3$ 的复量子模型内，存在二维支持真面球 $B$、同一原 $\omega$ 及正交单位 $a,b$，使两个同向零及305式在 $b$ 处的同向对径比较成立，但同一 $\omega$ 没有第三个不同方向的同向产品零；307.1的新跨方向比较不成立。

证明。在 $B$ 中取 $\omega=p_{-a}\otimes p_{-b}$、$a\cdot b=0$。两边缘都在 $B$，两个指定同向零成立，第一边缘给 $e_b(m_1)=e_{-b}(m_1)=1/2$。对任意单位方向 $x$，

$$
(e_x\otimes e_x)(\omega)
=\frac{(1-a\cdot x)(1-b\cdot x)}4.
\tag{307.14}
$$

非负因子只在 $x=a$ 或 $x=b$ 为零，故没有第三方向。新比较却要求 $0=e_a(m_1)\ge e_{-b}(m_1)=1/2$，确实失败；(307.11)的补对角读数为 $1/2$。这是区分同一见证上两种比较的反例，不是完整候选存在断言的非量子反模型。若允许 $b=-a$，不等权混合 $t\,p_a\otimes p_{-a}+(1-t)p_{-a}\otimes p_a$、$0<t<1,t\ne1/2$ 满足两零及退化的跨方向比较，却只有一条直径、边缘非球心；所以非对径限定不能从307.3中删去。$\square$

**命题 307.6（更简几何、反事实与量子结构）。** 此候选的几何见证是两条不同直径的原条件读数换位，第三接触由一个一体边缘比较补出。它以较低阶原读数替换一个显列双体零，仍保留完整有限背景及原确认关系。

证明与范围。一个同向零使对应原正条件向量只能落在唯一对径点，两个零使同一个交叉联合读数从两侧计算时交换边缘概率；原least又给合法正余门。由此得到跨阶恒等式(307.11)：一体边缘读数差恰等于同一准备的一只补对角联合概率。比较与正性把这项共同余量压到零，才产生第三大圆接触。没有以新的谓词直接定义第三零，也没有把球内互补式强加到全原菜单。

在已经证明的两零结构中，新比较确与补对角零等价；因此减少的是显列的双体零数目及见证阶次，不是已证的逻辑独立信息减少。删比较时307.5即留下正补读数，删非对径限定时其不等权混合即留下偏心边缘；这两者都是对所指同见证结论的精确反例。边界Link、球内双边缘、实际L2、整个原菜单、全相关旁观min/max、非Bin的Jordan／复类型、M-only、双预算及全有限传播供应均保留。完整模型类仍由等价定理识别，不申领严格弱化、最少独立公理或全球原创。

原实际面条件向量、球上仿射极值及非负质量分解是成熟中间工具；单零校准沿280.2的(280.8)条件态下界，least与补门的原序比较沿299.2及304。新增repo-derived接合是(307.9)—(307.11)的两零交叉换位、原正余门消失及低阶比较补零，再与306的真面二分和既有全有限链结合。不将全部ensemble的steering、面投影或测量更新从这两个特定条件分解中读出。结论为条件纸面理论，非Lean核验。

(307.13)使同一原归一底及极点成为密度矩阵和复纯射线，完整逆对偶和原配对给 $0\preceq E\preceq I$ 及Born迹概率，全部有限单位分解给数学POVM并包含投影型PVM。原产品、重括号、正置换与单位丢弃给同一复张量及矩阵部分迹。过程字典保持306.4的条件：CP／Kraus须指定映射在全部有限相关旁观者上保正，TNI／TP及仪器须全输入和合计分支预算，实际事件另需供应；Lüders须锐效应及yes支持中性，酉动力学须指定连续可逆保单位且全旁观保正的群。物理钟、能量、$\hbar$ 及无限极限均未由这项静态比较给出。

白话：仍在同一张实际球里，看同一份双份准备的左右两张影子，但只先要求两个不同、也不对径的方向都不会“左右同时说是”。每个零都把对应的条件影子压到唯一的对面；于是同一个交叉读数，无论先从左边还是右边算，都会交换两张影子上的概率。再要求第一张影子在方向 $a$ 的读数不低于另一方向的对面 $-b$。原正余门和两零关系却告诉我们，这个差的相反数正好是一项联合概率：它既不能负，又被比较压成非正，只能为零。因此原来同一份准备自动补出第三个大圆零，两张影子也落到球心。最小整体球仍按306直接重建，嵌在更大单体里的小球才需要这两个零和一次跨方向比较；边界确认关系与完整传播条件不变，后续证明给全部有限量子静态结构。$\square$

## 追加锚（本行以下为增补区）

## 308. 两只原帽的单位预算正规式，以及小角替身在六份中的失败

**定义 308.1（不用预先指定对径点的原读数正规式）。** 保留307.1的完整强全有限背景、原边界选择族、固定原纯旁观者 $b_*$、$\mathsf{Link}(\mathcal F^\partial_{b_*})$、实际 $\mathrm{L2}_1$ 及全部具名供应，仍先由Link取得M1。定义 $\mathsf G^{\Sigma,\rm prop}_{2,1}$：每张实际二纯真面球 $B\ne K_1$ 内都存在不同原纯点 $p,q$ 和同一个原 $\omega\in K_2$，满足

$$
\begin{aligned}
e_p(q)&>0,\qquad m_1=\pi_1\omega\in B,\quad m_2=\pi_2\omega\in B,\\
(e_p\otimes e_p)(\omega)&=(e_q\otimes e_q)(\omega)=0,\\
(e_p+e_q)(m_1)&\ge1.
\end{aligned}
\tag{308.1}
$$

这里直接使用两个原纯点、它们的全原least和同一原边缘；不在原始关系中指定球坐标或第三个对径点。$e_p+e_q$ 不被宣称为原proper效应，最后一行只是两只已有原帽在同一原态上的读数和。完整候选写为

$$
\boxed{\quad
\mathsf Q^{\Sigma}_\partial(b_*)=
\mathsf{Link}(\mathcal F^\partial_{b_*})+
\mathrm{L2}_1+\mathsf G^{\Sigma,\rm prop}_{2,1}.
\quad}
\tag{308.2}
$$

**定理 308.2（预算正规式仍为完整候选）。** 在308.1保留的同一完整背景及供应下，$\mathsf Q^{\Sigma}_\partial(b_*)$ 与307.1的 $\mathsf Q^{\times}_\partial(b_*)$、306.1及其前述完整候选、全部有限复PSD重建等价：存在同一保单位实线性序同构 $\theta$ 及 $n\ge2$，使

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{308.3}
$$

证明。只为推导选球坐标 $p=p_a,q=p_b$。两个原零按307.2先校准这两只帽及其对径帽。此时 $p\ne q$ 给 $a\ne b$，而 $e_p(q)=(1+a\cdot b)/2>0$ 给 $a\ne-b$。307.7的原正余门在 $m_1\in B$ 上为零，故

$$
e_{p_{-b}}(m_1)=1-e_q(m_1),\qquad
(e_p+e_q)(m_1)\ge1
\ \Longleftrightarrow\ e_p(m_1)\ge e_{p_{-b}}(m_1).
\tag{308.4}
$$

这正是307.1的跨方向比较；反向也由同一已付校准成立。因此逐球使用同一原见证，几何条件等价。307.4给完整正向、反向及全部有限量词；Bin分支仍按306.2，不索取(308.1)。

在两零条件下，307.11还将末行精确锁成饱和预算：

$$
0\le(e_{p_{-a}}\otimes e_{p_{-a}})(\omega)
=1-e_p(m_1)-e_q(m_1)\le0.
\tag{308.5}
$$

所以第三大圆零及双边缘球心仍是后果。重建后的归一底、纯点、逆对偶及原配对给密度矩阵、复射线、Born迹读数、全部数学POVM及其中PVM；原乘积、置换、重括号与丢弃给同一复张量及偏迹。CP／Kraus、数学仪器、Lüders和酉动力学继续保留307.6的全旁观正性、全输入及分支预算、事件供应、中性或连续群等各自条件。此正规式只减少原始几何表述中需要指名的对象，不将(308.4)的等价改写计为独立信息或新增一般定理。$\square$

**命题 308.3（完整量子小角不能单独供应全原least）。** 对任意 $n>k\ge2$，存在同一整个三层矩阵载体上的原锥及完整原菜单，使 $C_1=\operatorname{PSD}_n,C_2=\operatorname{PSD}_{n^2}$，总层数至多三的全部分割min/max、正置换及逆、正丢弃、一体合同在此三层域内的全部旁观提升均成立。任意三张 $k$ 维局域支持上的整个三份角都是完整PSD，正交压缩原正且不增迹，全部内在proper均能零延拓为原proper；但302.10的实际来源 $q_k$ 的归一投影没有全原least确认效应。

证明。（一）整个三层模型。令 $K\subseteq H_{n^3}$ 为下列归一投影的闭凸锥：

$$
K=C_3=\operatorname{cone}\{P_\xi:\ \|\xi\|=1,\quad
\xi\text{ 跨某个一腿割二可分，或其三项一腿Schmidt秩均不超过 }k\}.
\tag{308.6}
$$

生成点集合紧，归一迹均为一，故其凸包紧，锥闭；包含全部完全乘积纯投影使其生成整个原实载体，$K\subseteq\operatorname{PSD}$ 使其尖，普通迹严格正。使用整个原基、全部原纯点、完整 $K^*$ 和整个 $[0,I]_{K^*}$，有限菜单为全部有限单位分解。

每个 $1|2$ 分割的全部二可分PSD都已加入，故满足该割min；$K\subseteq\operatorname{PSD}$ 给该割max，三个实际分割同时成立。原置换保持生成条件，矩阵偏迹落在完整低层PSD。一体合同不增加任何一腿Schmidt秩，也保持二可分性，故在此三层域内的所有作用位置原正；收缩合同不增迹。

取任意局域 $k$ 维支持 $S_1,S_2,S_3$。其中全部纯投影都在(308.6)，而原锥包含于PSD，故整个支持角恰为 $\operatorname{PSD}(S_1\otimes S_2\otimes S_3)$。相应正交压缩 $\Pi$ 为已付一体合同之积，映 $K$ 到这个完整角。内在proper $f$ 的零延拓 $f\circ\Pi$ 原正，且 $u-f\circ\Pi=(u-u\circ\Pi)+(u\circ\Pi-f\circ\Pi)$ 原正，遂为全原proper。尤其实际L2及308.1的双份几何关系均由低层PSD满足；这里没有补入原边界Link。

（二）直接选实际升维来源。沿302.10取

$$
\begin{aligned}
I_k&=\sum_{i<k}E_{ii},\qquad Q_k=kE_{00}+E_{0k}-I_k,\\
b_k&=k^2-k+1,\qquad
\chi=|Q_k\rangle\!\rangle/\sqrt{b_k},\qquad q=\chi\otimes|0\rangle.
\end{aligned}
\tag{308.7}
$$

$\chi$ 的非零Schmidt系数为 $\sqrt{(k-1)^2+1}/\sqrt{b_k}$ 及 $k-1$ 个 $1/\sqrt{b_k}$。分别在它两边Schmidt支撑外选实单位 $r,s$，这是 $k<n$ 所允许的。取

$$
z=r\otimes s\otimes|1\rangle,\qquad
0<t\le1/\sqrt{b_k},\qquad h=q+tz,\qquad F=|h\rangle\langle h|.
\tag{308.8}
$$

$F$ 是未归一dyad，$\operatorname{Tr}F=1+t^2$，不是本卷约定的归一 $P_h$。$P_q$ 是原纯准备及原proper：它在完整角内，且自身与普通补投影都为PSD，故属于 $K^*$ 的完整区间。

（三）另一只原proper确认门。$F\succeq0$ 先给 $F\in K^*$。跨控制割，$h$ 的Schmidt系数平方为 $1,t^2$；跨任一数据割，为 $\chi$ 的 $k$ 项系数平方再加 $t^2$。各割最大项均不超过一，故对每个二可分单位生成向量 $\xi$ 有 $|\langle h,\xi\rangle|^2\le1$。若 $\xi$ 的三项局域秩均至多 $k$，沿第一数据割用Schmidt截断和Cauchy–Schwarz，得

$$
|\langle h,\xi\rangle|^2
\le\sum_{j=1}^k s_j(h)^2=1,
\tag{308.9}
$$

因为 $t$ 不大于 $\chi$ 的最小非零系数。此界也可由把矩阵 $h$ 投影到 $\xi$ 的至多 $k$ 维左支撑，再用HS Cauchy–Schwarz及最大 $k$ 个奇异值平方和得到。故 $I-F\in K^*$，$F$ 确为整个原proper，且 $F(P_q)=1$。

取同一原二可分单位向量

$$
x=\frac{(\chi+r\otimes s)\otimes(t|0\rangle-|1\rangle)}{\sqrt{2(1+t^2)}}.
\tag{308.10}
$$

它的数据双块可以有秩 $k+1$，但 $C_2$ 已是完整PSD，所以它仍是原合法二可分准备。直接计算给

$$
F(P_x)=0,\qquad
\operatorname{Tr}(P_qP_x)=\frac{t^2}{2(1+t^2)}>0.
\tag{308.11}
$$

所以 $F-P_q\notin K^*$。

这也排除任何别的全原least。若 $L$ 是该目标的least，则 $L\le P_q$，而 $K^*\subseteq\operatorname{BP}((12)|3)$。双块乘积rank-one投影 $P_q$ 是这个BP锥的极端射线：支配于 $P_q$ 的两个块正项在控制腿 $|0\rangle^\perp$ 上均为零，块正小角消去交叉块，剩余数据矩阵受普通rank-one正投影支配，故只能是其非负倍数。因此 $L=cP_q$；确认迫 $c=1$，又与(308.11)矛盾。这里也可直接复用272.2的局域完整M及所选产品目标least因子化。相同极端射线论证加原态 $P_q$ 上的proper预算，还说明 $P_q$ 本身是整个原proper区间极点；反例没有通过丢弃极端性或缩小菜单制造缺口。$\square$

**命题 308.4（该三层替身必在六份复制中失败）。** 任何保留308.6整个 $K$ 及其完整对偶菜单、低二层PSD的模型，都不能延拓成满足所有有限分块min/max的完整背景 $\mathsf F$。

证明。构造全实，令 $G=I-F\in K^*$。三张低二层原Bell准备的产品经正置换成为

$$
\Phi_{n^3}=\frac1{\sqrt{n^3}}\sum_{i,j,l=0}^{n-1}|ijl\rangle\otimes|ijl\rangle.
\tag{308.12}
$$

任何所指延拓的min必须接纳 $P_{\Phi_{n^3}}\in C_6$；同一个延拓在 $3|3$ 割的max又要求原正效应 $F\otimes G$ 对其读数非负。但普通迹配对直接给

$$
(F\otimes G)(P_{\Phi_{n^3}})
=\frac{\operatorname{Tr}(F^{\mathsf T}G)}{n^3}
=\frac{(1+t^2)-(1+t^2)^2}{n^3}
=-\frac{t^2(1+t^2)}{n^3}<0.
\tag{308.13}
$$

转置只出现在同一实际Bell配对的矩阵恒等式中，未被当成原正操作。矛盾在六层的一个明确原态与一个明确原产品正效应上发生，故不存在保留这些完整三层数据的全有限延拓。$\square$

**命题 308.5（简洁表示与未被删除的整体条件）。** 308.1是307完整候选的两帽预算正规式；308.3—308.4表明，试图以“小角已经完整”为由删除升维来源的全原least时，三层数据并不足够，而全部复制中的关系相容性又严格排除该局部替身。

证明与范围。(308.1)只指名两个原纯点及其原读数，不把对径构造作为输入；(308.4)给其完整等价边界。反例中连整个低二层、全部旋转小角、原菜单和三层一体合同都已保留，仍有合法确认门 $F$ 不含 $P_q$。因此“角内least”不能直接升格为“全原least”。六层反证却说明该局部构造不满足完整 $\mathsf F$，所以它不证明边界Link相对全部原前件逻辑独立，也不证明全有限背景不能自行供应该来源。本条没有删去边界族、全有限分块关系、Jordan／复类型、M-only、双预算或传播供应；是否能利用尚未消费的更高相容性真正删源，仍是具体未证问题。

Schmidt截断及投影型见证是成熟工具。[Q308Witness]式(28)—(29)与(70)—(71)用最大重叠及各二分Schmidt系数构造二体、多体纠缠见证；(308.9)只将相同重叠界用于指定局域秩截断，未将见证方法另领为新理论。原产品least因子化沿272.2，实际来源矩阵沿302.10。新增repo-derived承重是对每个实际 $q_k$ 的完整三层锥、全原proper确认门与显式测试点，以及同一数据在六份中必然出现的负读数；预算候选的等价写法仅作几何说明，不算新的独立数学信息，不申领全球原创。

白话：完整候选可以先只看两只原最低帽：它们各自在同一双份准备上同向不响，又对第一张影子合起来至少读到一个单位。两个零本来就让这笔总账不能超过一，于是它必须恰好为一，第三个大圆零随之长出，不必先把对径点写进规则。还要分清“小角里有最低门”和“整个世界里都有这个最低门”：反例把每个小角都做成完整量子体，却仍造出另一只合法门，它认得同一升维准备，却不包含那只角内最低门。这个替身也不能冒充完整世界——把三张Bell对接成六份，同样两只原正门会读出明确负数。缺口因此落在小角与整体复制的相容关系上；只有补出这一桥，才可以真的删去来源条件。$\square$

[Q308Witness]: https://arxiv.org/abs/0811.2803v3 "Gühne–Tóth，Entanglement detection，式(28)—(29)、(70)—(71)；投影型纠缠见证及跨二分的最大Schmidt重叠界。"

## 追加锚（本行以下为增补区）

## 309. 只借一张固定球：产品最低门支付坐标压缩与满维种子

**定义 309.1（固定一球的原来源候选）。** 完整保留308.1的强全有限背景 $\mathsf F$：所有有限实张量载体、整个闭尖生成锥、严格正乘积单位、整个归一底与全部原纯点、完整正对偶及proper区间、全部有限单位分解，原产品、正置换及逆、规范重括号、正丢弃，以及每个有限分块对全部相关原输入的min/max。单体采用277.1的 $\mathrm{L2}^{\mathrm{exp}}_1$：任意不同原纯点 $p,q$ 的整个最小实际面 $B(p,q)$ 是非退化仿射闭三球，且存在全原proper效应 $h$，使 $\{x\in K_1:h(x)=1\}=B(p,q)$；整底为球时允许 $h=u_1$。

固定任意不同 $p_*,q_*\in P_1$，置 $B_*=B(p_*,q_*)$，另固定任意原纯旁观者 $b_*\in P_1$。只选原双份纯点

$$
\Sigma_*=
\{p\otimes q:p,q\in P_1\}
\ \cup\ \{a\in P_2:\pi_1a\in B_*,\ \pi_2a\in B_*\}.
\tag{309.1}
$$

对每个 $a\in\Sigma_*$，在三份目标 $\{a\otimes b_*\}$ 上使用296.1的原 $\mathsf{Link}$：每个原极端确认上门严格下方的原极端确认者可比图为空或连通，排除上门而保留最低点，路径有限，整个图不必有限。所有确认和序比较仍作用于整个原三份菜单及全部原相关输入。记该固定目标族为 $\mathcal F^*_{b_*}$，完整候选为

$$
\boxed{\quad \mathsf Q_*(B_*;b_*)
=\mathrm{L2}^{\mathrm{exp}}_1+\mathsf{Link}(\mathcal F^*_{b_*}).\quad}
\tag{309.2}
$$

保留具名M加数值互易的单体Jordan／复类型桥、[XIX274.3]的 $2\times2$ M-only特例、Gurvits—Barnum[GB271]的二体HS预算及302.2—302.3的双HS／迹接口、XIII165.9的全有限传播。XIII166.5的完整角继承只在取得完整二维角时消费一次。此处没有双份接触方向、零读数或边缘比较输入；单体球的原暴露性是明列前件。

**定理 309.2（外部基点的全原least迫使支撑压缩正）。** 设 $D\subseteq\operatorname{Herm}_d$ 是闭尖生成原态锥，迹严格正，$K$ 为整个迹一底，使用完整对偶及proper菜单。某正交单位基的每个投影 $P_i$ 均为原态，且其全原least确认效应就是 $P_i$。取非空基子集的投影和 $h$，置 $K_h=\{Y\in K:\operatorname{Tr}(hY)=1\}$。若对某有限 $c>0$，

$$
\|hXh\|_2\le c\operatorname{Tr}(hX)\quad(X\in D),
\qquad Y=hYh\quad(Y\in K_h),
\tag{309.3}
$$

则矩阵压缩 $\Pi_h:X\mapsto hXh$ 同时保持 $D,D^*$，并对原态不增迹。

证明。$h$ 与 $I-h$ 是原正效应之和，故 $h$ proper，$K_h$ 非空紧。取非零 $f=hfh\in D^*$，令 $t=\max_K\operatorname{Tr}(fY)>0$。$I-f/t$ 为原proper，且确认 $h$ 外的全部基点。逐只扣去这些基点的全原least $P_i$：先前扣去的投影在下一基点上为零，所以每一步仍确认下一点；leastness保证减后仍原正。最终

$$
h-f/t\in D^*,\qquad
 t=\max_{Y\in K_h}\operatorname{Tr}(fY).
\tag{309.4}
$$

第二式因任一 $f$ 的最大点满足 $1\le\operatorname{Tr}(hY)\le1$ 而成立；不假设普通PSD序支配。对任意 $g=hgh\in\operatorname{Herm}_d$，取 $\lambda>c\|g\|_2$。式(309.3)及HS Cauchy—Schwarz使 $f=g+\lambda h$ 在整个 $D$ 上正且非零。将其代入(309.4)，用 $K_h$ 上的 $\operatorname{Tr}(hY)=1$ 消去 $\lambda$，得

$$
\operatorname{Tr}(g\,hXh)
\le\operatorname{Tr}(hX)\max_{Y\in K_h}\operatorname{Tr}(gY)
\quad(X\in D).
\tag{309.5}
$$

若 $\operatorname{Tr}(hX)=0$，(309.3)给 $hXh=0$；否则，由全部受支撑 $g$ 的分离不等式及 $K_h\subseteq\{Y=hYh\}$，得 $hXh/\operatorname{Tr}(hX)\in K_h$。这证明态侧压缩正。压缩对迹配对自伴，故效应侧也正；$0\le h\le I$ 给不增迹。此结论只在给定原层上成立，不将其自动升级为全旁观正性。$\square$

**定理 309.3（一张固定方角补齐整个双份锥）。** 在309.1的同一完整背景及单体、$2\times2$具名供应下，存在同一个保单位坐标 $\theta:V\to\operatorname{Herm}_n$、$n\ge2$，使

$$
\theta C_1=\operatorname{PSD}_n,\qquad
\theta^{\otimes2}C_2=T_2^\varepsilon\operatorname{PSD}_{n^2},
\qquad \varepsilon\in\{0,1\}.
\tag{309.6}
$$

证明。（一）先付单体和产品门。296.2逐个给所选三份目标的全原least。沿 $x\mapsto x\otimes b_*$ 限制，并与全部 $f\otimes u_1$ 比较，给每个所选双份点的least；包含全部双份纯产品，再限制一次即给完整M1。272.2只消费两侧M1及当前产品目标least，故 $e_{p\otimes q}=e_p\otimes e_q$。277.2—277.3在实际暴露三球上排除塌缩并给半球刻度及全单体数值互易；此时才消费具名Jordan／复类型桥，取得 $C_1=\operatorname{PSD}_n,u_1=\operatorname{Tr},e_p=P_p$ 的同一坐标。整底为球时也可直接用306.2的Pauli坐标。以下在此坐标工作。

（二）先证明双份矩形压缩。$C_2,C_2^*$ 均夹于标准Sep与BP之间。取任意单腿支持 $S$、$h=P_S\otimes I$，采用适配的完整产品正交基，其每个产品投影已有全原least。对 $X\in C_2$，$hXh$ 在 $S\otimes\mathbb C^n$ 上块正，Gurvits—Barnum[GB271, §III Theorem1]的未归一二体可分HS半径一给

$$
\|hXh\|_2\le\operatorname{Tr}(hX).
\tag{309.7}
$$

若原 $Y\in K_2$ 满足 $\operatorname{Tr}(hY)=1$，其第一边缘在 $S^\perp$ 的正压缩迹为零，故为零。对第二腿任意向量 $v$ 切片，第一腿条件矩阵为PSD，在 $S^\perp$ 上的对角块为零，PSD消去相连行列；再对 $v$ 极化，得 $Y=hYh$。309.2因而给两侧原正压缩。第二腿同理，复合即得

$$
\Pi_{S,T}(X)=(P_S\otimes P_T)X(P_S\otimes P_T)
\tag{309.8}
$$

保持 $C_2,C_2^*$ 并不增迹。到这里仅取得双份正性，没有借原酉或高阶矩阵过程。

（三）只分类一张 $2\times2$ 角。$B_*=\mathcal D(S_*)$，$\dim S_*=2$。由上步的饱和支撑证明，$\Pi_{S_*,S_*}(C_2)$ 恰为双边缘同落 $B_*$ 的整个原面锥。面纯点是原纯点，故全部已在(309.1)中；内在proper沿(309.8)拉回仍为原proper，因为其正补为 $(u-u\Pi)+(u\Pi-f\Pi)$。所选least限制后遂为完整内在菜单的least。该角具有整载体、迹单位、Sep/BP界及完整M；准确调用[XIX274.3, (274.9)—(274.11)]的 $2\times2$ 特例，得它为PSD或 $T_2\mathrm{PSD}$。角内全部正效应也能零延拓。

固定此方向 $\varepsilon$。任取二维目标支持 $T$，选 $S_*,T$ 的主向量基 $s_i,t_i$，使 $\langle t_i,s_j\rangle=\delta_{ij}c_i$、$c_i\ge0$。$L=\operatorname{span}\{s_1+t_1,s_2+t_2\}$ 满足

$$
P_TP_LP_{S_*}s_i=(1+c_i)t_i/2.
\tag{309.9}
$$

两系数均严格正，所以此有限投影串在源、目标支持间可逆，包括直角情形。两腿分别使用(309.8)，态侧和效应侧都原正；对任意目标向量，先在这两个可逆限制下取源角原像，即能运输其dyad。转置方向在第二腿相应使用共轭映射、共轭目标支持，仍遍及全部目标。故置 $D=T_2^\varepsilon C_2$ 后，所有Schmidt秩至多二的投影均属于 $D\cap D^*$；未使用投影串的正逆。

（四）一次相关压缩补全全部秩。$D$ 中每个产品投影的全原least仍为自身。任取两组局部正交向量 $a_i,b_i$，令 $W=\operatorname{span}\{a_i\otimes b_i\}$、$h=P_W$，将这些向量补为完整产品基。上步的秩二正效应使任意 $X\in D$ 在该基的每个二阶主块均PSD。因此其矩阵元满足

$$
|X_{ij}|^2\le X_{ii}X_{jj},\quad X_{ii}\ge0,
\qquad \|hXh\|_2\le\operatorname{Tr}(hX).
\tag{309.10}
$$

若 $Y\in K_D$ 在 $h$ 上取一，外部非负对角元之和为零；二阶不等式消去外部每行每列，得 $Y=hYh$。309.2给此相关子空间压缩在 $D,D^*$ 中正。对任意Schmidt向量 $\psi=\sum_i d_i a_i\otimes b_i$，取实际产品向量 $z=(\sum_i d_i a_i)\otimes(\sum_i b_i)$，则 $zz^*\in D\cap D^*$、$hz=\psi$。所以全部 $\psi\psi^*\in D\cap D^*$；谱分解和PSD自对偶给 $D=D^*=\operatorname{PSD}_{n^2}$，即(309.6)。此时才得到完整M2，无需向高Schmidt秩原点预借least。$\square$

**定理 309.4（三份坐标压缩直接产生满维种子）。** 在309.1的同一完整背景和传播供应下，$\varepsilon=0$，且对每个有限 $N\ge0$，

$$
\theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{309.11}
$$

证明。（一）低二层之后才用一体全旁观运输。抽取302.2的实际杯帽证明：标准方向使用XIII165.3；镜像方向使用(302.4)—(302.5)的交换杯帽。两者只消费(309.6)及完整原min/max，故支付所有一体合同的全有限相关旁观正性，酉及逆保单位。固定 $b_*$ 的least可由此运输到任意孤立原纯腿，正置换及逆运输分割。

取实计算基使 $S_*=\operatorname{span}\{0,1\}$。七点(302.6)中 $u_1,u_2,u_3$ 的双份块都在这张固定 $S_*\otimes S_*$；$u_4,\ldots,u_7$ 及角外补基点全为产品，故所需固定纤维least全部由(309.1)支付。对这些目标 $X$，原产品proper上界和双HS／迹沿306.6给

$$
1=\operatorname{Tr}(e_XX)\le\|e_X\|_2\|X\|_2
=\|e_X\|_2\le\operatorname{Tr}e_X\le\operatorname{Tr}X=1,
\tag{309.12}
$$

因而 $e_X=X$。这里双预算在实际标准或转置的 $2|1$ 分割中成立，不把普通三体HS界免费加入。全部三份产品投影也由同一运输取得全原least。

现可逐项复用302.3的局部原序证明，而非调用其带三零的完整候选：从极端单位门扣除这七只跨割正交门及角外基点，镜像方向留下(302.8)的同一原余态；同一原产品proper效应(302.9)读出 $-1/6$，违背max。故 $\varepsilon=0$。标准方向的同一逐只减法留下实际原 $P_w$，$w=(100+010+001)/\sqrt3$；其三秩为 $(2,2,2)$。

（二）只继承一次完整二维层级。由已付的一体合同，$\Pi_{2,N}=\operatorname{Ad}_{P_{S_*}}^{\otimes N}$ 对全部原相关输入正且不增迹。XIII166.5的压缩像、交角、完整对偶及proper零延拓于是给尺寸二的整个全有限模型。低二层为PSD，$w$ 满足XIII165.2，所以在此二维模型中准确调用165.9，取得所有有限角 $\operatorname{PSD}_{2^N}$。独立一体酉及其逆再把三份角送到任意三张局部二维支持；各角全部正效应都能原正零延拓。

（三）全产品least给需要的相关三份压缩。任取完整三腿产品正交基。任意两只基向量 $v_i,v_j$ 的叠加 $\alpha v_i+\beta v_j$ 逐腿支撑至多二维，所以其dyad由上步属于全原 $C_3^*$。于是对每个 $X\in C_3$，该产品基上全部二阶主块PSD。式(309.10)及零行列证明适用于任意非空基子集，309.2遂给对应坐标压缩在 $C_3,C_3^*$ 上正。这个三份结论没有先假定相关压缩的全旁观正性。

现在只取

$$
\mathcal I=\{(i,i,0):0\le i<n\}\cup\{(0,0,1)\},\qquad
h=P_{\operatorname{span}\{|ijk\rangle:(i,j,k)\in\mathcal I\}}.
\tag{309.13}
$$

令 $s=\sum_{i<n}|i\rangle$、$z=s\otimes s\otimes(|0\rangle+|1\rangle)$。原产品 $zz^*\in C_3$，刚证明的原正压缩给

$$
hzz^*h=\psi\psi^*\in C_3,\qquad
\psi=\sum_{i<n}|ii0\rangle+|001\rangle
=|I_n\rangle\!\rangle|0\rangle+|E_{00}\rangle\!\rangle|1\rangle.
\tag{309.14}
$$

$\operatorname{Tr}(\psi\psi^*)=n+1$，可以归一成原准备；不需预认它为原纯点。$I_n,E_{00}$ 独立、像之和为整个 $\mathbb C^n$、共同核为零，三展平秩为 $(n,n,2)$。完整标准低二层、原全有限背景和这只实际dyad准确满足XIII165.1—165.2；165.9直接给(309.11)。没有任何 $k\to k+1$ 升阶，也未向 $q_k,u_k$ 或最终种子借least。$\square$

**定理 309.5（反向、来源收缩及原量子字典）。** 相对于309.1明列的同一背景和供应，$\mathsf Q_*(B_*;b_*)$ 与(309.11)等价；反向对任意固定球和纯旁观者成立。

证明与范围。在完整复PSD层级中，两个不同纯点的最小实际面是复二维支持的完整密度球，其支持投影为全原proper并恰暴露该球。每个所选三份纯目标的支持投影是完整菜单least，296.2反向给Link。这证明完整反向，并使原三零、两零预算及全部 $q_k,u_k$ 的least均成为后果。

若在同一 $\mathrm{L2}^{\mathrm{exp}}_1$ 背景中比较初始来源，$n\ge3$ 时 $\Sigma_*\subsetneq\Sigma_\partial$。例如取 $B_*=\mathcal D(\operatorname{span}\{0,1\})$，原双份纯点 $P_{(|0,1\rangle+|1,2\rangle)/\sqrt2}$ 的第一边缘未满，属旧边界族；它不是产品，第二边缘又不在 $B_*$，故不属新族。任意固定球可在标准模型中取适配基得到同类例子。$n=2$ 时 $B_*=K_1$，准确回退为全 $P_2$。此为同一量子模型中的来源清单严格收缩，不是完整候选模型类严格扩张。

本条以已有的单体暴露几何替代307—308的裸L2及双份接触见证，是明确的条件交换；没有从裸L2、产品least或完整 $\mathsf F$ 推出一般维数的原球暴露性。删除暴露性后，277.6的单体刻度／互易桥仍缺；删除固定方角中非产品来源后，309.3（三）的内在完整M仍缺；只保留角内least而删除外部全产品基点的全原least，则(309.4)的逐只扣门不再有依据。308的三层替身表明小角完整不能代付这一全原比较。完整全有限分块、原菜单、单体Jordan／复类型和传播供应继续保留；一般矩形M-only整锥、每张球的双份见证及逐维来源供应退出本证明。

(309.11)将原归一底、纯域、完整逆对偶proper菜单和配对分别识别为密度矩阵、复射线、$0\preceq E\preceq I$ 及Born迹概率；全部有限单位分解给数学POVM，锐正交分解给PVM。原产品、置换、重括号和丢弃给同一复张量及偏迹。指定分支的全部有限相关旁观正性才给CP／Kraus，全正输入及分支总质量预算才给TNI／TP和数学仪器；设备事件供应、锐事件整个yes支持中性、连续可逆保单位动力学及物理时间／能量标定仍各保留其前件，不从静态锥等式选择Lüders或物理哈密顿量。

Gurvits—Barnum[GB271]§III Theorem1及其对偶HS界、有限维凸分离、主角和正交投影运算是成熟工具。Oi[Q309Projection]式(2)—(4)在已给Hilbert模型中研究有限投影串及子空间变换，不提供未知原锥上的正性；(309.3)—(309.8)在使用投影串前另付此义务。单体暴露球刻度沿277.2—277.3，产品因子化沿272.2，七点及双预算沿302.2—302.3，完整角与传播沿XIII166.5、165.9。新增接合是基点least的支撑最大值原序不等式、其两类可验证压缩接口、固定一球来源到全部双份方向，以及一次产品压缩产生满维三份种子；不申领成熟工具的发明或全球优先性。

白话：先只选一张能由原门筛出的二纯小球，把非产品的最低门集中借在这张球上，其余只借全产品点的最低门。一只门若完全不看外面的产品基点，就从它的补门里把这些外部基点逐个扣掉；最低性保证每次都合法，最后迫使这只门的最大读数落在留下的支撑内。对所有门都成立，就证明“只留下这些坐标”确实保持原准备合法。先在双份搬运这一张小球，恢复任意纠缠方向；再在三份只留所有 $ii0$ 和一个 $001$，一份普通产品准备就长成满维三体种子，不必每升一维再借新门。简洁之处是用同一条外部扣门关系替代反复升阶；仍须明确保留小球可被原门筛出这一条件，不能把它说成已经无条件内生。$\square$

[XIX274.3]: QUANTUM_ORIGIN_QUBIT_COMMON_RULER_AND_PRODUCT_ZERO_FACES_XIX.md "274.3，式(274.9)—(274.11)：M-only二体秩二方向；此处仅消费2×2全秩二特例。"
[Q309Projection]: https://arxiv.org/abs/1402.1104v3 "Daniel K. L. Oi，Unitary Holonomies by Direct Degenerate Projections，式(2)—(4)：已给Hilbert空间中的投影串；不供应未知原锥正性。"

## 追加锚（本行以下为增补区）
