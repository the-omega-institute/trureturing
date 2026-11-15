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
| 另给投影效应及整个 certain-yes 支持上的逐点中性 | 唯一锐更新 $X\mapsto PXP$ |
| 另给连续可逆保锥保单位的一参数群 | 酉共轭及 Hamilton 生成元形式；物理钟、能量与 $\hbar$ 的标定仍另给 |

证明与范围。273.3已经供应270.13的整个实际矩阵锥、单位、配对和张量坐标，故逐项代入该既有字典；各过程行只在同一行所列的额外前提下成立。无限维、无限张量极限、近似稳定性、设备实现和资源成本仍无新增结论。数值互易只交换同一比较的两个纯端点，不改变两个有序仪器的状态更新；270.7已有非正交 qubit 测量的不同先后概率反例。

本节新增的 repo-derived 接合是从每张实际球的四个原纯锚与两种**全体**换位，恢复内禀正四面体及同一全体协方差尺下的逐面圆性，再接到270的任意原维数全有限供应。有限置换群 $A_4$、不变二次型的有限维刚性、仿射球的中心与体积换元、Bloch 旋转的酉提升都是成熟中间工具；不将它们另领为新一般定理。关于对称与量子重建的成熟先例，[Müller—Ududec，Theorem 1及其bit symmetry定义][M273]使用有序可区分纯对的群传递性；本节未调用该定理，也未从两张映射直接申领它的自对偶结论。关于共同尺和完整重建的实际供应分别是[C273]与270.12—270.13，不将有限置换替换整个全域合同。不主张本入口相对 $\mathsf M_3+\mathrm{L2}$ 更弱、严格独立、全球最少或具有文献优先权；$\mathsf M_3+\mathrm{L2}$ 能否在任意原维数自行供应共同尺，仍未由本节解决。

白话说，每两个不同的纯准备真正撑起一整颗三维球。在每颗球上，只挑四个不同的纯准备：前三个轮换、第四个不动；再让两对准备同时互换。要求这两种换位都能放回整个系统，所有原混合关系仍成立。四点于是自动变成不共面的正四面体，各颗球也被同一把从整体定义的尺量圆，不必先输入这把尺或逐方向输入连续旋转。保持原来全部有限复合和完整测试背景，已有重建才把它接成全部密度态、Born 读数、张量积与纠缠；实际更新、仪器和物理时间仍各有自己的条件。$\square$

[C273]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "200.1、(200.5)—(200.6)：整个原体的协方差尺及仿射自然性。"
[F273]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "250.1的强全有限原域；273.3完整保留其条件。"
[M273]: ../../../Library/QuantumStates/mullerududec2012selfduality.md "Müller—Ududec，The structure of reversible computation determines the self-duality of quantum theory，Theorem 1；有序可区分纯对的bit symmetry及其条件边界。"

## 追加锚（本行以下为增补区）
