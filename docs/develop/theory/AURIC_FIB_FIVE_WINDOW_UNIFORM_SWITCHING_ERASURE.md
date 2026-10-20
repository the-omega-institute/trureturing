# AURIC FIB 五窗口一致切换遗忘

> 本卷是独立的数学参考卷，采用普通 `generic-v1` 结构。参数可在每个字母独立变化；正文在完整全复输入 CPTP 类上证明共同有限严格收缩块、实际移动重置界及紧参数集的尖锐半参数二分。固定参数结论是其推论。所有证明均为可错、未执行的条件性符号数学，不是独立评审、形式内核或经验认证。文末保留追加锚。

## 1. 逐字母变参数合同与主结论

**定义 1.1（完整实际通道类）。** 保留系统只有 $H=\mathbb C^5$，有序正交基 $e_0,\ldots,e_4$ 对应 $(000,100,010,001,101)$。对 $0<\eta<1$，记 $r=1-\eta$，定义行随机矩阵

$$
Q_\eta=\begin{pmatrix}
r&0&0&\eta&0\\r&0&0&\eta&0\\0&r&0&0&\eta\\
0&0&1&0&0\\0&0&1&0&0
\end{pmatrix}.
\tag{1.1}
$$

$Q_{ij}$ 从输入 $i$ 到输出 $j$。$\mathcal L_\eta$ 是所有复线性 CPTP 映射 $\Phi:M_5(\mathbb C)\to M_5(\mathbb C)$ 中满足

$$
\operatorname{diag}\Phi(X)=Q_\eta^{\mathsf T}\operatorname{diag}X
\qquad\text{对每个复矩阵 }X
\tag{1.2}
$$

者的完整集合。该式包括每个有序非厄米矩阵单位；只检验五个基态不充分。一个字母的八个环境向量必须在该字母同一个实际环境中共同实现，不允许独立指定不相容的两两重叠。每步使用该实际映射的一份共同 dilation，不将不同来源的边、支持或环境重叠拼接成虚构字母。

令 $K\subset(0,1)$ 非空且紧。实际序列在选择输入标签之前指定：每个时刻独立选择 $\eta_j\in K$ 和一个实际 $\Phi_j\in\mathcal L_{\eta_j}$。允许 $K$ 有限或无限、处于半参数一侧或跨越两侧。记

$$
T_{b:a}=\Phi_b\circ\cdots\circ\Phi_a,\quad
T_n=T_{n:1},\quad T_0=\operatorname{id},\quad r_j=1-\eta_j.
\tag{1.3}
$$

序列不依赖输入、测量结果或反馈。每步用新鲜环境并立即丢弃；两步之间不保留环境、分支、综合征、输入相关历史或输入副本。没有途中读出或恢复。终端操作只在最后一步之后作用于 $H$。有限外部参考不受通道作用，仅用于完全范数的数学检验，不是可用的保留数据。证明中的对角规范、支持坐标和环境基不增加操作权限。

**定义 1.2（系数、完全范数与遗忘）。** 迹范数不除以二，令

$$
\begin{aligned}
\mathcal H_0&=\{Y=Y^\dagger\in M_5:\operatorname{Tr}Y=0\},\\
\delta(T)&=\max_{Y\in\mathcal H_0,\ \|Y\|_1=1}\|T(Y)\|_1,\\
a_n(K)&=\max_{\eta_j\in K,\ \Phi_j\in\mathcal L_{\eta_j}}
                     \delta(T_n),\qquad a_0(K)=1,\\
\mathcal R_\sigma(X)&=\sigma\operatorname{Tr}X,\qquad
\|L\|_\diamond=\sup_{m\ge1,\ Z\ne0}
 \frac{\|(L\otimes\operatorname{id}_m)(Z)\|_1}{\|Z\|_1}.
\end{aligned}
\tag{1.4}
$$

$Z$ 可以是任意复矩阵；最大值的存在见第 2、3 节。全部词一致遗忘指 $a_n(K)\to0$。一个序列保留非零经典区别指存在固定密度对，使其实际输出迹距离有严格正极限；距离在 CPTP 更新下单调不增，极限总存在。这不等同于要求某个有限时刻距离恰为零。

**定理 1.3（独立变参数的一致完全遗忘与尖锐二分）。** 对任意非空紧集 $K\subset(0,1)\setminus\{1/2\}$，存在有限整数 $N_K\ge1$ 和 $0<q_K<1$，使每个长度 $n$ 的实际允许词、每个种子密度 $\tau$ 都有

$$
\begin{aligned}
\delta(T_n)&\le q_K^{\lfloor n/N_K\rfloor},\\
\|T_n-\mathcal R_{T_n(\tau)}\|_\diamond
 &\le\min\{2,10q_K^{\lfloor n/N_K\rfloor}\}.
\end{aligned}
\tag{1.5}
$$

对任意有限参考及任意复 $Z$，同一常数给出

$$
\|(T_n\otimes\operatorname{id})(Z)
       -T_n(\tau)\otimes\operatorname{Tr}_H Z\|_1
\le\min\{2,10q_K^{\lfloor n/N_K\rfloor}\}\|Z\|_1.
\tag{1.6}
$$

同一界控制任意连续子词。因此全部预定义序列都遗忘所有输入差异，包含互补二周期参数 $a,1-a$（$a\ne1/2$）及跨半参数的紧集。实际重置密度是该词的 $T_n(\tau)$，不要求共同平稳密度、共同平稳人口或一般非周期输出密度收敛。

对不预先排除半参数的任意非空紧集 $K\subset(0,1)$，全部允许调度一致遗忘当且仅当 $1/2\notin K$。若包含半参数，存在合法固定通道永久保留距离二的经典位；还存在两个各自重复时混合、交替时永久保留该位的合法字母。并非每个半参数通道或每个半参数序列都保留信息。

这里 $N_K$ 只由存在性论证给出，可以取 $q_K=a_{N_K}(K)$。没有给出有效求取算法、最优值或显式量子时域。第 2 节的四步经典界只用于提取见证，既不是量子严格收缩时域，也不是 CP 重置下界。定理不分类被强制同时使用半参数及非半参数字母的调度。

## 2. 全复输入合法性与实际变参数人口

**引理 2.1（共同八向量、反序 Choi 与紧致性）。** 内积对第一变量共轭线性。每个 $\Phi\in\mathcal L_\eta$ 有实际等距 dilation

$$
\begin{aligned}
Ve_i&=\sqrt r\,e_0\otimes\alpha_i+
              \sqrt\eta\,e_3\otimes\beta_i\quad(i=0,1),\\
Ve_2&=\sqrt r\,e_1\otimes\gamma_0+
              \sqrt\eta\,e_4\otimes\gamma_1,\\
Ve_3&=z\otimes\delta_0,\qquad Ve_4=z\otimes\delta_1,
\qquad z=e_2,
\end{aligned}
\tag{2.1}
$$

其中八个单位向量属于该字母同一个复环境，规定正交性恰为

$$
\alpha_0\perp\alpha_1,\qquad\beta_0\perp\beta_1,
\qquad\delta_0\perp\delta_1.
\tag{2.2}
$$

其他重叠只受共同 Gram 正性约束，特别不要求两个 $\gamma$ 正交。反之任意满足这些条件的实际向量列都给出允许通道。最小环境维数等于 Choi 秩，在二至八之间。

证明。采用未归一化、输出在前的 Choi 矩阵

$$
J_\Phi=\sum_{ii'}\Phi(|e_i\rangle\langle e_{i'}|)
                       \otimes|e_i\rangle\langle e_{i'}|.
$$

在全部有序复矩阵单位上检验 (1.2)，恰得

$$
J\ge0,\qquad J_{jj}=\operatorname{diag}_i(Q_\eta)_{ij}.
\tag{2.3}
$$

这里 $J_{jj}$ 是固定输出 $j$ 的输入块，块之和为 $I_5$。向量化 Kraus 给出 Choi 正性；反之正 Choi 的外积分解经逆向量化给出 Kraus，偏输出迹 $I_5$ 正是其平方和完备性。这是有限维 Choi–Stinespring 接口，且 $\operatorname{Tr}J=5$。

正矩阵的二阶主子式给出 $|J_{ab}|^2\le J_{aa}J_{bb}$，零对角元因此消去整行整列，只剩八条正边。若 $Ve_i=\sum_j e_j\otimes e_{ji}$，则

$$
J_{(j,i),(k,l)}=\langle e_{kl},e_{ji}\rangle,
\qquad\langle e_{ji'},e_{ji}\rangle=\delta_{ii'}Q_{ij}.
\tag{2.4}
$$

除去正边权重就是 (2.1)–(2.2)。反之每列范数为一，异列的同输出内积均被三个正交对消去，故 $V$ 等距，并在所有复矩阵单位上满足 (1.2)。

固定顺序

$$
\begin{aligned}
f&=(\alpha_0,\alpha_1,\beta_0,\beta_1,
                         \gamma_0,\gamma_1,\delta_0,\delta_1),\\
\mathcal E&=((0,0),(0,1),(3,0),(3,1),(1,2),(4,2),(2,3),(2,4)),\\
w&=(\sqrt r,\sqrt r,\sqrt\eta,\sqrt\eta,
                         \sqrt r,\sqrt\eta,1,1),\qquad G_{ab}=\langle f_a,f_b\rangle.
\end{aligned}
\tag{2.5}
$$

活动 Choi 块是 $\operatorname{diag}(w)\overline G\operatorname{diag}(w)$，其 $(a,b)$ 元为 $w_aw_bG_{ba}$；反序来自环境迹 $\operatorname{Tr}|f_a\rangle\langle f_b|=\langle f_b,f_a\rangle$。规定零为 $G_{12}=G_{34}=G_{78}=0$（一基下标）。共同张成维数至多八，正交对使其至少二；所有权重正，Gram 秩与 Choi 秩相同。

联合字母空间

$$
\mathfrak F_K=\{(\eta,J):\eta\in K,\ J\ge0,
             \ J_{jj}=\operatorname{diag}_i(Q_\eta)_{ij}\}
\tag{2.6}
$$

在固定有限维空间中闭且有界，因为 $Q_\eta$ 连续且每个正 $J$ 的迹为五，故紧。不同时间无需辨认环境向量；每个极限 Choi 自有合法共同环境。$\square$

**引理 2.2（有序人口传播、重置扇区与实际三步正效应）。** 置

$$
\mathsf A=\operatorname{span}\{e_0,e_1\},\quad
\mathsf D=\operatorname{span}\{e_3,e_4\},\quad
\mathsf L=\operatorname{span}\{e_0,e_1,e_2\},\quad E_i=|e_i\rangle\langle e_i|.
$$

每个实际连续块满足

$$
\operatorname{diag}T_{b:a}(X)
 =Q_{\eta_b}^{\mathsf T}\cdots Q_{\eta_a}^{\mathsf T}\operatorname{diag}X
\qquad(X\in M_5).
\tag{2.7}
$$

参数为 $\eta_j$ 的单步满足

$$
\begin{aligned}
\Phi_j^\dagger(E_0)&=r_jP_{\mathsf A},&
\Phi_j^\dagger(E_1)&=r_jE_2,&
\Phi_j^\dagger(E_2)&=P_{\mathsf D},\\
\Phi_j^\dagger(E_3)&=\eta_jP_{\mathsf A},&
\Phi_j^\dagger(E_4)&=\eta_jE_2,&
\Phi_j(X)&=\operatorname{Tr}(X)E_2\quad(X\in\mathcal B(\mathsf D)).
\end{aligned}
\tag{2.8}
$$

任意三个实际字母的拉回为

$$
(\Phi_{j+2}\Phi_{j+1}\Phi_j)^\dagger(E_2)
       =\eta_{j+1}(r_jP_{\mathsf L}+P_{\mathsf D})>0.
\tag{2.9}
$$

证明。将 (1.2) 用于每个实际中间复矩阵，归纳得 (2.7)，行人口按时间右乘 $Q_{\eta_a}\cdots Q_{\eta_b}$。迹配对给出五个效应。正输入支持于 $\mathsf D$ 时，输出对角只在坐标二非零；正性消去其他行列，保迹确定重置系数，复线性张成给出整个代数上的重置式。

依实际反向次序拉回 $E_2$：最后一步给 $P_{\mathsf D}$，中间一步给 $\eta_{j+1}P_{\mathsf L}$，第一步再给 (2.9)，因为 $\Phi_j^\dagger(P_{\mathsf L})=r_jP_{\mathsf L}+P_{\mathsf D}$。其在 $\mathsf L,\mathsf D$ 上的特征值分别为 $\eta_{j+1}r_j,\eta_{j+1}$，均正。它是效应而非正密度，不是 CP 通道下界。$\square$

**引理 2.3（实际四步图路径与经典合流）。** 令

$$
\kappa=\min_{\eta\in K}\min\{\eta,1-\eta\}>0,
\qquad \lambda_K=1-5\kappa^4\in(0,1).
\tag{2.10}
$$

任意连续四个人口矩阵的有序乘积，每个条目至少 $\kappa^4$。任意实零和行 $v$ 有

$$
\|vQ_{\eta_1}\cdots Q_{\eta_n}\|_1
 \le\lambda_K^{\lfloor n/4\rfloor}\|v\|_1.
\tag{2.11}
$$

任一密度经过至少四次实际更新后，每个人口坐标至少 $\kappa^4$；两条密度轨迹的人口距离至多 $2\lambda_K^{\lfloor n/4\rfloor}$。

证明。共同图是合法无相邻一的三位窗口 $abc\to bcd$。从任意初始窗口到任意目标合法三位 $ijk$，依次追加四位 $(0,i,j,k)$。第一个零对任意初始末位都合法；从零到 $i$ 合法；后两条边由目标窗口合法性保证。因此这是四步实际图路径。四个时间各用自己的参数，每个非零概率至少 $\kappa$，强制概率一也满足此界，路径权重至少 $\kappa^4$。矩阵条目是路径正权之和，故得到逐项下界。

对任何这样的行随机四步乘积 $M$，令 $U$ 每行均为五点均匀概率，$\epsilon=5\kappa^4$。因 $0<\kappa\le1/2$，$0<\epsilon\le5/16<1$，于是

$$
M=\epsilon U+(1-\epsilon)R,
$$

其中 $R$ 行随机。零和 $v$ 有 $vU=0$；三角不等式与随机性给出 $\|vR\|_1\le\|v\|_1$。按实际时间分四步块，余块用普通随机收缩，即得 (2.11)。用最后四步作用于任意概率行，得到所有坐标的正下界；对两个起始概率之差应用 (2.11) 得合流界。这个 Doeblin 分解属于经典人口矩阵，不属于完整量子通道；不能由它推出量子忠实性、量子严格收缩或 CP 重置次序。$\square$

## 3. 从有限严格块失败到同一条实际正交轨迹

**引理 3.1（迹系数、次乘性与实际取等）。** 对 CPTP $T$，$0\le\delta(T)\le1$，$\delta$ 连续，且

$$
\delta(ST)\le\delta(S)\delta(T),\qquad
\delta(T)=\tfrac12\max_{\rho,\sigma\text{ 密度}}\|T(\rho)-T(\sigma)\|_1.
\tag{3.1}
$$

$\delta(T)=1$ 当且仅当有两个正交纯输入，其实际输出支持正交。

证明。对厄米 $Y=Y_+-Y_-$，正保迹映射与三角不等式给出 $\|T(Y)\|_1\le\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1$。它保持 $\mathcal H_0$，故得上界及次乘性。$\delta$ 是固定有限维实空间上的诱导范数，因此连续。非零 $Y\in\mathcal H_0$ 有

$$
Y=t(\rho_+-\rho_-),\qquad t=\|Y\|_1/2,
\tag{3.2}
$$

其中 $\rho_\pm$ 为归一化的正交 Jordan 部分。这给出 (3.1) 的一个方向；另一个用 $\|\rho-\sigma\|_1\le2$。密度空间与 $\mathcal H_0$ 单位球面都紧，所以最大值达到。

对正矩阵 $A,B$，$\|A-B\|_1=\operatorname{Tr}A+\operatorname{Tr}B$ 恰等价于支持正交。必要性由 $A-B$ 的正谱投影 $P$ 给出：迹范数变分等号强制 $\operatorname{Tr}(PA)=\operatorname{Tr}A$、$\operatorname{Tr}(PB)=0$，正性使 $P$ 包含第一个支持并消去第二个支持。充分性由正交直和直接得到。

若 $\delta(T)=1$，最大化 Jordan 密度的实际输出距离为二，故支持正交。分别对两个输入谱分解；正和的核是各正项核的交，所以每个纯输入的正输出项落在所属密度的输出支持内。从两边各选一个正权重纯项，便得到实际输出正交的纯输入对。收缩又强制该纯输入对本身距离二，即正交。反向直接以这对输入达到系数一。$\square$

**引理 3.2（移动共同人口的相容无限见证）。** $a_n(K)$ 的最大值存在，且

$$
a_{m+n}(K)\le a_m(K)a_n(K)\le1.
\tag{3.3}
$$

若不存在有限 $N$ 使 $a_N(K)<1$，则存在一条实际合法无限序列和两个实际密度轨迹，同时满足

$$
\begin{aligned}
\rho_{t+1}&=\Phi_{t+1}(\rho_t),&
\sigma_{t+1}&=\Phi_{t+1}(\sigma_t),\\
\rho_t\sigma_t&=0,&
\operatorname{diag}\rho_t&=\operatorname{diag}\sigma_t=\pi_t,\\
\pi_{t+1}&=Q_{\eta_{t+1}}^{\mathsf T}\pi_t,&
\pi_{t,i}&\ge\kappa^4\quad(t\ge0,\ 0\le i\le4).
\end{aligned}
\tag{3.4}
$$

$\pi_t$ 是移动人口，不预设等于任何固定参数的平稳概率。

证明。$\mathfrak F_K^n$ 紧，有限乘积与 $\delta$ 连续，所以最大值达到。按实际时间分词并用引理 3.1 得 (3.3)。若某 $a_N<1$，分块给 $a_n\le a_N^{\lfloor n/N\rfloor}\to0$；因此没有有限严格块意味着所有 $a_n=1$。

对每个 $m\ge4$ 选达到一的实际长度 $2m$ 词及引理 3.1 的纯正交输入对。最终距离二，而后缀 CPTP 不能增加距离，故每个实际前缀距离也恰为二。在时间 $m$ 保留两个实际中点密度及后面的 $m$ 个参数—通道字母。引理 2.3 使两中点的人口差趋零，且它们及之后所有原词输出的每个人口坐标均至少 $\kappa^4$。

为得到无限坐标列，在保留后缀之后填入任一固定合法字母，例如某 $\eta_*\in K$ 的 $\Psi(X)=\sum_{i,j}(Q_{\eta_*})_{ij}X_{ii}E_j$。这只填充坐标，不声称填充段保持正交。先对中点密度对取收敛子列，再对第一保留参数—Choi 字母取子列，再对第二个取子列，依此对角抽取。每个固定有限坐标集在同一子列上收敛，极限密度仍正、迹一，极限字母仍在闭紧 $\mathfrak F_K$ 内。

从极限中点密度出发，用极限字母实际递推定义所有后继密度。对每个固定 $j$，子列最终有 $m\ge j$，前 $j$ 个保留字母仍来自原正交后缀；有限乘积连续性同时保证极限输出就是实际递推输出，距离仍为二。引理 3.1 的取等判据给出每个时刻支持正交。中点人口差趋零使两个极限初始人口相同；完整人口律传播这一等式，正下界亦在所有固定时刻保留。这便是 (3.4)。

这里没有拼接不相容最大化词，没有使用秩的连续性，也没有假定非零量子特征值的统一下界。每个极限字母有自己的共同环境。极限初始密度可直接作为允许编码，无需无限前史。序列与编码对一起选定后，选择标签不改变序列，仍符合预定义输入无关合同。$\square$

## 4. 支持运输与全部尾部秩型

**引理 4.1（真实支持运输与目标线的前驱）。** 若 $\rho$ 在实际支持 $S$ 上严格正，$\Phi(\rho)$ 的支持为 $S'$，则每个实际 Kraus 都将 $S$ 送入 $S'$，即 $VS\subseteq S'\otimes\mathcal E$。在 (3.4) 中，目标支持若为直线，源支持亦为直线。

证明。对 $y\perp S'$，

$$
0=\langle y,\Phi(\rho)y\rangle
 =\sum_\mu\|\rho^{1/2}K_\mu^\dagger y\|^2.
\tag{4.1}
$$

各项为零，$\rho$ 在 $S$ 可逆，便得到整个支持上的运输。若 $S'=\mathbb C\psi'$，则 $Vx=\psi'\otimes Wx$（$x\in S$），$W$ 等距。该实际字母的坐标一给出

$$
\sqrt r\,x_2\gamma_0=\psi'_1Wx.
\tag{4.2}
$$

右侧因 $|\psi'_1|^2=\pi'_1>0$ 而秩为 $\dim S$，左侧作为环境值线性映射秩至多一，故 $\dim S=1$。因此每条轨迹的“秩至少二”谓词只能从假变真，至多一次；没有证明其他精确秩单调性。$\square$

**引理 4.2（两条纯轨迹的实际三步矛盾）。** (3.4) 不可能在连续三次更新的四个端点都为纯态。

证明。写两条纯轨迹单位向量为 $\psi_t,\varphi_t$。在每个实际字母中，纯像使

$$
V_t\psi_t=\psi_{t+1}\otimes c_t,\qquad
V_t\varphi_t=\varphi_{t+1}\otimes d_t.
$$

坐标一的 (4.2) 使 $c_t,d_t$ 都是同一个该字母 $\gamma_{t,0}$ 的单位相位倍数；模长一来自实际人口关系 $\pi_{t+1,1}=r_{t+1}\pi_{t,2}$。吸收相位到输出等距后，通道在两条正交线张成的整个二维复代数上是单个等距共轭，包括两个有序交叉矩阵单位。三次实际限制的乘积遂在初始二维平面等距。

等距将秩一输出效应 $E_2$ 拉回成至多秩一的压缩，而实际三步的完整效应是 (2.9)，在任意二维平面的压缩严格正、秩二，矛盾。这是变参数下两条始终纯轨迹的直接排除；没有将固定参数三步精确量子位定理扩大到一般变参数码。$\square$

**引理 4.3（$2+3$ 的满空间排除）。** 若某时刻两条正交支持维数为 $2+3$，而下一时刻二者均至少二维，则不可能。

证明。源支持 $S_0,S_1$ 穷尽 $H$，目标 $S'_0,S'_1$ 正交。运输给出全输入交织

$$
VP_{S_a}=(P_{S'_a}\otimes I)V\qquad(a=0,1).
\tag{4.3}
$$

选二维源 $S_a$，$z'_a=P_{S'_a}z\ne0$ 由目标人口正性得到。对 $e_3,e_4$ 应用交织：

$$
VP_{S_a}e_3=z'_a\otimes\delta_0,\qquad
VP_{S_a}e_4=z'_a\otimes\delta_1.
\tag{4.4}
$$

右侧非零、正交；等距性使两个源投影独立，张成二维 $S_a$。其全部系统输出因此落在单条线 $\mathbb Cz'_a$，违反实际目标秩至少二。源目标维数不需相同。$\square$

**推论 4.4（穷尽尾部）。** 去掉有限前缀后，(3.4) 恰剩三种秩型之一：两条始终纯；两条始终混；一条始终纯而另一条始终混。第一种由引理 4.2 排除，第二种每个时刻恰为 $2+2$。

证明。分别应用引理 4.1 的单调谓词，经过所有实际发生的至多两次改变后便稳定。五维中两条正交混支持只可能 $2+2$ 或 $2+3$；后者由下一时刻仍混及引理 4.3 排除。$\square$

## 5. 移动源、目标超平面的全输入压缩

**引理 5.1（两种四维目标支持）。** (3.4) 的一个步骤若源、目标都为 $2+2$，合支持为 $R,R'$，则该字母在整个 $H$ 上输出均压入 $R'$。令该步参数为 $\eta$、$r=1-\eta$，目标恰有下列一种形式：

$$
\begin{aligned}
\mathrm U:\quad&R'=\operatorname{span}\{u',e_1,z,e_4\},
&u'&=\sqrt r\,e_0+\omega\sqrt\eta\,e_3,\\
\mathrm V:\quad&R'=\operatorname{span}\{e_0,e_3,v',z\},
&v'&=\sqrt r\,e_1+\omega\sqrt\eta\,e_4,
\end{aligned}
\qquad |\omega|=1.
\tag{5.1}
$$

证明。取 $R^\perp=\mathbb C\tau$、$(R')^\perp=\mathbb C\tau'$，两者单位。运输使环境值行消去 $R$，故在全输入上有

$$
(\langle\tau'|\otimes I)V=\xi\langle\tau|.
\tag{5.2}
$$

列三、四给出

$$
\overline{\tau'_2}\delta_0=\overline{\tau_3}\xi,
\qquad\overline{\tau'_2}\delta_1=\overline{\tau_4}\xi.
\tag{5.3}
$$

正交单位 $\delta$ 强制 $\tau'_2=0$。若 $\xi\ne0$，则 $\tau_3=\tau_4=0$，所以 $\mathsf D\subset R$。交织在 $R$ 上成立，此时可应用于 $e_3,e_4$；对任一二维源扇区，正目标人口使其两个像成为 (4.4) 那样的非零正交向量，又将整个目标压成一条线，矛盾。因此 $\xi=0$，全输入均压入 $R'$。

其余列满足

$$
\begin{aligned}
\sqrt r\,\overline{\tau'_0}\alpha_i+
 \sqrt\eta\,\overline{\tau'_3}\beta_i&=0\quad(i=0,1),\\
\sqrt r\,\overline{\tau'_1}\gamma_0+
 \sqrt\eta\,\overline{\tau'_4}\gamma_1&=0.
\end{aligned}
\tag{5.4}
$$

每对系数一个非零强制另一个非零，因为权重正且环境向量单位。第一对非零使两个 $\beta_i$ 与对应 $\alpha_i$ 有同一个单位相位关系，将 $(0,3)$ 系统平面压成平方权重 $r,\eta$ 的线；第二对将 $(1,4)$ 压成这样的线。单位法向量且 $\tau'_2=0$，故至少一对非零。

若两对都非零，整个输出支持在两条线与 $\mathbb Cz$ 的和中，维数至多三；实际目标均值 $(\rho'+\sigma')/2$ 秩四，矛盾。所以恰有一种压缩。任何额外的第二压缩也会降秩至三，故不存在；四维实际目标合支持等于所显示的四维输出空间。这没有将两个法向量、两个合支持或不同时间相位混同。$\square$

**引理 5.2（U 型迫使当前参数为半）。** 引理 5.1 的 U 型只能在该步 $\eta=1/2$ 出现。

证明。对一个扇区限制 $T:\mathcal B(S_a)\to\mathcal B(S'_a)$，这是两个二维空间间的 CPTP 映射，故其伴随正且保持扇区单位元。记 $F_j=P_{S_a}E_jP_{S_a}$、$F'_j=P_{S'_a}E_jP_{S'_a}$。正人口使所有这些秩一效应非零。压缩完整效应得

$$
T^\dagger(F'_1)=rF_2,\qquad T^\dagger(F'_4)=\eta F_2.
\tag{5.5}
$$

若目标两个投影向量独立，$F'_1+F'_4\ge\epsilon I_{S'_a}$ 对某 $\epsilon>0$ 成立；正且保持单位元的伴随会使其像也正定，但像为秩一 $F_2$。故二效应比例，非零像确定比例为 $F'_1=(r/\eta)F'_4$。U 型中 $e_1,e_4\in R'$，对两目标扇区求迹相加得 $1=r/\eta$，于是 $r=\eta=1/2$。未假设 Schrödinger 限制保持单位元。$\square$

## 6. 不同参数的 V 型与源参数迹矛盾

**引理 6.1（移动 V 型尾部排除）。** 若所有字母参数排除半参数，则 (3.4) 不存在两条始终混的尾部。

证明。推论 4.4 使每步为 $2+2$；引理 5.1–5.2 使每个目标为 V 型。丢弃初始一步后，源和目标皆为 V 型，写

$$
R_t=\operatorname{span}\{e_0,e_3,v_t,z\},\qquad
v_t=\sqrt{r_t}\,e_1+\nu_t\sqrt{\eta_t}\,e_4,
\quad |\nu_t|=1.
\tag{6.1}
$$

这里 $\eta_t$ 是生成源合支持的前一步参数。实际下一步 $\Phi_{t+1}$ 的等距 $V_t$ 满足

$$
V_tz=v_{t+1}\otimes\gamma_t,\quad
V_te_3=z\otimes\delta_{t,0},\quad
\Phi_{t+1}^\dagger(|v_{t+1}\rangle\langle v_{t+1}|)=E_2.
\tag{6.2}
$$

$\gamma_t$ 单位；相位吸入它即可。最后的全输入效应恒等式来自：只有输入列二含该输出线，且该列全部在该线。

固定一个扇区，置 $P=P_{S_{a,t}}$、$P'=P_{S_{a,t+1}}$，以及

$$
b=Pe_3,\quad c=Pz,\quad v=Pv_t,\qquad
c'=P'z,\quad v'=P'v_{t+1}.
\tag{6.3}
$$

$e_3,z$ 的投影由正人口非零；$P_{R_t}e_1=\sqrt{r_t}v_t$ 及目标对应式使两个 $v$ 投影也非零。交织在源 $R_t$ 上成立；$e_3,z\in R_t$，故

$$
V_tb=c'\otimes\delta_{t,0},\quad V_tc=v'\otimes\gamma_t,
\qquad\|b\|^2=\|c'\|^2,\quad\|c\|^2=\|v'\|^2>0.
\tag{6.4}
$$

令 $T$ 为该二维 CPTP 限制，压缩 (6.2) 得

$$
T^\dagger(|v'\rangle\langle v'|)=|c\rangle\langle c|.
\tag{6.5}
$$

除以刚证明的相同正范数，得到秩一投影到投影 $T^\dagger(P_1)=Q_1$。密度 $Q_1$ 的输出对 $P_1$ 期望为一，故输出为 $P_1$；密度 $I-Q_1$ 的期望为零，二维目标中只能输出 $I-P_1$。相加得 $T(I)=I$，因此 $T^\dagger$ 保迹。等范数和二维性是本处必要前提，不能从不相关的秩一效应直接推出双随机性。

再压缩 $\Phi_{t+1}^\dagger(E_2)=E_3+E_4$。在源 V 型支持上 $PE_4P=\eta_t|v\rangle\langle v|$，相位在外积中消失，所以

$$
T^\dagger(|c'\rangle\langle c'|)
 =|b\rangle\langle b|+\eta_t|v\rangle\langle v|.
\tag{6.6}
$$

求迹并用 (6.4) 和刚证明的伴随保迹得

$$
\|c'\|^2=\|b\|^2+\eta_t\|v\|^2
         =\|c'\|^2+\eta_t\|v\|^2,
\tag{6.7}
$$

与 $\eta_t>0,v\ne0$ 矛盾。系数是源参数 $\eta_t$，不是当前 $\eta_{t+1}$。所有投影非零及除数正性均已由实际人口和等距性建立。$\square$

## 7. 实际移动人口、正纯线与时变部分等距

**引理 7.1（逐时刻证明规范及望远镜消去）。** 设 (3.4) 一条轨迹始终纯、另一条始终混。只作坐标变换，可令纯轨迹单位向量为每个坐标严格正的

$$
\psi_t=(\sqrt{\pi_{t,0}},\ldots,\sqrt{\pi_{t,4}})^{\mathsf T},
\tag{7.1}
$$

伴侣支持 $S_t\perp\psi_t$，人口仍为 $\pi_t$；不要求 $\psi_t$ 相同。

证明。正人口使原纯向量每个坐标非零。逐时刻取对角酉 $D_t$ 将它送到 (7.1)，并用

$$
\widetilde\Phi_{t+1}=\operatorname{Ad}_{D_{t+1}}\circ\Phi_{t+1}
                                      \circ\operatorname{Ad}_{D_t^\dagger}.
\tag{7.2}
$$

对角酉在输入、输出都保持计算基对角；对每个复 $X$，(1.2) 仍以原参数成立，CPTP 性亦保持。实际有限乘积满足

$$
\widetilde\Phi_b\cdots\widetilde\Phi_a
 =\operatorname{Ad}_{D_b}\circ T_{b:a}\circ\operatorname{Ad}_{D_{a-1}^\dagger}.
\tag{7.3}
$$

内部相位严格消去，秩、迹距离和支持正交均保持。它只是同一实际词的证明表示，不在物理序列中实施免费恢复。下文省去波浪号，$V_t$ 表示 $\Phi_{t+1}$ 的实际等距。$\square$

**引理 7.2（人口条件比例与时变 $K_t,W_t$）。** 保留原时间参数下标并去掉有限前缀，使 $t\ge1$。令

$$
A_t=\pi_{t,0}+\pi_{t,1},\quad B_t=\pi_{t,2},\quad
D_t^{\rm mass}=\pi_{t,3}+\pi_{t,4},\qquad
 a_t=\frac{\pi_{t,1}}{A_t}=\frac{\pi_{t,4}}{D_t^{\rm mass}}\in(0,1).
\tag{7.4}
$$

则 $D_t^{\rm mass}/A_t=\eta_t/r_t$。定义

$$
\begin{aligned}
h_A(a)&=\sqrt{1-a}\,e_0+\sqrt a\,e_1,&
l_A(a)&=\sqrt a\,e_0-\sqrt{1-a}\,e_1,\\
h_D(a)&=\sqrt{1-a}\,e_3+\sqrt a\,e_4,&
l_D(a)&=\sqrt a\,e_3-\sqrt{1-a}\,e_4,\\
u_b&=\sqrt{1-b}\,e_0+\sqrt b\,e_3,&
v_b&=\sqrt{1-b}\,e_1+\sqrt b\,e_4.
\end{aligned}
\tag{7.5}
$$

每个实际字母的同一个环境内存在单位 $c_t$ 及单位 $f_t,g_t,d_t\perp c_t$，使

$$
\begin{aligned}
\alpha_0&=\sqrt{1-a_t}\,c_t+\sqrt{a_t}\,f_t,&
\alpha_1&=\sqrt{a_t}\,c_t-\sqrt{1-a_t}\,f_t,\\
\beta_0&=\sqrt{1-a_t}\,c_t+\sqrt{a_t}\,g_t,&
\beta_1&=\sqrt{a_t}\,c_t-\sqrt{1-a_t}\,g_t,\\
\delta_0&=\sqrt{1-a_t}\,c_t+\sqrt{a_t}\,d_t,&
\delta_1&=\sqrt{a_t}\,c_t-\sqrt{1-a_t}\,d_t,\\
\gamma_0&=\gamma_1=c_t.
\end{aligned}
\tag{7.6}
$$

环境向量的时间下标除 $c_t,f_t,g_t,d_t$ 外省略。置

$$
\begin{aligned}
K_t&=|u_{\eta_{t+1}}\rangle\langle h_A(a_t)|
       +|v_{\eta_{t+1}}\rangle\langle z|
       +|z\rangle\langle h_D(a_t)|,\\
x_A&=\langle l_A(a_t),x\rangle,\qquad
x_D=\langle l_D(a_t),x\rangle,\\
W_tx&=x_A(\sqrt{r_{t+1}}e_0\otimes f_t
                 +\sqrt{\eta_{t+1}}e_3\otimes g_t)+x_Dz\otimes d_t.
\end{aligned}
\tag{7.7}
$$

实际分解和移动支持关系是

$$
\begin{aligned}
V_tx&=K_tx\otimes c_t+W_tx,\\
K_t^\dagger K_t&=P_{H_+(a_t)},\qquad
 H_+(a)=\operatorname{span}\{h_A(a),z,h_D(a)\},\\
K_t\psi_t&=\psi_{t+1},\quad K_t^\dagger\psi_{t+1}=\psi_t,\\
K_tS_t&\subseteq S_{t+1},\qquad
W_tS_t\subseteq S_{t+1}\otimes\mathcal E_t.
\end{aligned}
\tag{7.8}
$$

证明。实际人口更新给出

$$
\begin{aligned}
\pi_{t,0}&=r_tA_{t-1},&\pi_{t,1}&=r_tB_{t-1},\\
\pi_{t,3}&=\eta_tA_{t-1},&\pi_{t,4}&=\eta_tB_{t-1},
&\pi_{t,2}&=D_{t-1}^{\rm mass}.
\end{aligned}
\tag{7.9}
$$

所有量正，故两条件比例都等于 $B_{t-1}/(A_{t-1}+B_{t-1})\in(0,1)$，且得到 $D_t^{\rm mass}/A_t=\eta_t/r_t$。于是

$$
\psi_t=\sqrt{A_t}\,h_A(a_t)+\sqrt{B_t}\,z
                   +\sqrt{D_t^{\rm mass}}\,h_D(a_t).
\tag{7.10}
$$

纯像给 $V_t\psi_t=\psi_{t+1}\otimes c_t$。坐标一、四的正幅度由实际人口律相等，可除去，得两个 $\gamma$ 均为 $c_t$。坐标零、三、二依次给

$$
\begin{aligned}
\sqrt{1-a_t}\alpha_0+\sqrt{a_t}\alpha_1&=c_t,\\
\sqrt{1-a_t}\beta_0+\sqrt{a_t}\beta_1&=c_t,\\
\sqrt{1-a_t}\delta_0+\sqrt{a_t}\delta_1&=c_t.
\end{aligned}
$$

每对正交归一，其正交组合定义 $f_t,g_t,d_t$，均单位且正交于 $c_t$；反解恰得 (7.6)。没有设定三者之间的任何重叠。

将它们代入该步 (2.1) 得 (7.7)–(7.8) 的分解。$K_t$ 的三条输入、三条输出向量各正交归一，故为部分等距；(7.9)–(7.10) 使 $K_t\psi_t=\psi_{t+1}$，反向伴随式亦由该初始空间得到。支持运输与环境上沿 $c_t$ 及其正交补的分别投影给出两个移动包含式。$K_t$ 真正随时间变动；没有使用固定算子的谱、$K_tS_t\subset S_t$ 或固定纯态。$\square$

**引理 7.3（真实环境行排除秩三，并先证 $x_A$ 非零）。** 在上述无限混伴侣尾部，每个 $S_t$ 恰为二维，且

$$
S_t\subset R_t^V\cap\psi_t^\perp,\qquad
R_t^V=\operatorname{span}\{e_0,e_3,v_{\eta_t},z\}.
\tag{7.11}
$$

泛函 $x\mapsto x_A$ 在每个 $S_t$ 上不恒为零。

证明。前一步的两个 $\gamma$ 相等使其全输入输出压入 $R_t^V$。因此第一步之后伴侣秩至多三。将 $W_tS_t$ 的系统部分投影到 $\psi_{t+1}$，用 (7.9) 得实际环境值行

$$
\ell_t(x)=\sqrt{A_t}(r_{t+1}f_t+\eta_{t+1}g_t)x_A
                    +\sqrt{D_t^{\rm mass}}d_tx_D=0
\quad(x\in S_t).
\tag{7.12}
$$

该行也消去 $\psi_t$，因为它的 $l_A,l_D$ 坐标均零，但

$$
\ell_t(e_3)=\sqrt{D_t^{\rm mass}}\sqrt{a_t}\,d_t\ne0.
\tag{7.13}
$$

若 $S_t$ 三维，就等于三维 $R_t^V\cap\psi_t^\perp$，与 $\psi_t$ 一起张成 $R_t^V$，使 $\ell_t$ 消去其中的 $e_3$，矛盾。因此混伴侣只能二维；秩四已经由 (7.11) 排除。

若 $x_A$ 在二维 $S_t$ 恒零，(7.12) 及单位 $d_t$ 使 $x_D$ 亦恒零，所以 $S_t\subset H_+(a_t)$。写 $x=Xh_A(a_t)+Yz+Th_D(a_t)$；属于 $R_t^V$ 的条件是 $x_4=\sqrt{\eta_t/r_t}\,x_1$，因 $a_t>0$，它等价于 $T=\sqrt{\eta_t/r_t}\,X$。故

$$
H_+(a_t)\cap R_t^V
 =\operatorname{span}\{z,h_A(a_t)+\sqrt{\eta_t/r_t}\,h_D(a_t)\}.
\tag{7.14}
$$

这是包含非零 $\psi_t$ 的二维空间，与 $\psi_t^\perp$ 交只有一维，不可能包含 $S_t$。非零泛函因此在使用任何 $x_A$ 除法之前已被证明。$\square$

## 8. 变参数消去行、两次实际求值与强迫半参数

**引理 8.1（消去行与环境共线，包含零分支）。** 每个上述时刻有复数 $\zeta_t$，满足

$$
\begin{aligned}
r_{t+1}f_t+\eta_{t+1}g_t&=\zeta_td_t,\qquad |\zeta_t|\le1,\\
x_D&=-\sqrt{r_t/\eta_t}\,\zeta_t x_A\quad(x\in S_t).
\end{aligned}
\tag{8.1}
$$

因此复线性行

$$
L_t=\sqrt{r_t}\,\zeta_t\langle l_A(a_t)|
                         +\sqrt{\eta_t}\langle l_D(a_t)|
\tag{8.2}
$$

消去 $S_t$。还存在单位相位 $\beta_t$，使

$$
g_t=\beta_tf_t,\quad |\zeta_t|=|r_{t+1}+\eta_{t+1}\beta_t|,
\tag{8.3}
$$

且以下非零向量属于实际下一支持：

$$
w_t=\sqrt{r_{t+1}}e_0+\sqrt{\eta_{t+1}}\beta_te_3
       -\sqrt{r_t/\eta_t}(r_{t+1}+\eta_{t+1}\beta_t)z\in S_{t+1}.
\tag{8.4}
$$

证明。选已证明存在的 $x\in S_t$ 使 $x_A\ne0$，在 (7.12) 中定义
$\zeta_t=-\sqrt{D_t^{\rm mass}/A_t}\,x_D/x_A$，得到第一式。将其代回任意 $x\in S_t$ 的环境行，单位 $d_t$ 给第二式，所用质量比正是 $D_t^{\rm mass}/A_t=\eta_t/r_t$。三角不等式和环境单位范数给 $|\zeta_t|\le r_{t+1}+\eta_{t+1}=1$。没有除以 $\zeta_t$，而 (8.2) 的系数是 $\zeta_t$ 本身，不擅自复共轭。

在 $W_t$ 中替换 $x_D$ 并对选定非零 $x_A$ 除一次，实际运输迫使

$$
\begin{aligned}
F_t={}&\sqrt{r_{t+1}}e_0\otimes f_t+\sqrt{\eta_{t+1}}e_3\otimes g_t\\
 &-\sqrt{r_t/\eta_t}\,z\otimes(r_{t+1}f_t+\eta_{t+1}g_t)
       \in S_{t+1}\otimes\mathcal E_t.
\end{aligned}
\tag{8.5}
$$

若 $f_t,g_t$ 独立，在其张成空间取两个对偶环境线性泛函，得到两条系统向量

$$
\sqrt{r_{t+1}}e_0-\sqrt{r_t/\eta_t}\,r_{t+1}z,
\qquad
\sqrt{\eta_{t+1}}e_3-\sqrt{r_t/\eta_t}\,\eta_{t+1}z
\tag{8.6}
$$

都在 $S_{t+1}$。二者独立，张成整个二维目标支持，但其坐标一、四全零，不能支持人口 $\pi_{t+1,1},\pi_{t+1,4}>0$ 的实际密度。故环境必共线，单位范数给 $g_t=\beta_tf_t$。对 (8.1) 取范数即得 (8.3)，包括两边同时零。于是 (8.5) 恰为 $w_t\otimes f_t$，给出 (8.4)。$w_t$ 的坐标零是 $\sqrt{r_{t+1}}>0$，所以非零；下一步 (7.8) 还给 $K_{t+1}w_t\in S_{t+2}$。没有除以可能为零的 $r_{t+1}+\eta_{t+1}\beta_t$。$\square$

**引理 8.2（第一求值先强制不超过半参数）。** 在每个上述尾部时刻，

$$
\zeta_{t+1}=-\frac{\eta_{t+1}}{r_{t+1}}\beta_t,
\qquad \eta_{t+1}\le\tfrac12.
\tag{8.7}
$$

证明。实际向量 $w_t\in S_{t+1}$，必须由下一时刻的行 $L_{t+1}$ 消去。直接列出所需两个坐标：

$$
\begin{aligned}
\langle l_A(a_{t+1}),w_t\rangle
 &=\sqrt{a_{t+1}r_{t+1}},\\
\langle l_D(a_{t+1}),w_t\rangle
 &=\sqrt{a_{t+1}\eta_{t+1}}\beta_t.
\end{aligned}
\tag{8.8}
$$

$z$ 项在两行中均为零，因此

$$
0=L_{t+1}(w_t)
 =\sqrt{a_{t+1}}(r_{t+1}\zeta_{t+1}+\eta_{t+1}\beta_t).
\tag{8.9}
$$

除以已证正的 $\sqrt{a_{t+1}}r_{t+1}$ 得第一式。由 (8.1) 在时刻 $t+1$ 的范数界 $|\zeta_{t+1}|\le1$，得 $\eta_{t+1}/r_{t+1}\le1$，即第二式。这是从轨迹推出的不等式；不要求原始 $K$ 在半参数同一侧。$\square$

**引理 8.3（第二求值及正确的下一参数范数强制半参数）。** 任何这样的无限纯线—混伴侣轨迹，其参数在尾部每个时刻均为 $1/2$。

证明。简写

$$
b=\eta_{t+1},\quad s=1-b,\quad c=\eta_{t+2},\quad
R=\sqrt{r_t/\eta_t},\quad u=a_{t+1},\quad v=a_{t+2}.
\tag{8.10}
$$

$R>0$，$u,v\in(0,1)$。将实际时变 $K_{t+1}$ 作用于 (8.4)，分别取 $h_A(u),z,h_D(u)$ 三个输入坐标，得到完整向量

$$
K_{t+1}w_t=\sqrt{(1-u)s}\,u_c
             -R(s+b\beta_t)v_c+\sqrt{(1-u)b}\,\beta_t z.
\tag{8.11}
$$

它属于 $S_{t+2}$。为了展开第二次消去求值，定义

$$
H=\sqrt{v(1-u)s}+\sqrt{1-v}\,R(s+b\beta_t).
\tag{8.12}
$$

在 (8.11) 中，$u_c$ 的系统坐标零、三为 $\sqrt{1-c},\sqrt c$，$v_c$ 的坐标一、四亦分别为这两个数，$z$ 不贡献两条消去坐标。于是逐项有

$$
\begin{aligned}
\langle l_A(v),K_{t+1}w_t\rangle
 &=\sqrt v\sqrt{(1-u)s}\sqrt{1-c}
       +\sqrt{1-v}\,R(s+b\beta_t)\sqrt{1-c}
   =\sqrt{1-c}\,H,\\
\langle l_D(v),K_{t+1}w_t\rangle
 &=\sqrt v\sqrt{(1-u)s}\sqrt c
       +\sqrt{1-v}\,R(s+b\beta_t)\sqrt c
   =\sqrt c\,H.
\end{aligned}
\tag{8.13}
$$

因此正确时间的消去行给出

$$
0=L_{t+2}(K_{t+1}w_t)
       =\bigl((1-c)\zeta_{t+2}+c\bigr)H.
\tag{8.14}
$$

除去 $H$ 之前必须证明它非零。引理 8.2 已先给 $b\le1/2$，所以

$$
\operatorname{Re}(s+b\beta_t)\ge s-b\ge0,
\qquad
\operatorname{Re}H\ge\sqrt{v(1-u)s}>0.
\tag{8.15}
$$

这包括 $b=1/2,\beta_t=-1$ 时第二项为零的分支。现在合法除以 $H$ 和 $1-c>0$，得 $\zeta_{t+2}=-c/(1-c)$。再将引理 8.2 用于下一时刻，有 $\zeta_{t+2}=-(c/(1-c))\beta_{t+1}$；由于 $c>0$，故 $\beta_{t+1}=1$。

关键是 (8.3) 在时刻 $t+1$ 使用下一参数 $\eta_{t+2}=c$，所以

$$
|\zeta_{t+1}|=|(1-c)+c\beta_{t+1}|=1.
\tag{8.16}
$$

而 (8.7) 在时刻 $t$ 给同一模长为 $b/s$。故 $b=s=1/2$，即 $\eta_{t+1}=1/2$。对每个尾部 $t$ 均可使用这三个连续支持，得到整个尾部结论。

所有零分支已被包含：$\zeta_t=0$ 从未作除数，$r_{t+1}+\eta_{t+1}\beta_t=0$ 也没有被除；$\beta_t=-1$ 仍满足 (8.15)。环境之间的任何其他零重叠均未被除去。实际支持中个别向量可有零坐标；只使用了实际密度人口正、已证存在的非零 $x_A$ 及已证 $H\ne0$。三条移动支持与时变 $a_t,K_t$ 各按实际时间使用，没有把固定参数的平稳公式移植为变参数等式。$\square$

## 9. 有限严格量子块、正标量模式与完整复参考界

**引理 9.1（共同有限严格块与严格正系数）。** 对非空紧 $K\subset(0,1)\setminus\{1/2\}$，存在有限 $N_K$，使

$$
q_K=a_{N_K}(K)\in(0,1),\qquad
 a_n(K)\le q_K^{\lfloor n/N_K\rfloor}.
\tag{9.1}
$$

证明。若没有严格块，引理 3.2 构造同一条实际相容正交轨迹。推论 4.4 穷尽尾部秩型：两条纯由实际三步正效应矛盾排除；两条混由不同源目标超平面全输入压缩、当前参数的 U 型阻碍及源参数的 V 型迹矛盾排除；纯线加混伴侣由真实环境行降为秩二，再由引理 8.3 强迫尾部半参数，与所有参数属于排除半参数的 $K$ 矛盾。因此存在 $a_{N_K}(K)<1$。对实际词分完整块及余块，用 (3.3) 得上界；这是存在性证明，不提供具体长度。

严格正性可由任意实际字母共有的双效应标量模式证明，无需固定参数特征向量。由 (2.8)，

$$
\Phi_j^\dagger(P_{\mathsf D})=\eta_j(I-P_{\mathsf D}).
\tag{9.2}
$$

对无迹输入，每一步的 $P_{\mathsf D}$ 期望因此乘以 $-\eta_j$。取 $Y=E_3-E_0$，$\|Y\|_1=2$、$\operatorname{Tr}(P_{\mathsf D}Y)=1$，得

$$
\operatorname{Tr}(P_{\mathsf D}T_n(Y))=(-1)^n\prod_{j=1}^n\eta_j.
\tag{9.3}
$$

对任意无迹厄米 $Z$ 和投影 $P$，

$$
|\operatorname{Tr}(PZ)|
 =|\operatorname{Tr}((P-I/2)Z)|\le\tfrac12\|Z\|_1.
$$

故每个实际词满足

$$
\delta(T_n)\ge\prod_{j=1}^n\eta_j>0\qquad(n\ge1).
\tag{9.4}
$$

非空 $K$ 中的任一合法词就使 $a_{N_K}(K)>0$。这只是必要速率下界，非最优率；尤其不将四步经典合流或同质 24 步结果指定为量子混合词时域。$\square$

**引理 9.2（任意复参考、因子十及上限二）。** 对 CPTP $T$ 与任意密度 $\tau,\sigma$，

$$
\delta(T)\le\|T-\mathcal R_\sigma\|_\diamond,
\qquad
\|T-\mathcal R_{T(\tau)}\|_\diamond\le\min\{2,10\delta(T)\}.
\tag{9.5}
$$

证明。重置消去 $\mathcal H_0$，给出第一式。令 $L=T-\mathcal R_{T(\tau)}=T(\operatorname{id}-\mathcal R_\tau)$。对角矩阵单位满足 $L(E_{ii})=T(E_{ii}-\tau)$，括号无迹厄米且范数至多二，所以 $\|L(E_{ii})\|_1\le2\delta(T)$。对 $i\ne j$，写

$$
E_{ij}=\frac{E_{ij}+E_{ji}}2+i\frac{E_{ij}-E_{ji}}{2i}.
\tag{9.6}
$$

两个厄米项均无迹、迹范数一，重置都消去它们，故仍有 $\|L(E_{ij})\|_1\le2\delta(T)$。

对任意有限参考及任意复 $Z=\sum_{ij}E_{ij}\otimes Z_{ij}$，取完整 SVD

$$
Z=\sum_\ell s_\ell|u_\ell\rangle\langle v_\ell|,
\qquad s_\ell\ge0,\quad\|u_\ell\|=\|v_\ell\|=1.
$$

按系统指标分块 $u_\ell=(u_{\ell i})$、$v_\ell=(v_{\ell j})$。每个块的秩一迹范数是两向量范数之积，因此

$$
\begin{aligned}
\sum_{ij}\|Z_{ij}\|_1
 &\le\sum_\ell s_\ell
       \left(\sum_i\|u_{\ell i}\|\right)
       \left(\sum_j\|v_{\ell j}\|\right)\\
 &\le5\sum_\ell s_\ell=5\|Z\|_1.
\end{aligned}
\tag{9.7}
$$

最后用两次 Cauchy–Schwarz 及各块平方范数之和为一；没有参考维数因子。三角不等式和张量积迹范数乘法性给

$$
\|(L\otimes\operatorname{id})(Z)\|_1
 \le\sum_{ij}\|L(E_{ij})\|_1\|Z_{ij}\|_1
 \le10\delta(T)\|Z\|_1.
\tag{9.8}
$$

因子十是矩阵单位因子二乘系统维数五，未称最优。

上限二也必须对任意复输入成立。在每个放大维数，CPTP 的伴随 $\Theta$ 保持单位元且 CP。对正块

$$
\begin{pmatrix}Y^\dagger Y&Y^\dagger\\Y&I\end{pmatrix}
$$

应用其二阶放大并取 Schur 补，得

$$
\Theta(Y)^\dagger\Theta(Y)\le\Theta(Y^\dagger Y)
                                     \le\|Y\|_\infty^2I.
$$

故放大伴随收缩算子范数；迹范数对偶使原通道在任意复放大输入上完全收缩，密度输入达到一。两个通道之差的 diamond 范数至多二。与 (9.8) 取最小即得 (9.5)。重置的放大严格为 $T(\tau)\otimes\operatorname{Tr}_H Z$；保迹使参考边缘保持，不曾由总迹为零错误推断系统偏迹为零。$\square$

**定理 9.3（主定理量词与终端恢复后果）。** 定理 1.3 的非半参数断言成立。任意两个密度还满足

$$
\|T_n(\rho)-T_n(\sigma)\|_1
 \le q_K^{\lfloor n/N_K\rfloor}\|\rho-\sigma\|_1.
\tag{9.9}
$$

在 $n\ge N_K$ 时，不存在维数至少二的终端精确可恢复复子空间。

证明。引理 9.1 给每个实际词的无迹厄米收缩；引理 9.2 对每个种子给 (1.5)–(1.6)。连续子词仍由同一完整联合类的字母组成，所以同一常数适用。密度差属于 $\mathcal H_0$，故得 (9.9)，右侧趋零，排除任何固定输入对保留正极限距离。

如果二维或更大子空间在 $n\ge N_K$ 有终端 CPTP 精确恢复，取其中两个正交纯态；恢复后距离二，收缩性迫使实际通道输出距离也二，但 $\delta(T_n)\le q_K<1$，矛盾。这里只得到隐式时域 $N_K$，没有证明一般变参数的尖锐三步量子码结论。固定参数三步定理的独立范围见约定 10.5。

重置密度随实际词、时刻和种子变化，不需要共同固定密度。引理 9.2 的两向比较证明，在此有限维模型中，全部词的迹系数趋零等价于全部词一致趋近其实际移动重置。半参数合法反例见第 10 节，结合即完成紧集的当且仅当。$\square$

## 10. 半参数的完整合法见证与个体混合反差

**定义 10.1（典范 C 与两个相位更新）。** 本节令 $\eta=r=1/2$，$q=1/\sqrt2$，并置

$$
u=q(e_0+e_3),\quad v=q(e_1+e_4),\quad z=e_2,
\quad R=\operatorname{span}\{u,v,z\},\quad s=(u+v+z)/\sqrt3.
$$

取完整五维 Kraus 算子

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|
                                      +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|
                                      +|z\rangle\langle e_3|,\\
C(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger.
\end{aligned}
\tag{10.1}
$$

令 $S=\operatorname{diag}(1,-1,1,1,1)$、$\mathcal U=\operatorname{Ad}_S$，定义

$$
A=\mathcal U C,\qquad B=C\mathcal U,
\tag{10.2}
$$

其完整 Kraus 分别为 $A_i=SK_i$、$B_i=K_iS$。这些是 [QM] 定义 17.2 与 《五窗口切换记忆》 第 2 节的既有见证，下面明确所有所需全输入对应。

**命题 10.2（全映射和共同 Gram 的合法性）。** $C,A,B$ 都属于 $\mathcal L_{1/2}$，Gram 和 Choi 秩均二。

证明。正交的 $u,v,z$ 给出

$$
K_0^\dagger K_0=E_0+E_2/2+E_4,\qquad
K_1^\dagger K_1=E_1+E_2/2+E_3,
$$

和为 $I_5$，故 Kraus 映射 CPTP。对每个复 $X$，

$$
\operatorname{diag}C(X)=
\bigl((X_{00}+X_{11})/2,\ X_{22}/2,\ X_{33}+X_{44},\
       (X_{00}+X_{11})/2,\ X_{22}/2\bigr)^{\mathsf T}.
\tag{10.3}
$$

这是因为三个方向 $u,v,z$ 的计算基支持互不相交，它们自身外积的总系数分别为 $X_{00}+X_{11},X_{22},X_{33}+X_{44}$，交叉算子的对角为零。独立输入或输出的对角酉共轭保持 (1.2)，故 $A,B$ 也合法且 TP。

为给出所有重叠的联合实现，取同一正交环境对 $f_0,f_1$、$c=q(f_0+f_1)$。按 (2.5) 顺序，三个实际列表为

$$
\begin{aligned}
f^C&=(f_0,f_1,f_0,f_1,c,c,f_1,f_0),\\
f^A&=(f_0,f_1,f_0,f_1,-c,c,f_1,f_0),\\
f^B&=(f_0,-f_1,f_0,-f_1,c,c,f_1,f_0).
\end{aligned}
\tag{10.4}
$$

完整 Gram 可由以下显示因子逐项确定，无未指定条目：

$$
F_C=\begin{pmatrix}1&0&1&0&q&q&0&1\\0&1&0&1&q&q&1&0\end{pmatrix},
\quad
F_A=F_C\operatorname{diag}(1,1,1,1,-1,1,1,1),
\quad
F_B=F_C\operatorname{diag}(1,-1,1,-1,1,1,1,1),
\quad G_D=F_D^\dagger F_D\ (D=C,A,B).
\tag{10.5}
$$

它们同时 PSD、单位对角且有三个规定零；前两列独立，所以恰为秩二。完整 Choi 的活动块是 $\operatorname{diag}(q,q,q,q,q,q,1,1)\overline{G_D}\operatorname{diag}(q,q,q,q,q,q,1,1)$，其余行列为零，保留 (2.4) 的反序。列表来自实际完整 Kraus，不是独立指定的两两模长。$\square$

**命题 10.3（永久经典位及交替全映射）。** 置

$$
P=|s\rangle\langle s|,\qquad M=(P_R-P)/2.
\tag{10.6}
$$

它们是正交支持、同人口 $p=(1,1,2,1,1)^{\mathsf T}/6$ 的平稳密度，$C(P)=P$、$C(M)=M$。因此 $C$ 的重复永久保留距离二。对 $A,B,A,B,\ldots$ 的实际乘积，有全输入恒等式

$$
T_{2m}=C^{2m},\qquad T_{2m+1}=\mathcal U C^{2m+1}\quad(m\ge0).
\tag{10.7}
$$

编码 $P,M$ 在偶数时刻输出 $P,M$，奇数时刻输出 $SPS,SMS$，以终端投影 $\{P,I-P\}$ 或 $\{SPS,I-SPS\}$ 按公开奇偶读出，永远零误差。

证明。在 $R$ 的有序基 $(u,v,z)$ 上，$C$ 的实际 Kraus 限制是 $qU_0,qU_1$，其中

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{10.8}
$$

两个置换都固定 $s$ 且保持 $R\cap s^\perp$，所以固定 $P$ 及该二维扇区的均匀密度 $M$。它们的支持正交，迹都为一；$\operatorname{diag}P=p$、$\operatorname{diag}P_R=3p$ 给出相同人口。

$S^2=I$ 使每个实际两步 Kraus 词满足 $B_jA_i=K_jK_i$，故在整个 $M_5$ 上 $BA=C^2$；同理 $AB=\mathcal U C^2\mathcal U$。按实际顺序归纳便得 (10.7)，包括时间零。若从 $B$ 开始，则有

$$
T_{2m}=\mathcal U C^{2m}\mathcal U,\qquad
T_{2m+1}=C^{2m+1}\mathcal U,
\tag{10.9}
$$

相应初始对为 $SPS,SMS$，读出相位互换。所有等式都是完整映射恒等式，包含瞬态输入和复交叉项，张量任意参考仍成立。

正交输出的距离始终二，所以这些词的 $\delta$ 恒一。对任意重置密度 $\sigma$，三角不等式给出

$$
2\le\|T_n(P)-\sigma\|_1+\|T_n(M)-\sigma\|_1
                    \le2\|T_n-\mathcal R_\sigma\|_\diamond,
\tag{10.10}
$$

交替时用对应相位输入即可。故每个时刻到每个重置的距离至少一；允许逐时刻优化重置也不能遗忘。$\square$

**命题 10.4（A、B 各自却混合）。** 单独重复两个更新时，

$$
A^n\longrightarrow\mathcal R_{P_{R_-}/3},\qquad
B^n\longrightarrow\mathcal R_{P_R/3}
\quad\text{于 diamond 范数},\qquad R_-=SR.
\tag{10.11}
$$

证明。$A$ 的全部输出在 $R_-$ 内。在正交基 $(u,v_-=Sv,z)$ 上，实际限制为 $qU_0,qV_1$，其中

$$
V_1=\begin{pmatrix}0&-1&0\\0&0&1\\1&0&0\end{pmatrix},\qquad
U_0^2=I,\quad V_1^3=-I.
\tag{10.12}
$$

具体地，$A_0(u,v_-,z)=q(u,z,v_-)$，$A_1(u,v_-,z)=q(z,-u,v_-)$。若平均共轭 $F_A=(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{V_1})/2$ 满足 $F_A(X)=\lambda X$、$|\lambda|=1$，等长向量平均的 Hilbert–Schmidt 范数取等迫使两个共轭都等于 $\lambda X$。这个等号直接由

$$
\left\|\frac{Y_0+Y_1}2\right\|_2^2
=\frac{\|Y_0\|_2^2+\|Y_1\|_2^2}2-\frac{\|Y_0-Y_1\|_2^2}4
$$

得到。两个共轭的阶分别整除二和三，所以 $\lambda^2=\lambda^3=1$，即 $\lambda=1$。

固定 $X$ 必与 $U_0,V_1$ 对易。令

$$
J=U_0V_1=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&1\end{pmatrix}.
$$

则 $J^2=\operatorname{diag}(-1,-1,1)$，$V_1J^2V_1^\dagger=\operatorname{diag}(-1,1,-1)$。二者的共同特征空间恰为三条坐标线，故 $X$ 对角；再与循环带符号置换 $V_1$ 对易，使三个对角元相等。因此固定空间恰为标量。$F_A$ 是 Hilbert–Schmidt 收缩，幂有界，单位圆 Jordan 块不可能非平凡；其余 Jordan 项衰减，保迹确定限制极限为 $Y\mapsto I_{R_-}\operatorname{Tr}Y/3$。

对任意完整输入 $X$，第一步 $A(X)$ 已在 $\mathcal B(R_-)$，且保留原迹，所以相同极限适用于全 $M_5$，包含初始支持外的输入和所有交叉项。全矩阵单位收敛和 (9.7) 的 SVD 放大给出 diamond 收敛。最后 $B=\mathcal U A\mathcal U$，共轭传递得到第二个极限。这里没有将 $A$ 或 $B$ 误认成 $C$ 的固定对角共轭；它们是彼此对角共轭。$\square$

**约定 10.5（精确量子位与经典标签的不同结论）。** 《五窗口切换记忆》 定理 8.1 对每个固定内部参数、每个预定义允许序列证明：三步及以后，任意复子空间上的终端精确可恢复维数恰为一。其证明使用实际连续前缀、支持综合征形式、不同下一通道的全范围传递和最终通道的完整复强迫平面矛盾；没有中途恢复。本卷不把该精确量子位结论当作经典遗忘的证明。引理 4.2 只另证本卷所需的两条始终纯轨迹特例。半参数永久保留的是两个正交扇区的经典标签，不是永久复量子位；有限 NPT、精确码和渐近经典标签也是不同性质。这里不新增纠缠破坏指数或容量断言。

## 11. 周期变参数、固定参数推论与半参数邻界

**推论 11.1（周期变参数调度的唯一吸引轨道）。** 若 $K$ 排除半参数，任意周期 $\ell$ 的实际调度有唯一周期密度轨道

$$
\sigma_j=\Phi_j(\sigma_{j-1}),\qquad\sigma_\ell=\sigma_0.
\tag{11.1}
$$

基本周期可小于 $\ell$。取主定理种子 $\sigma_0$，则 $T_n(\sigma_0)=\sigma_{n\bmod\ell}$，在所有时刻有 (1.5)–(1.6) 的完整相位吸引界。实际相位人口是唯一周期解

$$
\pi_j=Q_{\eta_j}^{\mathsf T}\pi_{j-1},\quad\pi_\ell=\pi_0,
\qquad\pi_{j,i}\ge\kappa^4>0.
\tag{11.2}
$$

不同相位不要求有同一人口或同一密度。

证明。令周期乘积 $F=\Phi_\ell\cdots\Phi_1$。任一种子的 $m$ 项 Cesàro 平均在 $F$ 下差范数至多 $2/m$；密度空间紧，收敛子列给出固定密度 $\sigma_0$。若有两个固定密度，其差在 $F^m$ 下不变，而 $F^m$ 是实际长度 $m\ell$ 允许词，(9.9) 使该差趋零，所以唯一。逐相位定义 $\sigma_j=T_j(\sigma_0)$ 得闭轨道；任何其他周期轨道也在相位零给出固定密度，故相同。周期性与主定理给出完整复参考吸引。

固定轨道对角给 (11.2) 的解。对任何两个人口周期解，重复实际经典周期词并用 (2.11)，其差亦趋零而又固定，故相同。每个相位沿周期向前回溯足够整周期，使最后四步存在；用引理 2.3 得各坐标至少 $\kappa^4$。这没有将时钟寄存器加进保留数据空间。$\square$

**命题 11.2（二周期人口的完整公式）。** 对任意 $a,b\in(0,1)$，记 $r=1-a$、$s=1-b$、$\Delta=1-ab>0$。以 $a$ 更新结束时为相位 $a$，唯一经典周期人口是

$$
\pi^a=\frac{(r^2s,\,ars,\,br,\,ars,\,a^2s)^{\mathsf T}}{\Delta},
\qquad
\pi^b=\frac{(s^2r,\,bsr,\,as,\,bsr,\,b^2r)^{\mathsf T}}{\Delta}.
\tag{11.3}
$$

若 $a,b$ 均非半参数，任意完整通道二周期都有推论 11.1 的唯一吸引密度轨道；特别 $b=1-a$、$a\ne1/2$ 不提供永久标签的例外。

证明。所有分子严格正。第一个分子之和为 $s(r+a)^2+br=s+br=1-ab$，第二个为 $r(s+b)^2+as=r+as=1-ab$。相应 $\mathsf A$ 质量都是 $rs/\Delta$；相位 $a,b$ 的坐标二分别为 $br/\Delta,as/\Delta$，$\mathsf D$ 质量分别为 $as/\Delta,br/\Delta$。所以

$$
Q_a^{\mathsf T}\pi^b
 =\frac{(r\cdot sr,\ r\cdot as,\ br,\ a\cdot sr,\ a\cdot as)^{\mathsf T}}{\Delta}
 =\pi^a.
$$

互换 $a,b$ 得另一更新等式。引理 2.3 对重复二周期经典词给唯一性，不需要二者排除半参数。量子吸引及不存在正距离极限则在二者均非半参数时取 $K=\{a,b\}$ 应用主定理；没有把这句话扩展成含半参数的强制交替分类。$\square$

**推论 11.3（固定参数及词内常参数紧集）。** 对每个固定 $\eta\ne1/2$，$K=\{\eta\}$ 给出固定参数全部切换词的共同有限块和实际重置界。对任意非空紧 $K\subset(0,1)\setminus\{1/2\}$，主定理同样控制“每个词先选一个 $\eta\in K$、词内保持该参数”的子类；这是更强独立变参数结论的直接限制，不需另一有限覆盖论证。

单个通道重复时有唯一平稳密度 $\sigma_\Phi$，全复输入及任意有限参考趋于其重置。其人口为

$$
p_\eta=\frac{(r^2,\eta r,\eta,\eta r,\eta^2)^{\mathsf T}}{1+\eta}.
\tag{11.4}
$$

固定人口矩阵保留有用的精确恒等式：令 $\Pi=\mathbf1p_\eta^{\mathsf T}$，则

$$
Q_\eta^n=\Pi+(-\eta)^{n-2}(Q_\eta^2-\Pi)\quad(n\ge2),
\qquad
\|vQ_\eta^n-p_\eta^{\mathsf T}\|_1\le2\eta^{n-2}
\tag{11.5}
$$

对每个概率行 $v$ 成立。

证明。前两个词类是主定理所量化词类的子集。单个通道的唯一平稳重置是推论 11.1 的 $\ell=1$ 情形，包含全部瞬态和复交叉输入。

为识别固定人口及精确公式，$Q^2$ 的前三行是 $a_Q=(r^2,0,\eta,r\eta,0)$，后两行是 $b_Q=(0,r,0,0,\eta)$。其由两步实际路径分组得到。继续一步有

$$
a_QQ=ra_Q+\eta b_Q,\quad b_QQ=a_Q,
\qquad p_\eta^{\mathsf T}=(a_Q+\eta b_Q)/(1+\eta).
\tag{11.6}
$$

因此该概率严格正且平稳，$Q\Pi=\Pi Q=\Pi$，并在 $Q^2$ 的两种行上都有 $(Q^2-\Pi)Q=-\eta(Q^2-\Pi)$。由 $n=2$ 归纳得 (11.5) 第一式；$vQ^2$ 与 $p_\eta^{\mathsf T}$ 都为概率，差范数至多二，给第二式。任一平稳概率在其下的迭代极限只能为 $p_\eta$，故唯一。单个量子通道平稳密度的对角满足该平稳式，所以是 (11.4)。当 (11.3) 的 $a=b=\eta$，用 $1-\eta^2=r(1+\eta)$ 逐项约去 $r>0$，亦得同一人口。以上恒等式只用于固定参数推论，不用于变参数纯线证明。$\square$

**命题 11.4（连续合法族与靠近半参数的非一致性）。** 对任何 $S\subset(0,1)$，若其闭包包含 $1/2$，则不存在趋零函数能统一控制所有参数属于 $S$ 的实际词到重置的误差，即使每个词、每个时刻可优化重置密度。即便 $S$ 不含半参数也如此。

证明。保持第 10 节 $C$ 的实际环境列表不变，对每个内部参数定义

$$
\begin{aligned}
u_\eta&=\sqrt{1-\eta}\,e_0+\sqrt\eta\,e_3,&
v_\eta&=\sqrt{1-\eta}\,e_1+\sqrt\eta\,e_4,\\
K_0(\eta)&=|u_\eta\rangle\langle e_0|
       +\tfrac1{\sqrt2}|v_\eta\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1(\eta)&=|u_\eta\rangle\langle e_1|
       +\tfrac1{\sqrt2}|v_\eta\rangle\langle e_2|+|z\rangle\langle e_3|,\\
C_\eta(X)&=\sum_{i=0}^1 K_i(\eta)XK_i(\eta)^\dagger.
\end{aligned}
\tag{11.7}
$$

正交的 $u_\eta,v_\eta,z$ 使 Kraus 平方和仍为 $I$。同一共同 Gram 及当前参数边权重通过引理 2.1 给合法性；也可直接用三个不交坐标支持，得到任意复 $X$ 的对角

$$
(r(X_{00}+X_{11}),\ rX_{22},\ X_{33}+X_{44},\
 \eta(X_{00}+X_{11}),\ \eta X_{22})^{\mathsf T}.
$$

因此 $C_\eta\in\mathcal L_\eta$，且对参数连续，半参数恰为 $C$。第 10 节固定的 $P,M$ 给每个固定有限 $n$ 的连续极限

$$
\|C_\eta^n(P)-C_\eta^n(M)\|_1\longrightarrow2
\qquad(\eta\to1/2).
\tag{11.8}
$$

故对每个固定 $n$，这些合法常参数词的迹系数上确界为一。对任意密度 $\sigma$，三角不等式使两个输入中至少一个的重置误差不小于上述输出距离一半；所以即使优化 $\sigma$，其 diamond 误差的参数上确界仍至少一。若 $S$ 含半参数，直接用 $C$；若不含，沿 $S$ 中趋于半参数的参数取该连续极限。它们都是独立变参数词的合法子类，因而排除整个类的共同趋零界。这里先固定 $n$，不交换两个极限，也不声称任何单个离半参数的 $C_\eta$ 不遗忘。$\square$

## 12. 来源对应、操作成本与准确边界

**约定 12.1（来源与所用条件）。** 以下来源定位只表明所给文本的数学对应，不独立认证嵌入链接的版本，也不作全球原创性或文献优先权判断。一般方法与模型中特定的移动支持代数分开归属。

| 给定来源或标准方法 | 精确对应及使用范围 |
| --- | --- |
| [量子记忆卷][QM] 定义 2.2、定理 4.1–4.2 | 本卷 (1.1)–(1.2) 的同一个五维全复输入模型，参数逐字母对应 $\eta_j$；第 2 节重建每个实际字母自身的共同八向量与完整 Choi 条件。不同字母不共享环境。 |
| [半参数卷][HG] 定义 2.1–2.3 | 本卷 (2.5) 的环境顺序与反序共轭 Choi。它是 [QM] 一基边序 (4.3) 的置换 $(1,2,6,7,3,8,4,5)$；$\eta=1/2$ 时六个非强制边权均 $1/\sqrt2$。 |
| [QM] §3、定理 29.1 | 所选固定有限活动 Perron–Markov 源有 $\lambda=\eta/(1-\eta)^2$，固定人口为 (11.4)，精确幂为 (11.5)。半参数对应该选定源的 $\lambda=2$。这些是每个固定参数的来源接口，不将变参数调度识别为一个平稳固定活动源。 |
| 本卷所给固定参数来源稿第 3–9 节 | 相容中点抽取、移动支持运输、源目标超平面压缩、U/V 排除及固定纯线的三时刻消去提供直接结构来源。本卷将固定 $p,\psi,K$ 换为实际 $\pi_t,\psi_t,a_t,K_t$ 并给出变参数所需的新桥梁；固定参数定理由推论 11.3 统一继承，不作为较强定理的循环前提。 |
| 所给变参数提案 P1–P12 | 提供四步图路径合流、共同移动人口提取、源参数 V 型效应及变参数消去路线的候选推导。第 2–9 节列全所需符号证明：先从范数推出 $\eta_{t+1}\le1/2$，再证明 $\operatorname{Re}H>0$，最后用下一参数的范数恒等式强迫半参数。提案身份不提供批准或独立核验。 |
| [QM] §§32–35；[HG] 引理 3.1、4.1 | 平稳/交换支持、全输入压缩与纯线结构的来源。本卷处理不同源目标合支持，(6.6) 用源参数 $\eta_t$；纯线部分用真正时变 $K_t,W_t$。没有将同质结构分类或半参数个体 Gram 分类当成任意混合词定理。 |
| [QM] 定义 17.2、定理 17.3、18.1；《五窗口切换记忆》 第 2–4 节 | 第 10 节的 $C=\Phi_\circ$、完整 $A,B$、实际联合 Gram、个体全空间混合、两种实际交替乘积与终端经典位均为这些既有构造的复用。重建合法性和证明是为独立阅读，不列作新的固定通道数学成果。 |
| 《五窗口切换记忆》定理 8.1；[QM] 定理 9.1–9.2 | 固定内部参数的尖锐三步终端精确量子位障碍及复强迫平面来源。约定 10.5 只在其原固定参数范围陈述；变参数这里只得定理 9.3 的隐式有限时域，引理 4.2 另证两条纯轨迹的直接特例。 |
| [QM] §§27–30；《五窗口切换记忆》§§10–11 | 秩一重人口帽的完整混态几何、显式小参数充分界和 SVD 放大保留独立用途。固定 $0<\eta<(5-\sqrt{17})/4$ 的显式率由这些给定结果供应；帽判据失效不否定其他遗忘机制。本卷一般定性存在性不自动提供同样显式率。 |
| [Choi][CHOI]、[Stinespring][STI] | CP 与正 Choi、向量化 Kraus 和等距 dilation 的标准有限维表示。本卷的边权、复共轭次序及 TP 偏迹均已直接展开。 |
| [Gaubert–Qu][GQ] §7；[Szehr–Wolf][SWOLF] §II.B | Dobrushin 迹系数、复合不等式及正交输出等号的标准框架。第 3 节给出所用直接证明。四步 Doeblin 分解只在经典随机矩阵上实施；不由同质算子空间稳定性或同质 24 步界推出任意词时域。 |
| [Burgarth 等][MIX] 的支持正性框架；标准投影论证 | 第 4 节在实际密度支持上直接证明运输，不用全空间忠实性。第 6 节先证等范数和二维投影到投影，再推出双随机性；不对任意秩一效应冒用该结论。 |
| 紧致性、对角抽取、Cesàro 平均及 SVD | 都是标准有限维方法。第 3 节保证所有实际转移、正交和人口条件同时实现；第 9 节以完整复 SVD 控制任意参考；第 11 节将周期乘积固定点接回真实相位轨道。 |

本卷的模型特定推导是完整五窗口类中这些关系的变参数组合，特别是移动人口几何与两个实际消去求值。一般表示、紧致性、Dobrushin/Doeblin、支持正性、投影方法和 SVD 均不据为本卷发明。

标准文献标识沿用给定文本：W. F. Stinespring，*Positive Functions on C*-Algebras*，Proc. Amer. Math. Soc. 6，211–216；M.-D. Choi，*Completely positive linear maps on complex matrices*，Linear Algebra Appl. 10，285–290；S. Gaubert 与 Z. Qu，*Dobrushin’s Ergodicity Coefficient for Markov Operators on Cones*，arXiv:1307.4649v3；O. Szehr 与 M. M. Wolf，*Perturbation Bounds for Quantum Markov Processes and their Fixed Points*，arXiv:1210.1171v2；D. Burgarth、G. Chiribella、V. Giovannetti、P. Perinotti 与 K. Yuasa，*Ergodic and Mixing Quantum Channels in Finite Dimensions*，arXiv:1210.5625v3。它们在此是给定来源的准确归属标识，不表示本文打开链接核对过外部版本。

**约定 12.2（资源与常数取得成本）。** 所有操作计数按模型合同解释，不换成未给定的物理或总成本。

| 项目 | 实际使用与未求得的成本 |
| --- | --- |
| 保留数据 | 始终一个 $\mathbb C^5$。支持平面和逻辑坐标不增加寄存器；无额外输入副本、环境记录、综合征或输入相关历史。 |
| 实际次数 | $n$ 就是 $n$ 次完整允许更新。每步一个新鲜环境相互作用并丢弃；单步最小环境维数二至八，不累计保留。形式 Kraus 展开可有至多 $8^n$ 个词，它们不是可访问分支。 |
| 参数与映射控制 | 每个时间需提供实际 $\eta_j$ 和一个实际合法通道的表示，且事先独立于标签。有限 $K$ 仍需程序选择字母；无限 $K$ 不预设有限精确调度描述。任意无限调度可需要无界的公开程序资源。 |
| 表示尺寸 | 每个字母可用完整 $8\times8$ 复 Hermitian Gram 或等价八边 Choi 块表示；完整 Choi 为 $25\times25$，复超算子为 $25\times25$，$\delta$ 作用于实维二十四的无迹厄米空间。任意实参数或 Gram 的有限硬件精确合成没有被给出。 |
| 量子块常数 | $N_K$ 是某个满足 $a_N(K)<1$ 的有限长度，$q_K=a_{N_K}(K)\in(0,1)$。二者只有存在性及隐式定义，没有计算、寻找、认证算法、复杂度或精度方案。四步经典界不能替代它们。 |
| 条件误差应用数 | 若另已取得可用 $N_K,q_K$，对 $0<\epsilon<2$，$n=N_K\lceil\log(10/\epsilon)/(-\log q_K)\rceil$ 次完整更新足够给显示的 diamond 误差界。这只是在给定常数后的应用计数，不是获得常数的算法或效率认证。 |
| 半参数固定例 | $C$ 单独重复即可保留经典位，每步新鲜二维环境，最后一次两结果投影测量。 |
| 半参数交替例 | 两个固定完整更新 $A,B$，各 Gram/Choi/最小环境秩二；每周期两次更新，并支付公开起始相位、终端奇偶和相位选择控制。相位不承载输入标签。 |
| 实际相位算子 | 若按 (10.2) 分解，每个 $A$ 支付一次输出 $S$，每个 $B$ 支付一次输入 $S$，均是完整更新的一部分。相邻相位抵消是映射等式，不是免费中途恢复。第 7 节 $D_t$ 仅为证明规范。 |
| 终端经典读出 | 从 $\{P,I-P\}$ 与 $\{SPS,I-SPS\}$ 中按已知相位选一次测量；若统一用前一个读出，可另支付至多一次终端 $S$。未知相位是另一合同。 |
| 外部参考及恢复 | 任意有限参考仅为不受作用的数学检验，因子十不随其维数增加；不授权编码方使用它。终端 CPTP 恢复若用于码断言，只在最后执行，不提供途中恢复或分支访问。 |

这些表示维数、应用次数和控制合同不等于硬件门数、物理时间、本征完整窗口次数、全部工作量或总存储成本。没有由证明规范免费生成调度、实现相位、合成映射或获得精确常数。

**约定 12.3（定性完成范围与有效率缺口）。** 在一个非空紧 $K\subset(0,1)$ 的完整类、预定义输入无关调度及新鲜丢弃环境合同下，全部词一致遗忘的定性当且仅当是半参数不属于 $K$。固定参数、词内常参数紧集、任意同侧或跨半参数紧集、离半参数的互补二周期均已包含，没有留下未说明的离半参数定性区间。半参数反方向只需允许选择合法恒定 $C$，不要求调度实际访问 $K$ 中每个元素。

真正尚缺的是有效量子率：从端点分离 $\kappa=\min_K\min(\eta,1-\eta)$ 与半参数分离 $d=\min_K|\eta-1/2|$ 等可用数据，求共同有限长度 $N_K$ 及可认证 $q_K<1$ 的有效上界、算法和精度成本。这里没有这样的公式，也没有最优率、最优前因子、普遍 24 步混合词时域或有限搜索算法。近取等的定量支持分析必须处理量子支持退化，不能假设非零量子特征值有统一正下界。必要下界 (9.4) 也禁止由存在性声称任意快的遗忘；靠近半参数的共同趋零界由命题 11.4 排除。

未分类被强制交错使用半参数及非半参数的调度、所有半参数调度或每个半参数 Gram；$\{A\}$ 的个体混合与 $\{A,B\}$ 的交替记忆已表明受限字母类的量词不同。非闭子类不能直接取得引理 3.2 的达最大值见证，但排除半参数紧集完整类中的任何子类继承其上界。非紧参数集接近端点的全局分类、一般变参数的尖锐精确码时域及未知相位读出模型仍是不同问题。

人口严格正不推出量子密度全空间忠实，也不推出 CP 重置下界；个体混合不推出任意交替混合；精确量子位消失不推出经典标签遗忘。主定理只保证接近实际 $T_n(\tau)$，不保证所有词有共同固定密度或一般非周期状态轨迹有极限。有限 NPT、精确子空间码、经典零误差标签和渐近重置各有不同含义；没有由渐近重置新增有限纠缠破坏指数或量子容量结论。

端点参数、反馈、环境或分支访问、途中主动恢复、额外输入相关历史及更大保留系统均超出此定理。经典源接口不提供从同一个局部边缘到任意实际源、从源到 CPTP、从更新次数到本征窗口计时、Hamiltonian、场论或物理实现的桥梁。所有数学论证均未执行；没有数值、公式计算、实验、数学测试、构建或 Lean 内核核验。字节与 JSON 身份核对不验证数学。本文不提供形式内核、物理、经验机器学习、全球新颖性、总资源或持续目标完成认证。

[QM]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[HG]: AURIC_FIB_FIVE_WINDOW_HALF_GRAM_CLASSIFICATION.md
[GQ]: https://arxiv.org/pdf/1307.4649v3
[SWOLF]: https://arxiv.org/abs/1210.1171v2
[CHOI]: https://doi.org/10.1016/0024-3795(75)90075-0
[STI]: https://doi.org/10.1090/S0002-9939-1955-0069403-4
[MIX]: https://arxiv.org/pdf/1210.5625v3

## 追加锚（本行以下为增补区）
