# AURIC C128：原有限门词校准与固定有向关系

## 319. 同一原有向关系的字面端点标定问题

**定义 319.1（原对象与原生矩阵的分别身份）。** 母卷为 [C123 原生互易比较母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，前续卷为 [共同框架与半角关系续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)，配平续卷为 [原生切口配平续卷](AURIC_C128_NATIVE_CUT_BALANCE_CONTINUATION.md)。原 $d_A$ 始终是母卷假设 1.5、[前续卷定义 293.2](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#293-左单位中性候选与原有向关系的类型) 中预先固定的向量值实双线性关系，$D_ab=d_A(a,b)$；其评价为原准备的 $\alpha(D_ab)$，不是正事件。以下原生矩阵取 [native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#1-原来源完整端点与不变的实际读取) 的同一来源：
$\mathcal K=\mathbb C^E$、$|E|=89$、唯一 ready $e_{\rm r}=e_{\{3,7\}}$、全部十一原地址、原记录 $M_i$、全部旧终端 $N_w$、原失败与合法性。令

$$
\begin{gathered}
\mathsf W_{11}=\{0,\ldots,10\}^{<\infty},\quad
\mathsf W_7=\{0,\ldots,6\}^{<\infty},\quad
K_{gh}=K_hK_g,\quad \chi_a=K_ae_{\rm r},\\
\vartheta=3\pi/5,\quad \zeta=e^{\mathrm i\vartheta},\quad
K_j=\zeta[I+(\zeta-1)\mathcal P_j],\quad
\mathcal P_j^2=\mathcal P_j,\quad K_j^{10}=I.
\end{gathered}
\tag{319.1}
$$

原事件 $A=\{b_1=1\}$ 是旧标签中该位为一的分组，故

$$
Q=\sum_{w:\,b_1(w)=1}N_w=n_1=\mathcal P_0,\qquad Q^2=Q,\quad Q\ne0,I.
\tag{319.2}
$$

这里 $\Omega_{10}$ 中全部 $1024$ 个旧标签仍在；非法标签的投影仍为零。$A$ 不是新增读口。

若 $g=(j_1,\ldots,j_m)$，记 $g^-=(j_m^9,\ldots,j_1^9)$，其中 $j^9$ 表示九次原正向调用。于是 $K_{g^-}=K_g^{-1}$，包括边界单点、阻塞分量和代码补空间。它是端点逆字，不是原路径核的时间反演。置

$$
A_g=K_g^*QK_g,\qquad
U_g=K_g^*K_0K_g=\zeta[I+(\zeta-1)A_g].
\tag{319.3}
$$

两个字面菜单 $g\,0\,g^-h$、$g\,0^9g^-h$ 都是十一地址读前词；$h$ 后接原旧终端。所有实线性组合仅为响应商中的运算，不供应凸混合、reset、并行副本或相干控制。

**假设 319.2（限定切口的来源采用与新 D 等式）。** 在一个指定原对象的读前切口，另须已经供应保原响应的含幺 Jordan 同构 $\theta:E_A\to H_{89}(\mathbb C)$，以及同一原 ready 前缀准备的评价

$$
\alpha_a(x)=\operatorname{Tr}(\rho_a\theta x),\qquad
\rho_a=|\chi_a\rangle\langle\chi_a|.
\tag{319.4}
$$

原字和旧终端在这些坐标中确为 (319.1)–(319.3)，并具有该复载体上的 Born 数值。这里只在这个已付接口内写 $D$ 的矩阵坐标，未把 $\theta$ 或 (319.4) 从 native 的名称推给任意 C123 对象。

对有限原字表 $G,H,F$，分别记其元素为 $g_r,h_s,a_l$。新来源前提是下列关于**同一原 D** 的有符号响应等式：

$$
\begin{aligned}
\mathsf{Cal}_{lrs}:\quad
\alpha_{a_l}\!\left(D_{\theta^{-1}A_{g_r}}(\theta^{-1}A_{h_s})\right)
&=\frac{p^-_{lrs}-p^+_{lrs}}{4\sin\vartheta},\\
p^+_{lrs}&=P_{\mathsf T(a_lg_r0g_r^-h_s)}(A),\\
p^-_{lrs}&=P_{\mathsf T(a_lg_r0^9g_r^-h_s)}(A).
\end{aligned}
\tag{319.5}
$$

概率各自属于一个原外生请求，差不是新事件；此处不要求两请求有一份额外可访问的共同反事实样本。$\sin\vartheta>0$，因为 $0<3\pi/5<\pi$。新等式没有用交换子定义原 $d$，也没有要求一般 CP 事件保持它。

## 320. 有限原词对固定 D 的全响应呈示

**定理 320.1（读前有限标定及原线性关系相容）。** 在假设 319.2 的已付来源接口中，可以选择有限原字表 $G,H,F$，只依非 $D$ 数据，使 $\{A_{g_r}\}$、$\{A_{h_s}\}$ 实张成整个 $H_{89}(\mathbb C)$，而 $\{\rho_{a_l}\}$ 在迹配对下分离它。对任意事先固定的原实双线性 $D$，

$$
\{\mathsf{Cal}_{lrs}:\text{全部有限 }l,r,s\}
\quad\Longleftrightarrow\quad
\theta(D_ab)=\frac{\mathrm i}{2}[\theta a,\theta b]
\quad(a,b\in E_A).
\tag{320.1}
$$

此呈示尊重输入向量的全部实线性关系，且恢复整个输出，不只恢复一组对角或同块读数。可各取 $89^2=7921$ 个字组成基；这只是有限存在结论，没有列出字表、字长上界、条件数、含噪稳定性或取得与认证效率。

证明。直接复用 [native III (144.12) 及其前的全载体密度对应](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#144-一个未知终端事件与真实历史守恒的条件刻画)、[native II (121.7)](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md#121-同一个旧终端的三组事件与全效果域覆盖)：十一地址原字在 $PU(89)$ 稠密，原 ready 射线轨道稠密。其 FLW 对应是 $(k,r,n)=(2,5,12)$、图 $[6,6]$ 的全部 $89$ 张可容许表；没有从逻辑子码或七地址闭包外推。这是已有矩阵供应，不重证密度，也不以极限点增加实际准备。

先说明所用成熟张成步骤。若 Hermitian $T$ 与某个非平凡秩 $k$ 投影的全部酉共轭迹正交，在 $T$ 的本征基中任意 $k$ 个本征值之和均为零。比较共享 $k-1$ 个指标的两组，所有本征值相同；再由 $k>0$ 得它们为零。因此这些共轭实张成整个 Hermitian 空间。对 $Q$ 应用此步；共轭的相位消失，有限维线性子空间闭性使实际有限 $A_g$ 已有同样张成。原 ready 投影轨道同理张成：全部秩一投影分离 Hermitian 元。分别抽取有限基即得三个字表，选择不依原 $D$。这是算子框架中间步骤，非新增准备生成定理。

现在核对端点和符号。对任意投影 $P$ 及 Hermitian $B$，令 $V=I+(e^{\mathrm i\vartheta}-1)P$。展开或比较 $P$ 与 $I-P$ 的两个非对角矩形块，得

$$
\begin{aligned}
VBV^*-V^*BV
&=2\mathrm i\sin\vartheta\,[P,B],\\
p^-_{lrs}-p^+_{lrs}
&=\operatorname{Tr}\rho_{a_l}
 (U_{g_r}A_{h_s}U_{g_r}^*-U_{g_r}^*A_{h_s}U_{g_r})\\
&=4\sin\vartheta\,
 \operatorname{Tr}\rho_{a_l}\,\delta(A_{g_r},A_{h_s}),\qquad
\delta(X,Y)=\mathrm i[X,Y]/2 .
\end{aligned}
\tag{320.2}
$$

第二行的先后顺序来自 $K_{gh}=K_hK_g$；$0^9$ 给 $U_g^{-1}$，整体 $\zeta$ 相位相消。正反两菜单都是完整正向原词，不需要脉冲内部时刻或可调角度。这个二谱端点恒等式是成熟参数移位机制的代数形式，不作为独立新定理。

令 $\widetilde D(X,Y)=\theta(D_{\theta^{-1}X}(\theta^{-1}Y))$。有限等式遂令 $\widetilde D-\delta$ 在每个输入基对上被全部 $\rho_{a_l}$ 评价为零。分离性给该对的整个输出为零，实双线性再给 (320.1)；反向由 (320.2) 逐项成立。这里才把预先固定的原 $D$ 识别为 $\delta$。

为写清过完备表也不会按不同分解给出不同向量，允许在三个基中再加入任意有限原字，定义可逆框架算子

$$
S(X)=\sum_l\rho_{a_l}\operatorname{Tr}(\rho_{a_l}X),\qquad
\operatorname{Tr}(X\,S(X))=\sum_l(\operatorname{Tr}\rho_{a_l}X)^2>0\quad(X\ne0).
\tag{320.3}
$$

若 $X=\sum_rc_rA_{g_r}$、$Y=\sum_sd_sA_{h_s}$，整个原输出的呈示为

$$
\theta\!\left(D_{\theta^{-1}X}(\theta^{-1}Y)\right)
=\sum_{r,s,l}c_rd_s\,\frac{p^-_{lrs}-p^+_{lrs}}{4\sin\vartheta}\,S^{-1}(\rho_{a_l}).
\tag{320.4}
$$

由 (320.2)，$\sum_r\lambda_rA_{g_r}=0$ 蕴含每个 $l,s$ 上的 $\sum_r\lambda_r(p^-_{lrs}-p^+_{lrs})=0$；第二槽完全同理。若 $\sum_l\nu_l\rho_{a_l}=0$，每个 $r,s$ 上也有相应评价关系。故任一输入展开之差属于原线性关系核，输出不变；输出数据也尊重全部准备关系。$S^{-1}$ 是数学重构，不是实际仪器。逆向重构用到 $\sum_lS^{-1}(\rho_l)\operatorname{Tr}(\rho_lX)=X$，这是直接对 $S(X)$ 应用 $S^{-1}$。∎

**定义 320.2（相对既有有限框架的增量）。** 母卷 §§88–93 已将每个半重叠对的角外 primitive 读回有限化；配平续卷 §§89–90 已给原关系的余切下降与量子消费者。本定理不重新交付这些框架、几何或有限维代数。区别是 (319.5) 将固定原有向向量的评价，绑定到原 ready、原地址 $0$ 的正反端点词及同一旧标签分组，并明确所需的第一槽方向、第二槽方向和整输出分离。该绑定是新增来源前提，不由上述有限框架、非 $D$ 响应相同或密度自身取得；[前续卷 §§295–300](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#295-一份预先完整固定且保留经典分支的原签名) 的完整非 $D$ 同响应族保持原结论，不在这里另造一份全签名反模型。

## 321. 原记录零切口的第一槽缺口

**定理 321.1（同步门方向不能标定整个原响应的第一输入）。** 在 [native III 定义 151.1–定理 151.2](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的记录零切口，按同一字面前缀规范有

$$
E_0=H_{21}(\mathbb C)\oplus H_{21}(\mathbb C)\oplus H_{13}(\mathbb C),
\quad(s=000,010,100),\quad \dim_{\mathbb R}E_0=2\cdot441+169=1051.
\tag{321.1}
$$

所有合法七地址原脉冲的共轭方向连同单位都留在

$$
W_{\rm syn}=\{(X,X,Y):X\in H_{21},\,Y\in H_{13}\},
\qquad \dim_{\mathbb R}W_{\rm syn}=441+169=610.
\tag{321.2}
$$

事实上，原 $Q=\mathcal P_0$ 的七地址共轭加单位已张成该空间；这是[原生终端认证卷定理 13.1](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md#13-原七地址-a-效果的精确同步张成)的既有结论。即使全部原旧标签为第二槽、全部线性泛函为输出读回，全部这些第一槽的端点标定仍不能唯一确定 $E_0\times E_0\to E_0$ 的实双线性关系。可以显式保留双单位零、每个第一输入产生第二槽 Jordan 导子以及迹型斜伴随性而出现此歧义；这里不声称满足完整原 $B_*$、X 或 $\mathsf C_{0h}$。

证明。III151.1 逐路径给两个 $21$ 副本上的每个 $K_j$、$\mathcal P_j$ 完全相同，$0\le j\le6$；第三块维数为 $13$。同一七地址字的共轭仍同步，所以其方向包不超过 (321.2)。单位也同步。普通实迹内积下

$$
W_{\rm syn}^{\perp}=\{(T,-T,0):T\in H_{21}\},\qquad
\dim_{\mathbb R}W_{\rm syn}^{\perp}=441.
\tag{321.3}
$$

因为与任意 $(X,X,Y)$ 配对为 $\operatorname{Tr}((T_0+T_1)X)+\operatorname{Tr}(T_2Y)$，正交恰为 $T_1=-T_0,T_2=0$。这缺的是第一输入方向；与 III (151.5) 已有的逐尾标签读回不同。

给出原标签上的具体残差。令 $u$ 为六个前缀位全零、$v$ 为只有第一位占据的前缀路径；二者在两个 $21$ 块中都合法。以下 $\widehat u,\widehat v$ 指尾 $000$ 中的这两条路径，即完整配置 $\varnothing,\{1\}$。定义数学向量

$$
\begin{gathered}
e=|\widehat u\rangle\langle\widehat u|,\quad
f=|\widehat v\rangle\langle\widehat v|,\quad
H=|\widehat u\rangle\langle\widehat v|+|\widehat v\rangle\langle\widehat u|,\\
Z=\mathrm i(|\widehat u\rangle\langle\widehat v|
             -|\widehat v\rangle\langle\widehat u|),\qquad
\ell(a)=\langle u,a_{000}u\rangle-\langle u,a_{010}u\rangle,\\
D^\varepsilon_ab=\mathrm i[a,b]/2+
       \varepsilon\ell(a)\,\mathrm i[H,b]/2
\quad(a,b\in E_0,\ \varepsilon\in\mathbb R).
\end{gathered}
\tag{321.4}
$$

各 $D^\varepsilon$ 是不同局部比较模型中事先给定的关系，不是在同一已固定原世界里改写 $d$。这里 $H,Z$ 只在尾 $000$ 中支撑。$e,f$ 分别就是固定记录零后的原旧标签 $w(\varnothing)$、$w(\{1\})$ 的 $E^0_{\epsilon,w}$，不是新增制备或门。$\ell$ 在整个 $W_{\rm syn}$ 上为零，且 $\ell(I)=0$，故

$$
D^\varepsilon_ab=\delta_ab\quad(a\in W_{\rm syn},\ b\in E_0),
\qquad D^\varepsilon_Ib=D^\varepsilon_aI=0.
\tag{321.5}
$$

对每个固定 $a$，令 $C=a+\varepsilon\ell(a)H$，则 $C$ 是 Hermitian，$D^\varepsilon_a=\mathrm i[C,\cdot]/2$。直接展开乘积给 $[C,x\circ y]=[C,x]\circ y+x\circ[C,y]$，故为第二槽 Jordan 导子。对 $q_w(x,y)=\sum_sw_s\operatorname{Tr}(x_sy_s)$、$w_s>0$，迹循环性逐块给

$$
q_w(D^\varepsilon_ax,y)+q_w(x,D^\varepsilon_ay)
=\frac{\mathrm i}{2}\sum_sw_s\operatorname{Tr}(C_sx_sy_s-x_sy_sC_s)=0.
$$

这些性质没有偷用全局来源合同。

但 $\ell(e)=1$、$[e,f]=0$、$\mathrm i[H,f]=Z$，所以

$$
D^0_ef=0,\qquad D^\varepsilon_ef=\varepsilon Z/2\ne0\quad(\varepsilon\ne0).
\tag{321.6}
$$

这已是同一原标签第一输入上的明确歧义；所有同步方向上的**完整输出**却逐字相同。因此增加第二槽标签或输出准备不能补出第一槽的反同步方向。

残差确为非零 Hermitian 响应：$\eta=(\widehat u-\mathrm i\widehat v)/\sqrt2$ 满足 $\langle\eta,Z\eta\rangle=1$。不把 $\eta$ 当作新实际准备。由原 ready 的十一地址密度，可选一个实际有限前缀 $a_*$ 使

$$
\langle\chi_{a_*},M_0ZM_0\chi_{a_*}\rangle>1/2,
\qquad \|M_0\chi_{a_*}\|^2>0.
\tag{321.7}
$$

理由是左式在 $\eta$ 处为一且对射线连续，该严格开集与稠密原轨道相交。若另保留 Born 记录质量，原未归一分支评价 $\beta_{a_*,0}(x)=\langle\chi_{a_*},M_0xM_0\chi_{a_*}\rangle$ 遂在 (321.6) 的两关系间给绝对差大于 $|\varepsilon|/4$。没有 Born 记录采用时，只保留此矩阵分离结论，不从正投影范数推断实际分支质量为正。

本构造只给记录零响应载体上的双线性歧义；它对正交 $e,f$ 违反原正交零，也未提供全对象、实际联合和 X 保持的延拓，因此不是完整量子起源反模型。$H$ 没有被宣称可作独立尾控制。III (151.5) 虽以旧标签分别读到尾 $000,010$，它给的是第二槽效果，不能将 $g\,j\,g^-$ 的同一原脉冲变成只作用于一个副本的门。∎

## 322. 三实维角与全部原消费者的回接条件

**定义 322.1（有限标定的几何及全消费者接口）。** 在定理 320.1 的指定读前对象上，取数学正交 primitive $e,f$，$c=e+f$，以及该二维复角中的 $X=E_{12}+E_{21}$、$Z=\mathrm i(E_{12}-E_{21})$、$h=e-f$。由已识别的同一原 $D$，

$$
h^2=X^2=Z^2=c,\quad
h\circ X=h\circ Z=X\circ Z=0,\quad
D_eX=Z/2,\quad D_eZ=-X/2.
\tag{322.1}
$$

$\rho=(c+rh+sX+tZ)/2$ 为角内迹一正元恰当且仅当 $r^2+s^2+t^2\le1$，球面上为 primitive。这个三实维无迹截面及相交角共享原 $D$ 的含义复用母卷 §91、[前续卷定义 277.2](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#277-全部原系数三维角与逐字原-s)、[前续卷定义 309.2](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#309-来源对应与实质几何增量的准确范围)；不是物理空间三维，也不供应实际 $M_2$。

此处只将既有角几何作为定理 320.1 的后果使用，不另立 Bloch 或量子重构定理。矩阵相乘给 (322.1)；令 $V=rh+sX+tZ$，反对易使 $V^2=(r^2+s^2+t^2)c$，故 $\rho$ 的两个本征值是 $(1\pm\sqrt{r^2+s^2+t^2})/2$。每个角的取向都取自定理 320.1 识别的同一个双线性关系，未逐角挑选独立旋转。此结论的复载体和 Born 实现是 (319.4) 的前件，不能用它反过来推导自己的复／Born 来源。

若要将这种局部标定接回每个原对象，须另外给出同源的分离运输：对每个原 $A$，已标定目标 $T$ 的原实线性映射 $j_T:E_A\to E_T$ 必须同时满足

$$
j_T(a\circ b)=j_Ta\circ j_Tb,\qquad
j_T(D^A_ab)=D^T_{j_Ta}(j_Tb),\qquad
\bigcap_T\ker j_T=\{0\}.
\tag{322.2}
$$

这些条件确有代数下降作用：把原导子残差及原曲率残差分别经 $j_T$ 送出，目标的 $\delta$ 使每个像为零，分离再令原残差为零。因此得到的是**若有这些同一原映射**才成立的下降，不是由字密度自动产生映射。一般事件、特别 $M_0$ 读后的更新，未被假设保持 $D$；不能把它冒充 (322.2)。定理 321.1 表明甚至同一 native 来源的合法后读第一槽也须另补方向来源或有效下降。记录一的两个不同维数块没有上述同型副本障碍，但本文没有据此断言其脉冲方向完整张成或全前缀采用。

在所有原对象和实际联合上另已供应完整 $B_*$、同一原关系的 LU、$\mathsf G_{0h}$ 与同一 $\sigma_{t_0}$ 时，[前续卷定理 305.1–308.1](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#305-标定以前回到全部原对象) 才按原前件回接复乘法、全部原准备的 Born 双运输、保全部中心对的实际普通复张量、全事件及相关参考上的 CP/TNI、完整测试 TP、所选完整平方根词与每个完整失败、细记录／分组／遗忘、具名同数双返回和全部原合法有限历史。这里既不重证这些消费者，也不以 (319.5) 在一个 $89$ 维读前对象成立代替其全对象前件。

原来源到 $\theta$ 的识别、C123 精确正准备生成或其另名闭版本、零和非零原质量、全部实际联合及参考的共同实现、旧输出和失败、每条合法过去与未来的来源绑定，均未由定理 320.1 或 321.1 供应。native 原 ready 词的稠密轨道不等于所有准备的有限正锥恰为完整正对偶锥。物理时钟、能量／作用量与 $\hbar$、可靠控制和资源尺度、任意独立成功支的共同仪器组装及旧同效果设备的完整输出校准仍各需原条件。故完整唯一 $\Omega$ 的量子起源目标保持未解。∎

## 323. 来源输入与数学归属

**定义 323.1（既有工具、新等式与来源特定推导）。** 以下区分是命题适用条件的一部分：

| 来源 | 使用范围 |
| --- | --- |
| 母卷 1.1、1.5；[前续卷定义 293.2](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#293-左单位中性候选与原有向关系的类型) | 同一原响应商、原向量值实双线性 $D$、有符号评价；不将 $D$ 设为正事件，不给一般 CP 的 $D$ 保持。 |
| native XI1；III144、151；II121 | 原唯一 ready、原正向词／端点逆词、原标签、全十一地址密度、七地址同步尾块及完整标签效果空间。复载体及所用 Born 实现为输入，不是本节从原关系导出的量子公理。 |
| 原生终端认证卷 §§13–17；母卷 §§88–93；配平续卷 §§89–90 | 已有同步效果商、有限算子框架、原余切和角网。状态／后验不可见方向与此处第一输入 $D$ 的歧义分别承担自己的量词。 |
| [Freedman–Larsen–Wang，math/0103200v1](https://arxiv.org/abs/math/0103200v1)，Theorem 0.1、§2 Lemma 2.1 及 Definitions 1–2 | Jones 直和闭像包含各扇区 $SU$ 的乘积及投影表示；按 native 的既有路径对应复用，不把相同旁观副本当成独立因子。 |
| [D’Ariano–Perinotti–Sacchi，quant-ph/0310013v1](https://arxiv.org/abs/quant-ph/0310013v1)，§2 (4)–(8)、§3 | 算子框架、正可逆框架算子与对偶重构；不借其 POVM 构造来供应新测量。 |
| [Schuld 等，1811.11184v1](https://arxiv.org/abs/1811.11184v1)，§III.A Theorem 1 及 (12)–(14) | 两谱生成元的成熟精确参数移位机制；(320.2) 明写本来源固定角、原正向端点词和符号，不请求可调参数或辅助受控门。 |

这些一般中间工具为 $\texttt{literature-attested}$。本节 $\texttt{repo-derived}$ 的来源特定综合是 (319.5) 到同一固定原 $D$ 的有限全响应接口，以及 (321.4)–(321.7) 在原同步门第一槽上完全一致、在具体原标签第一输入上分离的残差。有限框架或参数移位本身不作为新增成果；这里不主张全球原创、较少独立公理或普遍认证效率。来源采用 (319.4) 与新增 D 等式 (319.5) 都是明确前提，后者尚无原来源推导；同步第一槽缺口也没有被已存在的完整标签读回填平。

## 追加锚 C128323（本行以下为增补区）

## 324. 原七地址第一槽与分别保留的三个尾块

**定义 324.1（同一固定关系与来源载体）。** 本节接续[原有限门词校准卷 §§319–323](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#319-同一原有向关系的字面端点标定问题)。母卷为 [C123 原生互易比较卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，支撑关系取[共同框架续卷 §§272–280、311–318](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#272-原正交零整输出支撑与一张预先固定的原标签)。原有向关系始终是这些条目中事先给定的实双线性 $d_A(a,b)=D^A_ab$，不是由下文的重构公式重新定义原 $d_A$。

固定 [native III 定义 151.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的记录零切口及字面前缀规范，记

$$
\begin{gathered}
E=H_{21}(\mathbb C)_{000}\oplus H_{21}(\mathbb C)_{010}\oplus H_{13}(\mathbb C)_{100},\qquad
u=(I_{21},I_{21},I_{13}),\\
\dim_{\mathbb R}E=1051,\qquad S=\{000,010,100\}.
\end{gathered}
\tag{324.1}
$$

$\pi_s$ 和 $\iota_s$ 是这份直和的数学投影与补零包含，$z_s=\iota_sI_{n_s}$。两个 $21$ 维尾块各有自己的原标签、准备评价与输出分量，未取其和，也不以同构合并。所有向量等式均在整个 $E$ 中成立。

在还未取得原对象 $E_A$ 与这个矩阵载体的含幺 Jordan 识别时，以下首先是字面矩阵载体上的条件命题。应用于原对象时另须给定保原响应的含幺 Jordan 同构 $\theta:E_A\to E$，并在本节记

$$
D(a,b)=\theta\bigl(D^A_{\theta^{-1}a}(\theta^{-1}b)\bigr).
\tag{324.2}
$$

这只是运输同一原 $D^A$，不假设一般原事件保持 $D$，也不从矩阵名称推出 $\theta$ 的存在。

**定义 324.2（实际脉冲效果空间）。** 取原旧事件 $A=\{b_1=1\}$、$Q_0=Q|_{\mathcal K_0}$，对原七地址有限字 $g$ 置

$$
A_g=K_g^*Q_0K_g\in E.
$$

直接复用[原生终端认证卷定理 13.1](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md#13-原七地址-a-效果的精确同步张成)：

$$
\begin{aligned}
\mathcal R&=\operatorname{span}_{\mathbb R}\{A_g:g\in\mathsf W_7\}
 =\{(X,X,Y):5\operatorname{Tr}X=8\operatorname{Tr}Y\},\\
\dim\mathcal R&=609,\qquad
\mathcal R+\mathbb R\nu=\mathcal S=\{(X,X,Y)\},\qquad\dim\mathcal S=610.
\end{aligned}
\tag{324.3}
$$

两类投影秩分别为 $8,5$，所以关系中的 $5,8$ 与维数 $21,13$ 各有不同来源。全部原旧标签效果
$B_{h,w}=E^0_{h,w}$ 则按 III151.2 实张成整个 $E$；固定合法标签已将其支撑限定在指定尾块，见 III (151.5)。第一槽的 $\mathcal R$ 与第二槽的完整标签空间不能互换。这里的实张成只在响应商内运算，不把线性组合变成实际混合、尾控制或新准备。

**定义 324.3（整输出的跨中心正交零）。** 对每个不同的有序尾块对 $s\ne t$，要求

$$
\mathsf O_\times:\qquad
D(\iota_se,\iota_tp)=0\ \text{于整个 }E,
\qquad e\in\operatorname{Prim}H_{n_s},\quad p\in\operatorname{Prim}H_{n_t}.
\tag{324.4}
$$

共同框架续卷 (272.1) 的完整 $\mathsf O$ 含有本条件。只说某个输出压缩为零、某个准备读数为零，或只检查同一尾块内的正交对，都不是 (324.4)。本节不先要求块内正常形、输出理想保持、SC、导子律、斜伴随、长度或单位曲率。

## 325. 六百零九维原方向决定整个原双线性关系

**定理 325.1（有标签第二槽下的原方向决定公式）。** 对 (324.1) 上任何事先固定的实双线性 $D:E\times E\to E$，若满足 $\mathsf O_\times$，则 $D|_{\mathcal R\times E}$ 唯一决定 $D$ 的全部值，因而 $D|_{\mathcal S\times E}$ 也唯一决定它。定义两个数学提升

$$
\begin{aligned}
J_{21}(X)&=\left(X,X,\frac{5\operatorname{Tr}X}{104}I_{13}\right),\\
J_{13}(Y)&=\left(\frac{8\operatorname{Tr}Y}{105}I_{21},
                         \frac{8\operatorname{Tr}Y}{105}I_{21},Y\right).
\end{aligned}
\tag{325.1}
$$

它们都取值于 $\mathcal R$。对所有完整 $a,b\in E$，有整输出公式

$$
\boxed{\begin{aligned}
D(a,b)={}&D(J_{21}(a_{000}),\iota_{000}b_{000})\\
&+D(J_{21}(a_{010}),\iota_{010}b_{010})\\
&+D(J_{13}(a_{100}),\iota_{100}b_{100}).
\end{aligned}}
\tag{325.2}
$$

特别地，对任何两个都满足本条件的固定关系 $D,\widetilde D$，若它们在全部实际 $A_g$ 的第一槽和全部旧标签效果 $B_{h,w}$ 的第二槽上具有相同的整个输出，则它们在 $E\times E$ 上相等。结论不需要 $D(a,\nu)=0$，所以不必把单位补成第 $610$ 个第一槽方向。

证明。Hermitian 元的谱分解将每块写成 primitive 投影的实线性组合。对不同块分别展开两个输入，双线性及 (324.4) 给

$$
D(\iota_sx,\iota_ty)=0\quad(s\ne t;\ x\in H_{n_s},y\in H_{n_t}).
\tag{325.3}
$$

这里只复用成熟有限维谱分解及既有正交展开步骤，不调用交换映射分类。(325.3) 是完整向量零，因此

$$
D(a,b)=\sum_{s\in S}D(\iota_sa_s,\iota_sb_s).
\tag{325.4}
$$

$5\operatorname{Tr}X=8\cdot13\cdot5\operatorname{Tr}X/104$，且
$5\cdot21\cdot8\operatorname{Tr}Y/105=8\operatorname{Tr}Y$，故 (325.1) 确在 $\mathcal R$。其对应块投影分别为 $X,Y$。在 (325.4) 的每项，将 $\iota_sa_s$ 换为对应的 $J_{21}(a_s)$ 或 $J_{13}(a_s)$，所添的其他块均被 (325.3) 消去，得到 (325.2)。两个 $21$ 维项使用相同形式的第一槽提升，却分别使用 $\iota_{000}b_{000}$ 和 $\iota_{010}b_{010}$；没有混同两个尾块或选择新的输出取向。

最后，(324.3) 与 III151.2 将实际 $A_g,B_{h,w}$ 上的相等双线性延拓到 $\mathcal R\times E$，再由 (325.2) 得全域相等。所有消去在输入槽进行；每一项的输出一直是整个 $E$，未假设它留在对应源块。∎

**定理 325.2（存在、唯一与原关系识别分别承担的条件）。** 设 $r:\mathcal R\times E\to E$ 是给定实双线性数据。存在满足 $\mathsf O_\times$ 且限制为 $r$ 的全域双线性关系，当且仅当

$$
r(x,\iota_tb)=0
\quad(t\in S,\ x\in\mathcal R\cap\ker\pi_t,\ b\in H_{n_t}).
\tag{325.5}
$$

若存在，它唯一，且由 (325.2) 中将右边 $D$ 换成 $r$ 给出。此唯一扩张等于一份预先固定的原 $D$，还必须取得该原 $D$ 自身满足 $\mathsf O_\times$ 以及 $D|_{\mathcal R\times E}=r$；选择一个扩张不供应这两条原等式。

证明。若已有这样的 $D$，当 $\pi_tx=0$ 时，$x$ 只含非 $t$ 的块，(325.3) 给 (325.5)。反之，以 (325.2) 的右边定义辅助关系 $D_r$。它实双线性；不同块输入时，第二槽所在块对应的第一坐标为零，所以 $D_r(\iota_sa,\iota_tb)=0$ 对 $s\ne t$ 成立。对 $x\in\mathcal R$，$x-J_{n_t}(\pi_tx)\in\mathcal R\cap\ker\pi_t$，其中 $J_{n_t}$ 按块大小取 (325.1) 的对应提升。因此 (325.5) 给

$$
D_r(x,b)=\sum_tr(J_{n_t}(\pi_tx),\iota_tb_t)
        =\sum_tr(x,\iota_tb_t)=r(x,b).
$$

定理 325.1 给唯一性。这里仅构造辅助候选 $D_r$，没有用它改写一份未知的原 $d_A$。

在这个具体来源中，两个 $21$ 块各自的第一投影核均为
$\{(0,0,Y):\operatorname{Tr}Y=0\}$，维数 $168$；$13$ 块的核为
$\{(X,X,0):\operatorname{Tr}X=0\}$，维数 $440$。所以 (325.5) 的对象、两个重复核及其第二槽标签均为明确有限维关系；它不是任意表值都能延拓的保证。∎

## 326. 完整原正交律与守恒导子入口的分别适用

**定理 326.1（原结构入口的准确消费范围）。** 定理 325.1 的原来源应用有两种充分入口：同一载体上的完整整向量 $\mathsf O$；或同一载体上的实双线性 $D$、全域自守恒 $D(a,a)=0$ 及每个 $D_a$ 对整个 $E$ 的 Jordan 导子律。后一入口已经推出 $\mathsf O_\times$，不另需要斜伴随或一般交换映射分类。

证明。第一入口只是 (324.4) 的原有序子域。对第二入口，SC 在 $a+b$ 处极化得 $D(a,b)=-D(b,a)$。固定任意 $a$，将全域导子 $D_a$ 作用于中央幂等元 $z_t^2=z_t$，得

$$
D_a z_t=2z_t\circ D_a z_t.
$$

$L_{z_t}$ 是逐块坐标投影，只有本征值 $0,1$，故 $I-2L_{z_t}$ 可逆，$D_a z_t=0$。再对 $z_t\circ b$ 用导子律，得

$$
D_a(\iota_tb_t)=z_t\circ D_a(\iota_tb_t)\in\iota_tH_{n_t}.
$$

若 $a\in\iota_sH_{n_s}$、$b\in\iota_tH_{n_t}$、$s\ne t$，这个值在第 $t$ 个输出理想；交替后它又在第 $s$ 个输出理想，因此为零。这是从**完整环境**导子律取得的交叉零，不是只在单个块内部试验导子。随后直接应用定理 325.1。∎

**定义 326.2（既有结构的复用与来源限定）。** 共同框架续卷定理 274.1、275.1、314.1 的正常形及原参考下降全部保持。若已在同一个原 $\Omega$ 上取得它们要求的完整 $B_*$、原选中域的几何及原实际参考，则按其全对象结论，本节切口一旦是其中一个已识别原对象，就具有上述入口。不能只从 native 的字面 $E$ 或某次 $M_0$ 压缩推出该切口拥有原全背景，不能将一般记录更新当作保 $D$ 的原含幺 Jordan 嵌入。

相反，§321 的 $D^\varepsilon$ 已逐项给出：双单位零、每个第一输入的全域第二槽导子及正块权迹型斜伴随，仍不足以确定全域 $D$。其具体原标签 $e,f$ 的 $D^\varepsilon(e,f)\ne0$ 违反完整正交零。它也违反本节所需的跨中心子域：令 $e^\prime=\iota_{010}|u\rangle\langle u|$ 使用 §321 的同一前缀 $u$，则 $\ell(e^\prime)=-1$，$D^\varepsilon(e^\prime,f)=-\varepsilon Z/2\ne0$。它还违反全域 SC：§321 的 $e,H$ 满足 $\ell(e+H)=1$ 且 $[H,e]\ne0$，所以对 $\varepsilon\ne0$ 有
$D^\varepsilon(e+H,e+H)=\varepsilon\mathrm i[H,e]/2\ne0$。因此它不能反驳定理 326.1 的守恒导子入口，也没有被升级为完整原合同反模型。原迹型斜伴随不是缺失 SC 的替代条件。

## 327. 原脉冲的符号、尺度与仍缺的同一 D 等式

**假设 327.1（这个原切口的响应采用）。** 除 (324.2) 外，另须将原 ready、全部十一地址前缀 $a$、原记录零和原旧终端在此切口的响应采用为

$$
\begin{gathered}
\chi_a=K_ae_{\rm r},\qquad
\beta_a(x)=\langle\chi_a,M_0xM_0\chi_a\rangle,
\qquad \beta_a(\nu)=t_0(a),\\
P_{\mathsf R(a,f)}(i=0,w)=\beta_a(B_{f,w})
\quad(a\in\mathsf W_{11},\ f\in\mathsf W_7,\ w\in\Omega_{10}).
\end{gathered}
\tag{327.1}
$$

这里 $x$ 按 $E\subset\operatorname{End}\mathcal K_0$ 作用并向整个 $\mathcal K$ 补零；$\beta_a$ 是未归一原分支评价，零质量时为零。它是 §319.2 的 Jordan／Born 来源采用在这个指定切口上的版本，不是由 (324.3) 或 (325.2) 推出的概率规律。所有 $1024$ 个旧标签、非法标签的零投影、完整失败、真实调用和原记录仍在同一来源。

**定义 327.2（原正向字及必须另供的有符号来源等式）。** 原相位为 $\vartheta=3\pi/5$、$\zeta=e^{\mathrm i\vartheta}$，$K_j=\zeta[I+(\zeta-1)\mathcal P_j]$。若 $g=(j_1,\ldots,j_m)\in\mathsf W_7$，$g^-=(j_m^9,\ldots,j_1^9)$ 是原正向端点逆字。它不是隐藏配置历史的反向过程。定义合法后读菜单及原联合响应

$$
\begin{aligned}
f^+_{g,h}&=g\,0\,g^-h,&
p^+_{a,g,h,w}&=P_{\mathsf R(a,f^+_{g,h})}(i=0,w),\\
f^-_{g,h}&=g\,0^9g^-h,&
p^-_{a,g,h,w}&=P_{\mathsf R(a,f^-_{g,h})}(i=0,w).
\end{aligned}
\tag{327.2}
$$

两请求均为原外生七地址后读字，不依赖记录值；只在记录结果中读取 $i=0$ 那一组。它们不增加条件控制。所需新来源等式为

$$
\boxed{\quad
\beta_a\bigl(D(A_g,B_{h,w})\bigr)
=\frac{p^-_{a,g,h,w}-p^+_{a,g,h,w}}{4\sin\vartheta}.
\quad}
\tag{327.3}
$$

左边必须评价预先固定的原 $D$。右边是两个实际请求的联合概率差，不是新正事件或一份可访问的共同反事实样本。未除以记录质量，所以零质量分支亦有意义；若改用正质量条件概率，两边须同时除以同一个 $t_0(a)>0$。

**定理 327.3（有来源前件的完整关系识别）。** 在假设 327.1 下，若同一原 $D$ 另满足定理 326.1 的任一充分入口，并供应 (327.3)，则在整个字面 $1051$ 维载体上

$$
D(a,b)=\delta(a,b):=\tfrac{\mathrm i}{2}[a,b]
\qquad(a,b\in E).
\tag{327.4}
$$

可以只在有限个实际前缀、有限个实际 $g$ 与有限个实际 $(h,w)$ 上供应 (327.3)：分别选取分离全部输出的原 $\beta_a$、张成 $\mathcal R$ 的原 $A_g$ 及张成 $E$ 的完整标签效果即可。三组选择只依原非 $D$ 数据，不按原 $D$ 的输出重选。结论不请求分别控制两个 $21$ 维尾块，也不从有限精确等式取得含噪认证或效率保证。

证明。以下端点计算只是 §320 (320.2) 的成熟两谱恒等式在原记录零和完整标签上的应用。令
$V_g=K_g^*K_0K_g=\zeta[I+(\zeta-1)A_g]$，则原字顺序 $K_{gh}=K_hK_g$ 及 (327.1) 给

$$
\begin{aligned}
p^+_{a,g,h,w}&=\beta_a(V_g^*B_{h,w}V_g),\\
p^-_{a,g,h,w}&=\beta_a(V_g B_{h,w}V_g^*),\\
V_g B V_g^*-V_g^*B V_g
 &=2\mathrm i\sin\vartheta[A_g,B]
  =4\sin\vartheta\,\delta(A_g,B).
\end{aligned}
\tag{327.5}
$$

所以端点给的是 $\beta_a(\delta(A_g,B_{h,w}))$。只有再用 (327.3)，才得到它与原 $\beta_a(D(A_g,B_{h,w}))$ 相等。$\sin\vartheta>0$，正负标签、$0^9$ 及因子四不能省略。

全部十一地址原有限前缀的 ready 射线轨道在 $\mathbb{CP}^{88}$ 稠密，复用 III144 及 §320 已核对的来源对应。若 $x\in E$ 被每个 $\beta_a$ 杀掉，将 $M_0xM_0$ 向全 $89$ 维空间补零，其二次型在该实际稠密轨道为零；连续性使其在全部射线上为零，故 $x=0$。有限维性允许抽取有限个实际 $\beta_a$ 分离 $E$。这只证明已有原前缀评价的线性分离，不供应任意准备、reset 或其物理凸混合；非零分离行自然有正记录质量。原 $A_g$ 与完整标签效果的有限基分别由 (324.3) 和 III151.2 取得。因此有限 (327.3) 已使 $D-\delta$ 在 $\mathcal R\times E$ 上有完整输出零。$\delta$ 满足 $\mathsf O_\times$，原 $D$ 也满足；定理 325.1 给 (327.4)。这里没有重新交付 §320 的全载体框架重构，而是用 (325.2) 跨过原七地址第一槽的反同步缺口。∎

**定义 327.4（原供应与未建立的等式）。** native III145 的固定内部模型取
$H_j=-\vartheta(I+\mathcal P_j)$、$U_j(s)=e^{-\mathrm i sH_j}$。在已经采用 Born 的矩阵模型中，数学 Heisenberg 生成元为

$$
\mathcal L_j(B)=\mathrm i[H_j,B]
=-2\vartheta\,\delta(\mathcal P_j,B).
\tag{327.6}
$$

因此若额外把原 $D_{\mathcal P_j}$ 识别为这个生成元的 $-1/(2\vartheta)$ 倍，可取得相应符号与尺度；这项识别本身正是尚需供应的原等式。原地址不允许中断脉冲、改变内部 $s$ 或请求非整数调用，故不能把 (327.6) 的数学微分当作额外实际读数。

C1231.5 给原双线性 $d_A$ 并另要求全三元律；它没有给 (327.3) 的原脉冲评价。III151 给字面矩阵和比较行，并明确比较行成为实际概率另需接口；III145 的 Bell 最小电流、平方权重、纯更新和细档案独立性都是该生成模型的输入。其引用的 DGTZ 原文 §2.7 (23)–(29) 也明确先给 Hilbert 空间、Hamiltonian 和 Born POVM 概率，再构造等变率，未从率反向识别这里的原 $d_A$。[native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#1-原来源完整端点与不变的实际读取) 的端点守恒与 retained-read 条件约束同一个 $\Pi$，也未出现原有向响应 $\beta_a(d_A(A_g,B_{h,w}))$ 的等式。即使在各自额外校准条件下取得 Born 响应，也仍须连接这个原 $d_A$。

因而，在所引 C123、共同框架 §§272–280、293、311–318、native III144–145、151、XI1、原生终端认证 §13 及本卷 §§319–323 的限定来源范围内，尚未由原生端点／记录数据推出的是：这个原切口的 $\theta$ 与全部 $\beta_a$ 采用、原 $D$ 在完整跨中心有序域上的零关系或完整守恒导子入口，以及关于同一原 $D$ 的 (327.3)。不把未找到供应写成不存在供应，也不以 §321 的弱律歧义制造一个完整原合同反例。

## 328. 三实维角、相同来源与不变的全部消费者

**定义 328.1（决定关系后的有限角几何）。** 若已取得 (327.4)，在任一尾块内复用 §322、共同框架定义 277.2 的数学二阶角：取正交 primitive $e,f$，$c=e+f$，$h=e-f$、$X=E_{12}+E_{21}$、$Z=\mathrm i(E_{12}-E_{21})$。它们满足

$$
h^2=X^2=Z^2=c,\qquad h\circ X=h\circ Z=X\circ Z=0,
\qquad D_eX=Z/2,\quad D_eZ=-X/2.
\tag{328.1}
$$

$(c+rh+sX+tZ)/2$ 为角内迹一正元恰要求 $r^2+s^2+t^2\le1$。这是同一尾块的三实维无迹截面；(325.2) 恢复不同尾块中各自带标签的 $D$，没有取平均、抵消或为每个角另选一个推动。不同角的内部相容性复用既有完整正常形与量子重构，不重证一般交换映射或 Jordan 分类。这里的跨块输入零也不能替代同块角内的导子、复结构或单位曲率；这些在 (327.4) 识别后才具有上述具体数值。

这项三实维几何不是物理空间维数，也不供应实际 $M_2$、连续时间或新操作。$J_{21},J_{13},\pi_s,\iota_s$ 是响应线性运算；原程序没有因为出现这些符号而获得独立尾控制。

**定义 328.2（原全目标的消费接口）。** 只有在同一个原 $\Omega$ 上对全部原对象和实际联合另已建立完整 $B_*$、相应原几何、原参考、同一固定 $\sigma$ 及所有来源接口时，才直接复用共同框架定理 314.1–316.1、279.1 的整链：原复乘法及全部原准备的 Born 双运输、保全部中心对的实际普通复张量、全事件及相关参考上的 CP/TNI、完整装置 TP、所选完整平方根词与原失败输出、细记录／分组／遗忘、原同数支持双返回及每条原合法有限顺序、自适应和并行历史。原有准备、实际乘积与相关输入、零与次归一质量、旧设备／端口、真实记录、失败、停止、返回及全部合法未来保持原身份；不以这个记录零切口替换它们。

本节只解决这个已经识别切口中“同步第一输入是否在强结构律下决定同一原 $D$”的问题。它不把 $M_0$ 更新变成保 $D$ 的下降，不供应其他对象所需的分离嵌入，不从 ready 轨道的稠密性推出实际准备的精确有限正生成，也不自动证明已列全局前件。物理时钟、能量和作用量／$\hbar$ 单位、可靠控制及取得／认证成本、任意独立成功支的共同完整仪器组装、旧同效果设备的完整输出校准仍各需原来源。完整唯一 $\Omega$ 的量子起源目标因此未由本条件桥闭合。

## 329. 原始文献、既有结果与来源特定增量

**定义 329.1（参数映射与数学归属）。** 以下成熟结果只在上述来源特定推导内复用，不另作为新增分类或一般校准定理：

| 来源 | 此处使用与适用边界 |
| --- | --- |
| C1231.1、1.5；共同框架293.2 | 同一个全语境响应商、事先固定的向量值实双线性 $d_A$ 与有符号准备评价；不把 $D$ 设为正事件。 |
| native III151.1–151.2；原生终端认证13.1 | 全部原标签第二槽空间 $E$、同步第一槽原始空间 $\mathcal R$、含幺空间 $\mathcal S$，分别为 $1051,609,610$ 维；全部同型旁观尾块保留。 |
| 共同框架274–280、311–318；本卷319–323 | 既有结构正常形、全背景原参考下降、尺度与全量子消费者；既有端点恒等式和弱律歧义。不重作一般分类、算子框架或全载体端点标定。 |
| [Freedman–Larsen–Wang，math/0103200v1](https://arxiv.org/pdf/math/0103200v1)，Theorem 0.1、§2 Lemma 2.1、Definitions 1–2 | 原文定理是整个 Jones 直和闭像包含各扇区 $SU$ 的乘积。按 III151 的既有逐路径对应取 $(k,r,n)=(2,5,8)$、表形 $[5,3],[4,4]$；按 III144／§320 取 $(2,5,12)$、$[6,6]$ 的全 $89$ 维来源。$r=5$ 满足其例外与维数门槛；相同 $21$ 维旁观副本不成为两个独立因子。 |
| [Schuld 等，1811.11184v1](https://arxiv.org/pdf/1811.11184v1)，§III.A Theorem 1、(12)–(14) | 已知两谱生成元可精确移位。这里 (327.5) 直接使用已有固定角端点恒等式及原 $0^9$ 正向字，不向原菜单增加可调参数、内部读口或辅助受控门。它确定 $\delta$ 的端点读数，不能自行确定原 $D$。 |
| [Tao–Gowda，作者原文](https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf)，§2、Proposition 3 | 有限 EJA 导子及 Lyapunov-like／单位零／斜伴随之间的成熟关系。§326 只在导子律已覆盖整个 $E$ 时用中央幂等元微分消去跨块输入；未从斜伴随单独推出导子或 SC。 |
| [Dürr–Goldstein–Tumulka–Zanghì，quant-ph/0407116v1](https://arxiv.org/pdf/quant-ph/0407116v1)，§2.7 (23)–(29) | 原文先供量子演化与 Born POVM 分布，再构造等变最小跳率；这里只用于限定 III145 的来源层次，不将其作为原有向双线性 $d_A$ 或概率指数的起源证明。 |

上述成熟中间工具属 $\texttt{literature-attested}$。本节 $\texttt{repo-derived}$ 的实质综合是：(325.1)–(325.5) 将原 $8/5$ 秩轨道的 $609$ 维同步第一槽，借完整带标签第二槽及原跨中心整向量零关系，接回两个分别保留的 $21$ 维尾块和 $13$ 维尾块上的全部原双线性值；并将这个结构决定命题与 (327.3) 的同一原关系来源义务明确分开。其结论改变的是原第一槽缺口在强结构域内的地位，不是宣布实际来源已经校准，也不主张全球原创、独立公理数减少或认证效率。

## 追加锚 C128329（本行以下为增补区）
