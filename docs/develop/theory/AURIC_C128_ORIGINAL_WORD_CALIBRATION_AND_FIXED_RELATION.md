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

## 324. 只删除同一简单块内零重叠迹的完整候选

**定义 324.1（固定原范围与半层／跨中心迹候选）。** 母卷为 [C123 原生互易比较母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，以下“框架卷”指 [C128 框架与角关系续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)。分别取母卷定义 35.1、41.1、88.1 与框架卷定义 264.1、272.1–272.2 的完整背景 $B$，以及母卷定义 67.1 的另名完整背景 $\mathsf B_{\rm cl}$；任一记作 $B_*$。两者分别使用实际准备的精确有限正生成和闭正生成，后者不把数学极限态增加为实际准备。

固定同一完整原 $\Omega$、原全语境响应商、字面实双线性向量关系 $d_A(a,b)=D^A_ab$ 及由原 P/G 固定的同一 $q_A,L_A,\circ_A$。对象包括全部原单体、全部实际联合、旧输出、失败输出、经典标签与参考；全部中心、经典块、不等量子块和不等正 $q$ 块权保留。全部原准备及零／次归一质量、实际乘积准备、全部实际相关输入、设备／端口／记录身份、整个 AC、精确 $N_u$、X/Xs、全事件 R、原 F、实际细化／分组／遗忘、零／失败／停止、具名原同标量支持双返回及其同数反向资料、每条原合法有限顺序、自适应和并行历史保留。相同响应不合并原设备，数学角不增加对象或压缩设备。

重构前的 F 逐字取母卷 (29.3)–(29.5) 的实 Jordan 合同。对原资料 $(S:A\to B,U:B\to A,q_{\rm ret})$，状态表示 $S^J:E_A\to E_B$、$U^J:E_B\to E_A$ 用各自规范 Jordan 迹的对偶 $\sharp$；源支持 $e=\operatorname{supp}((S^J)^\sharp u_B)$ 属于 $A$ 的一个简单理想，目标支持 $h=\operatorname{supp}(S^Ju_A)$ 属于 $B$ 的一个简单理想，且

$$
U^J=\mathsf C_e^A U^J\mathsf C_h^B,\qquad
U^JS^J|_{E_A(e)}=q_{\rm ret}\operatorname{Id}_{E_A(e)},\qquad
S^JU^J|_{E_B(h)}=q_{\rm ret}\operatorname{Id}_{E_B(h)}.
\tag{324.1}
$$

这里 $\mathsf C_e=2L_e^2-L_e$，原 $q_{\rm ret}>0$ 不是比较型 $q_A$；原反向资料 $(U,S,q_{\rm ret})$ 用同一个数。每个原事件的同实现有限细记录、原分组和遗忘均按 F 保留；零标签不需逆。式 (324.1) 不是对返回重标，也不供应新记录。

只用框架卷定理 246.1 取静态坐标

$$
E_A=\bigoplus_sH_{n_{A,s}}(\mathbb C),\qquad
q_A(x,y)=\sum_s w_{A,s}\operatorname{Tr}(x_sy_s),\quad w_{A,s}>0,\qquad
\tau_A(x)=\sum_s\operatorname{Tr}(x_s).
\tag{324.2}
$$

$\tau_A$ 始终是每颗 primitive 迹一的原规范谱迹，不是任取 $q$ 加权迹；此时没有识别原 $D$，也未统一静态取向。令 $z(e)$ 为 primitive 的最小中央支持，仍令 $p_*=\operatorname{rank}E_P\ge2$。唯一新增几何为

$$
\begin{aligned}
\mathsf G_{\rm HC}:\quad&
D^A_ep=Q_cD^A_ep,\quad c=\operatorname{supp}(e+p),\quad Q_c=2L_c^2-L_c,
&& t:=\tau_A(e\circ_Ap)\in\{0,\tfrac12\};\\
&\tau_A(D^A_ep)=0,
&& t=\tfrac12\ \text{或}\ z(e)\ne z(p),
\end{aligned}
\qquad
\begin{gathered}
e,p\in\operatorname{Prim}(E_A),\\
\operatorname{rank}E_A>p_* .
\end{gathered}
\tag{324.3}
$$

量词包括全部有序输入、全部实际联合中的纠缠 primitive 及整个输出。不同中心的 primitive 本来就有 $t=0$；第二行在这个域上只是框架卷 (311.1) 的保留子域。相对于该式，唯一删去的是同一简单块内 $t=0$ 的标量迹式，零／半层整支持与全部半层迹式均保持。没有输入 LU、O、交替、SC、导子、协变、斜伴随、输出理想保持或 $D$ 模身份；也未输入反向交叉零、实际 $M_2$、直接 $AP$、共同参考指数、任意操作或共同仪器供应。X 保留其原有含幺 Jordan／同一 $D$ 嵌入、原有序交叉零、乘积张成与每对原实际准备的实际乘积，不撤去任何已经供应的原接口。

原菜单 $\mathcal M_{ep}$、原有限 $\mathcal K_A$、实际 $J_0=P^{\otimes2}$ 与先于 $D$ 固定的同一 $t_0=(e_0,p_0,r_0)\in\mathcal K_{J_0}$ 均逐字取母卷 88.2–88.3 和框架卷 265.2、272.1。原 $P_e=4(L_e-L_e^2)$、$W_e(x)=\|P_ex\|_{q}^2/2$ 不变，$P_e$ 不能替换支持投影 $Q_c$。定义一个完整候选

$$
\begin{aligned}
\sigma_{t_0}:\quad&
W_{e_0}(p_0)=2q_{J_0}(D_{p_0}e_0,r_0)+W_{e_0}(2D_{e_0}p_0),\\
\mathsf C_{\rm HC}(B_*):={}&B_*+\mathsf G_{\rm HC}+\sigma_{t_0}.
\end{aligned}
\tag{324.4}
$$

框架卷命题 267.1 保证原 $J_0$ 与该标签非空；不按原 $D$ 的输出重选菜单、$\mathcal K$ 或 $t_0$。

## 325. 半重叠迹怎样恢复高阶块的正交迹

**引理 325.1（仅有右单位的局部恢复）。** 设 $E=\bigoplus_sH_{n_s}(\mathbb C)$，$D:E\times E\to E$ 实双线性，有 $D(a,u)=0$，并在此载体全部 primitive 对上满足 (324.3) 的几何。记 $j_s,\pi_s$ 为数学理想包含与投影。则每个 $n_s\ge2$ 的源块满足

$$
\begin{gathered}
D(j_sa,j_rb)=0\quad(r\ne s),\qquad
D(j_sa,j_sb)\in j_sH_{n_s},\qquad D(j_sa,j_sI_s)=0.
\end{gathered}
\tag{325.1}
$$

每个 $n_s\ge3$ 的块还恢复全部同块正交 primitive 的迹式及整向量零式，且有实数 $\alpha_s$ 使

$$
D(j_sa,j_sb)=j_s\bigl(\alpha_s\,\mathrm i[a,b]\bigr).
\tag{325.2}
$$

不对孤立二阶块断言这些后两项，也不把该理想视作实际对象。

证明。固定非经典源中 $e=|v\rangle\langle v|$ 和同块 $f=|w\rangle\langle w|\perp e$。令

$$
y=|v\rangle\langle w|+|w\rangle\langle v|,\qquad
p_\pm=(e+f\pm y)/2.
\tag{325.3}
$$

两颗 $p_\pm$ 与 $e$ 半重叠，三对输入的支持都是 $c=e+f$。双线性给

$$
D(e,e)=D(e,p_+)+D(e,p_-)-D(e,f)\in E_1(c).
\tag{325.4}
$$

此处只用整支持，尚未令 $D(e,f)$ 无迹。因此 $D(e,e)$ 的整个输出在源块内，二阶源也成立。

把 $e$ 补成整个直和的框架。在 $0=D(e,u)=D(e,e)+\sum_{g\perp e}D(e,g)$ 中，跨中心项各为 $a_ge+b_gg$。自输入与同块输入均在源块内；其他跨中心项只沿 $e$ 与各自的框架元。故只有这一项能有沿 $g$ 的输出，逐分量得 $b_g=0$。保留的跨中心规范无迹又给 $a_g=0$。任意跨中心 primitive 均可置于这样的框架，因此这些有序输入的整个输出为零；不曾交换两个输入。

再固定 $e$。同块 $f\perp e$ 的输出在源块内；由 $D(e,y)=D(e,p_+)-D(e,p_-)$，同样适用于 (325.3) 的 $y$。让 $w$ 遍历 $v^\perp$ 并改变其复相位，所得 $y$ 张成从 $v$ 到 $v^\perp$ 的全部 Hermitian 非对角元；$v^\perp$ 中的 primitive 张成下方 Hermitian 块，连同 $e$ 张成整个输入块。再让第一槽 primitive 张成，得到整输出局部性。跨中心行已零，原右单位遂给内部右单位，证明 (325.1)。

现在设 $n_s\ge3$。对 $e$ 可取两颗相互正交且均正交于 $e$ 的 $f_1,f_2$。两个角的交集只有 $\mathbb Re$，所以 (325.4) 使 $D(e,e)=a_e e$。两个保留的半重叠迹式相加给

$$
\tau D(e,f)=-\tau D(e,e)=-a_e
\quad(f\perp e\text{ 在同一块内}).
\tag{325.5}
$$

在该块取任一包含 $e$ 的框架 $(e,f_2,\ldots,f_{n_s})$。由已证内部右单位，

$$
0=\tau D(e,I_s)
=a_e+\sum_{j=2}^{n_s}\tau D(e,f_j)
=(2-n_s)a_e.
\tag{325.6}
$$

$n_s\ge3$，故 $a_e=0$，$D(e,e)=0$，而每个同块正交 $D(e,f)$ 都恢复规范迹零。这一步没有输入被删的迹式，使用的是半层迹、原右单位及整数 $n_s\ne2$。

还须从迹零取得完整 O。在同一框架的向量式 $0=\sum_{j=2}^{n_s}D(e,f_j)$ 中，第 $j$ 项支撑于 $e+f_j$。各 $\mathbb Rf_j$ 和各 Peirce 非对角空间 $V_{ef_j}$ 互不相交，故每项只能沿 $e$；刚恢复的迹零又使这一系数为零。框架可包含任意同块正交对，因此内部完整 O 成立。现在内部映射的域、值域均为同一个 $H_{n_s}$，右单位、O、H 全已证明，才应用框架卷单载体定理 274.1，得到 (325.2)。所用正 Frobenius 型是原 $w_s\operatorname{Tr}$；未给这个数学限制映射添加原 X 或任何实际供应。∎

**命题 325.2（二阶局部诊断不代替全背景）。** 在单独 $H_2(\mathbb C)$ 上，

$$
D(a,b)=\left(\operatorname{Tr}(ab)-\tfrac12\operatorname{Tr}(a)\operatorname{Tr}(b)\right)I_2
\tag{325.7}
$$

有右单位零、零／半整支持与半层无迹，但同块零层迹不全为零。证明。直接代入 $u=I_2$ 得右单位零。两颗不同 primitive 的支持为整个 $I_2$，所以所要求支持自动成立；半重叠给系数零，正交则给 $D(e,f)=-I_2/2$、$\tau D(e,f)=-1$。它没有给原实际联合、X、过程或全称参考，不是完整 $B_*$ 的反模型，也没有提供一件实际二阶对象。式 (325.6) 在 $n_s=2$ 确实没有信息；下述全原范围证明须处理这个边界。∎

## 326. 保留的跨中心迹与全部经典来源

**定理 326.1（高阶目标的全输入公式）。** 在引理 325.1 的载体上，令 $\mathcal C=\{s:n_s=1\}$。对每个 $n_t\ge3$ 的目标块，存在实数 $\alpha_t,\ell_{ts}$，使任意完整输入 $a,b\in E$ 满足

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s\in\mathcal C}\ell_{ts}a_s(b_t-b_sI_t).
\tag{326.1}
$$

经典坐标是原标量，不乘 $q$ 权；公式量化全部来源，不只量化目标内部。这一公式的形式及经典余量的类型复用框架卷定理 313.1；以下核对较弱几何仍提供它所需的每种来源。

证明。固定经典 primitive $e_s=j_s1$。对目标 $t$ 的任一 primitive $p$，跨中心整支持与保留的迹式给

$$
D(e_s,j_tp)=\beta(p)(j_tp-e_s).
\tag{326.2}
$$

令 $F(b)=\pi_tD(e_s,j_tb)$。每个 $F(p)$ 沿 $p$，故 $F(I_t)$ 在任意正交基中都对角，因而是 $\ell_{ts}I_t$。在任一包含 $p$ 的框架逐对角比较，得 $\beta(p)=\ell_{ts}$。primitive 张成于是给整个输出
$D(e_s,j_tb)=\ell_{ts}(j_tb-\operatorname{Tr}(b)e_s)$。反向 $D(j_tb,e_s)=0$ 已由 (325.1) 建立，未输入反向交叉零。

同一完整单位式投影至 $t$ 后，只有经典自输入和这一个混合来源可能留下，故

$$
\pi_tD(e_s,e_s)=-\ell_{ts}I_t.
\tag{326.3}
$$

其余来源逐项如下。

| 有序来源 | 对目标 $t$ 的输出 |
| --- | --- |
| $t,t$ | (325.2) 的 $\alpha_t\mathrm i[a_t,b_t]$ |
| 同一非经典源 $r\ne t$，含二阶源 | 零，由 (325.1) 的整输出局部性 |
| 两个不同源，均非 $t$ | 零，由零层整支持及 primitive 张成 |
| 非经典第一源与不同第二源 | 零，由 (325.1) 的跨中心行零 |
| 经典第一源 $s$ 与第二源 $t$ | $\ell_{ts}a_sb_t$，由 (326.2) |
| 同一经典源 $s,s$ | $-\ell_{ts}a_sb_sI_t$，由 (326.3) |

表中包括所有非经典、经典及混合来源，双线性相加即得 (326.1)。没有令经典自输入零，也没有假设二阶内部已经为导子。∎

**引理 326.2（实际双非经典中心对消去余量）。** 设原实际 $K=JR$ 位于原选中域并满足 $\mathsf G_{\rm HC}$。若 $T\subset E_J$、$V\subset E_R$ 为非经典简单块，$U=(T,V)$ 为其原实际中心对，$n_Tn_V\ge3$，则对所有完整 $x,y\in E_K$，

$$
\pi_UD^K(x,y)=\alpha_U\,\mathrm i[x_U,y_U]
\tag{326.4}
$$

其中 $\alpha_U$ 为一个实数。

证明。右单位只来自母卷 30.1／67.3。框架卷 246.1 给 $K$ 的全部中心对与逐对普通／相反静态表示，故每个经典源唯一为 $s=(r,d)$，其中两因子均经典。可对整个 $E_K$ 使用定理 326.1。记原有序嵌入为 $k,l$。对每个这样的 $s$，取 $J,R$ 中的数学中心单位 $z_r,z_d$，其余坐标补零。原有序交叉零给 $D^K(kz_r,lz_d)=0$。两个输入在 $U$ 上都零，在经典源中同时为一的只有 $s$，所以 (326.1) 恰给

$$
0=-\ell_{Us}I_U.
\tag{326.5}
$$

每个 $\ell_{Us}$ 分别为零，没有经典源时和本来为空，证明 (326.4)。这是框架卷引理 313.2 的同一消去步骤，所需全输入公式已由较弱几何独立建立。单位与经典标量不受转置影响，故静态两种取向均包含；没有交换 $D$ 的输入次序，没有把中心向量或角变为实际对象。∎

## 327. 全部原对象的无标定桥与所有被删迹式

**定理 327.1（两份完整背景的同块零迹冗余）。** 不用 $\sigma$，分别有

$$
\begin{aligned}
B+\mathsf G_{\rm HC}
&\Longleftrightarrow B+\mathsf G^0_{0h}
\Longleftrightarrow B+\mathrm I+\mathrm{SC}
\Longleftrightarrow B+\mathsf O+\mathsf H,\\
\mathsf B_{\rm cl}+\mathsf G_{\rm HC}
&\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G^0_{0h}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathrm I+\mathrm{SC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf O+\mathsf H.
\end{aligned}
\tag{327.1}
$$

$\mathsf G^0_{0h}$、O、H 准确取框架卷 311.1、272.1 的原选中域。I、SC 及所恢复的导子律、交替、双单位、LU、原 $q$ 斜伴随、正交零和规范迹零则覆盖全部原对象、全部输入与全部源／目标块，含未选中小对象、二阶块、全部经典中心、旧输出和失败输出。尤其恢复每条被删的同块零层迹式。

证明。只需补 $\mathsf G_{\rm HC}\Rightarrow\mathrm I+\mathrm{SC}$ 的完整原范围桥，不能把引理 325.1 的高阶内部结果直接当作全域结果。两份背景分别由母卷 30.1／67.3 独立给原右单位；静态结构只用框架卷 246.1。

固定任意非零原对象 $A$，在框架卷定理 202.1 取 $N\ge\max\{3,p_*\}$，得到同一个实际 $J$、原含幺 Jordan／同一 $D$ 单射 $i:E_A\to E_J$ 和高阶目标族 $\mathcal V_N$，满足

$$
n_T>N\quad(T\in\mathcal V_N),\qquad
\bigcap_{T\in\mathcal V_N}\ker(\pi_Ti)=\{0\}.
\tag{327.2}
$$

它分离的是整个 $E_A$，不要求所有联合源块都高阶，不要求 $i$ 保 primitive、保秩或等距。这个定理的前件仅为各自完整背景，不消费本处待证 SC、导子、LU 或任何标定。

再对这个 $J$ 使用它自己由身份事件和全事件 R 已供应的某个实际 $K=JR$、$R=P^{\otimes k}$、$k\ge1$，记原嵌入 $k_J:E_J\to E_K$。不预设 $AP$、不选共同指数、不增加未供应的重括号联合。整个 AC 和原指针幂使 $R$ 有非经典块 $V$，固定其中一个。静态全部中心对保证同一个 $K$ 中每个 $U_T=(T,V)$ 都存在，且 $n_{U_T}=n_Tn_V>p_*$，所以 $K$ 在原选中域，(324.3) 在这里确实可用。

引理 326.2 给每个目标上对所有完整输入的 (326.4)，包含经典自输入、二阶来源和其他混合来源。静态逐中心对表示又给单射

$$
\pi_{U_T}k_J(x)=\theta_T(x_T),\qquad
\theta_T:H_{n_T}(\mathbb C)\longrightarrow H_{n_Tn_V}(\mathbb C),
\quad x_T\longmapsto x_T\otimes I_V
\tag{327.3}
$$

于适当逐对 Jordan 坐标中成立；允许的转置也不改变单射性。因此 $h=k_Ji$ 的这些目标共同分离整个 $E_A$。

对任意原 $a,b,c$，令

$$
r_A=D^A_a(b\circ_Ac)-(D^A_ab)\circ_Ac-b\circ_A(D^A_ac).
\tag{327.4}
$$

原 $h$ 同时保持 Jordan 乘法和同一个原 $D$。目标 (326.4) 是第二槽导子且交替，故每个 $\pi_{U_T}h(r_A)=0$ 以及 $\pi_{U_T}h(D^A_aa)=0$。由 (327.2)–(327.3) 的共同分离，$r_A=0$、$D^A_aa=0$。$A$ 任意，故原导子律和 SC 在全域成立，零空间情形平凡。SC 极化给 $D_ab=-D_ba$，原右单位再给 $D_ub=-D_bu=0$；LU 到此才成为结论。

有限 EJA 每个导子为有限个 $[L_x,L_y]$ 的和，故取得原 I。每个 $L_x$ 对本对象原 $q_A$ 自伴随，所以原导子对该 $q_A$ 斜伴随；没有沿 $h$ 运输内积或要求联合权因子化。

现在才使用框架卷定理 275.2：完整 $B$ 按原 Z 接口，完整 $\mathsf B_{\rm cl}$ 按原完整 $\mathsf Q$ 接口，分别从刚已建立的全域 I+SC 得到 II、共同 $\kappa\ge0$ 及各非经典块的原实标量交换子，经典与跨块为零，包含 $\kappa=0$ 的全零分支。于是全部原正交输入输出零，任意输出规范迹零，半重叠输出留在自己的支持角；这同时恢复 $\mathsf G^0_{0h}$ 及所有遗漏迹式，包括二阶块和未测试的小对象。

反向，$\mathsf G^0_{0h}$ 限制测试域立即给 $\mathsf G_{\rm HC}$。I+SC 到完整无迹支持的方向由刚述不依赖本定理的 275.2 直接给出；O/H 到 I+SC 及其反向是框架卷 275.1，完整无迹支持的既有等价是 314.1。所有这些应用的前件已由上述独立桥建立，不循环使用 $\mathsf C_T$ 的结论来补 (325.5)–(325.6)。∎

## 328. 同一预选 sigma 的候选恒等等价

**定理 328.1（完整 $\mathsf C_{\rm HC}$ 的准确结论）。** 对同一完整原 $\Omega$、同一非 $D$ 选择及同一预选 $t_0$，分别有

$$
\begin{aligned}
\mathsf C_{\rm HC}(B)
&\Longleftrightarrow\mathsf C_T(B)
\Longleftrightarrow\mathsf C_{\rm support}(B)
\Longleftrightarrow\mathsf C_{0h}(B),\\
\mathsf C_{\rm HC}(\mathsf B_{\rm cl})
&\Longleftrightarrow\mathsf C_T(\mathsf B_{\rm cl})
\Longleftrightarrow\mathsf C_{\rm support}(\mathsf B_{\rm cl})
\Longleftrightarrow\mathsf C_{0h}(\mathsf B_{\rm cl}).
\end{aligned}
\tag{328.1}
$$

所有对应在全部原数据、字面原 $D$、原 $q/L$、原返回数、设备／记录与每条原合法有限历史上均为恒等。在由同一原 $D$ 确定取向的复坐标中，对每个原对象及全部 $a,b,c$，

$$
\begin{gathered}
D_ab=\mathrm i[a,b]/2,\qquad a\cdot b=a\circ b-\mathrm iD_ab,\\
D_aa=D_au=D_ua=0,\quad D_ab=-D_ba,\quad
D_a\in\mathfrak k_A,\quad D_a^{\dagger_q}=-D_a,\\
D_a(b\circ c)=D_ab\circ c+b\circ D_ac,\qquad
[K,D_a]=D_{Ka}\quad(K\in\mathfrak k_A),\\
[D_a,D_b]=-[L_a,L_b],\qquad
D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{328.2}
$$

原整个指针的 $d=T_m(u_I)$、$d_0=d-z_P(d)$ 仍满足逐字 S，
$-\operatorname{Tr}_{\mathbb R,E_P}(D_{d_0}^2)=\operatorname{Tr}_{\mathbb R,E_P}(L_{d_0}^2)$，其中去掉的是原整个中心。

证明。定理 327.1 先在没有 sigma 时恢复原全域 I+SC、O/H 和共同尺度。框架卷定理 276.1 对同一原 $t_0$ 给

$$
W_{e_0}(p_0)=w_0/4>0,\qquad
q_{J_0}(D_{p_0}e_0,r_0)=0,\qquad
W_{e_0}(2D_{e_0}p_0)=\kappa w_0/4.
\tag{328.3}
$$

所以原 $\sigma_{t_0}$ 恰为 $\kappa=1$；这里未重选标签，未缩放原 $D,q,W$ 或任何原返回数。定理 327.1 加上这同一条 sigma，立即给 $\mathsf C_T$，然后才复用框架卷 315.1 的已发表候选等价、277.1 的原系数与原 S。反向由 $\mathsf C_T$ 限制其迹域得到 $\mathsf C_{\rm HC}$；原 sigma 本来相同。式 (328.2) 及 S 是上述既有单位尺度消费者，非新增的尺度或量子分类。∎

**命题 328.2（严格删除的只是一个迹子域）。** 若把标量迹测试按原标签 $(A,e,p)$ 区分，则 $\mathsf C_T$ 与 $\mathsf C_{\rm HC}$ 的差恰为

$$
\mathcal Z_{\rm same}
=\{(A,e,p):\operatorname{rank}E_A>p_*,\
e,p\in\operatorname{Prim}(E_A),\
\tau_A(e\circ p)=0,\ z(e)=z(p)\}.
\tag{328.4}
$$

这个删除域非空，整支持域及其他迹域完全相同。证明。差集由 (311.1) 与 (324.3) 的定义直接得到。原 $P$ 有一个 $H_m$、$m\ge2$ 的块，其实际平方 $J_0$ 有 $H_{m^2}$ 块，总秩 $p_*^2>p_*$。其中任取两颗正交 primitive 就属于 (328.4)。定理 327.1 证明这一非空子域在完整背景中冗余，而非使可行原结构类严格增大。没有计算独立前提数、全局最小性、认证成本或稳定性。∎

## 329. 复量子、原过程、具名返回及全部历史

**定理 329.1（原全消费者的完整对应）。** 在任一 $\mathsf C_{\rm HC}(B_*)$ 中，框架卷 279.1、308.1、316.1 的全部原范围消费者成立。以下列明完整参数和类型，作为已发表消费者的应用，不另立一般 QM 重构成果。

每个原对象为

$$
\mathcal A_A=\bigoplus_sB(H_{A,s}),\qquad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\quad u_A=(I_s)_s,
\tag{329.1}
$$

乘法是 (328.2)，保留全部中心、经典块和不等块，没有跨中心相干。令 $x_\alpha$ 为原泛函 $\alpha$ 的原 $g_A^0$-Riesz 向量，$\mathcal B_A$ 表示母卷及框架卷中记作 $B_A$ 的同一比较运输，则

$$
\begin{gathered}
g_A^0(x,y)=\tau_A((\mathcal B_Ax)\circ_Ay),\qquad
\rho_\alpha=\mathcal B_Ax_\alpha\ge0,\\
\alpha(e)=\tau_A(\rho_\alpha e),\qquad
\tau_A(\rho_\alpha)=\alpha(u_A),\\
T_f:E_B\to E_A,\qquad
\Phi_f=\mathcal B_BT_f^{\dagger_0}\mathcal B_A^{-1}:E_A\to E_B
\quad(f:A\to B).
\end{gathered}
\tag{329.2}
$$

$\dagger_0$ 是原 $g^0$ 伴随。为明确 $q$ 与原评价的分别身份，记 $\mathcal W_A(x)_s=w_{A,s}x_s$，$\widehat x_\alpha$ 为同一泛函的 $q_A$-Riesz 向量，则

$$
\begin{gathered}
\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha
=\mathcal W_A^{-1}\mathcal B_Ax_\alpha,\\
\alpha(y)=g_A^0(x_\alpha,y)
=q_A(\widehat x_\alpha,y)=\tau_A(\rho_\alpha y),\\
\alpha(D_ab)=g_A^0(x_\alpha,D_ab)
=q_A(\widehat x_\alpha,D_ab)=\tau_A(\rho_\alpha D_ab).
\end{gathered}
\tag{329.3}
$$

一般不能用 $q_A(x_\alpha,y)$ 代替原评价。所有原零准备、次归一质量、实际乘积准备和实际相关准备均按 (329.2) 保持，不除以质量。$B$ 的精确正生成与 $\mathsf B_{\rm cl}$ 的闭覆盖分别保持。

每个原已经声明的实际联合成为保留全部中心对的普通复张量，原局部嵌入成为交换的含幺 $*$-嵌入。没有增加原联合；不要求 $q_{AB}$ 或 $\mathcal B_{AB}$ 因子化。所有旧事件、旧输出、实际细记录、标签箭头、失败、遗忘、返回及合法接续均 CP/TNI；每个原完整装置 TP。

对每个数学效果 $0\le e\le u_A$，含零、奇异及零中心分量，原所选精确完整有限平方根词及其已许可的相关参考执行满足

$$
\Phi_{W_e}(\rho)=\sqrt e\,\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{329.4}
$$

投影时为所选 Lüders 支。对该词占用的原指针失败方向 $p_1$ 及每个原失败 $\Psi_\ell:P\to B_\ell$，完整失败输出为
$\sqrt{I-e}\,\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；只有原实际丢弃才取其质量因子，其他输入方向及中心仍取原失败映射。

原 F 给同一原实现的实际有限细记录，非零细支及原具名返回为

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell}:E_A\to E_B,\qquad
\Phi_f=\sum_\ell S_\ell,\qquad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}:E_B\to E_A,\\
e_\ell=\operatorname{supp}(K_\ell^\ast K_\ell)\text{ 在源 }A,\qquad
h_\ell=\operatorname{supp}(K_\ell K_\ell^\ast)\text{ 在目标 }B,\\
U_\ell=\mathsf C_{e_\ell}^AU_\ell\mathsf C_{h_\ell}^B,\qquad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}^A,\qquad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}^B.
\end{gathered}
\tag{329.5}
$$

每个 $q_\ell>0$ 是 (324.1) 中同一个原数，其原同数反向资料、原失败完成和全部后续合法历史保留。原零标签、细化、分组与遗忘保留；数学 Kraus 指标不替换实际可访问记录。

对每份原准备、每条原合法有限历史 $h=(f_1:A_0\to A_1,\ldots,f_m:A_{m-1}\to A_m)$ 与末端原效果 $w$，

$$
\alpha(T_{f_1}\cdots T_{f_m}w)
=\tau_{A_m}\left(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{329.6}
$$

自适应按原实际记录逐支解释，并行使用原实际联合和相关输入，分组／遗忘用原线性和，失败／返回／停止用原箭头；条件概率只在原分母正时取比值。

证明。定理 328.1 已在同一完整数据上恢复 $\mathsf C_T$ 和 $\mathsf C_{\rm support}$ 的全部前件，故直接适用框架卷 316.1，而非把其结论当成新增几何的前提。原导子、曲率与同一 $D$ 给 (329.1) 的复乘法。原 $g^0$ 与规范谱迹的双对偶给 (329.2)；代入 $\mathcal W_A\widehat x_\alpha=\mathcal B_Ax_\alpha$ 并用 Riesz 唯一性即得 (329.3)，包括有符号的原 $D$ 输出。

原 X 同时保 Jordan 与原 $D$，所以保该复乘法；原有序交叉零及已得交替性给两像交换。原乘积张成与实际乘积准备分离给普通复张量的双射，保全部中心对。这是在原 $D$ 已识别后所得的取向，不由母卷 §86 的纯静态片段预先消去全部取向义务。

全事件 R 给每条原事件的同设备同记录充分大实际参考执行，其在全部原相关准备上保正；$B$ 用精确正生成，$\mathsf B_{\rm cl}$ 按母卷 69.2 在同一固定执行上连续延拓到完整相关锥，分别给既有 CP 消费者的完整前件。原事件的次幺性给 TNI，完整装置的原效果和给 TP；这不以所选新词替换旧设备。

整个 AC、精确 $N_u$、Xs 和原被消费参考／合法连线，正是母卷 12.1、32.1 的词供应前件，25.2 保其完整失败，故取得 (329.4)。原 F 的同实现实际细记录、遗忘与同数两侧支持资料再给 (329.5)，不是只从一个 CP 表示推断原细口存在。最后一步迹对偶等式逐箭头迭代给 (329.6)，自适应逐原分支，原并行逐原已供联合。因此全部原合法有限历史同时保持，未新增合法连线，未按同算子值识别设备。∎

**定义 329.2（三种分别的供应边界）。** 连续 Hamilton／Schrödinger 动力仍需原连续确定可逆一参数器件、物理时钟和具体 Hamiltonian，时间与作用量／$\hbar$ 另须标定；任意独立成功支的共同完整仪器组装仍需原类型控制、记录和共同合法连线；某个旧同效果设备的理想完整输出仍需该设备自己的完整输出校准。这些义务分别取框架卷 279.2、308.2、316.2 的原范围，均不由 (324.3)、代数系数 $1/2$ 或 (329.4) 自动供应。

## 330. 含一般原比较和全部原过程的非空族

**定理 330.1（完整满足族及无实际二阶对象选项）。** 母卷 5.1、13.1–13.2、33.1 与框架卷 278.1、317.1 的完整 tagged-CP 族，对任意原菜单、$\mathcal K$ 和同一预选 $t_0$，分别满足 $\mathsf C_{\rm HC}(B)$ 与 $\mathsf C_{\rm HC}(\mathsf B_{\rm cl})$。该族包含全部中心、经典块、任意不等有限量子块、任意不等正 $q$ 块权及一般 $g^0\ne q$；并有不含实际 $M_2$ 对象或简单块的完整子族。

证明。复用原完整族，明确其全数据如下。对象为带原因子、块与实现标签的非零有限复矩阵直和、实际普通张量和经典副本；不按代数同构识别原对象。每个对象初始给逐块 $r_{A,s}>0$ 与 $w_{A,s}>0$，取

$$
\begin{gathered}
g_A^0(x,y)=\sum_sw_{A,s}\operatorname{Tr}(r_{A,s}x_sr_{A,s}y_s),\qquad
\mathcal B_A(x)_s=w_{A,s}r_{A,s}x_sr_{A,s},\\
q_A(x,y)=\sum_sw_{A,s}\operatorname{Tr}(x_sy_s),\qquad
D^A_ab=\mathrm i[a,b]/2,\qquad
x_{\alpha_\rho,s}=w_{A,s}^{-1}r_{A,s}^{-1}\rho_sr_{A,s}^{-1},\quad
\widehat x_{\alpha_\rho,s}=w_{A,s}^{-1}\rho_s .
\end{gathered}
\tag{330.1}
$$

原锥、单位、Jordan 乘法和评价为矩阵锥、单位、对称乘积及 $\alpha_\rho(x)=\sum_s\operatorname{Tr}(\rho_sx_s)$。原指定群是逐块可逆合同群，原伴随为母卷 (5.2)，正块权在伴随等式两侧抵消；框架卷 278.1 的单位适配给 (330.1) 的同一 $q_A,L_A$。每个实际联合用自己的原比较与运输，联合权不必因子化。这里是在定义不同完整模型的初始数据，不调整任何固定模型的原比较。式 (330.1) 逐项代入 (329.3) 保留所有原 $D$ 评价；一般不能将原 $x_{\alpha_\rho}$ 直接用于 $q$ 裸配对。

全部正密度及零、次归一密度均有原准备，全部实际联合纠缠密度也有，故精确有限正生成成立，也分别满足另名闭正生成。全部带实现标记的有限完整 CP 仪器取原菜单，原已安装单中心细记录含源／目标块名及原 Kraus 标签；其矩形算子逐输入块满足完整和式 $\sum_{\ell,t}K_{\ell,ts}^\ast K_{\ell,ts}=I_s$。原粗事件、分组、遗忘、零记录、停止、每个输出和失败均保留；所有有限合法顺序、自适应、并行和返回接续仍取原完整菜单。谱分解把任意 Hermitian 响应写成原破坏性效果响应的实线性组合，全部密度分离它，所以同一全语境响应空间及原向量值 $D$ 均被保留。

整个原指针的非经典块取秩一 $d=E_{11}$、质量一纯准备及原破坏性概率一读口，连同完整失败，给 AC。每个指定单位稳定子由原精确合同支及其全部补记录供应 $N_u$；所有原群、装置和失败输出分别在原全对象范围内。普通实际联合的含幺嵌入保 Jordan 和原 $D$，交叉交换子零，乘积张成；所有实际乘积准备存在，给 X。同设备同记录 CP 旁接及全部原相关输入给 Xs 与全事件 R，实际指针幂含无界大矩阵块。

对每条非零原单中心细路径 $K:H_s\to H_t$，仍配原具名

$$
S_K=\operatorname{Ad}_K,\qquad
U_K=q_K\operatorname{Ad}_{K^+},\qquad
0<q_K\le\lambda_{\min}^+(K^\ast K),
\tag{330.2}
$$

其源、目标支持分别为 $e=\operatorname{supp}(K^\ast K)$、$h=\operatorname{supp}(KK^\ast)$。伪逆给 $K^+K=e$、$KK^+=h$，直接得到 (329.5) 的同数两侧复合。给定范围使 $U_K$ 为 TNI，原完整失败完成在菜单内；$S_K$ 本来也为 TNI。反向资料 $(U_K,S_K,q_K)$ 用同一数，非改成一。全部进一步有限细路径、其指定返回和失败完成的闭合，完整复用母卷 33.1 的原类型构造；同实现细记录、原分组与实际遗忘给整个 F。此处没有从数学分解为别的原世界补造记录，也不把矩形算子的支持当作新对象。

最后，交换子整输出在输入支持内、规范迹为零，故 (324.3) 对全部有序 primitive、包括实际联合纠缠 primitive 成立。原 $\kappa=1$，所以 (328.3) 对任意事先固定的原 $t_0$ 成立。取原 $P=\mathbb C\oplus M_3$ 和母卷 $\mathcal D_3$ 时，对象的所有块大小为 $3^k$，有限和、标签和实际张量均在此域内；全部原 CP 仪器、矩形细支、伪逆返回、补效果完成和所有有限历史依然存在，没有实际 $M_2$。这是一整个满足签名，而非局部角例子；精确背景与闭背景各有非空见证。∎

## 331. 两原子角、三实维截面与较大角网

**定义 331.1（支持几何及删除条款的位置）。** 在一个量子块内，两颗不同 primitive 的数学支持角为 $H_2(\mathbb C)$，实维四，其规范无迹部分实维三。若 $e,f$ 正交、$c=e+f$，取 $y\in V_{ef}$、$y^2=c$，在定理 328.1 之后令 $h=e-f$、$z=2D_ey$，则

$$
h^2=y^2=z^2=c,\qquad
h\circ y=h\circ z=y\circ z=0,\qquad
D_ey=z/2,\quad D_ez=-y/2.
\tag{331.1}
$$

这些性质复用母卷 91.1、框架卷 277.2、317.2 的同一角几何。直接平方说明 $\rho=(c+rh+sy+tz)/2$ 为角内迹一正元恰当且仅当 $r^2+s^2+t^2\le1$，等号时为 primitive；本征值为 $(1\pm\sqrt{r^2+s^2+t^2})/2$。同块零重叠是复射影角 $\pi/2$，半重叠是 $\pi/4$，在 Bloch 球面上分别为对径与正交方向。原横向 $J_e=2D_e$ 在 $E_{1/2}(e)$ 上满足 $J_e^2=-I$ 并对原 $q$ 正交，$\omega_e(v,w)=q(J_ev,w)$ 非退化交替。

不同简单中心的 primitive 却只有 $\mathbb Re\oplus\mathbb Rp$ 的支持角，其无迹交集是 $\mathbb R(e-p)$；不存在连接两中心的 Peirce 非对角元，也没有跨中心半重叠。保留的跨中心迹式在 (325.1) 中先切断非经典第一槽的跨中心行，并在 (326.2) 中把经典第一槽的两个系数绑定；它不是关于跨中心相干的新公理。被删的同块零迹先由半层两扇窗、整支持交集与 (325.6) 的右单位恢复于高阶块，再由实际联合与整个对象分离恢复到二阶和经典范围；因此这里的冗余是完整关系网中的结论，命题 325.2 说明不能在孤立二阶角里照搬。

更大几何为各块 $\mathbb{CP}^{n_s-1}$ 及其相交的复二阶支持角网，所有角共享同一个原双线性 $D$。证明中的第三个复向量位置用于分开支持交集，不等于这个三实维无迹截面；二者均非物理空间三维，也不供应实际量子比特、时钟或作用量。规范迹与原 $q$ 权不同，故几何上的迹零不是把不同中心的原权抹平。

## 332. 数学归属、未决来源与完整直观定义

**定义 332.1（复用与新增差额的准确归属）。** 仓内引文取固定源 [a3fcb35d79fe06ae27fdca792d1ae0cc3ec0f0b4](https://github.com/the-omega-institute/trureturing/tree/a3fcb35d79fe06ae27fdca792d1ae0cc3ec0f0b4) 的对应保护正文。证明的依赖与适用范围如下。

| 来源 | 使用的准确结论及前件 |
| --- | --- |
| 母卷 1.1、29.3、35.1、41.1、67.1、88.1；框架卷 264.1、272.1–272.2、311.1 | 完整原响应、原向量值 $D$、两份分别命名的全背景、原实 F／同数双返回与原测试门槛；不输入原完整三元律。 |
| 母卷 30.1／67.3；框架卷 246.1 与母卷 85.2 | 右单位、各对象自己的实际身份参考、静态复直和与全部实际中心对；不输入 LU，不提前识别 $D$。 |
| 框架卷 273.1、274.1、280.1 | 仅在 (325.5)–(325.6) 已恢复高阶块 O 后，复用单载体 O/H 正常形；不重新声称证明正交双线性分类。 |
| 框架卷 312.1–313.2 | 整输出局部性与经典余量的原组织；(325.4)–(325.6) 独立补足删除同块零迹后的入口，再逐来源复用其消去机制。 |
| 框架卷 202.1、314.1 | 高阶目标共同分离整个对象、实际 $JR$ 清除经典来源的原范围路线；(327.1) 对较弱几何重新建立完整入口，未预用 $\mathsf C_T$。 |
| 框架卷 275.1–277.1、315.1 | 全域 I+SC 建立后，分别按精确／闭准备前件恢复共同尺度、同一预选 sigma 的单位尺度和原 S。 |
| 母卷 85–93、框架卷 279.1、308.1、316.1–317.2 | 静态类型、量子／过程／历史、一般 $g^0$ 与 $q$／规范迹的区别、完整满足族及角几何；均为已发表条件纸笔结果的应用。 |

成熟中间工具按原文 [Haagerup–Laustsen，Weak amenability of C*-algebras and a theorem of Goldstein，Theorem 3.1(1)、Lemma 3.4，原文 pp.237–238](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-haagerup/1990s/1998_Weak_amenability_of_C-star_algebras_and_a_theorem_of_Goldstein.pdf)（DOI 10.1515/9783110802009.223）以及 [Tao–Gowda，A Representation Theorem for Lyapunov-like Transformations on Euclidean Jordan Algebras，§2、Proposition 3](https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf) 归属。前者的定理针对 C*-代数上的有界复双线性标量型在自伴正交输入消失的乘积表示，引理为反对称型的三次极化；这里仅通过已经满足内部 O 的框架卷 274.1 消费，不把原矩阵值 $D$ 直接当作该原文标量型。后者明确有限 EJA 导子的内性及原迹型斜伴随联系；本处先证明原导子律，才用内性及原 $L_x$ 的 $q$ 自伴随性。这些为 literature-attested 中间工具，静态类型表、Born／CP、伪逆返回和 Bloch 几何也均不是本候选的新一般数学。

本处 repo-derived 的新增差额恰为：(325.5)–(325.6) 从保留的半层迹及原右单位恢复高阶同块零迹，结合跨中心旧迹子域，取得对全部来源有效的 (326.1) 与原全范围桥 (327.1)，从而得到同一 $\sigma$、同一字面 $D$ 下的 (328.1)。没有将既有 274、313、314、315 的分类、下降机制或量子消费者换名充作新增成果；没有作历史原创、全球最小、独立前提总数、效率或稳定性结论。

**定义 332.2（较强删除问题与实际来源边界）。** 删除全部零层迹的较强问题仍保持未决：本处保留全部跨中心零迹，证明中的 (325.1)、(326.2) 明确使用它，不能把定理 327.1 读成对它也可删除的证明。配平续卷 §170 的中央三形式完整反模型针对其原条件；其 (170.4)–(170.5) 将跨中心输出送到输入支持之外，已违反这里保留的零层整支持，因而也不能用来否证本处候选或解决只删全部零迹的问题。框架卷 §286 的 O_same 删除目标具有自己的前件与未决范围，同样不被这里改判。

具体原 $\Omega$ 仍须从实际来源建立完整 $B_*$、$\mathsf G_{\rm HC}$、同一预选 sigma 及所有被消费接口；本条件等价既不供应这些来源，也不证明来源不能供应。母卷 §86.4 的静态接口取向来源、SourceU27047 与框架卷 §286 的 static supplier／overlap 及实际标量接口义务保留原义；不由缺少普遍 $(I,A)$ 的打印断言可删某个真实接口。本处在完整新几何下推得 LU，不是从较弱旧来源无条件取得 LU。

本卷 319–323 的原有限词校准只有在明确采用复／Born 来源接口 (319.4) 并另给新 $D$-响应等式 (319.5) 后，才对指定读前对象识别整个原 $D$；其记录后第一输入与全世界来源限制保持。不能把该局部标定、native 字密度、任何局部二阶诊断或已给复量子矩阵当作 (324.3) 的全对象来源。329.2 的三类物理义务分别保留。这里给出完整条件候选的纸笔证明，不作 Lean/kernel、数值、实验、经验或本体真实性结论，完整原量子内生来源目标仍未完成。

**定义 332.3（半窗、街区边界与整座城市）。** 白话说，原世界这座城市里的量子街区、经典房间、大小不同的中心、所有真实联合与纠缠准备、每台旧设备、原记录、失败出口、细化和遗忘、带原成功数的双返回以及每条合法有限历史都原样留下；只在原来选中的大对象里问同一条有向关系：两颗原子完全错开或恰好重叠一半时，整份变化都待在它们共同的小屋里，半重叠时屋内总增减为零，跨街区错开时也保留原来的总增减为零，却不再另问同一量子街区内错开时的总增减。为什么这笔能省？沿同一原子朝旁边开两扇半窗，两份半窗变化相加，正好把自推动和错开推动绑在一起；在至少三个方向的房间里，不同小屋的交集只剩原子自己，再把原整个单位放在右边，重复出现的那笔账只能为零，于是错开时连整份推动也为零。二阶小屋单独还藏得住余量，经典第一槽也能向大房间发一笔、再在自己身上补一笔，所以不能只看局部球面就宣布全世界完成；保留的跨街区旧迹先堵住非经典第一槽的越界，再在原来实际存在的参考整体里，用原有序交叉零逐个清掉经典余量。那些高阶目标共同看得见原对象的每个区别，便把导子、自守恒、左单位零和所有省去的迹式带回小对象、经典中心与全部旧输出。最后仍用那张早已选定的原刻度单把共同转动大小锁到一，不换原推动、比较权或返回率，复量子块与经典块、保原质量的 Born 双运输、实际普通张量和相关输入、所有旧事件、所选精确平方根词与每个完整失败、真实细记录和同数双返回、所有合法有限历史便按已有理论接回。同块小屋的无迹部分是三实维 Bloch 球空间，跨中心小屋只有一条增减相抵的线，不能画成跨中心量子相干；所有小屋共享同一条原关系，嵌在更大的复射影角网里。这里省去的只是同街区错开时那一类迹问句，全部零层迹能否一并省去仍未解决；原城市为何实际供应这些关系、物理钟与作用量怎样标定、独立支怎样成为共同仪器、旧同效果设备怎样具有理想完整输出，也各守自己的来源与接口条件。

## 追加锚 C128323（本行以下为增补区）

## 333. 只删除经典与经典之间跨中心迹的完整候选

**定义 333.1（同一原签名上的 C_HQ）。** 本节的母卷指 [C123 原生互易比较母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，框架卷指 [C128 框架与角关系续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)。分别固定定义 324.1 的完整 $B$ 与另名完整 $\mathsf B_{\rm cl}$，任一写为 $B_*$。它们分别取母卷 35.1、41.1、88.1 与母卷 67.1 的精确有限正生成、闭正生成；闭包不是新增实际准备。保留同一完整原 $\Omega$、原全语境响应商、已经给定的实双线性向量关系 $d_A(a,b)=D^A_ab$、由原 P/G 固定的 $q_A,L_A,\circ_A$。全部对象、全部实际联合、旧输出、失败输出、经典标签和参考都在原量词中；全部中心、一维经典块、不等量子块和不等正 $q$ 块权均保留。

全部原准备及零／次归一质量、每个实际联合的全部相关输入、每对实际准备的原乘积、设备／端口／记录身份、整个 AC、精确 $N_u$、X/Xs、全事件 R、原 F、同实现细化／分组／遗忘、零／失败／停止、具名原同标量两侧支持返回与同数反向资料，以及每条原合法有限顺序、自适应和并行历史全部保留。F 在重构前逐字按母卷 (29.3)–(29.5) 及本卷 (324.1) 解释：规范 Jordan 迹对偶的源支持 $e$、目标支持 $h$ 各在一个简单理想内，原 $U^J=\mathsf C_e^AU^J\mathsf C_h^B$，$U^JS^J=q_{\rm ret}\operatorname{Id}$、$S^JU^J=q_{\rm ret}\operatorname{Id}$ 分别在两个支持角上成立，反向资料 $(U,S,q_{\rm ret})$ 使用同一个原正数；$q_{\rm ret}$ 不是比较型 $q_A$。

只由框架卷 246.1 取静态坐标与记号

$$
\begin{gathered}
E_A=\bigoplus_sH_{n_{A,s}}(\mathbb C),\qquad
q_A(a,b)=\sum_sw_{A,s}\operatorname{Tr}(a_sb_s),\quad w_{A,s}>0,\\
\tau_A(a)=\sum_s\operatorname{Tr}(a_s),\qquad
z(e)=\text{primitive }e\text{ 的最小中央支持},\qquad
n(e)=n_{A,s}\quad(z(e)=z_s).
\end{gathered}
\tag{333.1}
$$

$\tau_A$ 是每颗 primitive 迹一的原规范谱迹，不改成加权迹；静态表示没有识别原 $D$ 或解决联合的取向。原选中对象仍恰为 $\operatorname{rank}E_A>p_*$，$p_*=\operatorname{rank}E_P\ge2$。唯一新增几何是对这些对象的全部有序 primitive 输入施加

$$
\begin{aligned}
\mathsf G_{\rm HQ}:\qquad
&D^A_ep=Q_cD^A_ep,
&&t:=\tau_A(e\circ_Ap)\in\{0,\tfrac12\},\\
&\tau_A(D^A_ep)=0,
&&t=\tfrac12\ \text{或}\
\bigl(z(e)\ne z(p)\ \text{且}\ \max\{n(e),n(p)\}\ge2\bigr),\\
&c=\operatorname{supp}(e+p),\qquad Q_c=2L_c^2-L_c.
\end{aligned}
\tag{333.2}
$$

不同中心必有 $t=0$。整支持限制整个输出，包括其他中心及连向角外的项；$Q_c$ 不换成 $P_c=4(L_c-L_c^2)$。量词包含实际联合中的全部纠缠 primitive，不只包含局部乘积。相对 (324.3)，只删除两个输入各属一维经典简单块时的有序跨中心规范零迹；全部零／半整支持、全部半层迹及涉及任一非经典块的跨中心迹均不变，同块正交迹仍未作为输入。

原菜单 $\mathcal M_{ep}$、$\mathcal K_A$、实际 $J_0=P^{\otimes2}$ 与先于 $D$ 选定的同一 $t_0=(e_0,p_0,r_0)\in\mathcal K_{J_0}$ 逐字沿用母卷 88.2–88.3、框架卷 265.2、272.1。令 $W_e(x)=\|P_ex\|_{q_A}^2/2$，定义完整候选

$$
\begin{aligned}
\sigma_{t_0}:\quad&W_{e_0}(p_0)
=2q_{J_0}(D_{p_0}e_0,r_0)+W_{e_0}(2D_{e_0}p_0),\\
\mathsf C_{\rm HQ}(B_*):={}&B_*+\mathsf G_{\rm HQ}+\sigma_{t_0}.
\end{aligned}
\tag{333.3}
$$

没有按输出重选菜单、$t_0$、$D$ 或 $q$。不输入 LU、O、交替、SC、导子、协变、斜伴随、$D$ 模身份、输出理想保持或中心零，也不输入反向交叉零、实际 $M_2$、直接 $AP$、共同参考指数、任意操作或共同仪器供应。X 仍保持原含幺 Jordan／同一 $D$ 嵌入、原有序交叉零、乘积张成及实际乘积准备。数学理想、支持角及压缩不是新的原对象或设备；任何已经供应的原有序联合也没有删除。

## 334. 保留的非经典迹已经控制全部非经典第一槽

**引理 334.1（不消费经典—经典迹的局部入口）。** 设 $E=\bigoplus_sH_{n_s}(\mathbb C)$，$D:E\times E\to E$ 实双线性，$D(a,u)=0$，在这个载体满足 (333.2)。用 $j_s,\pi_s$ 表示数学理想包含与投影。每个 $n_s\ge2$ 的源块都有

$$
\begin{gathered}
D(j_sa,j_rb)=0\quad(r\ne s),\qquad
D(j_sa,j_sb)\in j_sH_{n_s},\qquad D(j_sa,j_sI_s)=0.
\end{gathered}
\tag{334.1}
$$

每个 $n_s\ge3$ 的内部限制还满足全部正交 primitive 的整向量零，并有一个实数 $\alpha_s$ 使

$$
D(j_sa,j_sb)=j_s\bigl(\alpha_s\,\mathrm i[a,b]\bigr).
\tag{334.2}
$$

这是既有局部入口在更小迹域下的适用证明，不重新分类正交双线性关系；二阶源只取得 (334.1)。

证明。固定非经典源中的 $e=|v\rangle\langle v|$ 与同块 $f=|w\rangle\langle w|\perp e$，置

$$
y=|v\rangle\langle w|+|w\rangle\langle v|,\quad
p_\pm=(e+f\pm y)/2,\quad c=e+f.
$$

两颗 $p_\pm$ 与 $e$ 半重叠。零／半整支持及双线性给

$$
D(e,e)=D(e,p_+)+D(e,p_-)-D(e,f)\in E_1(c).
\tag{334.3}
$$

没有给 $D(e,f)$ 输入迹零；(334.3) 先只说明自输入的整个输出在该非经典源内。将 $e$ 补成整个直和的框架。在 $0=D(e,u)=D(e,e)+\sum_{g\perp e}D(e,g)$ 中，一个不同中心的 $g$ 对应的项只能为 $a_ge+b_gg$。自输入及同块项都在源块内，其他跨中心项只沿 $e$ 与各自的框架元，故只有这一项能在 $g$ 方向输出，得到 $b_g=0$。此处第一输入 $e$ 非经典，所以 (333.2) 仍保留这项的规范迹零，进而 $a_g=0$。任意跨中心 primitive 都能放入这样的框架，故该有序行全部为零，包含经典第二槽；没有交换两个输入。

对固定 $e$，$D(e,f)$、$D(e,e)$ 均在源内，而 $D(e,y)=D(e,p_+)-D(e,p_-)$ 也在源内。让 $w$ 遍历 $v^\perp$ 并改变复相位，所得 $y$ 张成全部连接 $v$ 与其正交补的 Hermitian 非对角元；正交补中的 primitive 张成下方 Hermitian 块。加上 $e$，第二输入张成整块；第一槽 primitive 也张成，故得到整输出局部性。全单位及已证跨中心行零给内部右单位。这证明 (334.1)，包括二阶源。

设 $n_s\ge3$。在 (334.3) 取两个互相正交且均正交于 $e$ 的 $f$，对应支持角的交集只有 $\mathbb Re$，故 $D(e,e)=a_e e$。两个保留的半层迹式相加给每个同块 $f\perp e$ 的

$$
\tau D(e,f)=-a_e.
$$

取包含 $e$ 的该块框架，由内部右单位得到

$$
0=\tau D(e,I_s)=a_e-(n_s-1)a_e=(2-n_s)a_e.
\tag{334.4}
$$

$n_s\ne2$，所以 $a_e=0$，并恢复全部同块正交迹零。向量单位式此时为 $\sum_{f\perp e}D(e,f)=0$；每项支撑于 $e+f$，不同 $f$ 的 $\mathbb Rf$ 与 Peirce 非对角空间 $V_{ef}$ 独立，故每项只能沿 $e$，刚恢复的迹零再使它为零。任意同块正交对均可补成框架，内部完整 O 成立。

现在内部映射的域、整个值域均为 $H_{n_s}$，内部右单位、O 及半层整支持 H 已齐，才对这个数学限制映射直接应用框架卷 274.1，正 Frobenius 型取原 $w_s\operatorname{Tr}$。其单载体结论给 (334.2)；不需要给该理想虚构实际 X，也未使用经典—经典输入、LU 或孤立二阶导子结论。∎

## 335. 高阶目标的全输入公式仍不看经典—经典迹

**定理 335.1（保留经典自输入的完整来源公式）。** 在引理 334.1 的载体上，记 $\mathcal C=\{s:n_s=1\}$。每个 $n_t\ge3$ 的目标块都有实数 $\alpha_t,\ell_{ts}$，使对全部完整输入 $a,b\in E$，

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s\in\mathcal C}\ell_{ts}a_s(b_t-b_sI_t).
\tag{335.1}
$$

尤其经典—经典非自输入可暂时具有非零规范迹，经典自输入也没有提前置零；公式仍覆盖它们对 $t$ 的全部贡献。

证明。固定经典 primitive $e_s=j_s1$ 及目标 $t$ 的任意 primitive $p$。零层整支持给 $D(e_s,j_tp)\in\mathbb Re_s\oplus\mathbb Rj_tp$，且因为 $t$ 非经典，保留的混合迹式给

$$
D(e_s,j_tp)=\beta(p)(j_tp-e_s).
\tag{335.2}
$$

令 $F(b)=\pi_tD(e_s,j_tb)$。每个 $F(p)=\beta(p)p$，所以 $F(I_t)$ 在每个正交基中都对角：任意 primitive 都可补基，故它与每个秩一投影交换，只能是 $\ell_{ts}I_t$。在一个包含 $p$ 的框架中比较 $p$ 的对角元，得 $\beta(p)=\ell_{ts}$。primitive 张成于是给

$$
D(e_s,j_tb)=\ell_{ts}\bigl(j_tb-\operatorname{Tr}(b)e_s\bigr).
\tag{335.3}
$$

反向 $D(j_tb,e_s)=0$ 来自 (334.1)，不是反向交叉零假设。

现在对同一经典第一槽的整个单位式投影至 $t$。除第二槽在 $t$ 内和经典自输入 $D(e_s,e_s)$ 外，其他项不能向 $t$ 输出：不同经典第二槽 $e_r$ 的整输出在 $\mathbb Re_s\oplus\mathbb Re_r$，不同非经典第二槽的整输出也在其与 $e_s$ 的支持内。因此

$$
\pi_tD(e_s,e_s)=-\ell_{ts}I_t.
\tag{335.4}
$$

这一步没有取那些经典—经典项的迹，不能把 (335.4) 漏掉。

全部有序来源逐项为

| 输入来源 | 对非经典目标 $t$ 的完整输出 |
| --- | --- |
| 两槽都在 $t$ | (334.2) 的 $\alpha_t\mathrm i[a_t,b_t]$ |
| 同一非经典源 $r\ne t$，包括二阶源 | 零，由 (334.1) 的整输出局部性 |
| 非经典第一源、不同第二源 | 零，由 (334.1) 的跨中心行零 |
| 经典第一源 $s$、第二源 $t$ | $\ell_{ts}a_sb_t$，由 (335.3) |
| 同一经典源 $s,s$ | $-\ell_{ts}a_sb_sI_t$，由 (335.4) |
| 不同经典源 $s,r$ | 零，由整支持；不需要其迹零 |
| 经典第一源、非经典第二源 $r\ne t$ | 零，由整支持 |

这些来源穷尽 $E\times E$ 的双线性分解，得到 (335.1)。其中与既有 (326.1) 同型的部分是复用；新增适用点是最后两行与 (335.4) 在没有经典—经典迹时仍成立。没有将高阶内部分类等同整个输出。∎

## 336. 原实际联合逐项清掉经典自输入的高阶影像

**引理 336.1（实际双非经典中心对）。** 设一个原实际 $K=JR$ 满足 $\operatorname{rank}E_K>p_*$ 与 $\mathsf G_{\rm HQ}$。若 $T\subset E_J$、$V\subset E_R$ 均非经典，$U=(T,V)$ 是其实际中心对，$n_Tn_V\ge3$，则存在实数 $\alpha_U$，使

$$
\pi_UD^K(x,y)=\alpha_U\,\mathrm i[x_U,y_U]
\qquad(x,y\in E_K).
\tag{336.1}
$$

证明。母卷 30.1／67.3 分别给右单位，框架卷 246.1 给全部原实际中心对的静态复表示，故定理 335.1 对整个 $E_K$ 适用。这里允许逐中心对普通或相反取向，没有预识别原 $D$。

$K$ 的一个经典源恰为 $s=(r,d)$，其中 $r\subset E_J,d\subset E_R$ 都是一维经典块。令 $k,l$ 为原有序局部嵌入，取两个因子中的数学中心单位 $z_r,z_d$。原 X 给 $D^K(kz_r,lz_d)=0$。这两个输入在 $U=(T,V)$ 上都为零；对 $K$ 的经典源而言，二者同时为一的只有 $s=(r,d)$。将它们代入全输入公式 (335.1)，恰得

$$
0=\pi_UD^K(kz_r,lz_d)=-\ell_{Us}I_U.
\tag{336.2}
$$

因此每个 $\ell_{Us}=0$；无经典源时和为空。单位与经典数不受转置影响，所以静态两种取向都包括。此证明沿用既有实际交叉零消去机制，但其全部来源公式已在更弱迹条件下先行证明。没有输入经典—经典规范迹，没有使用反向交叉零，也没有把中心单位或支持角当作实际对象。∎

## 337. 完整原关系网恢复全部被删经典迹

**定理 337.1（两个全背景的无标定恒等桥）。** 对同一完整原数据，不使用 $\sigma_{t_0}$，分别有

$$
\begin{aligned}
B+\mathsf G_{\rm HQ}
&\Longleftrightarrow B+\mathsf G_{\rm HC}
\Longleftrightarrow B+\mathsf G^0_{0h}
\Longleftrightarrow B+\mathrm I+\mathrm{SC}
\Longleftrightarrow B+\mathsf O+\mathsf H,\\
\mathsf B_{\rm cl}+\mathsf G_{\rm HQ}
&\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G_{\rm HC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G^0_{0h}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathrm I+\mathrm{SC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf O+\mathsf H.
\end{aligned}
\tag{337.1}
$$

$\mathsf G^0_{0h}$、O、H 仍取框架卷 311.1、272.1 的原选中域。所得 SC、导子律、I、交替、LU、双单位、原 $q$ 斜伴随、正交零和输出规范迹零则覆盖全部原对象和全部输入，包括未选中的小对象、所有经典对象、二阶块、全部旧输出与失败输出；尤其恢复每条被删经典—经典跨中心迹。

证明。只须独立建立从 $\mathsf G_{\rm HQ}$ 到全域 I+SC 的箭头。母卷 30.1／67.3 与框架卷 246.1 的背景前件已由定义 333.1 保留，故取得右单位与静态复直和，不取得 LU 或原 $D$ 的任何矩阵公式。

任取非零原对象 $A$，在框架卷 202.1 取 $N\ge\max\{3,p_*\}$，固定它实际供应的同一个 $J$、原含幺 Jordan／同一 $D$ 单射 $i:E_A\to E_J$ 与高阶族 $\mathcal V_N$，满足

$$
n_T>N\quad(T\in\mathcal V_N),\qquad
\bigcap_{T\in\mathcal V_N}\ker(\pi_Ti)=\{0\}.
\tag{337.2}
$$

该定理只消费各自完整背景，不消费待证 SC、导子、LU 或标定。它分离的是整个 $E_A$，不要求所有联合块高阶，不要求任何单个投影单射、保 primitive、保秩或等距。

再对这个 $J$ 本身用原身份事件与全事件 R，取它已经供应的某个实际 $K=JR$、$R=P^{\otimes k}$、$k\ge1$，原嵌入记为 $k_J$。不预设直接 $AP$、共同指数或额外的重括号联合。整个原 AC 保证 $P$ 有非经典块，原实际幂的静态全部中心对保证 $R$ 有一个非经典块 $V$。同一个 $K$ 中每个 $U_T=(T,V)$ 都存在，且 $n_{U_T}=n_Tn_V>p_*$，所以 $K$ 在原选中域，(333.2) 在这个完整对象上确实成立。

由引理 336.1，每个 $U_T$ 上对全部完整输入有 (336.1)。静态中心对表示还给单射

$$
\pi_{U_T}k_J(x)=\theta_T(x_T),\qquad
\theta_T:H_{n_T}(\mathbb C)\longrightarrow H_{n_Tn_V}(\mathbb C),
\qquad x_T\longmapsto x_T\otimes I_V
\tag{337.3}
$$

于适当逐对 Jordan 坐标中成立；允许的相反表示不改变其单射性与 Jordan 保持。因此 $h=k_Ji$ 的这些目标共同分离整个 $E_A$。

对全部 $a,b,c\in E_A$，定义原导子缺陷

$$
r_A=D^A_a(b\circ_Ac)-(D^A_ab)\circ_Ac-b\circ_A(D^A_ac).
\tag{337.4}
$$

原 $h$ 保 Jordan 乘法和同一个原 $D$；(336.1) 对全部来源成立，是第二槽导子且交替。故每个 $\pi_{U_T}h(r_A)=0$、$\pi_{U_T}h(D^A_aa)=0$。共同分离给 $r_A=0$、$D^A_aa=0$。这里经典自输入、二阶源和混合源均已由 (335.1)–(336.2) 处理，不能只引用目标内部的 (334.2)。$A$ 任意，所以原导子律与 SC 在全部对象上成立。

SC 极化给 $D_ab=-D_ba$，与已知右单位合用才给 $D_ub=0$。有限 EJA 导子的内性以及原 P/G 的 $\mathfrak k_A$ 识别给 I；每个原 $L_x$ 对本对象原 $q_A$ 自伴随，内导子的有限交换子和便对同一 $q_A$ 斜伴随。没有沿 $h$ 运输内积，不要求不同对象或联合的块权因子化。

现在全域 I+SC 已独立建立，才直接应用框架卷 275.2。完整 $B$ 先按母卷 41.2 取得 Z，再用其原尺度结果；完整 $\mathsf B_{\rm cl}$ 先按母卷 68.2 取得全范围 $\mathsf Q$，再用 70.1、71.1。闭背景的常数可取 $K(A,a)=\|(D^A_a)^2\|_{u_A\to u_A}$，包含全部实际准备、零／小质量和全部数学效果，不能用只对实际零接触成立的 Z 替代它。两边分别得到 II、共同 $\kappa\ge0$，在任意静态坐标中

$$
D^A_ab=\bigoplus_s\lambda_{A,s}\,\frac{\mathrm i}{2}[a_s,b_s],
\quad \lambda_{A,s}^2=\kappa\quad(n_{A,s}\ge2),
\tag{337.5}
$$

经典输出与跨块项全为零；$\kappa=0$ 是全部 $D=0$ 的分支。故全部正交 primitive 输出为零，全部有向输出的规范迹为零，半层输出有原支持。特别地，两个经典 primitive 的整输出为零，因而恢复其原规范迹零，而非仅恢复一组 $q$ 加权评价。

这样已得 $\mathsf G_{\rm HC}$、$\mathsf G^0_{0h}$ 与 O/H 的完整前件。反向 $\mathsf G_{\rm HC}\Rightarrow\mathsf G_{\rm HQ}$ 只需删去经典—经典迹子域；其余等价直接复用定理 327.1、框架卷 275.1 与 314.1。正向在得到 (337.5) 之前没有调用这些候选的全迹结论，也没有输入被删迹。所有箭头保持原 $D$、$q/L$、准备、设备、返回数与合法性不动，故是恒等关系，不是存在某个替代模型的对应。∎

## 338. 同一张原 sigma 的精确单位刻度与候选等价

**定理 338.1（完整 C_HQ 的恒等等价）。** 对同一完整原 $\Omega$、同一原非 $D$ 选择与先于 $D$ 固定的同一 $t_0$，分别有

$$
\begin{aligned}
\mathsf C_{\rm HQ}(B)
&\Longleftrightarrow\mathsf C_{\rm HC}(B)
\Longleftrightarrow\mathsf C_T(B)
\Longleftrightarrow\mathsf C_{\rm support}(B),\\
\mathsf C_{\rm HQ}(\mathsf B_{\rm cl})
&\Longleftrightarrow\mathsf C_{\rm HC}(\mathsf B_{\rm cl})
\Longleftrightarrow\mathsf C_T(\mathsf B_{\rm cl})
\Longleftrightarrow\mathsf C_{\rm support}(\mathsf B_{\rm cl}).
\end{aligned}
\tag{338.1}
$$

全部原数据、字面原 $D$、原比较、质量、同数返回、设备／记录及每条原合法有限历史上的对应均为恒等。由原 $D$ 确定的相容复坐标满足

$$
\begin{gathered}
D_ab=\mathrm i[a,b]/2,\qquad a\cdot b=a\circ b-\mathrm iD_ab,\\
D_aa=D_au=D_ua=0,\quad D_ab=-D_ba,\quad
D_a\in\mathfrak k_A,\quad D_a^{\dagger_{q_A}}=-D_a,\\
D_a(b\circ c)=D_ab\circ c+b\circ D_ac,\qquad
[K,D_a]=D_{Ka}\quad(K\in\mathfrak k_A),\\
[D_a,D_b]=-[L_a,L_b],\qquad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{338.2}
$$

原整个指针的 $d=T_m(u_I)$、$d_0=d-z_P(d)$ 仍满足逐字 S：
$-\operatorname{Tr}_{\mathbb R,E_P}(D_{d_0}^2)=\operatorname{Tr}_{\mathbb R,E_P}(L_{d_0}^2)$，去掉的是整个中心。

证明。定理 337.1 在无标定前已给完整 O/H 和共同尺度；框架卷 276.1 因此在同一张原标签上给

$$
W_{e_0}(p_0)=w_0/4>0,\qquad
q_{J_0}(D_{p_0}e_0,r_0)=0,\qquad
W_{e_0}(2D_{e_0}p_0)=\kappa w_0/4.
\tag{338.3}
$$

所以字面 $\sigma_{t_0}$ 等价于 $\kappa=1$。未改原 $D$、$q$、$W$ 或任何原返回数，亦未按输出更换 $t_0$。给 (337.1) 两边加上这同一条 sigma，即取得 $\mathsf C_{\rm HC}$ 与 $\mathsf C_T$ 的全部前件；此后才直接使用定理 328.1 和框架卷 315.1 得 (338.1)。反向各候选恢复同一 $\mathsf G_{\rm HC}$ 后限制其迹域即得 $\mathsf G_{\rm HQ}$，sigma 本来相同。式 (338.2) 与 S 直接是框架卷 277.1 的未缩放结论，非新尺度或分类定理。相反块的坐标乘法按原 $D$ 定向，不是对原 $D$ 改符号。∎

## 339. 原量子公理、旧过程、完整失败与全部历史的对应

**推论 339.1（准确应用既有量子消费者）。** 在每个 $\mathsf C_{\rm HQ}(B_*)$ 中，定理 329.1 的完整原范围结论成立。其具体对应如下；这些为既有 QM、过程与历史结果的应用。

每个原对象具有同空间复代数

$$
\mathcal A_A=\bigoplus_sB(H_{A,s}),\qquad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\quad
u_A=(I_s)_s,
\tag{339.1}
$$

全部中心与经典块、不等大小均保留，乘法为 (338.2)，没有跨中心相干。记 $\mathcal B_A$ 为原 $g_A^0$ 与规范谱迹间的双运输，$x_\alpha$ 为原泛函的 $g_A^0$-Riesz 向量，$\widehat x_\alpha$ 为其 $q_A$-Riesz 向量，$\mathcal W_A(x)_s=w_{A,s}x_s$。则

$$
\begin{gathered}
g_A^0(x,y)=\tau_A((\mathcal B_Ax)\circ_Ay),\quad
\rho_\alpha=\mathcal B_Ax_\alpha\ge0,\quad
\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)=g_A^0(x_\alpha,y)
=q_A(\widehat x_\alpha,y)=\tau_A(\rho_\alpha y),\quad
\tau_A(\rho_\alpha)=\alpha(u_A),\\
\alpha(D_ab)=g_A^0(x_\alpha,D_ab)
=q_A(\widehat x_\alpha,D_ab)=\tau_A(\rho_\alpha D_ab),\\
T_f:E_B\to E_A,\qquad
\Phi_f=\mathcal B_BT_f^{\dagger_0}\mathcal B_A^{-1}:E_A\to E_B
\quad(f:A\to B).
\end{gathered}
\tag{339.2}
$$

$\dagger_0$ 是原 $g^0$ 伴随，不能用 $q_A(x_\alpha,y)$ 替代原评价；规范迹、适配 $q$、原 $g^0$-Riesz 三者各守自己的类型。零与次归一准备不重新归一，全部相关准备与原乘积准备保原质量；两个背景各保其原生成条件。

每个已经声明的实际联合成为保留全部中心对的普通复张量，原局部嵌入成为交换的含幺 $*$-嵌入。没有增加未声明联合，也不要求 $q_{AB}$ 或 $\mathcal B_{AB}$ 因子化。全部旧事件、实际细记录、原标签、失败、遗忘、返回及合法接续均为 CP/TNI；每个原完整装置为 TP。

对每个数学效果 $0\le e\le u_A$，含零、奇异及零中心分量，整个原 AC、精确 $N_u$、Xs 与原合法连线供应一份所选精确完整有限平方根词，并在其被许可的相关参考上满足

$$
\Phi_{W_e}(\rho)=\sqrt e\,\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{339.3}
$$

投影时为该所选 Lüders 支。若 $p_1$ 为词所用原指针失败方向，$\Psi_\ell:P\to B_\ell$ 为一个原失败映射，其完整失败输出仍为

$$
\sqrt{I-e}\,\rho\sqrt{I-e}\otimes\Psi_\ell(p_1).
\tag{339.4}
$$

只有原实际丢弃才取该失败输出的质量因子，其他指针输入方向与中心仍用原失败映射。此词没有替换任一旧同效果设备。

原 F 的同一实现实际有限细记录、原分组与遗忘给非零单中心细支及其具名返回

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\qquad
\Phi_f=\sum_\ell S_\ell,\qquad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell)\text{ 属源 }A,\qquad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*)\text{ 属目标 }B,\\
U_\ell=\mathsf C_{e_\ell}^AU_\ell\mathsf C_{h_\ell}^B,\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}^A,\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}^B.
\end{gathered}
\tag{339.5}
$$

$q_\ell$ 是原资料中的同一个正数；两条支持等式分别是两侧返回，原反向资料 $(U_\ell,S_\ell,q_\ell)$ 另用同一数。它们各自的完整失败及全部合法后续保留；零标签保留而不要求逆。Kraus 指标没有取代原可访问记录，数学支持没有成为压缩设备。

对每份原准备、每条原合法有限历史 $h=(f_1:A_0\to A_1,\ldots,f_m:A_{m-1}\to A_m)$ 及末端原效果 $w$，有

$$
\alpha(T_{f_1}\cdots T_{f_m}w)
=\tau_{A_m}\!\left(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{339.6}
$$

包括空历史；自适应逐原实际记录分支，原并行逐已供联合与相关输入，分组／遗忘用原线性和，失败／返回／停止取原箭头，条件概率只在原分母正时取比值。

证明。定理 338.1 已先建立定理 329.1 所需完整 $\mathsf C_{\rm HC}(B_*)$，所以该条件纸笔定理直接适用于同一整份原数据。明确其前件对应：全域原导子与曲率给复乘法；原 X 保 Jordan 与同一 $D$，已得交替再给两像交换，原乘积张成和原乘积准备分离才给普通复张量。全事件 R 是每个旧事件的同设备同记录充分大实际参考，在全部相关准备上保正；精确背景使用有限正生成，闭背景使用母卷 69.2 在同一个执行上的完整锥连续延拓，分别给 CP，次幺与原装置效果和给 TNI/TP。整个 AC、精确 $N_u$、Xs 与合法连线对应母卷 12.1、32.1 的词供应，25.2 对应完整失败；原 F 的同实现细记录和原双返回才给 (339.5)。没有用 CP 的数学分解供应缺少的实际记录。

原 $g^0$ 的双对偶给 (339.2)；Riesz 唯一性给 $\mathcal W_A\widehat x_\alpha=\mathcal B_Ax_\alpha$。逐箭头的迹对偶等式迭代得到 (339.6)，逐原分支与原联合组合给全部有限历史。因此没有从局部球面或局部矩阵例子直接跳到全世界消费者。∎

**定义 339.2（分别的物理接口）。** 连续 Hamilton／Schrödinger 动力需要原连续确定可逆一参数器件、物理时钟和具体 Hamiltonian；时间与作用量／$\hbar$ 另须标定。任意独立成功支要装成同一个完整仪器，另需原类型控制、记录与共同合法连线。某个旧同效果设备若要有理想完整输出，另需该旧设备自己的完整输出校准。三者分别取 329.2 的原条件；(338.2) 的系数 $1/2$、(339.3) 的所选词和本候选的迹冗余均不供应这些条件。

## 340. 非空完整满足族与非空删域

**定理 340.1（全签名见证与严格的字面子域删除）。** 定理 330.1 的整个 tagged-CP 族，含无实际 $M_2$ 子族，在任意原菜单、$\mathcal K$ 及同一预选 $t_0$ 下分别满足 $\mathsf C_{\rm HQ}(B)$ 与 $\mathsf C_{\rm HQ}(\mathsf B_{\rm cl})$。相对 $\mathsf G_{\rm HC}$，准确删域为

$$
\mathcal Z_{\rm cc}=\{(A,e,p):\operatorname{rank}E_A>p_*,\quad
 e,p\in\operatorname{Prim}(E_A),\quad
 z(e)\ne z(p),\quad n(e)=n(p)=1\}.
\tag{340.1}
$$

这是有序原标签域，支持域及其余迹域完全相同。存在上述完整满足签名使这个删除域非空；在该域上的冗余不改变完整背景中的可行原结构类。

证明。为明确见证不是局部例子，取带原因子／块／实现标签的所有非零有限复矩阵直和、经典副本及普通实际张量，不按同构合并对象。逐对象预先取任意正定 $r_{A,s}$、正权 $w_{A,s}$，初始定义

$$
\begin{gathered}
g_A^0(x,y)=\sum_sw_{A,s}\operatorname{Tr}(r_{A,s}x_sr_{A,s}y_s),\qquad
\mathcal B_A(x)_s=w_{A,s}r_{A,s}x_sr_{A,s},\\
q_A(x,y)=\sum_sw_{A,s}\operatorname{Tr}(x_sy_s),\quad
D^A_ab=\mathrm i[a,b]/2,\\
x_{\alpha_\rho,s}=w_{A,s}^{-1}r_{A,s}^{-1}\rho_sr_{A,s}^{-1},\qquad
\widehat x_{\alpha_\rho,s}=w_{A,s}^{-1}\rho_s,\qquad
\alpha_\rho(y)=\sum_s\operatorname{Tr}(\rho_sy_s).
\end{gathered}
\tag{340.2}
$$

矩阵正锥、单位、对称乘积与逐块可逆合同群给 P/G；原群对 $g^0$ 的伴随仍在同一合同群内，单位适配恰给上式的原 $q,L$，具体复用框架卷 278.1 与定理 330.1。所有正密度、零与次归一密度均为实际准备，所有实际联合的相关密度也有，所以精确背景和另名闭背景各自成立。各联合可预先有自己的 $r,w$，不要求权因子化。谱分解把任何 Hermitian 响应写成原破坏性效果响应的实线性组合，全部密度分离它，给同一全语境响应商；(340.2) 保持其原 $D$ 的全部有符号评价，允许一般 $g^0\ne q$。

原菜单取全部带实现标记的有限完整 CP 仪器，其已经安装的单中心细口含源／目标块名与 Kraus 标签，完整式为每个输入块的 $\sum_{\ell,t}K_{\ell,ts}^*K_{\ell,ts}=I_s$。全部粗事件、细记录、零标签、分组／遗忘、输出、失败、停止、合法有限顺序／自适应／并行／返回接续均保留。原指针的一个非经典块中取秩一 $d$、质量一纯准备及原破坏性概率一读口和全部失败，给整个 AC；精确合同支与完整补事件给 $N_u$。普通实际联合的嵌入保持 Jordan 和原 $D$，原有序交叉零、乘积张成和实际乘积准备给 X，同设备同记录的 CP 旁接及全部相关输入给 Xs/R，指针幂提供无界大参考。

每条非零单中心细路径 $K$ 配原具名 $S_K=\operatorname{Ad}_K$、$U_K=q_K\operatorname{Ad}_{K^+}$，其中原初始数 $0<q_K\le\lambda_{\min}^+(K^*K)$。伪逆恒等式 $K^+K=e$、$KK^+=h$ 逐项给 (339.5) 的两个支持返回，所给范围使 $U_K$ TNI。原完整失败完成及反向资料 $(U_K,S_K,q_K)$ 用同一个数；其进一步细路径、原遗忘与所有有限接续的闭合完整复用母卷 33.1。这是同一实现已经有的细口，不是由候选为另一个世界增造记录。

交换子的整输出留在输入支持且规范迹零，故 (333.2) 对所有原有序 primitive、包括联合纠缠 primitive 成立；原 $\kappa=1$，(338.3) 对任意预选 $t_0$ 给同一 sigma。至此是定理 330.1 的整个满足族的直接限制应用，没有新一般模型分类。

进一步取原 $P=\mathbb C\oplus M_3$，并把对象域限制为母卷 $\mathcal D_3$ 的有限和、经典标签与实际张量：简单块大小都是 $3^k$，$k\ge0$，故没有实际 $M_2$ 对象或简单块，矩形细支、伪逆、补效果完成及全部历史仍在原输入输出对象内。这个完整子族中已有对象

$$
E_A=\mathbb R\oplus\mathbb R\oplus H_3(\mathbb C),\qquad
p_*=4,\qquad \operatorname{rank}E_A=5>4.
$$

其 $e=(1,0,0)$、$p=(0,1,0)$ 是不同经典中心的 primitive，$(A,e,p)$ 及 $(A,p,e)$ 均属 (340.1)。因此删除域在一份满足两背景的完整原签名中非空，不靠局部反模型或新增实际二阶对象见证。差集公式由 (324.3)、(333.2) 逐字比较得到；定理 337.1 证明冗余。对任意指定 $\Omega$，(340.1) 是否非空只取决于它实际有没有这样的选中对象，不能从本处模型的存在给别的原签名增补对象。∎

## 341. 二元约束、三实维角与全网中的经典房间

**定义 341.1（候选的几何内容与局部失效）。** 同块两颗不同 primitive 的数学支持角是 $H_2(\mathbb C)$，实维四，规范无迹部分实维三。定理 338.1 后，对同块正交 $e,f$，取 $c=e+f$、$y\in V_{ef}$、$y^2=c$，置 $h=e-f$、$z=2D_ey$，已有几何给

$$
h^2=y^2=z^2=c,\quad h\circ y=h\circ z=y\circ z=0,\quad
D_ey=z/2,\quad D_ez=-y/2.
\tag{341.1}
$$

所以 $\rho=(c+rh+sy+tz)/2$ 为迹一正元恰在 $r^2+s^2+t^2\le1$，边界是 primitive。同块零重叠与半重叠分别对应复射影角 $\pi/2,\pi/4$，在 Bloch 球面是对径和正交方向。原 $J_e=2D_e$ 在 $E_{1/2}(e)$ 上满足 $J_e^2=-I$、对原 $q$ 正交，$\omega_e(v,w)=q(J_ev,w)$ 为非退化交替型。这些直接复用 331.1 及其原来源，不计为新的球或复结构定理。

不同中心的两颗 primitive 只有 $\mathbb Re\oplus\mathbb Rp$ 的二维实支持角，原规范无迹交集为一条 $\mathbb R(e-p)$，没有跨中心 Peirce 非对角元或半重叠。若至少一个块非经典，候选仍输入这条无迹线；若两个块都经典，候选只输入整个二维支持面，连这条线也不预先指定。定理 337.1 最终把两类跨中心输出都收为零，但这来自完整原关系网，不是把两个经典中心画成量子相干。

说明删除为何作用在二元关系上：规范迹限制的是同一有向配对的整输出，不能由单个输入的标签单独判定。若孤立看经典二元面，遗漏迹式确会容许总量产生。例如在裸载体 $E=\mathbb R^2\oplus H_3$ 上定义

$$
D^{\rm loc}(a,b)=a_1(b_2-b_1)e_1.
\tag{341.2}
$$

它有右单位零，满足 (333.2) 的全部支持与保留迹：量子第一槽为零，经典与量子混合输入为零，同块量子输入也为零；唯有经典输入的变化沿经典支持。可是 $D^{\rm loc}(e_1,e_2)=e_1$，规范迹一，且 $D^{\rm loc}(e_1,e_1)=-e_1$。这只是局部诊断，没有给完整 X、原实际参考、F 或全历史，不能充当完整背景反模型。它具体说明不能仅凭半层、局部右单位或二维支撑面就宣布经典迹冗余；(335.4) 的经典自输入与 (336.2) 的实际交叉零不可跳过。

较大结构仍是各非经典块 $\mathbb{CP}^{n_s-1}$ 的相交支持角网与各经典中心，全部共享同一原双线性 $D$。半层的两扇窗与第三个复向量位置让高阶内部输出刚性化，实际联合再把经典与低阶来源纳入共同分离。第三个复向量位置不等于三实维 Bloch 截面，两者都不指物理空间三维，不供应实际量子比特、时钟或作用量。规范迹与各块原正 $q$ 权的区别一直保留；此次只少问一个非空有序迹子域，没有独立前提总数、全局最小性、效率或历史优先权结论。

## 342. 证明来源、数学增量与尚未建立的原来源

**定义 342.1（准确复用与新增差额）。** 母卷及框架卷的主源版本固定为 [62e480f8f0a8d9495fed781f3bda49ce922f5795](https://github.com/the-omega-institute/trureturing/tree/62e480f8f0a8d9495fed781f3bda49ce922f5795)，本卷 §§319–332 固定为 [de5a36c756f61b1afc8e37fe80794595b0ebeeed](https://github.com/the-omega-institute/trureturing/tree/de5a36c756f61b1afc8e37fe80794595b0ebeeed)。依赖与实际使用条件如下。

| 来源 | 所用结果与先行条件 |
| --- | --- |
| 母卷 1.1、10.1–10.2、29.3、35.1、41.1、67.1、88.1；框架卷 264.1、272.1–272.2；本卷 324.1 | 两份分别命名的完整原背景、原 $d/D$、准备质量、实 F／同数两侧及反向返回、原选中门槛与预选 sigma；不输入完整三元律。 |
| 母卷 30.1／67.3；框架卷 246.1、202.1 | 先只用完整背景取得右单位、逐对象实际身份参考、静态复载体／全部中心对和高阶目标的整个对象分离；不取得 LU、原 $D$ 识别或共同参考指数。 |
| 框架卷 274.1、273.1；本卷 325.1、326.1–326.2 的机制 | 334.1 先在较弱几何下证明内部右单位、整输出局部性、高阶内部 O；335.1 补足不使用经典—经典迹的全部来源，再用原实际交叉零。既有分类与消去机制不充作新发现。 |
| 框架卷 275.2、276.1、277.1、315.1；本卷 327.1、328.1 | 337.1 先独立建立全域 I+SC，精确／闭准备分别经 Z／完整 Q，才用共同尺度及同一原 sigma，随后应用已发表候选等价。 |
| 母卷 12.1、25.2、32.1、33.1；框架卷 279.1、308.1、316.1–317.2；本卷 329.1–331.1 | 338.1 已齐全部前件，才消费 Born 双运输、实际普通张量、全事件 CP/TNI、完整平方根词与失败、F／同数双返回、全历史、完整满足族与角几何。 |

成熟工具按 [Haagerup–Laustsen, Weak amenability of C*-algebras and a theorem of Goldstein，Theorem 3.1(1)、Lemma 3.4，pp.237–238](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-haagerup/1990s/1998_Weak_amenability_of_C-star_algebras_and_a_theorem_of_Goldstein.pdf)（DOI 10.1515/9783110802009.223）与 [Tao–Gowda, A Representation Theorem for Lyapunov-like Transformations on Euclidean Jordan Algebras，§2、Proposition 3](https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf) 归属。前者 Theorem 3.1(1) 的对象是 C*-代数上的有界复双线性标量型，自伴正交输入消失才等价于两个乘积泛函之和；Lemma 3.4 要求反对称有界型及张成的加法子群上的三次消失，才给到对偶模的 Jordan 导子。本处只通过已经恢复内部 O 的框架卷 274.1 消费其有限维极化机制，不把矩阵值原 $D$ 直接当成原文标量型。后者 §2 明确有限 EJA 导子的内性，Proposition 3 联系导子、Lyapunov-like 与斜伴随；本处先证明原导子律，再用内性及原 $L_x$ 的 $q$ 自伴随性。两类工具及静态分类、尺度、Born／CP、伪逆和 Bloch 几何均为既有中间结果。

本处新增的 $\texttt{repo-derived}$ 差额是：经典—经典非自输入由保留整支持挡在非经典目标之外，而经典自输入仍由 (335.4) 与全部混合来源一同进入 (335.1)，原实际交叉零遂在没有被删迹的条件下消去它们的高阶影像；这使整个对象分离仍可使用，得到 (337.1) 与同一 sigma 下的 (338.1)。新增结论恰为非空经典—经典跨中心迹子域的冗余及其完整原范围桥，不重新交付既有分类、尺度、消费者或满足族。

**定义 342.2（较强删层、native 量化与实际来源的分别边界）。** $\mathsf C_C$ 的半层迹删除问题、全部零层迹删除问题及其既有未决状态均保持；本证明明确使用半层迹和涉及非经典块的跨中心迹，不能由 (337.1) 把它们一起删掉。SourceU27047、母卷 §86.4 的静态接口取向来源、框架卷 §286 的 static supplier／overlap 与实际标量接口问题也保持；不由未打印普遍 $(I,A)$ 推断某个真实联合可删，不重新结算其来源因果链。

[原生 Fibonacci 混合证书 §§1、3–6](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FIBONACCI_MIXING_CERTIFICATES.md) 的有限率／有限编码与字长结果，以及 [native XI §§54–56](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#54-原生完整标记历史的全射线输入界) 的全射线完整标记历史稳定结果，各守其原有前件：全部 $89$ 维复来源、$26+63$ 载体、唯一 ready、十一／七原地址、平方最小电流率、原投影更新、正支撑接续、原读器与独立被动档案接口，保留全部原标签、节点／零／失败／返回和来源已经实现的相关过去。有限率证书不等于取得实际字表或可行物理预算；全射线比较保留原切口全联合差别、共同可读输入与共同档案核，不把不同原向量图的 Dirac 支撑直接混为同一坐标，也不给隐藏过去读权。这些定量定理没有供应整个原 $\Omega$ 对其复来源的采用，没有推出 (333.2)，也没有支付 C128319–323 的 Jordan／Born 来源识别和有符号 $D$ 校准等式。

因此具体原 $\Omega$ 仍须建立完整 $B_*$、$\mathsf G_{\rm HQ}$、同一预选 sigma 及全部被消费的来源／接口。这里把外加迹式的一处要求转为完整定义关系网的结论，不声称所有量子前提已内生，不把条件模型的数学一致性当成本体或经验结论。339.2 的物理时钟／作用量、共同仪器组装和旧同效果设备全输出校准分别保留。全部新旧依赖均是条件纸笔数学，不是 Lean/kernel 或经验验证；整体量子起源目标仍未完成。

## 343. 经典双房间与整座城市的完整直观定义

**定义 343.1（同一条有向关系怎样少问一类问题）。** 白话说，原世界仍是一整座城市：每个量子街区和经典房间、大小不同的中心与原比较权、所有真正的联合与纠缠准备、旧设备和细记录、失败出口、分组遗忘、带原成功数的两侧返回及同数反向资料、每条合法有限历史都原样留下；只在原来选中的大对象里检查同一条有向二元关系，两颗原子完全错开或恰好重叠一半时，整份变化不能跑出它们共同的小屋，半重叠时总增减为零，跨街区错开且至少一边是量子街区时也总增减为零，却不再单独追问两间纯经典房之间的总增减。同一量子街区的两扇半窗和右边整个单位先把高阶内部变化锁为转动，保留的混合迹则切断量子第一槽的跨街输出；经典第一槽仍可能向量子大屋送一笔、再在自己的自输入上补一笔，所以这两笔必须一起计算，不能只看球面。两间经典房之间的变化虽然暂时可以不平衡，却因整支持只能留在那两间房里，照不到非经典目标；把对象接入它原来就有的真实参考整体后，两侧经典中心的原有序交叉零又逐笔清掉自输入留下的高阶影像。那些共同看得见原对象每个区别的大屋便把导子、自守恒、左单位零和所有省去的迹式带回每个小对象、经典房与旧输出，最后仍用早已选好的同一张原刻度单固定共同转动大小，不改原推动、权重或返回率。于是已有理论中的复量子块与经典块、保质量的 Born 双运输、全部实际普通张量和相关输入、所有旧事件、所选精确平方根词及完整失败、原细记录和同数双返回、全部合法有限历史逐项接回。同块小屋的无迹部分是三实维 Bloch 球空间，跨中心小屋却只有一条增减相抵的线，删去经典双房迹后暂时放宽的是它的二维实平面，并没有创造跨中心量子相干；这些小屋共享同一原关系，嵌在更大的复射影角网里，整个原关系网才使这类额外迹问句冗余。半层迹或全部零层迹能否再删仍未解决，原世界实际为何供应这些关系、物理钟和作用量如何标定、独立成功支如何装成共同仪器、旧同效果设备如何有理想完整输出，也各须自己的来源与接口条件。

## 追加锚 C128323（本行以下为增补区）

## 344. 原七地址第一槽与分别保留的三个尾块

**定义 344.1（同一固定关系与来源载体）。** 本卷 §§319–323 固定原有限词校准问题，§§324–332 给出另有完整来源前件的半迹候选。本节研究同一个已识别原生记录零切口的第一输入决定问题。母卷为 [C123 原生互易比较卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，支撑关系取[共同框架续卷 §§272–280、311–318](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#272-原正交零整输出支撑与一张预先固定的原标签)。原有向关系始终是这些条目中事先给定的实双线性 $d_A(a,b)=D^A_ab$，不是由下文的重构公式重新定义原 $d_A$。

固定 [native III 定义 151.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的记录零切口及字面前缀规范，记

$$
\begin{gathered}
E=H_{21}(\mathbb C)_{000}\oplus H_{21}(\mathbb C)_{010}\oplus H_{13}(\mathbb C)_{100},\qquad
u=(I_{21},I_{21},I_{13}),\\
\dim_{\mathbb R}E=1051,\qquad S=\{000,010,100\}.
\end{gathered}
\tag{344.1}
$$

$\pi_s$ 和 $\iota_s$ 是这份直和的数学投影与补零包含，$z_s=\iota_sI_{n_s}$。两个 $21$ 维尾块各有自己的原标签、准备评价与输出分量，未取其和，也不以同构合并。所有向量等式均在整个 $E$ 中成立。

在还未取得原对象 $E_A$ 与这个矩阵载体的含幺 Jordan 识别时，以下首先是字面矩阵载体上的条件命题。应用于原对象时另须给定保原响应的含幺 Jordan 同构 $\theta:E_A\to E$，并在本节记

$$
D(a,b)=\theta\bigl(D^A_{\theta^{-1}a}(\theta^{-1}b)\bigr).
\tag{344.2}
$$

这只是运输同一原 $D^A$，不假设一般原事件保持 $D$，也不从矩阵名称推出 $\theta$ 的存在。

**定义 344.2（实际脉冲效果空间）。** 取原旧事件 $A=\{b_1=1\}$、$Q_0=Q|_{\mathcal K_0}$，对原七地址有限字 $g$ 置

$$
A_g=K_g^*Q_0K_g\in E.
$$

直接复用[原生终端认证卷定理 13.1](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md#13-原七地址-a-效果的精确同步张成)：

$$
\begin{aligned}
\mathcal R&=\operatorname{span}_{\mathbb R}\{A_g:g\in\mathsf W_7\}
 =\{(X,X,Y):5\operatorname{Tr}X=8\operatorname{Tr}Y\},\\
\dim\mathcal R&=609,\qquad
\mathcal R+\mathbb R u=\mathcal S=\{(X,X,Y)\},\qquad\dim\mathcal S=610.
\end{aligned}
\tag{344.3}
$$

两类投影秩分别为 $8,5$，所以关系中的 $5,8$ 与维数 $21,13$ 各有不同来源。全部原旧标签效果
$B_{h,w}=E^0_{h,w}$ 则按 III151.2 实张成整个 $E$；固定合法标签已将其支撑限定在指定尾块，见 III (151.5)。第一槽的 $\mathcal R$ 与第二槽的完整标签空间不能互换。这里的实张成只在响应商内运算，不把线性组合变成实际混合、尾控制或新准备。

**定义 344.3（整输出的跨中心正交零）。** 对每个不同的有序尾块对 $s\ne t$，要求

$$
\mathsf O_\times:\qquad
D(\iota_se,\iota_tp)=0\ \text{于整个 }E,
\qquad e\in\operatorname{Prim}H_{n_s},\quad p\in\operatorname{Prim}H_{n_t}.
\tag{344.4}
$$

共同框架续卷 (272.1) 的完整 $\mathsf O$ 含有本条件。只说某个输出压缩为零、某个准备读数为零，或只检查同一尾块内的正交对，都不是 (344.4)。本节不先要求块内正常形、输出理想保持、SC、导子律、斜伴随、长度或单位曲率。

## 345. 六百零九维原方向决定整个原双线性关系

**定理 345.1（有标签第二槽下的原方向决定公式）。** 对 (344.1) 上任何事先固定的实双线性 $D:E\times E\to E$，若满足 $\mathsf O_\times$，则 $D|_{\mathcal R\times E}$ 唯一决定 $D$ 的全部值，因而 $D|_{\mathcal S\times E}$ 也唯一决定它。定义两个数学提升

$$
\begin{aligned}
J_{21}(X)&=\left(X,X,\frac{5\operatorname{Tr}X}{104}I_{13}\right),\\
J_{13}(Y)&=\left(\frac{8\operatorname{Tr}Y}{105}I_{21},
                         \frac{8\operatorname{Tr}Y}{105}I_{21},Y\right).
\end{aligned}
\tag{345.1}
$$

它们都取值于 $\mathcal R$。对所有完整 $a,b\in E$，有整输出公式

$$
\boxed{\begin{aligned}
D(a,b)={}&D(J_{21}(a_{000}),\iota_{000}b_{000})\\
&+D(J_{21}(a_{010}),\iota_{010}b_{010})\\
&+D(J_{13}(a_{100}),\iota_{100}b_{100}).
\end{aligned}}
\tag{345.2}
$$

特别地，对任何两个都满足本条件的固定关系 $D,\widetilde D$，若它们在全部实际 $A_g$ 的第一槽和全部旧标签效果 $B_{h,w}$ 的第二槽上具有相同的整个输出，则它们在 $E\times E$ 上相等。结论不需要 $D(a,u)=0$，所以不必把单位补成第 $610$ 个第一槽方向。

证明。Hermitian 元的谱分解将每块写成 primitive 投影的实线性组合。对不同块分别展开两个输入，双线性及 (344.4) 给

$$
D(\iota_sx,\iota_ty)=0\quad(s\ne t;\ x\in H_{n_s},y\in H_{n_t}).
\tag{345.3}
$$

这里只复用成熟有限维谱分解及既有正交展开步骤，不调用交换映射分类。(345.3) 是完整向量零，因此

$$
D(a,b)=\sum_{s\in S}D(\iota_sa_s,\iota_sb_s).
\tag{345.4}
$$

$5\operatorname{Tr}X=8\cdot13\cdot5\operatorname{Tr}X/104$，且
$5\cdot21\cdot8\operatorname{Tr}Y/105=8\operatorname{Tr}Y$，故 (345.1) 确在 $\mathcal R$。其对应块投影分别为 $X,Y$。在 (345.4) 的每项，将 $\iota_sa_s$ 换为对应的 $J_{21}(a_s)$ 或 $J_{13}(a_s)$，所添的其他块均被 (345.3) 消去，得到 (345.2)。两个 $21$ 维项使用相同形式的第一槽提升，却分别使用 $\iota_{000}b_{000}$ 和 $\iota_{010}b_{010}$；没有混同两个尾块或选择新的输出取向。

最后，(344.3) 与 III151.2 将实际 $A_g,B_{h,w}$ 上的相等双线性延拓到 $\mathcal R\times E$，再由 (345.2) 得全域相等。所有消去在输入槽进行；每一项的输出一直是整个 $E$，未假设它留在对应源块。∎

**定理 345.2（存在、唯一与原关系识别分别承担的条件）。** 设 $r:\mathcal R\times E\to E$ 是给定实双线性数据。存在满足 $\mathsf O_\times$ 且限制为 $r$ 的全域双线性关系，当且仅当

$$
r(x,\iota_tb)=0
\quad(t\in S,\ x\in\mathcal R\cap\ker\pi_t,\ b\in H_{n_t}).
\tag{345.5}
$$

若存在，它唯一，且由 (345.2) 中将右边 $D$ 换成 $r$ 给出。此唯一扩张等于一份预先固定的原 $D$，还必须取得该原 $D$ 自身满足 $\mathsf O_\times$ 以及 $D|_{\mathcal R\times E}=r$；选择一个扩张不供应这两条原等式。

证明。若已有这样的 $D$，当 $\pi_tx=0$ 时，$x$ 只含非 $t$ 的块，(345.3) 给 (345.5)。反之，以 (345.2) 的右边定义辅助关系 $D_r$。它实双线性；不同块输入时，第二槽所在块对应的第一坐标为零，所以 $D_r(\iota_sa,\iota_tb)=0$ 对 $s\ne t$ 成立。对 $x\in\mathcal R$，$x-J_{n_t}(\pi_tx)\in\mathcal R\cap\ker\pi_t$，其中 $J_{n_t}$ 按块大小取 (345.1) 的对应提升。因此 (345.5) 给

$$
D_r(x,b)=\sum_tr(J_{n_t}(\pi_tx),\iota_tb_t)
        =\sum_tr(x,\iota_tb_t)=r(x,b).
$$

定理 345.1 给唯一性。这里仅构造辅助候选 $D_r$，没有用它改写一份未知的原 $d_A$。

在这个具体来源中，两个 $21$ 块各自的第一投影核均为
$\{(0,0,Y):\operatorname{Tr}Y=0\}$，维数 $168$；$13$ 块的核为
$\{(X,X,0):\operatorname{Tr}X=0\}$，维数 $440$。所以 (345.5) 的对象、两个重复核及其第二槽标签均为明确有限维关系；它不是任意表值都能延拓的保证。∎

## 346. 完整原正交律与守恒导子入口的分别适用

**定理 346.1（原结构入口的准确消费范围）。** 定理 345.1 的原来源应用有两种充分入口：同一载体上的完整整向量 $\mathsf O$；或同一载体上的实双线性 $D$、全域自守恒 $D(a,a)=0$ 及每个 $D_a$ 对整个 $E$ 的 Jordan 导子律。后一入口已经推出 $\mathsf O_\times$，不另需要斜伴随或一般交换映射分类。

证明。第一入口只是 (344.4) 的原有序子域。对第二入口，SC 在 $a+b$ 处极化得 $D(a,b)=-D(b,a)$。固定任意 $a$，将全域导子 $D_a$ 作用于中央幂等元 $z_t^2=z_t$，得

$$
D_a z_t=2z_t\circ D_a z_t.
$$

$L_{z_t}$ 是逐块坐标投影，只有本征值 $0,1$，故 $I-2L_{z_t}$ 可逆，$D_a z_t=0$。再对 $z_t\circ b$ 用导子律，得

$$
D_a(\iota_tb_t)=z_t\circ D_a(\iota_tb_t)\in\iota_tH_{n_t}.
$$

若 $a\in\iota_sH_{n_s}$、$b\in\iota_tH_{n_t}$、$s\ne t$，这个值在第 $t$ 个输出理想；交替后它又在第 $s$ 个输出理想，因此为零。这是从**完整环境**导子律取得的交叉零，不是只在单个块内部试验导子。随后直接应用定理 345.1。∎

**定义 346.2（既有结构的复用与来源限定）。** 共同框架续卷定理 274.1、275.1、314.1 的正常形及原参考下降全部保持。若已在同一个原 $\Omega$ 上取得它们要求的完整 $B_*$、原选中域的几何及原实际参考，则按其全对象结论，本节切口一旦是其中一个已识别原对象，就具有上述入口。不能只从 native 的字面 $E$ 或某次 $M_0$ 压缩推出该切口拥有原全背景，不能将一般记录更新当作保 $D$ 的原含幺 Jordan 嵌入。

本卷 §§324–332 的完整半迹候选与上述结构入口有条件地重叠：若这个记录零切口确为同一原 $\Omega$ 的完整 $B_*$ 中的原对象，并已供应定理 327.1 的全部前件，则该定理的全域 I+SC 给出本节的守恒导子入口，因而可用定理 345.1。若另有同一预选 $\sigma$，定理 328.1 还给单位尺度；这是在由原 $D$ 确定取向的复坐标中成立的条件结论，未把该取向绑定到原字的既定矩阵坐标。这里直接复用半迹恢复与全原范围下降，不重作其一般分类；这些结论不供应具体 native 切口的原对象身份、$\theta$、全部原 $\beta_a$ 采用或 (347.3) 的实际有符号 $D$ 等式。

相反，§321 的 $D^\varepsilon$ 已逐项给出：双单位零、每个第一输入的全域第二槽导子及正块权迹型斜伴随，仍不足以确定全域 $D$。其具体原标签 $e,f$ 的 $D^\varepsilon(e,f)\ne0$ 违反完整正交零。它也违反本节所需的跨中心子域：令 $e^\prime=\iota_{010}|u\rangle\langle u|$ 使用 §321 的同一前缀 $u$，则 $\ell(e^\prime)=-1$，$D^\varepsilon(e^\prime,f)=-\varepsilon Z/2\ne0$。它还违反全域 SC：§321 的 $e,H$ 满足 $\ell(e+H)=1$ 且 $[H,e]\ne0$，所以对 $\varepsilon\ne0$ 有
$D^\varepsilon(e+H,e+H)=\varepsilon\mathrm i[H,e]/2\ne0$。因此它不能反驳定理 346.1 的守恒导子入口，也没有被升级为完整原合同反模型。原迹型斜伴随不是缺失 SC 的替代条件。

## 347. 原脉冲的符号、尺度与仍缺的同一 D 等式

**假设 347.1（这个原切口的响应采用）。** 除 (344.2) 外，另须将原 ready、全部十一地址前缀 $a$、原记录零和原旧终端在此切口的响应采用为

$$
\begin{gathered}
\chi_a=K_ae_{\rm r},\qquad
\beta_a(x)=\langle\chi_a,M_0xM_0\chi_a\rangle,
\qquad \beta_a(u)=t_0(a),\\
P_{\mathsf R(a,f)}(i=0,w)=\beta_a(B_{f,w})
\quad(a\in\mathsf W_{11},\ f\in\mathsf W_7,\ w\in\Omega_{10}).
\end{gathered}
\tag{347.1}
$$

这里 $x$ 按 $E\subset\operatorname{End}\mathcal K_0$ 作用并向整个 $\mathcal K$ 补零；$\beta_a$ 是未归一原分支评价，零质量时为零。它是 §319.2 的 Jordan／Born 来源采用在这个指定切口上的版本，不是由 (344.3) 或 (345.2) 推出的概率规律。所有 $1024$ 个旧标签、非法标签的零投影、完整失败、真实调用和原记录仍在同一来源。

**定义 347.2（原正向字及必须另供的有符号来源等式）。** 原相位为 $\vartheta=3\pi/5$、$\zeta=e^{\mathrm i\vartheta}$，$K_j=\zeta[I+(\zeta-1)\mathcal P_j]$。若 $g=(j_1,\ldots,j_m)\in\mathsf W_7$，$g^-=(j_m^9,\ldots,j_1^9)$ 是原正向端点逆字。它不是隐藏配置历史的反向过程。定义合法后读菜单及原联合响应

$$
\begin{aligned}
f^+_{g,h}&=g\,0\,g^-h,&
p^+_{a,g,h,w}&=P_{\mathsf R(a,f^+_{g,h})}(i=0,w),\\
f^-_{g,h}&=g\,0^9g^-h,&
p^-_{a,g,h,w}&=P_{\mathsf R(a,f^-_{g,h})}(i=0,w).
\end{aligned}
\tag{347.2}
$$

两请求均为原外生七地址后读字，不依赖记录值；只在记录结果中读取 $i=0$ 那一组。它们不增加条件控制。所需新来源等式为

$$
\boxed{\quad
\beta_a\bigl(D(A_g,B_{h,w})\bigr)
=\frac{p^-_{a,g,h,w}-p^+_{a,g,h,w}}{4\sin\vartheta}.
\quad}
\tag{347.3}
$$

左边必须评价预先固定的原 $D$。右边是两个实际请求的联合概率差，不是新正事件或一份可访问的共同反事实样本。未除以记录质量，所以零质量分支亦有意义；若改用正质量条件概率，两边须同时除以同一个 $t_0(a)>0$。

**定理 347.3（有来源前件的完整关系识别）。** 在假设 347.1 下，若同一原 $D$ 另满足定理 346.1 的任一充分入口，并供应 (347.3)，则在整个字面 $1051$ 维载体上

$$
D(a,b)=\delta(a,b):=\tfrac{\mathrm i}{2}[a,b]
\qquad(a,b\in E).
\tag{347.4}
$$

可以只在有限个实际前缀、有限个实际 $g$ 与有限个实际 $(h,w)$ 上供应 (347.3)：分别选取分离全部输出的原 $\beta_a$、张成 $\mathcal R$ 的原 $A_g$ 及张成 $E$ 的完整标签效果即可。三组选择只依原非 $D$ 数据，不按原 $D$ 的输出重选。结论不请求分别控制两个 $21$ 维尾块，也不从有限精确等式取得含噪认证或效率保证。

证明。以下端点计算只是 §320 (320.2) 的成熟两谱恒等式在原记录零和完整标签上的应用。令
$V_g=K_g^*K_0K_g=\zeta[I+(\zeta-1)A_g]$，则原字顺序 $K_{gh}=K_hK_g$ 及 (347.1) 给

$$
\begin{aligned}
p^+_{a,g,h,w}&=\beta_a(V_g^*B_{h,w}V_g),\\
p^-_{a,g,h,w}&=\beta_a(V_g B_{h,w}V_g^*),\\
V_g B V_g^*-V_g^*B V_g
 &=2\mathrm i\sin\vartheta[A_g,B]
  =4\sin\vartheta\,\delta(A_g,B).
\end{aligned}
\tag{347.5}
$$

所以端点给的是 $\beta_a(\delta(A_g,B_{h,w}))$。只有再用 (347.3)，才得到它与原 $\beta_a(D(A_g,B_{h,w}))$ 相等。$\sin\vartheta>0$，正负标签、$0^9$ 及因子四不能省略。

全部十一地址原有限前缀的 ready 射线轨道在 $\mathbb{CP}^{88}$ 稠密，复用 III144 及 §320 已核对的来源对应。若 $x\in E$ 被每个 $\beta_a$ 杀掉，将 $M_0xM_0$ 向全 $89$ 维空间补零，其二次型在该实际稠密轨道为零；连续性使其在全部射线上为零，故 $x=0$。有限维性允许抽取有限个实际 $\beta_a$ 分离 $E$。这只证明已有原前缀评价的线性分离，不供应任意准备、reset 或其物理凸混合；非零分离行自然有正记录质量。原 $A_g$ 与完整标签效果的有限基分别由 (344.3) 和 III151.2 取得。因此有限 (347.3) 已使 $D-\delta$ 在 $\mathcal R\times E$ 上有完整输出零。$\delta$ 满足 $\mathsf O_\times$，原 $D$ 也满足；定理 345.1 给 (347.4)。这里没有重新交付 §320 的全载体框架重构，而是用 (345.2) 跨过原七地址第一槽的反同步缺口。∎

**定义 347.4（原供应与未建立的等式）。** native III145 的固定内部模型取
$H_j=-\vartheta(I+\mathcal P_j)$、$U_j(s)=e^{-\mathrm i sH_j}$。在已经采用 Born 的矩阵模型中，数学 Heisenberg 生成元为

$$
\mathcal L_j(B)=\mathrm i[H_j,B]
=-2\vartheta\,\delta(\mathcal P_j,B).
\tag{347.6}
$$

因此若额外把原 $D_{\mathcal P_j}$ 识别为这个生成元的 $-1/(2\vartheta)$ 倍，可取得相应符号与尺度；这项识别本身正是尚需供应的原等式。原地址不允许中断脉冲、改变内部 $s$ 或请求非整数调用，故不能把 (347.6) 的数学微分当作额外实际读数。

C1231.5 给原双线性 $d_A$ 并另要求全三元律；它没有给 (347.3) 的原脉冲评价。III151 给字面矩阵和比较行，并明确比较行成为实际概率另需接口；III145 的 Bell 最小电流、平方权重、纯更新和细档案独立性都是该生成模型的输入。其引用的 DGTZ 原文 §2.7 (23)–(29) 也明确先给 Hilbert 空间、Hamiltonian 和 Born POVM 概率，再构造等变率，未从率反向识别这里的原 $d_A$。[native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#1-原来源完整端点与不变的实际读取) 的端点守恒与 retained-read 条件约束同一个 $\Pi$，也未出现原有向响应 $\beta_a(d_A(A_g,B_{h,w}))$ 的等式。即使在各自额外校准条件下取得 Born 响应，也仍须连接这个原 $d_A$。

因而，在所引 C123、共同框架 §§272–280、293、311–318、native III144–145、151、XI1、原生终端认证 §13 及本卷 §§319–323 的限定原生来源范围内，尚未由原生端点／记录数据推出的是：这个原切口的 $\theta$ 与全部 $\beta_a$ 采用、原 $D$ 在完整跨中心有序域上的零关系或完整守恒导子入口，以及关于同一原 $D$ 的 (347.3)。不把未找到供应写成不存在供应，也不以 §321 的弱律歧义制造一个完整原合同反例。

## 348. 三实维角、相同来源与不变的全部消费者

**定义 348.1（决定关系后的有限角几何）。** 若已取得 (347.4)，在任一尾块内复用 §322、共同框架定义 277.2 的数学二阶角：取正交 primitive $e,f$，$c=e+f$，$h=e-f$、$X=E_{12}+E_{21}$、$Z=\mathrm i(E_{12}-E_{21})$。它们满足

$$
h^2=X^2=Z^2=c,\qquad h\circ X=h\circ Z=X\circ Z=0,
\qquad D_eX=Z/2,\quad D_eZ=-X/2.
\tag{348.1}
$$

$(c+rh+sX+tZ)/2$ 为角内迹一正元恰要求 $r^2+s^2+t^2\le1$。这是同一尾块的三实维无迹截面；(345.2) 恢复不同尾块中各自带标签的 $D$，没有取平均、抵消或为每个角另选一个推动。不同角的内部相容性复用既有完整正常形与量子重构，不重证一般交换映射或 Jordan 分类。这里的跨块输入零也不能替代同块角内的导子、复结构或单位曲率；这些在 (347.4) 识别后才具有上述具体数值。

这项三实维几何不是物理空间维数，也不供应实际 $M_2$、连续时间或新操作。$J_{21},J_{13},\pi_s,\iota_s$ 是响应线性运算；原程序没有因为出现这些符号而获得独立尾控制。

**定义 348.2（原全目标的消费接口）。** 只有在同一个原 $\Omega$ 上对全部原对象和实际联合另已建立完整 $B_*$、相应原几何、原参考、同一固定 $\sigma$ 及所有来源接口时，才直接复用共同框架定理 314.1–316.1、279.1 的整链：原复乘法及全部原准备的 Born 双运输、保全部中心对的实际普通复张量、全事件及相关参考上的 CP/TNI、完整装置 TP、所选完整平方根词与原失败输出、细记录／分组／遗忘、原同数支持双返回及每条原合法有限顺序、自适应和并行历史。原有准备、实际乘积与相关输入、零与次归一质量、旧设备／端口、真实记录、失败、停止、返回及全部合法未来保持原身份；不以这个记录零切口替换它们。

本节只解决这个已经识别切口中“同步第一输入是否在强结构律下决定同一原 $D$”的问题。它不把 $M_0$ 更新变成保 $D$ 的下降，不供应其他对象所需的分离嵌入，不从 ready 轨道的稠密性推出实际准备的精确有限正生成，也不自动证明已列全局前件。物理时钟、能量和作用量／$\hbar$ 单位、可靠控制及取得／认证成本、任意独立成功支的共同完整仪器组装、旧同效果设备的完整输出校准仍各需原来源。完整唯一 $\Omega$ 的量子起源目标因此未由本条件桥闭合。

## 349. 原始文献、既有结果与来源特定增量

**定义 349.1（参数映射与数学归属）。** 以下成熟结果只在上述来源特定推导内复用，不另作为新增分类或一般校准定理：

| 来源 | 此处使用与适用边界 |
| --- | --- |
| C1231.1、1.5；共同框架293.2 | 同一个全语境响应商、事先固定的向量值实双线性 $d_A$ 与有符号准备评价；不把 $D$ 设为正事件。 |
| native III151.1–151.2；原生终端认证13.1 | 全部原标签第二槽空间 $E$、同步第一槽原始空间 $\mathcal R$、含幺空间 $\mathcal S$，分别为 $1051,609,610$ 维；全部同型旁观尾块保留。 |
| 共同框架274–280、311–318；本卷319–323 | 既有结构正常形、全背景原参考下降、尺度与全量子消费者；既有端点恒等式和弱律歧义。不重作一般分类、算子框架或全载体端点标定。 |
| 本卷324–332 | 完整 $B_*$、半层／跨中心迹几何及同一预选 $\sigma$ 下的条件等价；定理 327.1 的结构入口可按定义 346.2 消费。该候选没有使用原 $609$ 维脉冲空间、(345.1) 的迹相容提升或 (345.5) 的延拓核，也不供应 (347.3) 的 native 有符号校准。 |
| [Freedman–Larsen–Wang，math/0103200v1](https://arxiv.org/pdf/math/0103200v1)，Theorem 0.1、§2 Lemma 2.1、Definitions 1–2 | 原文定理是整个 Jones 直和闭像包含各扇区 $SU$ 的乘积。按 III151 的既有逐路径对应取 $(k,r,n)=(2,5,8)$、表形 $[5,3],[4,4]$；按 III144／§320 取 $(2,5,12)$、$[6,6]$ 的全 $89$ 维来源。$r=5$ 满足其例外与维数门槛；相同 $21$ 维旁观副本不成为两个独立因子。 |
| [Schuld 等，1811.11184v1](https://arxiv.org/pdf/1811.11184v1)，§III.A Theorem 1、(12)–(14) | 已知两谱生成元可精确移位。这里 (347.5) 直接使用已有固定角端点恒等式及原 $0^9$ 正向字，不向原菜单增加可调参数、内部读口或辅助受控门。它确定 $\delta$ 的端点读数，不能自行确定原 $D$。 |
| [Tao–Gowda，作者原文](https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf)，§2、Proposition 3 | 有限 EJA 导子及 Lyapunov-like／单位零／斜伴随之间的成熟关系。§346 只在导子律已覆盖整个 $E$ 时用中央幂等元微分消去跨块输入；未从斜伴随单独推出导子或 SC。 |
| [Dürr–Goldstein–Tumulka–Zanghì，quant-ph/0407116v1](https://arxiv.org/pdf/quant-ph/0407116v1)，§2.7 (23)–(29) | 原文先供量子演化与 Born POVM 分布，再构造等变最小跳率；这里只用于限定 III145 的来源层次，不将其作为原有向双线性 $d_A$ 或概率指数的起源证明。 |

上述成熟中间工具属 $\texttt{literature-attested}$。本节 $\texttt{repo-derived}$ 的实质综合是：(345.1)–(345.5) 将原 $8/5$ 秩轨道的 $609$ 维同步第一槽，借完整带标签第二槽及原跨中心整向量零关系，接回两个分别保留的 $21$ 维尾块和 $13$ 维尾块上的全部原双线性值；并将这个结构决定命题与 (347.3) 的同一原关系来源义务明确分开。其结论改变的是原第一槽缺口在强结构域内的地位，不是宣布实际来源已经校准，也不主张全球原创、独立公理数减少或认证效率。

## 追加锚 C128349（本行以下为增补区）

## 350. 原有限词上的实偶部与同一原有向奇部

**定义 350.1（采用层次及保留的原来源）。** 原签名、全语境响应商和预先固定的实双线性关系始终取 [C123 母卷定义 1.1、假设 1.5](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#1-原响应二元关系与有限三元相容)：$D_ab=d_A(a,b)$。指定切口的原实响应商另已成为有限实 Euclidean Jordan 代数 $(E,\circ,u,q)$，其中 $q$ 是该商的原正定 Frobenius 比较，$q(a\circ b,c)=q(a,b\circ c)$。这个实 EJA 的来源采用是前提；不由“归一化”一词、有限维、相同端点概率或以下方程自动供应。此时尚不采用复矩阵载体、Born 公式或普通复张量。

令 $e\in E$ 为一个确已供应的原效果，另已知 $e^2=e$。它不必 primitive。令一个原正向有限词的 Heisenberg 代入确实下降为含幺 Jordan 自同构 $R:E\to E$，且十次同词调用下降为恒等，$R^{10}=I$。九次原正向调用遂给 $R^{-1}=R^9$。这是端点逆词，原设备身份、调用位置、时点、内部路径及历史不取这个响应商，也不认作时间反演。良定下降、幂等性、自同构性及十次恒等均为需由原来源给出的事实，不从状态空间中任选的数学变换代替原词。

固定

$$
\vartheta=\frac{3\pi}{5},\qquad c_\vartheta=\cos\vartheta,\qquad
s_\vartheta=\sin\vartheta>0,\qquad
P_e=4(L_e-L_e^2),\qquad L_ex=e\circ x.
\tag{350.1}
$$

成熟 Peirce 分解给 $P_e$ 为 $E_{1/2}(e)$ 的 $q$-正交投影，$\ker P_e=E_1(e)\oplus E_0(e)$。它不是支持压缩 $2L_e^2-L_e$。一维经典块、跨中心项及高秩幂等元的整个 $E_1(e)$ 都保留。

**假设 350.2（原有限词的有向实响应律）。** 对定义 350.1 的同一原 $e,R,D$，在整个原输出空间上要求

$$
\begin{aligned}
\mathsf{Even}_e:\quad R+R^{-1}
 &=2I-2(1-c_\vartheta)P_e,\\
\mathsf{Odd}_{e,D}:\quad R^{-1}-R
 &=4s_\vartheta D_e.
\end{aligned}
\tag{350.2}
$$

这是原响应向量的等式，不能只在某块压缩后或某几个输出评价上成立。实加减仅在原线性商中进行，不供应混合、复制、reset、控制或新仪器。原准备 $\alpha$ 对第二式的评价为

$$
\alpha(D_eb)=\frac{\alpha(R^{-1}b)-\alpha(Rb)}{4s_\vartheta}
\qquad(b\in E).
\tag{350.3}
$$

其中 $\alpha(D_eb)$ 是原有符号响应评价，未被宣称为正事件；若 $b$ 是实际后续效果，右边来自两个各自合法的原请求，不把二者之差当作新事件或额外可访问的共同反事实样本。

可以另定义一个新算子 $\widehat D_e=(R^{-1}-R)/(4s_\vartheta)$，但这只定义新响应。只有另给 $D_e=\widehat D_e$，才有关于预先固定原 $D$ 的结论。特别地，$\mathsf{Even}_e$ 不含 $D$；原端点、有限阶或一个存在的守恒对数，都不自动证明 $\mathsf{Odd}_{e,D}$。以下把它作为独立候选来源公理，未断言原来源已经满足它。

## 351. 十个原整数端点给出的局部导子与三实维子截面

**定理 351.1（原有限响应律的局部结论）。** 在定义 350.1、假设 350.2 下，令 $J=2D_e$。则在整个原 $E$ 上有

$$
\begin{gathered}
JP_e=P_eJ=J,\qquad J^2=-P_e,\qquad
D_eu=D_ee=0,\\
J(x\circ y)=Jx\circ y+x\circ Jy,\qquad
q(Jx,y)=-q(x,Jy),\\
q(Jx,Jy)=q(P_ex,P_ey),\qquad
R=I-P_e+c_\vartheta P_e-s_\vartheta J
 =\exp(-\vartheta J)=\exp(-2\vartheta D_e).
\end{gathered}
\tag{351.1}
$$

$D_e$ 因而是守恒 $e$ 的原 Jordan 导子，且对原比较斜伴随；$J$ 在横向 Peirce 空间上是正交四分之一转动，在另两个 Peirce 空间上为零。这里不声称所有其他第一输入 $D_a$ 已为导子、自守恒或满足混合曲率。$P_e=0$ 时 $R=I,D_e=0$；这种中央或退化切口没有非零转动，也不能标定共同尺度。

若还存在同一实 EJA 中的正交 primitive $p,f$ 及数学元 $X$，满足

$$
\begin{gathered}
p\le e,\qquad f\le u-e,\qquad c=p+f,\qquad h=p-f,\\
p\circ X=f\circ X=X/2,\qquad X^2=c,
\end{gathered}
\tag{351.2}
$$

则 $Z=JX$ 使 $\mathcal B=\operatorname{span}_{\mathbb R}\{c,h,X,Z\}$ 成为 $R$ 不变的四实维 Jordan 子代数，$c$ 为其单位，其规范迹一正截面为三实维闭球。条件 (351.2) 要求一个跨过原切口的非零秩二方向；单生成元响应律本身不供应这组方向、原准备或相应设备。

证明。以下使用 Peirce 谱分解、有限三角插值及实 EJA 谱论作为成熟中间工具，所求结论始终关于定义 350.1 的原词和原 $D_e$。

由 $\mathsf{Even}_e$，$P_e$ 是 $R,R^{-1}$ 的多项式，故与它们对易。在 $N=\ker P_e$ 上，$R+R^{-1}=2I$，从而 $(R-I)^2=0$。写 $R|_N=I+N_0$，则 $R^{10}|_N=I+10N_0=I$，故 $R|_N=I$。在 $W=\operatorname{im}P_e$ 上，$R+R^{-1}=2c_\vartheta I$，于是

$$
\left.\left(\frac{R^{-1}-R}{2s_\vartheta}\right)^2\right|_W
=\frac{(2c_\vartheta)^2-4}{4s_\vartheta^2}I=-I.
\tag{351.3}
$$

$\mathsf{Odd}_{e,D}$ 说这里的算子就是原 $J$。它在 $N$ 上为零，给 $J^2=-P_e$、$JP_e=P_eJ=J$。$u,e\in N$，故两个守恒等式成立。把 (350.2) 相减，得 (351.1) 的 $R$ 公式。由 $J^2=-P_e$ 及 $J|_N=0$ 的实幂级数，定义数学族

$$
T(t)=I-P_e+\cos t\,P_e-\sin t\,J=\exp(-tJ).
\tag{351.4}
$$

其整数值满足 $T(k\vartheta)=R^k$。现在证明这个数学族保持原乘法，而非假设一个实际连续控制。对任意原 $x,y$，

$$
F_{x,y}(t)=T(t)(x\circ y)-T(t)x\circ T(t)y
\tag{351.5}
$$

在任何实坐标中都是次数至多二的三角多项式。$k=0,\ldots,9$ 时，$R^k$ 为原 Jordan 自同构，故 $F_{x,y}(k\vartheta)=0$。$\gcd(3,10)=1$，这十个角模 $2\pi$ 互异。一个次数至多二的非零三角多项式至多有四个互异圆周零点：置 $z=e^{it}$ 并乘 $z^2$，得到次数至多四的普通多项式即可。故每个坐标恒零，$T(t)$ 对全部数学实参数保持乘法；其逆为 $T(-t)$。在零点求导，$T'(0)=-J$，遂得原 $J$ 的导子律。这一步只用十个原整数端点和原乘法相容，不引入复量子载体；证明多项式零点所用的标量复化不等于物理复结构的采用。

为核对比较仍是原 $q$，对任意 primitive frame $(r_i)$，导子律给 $Jr_i=2r_i\circ Jr_i$，故 $Jr_i\in E_{1/2}(r_i)$。$r_i$ 及所有 $r_j$、$j\ne i$，分别在它的 $E_1,E_0$ 中，Peirce 正交性给 $q(Jr_i,r_j)=0$。任意 $x$ 在某个 frame 中谱展开，所以 $q(Jx,x)=0$；实极化给斜伴随。再用 $J^2=-P_e$ 即得 $q(Jx,Jy)=q(P_ex,P_ey)$。这对不等正简单块权同样成立，未将原 $q$ 换成规范迹。

最后取 (351.2)。$p,f\in\ker P_e$，故 $Jp=Jf=Jc=Jh=0$。导子律使 $J$ 保持 $E_1(c)$ 和 $p,f$ 的共同横向空间。因为 $e=p+(e-p)$，且 $e-p$ 与 $c$ 正交，$L_e$ 在 $E_1(c)$ 上就是 $L_p$；所以 $P_eX=X$、$J^2X=-X$。对 $X^2=c$ 求导，再对所得 $X\circ JX=0$ 求导，有

$$
X\circ Z=0,\qquad Z^2=X^2=c.
\tag{351.6}
$$

另外 $h^2=c$、$h\circ X=h\circ Z=0$。$J$ 的斜伴随性和等距性使非零 $X,Z$ 正交等长；它们属于 $p,f$ 的非对角 Peirce 空间，与 $c,h$ 线性独立。故 $\mathcal B$ 恰为四实维，且

$$
\begin{gathered}
h^2=X^2=Z^2=c,\qquad
h\circ X=h\circ Z=X\circ Z=0,\\
JX=Z,\quad JZ=-X,\quad
RX=c_\vartheta X-s_\vartheta Z,\quad
RZ=s_\vartheta X+c_\vartheta Z.
\end{gathered}
\tag{351.7}
$$

这是成熟秩二 spin 乘法在同一原 $D_e$ 下的具体不变子代数。令 $v=rh+sX+tZ$，则 $v^2=(r^2+s^2+t^2)c$；原 EJA 谱演算给

$$
\rho=\frac{c+rh+sX+tZ}{2}\ge0
\quad\Longleftrightarrow\quad r^2+s^2+t^2\le1,
\qquad \tau^J(\rho)=1.
\tag{351.8}
$$

确切地，两个角内本征值为 $(1\pm\sqrt{r^2+s^2+t^2})/2$，角外补零；球面点为 primitive。此处采用规范 Jordan 谱迹描述数学正截面，未把它当作原 $q$、实际准备评价或 Born 来源。

整个支持角 $E_1(c)$ 要恰为这四维，还须其共同横向空间只有二实维；否则 $\mathcal B$ 仅是其中一张不变三实维无迹截面。一般 $E_{1/2}(e)$ 可以有许多这样的转动平面。$J$ 是响应商算子，不是新实际四分之一脉冲；三实维是数学截面维数，不是物理空间维数、实际 qubit 对象或全局维数结论。尤其原 $e$ 高秩时，只在上述子代数内使用 $L_e=L_p$，没有推出或使用全域 $D_e=D_p$。∎

## 352. 原词响应律接回半层几何与同一旧刻度单

**定理 352.1（非退化原脉冲在完整原背景中的应用）。** 在同一完整原来源上，另已供应[本卷定义 324.1–324.4](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#324-只删除同一简单块内零重叠迹的完整候选)的完整 $B_*+\mathsf G_{\rm HC}$，这里尚不假设 $\sigma_{t_0}$。$B_*$ 分别取完整 $B$ 或另名完整 $\mathsf B_{\rm cl}$：前者要求每个所需原对象和实际联合的实际准备精确有限正生成，后者要求其闭正生成；两者均保留全部实际准备、零及次归一质量，不将数学闭包中的极限态增加为实际准备。

全部原单体、实际联合、旧输出、失败输出、标签与参考，所有中心、经典块、不等量子块、原不等正 $q$ 块权及一般原 $g^0\ne q$ 均保留。原 X 的含幺 Jordan／同一 $D$ 嵌入、原有序交叉零、乘积张成及每对实际准备的实际乘积，整个 AC、精确 $N_u$、Xs、全事件 R、实 Jordan 意义的 F、同实现实际细记录、分组／遗忘、零／失败／停止、具名同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应与并行历史，均取定义 324.1 的原量词；相同响应不识别设备、端口或记录。

$\mathsf G_{\rm HC}$ 严格取 (324.3)：只在原选中对象 $\operatorname{rank}E_A>p_*$ 的全部有序 primitive 对、含全部实际联合中的纠缠 primitive 上要求零／半重叠的整输出支持；规范谱迹为零只要求于半重叠和跨中心对。它保留跨中心零层迹，不补回同块零层迹，也不预设 LU、导子、SC、协变、输出理想保持或单位曲率。原菜单、$\mathcal K_A$、实际 $J_0=P^{\otimes2}$ 及先于 $D$ 固定的同一 $t_0=(e_0,p_0,r_0)$ 均按 (324.4) 保持。

若其中一个原对象确已供应定义 350.1 的一个原脉冲对 $(e,R)$，在该对象的整个原输出上满足同一旧 $D$ 的 (350.2)，且 $P_e\ne0$，则同一原共同尺度为一；全部原对象、全部输入满足

$$
[D_a,D_b]=-[L_a,L_b],\qquad
D_c^2=-P_c/4\quad(c^2=c),
\tag{352.1}
$$

并且那张预先固定的同一原 $\sigma_{t_0}$ 成立。原脉冲效果 $e$ 可以高秩、可以不在选中测试域，不需等于 $e_0$ 或任何原指针 primitive；不要求原脉冲的秩为一，也不由数学支持角供应替代脉冲。

证明。先直接复用[本卷定理 327.1](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#327-全部原对象的无标定桥与所有被删迹式)：完整 $B_*+\mathsf G_{\rm HC}$ 在尚未使用 sigma 时，已经给全部原对象上的 I、SC、导子律、原 $q$ 斜伴随，以及 $\mathsf G^0_{0h}$ 和 O/H；这包括未选中小对象、二阶块、全部经典中心和失败输出。这个原范围桥消费的是其完整实际联合、原同一 $D$ 嵌入及分离条件，不从一个局部脉冲补造这些条件。

再直接消费[框架卷定理 275.2](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#275-标定以前已经恢复全部原-i-与-sc)：精确背景按其原 Z 接口，闭背景按其原完整 $\mathsf Q$ 接口，得到全域 II 和唯一共同 $\kappa\ge0$，包含 $\kappa=0$ 时全部 $D=0$ 的分支。按 [C123 引理 63.2 的 (63.6)](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#63-不作标定时的全网尺度二分) 及该同一全网尺度，对原任意秩幂等效果有 $D_e^2=-\kappa P_e/4$：非经典活动块用 (63.6)，经典块上 $D_e=P_e=0$，零分支亦成立。

另一方面，定理 351.1 只用这一个原脉冲的实偶／奇响应律，给同一个原 $D_e^2=-P_e/4$。相减得 $(\kappa-1)P_e=0$。取原响应空间中任一 $0\ne x\in\operatorname{im}P_e$，即有 $(\kappa-1)x=0$，故 $\kappa=1$，同时排除全零分支。这里的 $x$ 只用于数学非退化判断，不新增实际准备、读口或控制；定理 351.1 的条件秩二子代数 (351.2) 不参与这个尺度推论。

[框架卷定理 276.1](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#276-一张原半角标签恰好固定原单位尺度) 及[本卷 (328.3)](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#328-同一预选-sigma-的候选恒等等价) 对原来那张 $t_0$ 给 $W_{e_0}(p_0)=w_0/4>0$、$q_{J_0}(D_{p_0}e_0,r_0)=0$、$W_{e_0}(2D_{e_0}p_0)=\kappa w_0/4$。故 $\kappa=1$ 正好使同一原 (324.4) 成立；没有看 $D$ 输出后重选 $t_0$，没有重标 $D,q,W$ 或任一原返回数。到这里才已取得完整 $\mathsf C_{\rm HC}(B_*)$，并消费本卷定理 328.1 的单位曲率及既有候选等价，得到 (352.1)。这是实有限词条件在已发表全网尺度桥上的应用，不另立共同尺度或候选等价定理。

若此外已采用原矩阵坐标且原词确为投影相位门，则其 Heisenberg 方向为 $R=\exp(-2\vartheta\delta_e)$，$\delta_ab=\mathrm i[a,b]/2$。在 $e$ 与 $I-e$ 的两个对角块上 $R$ 为恒等，在两个非对角矩形块上分别乘 $e^{\mp\mathrm i\vartheta}$；成熟二谱计算因而同时给

$$
\begin{aligned}
P_eb&=eb+be-2ebe,\\
(R+R^{-1})b&=2b-2(1-c_\vartheta)(eb+be-2ebe),\\
(R^{-1}-R)b&=2\mathrm i s_\vartheta[e,b]
=4s_\vartheta\delta_eb.
\end{aligned}
\tag{352.2}
$$

这对任意秩的 $e$ 作用于完整输出。因此偶部在该已付采用中成立，原奇部还识别该原脉冲上 $D_e=\delta_e$ 的有符号方向。原 $\sigma$ 自身只固定平方尺度，不单独识别相对于已命名原门的正负。一个脉冲上的奇部不因此供应所有其他原门的独立有符号校准、全域内部生成元绑定或物理时钟。这个矩阵核对不是定理 351.1 的前件，亦不是复数来源证明。

完整消费者现在直接复用[本卷定理 329.1](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#329-复量子原过程具名返回及全部历史)，其来源为框架卷 315.1–316.1。在同一原 $D$ 确定取向的复坐标中，原乘法为 $a\cdot b=a\circ b-\mathrm iD_ab$；全部中心和经典块保留，没有跨中心相干。对每个原准备 $\alpha$，其 $g_A^0$-Riesz 向量 $x_\alpha$、原双对偶运输 $\mathcal B_A$ 及每个原事件 $f:A\to B$ 给

$$
\begin{gathered}
\rho_\alpha=\mathcal B_Ax_\alpha\ge0,\qquad
\alpha(y)=g_A^0(x_\alpha,y)
=q_A(\widehat x_\alpha,y)=\tau_A(\rho_\alpha y),\\
\widehat x_\alpha=\mathcal W_A^{-1}\mathcal B_Ax_\alpha,\qquad
\mathcal W_A(x)_s=w_{A,s}x_s,\qquad
\tau_A(\rho_\alpha)=\alpha(u_A),\\
\Phi_f=\mathcal B_BT_f^{\dagger_0}\mathcal B_A^{-1},
\qquad T_f:E_B\to E_A.
\end{gathered}
\tag{352.3}
$$

这里 $y$ 覆盖整个原响应空间，含同一旧 $D_ab$；$\dagger_0$ 是原 $g^0$ 伴随，$\mathcal B_A$ 不是背景 $B_*$ 或原 $q_A$。不以 $q_A(x_\alpha,y)$ 代替一般原评价。零及次归一质量不除去，闭背景里的极限态不变为实际准备。全部原实际联合保留全部中心对，成为普通复张量，全部原相关输入及参考保留；不要求原联合 $q$ 或 $\mathcal B$ 因子化。

所有原事件及原参考执行为 CP/TNI、原完整测试 TP；整个 AC／精确 $N_u$／Xs 和原合法连线供应的所选完整有限平方根词给 $\sqrt e\rho\sqrt e$，并保留每个完整失败输出。原 F 给同实现实际细记录及其分组／遗忘，不从数学 Kraus 指标补造记录；具名两侧支持返回及其原同数反向资料保留原 $q_\ell>0$，不归一成一。对每份原准备、每条原合法有限历史 $h=(f_1:A_0\to A_1,\ldots,f_m:A_{m-1}\to A_m)$ 和末端原效果 $w$，既有消费者给

$$
\alpha(T_{f_1}\cdots T_{f_m}w)
=\tau_{A_m}\!\left(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{352.4}
$$

原自适应逐实际记录分支，原并行只用原实际联合与相关输入，失败／返回／停止用原箭头，条件概率只在原分母正时取比值。以上结论只在完整 $B_*+\mathsf G_{\rm HC}$ 与确已供应的同一 $D$ 实响应律全部成立时消费，不以一处局部转动代替其前件。实际来源供应、物理时间／能量／作用量、独立支的共同仪器和旧同效果设备完整输出，仍逐项保持本卷定义 329.2 的条件；这里既无全局公理数／最小性结论，亦无完整量子起源完成结论。∎

**定义 352.2（单生成元与整体相容的不同义务）。** 若未给定定理 352.1 的完整背景，定理 351.1 只涉及 $D_e$，不能推出全域 SC、II、Jacobi 或两不同输入的曲率。原生配平续卷[命题 100.3](AURIC_C128_NATIVE_CUT_BALANCE_CONTINUATION.md#100-配平自行恢复单位尺度)的同一个八实维 spin 因子已具有全部原子上的正交 $J_p$、所有 $D_a$ 导子、SC 及单生成元平方，却违反 Jacobi 和混合曲率；不重造该例，也不把它当原有限门来源。故“每处能画转动平面”与“全部原联合共享量子动力对应”是不同条件。

实际后读切口也不因改写有限响应律而变为 primitive。在 [native III 定义 151.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的记录零对象中，原 $Q=n_1$ 在 $21,21,13$ 三个字面块内的秩分别为 $8,8,5$：前两个自由前缀为六位，无相邻且首位占据后余四位有八种；第三个为五位，余三位有五种。原 $Q$ 是这三个原块上的整个幂等效果，$P_Q$ 保留其全部横向矩形输出。定理 351.1 若适用于该原 $Q$，使用的就是原 $D_Q$；数学支持内的一个 $p$ 不能代替它。

## 353. 同一原端点指数仍容许的整数绕圈

**定义 353.1（保持全部非 D 数据的比较域）。** 以下反事实只在已经采用原矩阵和原 Born 过程的来源域中构造：所声称保留的每个原对象、输出和实际联合均已给出同一原过程的有限复矩阵直和表示，原准备及所有原过程／历史评价在此表示中已有实现；在需保持关系的实际接口上，原嵌入也已保持标准 $\delta$。这是一项明确的全域采用条件，比 [假设 319.2 的单读前切口采用](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#319-同一原有向关系的字面端点标定问题) 更强，不能由后者推出。若仅有该单切口采用，以下只给那个切口的比较，不声称已构造完整原来源的延拓。

在这一固定来源域上保留同一 $\Omega$ 的全部非 $D$ 数据：唯一 ready、十一地址前读词、七地址合法后读词、全部原准备及次归一质量、实际联合及相关参考、完整原事件和输出、$M_i$ 与全部 $1024$ 旧标签（含零投影）、每个失败／零支、细记录／分组／遗忘、原返回数、内部 Hamiltonian／路径核、过去、记录和所有原合法未来。没有新增操作或制备。

在这样固定的非 $D$ 过程 reduct 上，不同模型成员从一开始分别赋予

$$
D^{[m]}_ab=c_m\delta_ab,\qquad
c_m=1+\frac{10m}{3},\qquad
\delta_ab=\frac{\mathrm i}{2}[a,b],\qquad m\in\mathbb Z.
\tag{353.1}
$$

每个成员内部的 $D^{[m]}$ 此后固定。在所有已采用的直和块和实际联合对象上使用同一个 $c_m$；保留原有的同一嵌入、设备和合法性。若固定来源已给完整 tagged-CP 背景，这正是 [C123 定理 33.2、42.2](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#33-完整满足族及准确的删除范围) 的既有尺度族之特定子族。若来源只供应 native 的较小实际菜单，则只保留那个原菜单，不从完整满足族借来额外器件、所有密度准备或参考。以下没有改变原内部生成元来重新生成一套历史。

**定理 353.2（全部原投影相位端点的绕圈别名）。** 对定义 353.1 中的每个原地址、每个合法整词共轭及其原所在对象，均有

$$
\exp(-2\vartheta D^{[m]}_{\mathcal P_j})
=\exp(-2\vartheta\delta_{\mathcal P_j})
=\left[b\mapsto K_j^*bK_j\right],
\qquad K_j=\zeta[I+(\zeta-1)\mathcal P_j],\quad
\zeta=e^{\mathrm i\vartheta}.
\tag{353.2}
$$

各合法整词的共轭版本也在完整原输出上成立。这些成员共享全部原非 $D$ 端点和实际历史，但 $m\ne0$ 时不满足关于同一原 $D$ 的 (350.2) 奇部、§319 的同一 $D$ 校准或单位平方尺度。它们的曲率残差为

$$
[L_a,L_b]+[D^{[m]}_a,D^{[m]}_b]
=(1-c_m^2)[L_a,L_b].
\tag{353.3}
$$

特别地，$m=1$ 给 $c_1=13/3$、$1-c_1^2=-160/9$。

证明。对任意秩投影 $P$ 和任意 Hermitian $b$，矩阵指数的成熟共轭恒等式给

$$
\exp(-2\vartheta c_m\delta_P)b
=e^{-\mathrm i\vartheta c_mP}b\,e^{\mathrm i\vartheta c_mP}.
\tag{353.4}
$$

$\vartheta c_m=\vartheta+2\pi m$，而 $P^2=P$，所以两个矩阵指数分别就是 $e^{\mp\mathrm i\vartheta P}$。$K_j$ 的共同标量相位在共轭中相消，得到 (353.2)，包括全部阻塞和边界分量。合法原词给出的酉共轭仍将投影变为投影，故同一证明涵盖它们，而不需追加新门。合法后读字在原记录块上的限制也仍是同一投影相位的限制。这是整输出等式，不只某个概率相同。

标准交换子满足 $[\delta_a,\delta_b]=-[L_a,L_b]$，故 (353.3) 直接是已有尺度族的残差，所列有理数由 $1-169/9=-160/9$ 得。每个 $D^{[m]}_a$ 仍为守恒 $a$ 的 Jordan 导子并对原迹型比较斜伴随，但 $D^{[m]2}_e=-c_m^2P_e/4$，非零横向切口上不能满足 (351.1)。原端点的 $R^{-1}-R$ 仍为 $4s_\vartheta\delta_e$，因此 (350.2) 奇部在该切口恰要求 $c_m=1$。整数族中只有 $m=0$ 满足；偶部则全部相同。

在定义 353.1 的已采用矩阵过程 reduct 上，$\mathsf G_{\rm HC}$ 的整输出支持及零迹式对原 $D$ 都是齐次线性条件。每个 $D^{[m]}=c_m\delta$ 在所有 primitive 对上的输出均留在输入支持内且规范迹为零，故全部成员保留该 $\mathsf G_{\rm HC}$，实际上也保留较强的 $\mathsf G^0_{0h}$。若这个原来源还具备完整 $B_*$，则原 X 的同一嵌入保持及交叉零也因统一 $c_m$ 保持；既有 C123 定理 42.2 的全背景尺度族遂给 $B_*+\mathsf G_{\rm HC}$ 内的这些成员。未具备完整 $B_*$ 的单切口不能借此获得它，来源范围仍严格取定义 353.1。

在这项完整背景成立时，定理 327.1 及框架卷定理 275.2 给该族的共同尺度 $\kappa=c_m^2$；[共同框架续卷定理 276.1](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#276-一张原半角标签恰好固定原单位尺度) 在同一原 $t_0$ 上给 $\mathscr P_{t_0}=(1-c_m^2)w_0/4$，$w_0>0$。整数族中 $c_m^2=1$ 当且仅当 $m=0$。所以仅附加同一 $D$ 的指数端点等式，即使保留完整 $B_*+\mathsf G_{\rm HC}$，仍不强制单位尺度；$m\ne0$ 的成员失败于同一原 $\sigma_{t_0}$、C123 的 S、精确三元曲率及任一非零横向原脉冲的 (350.2) 奇部。它们不是 $\mathsf C_{\rm HC}(B_*)$ 或定理 352.1 全部前件的反模型。若还要求旧 $D$ 与原内部 Hamiltonian 的无穷小响应相等，它们同样失败于该绑定，不能宣称保留它。

所有非 $D$ 数据从定义起没有改变，故原实际联合、参考、原过程概率、全部失败、记录和每条合法有限历史逐项相同。这不是在一个固定世界中重标 $D$；也没有把不同请求的历史相互识别。额外等式 $R=\exp(-2\vartheta D_e)$ 本身不能消除此族，正是比完全不含 $D$ 的端点歧义更强的缺口。∎

**定义 353.3（主对数比较的限定范围）。** 在这个特定标量子族内，$|c_m|$ 唯一最小值为 $c_0=1$，因为 $m\ge1$ 时 $c_m\ge13/3$，$m\le-1$ 时 $c_m\le-7/3$。在非零横向空间上 $\|-2\vartheta D_e^{[m]}\|_q=\vartheta|c_m|$；要求其谱落在主对数带 $|\operatorname{Im}z|<\pi$ 也只留下 $m=0$。主对数的存在唯一性是成熟矩阵函数结果；这里没有证明原 $D$ 必须等于最小范数或主支选择，没有分类所有可能对数，也没有供应连续物理时钟、可中断脉冲或新控制。

## 354. 原 ready 上两份字面终端请求的有符号分离

**定理 354.1（地址 1 的实际原词见证）。** 在定义 353.1 的原矩阵／Born 采用中，只用唯一原 ready、原地址 $0,1$ 及原旧事件 $A=\{b_1=1\}$，便有非零的同一 $D$ 校准检验。令

$$
\begin{gathered}
x=\varphi^{-1},\quad x+x^2=1,\quad
r=\{3,7\},\quad r'=\{1,3,7\},\\
Q=\mathcal P_0=n_1,\qquad A_1=K_1^*QK_1,\qquad
\alpha_1(b)=\langle K_1e_r,bK_1e_r\rangle.
\end{gathered}
\tag{354.1}
$$

则

$$
C:=\alpha_1(\delta_QA_1)
=-2x^6(1-c_\vartheta)s_\vartheta\ne0.
\tag{354.2}
$$

取两个实际终端请求

$$
p_+=P_{\mathsf T(1\,0\,1)}(A),\qquad
p_-=P_{\mathsf T(1\,0^9\,1)}(A),
\tag{354.3}
$$

其中 $0^9$ 是九次原正向地址 $0$，则

$$
p_--p_+=4s_\vartheta C,
\qquad
\alpha_1(D_Q^{[m]}A_1)-\frac{p_--p_+}{4s_\vartheta}
=(c_m-1)C.
\tag{354.4}
$$

因此这个固定原准备、原第一输入 $Q$、原后续效果 $A_1$ 的单一校准实例，排除所有 $m\ne0$ 的绕圈别名。它没有单凭两个概率确定任意原双线性 $D$。

证明。[native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#1-原来源完整端点与不变的实际读取)给同一 ready $e_r$。在 $r$ 处，地址 $1$ 的两邻位均为零，故它的完整活动分量恰为 $(r,r')$；原其余分量也全部保留。按这两个原基向量的顺序，

$$
\left.\mathcal P_1\right|_{r,r'}=
\begin{pmatrix}x&x\sqrt x\\x\sqrt x&x^2\end{pmatrix},
\qquad
\left.Q\right|_{r,r'}=\begin{pmatrix}0&0\\0&1\end{pmatrix}.
\tag{354.5}
$$

置 $t=\zeta-1$，并去掉在所有评价中相消的共同相位，写

$$
V=\left.\zeta^{-1}K_1\right|_{r,r'}=
\begin{pmatrix}a&b\\b&d\end{pmatrix},\qquad
a=1+xt,\quad b=x\sqrt x\,t,\quad d=1+x^2t.
\tag{354.6}
$$

原 $K_1e_r$ 在这块内是 $\zeta(a,b)^{\mathsf T}$，$A_1=V^*QV$ 的 $(1,2)$ 元为 $\bar b d$。由

$$
\delta_QA_1=
\frac12\begin{pmatrix}0&-\mathrm i\bar b d\\
\mathrm i\bar d b&0\end{pmatrix}
\tag{354.7}
$$

可得

$$
\begin{aligned}
C&=|b|^2\operatorname{Im}(\bar a d),\\
|b|^2&=2x^3(1-c_\vartheta),\\
\operatorname{Im}(\bar a d)&=(x^2-x)s_\vartheta
=-x^3s_\vartheta.
\end{aligned}
\tag{354.8}
$$

最后一式用 $1-x=x^2$。$x>0$、$1-c_\vartheta>0$、$s_\vartheta>0$，故 (354.2) 严格非零。这个二点矩阵是原状态在原不变活动分量上的计算，不把它另造为实际二阶对象；原 $Q$ 在全载体上仍为高秩投影。

按原词顺序 $K_{gh}=K_hK_g$，两个概率分别为

$$
p_+=\alpha_1(K_0^*A_1K_0),\qquad
p_-=\alpha_1(K_0A_1K_0^*).
\tag{354.9}
$$

$K_0^9=K_0^{-1}$ 只用于这些端点，未反演原内部路径。成熟二谱展开，即已发表 (320.2) 的原参数移位恒等式，给

$$
K_0A_1K_0^*-K_0^*A_1K_0
=2\mathrm i s_\vartheta[Q,A_1]
=4s_\vartheta\delta_QA_1.
\tag{354.10}
$$

评价得 (354.4) 的第一式；$D_Q^{[m]}=c_m\delta_Q$ 给第二式。两个请求分别是三个和十一个原门调用后接同一旧终端；没有条件化、额外参考、新标签、连续角、重置或追加准备。取 $m=1$，残差明确为 $\tfrac{10}{3}C\ne0$。

也可直接按原矩阵乘法核对符号：在该活动分量上去掉共同相位，两个末态的第二坐标分别是 $b(a+\zeta d)$ 和 $b(a+\zeta^{-1}d)$，所以

$$
p_-=|b|^2|a+\zeta^{-1}d|^2,\qquad
p_+=|b|^2|a+\zeta d|^2,\qquad
p_--p_+=4s_\vartheta|b|^2\operatorname{Im}(\bar a d).
\tag{354.11}
$$

这一直接计算与 (354.9)–(354.10) 的 Heisenberg 顺序相同。

若只保留没有 Born 采用的原端点裸类，此证明只给 (354.2) 的矩阵评价，不能把 (354.9) 的二次型直接认作原实际概率。因此这个原词分离检验不充当无 Born 的量子起源证明；无复／Born 前件的条件推导是定理 351.1，二者的来源层次分开。∎

## 355. 原内部生成元、既有结果及完整来源的未接接口

**定义 355.1（内部实响应与旧 D 的类型桥）。** [V63 定义 10.1、定理 10.2](AURIC_NATIVE_COMPLEX_STRUCTURE_STABLE_ASSEMBLY_AND_FINITE_BORN_READOUT_CERTIFICATES_V63.md#10-原八十九配置的离散端点关系强制实际内部守恒)已从原黄金块、十次幂、端点正交、相邻编织和原根钟，推出实际 $L_q:V_q\to V_q$ 的反自伴、平方 $-I$ 及共同平坦运输。这里直接复用，不用任意矩阵对数的存在替代它的实际生成元，也不以绕圈修改根钟。

这些 $L_q$ 作用在原二维实纤维，$A_j$ 作用在其全实直和；旧 $D$ 则是响应商 $E\times E\to E$。二者类型不同。若已有原保响应的实线性单射表示 $\iota$，其算子值像在原内部 Heisenberg 族下不变，令该族的生成元为 $\mathcal G_j$，则还需关于同一旧 $D$ 的等式

$$
\iota(D_{e_j}b)=-\frac1{2\vartheta}\mathcal G_j(\iota b)
\qquad(b\in E).
\tag{355.1}
$$

式中 $e_j$ 必须是同一原门方向所对应的原效果，表示、下降和尺度都需原来源供应。在已采用复坐标、$\iota(e_j)=\mathcal P_j$、原 $H_j=-\vartheta(I+\mathcal P_j)$ 的情形，$\mathcal G_j(B)=\mathrm i[H_j,B]=-2\vartheta\delta_{\mathcal P_j}B$；所以 (355.1) 正是缺少的旧 $D$—内部作用绑定，不能从 $L_q^2=-I$ 或端点相等自动取得。§353 的成员保持原 $L_q,H_j$ 及内部历史不变，$m\ne0$ 时失败的是 (355.1)，并未反驳 V63 的刚性结论。

**定义 355.2（完整目标的来源义务）。** (350.2) 是原实商、原幂等效果与原有限词之间的新候选关系，尚未从裸来源推出。完整目标还要求在同一 $\Omega$ 中给出原全语境商及原 $q/L/\circ$ 的来源、全部原对象上的适用关系、原精确或闭准备生成及质量、全部实际联合和相关参考的共同实现、同一 $D$ 的跨对象保持与混合曲率、原记录和每个旧事件的完整输出、失败及合法历史。若走定理 352.1 的路线，就必须实际供应其完整 $B_*+\mathsf G_{\rm HC}$，以及一个非零横向原脉冲在完整输出上的同一旧 $D$ 实偶／奇律；不以一处局部转动、数学不变子代数或 (353.2) 代替。该条件应用已经从这些前件推出同一预选 $\sigma_{t_0}$，不再额外索取一张 sigma；但从原裸来源取得这些前件仍未证成。

原生有限词的稠密轨道、完整旧标签的线性张成以及现成量子消费者都按 [§§319–323](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#319-同一原有向关系的字面端点标定问题) 的条件复用；本增补不提供新解码器、有限词查找算法、统一长度、含噪条件数或认证资源界。

本卷 [§§344–349](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#344-原七地址第一槽与分别保留的三个尾块) 已给这个记录零切口的条件决定和延拓结论：在定义 344.1–344.3 的同一已识别字面载体、原实双线性 $D$ 及跨中心整输出零 $\mathsf O_\times$ 下，定理 345.1 使全部原 $A_g$ 第一槽和全部旧标签第二槽上的整输出决定全域 $D$；定理 345.2 还精确要求限制数据满足 (345.5)，才有该结构域内的唯一扩张。定理 346.1 给完整正交零或全域自守恒／导子律这两种充分入口；定理 347.3 只有另得假设 347.1 的原响应采用及其所需的 (347.3) 有符号来源等式，才把同一原 $D$ 识别为原既定矩阵取向的 $\delta$；这些等式可按该定理选取有限个原张成／分离数据。这些结论与 §321 的较弱结构歧义具有不同前件，不能再把该弱例当作强结构域内的不唯一证明。

本节一个原 $e$ 上的 (350.2) 只约束 $D_e$，未供应上述全域 $\mathsf O_\times$、全域 SC／导子律、全部同步 $A_g$ 的旧 $D$ 校准或全部原 $\beta_a$ 的来源采用；也不因此绑定每个原第一输入。定理 352.1 的全网应用直接消费已发表 §§324–332 及既有尺度桥，不以 §§344–349 为证明前件，更不从它们取得裸来源供应。

物理时钟、具体 Hamiltonian／能量和共同作用量／$\hbar$、实际连续器件与可靠控制的资源尺度、任意独立成功支的共同仪器及合法连线、旧同效果设备的完整输出校准，分别保持共同框架续卷定义 316.2 的原义务。数学 $\vartheta$、$1/2$ 或一个主对数不供应这些物理尺度。唯一 $\Omega$ 的完整量子起源目标因此仍未由本条件桥闭合。

**定义 355.3（数学归属与文献适用范围）。** 下列一般结果是成熟中间工具，文献状态为 $\texttt{literature-attested}$；原来源特定的综合为 $\texttt{repo-derived}$，不主张一般理论新发现、全球原创、独立公理最少或经验本体成立。

| 来源 | 准确使用及保留条件 |
| --- | --- |
| [C123 母卷 §§1、33、42、63](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)；共同框架续卷 §§264–277、293、311–318；[本卷已发表 §§324–332](https://github.com/the-omega-institute/trureturing/blob/ae4d78c26e5c5167fa470849ca0c95842fc7b61f/docs/develop/theory/AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#324-只删除同一简单块内零重叠迹的完整候选) | 原有向响应的类型、既有完整尺度族；定理 327.1 在无 sigma 时把完整 $B_*+\mathsf G_{\rm HC}$ 接到全域 I+SC，再由框架卷 275.2 给共同尺度；定理 352.1 内用一个非退化原脉冲令该尺度为一，最后才消费原 328.1–329.1。复用原整支持、归一化与全部量子消费者，不另立同义等价或分类，不从支持角或原 sigma 读出原门的有符号绑定。 |
| 本卷 §§319–323；native XI 定义 1.1–1.4；native III 定义 151.1 | 原 ready、全部门／标签／合法词、已付矩阵／Born 采用、端点顺序及记录块；§354 使用实际有限原词，不要求密度提供新准备。 |
| 本卷 §§344–349 | 已识别记录零载体在跨中心整输出零等准确结构入口下的条件决定、(345.5) 下的唯一扩张及另需 (347.3) 的同一旧 $D$ 来源识别；一个原脉冲不供应这些全域前件，也不替换其带标签第二槽。 |
| 原生配平续卷 §§89–90、100.3、107–110；共同框架续卷 §§222–242、264–277 | 既有余切、有限比较、四分之一转动与三实维角，以及逐点平方不足以给全曲率的边界；不是本增补新增的几何分类或有限框架。 |
| V63 §10；[Yue–Thunberg–Gonçalves, arXiv:1605.06973v1](https://arxiv.org/pdf/1605.06973v1)，§II.A Theorems 1–3、式 (2)–(4) | 前者是原内部生成元的既有供应；后者陈述主对数带及一般对数的 $2\pi\mathrm i$ 分支。§353 将既有尺度族限制为原 $3\pi/5$ 门端点的整数别名；不是新对数分类。 |
| [Barnum–Hilgert, arXiv:1904.03753v1](https://arxiv.org/html/1904.03753v1)，§§4、9–10 及其 Faraut–Korányi 引文 | EJA 谱／Peirce／spin 几何和动力对应背景；不由该文的强对称性结论倒供当前原来源，也不从三实维截面推出全部复矩阵。 |
| [Niestegge, arXiv:1402.0158v2](https://arxiv.org/html/1402.0158v2#S5)，§5 Definition 1、Theorem 1、Corollary 1；[Baez, arXiv:2006.14741v5](https://arxiv.org/html/2006.14741v5)，§§4–5 | 动力对应分别需要自守恒和混合乘法相容；后文的“逆温为虚时间”解释不提供本来源的温度、状态供应或旧 $D$ 绑定。这里不重复其从完整动力对应恢复复代数的已知定理。 |
| [Schuld 等, arXiv:1811.11184v1](https://arxiv.org/html/1811.11184v1)，§III.A Theorem 1、式 (12)–(14) | 成熟二谱参数移位；(354.10) 的一般恒等式已在 (320.2) 使用。新增的是本原 ready 和两份完整字面请求的严格非零值及其对整数别名的残差，不是新参数移位定理。 |

这里的实质联系为：先把同一旧 $D$ 的独立奇部等式与原实偶部分开，在原十个整数端点上取得局部守恒导子和条件三实维截面；在完整 $B_*+\mathsf G_{\rm HC}$ 已供应时，直接用已发表定理 327.1 进入原共同尺度桥，再把这份非退化原词条件接回同一预选旧刻度单与完整消费者；不把这个应用另报为新共同尺度定理。另一方面，既有尺度族的整数子族即使指数等于所有原投影相位端点，也会在 $1\,0\,1$ 与 $1\,0^9\,1$ 的原有符号绑定中留下 (354.4) 的非零残差。这保留了来源采用与旧关系绑定的两个不同缺口，没有把二者改名为量子起源完成。

## 追加锚 C128355（本行以下为增补区）

## 356. 两个保留记录上的原词校准与同一旧关系

**假设 356.1（同一完整背景中的双切口采用）。** 固定定义 324.1、333.1 的同一原 $\Omega$、同一整份非 $D$ 数据和事先给定的实双线性关系族 $D^A$。分别取完整 $B+\mathsf G_{\rm HQ}$，或另名完整 $\mathsf B_{\rm cl}+\mathsf G_{\rm HQ}$，记作 $B_*+\mathsf G_{\rm HQ}$；不输入 $\sigma_{t_0}$ 或单位尺度。保留这些定义的全部量词：原全语境响应商、P/G 固定的 $q/L/\circ$、全部原准备及零／次归一质量、精确有限正生成或各自的闭正生成、全部实际联合及相关输入、原乘积准备、整个 AC、精确 $N_u$、含幺 Jordan／同一 $D$ 的 X/Xs 嵌入及原有序交叉零与乘积张成、全事件实际参考 R、同实现 F 的细记录／分组／遗忘、每个完整失败输出、具名同数两侧支持返回及其同数反向资料、每条原合法有限顺序／自适应／并行历史。闭包中的数学极限态不增加为实际准备，数学支持角不增加为原对象。

采用 [native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#1-原来源完整端点与不变的实际读取) 的唯一原 ready $e_{\rm r}=e_{\{3,7\}}$、原门 $K_j$、$\chi_a=K_ae_{\rm r}$、调用顺序 $K_{aj}=K_jK_a$、保留读者 $M_i$ 和全部旧终端 $N_w$。令 $\mathcal K_i=M_i\mathcal K$，按 [native III 定义 151.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的固定原复坐标与字面尾序，记

$$
\begin{gathered}
S_0=(000,010,100),\qquad S_1=(001,101),\\
E_0=H_{21}(\mathbb C)_{000}\oplus H_{21}(\mathbb C)_{010}\oplus H_{13}(\mathbb C)_{100},\qquad
E_1=H_{21}(\mathbb C)_{001}\oplus H_{13}(\mathbb C)_{101}.
\end{gathered}
\tag{356.1}
$$

另须供应同一完整背景内的两个原对象 $A_0,A_1$ 及保原响应的含幺 Jordan 同构 $\Theta_i:E_{A_i}\to E_i$，把原记录 $i$ 后的准备、原七地址未来及旧标签识别为上述字面对象。坐标及其原生复取向固定，不按 $D$ 的输出转置或重选。传送的是同一旧关系

$$
D^i(X,Y)=\Theta_i\!\left(D^{A_i}(\Theta_i^{-1}X,\Theta_i^{-1}Y)\right),
\qquad X,Y\in E_i.
\tag{356.2}
$$

这项原对象识别不是从 $M_i$ 压缩或矩阵代数的存在推出。对两个切口都采用原准备／保留读者／Born 接口：对全部原 $a\in\mathsf W_{11}$、$h\in\mathsf W_7$、$w\in\Omega_{10}$，原分支泛函及原实际联合概率为

$$
\begin{aligned}
\alpha_{a,i}(Y)
&=\langle M_i\chi_a,YM_i\chi_a\rangle,
&\alpha_{a,i}(I_i)&=\|M_i\chi_a\|^2,\\
P_{\mathsf R(a,h)}(i,w)
&=\langle K_hM_i\chi_a,N_wK_hM_i\chi_a\rangle.
\end{aligned}
\tag{356.3}
$$

$\alpha_{a,i}$ 是已采用的原准备评价，未按记录质量归一；零支评价恒为零。原 $g^0$-Riesz 向量 $x_{a,i}$ 与原 $q$-Riesz 向量 $\widehat x_{a,i}$ 分别满足 $\alpha_{a,i}(Y)=g^0_{A_i}(x_{a,i},\Theta_i^{-1}Y)=q_{A_i}(\widehat x_{a,i},\Theta_i^{-1}Y)$，不以 $q_{A_i}(x_{a,i},\Theta_i^{-1}Y)$ 代替。所有 $2048$ 个原形式 $(i,w)$、零投影标签、合法代码补空间、原档案、失败与历史均保留。(356.3) 是来源采用前件，既不由下面两个概率差推出，也不把全射线数学域变成实际准备菜单。

**定义 356.2（恰好两条有符号旧关系等式）。** 令 $x=\varphi^{-1}$、$x+x^2=1$、$\vartheta=3\pi/5$、$s_\vartheta=\sin\vartheta>0$、$\zeta=e^{\mathrm i\vartheta}$，并保持旧事件 $A=\{b_1=1\}$。在 $E_i$ 内置 $Q_i=n_1|_{\mathcal K_i}$、$B_i=(K_1|_{\mathcal K_i})^*Q_i(K_1|_{\mathcal K_i})$、$\delta_i(X,Y)=\mathrm i[X,Y]/2$。对恰好两个原字 $a=1,7891$，定义关系 $\mathsf C_a$ 为

$$
\boxed{\quad
\sum_{i=0}^1\alpha_{a,i}\!\left(D^i(Q_i,B_i)\right)
=\frac{\displaystyle\sum_{i=0}^1P_{\mathsf R(a\,0^9,1)}(i,A)
-\displaystyle\sum_{i=0}^1P_{\mathsf R(a\,0,1)}(i,A)}{4s_\vartheta}.
\quad}
\tag{356.4}
$$

这里 $0^9$ 是九次原正向地址 $0$，$P(i,A)=\sum_{w\in A}P(i,w)$。四份程序仍各保留两个记录；求和只是同一程序旧联合律的分组。$D^i(Q_i,B_i)$ 是原实响应向量，不要求正，也不是新可调用事件或 $D$ 测量器。两条等式都约束 (356.2) 的同一旧 $D$，没有另选拟合关系。

**定理 356.3（双记录的条件全域校准）。** 在假设 356.1 的完整域内，

$$
\mathsf C_1\ \wedge\ \mathsf C_{7891}
\quad\Longleftrightarrow\quad
D^i(X,Y)=\frac{\mathrm i}{2}[X,Y]
\quad\bigl(i=0,1,\ X,Y\in E_i\bigr).
\tag{356.5}
$$

右式取固定原生取向，覆盖两个直和空间上的全部输入，包括跨尾输入；不是只确定 $Q_i$ 第一槽。此时原全网共同尺度为一，故同一预选 $t_0$ 的原 $\sigma_{t_0}$ 也成立。

证明。先消费定理 337.1 及框架卷定理 275.2 的既有分类与共同尺度：在已经固定的原生坐标中，

$$
D^i(X,Y)=\bigoplus_{t\in S_i}\lambda_{i,t}\delta(X_t,Y_t),
\qquad \lambda_{i,t}^2=\kappa\ge0,
\tag{356.6}
$$

且跨中心输出为零。$\kappa$ 来自这同一完整原关系网，不能从两个分别的局部模型拼接。

由 $K_0$ 与 $M_i$ 交换、$K_0^{10}=I$ 及既有二谱恒等式 (320.2)、(354.10)，有

$$
\begin{aligned}
P_{\mathsf R(a\,0^k,1)}(i,A)
&=\alpha_{a,i}\!\left((K_0|_{\mathcal K_i})^{*k}B_i(K_0|_{\mathcal K_i})^k\right),\\
K_0B_iK_0^*-K_0^*B_iK_0
&=4s_\vartheta\delta_i(Q_i,B_i).
\end{aligned}
\tag{356.7}
$$

第二行的 $K_0$ 均限制于 $\mathcal K_i$；第一行取 $k=1,9$。因此 (356.4) 的右端恰为 $\sum_i\alpha_{a,i}(\delta_i(Q_i,B_i))$，符号由九次地址 $0$ 项减一次项固定。

复用定理 354.1 的 ready 系数：$a=1$ 只占记录零的 $100$ 尾，记录一为零，且其原生 $\delta$ 评价为

$$
C=-2x^6(1-\cos\vartheta)s_\vartheta=-x^4s_\vartheta\ne0.
\tag{356.8}
$$

最后一个等号用 $\cos\vartheta=-x/2$ 与 $2+x=x^{-2}$。故 $\mathsf C_1$ 就是 $\lambda_{0,100}C=C$，给 $\lambda_{0,100}=1$，进而 $\kappa=1$。

为评价第二行，直接使用[原终端认证定理 15.1 的 (15.4)–(15.5)](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md#15-唯一-ready-源的实际-78-前缀与不可见方向)。以其振幅改记为 $\eta=\zeta(\zeta-1)x\sqrt x$、$d=\zeta[1+x(\zeta-1)]$、$g=\zeta[1+x^2(\zeta-1)]$，已有 $|\eta|^2=x$、$|d|^2=|g|^2=x^2$ 和
$\chi_{78}=\eta d e_{000}+\eta^2e_{010}+\zeta g e_{100}$；这里各 $e_t$ 的前六位同为 $001000$。原地址 $9$ 在 $000,100$ 上活动，在 $010$ 上阻塞且乘相位 $\zeta$，所以

$$
\chi_{789}=\eta d^2e_{000}+\zeta\eta^2e_{010}+\zeta gd e_{100}
+\eta^2d e_{001}+\zeta g\eta e_{101}.
\tag{356.9}
$$

地址 $1$ 在每个 $e_t$ 上具有定理 354.1 的同一个原活动对 $(e_t,e'_t)$，其中 $e'_t$ 仅加占位 $1$，故 $K_1e_t=de_t+\eta e'_t$。它不改变尾标，且每对的单位质量 $\delta$ 评价都是 (356.8) 的 $C$。令 $P_t$ 为原字面尾投影，则 $a=7891$ 的五个尾质量及其评价为

| 记录 $i$ | 原尾 $t$ | $\mu_{i,t}=\|P_t\chi_{7891}\|^2$ | $\alpha_{7891,i}(\delta_i(Q_i,B_i))$ 的该尾项 |
| --- | --- | --- | --- |
| $0$ | $000$ | $x^5$ | $x^5C$ |
| $0$ | $010$ | $x^2$ | $x^2C$ |
| $0$ | $100$ | $x^4$ | $x^4C$ |
| $1$ | $001$ | $x^4$ | $x^4C$ |
| $1$ | $101$ | $x^3$ | $x^3C$ |

全部 $\mu_{i,t}>0$，总和为一，两个记录质量分别为 $x^5+x^2+x^4=x$、$x^4+x^3=x^2$。这是同一相干原态的直和评价，不要求准备随机混合或调用跨尾算子。原 $K_9$ 始终在保留读者之前，未穿过读者。

现在 (356.6) 中五个系数均为 $\pm1$；$\mathsf C_{7891}$ 精确变为

$$
C\sum_{i,t}\mu_{i,t}\lambda_{i,t}=C\sum_{i,t}\mu_{i,t}=C,
\qquad
\sum_{i,t}\mu_{i,t}(1-\lambda_{i,t})=0.
\tag{356.10}
$$

每项非负且每个权重严格正，故五个 $\lambda_{i,t}$ 全为一；(356.6) 给全部 $E_i\times E_i$ 上的右式。反向只需在 (356.7) 中代入同一 $D^i=\delta_i$，便对这两个 $a$ 得 (356.4)。共同尺度为一后，框架卷定理 276.1 的既有公式 $\mathscr P_{t_0}=(1-\kappa)w_0/4$、$w_0>0$ 给同一原 $\sigma_{t_0}$，没有输入新标定单。

两个请求对的总概率事实上相同。沿定理 354.1 的 $a_0=1+x(\zeta-1)$、$b_0=x\sqrt x(\zeta-1)$、$h_0=1+x^2(\zeta-1)$，有 $a_0+\zeta h_0=\zeta$、$a_0+\zeta^{-1}h_0=x^2$、$|b_0|^2=x$。故对 $a=1$ 和 $7891$ 均有

$$
\left(\sum_iP_{\mathsf R(a\,0,1)}(i,A),\ \sum_iP_{\mathsf R(a\,0^9,1)}(i,A)\right)=(x,x^5).
\tag{356.11}
$$

两条校准的区别在旧 $D$ 左端的系数行 $(0,0,1,0,0)$ 与 $(x^5,x^2,x^4,x^4,x^3)$，不在右端数值。四份原程序分别含 $3,11,6,14$ 次原门调用，各接同一保留读者和旧终端；这只是原词长度，不给物理成本、最小性或全网独立性结论。∎

**定义 356.4（复用范围与来源界面）。** (356.5) 是 $\texttt{repo-derived}$ 的原来源特定条件应用；native III 151.1–151.2 已有两个字面代数与效果张成，原终端认证 15.1 已有 $78$ 振幅，定理 354.1 已有 ready 非零系数，定理 337.1 与框架卷 275.2、276.1 已有分类、共同尺度和 sigma 后果。二谱移位沿定义 355.3 所引 Schuld 等 §III.A Theorem 1 及本卷 (320.2) 复用；正权饱和只是证明中的有限非负和论证。新增对应是原 $7891$ 同时覆盖两个记录的五个严格正尾权，以及它与 ready 行共同校准固定旧关系的 (356.5)，不另立一般分类或参数移位结果。

若从[正交迹续卷定理 352.1](AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md#352-选中域自比较与原全域量子关系等价) 进入，须在同一完整 $B_*$ 中供应其整个 $\mathsf G_{0h}+\mathsf T_{\rm self}^{>}$；该定理给全域 I+SC，再由本卷定理 337.1 进入上述无 sigma 域。这个入口不供应 (356.1)–(356.3) 的原对象／Born 采用或 (356.4) 的旧 $D$ 等式。

单位尺度后的混合曲率、$D_e^2=-P_e/4$、半 Peirce 空间上原 $q$ 正交的 $J_e=2D_e$ 和数学二原子角的三实维无迹球截面，直接取框架卷定理 277.1、定义 277.2；这里只把两个已采用切口的取向校准为原生取向。其余对象仍取同一原 $D$ 决定的相容取向。三实维数学截面不是物理三空间或实际二阶设备；定理 338.1、339.1 的完整消费者仍消费同一整份原背景、实际联合、原响应映射及全部历史前件，不由两条标量等式单独重构原事件更新或全语境历史。

从原裸来源取得完整 $B_*$、几何前件、双切口识别与 (356.3)、同一旧 $D$ 的两条 (356.4)，仍是分别的来源前件。定义 339.2、355.2 的物理时间／能量／作用量、独立成功支的共同仪器、旧同效果设备的完整输出及全部原合法过程接口也保留各自前件；(356.5) 的条件等价不蕴含这些来源前件或物理接口的存在。

## 追加锚 C128355（本行以下为增补区）

## 357. 同源插入比较与原对象的联合采用候选

**定义 357.1（完整原域与不预设维数的入口）。** 对同一原 $\Omega$ 的一个固定有类型切口 $A$，取全部原准备、已发生的合法历史、参考和记录上下文的评价族 $\mathcal P_A$，以及全部仍合法的未来事件请求的实响应商 $E_A$。类型或合法性不同的请求不相减，未定义的请求不补零；取商只识别所有这些上下文上的相同响应，不识别原历史、设备或档案。下文暂省 $A$。假定原请求有共同总事件 $u$，每个 $a\in E$ 在原序中有界，即存在 $r\ge0$ 使 $-ru\le a\le ru$，并且

$$
\begin{gathered}
\bigl[\alpha(a)=0\ (\alpha\in\mathcal P)\bigr]\Longrightarrow a=0,\qquad
E_+=\{a:\alpha(a)\ge0\ (\alpha\in\mathcal P)\},\\
\alpha(u)=m_\alpha\in[0,\infty),\qquad
u\circ a=a,\qquad D(a,u)=0.
\end{gathered}
\tag{357.1}
$$

这里 $\circ$ 是给定的原实对称双线性乘法，$L_a b=a\circ b$；$D:E\times E\to E$ 是事先固定的字面旧实双线性关系。最后一个右单位式是所保留原背景已有的条款，不是导子律、SC 或取向校准。原 $q$ 若已供应，逐字保留；不以本节的来源比较替换它。没有有限维、EJA、谱分解、支持、LU、SC、理想保持、逆向交叉零或张量的前件。若某个来源尚未供应原 $\circ$、$D$、共同单位或上述有界性，本节不替它制造这些输入。

对完整目标，$\mathcal P$ 包含每个实际相关输入、零与次归一准备、每个记录／失败及每条原合法有限历史的上下文。此定义与 [C139 固定源卷定义 32.1](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md#32有限标记共轭关系下降与复型选择) 的全未来商相容，但不从那个商的定义推出乘法。该卷命题 32.1a 已证明保留 CountRead 的共同切口 $E_A$ 无穷维；本节允许这个维数，不将它改成有限采用仍未供应的说法。

**定义 357.2（同一来源的插入比较资料）。** 另给一个由原来源标签的有限形式比较配方组成的复向量空间 $V$。每个原上下文 $\alpha\in\mathcal P$ 有自己的标签 $\xi_\alpha\in V$；不同标签可以有相同可见像，原档案不因此合并。给定一个第一槽共轭线性的半正定 Hermitian 二元比较 $K:V\times V\to\mathbb C$，以及关于 $a$ 实线性、关于 $z$ 复线性的插入

$$
J_a:V\longrightarrow V\qquad(a\in E).
$$

$V$ 由全部 $J_{a_1}\cdots J_{a_n}\xi_\alpha$ 的有限复线性组合张成，$n=0$ 也在内。这里的复组合是比较配方的形式线性包，不宣称每个组合都是实际准备；$J_a$ 是比较插入的来源接口，不预称物理门、正分支或可调用 $D$ 测量器。来源须给出这些标签、比较和插入的同源解释，不能在看到所需算子答案后才把它们定义为合法操作。

要求同一单位、同一原读数和全配方的来源正性：

$$
\begin{aligned}
K(z,J_u w)&=K(z,w)&& (z,w\in V),\\
K(\xi_\alpha,J_a\xi_\alpha)&=\alpha(a)&& (\alpha\in\mathcal P,\ a\in E),\\
K(z,J_bz)&\ge0&& (z\in V,\ b\in E_+).
\end{aligned}
\tag{357.2}
$$

半正定性包括任意有限族的全部复系数 Gram 正性；最后一行也量化全部形式配方。只在各个原标签上非负，不是这一全配方条件；分别为每个准备任选一个正核，也不供应这份共同 $K$。第一行只要求单位在比较中为恒等，不先要求 $J_u=I_V$，从而允许零质量标签及整个零响应域。

**定义 357.3（一个联合采用候选）。** 在 (357.1)–(357.2) 的同一资料上，对每个原有序响应对 $(a,b)$ 要求

$$
\boxed{\mathsf R_{\rm ins}(a,b):\quad
K(J_a z,J_b w)
 =K(z,J_{a\circ b}w)-\mathrm iK(z,J_{D(a,b)}w)
 \quad(z,w\in V).}
\tag{357.3}
$$

这是一份原二元关系的比较相容式：同一比较的实对称来源与有向来源必须由同一对原输入给出，不能分别选择 Jordan 像、Born 态和另一个拟合关系。$-\mathrm i$ 的号相对于该 $K$ 的原标记方向固定；实正性单独不选择这个方向。复 Gram 可以在准确满足 [R5-009 §6.1](AURIC_R5_009_POSITIVE_RECIPES_SAME_SOURCE_BALANCE_AND_QUANTUM_GEOMETRY.md#61一个有序二元比较读出完整复关系) 或 [C140 定理 3.2](AURIC_C140_COMMON_SOURCE_THREE_PATH_BALANCE_AND_QUANTUM_GEOMETRY.md#3同一读数的三路配平唯一候选与完整分类) 的来源上复用，但它们不供应 (357.2) 的旧读口身份或 (357.3)。本候选明确输入这些新的来源关系，不称它们为裸来源的已证后果。

## 358. 从同一比较构造对象、Born 配对与有符号旧 D

**定理 358.1（无全局有限维前件的联合采用）。** 在定义 357.1–357.3 的全部前件下，存在由这份资料确定的最小复 Hilbert 空间 $H$、稠密像映射 $F:V\to H$ 和实线性单射 $\pi:E\to B(H)_{\rm sa}$，满足

$$
\begin{gathered}
\langle Fz,Fw\rangle=K(z,w),\qquad
\pi(a)Fz=F(J_a z),\qquad \pi(u)=I_H,\\
\pi(a\circ b)=\frac{\pi(a)\pi(b)+\pi(b)\pi(a)}2,\qquad
\pi(D(a,b))=\frac{\mathrm i}{2}[\pi(a),\pi(b)],\\
\alpha(a)=\langle F\xi_\alpha,\pi(a)F\xi_\alpha\rangle,\qquad
\|F\xi_\alpha\|^2=m_\alpha,\\
a\in E_+\quad\Longleftrightarrow\quad\pi(a)\ge0.
\end{gathered}
\tag{358.1}
$$

因此 $\pi$ 保持并反映原序、单位及全部原评价，识别的是同一旧 $D$ 的号和尺度；无需先给独立的对象同构、Born 密度或交换子绑定。$\pi$ 对原序单位范数等距。$E_{\mathbb C}=E+\mathrm iE$ 上的原式

$$
a\cdot b=a\circ b-\mathrm iD(a,b)
\tag{358.2}
$$

复双线性延拓后是结合的含幺 $*$-代数乘法，其忠实表示为 $\pi_{\mathbb C}(a+\mathrm ib)=\pi(a)+\mathrm i\pi(b)$。其算子范数闭包 $\mathcal A$ 是复 $C^*$-代数，$\pi(E)$ 在 $\mathcal A_{\rm sa}$ 中稠密；只有另有原序单位范数完备性时，才有 $\pi(E)=\mathcal A_{\rm sa}$。不声称 $\mathcal A=B(H)$。由所给张成条件，$H\ne0$ 当且仅当存在某个 $m_\alpha>0$；正质量仅承担非平凡性，不承担原评价的全域分离。保标签并交织全部插入的最小表示唯一到唯一酉同构。

证明。正核的零空间商与完成直接复用 Aronszajn 的正矩阵实现和 C117 命题 8.2 的同一机制。写

$$
N=\{z:K(z,z)=0\},\qquad H=\overline{V/N},\qquad Fz=[z].
$$

Cauchy–Schwarz 使 $N$ 与全部 $V$ 配对为零。现在必须证明原插入保持 $N$；不能仅凭核表示就假定它可下降。先在 (357.3) 取 $b=u$。由 $a\circ u=a$、$D(a,u)=0$ 和 (357.2) 的单位式，得到

$$
K(J_a z,w)=K(z,J_a w).
\tag{358.3}
$$

其中单位式及 Hermitian 性保证 $J_u w-w\in N$。故每个实 $c$ 的 $K(z,J_cz)$ 为实数。在 (357.3) 再取 $b=a,w=z$；左端实且非负，右端两个内读数均实，因此

$$
K(z,J_{D(a,a)}z)=0,\qquad
K(J_a z,J_a z)=K(z,J_{a\circ a}z).
\tag{358.4}
$$

在所有 $\xi_\alpha$ 上用原读数式及分离性，先得原向量 $D(a,a)=0$；实极化给 $D(a,b)=-D(b,a)$。对每个 $a$，原序单位有界性给某个 $r_a\ge0$ 使 $a\circ a\le r_a u$。全配方来源正性遂给

$$
0\le K(J_a z,J_a z)\le r_a K(z,z).
\tag{358.5}
$$

故 $J_aN\subseteq N$，$Fz\mapsto F(J_a z)$ 良定义且有界，延至 $H$。由 (358.3) 这个延拓 $\pi(a)$ 自伴，单位式给 $\pi(u)=I_H$。原读数立即成为 (358.1) 的 Born 配对；在 $a=u$ 处给精确原质量。若全部 $m_\alpha=0$，各 $F\xi_\alpha=0$，插入有界性与 $V$ 的张成条件使 $H=0$；反向由质量式直接得到。若 $\pi(a)=0$，则每个原 $\alpha(a)=0$，分离性给 $a=0$。正锥的正向由全配方正性及稠密性得到，反向由全部原 $\alpha$ 与 (357.1) 的锥定义得到。因此 $\pi$ 是原序的嵌入，$-ru\le a\le ru$ 当且仅当 $-rI\le\pi(a)\le rI$；取下确界即为等距性。

把 (357.3) 放到已合法下降的稠密域，得到

$$
\langle Fz,\pi(a)\pi(b)Fw\rangle
=\langle Fz,\pi_{\mathbb C}(a\circ b-\mathrm iD(a,b))Fw\rangle.
\tag{358.6}
$$

有界性和稠密性使它成为整个算子等式。交换 $a,b$ 并用刚证的交替性，取和、差即得 (358.1) 的两式；这一步绑定原 $D$，不是另定义一个 $A$ 后将名字换成 $D$。若 $\pi(a)+\mathrm i\pi(b)=0$，取伴随并相减得 $\pi(a)=\pi(b)=0$，所以 $\pi_{\mathbb C}$ 也单射。由 (358.6)，(358.2) 的结合子被忠实送为算子结合子零，故原结合子零；伴随、单位和闭包的 $C^*$ 性由该忠实算子像继承。自伴部分的稠密性通过对每个近似元取 $(x+x^*)/2$ 得到，原 $E$ 完备时等距像闭，才得到等号。最小像的 Gram 已由 $K$ 钉定，保 $Fz$ 的对应等距且稠密，因而延成唯一酉；交织插入由其在 $F(V)$ 上的公式给出。∎

**定义 358.2（新推导和仍输入的资料）。** 这里的新增综合是：将原全响应商的分离和质量接到同一插入比较，在尚未采用算子对象时用 (358.4)–(358.5) 取得零方向稳定，再同时取得忠实原对象、所有原评价的向量配对及字面旧 $D$ 的定向乘法。正核完成、GNS、$C^*$ 闭包和交换子代数均为成熟工具，不另立新的一般表示原理或复型分类。特别地，[正交迹续卷 §§398–401](AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md#398-同一输出在两个原子端点都切向) 的 $\mathsf F_{\rm 2tan}$ 分类不作为待重证结果；本定理另付来源关系，处理它未供应的联合采用入口。

被推导的数据是 $H,F,\pi$、同一评价的 Born 配对及同一 $D$ 的交换子识别；替代独立采用这些数据的来源前件是完整 $E,u,\circ,D$、全部分离评价和序界、共同 $K$、线性插入、(357.2) 与全部 (357.3)。这不是“没有前提”的推导，也未证明这些来源前件在逻辑上弱于旧前件、信息总量更少、全局最小或有限可认证。标量 $K(\xi_\alpha,\xi_\alpha)$ 正好成为原质量，是单位与原读数共同约束的后果，不把另一来源的 $Q$、总份额 $\nu$ 或独立强度 $W_e$ 自动认作质量。

## 359. 三点来源几何、非空无限模型与删除边界

**定理 359.1（带字面旧 D 的三点几何）。** 在定理 358.1 下，固定一个 $m=\alpha(u)>0$ 的原上下文及任意原 $a,b$。三个比较标签 $\xi_\alpha,J_a\xi_\alpha,J_b\xi_\alpha$ 的 Gram 恰为

$$
G_{\alpha;a,b}=\begin{pmatrix}
m&\alpha(a)&\alpha(b)\\
\alpha(a)&\alpha(a\circ a)&\alpha(a\circ b)-\mathrm i\alpha(D(a,b))\\
\alpha(b)&\alpha(a\circ b)+\mathrm i\alpha(D(a,b))&\alpha(b\circ b)
\end{pmatrix}\succeq0.
\tag{359.1}
$$

置

$$
\begin{gathered}
v_a=\alpha(a\circ a)-\alpha(a)^2/m,\quad
v_b=\alpha(b\circ b)-\alpha(b)^2/m,\\
c=\alpha(a\circ b)-\alpha(a)\alpha(b)/m,\qquad d=\alpha(D(a,b)).
\end{gathered}
$$

则 $v_a,v_b\ge0$ 且 $v_av_b\ge c^2+d^2$。若 $v_a>0$，等号当且仅当

$$
F(J_b\xi_\alpha)-\frac{\alpha(b)}mF\xi_\alpha
=\frac{c-\mathrm id}{v_a}
 \left(F(J_a\xi_\alpha)-\frac{\alpha(a)}mF\xi_\alpha\right).
\tag{359.2}
$$

若 $v_a=0$，则 $c=d=0$；若 $m=0$，整个 (359.1) 为零，不作条件化。此三点结论不反推全部 (357.3) 或全有限 Gram 正性。

证明。单位、对称插入与 (357.3) 逐项给 (359.1)。从后两向量分别减去第一向量的正交投影，得到二阶 Gram $\left(\begin{smallmatrix}v_a&c-\mathrm id\\c+\mathrm id&v_b\end{smallmatrix}\right)$。其正性和 Cauchy–Schwarz 的等号条件给全部结论。$m=0$ 时 $F\xi_\alpha=0$，有界插入使另两向量也为零。这里复用的是标准 Gram／协方差不等式；新增对应是这份三点表的虚部恰为已共同采用的原旧 $D$ 评价，不是由平方面积选择一个新号。∎

**定义 359.2（三维截面与更大结构）。** 对上述两个中心化向量，置 $t=v_a+v_b$。$t>0$ 时其二阶 Gram 除以 $t$ 的三个实坐标为

$$
r=\frac{(2c,\,2d,\,v_a-v_b)}{t},\qquad
|r|^2=1-\frac{4(v_av_b-c^2-d^2)}{t^2}\le1.
\tag{359.3}
$$

这是 [C117 §8.1](AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md#81-两条历史的三维关系坐标) 的既有二阶 Gram 球在本来源三点表上的应用。$t=0$ 只给零表，不制造一个球面点；$d$ 的正负保留原方向。这里三实维是二阶 Hermitian 表去掉总量后的坐标，不是物理三维，也不供应实际 $M_2$。若某个另已供应的有限复块含数学二阶角，其原子 Bloch 球和更大的 $\mathbb{CP}^{n-1}$ 角网直接复用 C128 原几何；跨中心仍是直和，不添加相干。无限情形的更大结构是 $\mathcal A$ 的算子／状态及正核网，不宣称每个无限域具有有限 EJA 的谱或原子结构。

**命题 359.3（候选有无穷维的非平凡一致模型）。** 任取可数无限指标集 $S$、有限正整数 $n_s$（允许 $n_s=1$ 和不等大小），令

$$
\mathcal M=\prod_{s\in S}^{\ell^\infty}M_{n_s}(\mathbb C),\quad
E=\mathcal M_{\rm sa},\quad
a\circ b=(ab+ba)/2,\quad D(a,b)=\mathrm i[a,b]/2.
\tag{359.4}
$$

取全部 $\rho_s\ge0$、$\sum_s\operatorname{Tr}\rho_s<\infty$ 所给的评价 $\alpha_\rho(a)=\sum_s\operatorname{Tr}(\rho_sa_s)$，包括零和任意次归一质量。则存在满足定义 357.1–357.3 的共同来源比较资料。还可独立保留任意正权 $w_s$ 满足 $\sum_sw_sn_s<\infty$ 的正定 Frobenius 型 $q(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s)$；这些权不成为 Born 概率权。

证明。在 $\mathscr H=\bigoplus_s\operatorname{HS}(M_{n_s})$ 中令 $v_\rho=(\sqrt{\rho_s})_s$，令 $a$ 左乘每个矩阵分量。$\|v_\rho\|^2=\alpha_\rho(u)$，左乘的范数至多 $\sup_s\|a_s\|$。取由所有有限原形式词及各 $\xi_\rho$ 生成的自由线性插入空间 $V$，将 $J_{a_1}\cdots J_{a_n}\xi_\rho$ 送到 $a_1\cdots a_nv_\rho$，以该像的内积定义 $K$。词槽关于 $a$ 的线性关系先按张量线性处理；单位只需在像中恒等。正性、(357.2) 及 (357.3) 分别来自同一 Hilbert 内积、正左乘和 $ab=a\circ b-\mathrm iD(a,b)$。逐块秩一评价分离整个 $E$ 并决定其正锥。任意多个不同中心单位线性无关，故 $E$ 无穷维；正质量来源给非零向量。$q$ 的绝对收敛由 $|\operatorname{Tr}(a_sb_s)|\le n_s\|a\|\|b\|$ 保证，其正定性与 Frobenius 性逐块继承。此为抽象类的一致实例，不把这里任选的权强加到原 $\Omega$，也不是 CountRead 的实际模型或完整 $B$ 的新供应。∎

**命题 359.4（单位、分离与有向部分的删除边界）。** 三个不同角色不能由正核完成单独替代。

第一，若删 (357.2) 的单位式，即使保留原读数、正性、分离和 (357.3)，比较向量范数也不必等于原质量。取 $E=\mathbb R$、$u=1$、通常乘法、$D=0$，原评价 $\alpha(a)=ma$，$m>0$。在 $\mathbb C^2$ 的通常内积中取 $\xi_\alpha=(\sqrt m,1)$、$J_a=\operatorname{diag}(a,0)$，以 $\xi_\alpha$ 及其插入张成 $V$。则 $\alpha(a)=K(\xi_\alpha,J_a\xi_\alpha)$，全部正性及乘法比较成立，但 $K(\xi_\alpha,\xi_\alpha)=m+1$。

第二，只让一部分准备分离某个模型的可见部分，不能识别完整原对象。取 $E=\mathbb R^2$ 的通常逐项乘法和锥、$D=0$，仅取 $\alpha(a_1,a_2)=a_1$，$J_a=a_1I$，$K$ 为一维内积。单位、原读数、正性和 (357.3) 都成立，第二分量却不可见。该例删去了 (357.1) 的完整分离／锥决定条件，不是完整原响应商的反模型；在真正的全未来商中，不能因当前少数读口看不见就删除仍被其他合法未来分离的分量。

第三，若把 (357.3) 换成只含原 Jordan 对称部的

$$
K(J_a z,J_b w)+K(J_b z,J_a w)=2K(z,J_{a\circ b}w),
\tag{359.5}
$$

则所有来源比较、Born 读数及 Jordan 对象均不再约束 $D$ 的号或尺度。在任一含非交换块的 (359.4) 模型中，保持全部 $K,J,\alpha,\circ,q$，分别令旧 $D$ 为 $\delta=\mathrm i[a,b]/2$ 与 $c\delta$，$c\in\mathbb R$；(359.5) 和右单位均相同。原 (357.3) 对后者的残差恰为

$$
\mathrm i(c-1)K(z,J_{\delta(a,b)}w).
\tag{359.6}
$$

非交换块及分离评价使某个残差非零，故只有 $c=1$ 通过整份联合式。这里删的是有向来源相容，不是只把 (357.3) 的两边取实部后仍量化全部复 $z,w$：后者可将一个输入乘 $\mathrm i$ 而恢复虚部。上述尺度歧义是已有 C123／本卷 §§353–356 的成熟边界在来源接口上的应用，不重报完整反模型或原词校准。三个例子的断言均由所给内积与线性作用直接验证；不称它们为完整原 $\Omega$ 或 R5-009 的反模型。∎

## 360. 有限 C128 消费者与完整无限来源分别采用

**定义 360.1（保持原目标的有限条件应用）。** 对一个与完整 CountRead 切口分别表述、确有有限维原响应商的 C128 对象，若定理 358.1 的来源前件已供应，则其原对象与原评价已共同嵌入同一复代数，且字面旧 $D$ 已被定向绑定。结合乘法给原 SC、导子律和混合曲率；这些是定理的后果，未作为其假设输入。完整消费者另在一份独立表述的有限响应背景上应用：须对该背景所需的每个原对象、实际联合、输出、标签和参考供应定理 358.1 的前件，再分别保留完整 $B$ 的精确有限正生成，或完整 $\mathsf B_{\rm cl}$ 的闭正生成，以及各自全部原接口，才按[正交迹续卷定理 399.2 的消费者](AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md#399-原选中域同一固定标签与完整消费者)接回。闭包中的数学极限不成为实际准备，二者不合写成同一种生成条件。单个有限对象的采用不供应整份背景；这份全有限条件应用不能用于包含原 CountRead 共同切口的完整 $\Omega$，后者的该切口已被证明无穷维。

原 $t_0$ 与字面 $\sigma_{t_0}$ 仍为事先选定的同一资料。在上述有限完整背景中，已绑定的单位交换子尺度通过既有共同尺度公式使同一 sigma 成立；不重选刻度或从平方尺度倒推来源取向。无限定理自身不声称原有限 sigma 公式在任意无限代数上有定义或适用。

若还要得到 §356 的固定 native 矩阵坐标 $\Theta_i$ 和字面 (356.3)，仍须证明这个来源构造的代数与那份固定矩阵词／保留读者／终端的保标签对应。定理 358.1 构造的是原 $E_A$ 自身的算子身份，既不从一个矩阵代数存在性挑选原对象，也不凭抽象同构将 $\pi(a)$ 自动认作指定 $K_h^*N_wK_h$。[native III 151.1–151.3](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#151-原七地址未来的字面效果张成与纯源预测面的中心自由度) 的字面效果张成与 ready 轨道不供应这种全原准备／来源比较绑定；§344–349 在其强 $\mathsf O_\times$ 入口下的唯一延拓和 §356 的双原词结论均保持原条件，不被较弱歧义推翻。本候选推进的是不预采用对象、Born 和旧 $D$ 三份独立数据的共同构造；它未完成这份具体 native 对应。

**定义 360.2（精确量子对应与实际来源余项）。** 各行的后果只在同一行所列前件下成立。

| 公理或接口 | 本候选的条件后果与仍需来源的部分 |
| --- | --- |
| 复 Hilbert 与原对象 | (357.1)–(357.3) 构造忠实 $\pi$ 与比较空间 $H$；复比较及其标记方向是输入，可从已有正配方路线在其准确条件下取得，不称复数从裸存在无前提产生。$H$ 不自动等于既定物理载体；数学完成不增添原对象或准备。 |
| 原状态／效果与 Born | 每个原 $0\le e\le u$ 满足 $0\le\pi(e)\le I$，原 $\alpha(e)=\langle F\xi_\alpha,\pi(e)F\xi_\alpha\rangle$，总质量为 $m_\alpha$；只在 $m_\alpha>0$ 时除以它。比较空间中的 $|F\xi_\alpha\rangle\langle F\xi_\alpha|$ 是该表示的迹类代表，不意味着原混合准备变成实际纯准备，也不证明另一个预定无限表示中的正规性。原效果菜单的完备性、独立 $W_e$ 和实际接受归属仍按原接口。 |
| 有限块密度与旧 $q$ | 有限复直和中直接复用 $\alpha(a)=\tau(\rho_\alpha a)=q(\widehat x_\alpha,a)$、$\tau(\rho_\alpha)=m_\alpha$、$\rho_{\alpha,s}=w_s\widehat x_{\alpha,s}$。原 $g^0$ 的 Riesz 元另经既有 $B_A$ 运输；不把它当成 $\widehat x_\alpha$。不等正 $q$ 权不改为概率权，也不要求各中心质量相同。 |
| 字面有符号旧 $D$ | 整份 (357.3) 给 $\pi(D(a,b))=\mathrm i[\pi(a),\pi(b)]/2$，连同旧 Jordan、SC 和曲率；来源须真实供应这个有向比较，不能用 C139 §32 新造的 $A$、主对数或概率面积替代它。 |
| 实际联合与全部相关输入 | 单切口定理不供应联合。另需同一实际联合的原嵌入、旧乘法／旧 $D$ 保持、相应交叉零、全部中心对、生成／分离和实际乘积及相关准备，才复用 C128 普通张量消费者；不能从各自比较空间任取张量积充当原联合，也不输入共同参考指数。 |
| 原过程、CP、质量与更新 | 插入 $J_a$ 不是原过程。每个旧设备／事件自己的全输入运输、实际全参考／记录放大、充分标准矩阵锥或其已证等价入口、次幺及完整测试归一仍分别需要；已有实际参考保正不自动是所有标准矩阵层 CP，按 C139 §§34–35 的准确区别。然后复用 C128 CP/TNI、完整测试 TP、整个 AC／精确 $N_u$／Xs 的平方根词和每个完整失败输出；数学 Kraus 指标不供应细记录，同效果不替换旧设备。 |
| 分组／遗忘、返回和全部历史 | 全部原细记录、实际分组遗忘、具名同数两侧支持返回及同数反向资料保留。只有对应的原箭头和合法复合已绑定时，才按既有迹对偶逐条评价顺序、自适应、并行和每条合法有限历史；$F\xi=0$ 不删除零支、失败、停止或原档案，也不准任意右接续。 |
| 酉时间与尺度 | 保比较并保原相位的实际可逆过程可复用 C140 §6 的酉桥；物理连续时钟、Hamiltonian／能量、共同作用量及 $\hbar$、原控制和独立成功支的共同仪器仍各需实际来源。数学交换子、形式指数与 $1/2$ 不提供它们。 |

**命题 360.3（与 CountRead 无限响应的相容性及未构造部分）。** 如果完整原 CountRead 切口满足定义 357.1–357.3，则其来源表示 $\pi(E_A)$ 必为无穷维；定理 358.1 不与 C139 命题 32.1a 矛盾。但本定理及命题 359.3 均不证明那个实际来源满足这些前件，也不构造其全部记忆、操作与未来的表示图。

证明。该原切口的 $[E_n]$ 已线性无关，$\pi$ 的单射性保持它们的线性无关，故其像不能有限维。若 $H$ 有限维，则 $B(H)$ 有限维，亦与单射性矛盾，所以这种采用的 $H$ 也必无限维。没有有限扩维、切分原共同切口、重命名每条历史或删除未来的步骤。命题 359.3 只证明此抽象候选允许无限结构；它不含 CountRead 的原负载、记忆递推、全部细读输出及各原操作，故不能成为该实际全未来表示。原整 $\Omega$、所有经典与不等量子块及原正权、全部实际联合、零／次归一及相关／积准备、设备／端口／细记录、完整失败、分组遗忘、同数双向和逆向返回及每条合法有限历史继续属于同一个目标。∎

## 361. 来源关系的简化坐标与完整直观解释

**定义 361.1（简化的准确坐标及文献范围）。** 在固定原响应／准备前端上，本候选把“先选算子对象，再另选 Born 运输，最后校准旧 $D$”改为“给同一来源插入比较，再共同构造三者”。减少的是独立选取这三份采用数据的自由度；新增的全配方正性、单位身份、原读数和有向乘法关系仍是明确的承重前件。未证明独立逻辑前提总数、实际供给成本、比较数量或全部信息下降。此处没有用有限三点条件替换全部来源比较，也没有把一个条件接口定理称为完整起源。

成熟正核与表示工具的文献归属为 $\texttt{literature-attested}$：[Aronszajn, *Theory of Reproducing Kernels*, 原文 Part I §2(3)–(4), p.344](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf) 从任意集合上的全部有限正矩阵构造唯一最小 Hilbert 实现，不要求整个指标域有限；本文使用第一槽共轭线性的约定，相应调整原文内积记号。仓内 [C117 §8 命题 8.2](AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md#prop-c117-gns) 已有 GNS、零方向与左接续稳定机制，明确没有任意右接续保证；这里不重复认领该一般结果。R5-009 §6、C140 §§3、6–7、C133 五点桥第 6 节各保留自身相位／正性／实际事件接口，不自动变成本候选前件。

[Niestegge, arXiv:1402.0158v2, §5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2#S5) 的成熟路线先要求 dynamical correspondence，再用正平方取得复 $C^*$ 结构；本节不把该文提供的条件结论冒充原来源已有动力对应，也不重新认领其结合乘法定理。本节的 $\texttt{repo-derived}$ 内容是原来源接口的联合采用应用：从一份尚未下降的比较插入证明 (358.4)–(358.5)，把全原评价分离和单位质量同时接到对象及旧 $D$ 的识别，再给 (359.1) 的具体来源对应及 (360.3) 的无限适用性。标准 Gram 不等式、Bloch 坐标、有限复块分类、概率迹运输和过程消费者不是新成果。不作历史优先权、经验本体、全坐标最小性或完整量子起源的结论。

**定义 361.2（完整白话）。** 白话说，整份原世界和每条历史都留在原处，先不把它塞进某个有限矩阵房间，也不分别发给它一张“这是哪个量子对象”、一张“概率按哪个 Born 向量读”、再一张“旧关系朝哪边转”的证明书；改为要求同一来源对比较配方确有一份共同的正比较，把原总事件当同一个单位，把每份原准备和历史的真实读数原样接进来，并要求两个原响应插入后的比较，同时等于旧 Jordan 的对称部分减去同一旧 D 的有向部分。这个要求仍是一条必须从来源证明的强关系，不因换了名字就已经成立。若它在全部配方和全部原上下文成立，原单位先把质量钉住，正性使看不见的零方向在插入后仍看不见，随后同一比较空间就共同给出忠实的原对象、保零与次归一质量的 Born 配对和有确定号的旧 D，而不是事后另挑一个交换子。取同一准备和两个插入便得到一张三点比较表，去掉共同方向后，两点的相干、质量差与有向读数落在熟悉的三实维球中；这只是关系表的几何，不是物理三维或实际量子比特，更大的网可以无限维。有限 C128 对象在各自完整背景和同一预选刻度下继续使用已有量子与过程定理，原不等比较权也不冒充概率权；完整 CountRead 的无限响应却必须继续留在无限载体上，本候选并未构造它的实际记忆和所有未来操作。来源为何供应共同比较及这些插入关系，怎样对应固定 native 门和终端，如何取得全部真实联合、参考、每台设备及细记录的完整输出和失败、分组遗忘与同数返回，以及物理钟、能量、作用量和共同仪器，仍各有明确未补的接口，完整量子起源目标因此继续保留。

## 追加锚 C128361INS（本行以下为增补区）

## 362. 总插入候选与两种可见线性的内生

**定义 362.1（保留原前端的总插入候选）。** 固定定义 357.1 的同一个完整原切口及其全部资料：原实响应商 $E$、全部原实线性评价 $\mathcal P$、原单位 $u$、原对称双线性乘法 $\circ$、$L_a b=a\circ b$ 和字面旧实双线性 $D$。仍要求这些评价分离 $E$ 并决定原正锥 $E_+$，每个原响应在 $u$ 的原序中有界，$\alpha(u)=m_\alpha\ge0$、$u\circ a=a$、$D(a,u)=0$。原 $q$ 若已供应仍逐字保留。本候选只撤去定义 357.2 中“插入关于 $a$ 实线性、关于 $z$ 复线性”这一对独立要求，改为每个 $a\in E$ 仅有一个处处定义的集合映射 $J_a:V\to V$；不要求它可加、齐次、连续、保零或保零方向。

其余来源条件全部保留。$V$ 仍是同一来源标签的有限形式比较配方所成的复向量空间，$K$ 仍是同一个第一槽共轭线性、第二槽线性的半正定 Hermitian 形式，包括全部有限复系数 Gram 正性。每个原上下文有原标签 $\xi_\alpha$，并且仍有精确的代数生成

$$
V=\operatorname{span}_{\mathbb C}
 \{J_{a_1}\cdots J_{a_n}\xi_\alpha:
 n\ge0,\ a_j\in E,\ \alpha\in\mathcal P\}.
\tag{362.1}
$$

这里先将 $J_{a_1}\cdots J_{a_n}$ 理解为任意总映射的实际复合，再取这些向量的有限线性张成；没有按线性延拓来定义原 $J$。$n=0$ 包括所有原标签，不设统一词长上限。对全部 $z,w\in V$、$a,b\in E$、$c\in E_+$ 和 $\alpha\in\mathcal P$，保留原单位、原读数、全配方正性与完整有向来源式：

$$
\begin{aligned}
K(z,J_u w)&=K(z,w),&
K(\xi_\alpha,J_a\xi_\alpha)&=\alpha(a),\\
K(z,J_cz)&\ge0,&
K(J_a z,J_b w)&=K(z,J_{a\circ b}w)
                  -\mathrm iK(z,J_{D(a,b)}w).
\end{aligned}
\tag{362.2}
$$

这正是 (357.2)–(357.3) 的原关系和原量词，没有用另一条线性、支配或来源完成公设替代被撤去的要求。比较配方和插入仍不被认作实际准备或物理设备；共同 $K$ 及有向式的实际同源解释仍由来源供应。

**定理 362.2（原校准与全词生成强制两种可见线性）。** 在定义 362.1 下，令

$$
N=\{z:K(z,z)=0\},\qquad W=V/N,\qquad p:V\to W
\tag{362.3}
$$

为正比较的代数零空间商及自然线性映射。则对全部 $a,b\in E$、$z,w\in V$、$n\in N$、$\lambda,\mu\in\mathbb C$ 和 $r,s\in\mathbb R$，有

$$
\begin{aligned}
p(J_0z)&=0,&p(J_uz)&=p(z),\\
p(J_a(z+n))&=p(J_az),&J_aN&\subseteq N,\\
p(J_a(\lambda z+\mu w))
 &=\lambda p(J_az)+\mu p(J_aw),\\
p(J_{ra+sb}z)&=r p(J_az)+s p(J_bz).
\end{aligned}
\tag{362.4}
$$

因此 $T_a p(z)=p(J_az)$ 是良定义的复线性算子 $W\to W$，$a\mapsto T_a$ 实线性，$T_u=I_W$。每个 $T_a$ 在 $W$ 的正定内积中对称，且

$$
T_aT_b=T_{a\circ b}-\mathrm iT_{D(a,b)}.
\tag{362.5}
$$

这些结论未预设 $W$ 完备或任何算子有界。零方向稳定是对原任意总插入的结论，不是定义商时另加的合法性。

证明。半正定 Hermitian 形式的 Cauchy–Schwarz 不等式使 $N$ 成为线性子空间，且与全部 $V$ 配对为零；故 (362.3) 的内积正定。先处理不能再由原线性性取得的 $J_0$。因为 $0\in E_+$，$t=K(z,J_0z)$ 为非负实数。将完整有向式用于 $a=b=0,w=z$，由原双线性得

$$
K(J_0z,J_0z)=(1-\mathrm i)K(z,J_0z)=(1-\mathrm i)t.
\tag{362.6}
$$

左端为实数，所以 $t=0$，并且 $J_0z\in N$。单位式另给 $J_uw-w\in N$。在有向式取 $b=u$，用原 $a\circ u=a$、$D(a,u)=0$，遂得

$$
K(J_az,w)=K(z,J_aw)\qquad(z,w\in V).
\tag{362.7}
$$

这一步没有把 $J_u$ 或 $J_0$ 在原 $V$ 上认作恒等或零。

对每个测试向量 $v\in V$，(362.7) 将 $K(J_a(\lambda z+\mu w),v)$ 化成 $K(\lambda z+\mu w,J_av)$，后者等于 $\bar\lambda K(J_az,v)+\bar\mu K(J_aw,v)$。因此相应线性缺陷与所有 $v$ 配对为零，缺陷属于 $N$。同样，若 $z-w\in N$，则 $K(J_az-J_aw,v)=K(z-w,J_av)=0$，故可见像只依赖 $p(z)$；取 $w=0$ 并用刚证的可见线性便得 $J_aN\subseteq N$。这证明了配方复线性、零方向稳定和 $T_a$ 的良定义。(362.7) 也给 $T_a$ 对称。

现在才可在 $W$ 上复合线性算子。对 $x=p(z),y=p(w)$，有

$$
\begin{aligned}
\langle x,T_aT_by\rangle
 &=\langle T_ax,T_by\rangle\\
 &=K(J_az,J_bw)\\
 &=\langle x,(T_{a\circ b}-\mathrm iT_{D(a,b)})y\rangle.
\end{aligned}
$$

正定内积的分离性给 (362.5)。此时尚未使用 $a\mapsto T_a$ 的线性。

为证明响应实线性，同时考虑所有有限原实线性关系

$$
\mathcal R=((r_j,a_j))_{j=1}^k,\qquad
s_{\mathcal R}=\sum_jr_ja_j=0,\qquad
S_{\mathcal R}=\sum_jr_jT_{a_j}.
\tag{362.8}
$$

末式只是在算子空间中取有限和，不预断言它等于 $T_{s_{\mathcal R}}$。在每个校准标签 $x_\alpha=p(\xi_\alpha)$ 上，完整有向式与同一个原读数给

$$
\begin{aligned}
\|S_{\mathcal R}x_\alpha\|^2
 &=\sum_{j,k}r_jr_k
   \bigl(\alpha(a_j\circ a_k)-\mathrm i\alpha(D(a_j,a_k))\bigr)\\
 &=\alpha(s_{\mathcal R}\circ s_{\mathcal R})
       -\mathrm i\alpha(D(s_{\mathcal R},s_{\mathcal R}))=0.
\end{aligned}
\tag{362.9}
$$

这里使用的是原 $\alpha$ 的实线性及原 $\circ,D$ 的双线性，未使用插入对响应线性。故所有 $S_{\mathcal R}$ 都消去所有 $x_\alpha$。

这还不等于消去整个 $W$，必须使用保留的全词生成。对任意 $b\in E$，由 (362.5) 得

$$
S_{\mathcal R}T_b
 =\sum_jr_jT_{a_j\circ b}
       -\mathrm i\sum_jr_jT_{D(a_j,b)}.
\tag{362.10}
$$

右边两族响应也分别具有同一系数的零关系，因为 $\sum_jr_j(a_j\circ b)=s_{\mathcal R}\circ b=0$、$\sum_jr_jD(a_j,b)=D(s_{\mathcal R},b)=0$。对词长作同时覆盖所有 $\mathcal R$ 的归纳：(362.9) 给长度零；若所有零关系消去每个长度 $n$ 的词向量，(362.10) 就使任意零关系消去每个长度 $n+1$ 的词向量。由已证的下降，原词的像恰为 $T_{a_1}\cdots T_{a_n}x_\alpha$；(362.1) 使它们的有限复线性包等于 $W$。故每个 $S_{\mathcal R}=0$。取 $\mathcal R=((1,ra+sb),(-r,a),(-s,b))$，即得 (362.4) 最后一式。全过程既未增加校准标签，也未假定词状态另有原准备。∎

## 363. 原插入可非线性与生成条件的删除边界

**命题 363.1（无限、非交换且原插入非线性的相容实例）。** 定理 362.2 不强制原 $V$ 上的 $J_a$ 具有任一种原线性；新候选的原资料类严格包含定义 357.1–357.3 的原联合候选资料类。这个区别可以与无穷维响应、非零旧 $D$、经典及不等大小复块、零及次归一质量和正 $q$ 权同时存在。

证明。取命题 359.3 的同一个抽象模型 (359.4)，使可数块族包含一维、二阶和三阶块；保留其全部 $\alpha_\rho$、旧乘法、$D$ 及任意该命题允许的正 $w_s$ 和 $q$。在其 $\mathscr H$ 中，令 $W_0$ 为所有有限左乘词作用于 $v_\rho=(\sqrt{\rho_s})_s$ 的代数复线性包。它对每个原 $a\in E$ 的左乘稳定。固定一份 $\beta=\alpha_{\rho_*}$，$\beta(u)=1$，只用于下面实例的零方向坐标。令

$$
\begin{gathered}
V=W_0\oplus\mathbb C,\qquad
K((v,t),(w,s))=\langle v,w\rangle_{\mathscr H},\\
\xi_\rho=(v_\rho,0)\ (\rho\ne0),\qquad \xi_0=(0,1),\\
J_a(v,t)=\bigl(av,\ |t|^2+\|v\|^2+\beta(a)^2\bigr).
\end{gathered}
\tag{363.1}
$$

每个 $J_a$ 处处有定义。比较只看第一坐标，故全部单位、原读数、全配方正性及有向式直接继承同一左乘模型；零标签的全部读数仍为零。这里 $ab=a\circ b-\mathrm iD(a,b)$ 是该一致实例的原式，不是用它重命名任意既给的 $D$。任意原词的第一坐标正是相应左乘词向量，这些向量张成 $W_0$；再加已保留的零标签 $(0,1)$，便得整个 $V$ 的精确生成 (362.1)，而非只得稠密性。

但 $J_u(0,0)=(0,1)$，所以原配方映射并非复线性；又有 $J_{2u}(0,0)=(0,4)\ne(0,2)=2J_u(0,0)$，所以原响应参数亦非实线性。所有这些缺陷都位于 $N=\{0\}\oplus\mathbb C$，不影响定理的两种可见线性。原评价仍分离整个无穷维 $E$，原 $D$ 在非交换块非零，原正权不成为概率权。这是抽象候选类的严格相容性和原线性删除见证，不是原 CountRead 的记忆模型，也不供应完整原 $\Omega$ 的实际联合、设备或历史图。∎

**命题 363.2（全标签校准不能替代全词生成）。** 若仅删除 (362.1)，其余定义 362.1 的条件均可成立，而可见响应实线性失败；即使 $K$ 正定、原评价包含全部非负质量且分离整个原 $E$，也不能排除这一失败。

证明。只为此删除边界取 $E=\mathbb R$、$u=1$、通常乘法和序、$D=0$，以及全部 $\alpha_m(a)=ma$、$m\ge0$。它们决定 $E_+$ 并分离 $E$，每个响应有序有界。取 $V=\mathbb C^2$ 的通常内积及

$$
\xi_m=(\sqrt m,0),\qquad
J_a=\operatorname{diag}(a,a^2).
\tag{363.2}
$$

这些插入已对配方复线性，$J_1=I$、$J_0=0$，$K(\xi_m,J_a\xi_m)=ma$。若 $c\ge0$，则 $K(z,J_cz)=c|z_1|^2+c^2|z_2|^2\ge0$；又 $J_a^*J_b=J_{ab}$，恰给全部有向式。所有原标签及其任意插入词却只张成第一坐标轴，未生成第二轴。在第二轴，$J_2$ 为 $4$ 而 $2J_1$ 为 $2$，响应实线性失败。此处 $N=0$，故非线性不是不可见档案。反例没有删原响应的分离性，删的是比较空间的全词生成；它不用于削弱完整原域。本候选始终保留 (362.1)，也不以某个有限词深或未给拓扑的闭生成替代它。∎

## 364. 删除前件后的既有消费者与准确适用范围

**推论 364.1（在已推导的可见资料上应用原联合采用）。** 定义 362.1 的全部前件足以给定理 358.1 的全部结论，而无需独立供应原插入的任一种线性。应用的是代数商上的资料 $(W,\widetilde K,(x_\alpha),(T_a))$，其中 $\widetilde K(pz,pw)=K(z,w)$，不是将原非线性 $J_a$ 直接冒充定理 358.1 的线性输入。尤其同一原 $E$ 和所有原评价具有该定理的忠实、保序单位表示，且

$$
\pi(a\circ b)=\tfrac12(\pi(a)\pi(b)+\pi(b)\pi(a)),\quad
\pi(D(a,b))=\tfrac{\mathrm i}{2}[\pi(a),\pi(b)],\quad
\alpha(a)=\langle F\xi_\alpha,\pi(a)F\xi_\alpha\rangle,
\quad\|F\xi_\alpha\|^2=m_\alpha.
\tag{364.1}
$$

这里 $F$ 是 $p$ 后接所构造完成的映射。原序单位范数、有界性、$E_{\mathbb C}$ 的结合乘法及 $C^*$ 闭包 $\mathcal A$ 均逐项取定理 358.1；$\pi(E)=\mathcal A_{\rm sa}$ 仍须原 $E$ 的范数完备性，不能仅因比较空间被完成就取得这个等号。

证明。定理 362.2 给出所需两种精确线性和零方向稳定。原单位、读数、全配方正性及有向式在 $p$ 下保留；(362.1) 的像给 $W$ 的同样代数生成，原 $E$ 的全部前端条件未改。因此定理 358.1 的假设在这份可见资料上逐项满足。直接应用该定理并将原标签复合到完成，便得全部结论。这里不另证正核、Riesz、GNS 或一般表示定理，也不从尚未有界的对称算子直接跳到 $B(H)$。∎

**定义 364.2（同一前端下的前提比较、几何和量子对应）。** 以下比较只涉及独立的来源输入，不改变旧文本的条件结论。

| 来源条款 | 定义 357.1–357.3 | 定义 362.1 |
| --- | --- | --- |
| 完整原 $E,u,\mathcal P,\circ,L,D$、分离、原锥和序界，已给的原 $q$ | 保留 | 全部相同 |
| 同一 $V,K,\xi_\alpha$，全有限复 Gram 正性 | 保留 | 全部相同 |
| 全配方单位、原评价、正性及完整有向来源式 | 保留 | 全部相同，仍量化全部原响应对及全部配方对 |
| 所有原插入词的精确代数生成 | 保留 | 原样保留，未换成有限截断 |
| 原 $J$ 的配方复线性及响应实线性 | 分别要求 | 两项均撤去；定理 362.2 推出各自可见版本 |
| 替代性的线性或来源假设 | 无 | 无新增 |

这给出可核对的删除前件增益：旧候选蕴含新候选，新候选在不换前端或有向式的条件下足以进入同一消费者；命题 363.1 则表明新候选确实容许旧定义排除的原资料。若 $K$ 原本正定，零空间为零，两种原线性本就由保留条款强制；允许退化 $K$ 时，严格扩大的自由只在原插入的零方向行为中。因而减少的是两种原线性必须独立验证的要求，没有减少共同正比较、有向来源关系、全词生成或任何物理供应；不声称比较次数、供给成本、信息总量或全部前提坐标严格下降。

有限三点和三实坐标的几何不另分类：对同一 $\alpha,a,b$ 直接应用定理 359.1，其原三点 Gram 仍为 (359.1)，虚部仍为 $-\alpha(D(a,b))$。沿定义 359.2 的 $v_a,v_b,c,d$，当 $t=v_a+v_b>0$ 时仍是 $r=(2c,2d,v_a-v_b)/t$、$|r|\le1$；$t=0$ 和零质量分别沿原零表条款处理。它是二元关系表的三实参数，不是实际 $M_2$ 或物理三空间。更大结构仍是可能无穷维的 $\mathcal A$、其状态和比较向量网；原 $E$ 与原档案未被换成三维截面。C117 §8 和 V78 综合卷 §5 的既有 Gram 球、C133 原卷定理 2.3 的完成及整数续篇 II 定义 6.1–定理 6.2、续篇 III 定理 5.1 的完整事件效果，只在各自前件吻合时直接复用，不由三点表单独供应它们的事件族、相位或过程接口。

量子对应仍逐行受定义 360.2 的全部前件约束。推论 364.1 现在从总插入候选取得同一复 Hilbert 比较表示、原状态／效果的 Born 配对及质量、原 Jordan 和有符号旧 $D$；有限复块上的密度、原 $q$ 权运输、SC 与曲率分别沿既有消费者，不重做有限分类。没有从单切口推得实际联合：同一实际联合的原嵌入、旧乘法与 $D$ 保持、所需交叉零、全部中心对、乘积及相关准备、生成和分离仍须供应。每台原设备／事件仍须其全输入运输、原接受事件归属、实际全参考／记录放大及充分标准矩阵锥或已证等价接口，才能进入 CP/TNI 和完整测试 TP；原 AC、精确 $N_u$、Xs、细记录、全部输出和完整失败均不由比较插入制造。同效果不确定设备更新，数学 Kraus 指标不替代记录。

全部实际分组／遗忘、同数双向及同数逆向返回、每个合法复合与全部有限历史继续按原箭头逐条绑定，不从零方向商取得任意右接续。酉时间的后果仍需实际可逆保比较并保相位的过程；连续物理时钟、Hamiltonian／能量、共同作用量、原控制和独立成功支的共同仪器均保留各自来源义务。完整 $B$ 的精确有限正生成与另名 $\mathsf B_{\rm cl}$ 的闭正生成继续分开，闭包不成为实际准备；数学比较词生成 (362.1) 不是这两种准备生成的替代。同一原 $\sigma$ 和预选 $t_0$ 不变，有限尺度公式仅在原有限完整背景适用。

对完整原 $\Omega$，所有经典与不等维量子块及原正权、实际联合、相关／积／零／次归一准备和质量、设备／端口／细记录／全失败、分组遗忘、双向及逆向返回和每条合法有限历史均保留。C139 固定源卷命题 32.1a 的完整 CountRead 商仍无穷维；若它实际满足本候选，单射 $\pi$ 及其 $H$ 必无穷维，直接复用命题 360.3。全有限 C128 消费者仍只能在另行表述且确有有限响应商的完整背景采用；有限扩维、切分共同切口、重命名历史或删除未来均不解决原目标。实际 CountRead 的完整记忆／操作／全未来表示仍未构造，本节没有证明其 $K$ 或有向来源律存在。

**定义 364.3（成熟成分、原来源综合与完整白话）。** 精确伴随关系强制线性是成熟工具，归属 $\texttt{literature-attested}$：[Frank–Găvruţa–Moslehian, Superstability of adjointable mappings on Hilbert C∗-modules, arXiv:math/0501139v6，Lemma 2.2，pp.3–4](https://arxiv.org/pdf/math/0501139v6)，期刊 DOI [10.2298/AADM0901039F](https://doi.org/10.2298/AADM0901039F)。本文采用其通过全部测试配对分离线性缺陷的标准论证，在半正定商上直接给出 (362.7) 及其应用；不把该文完备 Hilbert 模上处处定义时的有界性结论提前套到尚未完成的 $W$，也不认领一般自动线性为新发现。[Niestegge, arXiv:1402.0158v2，§5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2#S5) 的动力对应与复代数后果仍取定义 361.1 的成熟范围；本文未把那些条件定理当成原来源已供应旧 $D$ 的证据。

本节的 $\texttt{repo-derived}$ 内容是这个固定原来源接口上的删除前件应用：先从保留的零响应正性、单位及有向式取得精确伴随关系，再由原校准的 (362.9) 和保持原零关系的 (362.10)，把响应实线性传遍全部原比较词。C133 续篇 IV 定理 1.3、5.2 已在双端三向距离／完整分支接口上内生可见标记或过程线性，但不处理本节原 $E,\circ,D$ 的有向插入兼容；C117 的既有 GNS 先有代数左乘，定理 358.1 则先要求两种原线性。这些结果不替本节补上这一具体删除前件步骤。推论 364.1 只复用既有消费者，新增相容实例与生成删除边界分别限定原插入和可见响应的结论强度。不作历史新颖性、物理起源已完成或全坐标最简的主张。

白话说，整份原世界、每条过去和未来、每个失败和记录都仍保留，旧 D、旧 Jordan、原比较权和预先选定的刻度也没有换名；我们只不再另行规定“插入合起来的配方必须等于分别插入再合起来”和“插入两个响应的实线性组合必须按同样系数组合”。原插入可以任意改动档案中比较看不见的部分。若同一来源确有原来的共同正比较、单位和全部有向配对关系，零响应先被迫不可见，单位继而使插入在两边比较中互为伴随，所以配方的复线性和零方向稳定已经被关系本身强制。响应一侧还需要原读数校准：原响应中任何和为零的实线性关系，在每个原标签上产生的向量也只能为零；有向乘法关系让这个零关系穿过每一层插入，原来保留的全词生成才使它覆盖整个可见空间。若漏掉这一生成，另一个从未被原标签到达的比较方向就能偷偷按响应的平方变化，虽然所有已校准读数仍正确。这样省下的是两份额外原线性要求，而不是凭空省掉共同比较或有向来源律。随后直接使用已有采用定理，同一准备和两个插入仍给三点比较表，去掉共同方向后的相干、方向和质量差仍落在三实坐标的球内，更大的比较网络可以无限维；这不是物理三空间或新设备。完整 CountRead 的无限响应仍须无限表示，它的实际记忆和所有操作尚未构造；真实联合、全部相关输入、原接受事件、参考与 CP、每台设备的完整更新和细记录失败、分组遗忘与同数返回，以及物理钟、能量、作用量和共同仪器，仍须各自原来源接口。所证明的是保留强来源关系时两种可见线性不必再独立输入，不是裸来源已经产生这些关系或整个量子世界。

## 追加锚 C128364INS（本行以下为增补区）

## 365. 同一原正锥的一次实插入测试

**定义 365.1（只撤全配方正性的固定背景）。** 保留定义 362.1 的同一完整 $E,u,\mathcal P,\circ,L,D$、已给的原 $q$、原评价分离及锥决定、原序单位界、全部原标签、同一 $V,K$ 的全有限复 Gram 正性、原单位与校准、全部原词的精确代数生成 (362.1)。每个 $J_a:V\to V$ 仍只是总集合映射。仅暂不要求 (362.2) 的 $K(z,J_cz)\ge0$；其余各行保留原量词，特别是

$$
K(J_a z,J_b w)=K(z,J_{a\circ b}w)-\mathrm iK(z,J_{D(a,b)}w)
\quad(a,b\in E,\ z,w\in V).
\tag{365.1}
$$

记这份背景为 $\mathsf H$。这里的 $E_+=\{c:\alpha(c)\ge0\ (\alpha\in\mathcal P)\}$ 仍是原锥，不另选正元族。以下三条条件在同一份 $\mathsf H$ 上比较：

$$
\begin{aligned}
\mathsf P_{\rm all}:&\quad K(z,J_cz)\ge0
 &&(c\in E_+,\ z\in V),\\
\mathsf P_{\rm one}:&\quad K(J_a\xi_\alpha,J_c(J_a\xi_\alpha))\ge0
 &&(c\in E_+,\ a\in E,\ \alpha\in\mathcal P),\\
\mathsf Q_{\rm old}:&\quad Q_a(E_+)\subseteq E_+,
 \qquad Q_a=2L_a^2-L_{a\circ a}
 &&(a\in E).
\end{aligned}
\tag{365.2}
$$

$\mathsf P_{\rm one}$ 不含不同标签的组合、不含任意复系数组合，也不直接测试两次或更多插入；$a$ 仍遍历全部原实响应，$c$ 仍遍历整个原锥。$Q_a$ 是旧 Jordan 的原二次多项式，暂未将它当作实际滤器。没有预设插入线性、有界性、谱、平方根、完备性或复二次模闭性。

## 366. 从一次原测试到全部词与复组合

**引理 366.1（不使用正插入条件的可见代数）。** 单独的 $\mathsf H$ 已足以给出定理 362.2 的全部代数结论 (362.3)–(362.5)。此外，$a\mapsto T_a$ 单射，旧 $D$ 交替，$E_{\mathbb C}=E+\mathrm iE$ 的旧式 $a\cdot b=a\circ b-\mathrm iD(a,b)$ 复双线性延拓为结合含幺 $*$-代数，且在尚未完成的 $W=V/N$ 上忠实表示。其共轭为 $(a+\mathrm ib)^*=a-\mathrm ib$。对每个原 $a,c$，有

$$
T_{Q_a c}=T_aT_cT_a,\qquad
\alpha(Q_a c)=K(J_a\xi_\alpha,J_c(J_a\xi_\alpha)),\qquad
W=\operatorname{span}_{\mathbb C}\{T_bx_\alpha:b\in E,\ \alpha\in\mathcal P\},
\quad x_\alpha=p\xi_\alpha.
\tag{366.1}
$$

这些结论没有先调用缺少正性前件的定理 362.2 或 358.1。

证明。由 $K$ 的正性，$N=\{z:K(z,z)=0\}$ 与全部 $V$ 正交。单位式使 $J_uw-w\in N$。在 (365.1) 取 $a=0,b=u$，原双线性给

$$
A:=K(J_0z,w)=(1-\mathrm i)K(z,J_0w)=:(1-\mathrm i)B.
\tag{366.2}
$$

交换 $z,w$ 再共轭得到 $B=(1+\mathrm i)A$，故 $A=2A$、$A=B=0$。因此每个 $J_0w\in N$。这替代了 (362.6) 证明中对 $c=0$ 的正插入调用；没有假定 $K(z,J_0z)$ 是实数。在 (365.1) 取 $b=u$，现在得到精确伴随关系

$$
K(J_az,w)=K(z,J_aw).
\tag{366.3}
$$

对全部测试向量使用此式，配方的复线性缺陷及零方向差都与 $V$ 正交。因此 $T_apz=p(J_az)$ 良定义、复线性、对称，并有 $T_0=0,T_u=I$；(365.1) 在商上给 (362.5)。

响应实线性直接复用 (362.8)–(362.10) 的代数论证：若 $\sum_jr_ja_j=0$，则原校准和双线性使 $\|\sum_jr_jT_{a_j}x_\alpha\|^2=0$。将这个零关系右接 $T_b$，(362.5) 把它分成 $\sum_jr_j(a_j\circ b)=0$ 与 $\sum_jr_jD(a_j,b)=0$ 两个原零关系。对所有零关系同时作任意词长归纳，再用精确全词生成，得到 $\sum_jr_jT_{a_j}=0$。此段只用 $K$ 正定商上的零范数、校准、有向式和生成，不用任何正插入条件。故两种可见线性及 (362.4) 全部成立。

若 $T_a=0$，全部 $\alpha(a)=\langle x_\alpha,T_ax_\alpha\rangle=0$，原分离性给 $a=0$。取 $b=a$，$T_a^2=T_{a\circ a}-\mathrm iT_{D(a,a)}$；前两算子在共同不变域 $W$ 对称，故 $\langle x,T_{D(a,a)}x\rangle=0$ 对全部 $x$ 成立。复极化及单射性给 $D(a,a)=0$，原双线性再给交替性。交换 $a,b$ 后相加、相减，得到

$$
T_{a\circ b}=\tfrac12(T_aT_b+T_bT_a),\qquad
T_{D(a,b)}=\tfrac{\mathrm i}{2}[T_a,T_b].
\tag{366.4}
$$

若 $T_a+\mathrm iT_b=0$，对所有内积配对取形式伴随还得到 $T_a-\mathrm iT_b=0$，所以复化亦单射。由 (362.5)，$T_{\mathbb C}$ 保持旧乘法；算子乘法的结合性与单射性遂给原乘法结合，(366.4) 给其 $*$ 性。这些都是不变代数域上的等式，不含闭算子或有界延拓的断言。

把 $Q_a c=2a\circ(a\circ c)-(a\circ a)\circ c$ 送入 (366.4)，展开得到 $T_{Q_a c}=T_aT_cT_a$。在 $x_\alpha$ 上配对并用 (366.3) 给 (366.1) 的校准恒等式。最后，结合乘法把任意有限实响应词的乘积写成某个 $b+\mathrm id\in E_{\mathbb C}$，其词向量为 $(T_b+\mathrm iT_d)x_\alpha$。原全词生成因而给 (366.1) 的精确复线性张成；这里不把这个形式组合宣告为原准备。∎

**定理 366.2（同一前端上的正性测试域等价）。** 在定义 365.1 的全部不变背景 $\mathsf H$ 上，恰有

$$
\boxed{\mathsf P_{\rm all}\ \Longleftrightarrow\
       \mathsf P_{\rm one}\ \Longleftrightarrow\
       \mathsf Q_{\rm old}.}
\tag{366.5}
$$

因此以一次实插入测试替换原全配方正性后，无需新增条件即可恢复推论 364.1／定理 358.1 的同一原对象、同一旧 $D$、全部原 Born 读数、原序单位范数及 $C^*$ 闭包结论。等价覆盖任意有限词长、任意有限复系数组合和跨标签组合；不要求完整原商有限维或完备。原 $J$ 的不可见非线性仍然允许。

证明。$\mathsf P_{\rm all}\Rightarrow\mathsf P_{\rm one}$ 是取测试向量。由引理 366.1 的校准恒等式与原锥的全部评价定义，$\mathsf P_{\rm one}\Longleftrightarrow\mathsf Q_{\rm old}$。关键是只用 $\mathsf Q_{\rm old}$ 证明 $\mathsf P_{\rm all}$。

先在引理给出的代数中定义实幂 $a^0=u$；结合性与 $*$ 性保证每个 $a^n\in E$，并且 $T_{a^n}=T_a^n$。固定任意 $a\in E$。原序界可用于原响应 $a^2=a\circ a$，故存在某个 $R>0$ 使 $a^2\le Ru$。由 $u\in E_+$ 及保锥，$a^2=Q_a u\in E_+$。反复对 $Ru-a^2$ 应用同一个旧 $Q_a$，得到

$$
0\le a^{2n}\le R^n u\qquad(n\ge0).
\tag{366.6}
$$

具体而言，$Q_a^n u=a^{2n}\ge0$，而 $Q_a^n(Ru-a^2)=Ra^{2n}-a^{2n+2}\ge0$；从 $n=0$ 归纳即得上界。这里只反复应用已证明等价的一次测试的几何版本，未直接假定多词或复二次模正性。

对每个实 $b$ 和原 $\alpha$，保锥使 $Q_b$ 保序。故全部整数 $n\ge0$ 满足

$$
\begin{aligned}
\|T_a^nT_bx_\alpha\|^2
 &=\alpha(Q_b(a^{2n}))\\
 &\le R^n\alpha(Q_bu)
 =R^n\|T_bx_\alpha\|^2.
\end{aligned}
\tag{366.7}
$$

现取任意 $w\in W$。由 (366.1)，可选某个有限分解 $w=\sum_{j=1}^k\lambda_jT_{b_j}x_{\alpha_j}$，$b_j\in E,\lambda_j\in\mathbb C$，并令 $C_w=\sum_j|\lambda_j|\|T_{b_j}x_{\alpha_j}\|$。三角不等式给

$$
\|T_a^n w\|\le R^{n/2}C_w\qquad(n\ge0).
\tag{366.8}
$$

$C_w$ 可以依赖分解，不能直接用它冒充 $\|w\|$。但是共同不变域上的对称性给 $\|T_aw\|^2=\langle w,T_a^2w\rangle\le\|w\|\|T_a^2w\|$。反复对偶次幂使用同一不等式，得到

$$
\|T_aw\|
\le\|w\|^{1-2^{-k}}\|T_a^{2^k}w\|^{2^{-k}}
\le\sqrt R\,\|w\|^{1-2^{-k}}C_w^{2^{-k}}
\quad(k\ge1).
\tag{366.9}
$$

$w=0$ 时结论直接成立；$w\ne0$ 时 $C_w\ge\|w\|>0$，令 $k\to\infty$ 得 $\|T_aw\|\le\sqrt R\|w\|$。所以每个 $T_a$ 确实有界，才可延为 $H=\overline W$ 上的有界自伴 $\pi(a)$。这一步没有引用不完备内积空间上的处处定义对称算子自动有界的错误命题，也没有预设任何统一词长。所有代数等式在稠密共同域上成立，现因有界性而延至整个 $H$。

还须证明原正 $c$ 的 $\pi(c)$ 为正，不能把实测试直接提升为复测试。固定 $c\in E_+$，令 $S=\pi(c)$；其有界自伴性刚已证明。对任意实多项式 $f$，$f(c)\in E$；对每个 $v=T_bx_\alpha$，两次使用原保锥得到

$$
\langle v,Sf(S)^2v\rangle
 =\alpha\bigl(Q_b(Q_{f(c)}c)\bigr)\ge0.
\tag{366.10}
$$

现在才使用有界自伴算子的谱定理。记 $S$ 的投影谱测度为 $\mathsf E_S$，$\mu_v(B)=\langle v,\mathsf E_S(B)v\rangle$，其支撑在某个紧实区间 $[-M,M]$。若 $M=0$，$S=0$。若 $\mu_v(( -\infty,0))>0$，则存在 $\varepsilon>0$ 使 $\mu_v([-M,-\varepsilon])>0$。取实连续函数 $g$，在此负区间等于一，在 $[-\varepsilon/2,M]$ 为零，且 $0\le g\le1$。于是 $\int t g(t)^2\,d\mu_v(t)<0$。实多项式在紧区间上一致逼近 $g$，使相应 $\int t f(t)^2\,d\mu_v(t)$ 也为负，违反 (366.10)。故负谱投影消去每个 $T_bx_\alpha$。这些向量的复线性包在 $H$ 稠密，投影有界，遂为零；所以 $S\ge0$。

这确实处理跨标签和任意复相位：既已在整个 $H$ 得到 $\pi(c)\ge0$，任意原 $z\in V$ 均有

$$
K(z,J_cz)=\langle pz,\pi(c)pz\rangle\ge0.
\tag{366.11}
$$

因此 $\mathsf P_{\rm all}$ 恢复。至此才满足定义 362.1 的全部前件，直接应用推论 364.1 及其既有消费者，不重建一般 GNS 或另选 Born／旧 $D$。比较空间的完成不要求原 $E$ 完备；$\pi(E)=\mathcal A_{\rm sa}$ 仍只在原序单位范数完备时成立。∎

**推论 366.3（复夹乘闭性是后果）。** 在上述三个等价条件下，若 $c\in E_+$、$h\in E_{\mathbb C}$，则 $h^*\cdot c\cdot h$ 是 $E_+$ 的元素。

证明。引理 366.1 的 $*$ 性先使该元自伴，故属于原 $E$；定理 366.2 后取得的保序忠实表示将它送为 $\pi_{\mathbb C}(h)^*\pi(c)\pi_{\mathbb C}(h)\ge0$，再由原序的反映性带回。这里是推出复夹乘闭性，不将它作为从实测试到 (366.11) 的前件；它也没有供应实际矩阵参考或 CP 所需的完整矩阵层接口。∎

## 367. 删除一次测试留下的原锥缺口

**命题 367.1（保留其余背景的抽象接口删除见证）。** 若从 $\mathsf H+\mathsf P_{\rm one}$ 中只删去 $\mathsf P_{\rm one}$，其余背景可以全部满足，原裸标签在所有 $c\in E_+$ 上的读数也全非负，但一个单标签经过一次实插入即可给负值。此见证可同时具有无限响应、非交换旧 $D$、经典及不等大小块、正 $q$ 权、零及次归一质量和原插入的不可见非线性。它是抽象接口模型，不是实际 $\Omega$ 或 CountRead 的实现。

证明。先给出负值所在的二阶局部因子。取四个单位向量

$$
v_1=(1,0)^{\mathsf T},\quad v_2=(0,1)^{\mathsf T},\quad
v_3=(1,1)^{\mathsf T}/\sqrt2,\quad
v_4=(1,\mathrm i)^{\mathsf T}/\sqrt2,
\qquad f_j(A)=v_j^*Av_j.
\tag{367.1}
$$

在 $H_2(\mathbb C)$ 上取原评价族 $\alpha_t=\sum_{j=1}^4t_jf_j$、$t_j\ge0$，包括 $t=0$。四个 $f_j$ 分别读出两个对角和两个交叉实分量，所以分离整个实空间。它们决定的原锥恰为 $f_j(A)\ge0$ 的交，单位为 $I_2$，每个响应在此序中有单位界。保留通常旧 Jordan 和 $D(A,B)=\mathrm i[A,B]/2$。在四份 $\mathbb C^2$ 的直和上，以通常内积作 $K$，以 $A$ 在各份左乘作 $J_A$，标签为 $(\sqrt{t_j}v_j)_j$。各独立 $t$ 方向的标签及其 Hermitian 左乘词复线性张成整个直和，故全词生成精确成立。原单位、质量 $\sum_jt_j$、全部校准和全部有向式均成立。

取同一原实响应

$$
c=\begin{pmatrix}1&1-\mathrm i\\1+\mathrm i&1\end{pmatrix},\qquad
a=\begin{pmatrix}1&-1+\mathrm i\\-1-\mathrm i&0\end{pmatrix},\qquad
w=av_1=(1,-1-\mathrm i)^{\mathsf T}.
\tag{367.2}
$$

直接的纸面乘法给 $(f_1(c),f_2(c),f_3(c),f_4(c))=(1,1,2,2)$，所以 $c$ 在该原锥内；但 $cw=(-1,0)^{\mathsf T}$，故

$$
f_1(Q_a c)=w^*cw=-1
 =K(J_a\xi_{(1,0,0,0)},J_c(J_a\xi_{(1,0,0,0)})).
\tag{367.3}
$$

这里没有删除评价分离、改掉字面有向式或破坏 $K$ 正性。失效的是原评价所定义的较大锥在旧 $Q_a$ 下不稳定；裸标签校准不能排除它。所有插入甚至已经有界且线性，故仅补这两项也不修复删除。

为同时保留无限与不等块，复用命题 359.3 的可数乘积 (359.4)，令其含一维、二阶和三阶块，并在一个指定二阶块 $s_*$ 用上述四射线评价代替该块的全部正密度评价；其余块仍取该命题的全部正迹类评价。完整评价为

$$
\alpha_{t,\rho}(A)=\sum_{j=1}^4t_jf_j(A_{s_*})
 +\sum_{s\ne s_*}\operatorname{Tr}(\rho_sA_s),\qquad
t_j\ge0,\quad \rho_s\ge0,\quad
\sum_{s\ne s_*}\operatorname{Tr}\rho_s<\infty.
\tag{367.4}
$$

该族分离整个 $E$；其锥在 $s_*$ 为四不等式锥，在其余块为通常正锥。$\ell^\infty$ 算子界仍给原序单位界。将原比较 Hilbert 空间取为上述四份 $\mathbb C^2$ 与其余块 Hilbert–Schmidt 空间的直和，标签取 $(\sqrt{t_j}v_j)_j\oplus(\sqrt{\rho_s})_{s\ne s_*}$，并取全部左乘词的代数复线性包 $W_0$。以此 $W_0$ 作 $V$ 时，所有背景式及精确生成逐项成立。把 (367.2) 的 $a,c$ 只放在 $s_*$、其余分量置零，(367.3) 原样保留。命题 359.3 允许的任意正 $w_s$ 与 $q(A,B)=\sum_sw_s\operatorname{Tr}(A_sB_s)$ 均保留；这些权不成为概率权。

若还要原 $J$ 非线性，准确复用命题 363.1 的零方向扩充：取 $V=W_0\oplus\mathbb C$，比较只读 $W_0$，保留非零标签的零末坐标而将零标签置为 $(0,1)$，令 $J_A(v,t)=(Av,|t|^2+\|v\|^2+\beta(A)^2)$，其中 $\beta$ 是 (367.4) 中任一单位质量评价。比较中全部背景关系与负值不变。所有词的第一坐标张成 $W_0$，零标签补齐末坐标，所以仍精确生成；非线性全部落在比较零空间。这一模型不要求被删除的正插入条件，因而不与命题 363.1 原先的正模型混淆。其全部质量、块和标签只是所给抽象接口的资料，没有将它认作实际原世界的设备、历史或联合。∎

## 368. 同一消费者、三点几何与完整来源范围

**定义 368.1（改善坐标和准确量子对应）。** 在同一原前端下，$\mathsf H+\mathsf P_{\rm one}$ 是完整候选，$\mathsf H+\mathsf Q_{\rm old}$ 是它的等价几何表述。定理 366.2 缩小的是需要独立检验的正插入测试域：从全部 $z\in V$ 缩到每个原标签经一次实插入的 $J_a\xi_\alpha$。这族在某些退化资料上可以已覆盖全部可见向量，因此不声称每个模型都严格少测；也不声称有限可认证。完整模型类与 $\mathsf H+\mathsf P_{\rm all}$ 相同，并未因等价表述而扩大或在每个逻辑／物理坐标上变得更简单。

共同 $K$ 的全部有限复 Gram 正性、全配方单位／校准、所有 $a,b,z,w$ 的有向来源律、无上限词长的精确生成、全部原序界与原评价分离均原样保留。特别地，三点 Gram 正性不能替代共同正 $K$；实际来源仍须供应 $\mathsf P_{\rm one}$ 或等价的旧 $Q$ 保锥，不能从裸标签读数或来源名字推出它。命题 367.1 说明只删这项条件时原锥确会失稳；本定理没有证明其余保留条件在完整原来源上彼此独立。

量子后果准确复用推论 364.1 和定义 360.2：同一原 $E$ 忠实保序进入复 Hilbert 表示，同一 $\alpha(e)$ 与质量成为 Born 配对，同一旧 Jordan 和有向 $D$ 成为 (364.1) 的反交换子与有符号交换子。复比较是输入，未由此次测试域缩减产生。$H$ 的完成不增加实际准备，也不赋予预定另一表示的正规性。有限复块中的密度／原 $q$ 权运输、SC、导子律、混合曲率和完整过程消费者均沿原结论采用，不重新分类。

几何直接复用定理 359.1 和定义 359.2：对同一 $\alpha,a,b$ 的三个标签，原 Gram 仍是 (359.1)，其有向交叉项仍为 $-\mathrm i\alpha(D(a,b))$。$m_\alpha>0$ 时去掉共同标签方向，二阶协方差满足 $v_av_b\ge c^2+d^2$；$t=v_a+v_b>0$ 时 $r=(2c,2d,v_a-v_b)/t$ 在三实单位球内。$t=0$ 只给零表；$m_\alpha=0$ 不作条件化。这里的二元比较、三标签及三实坐标是局部关系表几何，不是物理三维、实际 $M_2$ 或整个系统的维数。更大结构仍是可能无限维的 $\mathcal A$、状态及比较网，跨中心不增添相干。

实际联合、积和相关准备仍须原嵌入保持旧乘法与 $D$、所需交叉零、全部中心对及各自生成／分离。每台旧设备的全输入运输、原接受事件、实际全参考／记录放大和充分标准矩阵锥或已证等价接口，仍是 CP/TNI 与完整测试 TP 的条件；一次比较插入或旧 $Q_a$ 保锥都不供应实际滤器、同效果设备的完整更新、原 AC／精确 $N_u$／Xs、细记录与完整失败。全部分组遗忘、同数双向及逆向返回、顺序／自适应／已供并行的每个合法有限历史仍按原箭头绑定，不由代数商取得任意右接续。保比较保相位的实际可逆过程才进入既有酉桥；物理时钟、Hamiltonian／能量、共同作用量、原控制和独立成功支的共同仪器仍分别需要实际来源。

完整 $B$ 的精确有限正生成和另名 $\mathsf B_{\rm cl}$ 的闭正生成继续分开；比较词的精确复张成不替代任一准备生成。所有经典与不等维量子块、原正权、零／次归一及奇异准备、原质量、设备／端口／全细记录／失败、实际联合和全部历史均保留，同一原 $\sigma$ 和预选 $t_0$ 不改。正交迹续卷定理 419.2 只在其另行表述的完整有限背景、有限谱星及原刻度前件俱全时复用；本定理没有供应它的有限性或有限谱星。完整 CountRead 商依 C139 命题 32.1a 仍无穷维，任何满足本候选的忠实表示也须无穷维；不以有限扩维、切分对象或忘记未来解决它。

**定义 368.2（实际来源仍缺的共同关系）。** 原 passive memory 卷定理 2.1 的 $z_{uy}=P(f_yz_u)$、全词残差商及定理 3.1 的无限 Hankel 秩属于其独立扩散源，不给任意原 $\Omega$ 的旧 $D$、共同 $K/J$ 或旧 $Q$ 保锥；diffusion-phase 卷定义 11.5 的参数／求值界也不供应实际读口。C139 §§36–37 的 terminal $K$、history/future $H$ 与 history Gram $G$ 不混用：全前缀聚合移位表示中的 $G$ 是所选数学记忆，其定理 37.4 的共同接受效果细记录细化仍须全部归一接受记录律相同，原负载事件在真正共同事件域内给条件冲突。这个冲突不排除另设比较实验或依上下文区分输出接口，也不由聚合概率相容性解除。本节没有为实际 CountRead 构造共同 $K/J/D$、旧 $Q$ 稳定性或全部记忆／操作／全未来表示。

## 369. 成熟工具、来源增量与完整白话

**定义 369.1（文献范围及原接口综合）。** 精确伴随关系强制线性的成熟工具直接复用定义 364.3 及 [Frank–Găvruţa–Moslehian，arXiv:math/0501139v6，Lemma 2.2](https://arxiv.org/html/math/0501139v6)：其稠密定义可伴随映射在线性测试配对下成为模线性，处处定义在完备 Hilbert 模时另有有界性。这里从半正定商上的全部配对分离线性缺陷，未提前套用完备模上的有界性部分。(362.8)–(362.10) 的校准及全词传播直接复用仓内证明，引理 366.1 仅补其在撤掉全部正插入时所需的零插入起步。

[Cimprič，*Maximal quadratic modules on $*$-rings*，arXiv:0807.5011v1，§2 定义及 §6 Theorem 5](https://arxiv.org/html/0807.5011v1) 的二次模要求 $rMr^*\subseteq M$ 对整个 $*$-环的全部 $r$ 成立；Theorem 5 另要求复 $*$-代数上的 proper Archimedean 二次模，其 Archimedean 条件量化全部代数元的 $n-rr^*\in M$。本节起初只有原实自伴 $a$ 的 $Q_a$ 保锥，尚未取得结合代数或复夹乘闭性，因此不能把那份完整二次模前件偷偷加回并直接使用其表示结论。实幂的序界、对称算子增长的 Cauchy–Schwarz 论证、有界自伴谱定理及紧区间实多项式逼近均是成熟中间工具；谱定理在 (366.9) 证明有界之后才使用，谱与平方根没有作为来源资料输入。

[Niestegge，arXiv:1402.0158v2，§2(A)–(D)、§5 Definition 1、Theorem 1 及 Corollary 1](https://arxiv.org/html/1402.0158v2#S5) 在其完备序单位及所列乘法／事件背景上，先输入动力对应，再由非负平方得到复 $C^*$ 结构。本节不调用该文消去原来源的旧 $D$ 义务，也不把其已给结论重命名为新增重构。共同正核、一般 Hilbert／GNS 表示、标准复块与三点协方差球，分别复用 §§358–360、364、正交迹续卷 §419 及其准确前件。

本节的 $\texttt{repo-derived}$ 增量是固定原接口上的正性域缩减应用：(366.2) 在缺少正插入时给可见代数的合法起点，(366.1) 将单标签一次原测试与旧锥的 $Q$ 稳定性逐字等同，(366.6)–(366.10) 在未预设复二次模或有界性的条件下覆盖全部原词和跨标签复组合，随后原样消费已有联合采用。命题 367.1 保留其余背景而定位删掉该测试的后果。上述文献中的一般线性、二次模、动力对应或表示定理不是此处的新定理；不主张历史优先权、全域文献不存在性、经验本体或完整量子起源已经完成。

**定义 369.2（完整直观数学描述）。** 白话说，整份原世界及所有过去未来、设备、记录、失败、实际联合和各种质量都仍在原处，旧 Jordan、旧 D、原比较权、同一 sigma 与预选刻度也完全不换；共同正比较、每个原标签的真实读数、全部有向配对关系以及没有词长上限的生成仍是强前提。省下的是必须另对“所有比较配方”检查正插入：现在只要求每个原标签先插入任意一个原实响应，再对任意原正响应检查一次。原单位和有向关系先使零插入不可见，并让两种线性在可见商上成立；所以这个小测试恰好是在说，旧 Jordan 已定义的二次夹乘不能把原正锥推出去。这个锥稳定性并不只是换个名字：原序界约束每个实响应平方，反复夹乘就控制所有幂，内积的 Cauchy–Schwarz 再把逐向量的幂增长压成真正统一的算子界。只有到这时才可用谱定理；若还有负谱，一份实多项式就能从某个单标签一次实插入产生的方向中检出它，违反保锥。因此全部复相位、不同标签的组合及任意长词也都恢复正性，而不是未经证明地从实数跳到复数。若连这一个小测试也删掉，四种裸标签完全认可的响应仍可在一次插入后给负值，说明原读数非负本身不够。恢复正性后直接用已有定理，同一准备、两个插入的三点表仍给由相干、旧 D 方向及质量差组成的三实坐标球，更大的比较网可以无限维；这既不是物理三空间，也不是已造出的量子比特或仪器。等价测试没有扩大模型类，更没有使裸来源自动供应共同 K、插入、有向旧 D 或锥稳定性。完整 CountRead 仍必须留在无限结构中，其实际全未来表示尚未构造；Born 与原对象的条件桥已经复用，但真实联合、全参考与 CP、每台设备的完整更新和细记录失败、分组遗忘及同数返回，以及物理钟、能量、作用量和共同仪器仍各要原来源接口，完整量子起源的目标没有被缩小或宣布完成。

## 追加锚 C128369POS（本行以下为增补区）

## 370. 固定原终端的校准与全部历史边界

**定义 370.1（原被动源及不变信息前件）。** 本节至 §374 全部使用[原词几何卷](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md)假设 1.1–1.3、定义 1.2 和定理 2.2–2.3、3.3、5.3 的同一个源。其分析前件完整保留：原 $G=H^1\times\mathbb R$ 的乘法、原 Haar 测度、单位源 $L\Gamma=\delta_e$、有限正 $a,\eta,d$、原最大定义域的 $A,C$、系数为一的零线、正归一 $h$ 及整个复端点 $A=\rho C$，连同与之不同的 Friedrichs 端点、源迹、保守连续路径和入口 $g_t$。不改用杀死端点或平稳初态，不给 $h(e)$ 赋普通点值。此处历史字 $h$ 与该卷的零态函数 $h$ 不同；下文只在“历史 $h$”这一意义下使用带下标 $h$ 的词算子。

在 $L^2(m;\mathbb C)$ 中保留 $m(G)=1$、第一槽共轭线性的内积、$b=g_d$、$P=T_d=e^{-dK}$、$\ker K=\mathbb C1$，以及逐字原校准

$$
\begin{gathered}
c=\frac1{4(1+\|b\|_\infty)},\qquad
f_3=cb,\quad f_B=\frac14,\quad
f_0=f_1=\frac38-\frac12f_3,\\
F_\varnothing=1,\qquad F_{yu}=M_{f_y}PF_u,\qquad
p(w)=\langle Pb,F_w\rangle_m.
\end{gathered}
\tag{370.1}
$$

第一次读数仍在 $2d$，以后每个间隔仍为 $d$；给定同一路径的读噪声独立，被动读取不改变源。允许原来全部 Borel 零集修补。精确信息前件仍是整个 $p:\mathcal L^*\to[0,1]$，$\mathcal L=\{0,1,3,B\}$；它不是有限记录、逐词认证数值求值器、重启许可、额外时刻或可选择标签结果。

沿用原词几何卷 (2.6) 的实际表示，而不另建核表示：

$$
\begin{gathered}
C_y=P^{1/2}M_{f_y}P^{1/2},\qquad
C_w=C_{w_1}\cdots C_{w_k},\quad C_\varnothing=I,\quad
C_w^*=C_{w^R},\\
\mathcal O=\overline{\operatorname{span}_{\mathbb C}
 \{F_w:w\in\mathcal L^*\}},\qquad
x=C_31=cP^{1/2}b,\qquad y_h=C_h^*x,\qquad
\Pi z=1\langle1,z\rangle_m.
\end{gathered}
\tag{370.2}
$$

这些是同一 $\mathcal O$ 中的向量和其上的限制；$P^{1/2}$ 是谱平方根，不是新采样。原定理 2.2 的等距映射满足 $x=\sqrt c\,U[\varnothing]$，故这里的 $x$ 已由原标记和校准固定。记 $\mathcal W=\{3,B\}^*$。对一条质量正的原历史定义唯一选定的固定终端核

$$
K_h(u,v)=\frac{p(hu^Rv3)}{p(h)}\qquad(u,v\in\mathcal W),
\tag{370.3}
$$

并用相同公式记其在 $\mathcal L^*\times\mathcal L^*$ 上的原词扩展。没有改变终端 3、重缩放某个端点或另选匹配核。

**定理 370.2（原方向、正质量及标记双边式）。** 每个 $h\in\mathcal L^*$ 都有 $p(h)>0$。对全部 $w,h,u,v\in\mathcal L^*$，有

$$
\begin{aligned}
p(w)&=c^{-1}\langle x,C_w1\rangle_m,\qquad
p(hw)=c^{-1}\langle y_h,C_w1\rangle_m,\\
K_h(u,v)&=\frac{\langle C_uy_h,C_vx\rangle_m}{c\,p(h)},\\
\langle1,x\rangle_m&=c,\qquad
\langle y_h,1\rangle_m=c\,p(h),\qquad
p(3)=c\langle b,Pb\rangle_m=c\|g_{3d/2}\|_2^2.
\end{aligned}
\tag{370.4}
$$

特别地，原 $p(3)$ 不是 $c\|b\|_2^2$。所有除法只在上述已证正质量域内进行。

证明。原入口在每个正时刻相对于 $m$ 绝对连续，$b>0$ 几乎处处，且 $\|f_3\|_\infty<1/4$。所以四个原发射函数都几乎处处严格正。任一有限历史在其各原采样时刻给出有限个严格正因子的乘积，其期望严格正。零集修补不改变这些期望；有限时刻的零集并仍为零。这也重述原定理 3.3 所已证明的正质量事实，而非给一般原 $\Omega$ 的零支作除法。

由 $P1=1$ 及原递推归纳，$C_w1=P^{1/2}F_w$。因而

$$
c^{-1}\langle x,C_w1\rangle_m
 =\langle P^{1/2}b,P^{1/2}F_w\rangle_m
 =\langle Pb,F_w\rangle_m=p(w).
$$

这正是原词几何卷 (2.7) 的方向。把 $C_{hw}=C_hC_w$ 移过内积，得到第二式；再取 $w=u^Rv3$，用 $C_31=x$，便得第三式。$\int b\,dm=1$ 给 $\langle1,x\rangle=c$，取空未来给历史质量式。最后 $F_3=cb$，而 $P^{1/2}b=g_{3d/2}$，所以 $p(3)=c\langle Pb,b\rangle=c\|g_{3d/2}\|^2$。初始密度是 $g_{2d}=Pb$，不是 $b$；将它替成 $b$ 才会得到错误的 $c\|b\|^2$。∎

## 371. B 等待尾互易的精确身份与正性判别

**定理 371.1（原概率尾差与预测缺陷）。** 对每条原历史 $h\in\mathcal L^*$ 和每个 $u\in\mathcal L^*$，包括空字，定义

$$
D_n(h,u)=4^n\bigl[p(huB^n3)-p(hB^nu^R3)\bigr].
$$

则在同一原 $c$、同一原时刻和同一终端 3 下，恰有

$$
\boxed{\lim_{n\to\infty}D_n(h,u)
 =c\,[p(hu)-p(h)p(u)].}
\tag{371.1}
$$

特别地，所要求的 $u\in\mathcal W$ 全部在此范围。若 $r_n(z)=\|(P^n-\Pi)z\|_2$，则还有逐对象的精确误差上界

$$
\left|D_n(h,u)-c[p(hu)-p(h)p(u)]\right|
\le\frac{\|y_h\|_2}{c}
 \bigl(\|C_u\|\,r_n(x)+r_n(C_u^*x)\bigr)
 \longrightarrow0.
\tag{371.2}
$$

此式不声称右侧已有有效模数或统一速率。

证明。源谱在 $[0,\infty)$，而零谱空间恰为常数，故 $P^n\to\Pi$ 强收敛；例如对任意 $z$，谱积分 $\int_{(0,\infty)}e^{-2ndk}\,d\sigma_z^K(k)$ 趋零。这里使用成熟的自伴谱定理及有界支配收敛，不预设谱隙。原 $C_B=P/4$ 与 (370.4) 给

$$
D_n(h,u)=c^{-1}\bigl[
 \langle y_h,C_uP^nx\rangle_m
 -\langle y_h,P^nC_u^*x\rangle_m\bigr].
\tag{371.3}
$$

第一项的极限利用 $\Pi x=c1$，等于 $\langle y_h,C_u1\rangle=c\,p(hu)$。第二项利用
$\langle1,C_u^*x\rangle=\langle C_u1,x\rangle=c\,p(u)$，等于 $c\,p(h)p(u)$；这里原词概率为实数，内积的共轭方向没有省略。两项相减给 (371.1)。在 (371.3) 中以 $P^n-\Pi$ 替换两个余项，再分别用 Cauchy–Schwarz 和算子范数界，便得 (371.2)。所有 $C_u$ 都是有限个有界原算子的乘积，无需限制词长。∎

**定义 371.2（唯一的历史互易候选）。** 在定义 370.1 的全部不变源前件及精确全词信息上，对一条给定历史 $h$ 要求二元原概率关系

$$
\mathsf R_h:\quad
p(huB^n3)=p(hB^nu^R3)
\quad(u\in\mathcal W,\ n\ge0).
\tag{371.4}
$$

反转只是词索引 $u^R$，不是物理倒走或同数返回。此候选在全部原历史上同时成立的断言为 $\forall h\in\mathcal L^*\,\mathsf R_h$；下面既给逐历史判别，也判定这一全历史断言。没有将合法历史集合改成仅有满足候选的子集。

**定理 371.3（全部历史、全部词长的等价判别）。** 对每个 $h\in\mathcal L^*$，下列条件等价：

1. $\mathsf R_h$ 成立。
2. 每个 $u\in\mathcal W$ 都有 $\lim_nD_n(h,u)=0$。
3. $K_h$ 在 $\mathcal W$ 上为 Hermitian 核。
4. $K_h$ 满足全部有限复 Gram 正性：对每个有限族 $u_1,\ldots,u_s\in\mathcal W$ 和每个 $z\in\mathbb C^s$，$\sum_{i,j}\bar z_i z_jK_h(u_i,u_j)$ 是非负实数。
5. 原历史边界满足 $y_h=p(h)x$。
6. 历史不改全部原未来律：$p(hv)/p(h)=p(v)$ 对每个 $v\in\mathcal L^*$ 成立。

而且它们都等价于将第 1、3、4 项的测试词域扩到全部 $\mathcal L^*$ 后所得的对应条件。只用 $\mathcal W$ 检验便已足够，不是删除原来的 0、1 历史或未来。条件成立时，指定的条件核恰好等于既有未条件化标记核：

$$
K_h(u,v)=\mathsf G(u,v)=p(u^Rv3)
 =c^{-1}\langle C_ux,C_vx\rangle_m
\quad(u,v\in\mathcal L^*).
\tag{371.5}
$$

在原词几何卷 (3.6) 的固有预测向量中，第 5 项也恰是 $Uz_h=x/c=Uz_\varnothing$。因此正性在此没有产生新的历史态，而是把此特定核的可用范围精确限制为同一未来律的历史。

证明。由定理 371.1，第 2 项等价于 $p(hu)=p(h)p(u)$ 对全部 $u\in\mathcal W$ 成立。由 (370.4)，这等价于

$$
\langle y_h-p(h)x,C_u1\rangle_m=0
\quad(u\in\mathcal W).
\tag{371.6}
$$

原词几何卷 (2.9)–(2.10) 已证明这些 $C_u1$ 的复线性包在同一 $\mathcal O$ 中稠密；其证明使用 $P$ 的单射性及
$C_0=C_1=3C_B/2-C_3/2$，没有有限维前件。$y_h,x\in\mathcal O$，故 (371.6) 当且仅当第 5 项。反向亦由同一配对直接得到。这一步适用于含任意多个 0、1、3、B 的 $h$，因为 $\mathcal O$ 对每个 $C_y$ 约化；未要求 $h\in\mathcal W$。

第 5 项代入 (370.4) 立即给第 6 项；第 6 项取 $v\in\mathcal W$ 又回到 (371.6)。同样代入标记双边式得到 (371.5)，它给全部 $\mathcal L^*$ 上的 Hermitian 性和全部有限复 Gram 正性。此处直接复用原定理 2.2 的实际 Gram 身份；0、1 的线性展开也给相同的全词扩展，不另做 GNS 或选择另一表示。

第 4 项蕴含第 3 项：在任意两个指标上用系数 $(1,t)$ 和 $(1,\mathrm it)$，$t\in\mathbb R$，二次式均为实数迫使两个交叉项互为共轭。第 3 项用于指标 $(u^R,B^n)$；所有原概率为实数，故正好得到 (371.4)，即第 1 项。第 1 项蕴含第 2 项由零差直接成立。由此六项构成闭合推导。全 $\mathcal L^*$ 条件向 $\mathcal W$ 的限制当然成立，反向已由第 5 项及 (371.5) 证明；全部词长和全部有限复组合均在其量词内。

最后由原预测向量公式，$Uz_h=y_h/(cp(h))$，空历史则为 $x/c$，所以两者相等恰是第 5 项。这里不因向量相同而合并档案或给予任意右接续许可，比较的是原本全部合法未来的概率。∎

## 372. 原 B 历史的严格源内障碍及两个有限词

**命题 372.1（无读口信息的 B 仍有严格预测缺陷）。** 在同一原源的每个有限正 $a,\eta,d$ 下，令

$$
\delta=\langle b,P(I-P)b\rangle_m
       =\|g_{3d/2}\|_2^2-\|g_{2d}\|_2^2.
\tag{372.1}
$$

则 $\delta>0$，而

$$
\begin{gathered}
p(B)=\frac14,\qquad
p(B3)=\frac c4\langle b,P^2b\rangle_m
      =\frac c4\|g_{2d}\|_2^2,\\
p(B3)-p(B)p(3)=-\frac c4\delta<0,\qquad
y_B=\frac14Px\ne\frac14x,\\
\lim_n4^n[p(B3B^n3)-p(B^{n+1}33)]
       =-\frac{c^2}4\delta<0.
\end{gathered}
\tag{372.2}
$$

因此全历史候选 $\forall h\,\mathsf R_h$ 在这个原被动源中不成立，且指定 $K_B$ 不为 Hermitian 核，也不满足全有限复 Gram 正性。这不是另造的抽象反模型。

更精确地，以同一原概率定义确定的正整数

$$
n_*:=\min\left\{n\ge1:
4^n[p(B3B^n3)-p(B^{n+1}33)]
                <-\frac{c^2\delta}{8}\right\}.
\tag{372.3}
$$

该集合非空，故 $n_*$ 有限。两个实际原有限字

$$
w_1=B3B^{n_*}3,\qquad w_2=B^{n_*+1}33
\tag{372.4}
$$

都长 $n_*+3$，都从原 $2d$ 开始，终端读数都在 $(n_*+4)d$，且 $p(w_1)<p(w_2)$。它们正是同一个二阶条件表中的非 Hermitian 对子：

$$
K_B(3,B^{n_*})=4p(w_1)
<4p(w_2)=K_B(B^{n_*},3).
\tag{372.5}
$$

证明。先说明严格性而不假设谱隙。原词几何卷定理 5.3 已证明每个 $g_t$ 非常数：若 $g_t=1$，传播及 $T_{t-s}$ 的单射性使所有 $0<s<t$ 也有 $g_s=1$；但在离开 $e$ 的紧支非负连续函数上，源的连续路径给 $\mathbb E_e\varphi(Z_s)\to0$，常数密度却给严格正的 $\int\varphi\,dm$，矛盾。正积分来自源测度离开 $e$ 的局部全支撑。因此 $b$ 的谱测度在 $K$ 的正能量部分有正质量。于是

$$
\delta=\int_{(0,\infty)}e^{-dk}(1-e^{-dk})\,
                    d\sigma_b^K(k)>0.
\tag{372.6}
$$

传播和自伴性给 (372.1) 的两个范数。由 $F_B=1/4$、$F_{B3}=cPb/4$ 及 (370.1)，得到 (372.2) 的前三个概率式。由于 $x=cP^{1/2}b$，其非常数谱部分也非零，故 $Px\ne x$，这给边界失败。定理 371.1 在 $h=B,u=3$ 上给最后的严格负极限，定理 371.3 给相应核障碍。

严格负极限还保证 (372.3) 的集合包含所有充分大的整数；良序性给有限的 $n_*$，而 (372.4) 是两个合法的原字，不是形式差、外来终端或额外实验。原采样第 $j$ 个位置为 $(j+2)d$，直接给其共同终端时刻。(372.5) 用 $p(B)=1/4$ 即得。若记这两个指标的条件矩阵为 $H$，则 $H_{12},H_{21}$ 为不同的实数。系数 $z=(1,\mathrm i)$ 给

$$
z^*Hz=H_{11}+H_{22}+\mathrm i(H_{12}-H_{21})\notin\mathbb R,
\tag{372.7}
$$

所以已在两个实际词指标上失败的是复 Gram 正性所要求的实非负性；不把非 Hermitian 矩阵的某个形式“负特征值”当作证明。∎

**定义 372.2（等待、有效见证和采集界的区别）。** 原词几何卷 (2.13) 的 $N_B=I/4$ 是已经去掉热夹层的发射乘法，原 (2.4) 的 $C_B=P/4$ 则是带同一原传播的词插入。二者都正确，角色不同。B 的概率与隐藏位置无关，所以一次 B 不筛选位置；但是下一次读数已从 $2d$ 推迟到 $3d$。故 $p(B3)/p(B)=c\|g_{2d}\|^2$ 与没有这个前缀时的 $p(3)=c\|g_{3d/2}\|^2$ 严格不同。把 $C_B$ 换成 $I/4$ 会删掉这一个原间隔，不能用来修复 (372.5)。这种失败不涉及破坏性测量：被动源自己仍在演化。

(372.3) 给出确定且有限的数学见证，但没有给 $n_*$ 的数值、从参数名取得的预先词长界、统一收敛模或有限置信采集费用。(371.2) 只在另有其各项的认证上界及衰减控制时才给相应的词长保证。另一方面，若另给每个有限 $p(w)$ 的认证绝对误差求值器，则交错检查各 $n$ 的差是否严格小于零会终止并输出某个有限非 Hermitian 对子；无需先有极限速率，但这使用了新增的数值信息，不是从有限记录中自动获得了求值器，也不保证输出最小的 $n_*$。

[diffusion-phase 卷定理 12.6、定义 12.8](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md#12-the-original-heat-and-source-names-and-the-exact-calibration-needed-by-passive-words)精确限定这一区别：相对于该卷已构造的系数／热源服务，原 $\|g_d\|_\infty$ 的数值名、原校准名、第一读口 $p(3)$ 的数值名和全部有限词求值相互可计算；其等价不供应尚缺的全局上证书。用一个较大热界替换原 $c$ 会改变四标签原律，不能用于此处。原源的一条连续记录中的重复片段也未被证明是从同一个 $2d$ 入口独立重启的圆柱样本；实际重复许可、相关误差、停止规则和概率采集成本仍需各自条件。这里不主张该参数族不可计算或任何物理采集不可能。

## 373. 同一二元判别的三点几何及完整原目标

**推论 373.1（通过判别的历史与既有三点几何）。** 若给定历史 $h$ 满足定理 371.3 的等价条件，则对任意 $u,v\in\mathcal L^*$，其三个指标 $\varnothing,u,v$ 的条件比较表恰是同一个原表

$$
\begin{pmatrix}
p(3)&p(u3)&p(v3)\\
p(u3)&p(u^Ru3)&p(u^Rv3)\\
p(v3)&p(v^Ru3)&p(v^Rv3)
\end{pmatrix}\succeq0.
\tag{373.1}
$$

令 $a=p(3)>0$，并令

$$
\begin{aligned}
A&=p(u^Ru3)-p(u3)^2/a,\\
B&=p(v^Rv3)-p(v3)^2/a,\\
Z&=p(u^Rv3)-p(u3)p(v3)/a.
\end{aligned}
$$

则 $A,B\ge0$、$AB\ge|Z|^2$。对任意两个有限复比较配方亦有相同的中心化 Gram 结论，允许 $Z$ 为复数；$t=A+B>0$ 时

$$
r=\frac{(2\Re Z,-2\Im Z,A-B)}t,\qquad
|r|^2=1-\frac{4(AB-|Z|^2)}{t^2}\le1.
\tag{373.2}
$$

$t=0$ 时两个中心化向量均为零，不赋球坐标。仅取原单词时 $Z$ 为实数，故只占这个球的一个平面截面。对 B 历史，(372.5) 阻止把同样的条件表称作 Gram 表；未条件化表的正性仍保留。

证明。定理 371.3 使 $K_h=\mathsf G$，原定理 2.2 的同一向量 $C_ux/\sqrt c$ 给 (373.1)。从后两个向量中减去沿 $x/\sqrt c$ 的正交投影，中心化二阶 Gram 恰为 $\left(\begin{smallmatrix}A&Z\\\bar Z&B\end{smallmatrix}\right)$。正性给所列不等式；有限复配方只对同一向量作有限复线性组合，论证不变。展开 $|r|^2$ 得 (373.2)。这直接使用定理 359.1、定义 359.2 的成熟 Gram／协方差几何，不把它另称为新的球或有限代数分类；这里新对应的是该表何时真等于原历史的指定条件概率表。B 的排除来自已经给出的实际两个词。∎

**定义 373.2（简化坐标及有限与整体的区别）。** 在固定的原被动源、同一终端和全部精确信息下，定理 371.3 将这个指定核的全部有限复 Gram 正性检验，等价地换成 (371.4) 的二元原概率互易，或换成原边界 $C_h^*x=p(h)x$。检验字域可从四标签缩到 $\mathcal W$，因为另外两标签已有精确线性表达；历史域仍是全部四标签，词长和历史长均无上限。这只比较同一资料上的正性测试域和二元概率关系，不声称完整 C128 的独立前件数、模型类、整体供给、有限认证或物理成本减少。全历史版本两边同样为假，不能以等价表述把原源纳入该候选。

二点表、三点表及三实坐标属于有限截面；全域正性始终量化同一个核的任意有限集合和任意有限复系数。有限多个截面的正性不替代这个无上限量词，逐对可完成也不保证三个及更多指标共同可完成；直接复用 C139 定义 39.2 的三阶反例。更大的既有对象仍是原 $\mathcal O$、其全部标记词向量和源谱，原词几何卷定理 6.1 已给 $\mathcal O$ 无穷维及它在全 $L^2(m)$ 中的严格子空间边界。本节不重复证明其无限秩，不把三实坐标当物理三空间、实际 $M_2$ 或全源维数，也不新增原相干准备；形式复系数不供应物理相位参照。

**定义 373.3（量子公理的准确条件对应）。** 此指定被动核与共同来源候选的关系逐项如下；表内尚须给出的接口不作为已从裸词律推得的结论。

| 原目标或量子条款 | 此判别实际给出的后果 | 完整原来源仍须供应的条件 |
| --- | --- | --- |
| Hilbert 与 Born | 直接复用原词几何卷定理 2.2 的 $\mathsf G$、$U$ 和 $\mathcal O$；$p(u^Ru3)=\|C_ux\|^2/c$。只有 $y_h=p(h)x$ 时，指定 $K_h$ 才给同一 Gram。 | 标记平方范数不将全部原 $E$、准备和效果自动认作这一词空间的算子／状态。完整 Born 采用仍需本卷 §§357–369 的共同来源接口及其原量词。 |
| 完整状态、效果与原质量 | 原四个 $N_y=M_{f_y}|_{\mathcal O}$ 是既有发射乘法，和为 $I$；全部原词概率及正质量条件化保留。等价条件只识别未来律，不合并原档案。 | 全部原状态／效果菜单、零与次归一及奇异准备、质量和 $q$ 的正确运输仍分别需原身份；一般零质量支不条件化。不等正 $q$ 权不成为 Born 概率权。 |
| 原 Jordan、$L$、字面旧 $D$ | 本判别不改变旧有向关系，也不从实词概率选择其号、尺度或交换子。$C_y$ 的乘积只是原词传播表示。 | 原 $E,u,\circ,L,D$ 的共同插入与有向校准、分离、原锥、序界和全词生成仍按定义 365.1 保留，正性条件沿定理 366.2；未证明本被动源供应那份完整 $\mathsf H$。 |
| 更新、顺序与合法历史 | 原词几何卷定理 3.3 的 $z_h$ 和全部条件未来律仍有效；B 反例显示源演化可使未来改变，不能以要求 $K_h$ 正而删掉它。 | 所有实际旧设备的全输入运输、原 AC／精确 $N_u$／Xs、完整更新和接受归属仍须逐个绑定；同效果不决定更新，指定核失败不否定原条件概率或其他历史表示。 |
| 实际联合与参考、CP | 本节没有从单源词域产生实际张量积、相关输入或标准矩阵层。 | 原联合、积与相关准备、全部中心对、旧乘法／旧 $D$ 保持、所需交叉零、生成／分离，以及实际全参考与充分标准矩阵锥或已证等价接口仍各自保留，才能沿原消费者取得 CP。 |
| 记录、失败与分组遗忘 | 四标签圆柱与全部有限历史原样保留，没有以 Gram 商删去记录或失败。 | C139 §§38–40 的完整细记录正交及无限维结论保持各自共同记录前件；本被动源不是该 CountRead 的全源实现。全部细输出、端口、完整失败、真实分组／遗忘及其未来仍须来源绑定。C139 定理 41.2 的 $\beta,W$ 运输仍需 (41.1)–(41.2)，不由本互易推出。 |
| 同数返回、原刻度与整体生成 | 词反转不执行原双向或逆向返回，$P^{1/2}$ 不增加采样；同一原 $\sigma$ 和预选 $t_0$ 不变。 | 全部具名同数两侧支持返回及同数反向资料继续保留；完整 $B$ 的精确有限正生成与另名 $\mathsf B_{\rm cl}$ 的闭正生成分开，比较词张成不替代它们，数学闭包不增添实际准备。 |
| 酉时间、能量与物理单位 | 既有源谱在其原定义域上仍给 $-\log P=dK$；原 $d$ 已校准时才还原物理生成元。这里的 $P$ 是热收缩，B 确有等待。 | 数学谱演算不把热过程变为实际可逆酉演化；保比较保相位的实际可逆过程、连续钟、Hamiltonian／能量、共同作用量及 $\hbar$、原控制和共同仪器仍需各自来源。 |

完整原 $\Omega$、原类型、所有经典与不等维量子块及原正权、实际联合、相关／积／零／次归一准备及质量、设备／端口／细记录／全部失败、分组遗忘、同数双向及逆向返回和每条原合法有限历史均不删减。有限 C128 消费者只在另行完整供应的有限背景及原刻度前件下采用；C139 命题 32.1a 的完整 CountRead 共同切口仍无穷维，不能以有限扩维、分割共同对象或忘记历史规避。本节不构造它的完整记忆／操作／全未来表示，也不将原被动源的这项严格障碍提升为完整 $\Omega$ 的不可表示结论。

## 374. 原源增量、成熟文献与直观数学说明

**定义 374.1（文献对应与结论范围）。** 定理 371.1 所用的谱极限及命题 372.1 所用的严格谱积分是 $\texttt{literature-attested}$ 的成熟工具：[Teschl, *Mathematical Methods in Quantum Mechanics*, §3.1，Theorems 3.1、3.7，(3.18)、(3.21)、(3.49)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)。其有界 Borel 演算把一致有界的逐点收敛变成强收敛；在这里取原 $P$ 的幂，或原 $K$ 上的 $e^{-ndk}$，保留零谱投影，不假设正谱离零有统一距离。极化、稠密配对分离、Cauchy–Schwarz、有限 Gram 的球坐标均是证明内的成熟步骤，不单列为新的表示定理。

[Jorgensen–Neeb–Ólafsson, *Reflection Positive Stochastic Processes Indexed by Lie Groups*, arXiv:1510.07445v3，Proposition 3.7、Lemma 3.16、Theorem 3.27](https://arxiv.org/pdf/1510.07445v3)要求相应的正半群／测度结构；其中空间乘法代数上的循环性强于时间与读口共同循环性。本文只使用既有原词表示，不以这些成熟重构结果补入未供应的全空间字典、原时钟、实际仪器或整个量子来源。

这里的 $\texttt{repo-derived}$ 增量是固定原端点与同一原终端 3 的 (371.1)、逐历史的六项等价，以及严格原 B 缺陷通往 (372.4)–(372.7) 的实际有限词障碍。其身份真源是原词几何卷 (1.6)–(1.7)、(2.7)–(2.10)、定理 2.3、3.3、5.3，特别是原 $2d$ 入口；diffusion-phase (12.26) 独立给同一 $p(3)=c\|g_{3d/2}\|^2$ 校准。本卷 §§357–369 的共同 $K/J$、旧 $D$、可见线性及正性测试域结果，C139 §§38–43 的记录与条件运输，以及原词几何卷的正核实现、全词生成、谱恢复和无限维边界均直接复用，不重计为新增数学。此处不作任意双端终端分类、重缩放匹配核或旧 $D$ 取向的新候选，也不主张一般 GNS、有限复块分类或文献优先权。结论是上述分析前件内的普通数学推导，不主张内核形式化或已完成完整来源采用。

**定义 374.2（完整直观说明）。** 白话说，我们要知道，已经能把原词排成一张正比较表，是否就能在每条真实历史之后仍用同一终端、同一反转规则，把条件概率直接当成同样的内积。需要检查这一点，是因为合法条件概率非负，并不保证把它们摆进这种交叉表后仍能作为内积。原 B 标签本身像一次与位置无关的四分之一抽签，却仍让源向前走了一个原时间间隔；因此它不透露位置，也不把源送回初始时刻。把同一个长 B 等待尾分别放在字的两侧，等待极限只保留常数方向，两边的差恰好留下这条历史改变未来预测的程度，连前面的常数都是原读口给出的那个 c。于是这种指定表能否互易、能否 Hermitian、能否对所有有限复组合保持正性，恰好都在问：这条历史后的全部原未来律是否仍与没有前缀时完全相同。答案不能靠裸概率非负来保证；原 B 历史已经让下一次读到 3 的概率严格降低，因而必有两条真正有限、长度相同、终端时刻也相同的原词给出不相等的交叉值，不能成为 Hermitian 内积表。有限词的存在已被证明，但没有因此得到可采集的词长、误差和费用界。通过判别的历史则复用原来那张正表，两个比较方向与共同基点形成三点几何，去掉共同分量后落在熟悉的三实坐标球内；这只是有限关系截面，整张既有源网络仍可无限维，也没有因此造出物理三空间或量子比特。我们没有删掉失败的 B 历史，也没有否定它完全合法的条件未来律，更没有换终端、换原 c、换时刻或另选旧 D；所排除的是这一份直接条件核可以覆盖所有原历史的断言。完整原世界里的状态效果、旧 Jordan 和有向关系、实际联合与相关输入、全参考和每台设备的完整更新、记录和失败、分组遗忘与同数返回、同一 sigma 和预选刻度，以及物理钟、能量、作用量和共同仪器仍全部保留，仍须各自的同源桥梁，完整量子起源目标因而没有被缩小或宣布完成。

## 追加锚 C128374TAIL（本行以下为增补区）

## 375. 同一原前缀乘法上的实际历史正状态候选

**定义 375.1（不换来源、乘法或未来字典）。** 沿用定义 370.1 的全部分析及精确信息前件，特别是原群乘法、Haar 测度、单位源、完整复端点 $A=\rho C$、原 $a,\eta,d>0$、$m=h^2\mu$、$e$ 起点、$2d$ 首读、$d$ 间隔、同一个 $b=g_d$ 和原校准 $c$。所有四标签 $\mathcal L=\{0,1,3,B\}$、所有合法有限历史及所有有限未来字均保留。历史下标 $h$ 仍不表示零态函数。直接使用原词几何卷定理 2.2–2.3、3.3 的同一 $\mathcal O,U,1,P,C_y$，不再构造 Hilbert 表示。记其已有前缀算子的代数及范数闭包为

$$
\begin{gathered}
\mathscr C_0=\operatorname{span}_{\mathbb C}\{C_w|_{\mathcal O}:w\in\mathcal L^*\},\qquad
\mathscr C=\overline{\mathscr C_0}^{\|\cdot\|},\\
C_{uv}=C_uC_v,\quad C_w^*=C_{w^R},\quad
C_B=P/4,\quad \sum_{y\in\mathcal L}C_y=P,\quad P1=1,\\
z_h=\frac{C_h^*x}{c\,p(h)},\qquad x=C_31=cP^{1/2}b,\qquad
R_h(w)=\frac{p(hw)}{p(h)}=\langle z_h,C_w1\rangle_m.
\end{gathered}
\tag{375.1}
$$

这里每个 $p(h)>0$，$z_h\in\mathcal O$，且 $\langle z_h,1\rangle_m=1$。$\mathscr C_0$ 是含幺 $*$-代数；$C_0=C_1=3C_B/2-C_3/2$ 使二标签生成同一代数，但没有删除 0、1 历史或未来。第一槽共轭线性。原词的时间顺序按 (375.1) 固定，伴随反字不执行物理逆时或具名返回。

整条实际未来律已经唯一指定一个有界复线性泛函

$$
\ell_h(T)=\langle z_h,T1\rangle_m\quad(T\in\mathscr C),\qquad
\ell_h(I)=1,\qquad |\ell_h(T)|\le\|z_h\|_2\|T\|.
\tag{375.2}
$$

它在 $\mathscr C_0$ 上的良定义来自实际算子和配对，未假定原词自由无关系。任何在 $\mathscr C$ 上逐字给出 $R_h(w)$ 的有界泛函都必须等于它。唯一待判的直接绑定候选为

$$
\mathsf S_h:\quad \ell_h(T^*T)\in[0,\infty)
\quad\text{对全部 }T\in\mathscr C_0.
\tag{375.3}
$$

这是在**同一前缀乘法**上要求正归一泛函，不是要求各合法圆柱概率非负，也不是要求定义 370.1 的固定终端核 $K_h$ 正。其二元比较是 $\ell_h(S^*T)$，候选量化任意有限复配方平方。$C_y$ 是带热传播的前缀，不是去掉夹层的发射 $N_y=M_{f_y}$；特别不能把 $C_B$ 换成 $N_B=I/4$。一般 $C_w$ 也不是自伴效果。实际未来仍由原 $F_w$ 和实际后密度评价；原 passive memory 卷定理 2.1 的 $\pi_{hy}=P(f_y\pi_h)/R_h(y)$ 保持原更新和下一读时刻。形式配方 $T$、$T^*T$ 不被宣称为原可执行操作或新增准备。

## 376. 常数边界判别与每条有限 B 历史的正平方障碍

**定理 376.1（同一原源的精确直接绑定边界）。** 在定义 375.1 的全部前件下，对每条 $h\in\mathcal L^*$，下列五项等价：

1. $\mathsf S_h$ 成立；等价地，存在 $\mathscr C$ 上的正归一泛函 $\omega_h$，对每个原未来字满足 $\omega_h(C_w)=R_h(w)$。
2. $\ell_h$ 在 $\mathscr C_0$ 上为 Hermitian，即 $\ell_h(T^*)=\overline{\ell_h(T)}$。
3. 原二元等待关系 $p(hBw)=p(hw)/4$ 对每个 $w\in\mathcal L^*$ 成立。
4. $z_h=1$，即 $C_h^*x=c\,p(h)1$。
5. 全部条件未来律等于同一常数比较律

$$
R_h(w)=q_*(w),\qquad
q_*(w):=\langle1,C_w1\rangle_m
       =\lim_{n\to\infty}4^np(B^nw)
\quad(w\in\mathcal L^*).
\tag{376.1}
$$

第 3 项只在 $\mathcal W=\{3,B\}^*$ 上检验也等价。成立时唯一的态为 $\omega_h(T)=\langle1,T1\rangle_m$。常数向量和 $q_*$ 是同一原表示中的数学比较对象，不是已供应的平稳准备、重启或无限等待操作。

但在这个原源的每个有限正 $a,\eta,d$ 下，$\mathsf S_{B^r}$ 对每个整数 $r\ge0$ 都失败，$B^0=\varnothing$。这个失败有有限原词正平方见证。精确定义

$$
\begin{gathered}
R_r(w)=4^rp(B^rw),\qquad
\Delta_r=R_r(3)-4R_r(B3),\qquad a_r=R_r(33),\\
D_0=I-P=I-4C_B,\qquad S=C_3,\qquad
\tau_r=\Delta_r/(2a_r),\qquad A_r=D_0-\tau_rS.
\end{gathered}
\tag{376.2}
$$

这里 $D_0$ 是数学等待缺陷，**不是字面旧关系 $D$**。则 $\Delta_r,a_r,\tau_r>0$，$A_r=A_r^*\in\mathscr C_0$，而

$$
\boxed{\ell_{B^r}(A_r^*A_r)=-\frac{\Delta_r^2}{4a_r}<0.}
\tag{376.3}
$$

证明。先判定等价条件。正平方性蕴含 Hermitian 性，不需要 GNS：对自伴 $H\in\mathscr C_0$，恒等式 $4H=(H+I)^2-(H-I)^2$ 使 $\ell_h(H)$ 为实数；将任意 $T$ 分成两个自伴实、虚部即可。因此第 1 项蕴含第 2 项。

令 $D_0=I-P$。由 $D_01=0$，每个 $T\in\mathscr C_0$ 都有 $\ell_h(TD_0)=0$。若第 2 项成立，取伴随也给

$$
0=\ell_h(D_0T)=\langle (I-P)z_h,T1\rangle_m
\quad(T\in\mathscr C_0).
\tag{376.4}
$$

原词几何卷 (2.10) 已证明 $\{C_w1:w\in\mathcal W\}$ 的复线性包在同一 $\mathcal O$ 中稠密，故 $(I-P)z_h=0$。原 $\ker K=\mathbb C1$ 与 $P=e^{-dK}$ 的谱演算给 $\ker(I-P)=\mathbb C1$；归一式遂强制 $z_h=1$。这证明第 2 项蕴含第 4 项，并明确用到了可见全词循环性及原固定空间，而非对所有有界算子的分类。

另一方面，(375.1) 直接给

$$
R_h(w)-4R_h(Bw)
 =\langle(I-P)z_h,C_w1\rangle_m.
\tag{376.5}
$$

同一稠密性使第 3 项与第 4 项等价，也证明只检验 $\mathcal W$ 已足够。若 $z_h=1$，$\ell_h(T^*T)=\|T1\|_2^2$，故它在 $\mathscr C$ 上就是正归一向量态，逐字给第 5 项。反过来，第 5 项及同一稠密性使 $z_h-1=0$。

为核对 (376.1) 的极限和原源身份，$p(B^n)=4^{-n}$，而

$$
z_{B^n}=P^{n+1/2}b=g_{(n+3/2)d}.
\tag{376.6}
$$

原 $P^n\to\Pi$ 强收敛及 $\int b\,dm=1$ 给 $z_{B^n}\to1$，与每个固定的 $C_w1$ 配对即得极限。没有速率或统一词长界被使用。$q_*$ 在每个有限长度归一，因为 $\sum_{|w|=k}C_w=P^k$ 且 $P1=1$；左右边缘一致性同样由 $P1=1$ 及自伴性给出。它是同一原热过程的平稳比较律，不改变实际 $e$ 入口。由范数稠密性，任何给出相同全部字值的态都只能是 (375.2)，所以不存在另一个正归一泛函可以在此代数上补救同一字典。

再证有限障碍。式 (376.6) 及 $x=cP^{1/2}b$ 给

$$
\begin{aligned}
\Delta_r
 &=c\langle b,P^{r+1}(I-P)b\rangle_m\\
 &=c\bigl(\|g_{(r+3)d/2}\|_2^2
             -\|g_{(r+4)d/2}\|_2^2\bigr)\\
 &=c\int_{(0,\infty)}e^{-(r+1)dk}(1-e^{-dk})\,
                      d\sigma_b^K(k)>0.
\end{aligned}
\tag{376.7}
$$

最后的严格性直接沿用命题 372.1 所用的原源事实：原词几何卷定理 5.3 证明 $b=g_d$ 非常数，故其正能量谱质量非零；被积因子在每个 $k>0$ 严格正，任意有限 $r$ 都保留严格正积分。不要求谱隙。$a_r>0$ 则由原合法字 $B^r33$ 的正概率给出。

以 $\ell=\ell_{B^r}$ 简记，$D_01=0$ 和 (376.5) 给出完全源内的二元表

$$
\begin{pmatrix}
\ell(D_0^*D_0)&\ell(D_0^*S)\\
\ell(S^*D_0)&\ell(S^*S)
\end{pmatrix}
 =\begin{pmatrix}0&\Delta_r\\0&a_r\end{pmatrix}.
\tag{376.8}
$$

因此展开同一个自伴平方 $A_r^2$，恰有
$\ell(A_r^2)=-\tau_r\Delta_r+\tau_r^2a_r$，代入 (376.2) 即得 (376.3)。它不是从非 Hermitian 矩阵虚构负特征值，而是一个实际正算子平方被指定泛函评价为严格负数。

该平方的逐字评价只用同一条件律在 $\varnothing,B,BB,3,B3,3B,33$ 上的值；其中
$R_r(B)=1/4$、$R_r(BB)=1/16$、$R_r(3B)=R_r(3)/4$。所有这些字接在真实 $B^r$ 历史后，均为原合法字。形式负系数和原精确概率所定义的 $\tau_r$ 只用于证明，不供应相干制备、可选择 B 或新仪器。被组合字长不同，故这里不主张同一终端时刻。∎

## 377. 两种边界、删条件后果与有限关系几何

**定义 377.1（不混用入口、常数和实际更新）。** 定理 371.3 对指定 $K_h$ 的条件是 $z_h=z_\varnothing=P^{1/2}b=g_{3d/2}$；定理 376.1 对同一前缀代数上的实际全未来正状态的条件是 $z_h=1$。原入口非常数，故这两个逐历史采用条件在本源上不相交。特别是空历史的 $K_\varnothing=\mathsf G$ 正，但 $\ell_\varnothing$ 已由 (376.3) 排除；既有标记核不是实际历史状态字典的无条件供应。原 terminal 3、$x$、$c$、$2d$ 和核 $K_h$ 均未被替换。

删掉 (375.3) 而只留全部实际圆柱非负、每个长度质量为一和原密度更新，原源本身就是满足其余这些要求却失败的实现；裸概率正性不能代替同一乘法上的正平方性。只检查字尾 B 的 $p(hwB)=p(hw)/4$ 也不够：这在每条历史和每个未来字上自动成立，$B^r$ 却在字首 B 的 $w=3$ 处有严格缺陷 (376.7)。两条关系都是原合法未来比较，差别来自等待位置。只检验若干未来也不能代替定理中的全部词量词；此处未证明一般历史的有限认证定理。严格符号需要原 $f_3=cb$ 及其正能量谱，不能从“任意被动读口”直接声称 (376.7)。

在同一原前端上，定理 376.1 把本候选的全部平方正性等价地定位为一份原等待关系及一个常数边界；(376.3) 又使每条有限 B 历史的否定证据只涉及至多两个未来标签。改善的是这个失败候选的判别和障碍范围，不是总独立输入数、取得费用或全量子公理数。系数由精确全词律定义，不声称从有限记录取得、抗噪认证、参数名计算、统一精度或费用界。原词几何卷 §9 的有限记录载体、ambient residual 及指定条件未来证书仍取其容量／钟、泄漏和分母前件，不变成一个归一的有限全未来态；diffusion-phase §14 的外部衰减与定性局部化也没有提供尚缺的全局上证书或源点模。

**定义 377.2（二元比较与三实坐标的直接复用）。** 若某条实际历史通过判别，对任意 $S,T\in\mathscr C_0$，直接取既有 $\mathcal O$ 中的三个数学向量 $1,S1,T1$。它们的 Gram 是 $[\omega_h(A_i^*A_j)]_{i,j=0}^2\succeq0$，其中 $A_0=I,A_1=S,A_2=T$。去掉沿 $1$ 的共同分量后，记剩余二阶 Gram 为 $\left(\begin{smallmatrix}v_S&Z\\\bar Z&v_T\end{smallmatrix}\right)$。直接复用定义 359.2、推论 373.1 证明中的中心化 Gram 几何：$v_S,v_T\ge0$、$|Z|^2\le v_Sv_T$；$t=v_S+v_T>0$ 时

$$
r=\frac{(2\Re Z,-2\Im Z,v_S-v_T)}t,\qquad |r|\le1.
\tag{377.1}
$$

$t=0$ 时两余向量均零，不赋球坐标；只取实词时虚部为零，形式复配方允许三实坐标。这里不重新分类 Gram 球。对实际 $B^r$，(376.8) 已不是 Hermitian 表，故不能把该历史的指定条件比较送入这个消费者；数学向量 $D_01=0$ 本应与一切方向零配对，而条件字典却给它与 $S$ 的单向值 $\Delta_r$，这就是二元关系的有限几何失败。已有标记 Gram 几何仍有效。大结构仍是原无穷维 $\mathcal O$ 及其全词算子网，未改作有限 EJA、实际 $M_2$ 或物理三空间，复配方也未供应物理相位参照。

## 378. 原公理接口、成熟来源与完整白话

**定义 378.1（条件消费者与保留的完整目标）。** 以下接口直接复用既有结果，不从这个失败候选重推量子公理。

| 目标 | 精确结果及仍需的原来源接口 |
| --- | --- |
| Hilbert、状态效果与 Born | 原词几何卷定理 2.2–2.3 的同一表示和标记平方律保持；376.1 只判定原实际未来能否直接当作 $C_w$ 的正状态。完整原状态／效果及质量的 Born 采用仍需本卷 362–369 的共同 $K,J$、原读数、原锥和序界、分离、精确全词生成及有向式；无此接口，不以常数比较向量代替原准备。 |
| 原 $G/J$、Jordan、$L$、字面旧 $D/q$ | $\mathscr C$ 是原被动前缀算子的乘法，未识别为完整原响应代数，未将其对称积或交换子改名为旧关系。旧 $D$ 的号、尺度及原 $q$ 正权运输仍取定理 364.1、366.2 的全部同源前件；R5-014 的有限双线性乘法／正尺恢复不支付这份全源身份，也不减少总独立数值信息。 |
| 实际更新、设备、记录和失败 | 原 passive memory 定理 2.1 的条件密度及更新保留。C139 §§44–49 的后状态、细记录和真正遗忘消费者仍需同一完整原记录、实际全未来 $\beta$、共同来源比较及 (45.1) 的全域联合正性；该候选已不另要求独立 $W$，这里不重新加回，也不把它重报为本节新关系。终端／聚合质量不替代这些前件，比较平方不成为实际设备。 |
| 实际联合、参考与 CP | 仍须原有序联合、全部乘积及相关输入、同一嵌入和交叉关系、原全参考锥与事件归属；C139 定理 45.2 仅在其实际回溯与共同正比较前件下给 CP。单源词概率或某个前缀压缩不能供应全源 CP、完整输出或副本。 |
| 合法历史、原质量和返回 | 全部设备／端口／细记录／全失败、零及次归一准备与质量、分组遗忘、每条合法有限历史、具名同数双向及逆向返回均保留；零质量不作条件化。比较商和伴随不增加右接续或返回许可。完整 $B$ 的精确有限正生成与 $\mathsf B_{\rm cl}$ 的闭正生成分开，同一原 $\sigma$ 和预选 $t_0$ 不变，数学闭包不变成实际准备。 |
| 酉时间与完整维数 | 原谱仍给样本单位下的 $-\log P=dK$；热收缩不成为实际酉演化。实际可逆保比较／保相位过程、连续钟、Hamiltonian／能量、共同作用量及仪器仍另需来源。有限 C128 仅在另供的有限完整背景采用；完整 CountRead 的无穷响应及 C139 有限固定标量环障碍保持各自范围，不排除一般 QM 或无限表示。 |

完整原 $\Omega$、字面旧 $D/q/L/Jordan$、所有经典与不等维量子块及正权，以及表内全部原资料不删减。此处推进的是一个确切源内失败的直接绑定候选及其边界，不构造完整 CountRead 或全 $\Omega$ 的记忆／操作／全未来表示，不宣称更少完整来源公理或总体量子起源完成。

**定义 378.2（文献与本源增量）。** 正泛函为 Hermitian、零平方方向的配对约束、热谱演算和有限 Gram 几何均为成熟工具；定理 376.1 已在本源上给出所需普通数学证明，不重做 GNS、CP 核、商下降、源密度重构或一般代数分类。原文 [Jorgensen–Neeb–Ólafsson, *Reflection Positive Stochastic Processes Indexed by Lie Groups*, arXiv:1510.07445v3，Proposition 3.7、Lemma 3.16(c)–(f)、Theorem 3.27](https://arxiv.org/html/1510.07445v3) 的正半群及 Markov 概率空间框架使用常数守恒向量，并区分空间乘法循环性与时间／读口共同循环性；它不把本源非平稳入口的全部条件律自动变成前缀代数上的正状态。这里不从其平稳框架添加原准备或反推物理实现。

本节的 $\texttt{repo-derived}$ 应用是 (376.4)–(376.8)：在已经恢复的原前缀乘法和实际全未来字典之间，用原 B 等待、循环性及原单一常数固定空间确定逐历史的精确边界，再由原标记 $f_3=cb$ 给空历史和每条有限 B 历史的有限正平方障碍。原词几何卷 §§1–8 的表示、循环性与未来配对，原 passive memory 的密度更新，本卷 362–374，C139 44–49 和 R5-014 的相应消费者均只按原前件复用。C123／V78 的通用保核下降、Omega phase-gain §§9–10 的完整信道共同恢复纤维，以及 predictive-memory 的各自来源合同不回答这份固定扩散源上的同乘法判别。所查这些位置未给出本应用；不主张全库穷尽或文献优先权。本文为纯纸面普通数学，无 Lean、数学程序、数值／符号计算、枚举、模拟或实验核验声明。

**定义 378.3（完整直观说明）。** 白话说，原来的世界、入口、四个标签、每条过去和未来以及所有失败都留着；我们已经有一套把原词写成算子的真实表示，现在只问，能否把每条历史后的整份未来概率，直接当成这同一套算子乘法上的量子式正状态。概率逐字非负还不够，因为正状态也必须把任何形式配方的平方判为非负。B 像一次不透露位置的四分之一抽签，却确实让原源多走一个时间间隔；在常数方向上，这一步与不等待没有差别，所以等待差的平方在指定配对中为零。如果这份配对真是正状态，零方向就必须与所有未来都零配对；原来全部词能看见的方向足够多，这便强制历史预测向量只能是常数，未来律只能等于同一原源长等待极限给出的平稳比较律。这不是旧固定终端核的条件：旧核要求保留原入口的未来律，而入口本身并不平稳。原源中即使还没有读任何标签，或者只读过任意有限个 B，下一次读到 3 的概率仍会因再等一步而严格下降；只用至多两个未来标签，便能把这个下降放进一个形式自伴配方，使其平方得到严格负值。因此失败的是“直接把当前全未来字典当成同乘法正状态”这一步，合法概率和原实际密度更新都没有被否定，也没有换终端、校准、入口或旧 D。通过条件时，同一常数向量和两个比较方向仍能复用三点 Gram 与三实坐标球的有限图景；失败时连所需的 Hermitian 配对都不成立，不能靠画球补上。常数向量、长等待极限和比较平方都只是证明对象，没有变成可制备平稳态、新仪器或可调用相干操作；也没有给出速率、采集词长或费用界。整个网络仍可无穷维，完整原 G/J 与旧有向关系、Born 状态效果的同源采用、实际联合和相关输入、全参考与 CP、每台设备的完整更新和细记录失败、真正遗忘与同数返回，以及同一 sigma、预选刻度、物理钟、能量、作用量和共同仪器仍须各自的来源桥梁；这些缺口仍然开放，完整量子起源目标保持不变。

## 追加锚 C128378STATE（本行以下为增补区）

## 379. 用全部原标签的质量上界检验单位

**定义 379.1（保留原 Jordan 单位的缩减背景）。** 固定定义 357.1、362.1、365.1 的同一完整原切口、全部原响应 $E$、原单位 $u$、全部原实线性评价 $\mathcal P$、原对称双线性 Jordan 乘法 $\circ$、$L_a b=a\circ b$ 和字面旧实双线性 $D$；已给的原 $q$ 原样保留。原评价仍分离整个 $E$，决定原锥 $E_+=\{c:\alpha(c)\ge0\ (\alpha\in\mathcal P)\}$；每个原响应仍有原序单位界，且 $\alpha(u)=m_\alpha\in[0,\infty)$。保留 $u\circ a=a$，但不要求 $D(a,u)=0$，也不要求全域单位配对 $K(z,J_u w)=K(z,w)$。

同一个复比较配方空间 $V$、共同半正定 Hermitian 形式 $K$、全部原标签 $\xi_\alpha$ 和每个处处定义的集合映射 $J_a:V\to V$ 保持原义。$K$ 第一槽共轭线性，包含全部有限复系数 Gram 正性；不同原标签不因比较相同而合并。保留原校准、完整有向式及精确全词生成：

$$
\begin{aligned}
K(\xi_\alpha,J_a\xi_\alpha)&=\alpha(a),\\
K(J_a z,J_b w)&=K(z,J_{a\circ b}w)
                  -\mathrm iK(z,J_{D(a,b)}w),\\
V&=\operatorname{span}_{\mathbb C}
 \{J_{a_1}\cdots J_{a_n}\xi_\alpha:
 n\ge0,\ a_j\in E,\ \alpha\in\mathcal P\}.
\end{aligned}
\tag{379.1}
$$

前两行分别量化全部原 $\alpha,a$ 和全部 $a,b,z,w$；最后一行先作原总映射的实际复合，再取有限复线性包，含零长度词而无统一词长上限。记这份背景为 $\mathsf H_{\rm red}$。它正是定义 365.1 的 $\mathsf H$ 撤去上述两项单位要求后的资料，没有撤去原 Jordan 单位。没有预设可见线性、$J_0=0$、$J_u=I_V$、零方向稳定、伴随、$D$ 交替、有界性、完成或谱。

**定义 379.2（标签质量条件与完整候选）。** 在 $\mathsf H_{\rm red}$ 上只加下面的质量上界作为单位配对的替代：

$$
\mathsf M_{\rm lab}:\qquad
K(\xi_\alpha,\xi_\alpha)\le\alpha(u)=m_\alpha
\quad(\alpha\in\mathcal P).
\tag{379.2}
$$

其测试对象是全部原标签，不包含标签插入后的词或任意配方对。它不把原质量归一为一，不排除零、次归一或不同中心的质量。完整候选为 $\mathsf H_{\rm red}+\mathsf M_{\rm lab}+\mathsf P_{\rm one}$，其中仍是定义 365.1 的同一一次测试

$$
\mathsf P_{\rm one}:\qquad
K(J_a\xi_\alpha,J_c(J_a\xi_\alpha))\ge0
\quad(a\in E,\ c\in E_+,\ \alpha\in\mathcal P).
\tag{379.3}
$$

$J$ 不是实际设备，配方线性包不是实际准备；原正锥、共同 $K$、原标签、全部有向式和这些测试的同源解释仍须来源供应。该候选不预设有限维数或独立复二次模；这些资料没有供应原谱／平方根、物理相位参照、环境、时钟或参考。共同复比较及其标记方向仍是输入。

## 380. 标签质量恢复全域单位和旧 D 的两侧单位

**定理 380.1（同一原资料的单位恢复）。** 单独的 $\mathsf H_{\rm red}$ 已给出 $D(a,a)=0$、$D(a,b)=-D(b,a)$、$J_0z\in N$，以及每个原标签的精确缺陷式

$$
\begin{gathered}
N=\{z:K(z,z)=0\},\qquad
K(J_u\xi_\alpha,J_u\xi_\alpha)=m_\alpha,\\
K(J_u\xi_\alpha-\xi_\alpha,J_u\xi_\alpha-\xi_\alpha)
 =K(\xi_\alpha,\xi_\alpha)-m_\alpha\ge0.
\end{gathered}
\tag{380.1}
$$

再加 $\mathsf M_{\rm lab}$ 就有

$$
\boxed{\begin{gathered}
K(\xi_\alpha,\xi_\alpha)=m_\alpha,\qquad
J_u\xi_\alpha-\xi_\alpha\in N,\\
D(a,u)=D(u,a)=0,\qquad J_u w-w\in N,\\
K(z,J_u w)=K(z,w)\quad(z,w\in V).
\end{gathered}}
\tag{380.2}
$$

这些结论不使用 $\mathsf P_{\rm one}$、正插入提升、序单位有界性或任何已下降的插入线性；原 $J$ 在 $N$ 中仍可非线性。

证明。半正定 Hermitian 形式的 Cauchy–Schwarz 使 $N$ 成为与整个 $V$ 配对为零的线性子空间。先在 (379.1) 的有向式取 $z=w=\xi_\alpha$、$b=a$，用原校准得到

$$
K(J_a\xi_\alpha,J_a\xi_\alpha)
 =\alpha(a\circ a)-\mathrm i\alpha(D(a,a)).
\tag{380.3}
$$

左端为实数，两项原评价也均为实数，故全部 $\alpha(D(a,a))=0$。原全域分离给 $D(a,a)=0$，原双线性在 $a+b$ 处极化便给交替性。这一步既不需要单位配对，也未将对角为零预先放进 $D$。

接着证明 $J_0$ 在整个 $V$ 上不可见，不能仅在标签上证明后直接外推。原双线性使有向式在 $a=0$ 时成为

$$
K(J_0z,J_b w)=(1-\mathrm i)K(z,J_0w)
\quad(b\in E,\ z,w\in V).
\tag{380.4}
$$

令 $S=\{v\in V:K(v,J_0w)=0\ \text{对全部 }w\in V\}$，这是线性子空间。原零响应校准和 (380.4) 在 $b=0,z=w=\xi_\alpha$ 给 $K(J_0\xi_\alpha,J_0\xi_\alpha)=0$。因此 $J_0\xi_\alpha\in N$；再在 (380.4) 取 $b=0,z=\xi_\alpha$、任意 $w$，可得 $\xi_\alpha\in S$。

若 $v\in S$，则 (380.4) 在 $b=0,z=w=v$ 给 $J_0v\in N$。对任意 $z,b$，同式于是给 $K(J_0z,J_bv)=(1-\mathrm i)K(z,J_0v)=0$；取共轭即得 $J_bv\in S$。所以 $S$ 包含所有原标签并在每个原总映射 $J_b$ 下稳定，因而包含每个有限原词。精确全词生成强制 $S=V$，遂有 $J_0v\in N$ 对全部 $v$ 成立。此处未用 $J$ 的可加性，也未把 $J_0$ 当作原零映射。

回到 (380.3) 取 $a=u$，由 $u\circ u=u$ 及刚证的 $D(u,u)=0$，得到 $\|J_u\xi_\alpha\|_K^2=m_\alpha$。原校准另给 $K(\xi_\alpha,J_u\xi_\alpha)=m_\alpha$；展开半正定平方即为 (380.1)。故原关系已经强制 $K(\xi_\alpha,\xi_\alpha)\ge m_\alpha$。质量上界恰使缺陷平方为零，得到 (380.2) 第一行。这也覆盖 $m_\alpha=0$：此时两个向量均属 $N$，全过程没有除以质量。

现在只在这些已恢复单位的原标签上使用有向式。对任意 $a,\alpha$，有

$$
\begin{aligned}
\alpha(a)
 &=K(J_a\xi_\alpha,\xi_\alpha)
  =K(J_a\xi_\alpha,J_u\xi_\alpha)\\
 &=\alpha(a\circ u)-\mathrm i\alpha(D(a,u))
  =\alpha(a)-\mathrm i\alpha(D(a,u)).
\end{aligned}
\tag{380.5}
$$

第一等式用 Hermitian 性及原实评价，第二等式只用标签单位缺陷属于 $N$。全部原评价分离遂给 $D(a,u)=0$，交替性再给 $D(u,a)=0$；没有先用全域单位配对来证明它们。

最后才恢复全域单位。将 $D(u,a)=0$、$u\circ a=a$ 和 $J_0w\in N$ 代入有向式，得到

$$
K(J_uz-z,J_aw)=0
\quad(a\in E,\ z,w\in V).
\tag{380.6}
$$

固定 $z$，其单位缺陷与每个非空原词正交，因为这样的词属于某个 $J_a(V)$。取 $a=u,w=\xi_\alpha$，再用已证的标签单位，(380.6) 也使它与每个零长度词 $\xi_\alpha$ 正交。精确全词生成遂使 $J_uz-z$ 与整个 $V$ 正交，故属于 $N$。取 Hermitian 共轭即为 (380.2) 的全域单位配对。这里没有把原非线性插入的单位缺陷从标签作线性延拓，而是用全部原词检验同一缺陷。∎

**推论 380.2（合法进入既有联合采用）。** 完整候选 $\mathsf H_{\rm red}+\mathsf M_{\rm lab}+\mathsf P_{\rm one}$ 满足定义 365.1 的全部 $\mathsf H+\mathsf P_{\rm one}$，因此直接取得定理 366.2、推论 364.1 和定理 358.1 的全部结论。

证明。定理 380.1 已在不依赖这些消费者的条件下恢复唯一缺少的两项：字面旧 $D$ 的右单位和原全域单位配对。其余背景逐项未变，故先由引理 366.1 取得可见代数，再由定理 366.2 取得全配方正性及有界性，随后使用原联合采用。$H,F,\pi$、原序单位范数、同一 Born 配对、准确质量和同号同尺度旧 $D$ 均是这些既有结论，不另作一般表示证明。特别地，$E_{\mathbb C}$ 的旧乘法仍为 $a\cdot b=a\circ b-\mathrm iD(a,b)$，其算子闭包仍是 $\mathcal A$；只有原 $E$ 在原序单位范数下完备时才有 $\pi(E)=\mathcal A_{\rm sa}$。比较空间的数学完成不补这个原完备性。∎

## 381. 保留旧单位时右单位可无替代地删除

**命题 381.1（无需质量替代的单项删除）。** 在 $\mathsf H_{\rm red}$ 上若仍保留旧全域单位配对 $\mathsf U:K(z,J_u w)=K(z,w)$，则不加任何替代条件也必有 $D(a,u)=D(u,a)=0$ 和 $K(\xi_\alpha,\xi_\alpha)=m_\alpha$。这项结论只用共同半正定比较、原校准、原评价分离、原双线性、有向式和 Jordan 单位；不需全词生成、序界或 $\mathsf P_{\rm one}$。

证明。$\mathsf U$ 使 $J_uw-w\in N$。在原标签上，$K(\xi_\alpha,\xi_\alpha)=K(\xi_\alpha,J_u\xi_\alpha)=m_\alpha$。式 (380.3) 的对角实数论证及分离性仍给 $D$ 交替；式 (380.5) 逐字适用，遂给右单位和左单位。该证明不使用定理 380.1 中借生成恢复单位的步骤，因而没有循环地用被删右单位取得伴随。∎

**推论 381.2（同一资料类上的准确等价）。** 在同一个 $\mathsf H_{\rm red}$ 上，$\mathsf M_{\rm lab}$ 与 $\mathsf U$ 等价；并且

$$
\mathsf H_{\rm red}+\mathsf M_{\rm lab}+\mathsf P_{\rm one}
\quad\Longleftrightarrow\quad
\mathsf H+\mathsf P_{\rm one}.
\tag{381.1}
$$

证明。正向由定理 380.1；反向由命题 381.1 的准确质量。原 $\mathsf H$ 恰比 $\mathsf H_{\rm red}$ 多 $\mathsf U$ 与 $D(a,u)=0$，后者由前者已强制，故 (381.1) 两向均成立。∎

**定义 381.3（减少的独立检查与保留的关系）。** 无替代删除的是原先单列的 $D(a,u)=0$；另把全 $V\times V$ 的单位配对要求改为全部原标签的质量上界，由原校准、有向式和全词生成恢复它。质量上界在这份背景中不是一个宽松误差条件：由 (380.1)，它恰使单位缺陷饱和为零。全词、有向式的全域量词及共同 $K$ 的全部有限正性均保留，因此这不是有限认证或完整来源总信息量下降的结论。新旧完整资料类相同，不称严格模型扩张、总物理前提更弱或全局最小。两种可见线性和 $\mathsf P_{\rm one}$ 到全配方正性的提升已分别属于 §§362、366，不再次计为此处新增删除。

## 382. 质量和生成不能同时省略

**命题 382.1（既有单位见证的两个准确删条件用途）。** 只删 $\mathsf M_{\rm lab}$ 时，$\mathsf H_{\rm red}+\mathsf P_{\rm one}$ 不保证全域单位或标签质量。保留 $\mathsf M_{\rm lab}$ 而只删精确全词生成时，其余条件也不保证全域单位。两项均可用命题 359.4 第一项的同一抽象接口见证核对，无需改变 $D$、原锥或校准。

证明。取该见证的 $E=\mathbb R$、$u=1$、通常乘法与序、$D=0$，将原评价族保留为全部 $\alpha_m(a)=ma$、$m\ge0$。其原质量为 $m$，评价分离整个 $E$ 并决定通常正锥；每个 $a$ 有 $-|a|u\le a\le|a|u$，Jordan 单位和旧 $D$ 两侧单位均成立。若保留 $q$，可取 $q(a,b)=ab$，正定且有 Frobenius 性。对 $\epsilon\in\{0,1\}$，在同一个 $V=\mathbb C^2$、通常正定内积上取

$$
\xi_m^{\epsilon}=(\sqrt m,\epsilon),\qquad
J_a=\operatorname{diag}(a,0).
\tag{382.1}
$$

$J_a$ 均处处定义，且这里甚至原本线性；不以此作为一般候选的前件。全部原校准成立，因为 $K(\xi_m^{\epsilon},J_a\xi_m^{\epsilon})=ma$。对所有 $z,w,a,b$，两边有向式同为 $ab\bar z_1w_1$，因为 $a\circ b=ab$、$D=0$、$J_0=0$；对所有 $c\ge0$，全配方正性为 $K(z,J_cz)=c|z_1|^2\ge0$。故 (379.3) 也成立，且其准确值为 $ca^2m\ge0$。共同 $K$ 正定，全部有限 Gram 正性没有缺项。零质量和任意次归一质量均在此同一评价族内。

当 $\epsilon=1$ 时，零长度标签 $\xi_0=(0,1)$、$\xi_1=(1,1)$ 已张成整个 $V$，所以精确全词生成成立。标签平方范数却为 $m+1$，质量上界恰好失败；$J_u=\operatorname{diag}(1,0)$ 在第二坐标不恒等。具体地，$K((0,1),J_u(0,1))=0\ne1$。这正是命题 359.4 的缺质量方向，现将同一个构造中的零与全部质量逐项保留；它没有删去任何其他 $\mathsf H_{\rm red}$ 条件。

当 $\epsilon=0$ 时，全部标签质量恰为 $m$，所以 $\mathsf M_{\rm lab}$ 成立。所有标签及其任意长插入词恰好只张成第一坐标轴，精确生成恰好失败；第二坐标仍给上述单位配对失败。其余校准、正性、序界、分离及全部有向式均已在共同计算中核对，故这只定位生成的作用。命题 363.2 原先针对可见响应线性，不能不加核对地拿来宣称它也反驳单位恢复；此处明确使用 (382.1) 的零第二分量作用。

以上是抽象来源接口模型，不是实际 $\Omega$、CountRead、原被动源或其完整设备／历史的替代实现；只证明所述接口条件的逻辑边界。主定理仍保留完整原域和精确全词生成，不以这两个有限见证截断原目标。∎

**命题 382.2（无限与不可见非线性不被质量条件排除）。** 命题 363.1 的同一无限非交换实例满足完整候选；因此定理 380.1 不要求原 $J$ 在 $V$ 上线性或保零，也不要求 $J_u=I_V$。

证明。直接复用命题 363.1 的全部资料：含经典、二阶和三阶块的可数乘积、所有正迹类评价及零标签、原正 $q$ 权、$V=W_0\oplus\mathbb C$、只读第一坐标的 $K$ 及其给定非线性总插入。该命题已核对原单位配对、校准、完整有向式、精确生成和全配方正性；原单位与校准给每个标签 $K(\xi_\alpha,\xi_\alpha)=m_\alpha$，故满足 $\mathsf M_{\rm lab}$ 和 $\mathsf P_{\rm one}$。其 $J_u(0,0)=(0,1)$ 等原缺陷仍在 $N$ 中，不被改写为零映射。这里只证明候选与这些特征相容，不构造实际原源。∎

## 383. 二元单位缺陷、第三标签与完整量子对应

**定义 383.1（原质量固定的有限比较几何）。** 在 $\mathsf H_{\rm red}$ 上，两个比较标签 $\xi_\alpha,J_u\xi_\alpha$ 的表由 (380.1) 恰为

$$
\begin{pmatrix}n_\alpha&m_\alpha\\m_\alpha&m_\alpha\end{pmatrix},
\qquad n_\alpha=K(\xi_\alpha,\xi_\alpha).
\tag{383.1}
$$

其单位差的平方正是 $n_\alpha-m_\alpha$；$\mathsf M_{\rm lab}$ 把这份二元关系钉到两标签具有同一可见像。加入第三个比较标签 $J_a\xi_\alpha$ 后，它与前两个标签的配对必须相同；式 (380.5) 正是把这一同一性带回字面旧 $D(a,u)$。$m_\alpha=0$ 时整项通过零平方处理，不从秩一图景除以零。这里描述的是原质量对单位的约束，不以两点正性替代整个共同 $K$。

在完整候选下，单位恢复后同一 $\alpha$ 和两个任意原响应 $a,b$ 的三个标签 $\xi_\alpha,J_a\xi_\alpha,J_b\xi_\alpha$ 直接复用定理 359.1 的完整 Gram (359.1)，不再另证一般三点不等式。$m=m_\alpha>0$ 时，去掉共同标签方向的二阶表仍是

$$
\begin{pmatrix}v_a&c-\mathrm id\\c+\mathrm id&v_b\end{pmatrix}\succeq0,
\quad
\begin{gathered}
v_a=\alpha(a\circ a)-\alpha(a)^2/m,\quad
v_b=\alpha(b\circ b)-\alpha(b)^2/m,\\
c=\alpha(a\circ b)-\alpha(a)\alpha(b)/m,\quad
d=\alpha(D(a,b)).
\end{gathered}
\tag{383.2}
$$

因此沿定义 359.2，$t=v_a+v_b>0$ 时仍有 $r=(2c,2d,v_a-v_b)/t$、$|r|\le1$；$t=0$ 只给零表，$m=0$ 时三个可见向量全为零。二元比较的三实坐标不是物理三维、实际量子比特或整个响应商的维数。更多比较标签必须同时来自这一份全有限正 $K$，不能各自任选两点表；更大结构仍为推论 380.2 的可能无限维 $\mathcal A$、状态与比较网。另已供应的有限复块、原子 Bloch 球及 $\mathbb{CP}^{n-1}$ 角网沿既有消费者，跨中心不新增相干。

**定义 383.2（同一候选的准确消费者及未供应接口）。** 下表只在完整候选及各行另列来源条件下应用原结论，不把比较插入当作原设备。

| 原对象或公理 | 条件后果与仍须给出的原关系 |
| --- | --- |
| 复 Hilbert、原对象与态／效果／Born | 推论 380.2 给忠实保序单位 $\pi$、$\alpha(e)=\langle F\xi_\alpha,\pi(e)F\xi_\alpha\rangle$、$\|F\xi_\alpha\|^2=m_\alpha$。原 $0\le e\le u$ 对应算子效果；只在 $m_\alpha>0$ 时条件化。共同复比较及其原方向仍是输入，向量代表不把原混合准备改成实际纯准备，也不供应预定另一表示的正规性。 |
| 原 Jordan、$L$、字面旧 $D/q$ | 原 $\circ,D$ 分别成为同一 $\pi$ 的反交换子与 $\mathrm i[\pi(a),\pi(b)]/2$；交替及两侧单位先由定理 380.1 给出。SC、导子律、曲率及有限块密度／原正 $q$ 权运输沿 §§358–360；$q$ 权不成为 Born 概率权。原 $G/J$ 字典、固定 native 门／终端与该表示的保标签对应仍须证明。 |
| 实际联合与复合 | 仍需同一实际有序联合的含幺原嵌入保持旧乘法和旧 $D$、所需交叉零、全部中心对、原生成／分离、实际乘积和相关准备。分别有比较表示不等于已给实际联合，任取数学张量积不支付这些条件。 |
| 原过程、全参考与 CP | C139 §§50–53 的原合法 typed 前接、实际后上下文及菜单复合按其原条件供应唯一正次单位 $\beta$；其 §52 的单标签／单位区间测试仍是整张共同过程比较的条件。该来源关系不由 $\mathsf M_{\rm lab}$ 或 $\mathsf P_{\rm one}$ 推出。CP／TNI、完整测试 TP 仍需实际全参考／记录放大、同事件归属和充分矩阵锥或其已证等价入口；不把实际参考保正自动当全部标准矩阵层 CP。 |
| 仪器、细记录与全部输出 | 每台旧设备自己的全输入运输、原 AC、精确 $N_u$、Xs、所需平方根词、原接受归属和完整失败输出仍独立保留；同效果不决定更新，数学 Kraus 标签不替代实际细记录。原相位、环境、完成供给和独立成功支成为共同仪器仍须来源。 |
| 全历史、质量、遗忘与返回 | 全部零／次归一／相关／乘积准备及其原质量，设备／端口／细记录／失败／拒绝／停止／销毁／返回，真正分组遗忘、具名同数两侧返回和同数逆向返回均保留。每条合法有限顺序、自适应和并行历史须按原有类型箭头及接头绑定；零方向商不删除原档案，不增加任意右接续。 |
| 演化、尺度与准备生成 | 实际可逆保比较并保相位过程才接入既有酉桥；连续物理钟、Hamiltonian／能量、共同作用量与 $\hbar$、原控制仍各需来源。同一原 $\sigma$ 和预选 $t_0$ 固定，有限尺度消费者只在完整有限背景应用。精确 $B$ 与闭 $\mathsf B_{\rm cl}$ 分开，比较词的复线性生成不替代任何原正准备生成。 |

完整原 $\Omega$ 和所有原类型均未缩小。C139 命题 32.1a 的完整 CountRead 响应商及其 §53 的原被动全历史 $E_*$ 各自无穷维；若某个这样的完整原商满足本候选，忠实 $\pi$ 和其 Hilbert 载体都必无穷维，沿命题 360.3 的同一单射性论证。它们与 FIB 的89配置来源分开，不以有限扩维、切时刻、改终端或删未来规避。当前候选没有构造实际 CountRead、原被动源或完整 $\Omega$ 的共同 $K/J$、全操作和全未来表示；定理 376.1 对实际前缀乘法直接绑定的源内障碍不因单位条件等价而解除。

## 384. 数学来源与标签质量的直观含义

**定义 384.1（复用范围及原来源增量）。** 半正定形式的零平方方向与全部向量正交、平方展开和全测试配对的分离均是成熟工具，不另立一般正核、GNS、自动线性或 Gram 球定理。核与完成的来源沿定义 361.1；精确伴随强制线性的成熟论证沿定义 364.3 及 [Frank–Găvruţa–Moslehian, *Superstability of adjointable mappings on Hilbert C*-modules*, arXiv:math/0501139v6, Lemma 2.2](https://arxiv.org/html/math/0501139v6)。该引理的完备模有界性不在单位恢复之前使用。[Niestegge, arXiv:1402.0158v2, §5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2#S5) 输入动力对应并另用正平方取得复 $C^*$ 结构；它不供应本候选的原标签、共同 $K/J$ 或质量上界，也不替本节证明旧 $D$ 单位的原校准绑定。

本节的 $\texttt{repo-derived}$ 内容限于固定原接口的单位删除与检查域缩减：(380.4) 在尚无单位配对时以零标签校准及全词生成清除全域 $J_0$，(380.1) 用原质量上界消去标签单位缺陷，(380.5) 以原分离评价恢复字面旧 $D$ 的两侧单位，(380.6) 再以全部原词恢复全域单位。命题 381.1 另给保留旧全域单位时无替代删除右单位的准确结论。可见线性、正性提升、联合采用、$C^*$ 结构、有限块分类及几何均只消费原条目，不计为本节新内容；不作历史优先权或全域文献不存在性的主张。

[FIB 续卷 IV §§285–289](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md#285-原实脉冲的方向交换与对称缺陷) 的两份原脉冲交换子互易只在其原实局部来源类中等价地供应守恒，静态 R5 及尖锐循环不蕴含该动力学绑定；这里不从那些接口取得全原比较或将其内部负平方认作实际原响应。[来源相对序卷定理 4.1、5.1 与定义 6.1](RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_RELATIVE_ORDER.md#4-relative-source-order-at-the-original-deterministic-time) 给原全角度局部源迹控制与局部上证书，不给全局 $N_d=\|g_d\|_\infty$ 的准确归一化或本节的共同 $K/J$。这两条来源路线与本定理各保留原前件，既不充当质量上界的已证供应，也不因这里恢复单位而完成各自尚缺的接口。

**定义 384.2（完整直观数学说明）。** 白话说，整份原世界、所有历史和未来、旧 Jordan、旧 D、原比较权与各种真实质量都留着；同一来源仍须给共同的正比较、原标签的真实读数、全部有向插入关系和无词长上限的生成。这里不再另发“旧 D 遇到整个单位必须为零”的证明书，也把“单位对所有配方都不起作用”改成只问每个原标签：比较平方是否不超过它自己的原总质量。为什么够用？有向关系先在每个标签上迫使旧 D 交替；零响应的校准再借全词生成，排除任何插入词偷偷带出可见的零响应。单位插入后的平方已经等于原质量，因此标签本身多出来的平方恰是单位前后之差的平方；质量上界使这份差为零，连零质量标签也不例外。再加一个任意原响应作第三标签，前两个单位标签与它的比较必须相同，这就让同一旧 D 的右单位和左单位都归零；全部词随后把标签上的单位身份推广到整个比较空间，原插入在看不见的档案方向仍可非线性。若保留旧全域单位，旧 D 右单位本来就由这些原校准强制，不需要另加质量条件。若把质量上界也删掉，多出的平方可躲在不被单位作用的方向；若不保留全词生成，则从未由原标签到达的方向仍可逃过单位检验。恢复单位后直接用已有定理取得同一原对象、保原质量的 Born 配对和有确定号尺度的旧 D；三标签的中心化关系仍落在熟悉的三实坐标球内，更大的网可以无限维。这是独立检查的缩减，新旧完整模型类相同，没有凭空降低总信息或造出实际量子比特。完整 CountRead 与原被动全历史源仍须无限结构，有限89配置源仍是另一来源；真实联合和相关输入、全参考与 CP、每台设备及细记录的完整更新失败、真正遗忘、同数双向与逆向返回，以及物理钟、能量、作用量和共同仪器仍各有原来源义务，原 sigma 与预选刻度也未换。裸原源为何供应这份共同 K/J 和关系仍未由本条件定理解决，完整量子起源的目标保持原范围。

## 追加锚 C128384MASS（本行以下为增补区）

## 385. 不预设方向双线性与乘法单位的原标签二元预算

**定义 385.1（保留原总事件与原关系而撤去结构检查）。** 固定定义 357.1、362.1、365.1 的同一完整原切口、全部原实响应 $E$、原总事件 $u$、全部原实线性评价 $\mathcal P$、原锥及原序单位界，$m_\alpha=\alpha(u)\ge0$；原评价仍分离整个 $E$ 并决定原锥，已供应的原 $q$ 原样保留。保留原来逐字固定的实双线性关系 $S(a,b)=a\circ b$ 以及总映射 $D:E\times E\to E$；入口不要求 $D$ 在任一槽线性，也暂不要求 $S$ 对称、Jordan、结合、$S(u,u)=u$ 或任何左右乘法单位，也不要求 $D$ 交替或两侧单位。$u$ 在入口仅为原总事件与序单位，尚不是由乘法定义的单位；不换用另一份 $S$ 或交换子。

共同复比较空间 $V$、全有限半正定 Hermitian 二元比较 $K$、全部原标签 $\xi_\alpha$、处处定义的集合插入 $J_a$ 及无统一词长上限的精确全词生成保持定义 379.1 的原义。保留原全域校准和同一有向关系

$$
\begin{aligned}
K(\xi_\alpha,J_a\xi_\alpha)&=\alpha(a),\\
K(J_a z,J_b w)&=K(z,J_{S(a,b)}w)
 -\mathrm iK(z,J_{D(a,b)}w),\\
V&=\operatorname{span}_{\mathbb C}
 \{J_{a_1}\cdots J_{a_n}\xi_\alpha:n\ge0\}.
\end{aligned}
\tag{385.1}
$$

第一行遍历全部原 $\alpha,a$，第二行遍历全部原 $a,b,z,w$，第三行保留全部原标签及每个有限实响应词。没有预设 $J$ 的任一种线性、零方向稳定、伴随、$J_0=0$、$J_u=I$、算子有界性、谱或完成。记这份缩减背景为 $\mathsf H_{\rm pair}$。

**定义 385.2（同一对标签的预算与完整候选）。** 单位的新增测试只作用于 $\xi_\alpha,J_u\xi_\alpha$ 这一对原比较标签，要求

$$
\boxed{\mathsf B_u:\qquad
K(\xi_\alpha,\xi_\alpha)+\alpha(S(u,u))
 \le2\alpha(u)\quad(\alpha\in\mathcal P).}
\tag{385.2}
$$

这里第二项是同一个旧实响应 $S(u,u)$ 的原评价，不先把它换成 $\alpha(u)$。完整静态候选为 $\mathsf H_{\rm pair}+\mathsf B_u+\mathsf P_{\rm one}$；$\mathsf P_{\rm one}$ 仍是定义 365.1 的一次实插入测试，量化全部原 $a\in E,c\in E_+,\alpha\in\mathcal P$。旧 $S$ 的实双线性、两个旧关系的原身份、共同复比较及其原方向、原标签、来源校准和全词生成依旧是来源前提；比较插入及形式复组合不被认作实际设备或实际准备。

## 386. 原标签关系恢复方向双线性与乘法单位

**定理 386.1（同一原关系的稀疏单位入口）。** 在 $\mathsf H_{\rm pair}+\mathsf B_u$ 下，同一个旧 $S,D$ 和同一个 $K,J$ 满足

$$
\begin{gathered}
S(a,b)=S(b,a),\qquad D(a,b)=-D(b,a),\\
D\text{ 在两槽实线性},\\
S(a,u)=S(u,a)=a,\qquad D(a,u)=D(u,a)=0,\\
K(\xi_\alpha,\xi_\alpha)=m_\alpha,\qquad
J_0z\in N,\quad J_uz-z\in N,\qquad
N=\{v:K(v,v)=0\},\\
K(z,J_uw)=K(z,w)\quad(z,w\in V).
\end{gathered}
\tag{386.1}
$$

此结论不消费 $\mathsf P_{\rm one}$、序单位有界性、预设的 Jordan 律或可见插入线性。再保留 $\mathsf P_{\rm one}$，即可进入引理 366.1、定理 366.2 和定理 358.1 的同一原对象、同号同尺度旧 $D$、Born 评价及 $C^*$ 闭包结论。反向，原 $\mathsf H+\mathsf P_{\rm one}$ 使 (385.2) 恰取等号，故两份完整静态资料类相同。

证明。正比较的零平方方向与全部 $V$ 正交，以下只用这一成熟事实处理不可见缺陷，不把原集合插入当作线性算子。先只在原标签上读 (385.1)：

$$
K(J_a\xi_\alpha,J_b\xi_\alpha)
 =\alpha(S(a,b))-\mathrm i\alpha(D(a,b)).
\tag{386.2}
$$

交换 $a,b$ 后取共轭，Hermitian 性使两边相等。原评价实值且分离整个 $E$，故实部给 $S$ 对称，虚部给 $D$ 交替；特别 $D(u,u)=0$。这一步不先使用任何乘法单位。

先恢复同一旧 $D$ 的实双线性。任取有限实系数与响应，使 $\sum_j r_j a_j=0$；在原比较空间中取 $v_\alpha=\sum_j r_jJ_{a_j}\xi_\alpha$。这里只使用 $V$ 中的线性组合，未把和移入原集合插入。由 (386.2)、$S$ 的实双线性和 $K$ 的实非负对角值，

$$
\begin{aligned}
K(v_\alpha,v_\alpha)
 &=\operatorname{Re}K(v_\alpha,v_\alpha)\\
 &=\sum_{j,k}r_jr_k\alpha(S(a_j,a_k))\\
 &=\alpha\!\left(S\!\left(\sum_jr_ja_j,\sum_kr_ka_k\right)\right)=0.
\end{aligned}
\tag{386.2a}
$$

故 $v_\alpha\in N$。与任意第三个原标签 $J_d\xi_\alpha$ 配对，零方向正交和 (386.2) 给

$$
0=K(v_\alpha,J_d\xi_\alpha)
 =-\mathrm i\alpha\!\left(\sum_jr_jD(a_j,d)\right).
\tag{386.2b}
$$

全部原实评价分离 $E$，因而每个实关系 $\sum_jr_ja_j=0$ 都蕴涵 $\sum_jr_jD(a_j,d)=0$。分别取加法、齐次及零响应的关系，得第一槽实线性；已得交替性再给第二槽实线性。此段不消费预算、单位、生成、$\mathsf P_{\rm one}$ 或维数界，也未预用 $D$ 的双线性；任意有限响应关系仍须由同一个全有限正 $K$ 承担。它不是只测固定三标签就足够的断言。

再由原校准及 (386.2)，同一对单位标签的精确平方为

$$
\|J_u\xi_\alpha-\xi_\alpha\|_K^2
 =\alpha(S(u,u))+K(\xi_\alpha,\xi_\alpha)-2m_\alpha.
\tag{386.3}
$$

预算使右端非正，正比较使左端非负，故该差属于 $N$。这里没有调用 $S(u,u)=u$，也未除以 $m_\alpha$。

加入第三个标签 $J_a\xi_\alpha$。与零方向配对为零给

$$
\begin{aligned}
\alpha(S(a,u))-\mathrm i\alpha(D(a,u))
 &=K(J_a\xi_\alpha,J_u\xi_\alpha)\\
 &=K(J_a\xi_\alpha,\xi_\alpha)=\alpha(a).
\end{aligned}
\tag{386.4}
$$

最后一步用校准、Hermitian 性和原读数实值。全部原评价分离给 $S(a,u)=a,D(a,u)=0$；已得对称与交替再给另一侧。特别 $S(u,u)=u$，故 (386.2) 在 $a=b=u$ 给 $\|J_u\xi_\alpha\|_K^2=m_\alpha$。两个标签相差零方向，便有 $\|\xi_\alpha\|_K^2=m_\alpha$，包括零质量。

全域零插入直接复用定理 380.1 的 (380.4) 至辅助正交子空间等于 $V$ 的子论证：实双线性使 $S(0,b)=D(0,b)=0$；零响应校准先消去原标签上的 $J_0$ 平方，有向式使与所有 $J_0w$ 正交的线性子空间包含全部标签并在每个原集合插入下稳定，精确全词生成便使该子空间等于 $V$。该段只消费这些条件，未使用旧乘法单位、对称性、正插入或插入线性，故在当前入口仍适用。于是 $J_0V\subseteq N$。恢复的两侧单位再代入有向式，正是 (380.6) 的

$$
K(J_uz-z,J_aw)=0\quad(a\in E,\ z,w\in V).
\tag{386.5}
$$

每个非空原词落在某个 $J_a(V)$；零长度标签已与自己的 $J_u$ 像相差零方向。因此同一单位缺陷与全部词、继而与其精确线性包 $V$ 正交，得到全域单位。此为 (380.6) 的同一全词检验，不从原标签对非线性插入作线性延拓。

此时定义 362.1、365.1 从定义 357.1 保留的实对称双线性乘法、原乘法单位、旧 $D$ 右单位及全域比较单位已经全部恢复，其余前端未变。故直接用引理 366.1 取得可见代数和结合复乘法，用定理 366.2 取得有界性及全配方正性，再用定理 358.1；旧 $S$ 的 Jordan 恒等式成为同一忠实算子表示的后果。没有先以 Jordan 假设补回这一步。反向原 $\mathsf H$ 的单位与校准给 $K(\xi_\alpha,\xi_\alpha)=m_\alpha$，原乘法单位给 $\alpha(S(u,u))=m_\alpha$，于是预算恰饱和，其余候选条件逐项不变。∎

## 387. 检查域缩减、删除后果与完整原范围

**定义 387.1（与标签质量入口的准确比较）。** §§379–384 已从标签质量恢复全域比较单位及旧 $D$ 两侧单位，本候选不再次认领那些一般桥梁。相对定义 379.1–379.2，新增的缩减是撤去另行给定的旧 $D$ 两槽实线性、$S$ 对称及全响应乘法单位；单标签测试由 $K(\xi_\alpha,\xi_\alpha)\le m_\alpha$ 改为同一对标签的 (385.2)，其第二项保留原 $S(u,u)$，再由 (386.2)–(386.4) 识别同一旧乘法。新旧最终模型类等价，不声称严格更弱、独立信息总量更少、取得成本更低、有限认证或全局最少公理。该等价允许一般无穷维响应，不以有限 EJA、矩阵角稠密性或共同参考指数代替原范围。

删除预算或精确生成时，直接复用命题 382.1 的原抽象接口，逐项代入新预算即可：$E=\mathbb R,u=1,S(a,b)=ab,D=0,J_a=\operatorname{diag}(a,0)$，$\xi_m=(\sqrt m,\epsilon)$。$\epsilon=1$ 时原全词精确生成成立，预算左端为 $2m+1$，单位失败；$\epsilon=0$ 时预算饱和但全词仅到达第一坐标，不可达第二坐标仍使全域单位失败。所有质量和零标签均沿原族保留。这些既有接口见证只定位新增入口的必要检查，不是完整原 $\Omega$ 的反模型。命题 382.2 的同一无限非交换实例仍满足新预算，原插入在零方向中的非线性不被排除。

原完整 $\Omega$、全部类型与实际准备、零／次归一及原正权和 $q$、native、精确 $B$ 与另名闭生成 $\mathsf B_{\rm cl}$、同一 $\sigma,t_0$、实际有序联合及全部乘积／相关输入、参考副本、ready、控制、时钟、设备端口、细记录、全部失败／拒绝／停止／销毁／返回、真正 typed 分组遗忘、具名同数双向及逆向返回、全部合法有限顺序／自适应／并行历史逐项保留。输入是同一旧 $S,D$；不因得出表示而更换原响应、设备或合法性。预算仍须同一来源支付；把 $u$ 叫作总事件并不自动给出它与共同 $K/J$ 的比较合同。

## 388. 二元预算、关系缺陷与更大的比较网

**定义 388.1（原响应关系与总事件的有限比较几何）。** (386.2a)–(386.2b) 先把原响应间每个有限实线性关系变成比较空间中的零平方方向；任加第三个探测标签，虚部都不能区别该方向，分离族遂把这一限制读回同一旧 $D$。这是“关系的关系”的明确意义：不是重定义方向，而是约束原二元方向关系必须尊重原响应之间的实关系。任意有限关系可以涉及任意多个标签，三标签只是单位恢复或两个响应的局部几何，不替代全有限正性。

令 $n=K(\xi_\alpha,\xi_\alpha)$、$s=\alpha(S(u,u))$、$m=m_\alpha$。定理 386.1 的标签起步给

$$
\begin{pmatrix}n&m\\m&s\end{pmatrix}\succeq0,
\qquad n+s\le2m.
\tag{388.1}
$$

预算把同一二元表推到 $n=s=m$ 的边界，两个标签具有同一可见像；这只是成熟零平方几何在原总事件上的应用。加第三个原标签 $J_a\xi_\alpha$，它与前两个标签的交叉项必须相同，(386.4) 遂把这份相同读回为旧 $S,D$ 的两侧单位。零质量时三标签通过零平方处理，不从秩一图景作条件化。

完整候选下再取 $\xi_\alpha,J_a\xi_\alpha,J_b\xi_\alpha$，直接复用定义 383.1 的 (383.2)：$m>0$ 时去掉共同标签方向，二阶协方差表给 $v_av_b\ge c^2+d^2$，$d=\alpha(D(a,b))$。当 $t=v_a+v_b>0$，$r=(2c,2d,v_a-v_b)/t$ 位于三实单位球；$t=0$ 给零表。它不是物理三维、实际量子比特或整个响应空间的维数。全部标签仍须来自同一个全有限正 $K$，更大结构仍为同一可能无限维的比较网、忠实复代数及其态；预算不能由分别任选的两点或三点表拼出。

## 389. 同一完整候选对现有量子公理的采用

**定义 389.1（全原范围的准确对应）。** 每个被消费原类型均须满足定义 385.1–385.2 的静态候选；过程侧保留 C139 定义 66.1 的全部原来源条件，只以定理 386.1 供应它所需的同一静态 $\mathsf H+\mathsf P_{\rm one}$。

| 量子理论部分 | 由候选取得的结果与仍须给出的原关系 |
| --- | --- |
| 原乘法、有号旧 $D$ 与复对象 | 定理 386.1 从标签关系恢复旧 $D$ 两槽实线性、原 $S$ 对称及两侧单位、原 $D$ 交替及两侧单位；直接用 §§366、358 得忠实复 Hilbert 表示和同号同尺度交换子。共同复比较及标记方向仍是输入，未从预算创造复相位或旧 $D$ 的物理来源。 |
| 状态、效果、质量与 Born | 同一 $\alpha(e)$ 成为同一向量的 Born 配对，向量平方为原 $m_\alpha$；原锥与效果由 $\mathsf P_{\rm one}$ 及原序界保留。仅在原质量严格正时条件化，混合准备的向量代表不改成实际纯准备。 |
| 实际联合与每个中心 | 保原乘法和旧 $D$ 的原嵌入、交叉零、同一实际联合的生成／分离及乘积和相关输入仍须来源供应；数学张量积不提供实际接线。全部经典、不等维块与原 $q$ 权继续保留，$q$ 权不冒充概率权。 |
| 原分支、过程比较与 CP | C139 §§50–52 的全部合法前接和原后口给唯一正次单位回溯；其 §§66–73 的完整箭头可再次二元旁接、忠实交换系统／参考腿、共同真支持、三方向原事件支配及全部相关正输入，给每条有限链的 $2^L$ 正性及所有有限长度下的 CP。静态标签预算不供应下一份实际旁接，也不只检验根代码。 |
| 仪器、细记录、更新与 TP | 全部原菜单、完整 typed 输出、失败及真正分组仍各自供应；有限维或指定正常前对偶下采用既有 CP/TNI、TP 对应。Lüders 仍须旧设备自己的射线／完整输出校准，同效果不决定更新。 |
| 历史、遗忘与返回 | 原 typed 接续、记录加和、同数双向及逆向返回使既有逐历史等式适用，不从零方向商删原档案或增加非法未来。可数／非离散记录、无限历史一致性、正常性和指定前对偶仍各有来源条件。 |
| 演化、刻度与原生来源 | 实际保比较保相位的可逆过程才接入酉桥；物理钟、Hamiltonian／能量、共同作用量、控制和共同仪器仍须来源。同一原 $\sigma,t_0$ 不变，完整 CountRead 响应仍可无穷维，有限八十九配置来源不替代它。 |

原固定 $d$ 的相位覆盖／resolvent 适用范围和 $3s+r\le1$ 保持原条件；不扩大到带符号系数、重复幂或上包络，不制造精确 $\|g_d\|_\infty$，不以正时间平均替换原 $d$。预算并未为 CountRead、原被动源或完整 $\Omega$ 构造共同 $K/J$、全部操作或全未来表示。

## 390. 引用范围、原接口增量与完整直观说明

**定义 390.1（成熟工具与新增的原关系识别）。** 半正定 Hermitian 形式的零平方正交、Gram 表与全配对分离是成熟工具；可见线性、正性提升和联合采用直接复用 §§362、366、358，零插入和全词单位直接复用 §380 的准确子论证。非幺表示与一般核表示不在这里重新构造；既有数学来源沿定义 364.3、369.1、384.1 采用，尤其 Frank–Găvruţa–Moslehian [arXiv:math/0501139v6，Lemma 2.2](https://arxiv.org/html/math/0501139v6) 的伴随强制线性不在当前单位恢复之前用于假定 $J$ 线性。一般表示、Jordan 分类、三实球和 C139 的全箭头旁接均非本节新增。

本批的 $\texttt{repo-derived}$ 应用限于：在同一旧 $D$ 仅为总映射、旧乘法不预设对称或乘法单位的原入口，先以原实响应关系的零平方缺陷 (386.2a)–(386.2b) 识别旧 $D$ 双线性，随后将 $\alpha(S(u,u))$ 保留为独立原读数，以 (385.2) 的单标签二元预算饱和得到 (386.3)，再用第三标签的 (386.4) 识别同一旧 $S,D$，从而合法接回已有全域单位和一般完成响应消费者。它是既有比较工具对固定原接口的检查域缩减，不主张一般零平方原理、历史优先权、全球文献不存在性、物理本体或完整量子起源已完成。

**定义 390.2（完整白话）。** 白话说，整份原世界及其所有准备、设备、端口、细记录、失败和合法过去未来都留着，旧的两种二元关系、原比较权、各种真实质量以及同一 sigma 和刻度也不换。起步时不用另告诉旧方向关系怎样随响应加法和实倍数变化，也不用另告诉旧乘法必须对称，或总事件在乘法里怎样当单位；只保留同一来源的共同正比较、原标签的真实读数、全部有向插入关系和无词长上限的生成。先把原响应之间任何一条有限实关系搬到各自插入标签的比较中：旧乘法的双线性使这份差的平方为零，共同正比较便不许它与任何第三标签产生虚部差；原读数能区分响应，因此同一个旧方向关系必须尊重每一条实关系，两槽实线性由此成为后果。这一步仍要检验任意有限关系，不能只靠三个标签代替整张正比较网。新的单位约束再只看一对比较标签：原标签自己的比较平方，加上旧乘法把总事件与自身配对所得的原读数，不能超过二倍原总质量。有向式已经把后一个读数等同于插入总事件后标签的平方，因此这句话恰好把两标签之间的平方距离压成零，连零质量也不例外。再加任意一个原响应作第三标签，前两者与它的比较必须相同；实部便迫使同一个旧乘法在总事件旁不改变任何响应，虚部便迫使同一个旧方向遇总事件为零。两个插入标签互换时，共同比较的实虚部又分别恢复旧乘法的对称和旧方向的反对称；全部原词随后把这些标签关系带到整个可见比较空间，原插入在看不见的方向仍可非线性。恢复后直接用已有结果，同一原对象得到保质量的 Born 表示和有确定号尺度的旧方向，三标签中心化后仍给相干、方向和质量差组成的三实坐标球，更大的网允许无限维。过程侧仍要整台实际操作连同环境、档案和出口一起反复旁接原二能级参考，由三个实际投影方向及其支持内互补检验同一细分支；所有有限层确能供应，才得到完全正性，单盯旧代码不能代付。预算是更小检查域的等价入口，完整资料类没有变，也不使共同比较或实际旁接免费。真实联合、完整仪器与更新、失败和遗忘、同数返回、正常性、无限历史以及物理钟、能量和作用量仍各有原来源条件；裸原源为何同时供应这些关系仍未解决，原目标没有缩成一个有限小球。

## 追加锚 C128384MASS（本行以下为增补区）
