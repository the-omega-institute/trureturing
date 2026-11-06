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
