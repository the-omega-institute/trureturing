# AURIC C128：正交迹与整支持角续卷

## 319. 仅在零重叠处要求无迹的完整候选

**定义 319.1（同一原签名与单一新候选）。** 本卷续接[共同框架与半角关系续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md) §§180–318；下文简称前卷。母卷指 [C123 原生互易比较母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。分别固定前卷定义 264.1、272.1–272.2、311.1 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。整个原 $\Omega$、同一实双线性 $d_A(a,b)=D^A_ab$、原 $q_A,L_A,\circ_A$ 及规范 Jordan 谱迹 $\tau_A$ 均保持。静态坐标由前卷定理 246.1 给出，$\tau_A=\sum_s\operatorname{Tr}_{n_s}$，与原不等正块权的 Frobenius 型 $q_A$ 分开。

原选中域仍是 $\operatorname{rank}E_A>p_*$，其中 $p_*=\operatorname{rank}E_P\ge2$。对该域中全部有序 primitive 对，定义

$$
\begin{aligned}
\mathsf G_{0h}:\quad&D^A_ep=Q_cD^A_ep,\qquad
c=\operatorname{supp}(e+p),\quad Q_c=2L_c^2-L_c,\\
&\tau_A(e\circ_Ap)\in\{0,\tfrac12\};\\
\mathsf Z_0:\quad&\tau_A(D^A_ep)=0\qquad(e\perp p).
\end{aligned}
\tag{319.1}
$$

第一式管整个输出：包括所有其他中心和连接角内外的非对角分量。它不能换成角外压缩条件或 $P_c=4(L_c-L_c^2)$。第二式只在零重叠处要求，不在半重叠处另加迹约束。两个次序、跨中心正交对和原实际联合中的纠缠 primitive 都在量词内。

沿用前卷定义 272.1 的同一原菜单、原 $\mathcal K$、实际 $J_0=P^{\otimes2}$ 及先于 $D$ 固定的同一 $t_0=(e_0,p_0,r_0)\in\mathcal K_{J_0}$，定义

$$
\begin{aligned}
\sigma_{t_0}:\quad&W_{e_0}(p_0)
=2q_{J_0}(D_{p_0}e_0,r_0)+W_{e_0}(2D_{e_0}p_0),\\
\mathsf C_Z(B_*):={}&B_*+\mathsf G_{0h}+\mathsf Z_0+\sigma_{t_0}.
\end{aligned}
\tag{319.2}
$$

相对前卷 $\mathsf C_T$，这里只删除全部半重叠迹前件。未添加 LU、SC、原 $D$ 的交替性、导子律、斜伴随、模身份、primitive 保持或等距前件。

**定义 319.2（完整背景的保留）。** 全部原对象、实际有序联合、旧输出、经典块、不同大小的量子块和原不等正权保持；全部实际准备、零与次归一质量、实际乘积准备及全部原相关准备保持。设备、端口与记录身份不按响应合并。整个 AC、精确 $N_u$、原 X/Xs、全事件 R、实 Jordan 意义的原 F、实际细化／分组／遗忘、全部零／失败／停止、原具名同标量两侧支持返回和同数反向资料，以及每条原合法有限顺序、自适应和并行历史保持。$B$ 的精确有限正生成与 $\mathsf B_{\rm cl}$ 的闭正生成分别保持，不以极限准备替代实际准备。

X 仍只使用原含幺 Jordan/$D$ 嵌入、原有序交叉零、乘积张成与原实际乘积准备合同。不增直接 $AP$、共同参考指数、实际 $M_2$、任意操作或任意共同仪器，不删除原已供的标量两侧有序接口。原右单位只由母卷定理 30.1／引理 67.3 供应；静态结构及实际高简单秩分离分别只由前卷 246.1、202.1 供应。

## 320. 完全不使用迹前件的高秩完整来源正常形

**定理 320.1（单块径向项与全部来源）。** 设

$$
E=\bigoplus_{s\in S}H_{n_s}(\mathbb C),\qquad u=(I_{n_s})_s,
$$

$D:E\times E\to E$ 实双线性，满足右单位 $D(a,u)=0$ 和 $\mathsf G_{0h}$。本定理不假设 $\mathsf Z_0$。记数学理想包含与投影为 $j_s,\pi_s$，全部经典源为 $\mathcal C=\{s:n_s=1\}$。对每个 $n_t\ge3$ 的目标，存在实数 $\alpha_t,\eta_t,\ell_{ts}$ 和实线性泛函 $F_t:E\to\mathbb R$，使对所有完整输入

$$
\boxed{\displaystyle
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\eta_t a_t\circ b_t+a_tF_t(b)
+\sum_{s\in\mathcal C}\ell_{ts}a_s(b_t-b_sI_t),
\qquad \eta_t+F_t(u)=0.}
\tag{320.1}
$$

这包含全部源对，不仅是 $t\times t$ 限制。对单独 $H_n(\mathbb C)$、$n\ge3$，条件等价于

$$
D(a,b)=\alpha\,\mathrm i[a,b]+f(b)a-f(I)a\circ b
\tag{320.2}
$$

其中 $f$ 是任意实线性泛函、$\alpha\in\mathbb R$。不在此分类秩二目标的全部内部自由。

证明。先固定任一非经典源 $s$ 的 primitive $e$。对同块 $f\perp e$，取正交单位向量 $v,w$ 表示它们，置

$$
y=|v\rangle\langle w|+|w\rangle\langle v|,\qquad
p_\pm=(e+f\pm y)/2.
$$

两个 $p_\pm$ 均与 $e$ 半重叠。由双线性和三份整支持，

$$
D(e,e)=D(e,p_+)+D(e,p_-)-D(e,f)\in E_1(e+f).
\tag{320.3}
$$

故即使 $n_s=2$，自输入的整份输出也在源 $s$。若 $n_s\ge3$，两个相互正交的 $f$ 给两个角的交集 $\mathbb Re$，所以 $D(e,e)=k(e)e$；尚未断言 $k(e)=0$。此外，$D(e,f)$ 和 $D(e,y)=D(e,p_+)-D(e,p_-)$ 都在源 $s$。让 $w$ 及其相位遍历 $v^\perp$，连同下方 Hermitian 块与 $e$，这些第二输入张成 $H_{n_s}$。第一输入的 primitive 再张成，故同源 $s,s$ 的整个输出在 $s$，包括秩二源。

把 $e$ 补为整个直和的框架。在 $0=D(e,u)$ 中，对另一源 $r$ 的框架元 $p$，只有 $D(e,p)$ 能有沿 $p$ 的分量；零角支持把该项限制在 $\mathbb Re\oplus\mathbb Rp$，而刚证的自输入与同源项均不向 $r$ 输出。故 $D(e,p)\in\mathbb Re$。对固定 $p$，线性映射 $a\mapsto D(j_sa,j_rp)$ 的每颗 rank-one 投影都沿自身。它在任意框架上的单位像都对角，因而单位像为一个标量单位；再逐框架比较给该映射为相同标量倍的恒等。第二槽线性化便给实线性泛函 $\lambda_{sr}$，使

$$
D(j_sa,j_rb)=\lambda_{sr}(b)j_sa
\qquad(n_s\ge2,\ r\ne s).
\tag{320.4}
$$

这里没有交换输入，也没有令右端归零。

下面证明 (320.2)。在单块右单位的情形，(320.3) 给 $D(e,e)=k(e)e$。框架单位式中不同 Peirce 非对角分量及每个伙伴投影分量互不重叠，故

$$
D(e,p)=c(e,p)e\qquad(e\perp p).
\tag{320.5}
$$

任意 $a$ 的谱展开遂使 $Q(a)=D(a,a)$ 在该谱基中对角，故 $[Q(a),a]=0$ 对全部 Hermitian $a$ 成立。先将这条实多项式恒等式复化到 $M_n(\mathbb C)$，再应用 Brešar–Špenko，*Functional identities of one variable*，[arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2) 的交换二次迹标准形，得到

$$
Q(a)=A a^2+f(a)a+g(a)I.
\tag{320.6}
$$

此处“二次迹”指双线性映射的对角化，不是谱迹；$f$ 线性、$g$ 二次齐次。具有三个不同谱值的 Hermitian 元构成开稠密集，$I,a,a^2$ 在其上独立，故由 Hermitian 性和多项式延拓，$A,f,g$ 在实域取实。复化消费的是已证多项式恒等式，不把 primitive 条件直接扩张到任意复矩阵对。

由 $Q(e)\in\mathbb Re$ 得 $g(e)=0$。以 $g(a,b)$ 表示 $g$ 的对称极化。对正交 primitive $e,p$，(320.5) 使 $D(e,p)+D(p,e)$ 只沿 $e,p$，而 (320.6) 的极化给

$$
D(e,p)+D(p,e)=f(p)e+f(e)p+2g(e,p)I.
$$

$n\ge3$ 时角外还有一个非零方向，故 $g(e,p)=0$，并比较 $e,p$ 系数得 $c(e,p)=f(p)$。对任意谱展开，$g$ 的全部同框项现在为零，所以 $g(a)=0$ 对全部 $a$ 成立。右单位取框架和给

$$
0=D(e,I)=\{A+f(I)\}e,
$$

即 $A=-f(I)$。令 $D^0(a,b)=Aa\circ b+f(b)a$；它与 $D$ 在每颗 primitive 对角和每对正交 primitive 上相同，且自身满足右单位和半角整支持。其差 $\delta=D-D^0$ 满足完整 O、H 与右单位，故现在才应用前卷单载体定理 274.1，得 $\delta(a,b)=\alpha\,\mathrm i[a,b]$。这就证明 (320.2)。反向各项均支撑在输入支持内，右单位由直接代入成立。

回到直和，固定 $n_t\ge3$。由 (320.4) 和原右单位，内部限制满足

$$
D(j_ta,j_tI_t)=-\gamma_t j_ta,\qquad
\gamma_t=\sum_{r\ne t}\lambda_{tr}(I_r).
$$

给内部映射加上 $\gamma_t\operatorname{Tr}(b)a/n_t$ 即取得内部右单位；它仍有 $\mathsf G_{0h}$。应用刚证单块式再减回该项，内部形式为交换子、$\eta_ta\circ b$ 和一个第二槽线性泛函乘 $a$。把这个泛函与所有 $\lambda_{tr}$ 合为整个 $E$ 上的 $F_t$，右单位恰给 $\eta_t+F_t(u)=0$。

第一源为另一非经典块时，同源局部性及 (320.4) 均使其输出不向 $t$。两个不同源均非 $t$ 时，零角整支持及双线性也使目标投影为零，包含两个不同经典源。对经典首源 $e_s=j_s1$，零角支持使线性映射 $b\mapsto\pi_tD(e_s,j_tb)$ 把每颗 primitive $p$ 送入 $\mathbb Rp$；上述单位逐框架论证给它为 $\ell_{ts}b$。最后将 $D(e_s,u)=0$ 投影到 $t$，唯一其余来源是经典自输入，故

$$
\pi_tD(e_s,e_s)=-\ell_{ts}I_t.
\tag{320.7}
$$

逐源双线性展开现在穷尽全部来源，得到 (320.1)。其他经典坐标的输出从未被当作零；定理只陈述固定高秩目标的全部来源。∎

## 321. 实际交叉零能消去什么与仍留下什么

**定理 321.1（无迹删除后的实际联合余量）。** 设原实际 $K=JR$ 位于选中域并满足 $\mathsf G_{0h}$，$T\subset E_J,V\subset E_R$ 为非经典简单块，$U=(T,V)$ 为原实际中心对。则存在 $\alpha_U\in\mathbb R$ 和实线性 $F_U:E_K\to\mathbb R$，使

$$
\pi_UD^K(a,b)=\alpha_U\,\mathrm i[a_U,b_U]+a_UF_U(b),
\qquad F_U(u_K)=0,\quad F_U\circ l=0,
\tag{321.1}
$$

其中 $l:E_R\to E_K$ 是原第二槽嵌入。这一结论不宣称 $F_U=0$。

证明。原右单位和静态全部中心对独立供应，$n_U=n_Tn_V\ge4$，所以定理 320.1 可用于整个 $E_K$。静态坐标中的两嵌入在 $U$ 上分别为 $x\mapsto x\otimes I_V$ 与 $y\mapsto I_T\otimes y$，允许其中相应的转置；两范围交换。

取第一输入只支撑 $T$ 的非零无迹 $x$，第二输入只支撑 $V$ 的非零无迹 $y$。两者在所有经典源上的第一坐标均为零，原交叉零遂给

$$
0=\eta_U x\otimes y+F_U(l(y))x\otimes I_V.
\tag{321.2}
$$

对 $V$ 取数学部分迹，先得 $F_U(l(y))=0$，再得 $\eta_U=0$。这里部分迹仅为有限矩阵证明工具，不引入实际遗忘或原 $q$ 因子化。固定这个第一输入，让第二输入遍历整个 $E_R$，同一交叉零给 $F_U\circ l=0$。右单位于是给 $F_U(u_K)=0$。

每个经典源都是唯一的原中心对 $s=(r,d)$。分别取两个因子的经典中心单位 $z_r,z_d$；二者在 $U$ 上均为零，所有经典源中二者坐标乘积只有 $s$ 处为一。(320.1) 和原交叉零给 $0=-\ell_{Us}I_U$，逐项得 $\ell_{Us}=0$。普通／相反坐标的单位、标量和谱迹不变，故全部取向覆盖。剩余式正是 (321.1)。∎

**定义 321.2（全删迹的精确未证桥）。** 原右参考及第二槽交叉零给的是 $F_U\circ l=0$，未在上述证明中给出 $F_U\circ k=0$ 或 $F_U=0$。原 $D$ 保持只允许将实际已证的等式沿原嵌入运输，不能把整个联合的任意第二输入认作一个因子输入。若原 $A$ 确实作为某个实际有序联合的第二因子，前卷定理 287.1 已由原交叉零和 $D$ 保持给 LU；是否有覆盖每个原对象的这种实际来源仍按前卷 §§286–292 的原量词判断。这里不把单位／交换的散文补成未列出的普遍 $(I,A)$，也不从尚未建立普遍来源推断可以删除已存在的接口。

故 (321.1) 是全部来源分类后的准确残余，不是完整 $B_*$ 的反模型，也不是全删迹成功。将 $\mathsf Z_0$ 也删除后的完整原范围结论仍未在本卷证明。下面发展的是定义 319.1 的唯一完整新候选。

## 322. 零角迹条件关闭所有高秩余量

**定理 322.1（仅零角无迹的全来源恢复）。** 在定理 320.1 的前件上加入 $\mathsf Z_0$。则对每个非经典源 $s$，

$$
D(j_sa,j_rb)=0\ (r\ne s),\qquad
D(j_sa,j_sb)\in j_sH_{n_s},\qquad D(j_sa,j_sI_s)=0.
\tag{322.1}
$$

对每个高秩目标 $n_t\ge3$，对全部完整输入有

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s\in\mathcal C}\ell_{ts}a_s(b_t-b_sI_t).
\tag{322.2}
$$

本结论不使用半重叠输出的无迹性。

证明。先用 (320.3) 的纯支持论证：非经典自输入全在源块，高秩源中还沿 $e$。对任意非经典源 $s$，(320.4) 与零角迹给

$$
0=\tau(D(j_se,j_rp))=\lambda_{sr}(p)
$$

对每个另一源的 primitive $p$ 成立。它们张成该源，故所有 $\lambda_{sr}=0$；同源局部性和完整右单位随即给 (322.1)。对 $n_s\ge3$，将 $e$ 补为整个框架并取规范迹，

$$
0=\tau(D(e,u))=k(e)+\sum_{p\perp e}\tau(D(e,p))=k(e).
\tag{322.3}
$$

所以 $D(e,e)=0$；此式正以零角迹替代前卷 (312.3) 的半角迹。单位式再逐 Peirce 分量使同源正交 $D(e,p)$ 只能沿 $e$，零角迹使该系数为零。高秩内部现在具有右单位、完整 O 和 H，前卷 274.1 给同源交换子形式；秩二源只用整输出局部性，不套高秩分类。

经典首源到高秩目标的映射仍由 (320.7) 及其前一步给 $\ell_{ts}b_t$ 与补偿自输入 $-\ell_{ts}b_sI_t$。所有其他来源由 (322.1) 或零角整支持排除，故得到 (322.2)。这也可从 (320.1) 逐项核对，但证明没有借用已经要求半角无迹的前卷 312.1。∎

## 323. 从实际高秩目标返回所有原对象

**定理 323.1（两份背景分别的完整无标定桥）。** 分别有

$$
\begin{aligned}
B+\mathsf G_{0h}+\mathsf Z_0
&\Longleftrightarrow B+\mathrm I+\mathrm{SC}
\Longleftrightarrow B+\mathsf G^0_{0h},\\
\mathsf B_{\rm cl}+\mathsf G_{0h}+\mathsf Z_0
&\Longleftrightarrow\mathsf B_{\rm cl}+\mathrm I+\mathrm{SC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G^0_{0h}.
\end{aligned}
\tag{323.1}
$$

左端的几何只在原选中域要求。结论中的 I、SC、LU、交替、原导子律和原 $q$ 斜伴随覆盖全部原对象和实际联合，包括全部经典／低秩来源、目标和旧输出。原半角输出无迹成为结论。

证明。对左端，原右单位和静态结构分别由母卷 30.1／67.3、前卷 246.1 给出。固定任意非零原 $A$，用前卷 202.1 取 $N\ge\max\{3,p_*\}$，取得同一个实际 $J$、原含幺 Jordan/$D$ 单射 $i:E_A\to E_J$ 及目标族 $\mathcal V_N$，使

$$
n_T>N\quad(T\in\mathcal V_N),\qquad
\bigcap_{T\in\mathcal V_N}\ker(\pi_Ti)=\{0\}.
\tag{323.2}
$$

再取 $J$ 自己由原身份事件和全事件 R 已供应的一份实际 $K=JR$，$R=P^{\otimes k}$、$k\ge1$，及原第一槽嵌入 $k_J$。整个 AC、原指针幂与静态全部中心对给 $R$ 一个非经典块 $V$。每个 $U_T=(T,V)$ 都是该同一实际 $K$ 的高秩目标，故整个 $K$ 在选中域，(319.1) 确实可用；不要求每个源块都高秩。

在 $K$ 上用定理 322.1 的全部来源式。对每个经典源 $s=(r,d)$，用原有序交叉零 $D^K(k_J(z_r),l(z_d))=0$；高目标两个坐标均为零，经典坐标乘积只在 $s$ 处为一，故恰得 $\ell_{U_Ts}=0$。这一步与前卷 313.2 的参数相同，其所需完整来源式在此已由仅零角迹证明。于是

$$
\pi_{U_T}D^K(x,y)=\alpha_{U_T}\,\mathrm i[x_{U_T},y_{U_T}]
\qquad(x,y\in E_K).
\tag{323.3}
$$

静态逐中心对表示给单射 $\theta_T$，满足 $\pi_{U_T}k_J(x)=\theta_T(x_T)$，在所选坐标中为 $x_T\mapsto x_T\otimes I_V$，允许相应转置。故 $h=k_Ji$ 的这些目标共同分离整个原 $E_A$。对原任意 $a,b,c$，把

$$
r_A=D^A_a(b\circ c)-(D^A_ab)\circ c-b\circ(D^A_ac)
$$

和 $D^A_aa$ 沿 $h$ 运输；原 $h$ 保持同一 Jordan 乘法和同一 $D$，(323.3) 逐目标给两者投影为零。共同分离使两者在整个 $E_A$ 为零。因此原 $D_a$ 是 Jordan 导子，且 SC 成立。有限 EJA 导子内性使原 $D_a\in\mathfrak k_A$，即 I；原 $L_a$ 对不等权 $q_A$ 自伴随，内导子便对同一 $q_A$ 斜伴随。$A$ 任意，故所有原对象和接口覆盖。

从 I+SC 返回其余两端，只复用前卷 275.2、314.1：在各自完整准备背景上，它们已给原 II 和含零分支的共同 $\kappa\ge0$，逐块原 $D$ 为标量交换子，经典和跨块为零。因此全部双单位、O、H 与零／半角无迹均成立。这里在取得 I+SC 以后才消费该共同尺度定理，未拿其结论提前消去径向项。∎

## 324. 同一刻度与完整量子消费者

**定理 324.1（完整候选的恒等对应）。** 对定义 319.1 的任意同一原菜单及预先固定的同一 $t_0$，分别有

$$
\mathsf C_Z(B_*)\Longleftrightarrow\mathsf C_T(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\tag{324.1}
$$

对应对全部原数据和全部合法有限历史都是恒等。由同一原 $D$ 定向的复坐标中，所有原对象满足

$$
\begin{gathered}
\mathcal A_A=\bigoplus_s B(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
D_ab=\tfrac{\mathrm i}{2}[a,b],\qquad
 a\cdot b=a\circ b-\mathrm iD_ab,\\
D_ab=-D_ba,\quad D_aa=D_au=D_ua=0,\quad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\ (c^2=c).
\end{gathered}
\tag{324.2}
$$

全部原实际联合成为保持同一取向的普通复张量，全部原相关输入和原经典中心保持。

证明。323.1 的无标定桥先恢复前卷 315.1 的完整前件；共同尺度包含零分支。随后才在同一 $J_0,t_0,q,W,D$ 上使用原 $\sigma_{t_0}$，按前卷 276.1–276.2、315.1 使共同曲率系数为一，取得 (324.1)–(324.2)。不重标原 $D$、不重新选择标签，也不以单块符号选择替换整个原接口取向。全部实际张量结论复用前卷 316.1 的已匹配接口。∎

**定理 324.2（概率、全部旧事件与全历史）。** 设 $g_A^0$ 为原比较型，$T_f:E_B\to E_A$ 为原事件的 Heisenberg 映射，$T_f^{\dagger_0}$ 为其原 $g^0$ 伴随。定义正可逆线性 $B_A$ 为 $g_A^0(x,y)=\tau_A((B_Ax)y)$。同一原准备 $\alpha$ 的两个坐标运输为

$$
\begin{aligned}
\alpha(y)&=g_A^0(x_\alpha,y)=\tau_A(\rho_\alpha y),
&\rho_\alpha&=B_Ax_\alpha,\\
\mathcal T_f^0&=T_f^{\dagger_0},
&\Phi_f&=B_B\mathcal T_f^0B_A^{-1},\\
\alpha(D_ab)&=g_A^0(x_\alpha,D_ab)
=q_A(\widehat x_\alpha,D_ab),
&\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
q_A(x,y)&=\tau_A((\mathcal W_Ax)y).
\end{aligned}
\tag{324.3}
$$

一般 $x_\alpha\ne\widehat x_\alpha$，不能用未换算的 $q_A(x_\alpha,\cdot)$ 替代原准备。每个原事件的 $\Phi_f$ 为 CP/TNI，原完整设备的事件和为 TP；零、奇异、次归一和不等正权全部包括，各实际联合各用自己的 $B_A,\mathcal W_A$，无因子化前件。

对每个数学效果 $0\le e\le u_A$，原所选精确有限平方根词在原许可相关执行中给

$$
\Phi_{W_e}(\rho)=\sqrt e\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{324.4}
$$

其原占用指针失败方向 $p_1$ 的每个原失败 $\Psi_\ell:P\to B_\ell$ 的完整输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；只有原实际丢弃时才化为质量因子，其他原方向和中心的失败仍取原映射。原 F 给同一实现的实际可访问细口与原遗忘，逐支有

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad \Phi_f=\sum_\ell S_\ell,
\quad U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad
\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{324.5}
$$

$q_\ell$ 与原同数反向资料均保持，未归一成一。对每份原准备、每条原合法有限历史 $h=(f_1,\ldots,f_m)$ 及末端原效果 $w$，

$$
\alpha(T_{f_1}\cdots T_{f_m}w)
=\tau_{A_m}\!\left(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{324.6}
$$

证明。324.1 取得前卷 316.1 的完整候选，且 319.2 保留其所有原来源，故逐项复用而不重新重构：导子、曲率给复乘法；原双对偶给 (324.3)；X 的 Jordan/$D$ 保持、交叉零、乘积张成及实际乘积准备分离给普通张量；全事件 R、同设备同记录旁接和全部原相关正锥给旧事件 CP/TNI，原完整效果和给 TP。闭背景仅在同一已固定执行上用母卷 69.2 连续延拓，不补实际极限准备。

整个 AC、精确 $N_u$、Xs 及所消费的原参考／合法连线按母卷 12.1、32.1 给同一所选词，25.2 给完整失败。原 F、实际细口、同一分组／遗忘及母卷 (29.5) 的原同数两侧资料给 (324.5)，不从数学 Kraus 表示补造设备或记录。一步双对偶逐原箭头迭代给 (324.6)：自适应逐原实际记录分支，并行逐原已供联合及相关输入，粗化／遗忘取原线性和，失败／返回／停止取原箭头。故全部原合法有限历史覆盖，条件概率只在原分母正时取比值。∎

**定义 324.3（保留的三项物理来源）。** 连续确定可逆一参数器件、物理时钟、具体 Hamiltonian 和共同作用量／$\hbar$ 标定仍各需原来源；任意独立成功支的共同完整仪器需原类型控制、记录和共同合法连线；旧同效果设备的理想完整输出需其自己的完整输出校准。零角迹、支持角和代数 $1/2$ 不替代这些资料。

## 325. 非空满足族与简洁角网

**定理 325.1（完整满足及严格局部删除）。** 前卷 317.1 的全部 tagged-CP 满足族分别满足 $\mathsf C_Z(B)$ 与 $\mathsf C_Z(\mathsf B_{\rm cl})$，包括原 $P=\mathbb C\oplus M_3$、没有实际 $M_2$ 对象或简单块的子族。与此同时，$\mathsf G_{0h}+\mathsf Z_0$ 在单载体右单位层严格弱于 $\mathsf G^0_{0h}$。

证明。完整满足族的同一原 $D=\mathrm i[a,b]/2$ 在所有角内无迹，故新几何成立；同一原 sigma、全部过程背景及历史已由前卷 317.1 验明其数学模型条件。该族保留任意正定原比较参数 $r_s$ 与不等正块权 $w_s$，具体原双 Riesz 换算沿前卷 (317.1)，不限制为 $g^0=q$。因此完整族和无实际 $M_2$ 子族均直接保留。

为证局部严格性，取 $E=H_2(\mathbb C)\oplus\mathbb R^k$，$2+k>p_*$，以及 Pauli 矩阵 $\sigma_x,\sigma_y,\sigma_z$，定义整个输出只在二阶块的

$$
D(a,b)=\operatorname{Tr}(\sigma_z\,\mathrm i[a_2,b_2])I_2\oplus0.
\tag{325.1}
$$

它有右单位，且每个正交 primitive 对交换，故整向量 O 成立，包含跨中心对；半重叠对必在二阶块内，支持是该整块，故 $\mathsf G_{0h}$ 成立。取 $e=(I_2+\sigma_x)/2$、$p=(I_2+\sigma_y)/2$，则 $\operatorname{Tr}(ep)=1/2$、$\mathrm i[e,p]=-\sigma_z/2$，因而 $D(e,p)=-I_2\oplus0$，规范迹为 $-2$。这正是被删半角迹测试的非零值。此例只区分局部几何前件，未供应完整原联合或 sigma，不是两份完整背景的反模型。全背景中 323.1 恢复被删关系，故不声称完整模型类严格扩大。∎

**定义 325.2（三实维球截面和更大结构）。** 两颗同块不同 primitive 的支持角为数学 $H_2(\mathbb C)$，实维四；其无迹部分实维三。零重叠和半重叠在复射影线中分别为角 $\pi/2,\pi/4$，在 Bloch 球中分别为对径和正交方向。候选只在对径处输入迹零，其他零／半角只管整支持；原实际关系把转动的无迹性传播回来。

在 324.2 成立后，对同块正交 $e,f$、$c=e+f$、$y\in V_{ef}$、$y^2=c$，置 $h=e-f,z=2D_ey$，便有

$$
h^2=y^2=z^2=c,\qquad
h\circ y=h\circ z=y\circ z=0,\qquad
D_ey=z/2,\quad D_ez=-y/2.
\tag{325.2}
$$

横向 $J_e=2D_e$ 是同一原 $q$ 的正交复结构。跨中心原子却只有 $E_1(e+p)=\mathbb Re\oplus\mathbb Rp$，零迹部分为一条 $\mathbb R(e-p)$ 线，无跨中心 Peirce 非对角元。更大结构是各原块的 $\mathbb{CP}^{n_s-1}$ 与共享同一原 $D$ 的相交支持角网。证明的第三个复向量位置用于拼接，不等于三实维 Bloch 截面、实际量子比特或物理空间三维。

## 326. 来源、剩余问题与完整白话

**定义 326.1（准确复用和新增综合）。** 本卷的仓内中间来源固定为 [`9115948806b49420359b355f130c52cdcda8c9d8`](https://github.com/the-omega-institute/trureturing/tree/9115948806b49420359b355f130c52cdcda8c9d8) 的前卷与母卷：右单位及静态供应分别为母卷 30.1／67.3、前卷 246.1；全部来源的比较基准为前卷 303、312–314；单载体 O/H 分类为 273–274；整个源分离为 202.1；共同尺度及同一 sigma 为 275–276、315；全部消费者、双 Riesz 区别、完整满足族为 316–317。使用这些结论前各自的入口均在 320–324 证明，不以已有无迹分类替代新的无迹删除分类。

Brešar–Špenko [arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2) 是特征零全矩阵代数上交换多线性迹标准形的成熟中间工具；320.6 的实多项式复化桥与前卷 258.2 的用法相同，未借其原来更强的前件。Haagerup–Laustsen 的 *Weak amenability of C*-algebras and a theorem of Goldstein*，Theorem 3.1(1)、Lemma 3.4（DOI `10.1515/9783110802009.223`），及 Tao–Gowda 的 *A Representation Theorem for Lyapunov-like Transformations on Euclidean Jordan Algebras*，§2、Proposition 3，仍只按前卷 280.1 的准确前件供给既有 274.1 及有限 EJA 内导子。成熟中间工具记为 $\texttt{literature-attested}$，不作为新增定理交付。

本卷新增综合为：仅右单位和整支持下含全部经典自输入及全部源对的 (320.1)，实际交叉零后的精确径向残余 (321.1)，以及只以零角迹取代全部半角迹前件的 322–324 完整桥。其地位为 $\texttt{repo-derived}$，不由检索未命中推出文献原创或优先权。向量值 range-compatible 映射、双向固定角射影双射和一般保投影线性映射的相邻分类不直接满足本题矩阵值有序双线性的前件，未用作此桥的替代证明。

**定义 326.2（未解决的内生来源）。** 具体原 $\Omega$ 如何从其实际来源供应完整 $B_*$、$\mathsf G_{0h}$、$\mathsf Z_0$、同一 sigma 及所有消费接口，仍是实例化义务。条件候选及恒等对应不是这些来源已经内生的证明。全部删除迹后的径向 $F_U$ 仍按 321.2 未证，不以局部式当全背景反例。前卷的 static supplier／overlap、SourceU27047 和实际第二槽来源问题保持原义，不从其他载体或理论的相似图景移入未经证明的供应映射。324.3 的三项物理义务分别保留。

本轮简化只精确指删除所有半重叠处的独立迹要求，保持同一整支持域、同一原背景和同一刻度；不主张认证更便宜、独立前提总数的最小性、含噪稳定性或经验／本体结论。本文为纸笔数学，未取得 Lean/kernel、数值实验或经验验证。

**定义 326.3（只在错开时查一笔总账）。** 白话说，整座原世界仍完整保留：量子街区、经典房间、大小不同的中心、真实联合和纠缠准备、原比较尺、每台设备与记录、失败出口、细化和遗忘、带原成功数的双返回，以及每条合法有限历史，一样都不撤。新候选只要求两颗原子完全错开或恰好重叠一半时，整份推动都留在它们共同的小屋里；总增减为零这笔账，只在完全错开时检查，不再对每一扇半重叠窗另查一遍。两扇相反的半角窗先把自推动圈回本街区，大街区里不同小屋的交集只剩原子自身；原右单位把整个框架合起来，已查过的零角账便将这点自推动清零，同时逐项堵住跨街区的行。经典房间没有半角窗，其第一槽混合项和自输入补偿必须一起保留；原来已有的实际参考联合再用逐中心交叉零把这些余量清掉。高秩目标共同看得见原对象的每个区别，于是将导子、左单位、自守恒和所有半角的无迹性带回全部原对象。最后沿用同一张事先选好的刻度单，将共同转动钉到一；复乘法、Born 概率的原双运输、全部实际张量与相关输入、旧事件、所选平方根词及完整失败、原细记录与同数双返回、全部有限合法历史都接回来。只守小屋而连零角总账也不查，局部还能藏下“第二输入决定、沿第一输入伸缩”的径向项，实际交叉零目前只证明它不读取参考那一侧，尚未证明整个原网让它消失，所以这里没有把全删迹说成成功。同块小屋的无迹截面是三实维球空间，跨中心却只是一条相抵线；这些角共享同一关系，织成更大的复射影角网，并不凭图景新造设备、时钟或作用量。公理的具体原生来源及三项物理标定仍各守自己的证明义务。

## 追加锚 C128326（本行以下为增补区）

## 327. 三颗固定首原子与有限迹基的完整候选

**定义 327.1（先于推动关系固定的有限测试）。** 续接定义 319.1–319.2，分别保留完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。原 $\Omega,q,D,L,\circ$、规范谱迹 $\tau$、整个原选中域 $\operatorname{rank}E_A>p_*$、全部实际来源及同一预选 $t_0,\sigma_{t_0}$ 均不变。只替换 $\mathsf Z_0$；整个 $\mathsf G_{0h}$ 的量词不缩小。

由前卷 246.1 的静态表示，对每个选中原对象写

$$
E_A=\bigoplus_{s\in S_A}H_{n_s}(\mathbb C),\qquad
 m_A=\dim_{\mathbb R}E_A=\sum_s n_s^2.
\tag{327.1}
$$

在考察原 $D$ 之前，为每块任取一次正交归一坐标 $v_{s,1},\ldots,v_{s,n_s}$。以 $[v]=vv^*$ 表示单位向量的 rank-one 投影，第二输入只取数学集合

$$
\mathcal P_A=\bigcup_s j_s\left\{
[v_{s,j}],\quad
[(v_{s,j}+v_{s,k})/\sqrt2],\quad
[(v_{s,j}+\mathrm i v_{s,k})/\sqrt2]:j<k
\right\}.
\tag{327.2}
$$

花括号中的第一类遍历全部 $j$，后两类遍历 $j<k$；经典块贡献其一个单位。对每个 $n_t\ge3$，只用三颗第一输入

$$
e_{t,1}=j_t[v_{t,1}],\quad e_{t,2}=j_t[v_{t,2}],\quad e_{t,3}=j_t[v_{t,3}].
$$

为每个 $p\in\mathcal P_A$ 固定 $a_t(p)$：若 $p$ 在其他块，取 $e_{t,1}$；若在 $t$，取 $e_{t,1},e_{t,2},e_{t,3}$ 中下标不在其一个或两个坐标支撑下标中的最小者。因此 $a_t(p)\perp p$。全部选择只依赖静态坐标，不读取 $D$ 或其输出。定义

$$
\begin{aligned}
\mathsf Z_{\rm fin}:\quad&
\tau_A\bigl(D^A(a_t(p),p)\bigr)=0
\quad(n_t\ge3,\ p\in\mathcal P_A),\\
\mathsf C_{\rm fin}(B_*):={}&B_*+\mathsf G_{0h}+\mathsf Z_{\rm fin}+\sigma_{t_0}.
\end{aligned}
\tag{327.3}
$$

每个选中对象上，每个高秩目标只有 $m_A$ 个标量迹要求；没有高秩目标时该对象的迹要求为空。对象域本身无需有限。维数符号 $m_A$ 与原双线性数据 $d_A(a,b)=D^A_ab$ 分开。这些投影是数学测试标签，不宣称原来有对应仪器、准备或压缩事件；静态坐标也不是先验固定原 $D$ 的复取向。

**定义 327.2（不变的完整前件）。** 定义 319.2 的全部范围逐项保留：原全部单体、实际有序联合、旧输出、经典中心、不同量子块大小和不等正块权；全部实际准备、零与次归一质量、实际乘积与相关准备；设备、端口、细记录和失败身份；整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、实际细化／分组／遗忘、零／失败／返回／停止、原具名同标量两侧支持返回及同数反向资料；每条原合法有限顺序、自适应和并行历史。$B$ 的精确有限正生成和 $\mathsf B_{\rm cl}$ 的闭正生成分别保持。

不预设 LU、SC、交替、导子、斜伴随、原 $D$ 的理想保持、模身份、primitive 或等距嵌入；不增加直接 $AP$、共同指数、实际 $M_2$、任意仪器、时钟或 $\hbar$。原实际已供应的标量两侧有序接口继续保留。整支持条件仍检验原选中对象的全部有序零／半重叠 primitive 对，包含原实际联合中的纠缠 primitive。

## 328. 有限迹值恰好读取整个径向泛函

**定理 328.1（有限迹恢复的全来源式）。** 在定理 320.1 的前件上，固定定义 327.1 的任意静态选择。对每个 $n_t\ge3$，$\mathsf Z_{\rm fin}$ 中属于 $t$ 的 $m_A$ 条等式等价于 (320.1) 的 $F_t=0$。于是 $\eta_t=0$，且对全部完整输入

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s\in\mathcal C}\ell_{ts}a_s(b_t-b_sI_t).
\tag{328.1}
$$

本结论不要求任何秩二首源或经典首源的迹测试，也不提前断言它们的跨源项为零。

证明。对任一高秩 $t$ 内的 primitive $e$ 和整个 $E_A$ 的任一 primitive $p\perp e$，320.1 的证明已给：同源的整个输出在第一源块，异源的非经典首源输出也在第一源块。因此

$$
D(e,p)=j_t\pi_tD(e,p),\qquad
\tau_A(D(e,p))=F_t(p).
\tag{328.2}
$$

第二式直接将 $a=e,b=p$ 代入 (320.1)：交换子迹为零，$e\circ p=0$，全部经典第一坐标为零，而 $\operatorname{Tr}(e)=1$。若 $p$ 位于其他块，仍有 $b_t=0$ 和同一等式；没有把 $F_t$ 的定义域缩成 $t$。

集合 (327.2) 是整个 $E_A$ 的实线性基。其块内对角投影给对角矩阵；两种两坐标投影减去对应半个对角和，分别给每个非对角位置的实部与虚部方向；不同块直和。数量是 $\sum_s\{n_s+2\binom{n_s}{2}\}=m_A$。每个测试对都正交，故 (328.2) 把有限测试逐条化为 $F_t(p)=0$。基张成使 $F_t=0$；反向由同式成立。右单位关系 $\eta_t+F_t(u)=0$ 再给 $\eta_t=0$，剩余经典行及其自输入补偿恰为 (328.1)。∎

## 329. 有限测试经实际联合恢复全域量子关系

**定理 329.1（两份完整背景各自的无标定等价）。** 对定义 327.1 的任意先定静态选择，分别有

$$
\begin{aligned}
B+\mathsf G_{0h}+\mathsf Z_{\rm fin}
&\Longleftrightarrow B+\mathrm I+\mathrm{SC}
\Longleftrightarrow B+\mathsf G_{0h}+\mathsf Z_0,\\
\mathsf B_{\rm cl}+\mathsf G_{0h}+\mathsf Z_{\rm fin}
&\Longleftrightarrow\mathsf B_{\rm cl}+\mathrm I+\mathrm{SC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G_{0h}+\mathsf Z_0.
\end{aligned}
\tag{329.1}
$$

恢复的 I、SC、LU、交替、导子、原 $q$ 斜伴随、全部零／半角无迹覆盖全部原对象和实际联合，不限于有限测试或高秩块。

证明。原右单位仍独立来自母卷 30.1／67.3，静态表示独立来自前卷 246.1。固定非零原 $A$，按前卷 202.1 取 $N\ge\max\{3,p_*\}$，取得同一个实际 $J$、原含幺 Jordan/$D$ 单射 $i:E_A\to E_J$ 和高简单秩族 $\mathcal V_N$，满足

$$
n_T>N,\qquad
\bigcap_{T\in\mathcal V_N}\ker(\pi_Ti)=\{0\}.
\tag{329.2}
$$

与 323.1 相同，使用 $J$ 自己由原身份事件与全事件 R 供应的一份实际 $K=JR$，$R=P^{\otimes k}$、$k\ge1$。整个 AC、原指针幂与全部静态中心对给 $R$ 一个非经典块 $V$。每个 $U_T=(T,V)$ 都是同一 $K$ 的高秩目标；$K$ 因而在原选中域。于是 328.1 可用于整个 $E_K$，包括其中全部低秩和经典来源。

设 $k_J,l$ 为这份实际联合的原有序嵌入。每个经典源唯一为经典中心对 $s=(r,d)$；取两个因子对应的数学中心单位 $z_r,z_d$。原交叉零给 $D^K(k_Jz_r,lz_d)=0$。这两个输入在 $U_T$ 上均为零，经典坐标乘积仅在 $s$ 为一，故 (328.1) 恰给 $0=-\ell_{U_Ts}I_{U_T}$。逐个中心对取得 $\ell_{U_Ts}=0$，得到

$$
\pi_{U_T}D^K(x,y)=\alpha_{U_T}\,\mathrm i[x_{U_T},y_{U_T}]
\qquad(x,y\in E_K).
\tag{329.3}
$$

这是整个输入的式子，不是仅对 $U_T\times U_T$ 的内部限制。所用的是原交叉零，没有反向交叉零前件。

静态表示给单射 $\theta_T:x_T\mapsto x_T\otimes I_V$，允许相应转置，且 $\pi_{U_T}k_J(x)=\theta_T(x_T)$。故 $h=k_Ji$ 的这些目标共同分离整个原 $E_A$。将原任意 $a,b,c$ 的

$$
r_A=D^A_a(b\circ c)-(D^A_ab)\circ c-b\circ(D^A_ac),
\qquad D^A_aa
\tag{329.4}
$$

沿同一 $h$ 运输。原嵌入保持同一 Jordan 乘法和同一 $D$，(329.3) 的交换子逐目标使两者为零；共同分离给原 $r_A=0,D^A_aa=0$。有限 EJA 导子内性给 I，原 $q$ 的正 Frobenius 性给原斜伴随。零对象平凡，$A$ 任意，故全部原对象成立。

现在才使用前卷 275.2、314.1 或本卷 323.1 的反向桥：完整 I+SC 给全部原交换子结构与含零分支的共同曲率，从而全部 $\mathsf G_{0h},\mathsf Z_0$ 成立；$\mathsf Z_0$ 包含全部有限测试。两份准备背景各自使用自己的原桥，未用闭背景替换有限生成背景。这也证明结论不依赖哪一次先定静态坐标选择。∎

## 330. 同一刻度、量子公理与完整原过程理论

**定理 330.1（唯一完整新候选的恒等重构）。** 对同一原菜单和同一预选 $t_0$，分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中有

$$
\mathsf C_{\rm fin}(B_*)\Longleftrightarrow\mathsf C_Z(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\tag{330.1}
$$

对应保持全部原数据及全部原合法有限历史。原 $D$ 定向的复表示满足

$$
\begin{gathered}
\mathcal A_A=\bigoplus_s B(H_{A,s}),\qquad
 E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\qquad
D_ab=\tfrac{\mathrm i}{2}[a,b],\\
D_ab=-D_ba,\quad D_aa=D_au=D_ua=0,\quad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{330.2}
$$

全部原实际联合保留经典中心、相关输入及同一取向的普通复张量。全部原准备包括零／奇异／次归一质量，按原两套 Riesz 运输分别表示为

$$
\begin{aligned}
\alpha(y)&=g_A^0(x_\alpha,y)=\tau_A(\rho_\alpha y),
&\rho_\alpha&=B_Ax_\alpha,\\
g_A^0(x,y)&=\tau_A((B_Ax)y),
&q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,
&\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_B T_f^{\dagger_0}B_A^{-1}
&& (f:A\to B).
\end{aligned}
\tag{330.3}
$$

一般 $x_\alpha\ne\widehat x_\alpha$。不等正块权和每个联合自己的 $B_A,\mathcal W_A$ 均不因有限测试而改成因子化。每个原事件 $\Phi_f$ 为 CP/TNI，原完整设备事件和为 TP；对数学效果 $0\le e\le u_A$，原所选精确有限平方根词及其原许可相关执行满足

$$
\Phi_{W_e}(\rho)=\sqrt e\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{330.4}
$$

原占用失败方向 $p_1$ 上每个原失败 $\Psi_\ell:P\to B_\ell$ 的完整输出仍为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其他原方向／中心仍取其原映射。原 F 给同一实现的实际细口和原分组／遗忘；各非零细支保持

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad \Phi_f=\sum_\ell S_\ell,
\quad U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad
\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{330.5}
$$

具名原 $q_\ell$ 与原同数反向资料保留。每份原准备及每条原合法有限历史 $h=(f_1,\ldots,f_m)$ 的末端效果 $w$ 满足

$$
\alpha(T_{f_1}\cdots T_{f_m}w)
=\tau_{A_m}\!\left(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{330.6}
$$

自适应取原记录分支，并行取原实际联合及完整相关输入；分组、遗忘、零、失败、返回、停止取原有箭头和线性和。条件概率仅在原分母正时取比值。

证明。329.1 先恢复完整 I+SC，不使用 sigma。随后同一 $\sigma_{t_0}$ 经前卷 276.1–276.2 和本卷 324.1 排除共同曲率零分支并把共同系数定为一，得到 (330.1)–(330.2)。现在 324.2 的全部原前件逐字成立，其双 Riesz、全事件 R、整个 AC、精确 $N_u$、Xs 和实 Jordan F 的推导逐项给 (330.3)–(330.6)。没有由数学 Kraus 表示新造设备、细记录或共同仪器，没有用数学极限补实际准备。于是有限测试候选完整返回概率、事件、所选词及其完整失败、同数两侧返回和全历史，而不是只恢复状态空间。

324.3 的三类额外物理来源仍分别保留：连续可逆器件及其物理时钟／Hamiltonian／共同作用量标定；独立成功支的共同完整仪器供应；旧同效果设备自己的理想完整输出校准。上述条件重构不替代这些来源。∎

## 331. 被删条件的局部自由与三首原子的准确下界

**定理 331.1（局部严格删除及完整满足族）。** $\mathsf G_{0h}+\mathsf Z_{\rm fin}$ 在单载体右单位层严格弱于 $\mathsf G_{0h}+\mathsf Z_0$。另一方面，325.1 的完整 tagged-CP 满足族分别满足 $\mathsf C_{\rm fin}(B)$ 和 $\mathsf C_{\rm fin}(\mathsf B_{\rm cl})$，包括无实际 $M_2$ 对象或简单块的子族。

证明。局部取

$$
E=H_3(\mathbb C)\oplus H_2(\mathbb C)\oplus\mathbb R^k,
\quad 5+k>p_*,\qquad
D(a,b)=0\oplus\{\operatorname{Tr}(\sigma_zb_2)a_2\}\oplus0.
\tag{331.1}
$$

$\operatorname{Tr}\sigma_z=0$ 给右单位。primitive 输入若在不同块，输出为零；若同在二阶块，输出是第一原子的标量倍，总在两输入的支持角内；其他同源输入输出为零。因此整个 $\mathsf G_{0h}$ 成立。每个高秩首原子的输出恒为零，故不论先定静态坐标如何，全部 $\mathsf Z_{\rm fin}$ 成立。却取二阶块内 $p=(I_2+\sigma_z)/2$、$e=(I_2-\sigma_z)/2$，得 $e\perp p$ 且 $\tau(D(e,p))=1$。这只区分局部前件，没有供应完整原联合或 sigma，不是完整 $B_*$ 的反模型。完整背景中 329.1 恢复全部被删关系，完整模型类未因此扩大。

完整满足族原已满足全部零角迹，故包含本轮任意先定的有限测试；其同一 sigma、两份完整背景、全部过程及无实际 $M_2$ 子族均由 325.1 保留。∎

**定理 331.2（两颗首原子留下的共同盲方向）。** 固定单块 $H_n(\mathbb C)$、$n\ge3$。若迹测试只允许第一输入取任意先定的至多两颗 primitive，即使测试它们的全部正交第二输入，右单位和整个 $\mathsf G_{0h}$ 仍不足以消去非零径向项。三颗互相正交首原子则由 328.1 的有限子集足够。这里的下界仅指这个局部测试类型，不是完整原网络的公理最小性。

证明。两颗不同首原子写成 $e=[v],f=[w]$，调整向量相位使 $v^*w$ 为实。置

$$
H=\mathrm i(vw^*-wv^*),\qquad
\varphi(b)=\operatorname{Tr}(Hb),\qquad
D(a,b)=\varphi(b)a.
\tag{331.2}
$$

$H$ 为非零 Hermitian 且 $\operatorname{Tr}H=0$，因此 $D$ 非零且有右单位。$H$ 在 $v^\perp$ 和 $w^\perp$ 上的压缩均为零，故 $\varphi(p)=0$ 对所有 $p\perp e$ 或 $p\perp f$ 成立，全部许可的迹测试均为零。输出始终沿第一原子，所以整个 $\mathsf G_{0h}$ 成立。若首原子相同或仅选一颗，任选 $w\perp v$ 用同式即可；没有首原子时也可取此例。非零 $H$ 有非零本征值，取相应 primitive $p$ 并另取 $a\perp p$，就有 $\tau(D(a,p))=\varphi(p)\ne0$。因此两颗不足，三颗的足够性恰由 328.1 给出。∎

**定理 331.3（每个高目标的局部标量测试数）。** 固定直和 $E$、高目标 $t$，只考虑第一输入在 $t$ 的有序正交 primitive 对的逐条标量迹测试。若要仅由右单位、$\mathsf G_{0h}$ 及这些测试迫使 (320.1) 的整个 $F_t=0$，则第二输入必须张成整个 $E$；因而至少需要 $\dim_{\mathbb R}E$ 条这种标量测试。定义 327.1 达到此局部数目。

证明。充分性是 (328.2)。若第二输入集的实线性张成是真子空间，取非零实线性泛函 $F$ 消去该子空间，并定义整个输出只在 $t$ 的

$$
\pi_tD(a,b)=F(b)a_t-F(u)a_t\circ b_t,
\qquad \pi_rD(a,b)=0\quad(r\ne t).
\tag{331.3}
$$

这是 (320.1) 中 $\alpha=\ell=0,\eta=-F(u)$ 的合法式。直接代入给右单位；primitive 第一输入若不在 $t$ 则输出为零，若在 $t$ 则两项均在两输入的支持角内，故整个 $\mathsf G_{0h}$ 成立。每条允许测试值恰为 $F(p)=0$。但 $F\ne0$，整个 $E$ 的 primitive 张成给某颗 $p$ 满足 $F(p)\ne0$；在 $t$ 取与它正交的 primitive 便读出该值。故未张成不能强迫消失。有限组每条只提供一个线性评价，维数下界及 327.2 的达到性随即成立。本定理不计原实际联合所额外施加的关系，不宣称全网络需要此测试数、实验实现或含噪最优性。∎

## 332. 三位置拼接与三实维球截面的不同角色

**定义 332.1（有限关系的几何读法）。** 在每个高秩块选三条互相正交的复射线，任意两坐标支撑的 primitive 基元总有一条所选射线在其外。三条射线的正交超平面中的 rank-one 投影遂共同张成整个 Hermitian 空间；其他中心的原子又同时与这三条射线正交。有限迹测试由此读取整个 $F_t$，包括经典块、秩二块和所有其他来源。两条射线会遗漏 (331.2) 的虚交叉方向；第三条射线的正交超平面能看到它。三是这个局部首槽覆盖数，不是对整个原 $\Omega$ 的维数宣言。

在 330.2 恢复后，每对同块不同原子的支持角仍为实四维 $H_2(\mathbb C)$，其无迹截面为三实维 Bloch 球空间；325.2 的 $h,y,z$ 关系与横向 $J_e=2D_e$ 的正交复结构保持。三条正交射线的跨度为复三维，和这个三实维截面承担不同证明步骤。跨中心的支持角仍只有 $\mathbb Re\oplus\mathbb Rp$ 及其一维无迹线。所有这些角沿共享原子拼接成各块的复射影角网，实际联合再把共同导子关系传回全部原对象。

## 333. 成果来源、未证边界与完整白话

**定义 333.1（复用与新增综合的分界）。** 仓内前件固定于 [`e93eafe9cd14a2bdb415a4b1b38f4cb6a6170d78`](https://github.com/the-omega-institute/trureturing/tree/e93eafe9cd14a2bdb415a4b1b38f4cb6a6170d78)：母卷 30.1／67.3 供应原右单位，前卷 246.1 供应静态载体与全部中心对，202.1 供应实际高秩分离；本卷 320.1 供应无迹前件缺席时的全部来源正常形，323–325 供应完整桥、同一刻度和消费者。328–330 的新增综合是将全部零角迹压缩为三个固定首原子上的有限原始迹值，并在不提前使用低秩消失的情况下恢复两份完整背景的全部理论；331 给准确的局部严格性、首槽盲方向和该测试类型的数目下界，均记为 $\texttt{repo-derived}$，不主张文献原创优先权。

Brešar–Špenko，*Functional identities of one variable*，[arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2)，仍只作为既有 320.1 的 $\texttt{literature-attested}$ 中间来源；这里不重证交换多线性迹分类。rank-one 投影基和线性泛函的张成／零化关系是有限矩阵线性代数的成熟中间步骤，不作为独立原创定理。一般保交换／保正交映射分类及纯态层析的邻近结果不直接供应本题的有序向量双线性正常形或原全背景桥，未用它们替代 (328.2)–(329.4)。

**定义 333.2（保持的来源义务）。** 本轮简化精确指：整个 $\mathsf G_{0h}$ 不动，将全体零角迹前件替换成 (327.3) 的有限子集，并删除全部秩二和经典首源的独立迹要求。它不声称全部迹可删，不声称实际测试成本或原全网最小性。具体原 $\Omega$ 对完整 $B_*$、整支持、有限迹和同一 sigma 的原生供应仍各需证明；坐标选择的数学任意性不是该来源证明。321.2 的全删迹径向余量、前卷原静态供应／重叠来源边界及 324.3 的物理标定义务保持。这里只给纸笔条件理论，未取得 Lean/kernel 或经验验证。

**定义 333.3（三扇固定窗就能查清伸缩余量）。** 白话说，原来的整座世界仍在：大小不同的量子街区、经典房间、真实联合和纠缠准备、比较尺、每台设备与细记录、完整失败出口、原分组和遗忘、带原成功数的双返回，以及每条合法有限历史，全部照原样保留。新候选仍要求两颗原子完全错开或恰好重叠一半时，整份推动留在它们共同的小屋里；但总增减这笔账不再逐对检查，而是在每个至少有三个坐标位置的街区，先固定三扇互相错开的窗，再用有限组能拼出整个载体的第二输入查账。每个两坐标片总有第三扇窗站在外面；两扇会漏掉的一条虚交叉方向，第三扇恰能看到。上一轮的正常形说明，这些账值直接读出那种“看第二输入、沿第一输入伸缩”的余量，所以有限组全为零便把它彻底清掉。经典首源的补偿行仍原样保留到真实参考联合，再由逐中心交叉零清除；共同看得见原对象全部区别的高秩目标于是把导子、自守恒、左单位和所有原子对的无迹性带回整个原网。沿用同一张事先选好的刻度单后，复乘法、Born 概率的两套原运输、实际张量和相关输入、全部旧事件、所选平方根词及完整失败、原细口与同数双返回、所有合法有限历史一并接回。这里三扇窗是复坐标中的拼接位置；小屋内另有三实维球截面，两者都不自行变成物理空间、时钟或作用量。原关系从具体世界怎样内生供应，仍按各自缺口继续证明。

## 追加锚 C128333（本行以下为增补区）

## 334. 原实际参考中的单原子匹配几何

**定义 334.1（同一原来源与匹配资料）。** 续接 §§319–333；前卷与母卷仍指 319.1 的两卷。分别固定完整 $B$ 和完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$，同一原 $\Omega,q,D,L,\circ$ 和规范谱迹 $\tau$ 保持。固定 $N\ge\max\{3,p_*\}$，$p_*=\operatorname{rank}E_P\ge2$。对每个非零原对象 $A$，先于原 $D$ 的输出选择前卷 202.1 所供应的同一个实际 $J_A$、原含幺 Jordan/$D$ 单射 $i_A:E_A\to E_{J_A}$ 及有限非空高简单块族 $\mathcal V_A$，满足

$$
n_T>N\quad(T\in\mathcal V_A),\qquad
\bigcap_{T\in\mathcal V_A}\ker(\pi_Ti_A)=\{0\}.
\tag{334.1}
$$

再以 $J_A$ 自己的原身份事件及完整全事件 R，选择一份实际

$$
K_A=J_AR_A,\qquad R_A=P^{\otimes k_A},\quad k_A\ge1,
\qquad n_{V_A}\ge\max_{T\in\mathcal V_A}n_T
\tag{334.2}
$$

及其中一个非经典参考块 $V_A$。记原有序嵌入为 $k:E_{J_A}\to E_{K_A}$、$l:E_{R_A}\to E_{K_A}$，$h_A=ki_A$。每个目标 $U=U_{A,T}=(T,V_A)$ 共用这同一份 $K_A,R_A$。后述静态坐标、原子、线性补偿和基均在考察 $D$ 的值前固定；它们是数学标签，不是新原事件或准备。

**定理 334.2（全部来源的匹配角供应）。** 两份完整背景分别供应定义 334.1 的资料。对每个 $A,T$，可以在 $U$ 内选一颗 primitive $e=e_{A,T}$ 和一个实线性数学映射 $\beta_{A,T}:E_A\to E_{R_A}$，使

$$
z_{A,T}(a):=h_A(a)-l\beta_{A,T}(a)\in W_{A,T}:=\ker L_e
\qquad(a\in E_A).
\tag{334.3}
$$

核取在整个 $E_{K_A}$ 上，所有其他中心的分量保留。更强地，该构造给出 $k(E_{J_A})\subseteq W_{A,T}+l(E_{R_A})$。

证明。前卷 202.1 给 (334.1)。母卷假设 2.5 的全事件 R 明确允许参考矩阵块达到稍后选出的任意有限输入块大小；经定义 10.2，参考取整个原 $P$ 的实际幂。将其用于 $J_A$ 的身份事件，并取有限最大值 $\max_Tn_T$，即得同一份 (334.2)。母卷 30.1 的证明已消费这项充分大实际身份参考；闭背景的 67.1–67.3 保留它。这一步使用完整 R，不把仅有某个参考的 $R_0$ 扩强，也不要求每个指定指数都获许可。

前卷 246.1 在尚未识别原 $D$ 时给全部实际中心对及静态普通／相反表示。对固定 $U$，置 $m=n_T,n=n_{V_A}\ge m$；允许目标相关的转置 $\rho_U,\delta_U$，有

$$
\pi_Uk(x)=\rho_U(x_T)\otimes I_n,
\qquad \pi_Ul(y)=I_m\otimes\delta_U(y_{V_A}).
\tag{334.4}
$$

在所选正交坐标中取

$$
\xi_U=\frac1{\sqrt m}\sum_{r=1}^m v_r\otimes w_r,
\qquad e=j_U|\xi_U\rangle\langle\xi_U|.
\tag{334.5}
$$

$e$ 是整个 $E_{K_A}$ 的 primitive。对每个完整 $x\in E_{J_A}$，令 $y_U(x)$ 仅支撑 $V_A$，且

$$
\delta_U\bigl((y_U(x))_{V_A}\bigr)
=\rho_U(x_T)^{\mathsf T}\oplus0_{n-m}.
\tag{334.6}
$$

转置及上述角包含保持 Hermitian，故 $y_U$ 实线性。最大纠缠向量化的成熟恒等式逐指标给

$$
(\rho_U(x_T)\otimes I_n)\xi_U
=\{I_m\otimes(\rho_U(x_T)^{\mathsf T}\oplus0)}\xi_U.
\tag{334.7}
$$

因此 $k(x)-l(y_U(x))$ 的 $U$ 分量消去 $\xi_U$；它 Hermitian，左右乘 $e$ 均为零，其他中心又与 $e$ 正交，故整个差属于 $\ker L_e$。取 $\beta_{A,T}=y_Ui_A$ 即得 (334.3)。这是原 Jordan 结构和嵌入的匹配关系，没有消费原 $D$ 的交替、导子或左单位。

这里的全 Hermitian 两侧匹配不能仅由满 Schmidt 秩推出。取 $0<\lambda<1$、$\lambda\ne1/2$ 和 $\xi=\sqrt\lambda\,|00\rangle+\sqrt{1-\lambda}\,|11\rangle$。令第一侧输入为 $\sigma_x$。写 $C=\operatorname{diag}(\sqrt\lambda,\sqrt{1-\lambda})$；若存在 Hermitian $b$ 使 $(\sigma_x\otimes I)\xi=(I\otimes b)\xi$，则向量化给

$$
b^{\mathsf T}=C^{-1}\sigma_x C
=\begin{pmatrix}
0&\sqrt{(1-\lambda)/\lambda}\\
\sqrt{\lambda/(1-\lambda)}&0
\end{pmatrix}.
\tag{334.8}
$$

此矩阵不 Hermitian，矛盾。该成熟有限矩阵计算只说明选择匹配锚点的必要区别：上述等 Schmidt 系数构造由原充分参考直接供应，不把一般可逆向量化或通道忠实性改称本题的 Hermitian 正交补偿。∎

## 335. 单原子来源配平的唯一完整候选

**定义 335.1（只在匹配差上要求谱迹配平）。** 固定一套定义 334.1 的先定资料。原整个选中域仍为 $\operatorname{rank}E_X>p_*$，在其中保留

$$
\mathsf G_{0h}:\quad
D^X(e,p)=Q_cD^X(e,p),\qquad
c=\operatorname{supp}(e+p),\quad Q_c=2L_c^2-L_c,
\qquad \tau_X(e\circ p)\in\{0,\tfrac12\}
\tag{335.1}
$$

的全部有序 primitive 对及整个输出。唯一新的迹关系是

$$
\boxed{\mathsf Z_{\rm bal}:\quad
\tau_{K_A}\!\left(D^{K_A}(e_{A,T},z_{A,T}(a))\right)=0
\qquad(A\ne0,\ T\in\mathcal V_A,\ a\in E_A).}
\tag{335.2}
$$

每个目标只有一颗首原子；不同中心对不合并成一颗原子。补偿差及迹均作用在整个实际 $K_A$，不只取目标压缩。令 $m_A=\dim_{\mathbb R}E_A$；336.1 将证明每个所需目标只需至多 $m_A-1$ 条非平凡标量配平。

原菜单、$\mathcal K$、实际 $J_0=P^{\otimes2}$ 和先于 $D$ 固定的同一 $t_0=(e_0,p_0,r_0)\in\mathcal K_{J_0}$ 仍逐字沿用 319.1。保留同一

$$
\sigma_{t_0}:\quad
W_{e_0}(p_0)=2q_{J_0}(D_{p_0}e_0,r_0)+W_{e_0}(2D_{e_0}p_0),
\qquad
\mathsf C_{\rm bal}(B_*)=B_*+\mathsf G_{0h}+\mathsf Z_{\rm bal}+\sigma_{t_0}.
\tag{335.3}
$$

**定义 335.2（完整原范围与约束形式）。** 完整原 $\Omega$、全部原对象、实际有序联合、旧输出、经典中心、不等量子块大小和原正块权保留；原准备、零／次归一质量、实际乘积和全部相关准备保留。设备、端口、细记录、失败身份、整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、实际细化／分组／遗忘、零／失败／返回／停止、具名原同标量两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史全部保留。$B$ 的精确有限正生成与 $\mathsf B_{\rm cl}$ 的闭正生成分别保持。

(335.2) 是原嵌入、原 Jordan 匹配角及原双线性 $D$ 之间的兼容约束。它允许谱原子的迹贡献抵消，不等同于逐原子迹零的字面子集。其有限方程数不是实际读数或认证成本；原对象集合也无需有限。LU、SC、交替、导子、斜伴随、原 $D$ 的理想保持均留作结论；不添加模身份、primitive／等距嵌入、直接 $AP$、共同指数、实际 $M_2$、任意仪器、时钟或 $\hbar$，全部原已供应的标量两侧有序接口保持。

## 336. 一颗首原子的迹只需控制原来源限制

**定理 336.1（匹配差的有限表示与补偿独立性）。** 在 $B_*+\mathsf G_{0h}$ 中，对定义 334.1 的每个目标 $U$，存在实线性 $F_U:E_{K_A}\to\mathbb R$，使对全部完整输入

$$
\pi_UD(x,y)=\alpha_U\,\mathrm i[x_U,y_U]+x_UF_U(y),
\qquad F_U\circ l=0,\quad F_U(u_{K_A})=0.
\tag{336.1}
$$

并且对所有 $b\in E_{K_A}$，

$$
D(e,b)=j_U\pi_UD(e,b),\qquad
\tau_{K_A}(D(e,b))=F_U(b),\qquad
\tau_{K_A}(D(e,z_{A,T}(a)))=F_U(h_A(a)).
\tag{336.2}
$$

因此 (335.2) 恰为 $F_U\circ h_A=0$；它不先要求 $F_U$ 在整个 $E_{K_A}$ 消失。配平值不依赖哪一个匹配补偿，也不依赖原对象基的选择。

证明。原右单位由母卷 30.1／67.3 独立供应。$n_U=n_Tn_{V_A}\ge4$ 且整个 $K_A$ 总秩大于 $p_*$，所以无迹前件缺席的完整来源定理 320.1 适用。先保留其中 $\eta_U$、所有经典首源 $\ell_{Us}$ 及经典自输入补偿，再按 321.1 使用同一实际有序交叉零：非经典因子的无迹输入消去 $\eta_U$，各实际经典中心对逐项消去 $\ell_{Us}$，并给 $F_U\circ l=0$。这正给 (336.1)，没有加入反向交叉零。

320.1 证明中的非经典首源整输出局部性仅使用右单位及整支持：同源的全部输出在首源，异源的非经典首源输出也在首源。第二输入逐源展开，所以固定 $e\in U$ 的整个输出在 $U$；这里不调用含额外迹前件的 312.1 陈述。现在对 (336.1) 取整个规范谱迹，交换子迹为零且 $\operatorname{Tr}(e)=1$，给 (336.2) 前两式。再用 $F_U\circ l=0$ 即给最后一式。不同补偿的差仍来自 $l(E_{R_A})$，故同一配平值不变。

固定先定实基 $u_A,a_1,\ldots,a_{m_A-1}$。含幺性给 $h_A(u_A)=u_{K_A}=l(u_{R_A})$，故单位方向的配平已为零；线性性遂使 (335.2) 等价于该基其余 $m_A-1$ 条。每个 $z_j=z_{A,T}(a_j)\in\ker L_e$ 都在整个 Jordan 正交角内有有限谱分解

$$
z_j=\sum_\nu c_{j\nu}p_{j\nu},\qquad p_{j\nu}\perp e,
\qquad
\sum_\nu c_{j\nu}\tau_{K_A}(D(e,p_{j\nu}))=0.
\tag{336.3}
$$

Hermitian 块中 $\ker L_e$ 正是消去 $\xi_U$ 的整个 Hermitian 正交角，其他中心完整包含其中，故谱原子确实都是整个 $K_A$ 的 primitive 并与 $e$ 正交。谱选择及系数仅由静态 $z_j$ 决定，和 $D$ 无关。不同谱表示给同一线性配平；每项分别为零是额外条件。∎

## 337. 有限源像配平返回全部原对象

**定理 337.1（两份完整背景各自的无标定等价）。** 对任意一套先定匹配资料，分别有

$$
\begin{aligned}
B+\mathsf G_{0h}+\mathsf Z_{\rm bal}
&\Longleftrightarrow B+\mathrm I+\mathrm{SC}
\Longleftrightarrow B+\mathsf G_{0h}+\mathsf Z_0,\\
\mathsf B_{\rm cl}+\mathsf G_{0h}+\mathsf Z_{\rm bal}
&\Longleftrightarrow\mathsf B_{\rm cl}+\mathrm I+\mathrm{SC}
\Longleftrightarrow\mathsf B_{\rm cl}+\mathsf G_{0h}+\mathsf Z_0.
\end{aligned}
\tag{337.1}
$$

原导子律、SC、LU、交替、原 $q$ 斜伴随及全部原零／半角无迹覆盖整个原范围。

证明。固定任意原非零 $A$。336.1 先由该对象自己的配平给每个所需 $F_U\circ h_A=0$，所以只对原源像已有

$$
\pi_UD^{K_A}(h_A(a),h_A(b))
=\alpha_U\,\mathrm i[(h_A(a))_U,(h_A(b))_U]
\qquad(a,b\in E_A).
\tag{337.2}
$$

并未先把右式推广成整个 $E_{K_A}\times E_{K_A}$ 的纯交换子。

对原任意 $a,b,c$，将导子缺陷

$$
r_A=D^A_a(b\circ c)-(D^A_ab)\circ c-b\circ(D^A_ac)
\tag{337.3}
$$

及 $D^A_aa$ 沿同一原含幺 Jordan/$D$ 嵌入 $h_A$ 运输。(337.2) 对源输入、源乘积及源 $D$ 输出均成立，因此交换子的 Leibniz 律逐目标给

$$
\pi_Uh_A(r_A)=0,\qquad \pi_Uh_A(D^A_aa)=0.
\tag{337.4}
$$

静态 (334.4) 的 $x_T\mapsto\rho_U(x_T)\otimes I_{V_A}$ 单射，(334.1) 的同一目标族遂共同分离整个原 $E_A$，得 $r_A=0,D^A_aa=0$。有限 EJA 导子内性给原 I，原 Frobenius $q_A$ 给原斜伴随；SC 极化及右单位再给交替与 LU。零对象平凡，$A$ 任意，所以全部原对象及实际联合均恢复。对某个 $A$ 的证明只使用 $K_A$ 的原支持分类与该源的配平，不以 $K_A$ 已恢复 SC 为前件，因此没有向更大对象递归假设结论。

反向在各自完整背景上复用 323.1、329.1：I+SC 给全部原交换子形式和含零分支的共同曲率，所以整个 $\mathsf G_{0h}$、全部 $\mathsf Z_0$ 成立。每条 (336.3) 随即成立，故 $\mathsf Z_{\rm bal}$ 成立。两份准备背景各用自己的入口；不把数学闭包变成原实际准备。这个等价也表明，完整背景中的候选结论不依赖哪套先定匹配资料。∎

## 338. 同一刻度下的完整量子与过程理论

**定理 338.1（完整候选的恒等重构）。** 对同一原菜单、$t_0$ 及 $\sigma_{t_0}$，分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中有

$$
\mathsf C_{\rm bal}(B_*)\Longleftrightarrow
\mathsf C_{\rm fin}(B_*)\Longleftrightarrow
\mathsf C_Z(B_*)\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\tag{338.1}
$$

全部对应对原对象、原准备、设备／记录／失败及每条原合法有限历史都是恒等。由同一原 $D$ 定向的复表示满足

$$
\begin{gathered}
\mathcal A_A=\bigoplus_s B(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\qquad D_ab=\tfrac{\mathrm i}{2}[a,b],\\
D_aa=D_au=D_ua=0,\qquad D_ab=-D_ba,\qquad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{338.2}
$$

全部原实际联合具有同一取向的普通复张量，全部原经典中心及相关输入保持。原比较 $g_A^0$ 和原 $q_A$ 的两套运输保持区分：

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\rho_\alpha&=B_Ax_\alpha,&\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)&=\tau_A(\rho_\alpha y),&\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}&&(f:A\to B).
\end{aligned}
\tag{338.3}
$$

一般 $x_\alpha\ne\widehat x_\alpha$；各联合各取自己的 $B_A,\mathcal W_A$，不等正权和非因子化比较均保留。原准备含零、奇异和次归一质量；全部旧事件 $\Phi_f$ 为 CP/TNI，原完整设备的事件和为 TP。对每个数学效果 $0\le e\le u_A$，原所选精确有限平方根词和原许可相关执行满足

$$
\Phi_{W_e}(\rho)=\sqrt e\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{338.4}
$$

原占用失败方向 $p_1$ 的每个原失败 $\Psi_\ell:P\to B_\ell$ 保持完整输出 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；其他原方向和中心取原映射。原 F 供应同一实现的实际细口及原分组／遗忘；非零细支的具名原资料仍满足

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad \Phi_f=\sum_\ell S_\ell,
\quad U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad \mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{338.5}
$$

原 $q_\ell$ 与同数反向资料不归一掉。每份原准备、每条原合法有限历史 $(f_1,\ldots,f_r)$ 及原末端效果 $w$ 都有

$$
\alpha(T_{f_1}\cdots T_{f_r}w)
=\tau_{A_r}\!\left(w\,\Phi_{f_r}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{338.6}
$$

原顺序、自适应记录分支、实际并行联合与完整相关输入、细化、分组、实际遗忘、零／失败／返回／停止逐项保持；条件概率仅在原分母正时取比值。

证明。337.1 先恢复全域 I+SC，前卷 275–276 和本卷 324.1、330.1 再给含零分支的共同曲率 $\kappa\ge0$。现在才使用同一预选 $\sigma_{t_0}$，由原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 得 $\kappa=1$。不重标 $D$，不重选标签。此后 330.1 的全部原入口成立，逐项复用其概率双运输、原实际张量、全事件 R、整个 AC、精确 $N_u$、Xs、实 Jordan F 和逐原箭头迭代，得到 (338.2)–(338.6)。没有由单支的数学表示补造共同仪器或新细记录。

324.3 的三类物理来源继续分别保留：连续可逆器件及物理时钟／Hamiltonian／共同作用量标定；独立成功支的共同完整仪器；旧同效果设备自己的理想完整输出校准。∎

## 339. 原来源已恢复不等于局部联合余量已消失

**定理 339.1（非空满足族与单联合的隐藏方向）。** 325.1 的完整 tagged-CP 满足族分别满足 $\mathsf C_{\rm bal}(B)$ 与 $\mathsf C_{\rm bal}(\mathsf B_{\rm cl})$，包括无实际 $M_2$ 对象或简单块的子族。同时存在一个单联合数学片段，满足右单位、整个 $\mathsf G_{0h}$、两个因子的 $D$ 保持、有序交叉零，以及一颗匹配原子的全部正交迹零，却有非零联合径向项。

证明。完整满足族的标准 $D=\mathrm i[a,b]/2$ 在任意第二输入上迹零，故每套匹配资料的全部 (335.2) 成立；原全部背景、同一 sigma、实际过程及历史沿 325.1 保持。

局部片段取两个 $H_m(\mathbb C)$ 因子及 $E=H_{m^2}(\mathbb C)$，$m\ge2$；两因子 $D$ 均取零。取最大纠缠 $e=|\xi\rangle\langle\xi|$、非零无迹 Hermitian $A_0$，令

$$
H=\mathrm i[A_0\otimes I_m,e],\qquad
F(b)=\operatorname{Tr}(Hb),\qquad D(a,b)=F(b)a.
\tag{339.1}
$$

$H$ Hermitian 且迹零。若 $H=0$，则 $(A_0\otimes I)\xi$ 沿 $\xi$；向量化使 $A_0$ 为标量，与无迹非零矛盾。因此 $H\ne0$。交换子是相对于 $e$ 的交叉块，故其 $e^\perp$ 压缩为零；两个数学部分迹均为零：第一因子上的迹循环消去一个，另一个是 $\mathrm i[A_0,I_m/m]=0$。所以

$$
F|_{\ker L_e}=0,
\qquad F(x\otimes I_m)=F(I_m\otimes y)=0,
\qquad F\ne0.
\tag{339.2}
$$

$F(u)=0$ 给右单位；primitive 首输入的输出沿自身，所以整个支持条件成立。两因子范围上的 $F$ 为零，使两个零 $D$ 都被标准因子嵌入保持，原有序交叉零也成立。所有 $p\perp e$ 都有 $\tau(D(e,p))=0$，因而该锚点上的全部正交配平成立。但是取 $H$ 的非零本征值对应 primitive $p$，再取另一 primitive $f\perp p$，则 $\tau(D(f,p))=F(p)\ne0$。

这只说明该单联合片段仍能隐藏相关方向；它未供应完整 $B_*$ 的全部参考、事件、sigma 和各原对象自己的配平资料，不是完整候选的反模型。337.1 只在每个 $A$ 的回传阶段要求 $F_U\circ h_A=0$；全域 I+SC 取得以后，全部联合余量才被原全域结论消去。331.2–331.3 的局部原始测试下界保持：这里同时改变了来源条件、配平形式及局部恢复目标。∎

## 340. 一个共同原子上的两侧作用与更大结构

**定义 340.1（匹配差的几何）。** (334.7) 将第一侧作用沿同一向量转置搬到第二侧。等维部分可辨认为矩阵空间上的左右作用：$\xi_U$ 对应归一的单位矩阵，$(M\otimes I-I\otimes M^{\mathsf T})\xi_U=0$。新关系检验的是这两侧作用相抵后落入 $\ker L_e$ 的来源方向；$F_U$ 对第二侧已经为零，因此配平恰读取原来源在商 $E_{K_A}/l(E_{R_A})$ 中的像。该商是证明工具，不是原过程对象。原单位在此商中为零，对应每目标至多 $m_A-1$ 条方程。每个目标的一颗原子只是同一内在约束的坐标，补偿和基不改变 336.2 的值。

同块两原子的支持角仍为实四维 $H_2(\mathbb C)$，其无迹部分为三实维球空间；原 325.2 的横向复结构不变。更大的结构包含原复射影角网与实际张量中两侧共享的向量化关系。跨中心的角仍只有 $\mathbb Re\oplus\mathbb Rp$ 及一维无迹线；单联合锚点不合并这些中心，也不把复坐标维数或球截面解释成物理空间维数。


## 341. 来源、内生边界与完整白话

**定义 341.1（承重来源与新增综合）。** 仓内来源固定于 [`a36e4c0700e7cfa4c51e676356af67156c416d02`](https://github.com/the-omega-institute/trureturing/tree/a36e4c0700e7cfa4c51e676356af67156c416d02)。母卷 2.5、10.2、30.1、67.1–67.3 供应同一原全事件的充分大实际参考；前卷 202.1、246.1 供应整个原对象的高秩分离和全部静态中心对。本卷 320.1 的无迹前件缺席证明供应整输出局部性，321.1 供应完整来源的径向残余及 $F_U\circ l=0$，323–330 供应全域尺度、同一 sigma 及完整消费者。新推导不把含额外迹前件的旧局部性陈述用作无迹删除的入口。

D’Ariano–Lo Presti，*Imprinting Complete Information about a Quantum Channel on Its Output State*，DOI [10.1103/PhysRevLett.91.047902](https://doi.org/10.1103/PhysRevLett.91.047902)，[作者原文第 1 页 (2)–(5)](https://www.qubit.it/~lopresti/PRLfaith.pdf)，使用最大纠缠向量化和同基转置。这里只消费这些 $\texttt{literature-attested}$ 矩阵工具；334.2 证明中的指标恒等式与有限矩阵检验是成熟中间步骤，不单独取得原创地位。原文的通道忠实性、反演及层析资源不作为本题的原实际供应。Brešar–Špenko [arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2) 仍只作为既有 320.1 的交换多线性迹中间来源，不把 primitive 条件未经证明地复化。

新增承重综合是：用原充分参考构成完整来源的匹配差，识别只须消去 $F_U\circ h_A$，以单目标一颗原子的至多 $m_A-1$ 条来源配平返回整个原 $A$，再对全部原对象恢复两份完整量子与过程理论。其地位是 $\texttt{repo-derived}$，不据文献检索未命中主张优先权。配平值的补偿／基独立性和 339.1 的局部隐藏方向给出该综合的准确范围。

**定义 341.2（仍需内生的部分）。** 匹配角及补偿由所声明的完整原背景供应；新增配平仍需从具体原 $\Omega$ 的实际关系证明，并未从 $B_*+\mathsf G_{0h}$ 无条件推出。将它写成既有定义间的约束，不自动证明原世界满足它。全删迹的 321.2 残余、前卷既定原来源边界、普遍第二槽来源及 324.3 的各物理来源义务保持。本轮简化指单目标首原子数及来源配平的有限维上界，未主张全部原始迹值逐项为零、实际认证更便宜、原全网公理最小性或经验起源。本文为纸笔条件理论，未取得 Lean/kernel 或经验验证。

**定义 341.3（一颗共同珠子上的两边相抵）。** 白话说，整座原世界照样保留：量子街区、经典房间、大小不同的中心、真实联合和纠缠准备、比较尺、每台设备与细记录、完整失败出口、原分组和遗忘、带原成功数的两侧返回，以及全部合法有限历史。新候选仍让零角和半角的整份推动留在共同小屋里；查总账时，每个需要的分离目标只用一颗由原充分参考容纳的共同珠子。左边怎样作用，就在右边选一个转置补偿；二者之差碰不到这颗珠子，于是落进它的正交角。把原对象的有限组方向这样配好，只要求每个差的谱原子贡献合起来为零，允许各项相抵。原交叉零早已查清右边的账，所以这些有限配平只清掉原对象像里的径向伸缩，不必先看清整个大联合。高秩目标共同看得见原对象的每个区别，便把导子律、自守恒和左单位带回；每个原对象都这样完成以后，再沿用同一张刻度单，复乘法、Born 概率的两套原运输、实际张量、全部旧事件、平方根词及完整失败、原细口与同数双返回、全部合法有限历史一并接回。共同珠子和两侧匹配属于更大的张量与射影角网；三实维球截面仍是其中的小屋结构，不能自行变成物理空间、时钟或作用量。这些来源配平如何由具体原世界内生满足，仍是下一层的证明义务。

## 追加锚 C128341（本行以下为增补区）

## 342. 用原中心的迹中性替代所选匹配资料

**定义 342.1（唯一新增候选与原选中域）。** 沿用 319.1、335.2 的完整原签名、原菜单及同一预选 $t_0$。分别取完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$；静态复直和只由前卷 246.1 与母卷 85.2 取得。令 $Z(E_X)$ 为原 Jordan 代数的中心；在任一静态坐标中，它是各简单块的标量单位之直和。规范谱迹仍为 $\tau_X=\sum_s\operatorname{Tr}_{n_s}$，不换成原加权比较 $q_X$。保留整个 $\mathsf G_{0h}$，只在原选中域增加

$$
\boxed{\mathsf Z_{\rm cen}^{>}:
\quad\tau_X\!\left(D^X(z,b)\right)=0
\quad\left(\operatorname{rank}E_X>p_*,\ z\in Z(E_X),\ b\in E_X\right).}
\tag{342.1}
$$

唯一完整候选为

$$
\mathsf C_{\rm cen}(B_*)
:=B_*+\mathsf G_{0h}+\mathsf Z_{\rm cen}^{>}+\sigma_{t_0}.
\tag{342.2}
$$

这里不再选匹配原子、补偿映射、来源基或参考剖面作为公理资料。证明可以使用原背景已经供应的实际参考，候选本身只读取原中心、原 $D$ 和规范迹。$\mathsf G_{0h}$ 的零／半角、两个输入次序及整个输出支持仍逐字沿用 (319.1)；$\sigma_{t_0}$ 仍是 (319.2) 的同一原等式，不重标 $D$，不重选刻度。

**定义 342.2（完整量词及简化口径）。** 原全部对象、实际有序联合、旧输出、经典中心、不等块大小、原正权、全部原准备与相关准备、零／次归一质量均保留。整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、原设备／端口／细记录／失败身份、完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史均沿 335.2 保留。两份准备背景分别使用各自的精确有限正生成与闭正生成。

LU、SC、交替、导子、斜伴随、理想保持均不是输入；也不增加模身份、primitive／等距嵌入、直接 $AP$、共同参考指数、实际 $M_2$、任意仪器、时钟或 $\hbar$。本处简化精确指删除公理中的辅助匹配选择，改用中心的内在标量约束；不声称标量方程数少于所有旧候选，或原实际取得、认证成本下降。

## 343. 两次实际身份参考给每个原对象的完整正常形

**定理 343.1（无迹前件的全对象径向正常形）。** 分别在 $B_*+\mathsf G_{0h}$ 中，每个原非零对象 $A$ 都有

$$
E_A=\bigoplus_{s\in S_A}H_{n_s}(\mathbb C),\qquad
\pi_sD^A(a,b)=\gamma_s\,\mathrm i[a_s,b_s]+a_sF_s(b),
\qquad F_s(u_A)=0
\tag{343.1}
$$

对全部完整输入 $a,b\in E_A$ 成立。其中 $F_s:E_A\to\mathbb R$ 实线性，$\gamma_s$ 实数；经典块约定 $\gamma_s=0$。原对象的经典块、二阶块、跨中心第二输入均包括在内，没有先假设原 $D$ 理想保持。

证明。原右单位只用母卷 30.1／67.3。固定原 $A$ 的身份事件。母卷 2.5 的完整 R 经 10.2 允许充分大的实际参考，故可选原实际

$$
J=AR^{(0)},\qquad R^{(0)}=P^{\otimes k_0},
\qquad V_0\subset E_{R^{(0)}},\quad d_0=n_{V_0}>p_*.
\tag{343.2}
$$

$p_*\ge2$，故 $d_0\ge3$。这只选实际许可的某个指数；不是由弱 $R_0$ 推出任意指数。两份背景分别保留这项完整 R。

记原第一槽嵌入为 $i:E_A\to E_J$。前卷 246.1 的全部中心对给每个原 $s$ 一个目标 $T_s=(s,V_0)$，大小 $n_sd_0$；在目标自己的静态坐标中，$\pi_{T_s}i(a)$ 是 $a_s\otimes I_{d_0}$ 的普通或转置表示。其他原中心的输入在该目标投影为零。因此这些目标共同分离整个 $E_A$，包括原经典源，并非只分离原量子块。

再对 $J$ 自己的原身份事件使用同一完整 R，选择实际

$$
K=JR^{(1)},\qquad R^{(1)}=P^{\otimes k_1},
\qquad V_1\subset E_{R^{(1)}},\quad d_1=n_{V_1}\ge2.
\tag{343.3}
$$

原嵌入记为 $k,l$，$h=ki$。每个 $U_s=(T_s,V_1)$ 大小 $n_sd_0d_1>p_*$，整个 $K$ 遂在原选中域；$T_s,V_1$ 均非经典。于是 321.1 对整个 $E_K\times E_K$ 给

$$
\pi_{U_s}D^K(x,y)
=\alpha_{U_s}\,\mathrm i[x_{U_s},y_{U_s}]
+x_{U_s}F_{U_s}(y),\qquad
F_{U_s}(u_K)=0,\quad F_{U_s}\circ l=0.
\tag{343.4}
$$

此处消费 320.1、321.1 的完整来源证明：先保留 $\eta$、所有经典首源项及经典自输入补偿，再由原有序交叉零逐项消去。没有先丢经典项，也没有加入反向交叉零或迹前件。

两次静态坐标组合后，可在 $U_s$ 上写

$$
\pi_{U_s}h(a)=\varphi_s(a_s),\qquad
\varphi_s(x)=W_s\bigl(x^{\mathsf T^{\varepsilon_s}}\otimes I_{d_0d_1}\bigr)W_s^*,
\quad\varepsilon_s\in\{0,1\}.
\tag{343.5}
$$

这里的幺正坐标 $W_s$、逐目标取向和放大均只属于该数学表示，不要求全网已有共同取向。$\varphi_s$ 单射、含幺且保持 Jordan 乘法；对 Hermitian 输入满足

$$
\mathrm i[\varphi_s(x),\varphi_s(y)]
=(-1)^{\varepsilon_s}\varphi_s(\mathrm i[x,y]).
\tag{343.6}
$$

原 $D$ 保持将 (343.4) 限制到 $h(a),h(b)$。其左端等于 $\varphi_s(\pi_sD^A(a,b))$。令 $F_s=F_{U_s}\circ h$，取 $\gamma_s=(-1)^{\varepsilon_s}\alpha_{U_s}$；当 $n_s=1$ 时取零。由 (343.6) 并消去单射 $\varphi_s$，便得 (343.1)。含幺性给 $F_s(u_A)=0$。这对每个 $s$、全部源输入成立，故穷尽整个原输出；无需先在 $J$ 或 $K$ 上取得 SC，也无需递归假设更大对象已经恢复。∎

**定理 343.2（内在中心读数及选择独立性）。** 记原最小中心单位为 $z_s=j_s(I_{n_s})$。在 343.1 的同一背景中，整个原输出满足

$$
\begin{aligned}
D^A(z_s,b)&=F_s(b)z_s,&
F_s(b)&=\frac{\tau_A(D^A(z_s,b))}{n_s},\\
\mathcal R_A(b)&:=\sum_s\frac{\tau_A(D^A(z_s,b))}{n_s}z_s,&
D^A(a,b)&=\bigoplus_s\gamma_s\,\mathrm i[a_s,b_s]+a\circ\mathcal R_A(b),\\
\mathcal R_A(u_A)&=0,&D^A(u_A,b)&=\mathcal R_A(b)\in Z(E_A).
\end{aligned}
\tag{343.7}
$$

$F_s$ 和 $\mathcal R_A$ 不依赖证明中选择的参考、目标或转置坐标；$n_s\ge2$ 时 $\gamma_s$ 在固定原块坐标中也唯一。

证明。将 $a=z_s$ 代入 (343.1)：该中心的交换子为零，其他每个中心的第一坐标为零，故整输出恰为 $F_s(b)z_s$。其规范迹为 $n_sF_s(b)$，给出选择无关的读数。对所有 $s$ 求和即得其余式。固定这些 $F_s$ 后，两个正常形之差为 $(\gamma_s-\gamma'_s)\mathrm i[x,y]$；每个 $n_s\ge2$ 块都有不交换的 Hermitian $x,y$，故系数相等。中心单位的置换和 Jordan 坐标变换保留迹及上述中心元。∎

## 344. 只在原高秩域查中心便足以回传全域

**定理 344.1（选中域中心迹的全域下降）。** 在两份完整 $B_*$ 中，$\mathsf Z_{\rm cen}^{>}$ 等价于对全部原对象要求的

$$
\mathsf Z_{\rm cen}:\qquad
\tau_A(D^A(z,b))=0\quad(z\in Z(E_A),\ b\in E_A).
\tag{344.1}
$$

本结论不消费 $\mathsf G_{0h}$、LU、SC 或 $q$ 的因子化。

证明。全域蕴含选中域是限制。反向固定任意非零原 $A$，用其原身份事件的完整 R 选足够大的实际 $J=AR$，使 $\operatorname{rank}E_J>p_*$。写 $E_R=\bigoplus_tH_{m_t}(\mathbb C)$。全部静态中心对使

$$
i(z_s)=\sum_tz_{(s,t)}\in Z(E_J),\qquad
\tau_J(i(x))=\sum_{s,t}m_t\operatorname{Tr}_{n_s}(x_s)
=\tau_R(u_R)\tau_A(x).
\tag{344.2}
$$

逐对转置及幺正坐标不改变该式，$\tau_R(u_R)=\sum_tm_t>0$。中心线性组合也被 $i$ 送入中心。原 $D$ 保持及选中域中性于是给

$$
0=\tau_J(D^J(i(z),i(b)))
=\tau_J(i(D^A(z,b)))
=\tau_R(u_R)\tau_A(D^A(z,b)).
\tag{344.3}
$$

消去正因子即得全域中性。这里只计算规范矩阵谱迹，没有把它当作实际丢弃，也没有使用 $g^0$ 或 $q$ 的张量因子化。零对象结论平凡。∎

**定理 344.2（两份背景各自的无标定等价）。** 分别有

$$
B_*+\mathsf G_{0h}+\mathsf Z_{\rm cen}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC}
\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{\rm bal}.
\tag{344.4}
$$

任一套 334.1 的旧先定匹配资料均可用于最右式。左式恢复原全域的 LU、交替、导子、SC、原 $q$ 斜伴随及全部原零／半角无迹。

证明。先用 344.1 取得每个原对象的中心中性，再用 343.1–343.2。所有 $F_s$ 为零，故整个原 $D$ 是逐块交换子。对固定第一输入，它满足 Jordan Leibniz 律，且 $D^A(a,a)=0$；有限 EJA 导子内性给原 I，或直接将这些交换子视为各块的内导子。极化给交替，右单位给 LU；原 $q$ 是各块的正权 Frobenius 型，逐块迹循环给斜伴随。经典块上的 $D$ 及全部跨中心输出也为零，而非留作另一个前件。

反向在完整 $B_*+\mathrm I+\mathrm{SC}$ 上，323.1、329.1 的同一全域共同曲率结论包括零分支，并给整个 $\mathsf G_{0h}$ 和全部输入的交换子迹零，故特别给 (342.1)。与 $\mathsf Z_{\rm bal}$ 的等价直接复用 337.1，不重证原匹配候选。两份准备背景各用其自身静态入口和保单位供应，不将闭包中的数学准备补成实际准备。∎

## 345. 同一原刻度下的完整量子与过程理论

**定理 345.1（中心候选的恒等重构）。** 固定同一原菜单、$t_0$、$D$ 及原 $\sigma_{t_0}$，分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中有

$$
\mathsf C_{\rm cen}(B_*)\Longleftrightarrow
\mathsf C_{\rm bal}(B_*)\Longleftrightarrow
\mathsf C_{\rm fin}(B_*)\Longleftrightarrow
\mathsf C_Z(B_*)\Longleftrightarrow
\mathsf C_{\rm support}(B_*).
\tag{345.1}
$$

这些对应对全部原对象、准备、实际联合、设备／记录／失败及原合法有限历史都是恒等。由同一原 $D$ 定向的复代数满足

$$
\begin{gathered}
\mathcal A_A=\bigoplus_sB(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\qquad
D_ab=\tfrac{\mathrm i}{2}[a,b],\qquad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{345.2}
$$

原双概率运输及原事件的对应为

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&
q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\rho_\alpha&=B_Ax_\alpha,&
\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)&=\tau_A(\rho_\alpha y),&
\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}&&(f:A\to B).
\end{aligned}
\tag{345.3}
$$

全部原实际联合是同一取向的普通复张量；每个联合使用自己的 $B_A,\mathcal W_A$，一般 $x_\alpha\ne\widehat x_\alpha$。所有原正权、经典中心、不等块、零／奇异／次归一准备及全部相关准备保持。原旧事件为 CP/TNI，原完整设备事件和为 TP。每个原所选精确有限平方根词及其原相关执行给 $\rho\mapsto\sqrt e\rho\sqrt e$ 与 $X\mapsto(\sqrt e\otimes I)X(\sqrt e\otimes I)$。每个原占用指针方向 $p_1$ 的原失败 $\Psi_\ell$ 保持完整输出 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；其他原方向和中心保留其原映射，不把失败只换成概率质量。

原 F 给同一实现的实际细口和原分组／遗忘；每个非零细支的具名原资料仍满足

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\qquad
\Phi_f=\sum_\ell S_\ell,\qquad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad
\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\qquad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\qquad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{345.4}
$$

保留原 $q_\ell$ 及同数反向资料，不将成功数归一成一。对原准备、原末端效果 $w$ 和每条原合法有限历史 $(f_1,\ldots,f_r)$，

$$
\alpha(T_{f_1}\cdots T_{f_r}w)
=\tau_{A_r}\!\left(w\,\Phi_{f_r}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{345.5}
$$

证明。344.2 先恢复全域 I+SC，然后沿 338.1 的同一推导取得含零分支的共同曲率 $\kappa\ge0$。只在这时消费原 $\sigma_{t_0}$：原正 $w_0$ 给 $(1-\kappa)w_0/4=0$，故 $\kappa=1$。338.1 的全部入口至此逐项成立，直接复用其完整消费者，得到 (345.1)–(345.5)。全事件 R 针对所有相关准备，闭背景只在同一原执行上作连续正延拓；整个 AC、精确 $N_u$ 与 Xs 给原所选词和其完整失败，实 Jordan F 及具名同数两侧资料给原细记录与返回。逐原箭头的双对偶迭代涵盖顺序、原实际记录的自适应分支、实际并行联合及相关输入、细化、分组、实际遗忘、零／失败／返回／停止；只有原分母正时才取条件概率。此复用不供应任意新的仪器或连线。324.3 的连续器件／物理时钟／Hamiltonian／作用量、独立成功支的共同完整仪器及旧同效果设备的完整输出校准仍各需原来源。∎

## 346. 旧匹配迹其实读取一个原中心的径向电荷

**定理 346.1（源像匹配与中心读数的精确对应）。** 对 343.1 的两次实际参考，可将第二参考选到 $d_1\ge\max_sn_s$。每个原中心 $s$ 都能在 $U_s$ 中选 primitive $e_s$ 及实线性数学补偿 $\beta_s:E_A\to E_{R^{(1)}}$，使在整个 $E_K$ 上

$$
z_s^{\rm match}(a):=h(a)-l\beta_s(a)\in\ker L_{e_s},\qquad
\tau_KD^K(e_s,z_s^{\rm match}(b))
=\frac{\tau_AD^A(z_s,b)}{n_s}.
\tag{346.1}
$$

这里 $e_s$ 对第二参考的 Schmidt 秩仅为 $n_s$；原经典源可用乘积原子。对这样的 Hermitian 全源像匹配，$n_s$ 是该方法的最小 Schmidt 秩，不是公理数、原实际测试或全网认证的下界。

证明。在允许转置的目标坐标中吸收 (343.5) 的坐标变换，源像为 $a_s\otimes I_{d_0}\otimes I_{d_1}$。取放大因子中的单位向量 $\chi$、原源的正交基 $v_r$、第二参考中 $n_s$ 个正交向量 $w_r$，置

$$
\xi_s=\frac1{\sqrt{n_s}}\sum_{r=1}^{n_s}v_r\otimes\chi\otimes w_r,
\qquad e_s=|\xi_s\rangle\langle\xi_s|.
\tag{346.2}
$$

在第二参考所选角中取与原 $a_s$ 相应的转置矩阵，在其余坐标取零，并补偿静态坐标中的转置，得到 Hermitian 线性 $\beta_s(a)$。两侧在 $\xi_s$ 上作用相同，故 Hermitian 差消去 $\xi_s$；这等价于其在目标 $U_s$ 中属于 $\ker L_{e_s}$。其他中心与 $e_s$ Jordan 正交，故整个差均在同一核，不删除其他中心。

320.1 证明的非经典首源整输出局部性及 (343.4) 给

$$
\tau_KD^K(e_s,y)=F_{U_s}(y).
\tag{346.3}
$$

这里不调用含额外迹前件的 312.1 陈述。由 $F_{U_s}\circ l=0$，左边在匹配差上等于 $F_{U_s}(h(b))=F_s(b)$；343.2 遂给 (346.1)。因此旧式来源配平的值可直接用原中心读数表达，不需把所选原子和补偿提升为新候选的资料。

本证明内部的最小秩判据是成熟 Hermitian twin-observable 工具的有限矩阵形式。将任意归一匹配向量写成系数矩阵 $C$，源矩阵 $M$ 有 Hermitian 补偿 $N$ 当且仅当 $MC=CN^{\mathsf T}$ 可解；必要性由该式及其伴随给 $[M,CC^*]=0$。反向令 $R=CC^*$，在其支持上写 $C=\sqrt R\,W$，其中 $WW^*=\operatorname{supp}R$。若 $[M,R]=0$，取 $N^{\mathsf T}=W^*MW$ 并在核中取零，则 $N$ Hermitian 且 $CN^{\mathsf T}=MC$。对所有源矩阵 $M=a_s\otimes I_{d_0}$ 同时成立的条件恰为

$$
R\in(M_{n_s}\otimes I_{d_0})',\qquad
R=\frac{I_{n_s}}{n_s}\otimes Q,\quad
Q\ge0,\quad\operatorname{Tr}Q=1.
\tag{346.4}
$$

所以 $\operatorname{rank}R=n_s\operatorname{rank}Q\ge n_s$；(346.2) 以 $Q=|\chi\rangle\langle\chi|$ 取等号。若要求匹配整个 $H_{n_sd_0}$ 而非原源像，则才迫使 $R=I_{n_sd_0}/(n_sd_0)$。这些已知矩阵工具仅是本条原参考—原中心对应的中间步骤，不单独作为新增分类。∎

## 347. 不守中心账会留下什么与候选的非空性

**定理 347.1（两个局部边界及完整满足族）。** 中心迹中性在裸载体上不等同于左单位；只查总单位的单条标量迹也不足以区分不同中心的径向抵消。另一方面，325.1 的完整 tagged-CP 族分别满足 $\mathsf C_{\rm cen}(B)$ 与 $\mathsf C_{\rm cen}(\mathsf B_{\rm cl})$，包括没有实际 $M_2$ 对象或简单块的子族。

证明。第一边界取 $H_n(\mathbb C)$、$n\ge3$，非零无迹 Hermitian $H,M$，令

$$
D(a,b)=\operatorname{Tr}(a)\operatorname{Tr}(Hb)M.
\tag{347.1}
$$

$D(a,I)=0$；任意中心输入 $z=tI$ 的输出迹仍为零。但是 $D(I,H)=n\operatorname{Tr}(H^2)M\ne0$，所以 LU 失败。此例一般不满足整个 $\mathsf G_{0h}$，只区分两条裸关系；344.2 在完整背景中导出 LU 并无矛盾。

第二边界取 $E=\mathbb R^3$、$u=(1,1,1)$，

$$
K=\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},\qquad
D(a,b)_s=a_s(Kb)_s.
\tag{347.2}
$$

$Ku=0$ 给右单位；primitive 首输入的输出沿自身，故整支持条件成立。$\tau D(u,b)=\boldsymbol1^{\mathsf T}Kb=0$ 对全部 $b$ 成立，但 $\tau D(z_1,z_2)=1$，而取 $a=(1,1,0)$ 得 $D(a,a)=(1,-1,0)\ne0$。因此全局一笔迹账可掩盖中心之间相抵。本例只是 (343.1) 型局部代数片段，不供应完整 $B_*$ 的实际参考、全部过程或同一 sigma；不据它主张完整背景中中心测试不可再减。

对完整满足族，标准原 $D=\mathrm i[a,b]/2$ 的每个中心输入都给零向量，故满足 (342.1)。其原正权、准备、联合、设备、细记录、完整失败、具名同数双返回、同一 sigma 和全部合法有限历史均直接沿 325.1 保留。∎

## 348. 中心径向场、三维角与更大的关系结构

**定义 348.1（候选的几何内容与有限提升）。** 在 $B_*+\mathsf G_{0h}$ 已取得的正常形中，$\mathcal R_A:E_A\to Z(E_A)$ 是由二元关系 $D$ 读出的中心值径向场，且 $\mathcal R_A(u_A)=0$。它让第二输入控制第一输入在每个中心的伸缩；(342.1) 经实际参考回传后恰令这整个场为零。这里的消除是 343–344 的条件推论，不是把零场写进 $D$ 的定义。

对一个原对象，若中心数为 $c_A$、$m_A=\dim_{\mathbb R}E_A$，则中心单位与任一含 $u_A$ 的实基把全域中心中性写成至多 $c_A(m_A-1)$ 条标量关系。它是同一内在关系的有限表达，不要求在候选资料里选基；也不比较不同候选的实际认证成本。$\mathcal R_A=0$ 后，全部推动只剩逐块交换子；共同曲率及同一 sigma 再将这些角的转动接成同一原尺度。

对同块正交 $e,f$，令 $c=e+f$，取 $y\in V_{ef}$、$y^2=c$，置 $h=e-f$、$z=2D_ey$。345.1 与既有 (325.2) 给

$$
h^2=y^2=z^2=c,\qquad
h\circ y=h\circ z=y\circ z=0,\qquad
D_ey=z/2,\quad D_ez=-y/2.
\tag{348.1}
$$

这是四实维 $H_2(\mathbb C)$ 小屋内的三实维无迹球截面。把支持放进第三个复向量位置，可连接相交的二原子角；320.1 的高秩证明消费的正是这些可比较支持及其交集。第三个复向量位置、三实维无迹截面和物理三维空间是不同对象。跨中心只有 $\mathbb Re\oplus\mathbb Rf$，没有跨中心 Peirce 横向；中心迹条件恰清除逐中心伸缩，不生成跨中心相干。更大的结构是带经典中心的复 Jordan—Lie 关系网、各块的复射影角及原实际联合中的张量匹配；同一原 $D$ 把这些局部角与原过程共同连接。

**定义 348.2（仍需内生的部分）。** 具体原 $\Omega$ 是否满足完整背景、整支持、中心迹中性及同一 sigma，仍须从其实际来源证明。343.7 已把原残余锁定为内在中心读数，却没有从 $B_*+\mathsf G_{0h}$ 无条件推出该读数为零；定义间兼容不自动成为原世界的实现定理。既有实际来源量词和 324.3 的各物理来源义务均保留。局部边界不是完整背景反模型，条件重构不是经验起源，也未取得全网最小性、含噪稳定性或物理空间维数结论。本文为纸笔条件理论，未取得 Lean/kernel 或经验验证。

## 349. 承重来源与完整白话

**定义 349.1（来源与新增综合的边界）。** 仓内来源固定于 [`8bcd9134655d4c88a93778604e49583d6d9cf736`](https://github.com/the-omega-institute/trureturing/tree/8bcd9134655d4c88a93778604e49583d6d9cf736)。母卷指 [C123 原生互易比较母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)：2.5、10.2、30.1、67.1–67.3 供应完整 R 与右单位；85.2 供应全部静态中心对及逐对普通／相反表示。前卷指 [C128 框架与角关系续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)：246.1 将同一静态消费者分别接到闭准备背景。本卷 320.1 的无迹前件缺席证明及 321.1 供应完整来源正常形和整输出局部性；337–338 供应旧匹配等价、共同尺度、同一 sigma 和全部原消费者。

Herbut–Damnjanović，*Mixed-state twin observables*，J. Phys. A 33 (2000) 6023，DOI [10.1088/0305-4470/33/34/308](https://doi.org/10.1088/0305-4470/33/34/308)，[quant-ph/0004085v1 原文](https://arxiv.org/html/quant-ph/0004085v1)，Introduction、§4 的 (8)–(10)、§6 的 (12sa)–(12sb)，给 Hermitian twins 与约化态交换、支持／核分解及纯态 Schmidt 对应。D’Ariano–Lo Presti 的向量化来源沿 341.1。346.1 证明中的交换子、极分解与矩阵交换子代数只作为这些 $\texttt{literature-attested}$ 有限矩阵工具的应用，不借入远程实际测量、通道层析、原状态供应或实际资源结论。320.1 所需交换二次迹与有限 EJA 导子来源仍沿 326.1，不重复作为新增定理。

新增 $\texttt{repo-derived}$ 综合是：由两次原实际身份参考直接取得每个原对象、含经典和秩二源的完整径向正常形；用原中心迹唯一识别全部径向场；以全部静态中心对把原高秩域的中性下降到全域；由此删除公理中的匹配选择并保留同一刻度的完整理论。346.1 还把源像匹配的迹值等同于原中心读数，并区分源匹配和全目标匹配的 Schmidt 要求。这些结论不以检索未命中主张历史优先权。

**定义 349.2（每间房的总账都不凭空伸缩）。** 白话说，整座原世界完整留下：量子街区和经典房间、大小不同的中心、真实联合和纠缠准备、原比较尺、每台设备与细记录、完整失败出口、原分组和遗忘、带原成功数的双返回，以及全部合法有限历史。新候选仍要求两颗原子完全错开或重叠一半时，整份推动留在共同小屋里；但总账不再靠另选珠子、配补偿或列来源剖面来查，而直接查原来就有的每个中心：这间房作为一个整体，与任何输入发生关系，都不能凭空增加或减少总迹。为什么这够用，要把原对象真正带进两次已有的参考联合：第一层把每间房照进足够大的街区，第二层用原有的两侧交叉零排除混合补偿，于是带回的推动只剩转动和沿自身伸缩。每间房的中心迹恰好量出后者，逐间清零便只剩转动；在大联合查过的账又能沿实际嵌入返回小对象，所以经典房间和二阶角都没有漏下。最后仍用同一张刻度单，把各角的转动钉到共同尺度，接回复乘法、Born 概率的两套原运输、实际张量、全部旧事件、平方根词及完整失败、原细口与同数双返回和全部有限合法历史。小屋内是三实维球截面，相交小屋织成更大的复射影关系网；两侧共享珠子的旧图景只是这笔中心账的一种坐标。新关系怎样由具体原世界实际满足，仍要继续向内证明，不能靠改名或定义宣布已经发生。

## 追加锚 C128349（本行以下为增补区）

## 350. 只用原比较与二元关系的自比较中性

**定义 350.1（唯一新增候选）。** 分别取 342.1–342.2 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。保留同一原 $\Omega,q,D,L,\circ$、同一原菜单、同一预选 $t_0$、整个原 $\mathsf G_{0h}$ 及同一原 $\sigma_{t_0}$。只以如下关系替换中心迹前件：

$$
\boxed{\mathsf T_{\rm self}^{>}:\qquad
q_X\bigl(a,D^X(a,a)\bigr)=0
\quad\left(\operatorname{rank}E_X>p_*,\quad0\le a\le u_X\right).}
\tag{350.1}
$$

唯一完整候选为

$$
\mathsf C_{\rm self}(B_*)
:=B_*+\mathsf G_{0h}+\mathsf T_{\rm self}^{>}+\sigma_{t_0}.
\tag{350.2}
$$

$a$ 是原有序空间的数学效果，不由这个量词补造实际准备或实际操作。原 $D$ 仍是同一二元实双线性关系，$q$ 仍是原正比较；(350.1) 只比较第一输入和两次自输入的输出，不是向量式 $D(a,a)=0$，也不是其平方范数。它不在公理资料中点名中心、规范迹、匹配原子、补偿、来源基或参考剖面。

**定义 350.2（完整范围与简化尺度）。** 两份背景分别保持其精确有限正生成与闭正生成。全部原对象、经典中心、不等块大小、原不等正权、实际有序联合、全部实际乘积及相关准备、零与次归一质量均在量词内。原设备／端口／细记录／失败身份、整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史均沿 335.2 保留。

$\mathsf G_{0h}$ 仍逐字取 (319.1) 的零／半重叠、两个输入次序和整个输出支持；$\sigma_{t_0}$ 仍逐字取 (319.2)。LU、SC、交替、导子、斜伴随、理想保持和模身份均不作输入。不增加 primitive／等距嵌入、直接 $AP$、共同参考指数、实际 $M_2$、任意仪器、物理时钟或 $\hbar$，不删除原有的标量两侧有序接口。

这里的简化是公理表达中删除中心、规范迹及辅助选择，只留下原 $q,D$ 和效果区间之间的一个标量相容关系；没有证明独立标量方程数、原实际取得或认证成本更小。中心与迹仍可作为证明坐标，不能把表达上的删除误报为全部背景假设的减少。

## 351. 两种正比例足以逐项消去所有径向来源

**定理 351.1（效果自比较消去完整径向场）。** 在 $B_*+\mathsf G_{0h}$ 中，若原选中对象 $X$ 满足 (350.1)，则 343.1 在该对象上的每个全源泛函 $F_s:E_X\to\mathbb R$ 都为零。因此其整个原二元关系是逐块交换子，包括原经典块、二阶块与所有跨中心来源。

证明。直接复用不带迹前件的 343.1，不重新假设它的结论。写

$$
E_X=\bigoplus_sH_{n_s}(\mathbb C),\qquad
q_X(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s),\qquad w_s>0.
\tag{351.1}
$$

这里每个 $w_s$ 都是该原对象自己的正块权，不作归一化，也不要求联合间因子化。因为 $[a_s,a_s]=0$，正常形立即给

$$
P_X(a):=q_X(a,D^X(a,a))
=\sum_sw_s\operatorname{Tr}(a_s^2)F_s(a).
\tag{351.2}
$$

固定中心 $s$，取任意非零块效果 $0\le x\le I_{n_s}$，令 $a=j_sx$。这是整个 $E_X$ 的效果，其余中心为零。(350.1) 给

$$
0=w_s\operatorname{Tr}(x^2)F_s(j_sx).
\tag{351.3}
$$

前两因子严格为正，故 $F_s(j_sx)=0$；零效果由线性性同样成立。块效果实线性张成整个 Hermitian 块，例如谱分解把任意 Hermitian 矩阵写成实数乘 primitive 效果的和。因此 $F_s\circ j_s=0$，含 $n_s=1,2$，不需要在这些源上另做高秩分类。

再取不同中心 $s,r$，非零效果 $x\in H_{n_s}$、$y\in H_{n_r}$，记 $\widetilde x=j_sx$、$\widetilde y=j_ry$。对 $t=1,1/2$，$\widetilde x+t\widetilde y$ 都是原数学效果，因为两个支持在不同中心。已证的同源限制为零，故

$$
\begin{aligned}
P_X(\widetilde x+t\widetilde y)&=tA+t^2B,\\
A&=w_s\operatorname{Tr}(x^2)F_s(j_ry),\\
B&=w_r\operatorname{Tr}(y^2)F_r(j_sx).
\end{aligned}
\tag{351.4}
$$

两次中性分别给 $A+B=0$、$2A+B=0$，从而 $A=B=0$。消去正因子，变动 $x,y$ 并再用效果张成性，得到所有 $F_s\circ j_r=0$。全部来源的有限直和遂给 $F_s=0$。只有一个中心时 (351.3) 已完成证明。

整个消去只使用原效果及两个正比例，没有假设负输入也被实际实现，没有用不同中心间总和为零直接断言各项为零，也没有借用概率、实际混合程序或 $q$ 的联合运输。∎

## 352. 选中域自比较与原全域量子关系等价

**定理 352.1（不运输比较尺的全域回传）。** 分别在两份完整背景中有

$$
B_*+\mathsf G_{0h}+\mathsf T_{\rm self}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC}
\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{\rm cen}^{>}.
\tag{352.1}
$$

左式在全部原对象上导出 $D(a,a)=0$、LU、交替、Jordan 导子律、原 $q$ 斜伴随、中心及全部跨中心的零输出。自比较中性因而也扩展到每个原对象的全部实输入。

证明。先对每个原选中对象应用 351.1：它的整个 $D$ 为逐块交换子，故有 SC，且固定第一输入时是 Jordan 导子。对任意原非零对象 $A$，使用其原身份事件和完整 R，取充分大的原实际 $J=AR$，使 $\operatorname{rank}E_J>p_*$；这是 343.1 已使用的原参考供应，不以弱 $R_0$ 替代完整 R。原第一槽嵌入 $i:E_A\to E_J$ 含幺、单射并保持 Jordan 乘法和同一原 $D$。于是

$$
i(D^A(a,a))=D^J(i(a),i(a))=0.
\tag{352.2}
$$

单射性给原 $A$ 的 SC。令原导子缺陷为

$$
\Delta_A(a;b,c):=D^A(a,b\circ c)
-D^A(a,b)\circ c-b\circ D^A(a,c).
\tag{352.3}
$$

保持两种乘法给 $i(\Delta_A)=\Delta_J(i(a);i(b),i(c))=0$，再由单射性得全域 Jordan 导子律。有限 EJA 导子的内性给原 I；这是 344.2 已用的成熟工具。零对象结论平凡。此回传只运输原向量与乘法，完全没有运输 $q$，故不加入 $q_J=q_A\otimes q_R$ 或原实际遗忘前件。

反向在完整 $B_*+\mathrm I+\mathrm{SC}$ 中，344.2 的反向蕴含已给整个 $\mathsf G_{0h}$；SC 的零向量立即给 (350.1)。同一定理还给与最右式的等价。全域 LU、交替、斜伴随及中心输出结论直接沿 344.2；全域 $D(a,a)=0$ 则给所有实输入的自比较中性。两份准备背景各用自己的原静态入口与完整 R，没有把闭包中的数学准备改成实际准备。∎

## 353. 同一刻度下恢复全部原量子与过程公理

**定理 353.1（自比较候选的完整恒等重构）。** 固定同一原菜单、同一预选 $t_0$、同一原 $D$ 和 $\sigma_{t_0}$，分别有

$$
\mathsf C_{\rm self}(B_*)\Longleftrightarrow
\mathsf C_{\rm cen}(B_*)\Longleftrightarrow
\mathsf C_{\rm bal}(B_*)\Longleftrightarrow
\mathsf C_{\rm fin}(B_*)\Longleftrightarrow
\mathsf C_Z(B_*)\Longleftrightarrow
\mathsf C_{\rm support}(B_*).
\tag{353.1}
$$

对应恒等地保留原对象、准备、实际有序联合、设备／记录／完整失败、具名返回和每条原合法有限历史。由同一 $D$ 定向的复代数及其乘法为

$$
\begin{gathered}
\mathcal A_A=\bigoplus_sB(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\qquad
D_ab=\tfrac{\mathrm i}{2}[a,b],\qquad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{353.2}
$$

概率仍须经两套原 Riesz 运输：

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\rho_\alpha&=B_Ax_\alpha,&\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)&=\tau_A(\rho_\alpha y),&
\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}&&(f:A\to B).
\end{aligned}
\tag{353.3}
$$

所以 (350.1) 的 $q_A(a,\cdot)$ 不能未经运输就称为某份原准备的概率。一般 $x_\alpha\ne\widehat x_\alpha$；各实际联合各用自己的 $B,\mathcal W$。全部原经典中心、不等正权、零／奇异／次归一准备及全部相关准备保持，全部原实际联合为同一取向的普通复张量。

全部原旧事件为 CP/TNI，原完整设备事件和为 TP。整个 AC、精确 $N_u$ 和 Xs 供应的每个原所选有限平方根词及其原相关执行保留完整映射

$$
\rho\longmapsto\sqrt e\rho\sqrt e,\qquad
X\longmapsto(\sqrt e\otimes I)X(\sqrt e\otimes I).
\tag{353.4}
$$

原占用方向 $p_1$ 的每个原失败 $\Psi_\ell$ 保留完整输出 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其他原方向和中心保留原映射。实 Jordan F 保留同一原实现的实际细口、原分组与遗忘；非零细支的具名资料仍是

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad
\Phi_f=\sum_\ell S_\ell,\quad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{353.5}
$$

原成功数 $q_\ell$ 及同数反向资料不归一掉。对每份原准备、原末端效果 $w$ 和每条原合法有限历史，仍有

$$
\alpha(T_{f_1}\cdots T_{f_r}w)
=\tau_{A_r}\!\left(w\,\Phi_{f_r}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{353.6}
$$

这包括全部原顺序、实际细记录的自适应分支、实际并行联合及其相关输入、细化、分组、实际遗忘、零／失败／返回／停止；仅在原分母正时取条件概率，不增加任意新连线或仪器。

证明。352.1 给无标定的全域 I+SC 及与中心候选的等价。直接复用 345.1、338.1：先取得包含零分支的共同曲率 $\kappa\ge0$，再由同一原 $\sigma_{t_0}$ 和原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 得 $\kappa=1$。不重标原 $D$，不改选刻度。345.1 的全部原入口至此成立，其完整消费者给 (353.1)–(353.6)，不是只复用单载体或单成功事件。全事件 R 仍针对全部原相关准备；闭背景的连续正延拓只在同一原执行上进行。324.3 的物理时钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器、旧同效果设备自己的完整输出校准仍各需原来源。∎

## 354. 自比较没有暗写向量自零，也不能只查原子

**定理 354.1（裸载体上的严格标量边界）。** 存在含右单位的实双线性 $D$，对全部输入满足 $q(a,D(a,a))=0$，但严格效果也可有 $D(a,a)\ne0$。这种裸标量中性不足以给整支持条件；它不是完整 $B_*$ 的反模型。

证明。取 $E=H_3(\mathbb C)$、$u=I$、$q(a,b)=\operatorname{Tr}(ab)$，令

$$
H=\operatorname{diag}(1,-1,0),\quad h=H/2,\quad
\ell(b)=\operatorname{Tr}(Hb),\quad A(a)=\mathrm i[h,a],\quad
D(a,b)=\ell(b)A(a).
\tag{354.1}
$$

$\ell(I)=0$ 给右单位。迹循环给 $q(a,A(a))=0$，所以全部实输入都有标量自比较中性。记 $X=E_{12}+E_{21}$，则

$$
a=\frac{I+(H+X)/2}{2},\quad
0<a<I,\qquad
D(a,a)=\frac{\mathrm i}{8}(E_{12}-E_{21})\ne0.
\tag{354.2}
$$

严格效果性由 $H+X$ 的谱 $\{\sqrt2,-\sqrt2,0\}$ 得到。取 $e$ 为 $(v_1+v_3)/\sqrt2$ 的秩一投影、$p$ 为 $v_2$ 的秩一投影；它们正交，但

$$
D(e,p)=-\frac{\mathrm i}{4}(E_{13}-E_{31})\ne0,
\qquad (e+p)D(e,p)(e+p)=0.
\tag{354.3}
$$

故输出不在其整个支持角内，整支持关系失败。本例只说明裸标量关系与向量 SC 不同，没有供应完整原参考、全部过程或同一 sigma，不能据此否定 352.1，也不能据它主张完整背景中的前件独立性。∎

**定理 354.2（primitive 自比较会漏掉跨中心回路）。** 347.1 的经典三中心片段满足每个 primitive 的向量自零，仍有严格效果的自比较不为零。因此在该片段上，(350.1) 不能仅用 primitive 自比较替代。

证明。沿用 (347.2) 的同一 $K,D$ 及其右单位和整支持性质，不把这些旧性质重列为新增分类。对经典 primitive $e_s$，$K_{ss}=0$ 给 $D(e_s,e_s)=0$。取原等权比较 $q(a,b)=\sum_sa_sb_s$，直接代入得

$$
P(a)=\sum_sa_s^2(Ka)_s
=(a_1-a_2)(a_1-a_3)(a_2-a_3).
\tag{354.4}
$$

在严格效果 $a=(1/4,1/2,1/8)$ 上，$P(a)=-3/256\ne0$。单中心的自比较已消掉同源项，却未消掉这些异源系数；351.1 的两种正比例恰能将它们分开。此例仍只是一段局部代数，不是带全部实际来源的完整背景反模型。∎

## 355. 球面相切、三维小屋与更大的关系网

**定义 355.1（原比较球面的代数相切）。** 对非零效果 $a$，原 $q$ 球面 $q(x,x)=q(a,a)$ 在 $a$ 处的切空间为 $\{v:q(a,v)=0\}$。所以 (350.1) 表示自输入输出 $D(a,a)$ 与这张原比较球面相切；这是一个标量相容条件，未定义实际流、时间或物理能量。

其成熟几何对应是二次向量场 $V(a)=D(a,a)$ 的三次型 $q(a,V(a))$ 为零。Schlegel–Noack，*On long-term boundedness of Galerkin models*，DOI [10.1017/jfm.2014.736](https://doi.org/10.1017/jfm.2014.736)，[arXiv:1310.0053v1](https://arxiv.org/html/1310.0053v1) §2 的 (2)–(6)，用二次系数的全对称和为零消去平方长度导数中的三次项。这里仅取这种有限维相切关系作数学对应，不借入该文的实际流、Navier–Stokes、长时有界性或稳定性结论，也不把已知相切恒等式单独作为新增定理。

在原参考和整支持已给出的 (343.1) 中，$D(a,a)$ 只能沿各中心的 $a_s$ 伸缩。这样的分块径向向量在某一点可以互相抵消而相切；351.1 则用单中心及两种正比例效果排除整个线性径向场。故结论比一张球面上的相切强，所多出的力量来自完整正常形和跨输入的兼容，不能只从单个标量等式读出。

**定义 355.2（有限三维角的原关系提升）。** 完整候选经 353.1 给同块正交 primitive $e,f$ 的数学支持角 $H_2(\mathbb C)$。令 $c=e+f$、$h=e-f$，取 $y\in V_{ef}$、$y^2=c$，置 $z=2D_ey$。沿用 (348.1)，有

$$
h^2=y^2=z^2=c,\quad
h\circ y=h\circ z=y\circ z=0,\qquad
D_ey=z/2,\quad D_ez=-y/2.
\tag{355.1}
$$

$\mathbb Rh\oplus\mathbb Ry\oplus\mathbb Rz$ 是四实维支持角的三实维无迹球截面。再把两个支持角放进第三个复向量位置，便能比较相交角及其交集；343.1 已通过原实际参考把这种高秩相容带回全部原对象。第三个复向量位置、三实维无迹截面和物理三维空间相互不同。

更大的结构仍是带经典中心的复 Jordan–Lie 关系网、逐块复射影角及原实际联合的普通复张量。跨中心没有横向 Peirce 相干；(350.1) 经完整正常形排除的是各中心的径向伸缩，不凭空制造跨中心量子相干。原比较、二元关系、局部角及原过程通过已证的对应相连，而非仅凭相同的图像或名称统一。

## 356. 来源与仍需内生的约束

**定义 356.1（新增综合的确切依赖）。** 仓内前置固定于 [`11379dc57278ecf3d612a0ce0407c3f849586f63`](https://github.com/the-omega-institute/trureturing/tree/11379dc57278ecf3d612a0ce0407c3f849586f63)。349.1 所列母卷、前卷和本卷来源继续供应完整原签名、右单位、静态全部中心对、原实际参考及完整量子消费者。351.1 的关键前置是无迹前件的 343.1；352.1 只回传原向量和乘法；353.1 直接消费 344.2、345.1、338.1 及同一原 sigma。有限 EJA 导子、矩阵迹循环与三维角工具仍沿 326.1、349.1；二次场相切来源在 355.1 内明确限定。

本批 $\texttt{repo-derived}$ 综合是：用原效果区间上的单个三次自比较关系，经过两种正比例分离全部完整来源的径向泛函，并在不运输 $q$ 的情况下沿原实际参考恢复全域 I+SC，因而接回同一刻度的全部量子与过程对应。成熟矩阵与相切工具仅在这个新综合内部使用；不以文献检索未命中声称历史优先权。

**定义 356.2（内生化尚余的数学与物理边界）。** (350.1) 已把新前件写成同一原 $q,D$ 和效果定义域之间的关系，但具体原 $\Omega$ 是否满足完整 $B_*$、整个 $\mathsf G_{0h}$、该自比较中性及同一 sigma，仍须从其实际来源证明。把条件写得更内在不等于已经无前提推出条件；352.1 是明确前提下的等价，354 的裸例也没有解决完整背景中的最小性或独立性。

原对象和合法历史不要求有限，效果的有限维数学张成不构成全网实际认证程序。尚未取得全网最小标量条件、含噪稳定性、物理空间维数或经验性起源结论。324.3 的三类物理来源义务保持分立。这里的结果是纸笔条件理论，不宣称 Lean/kernel 或经验验证。

## 357. 完整白话：自己与自己的推动不凭空撑大比较球

**定义 357.1（这一完整候选的直观表述）。** 白话说，原世界整座留下：经典房间、大小不同的量子街区、原比较尺、全部真实联合与相关准备、每台设备和细记录、完整失败出口、原分组与遗忘、带同一个原成功数的双返回，以及每条原本合法的有限历史。新要求还是让完全错开或重叠一半的两颗原子，把整份推动留在共同小屋里；另一个要求则更短：拿任何一个原数学效果，放进二元关系的两个位置，再用它自己去比较输出，读数必须是零。画面就是自己的推动贴着原比较球面，不能顺着自己的方向撑大或缩小。为什么一个读数够，要用原来就有的实际参考把所有房间照进高秩街区；完整支持关系先把推动压成转动和逐房伸缩。只查一间房便排掉本房伸缩，再把两间房按两种正比例放在一起比较，就不能再拿一间的膨胀抵另一间的收缩，于是全部伸缩都消失。大街区上的向量关系沿原嵌入带回来，经典房间和二阶角都不会漏下，也不用偷换比较尺。最后仍由同一张原刻度单固定转动尺度，接回复乘法、Born 概率的两套正确运输、原实际张量、全部旧事件、平方根词与完整失败、原细口与同数两侧返回和全部合法历史。每个二原子小屋里出现三实维球截面，相交小屋织成更大的复射影关系网；这不是在宣布物理空间必为三维。公理里不再另点中心或迹，只约束原来定义之间的关系；这条关系为何在具体原世界内成立，仍须继续向内证明，不能靠定义把答案写进去。

## 追加锚 C128357（本行以下为增补区）

## 358. 只查一种不等权两原子效果的自比较

**定义 358.1（唯一新增候选与固定测试形状）。** 分别固定 350.1–350.2 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。同一原 $\Omega,q,D,L,\circ$、同一原菜单和预选 $t_0$、整个原 $\mathsf G_{0h}$ 与同一原 $\sigma_{t_0}$ 均保持。将整个效果区间上的新增自比较关系缩到

$$
\boxed{\mathsf T_{\rm uneq}^{>}:\quad
q_X\bigl(a_{ep},D^X(a_{ep},a_{ep})\bigr)=0,
\qquad a_{ep}=e+\tfrac12p,}
\tag{358.1}
$$

其中 $X$ 遍历原选中域 $\operatorname{rank}E_X>p_*$，$(e,p)$ 遍历整个 $E_X$ 中全部有序正交 primitive 对。唯一完整候选为

$$
\mathsf C_{\rm uneq}(B_*)
:=B_*+\mathsf G_{0h}+\mathsf T_{\rm uneq}^{>}+\sigma_{t_0}.
\tag{358.2}
$$

$e+\tfrac12p$ 是原数学效果，且交换次序的 $p+\tfrac12e$ 也在同一量词内。不另加 primitive 自测试、全单位自测试、中心迹、自由比例、所选框架或补偿作为公理资料。$\tfrac12$ 在此是两个正交谱方向的固定权重，不是半重叠；原 $\mathsf G_{0h}$ 仍含全部零及半重叠有序对的整个输出支持，不能据 (358.1) 删除后者。

**定义 358.2（原范围与简化的确切含义）。** 两份准备背景各保持其原精确有限正生成与闭正生成。全部原对象、旧输出、经典中心、不等块大小、原不等正权、实际有序联合、全部原乘积和相关准备、零与次归一质量均保留。原设备／端口／细记录／失败身份、整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史仍逐项沿 350.2 保留。

LU、SC、交替、导子、斜伴随、原理想保持和模身份均留作结论；不增加 primitive／等距嵌入、直接 $AP$、共同参考指数、实际 $M_2$、任意仪器、物理时钟或 $\hbar$，全部原标量两侧有序接口保持。固定谱权重不重标原 $D$ 或原成功数，也不改变原 sigma。数学效果和证明中的框架不供应实际准备、混合或操作。

相对 350.1，新增标量读数的显式测试域只剩固定谱形状的一种两原子效果，不再遍历全部效果。这里证明的是这种测试域缩减及其在完整背景中的等价，不是独立方程数的全网最小性或实际取得／认证成本下降。

## 359. 成对方程与整框架行和消去完整径向场

**定理 359.1（固定两原子测试的全源消去）。** 在 $B_*+\mathsf G_{0h}$ 中，对原选中对象 $X$，(358.1) 迫使 343.1 的每个全源泛函 $F_s:E_X\to\mathbb R$ 为零。因此在全部完整输入上

$$
D^X(a,b)=\bigoplus_s\gamma_s\,\mathrm i[a_s,b_s].
\tag{359.1}
$$

证明。复用不带任何迹或自比较前件的 343.1，以及 (351.1) 的原正权 Frobenius 型。对自输入，交换子直接消失，所以仍有

$$
P_X(a)=q_X(a,D^X(a,a))
=\sum_sw_s\operatorname{Tr}(a_s^2)F_s(a),
\qquad F_s(u_X)=0.
\tag{359.2}
$$

固定任意完整 Jordan 框架 $e_1,\ldots,e_N$，其中 $\sum_ie_i=u_X$、$N=\operatorname{rank}E_X>p_*\ge2$。$N$ 是原 Jordan 秩，不是实维数或中心数。记 $s(i)$ 为 $e_i$ 所属中心，定义纯证明坐标

$$
A_{ij}:=w_{s(i)}F_{s(i)}(e_j),\qquad
d_i:=A_{ii},\qquad S:=\sum_id_i.
\tag{359.3}
$$

原右单位在正常形中给的 $F_s(u_X)=0$ 使每行满足

$$
\sum_jA_{ij}=w_{s(i)}F_{s(i)}\!\left(\sum_je_j\right)=0.
\tag{359.4}
$$

对 $i\ne j$，展开 (359.2) 得

$$
P_X(e_i+\lambda e_j)
=d_i+\lambda A_{ij}+\lambda^2A_{ji}+\lambda^3d_j.
\tag{359.5}
$$

若 $s(i)\ne s(j)$，这是两个中心各自的平方长度贡献。若二者同块，则 $A_{ij}=d_j$、$A_{ji}=d_i$，右边为 $(1+\lambda^2)(d_i+\lambda d_j)$，同样等于该单块的直接展开。故本式没有将同块原子偷换成独立中心，也没有丢掉经典块或跨中心来源。这里只在 $\lambda=1/2$ 消费 (358.1)，不假设其他比例也被测试。

两个有序对 $(e_i,e_j)$ 与 $(e_j,e_i)$ 分别给

$$
\begin{aligned}
8d_i+4A_{ij}+2A_{ji}+d_j&=0,\\
d_i+2A_{ij}+4A_{ji}+8d_j&=0.
\end{aligned}
\tag{359.6}
$$

消元得到 $A_{ij}=d_j-\tfrac52d_i$。代回每行的 (359.4)，并对全部行求和：

$$
0=S-\tfrac52(N-1)d_i,\qquad
0=\left(N-\tfrac52(N-1)\right)S
=\tfrac{5-3N}{2}S.
\tag{359.7}
$$

$N\ge3$，故 $5-3N\ne0$，于是 $S=0$、每个 $d_i=0$，再由 (359.6) 得全部 $A_{ij}=0$。

现在任取完整输入 $b\in E_X$，选其完整谱框架，写 $b=\sum_j\beta_je_j$。对任意目标中心 $s$，该框架在 $s$ 中有至少一颗 $e_i$；上述结论给 $w_sF_s(e_j)=A_{ij}=0$ 对每个 $j$ 成立。因为 $w_s>0$，$F_s(b)=\sum_j\beta_jF_s(e_j)=0$。$s,b$ 任意，故每个全源 $F_s$ 为零，得 (359.1)。框架仅用于证明原关系的推论，不是新实际读口或公理选择。∎

## 360. 两原子测试恢复全部效果与原全域关系

**定理 360.1（无标定的完整等价）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中有

$$
B_*+\mathsf G_{0h}+\mathsf T_{\rm uneq}^{>}
\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf T_{\rm self}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC}.
\tag{360.1}
$$

两原子测试因而恢复全部原对象、全部实输入的自比较中性、LU、交替、Jordan 导子、原 $q$ 斜伴随和中心零输出。

证明。359.1 在每个原选中对象给纯交换子，故其全部自输入向量为零，特别得到整个效果区间上的 (350.1)。反向每个 $e+\tfrac12p$ 都在原效果区间内，所以限制 350.1 即得 358.1。与全域 I+SC 的等价直接消费 352.1。

其原回传仍是：对任意原 $A$，用身份事件的完整 R 选择实际充分大的 $J=AR$，仅沿原含幺 Jordan/$D$ 单射运输 $D^A(a,a)$ 和完整导子缺陷 (352.3)，然后用单射性消去；有限 EJA 内性把导子接回原指定 $\mathfrak k_A$。这同时覆盖原经典对象、二阶对象、全部中心及原输出。没有运输 $q$，不增加 $q_J$ 的因子化、等距或 primitive 保持。反向的整个 $\mathsf G_{0h}$ 仍由完整 $B_*+\mathrm I+\mathrm{SC}$ 及 344.2 供应，不能从 SC 单独偷取。两份准备背景分别使用其自身静态入口与完整 R。∎

## 361. 同一原尺度下的完整量子与过程理论

**定理 361.1（固定两原子候选的恒等重构）。** 对同一原菜单、预选 $t_0$、原 $D$ 与原 $\sigma_{t_0}$，分别有

$$
\mathsf C_{\rm uneq}(B_*)\Longleftrightarrow
\mathsf C_{\rm self}(B_*)\Longleftrightarrow
\mathsf C_{\rm cen}(B_*)\Longleftrightarrow
\mathsf C_{\rm bal}(B_*)\Longleftrightarrow
\mathsf C_{\rm fin}(B_*)\Longleftrightarrow
\mathsf C_Z(B_*)\Longleftrightarrow
\mathsf C_{\rm support}(B_*).
\tag{361.1}
$$

全部对应对原对象、准备、实际联合、设备／端口／细记录／完整失败、具名返回与每条原合法有限历史保持恒等。原 $D$ 定向的复乘法为

$$
\begin{gathered}
\mathcal A_A=\bigoplus_sB(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\qquad
D_ab=\tfrac{\mathrm i}{2}[a,b],\qquad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\quad(c^2=c).
\end{gathered}
\tag{361.2}
$$

原概率双运输及事件运输保持

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\rho_\alpha&=B_Ax_\alpha,&\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)&=\tau_A(\rho_\alpha y),&
\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}&&(f:A\to B).
\end{aligned}
\tag{361.3}
$$

一般 $x_\alpha\ne\widehat x_\alpha$，每个原实际联合各用自己的 $B,\mathcal W$。原不等正权、经典中心、不等块大小、零／奇异／次归一准备以及全部原相关准备均保持，全部实际联合为同一取向的普通复张量。固定两原子效果的自比较没有未经运输的原概率含义。

全部原旧事件为 CP/TNI，完整原设备的事件和为 TP；整个 AC、精确 $N_u$、X/Xs 和原合法连线供应的每个原所选有限平方根词及其原相关执行保持

$$
\rho\longmapsto\sqrt e\rho\sqrt e,\qquad
X\longmapsto(\sqrt e\otimes I)X(\sqrt e\otimes I).
\tag{361.4}
$$

每个原占用方向 $p_1$ 的原失败 $\Psi_\ell$ 仍给完整输出 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；其余原方向、中心和端口保留原映射，不以失败质量替代输出。原实 Jordan F 给同一实现的实际细口和原分组／遗忘，非零细支的原具名资料仍满足

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad
\Phi_f=\sum_\ell S_\ell,\quad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{361.5}
$$

成功数仍是原 $q_\ell$，同数反向资料仍保留。每份原准备、原末端效果 $w$ 和每条原合法有限历史都有

$$
\alpha(T_{f_1}\cdots T_{f_r}w)
=\tau_{A_r}\!\left(w\,\Phi_{f_r}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{361.6}
$$

这包含原顺序、实际记录的自适应分支、实际并行联合及全部相关输入、细化、分组、实际遗忘、零／失败／返回／停止。只在原分母为正时取条件概率，不补新的任意仪器、记录或连线。

证明。360.1 恢复 353.1 的全部入口。仍先在全域 I+SC 下取得包含零分支的共同曲率 $\kappa\ge0$，再消费同一原 sigma，由原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 得 $\kappa=1$。全部式子直接沿 353.1、345.1、338.1 保留，不重标 $D$，不改选刻度。全事件 R 针对全部原相关准备，闭准备背景只在同一已固定原执行上作连续正延拓。325.1、347.1 的完整 tagged-CP 族因其原 SC 同样满足 358.1，故也给本候选的完整满足族，含没有实际 $M_2$ 对象或简单块的子族。324.3 的三类物理来源义务仍各自保留。∎

## 362. 两原子读数的裸边界与投影测试的遗漏

**定理 362.1（裸两原子测试严格少于全部效果测试）。** 在右单位的裸实双线性层，固定两原子自比较中性可以成立而全部效果的自比较中性失败；此时整支持可失败，不构成完整背景中的反模型。

证明。取 $E=\mathbb R^4$、$u=(1,1,1,1)$、标准点积 $q$，定义

$$
D(a,b)=\bigl(a_2(b_3-b_4),0,0,0\bigr),\qquad
P(a)=q(a,D(a,a))=a_1a_2(a_3-a_4).
\tag{362.1}
$$

$D(a,u)=0$。每个 $e_i+\tfrac12e_j$、$i\ne j$ 至多有两个非零坐标，因此 $P$ 恒为零，全部有序两原子测试通过。严格效果

$$
a=(1/2,1/4,3/4,1/8),\qquad
D(a,a)=(5/32,0,0,0),\quad P(a)=5/64
\tag{362.2}
$$

却使全部效果中性失败。另一方面 $D(e_2,e_3)=e_1$ 不在 $e_2+e_3$ 的支持内，故原整支持关系失败。可零延拓这条 $D$ 到 $\mathbb R^N$，取 $N\ge\max\{4,p_*+1\}$，并给例中效果的新增坐标取 $1/2$；右单位、两原子中性和严格效果反例均保持。这仍没有供应完整原参考、过程或同一 sigma，只说明裸标量测试域有严格区别。354.1 的裸例还表明，连全部效果的标量中性也不是向量 SC 的范数重写。∎

**定理 362.2（全部投影自比较仍会遗漏固定不等权读数）。** 347.2 的经典三中心循环片段通过全部投影的自比较，但被 (358.1) 的一个不等权效果检出。

证明。沿用 (347.2) 的同一 $K,D$ 和 354.2 的等权比较。对任意经典投影 $a$，$a_s^2=a_s$，故

$$
P(a)=\sum_sa_s^2(Ka)_s=a^{\mathsf T}Ka=0
\tag{362.3}
$$

由 $K$ 的反对称性成立。但 $a=e_1+\tfrac12e_2=(1,1/2,0)$ 给 $Ka=(1/2,-1,1/2)$，从而 $P(a)=1/4\ne0$。固定不等权不能直接换成等权和或投影：那些读数会让相反方向的贡献抵消。该片段仍只用于局部区别，不宣告完整原背景的前件最小性或独立性。∎

## 363. 不等权两点、整框架相容与三维角

**定义 363.1（两个次序的几何）。** 对一对正交 primitive，令 $c=e+p$、$h=e-p$。两个被测效果是

$$
a_{ep}=\tfrac34c+\tfrac14h,\qquad
a_{pe}=\tfrac34c-\tfrac14h.
\tag{363.1}
$$

每条标量关系都说自输入输出在该效果处与原 $q$ 等长球面相切，含义沿 355.1。对同块原子，它们位于数学 $H_2(\mathbb C)$ 支持角中、以 $3c/4$ 为中点的两个相反位置；同块的原 Frobenius 权相同，故两者的原平方长度均为 $5w_s/4$。对不同中心，两条轴没有 Peirce 横向，两个效果的平方长度分别为 $w_s+w_r/4$、$w_s/4+w_r$，不要求相等，不把它们画成同一个原 $q$ 球面的等长对。

359.1 的整框架行和把每个二元小检查接回同一原单位：只看一对时，四个来源系数可相互补偿；整框架的原右单位则要求每行零和，使所有补偿同时消失。这里的单位平衡由既有原来源供应，不是另加全单位自比较。框架不被固定为一个全网共同参考，跨框架的谱展开才把结论覆盖到全部原输入。

**定义 363.2（三实维角及更大结构）。** 完整候选经 361.1 恢复同一原 $D$ 的角转动。对同块正交 $e,p$，取 $y\in V_{ep}$、$y^2=c$，置 $z=2D_ey$；沿 355.2 有

$$
h^2=y^2=z^2=c,\qquad
h\circ y=h\circ z=y\circ z=0,\qquad
D_ey=z/2,\quad D_ez=-y/2.
\tag{363.2}
$$

四实维支持角的三实维无迹截面为 $\mathbb Rh\oplus\mathbb Ry\oplus\mathbb Rz$。相交小角借第三个复向量位置相接，原实际参考把这种相容传回经典与低秩原对象。这个第三复位置、三实维 Bloch 截面和物理三维空间仍相互不同，也未产生实际 $M_2$ 对象。更大的结构是带经典中心的复 Jordan–Lie 关系网、逐块复射影角及原实际联合的普通复张量；不等权两点约束与整框架单位相容只是读取它的一种更小测试形状，不供应真实流、时钟或物理能量。

## 364. 承重来源与未决内生边界

**定义 364.1（来源及新增内容）。** 仓内前置固定于 [`5528d77d1db9517a93e821ff319d4a6910f969fc`](https://github.com/the-omega-institute/trureturing/tree/5528d77d1db9517a93e821ff319d4a6910f969fc)。350–357 供应上一效果候选、完整消费者与精确边界；343.1 的无迹前件全对象正常形及原右单位是本批消去的关键入口。完整 Jordan 谱框架、正 Frobenius 分块型、有限 EJA 导子内性和复角几何均沿 326.1、349.1、356.1 的成熟来源；355.1 中 Schlegel–Noack 的二次场相切恒等式仅作本条几何解释的中间工具，不借其动力学或有界性前提。

本批新增 $\texttt{repo-derived}$ 综合是 (359.5) 的同块／跨块统一展开、两个次序导出的系数关系与原整框架零行和的合用：不另查 primitive 或单位自输入，就把固定谱比例的两原子标量测试接回全部效果及全域 I+SC，继而保持同一原尺度的完整消费者。这里不把成熟谱分解、相切或线性消元单独列为新理论，也不以检索未命中声称历史优先权。

**定义 364.2（仍须从原世界内部取得的关系）。** 具体原 $\Omega$ 满足完整 $B_*$、整个 $\mathsf G_{0h}$、固定两原子中性及同一原 sigma，仍须由其实际来源证明。把公理锁定为原比较、二元关系、原谱次序和原单位之间的兼容约束，不自动证明这个约束已经在原世界成立。360–361 是这些明确模型前提下的完整条件等价。

324.3 的连续器件／物理时钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器、旧同效果设备自己的完整输出校准仍分属三项原来源义务。尚未取得全网最小独立方程数、实际认证成本、含噪稳定性、物理空间维数或经验性量子起源结论。原对象及合法历史无需有限；每个对象的有限谱框架不使整个世界成为有限测试。本文仍是纸笔条件理论，不宣称 Lean/kernel 或经验验证。

## 365. 完整白话：两颗珠子一全一半，换位之后不能藏伸缩

**定义 365.1（本候选的完整直观表述）。** 白话说，原世界整座保留：经典房间、大小不同的量子街区、原比较尺、全部真实联合与相关准备、每台设备及细记录、完整失败出口、原分组与遗忘、带同一个原成功数的两侧返回，以及每条原本合法的有限历史。整支持规则仍管完全错开和重叠一半的两颗原子，整份推动都得留在共同小屋里；新的自比较却不用再把所有效果逐个拿来查，只拿完全错开的两颗珠子，在数学效果里一颗给全权、一颗给半权，让这个组合与自己配对，再用自己比较输出，读数必须为零，换位也一样。图上是两个相反位置，各自的推动贴着各自原比较球面；跨房间的尺不同，不能硬说两边一样长。为什么这点检查够，原实际参考和整支持已经先把可能的自推动压成各房间的伸缩；一对珠子交换全权和半权，便把两个方向的补偿锁在同一组系数里。再把珠子放回任意完整框架，原来就有的右单位要求每行总和为零，这些补偿便无处藏身，全部伸缩同时消失。对任意原输入换用它自己的谱框架，就覆盖了整个来源；大联合中的向量和乘法关系仍沿原单射带回来，经典房间和二阶角也完整恢复，不偷换比较尺。最后仍用同一张原刻度单固定转动尺度，接回复乘法、Born 概率的两套正确运输、实际张量、全部旧事件、有限平方根词与完整失败、原细口、同数两侧返回及全部合法历史。每个同块二原子小屋里是三实维球截面，相交小屋织成更大的复射影关系网；这不等于已经推出物理三维空间或制造时钟。具体原世界为什么满足这条更小的成对关系，仍须从它自身继续证明，不能靠定义宣布完成。

## 追加锚 C128365（本行以下为增补区）
