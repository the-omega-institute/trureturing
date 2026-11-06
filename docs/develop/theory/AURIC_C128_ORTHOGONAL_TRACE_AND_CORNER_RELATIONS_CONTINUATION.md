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

## 334. 保留原跨中心域的有限半角候选

**定义 334.1（同一原数据上的有限 HALF）。** 母卷、框架卷分别指 [C123 母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)和[共同框架续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)；词卷指[原词与固定关系卷](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md)。分别固定母卷 88.1、框架卷 264.1、272.1–272.2 及词卷 333.1 的完整 $B$、另名完整 $\mathsf B_{\rm cl}$，任一记作 $B_*$。$B$ 要求每个所需对象及实际联合的实际准备精确有限正生成，$\mathsf B_{\rm cl}$ 要求其闭正生成；不互换两者，不把数学极限态增加为实际准备。

整个原 $\Omega$、原全语境响应商、已经给定的实双线性 $d_A(a,b)=D^A_ab$、原 $q_A,L_A,\circ_A$ 均固定。仅由框架卷 246.1 使用静态坐标

$$
E_A=\bigoplus_{s\in S_A}H_{n_s}(\mathbb C),\qquad
u_A=(I_s)_s,\qquad
\tau_A=\sum_s\operatorname{Tr}_{n_s},\qquad
q_A(a,b)=\sum_sw_{A,s}\operatorname{Tr}(a_sb_s),\quad w_{A,s}>0.
\tag{334.1}
$$

$\tau_A$ 是每颗 primitive 迹一的规范 Jordan 谱迹，不是 $q_A$ 的任取加权迹；静态坐标未识别原 $D$ 的复取向。选中对象仍恰为 $\operatorname{rank}E_A>p_*$，$p_*=\operatorname{rank}E_P\ge2$。在每个这样的对象的每个高简单块 $t$、$n_t\ge3$，先于考察 $D$ 固定任意有限有序族

$$
\begin{gathered}
\mathcal F_{A,t}\subset
\{(j_te,j_tp):e,p\in\operatorname{Prim}(H_{n_t}(\mathbb C)),
\ \operatorname{Tr}(ep)=\tfrac12\},\\
\operatorname{span}_{\mathbb R}
\{p:(j_te,j_tp)\in\mathcal F_{A,t}\}=H_{n_t}(\mathbb C).
\end{gathered}
\tag{334.2}
$$

这里 $j_t$ 是数学理想包含；第二槽张成的是整个该理想，包含单位方向，不是仅无迹部分。族可冗余，各对象、各块各自有限，原对象域不要求有限。选择只依静态非 $D$ 数据；同一选择同时用于比较所有原 $D$。定理 337.1 给这种族的存在性。

完整保留 (319.1) 的 $\mathsf G_{0h}$：在每个选中对象的全部有序 primitive 对上，若 $\tau_A(e\circ_Ap)\in\{0,\tfrac12\}$，则整份输出满足 $D^A_ep=Q_cD^A_ep$，$c=\operatorname{supp}(e+p)$、$Q_c=2L_c^2-L_c$。另定义

$$
\begin{aligned}
\mathsf X_{\rm HQ}:\quad&
\tau_A(D^A_ep)=0
&&\bigl(z(e)\ne z(p),\ \max\{n(e),n(p)\}\ge2\bigr),\\
\mathsf H_{\mathcal F}:\quad&
\tau_A(D^A_ep)=0
&&\bigl((e,p)\in\mathcal F_{A,t},\ n_t\ge3\bigr).
\end{aligned}
\tag{334.3}
$$

$\mathsf X_{\rm HQ}$ 逐字保留词卷 (333.2) 的全部原有序跨中心非经典迹域，两个次序分别量化，不限于高块或所选首原子。$\mathsf G_{0h}$ 仍检验其他中心及连接角内外的全部输出，包含原实际联合中的纠缠 primitive。$Q_c$ 不换成 $P_c=4(L_c-L_c^2)$。

原菜单、原 $\mathcal K_A$、实际 $J_0=P^{\otimes2}$ 和先于 $D$ 固定的同一 $t_0=(e_0,p_0,r_0)\in\mathcal K_{J_0}$ 全取框架卷 265.2、272.1，令

$$
\begin{aligned}
\sigma_{t_0}:\quad&
W_{e_0}(p_0)
=2q_{J_0}(D_{p_0}e_0,r_0)+W_{e_0}(2D_{e_0}p_0),\\
\mathsf C_{{\rm finHALF},\mathcal F}(B_*):={}&
B_*+\mathsf G_{0h}+\mathsf X_{\rm HQ}
+\mathsf H_{\mathcal F}+\sigma_{t_0}.
\end{aligned}
\tag{334.4}
$$

其中 $W_e(x)=\|P_ex\|_{q_A}^2/2$，不重选 $t_0$、不缩放 $D,q,W$ 或任何原返回数。相对词卷 $\mathsf C_{\rm HQ}$，全部连续半重叠迹只留下 (334.2) 的有限对：二阶块上的半角迹不再独立要求，高阶块上只要求所选有限族；经典块没有半重叠对。

**定义 334.2（完整原范围及数学选择的类型）。** 保留全部原单体、实际有序联合、旧输出、失败输出、经典标签和参考；全部中心、不等量子块、不等正 $q$ 块权、原比较 $g^0$；全部原准备、零及次归一质量、实际乘积准备与全部实际相关输入。设备、端口、实现和记录身份不按响应合并。整个 AC、精确 $N_u$、原 X/Xs、全事件 R、实 Jordan 意义的原 F、同实现实际细口、细化／分组／遗忘、零／失败／停止、具名原同标量两侧支持返回、同数反向资料及每条原合法有限顺序、自适应和并行历史均保持原量词。F 的两个支持、完整输出、同一正返回数及反向资料严格取词卷 333.1 的实 Jordan 合同。

X 仍仅取原含幺 Jordan／同一 $D$ 嵌入、原有序交叉零、乘积张成及实际乘积准备。不输入 LU、交替、SC、导子、斜伴随、协变、$D$ 模身份、输出理想保持或反向交叉零；不添直接 $AP$、共同参考指数、实际 $M_2$、任意操作、共同仪器或物理标定。数学理想、primitive、支持角、压缩和有限族的选择都不取得实际对象、准备、设备或控制身份，也不删除任何已经声明的实际接口。所有未直接测试的小对象、低简单块及经典来源仍属于完整背景。

## 335. 半角有限族怎样接到有限 ZERO 的全输入公式

**定理 335.1（保留跨中心域时的局部蕴涵）。** 固定一个复 Hermitian 直和 $E$ 及实双线性 $D$，只假设右单位 $D(a,u)=0$、整个 $\mathsf G_{0h}$。固定任意 (334.2) 的族。在这个单载体层，

$$
\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}
\ \Longrightarrow\
F_t=0\quad(n_t\ge3)
\ \Longrightarrow\ \mathsf Z_{\rm fin}
\tag{335.1}
$$

对定义 327.1 的每一种先定 ZERO 选择成立。$F_t$ 取定理 320.1 的全部来源正常形；消去后对全部完整输入，恰有

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s:n_s=1}\ell_{ts}a_s(b_t-b_sI_t).
\tag{335.2}
$$

不在此断言经典补偿行消失，亦不在此断言低目标或全部 $\mathsf X_{\rm HQ}$ 可由 $\mathsf Z_{\rm fin}$ 恢复。

证明。直接使用 320.1，而不重新分类 $D$。其纯支持证明 (320.3)–(320.4) 还保证：第一输入在非经典源 $t$ 时，同源输入的整个输出及异源输入的整个输出都在 $j_tH_{n_t}$。因此以下是原规范总迹，不是仅取目标压缩后遗漏其他输出的迹。

固定高块 $t$。对另一源 $r\ne t$ 的每颗 primitive $p$，取 $t$ 内任意 primitive $e$。两者正交，(328.2) 给

$$
\tau(D(j_te,j_rp))=F_t(j_rp).
\tag{335.3}
$$

$\mathsf X_{\rm HQ}$ 保留这个次序，包含经典与二阶第二源；primitive 张成各源，遂有 $F_t|_{\bigoplus_{r\ne t}H_{n_r}}=0$。记 $f_t=F_tj_t$。320.1 的原右单位关系现在是 $\eta_t=-f_t(I_t)$。对 (334.2) 的任一半角对，同源整输出局部性及 $\operatorname{Tr}e=\operatorname{Tr}p=1$ 给

$$
\tau(D(j_te,j_tp))
=f_t(p)-\tfrac12f_t(I_t).
\tag{335.4}
$$

故线性泛函 $g_t(b)=f_t(b)-\tfrac12f_t(I_t)\operatorname{Tr}b$ 在全部所选第二输入上为零。张成整个理想使 $g_t=0$；取 $b=I_t$，得到 $(1-n_t/2)f_t(I_t)=0$。$n_t\ge3$，故 $f_t(I_t)=0$、$f_t=0$，于是整个 $F_t=0$、$\eta_t=0$，(320.1) 恰变成 (335.2)。

对任意 ZERO 标签 $(a_t(p),p)$，首输入在高块且与第二输入正交；再用 (328.2) 得原总迹为 $F_t(p)=0$。这包括 ZERO 第二基的全部外部低块及经典元，故不是仅在 $t\times t$ 上的有限基改写。全程未消去经典第一槽，也未使用 LU、SC、导子或 sigma。∎

**定理 335.2（字面域、局部严格蕴涵与全网等价分开）。** 若 $E$ 有高块，则有限 HALF 与定义 327.1 的有限 ZERO 标量测试域互不包含。尽管如此，在定理 335.1 的单载体背景上，$\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}$ 蕴涵 $\mathsf Z_{\rm fin}$；反向一般不成立。

证明。HALF 的族非空且全部为同块半重叠，ZERO 全部为正交，故 HALF 有 ZERO 中没有的标签。ZERO 的 (327.2) 含高块自己的对角 primitive，与其配对的首输入是同块另一正交原子；这样的同块零角既非 HALF 标签，也非跨中心 $\mathsf X_{\rm HQ}$ 标签。因此字面上两域不嵌套；跨中心两域可能有交集不影响此结论。

正向是 335.1。反向的局部诊断取

$$
\begin{gathered}
E=H_3(\mathbb C)\oplus H_2(\mathbb C)\oplus\mathbb R^k,
\qquad 5+k>p_*,\\
D(a,b)=0\oplus
\left(\frac{\operatorname{Tr}b_3}{3}
-\frac{\operatorname{Tr}b_2}{2}\right)a_2\oplus0.
\end{gathered}
\tag{335.5}
$$

右单位由 $1-1=0$ 成立。primitive 第一输入不在二阶块时输出为零，在二阶块时输出沿该首原子，故整个零／半角整支持成立。全部高块首输入的输出为零，所以每一种 ZERO 选择及每一种高块 HALF 族均通过。但对二阶首原子 $e$ 和三阶第二原子 $p$，原规范总迹为 $\tau(D(e,p))=1/3$，违反保留的有序 $\mathsf X_{\rm HQ}$。这证明反向失败；没有给出 AC、X/R、原过程或 sigma，因而不是完整 $B_*$ 的反模型。完整背景的反向另由定理 336.1 提供，不能移到此单载体层。∎

## 336. 两份完整背景上的同签名对应及现有消费者

**定理 336.1（有限 HALF 的完整条件理论）。** 对任意预先固定的全部 admissible 族 $\mathcal F$、任意定义 327.1 的 ZERO 选择 $\mathcal Z$，以及同一原菜单、$\mathcal K$、$J_0,t_0$，分别对 $B_*=B$ 与 $B_*=\mathsf B_{\rm cl}$ 有

$$
\begin{aligned}
B_*+\mathsf G_{0h}+\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{{\rm fin},\mathcal Z}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{{\rm finHALF},\mathcal F}(B_*)
&\Longleftrightarrow\mathsf C_{{\rm fin},\mathcal Z}(B_*)
\Longleftrightarrow\mathsf C_{\rm HQ}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{336.1}
$$

$\mathsf C_{\rm fin}$ 就是 §§327–333 的公开有限 ZERO 候选。所有对应在全部原数据及全部原合法有限历史上为恒等，并对上述每种先定选择同时成立。词卷 340.1 及本卷 331.1 的整个非空 tagged-CP 族分别满足两份有限 HALF 候选，包含无实际 $M_2$ 对象或简单块的完整子族。

证明。母卷 30.1／67.3 独立供应全部对象的原右单位，框架卷 246.1 独立供应静态复直和；定义 334.1–334.2 保留它们在精确／闭背景中的各自全部前件。335.1 因此在每个选中对象给出全部 ZERO 测试，直接取得本卷 329.1 的完整入口。

精确匹配其实际参考桥：(335.2) 是 (328.1) 的同一全输入式，包含所有非经典源、二阶源、经典第一槽及经典自输入补偿。框架卷 202.1 分离的是任意原 $E_A$ 的整个空间；329.1 在同一个实际 $J$ 及其原身份事件／全事件 R 所供的某个实际 $K=JP^{\otimes k}$ 中使用此式。$K$ 因含高目标 $U=(T,V)$ 而确在原选中域；经典中心对的原有序交叉零才逐项清掉 $\ell_{Us}$。并非所有源或目标都高阶，也不要求原嵌入保 primitive、等距或任意一个目标单独分离。故 329.1 的既有下降覆盖所有原小对象、经典中心、旧输出及失败输出，取得全域 I+SC，不能把单块 (335.4) 独自当作此桥。

反向严格在完整背景中使用 329.1 及框架卷 275.2：全域 I+SC 在 $B$ 中通过原 Z，在 $\mathsf B_{\rm cl}$ 中通过母卷 68.2 的全范围 $\mathsf Q$，分别得到含零分支的共同尺度及逐块交换子，经典和跨块项为零。因此全部半角及全部跨中心规范迹为零，包含任意 $\mathcal F$、$\mathcal Z$。闭背景的延拓仍在同一固定原执行内进行，不补实际极限准备。由此也取得词卷 337.1 的 $\mathsf G_{\rm HQ}$，证明第一行与选择无关性。

最后只给这些等价加上同一字面 $\sigma_{t_0}$。框架卷 276.1、本卷 330.1 及词卷 338.1 已给其精确作用：$w_0/4=\kappa w_0/4$、$w_0>0$，故 $\kappa=1$。不更换原 $D$ 或复坐标中的原符号，不用词卷 350.2 的额外原脉冲律代替 sigma。第二行及单位尺度后的全部重构于是直接复用现有定理。

完整满足族原来就有同一 $D=\mathrm i[a,b]/2$，全部半角与跨中心迹均为零，故对每一种 $\mathcal F$ 成立；其同一 sigma、任意正定 $r_{A,s}$ 原比较参数与不等正权、全部密度及相关密度、带实现标签的完整 CP 仪器、实际细口、同数两侧返回／反向资料、全部失败与合法历史由词卷 340.1 的完整构造供应。无实际 $M_2$ 子族取同一 $P=\mathbb C\oplus M_3$ 及块大小 $3^k$ 的原对象域，不把数学二阶角升级为对象。以上只应用既有满足族，不另造局部模型充作完整见证。∎

**推论 336.2（完整消费者的准确引用对应）。** 在定理 336.1 的条件下，本卷定理 330.1、324.2 与词卷推论 339.1 的全部原范围消费者直接适用于同一数据；其前件对应为：

| 原量词与已取得的关系 | 现有结论及其所有者 |
| --- | --- |
| 全域 I+SC、同一 sigma、原 Jordan 乘法和同一 $D$ | 框架卷 277.1、本卷 (330.2)：$\mathcal A_A=\bigoplus_s B(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$，原正锥和全部中心保持，$a\cdot b=a\circ b-\mathrm iD_ab$、$D_ab=\mathrm i[a,b]/2$，原曲率及每个幂等元的 $D_c^2=-P_c/4$。 |
| 全部原准备、原 $g^0$ 和原不等权 $q$ | (330.3)、词卷 (339.2)：$\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$、$\alpha(y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$、$\tau_A(\rho_\alpha)=\alpha(u_A)$。一般不把 $x_\alpha$ 当作 $\widehat x_\alpha$；零、奇异及次归一质量保持。 |
| 原 X 的 Jordan／同一 $D$ 保持、有序交叉零、乘积张成及实际乘积准备分离 | 330.1、词卷 339.1：每个已声明实际联合是保留全部中心对的同取向普通复张量，全部实际相关输入保持；不要求联合的 $q$、$B_A$ 因子化。 |
| 每个旧事件的全事件 R、同设备同记录旁接及完整相关正锥；原次幺性与完整效果和 | (330.3)、词卷 339.1：$\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 是原事件的 CP/TNI 运输，原完整设备事件和为 TP；闭背景按母卷 69.2 在同一执行上延拓。 |
| 整个 AC、精确 $N_u$、Xs 及原合法连线 | (330.4)、324.2：对每个数学效果保留原所选精确有限平方根词的 $\sqrt e\rho\sqrt e$ 及原许可相关执行；每个占用失败方向的完整输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其他方向／中心用原失败映射，仅原实际丢弃才取质量。 |
| 实 Jordan F、同实现实际细记录、原分组／遗忘及具名同数双返回和反向资料 | (330.5)、词卷 (339.5)：$S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$，$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；原 $q_\ell>0$ 不归一，零标签、完整失败及原反向资料不丢失。 |
| 原箭头、实际记录分支、已供并行联合与所有原合法有限接续 | (330.6)、词卷 (339.6)：$\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$，含空历史、顺序、自适应、并行、分组／遗忘、零／失败／返回／停止；只在原分母正时取条件概率。 |

证明。336.1 已取得每个引用定理的完整候选及不变背景；表中逐项是其已有结论在同一原数据上的应用。$B_A$ 是比较双运输，$\dagger_0$ 是原 $g^0$ 伴随，不是背景 $B_*$ 或任取 $q$ 伴随。数学 Kraus 分解不供应实际记录，数学压缩不供应原事件，所选平方根词不替换任何旧同效果设备。故这里只引用完整消费者，不重复状态／过程重构。∎

## 337. 半角关系的两首槽读取与一首槽盲方向

**定理 337.1（局部高简单块的准确首槽数）。** 固定单块 $H_n(\mathbb C)$、$n\ge3$，以及右单位和整个 $\mathsf G_{0h}$ 的实双线性 $D$。任取先于 $D$ 固定的两颗不同 primitive $e,f$，无需正交。存在只以 $e,f$ 为第一输入、第二输入张成整个 $H_n$ 的有限半角族，可取 $n^2$ 个有序对。其迹零迫使 (320.2) 的整个径向泛函为零，因而局部 $D(a,b)=\alpha\,\mathrm i[a,b]$。

若只允许一颗固定首原子 $e$，即使测试它的全部半角第二输入，也不能取得该结论；正常形中的精确径向盲族为

$$
D_\lambda(a,b)=\lambda\{\operatorname{Tr}(eb)a-a\circ b\},
\qquad \lambda\in\mathbb R.
\tag{337.1}
$$

可另加任意交换子项。这里“两颗足够、一颗不足”仅针对这个单块半角首槽采样类型；不改动候选另行全量保留的 $\mathsf X_{\rm HQ}$，不与 ZERO 的正交首槽下界混算，也不是完整原网络的最低公理数或最低样本数。

证明。使用 Hermitian 迹对偶和算子 frame 的标准张成／消去子方法（Scott，*Tight informationally complete quantum measurements*，§III、式 (34)–(35)，[arXiv:quant-ph/0604049v2](https://arxiv.org/html/quant-ph/0604049v2)）作如下固定角计算；这些线性代数是中间工具，不是另立的几何分类。

记 $\mathcal S_e=\{p\in\operatorname{Prim}(H_n):\operatorname{Tr}(ep)=1/2\}$。写 $e=[v]$，$[v]=vv^*$；其全部元素可写成

$$
p_{w,\theta}=\tfrac12
\{e+[w]+\exp(-\mathrm i\theta)vw^*+
\exp(\mathrm i\theta)wv^*\},
\quad w\perp v,\quad \|w\|=1.
\tag{337.2}
$$

若 Hermitian $H$ 满足 $\operatorname{Tr}(Hp)=0$ 对全部 $p\in\mathcal S_e$，改变 $\theta$ 得 $v^*Hw=0$，再得 $w^*Hw=-v^*Hv$ 对所有单位 $w\perp v$ 成立。Hermitian 极化遂给 $H|_{v^\perp}=-hI$、$h=v^*Hv$，即 $H=h(2e-I)$；反向直接代入。因此在普通迹内积下

$$
(\operatorname{span}_{\mathbb R}\mathcal S_e)^\perp
=\mathbb R(I-2e),\qquad
\operatorname{span}_{\mathbb R}\mathcal S_e
=\{b:\operatorname{Tr}((I-2e)b)=0\}.
\tag{337.3}
$$

这是一份余维一的第二槽盲面，不是整个理想。对不同 $e,f$，$I-2e$ 与 $I-2f$ 不成比例：两者迹均为 $n-2\ne0$，比例必须为一，继而会有 $e=f$。所以 $\mathcal S_e\cup\mathcal S_f$ 的张成为整个 $H_n$。有限维基抽取给 $n^2$ 颗独立第二输入，每颗配上其所属的首锚，得到所需有限族；单一 $\mathcal S_e$ 只有维数 $n^2-1$，所以两颗首锚实际都会出现。选择全过程只依静态 $e,f$，不读取 $D$。

局部 (320.2) 写为

$$
D(a,b)=\alpha\,\mathrm i[a,b]+f_0(b)a-f_0(I)a\circ b.
\tag{337.4}
$$

令 $f_0(b)=\operatorname{Tr}(Hb)$。半角测试读取的不是任意双线性系数，而是同一个

$$
g_0(b)=f_0(b)-\tfrac12f_0(I)\operatorname{Tr}b
=\operatorname{Tr}\bigl((H-\tfrac12\operatorname{Tr}(H)I)b\bigr).
\tag{337.5}
$$

两首槽有限族使 $g_0=0$，取单位后因 $n\ne2$ 得 $f_0=0$，与 (335.4) 的径向消去一致。

若只取首锚 $e$，(337.3) 说全体许可测试恰使 $H-\tfrac12\operatorname{Tr}(H)I\in\mathbb R(I-2e)$。取迹并代回，等价于 $H\in\mathbb Re$，故留下的径向自由恰为 (337.1)。它满足右单位，且对任意 primitive 输入两项都支撑在其共同角内，故满足整个 $\mathsf G_{0h}$；首锚 $e$ 的每个半角迹为 $\lambda(1/2-1/2)=0$。为看见其非零盲值，在 $e^\perp$ 内取正交 primitive $r,s$，令 $p=[(v_r+v_s)/\sqrt2]$。则 $\operatorname{Tr}(rp)=1/2$、$\operatorname{Tr}(ep)=0$，从而 $\tau(D_\lambda(r,p))=-\lambda/2$。$\lambda\ne0$ 时原全半角迹已失败，不能把单锚通过读成全部半角通过。这是单块诊断，不声称它能扩成满足完整 $B_*$、实际联合和同一 sigma 的原世界。∎

**定义 337.2（不同几何对象的关系）。** (337.3) 的盲法向是 $I-2e$；将原右单位带来的中心化 (337.5) 还原以后，正常形泛函的盲方向才是 $b\mapsto\operatorname{Tr}(eb)$。两个不同首锚消去的是这份径向读取盲区。ZERO 的 331.2 使用全部正交第二输入，其共同盲方向是虚交叉 Hermitian 元，测试类型不同，三首槽结论不被 (337.3) 改判。

每个同块不同 primitive 的支持角仍是数学 $H_2(\mathbb C)$，实维四，无迹部分实维三；迹一正截面是 Bloch 球体，其纯态边界为球面。半重叠对应复射影角 $\pi/4$、Bloch 方向正交，零重叠对应射影角 $\pi/2$、Bloch 对径。有限族不把这一球截面变成实际 qubit 或物理三维空间。跨中心没有半角；其支持为 $\mathbb Re\oplus\mathbb Rp$，规范无迹截面只是一条 $\mathbb R(e-p)$。更大结构是每块的复射影角网及共享同一原 $D$ 的实际联合相容关系。两首锚的有限读取利用整个高块，三实维角描述一张秩二截面，二者不能互代。

## 338. 来源相对的增量及完整几何解释

**定义 338.1（成熟中间工具与承重综合）。** 仓内前件取固定公开修订 [13f4288c2940bd2aa4020cec789956b9265769f5](https://github.com/the-omega-institute/trureturing/tree/13f4288c2940bd2aa4020cec789956b9265769f5)：本卷 320.1、328–333 是无迹前件缺席时的全来源正常形及有限 ZERO 的现成全范围桥；词卷 333–343 是完整 $\mathsf C_{\rm HQ}$、其原跨中心迹域、消费者和完整满足族；母卷 30.1／67.3、框架卷 202.1、246.1、265、275–277 分别供应右单位、实际整个对象分离、静态坐标、原有限标签及共同尺度。它们保持各自完整前件，不以本增补重交既有分类或重构。

Brešar–Špenko，*Functional identities of one variable*，[arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2)，讨论特征零矩阵代数上交换多线性迹的标准形，是 320.1 已消费的中间来源；这里不另造函数恒等式分类。Scott 的上述 §III、Proposition 10、式 (34)–(35) 给已采用量子测量中的 informational completeness 和算子 frame 观点，有限张成／消去子及 (337.2)–(337.3) 的 Hermitian 极化计算均按成熟线性代数使用，不作为独立发明；任意所选半角族也未被宣称为归一化 POVM、紧 frame 或可供实际仪器。Gehér，*Symmetries of projective spaces and spheres*，[arXiv:1606.03584v1，§§1–2](https://arxiv.org/html/1606.03584v1)，处理双向保持固定角的射影双射；这里的矩阵值有序双线性 $D$ 不是那种双射，不借其 Wigner 分类充作 (335.3)–(335.4) 的证明。以上成熟工具记为 $\texttt{literature-attested}$。

本处 $\texttt{repo-derived}$ 的承重差额仅是：在原有序 $\mathsf X_{\rm HQ}$ 仍全量保留时，半角迹读数精确读取正常形的中心化泛函，任意 (334.2) 的有限族把它消掉，取得有限 ZERO 已发表桥所需的全来源入口；并准确区分该局部蕴涵、两首槽的径向盲方向和两份完整背景中的恒等等价。一般层析、固定角射影双射与交换迹标准形各自的原文结论不供应这个特定原签名的桥；这里不由检索未命中推断历史原创。有限 HALF 相对原 $\mathsf C_{\rm HQ}$ 确实删除迹标签：只要有高块，其连续半角族含所选有限族以外的对；原实际 $J_0$ 已有高块。与有限 ZERO 则是 335.2 的互不包含测试域，不称为 dev 上的进一步全局简化、独立前提数减少、认证更便宜、物理效率或全网最小性。

**定义 338.2（完整条件理论的来源义务）。** 具体原 $\Omega$ 是否供应完整 $B_*$、整个 $\mathsf G_{0h}$、原全部 $\mathsf X_{\rm HQ}$、有限半角关系和同一 sigma，仍是各自原来源义务；数学可选不等于实际可取得或可控制。词卷 350–355 的有限原脉冲结论严格以其原实商、同一旧 $D$ 的偶／奇响应律及相应完整网络前件为条件，不被本处有限族倒供；本处也不取得其有符号原门绑定。已有全删迹余量、HQQ／HM 及 SourceU27047、静态供应／重叠等聚焦问题保持各自原义，不在此重开或结算。

本卷 324.3 与词卷 339.2 的物理接口分别保留：连续确定可逆器件、物理时钟、具体 Hamiltonian／能量及共同作用量／$\hbar$ 标定；任意独立成功支的共同完整仪器及原类型控制、记录、合法连线；每个旧同效果设备自己的完整输出校准。代数系数 $1/2$、数学支持角和有限采样族不供应这些接口，条件理论也不证明全部公理已从原世界内生。

**定义 338.3（两扇半窗与整张关系网）。** 白话说，原来整座世界不动：量子街区与经典房间、大小不同的中心和原比较尺、全部实际准备及其质量、真正的联合与纠缠输入、每台旧设备和原细记录、完整失败、分组遗忘、带原成功数的双返回和同数反向资料，以及每条合法有限历史都留下。候选仍要求两颗原子完全错开或恰好重叠一半时，整份推动待在共同的小屋里；涉及量子街区的跨街区总账仍逐个次序全部检查，只把同街区无穷多扇半窗的总账，换成大街区内一份事先选好、第二输入能拼出整个房间的有限半窗。已有正常形说明，跨街区账先堵住大街区对外部来源的暗读，半窗账再读出内部那份“看第二输入、沿第一输入伸缩”的余量；右边整个单位使这个读数带着固定中心化，有限张成于是把余量清零。若只用一扇固定首窗，即使绕它检查全部半窗，也有一条明确的伸缩方向能藏住；任意两扇不同的首窗配上合适有限第二输入便能看清它，无需两窗正交。这里的两扇属于半角采样，不能拿来推翻零角采样的三扇结论，更不等于整张原网只需两个测试。小屋内的无迹空间是三实维球截面，跨中心却只有一条增减相抵线，它们共享同一关系并嵌在更大的复射影角网里。经典第一槽和自输入补偿不能凭球面图景删去；在原来实际存在的参考整体中，原有序交叉零才清掉它们，高阶目标共同分离整个原对象，沿已有有限 ZERO 桥把导子、自守恒、左单位和所有省去的迹式带回小对象、经典中心与旧输出。最后沿用同一张事先固定的刻度单，不改推动或返回数，既有的复乘法、Born 双运输、实际普通张量与全部相关输入、旧事件、所选精确平方根词及完整失败、真实细口与同数双返回、所有合法有限历史便逐项接回。这个候选因此有完整的条件理论和非空完整模型族；它没有让原来源、物理钟与作用量、共同仪器或旧设备完整输出的证明义务凭空消失，也没有宣告量子起源整体完成。

## 追加锚 C128338（本行以下为增补区）
