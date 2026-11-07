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

## 366. 附录：保留原跨中心域的有限半角候选

**定义 366.1（同一原数据上的有限 HALF）。** 母卷、框架卷分别指 [C123 母卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)和[共同框架续卷](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md)；词卷指[原词与固定关系卷](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md)。分别固定母卷 88.1、框架卷 264.1、272.1–272.2 及词卷 333.1 的完整 $B$、另名完整 $\mathsf B_{\rm cl}$，任一记作 $B_*$。$B$ 要求每个所需对象及实际联合的实际准备精确有限正生成，$\mathsf B_{\rm cl}$ 要求其闭正生成；不互换两者，不把数学极限态增加为实际准备。

整个原 $\Omega$、原全语境响应商、已经给定的实双线性 $d_A(a,b)=D^A_ab$、原 $q_A,L_A,\circ_A$ 均固定。仅由框架卷 246.1 使用静态坐标

$$
E_A=\bigoplus_{s\in S_A}H_{n_s}(\mathbb C),\qquad
u_A=(I_s)_s,\qquad
\tau_A=\sum_s\operatorname{Tr}_{n_s},\qquad
q_A(a,b)=\sum_sw_{A,s}\operatorname{Tr}(a_sb_s),\quad w_{A,s}>0.
\tag{366.1}
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
\tag{366.2}
$$

这里 $j_t$ 是数学理想包含；第二槽张成的是整个该理想，包含单位方向，不是仅无迹部分。族可冗余，各对象、各块各自有限，原对象域不要求有限。选择只依静态非 $D$ 数据；同一选择同时用于比较所有原 $D$。定理 369.1 给这种族的存在性。

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
\tag{366.3}
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
\tag{366.4}
$$

其中 $W_e(x)=\|P_ex\|_{q_A}^2/2$，不重选 $t_0$、不缩放 $D,q,W$ 或任何原返回数。相对词卷 $\mathsf C_{\rm HQ}$，全部连续半重叠迹只留下 (366.2) 的有限对：二阶块上的半角迹不再独立要求，高阶块上只要求所选有限族；经典块没有半重叠对。

**定义 366.2（完整原范围及数学选择的类型）。** 保留全部原单体、实际有序联合、旧输出、失败输出、经典标签和参考；全部中心、不等量子块、不等正 $q$ 块权、原比较 $g^0$；全部原准备、零及次归一质量、实际乘积准备与全部实际相关输入。设备、端口、实现和记录身份不按响应合并。整个 AC、精确 $N_u$、原 X/Xs、全事件 R、实 Jordan 意义的原 F、同实现实际细口、细化／分组／遗忘、零／失败／停止、具名原同标量两侧支持返回、同数反向资料及每条原合法有限顺序、自适应和并行历史均保持原量词。F 的两个支持、完整输出、同一正返回数及反向资料严格取词卷 333.1 的实 Jordan 合同。

X 仍仅取原含幺 Jordan／同一 $D$ 嵌入、原有序交叉零、乘积张成及实际乘积准备。不输入 LU、O、交替、SC、导子、斜伴随、协变、$D$ 模身份、输出理想保持或反向交叉零；不添直接 $AP$、共同参考指数、实际 $M_2$、任意操作、共同仪器或物理标定。数学理想、primitive、支持角、压缩和有限族的选择都不取得实际对象、准备、设备或控制身份，也不删除任何已经声明的实际接口。所有未直接测试的小对象、低简单块及经典来源仍属于完整背景。

## 367. 半角有限族怎样接到有限 ZERO 的全输入公式

**定理 367.1（保留跨中心域时的局部蕴涵）。** 固定一个复 Hermitian 直和 $E$ 及实双线性 $D$，只假设右单位 $D(a,u)=0$、整个 $\mathsf G_{0h}$。固定任意 (366.2) 的族。在这个单载体层，

$$
\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}
\ \Longrightarrow\
F_t=0\quad(n_t\ge3)
\ \Longrightarrow\ \mathsf Z_{\rm fin}
\tag{367.1}
$$

对定义 327.1 的每一种先定 ZERO 选择成立。$F_t$ 取定理 320.1 的全部来源正常形；消去后对全部完整输入，恰有

$$
\pi_tD(a,b)=\alpha_t\,\mathrm i[a_t,b_t]
+\sum_{s:n_s=1}\ell_{ts}a_s(b_t-b_sI_t).
\tag{367.2}
$$

不在此断言经典补偿行消失，亦不在此断言低目标或全部 $\mathsf X_{\rm HQ}$ 可由 $\mathsf Z_{\rm fin}$ 恢复。

证明。直接使用 320.1，而不重新分类 $D$。其纯支持证明 (320.3)–(320.4) 还保证：第一输入在非经典源 $t$ 时，同源输入的整个输出及异源输入的整个输出都在 $j_tH_{n_t}$。因此以下是原规范总迹，不是仅取目标压缩后遗漏其他输出的迹。

固定高块 $t$。对另一源 $r\ne t$ 的每颗 primitive $p$，取 $t$ 内任意 primitive $e$。两者正交，(328.2) 给

$$
\tau(D(j_te,j_rp))=F_t(j_rp).
\tag{367.3}
$$

$\mathsf X_{\rm HQ}$ 保留这个次序，包含经典与二阶第二源；primitive 张成各源，遂有 $F_t|_{\bigoplus_{r\ne t}H_{n_r}}=0$。记 $f_t=F_tj_t$。320.1 的原右单位关系现在是 $\eta_t=-f_t(I_t)$。对 (366.2) 的任一半角对，同源整输出局部性及 $\operatorname{Tr}e=\operatorname{Tr}p=1$ 给

$$
\tau(D(j_te,j_tp))
=f_t(p)-\tfrac12f_t(I_t).
\tag{367.4}
$$

故线性泛函 $g_t(b)=f_t(b)-\tfrac12f_t(I_t)\operatorname{Tr}b$ 在全部所选第二输入上为零。张成整个理想使 $g_t=0$；取 $b=I_t$，得到 $(1-n_t/2)f_t(I_t)=0$。$n_t\ge3$，故 $f_t(I_t)=0$、$f_t=0$，于是整个 $F_t=0$、$\eta_t=0$，(320.1) 恰变成 (367.2)。

对任意 ZERO 标签 $(a_t(p),p)$，首输入在高块且与第二输入正交；再用 (328.2) 得原总迹为 $F_t(p)=0$。这包括 ZERO 第二基的全部外部低块及经典元，故不是仅在 $t\times t$ 上的有限基改写。全程未消去经典第一槽，也未使用 LU、SC、导子或 sigma。∎

**定理 367.2（与有限 ZERO 的字面域、局部严格蕴涵及全网等价）。** 若 $E$ 有高块，则有限 HALF 与定义 327.1 的有限 ZERO 标量测试域互不包含。尽管如此，在定理 367.1 的单载体背景上，$\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}$ 蕴涵 $\mathsf Z_{\rm fin}$；反向一般不成立。

证明。HALF 的族非空且全部为同块半重叠，ZERO 全部为正交，故 HALF 有 ZERO 中没有的标签。ZERO 的 (327.2) 含高块自己的对角 primitive，与其配对的首输入是同块另一正交原子；这样的同块零角既非 HALF 标签，也非跨中心 $\mathsf X_{\rm HQ}$ 标签。因此字面上两域不嵌套；跨中心两域可能有交集不影响此结论。

正向是 367.1。反向的局部诊断取

$$
\begin{gathered}
E=H_3(\mathbb C)\oplus H_2(\mathbb C)\oplus\mathbb R^k,
\qquad 5+k>p_*,\\
D(a,b)=0\oplus
\left(\frac{\operatorname{Tr}b_3}{3}
-\frac{\operatorname{Tr}b_2}{2}\right)a_2\oplus0.
\end{gathered}
\tag{367.5}
$$

右单位由 $1-1=0$ 成立。primitive 第一输入不在二阶块时输出为零，在二阶块时输出沿该首原子，故整个零／半角整支持成立。全部高块首输入的输出为零，所以每一种 ZERO 选择及每一种高块 HALF 族均通过。但对二阶首原子 $e$ 和三阶第二原子 $p$，原规范总迹为 $\tau(D(e,p))=1/3$，违反保留的有序 $\mathsf X_{\rm HQ}$。这证明反向失败；没有给出 AC、X/R、原过程或 sigma，因而不是完整 $B_*$ 的反模型。完整背景的反向另由定理 368.1 提供，不能移到此单载体层。∎

**定理 367.3（与单匹配原子的准确来源比较）。** 取定义 334.1 的任意先定匹配资料。在 $B_*+\mathsf G_{0h}$ 给出的某个实际 $K_A$ 及目标 $U=U_{A,T}$ 上，记 $\mathsf Z_{\rm bal}(A,T)$ 为 (335.2) 在这个 $A,T$ 上的全部等式。则

$$
\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}
\ \Longrightarrow\ F_U=0
\ \Longrightarrow\ F_U\circ h_A=0
\ \Longleftrightarrow\ \mathsf Z_{\rm bal}(A,T).
\tag{367.6}
$$

其中 $F_U=0$ 指整个 $E_{K_A}$ 上清零，$F_U\circ h_A=0$ 只指原来源像上清零。在仅保留右单位、整支持、两因子 $D$ 保持和原有序交叉零的单联合片段中，来源像清零及该匹配原子的全部正交配平均不蕴涵任意一个 admissible 全块半角族通过。这一局部区别不构成两份完整背景中的严格性结论。

证明。该实际 $K_A$ 在选中域，且 $n_U\ge3$，所以 367.1 直接给第一个箭头。第二个箭头是限制泛函。定理 336.1 已在同一个完整来源上证明 $F_U\circ l=0$ 及 (336.2)，故最后的等价直接成立；匹配差的基与补偿任意性也保持其原结论。

局部反向直接复用定理 339.1 的同一个单联合片段，不另造完整世界。在该片段中任选 $m\ge2$ 使 $m^2>p_*$，取其两个 $H_m$ 因子、$E=H_{m^2}$ 和同一最大纠缠匹配原子 $e$；以 $h(x)=x\otimes I_m$、$l(y)=I_m\otimes y$ 记两像。该片段已经给出 $D(a,b)=F(b)a$、$F(I)=0$、$F\ne0$，且 $F\circ h=F\circ l=0$，$F|_{\ker L_e}=0$。于是同一转置匹配差 $z(x)=h(x)-l(x^{\mathsf T})$ 满足全部来源配平；在该锚点甚至每个正交 primitive 的迹分别为零。另一方面，对任意 (366.2) 的全块半角族，$\tau(D(e',p))=F(p)$。若全部有限值为零，第二输入张成整个 $E$ 就给 $F=0$，与该片段的 $F\ne0$ 矛盾。因此每一种这样的半角族都有非零值。该简单载体没有跨中心对，$\mathsf X_{\rm HQ}$ 为空，区别确由半角要求产生。

这个片段没有完整 $B_*$、同一 sigma 及每个原对象自己的匹配资料，不能反驳 337.1 或下面的 368.1。(335.2) 检验的是线性补偿差，允许谱原子贡献相抵；(366.3) 检验的是各有序 primitive 对的迹。故这里比较的是已证明的逻辑关系，不宣称配平与 HALF 的原始测试标签集合相互包含。∎

## 368. 两份完整背景上的同签名对应及现有消费者

**定理 368.1（有限 HALF 的完整条件理论）。** 对任意预先固定的全部 admissible 族 $\mathcal F$、任意定义 327.1 的 ZERO 选择 $\mathcal Z$，任一份定义 334.1 的先定匹配资料，以及同一原菜单、$\mathcal K$、$J_0,t_0$，分别对 $B_*=B$ 与 $B_*=\mathsf B_{\rm cl}$ 有

$$
\begin{aligned}
B_*+\mathsf G_{0h}+\mathsf X_{\rm HQ}+\mathsf H_{\mathcal F}
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{{\rm fin},\mathcal Z}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC}\\
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{\rm bal}\\
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf Z_{\rm cen}^{>}
\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf T_{\rm self}^{>}\\
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf T_{\rm uneq}^{>},\\
\mathsf C_{{\rm finHALF},\mathcal F}(B_*)
&\Longleftrightarrow\mathsf C_{{\rm fin},\mathcal Z}(B_*)
\Longleftrightarrow\mathsf C_{\rm bal}(B_*)\\
&\Longleftrightarrow\mathsf C_{\rm cen}(B_*)
\Longleftrightarrow\mathsf C_{\rm self}(B_*)
\Longleftrightarrow\mathsf C_{\rm uneq}(B_*)\\
&\Longleftrightarrow\mathsf C_{\rm HQ}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{368.1}
$$

$\mathsf C_{\rm fin}$ 就是 §§327–333 的公开有限 ZERO 候选。所有对应在全部原数据及全部原合法有限历史上为恒等，并对上述每种先定选择同时成立。中心候选、全效果自比较候选及固定不等权两原子候选的无标定箭头分别直接取公开定理 344.2、352.1、360.1；含同一 sigma 的对应分别复用 345.1、353.1、361.1。这里复用这些已经发表的完整等价与消费者，不另作重构。词卷 340.1 及本卷 331.1 的整个非空 tagged-CP 族分别满足两份有限 HALF 候选，包含无实际 $M_2$ 对象或简单块的完整子族。

证明。母卷 30.1／67.3 独立供应全部对象的原右单位，框架卷 246.1 独立供应静态复直和；定义 366.1–366.2 保留它们在精确／闭背景中的各自全部前件。367.1 因此在每个选中对象给出全部 ZERO 测试，直接取得本卷 329.1 的完整入口。

精确匹配其实际参考桥：(367.2) 是 (328.1) 的同一全输入式，包含所有非经典源、二阶源、经典第一槽及经典自输入补偿。框架卷 202.1 分离的是任意原 $E_A$ 的整个空间；329.1 在同一个实际 $J$ 及其原身份事件／全事件 R 所供的某个实际 $K=JP^{\otimes k}$ 中使用此式。$K$ 因含高目标 $U=(T,V)$ 而确在原选中域；经典中心对的原有序交叉零才逐项清掉 $\ell_{Us}$。并非所有源或目标都高阶，也不要求原嵌入保 primitive、等距或任意一个目标单独分离。故 329.1 的既有下降覆盖所有原小对象、经典中心、旧输出及失败输出，取得全域 I+SC，不能把单块 (367.4) 独自当作此桥。

反向严格在完整背景中使用 329.1 及框架卷 275.2：全域 I+SC 在 $B$ 中通过原 Z，在 $\mathsf B_{\rm cl}$ 中通过母卷 68.2 的全范围 $\mathsf Q$，分别得到含零分支的共同尺度及逐块交换子，经典和跨块项为零。因此全部半角及全部跨中心规范迹为零，包含任意 $\mathcal F$、$\mathcal Z$。闭背景的延拓仍在同一固定原执行内进行，不补实际极限准备。由此也取得词卷 337.1 的 $\mathsf G_{\rm HQ}$。本卷 337.1 又在各自同一完整背景中把 I+SC 与任意先定匹配资料的 $\mathsf Z_{\rm bal}$ 相接，故无标定的全部等价及选择无关性成立；没有把局部的 $F_U\circ h_A=0$ 擅自当作整个 $F_U=0$。公开 344.2、352.1 分别把这同一全域 I+SC 与原中心中性、自比较中性相接；它们的实际参考、完整正常形和效果区间量词保持全部原前件，不把这些完整背景结论移到 367.1 的单载体层。公开 360.1 在同一完整背景中将固定谱权重的 $\mathsf T_{\rm uneq}^{>}$ 与 $\mathsf T_{\rm self}^{>}$ 及全域 I+SC 相接，故再得不等权两原子一项；其 359.1 所用的全对象正常形 343.1、原正块权和整框架右单位行和均保持原前件，不由单载体 HALF 公式替代。

最后只给这些等价加上同一字面 $\sigma_{t_0}$。框架卷 276.1、本卷 330.1 及词卷 338.1 已给其精确作用：$w_0/4=\kappa w_0/4$、$w_0>0$，故 $\kappa=1$。不更换原 $D$ 或复坐标中的原符号，不用词卷 350.2 的额外原脉冲律代替 sigma。含同一 sigma 的等价再由本卷 338.1、345.1、353.1、361.1 分别接入 $\mathsf C_{\rm bal}$、$\mathsf C_{\rm cen}$、$\mathsf C_{\rm self}$、$\mathsf C_{\rm uneq}$；单位尺度后的全部重构直接复用现有定理。

完整满足族原来就有同一 $D=\mathrm i[a,b]/2$，全部半角与跨中心迹均为零，故对每一种 $\mathcal F$ 成立；其同一 sigma、任意正定 $r_{A,s}$ 原比较参数与不等正权、全部密度及相关密度、带实现标签的完整 CP 仪器、实际细口、同数两侧返回／反向资料、全部失败与合法历史由词卷 340.1 的完整构造供应。无实际 $M_2$ 子族取同一 $P=\mathbb C\oplus M_3$ 及块大小 $3^k$ 的原对象域，不把数学二阶角升级为对象。以上只应用既有满足族，不另造局部模型充作完整见证。∎

**推论 368.2（完整消费者的准确引用对应）。** 在定理 368.1 的条件下，本卷定理 330.1、324.2 与词卷推论 339.1 的全部原范围消费者直接适用于同一数据；其前件对应为：

| 原量词与已取得的关系 | 现有结论及其所有者 |
| --- | --- |
| 全域 I+SC、同一 sigma、原 Jordan 乘法和同一 $D$ | 框架卷 277.1、本卷 (330.2)：$\mathcal A_A=\bigoplus_s B(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$，原正锥和全部中心保持，$a\cdot b=a\circ b-\mathrm iD_ab$、$D_ab=\mathrm i[a,b]/2$，原曲率及每个幂等元的 $D_c^2=-P_c/4$。 |
| 全部原准备、原 $g^0$ 和原不等权 $q$ | (330.3)、词卷 (339.2)：$\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$、$\alpha(y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$、$\tau_A(\rho_\alpha)=\alpha(u_A)$。一般不把 $x_\alpha$ 当作 $\widehat x_\alpha$；零、奇异及次归一质量保持。 |
| 原 X 的 Jordan／同一 $D$ 保持、有序交叉零、乘积张成及实际乘积准备分离 | 330.1、词卷 339.1：每个已声明实际联合是保留全部中心对的同取向普通复张量，全部实际相关输入保持；不要求联合的 $q$、$B_A$ 因子化。 |
| 每个旧事件的全事件 R、同设备同记录旁接及完整相关正锥；原次幺性与完整效果和 | (330.3)、词卷 339.1：$\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 是原事件的 CP/TNI 运输，原完整设备事件和为 TP；闭背景按母卷 69.2 在同一执行上延拓。 |
| 整个 AC、精确 $N_u$、Xs 及原合法连线 | (330.4)、324.2：对每个数学效果保留原所选精确有限平方根词的 $\sqrt e\rho\sqrt e$ 及原许可相关执行；每个占用失败方向的完整输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其他方向／中心用原失败映射，仅原实际丢弃才取质量。 |
| 实 Jordan F、同实现实际细记录、原分组／遗忘及具名同数双返回和反向资料 | (330.5)、词卷 (339.5)：$S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$，$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；原 $q_\ell>0$ 不归一，零标签、完整失败及原反向资料不丢失。 |
| 原箭头、实际记录分支、已供并行联合与所有原合法有限接续 | (330.6)、词卷 (339.6)：$\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$，含空历史、顺序、自适应、并行、分组／遗忘、零／失败／返回／停止；只在原分母正时取条件概率。 |

证明。368.1 已取得每个引用定理的完整候选及不变背景；表中逐项是其已有结论在同一原数据上的应用。$B_A$ 是比较双运输，$\dagger_0$ 是原 $g^0$ 伴随，不是背景 $B_*$ 或任取 $q$ 伴随。数学 Kraus 分解不供应实际记录，数学压缩不供应原事件，所选平方根词不替换任何旧同效果设备。故这里只引用完整消费者，不重复状态／过程重构。∎

## 369. 半角关系的两首槽读取与一首槽盲方向

**定理 369.1（局部高简单块的准确首槽数）。** 固定单块 $H_n(\mathbb C)$、$n\ge3$，以及右单位和整个 $\mathsf G_{0h}$ 的实双线性 $D$。任取先于 $D$ 固定的两颗不同 primitive $e,f$，无需正交。存在只以 $e,f$ 为第一输入、第二输入张成整个 $H_n$ 的有限半角族，可取 $n^2$ 个有序对。其迹零迫使 (320.2) 的整个径向泛函为零，因而局部 $D(a,b)=\alpha\,\mathrm i[a,b]$。

若只允许一颗固定首原子 $e$，即使测试它的全部半角第二输入，也不能取得该结论；正常形中的精确径向盲族为

$$
D_\lambda(a,b)=\lambda\{\operatorname{Tr}(eb)a-a\circ b\},
\qquad \lambda\in\mathbb R.
\tag{369.1}
$$

可另加任意交换子项。这里“两颗足够、一颗不足”仅针对这个单块半角首槽采样类型；不改动候选另行全量保留的 $\mathsf X_{\rm HQ}$，不与 ZERO 的正交首槽下界混算，也不是完整原网络的最低公理数或最低样本数。公开 §§334–341 的单匹配原子检验来源配平，只需清掉 $F_U\circ h_A$，并使用完整实际来源；本定理则在没有这些来源关系的单块上清掉整个径向泛函。两首锚点因此不改进或否定该单匹配原子的完整世界结果。公开 §§342–349 又用原中心迹中性删除候选资料中的辅助匹配选择：不再选匹配原子、补偿映射、来源基或参考剖面。本条的两首锚是单块半角采样的数学选择，不是对该内在中心候选的进一步全局简化。公开 §§350–357 的自比较候选在公理表达中不点名中心、规范迹或辅助选择，只用原 $q_X(a,D^X(a,a))=0$，其量词仍是选中域的全部原数学效果。公开 351.1–352.1 在完整来源正常形中消去全部中心及来源的径向场；本条的单块两首锚数不替换这些完整前件，也不计作对自比较候选的全局改进。公开 §§358–365 的 $\mathsf C_{\rm uneq}$ 又把该自比较标量测试限于全部有序正交 primitive 对的 $e+\tfrac12p$；这里的半权是正交谱权重，不是 HALF 的半重叠。该候选借同一完整来源正常形及整框架右单位相容恢复全部效果，360.1、361.1 已供应其完整等价与消费者。本条仍只计算单块半角采样的首槽数，不减少这个两原子候选的全网前件、关系数或认证成本。

证明。使用 Hermitian 迹对偶和算子 frame 的标准张成／消去子方法（Scott，*Tight informationally complete quantum measurements*，§III、式 (34)–(35)，[arXiv:quant-ph/0604049v2](https://arxiv.org/html/quant-ph/0604049v2)）作如下固定角计算；这些线性代数是中间工具，不是另立的几何分类。

记 $\mathcal S_e=\{p\in\operatorname{Prim}(H_n):\operatorname{Tr}(ep)=1/2\}$。写 $e=[v]$，$[v]=vv^*$；其全部元素可写成

$$
p_{w,\theta}=\tfrac12
\{e+[w]+\exp(-\mathrm i\theta)vw^*+
\exp(\mathrm i\theta)wv^*\},
\quad w\perp v,\quad \|w\|=1.
\tag{369.2}
$$

若 Hermitian $H$ 满足 $\operatorname{Tr}(Hp)=0$ 对全部 $p\in\mathcal S_e$，改变 $\theta$ 得 $v^*Hw=0$，再得 $w^*Hw=-v^*Hv$ 对所有单位 $w\perp v$ 成立。Hermitian 极化遂给 $H|_{v^\perp}=-hI$、$h=v^*Hv$，即 $H=h(2e-I)$；反向直接代入。因此在普通迹内积下

$$
(\operatorname{span}_{\mathbb R}\mathcal S_e)^\perp
=\mathbb R(I-2e),\qquad
\operatorname{span}_{\mathbb R}\mathcal S_e
=\{b:\operatorname{Tr}((I-2e)b)=0\}.
\tag{369.3}
$$

这是一份余维一的第二槽盲面，不是整个理想。对不同 $e,f$，$I-2e$ 与 $I-2f$ 不成比例：两者迹均为 $n-2\ne0$，比例必须为一，继而会有 $e=f$。所以 $\mathcal S_e\cup\mathcal S_f$ 的张成为整个 $H_n$。有限维基抽取给 $n^2$ 颗独立第二输入，每颗配上其所属的首锚，得到所需有限族；单一 $\mathcal S_e$ 只有维数 $n^2-1$，所以两颗首锚实际都会出现。选择全过程只依静态 $e,f$，不读取 $D$。

局部 (320.2) 写为

$$
D(a,b)=\alpha\,\mathrm i[a,b]+f_0(b)a-f_0(I)a\circ b.
\tag{369.4}
$$

令 $f_0(b)=\operatorname{Tr}(Hb)$。半角测试读取的不是任意双线性系数，而是同一个

$$
g_0(b)=f_0(b)-\tfrac12f_0(I)\operatorname{Tr}b
=\operatorname{Tr}\bigl((H-\tfrac12\operatorname{Tr}(H)I)b\bigr).
\tag{369.5}
$$

两首槽有限族使 $g_0=0$，取单位后因 $n\ne2$ 得 $f_0=0$，与 (367.4) 的径向消去一致。

若只取首锚 $e$，(369.3) 说全体许可测试恰使 $H-\tfrac12\operatorname{Tr}(H)I\in\mathbb R(I-2e)$。取迹并代回，等价于 $H\in\mathbb Re$，故留下的径向自由恰为 (369.1)。它满足右单位，且对任意 primitive 输入两项都支撑在其共同角内，故满足整个 $\mathsf G_{0h}$；首锚 $e$ 的每个半角迹为 $\lambda(1/2-1/2)=0$。为看见其非零盲值，在 $e^\perp$ 内取正交 primitive $r,s$，令 $p=[(v_r+v_s)/\sqrt2]$。则 $\operatorname{Tr}(rp)=1/2$、$\operatorname{Tr}(ep)=0$，从而 $\tau(D_\lambda(r,p))=-\lambda/2$。$\lambda\ne0$ 时原全半角迹已失败，不能把单锚通过读成全部半角通过。这是单块诊断，不声称它能扩成满足完整 $B_*$、实际联合和同一 sigma 的原世界。∎

**定义 369.2（不同几何对象的关系）。** (369.3) 的盲法向是 $I-2e$；将原右单位带来的中心化 (369.5) 还原以后，正常形泛函的盲方向才是 $b\mapsto\operatorname{Tr}(eb)$。两个不同首锚消去的是这份径向读取盲区。ZERO 的 331.2 使用全部正交第二输入，其共同盲方向是虚交叉 Hermitian 元，测试类型不同，三首槽结论不被 (369.3) 改判。

每个同块不同 primitive 的支持角仍是数学 $H_2(\mathbb C)$，实维四，无迹部分实维三；迹一正截面是 Bloch 球体，其纯态边界为球面。半重叠对应复射影角 $\pi/4$、Bloch 方向正交，零重叠对应射影角 $\pi/2$、Bloch 对径。有限族不把这一球截面变成实际 qubit 或物理三维空间。跨中心没有半角；其支持为 $\mathbb Re\oplus\mathbb Rp$，规范无迹截面只是一条 $\mathbb R(e-p)$。更大结构是每块的复射影角网及共享同一原 $D$ 的实际联合相容关系。两首锚的有限读取利用整个高块，三实维角描述一张秩二截面，二者不能互代。

## 370. 来源相对的增量及完整几何解释

**定义 370.1（成熟中间工具与承重综合）。** 仓内来源固定于公开修订 [f2d0dcc67df99383eac5aabe2be977b762c7e18c](https://github.com/the-omega-institute/trureturing/tree/f2d0dcc67df99383eac5aabe2be977b762c7e18c)。其中 [13f4288c2940bd2aa4020cec789956b9265769f5](https://github.com/the-omega-institute/trureturing/tree/13f4288c2940bd2aa4020cec789956b9265769f5) 已有的本卷 320.1、328–333 是无迹前件缺席时的全来源正常形及有限 ZERO 的现成全范围桥；词卷 333–343 是完整 $\mathsf C_{\rm HQ}$、其原跨中心迹域、消费者和完整满足族；母卷 30.1／67.3、框架卷 202.1、246.1、265、275–277 分别供应右单位、实际整个对象分离、静态坐标、原有限标签及共同尺度。本卷公开 §§334–341 另给单匹配原子的来源配平、至多 $\dim E_A-1$ 条的每目标方程、两份完整背景的等价及单联合隐藏方向。公开 §§342–349 进一步给出全原对象径向正常形、原中心迹读数及其高秩域到全域下降；$\mathsf C_{\rm cen}$ 用原中心的内在关系删除候选资料中的辅助匹配选择，346.1 把旧来源匹配读数接到原中心读数，345.1 复用已有完整理论。公开 §§350–357 另以选中域全部效果上的原自比较中性 $q_X(a,D^X(a,a))=0$ 定义 $\mathsf C_{\rm self}$；351.1 借两种正比例分离全源径向泛函，352.1 不运输比较尺而回传全域 I+SC，353.1 接回同一 sigma 的完整消费者。该候选的表达不再点名中心、规范迹或辅助选择，354 的裸载体及 primitive 反例仍只承担其已声明的局部边界。公开 §§358–365 的 $\mathsf C_{\rm uneq}$ 使用选中域整个 $E_X$ 的全部有序正交 primitive 对，固定数学效果 $a_{ep}=e+\tfrac12p$ 并要求 $q_X(a_{ep},D^X(a_{ep},a_{ep}))=0$，换序亦然。359.1 用同一无迹前件全对象正常形 343.1，将两个次序的系数关系与原完整框架的右单位零行和合用，消掉全部来源径向场；360.1 接回全域 I+SC，361.1 保持同一 sigma 的完整消费者与非空完整满足族。362 的裸载体和投影片段只承担各自局部边界，364.2 的具体来源义务保留。这些结果保持各自完整前件，不以本附录重交既有分类或重构。

Brešar–Špenko，*Functional identities of one variable*，[arXiv:1307.2260v1，Lemma 3.2](https://arxiv.org/html/1307.2260v1#S3.Thmtheorem2)，讨论特征零矩阵代数上交换多线性迹的标准形，是 320.1 已消费的中间来源；这里不另造函数恒等式分类。Scott 的上述 §III、Proposition 10、式 (34)–(35) 给已采用量子测量中的 informational completeness 和算子 frame 观点，有限张成／消去子及 (369.2)–(369.3) 的 Hermitian 极化计算均按成熟线性代数使用，不作为独立发明；任意所选半角族也未被宣称为归一化 POVM、紧 frame 或可供实际仪器。Gehér，*Symmetries of projective spaces and spheres*，[arXiv:1606.03584v1，§§1–2](https://arxiv.org/html/1606.03584v1)，处理双向保持固定角的射影双射；这里的矩阵值有序双线性 $D$ 不是那种双射，不借其 Wigner 分类充作 (367.3)–(367.4) 的证明。以上成熟工具记为 $\texttt{literature-attested}$。

本处 $\texttt{repo-derived}$ 的承重差额仅是：在原有序 $\mathsf X_{\rm HQ}$ 仍全量保留时，半角迹读数精确读取正常形的中心化泛函，任意 (366.2) 的有限族把它消掉，取得有限 ZERO 已发表桥所需的全来源入口；并准确区分该局部蕴涵、两首槽的径向盲方向和两份完整背景中的恒等等价。一般层析、固定角射影双射与交换迹标准形各自的原文结论不供应这个特定原签名的桥；这里不由检索未命中推断历史原创。有限 HALF 相对原 $\mathsf C_{\rm HQ}$ 确实删除迹标签：只要有高块，其连续半角族含所选有限族以外的对；原实际 $J_0$ 已有高块。与有限 ZERO 则是 367.2 的互不包含测试域；与单匹配原子配平的比较只取 367.3 的明确来源及局部范围，并由 368.1 在完整背景中接到同一模型类。两首槽比三首槽少，只是半角与正交这两种单块逐原子测试类型的区别，不是比公开单匹配原子更少；对 $\mathsf C_{\rm bal}$ 不宣称原始测试域嵌套。相对公开中心候选，有限 HALF 仍保留全部 $\mathsf X_{\rm HQ}$ 并使用先定有限半角族；中心候选已在候选资料中删除匹配原子、补偿和来源基等辅助选择，二者在完整背景中的同类性由 368.1 及公开 344.2、345.1 给出，不把局部两首锚数、有限表示或原始标签改换计作对 $\mathsf C_{\rm cen}$ 的进一步简化，也不宣称两种原始测试域嵌套。相对公开自比较候选，有限 HALF 仍在候选资料中使用规范迹、先定有限族及全部原跨中心迹域；自比较候选使用原 $q,D$ 和全部效果区间，其三次评价不是一份有序 primitive 迹标签子集。两者在完整背景中的等价由 368.1 直接消费公开 352.1、353.1，不能从“每块有限”推出全网有限认证，也不按两首锚数、标量关系模式数或异型原始标签判全局优劣。相对公开不等权两原子候选，有限 HALF 仍使用规范迹、先定有限半角族及全部原跨中心非经典迹域；$\mathsf C_{\rm uneq}$ 的新增标量式只用原 $q,D$ 和固定谱形状，却遍历选中对象整个空间的全部有序正交 primitive 对，包含其经典与二阶块。正交谱半权与同块半重叠不是同一测试，三次自比较也不是有序 primitive 迹标签子集，故不宣称两种原始测试域嵌套。两者在完整背景和同一 sigma 下的同类性由 368.1 直接消费公开 360.1、361.1；其整框架相容不能从本附录的局部首锚数读出，亦不把“每高块有限”与固定两原子测试形状作无共同口径的计数比较。这里不取得 dev 上的进一步全局简化、独立前提数减少、认证更便宜、物理效率或全网最小性。

**定义 370.2（完整条件理论的来源义务）。** 具体原 $\Omega$ 是否供应完整 $B_*$、整个 $\mathsf G_{0h}$、原全部 $\mathsf X_{\rm HQ}$、有限半角关系和同一 sigma，仍是各自原来源义务；数学可选不等于实际可取得或可控制。词卷 350–355 的有限原脉冲结论严格以其原实商、同一旧 $D$ 的偶／奇响应律及相应完整网络前件为条件，不被本处有限族倒供；本处也不取得其有符号原门绑定。本卷 341.2 中来源配平由具体原世界供应的义务也不由本处等价自动证明；公开 348.2 的原中心迹中性及其具体来源义务同样保留；公开 350.1、356.2 的原效果自比较中性及其具体来源义务也未由有限族的数学选择自动供应；公开 358.1、364.2 的固定不等权两原子中性及其具体原来源义务同样保留。已有全删迹余量、HQQ／HM 及 SourceU27047、静态供应／重叠等聚焦问题保持各自原义，不在此重开或结算。

本卷 324.3 与词卷 339.2 的物理接口分别保留：连续确定可逆器件、物理时钟、具体 Hamiltonian／能量及共同作用量／$\hbar$ 标定；任意独立成功支的共同完整仪器及原类型控制、记录、合法连线；每个旧同效果设备自己的完整输出校准。代数系数 $1/2$、数学支持角和有限采样族不供应这些接口，条件理论也不证明全部公理已从原世界内生。

**定义 370.3（两扇半窗与整张关系网）。** 白话说，原来整座世界不动：量子街区与经典房间、大小不同的中心和原比较尺、全部实际准备及其质量、真正的联合与纠缠输入、每台旧设备和原细记录、完整失败、分组遗忘、带原成功数的双返回和同数反向资料，以及每条合法有限历史都留下。候选仍要求两颗原子完全错开或恰好重叠一半时，整份推动待在共同的小屋里；涉及量子街区的跨街区总账仍逐个次序全部检查，只把同街区无穷多扇半窗的总账，换成大街区内一份事先选好、第二输入能拼出整个房间的有限半窗。已有正常形说明，跨街区账先堵住大街区对外部来源的暗读，半窗账再读出内部那份“看第二输入、沿第一输入伸缩”的余量；右边整个单位使这个读数带着固定中心化，有限张成于是把余量清零。若只用一扇固定首窗，即使绕它检查全部半窗，也有一条明确的伸缩方向能藏住；任意两扇不同的首窗配上合适有限第二输入便能看清它，无需两窗正交。这里的两扇属于没有实际来源关系时的单块半角采样，不能拿来推翻零角采样的三扇结论，更不等于整张原网只需两个测试。公开的一颗共同珠子方案已经利用真实参考，把左右作用配成碰不到珠子的差，只检查原对象像里的余量；它可以允许谱原子账值相抵，也不先清空整个大联合。因此两扇半窗没有改进这一颗匹配珠子的完整世界结论，两者只在各自明确的局部目标上比较，完整背景中则沿已有桥相等。公开中心方案还把这颗珠子、补偿和来源基等辅助选择从候选资料中拿掉，直接逐间查原中心的总账；它已有自己的完整条件等价，有限半窗并未在全局上再简化它。公开自比较方案又直接拿每个原效果和自己的推动作原比较，不再在候选表达里点名中心、迹或辅助珠子；它检查的是全部效果，并借同一完整来源排除各房伸缩，不能与这里每块有限的半窗标签或两首锚数直接计数比优。有限半窗与它在完整背景和同一刻度下也沿现有定理相等，没有因此取得进一步全局简化。公开的不等权两珠方案还把自比较限为完全错开的两颗珠子，一颗全权、一颗半权，换位也查；它的“半”是谱权重，这里的“半”是两原子的重叠。它沿原整框架的单位总账清掉各房补偿，不再点名规范迹或先选半窗，但仍遍历选中对象的全部有序正交对。现成完整定理已把两种候选接到同一原世界，不能凭两珠、两窗或每块有限这些不同口径宣称谁在全局更少，也没有由有限半窗的数学存在替它供应具体来源。小屋内的无迹空间是三实维球截面，跨中心却只有一条增减相抵线，它们共享同一关系并嵌在更大的复射影角网里。经典第一槽和自输入补偿不能凭球面图景删去；在原来实际存在的参考整体中，原有序交叉零才清掉它们，高阶目标共同分离整个原对象，沿已有有限 ZERO 桥把导子、自守恒、左单位和所有省去的迹式带回小对象、经典中心与旧输出。最后沿用同一张事先固定的刻度单，不改推动或返回数，既有的复乘法、Born 双运输、实际普通张量与全部相关输入、旧事件、所选精确平方根词及完整失败、真实细口与同数双返回、所有合法有限历史便逐项接回。这个候选因此有完整的纸笔条件理论和非空完整模型族；它没有让原来源、物理钟与作用量、共同仪器或旧设备完整输出的证明义务凭空消失，也没有宣告量子起源整体完成。

## 追加锚 C128370（本行以下为增补区）


## 371. 两个正输入的共同面球相切

**定义 371.1（唯一统一几何候选）。** 分别固定 358.1–358.2 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。同一原 $\Omega,q,D,L,\circ$、全部原对象、原菜单、预选 $t_0$ 及同一原 $\sigma_{t_0}$ 保持。对原正锥中的数学元 $a,b\ge0$，置

$$
x=a+b,\qquad c=\operatorname{supp}(x),\qquad
\mathcal T_q(x)=E_1(c)\cap\{v:q(x,v)=0\},\quad
E_1(c)=Q_cE,\quad Q_c=2L_c^2-L_c.
\tag{371.1}
$$

约定 $\mathcal T_q(0)=\{0\}$。只在原选中域 $\operatorname{rank}E_X>p_*$ 上要求

$$
\boxed{\mathsf F_{\rm fsph}^{>}:\quad
D^X(a,b)\in\mathcal T_{q_X}(a+b)
\qquad(a,b\in C_X).}
\tag{371.2}
$$

唯一完整新候选为

$$
\boxed{\mathsf C_{\rm fsph}(B_*)
:=B_*+\mathsf F_{\rm fsph}^{>}+\sigma_{t_0}.}
\tag{371.3}
$$

$\mathsf G_{0h}$ 与 $\mathsf T_{\rm uneq}^{>}$ 均不另列作输入；它们须由 (371.2) 恢复。原右单位 $D(a,u)=0$ 仍只由完整 $B_*$ 的母卷 30.1／67.3 供应。新增关系 (371.2) 本身不另选 primitive、框架、重叠角、固定谱比、中心迹或匹配资料；完整候选仍保留同一原 $\sigma_{t_0}$ 及其原有的预选 primitive 与半重叠标签。$Q_c$ 管整个支持面，不能换成 $4(L_c-L_c^2)$ 或只查角外压缩。

**定义 371.2（完整量词与简化的尺度）。** 全部经典中心、不等块大小、原不等正权、实际有序联合及其全部原乘积和相关准备、零和次归一质量保持。整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、原设备／端口／细记录／失败身份及完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史均沿 358.2 原样保留。两份准备背景各保持自身的精确有限正生成或闭正生成。

LU、SC、交替、导子、斜伴随、理想保持和模身份均非新增前提。不增加 primitive／等距嵌入、直接 $AP$、共同参考指数、实际 $M_2$、任意仪器、物理时钟或 $\hbar$，不删除原已供应的标量两侧有序接口。$a,b$ 是原锥的数学元；其量词不新增实际准备、混合、操作或连线。

本轮简化是用原支持面和原比较球面的统一相切关系替代角度分层与另一份自比较规则，连谱比例也不进入表达。它的显式输入域扩大到全部正输入对；没有证明独立约束更少、有限认证、更低取得成本或前提最小性。下列单载体定理独立分类该统一关系，不以仅将旧条件合写作为新增内容。

## 372. 缩放给三形式，单位框架给正交零

**定理 372.1（正输入相切的全实代数后果）。** 设

$$
E=\bigoplus_sH_{n_s}(\mathbb C),\qquad
q(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s),\quad w_s>0,
\tag{372.1}
$$

$D:E\times E\to E$ 实双线性，满足 $D(a,u)=0$ 和对全部 $a,b\ge0$ 的 (371.2)。则对全部实输入

$$
\begin{gathered}
q(a,D(a,b))=q(b,D(a,b))=0,\\
T(a,b,c):=q(c,D(a,b))\in\Lambda^3E^*,\\
D(a,a)=0,\quad D(a,b)=-D(b,a),\quad D(u,a)=0,\quad
D_a^{\dagger_q}=-D_a.
\end{gathered}
\tag{372.2}
$$

此外，每个完整 $E$ 中的有序正交 primitive 对满足整个输出 $D(e,p)=0$；所有有序 primitive 对均满足 $D(e,p)\in E_1(\operatorname{supp}(e+p))$，因而恢复整个 $\mathsf O,\mathsf H$。

证明。先只用相切的标量部分。对固定正 $a,b$ 和每个 $t>0$，双线性给

$$
0=q(ta+b,D(ta,b))
=t^2q(a,D(a,b))+tq(b,D(a,b)).
\tag{372.3}
$$

两系数为零。它们分别是 $E\times E$ 上的实多项式；正定元对构成非空开集，所以两恒等式延伸到全部实输入，不要求负元被实际制备或操作。极化 $q(b,D(a,b))=0$ 得

$$
q(c,D(a,b))=-q(b,D(a,c)).
\tag{372.4}
$$

特别地，$q(b,D(a,a))=-q(a,D(a,b))=0$；$q$ 非退化使 $D(a,a)=0$。再极化给 $D$ 交替，故 $T$ 的前两槽交替，(372.4) 给后两槽交替，合为全交替三形式。右单位与交替给左单位。此时只得到斜伴随与 SC，尚未以此断言导子律。

任取正交 primitive $e,p$。若二者跨中心，支持部分使 $D(e,p)\in\mathbb Re\oplus\mathbb Rp$，与两输入的原 $q$ 正交使两个系数都为零。若二者同块，$E_1(e+p)$ 的 Hermitian 分解为

$$
E_1(e+p)=\mathbb Re\oplus\mathbb Rp\oplus V_{ep},\qquad
V_{ep}=\{v:e\circ v=p\circ v=v/2\}.
\tag{372.5}
$$

原 $q$ 为正 Frobenius 型，所以 (372.2) 消去两个对角分量，得 $D(e,p)\in V_{ep}$。把 $e=e_i$ 补为任意完整框架 $e_1,\ldots,e_N$。已证 SC 与原右单位使

$$
0=D(e_i,u)=\sum_{j\ne i}D(e_i,e_j),\qquad
D(e_i,e_j)\in V_{e_i e_j}.
\tag{372.6}
$$

跨中心项为零，同块不同 $j$ 的 Peirce 空间是直和：在该框架的矩阵坐标中分别只占 $(i,j)$ 与 $(j,i)$ 两位置。因此每项都为零。每个正交 primitive 对可补为这样的框架，故整个 $\mathsf O$ 成立。所有 primitive 本来为正，原支持入射直接给全部此类对的整支持，特别给 $\mathsf H$。没有只对角外分量求和，也没有把不同项的抵消当成逐项为零。∎

## 373. 不借实际参考的全部局部分类

**定理 373.1（任意经典、二阶及高阶块的精确分类）。** 对 (372.1) 的每个有限直和，右单位加全部正输入的 (371.2)，等价于存在任意实数 $\gamma_s$，使

$$
\boxed{\pi_sD(a,b)=\gamma_s\,\mathrm i[a_s,b_s]
\qquad(a,b\in E).}
\tag{373.1}
$$

经典块的输出为零；其 $\gamma_s$ 不承担可识别参数。各非经典块的 $\gamma_s$ 可独立且可为零，原 $w_s>0$ 不需相等。本定理不使用完整 $B_*$、实际联合、参考、交叉零、预设导子或共同尺度。

证明。372.1 已建立前卷定理 274.1 的准确前件：实双线性、原右单位、整个 $\mathsf O$ 和整个 $\mathsf H$。直接应用该已有单载体分类，不重证其正交双线性因式分解和三位置支撑刚性。它给所有经典与跨块输入零、无跨块输出、高阶块为 (373.1)，仅留下每个二阶块的

$$
D(a,b)_s=F_s\bigl(\mathrm i[a_s,b_s]\bigr),\qquad
F_s:H_2(\mathbb C)^0\to H_2(\mathbb C)
\text{ 实线性}.
\tag{373.2}
$$

这一步沿 274.1 的整个输出域和所有源块使用，未把不同来源提前删掉。

固定一个二阶块，写其单位为 $I$、无迹空间为 $V=H_2(\mathbb C)^0$。在该块取原 $T=q(\cdot,D(\cdot,\cdot))$。由 372.1 的交替、右单位和现有块局部性，$T$ 的任一槽为 $I$ 都为零，故它降为三实维 $V$ 上的三形式。$q(I,D(a,b))=0$ 同时使输出无迹。用标准 Pauli 基 $X,Y,Z$ 作纯证明坐标，$q(X,X)=q(Y,Y)=q(Z,Z)=2w_s$，两两正交。三形式空间为一维，记

$$
\theta_s=\frac{T(X,Y,Z)}{2w_s}.
\tag{373.3}
$$

则由与该正交基的全部配对唯一性，

$$
D(X,Y)=\theta_sZ,\quad
D(Y,Z)=\theta_sX,\quad
D(Z,X)=\theta_sY.
\tag{373.4}
$$

$\mathrm i[X,Y]=-2Z$ 及循环式使 $\gamma_s=-\theta_s/2$。单位输入为零，双线性遂在整个二阶块给 (373.1)。这是将 274.1 尚任意的内部 $F_s$ 限为标量的步骤，不用把数学二阶块命名为实际对象。成熟的三维交替形式与 Pauli 计算仅作这一步的中间工具。

反向，取任意 (373.1)。右单位直接成立。正 $a,b$ 满足 $\ker(a+b)=\ker a\cap\ker b$；若 $c=\operatorname{supp}(a+b)$，则每块 $a_s=c_sa_sc_s$、$b_s=c_sb_sc_s$，故交换子的整个输出在 $E_1(c)$。迹循环给

$$
q(a+b,D(a,b))
=\sum_sw_s\gamma_s\,\mathrm i\operatorname{Tr}\bigl((a_s+b_s)[a_s,b_s]\bigr)=0.
\tag{373.5}
$$

零和、奇异输入及不同中心均包括在内，所以 (371.2) 成立。∎

## 374. 同一原签名的全域恢复

**定理 374.1（统一相切候选与旧完整候选等价）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，

$$
\begin{aligned}
B_*+\mathsf F_{\rm fsph}^{>}
&\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm fsph}(B_*)
&\Longleftrightarrow\mathsf C_{\rm uneq}(B_*)
\Longleftrightarrow\mathsf C_{\rm self}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{374.1}
$$

同一原 $D$ 在全部对象的全部实输入上满足双单位、交替、Jordan 导子、原 $q$ 斜伴随、中心及跨块零输出；不重新定义推动。

证明。前卷 246.1 在各自准备背景给选中对象的静态复直和，原比较为正 Frobenius 型；原右单位独立供应。373.1 直接使每个选中对象的整个 $D$ 为逐块交换子，所以 SC 和完整 Jordan 导子缺陷都为零；没有借用 343.1 的两次实际参考正常形。

对任意原对象 $A$，沿 352.1 的原身份事件及完整 R，取实际充分大的 $J=AR$ 进入选中域。原含幺 Jordan/$D$ 单射 $i$ 给

$$
i(D^A(a,a))=D^J(i(a),i(a))=0,\qquad
 i(\Delta_A(a;b,c))=\Delta_J(i(a);i(b),i(c))=0,
\tag{374.2}
$$

其中 $\Delta$ 逐字取 (352.3)。单射性使两缺陷在原 $A$ 上为零；有限 EJA 导子内性给原指定 I。此处仍不运输 $q$，不要求原嵌入保 primitive、等距或 $q_J$ 因子化。零对象平凡。

反向，完整 $B_*+\mathrm I+\mathrm{SC}$ 直接消费前卷 275.2 在两份背景各自的准确入口，给全部原对象的逐块标量交换子和共同曲率，包含全零分支。373.1 的反向于是给全部原对象的正输入相切，特别给选中域。与既有候选的等价再用 360.1、361.1 及同一个原 $\sigma_{t_0}$。这也恢复被删去的整个 $\mathsf G_{0h}$ 和固定两原子自比较，而非只恢复一个兼容替代模型。∎

## 375. 固定原尺度及完整量子与过程消费者

**定理 375.1（同一推动、概率、事件和历史）。** 在唯一候选 (371.3) 中，全部 361.1 的原消费者逐字成立。特别地，先由原背景和 I+SC 取得共同 $\kappa\ge0$，再由同一原 $\sigma_{t_0}$ 取得 $\kappa=1$；在由原 $D$ 定向的坐标中有

$$
\begin{gathered}
\mathcal A_A=\bigoplus_sB(H_{A,s}),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\\
a\cdot b=a\circ b-\mathrm iD_ab,\quad D_ab=\tfrac{\mathrm i}{2}[a,b],\quad
[D_a,D_b]=-[L_a,L_b],\quad D_c^2=-P_c/4\ (c^2=c).
\end{gathered}
\tag{375.1}
$$

每个原准备的两套 Riesz 运输与原事件 $f:A\to B$ 的运输仍为

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&q_A(x,y)&=\tau_A((\mathcal W_Ax)y),\\
\rho_\alpha&=B_Ax_\alpha,&\widehat x_\alpha&=\mathcal W_A^{-1}\rho_\alpha,\\
\alpha(y)&=\tau_A(\rho_\alpha y),&
\alpha(D_ab)&=q_A(\widehat x_\alpha,D_ab),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}.
\end{aligned}
\tag{375.2}
$$

一般 $x_\alpha\ne\widehat x_\alpha$。原 $\tau_A(\rho_\alpha)=\alpha(u_A)$ 保留质量，不将零或次归一输入改成归一态；全部原相关准备均在其实际联合中运输。原不等正权与大小不同的中心保留，实际联合的全体中心对取得同一原取向的普通复张量。

全部原旧事件为 CP/TNI，原完整设备的事件和为 TP。整个 AC、精确 $N_u$、X/Xs 和原合法连线供应的每个原所选有限平方根词及原相关执行仍为

$$
\rho\longmapsto\sqrt e\rho\sqrt e,\qquad
X\longmapsto(\sqrt e\otimes I)X(\sqrt e\otimes I).
\tag{375.3}
$$

每个原占用方向 $p_1$ 的原失败 $\Psi_\ell$ 保留整个 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$；其余原方向、中心和端口仍为原映射，不以一个失败概率代替输出。原实 Jordan F 给同一实现的实际细口、原分组和遗忘；原具名非零细支及同数反向资料保留

$$
\begin{gathered}
S_\ell=\operatorname{Ad}_{K_\ell},\quad
\Phi_f=\sum_\ell S_\ell,\quad
U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+},\quad q_\ell>0,\\
e_\ell=\operatorname{supp}(K_\ell^*K_\ell),\quad
h_\ell=\operatorname{supp}(K_\ell K_\ell^*),\quad
\mathsf C_e(X)=eXe,\\
U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell},\quad
U_\ell S_\ell=q_\ell\mathsf C_{e_\ell},\quad
S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}.
\end{gathered}
\tag{375.4}
$$

原设备、端口、细记录和失败身份保持，$q_\ell$ 为原数，不另选成功率。对每份原准备、原末端效果 $w$ 和每条原合法有限历史，

$$
\alpha(T_{f_1}\cdots T_{f_r}w)
=\tau_{A_r}\!\left(w\,\Phi_{f_r}\cdots\Phi_{f_1}(\rho_\alpha)\right).
\tag{375.5}
$$

这包含原顺序、按实际记录自适应、实际并行联合、全部相关输入、细化／分组／实际遗忘、零／失败／返回／停止。仅对原分母为正的分支取条件概率。

证明。374.1 在原签名上恢复 361.1 的全部入口，故直接复用其完整对应。共同曲率不是 373.1 的局部结论：局部 $\gamma_s$ 可独立；前卷 275.2 消费完整原实际背景才给共同 $\kappa$，包括 $\kappa=0$。同一原 sigma 再以原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 强制 $\kappa=1$，未缩放原 $D$ 或重选 $t_0$。两份准备背景的入口分别按该前置成立；闭背景的正延拓只在同一已固定原执行上进行，不添加实际极限准备。全部式子随后沿 353.1、345.1、338.1，既有完整 tagged-CP 满足族也由反向蕴含满足新候选，含无实际 $M_2$ 的子族。∎

## 376. 只守一个几何分量或没有单位平衡时的局部后果

**定理 376.1（只有比较相切仍可跨出共同面）。** 右单位和全部正输入的 $q(a+b,D(a,b))=0$，即使加全实 SC 与斜伴随，也不单独强制 (371.2) 的支持部分。

证明。取 $E=\mathbb R^4$、原单位 $u=(1,1,1,1)$、标准点积，唯一地定义 $D$ 为

$$
q(c,D(a,b))=\det[u,a,b,c],
\tag{376.1}
$$

行列式中的四向量按列排列。它为实双线性，右单位因重复列为零；$T$ 全交替，故 $q(a+b,D(a,b))=0$、SC 和斜伴随对全部实输入成立。但

$$
D(e_1,e_2)=(0,0,-1,1)\notin E_1(e_1+e_2).
\tag{376.2}
$$

因此比较中性不能禁止输出逃往另外两个经典房间。此例仅为裸载体的局部区别，不供应完整 $B_*$、实际参考或同一原 sigma。∎

**定理 376.2（只有共同面仍可径向伸缩）。** 右单位和全部正输入的整支持条件不单独强制比较相切。

证明。取 $E=H_n(\mathbb C)$、$n\ge2$、$q=w\operatorname{Tr}$、$w>0$，置 $h=\operatorname{diag}(1,-1,0,\ldots,0)$，

$$
f(b)=\operatorname{Tr}(hb),\qquad D(a,b)=f(b)a.
\tag{376.3}
$$

$f(I)=0$ 给右单位；对正 $a,b$，$D(a,b)$ 的支持在 $a$ 的支持内，故整支持条件成立。取 $a=b=e_{11}$，则 $D(a,b)=e_{11}$、$q(a+b,D(a,b))=2w\ne0$。本例只分离几何条件的两个局部分量，不给完整原背景的独立性。∎

**定理 376.3（原右单位在裸二阶分类中确实承重）。** 不保留右单位时，全部正输入的统一相切关系仍可成立，而 (373.1) 失败。

证明。仅取数学 $H_2(\mathbb C)$，写 $a=a_0I+a_xX+a_yY+a_zZ$，$b$ 同样表示，$q=w\operatorname{Tr}$。定义

$$
\begin{aligned}
D(a,b)={}&(a_xb_y-a_yb_x)I\\
&+(a_yb_0-a_0b_y)X+(a_0b_x-a_xb_0)Y.
\end{aligned}
\tag{376.4}
$$

这是前三个实坐标 $(a_0,a_x,a_y)$ 的叉积，$Z$ 坐标为零；Pauli 基的原 $q$ 权均为 $2w$，故 $q(a+b,D(a,b))=0$ 对全部实输入成立。对正 $a,b$，若 $a+b$ 满秩则支持条件平凡；若其秩为一，则正性使 $a,b$ 为同一秩一投影的非负倍数，交替性使输出为零；零和也平凡。因此全部 (371.2) 成立。

但是 $D(X,I)=-Y\ne0$，且 $D(X,Y)=I$ 为非零中心输出，不是标量交换子。此例没有实际 $M_2$ 身份，也不删除完整 $B_*$ 已独立供应的右单位，只说明 372.6 与二阶三形式降维都不能凭空省去这项原供应。∎

## 377. 共同正面内的球面与三维角网

**定义 377.1（统一入射的准确几何）。** 对非零正 $x$、$c=\operatorname{supp}(x)$，定义原正面 $\mathcal F_c=C\cap E_1(c)$。$x$ 在该面的相对内部。面内的等长截面

$$
\mathcal S_x=\{y\in\operatorname{relint}\mathcal F_c:q(y,y)=q(x,x)\}
\tag{377.1}
$$

在 $x$ 处的切空间为 $\mathcal T_q(x)$：相对内部在 $E_1(c)$ 中开，平方长度的微分为 $2q(x,\cdot)$，且 $q(x,x)>0$。因此 (371.2) 的两个几何分量构成同一截面的切空间入射；不要求输出本身为正，也不把相切解释为实际可执行流。

**定义 377.2（三元相容与更大的结构）。** 两输入的关系输出再与第三元比较，得到原 $T(a,b,c)=q(c,D(a,b))$。372.1 把它锁为三形式；共同面的条件约束去处，整框架的单位平衡消去正交伙伴间的横向输出，已有三位置角网刚性再固定高阶内部形状。二阶块的单位方向被湮灭，三形式只剩三实维无迹空间上的体积方向，故局部也只剩一个交换子系数。

同块两颗不同 primitive 生成的数学 $H_2(\mathbb C)$ 支持角仍有三实维无迹截面；跨中心只得经典轴的直和，没有跨中心复相干方向。373.1 中二阶块的三实维计算、前卷 273.1 用于高阶拼接的第三个复支持位置和物理三维空间相互不同。完整原背景和同一 sigma 给出的较大结构仍为带经典中心的复 Jordan–Lie 网、逐块 $\mathbb{CP}^{n_s-1}$ 与相交的 Bloch/Peirce 角、实际有序联合中的普通复张量；原权不必等，不能把所有对象画成同一半径的球。

## 378. 来源、内生边界与完整白话

**定义 378.1（承重来源与准确新增内容）。** 仓内前置固定于 [`f2d0dcc67df99383eac5aabe2be977b762c7e18c`](https://github.com/the-omega-institute/trureturing/tree/f2d0dcc67df99383eac5aabe2be977b762c7e18c)。前卷 246.1 供应两份背景的静态复载体，274.1 供应尚容许二阶自由的全源局部分类，275.2 供应完整原背景下的共同尺度；本卷 352.1 供应只运输向量缺陷的实际参考回传，361.1 供应同一原刻度下的全部量子与过程对应。这些结果不重新立为公理。

完整谱框架与 Peirce 直和、有限维实多项式的开集恒等原理、交替三形式和 Pauli 代数均为成熟中间工具。274.1 的正交双线性因式分解及有限 EJA 内性仍只按前卷 280.1、本卷 326.1 所列 Haagerup–Laustsen 与 Tao–Gowda 的准确前件复用；这里没有借入全局共变、动力复合或保正流作为前提。母卷 41.7 的自旋三形式仅提供相邻图景，不以任意自旋维数的自由替代本条已固定的复二阶块。

本批 $\texttt{repo-derived}$ 综合为：正输入和的中性经缩放分出两个全实正交恒等式，共同面与原整框架单位将其变成整个正交零，再把 274.1 留下的二阶内部映射也由原三形式限制为标量，给不借实际参考的全有限复直和局部充要分类，以及 (376.1)–(376.4) 的准确局部边界。这是独立的局部分类桥，不仅是将两个旧条件合写。成熟中间结果不单列为新理论；不从文献未命中主张原创优先权。

具体原 $\Omega$ 内生满足完整 $B_*$、统一正面相切及同一原 sigma，仍须由其实际来源取得；条件等价没有把它们变成任意世界的定义真理。324.3 的三项来源义务分别保留：连续器件／物理时钟／Hamiltonian／共同作用量，独立成功支的共同完整仪器，旧同效果设备自己的完整输出校准。有限对象内的谱框架不使整个原世界成为有限菜单；含噪稳定、最小独立方程数、更低认证成本、物理空间维数及经验性量子起源均未由此得到。本文为纸笔条件数学，不宣称 Lean/kernel 或经验验证。

**定义 378.2（完整直观表述）。** 白话说，整座原世界连同经典房间、大小不同的量子街区、原比较尺、全部真实联合与相关准备、每台设备和细记录、完整失败出口、原分组和遗忘、带同一个原成功数的两侧返回以及每条合法有限历史，仍整座保留。新规则只画一幅图：拿两个原锥里的数学正元，把它们相加，找到刚好容得下它们的共同房间，再经过这个和画一张原比较球面；两者的关系输出必须留在这个房间里，同时贴着这张球面走。把一个输入放大，仍是同一条规则，于是输出分别与两个输入都正交，第三个比较读回便组成全交替的关系。两颗珠子完全错开时，可能的横向输出各占框架里不同的位置，原右单位要求它们合起来为零，便使每个位置单独归零。大块沿已有三位置拼接锁成交换子，二阶小屋里单位方向被消掉，三实维体积关系也只留下一个转动系数；这一步在单个数学载体就完成，无须新造实际量子比特。原真实参考再把向量和乘法关系带回所有旧对象，完整原背景把各处尺度接成同一个数，最后仍用那张原刻度单把它固定为一。于是复乘法、Born 概率的两套正确运输、实际张量、原全部事件与平方根词、完整失败、细记录、同数双返回及所有原合法历史都接回来。少了房间边界，输出能跑到别的经典房间；少了球面相切，输出能沿原元伸缩；裸小屋里少了单位平衡，还能把转动送到单位方向。这里简洁的是统一几何表达，检查域已扩大，没有宣称成本更小；这幅三实维角网也不自动产生物理三维空间、真实时钟或作用量。具体世界为什么从自身满足这条关系，仍要继续从它的实际来源证明。

## 追加锚 C128378（本行以下为增补区）

## 379. 只在原子方向上要求同一面球相切

**定义 379.1（原子对的统一关系与唯一完整候选）。** 分别固定 371.1–371.2 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$。同一原 $\Omega,q,D,L,\circ$、原菜单、预选 $t_0$ 和同一原 $\sigma_{t_0}$ 保持。$\operatorname{Prim}(E)$ 表示原 Jordan 代数的非零不可分幂等元集合，不可分意为不能拆成两个非零正交幂等元之和；这是由原乘法和单位定义的整个数学集合，不是一份所选框架，也不赋予其实际准备或操作身份。

对每个原选中对象 $\operatorname{rank}E_X>p_*$，只要求

$$
\boxed{\mathsf F_{\rm prph}^{>}:\quad
D^X(e,p)\in E_1(c)\cap\{v:q_X(e+p,v)=0\},\quad
c=\operatorname{supp}(e+p),\quad
(e,p)\in\operatorname{Prim}(E_X)^2.}
\tag{379.1}
$$

这里 $E_1(c)=Q_cE_X$、$Q_c=2L_c^2-L_c$，管整个支持面。量词包含 $e=p$、全部有序跨中心对及实际联合中的全部数学 primitive。唯一完整候选是

$$
\boxed{\mathsf C_{\rm prph}(B_*)
:=B_*+\mathsf F_{\rm prph}^{>}+\sigma_{t_0}.}
\tag{379.2}
$$

$\mathsf F_{\rm fsph}^{>}$、$\mathsf G_{0h}$ 及固定谱权重的自比较不另列为输入。原右单位 $D(a,u)=0$ 仍由完整背景的母卷 30.1／67.3 独立供应。新增关系本身不选择框架、重叠角、谱比、中心迹或匹配资料；完整候选仍保留原 sigma 所用的菜单与预选 primitive、半重叠标签。

**定义 379.2（完整范围与简化口径）。** 371.2 的全部原范围保留：所有中心、经典块、大小不同的量子块及原不等正权；全部实际有序联合、全部原乘积和相关准备、零与次归一质量；整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F；原设备／端口／细记录／失败身份、完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料，以及每条原合法有限顺序、自适应和并行历史。两份背景分别保持自身的精确有限正生成和闭正生成。

这里的简化是将 371.2 的全部正元对测试域收回到内在原子方向，公式的两个几何分量不变；不再把任意正比例、正和或谱权重放入新增关系的输入域。原子集合一般仍无限，整个原世界也未要求有限。没有独立方程数最少、有限认证或取得成本更低的结论。LU、SC、交替、斜伴随、导子律、理想保持和模身份都不是新增前提；不增加 primitive／等距嵌入、直接 $AP$、共同参考指数、实际 $M_2$、任意仪器、物理时钟或 $\hbar$。原已供应的标量两侧有序接口保持其全部前件。

## 380. 自对与整框架先恢复整个正交零

**定理 380.1（不放大原子输入的框架推论）。** 设

$$
E=\bigoplus_sH_{n_s}(\mathbb C),\qquad
q(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s),\quad w_s>0,
\tag{380.1}
$$

实双线性 $D:E\times E\to E$ 满足右单位及全部原子对的 (379.1)。则每个 primitive 有 $D(e,e)=0$，每个完整 $E$ 中的有序正交 primitive 对有整个输出 $D(e,p)=0$；全部半重叠 primitive 对满足整支持。因此前卷 274.1 的全部 $\mathsf O,\mathsf H$ 成立。

证明。$e=p$ 时，支持空间是 $\mathbb Re$，故 $D(e,e)=\lambda_e e$。相切给 $0=q(2e,\lambda_e e)=2\lambda_eq(e,e)$，原正权使 $\lambda_e=0$。这一步只在原子输入上取值，没有将 $te$ 当成另一颗原子。

固定完整谱框架 $e_1,\ldots,e_N$，任取 $i\ne j$。记 $w_i=q(e_i,e_i)>0$。原子对的整个支持使

$$
D(e_i,e_j)=\alpha_{ij}e_i+\beta_{ij}e_j+v_{ij},\qquad
v_{ij}\in V_{ij},\qquad
w_i\alpha_{ij}+w_j\beta_{ij}=0.
\tag{380.2}
$$

同块时 $V_{ij}$ 是只占矩阵位置 $(i,j),(j,i)$ 的 Peirce 空间；跨中心时 $V_{ij}=\{0\}$。各块的原 Frobenius 权可不同，相切仍恰给最后一个加权式。原右单位及已证的自对零给

$$
0=D(e_i,u)=\sum_{j\ne i}
\bigl(\alpha_{ij}e_i+\beta_{ij}e_j+v_{ij}\bigr).
\tag{380.3}
$$

对固定 $j\ne i$，沿 $e_j$ 的对角系数在和式中只出现一次，故 $\beta_{ij}=0$。不同 $j$ 的 $V_{ij}$ 也是独立直和，故各 $v_{ij}=0$。再由 (380.2) 的原加权关系得每个 $\alpha_{ij}=0$；没有把共有的 $e_i$ 系数之和为零误作逐项为零。

任意正交 primitive 对可补入这样的完整框架，所以整个 $\mathsf O$ 成立。全部半重叠对本来包含在 (379.1) 的支持量词中，故整个 $\mathsf H$ 成立。此时才可使用 274.1；不先假定一般输入的 SC、交替或 $q$ 斜伴随。∎

## 381. 补元成对读回的三维刚性

**定理 381.1（二阶内部映射的半角充分条件）。** 在数学 $H_2(\mathbb C)$ 中，令 $V=H_2(\mathbb C)^0$、$q=w\operatorname{Tr}$、$w>0$。对任意实线性 $F:V\to H_2(\mathbb C)$，以下等价：

$$
\begin{aligned}
&q\bigl(e+p,F(\mathrm i[e,p])\bigr)=0
\quad(e,p\in\operatorname{Prim}(H_2),\ \operatorname{Tr}(ep)=\tfrac12);\\
&\exists\gamma\in\mathbb R,\quad F(v)=\gamma v
\quad(v\in V).
\end{aligned}
\tag{381.1}
$$

这里的半角只限定本条局部引理的充分测试族；(379.1) 本身遍历全部原子对，不选择这个角度。

证明。用 Pauli 坐标 $\sigma=(X,Y,Z)$，写

$$
e=\tfrac12(I+r\cdot\sigma),\quad
p=\tfrac12(I+s\cdot\sigma),\quad
|r|=|s|=1,\quad r\cdot s=0,
\qquad \mathrm i[e,p]=-\tfrac12(r\times s)\cdot\sigma.
\tag{381.2}
$$

一般实线性 $F$ 唯一写成 $F(v\cdot\sigma)=f(v)I+(Av)\cdot\sigma$，其中 $f$ 为实线性泛函，$A$ 为实线性算子。置 $v=r\times s$、$h=r+s$；$\operatorname{Tr}(\sigma_j\sigma_k)=2\delta_{jk}$ 给

$$
q\bigl(e+p,F(\mathrm i[e,p])\bigr)
=-\frac w2\{2f(v)+h\cdot Av\}.
\tag{381.3}
$$

补元 $I-e,I-p$ 也是半重叠 primitive；其 Bloch 方向为 $-r,-s$，叉积仍为 $v$，和方向变为 $-h$。两条读回遂分别给 $2f(v)+h\cdot Av=0$ 与 $2f(v)-h\cdot Av=0$，因此

$$
f(v)=0,\qquad h\cdot Av=0.
\tag{381.4}
$$

给定任意单位 $v$ 及任意单位 $z\perp v$，置 $k=z\times v$、$r=(z+k)/\sqrt2$、$s=(z-k)/\sqrt2$。它们是正交单位向量，且 $r\times s=v$、$r+s=\sqrt2z$。故 (381.4) 对全部单位 $v$ 及全部 $z\perp v$ 成立。实线性使 $f=0$，而 $Av\in\mathbb Rv$ 对每个 $v$ 成立。

取正交基 $v_1,v_2,v_3$，写 $Av_j=\gamma_jv_j$。再用 $v_j+v_k$ 的直线保持性得 $\gamma_j=\gamma_k$，于是 $A=\gamma\operatorname{Id}$。这只是三实维线性代数在原补元读回中的应用，不假设三形式、旋转共变或任何实际流。反向，标量交换子的迹循环直接给第一式。∎

## 382. 原子测试恢复全部正输入的裸局部分类

**定理 382.1（全部有限复直和上的原子充分性）。** 对每个 (380.1) 的有限载体和每个实双线性 $D$，以下三项等价：

$$
\begin{aligned}
& D(a,u)=0\text{ 且全部原子对满足 (379.1)};\\
&\exists(\gamma_s)_s\in\mathbb R^{S},\quad
\pi_sD(a,b)=\gamma_s\mathrm i[a_s,b_s]
\quad(a,b\in E);\\
& D(a,u)=0\text{ 且全部正输入对满足 (371.2)}.
\end{aligned}
\tag{382.1}
$$

所有经典块、二阶块、高阶块及不等正权均包括在内。各非经典块的实系数可以独立且可以为零；经典块的输出为零，其系数不承担可识别参数。本条不使用完整 $B_*$、实际联合、实际参考、交叉零、共同尺度或预设导子。

证明。由 380.1 得右单位、整个 $\mathsf O,\mathsf H$。精确应用前卷 274.1 的全源、全输出分类，直接得到经典及所有跨块输入零、没有跨块输出、高阶块为所需标量交换子；二阶块只留下

$$
\pi_sD(a,b)=F_s(\mathrm i[a_s,b_s]),\qquad
F_s:H_2(\mathbb C)^0\longrightarrow H_2(\mathbb C).
\tag{382.2}
$$

没有重证该已有分类，也没有先删除其允许的二阶中央输出。原子对相切的限制在每个二阶块给 381.1 的准确前件，所以每个 $F_s=\gamma_s\operatorname{Id}$。所用补元是这个数学二阶块内的补元；它不需要是实际对象，不把大块的 $I-e$ 错当 primitive。

标量正常形与全部正输入相切的等价直接复用 373.1，包含零和、奇异正元、不同中心及任意原正权。全部正输入当然包含全部 primitive，因此闭合三向等价。空载体结论平凡。整个推导没有在 primitive 集合上调用开集多项式延拓，也没有把原子缩放或相加后仍当作原子。∎

## 383. 同一原签名上的全域等价

**定理 383.1（原子相切与完整量子候选）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，

$$
\begin{aligned}
B_*+\mathsf F_{\rm prph}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm fsph}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm prph}(B_*)
&\Longleftrightarrow\mathsf C_{\rm fsph}(B_*)
\Longleftrightarrow\mathsf C_{\rm uneq}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{383.1}
$$

对应在全部原数据及全部原合法有限历史上为恒等，不重新定义原 $D$ 或原比较。

证明。前卷 246.1 分别在两份完整准备背景中供应原静态复直和，原比较是各块正 Frobenius 型；原右单位由母卷 30.1／67.3 独立供应。故 382.1 在每个原选中对象上将原子相切等价地恢复为全部正输入相切。这里无需假设任一原嵌入保持 primitive，也未将某个数学角增补为实际对象。

随后完整消费 374.1：对任意原对象，用原身份事件及全事件 R 供应的充分大实际参考联合。原含幺 Jordan/$D$ 单射将 SC 与整个 Jordan 导子缺陷逐字运输，单射性将其带回原对象；运输对象是向量和两种乘法，不是 $q$。零对象也包括在内。原 I 的取得仍用该既有前件中的有限 EJA 内性。反向，374.1 已在完整 $B_*+\mathrm I+\mathrm{SC}$ 上取得全部正输入相切，限制到原子即可。

共同尺度仍只由前卷 275.2 消费完整背景取得，包含 $\kappa=0$；局部 382.1 并未要求各 $\gamma_s$ 同步。加入同一字面 $\sigma_{t_0}$ 后，375.1 以原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 固定 $\kappa=1$。与既有完整候选的其余对应直接复用 374.1、361.1 及 276.2。既有完整 tagged-CP 满足族由反向蕴含满足本候选，含无实际 $M_2$ 对象的子族。两份背景始终分别应用，没有将它们合取为一个更强前提。∎

## 384. 同一刻度下的量子、事件与全部历史

**定理 384.1（原消费者的准确前件对应）。** 在 (379.2) 中，375.1 的完整消费者适用于同一原结构。其原前件与结论的对应如下：

| 由原背景与 383.1 取得的关系 | 同一原结构上的结论 |
| --- | --- |
| 原 I+SC、同一 sigma、原 Jordan 乘法与同一 $D$ | $\mathcal A_A=\bigoplus_sB(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$，$C_A=(\mathcal A_A)_+$；$a\cdot b=a\circ b-\mathrm iD_ab$，$D_ab=\mathrm i[a,b]/2$，$[D_a,D_b]=-[L_a,L_b]$，每个幂等元满足 $D_c^2=-P_c/4$。 |
| 全部原准备、原 $g^0$、原不等正权 $q$ | $\rho_\alpha=B_Ax_\alpha$，$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$；$\tau_A(\rho_\alpha)=\alpha(u_A)$，包含零、奇异与次归一质量。 |
| 原 X、同一 $D$ 保持、有序交叉零、乘积张成及实际乘积准备分离 | 每个原实际联合为保留全部中心对的同取向普通复张量，全部原相关输入包括在内；不要求联合 $q$ 或 $B_A$ 因子化。 |
| 每个旧事件的完整 R、同设备同记录旁接、全部原相关正锥、次幺性与完整效果和 | $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为原事件的 CP/TNI 运输，原完整设备事件和为 TP。$\dagger_0$ 是原 $g^0$ 伴随，$B_A$ 是比较运输，不是背景符号 $B_*$。 |
| 整个 AC、精确 $N_u$、X/Xs、原所选平方根词及其原相关执行 | $\rho\mapsto\sqrt e\rho\sqrt e$ 及 $X\mapsto(\sqrt e\otimes I)X(\sqrt e\otimes I)$；每个原占用失败方向的整个输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其余原方向、中心与端口仍按原失败映射取完整输出。 |
| 实 Jordan F、同实现实际细记录、原分组／遗忘、具名同数双返回与反向资料 | $S_\ell=\operatorname{Ad}_{K_\ell}$，$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$，$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$，$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；原 $q_\ell>0$ 不归一，全部零标签、失败及原反向资料保留。 |
| 全部原准备、末端效果和每条原合法有限历史 | $\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$，覆盖空历史、顺序、按实际记录自适应、已供并行联合、细化／分组／实际遗忘、零／失败／返回／停止。只在原分母为正时取条件概率。 |

这里 $P_c=4(L_c-L_c^2)$，而 $\mathsf C_e(X)=eXe$；二者均不替代 (379.1) 的整支持投影 $Q_c$。全部原设备、端口、细记录与失败身份保持，不将数学 Kraus 分解变成实际记录，不以同效果替换旧设备自己的完整输出。

证明。383.1 已在各自同一背景中取得 375.1 的全部入口。逐项应用该定理及其原 353.1、361.1 消费者即得表中对应；无须重新证明状态、张量或过程重构。闭背景的正延拓只在同一已固定原执行上进行，不把数学极限准备增补为实际准备。整个表使用的是完整原事件、原标量与原历史，原子测试的数学量词没有新增任何物理资源。∎

## 385. 删除自对会漏掉孤立经典方向

**定理 385.1（全部不同原子对仍有局部盲方向）。** 在具有经典中心的裸载体上，即使保留右单位，只对所有 $e\ne p$ 的有序 primitive 对要求 (379.1)，也不强制 382.1 的正常形。

证明。取 $E=\mathbb R^3$、逐坐标 Jordan 乘法、标准点积、$u=(1,1,1)$，记标准 primitive 为 $e_1,e_2,e_3$，置

$$
v=e_1-e_2,\qquad
D(a,b)=a_1(b_2-b_1)v.
\tag{385.1}
$$

这是实双线性映射，$D(a,u)=0$。在全部有序不同 primitive 对中，唯一非零输出是 $D(e_1,e_2)=v$，它在 $E_1(e_1+e_2)$ 中且 $q(e_1+e_2,v)=0$；其余输出均为零。因此删去自对后的全部测试都成立。但

$$
D(e_1,e_1)=-e_1+e_2\notin\mathbb Re_1,
\tag{385.2}
$$

并非经典块应有的零映射。此例不具有完整 $B_*$、实际参考或原 sigma，只分离裸原子测试的局部条件。

本例的经典原子集合是离散的，不能通过取不同原子趋近同一原子填补自对；整个候选包含经典中心，因此不能依赖非经典方向的连续图景删去 $e=p$。∎

## 386. 原子关系、补元读回与三维角网

**定义 386.1（原子域中的共同面与原比较球面）。** 对原子对置 $x=e+p$、$c=\operatorname{supp}(x)$。$x$ 在原正面 $\mathcal F_c$ 的相对内部；377.1 已给

$$
T_x\{y\in\operatorname{relint}\mathcal F_c:
q(y,y)=q(x,x)\}
=E_1(c)\cap x^{\perp_q}.
\tag{386.1}
$$

因此 (379.1) 仍是整个共同面内的原比较球面相切，只将被检查的输入回到原子。原子在非经典块中另组成 $\mathbb{CP}^{n_s-1}$；该原子空间与通过 $e+p$ 的面内球面并不是同一个曲面。不同中心的原权不必相同，不能将所有原子或所有原子和画在同一半径上。

**定义 386.2（补元配对所约束的关系之关系）。** 在数学二阶块内，$(e,p)$ 与 $(I-e,I-p)$ 给同一个交换子输入，而和读回方向分别为 $I+(r+s)\cdot\sigma/2$ 与 $I-(r+s)\cdot\sigma/2$。两条读回的共同部分消去输出的单位方向，相反部分使剩下的线性输出垂直于叉积方向的全部横向探针。381.1 因而将内部映射限为同一条叉积方向上的标量，不需要先给输出三形式、旋转对称或实际时间。

高阶块的支撑角仍沿前卷 273.1 的三复位置拼接刚性相容；二阶块此处使用的是三实维无迹空间，两种“三”不同。较大结构由 383.1、384.1 取得带经典中心的复 Jordan–Lie 网、相交的 Bloch/Peirce 角和原实际有序联合的普通复张量。该结构不独自规定物理空间维数、时钟或共同作用量。

## 387. 来源、内生边界与完整白话

**定义 387.1（来源与新增综合的范围）。** 仓内前置固定于 [`50af3c7111e85c1112ee9dbc6e721adbb759a26b`](https://github.com/the-omega-institute/trureturing/tree/50af3c7111e85c1112ee9dbc6e721adbb759a26b)。前卷 246.1 供应两份完整背景的原静态载体，274.1 供应保留二阶自由的全源、全输出分类；本卷 373.1 供应标量正常形与全部正输入相切的等价，374.1 供应不运输 $q$ 的原实际参考下降，375.1 供应完整量子与过程消费者。其成熟正交双线性因式分解与有限 EJA 内性仍沿前卷 280.1、本卷 326.1 所列 Haagerup–Laustsen 与 Tao–Gowda 的准确前件复用。

完整谱框架、Peirce 直和、Pauli 坐标、补元及实线性直线保持刚性均为成熟中间工具。这里的 $\texttt{repo-derived}$ 综合是：原子自对与原单位框架恢复整个正交零，再在尚任意的二阶内部映射上用补元成对读回消去中央与横向自由，从而不借实际参考就在全部有限复直和上将原子相切等价地提升为全部正输入相切，并给出 (385.1) 的经典自对删除边界。成熟工具只承担此新推导的中间步骤，不以文献未命中主张历史优先权。376.1–376.3 的支持、中性与右单位删除见证也已适用于原子限制，按原结果直接复用，不重新立为新增分类。

具体原 $\Omega$ 仍须由其实际来源满足完整 $B_*$、原子相切和同一原 sigma；条件等价不把这些关系宣布为任意世界的定义真理。324.3 的三项来源义务分别保持：物理时钟／Hamiltonian／共同作用量，独立成功支的共同完整仪器，旧同效果设备自己的完整输出校准。含噪稳定、最少独立约束、有限认证、最低取得成本和物理空间维数均不由本候选的条件理论给出。

**定义 387.2（完整直观表述）。** 白话说，整座原世界仍在：经典房间、大小不同的量子街区、各自原比较尺、全部真实联合与相关准备、每台设备和细记录、完整失败出口、实际分组与遗忘、带同一个原成功数的两侧返回以及每条合法有限历史，都完整保留。新规则把上一幅面球图收回到最细的珠子：只拿两颗原子，也包含同一颗和自己，把它们的和放在刚好容得下它们的共同房间里，关系输出必须留在房间内，同时贴着经过这个和的原比较球面。珠子问自己时只剩一条轴，相切便使自推动归零；把一整框架相加，原单位要求总推动为零，不同位置的箭头与每个独占的对角读数一起，把完全错开的伙伴输出逐个消掉。大块于是沿已有三位置拼接锁成交换子，小二阶房间则把两颗珠子换成各自的补珠：关系输入相同，两个和的横向方向相反，两次读回先去掉输出的单位方向，再在三实维球图中把剩余自由压到叉积方向上的一个系数。这一步只在数学载体内完成，不另造实际量子比特；其结果反过来保证任意正元对也满足原来的面球关系。原真实参考再将向量和乘法关系带回所有旧对象，完整背景将尺度接成同一个数，同一张原刻度单最后固定为一，复乘法、Born 的两套正确运输、实际张量、全部旧事件、精确平方根词和完整失败、细记录、同数双返回及所有原合法历史便一起接回。只查两颗不同珠子会漏掉孤立经典房间的自推动，所以经典自对不能凭量子球面的连续图景删去。这里简化的是输入回到原子方向，原子族仍可无限，也没有宣称认证更便宜；三实维角网不自动产生物理三维、真实时钟或作用量。具体世界为何从自身满足这条更小的关系，仍须由它自己的来源继续证明。

## 追加锚 C128387（本行以下为增补区）

## 388. 附录：固定半权主表述的逐对谱比稳健性

**定义 388.1（每对自己的一个共同根）。** 固定 358.1–358.2 的完整原签名。分别取完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$；前者保持每个所需原对象及实际联合的实际准备精确有限正生成，后者保持各自的闭正生成，不互换两者，也不将数学极限准备增加为实际准备。置

$$
\begin{gathered}
P_X(a):=q_X(a,D^X(a,a)),\qquad p_*=\operatorname{rank}E_P\ge2,\\
\mathsf T_{\exists\mathrm{ratio}}^{>}:\quad
\forall X,\quad\operatorname{rank}E_X>p_*\ \Longrightarrow\\
\forall\{e,p\}\subset\operatorname{Prim}(E_X),\quad e\perp p\ \Longrightarrow
\exists\lambda=\lambda_{X,\{e,p\},D}\in(0,1):\\
\boxed{P_X(e+\lambda p)=P_X(p+\lambda e)=0.}
\end{gathered}
\tag{388.1}
$$

这里每个无序对由两颗不同 primitive 组成，同一对的两个换位效果必须共用该 $\lambda$。不同对象、不同对可取不同值，允许依赖原 $D$；不先选共同值，不要求统一端点余量、连续性、可测性或其他正则性。不另查 $P_X(e)$、$P_X(u_X)$，也不加入 primitive 或单位的向量自测试。两个混合输入都是原数学效果 $0\le e+\lambda p,p+\lambda e\le u_X$；它们不是由此新增的实际准备、混合程序、控制或仪器。$\lambda$ 是正交谱方向的权重比，不是 $\mathsf G_{0h}$ 的重叠半值。

整个原 $\Omega$ 及字面 $D,q,L,\circ$ 保持；完整 $\mathsf G_{0h}$ 仍逐字取 (319.1)：在原选中对象整个空间的全部有序 primitive 对上，零／半重叠时的整个输出均留在 $E_1(\operatorname{supp}(e+p))$，两个输入次序都保留，包括跨中心和实际联合中的纠缠 primitive。全部经典中心、不等量子块及原不等正权、实际有序联合、全部实际准备及其零／次归一质量、全部乘积和相关输入均沿 358.2 保留。整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、每个旧设备／端口／细记录／失败身份及完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回和同数反向资料，以及每条原合法有限顺序、自适应和并行历史保持原量词。原菜单、$\mathcal K$、预选 $t_0$ 与字面 $\sigma_{t_0}$ 均不变。

LU、SC、交替、导子、斜伴随、naturality、原理想保持、模身份和反向交叉零均不作为新增前提；不添 primitive／等距嵌入、实际 $M_2$、直接 $AP$、共同参考指数、物理时钟／作用量或共同仪器与控制供应。原有的标量两侧有序接口仍完整保留。以下仅是固定半权主表述 358.1 的精确稳健性引理。

**引理 388.2（逐对存在谱比的完整条件等价）。** 分别在上述完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，同一原数据上有

$$
\begin{aligned}
B_*+\mathsf G_{0h}+\mathsf T_{\exists\mathrm{ratio}}^{>}
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf T_{\rm uneq}^{>}\\
&\Longleftrightarrow B_*+\mathsf G_{0h}+\mathsf T_{\rm self}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC}.
\end{aligned}
\tag{388.2}
$$

因而这些前件还使每个原对象的全部实输入满足 $D^X(a,a)=0$，特别是每对的两个读数对所有 $\lambda\in(0,1)$ 都为零。加入同一原 $\sigma_{t_0}$ 后，记左端完整条件为 $\mathsf C_{\exists\mathrm{ratio}}(B_*)$，则

$$
\mathsf C_{\exists\mathrm{ratio}}(B_*)
\Longleftrightarrow\mathsf C_{\rm uneq}(B_*)
\Longleftrightarrow\mathsf C_{\rm self}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*),
\tag{388.3}
$$

361.1 的全部量子与过程消费者遂在同一原签名上适用，所有对应均为恒等。

证明。新的方向只须在每个原选中对象中消掉径向泛函。完整 $B_*+\mathsf G_{0h}$ 已供应 343.1 的全源、全输出正常形以及 351.1 的原正权型，故直接沿用

$$
P_X(a)=\sum_sw_s\operatorname{Tr}(a_s^2)F_s(a),\qquad
F_s(u_X)=0,\qquad w_s>0.
\tag{388.4}
$$

这里的 $F_s$ 作用于整个 $E_X$，包含全部经典、二阶与跨中心来源；没有重新分类或预设其为零。任取完整 Jordan 框架 $e_1,\ldots,e_N$，$\sum_ie_i=u_X$，$N=\operatorname{rank}E_X>p_*\ge2$。沿用 359.1 的证明坐标 $A_{ij}=w_{s(i)}F_{s(i)}(e_j)$、$d_i=A_{ii}$、$S=\sum_i d_i$，原右单位给每行 $\sum_jA_{ij}=0$。对这个有限框架的每个无序对选取 (388.1) 的一个见证 $\lambda_{ij}=\lambda_{ji}$；这只是有限次存在消去，不要求全网一致的选择。

精确应用 (359.5) 的同块／跨块统一展开，两个共同根方程为

$$
\begin{aligned}
0&=d_i+\lambda_{ij}A_{ij}+\lambda_{ij}^2A_{ji}+\lambda_{ij}^3d_j,\\
0&=d_j+\lambda_{ij}A_{ji}+\lambda_{ij}^2A_{ij}+\lambda_{ij}^3d_i.
\end{aligned}
\tag{388.5}
$$

同块时仍有 $A_{ij}=d_j$、$A_{ji}=d_i$，所以该式没有把同块原子误当独立中心。因 $0<\lambda_{ij}<1$，这对方程的 $A_{ij},A_{ji}$ 系数行列式为 $\lambda_{ij}^2(1-\lambda_{ij}^2)>0$，消元恰给

$$
\begin{gathered}
A_{ij}=d_j-c_{ij}d_i,\qquad
A_{ji}=d_i-c_{ij}d_j,\\
c_{ij}:=\lambda_{ij}+\lambda_{ij}^{-1}
=c_{ji}>2,\qquad
k_i:=\sum_{j\ne i}c_{ij}>2(N-1),\\
0=\sum_jA_{ij}=S-k_id_i.
\end{gathered}
\tag{388.6}
$$

各 $c_{ij}$、各 $k_i$ 不必相同。设 $M=\max_i|d_i|$；若 $M>0$，在取到最大值的行 $i$ 上，(388.6) 使

$$
|S|=k_iM>2(N-1)M\ge NM,
\qquad |S|\le\sum_j|d_j|\le NM,
\tag{388.7}
$$

矛盾。因此全部 $d_i=0$，再由 (388.6) 得全部 $A_{ij}=0$。这是有限矩阵严格对角占优的最大分量论证，不需要对 $\lambda_{ij}$ 作共同取值或极限处理。任意完整实输入 $b$ 都有自己的完整谱框架 $b=\sum_j\beta_je_j$；对每个目标中心 $s$，取该框架内属于 $s$ 的一颗 $e_i$，即得 $w_sF_s(e_j)=A_{ij}=0$ 对全部 $j$ 成立。正权与线性性给 $F_s(b)=0$。所以每个全源 $F_s=0$，所选对象上恢复整个逐块交换子和 $\mathsf T_{\rm self}^{>}$。

现在直接应用 360.1，得到 (388.2) 的全原域结论。其下降仍消费 352.1、343.1 的原身份事件、完整 R 与实际充分大参考，以及原含幺 Jordan／同一 $D$ 单射：沿单射运输 SC 和整个 Jordan 导子缺陷，不运输 $q$，不假设 primitive 保持或共同参考指数；有限 EJA 内性在原条件下给 I。故所有小对象、经典中心、二阶块、原输出与零对象均由既有全域桥覆盖。反向 $\mathsf T_{\rm uneq}^{>}$ 直接以每对 $\lambda=1/2$ 供应 (388.1)，其与其余条件的等价已由 360.1 给出。两份背景各自应用这些定理，不把精确正生成与闭正生成合取。

对 (388.3) 直接消费 361.1、353.1 及其原消费者。先在完整背景和全域 I+SC 下取得含零分支的共同曲率 $\kappa\ge0$，再由原菜单、$\mathcal K$、$t_0$ 和同一字面 sigma 以原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 固定 $\kappa=1$，不重标 $D,q$ 或任何返回数。因此原 $D$ 定向的复乘法与 Jordan–Lie 关系、两种正确 Riesz 运输及 Born 评价、保留全部中心对的实际普通复张量和所有相关输入，均按 (361.2)–(361.3) 保持。每个旧事件的完整 R 及原相关正锥给原 CP/TNI、完整设备事件和 TP；整个 AC、精确 $N_u$、X/Xs 与原合法连线给原所选精确平方根词及其全部相关执行、各占用失败方向的完整输出，实 Jordan F 则给同实现实际细口、原分组／遗忘、原具名同数两侧支持返回及同数反向资料。全部原准备、末端效果和原合法有限顺序／自适应／并行历史沿 (361.4)–(361.6) 保持；零、失败、返回和停止不删，只在原分母正时取条件概率。闭背景仍只对同一已固定原执行作连续正延拓。没有把数学效果、Kraus 分解或极限密度当作新供应的实际接口。

完整非空满足族直接取 361.1、347.1、325.1 所引用的[框架卷 317.1](AURIC_C128_FRAME_CORNER_RELATIONS_CONTINUATION.md#317-非空完整满足族与准确角几何) 的全部 tagged-CP 族：任意原正定比较参数 $r_s$、不等正 $w_s$、不同块大小及经典中心、全部归一／次归一／零密度及联合纠缠密度、带原实现和记录标签的完整 CP 仪器及已安装细口、完整失败、原具名返回和全部合法有限历史均保留，原 $g^0$ 与 $q$ 及联合权不必因子化或相等。其同一 $D=\mathrm i[a,b]/2$ 使全部自输入为零，故直接满足 (388.1)，无需另造模型；原 $P=\mathbb C\oplus M_3$、无实际 $M_2$ 对象或简单块的子族亦保留。∎

**定义 388.3（反事实、二元关系与既有几何）。** 在同一完整 $B_*+\mathsf G_{0h}$ 域内，否定 (388.1) 的精确反事实是：存在一个原选中 $X$ 及一个正交无序对，使每个 $\lambda\in(0,1)$ 都至少有一个换位读数非零；由 (388.2)，这恰等价于全原域 I+SC 不成立。它不声称两个读数在每个比例都同时非零。更局部地，在 (388.4) 的正常形与原右单位层，若有非零径向泛函，就必有这样的成对障碍：否则上述有限框架论证会消掉所有泛函。已发表 (347.2) 的经典循环片段便给 $P(e_1+\lambda e_2)=\lambda(1-\lambda)$、$P(e_2+\lambda e_1)=-\lambda(1-\lambda)$，全部内点被检出而端点等权会相抵；该片段没有完整 $B_*$、实际参考和同一 sigma，仍不是全背景反模型。反过来，(362.1) 的裸右单位片段在所有至多两原子支持上都使 $P=0$，故甚至通过所有谱比，却仍违反整支持及全部效果中性。因而本引理不取得不带完整背景的独立局部分类，也不能删除 $\mathsf G_{0h}$。

被约束的仍是原二元实双线性 $D(a,b)$ 与原 $q$ 的关系；(388.1) 将同一个混合效果放入它的两槽，再用该效果比较整个输出。对每对置 $c=e+p$、$h=e-p$，两个效果为

$$
e+\lambda p=\tfrac{1+\lambda}{2}c+\tfrac{1-\lambda}{2}h,
\qquad
p+\lambda e=\tfrac{1+\lambda}{2}c-\tfrac{1-\lambda}{2}h.
\tag{388.8}
$$

各自的零读数是 355.1 的原比较球面相切。若两颗原子同块，它们在同一个数学四实维 $H_2(\mathbb C)$ 支持角内，原平方长度均为 $w_s(1+\lambda^2)$，其规范无迹部分仍是三实维；同一 sigma 下的角转动及横向复结构直接取 363.2、355.2。若跨中心，两平方长度分别为 $w_s+\lambda^2w_r$ 与 $w_r+\lambda^2w_s$，不要求相等；支持只有 $\mathbb Re\oplus\mathbb Rp$，规范无迹线为 $\mathbb R(e-p)$，没有跨中心 Peirce 相干。相交支持角、第三复向量位置的拼接、各块 $\mathbb{CP}^{n_s-1}$、带经典中心的复 Jordan–Lie 网及原实际联合的普通复张量，都是既有较大几何，未由变动谱比新造。数学角不是实际 $M_2$ 对象或物理三空间，第三复位置也不等于三实维无迹角。

相对固定半权主表述，(388.1) 删除的是预先指定的测试谱比，增加的是逐对存在量词及两个换位共根的要求；$1/2$ 本来就是可数学定义的有理数，未因此移除一项经验尺度。精确方程对逐对比例的稳健性不等于含噪稳定性。371–378 的面球候选是在全部正输入 $a,b$ 上要求 $D(a,b)\in E_1(\operatorname{supp}(a+b))\cap(a+b)^{\perp_q}$，不另输入 $\mathsf G_{0h}$；379–387 将同一关系限制为全部有序 primitive 对，明确包括自对，并已由 382.1 给出不借实际参考的局部分类，再由 383.1–384.1 接回全部原域及消费者。本引理保留另一份 $\mathsf G_{0h}$，只在正交对的两个混合自输入上增加标量读数，没有单独 primitive／单位自测试；它不是上述任一面球关系的同一测试域。385.1 的自对删除边界仍约束原子面球候选，不能借本引理将其自对删去。完整背景中的同模型类可由 (388.2) 及 374.1、383.1 相接，但没有全局改进、取代或优于任一面球候选的结论，也没有总公理数、认证成本、全局简约、最小性、新模型类／几何、历史原创或内生起源结论。

**定义 388.4（来源与仍存的原义务）。** 仓内前置为公开修订 [b0f7c01b01511ea00428c1b6edad5dd2b372eaf8](https://github.com/the-omega-institute/trureturing/tree/b0f7c01b01511ea00428c1b6edad5dd2b372eaf8) 的上述条目。343.1、359.1 的正常形和完整框架展开、360.1 的原全域下降、361.1 的同一尺度消费者均按其全部实际条件复用。严格对角占优的最大分量论证是成熟中间工具，见 Higham，*What Is a Diagonally Dominant Matrix?*，[Theorem 1 及其证明](https://nhigham.com/2021/04/08/what-is-a-diagonally-dominant-matrix/)；完整谱框架和三维角几何的成熟来源仍取 364.1。本附录 $\texttt{repo-derived}$ 的承重差额仅是 (388.5)–(388.7)：不同对的存在谱比仍与同一原单位的全部零行和相容，从而在原完整签名上取得 (388.2)。不将上述成熟工具、已有分类、完整 CP/Born 重构或模型族重新算作新理论，不由未检出同题推断历史优先权。

具体原 $\Omega$ 为何供应完整 $B_*$、整个 $\mathsf G_{0h}$、(388.1) 和同一 sigma，仍是实际来源的证明义务；存在谱比的数学量词不提供取得它的控制程序。[词卷 356.1–356.3](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#356-两个保留记录上的原词校准与同一旧关系) 的 $A_0/A_1$ 原对象识别、原 Born 采用及恰好两条有符号旧 $D$ 等式 (356.4) 仍分别是其前件，本引理不从裸来源倒供它们，也不以平方尺度代替原门的有符号绑定。324.3、词卷 339.2 的物理时钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器与原类型控制／准备、每台旧同效果设备自己的完整输出校准仍各有未决供应义务。这里仅有纯纸笔条件证明，不主张 Lean/kernel 或经验验证，也不宣告持续量子起源目标完成。

**定义 388.5（完整直观表述）。** 白话说，整座原世界一件不搬：经典房间、大小不同且比较尺各异的量子街区、全部真实联合和相关准备及其原质量、每台旧设备与细记录、完整失败出口、实际分组遗忘、带同一个原成功数的双向返回，以及每条合法有限历史都留下。完全错开或重叠一半的两颗珠子仍受原整支持规则约束；固定半权方案依旧作主图，这个附录只说，两颗错开的珠子不必事先统一成一全一半，每对可以自己找一个严格介于零和一的数学配比，但全权和小权换位后，必须在同一个配比上各自与自己的推动比较为零。这里是两个数学效果，没有凭空添两种真实准备或控制。已有原参考和整支持先把剩余自由压成各房的伸缩；一对共根把两边补偿锁成一个大于二的系数，而每对的系数可以不同。把珠子放回任意完整框架，原单位仍要求每行总账为零；若还有伸缩，挑绝对值最大的一行，它按这条规则要求的总账就比所有行可能凑出的总账还大，于是矛盾，全部伸缩只能消失。这个结论沿已有原单射回到小对象与经典房间，再用同一张原刻度单接回复乘法、Born 的正确运输、实际张量、全部旧事件、精确平方根词和完整失败、细口、同数双返回及所有原合法历史。同块两珠的小屋仍有三实维无迹球截面，相交小屋织在更大的复射影与 Jordan–Lie 网里，跨房却只有增减相抵的一条线；这不是实际量子比特或物理三维空间。删掉的只是事先写死的谱比，原来的一半本就能数学定义，没有少付一项经验标定；代价是每对必须存在这样一个共同根，也不能因此宣称比全部正输入或含自对原子面球方案全局更简。具体原世界为什么满足它、怎样识别两份原记录对象和有符号旧关系、怎样供应真实时钟与作用量、共同仪器及每台旧设备的完整输出，仍须从原来源继续证明。

## 追加锚 C128388（本行以下为增补区）

## 389. 共同支持面内只沿第一原子的切向运动

**定义 389.1（不显含比较尺的原子关系）。** 对有限复 Hermitian 直和中的全部有序 primitive 对，包含 $e=p$，定义

$$
\boxed{\mathsf F_{\rm atan}(E,D):\quad
D(e,p)\in E_1\!\left(\operatorname{supp}(e+p)\right)
\cap E_{1/2}(e),\qquad e,p\in\operatorname{Prim}(E).}
\tag{389.1}
$$

这里 $E_{1/2}(e)=\{v:e\circ v=v/2\}$；整个支持空间仍为 $E_1(c)=Q_cE$、$Q_c=2L_c^2-L_c$。primitive 仍是由原乘法和单位定义的全部非零不可分幂等元，不是一份所选框架，也不附带实际准备或操作身份。新关系不使用 $q$，不另选角度、谱比、坐标、迹、匹配或参考。它把相切位置从原子和的比较球面收回到第一颗原子本身，而不是声称两种点态切空间相同。

**定义 389.2（唯一完整候选与原范围）。** 分别固定 379.1–379.2 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$；仍只在原选中对象 $\operatorname{rank}E_X>p_*\ge2$ 上要求 (389.1)，记为 $\mathsf F_{\rm atan}^{>}$。唯一完整候选是

$$
\boxed{\mathsf C_{\rm atan}(B_*)
=B_*+\mathsf F_{\rm atan}^{>}+\sigma_{t_0}.}
\tag{389.2}
$$

同一原 $\Omega,q,D,L,\circ$、全部中心、经典块、不等量子块及原正权保持；全部实际有序联合、原乘积与相关准备、零与次归一质量，整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F，原设备／端口／细记录／失败身份及完整失败输出、实际分组／遗忘、具名原同数两侧支持返回及反向资料、每条原合法有限顺序、自适应和并行历史保持。两份背景各保留其自身的有限正生成或闭正生成，不合取、不互换。完整候选仍有原 $q$、原菜单和同一字面 sigma 的预选 primitive／半重叠标签；只是不再让新增二元关系显含比较尺。原背景独立供应的单位律不从完整背景删除。

## 390. 二阶补元切空间迫使两侧单位静止

**引理 390.1（没有单位前件的二阶角平衡）。** 设 $W=H_2(\mathbb C)$，单位为 $c$，实双线性 $G:W\times W\to W$ 满足 $\mathsf F_{\rm atan}(W,G)$。则

$$
G(e,e)=0\quad(e\in\operatorname{Prim}(W)),\qquad
G(c,b)=G(a,c)=0\quad(a,b\in W).
\tag{390.1}
$$

前件没有右单位、左单位、比较型、SC、交替性、导子律或保迹。

证明。自对的支持空间为 $\mathbb Re$，与 $E_{1/2}(e)$ 的交为零，所以 $G(e,e)=0$。在二阶角内，$c-e$ 也是 primitive，且

$$
E_{1/2}(c-e)=E_{1/2}(e).
\tag{390.2}
$$

固定 primitive $p$。对每颗 primitive $e$，双线性给

$$
G(c,p)=G(e,p)+G(c-e,p)\in E_{1/2}(e).
\tag{390.3}
$$

该固定向量因而属于全部半 Peirce 空间的交，而此交为零。可用有限三实方向准确核验：写 $v=a_0c+a_1X+a_2Y+a_3Z$，其中 $X,Y,Z$ 是角内 Pauli 元。对 $e_X=(c+X)/2$，$e_X\circ v=v/2$ 等价于 $X\circ v=a_0X+a_1c=0$；对 $e_Y,e_Z$ 同理，依次使四个系数全零。这里仅为证明选取数学坐标，不向候选加入三个所选测试或实际三维对象。因此 $G(c,p)=0$；primitive 实张成 $W$，遂有 $G(c,b)=0$ 对全部 $b$ 成立。

再对补元自对展开：

$$
0=G(c-e,c-e)
=G(c,c)-G(c,e)-G(e,c)+G(e,e)
=-G(e,c).
\tag{390.4}
$$

primitive 张成也给 $G(a,c)=0$。两侧单位均为输出，没有被提前放入前件。∎

## 391. 从二原子角恢复全域单位与交替性

**定理 391.1（整支持使补元平衡可以拼接）。** 对任意有限

$$
E=\bigoplus_sH_{n_s}(\mathbb C)
\tag{391.1}
$$

及任意实双线性 $D:E\times E\to E$，若 $\mathsf F_{\rm atan}(E,D)$ 成立，则全部 primitive 自对和有序正交对的整个输出为零，且

$$
D(a,u)=D(u,a)=0,\qquad D(a,a)=D(a,a^2)=0,
\qquad D(a,b)=-D(b,a).
\tag{391.2}
$$

$D$ 在每个共同谱子代数上也为零。本条不预设任一单位律或比较型。

证明。自对零沿 390.1 的第一步逐原子成立。若正交 primitive $e,p$ 属于同一简单块，令 $c=e+p$、$W=E_1(c)\simeq H_2(\mathbb C)$。$W$ 的 primitive 正是此数学角内的原秩一投影，亦是 $E$ 的 primitive；这里没有使用一般原实际嵌入保持 primitive 的假设。对任意两颗这样的原子 $r,s$，其和的支持不超过 $c$，故 (389.1) 使 $D(r,s)\in W$。它们分别实张成 $W$，双线性遂给

$$
D(W,W)\subseteq W.
\tag{391.3}
$$

限制到 $W$ 的半 Peirce 条件也逐字保持，因而引理 390.1 适用于同一限制，给 $D(e,c)=0$。结合 $D(e,e)=0$，有 $D(e,p)=0$。

若 $e,p$ 分属不同中心，整个支持为 $\mathbb Re\oplus\mathbb Rp$；它与原 $E_{1/2}(e)$ 的交为零，所以同样有 $D(e,p)=0$。此步包括纯经典方向，没有用连续原子族代替孤立原子。

将任意 primitive $e$ 补入完整原谱框架。两个输入次序的正交零与自对零分别给 $D(e,u)=D(u,e)=0$；primitive 张成 $E$，故两侧单位全域成立。对任意 $a=\sum_i\lambda_ie_i$，同一框架中的每个 $D(e_i,e_j)$ 都为零，所以 $D(a,a)=D(a,a^2)=0$，共同框架中的两元亦然。最后极化 $D(a+b,a+b)=0$ 得交替性。空载体的结论平凡。∎

## 392. 不用比较型或单位前件的裸局部分类

**定理 392.1（第一原子切向关系的充分性）。** 在 (391.1) 上，对每个实双线性 $D$，以下等价：

$$
\begin{aligned}
&\mathsf F_{\rm atan}(E,D);\\
&\exists(\gamma_s)_s\in\mathbb R^S,\quad
\pi_sD(a,b)=\gamma_s\mathrm i[a_s,b_s]
\quad(a,b\in E);\\
&D(a,u)=0\text{ 且全部原子对满足 (379.1)};\\
&D(a,u)=0\text{ 且全部正输入对满足 (371.2)}.
\end{aligned}
\tag{392.1}
$$

后两项可使用任意原正 Frobenius 型 $q(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s)$、$w_s>0$，无需等权；同一 $D$ 的等价对每份这样的正权成立。第一项没有比较型或右单位前件。全部经典、二阶、高阶与不等块均包括在内；各非经典块的实系数可以独立并可为零，经典块输出为零。

证明。由 391.1 已得右单位和全域交替性。对 primitive $e,p$，记 $v=D(e,p)$；Frobenius 性与 $e\circ v=v/2$ 给

$$
q(e,v)=q(e\circ e,v)=q(e,e\circ v)
=\tfrac12q(e,v),
\qquad q(e,v)=0.
\tag{392.2}
$$

将同一条件用于有序反向对 $(p,e)$，再用已经推出的 $D(p,e)=-v$，得 $q(p,v)=0$。于是

$$
q(e+p,D(e,p))=0.
\tag{392.3}
$$

整支持本就在 (389.1) 中，故 382.1 的准确前件全部成立。直接消费该定理，得到第二项及后两项的等价；不重证前卷 274.1 的全源／全输出因式分解、381.1 的二阶刚性或 373.1 的正输入分类，也不提前删除其证明中曾允许的二阶中央输出。

反向，对每块的 primitive $e,p$，交换子支撑在 $\operatorname{supp}(e+p)$ 内，且

$$
e\circ\bigl(\mathrm i[e,p]\bigr)
=\tfrac12\mathrm i[e,p].
\tag{392.4}
$$

不同块的输出为零，故第二项给第一项。这里没有在 primitive 输入上缩放、作开集延拓或调用实际参考。∎

**定义 392.2（相对于旧入口的准确简化）。** 新的完整原子关系自身已蕴含裸局部分类所需的单位平衡，不再另列该前件；旧 (379.1) 或 (371.2) 的裸分类仍须保留其右单位，不能把 376.3 的删除反例改判。两种入射条件的逐对切空间并不相同，等价只在整个实双线性关系族上成立。这里减少的是新关系对显式比较尺和独立局部单位前件的依赖；完整 $B_*$ 的原单位来源及 $q$ 仍原样保留。没有最少独立约束、较少标量方程、有限认证或最低取得成本的结论。

## 393. 同一原世界上的完整候选等价

**定理 393.1（第一原子切向与全域量子入口）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，

$$
\begin{aligned}
B_*+\mathsf F_{\rm atan}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm prph}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm atan}(B_*)
&\Longleftrightarrow\mathsf C_{\rm prph}(B_*)
\Longleftrightarrow\mathsf C_{\rm fsph}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{393.1}
$$

对应为同一全部原数据及全部原合法有限历史上的恒等，不重定义原 $D$、原比较、实际事件或 sigma。

证明。前卷 246.1 分别供应两份完整背景中的原静态复直和。在每个原选中对象上，392.1 将 (389.1) 等价地变回原子面球关系；反向使用完整背景已独立供应的原右单位和 382.1，得到同一正常形，再用 (392.4)。两方向均不假设原嵌入保持 primitive 或 $q$，也不把数学二阶角添加成实际对象。

随后准确消费 383.1。该定理的原实际充分大身份参考、同一含幺 Jordan/$D$ 单射，将 SC 和整个 Jordan 导子缺陷作为向量带回全部原对象，包含零对象；运输的不是 $q$。前卷 275.2 再由完整原背景同步共同曲率，保留 $\kappa=0$ 分支；同一原 sigma 才以原正 $w_0$ 的 $(1-\kappa)w_0/4=0$ 固定 $\kappa=1$。局部 392.1 没有要求不同 $\gamma_s$ 同步，没有缩放原 $D$ 或重选 $t_0$。其余候选等价直接复用 383.1。既有完整 tagged-CP 满足族也由反向蕴含满足本候选，包含没有实际 $M_2$ 对象的子族。∎

## 394. 现有量子公理与全部原过程的回接

**定理 394.1（沿同一原刻度完整消费）。** 在唯一候选 (389.2) 中，384.1 的每个消费者及其全部原前件保持，具体对应为：

| 准确取得或保留的接口 | 同一原结构上的结论 |
| --- | --- |
| 393.1 给全域 I+SC，原 Jordan 乘法与同一 sigma | $\mathcal A_A=\bigoplus_sB(H_{A,s})$、$E_A=(\mathcal A_A)_{\rm sa}$、$C_A=(\mathcal A_A)_+$；$a\cdot b=a\circ b-\mathrm iD_ab$，$D_ab=\mathrm i[a,b]/2$，$[D_a,D_b]=-[L_a,L_b]$，每个幂等元 $c$ 满足 $D_c^2=-P_c/4$。 |
| 全部原准备、原 $g^0$ 和原不等正权 $q$ | $\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$，质量 $\tau_A(\rho_\alpha)=\alpha(u_A)$；零、奇异与次归一输入均保留。 |
| 原 X、同一 $D$ 保持、有序交叉零、乘积张成与原乘积准备分离 | 每个实际有序联合取得保留全部中心对的同取向普通复张量，包含全部原相关输入；不要求联合 $q$ 或 $B_A$ 因子化。 |
| 每个旧事件的全事件 R、同设备同记录旁接及完整效果和 | $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为旧事件的 CP/TNI 运输，原完整设备之和为 TP；不添加任意仪器或新实际记录。 |
| 整个 AC、精确 $N_u$、X/Xs 和原所选平方根词的相关执行 | 原成功输出为 $\sqrt e\rho\sqrt e$，相关执行为 $(\sqrt e\otimes I)X(\sqrt e\otimes I)$；失败按原全部方向、中心与端口保留完整输出，包括 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$ 的原占用方向。 |
| 实 Jordan F、原实际细记录、分组／遗忘及具名同数双侧返回 | $S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$；$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$、$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$。原 $q_\ell>0$、全部零标签、失败及反向资料不变。 |
| 全部原准备、末端效果及每条原合法有限历史 | $\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$；空历史、顺序、实际记录自适应、已供并行联合、细化／分组／实际遗忘、零／失败／返回／停止全部包括，仅在原分母为正时取条件概率。 |

这里 $P_c=4(L_c-L_c^2)$、$\mathsf C_e(X)=eXe$，不与整支持投影 $Q_c$ 混用；$\dagger_0$ 是原 $g^0$ 伴随，$B_A$ 是原比较运输，不是背景记号 $B_*$。不把数学 Kraus 分解当实际细记录，也不以同效果替换旧设备自己的完整输出。

证明。393.1 给出 384.1 的完整入口，在同一原对象、准备、设备、输出身份和执行上逐项应用该定理即可。两套准备背景分别使用其原正延拓；闭背景只在同一已固定原执行上延拓，不把极限数学准备增补为实际准备。此表是既有量子与过程消费者的完整参数对应，不将它们重计为新重构结果。∎

## 395. 删去共同支持仍会留下非零自推动

**定理 395.1（第一原子切向不能独自代替整支持）。** 即使额外保留右单位，仅要求 $D(e,p)\in E_{1/2}(e)$ 对全部有序 primitive 对成立，也不能强制 392.1。

证明。取数学 $H_2(\mathbb C)$、单位 $I$ 和 Pauli 元 $X,Y,Z$，定义

$$
D(a,b)=\operatorname{Tr}(Zb)\,\mathrm i[Z,a].
\tag{395.1}
$$

这是实双线性映射。$\operatorname{Tr}Z=0$ 给 $D(a,I)=0$；对任意 primitive $e,p$，固定交换子 $\mathrm i[Z,e]$ 属于 $E_{1/2}(e)$，故保留的全部切向条件成立。却取

$$
e=p=\tfrac12\left(I+\frac{X+Z}{\sqrt2}\right),
\qquad D(e,e)=-\tfrac12Y\ne0.
\tag{395.2}
$$

非零切向元不属于 $\mathbb Re$，所以整支持失败，也不是标量交换子正常形。本例仅分离裸局部条件，不供应完整 $B_*$、实际参考或同一原 sigma。

反向，删去第一原子切向而只保留整支持时，已有 376.2 的 $D(a,b)=\operatorname{Tr}(hb)a$ 连同右单位直接适用：$a=b=e_{11}$ 时输出为 $e_{11}\notin E_{1/2}(e_{11})$。这准确复用原删除见证，不另立为新的反例分类。∎

## 396. 原子流形中的有限三维提升

**定义 396.1（共同房间中的第一原子切向）。** 在 $H_n(\mathbb C)$ 块内，primitive 流形为 $\mathbb{CP}^{n-1}$，其在 $e$ 的实切空间是 $E_{1/2}(e)$，沿母卷 65.2、73.1 与前卷 277.2 的成熟几何接口使用。对 $c=\operatorname{supp}(e+p)$，(389.1) 是同一数学角 $E_1(c)$ 内第一颗原子的切向要求；若为非经典二原子角，则是嵌入该角的 $\mathbb{CP}^1$ 切平面。跨中心没有这样的量子横向，交空间直接为零；自对的房间只剩一条轴，切向与它也只交于零。

在数学二阶角写 $e=(c+r\cdot\sigma)/2$、$v=a_0c+w\cdot\sigma$，$|r|=1$。切向条件恰为

$$
a_0=0,\qquad r\cdot w=0.
\tag{396.1}
$$

这是三实维无迹空间中原子球面在 $r$ 的切平面，既不是整个三维球体，也不是上一轮经过 $e+p$ 的原比较球面。补原子对应 $-r$，两者切平面相同；390.1 的固定单位输出若对每个补元分解都相容，就必须同时落在三个独立方向的切平面中，因而为零。这个有限三方向论证不等于对全部原对象的有限认证。

**定义 396.2（反序后的关系之关系）。** 391.1 已推出交替性以后，同一输出也属于 $E_{1/2}(p)$。二阶角中它遂同时垂直于两颗原子的 Bloch 方向，非平行时沿叉积；平行与反平行则分别由自对零与正交零处理。392.1 保证系数不是逐输入任意选择，而是由原双线性关系拼成每块同一实数。较大结构仍为带经典中心的复 Jordan–Lie 网、相交的 Bloch／Peirce 角、复射影原子流形和原实际联合中的普通复张量。三实维角、用于高阶支撑拼接的第三复位置与物理空间维数不同，不产生实际量子比特、仪器、时钟或共同作用量。

## 397. 来源、内生边界与完整白话

**定义 397.1（新增桥梁及供应范围）。** 仓内前置固定于 [`b0f7c01b01511ea00428c1b6edad5dd2b372eaf8`](https://github.com/the-omega-institute/trureturing/tree/b0f7c01b01511ea00428c1b6edad5dd2b372eaf8)。前卷 246.1 供应两份原背景的静态复载体；本卷 382.1 供应包含右单位的原子面球正常形，其准确依赖仍是前卷 274.1 和本卷 381.1、373.1；383.1、384.1 供应原参考下降、共同原尺度与完整消费者。母卷 78.2 另有面积背景下的全幂等元切向等价，其面积和全域前件不是本轮的输入，不用它替代这里无面积、无局部单位前件的证明。

原子流形与半 Peirce 切空间的成熟对应还见 Nomura，*Manifold of primitive idempotents in a Jordan-Hilbert algebra*，[原文](https://www.jstage.jst.go.jp/article/jmath1948/45/1/45_1_37/_pdf)，§3，第 46–48 页。该文在拓扑简单 Jordan–Hilbert 代数中建立原子流形的嵌入与切空间识别；这里仅在各有限复简单块应用此几何接口，不用其归一化替换原 $q$，也不把它当作双线性分类的供应。

补元、Peirce 空间、原子张成、Pauli 坐标、谱分解与切空间描述是成熟中间工具。这里的 $\texttt{repo-derived}$ 综合是：共同支持先闭合数学二阶角，补元第一切向的交迫使角内左单位静止，自对展开再恢复右单位；由正交角拼接取得全域单位、SC 和交替性，再通过有序反向对恢复任意原正权的比较中性，准确接入旧分类。395.1 给出本关系的支持删除边界。没有把原有分类、面积关系、量子重构或成熟几何重计为新增结果，也不由文献未命中主张历史优先权。

具体原 $\Omega$ 仍须由自身实际来源满足完整 $B_*$、第一原子切向关系和同一原 sigma，条件等价不把这些宣布为任意世界的定义真理。324.3 的三项来源义务分别保持：物理时钟／Hamiltonian／共同作用量，独立成功支的共同完整仪器，旧同效果设备自己的完整输出校准。含噪稳定、最少独立约束、有限认证、最低取得成本及物理空间维数也不由本候选给出。

**定义 397.2（完整直观表述）。** 白话说，整座原世界仍完整保留：经典房间、大小不同的量子街区和各自原比较尺、所有真实联合与相关准备、每台旧设备和细记录、完整失败出口、实际分组与遗忘、带同一个原成功数的两侧返回及反向资料、每条原合法有限历史，都不换身份。新规则只看两颗最细的珠子，也包括自己问自己：关系输出不能离开两珠共同的小屋，并且要沿第一颗珠子所在的原子表面走，不再拿两珠之和去量一张比较球面。自己问自己时小屋只剩一条轴，轴与切面相交只有零；在二阶小屋里，一颗珠子和补珠站在球的相反位置，却有同一张切平面，把它们的关系输出相加所得的单位输出，必须对每一种补珠分法都躺在那张面里，三个独立方向便让它只能为零。再展开补珠问自己的零关系，另一侧的单位也静止；各个正交小屋于是共同把全世界的单位平衡和交换次序只反号接起来。反序后的同一箭头也贴着第二颗珠子，两端各自的切向使旧比较尺的中性自动回来，已有分类便把全部块锁成各自的交换子。原真实参考将向量和乘法缺陷带回所有旧对象，完整背景接成共同尺度，同一张原刻度单最后定为一，复乘法、Born 的两套正确运输、普通实际张量、全部旧事件、精确平方根词及完整失败、原细记录、同数双返回与全部合法历史便逐项接回。若只说沿第一珠表面走而不守共同小屋，关系仍可在自己问自己时转动，395.1 正给出这样的箭头。这里省去的是新关系对显式比较尺和独立局部单位前件的依赖，完整原背景的比较尺与单位来源并未删除；数学球面的三维不自动变成物理三维、时钟或作用量，具体世界为何内生满足这条关系仍要由自身来源继续证明。

## 追加锚 C128397（本行以下为增补区）

## 398. 同一输出在两个原子端点都切向

**定义 398.1（不显含支持或比较的二端关系）。** 对有限复 Hermitian 直和 $E=\bigoplus_{s\in S}H_{n_s}(\mathbb C)$ 及同一实双线性 $D:E\times E\to E$，定义

$$
\begin{gathered}
E_{1/2}(e)=\{v\in E:e\circ v=v/2\},\\
\boxed{\mathsf F_{\rm 2tan}(E,D):\quad
D(e,p)\in E_{1/2}(e)\cap E_{1/2}(p)
\quad\bigl((e,p)\in\operatorname{Prim}(E)^2\bigr).}
\end{gathered}
\tag{398.1}
$$

量词包括自对、两个次序、同块正交对及全部跨中心对；两个端点约束的是同一个 $D(e,p)$，不是分别约束 $D(e,p)$ 与 $D(p,e)$。此定义不输入 $q$、共同支持、单位湮灭、SC、导子、交替或理想保持。

**定理 398.2（裸二端切向的单位与整支持桥）。** 对每个上述有限直和，包括空载体、纯经典载体、任意不等块大小，以及任意比较

$$
q(a,b)=\sum_sw_s\operatorname{Tr}(a_sb_s),\qquad w_s>0,
$$

有精确等价

$$
\begin{aligned}
\mathsf F_{\rm 2tan}(E,D)
&\Longleftrightarrow
\bigl[D(a,u)=0\ (a\in E)\ \text{且全部原子对满足 (379.1)}\bigr]\\
&\Longleftrightarrow
\bigl[\exists(\gamma_s)_s\in\mathbb R^S,
\ \pi_sD(a,b)=\gamma_s\mathrm i[a_s,b_s]\ (a,b\in E)\bigr]\\
&\Longleftrightarrow
\bigl[D(a,u)=0\ (a\in E)\ \text{且全部正输入对满足 (371.2)}\bigr].
\end{aligned}
\tag{398.2}
$$

此外两单位均湮灭，$D(a,a)=0$、$D(a,b)=-D(b,a)$，且 $q(c,D(a,b))$ 全交替。非经典块的实 $\gamma_s$ 独立且允许为零；经典输出为零，其系数不承担可识别参数。这里只新增从 (398.1) 到单位和 (379.1) 的桥；后三种表述之间的全部局部分类直接继承 382.1。

证明。先核对所用成熟谱／Peirce 工具的前件。若实线性 $A:E\to E$ 对全部 primitive $f$ 满足 $Af\in E_{1/2}(f)$，则对任意完整谱框架 $f_1,\ldots,f_N$，

$$
q(f_i,Af_j)=0\quad(\text{全部 }i,j),\qquad
q(x,Ax)=0\quad\left(x=\sum_it_if_i\right).
\tag{398.3}
$$

因为 $f_i$ 分别在 $f_j$ 的 Peirce 一空间或零空间，而 $Af_j$ 在半空间；原正 Frobenius 型使这些空间正交，不要求各块等权。每个实 $x$ 有自己的谱框架，所以实极化给 $A^{\dagger_q}=-A$。同框求和给 $q(f_i,Au)=\sum_jq(f_i,Af_j)=0$；任意 primitive 均可入框，且 primitive 实张成整个 $E$，故 $Au=0$。这是配平续卷 88.1、107.2 及 Tao–Gowda Proposition 3 所用的成熟框架读数机制在当前全原子域上的应用；这里先由全部对角读数验证单位，未将它预设，也不另立为新线性映射分类。

在 (398.1) 下，primitive 的张成性使每个固定 $b$ 的 $a\mapsto D(a,b)$ 在所有 primitive $a$ 上切向；每个固定 $a$ 的 $b\mapsto D(a,b)$ 同样如此。(398.3) 因而给

$$
\begin{gathered}
D(u,b)=D(a,u)=0,\\
q(c,D(a,b))=-q(a,D(c,b)),\qquad
q(c,D(a,b))=-q(b,D(a,c)).
\end{gathered}
\tag{398.4}
$$

特别地，$q(c,D(a,a))=-q(a,D(c,a))=0$，最后一步用第二槽映射的斜伴随。非退化性给整个向量 $D(a,a)=0$，极化给交替性；(398.4) 随即给三形式。自对的共同切空间在非经典块中可以非零，因此自对零来自同一双线性关系的全域相容性，不能由 $E_{1/2}(e)\cap E_{1/2}(e)$ 的维数断言。

现在只证明缺失的整支持。对 primitive $e$，其半空间只在自身简单块中，矩阵形为相对于 $\operatorname{im}e\oplus\ker e$ 的纯非对角 Hermitian 矩阵；其他中心的整个输出为零。一维经典块的半空间就是零。因此跨中心对的两个半空间交为零，含经典端点的对也为零。

同块且 $e\ne p$ 时，取 $v=D(e,p)$、$W=(\operatorname{im}e+\operatorname{im}p)^\perp$。对任意 $z\in W$，$ev+ve=v$ 给 $vz\in\operatorname{im}e$，$pv+vp=v$ 又给 $vz\in\operatorname{im}p$。两条不同复直线的交为零，故 $vW=0$；Hermitian 性同时消去这些行，因而

$$
v=cvc\in E_1(c),\qquad c=\operatorname{supp}(e+p).
\tag{398.5}
$$

这排除所有角内外连接分量，而非只令角外压缩为零。对自对，刚证的 $v=0$ 给相同结论。Peirce 正交性还给 $q(e,v)=q(p,v)=0$，故全部有序对满足完整 (379.1)。正交同块对的点态交仍是非零 $V_{ep}$；此时已齐备 380.1 的准确前件，直接由该条的 $0=D(e_i,u)=\sum_{j\ne i}D(e_i,e_j)$ 及不同 $V_{e_ie_j}$ 的直和得到每项为零。因此正交／反足对亦为整个输出零，没有把点态交误当零空间。

现在才应用 382.1：同一全源、全输出 $D$ 的右单位和全部 (379.1) 已证，故取得其经典、二阶、高阶和跨中心全部正常形及正输入等价；不重作 274.1 或 381.1 的分类。反向只核对新增入口：对幂等 $e,p$，

$$
e\circ\mathrm i[e,p]=\tfrac12\mathrm i[e,p],\qquad
p\circ\mathrm i[e,p]=\tfrac12\mathrm i[e,p].
\tag{398.6}
$$

逐块乘任意实 $\gamma_s$ 仍成立，跨块及经典输出本来为零，故继承的正常形给 (398.1)。空载体各项平凡。整个证明没有缩放 primitive、将其和仍称 primitive，或把原比较权换成相同权。∎

## 399. 原选中域、同一固定标签与完整消费者

**定义 399.1（唯一完整候选与保留范围）。** 分别取母卷 88.1 的完整 $B$ 与 67.1 的完整 $\mathsf B_{\rm cl}$，并沿前卷 264.1、272.1–272.2 及本卷 379.2 保持全部原范围，任一记为 $B_*$。$B$ 的精确有限正生成与 $\mathsf B_{\rm cl}$ 的闭正生成分别保留。仅在原 $\operatorname{rank}E_X>p_*=\operatorname{rank}E_P\ge2$ 域施加 (398.1)，记为 $\mathsf F_{\rm 2tan}^{>}$，定义

$$
\boxed{\mathsf C_{\rm 2tan}(B_*)
=B_*+\mathsf F_{\rm 2tan}^{>}+\sigma_{t_0}.}
\tag{399.1}
$$

$t_0$、原菜单、$\mathcal K$、实际 $J_0=P^{\otimes2}$ 和字面 sigma 均为 272.1、379.1 的同一预选资料。整个原 $\Omega$、$D,q,L,\circ$、全部经典中心、不等块和原正权、实际有序联合、乘积及全部相关准备、零与次归一质量不变。整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F、全部旧设备／端口／细记录／失败身份及完整失败输出、实际细化／分组／遗忘、具名同数两侧支持返回及同数反向资料、每条原合法有限顺序／自适应／并行历史均保留。原完整背景独立供应的右单位仍然保留；398.2 的局部推导不是删去该背景条款的授权。不另加支持、SC、LU、导子、naturality、理想保持、反向交叉零、直接 $AP$、实际 $M_2$、共同参考指数、时钟／作用量或仪器供应。

**定理 399.2（两份完整背景上的恒等对应）。** 在各自同一完整原签名上，分别有

$$
\begin{aligned}
B_*+\mathsf F_{\rm 2tan}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm prph}^{>}
\Longleftrightarrow B_*+\mathsf F_{\rm fsph}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm 2tan}(B_*)&\Longleftrightarrow
\mathsf C_{\rm prph}(B_*)\Longleftrightarrow
\mathsf C_{\rm fsph}(B_*)\Longleftrightarrow
\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{399.2}
$$

同一原 $\sigma_{t_0}$ 使 384.1、375.1 的全部消费者按原量词适用。

证明。前卷 246.1 在两份准备背景分别供应每个原对象的静态复直和和原正 Frobenius 型；母卷 30.1／67.3 独立供应右单位。因此 398.2 在每个原选中对象恰好等价地给出 383.1 的原子前件，继而完整复用 383.1、374.1。其下降的准确对象是 352.1 的 SC 向量和整个导子缺陷 $\Delta_A(a;b,c)$：对每个原 $A$，原身份事件和完整 R 供应进入选中域的实际充分大 $J=AR$，原含幺 Jordan／同一 $D$ 单射满足

$$
i(D^A(a,a))=D^J(i(a),i(a))=0,\qquad
i(\Delta_A(a;b,c))=\Delta_J(i(a);i(b),i(c))=0.
\tag{399.3}
$$

398.2 已给选中对象的全部实输入正常形，故这里不要求 $i$ 保 primitive。单射性带回全部小对象、经典块、旧输出及零对象的原 SC 和导子律；有限 EJA 内性给原 I。不运输 $q$，不加入联合权因子化、等距、共同参考指数或原来未供的对象。反向亦可直接按前卷 275.2：各自完整 $B_*+\mathrm I+\mathrm{SC}$ 给逐块标量交换子，再由 (398.6) 给选中域二端切向。

共同尺度属于同一既有 275.2，而非裸 398.2。完整 $B$ 的入口是母卷 41.2、57.2、63.3 的 Z 链；完整 $\mathsf B_{\rm cl}$ 的入口是 68.2、70.1、71.1 的完整 $\mathsf Q$ 链。后者只在同一已固定原执行上作正锥连续延拓，不把极限准备变成实际准备。两份入口分别给唯一共同 $\kappa\ge0$、II 和 $\lambda_{A,s}^2=\kappa$，含全零分支。375.1 随后用同一预选 $t_0$ 和原正权 $w_0$ 得

$$
\sigma_{t_0}\quad\Longleftrightarrow\quad
(1-\kappa)w_0/4=0\quad\Longleftrightarrow\quad\kappa=1.
\tag{399.4}
$$

这固定原 $D$ 的尺度，不重选标签、不重标 $D/q/L$，也不把平方尺度当成某个固定来源坐标中的有符号旧 $D$ 绑定。此时 384.1 的原前件逐项齐备，下表只登记其继承应用，不另报量子或过程重构。

| 同一原资料及已恢复入口 | 既有消费者的准确应用 |
| --- | --- |
| 原 I+SC、原 Jordan 乘法、同一 sigma 和原 $D$ 的取向 | $a\cdot b=a\circ b-\mathrm iD_ab$，$D_ab=\mathrm i[a,b]/2$，$[D_a,D_b]=-[L_a,L_b]$，$D_c^2=-P_c/4$；全部原复矩阵直和和经典中心保留。 |
| 全部原准备、原 $g^0$ 和不等权 $q$；原 X 及实际乘积准备 | $\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$、$\tau_A(\rho_\alpha)=\alpha(u_A)$；全部中心对的同取向普通实际复张量和原相关输入。 |
| 每个旧事件自身的完整 R、同设备同记录旁接、完整相关正锥及完整效果和 | 原 $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为 CP/TNI，原完整设备事件和 TP；$\dagger_0$ 仍取原 $g^0$。 |
| 整个 AC、精确 $N_u$、X/Xs、原所选词及合法连线 | 同一原平方根成功支及相关执行；每个占用失败方向的整个 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其余方向、中心、端口按原失败映射。 |
| 实 Jordan F、实际细记录、分组／遗忘、具名同数双返回与反向资料 | 原 $S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$、$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；原 $q_\ell>0$、零标签和完整失败保留。 |
| 每份原准备、原末端效果和每条原合法有限历史 | 逐字用 (375.5) 的迹对偶评价，覆盖空历史、顺序、自适应、已供并行联合、全部相关输入、细化／分组／实际遗忘、零／失败／返回／停止；仅在原分母正时取条件概率。 |

数学 Kraus 指标不取得实际记录身份，同效果不替换任何旧设备自己的完整输出。原正向满足族直接继承 383.1、框架卷 317.1，包括无实际 $M_2$ 的子族；没有另造满足模型。∎

## 400. 删除端点的范围与两张切平面的几何

**命题 400.1（准确反事实与既有删除见证）。** 在完整 $B_*$ 中，(399.2) 的精确反事实为：全域 $\mathrm I\land\mathrm{SC}$ 失败，当且仅当存在原选中 $X$ 及有序 primitive 对 $(e,p)$，使同一 $v=D^X(e,p)$ 至少违反 $e\circ v=v/2$、$p\circ v=v/2$ 中的一式；不要求两式同时失败。即使保留同一 sigma，整个二端关系也不能无条件删除。仅保留一个端点则已不能在裸局部强制 (398.2)，包括保留双单位的情形。

证明。第一个断言是 (399.2) 在各自完整背景中的逻辑否定。删除整个关系时直接复用框架卷 282–284 的完整 $\mathfrak M_{170}(w)$：该模型在原选中域违反 O，而保留完整 $B$、完整 $\mathsf B_{\rm cl}$、H 和任意原预选 $\sigma_{t_0}$。398.2 已使二端关系推出 O，所以它也被同一既有模型否定；原全部准备、过程、失败、返回和合法历史仍由该原模型承担，不用裸四维片段代替完整性。

删除第一端点、仅留 $D(e,p)\in E_{1/2}(p)$ 时，取母卷 42.3、配平续卷 84.1 已有输入扭转映射的 $H_3(\mathbb C)$ 限制：$D(a,b)=\mathrm i[\Gamma(a),b]/2$，$\Gamma=\operatorname{Ad}_{\operatorname{diag}(1,-1,1)}$。固定 $a$ 时为内导子，故全部 primitive 第二端点切向；$\Gamma(I)=I$ 给双单位。母卷 (42.2) 的同一 $a=(e_{11}-e_{22})+(e_{12}+e_{21})$ 有 $D(a,a)\ne0$，所以由 398.2 不满足二端关系。删除第二端点的裸见证直接取这个既有双线性映射的负转置 $\widetilde D(a,b)=-D(b,a)$：第一端点切向、双单位保留，SC 仍失败。这里是比较不同局部赋值，没有改动 (399.2) 中任何固定原 $D$；这两个局部见证不证明当前完整 $B_*+\sigma_{t_0}$ 上逐端点独立。原 42.3 的完整模型结论也不自动验证当前任意预选 sigma。385.1 的经典自对删除见证针对 (379.1)，不满足这里的经典端点切向，不能搬来宣称二端条件的自对删法已经失败。∎

**定义 400.2（简化、代价及几何）。** 相对于 379.1，(398.1) 删除公式中的显式共同支持与 $q(e+p,\cdot)$，换成两个原子端点对同一输出的半 Peirce 方程。第二端点不是把输入次序交换再问一次：在尚未取得交替性时，$D(p,e)$ 与 $D(e,p)$ 是不同输出。新的代价是第二份完整切向约束及其与同一双线性 $D$ 的全原子相容性；没有更少独立信息／方程、更低取得成本或有限认证结论。裸局部它还恢复单位，而完整背景的原单位供应仍保留。371–378 的全正输入面球、379–387 的原子面球及 388 的逐对谱比附录各沿自己的输入域；本条不输入 388 所保留的另一份 $\mathsf G_{0h}$，也不产生新的完整模型类。

在同块数学 $H_2(\mathbb C)$ 角内，写 $e=(I+r\cdot\sigma)/2$、$p=(I+s\cdot\sigma)/2$，$|r|=|s|=1$。将两半空间都限制到这个角的 $H_2(\mathbb C)^0\cong\mathbb R^3$ 时，它们是 $r^\perp,s^\perp$；非平行时交线沿 $r\times s$。自对 $r=s$ 和正交／反足对 $r=-s$ 的两平面重合，交仍二维；这两种输出零须用 398.2 的全局双线性与框架论证，不能从图中删去。跨中心时是不同直和理想的切空间交零，没有跨中心 Bloch 球；经典端点的切空间为零。较大结构仍是既有 $\mathbb{CP}^{n_s-1}$ 原子流形、相交支撑角、复 Jordan–Lie 网及原实际有序张量；数学三实维角既不指物理维数，也不供应实际 $M_2$。

## 401. 来源适用性与未解决的原生绑定

**定义 401.1（承重来源与结果范围）。** 仓内数学前置取公开修订 [`648244ea807501955f4425547aa1ae5d0cad8764`](https://github.com/the-omega-institute/trureturing/tree/648244ea807501955f4425547aa1ae5d0cad8764)。新桥为 $\texttt{repo-derived}$：(398.3)–(398.5) 将同一双线性关系的两槽切向相容性变成单位、自对零及整支持，再接到现成 382.1；局部分类、全域下降、共同尺度和全部消费者分别继承 382.1、383.1／374.1／352.1、前卷 275.2、384.1／375.1。没有重新认领这些结果。

成熟中间来源的范围为：Nomura，*Manifold of primitive idempotents in a Jordan-Hilbert algebra*，[原文 §3](https://www.jstage.jst.go.jp/article/jmath1948/45/1/45_1_37/_pdf)，DOI `10.2969/jmsj/04510037`，识别 primitive 流形的半 Peirce 切空间；这里只逐有限简单块使用，不将其简单性或归一 Hilbert 型加到整个直和。Tao–Gowda，*A Representation Theorem for Lyapunov-like Transformations on Euclidean Jordan Algebras*，[作者原文 §2、Propositions 1、3](https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf)，DOI `10.1142/S0219198913400343`，供应 frame 零配对、Lyapunov-like／单位／导子与斜伴随的成熟关系；(398.3) 明列当前原不等权上的对应，未将该单线性定理冒充完整二端桥。Alaminos–Brešar–Extremera–Villena，[原文 Theorem 2.2](https://users.fmf.uni-lj.si/bresar/documents/bilmapsid.pdf)，DOI `10.1016/j.laa.2009.09.017`，量化关联矩阵代数的全部秩一幂等元，不限 Hermitian primitive，不能直接代替本条桥。配平续卷 83、88、89 的原子零接触、框架极化和余切下降是既有中间接口；母卷 78.2 另有全域面积前件，不能不带该前件调用。本结果不主张文献优先权、Lean/kernel 或经验验证。

具体原 $\Omega$ 满足完整 $B_*$、(398.1) 和同一 sigma 仍各需来源证明。R5-009 §§3、6 的正配方表示与具名分支／Kraus 相容保留其自身前件；该文 §5 的 $D$ 几何另行给定，不能由正配方表示推出本条原 $D$。最新 [RRO 来源特定标记词定理 8.2](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md) 以其原核、发射和实际路径合同取得相应词律与频率，没有提供此处原对象、Jordan/$D$ 或完整仪器接口。上述来源均不自动供应[词卷 356.1–356.3](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#356-两个保留记录上的原词校准与同一旧关系) 的双记录原对象识别、Born 采用及两条有符号旧 $D$ 等式 (356.4)。物理时钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器及原控制、每台旧同效果设备自己的完整输出校准，仍各守 324.3 的来源条件。

**定义 401.2（完整白话）。** 白话说，整座原世界原样留下：经典房间、大小不同且比较尺各异的量子街区、全部真实联合与相关准备及原质量、每台旧设备和细记录、完整失败出口、实际分组遗忘、带同一个原成功数的两侧返回与反向资料，以及每条合法有限历史都不搬。新规则只问原来选中对象里的两颗最细珠子，也问同一颗和自己：这份有向关系产生的同一根箭头，必须同时贴着两颗珠子各自的原子曲面。单看一对，重合或反足的两张切平面还容得下许多箭头，不能凭小图说它已经为零；但所有珠子共享同一双线性关系，把每个谱框架的读数放在一起便先使两端作用都守原比较与单位，再消掉自推动，两个不同端点还会共同排除支撑外的整列输出。于是不用把共同房间或比较尺写进新规则，也能恢复已有原子面球关系，随后只继承已有分类、真实参考下降和共同尺度，用同一张预选原刻度单接回复乘法、保质量 Born 运输、实际张量、全部旧事件、精确平方根词与完整失败、细记录、同数双返回和所有原合法历史。简化的是表达中的显式支持与比较，代价是增加第二端点的完整切向约束，没有证明独立信息更少、取得更便宜或有限可认证；三实维小角不等于物理三维或实际量子比特。正配方能表示正对象及其分支，也不自行认出这根旧的有符号关系箭头；具体来源为何满足二端规则、原背景及同一刻度，怎样绑定旧 $D$ 并供应真实时钟、作用量、共同仪器和每台旧设备的完整输出，仍须从各自来源继续证明。

## 追加锚 C128401（本行以下为增补区）

## 402. 二端切向只在零重叠与半重叠处输入

**定义 402.1（原乘法决定的两层输入域）。** 在有限复 Hermitian 直和 $E=\bigoplus_{s\in S}H_{n_s}(\mathbb C)$ 上，记 $L_ea=e\circ a$、$Q_e=2L_e^2-L_e$，primitive 与半 Peirce 空间仍取 398.1 的原定义。对同一实双线性 $D:E\times E\to E$，置

$$
\begin{gathered}
\mathcal Z_h(E)=\{(e,p)\in\operatorname{Prim}(E)^2:Q_ep=0\ \text{或}\ Q_ep=e/2\},\\
\boxed{\mathsf F_{\rm zhtan}(E,D):\quad
D(e,p)\in E_{1/2}(e)\cap E_{1/2}(p)
\quad\bigl((e,p)\in\mathcal Z_h(E)\bigr).}
\end{gathered}
\tag{402.1}
$$

矩阵实现中 $Q_ep=epe$：同块 primitive 的两层分别是 $\operatorname{Tr}(ep)=0,1/2$；跨中心对在零层。输入不含自对及其它重叠比例，也不是选定框架。它只使用原 Jordan 乘法；$Q_e$ 判定输入层，不是要求输出留在 $\operatorname{supp}(e+p)$ 的投影。新增关系不使用原 $q$、任一单位律、SC、交替性、导子律、协变或实际参考。

**定义 402.2（唯一完整候选与不变背景）。** 分别取 399.1 的完整 $B$ 与完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$，仅在同一原选中域 $\operatorname{rank}E_X>p_*=\operatorname{rank}E_P\ge2$ 上要求 (402.1)，记为 $\mathsf F_{\rm zhtan}^{>}$。唯一完整候选为

$$
\boxed{\mathsf C_{\rm zhtan}(B_*)
=B_*+\mathsf F_{\rm zhtan}^{>}+\sigma_{t_0}.}
\tag{402.2}
$$

完整背景独立供应的原右单位仍保留；有限正生成与闭正生成分别使用，不合取、不互换。同一原 $\Omega,q,D,L,\circ$、全部经典中心、不等量子块与原不等正权、原菜单、$\mathcal K$、实际 $J_0=P^{\otimes2}$ 及先于 $D$ 固定的同一字面 $t_0$ 和 sigma 不变。全部实际有序联合及乘积、相关、零、奇异和次归一准备；整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F；原设备／端口／细记录／失败身份与完整失败输出、实际细化／分组／遗忘、具名原同数两侧支持返回及同数反向资料、每条原合法有限顺序、自适应和并行历史，均保留原量词与身份。新域中的数学 primitive 不增加为实际准备或操作。

## 403. 四颗两层原子恢复遗漏角度与准确盲方向

**定理 403.1（两层切向的完整裸残余）。** 设 $\mathcal C=\{s\in S:n_s=1\}$，$e_j$ 是经典块 $j\in\mathcal C$ 的中央 primitive。任意实双线性 $D$ 满足 $\mathsf F_{\rm zhtan}(E,D)$，当且仅当存在实数 $\gamma_s$（$n_s\ge2$）和任意向量 $v_j\in E$（$j\in\mathcal C$），使

$$
\boxed{D(a,b)=
\bigoplus_{s:n_s\ge2}\gamma_s\mathrm i[a_s,b_s]
+\sum_{j\in\mathcal C}a_jb_jv_j\qquad(a,b\in E).}
\tag{403.1}
$$

第一项在经典分量补零。$v_j=D(e_j,e_j)$ 可以指向整个 $E$，不预设留在经典源块。尤其

$$
D(a,u)=D(u,a)=\sum_{j\in\mathcal C}a_jv_j.
\tag{403.2}
$$

因此在 (402.1) 下，全域右单位、全域左单位、仅经典行 $D(e_j,u)=0$、全部 $v_j=0$，以及全原子二端关系 $\mathsf F_{\rm 2tan}$ 彼此等价。没有经典块时无需任何裸单位前件；空载体也包括在内。新内容是两层域的恢复及全部经典自对盲向量；交换子分类消费既有 398.2。

证明。先只恢复第一端，所有输出仍取在整个 $E$。固定量子块中的 primitive $e$，在含 $e$ 的任意数学二阶角 $W\simeq H_2(\mathbb C)$ 中，取角单位 $c$、补原子 $f=c-e$，以及相对于 $e,f$ 的横向 Pauli 元 $X,Y$。令

$$
q_+=(c+X)/2,\qquad q_-=(c-X)/2,\qquad q_Y=(c+Y)/2.
\tag{403.3}
$$

$f$ 与 $e$ 零重叠，三颗 $q$ 均与 $e$ 半重叠，且均是整个 $E$ 的原数学 primitive。直接用成熟矩阵坐标的线性恒等式，

$$
c=q_++q_-,\quad e=c-f,\quad
X=q_+-q_-,\quad Y=2q_Y-c,
\tag{403.4}
$$

可见 $f,q_+,q_-,q_Y$ 实张成整个 $W$。这些辅助选择只在证明中出现，不成为候选输入的选基、实际菜单或固定控制。对每颗保留原子 $r$，(402.1) 给 $D(e,r)\in E_{1/2}(e)$；第二槽实线性遂给

$$
D(e,W)\subseteq E_{1/2}(e).
\tag{403.5}
$$

这里不要求展开系数非负，也没有先假设 $D(W,W)\subseteq W$。任意同块目标 primitive $p\ne e$ 都落在 $e,p$ 的整个数学二阶支持角中，故 (403.5) 恢复 $D(e,p)$ 的第一切向。若 $p=e$，量子块内另选一颗正交补原子构成二阶角，仍用 (403.4) 恢复自对第一切向。

对固定量子 primitive $p$ 在第一槽使用同一构造；零／半重叠对在当前矩阵实现中对称，所以每颗辅助 $r$ 的有序对 $(r,p)$ 仍属原测试域，第二端条件给

$$
D(W,p)\subseteq E_{1/2}(p).
\tag{403.6}
$$

于是全部同块量子 primitive 对，包括自对，恢复完整双端切向。跨中心对本就在零层，其两半 Peirce 空间位于不同块，故整个输出为零；含经典端点的不同对同样为零。唯一未约束的 primitive 输入是 $(e_j,e_j)$：它不在零／半层，且不能在一维经典块中选上述二阶角。

现在精确定义残余并扣除，

$$
v_j=D(e_j,e_j),\qquad
R(a,b)=\sum_{j\in\mathcal C}a_jb_jv_j,\qquad D_0=D-R.
\tag{403.7}
$$

$R$ 在全部已测试原子对及全部量子原子对上均为零；$D_0(e_j,e_j)=0$。因此 $D_0$ 在整个原 primitive 对域满足 $\mathsf F_{\rm 2tan}$，现在才准确应用 398.2 的无单位前件分类，取得 (403.1) 的交换子项。不重证其块内系数刚性、全源／全输出因式分解或单位恢复。代入 $u$ 给 (403.2)，且 $D(e_j,u)=v_j$，从而得到所有单位等价。若全 $\mathsf F_{\rm 2tan}$ 成立，398.2 已使每个经典自对为零，故同样无残余。

反向，交换子项按 (398.6) 对全部原子对双端切向，残余在 (402.1) 的每个输入上为零，所以任意 $v_j\in E$ 都通过两层关系。空直和为零映射；纯经典载体只剩 (403.7) 的自对项，恰与其全部不同原子测试一致。∎

## 404. 原背景不变时的全域候选等价

**定理 404.1（两层入口与同一量子刻度）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，

$$
\begin{aligned}
B_*+\mathsf F_{\rm zhtan}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm 2tan}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm zhtan}(B_*)
&\Longleftrightarrow\mathsf C_{\rm 2tan}(B_*)
\Longleftrightarrow\mathsf C_{\rm prph}(B_*)
\Longleftrightarrow\mathsf C_{\rm fsph}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{404.1}
$$

对应仍是同一全部原数据、原执行和全部原合法有限历史上的恒等。

证明。前卷 246.1 在各自完整背景中供应静态复直和，母卷 30.1／67.3 独立供应原右单位。故 403.1 在每个原选中对象消去全部经典自对盲向量，恢复 398.1；反向仅限制其输入域。随后准确消费 399.2，沿同一原充分大实际身份参考 $i:E_A\hookrightarrow E_J$ 将 SC 向量与整个 Jordan 导子缺陷带回每个原对象。明确地，若 $\Delta_A(a;b,c)=D^A(a,b\circ c)-D^A(a,b)\circ c-b\circ D^A(a,c)$，则

$$
i(D^A(a,a))=D^J(i(a),i(a))=0,\qquad
i(\Delta_A(a;b,c))=\Delta_J(i(a);i(b),i(c))=0.
\tag{404.2}
$$

单射性给结论，零对象平凡，原 I 仍用既有有限 EJA 内性。运输的是向量与乘法缺陷，不是 $q$；不要求原嵌入保 primitive 或等距，不加直接 AP、共同参考指数或实际 $M_2$。证明中角内 primitive 的矩阵识别不转化为这种原嵌入前件。

裸局部 $\gamma_s$ 独立且可为零；共同 $\kappa\ge0$ 仍仅由完整背景经前卷 275.2 取得，保留 $\kappa=0$，再由同一原 sigma 的 $(1-\kappa)w_0/4=0$、$w_0>0$ 固定 $\kappa=1$。两份背景沿各自原 Z 或完整 $\mathsf Q$ 入口，不合取；闭准备的正延拓只对同一已固定原执行进行，不增添数学极限准备。没有重标原 $D$ 或更换 $t_0$，原复取向仍由同一 $D$ 决定。其余等价与既有完整 tagged-CP 满足族直接继承 399.2，含没有实际 $M_2$ 对象的子族。∎

## 405. 现有量子公理与全部原过程的完整回接

**定理 405.1（两层候选的消费者）。** 在 (402.2) 中，404.1 取得 399.2、384.1 的准确原入口，故如下全部对应成立：

| 本候选取得或保留的原接口 | 同一原结构上的结论 |
| --- | --- |
| 全域 I+SC、原 Jordan 乘法、同一原 $D$ 与 sigma | $\mathcal A_A=\bigoplus_sB(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$，$C_A=(\mathcal A_A)_+$；$a\cdot b=a\circ b-\mathrm iD(a,b)$，$D(a,b)=\mathrm i[a,b]/2$，$[D_a,D_b]=-[L_a,L_b]$，每个幂等元有 $D_c^2=-P_c/4$。 |
| 全部原准备与原 $g^0,q$，包含原不等正权 | $\rho_\alpha=B_Ax_\alpha$，$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=g_A^0(x_\alpha,y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$；$\tau_A(\rho_\alpha)=\alpha(u_A)$，零、奇异及次归一输入保持。 |
| 原 X 的 Jordan/$D$ 保持、有序交叉零、乘积张成及实际乘积准备分离 | 每个实际有序联合取得保留全部中心对的同取向普通复张量，全部原相关输入保留；不要求联合 $q$ 或比较运输因子化。 |
| 每个旧事件的全事件 R、同设备同记录旁接、原相关正锥、次幺性及完整效果和 | 原事件的 $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为 CP/TNI，原完整设备的事件和为 TP。 |
| 整个 AC、精确 $N_u$、X/Xs、原所选精确平方根词及其原相关执行 | 成功为 $\sqrt e\rho\sqrt e$，相关执行为 $(\sqrt e\otimes I)\Xi(\sqrt e\otimes I)$；原占用失败方向的整个输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其余原方向、中心、端口及相关执行仍取各自完整原失败映射。 |
| 实 Jordan F、同实现实际细记录、原分组／遗忘、具名同数两侧返回及反向资料 | $S_\ell=\operatorname{Ad}_{K_\ell}$，$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$，$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$，$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；原 $q_\ell>0$、零标签、失败与同数反向资料不变。 |
| 全部原准备、末端效果与每条原合法有限历史 | $\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$；包括空历史、顺序、按实际记录自适应、已供并行联合、细化／分组／实际遗忘、零／失败／返回／停止，只在原分母为正时取条件概率。 |

这里 $P_c=4(L_c-L_c^2)$、$\mathsf C_e(X)=eXe$，不与输入层用的 $Q_e$ 或整个共同支持投影混用。$\dagger_0$ 是原 $g^0$ 伴随，$B_A$ 是原比较运输，区别于背景 $B_*$；$g_A^0(x,y)=\tau_A((B_Ax)y)$ 与 $q_A(x,y)=\tau_A((\mathcal W_Ax)y)$ 的两套 Riesz 运输不互换。原成功数不归一成一，失败不压成概率，数学 Kraus 指标不变成实际细记录，同效果不替换旧设备自己的完整输出。

证明。404.1 在同一原签名上取得 399.2 的完整条件，逐项应用其表及 384.1 即得。全部消费者沿其原实际执行与合法历史，不由四颗数学辅助原子的线性展开供应额外准备、仪器或连线；闭背景的延拓也只作用于每个同一已固定原执行。这里是新两层入口对既有消费者的完整应用，不重新认领量子或过程重构。∎

## 406. 删去某一层或经典单位会漏下什么

**定理 406.1（两层域的准确裸删除边界）。** 即使保留双侧单位零，只留下半层或只留下零层，都不能恢复 (403.1) 的无残余正常形。若保留两层而删去裸单位，经典自对的整个输出仍可非零。以下见证均只分离裸局部条件，不承担完整 $B_*$ 或原 sigma 的独立性。

证明。删零层时，准确复用词卷 325.2 的数学 $H_2(\mathbb C)$ 映射

$$
D(a,b)=\left(\operatorname{Tr}(ab)-\tfrac12\operatorname{Tr}(a)\operatorname{Tr}(b)\right)I.
\tag{406.1}
$$

两侧单位均为零；所有半重叠 primitive 对的输出均为零，所以双端切向成立。正交 $e,p$ 却有 $D(e,p)=-I/2$，不属于任一端半 Peirce 空间，故零层不能由该半层和单位独自恢复。

删半层时，复用 395.1 的映射 $D(a,b)=\operatorname{Tr}(Zb)\mathrm i[Z,a]$，两侧单位均为零。第一端切向对全部 primitive 对成立；在 $H_2$ 的零层上 $p=I-e$，两端半 Peirce 空间相同，所以全部保留零层测试均通过。按 $[Z,X]=2\mathrm iY$ 的 Pauli 约定，取

$$
e=(I+X)/2,\qquad p=\bigl(I+(Y+Z)/\sqrt2\bigr)/2.
\tag{406.2}
$$

它们恰半重叠，且

$$
v=D(e,p)=-Y/\sqrt2,\qquad
p\circ v-v/2=-I/4\ne0.
\tag{406.3}
$$

所以被删半层确有失败对。这一计算不借非零自对输出区分两个端点。

最后取 $E=\mathbb R\oplus H_2(\mathbb C)$，定义 $D((t,a),(s,b))=(0,tsZ)$。所有零／半原子对的整个输出均为零，量子块的保留测试也非空；经典自对却输出 $(0,Z)$，同时 $D((1,0),u)=(0,Z)\ne0$。盲项甚至可以送往量子块，不能先按经典源将其投影回经典值域。这正是 403.1 的一个 $v_j$，不是额外残余类型。∎

## 407. 对径与赤道如何读回三实维小角

**定义 407.1（两层的几何及有限提升）。** 在同块数学二阶角中，以 $Z=e-f$，写任意 primitive 为 $p=(c+rX+sY+tZ)/2$、$r^2+s^2+t^2=1$。相对 $e$，零层是对径点 $f$，半层是赤道 $t=0$；(403.3) 取赤道上的 $X,-X,Y$ 三点。四颗珠子的线性包为整个四实维 $W=H_2(\mathbb C)$，迹一仿射包为 $c/2+W^0$，其中 $W^0=\{a\in W:\operatorname{Tr}a=0\}$ 是三实维无迹空间。展开系数可为负，它们是同一响应空间中的数学等式，不是实际凸准备或测量菜单。

所恢复的全双端切向几何仍沿 400.2：两原子的非平行 Bloch 方向给叉积交线，$\mathrm i[e,p]=-(r_e\times r_p)\cdot\sigma/2$。相等或对径时点态切面交仍可非零，关系输出为零来自整个双线性族及 398.2。相等对在原 $H_n$ 中的半 Peirce 空间实维为 $2(n-1)$，不能一律画作二阶角内的二维面。经典原子是没有赤道的孤立方向，正是其自对输入不能用四珠展开、须由原单位消去盲项的原因。

整个支持角不同于两颗非正交 primitive 经 Jordan 乘法自身生成的三实维子代数；输出的叉积方向可在后者之外。高阶块中的第三复支持位置可以把不同二阶角放入同一数学 $H_3(\mathbb C)$ 比较，第三复位置、三实 Bloch 坐标和物理三维互不替代。较大结构仍是全部中心上的复射影原子流形、相交 Peirce 角、复 Jordan–Lie 网及原实际有序联合的普通复张量，不增加实际量子比特、仪器、时钟或作用量。

**定义 407.2（准确的简化方向）。** 相对于 398.1，(402.1) 的原子输入域只保留两个重叠层。只要有量子块，它严格省去其它重叠及自对；例如在同一数学角内取 $p=|\sqrt3\,v/2+w/2\rangle\langle\sqrt3\,v/2+w/2|$、$e=|v\rangle\langle v|$，有 $Q_ep=3e/4$，原全域测试包含此对，新域不含。完整背景中的实际选中量子块可直接沿母卷 90.1 的原 $J_0$ 供应取得，不新增对象。

代价是显式识别原零／半输入层，且一般裸载体要保留经典单位条件；前一无单位全域定理 398.2 不因此改判。完整 $B_*$ 本来已有该单位来源，故 (404.1) 未增加完整背景假设。不声称独立信息最少、较低取得成本、含噪稳定或有限认证：四珠是每个数学角内的证明工具，全部对象、全部原子及半层方向仍连续量化。原比较尺、菜单与同一 sigma 也仍属于完整候选。

## 408. 新增桥的来源与尚未内生的供应

**定义 408.1（既有结果与新增推导）。** 仓内供应固定于 [`240a601cbb760a88bc923c2e61142db4535eb7bb`](https://github.com/the-omega-institute/trureturing/tree/240a601cbb760a88bc923c2e61142db4535eb7bb)。398.2 供应全双端切向的无单位分类，399.2 供应完整背景、实际参考与共同尺度，384.1 供应完整量子及过程消费者。403.1 的 $\texttt{repo-derived}$ 增量是：在两槽分别使用同一个二阶角的零／半四珠张成，恢复整个量子输入域；然后准确扣除所有经典自对的任意值域盲向量，才调用既有全域分类。它不重新认领交换子刚性或全域重构。

四颗秩一投影张成 Hermitian 角是成熟有限算子框架的中间工具，(403.3)–(403.4) 直接给出当前参数对应；不单列为新框架定理。母卷 88–93 已在每个半重叠输入对的角外读回槽中用 primitive 仿射基恢复遗漏标签，本条改的是二元关系的输入重叠域，两次线性展开不要求输出先局部化，且留下 (403.7) 的准确经典盲项，不能将两种域或结论混用。词卷 325–343 与本卷早先零／半支持候选保留各自整支持及迹前件，388 的存在谱比也保留另一份 $\mathsf G_{0h}$；这些均不作为 (403.1) 的额外前件。原子流形和半 Peirce 切空间的成熟几何来源沿 401.1 的 Nomura 原文 §3，不替代两层恢复证明。有限检索不承担历史优先权，也不声称产生新的完整模型类。

具体原 $\Omega$ 为什么供应完整 $B_*$、两层切向和同一原 sigma，仍须从其自身来源证明。词卷 356.1–356.4 的双记录原对象识别、Born 采用及两条有符号旧 $D$ 绑定等式仍各为其前件，不由角域减少推出；正配方或来源词律的表示也不自动完成这些采用。324.3 的物理时钟／Hamiltonian／共同作用量，独立成功支的共同完整仪器及控制／合法连线，每台旧同效果设备自身的完整输出校准，仍分别有未决来源义务。

## 409. 两层候选的完整直观表述

**定义 409.1（完整白话）。** 整座原世界仍完整留下：经典房间、大小不同的量子街区、原比较尺与单位来源、原菜单和同一张刻度单，全部真实有序联合及乘积、相关、零和次归一准备，每台旧设备、端口、细记录、完整失败出口、实际分组与遗忘、带原同一个成功数的两侧返回及反向资料、每条原合法有限顺序、自适应和并行历史，都保持原身份。这次不再逐个角度问两颗珠子的关系，只在完全错开或重叠一半时，要求同一根箭头同时贴着两颗珠子各自的原子表面。为什么其它角度能省？固定一颗量子珠子，在它的三实维小球里取一颗对径珠和三颗赤道珠，这四颗就能线性读回整个小屋里的任何方向；先在第二槽读回，第一端的贴面条件便跟过去，再固定第二端在第一槽做同样的事，另一端也贴住了，全角度与量子自对一并回来，过程中从没先把输出关进小屋。经典房间没有赤道，唯独自己问自己的那一格仍看不见，它甚至能向别的量子街区送出任意向量；原世界已有的单位平衡恰好逐格清掉这些盲项，没有经典房间时这份裸单位前件也能省。已有全角度定理随后把整份关系锁成每块同一个交换子系数；原实际充分大参考再把自守恒与整个乘法缺陷带回所有小对象，搬的是向量和乘法，不是比较尺。完整背景同步尺度时先保留全零分支，最后才由同一原刻度固定为一，原关系不重标，复乘法、两套正确运输的 Born 评价、全部中心及相关输入的实际张量、所有旧事件、精确平方根词与每个方向的完整失败、原细记录、同数双返回和全部合法历史便沿既有理论接回。反着删也看得见代价：只看赤道，正交处能藏一笔标量输出；只看对径，另一个端点在赤道处仍会偏离。省去的是需要输入的相对角位置，不是说整个连续原子世界已能有限认证或取得更便宜，也没有改掉原比较、原菜单和原单位来源；数学三维小球不变成物理三维、时钟或作用量。具体世界为什么内生满足两层规则、怎样绑定旧有符号关系、怎样供应共同完整仪器及每台旧设备自己的完整输出，仍须由自身来源补全。

## 追加锚 C128409（本行以下为增补区）

## 410. 高阶块只保留半重叠及跨中心零对

**定义 410.1（由原中心与阶数选出的二元域）。** 仍取 402.1 的有限复 Hermitian 直和、原 Jordan 乘法与同一实双线性 $D$。记 $c_s$ 为简单块 $H_{n_s}(\mathbb C)$ 的中央单位；每颗 primitive $e$ 所属的唯一简单块记为 $s(e)$。置

$$
\begin{aligned}
\mathcal H(E)&=\{(e,p):Q_ep=e/2\},\\
\mathcal Z_{\rm cen}(E)&=\{(e,p):s(e)\ne s(p)\},\\
\mathcal Z_2(E)&=\{(e,p):s(e)=s(p)=s,\ n_s=2,\ Q_ep=0\},\\
\mathcal T_h(E)&=\mathcal H(E)\cup\mathcal Z_{\rm cen}(E)\cup\mathcal Z_2(E),\\
\boxed{\mathsf F_{\rm htan}(E,D):\quad
D(e,p)\in E_{1/2}(e)\cap E_{1/2}(p)
\quad((e,p)\in\mathcal T_h(E)).}
\end{aligned}
\tag{410.1}
$$

各集合的变量都是整个 $E$ 的有序 primitive 对，$Q_e=2L_e^2-L_e$。半层自动同块；跨中心对都是零层。相对 (402.1)，这里只删去 $n_s\ge3$ 的同块零层，不删除二阶块零层、跨中心零层或任何半层。不输入自对、其它重叠、输出共同支持、$q$、SC、交替性、导子或新的单位律；原中心和块阶数是输入域选择的额外结构，不由测试结果反推。

**定义 410.2（唯一完整候选）。** 分别保留 402.2 的完整 $B$ 和完整 $\mathsf B_{\rm cl}$，任一记为 $B_*$；只在同一原 $\operatorname{rank}E_X>p_*=\operatorname{rank}E_P\ge2$ 域要求 (410.1)，记为 $\mathsf F_{\rm htan}^{>}$。置

$$
\boxed{\mathsf C_{\rm htan}(B_*)=B_*+\mathsf F_{\rm htan}^{>}+\sigma_{t_0}.}
\tag{410.2}
$$

两份准备背景分别使用，不合取。完整背景本来供应的原右单位保留；同一原 $\Omega,q,D,L,\circ$、全部中心、经典及不等块、原不等正权、菜单、$\mathcal K$、实际 $J_0$、原预选字面 $t_0$ 和 sigma 不变。全部实际有序联合及乘积、相关、零、奇异和次归一准备与原质量；整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F；原设备、端口、细记录、失败身份和完整失败输出、实际细化／分组／遗忘、具名同数两侧返回及同数反向资料、每条原合法有限顺序、自适应和并行历史，均保留原范围。数学中心、primitive 和角不增加实际准备、仪器或控制。

## 411. 半层超平面、原单位与两槽恢复

**定理 411.1（删去高阶内部零层的恢复桥）。** 在任意上述有限直和上，若同一原 $D$ 满足 $D(a,u)=0$ 对全部 $a\in E$ 成立，则

$$
\mathsf F_{\rm htan}(E,D)
\Longleftrightarrow\mathsf F_{\rm zhtan}(E,D)
\Longleftrightarrow\mathsf F_{\rm 2tan}(E,D)
\Longleftrightarrow
\left[\exists\gamma_s\in\mathbb R:\ \pi_sD(a,b)=\gamma_s\mathrm i[a_s,b_s]\right].
\tag{411.1}
$$

最后量词为全部 $a,b\in E$，非经典系数各自独立且允许零，经典输出为零。空载体、纯经典载体及混合二阶／高阶块均包含。新内容是第一个弱域恢复方向；全双端分类直接消费 398.2。

证明。仅证从 (410.1) 恢复全双端切向，其他方向由域限制及 398.2、403.1 给出。

跨中心 primitive 的两半 Peirce 空间位于不同简单理想，交为零，故 (410.1) 给整个输出 $D(e,p)=0$。在两个输入槽分别用 primitive 的实张成性，得 $D(E_s,E_t)=0$（$s\ne t$），没有先限制同源输出的值域。因此原全局右单位逐源变成

$$
D(a_s,c_s)=D(a_s,u)=0\qquad(a_s\in E_s).
\tag{411.2}
$$

经典 primitive $e_j=c_j$ 的自对亦为零；结合跨源零，含经典输入的全部输出为零。

固定 $n=n_s\ge3$ 块中的 primitive $e=|v\rangle\langle v|$。只在证明中采用其原数学矩阵实现，写

$$
\ell_e(b)=2\operatorname{Tr}(eb)-\operatorname{Tr}b,\qquad K_e=\ker\ell_e\subset E_s.
\tag{411.3}
$$

这里的迹是块规范迹，不替换原不等权比较。半伙伴的成熟线性张成在当前参数下如下：对每个 $v^\perp$ 中的单位向量 $w$ 和相位 $\theta$，令 $f=|w\rangle\langle w|$，

$$
p_{w,\theta}=\tfrac12\bigl(e+f+e^{\mathrm i\theta}|v\rangle\langle w|+e^{-\mathrm i\theta}|w\rangle\langle v|\bigr).
\tag{411.4}
$$

它们都是与 $e$ 半重叠的整个原块 primitive，故全在原测试域。相位相反的两项之和给 $e+f$，差及相位 $\pi/2$ 给 $v$ 与 $v^\perp$ 之间的全部 Hermitian 非对角分量。由 $v^\perp$ 内 primitive 实张成 $H_{n-1}(\mathbb C)$，这些和还张成全部 $\operatorname{Tr}(b_0)e+b_0$。相对于 $\mathbb Cv\oplus v^\perp$，它们恰是全部对角块满足 $b_{11}=\operatorname{Tr}b_0$ 的 Hermitian 矩阵，加上任意交叉分量。因此半伙伴的实线性包正好为 $K_e$。此处只是成熟秩一框架工具的显式使用，不另立新的张成定理。

关键是 $\ell_e(c_s)=2-n\ne0$。任意 $b\in E_s$ 有准确分解

$$
b=k+\frac{\ell_e(b)}{2-n}c_s,\qquad k\in K_e.
\tag{411.5}
$$

半层第一端切向、第二槽实线性与 (411.2) 遂给 $D(e,E_s)\subseteq E_{1/2}(e)$。输出始终在整个 $E$ 中，没有预设 $D(E_s,E_s)\subseteq E_s$。在二阶块，直接使用既有 (403.3)–(403.5) 的零／半四珠展开恢复同一第一端结论；跨源已为零，经典输入也为零。于是对每个固定 $b\in E$，实线性映射 $A_b:a\mapsto D(a,b)$ 对整个 $E$ 的每颗 primitive $e$ 均满足 $A_be\in E_{1/2}(e)$。

现在准确使用 (398.3) 的成熟谱框架机制：任取原正 Frobenius 型 $q$，对每个完整谱框架 $(f_i)$ 都有 $q(f_i,A_bf_j)=0$。每颗 primitive 可入框，同框求和及 primitive 张成性给 $A_bu=0$。故

$$
D(u,b)=0\quad(b\in E),\qquad D(c_s,b_s)=0\quad(b_s\in E_s),
\tag{411.6}
$$

后一式再用跨源零。到这一步才取得左单位，没有循环使用全双端分类或先假设第二端已恢复。

最后固定高阶块中的 primitive $p$，在第一槽以 $K_p+\mathbb Rc_s$ 重复 (411.3)–(411.5)。半层第二端切向与刚取得的左单位给 $D(E_s,p)\subseteq E_{1/2}(p)$。二阶块直接使用 (403.6)，经典及跨源仍为零。全部有序 primitive 对，包括量子自对和删去的高阶正交对，因而恢复两个端点对同一输出的切向。此时才调用 398.2，取得 (411.1) 及双单位、SC、交替性与完整逐块正常形。空载体唯一映射为零，纯经典情形已由 (411.2) 逐格处理。∎

## 412. 不变完整背景中的量子与过程对应

**定理 412.1（同一原刻度上的完整理论）。** 分别在完整 $B$ 与完整 $\mathsf B_{\rm cl}$ 中，

$$
\begin{aligned}
B_*+\mathsf F_{\rm htan}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm zhtan}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\rm htan}(B_*)&\Longleftrightarrow\mathsf C_{\rm zhtan}(B_*)
\Longleftrightarrow\mathsf C_{\rm 2tan}(B_*)
\Longleftrightarrow\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{412.1}
$$

对应在全部原数据、原执行和每条原合法有限历史上都是恒等。

证明。前卷 246.1 分别供应静态复直和；母卷 30.1／67.3 分别独立供应原右单位。故在每个原选中对象准确应用 411.1，再消费 404.1。其实际充分大原身份参考仍由原合同供应；同一含幺 Jordan／$D$ 单射只运输原 SC 向量和整个 Jordan 导子缺陷，按 (404.2) 带回全部小对象、经典块及旧输出。不运输 $q$，不要求保 primitive 或等距，不增加 direct AP、共同参考指数或实际 $M_2$。两份背景仍走各自 Z／完整 $\mathsf Q$ 入口；闭背景只对同一固定执行作正延拓，不添加极限准备。

局部系数独立且可零；完整背景才由前卷 275.2 取得共同 $\kappa\ge0$，保留零分支。随后同一原 sigma 的 $(1-\kappa)w_0/4=0$、$w_0>0$ 固定 $\kappa=1$，原 $D$ 不重标、$t_0$ 不更换。405.1 的全部消费者现已在同一原签名具备前件，准确应用如下。

| 已取得或保留的接口 | 原理论的完整后果 |
| --- | --- |
| 原 Jordan 乘法、I+SC、同一 $D$ 及 sigma | $\mathcal A_A=\bigoplus_sB(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$、$C_A=(\mathcal A_A)_+$；$a\cdot b=a\circ b-\mathrm iD(a,b)$、$D(a,b)=\mathrm i[a,b]/2$、$[D_a,D_b]=-[L_a,L_b]$、$D_c^2=-P_c/4$。 |
| 全部原准备、原 $g^0,q$ 及原质量 | $\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=g_A^0(x_\alpha,y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$，$\tau_A(\rho_\alpha)=\alpha(u_A)$；两套 Riesz 不互换，零、奇异及次归一输入保留。 |
| 原 X 的 Jordan／$D$ 嵌入、交叉零、乘积张成与实际乘积准备 | 所有实际有序联合及全部中心对取得同取向普通复张量，全部原相关输入保留；不要求联合 $q$ 或比较运输因子化。 |
| 每个旧事件自身的全事件 R、同设备同记录旁接、完整相关正锥、次幺性与完整效果和 | $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为原事件的 CP/TNI 映射，原完整设备的事件和为 TP；$\dagger_0$ 是原 $g^0$ 伴随。 |
| 整个 AC、精确 $N_u$、X/Xs、原精确平方根词及同记录相关执行 | 原成功为 $\sqrt e\rho\sqrt e$；相关执行为 $(\sqrt e\otimes I)\Xi(\sqrt e\otimes I)$；占用失败方向的整个输出为 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其余方向、中心、端口及相关执行保持原完整失败映射。 |
| 实 Jordan F、实际细记录、实际分组／遗忘、原同数两侧返回及同数反向资料 | $S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$、$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；保留原 $q_\ell>0$、零标签及完整失败。 |
| 原准备、原末端效果与全部原合法有限历史 | $\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$；覆盖空历史、顺序、自适应、已供并行、细化／分组／实际遗忘、零／失败／返回／停止，仅在原分母正时条件化。 |

这里 $P_c=4(L_c-L_c^2)$、$\mathsf C_e(X)=eXe$，不与输入层的 $Q_e$ 混用；$B_A$ 为原比较运输，区别于背景 $B_*$。数学 Kraus 指标不取得实际细记录身份，同效果不替换旧设备自身完整输出。整个表是新域入口对 405.1 的应用，不另报矩阵、Born、张量、过程或历史重构；原 tagged-CP 满足族及无实际 $M_2$ 的子族仍直接继承。∎

## 413. 哪些零对可省，哪些仍能藏住输出

**定理 413.1（新域的准确裸删除边界）。** 高阶同块零层在 411.1 的原右单位下确实冗余；跨中心零层、二阶内部零层及半层则不能在所有有限复直和上一概删除。原右单位在新的裸局部桥中也不能一概省略。以下只分离裸条件，不声称完整 $B_*+\sigma_{t_0}$ 上的逐项独立性。

证明。高阶内部零层由 411.1 恢复，不为它编造必要性见证。若删跨中心零层，取 $E=H_3(\mathbb C)\oplus H_3(\mathbb C)$、$u=(I_3,I_3)$，并令

$$
\begin{aligned}
\beta(a,b)&=\sum_{j=1}^2\left[\operatorname{Tr}(a_jb_j)-\tfrac12\operatorname{Tr}(a_j)\operatorname{Tr}(b_j)\right]\\
&\quad+\tfrac16\left[\operatorname{Tr}(a_1)\operatorname{Tr}(b_2)+\operatorname{Tr}(a_2)\operatorname{Tr}(b_1)\right],\\
D(a,b)&=\beta(a,b)u.
\end{aligned}
\tag{413.1}
$$

它实双线性且对称。代入 $u$，每个块的系数为 $1-3/2+3/6=0$，所以双侧单位均为零。同块半重叠 primitive 给 $\beta=1/2-1/2=0$，全部保留测试通过；没有二阶块。跨中心 primitive 对却给 $\beta=1/6$，其输出 $u/6$ 不在任一端半 Peirce 空间。两个输入块各自的单位抵消依赖被删耦合，故不能直接从全局单位宣称逐块单位。

删二阶内部零层时，直接用既有 (406.1)：$H_2$ 上双单位及全部半层成立，正交对输出 $-I_2/2$。删半层时，直接用 406.1 已算清的 $D(a,b)=\operatorname{Tr}(Zb)\mathrm i[Z,a]$；在单个 $H_2$ 中剩余域只有正交对，双单位及所有保留测试成立，但 (406.2)–(406.3) 的半对第二端失败。这两项仅消费旧见证。

删裸右单位时，单个 $H_3$ 上取

$$
D(a,b)=\left[\operatorname{Tr}(ab)-\tfrac12\operatorname{Tr}(a)\operatorname{Tr}(b)\right]I_3.
\tag{413.2}
$$

新域仅含半层，全部输出零；但 $D(a,I_3)=-\operatorname{Tr}(a)I_3/2$，正交 primitive 对输出 $-I_3/2$。此见证把同一成熟迹型的二阶退化改为高阶单位缺口；不暗称原完整背景的单位供应可以删除。∎

## 414. 赤道的余维一与第三复位置

**定义 414.1（有限提升的几何）。** 在数学 $H_2$ 角 $W$ 中，固定 $e=(c+Z)/2$，半伙伴为 $p=(c+rX+sY)/2$、$r^2+s^2=1$。其线性包为 $\operatorname{span}_{\mathbb R}\{c,X,Y\}$，不是整个四实维 $W$；它已经含角单位 $c$，故再加 $c$ 不能恢复缺失的 $Z$。这正是 (411.5) 在 $n=2$ 分母为零的退化，原二阶对径测试仍须保留。

在 $H_n$ 中，半伙伴张成的 $K_e$ 仍只有余维一；不过块单位的 $\ell_e$ 读数为 $2-n$，高阶时它穿过这张超平面，原单位零输出遂补齐最后方向。以三个正交复位置 $e,f,g$ 的数学 $H_3$ 角单位 $c=e+f+g$ 为例，半伙伴两两相加给 $e+f$ 与 $e+g$，并有

$$
e=(e+f)+(e+g)-c.
\tag{414.1}
$$

这展示第三个复位置怎样解除二阶退化；只有当该三阶角就是整个块时，$D(a,c)=0$ 才由已证块单位直接提供。高阶块内的任意三阶子角不自动有独立单位律，完整证明始终用整个 $c_s$ 与 (411.5)。这些带符号线性组合是数学响应等式，不是新的实际混合或控制。

恢复后的三实维 Bloch 几何仍为 400.2、407.1 的两端切面与叉积方向，较大结构为复射影原子流形、相交 Peirce 角、复 Jordan–Lie 网及原实际有序复张量。第三复 Hilbert 位置、三实 Bloch 坐标和物理三维不同；不由有限角供应实际 $H_3$、实际 $M_2$、时钟、Hamiltonian 或作用量。

**定义 414.2（简化的精确偏序）。** $\mathcal T_h(E)\subseteq\mathcal Z_h(E)$，差集恰为高阶块内的全部正交 primitive 对。存在 $n_s\ge3$ 的块时包含严格；全部块阶数至多二时两域相同，空或纯经典情况也不冒称严格减少。简化仅指背景不变时该测试域的包含关系；显式分辨中心和块阶数是其代价。不主张独立信息最少、有限认证、噪声稳定、更低取得成本或新的完整模型类，全半层仍连续量化。

## 415. 新增桥、既有工具与来源适用性

**定义 415.1（数学归属）。** 仓内供应固定于公开修订 [`b96eecce7d2050357046126e9f4ff894ffb02ac3`](https://github.com/the-omega-institute/trureturing/tree/b96eecce7d2050357046126e9f4ff894ffb02ac3)。本批 $\texttt{repo-derived}$ 增量是：跨中心测试先使原单位逐块可用，半层超平面加块单位只恢复第一端，再经完整谱框架恢复左单位，最后在另一槽补齐第二端，从而删除所有高阶内部零测试；以及 (413.1) 对跨中心删除的全高阶双单位障碍。398.2 的分类、403.1 的二阶恢复与经典盲项、404.1–405.1 的完整消费者全部复用，不重新认领。

半伙伴的线性张成、谱框架和 Peirce 切空间都是中间工具。配平续卷 155–159 已给三重叠层的张成与切口配平应用，母卷 88–93 已给角外读回槽的有限框架，词卷 (325.6)、(334.4) 已利用 $2-n_s$ 因子恢复高阶迹量；本批不重报这些成熟或仓内工具。它们各自保留配平、整输出支持或迹条件，不能不带前件当作当前两槽弱域桥。原子流形的切空间文献仍取 401.1 的 Nomura §3，谱框架机制准确沿 (398.3)。有限检索没有取得优先权或穷尽性结论；未把固定转移概率保留映射的文献结论冒充本题双线性切向定理。

**定义 415.2（最新来源的准确边界）。** [C139 来源比较卷 §§32–35](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md#32有限标记共轭关系下降与复型选择) 已在有限 EJA 上用标签核下降及有限混合相位构造新关系 $A$ 并选择复型；其 (32.7)–(32.8) 没有识别预先固定的旧 $D$。同文 32.1a 在保留 CountRead 全部未来的原共同切口证明完整响应商无穷维，所以其有限采用前件在该切口不成立，不能把有限模型当作这个原切口的完整来源。这里的条件定理保留其自身完整 $B_*$，也不据此宣称已为原共同切口供应该背景；其它全未来记忆表示不在该有限性排除内。

[FIB 原子相干续卷 XI §§57–58](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md#57-原九十号正字的内部相对相位与完整报告) 将条纹绑定到原正字并给出同载体裸投影协议的全输入合并障碍，但明确以复数、Born、酉及保留读合同为前件，不供应本条旧 $D$ 的有符号绑定。这些来源结论与 R5 正配方、RRO 来源词律均不自动满足词卷 356.1–356.4 的原对象识别、Born 采用和两条旧 $D$ 等式。具体 $\Omega$ 满足完整 $B_*$、(410.1) 与同一 sigma 仍须来源证明；324.3 的物理钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器和原控制／连线、各旧同效果设备自身完整输出校准仍分别保留。

## 416. 更小二元域的完整直观表述

**定义 416.1（完整白话）。** 整座原世界和上一条候选一样完整保留：经典房间、二阶和更大街区、原比较尺与单位来源、同一张预选刻度单，所有真实联合、相关及零和次归一准备，每台旧设备、端口、细记录、完整失败出口、实际分组遗忘、带同一个原成功数的两侧返回及反向资料，以及全部合法有限历史，都保持原身份。新规则继续要求同一根关系箭头同时贴着两颗珠子的原子表面，但在三阶及以上街区只问重叠一半的珠子，完全错开的内部珠子不再逐对问；不同街区之间的零对和二阶小球里的对径对仍保留。为什么能省？固定一颗珠子，所有半重叠伙伴能读回一张只缺一个方向的平板。二阶小球的单位已经躺在板里，补不了缺口；多出第三个复位置后，整个街区的单位穿过这张板，原世界已有的单位平衡便补回最后方向。跨街区的零对先挡住暗中串账，才能把这份单位平衡分到各街区；先在一个输入槽补齐贴面条件，再由全部谱框架恢复另一侧单位，最后补齐另一个槽，所有遗漏角度和自对便一起回来，过程中没有预先把输出关在某个小角。已有定理随后把关系锁成逐块交换子，原实际参考把整个乘法缺陷带回所有小对象，完整背景同步尺度时先保留零分支，再由同一张原刻度固定为一；复乘法、保质量且区分两套运输的 Born 评价、全部中心及相关输入的实际张量、所有旧事件、平方根成功词与完整失败、原细记录、同数双返回和每条原合法历史，都沿原理论接回。反着删也清楚：连跨街区零对都删掉，两个三阶街区就能相互抵账并藏住整向量输出；二阶对径也删掉，赤道仍看不见一笔标量。省的是高阶街区内部一层相对位置，代价是要识别原中心与块阶数，并不保证取得更便宜或有限认证；数学三维小球及第三个复位置也没有变成物理三维、时钟或仪器。最新有限相位构造没有替换这根旧关系，CountRead 的全未来还阻止把那个共同原切口硬塞进有限模型；具体来源如何满足原背景和新关系、怎样绑定旧有符号 $D$ 并供应真实时钟、共同完整仪器和各旧设备完整输出，仍须继续从来源证明。

## 追加锚 C128416（本行以下为增补区）

## 417. 有限谱星上的双向贴面关系

**定义 417.1（先于原 D 的有限表）。** 固定 410.1 的有限复 Hermitian 直和 $E=\bigoplus_sH_{n_s}(\mathbb C)$，块单位为 $c_s$。这里只使用既有静态 Jordan 坐标，不先识别原 $D$。在每块取标准 primitive 实基

$$
\mathcal B_n=\{P_{v_j}\}_j\ \cup\
\{P_{(v_j+v_k)/\sqrt2},P_{(v_j+\mathrm i v_k)/\sqrt2}:j<k\},
\qquad |\mathcal B_n|=n^2,\quad P_x=|x\rangle\langle x|.
\tag{417.1}
$$

按[配平续卷定义 87.1](AURIC_C128_NATIVE_CUT_BALANCE_CONTINUATION.md#87-每个原对象的有限谱覆盖)，对这份基的每个 $b_i+b_j$、$i\le j$，选择一个对角化该和的完整块内谱框架，令 $\mathcal P_s$ 为所选框架之并。它包含 $\mathcal B_{n_s}$，张成整个块，并有

$$
|\mathcal P_s|\le n_s\,\frac{n_s^2(n_s^2+1)}2.
\tag{417.2}
$$

对于 $n_s\ge2$ 和每个 $e=P_v\in\mathcal P_s$，在 $v^\perp$ 上选择一份 (417.1) 型 primitive 实基 $\mathcal B_e^\perp$，并给其每个 $f=P_{w_f}$ 选择单位代表 $w_f$。置 $\zeta=e^{2\pi\mathrm i/3}$，定义有限半伙伴

$$
\mathcal H_e=\left\{
p_{e,f,r}=\tfrac12P_{\,v+\zeta^rw_f}:
f\in\mathcal B_e^\perp,\ r=0,1,2
\right\},\qquad
|\mathcal H_e|\le3(n_s-1)^2.
\tag{417.3}
$$

$P_x$ 对未归一向量仍表示外积，故 $p_{e,f,r}$ 的迹为一，且 $Q_ep_{e,f,r}=e/2$。在 $n_s\ge2$ 时令

$$
\mathcal S_s=\{(e,p):e\in\mathcal P_s,\ p\in\mathcal H_e\}
\ \cup\
\{(e,c_s-e):e\in\mathcal P_s,\ n_s=2\}.
\tag{417.4}
$$

第二项只用于二阶块；一阶块取空星表。所有坐标、框架、补空间基及向量相位均在查看 $D$ 前固定。它们是原数学响应空间中的有限选点，不增加实际制备、相位控制、读口或对象。不同容许选择均适用下述恢复定理。

**定义 417.2（唯一有限关系）。** 对同一原实双线性 $D:E\times E\to E$ 要求

$$
\boxed{\begin{aligned}
&D(e,p),\ D(p,e)\in E_{1/2}(e)
&&((e,p)\in\mathcal S_s,\ n_s\ge2),\\
&D(b_s,b_t)=0\quad\hbox{在整个 }E\hbox{ 中}
&&(b_s\in\mathcal B_{n_s},\ b_t\in\mathcal B_{n_t},\ s\ne t).
\end{aligned}}
\tag{417.5}
$$

记为 $\mathsf F_{\mathcal S}$。星心是 $e$：两条有向输出分别贴着同一星心的切面，不预设 $D(p,e)=-D(e,p)$，也不预设每条输出在伙伴 $p$ 的切面。跨中心式保留两个输入次序；它恰是原跨中心双端切向的零交集写法。除此之外不输入输出支持、交替性、SC、导子、左单位、$q$ 读回或新的右单位。右单位是否可用，仍由恢复定理或完整背景明确供应。

## 418. 有限半伙伴怎样恢复两槽完整切场

**定理 418.1（有限表的全输出恢复桥）。** 若同一 $D$ 有原右单位 $D(a,u)=0$，则对每份定义 417.1 的容许表，

$$
\mathsf F_{\mathcal S}
\ \Longleftrightarrow\
\mathsf F_{\rm htan}
\ \Longleftrightarrow\
\mathsf F_{\rm 2tan}
\ \Longleftrightarrow\
\left[\exists\gamma_s\in\mathbb R:
\pi_sD(a,b)=\gamma_s\mathrm i[a_s,b_s]\quad(a,b\in E)\right].
\tag{418.1}
$$

非经典系数独立且允许零，经典输出为零。后面两个等价沿 411.1、398.2 复用；新增方向是有限星心贴面恢复完整双端切向，不重新分类双线性作用。

证明。跨中心基张成及两槽双线性首先给 $D(E_s,E_t)=0$（$s\ne t$），所以原右单位给 $D(a_s,c_s)=0$。一阶块中 $D(c_s,c_s)=0$，故含经典输入的全部输出为零。此时尚未假定同源输入的输出留在源块。

固定非经典星心 $e=P_v$。写 $A_f=|v\rangle\langle w_f|$、$X_f=A_f+A_f^*$、$Y_f=\mathrm i(A_f^*-A_f)$，$\theta_r=2\pi r/3$。三相展开为

$$
\begin{aligned}
p_{e,f,r}&=\tfrac12(e+f+\cos\theta_rX_f+\sin\theta_rY_f),\\
e+f&=\tfrac23\sum_{r=0}^2p_{e,f,r},\qquad
X_f=\tfrac43\sum_{r=0}^2\cos\theta_r\,p_{e,f,r},\qquad
Y_f=\tfrac43\sum_{r=0}^2\sin\theta_r\,p_{e,f,r}.
\end{aligned}
\tag{418.2}
$$

补空间 primitive 基张成全部 $b_0\in H_{n_s-1}$，故第一组和张成 $\operatorname{Tr}(b_0)e+b_0$；该基包含补空间正交基投影，后两组给全部 $v$ 与 $v^\perp$ 之间的实、虚交叉分量。因此这份明确有限 $\mathcal H_e$ 的实线性包恰为 411.3 的 $K_e=\ker\ell_e$，$\ell_e(b)=2\operatorname{Tr}(eb)-\operatorname{Tr}b$。这里复用半伙伴超平面的既有机制，(418.2) 只给其有限供应表。

当 $n_s\ge3$，$\ell_e(c_s)=2-n_s\ne0$，故 $K_e+\mathbb Rc_s=E_s$。由 (417.5) 的 $D(e,p)$ 一行、第二槽线性和原块右单位，得 $D(e,E_s)\subseteq E_{1/2}(e)$。当 $n_s=2$，$K_e$ 含 $c_s$，而 $\ell_e(c_s-e)=-1$；(417.4) 的补元和相同线性延拓给同一结论。它对每个 $e\in\mathcal P_s$ 成立。$\mathcal P_s$ 张成整个输入块且 $E_{1/2}(e)\subseteq E_s$，此刻才得到

$$
D(E_s,E_s)\subseteq E_s.
\tag{418.3}
$$

固定 $b_s\in E_s$，令 $T(a_s)=D(a_s,b_s)$。还不能直接调用要求 $Tc_s=0$ 的有限框架引理。先对任意 $e\in\mathcal P_s$，取含它的所选完整框架 $\mathcal F$。每个 $f\in\mathcal F$ 都已满足 $Tf\in E_{1/2}(f)$，所以 $\operatorname{Tr}(eTf)=0$，包括 $f=e$。对框架求和得 $\operatorname{Tr}(eTc_s)=0$。由 $\mathcal P_s$ 张成及迹配对非退化，$Tc_s=0$。这一步的读数覆盖整个输出，依据正是已证 (418.3)，没有遗漏来自低阶源的角外或其他中心残余。

现在准确应用[配平续卷引理 88.1](AURIC_C128_NATIVE_CUT_BALANCE_CONTINUATION.md#88-谱框架的二次极化与全域恢复)：同一线性 $T$ 在原 $\mathcal P_s$ 上切向，且 $Tc_s=0$，故为整个块的 Jordan 导子。因此第一端切向已对全部 primitive、全部第二输入恢复；并有块左单位 $D(c_s,b_s)=0$，再由跨源零得到全左单位 $D(u,b)=0$。

回到 (417.5) 的另一条有向输出。对每个星心 $e\in\mathcal P_s$，$D(p,e)\in E_{1/2}(e)$ 沿 $\mathcal H_e$ 在第一槽延拓。高阶块用刚证的左单位补齐 $c_s$；二阶块用同表中的 $c_s-e$ 补齐缺向，得 $D(E_s,e)\subseteq E_{1/2}(e)$。固定任意 $a_s$，映射 $b_s\mapsto D(a_s,b_s)$ 本来就有原右单位，故再次准确应用同一有限框架引理，得到第二槽的全导子律及全部 primitive 第二端切向。跨源与经典已为零，全 $\mathsf F_{\rm 2tan}$ 齐备，此时才调用 398.2。

反向由已有正常形限制到 (417.5)：交换子在每个幂等输入端点都切向，跨源零。空载体的唯一映射为零；纯经典已在首步处理。证明不更改原不等正块权，也不需要输运 primitive、角、迹或 $q$ 的额外性质。∎

## 419. 同一完整背景与原量子公理的全部接合

**定义 419.1（唯一完整候选）。** 分别保持 410.2 的完整 $B$ 和完整 $\mathsf B_{\rm cl}$，任一记作 $B_*$，仍只在同一原 $\operatorname{rank}E_X>p_*=\operatorname{rank}E_P\ge2$ 域选表并施加 (417.5)，记为 $\mathsf F_{\mathcal S}^{>}$。定义

$$
\boxed{\mathsf C_{\mathcal S}(B_*)=
B_*+\mathsf F_{\mathcal S}^{>}+\sigma_{t_0}.}
\tag{419.1}
$$

精确有限正生成与闭正生成分别保留，数学极限态不新增为实际准备。同一原 $\Omega,D,q,L,\circ$、全部经典中心、不等块及不等正权、原规范迹、菜单、$\mathcal K$、实际 $J_0$ 和事先固定的字面 $t_0,\sigma_{t_0}$ 不变。所有实际有序联合、乘积与相关准备，零、奇异和次归一输入及原质量均保留；整个 AC、精确 $N_u$、X/Xs、全事件 R、实 Jordan F，全部旧设备、端口、细记录、失败身份及完整失败输出，实际细化、分组和遗忘，具名同一原成功数的两侧返回及同数反向资料，每条原合法有限顺序、自适应和并行历史均不缩小。

**定理 419.2（原数据和原历史上的恒等对应）。** 对每份容许有限表，两份完整背景分别有

$$
\begin{aligned}
B_*+\mathsf F_{\mathcal S}^{>}
&\Longleftrightarrow B_*+\mathsf F_{\rm htan}^{>}
\Longleftrightarrow B_*+\mathrm I+\mathrm{SC},\\
\mathsf C_{\mathcal S}(B_*)&\Longleftrightarrow
\mathsf C_{\rm htan}(B_*)\Longleftrightarrow
\mathsf C_{\rm support}(B_*).
\end{aligned}
\tag{419.2}
$$

证明。246.1 在两背景分别给静态复直和，母卷 30.1／67.3 独立给原右单位。故每个选中对象可用 418.1；其后直接应用 412.1，既有实际充分大身份参考只运输 SC 向量和整个 Jordan 导子缺陷，不要求保 primitive、等距或 $q$，不添加直接 $AP$、共同参考指数或实际 $M_2$。局部 $\gamma_s$ 独立含零；完整背景沿 275.2 同步为共同 $\kappa\ge0$，保留零分支，再由同一原 sigma 的 $(1-\kappa)w_0/4=0$、$w_0>0$ 固定 $\kappa=1$。以下准确复用 412.1／405.1 的完整消费者，不另认领量子重构。

| 同一原接口 | 对应的完整量子结论 |
| --- | --- |
| 原 Jordan、原 I+SC 与同一 sigma | $\mathcal A_A=\bigoplus_sB(H_{A,s})$，$E_A=(\mathcal A_A)_{\rm sa}$，原正锥为 $(\mathcal A_A)_+$；$a\cdot b=a\circ b-\mathrm iD(a,b)$、$D(a,b)=\mathrm i[a,b]/2$、$[D_a,D_b]=-[L_a,L_b]$，每个幂等元 $c$ 有 $D_c^2=-P_c/4$。 |
| 全部原准备、原质量及分别保留的 $g^0,q$ | $\rho_\alpha=B_Ax_\alpha$、$\widehat x_\alpha=\mathcal W_A^{-1}\rho_\alpha$，$\alpha(y)=g_A^0(x_\alpha,y)=\tau_A(\rho_\alpha y)=q_A(\widehat x_\alpha,y)$，$\tau_A(\rho_\alpha)=\alpha(u_A)$；零和次归一质量不归一化抹去。 |
| 原有序 X、实际乘积及全部相关输入 | 全部中心对的同取向普通复张量；不要求联合 $q$ 或比较运输因子化，不增加实际纠缠准备。 |
| 每个旧事件自己的全事件 R、同实现同记录旁接及完整相关正锥 | $\Phi_f=B_BT_f^{\dagger_0}B_A^{-1}$ 为 CP/TNI；原完整设备事件和 TP，$\dagger_0$ 仍为原 $g^0$ 伴随。 |
| 整个 AC、精确 $N_u$、Xs、原精确平方根词和合法连线 | 所选成功支 $\sqrt e\,\rho\sqrt e$ 及其同记录相关执行；占用失败方向的整个 $\sqrt{I-e}\rho\sqrt{I-e}\otimes\Psi_\ell(p_1)$，其他方向、中心、端口的完整失败映射保持原身份。 |
| 原实 F、细记录、实际分组遗忘、同数两侧返回及反向资料 | $S_\ell=\operatorname{Ad}_{K_\ell}$、$U_\ell=q_\ell\operatorname{Ad}_{K_\ell^+}$，$U_\ell S_\ell=q_\ell\mathsf C_{e_\ell}$、$S_\ell U_\ell=q_\ell\mathsf C_{h_\ell}$、$U_\ell=\mathsf C_{e_\ell}U_\ell\mathsf C_{h_\ell}$；同一原 $q_\ell>0$、零标签和完整失败保留。 |
| 每份原准备与每条原合法有限历史 | $\alpha(T_{f_1}\cdots T_{f_m}w)=\tau_{A_m}(w\,\Phi_{f_m}\cdots\Phi_{f_1}(\rho_\alpha))$；含空历史、顺序、自适应、已供并行、细化分组、实际遗忘、零、失败、返回、停止，仅在原分母正时条件化。 |

$P_c=4(L_c-L_c^2)$、$\mathsf C_e(X)=eXe$，不与原子输入的 $Q_e$ 混用；$B_A$ 不是背景 $B_*$。数学 Kraus 指标不取得实际细记录身份，同效果不替换任何旧设备自身完整输出。∎

## 420. 有限性、严格删减与反向删除的边界

**命题 420.1（删去的是原问句）。** 把 410.1 的每条双端条件分为“有序输入、所读端点”的两个标签。星表的两条问句分别取标签 $(e,p;e)$ 和 $(p,e;e)$；跨中心整输出零与原该有序对的两端切向等价。因此新表只保留原 $\mathcal T_h(E)$ 上的有限问句，不增加其它交叠、自对、归一化或新的向量等式。忽略重复，有向输入数有上界

$$
M(E)\le
\sum_{s:n_s\ge2}\left[6|\mathcal P_s|(n_s-1)^2+
2\mathbf1_{\{n_s=2\}}|\mathcal P_s|\right]
+\sum_{s\ne t}n_s^2n_t^2.
\tag{420.1}
$$

只要 $E$ 含非经典块，原半层有无穷多不同有序输入，这张有限表必遗漏原问句；纯经典时两域相同，空情形也不冒称严格。每份完整 $B_*$ 的实际 $J_0=P^{\otimes2}$ 有一个 $H_{m^2}$ 块、$m\ge2$，且总秩 $p_*^2>p_*$，沿母卷 90.1 直接给出全原选中网的严格删减。没有假设原 $P$ 的全部块非经典，也没有假设所有参考块都高阶。

证明。域包含由每个半伙伴和二阶补元的精确交叠直接给出；跨中心两个半 Peirce 空间交零，且两槽实基张成。有限上界是逐星、逐块及跨中心基对的计数，可能远未尖锐。固定两条正交复方向，$p_\theta=P_{(v_1+e^{\mathrm i\theta}v_2)/\sqrt2}$ 给无穷多个不同半伙伴，有限表不能全部包含；实际平方的供应直接复用母卷 90.1。∎

**命题 420.2（不把有限性误当逐点最小）。** 统一删除二阶补元的裸局部关系不足以一般恢复完整切场；在完整背景中，整张有限表亦不能无条件删除。以下不声称单点最小性。

证明。若在全部有限表里统一删掉二阶补元，直接取 406.1 的 $H_2$ 双单位迹型例，全部半层输出为零而 $D(e,I-e)=-I/2$。它通过任何所选半伙伴星，却不是完整切场；这只分离裸前件，不是完整 $B_*+\sigma_{t_0}$ 的反模型。高阶单位补向和跨中心供应的必要角色仍沿 413.1 的裸删除例，不重新包装旧见证。

在完整背景中整张新表不能全删。400.1 已有保完整 $B$、完整 $\mathsf B_{\rm cl}$ 和同一任意预选 sigma、却违反全域 I+SC 的完整模型；由 419.2，它必违反某个新有限问句。该结论不指定是哪一个点，不证明每点不可删，不证明三相或双向星在所有协议中的最小性。∎

## 421. 三相赤道、有限谱网与更大的几何

**定义 421.1（有限三维提升）。** 固定星心 $e=P_v$ 和一个补原子 $f=P_w$，它们的数学二阶角中，以 $c=e+f$、$Z=e-f$、(418.2) 的 $X,Y$ 为坐标，

$$
p_r=\tfrac12(c+\cos\theta_rX+\sin\theta_rY),\qquad
\theta_r=0,\tfrac{2\pi}3,\tfrac{4\pi}3.
\tag{421.1}
$$

三颗伙伴位于同一 Bloch 赤道的等边三角形；其线性组合读出 $c,X,Y$。在真正二阶块中，单位已在这张平板里，原表还保留对径补元以读到缺失的 $Z$。在高阶整个块中，半伙伴超平面仍缺一向，但整个块单位穿过它，原右单位先补齐一槽；完整谱框架再给左单位，另一槽遂也补齐。不把高阶子角的单位当作整个块单位。

有限谱网用那些对角化 $b_i+b_j$ 的框架连接不同星心。它的作用沿既有 88.1：同一线性作用的二次 Jordan 缺陷，在这些谱方向上已被确定，因而可回到全部方向。有限表不是把连续原子流形换成离散世界；恢复后的每颗原子仍属于完整 $\mathbb{CP}^{n_s-1}$，相交 Peirce 角织成原复 Jordan–Lie 网，再接原实际有序联合。三实维 Bloch 坐标、两复维支持和物理三维不同；这里的三相是有限静态选点，不是自动供应一台内部相干过程或实际量子比特。

## 422. 新桥的归属与来源内生化的未接部分

**定义 422.1（复用和新增的准确关系）。** 仓内供应固定于 [cb0d72ba9d70eae79731b3ce88549a376d7f5c72](https://github.com/the-omega-institute/trureturing/tree/cb0d72ba9d70eae79731b3ce88549a376d7f5c72)。配平 87.1／88.1 已有有限谱表及导子判据；框架 264–271 已有旧 F3 半层的普适系数有限抽基；本卷 411.1 已有连续半伙伴超平面加原单位的两槽恢复。三相极化、谱论和有限线性张成均为成熟工具，不是本批新定理。 三相极化的成熟直接先例为 Alexeev–Bandeira–Fickus–Mixon, *Phase retrieval with polarization*, [arXiv:1210.7752v2，Lemma 1及式(4)–(5)](https://arxiv.org/html/1210.7752v2)：三次单位根的 Mercedes-Benz 极化从三个平方模恢复复交叉项。(418.2) 是同一三相 Fourier 恒等式的外积写法；该文的信号相位恢复与测量设计不提供这里的双线性切场或原实际操作，亦不以本文为新的极化结果。

本批 $\texttt{repo-derived}$ 接口增量是 (417.3)–(418.3)：在原零／半域内明给有限谱星，只读星心一端、同时保留两条有向输出；先从这张有限表取得整个同源输出局部性和缺失左单位，合法调用既有有限框架，再补齐另一槽。它不靠先把未知 $D$ 分类、按 $D$ 读数挑点或给全部连续输入；(420.1) 给逐对象有限数量上界。已有一般有限抽基不作为新的存在性结果重报，398.2 的分类及 412.1 的全部消费者也不重新认领。本条不主张历史优先权、最少独立信息或新完整模型类。

**定义 422.2（共同比较、过程与完整来源）。** [原词卷 §§357–361](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md#357-同源插入比较与原对象的联合采用候选) 已从同源正比较、线性插入、原读数与有向相容式共同构造忠实算子对象、Born 原质量及同一有符号旧 $D$；它允许无限响应商。这是有明确来源前件的联合采用候选，不是原裸来源已供应该比较或插入关系的结论，也未自动识别指定 native 门、保留读者和终端。有限星表不重复该构造，不将 C139 的新关系 $A$ 改名为旧 $D$；完整 CountRead 原切口的无穷维结论仍阻止把它放进这里的有限全响应背景。

[R5-011 §§4–5、10](AURIC_R5_011_THREE_PHASE_INTERNAL_ANCHORS_AND_RELATION_CONSERVATION.md#4本轮唯一新候选三相内部参照) 的三相校准作用在同一实际完整幅度后继，连同总量和差分单边条件给复线性等距，再在其实际权重、参考、混合和遗忘合同下接到仪器。这里的 (418.2) 只是静态 rank-one 外积的有限张成式，不供应那份后继、相干差分读口或全部过程合同。

[RRO 来源扩散相位卷 §10](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md#10-explicit-original-source-exterior-mass-and-a-zero-energy-correction-modulus) 已给原源外部质量界与零能修正模量；其原局部对数解、环形图数据和正折扣 Friedrichs 解的数值名字仍分别保留。那些解析界不提供本条同一原 $D$、完整 $B_*$ 或有限星问句的实际来源。具体 $\Omega$ 满足 (419.1)、原固定 native 对应、物理钟／Hamiltonian／共同作用量、独立成功支的共同完整仪器及原控制连线、每台旧同效果设备自身完整输出，仍各须来源证明。

**定义 422.3（简化的范围）。** 简化是原条件问句的严格有限子域及每星只读星心一端；额外资料为先于 $D$ 固定的静态谱表、补空间基和相位代表。没有比较独立前提总数、取得或验证成本，不提供抗噪稳定性、条件数、实际测试装置、误差容忍或全局最小性。逐对象有限不使整个原对象网、全输入过程和所有合法历史有限；精确数学等价也不把有限次有噪读数升级为全称物理认证。本条是明确来源前件下的数学等价，不把其前件或经验真实性作为已经推出的结论。

## 423. 有限问句接回完整量子理论的白话

**定义 423.1（完整直观表述）。** 原世界的每个对象、经典房间和大小不同的量子街区、原比较尺和单位来源、所有真实联合及相关、零与次归一准备、每台旧设备的端口、细记录和完整失败出口、真实分组遗忘、带同一个原成功数的两侧返回及反向资料、每条合法有限历史都照样保留。新规则不再逐个追问整圈原子：先按原对称乘法选一张有限谱网，在每颗选中珠子的旁边，沿有限补方向各放三颗半重叠伙伴，组成赤道上的小三角形；只问进出这颗珠子的两条原关系箭头都贴着它自己的表面，不先把两条箭头说成互为负号，也不先要求它们贴着伙伴。不同街区之间，则用各自有限原子基把整份跨源输出查成零。小三角形的和与差能拼回一张只缺一个方向的关系平板；二阶小球用保留的对径珠子补上，高阶街区则由整个街区已有的单位平衡补上。有限谱网先让所有同源输出留回原街区，再恢复左边的单位平衡，已有有限框架定理便把第一槽的有限贴面推到全部方向；另一条有向箭头再把第二槽也补齐，于是每份输出在两个端点都贴面、所有未问角度及自对也一起回来。已有分类把它锁成原逐块交换子，原实际参考把整份乘法缺陷带回所有小对象，同一张预选刻度单最后固定共同大小；复乘法、区分两套运输且保原质量的 Born 评价、全部中心及相关输入的实际张量、旧事件、平方根成功词、每个完整失败、原细记录、同数双返回和全部原合法历史沿旧理论原样接回。这里少的是精确数学问句，世界和连续球面没有被删成有限颗粒，小三角形也不是自动多出一台相干装置。共同比较的联合采用已是一条可继续追问来源的新入口，完整 CountRead 仍须无限载体；原来源为何满足完整背景与有限关系、怎样对应固定旧门和有符号旧关系、物理钟和共同仪器怎样取得、每台旧设备自己的完整输出如何校准，都继续留在同一目标之内。

## 追加锚 C128423（本行以下为增补区）

## 424. 总事件不动点与效果平方收缩的完整候选

**定义 424.1（同一原总映射接口）。** 本节起的原参数取[原词卷](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md)定义 406.1、419.1 和 425.1：同一完整 $\Omega$、全部原类型、准备、合法历史和未来、实响应空间 $E$、全部分离实线性评价 $\mathcal P$、原总事件 $u$、原质量 $m_\alpha=\alpha(u)\ge0$、原锥及统一序单位界

$$
E_+=\{c\in E:\alpha(c)\ge0\ (\alpha\in\mathcal P)\},\qquad
\forall a\in E\ \exists r>0:\ -ru\le a\le ru.
\tag{424.1}
$$

$E$ 允许无限维；本卷 §§417–423 的有限谱表仍各按其原前件成立。全部原 $q$、正权、中心、经典及不等维块、native、$B$ 与 $\mathsf B_{\rm cl}$、同一 $\sigma,t_0$、实际联合、设备、记录、失败、遗忘、返回及许可范围保留。同一个旧 $S,D:E^2\to E$ 起步仍仅为总映射，不预设可加、实齐次、对称／交替、单位或结合律，不另给辅助比较 $V,K,\xi,J$。

**定义 424.2（唯一候选 $\mathsf C_{\rm sq}$）。** 置 $g_\alpha(a,b)=\alpha(S(a,b))-\mathrm i\alpha(D(a,b))$。要求四组原关系约束：

1. 对全部原 $\alpha$ 和任意至多三个纯响应标签 $a_j\in E$，共同表 $G_\alpha=[g_\alpha(a_j,a_k)]$ 半正定；允许重复标签，任意实平移或缩放后的响应仍在量词内。
2. 只要求原相加定义关系的零平方：

   $$
   (1,-1,-1)G_\alpha(a+b,a,b)(1,-1,-1)^{\mathsf T}=0.
   \tag{424.2}
   $$

3. 保留同一个旧 $S,D$ 的两条三元换括号相容式：

   $$
   \begin{aligned}
   S(S(a,b),c)-D(D(a,b),c)&=S(a,S(b,c))-D(a,D(b,c)),\\
   D(S(a,b),c)+S(D(a,b),c)&=D(a,S(b,c))+S(a,D(b,c)).
   \end{aligned}
   \tag{424.3}
   $$

4. 总事件的一个自组合不动点和全部原效果的平方上界：

   $$
   \boxed{S(u,u)=u,\qquad S(e,e)\le e\quad(0\le e\le u).}
   \tag{424.4}
   $$

这里没有独立的实缩放零关系、含质量槽的二点或三点正表、单位预算或任何 $Q_a$ 保锥前件。原实空间、实线性评价、序界、复标记方向及全部来源仍为输入。约束只使用原定义中的相加、总事件、次序和两种旧二元关系；它们是否由具体原来源供应，仍是同一模型的来源义务。

## 425. 互补效果先使旧乘法有界而不先借单位

**引理 425.1（原序范数、实线性与单位作用的单射性）。** 在定义 424.1 的原参数上，候选第一、二、四组给同一个旧 $S$ 实对称双线性、同一个旧 $D$ 实交替双线性及全部有限纯响应表正性。记 $a^2=S(a,a)$、$L_u a=S(u,a)$，则

$$
N(a^2)\le N(a)^2,\quad
N(S(a,c))\le N(a)N(c),\quad
N(a-L_u a)\le\tfrac12N(a),
\tag{425.1}
$$

特别 $L_u$ 单射。此处尚不使用 $S(u,a)=a$、原三元式或任何夹心保正。

证明。先直接采用原词卷引理 420.1：共同三标签正性及相加零平方给同一 $S$ 对称双可加、有理双线性，$D$ 交替。该证明只把两坐标零方向放进第三标签，不把三坐标零方向与外部第四标签配对。由 (424.1)，零质量评价在整个 $E$ 上恒零。若 $E=0$，全部结论平凡；以下设 $E\ne0$，至少有一个正质量评价。原序单位范数为

$$
N(a)=\inf\{r\ge0:-ru\le a\le ru\}
=\sup_{m_\alpha>0}\frac{|\alpha(a)|}{m_\alpha}.
\tag{425.2}
$$

序界使其有限，分离性使其正定，原评价实线性给三角不等式及实齐次，且 $N(u)=1$。这些性质属于原实空间与次序，不预设旧乘法实齐次。

对任意正有理数 $r>N(a)$，原互补效果 $e_\pm=(u\pm a/r)/2$ 都在 $[0,u]$。将其两份平方收缩相加，仅用有理双线性和 $S(u,u)=u$，得

$$
\tfrac12\bigl(u+a^2/r^2\bigr)
=S(e_+,e_+)+S(e_-,e_-)\le e_++e_-=u.
\tag{425.3}
$$

纯响应对角正性给 $a^2\in E_+$，所以 $0\le a^2\le r^2u$。按每个原评价令有理 $r\downarrow N(a)$，得 $N(a^2)\le N(a)^2$。纯响应二标签 Cauchy–Schwarz 随即给

$$
|\alpha(S(a,c))|
\le |g_\alpha(a,c)|
\le\sqrt{\alpha(a^2)\alpha(c^2)}
\le m_\alpha N(a)N(c).
\tag{425.4}
$$

由 (425.2) 得乘法界。对任意实数 $t$ 和有理数 $q\to t$，旧 $S$ 的双可加与有理齐次给

$$
\begin{aligned}
N\bigl(S(a,tc)-tS(a,c)\bigr)
&\le N\bigl(S(a,(t-q)c)\bigr)+|t-q|N(S(a,c))\\
&\le2|t-q|N(a)N(c)\longrightarrow0.
\end{aligned}
\tag{425.5}
$$

于是同一个旧 $S$ 实双线性，未要求 $E$ 完备。现在才准确应用原词卷 400.1、400.2：其证明只需原实对称双线性实部和共同三标签正性，不需乘法单位，因而恢复同一个旧 $D$ 实双线性及全部有限纯响应正性。

最后分别展开两份平方收缩，保留常数项：

$$
0\le e_\pm-S(e_\pm,e_\pm)
=\tfrac14\bigl[u\pm2(a-L_u a)/r-a^2/r^2\bigr].
\tag{425.6}
$$

因 $a^2\ge0$，有 $-ru/2\le a-L_u a\le ru/2$。令有理 $r\downarrow N(a)$ 得最后一个范数界；若 $L_u a=0$，则 $N(a)\le N(a)/2$，故 $a=0$。这里没有把未校准的 $(u,a)$ 表写成含 $\alpha(a)$ 的质量表，也未先取得平方范数的反向不等式。∎

## 426. 原正比较排除补角并恢复真正单位

**定理 426.1（同一个旧总事件成为两侧单位）。** 候选 $\mathsf C_{\rm sq}$ 使同一个旧 $S(u,a)=S(a,u)=a$、$D(u,a)=D(a,u)=0$。单位恢复消费 (424.3)，不需要对形式补单位供应任何原状态或实际事件。

证明。由 425.1，原复化 $\mathfrak A=E\oplus\mathrm iE$ 上的 $\mu=S-\mathrm iD$ 可复双线性延拓；(424.3) 使其结合。原共轭为星运算，实对称／交替性给 $\mu(z,w)^\ast=\mu(w^\ast,z^\ast)$。每个原评价的复线性延拓 $\varphi_\alpha(a+\mathrm ib)=\alpha(a)+\mathrm i\alpha(b)$ 分离 $\mathfrak A$。425.1 的全有限纯响应正性使

$$
h_\alpha(z,w)=\varphi_\alpha(z^\ast w)
\tag{426.1}
$$

成为原 $\mathfrak A$ 上的半正定 Hermitian 型。置 $p=u$；交替性与不动点给 $p^\ast=p$、$p^2=p$。Jordan 作用 $L_u=(\mathrm{left}_p+\mathrm{right}_p)/2$ 的复化仍单射。

仅在代数推理中取单位化 $\widetilde{\mathfrak A}=\mathbb C1\oplus\mathfrak A$，令 $\varepsilon=1-p$。原 $\mathfrak A$ 是其中双侧理想，以下各角均用原理想作中项。若 $z\in\varepsilon\mathfrak A\varepsilon$，则 $pz=zp=0$，单射性给 $z=0$。若 $n\in p\mathfrak A\varepsilon$，则 $n^\ast n\in\varepsilon\mathfrak A\varepsilon=0$。在原 $h_\alpha$ 上对 $p,n$ 使用 Cauchy–Schwarz，得

$$
|\varphi_\alpha(n)|^2
=|\varphi_\alpha(p^\ast n)|^2
\le\varphi_\alpha(p^\ast p)\varphi_\alpha(n^\ast n)=0.
\tag{426.2}
$$

全部原评价分离，故 $p\mathfrak A\varepsilon=0$；取星得 $\varepsilon\mathfrak A p=0$。对每个原 $z\in\mathfrak A$，

$$
z=(p+\varepsilon)z(p+\varepsilon)=pzp.
\tag{426.3}
$$

因此 $pz=z=zp$，取原实元素即得所述同一 $S,D$ 单位关系。被评价的 $p,n,n^\ast n$ 均在原 $\mathfrak A$ 内；没有把 $\varphi_\alpha$ 延到形式 $1$ 或 $\varepsilon$。结论是原理想 $\mathfrak A=p\mathfrak A p$；形式单位化中的标量角 $\mathbb C\varepsilon$ 仍可存在，不能据此把 $\varepsilon$ 本身判为零、正效果或实际参考。∎

## 427. 原序锥恰好切回 JB 完成并恢复全部夹心

**定理 427.1（同一乘法的完成与原锥返回）。** 候选 $\mathsf C_{\rm sq}$ 下，$E\ne0$ 时原 $E$ 的 $N$ 完成 $A$ 是以同一 $u$ 为单位的 JB 代数，原 $S$ 为其乘法的限制；$E=0$ 时取 $A=0$，以下等式按零空间解释。两种情形均有

$$
N(a^2)=N(a)^2,\qquad A_+\cap E=E_+,\qquad
Q_a c:=2S(a,S(a,c))-S(S(a,a),c)\in E_+
\quad(a\in E,\ c\in E_+).
\tag{427.1}
$$

完成是数学构造，不要求原 $E$ 完备或原来源取得完成后的全部元素。

证明。先处理 $E\ne0$；零空间结论逐式平凡。426.1 已给真正单位，故此时且仅此时原纯响应标签 $(u,a)$ 的表具有对角 $m_\alpha,\alpha(a^2)$、交叉 $\alpha(a)$。Cauchy–Schwarz 给 $|\alpha(a)|^2\le m_\alpha\alpha(a^2)$。对正质量评价取上确界，得 $N(a)^2\le N(a^2)$；与 425.1 合为平方范数等式。原平方非负还给

$$
N(a^2)\le N(a^2+b^2).
\tag{427.2}
$$

原 $S$ 是结合 $\mu$ 的对称化，因而满足 Jordan 恒等式。425.1 的乘法范数界使其唯一连续延拓到实 Banach 完成 $A$；单位、Jordan 式、平方范数等式和 (427.2) 均由稠密性延拓。准确采用 Hanche-Olsen–Størmer《Jordan Operator Algebras》3.1.3–3.1.4 的定义，$A$ 是 unital JB 代数。这里不要求延拓 $D$。

每个原 $\alpha$ 满足 $|\alpha(a)|\le m_\alpha N(a)$，唯一连续延拓为 $A$ 上的实泛函；零质量支仍恒零。原平方上的非负性延至 $A$ 全部平方。按该书 3.3.3 的成熟结论，JB 正锥等于平方集，故 $A_+\cap E\subseteq E_+$。

反向，若 $c\in E_+$，原序界给某个 $r>0$ 使 $0\le c\le ru$，于是 $N(ru-c)\le r$。在 $A$ 的同一范数中仍成立。按该书 3.2.4 的单生成等距谱表示，每个 $\lambda\in\operatorname{Sp}(c)$ 满足 $|r-\lambda|\le r$，故 $\lambda\ge0$；再按 3.3.3 得 $c\in A_+$。这证明准确交集等式，不假定原评价族已是全部数学正泛函。

最后采用成熟 JB 二次表示正性 3.3.6：对任意有符号 $a\in A$，$U_a(A_+)\subseteq A_+$，其中 $U_a c=2a\circ(a\circ c)-a^2\circ c$。对原 $a,c\in E$，$U_a c$ 正是原 $Q_a c$ 且仍在原 $E$，故由锥交集返回 $E_+$。没有先用要求全夹心保正的原词卷 408、366 或 358 取得此步骤。∎

## 428. 原完整候选与辅助存在端的两向等价

**定理 428.1（固定同一原资料的完整等价）。** 在定义 424.1 的完整原参数和来源范围上，$\mathsf C_{\rm sq}$ 等价于原词卷 419.1 的 $\mathsf C_{I,+}$、414.1 的 $\mathsf C_I$、406.2 的 $\mathsf C_3$，也等价于其 408.1 的原前端加 $\mathsf{Cmp}_{385}^{\rm alg}$ 辅助完整比较存在。等价固定同一个旧 $S,D$，忘去辅助实现。

证明。由 425.1–427.1 已恢复双线性、单位、原实缩放零平方和全部原 $Q$ 保锥。原纯响应有限正性与 426.1 又给 $g_\alpha(u,e)=\alpha(e)$、$g_\alpha(u,u)=m_\alpha$；故所有原效果二点质量表及全部有限扩展表自动正，原单位预算取等号。于是准确满足原词卷 419.1。现在直接沿其 422.1、415.2、408.1 接回全部完整候选及原词卷 366、358 的忠实有界表示；不重新证明旧 GNS 或辅助直接和构造。

反向，从任一旧完整候选沿上述既有等价取得同一 $S$ 的实对称双线性、单位与原 $Q$ 保锥。于是 $S(u,u)=u$。对效果 $e$ 置 $f=u-e$，直接展开同一个旧 $Q$：

$$
Q_e f=e^2-S(e,e^2),\qquad
Q_f e=e-2e^2+S(e,e^2),\qquad
Q_e f+Q_f e=e-e^2.
\tag{428.1}
$$

$e,f\ge0$，两项均正，故 $S(e,e)\le e$。该恒等式只用对称双线性及单位，不需要结合律；其余候选条款本已成立。两向保持全部原响应、号尺度、质量和许可范围。规范辅助存在不等于任意预先给定的 native 跨标签／全词 $K,J$ 身份。∎

## 429. 不守各条关系会留下什么

**命题 429.1（固定点不能全删）。** 删除 $S(u,u)=u$ 后，其余新条款容许非单位旧乘法。

证明。在静态参数投影取 $E=\mathbb R,u=1,\alpha_m(a)=ma$（全部 $m\ge0$）、$E_+=\mathbb R_+$，令 $S=D=0$。纯响应表恒零，相加和三元式成立，且 $0=S(e,e)\le e$ 对所有效果成立，但 $S(u,u)=0\ne u$。∎

**命题 429.2（共同正表不能替代原相加定义）。** 删除相加零平方后，其余条款仍容许可乘弯曲的原关系。

证明。直接复用原词卷 409.1 的同一 $F(x)=(x+x^3)/2$、$x_a=F^{-1}(a)$、$S(a,b)=F(x_ax_b),D=0$ 静态模型。其全部有限纯表正、乘法结合且 $S(1,1)=1$。若 $0\le e\le1$，则 $0\le x_e\le1$，所以 $S(e,e)=F(x_e^2)\le F(x_e)=e$。原词卷 423.1 已计算原 $2=1+1$ 的比较平方为 $(F^{-1}(2)-2)^2>0$，故新相加合同确实失败。∎

**命题 429.3（原锥的平方收缩有独立作用）。** 即使原乘法已双线性、结合、有单位，全部纯表正也不自动给原效果平方收缩或原锥上的完整夹心保正。

证明。取静态 $E=\mathbb R^2$，$u=(1,1)$、逐坐标乘法 $S$、$D=0$。原评价为 $\alpha_1(x,y)=x+y$、$\alpha_2(x,y)=2x+y$ 及其非负线性组合。它们分离 $E$；原锥由这两份原评价定义，每个 $a$ 可统一取 $r\ge\max_i|\alpha_i(a)|/\alpha_i(u)$ 给序界。全部纯 Gram 是两坐标正权 Gram 之和，故全有限正，相加、结合及固定点均成立。但 $e=(2,-1)$ 满足 $\alpha_1(e)=1\in[0,2]$、$\alpha_2(e)=3\in[0,3]$，所以是原效果；$e^2=(4,1)$ 有 $\alpha_1(e^2)=5>\alpha_1(e)$。又 $c=(1,-1)$ 原正，而 $Q_{(0,1)}c=(0,-1)$ 非原正。不能把这份原评价族换成所有数学正泛函来消去反例。∎

**命题 429.4（三元相容仍须保留其作用）。** 删除 (424.3) 时，其余条件不一般恢复原结合复乘法。

证明。直接采用原词卷 402.3 的 $M_2(\mathbb C)_{\rm sa}$、通常 Jordan 乘法、全部正评价与 $D=0$ 实例。它已有单位、全有限纯正性和全部 $Q$ 保正；(428.1) 的不依赖结合律的恒等式遂给全部效果平方收缩。其已算出的 $X\circ X=u,X\circ Z=0$ 使 $(X\circ X)\circ Z=Z\ne0=X\circ(X\circ Z)$，故原三元式失败。以上各例只声明准确静态参数投影，不冒充完整固定 $\Omega$ 的全来源反模型，也不证明三标签在全部背景中不可削弱或所有条款完全独立。∎

## 430. 效果区间、补角与三实坐标的几何

**定义 430.1（更大结构中的原关系）。** 相加零平方先把三标签共同正表的实部锁成同一旧 $S$ 的双可加型。总事件自组合固定与互补效果的平方上界，再把原乘法限制在原序单位范数内；效果的正负两个方向同时限制 $I-L_u$ 至多半个单位范数，因此原总事件作用不丢失任何非零方向。三元换括号将同一旧 $S,D$ 组成结合乘法；原理想中的三个补角消失，使总事件成为真正两侧单位。形式 $\varepsilon$ 本身只留在数学单位化里，不是一份实际旁接来源。其后原空间的范数完成为 JB 代数，原正锥正是完成平方正锥在原响应中的切片。

在恢复完成后，对正质量原评价置 $p_\alpha(e)=\alpha(e)/m_\alpha$、$v_\alpha(e)=\alpha(S(e,e))/m_\alpha$。效果满足

$$
p_\alpha(e)^2\le v_\alpha(e)\le p_\alpha(e),\qquad
0\le v_\alpha(e)-p_\alpha(e)^2\le p_\alpha(e)(1-p_\alpha(e)).
\tag{430.1}
$$

原词卷 403.2 的中心化两方向几何仍给 $c^2+d^2\le v_av_b$；只在 $m_\alpha>0$ 且 $t=v_a+v_b>0$ 时，三实坐标 $(2c,2d,v_a-v_b)/t$ 落入闭单位球。零质量支由序界恒零，$t=0$ 时中心化表零，均不作相应除法。三标签和三实坐标不是物理三维，原网与其表示仍可无限维。

**定义 430.2（简洁性的准确比较）。** 相同原接口中，不再独立供应整族效果质量二点、总事件预算和全部有符号夹心保锥；改由一个原总事件自组合等式及原效果的单输入平方上界恢复它们。实缩放零平方也仍为推论。新等式必须明列，不把它隐藏成已推出的定义；原世界、原次序和评价族均未更换。两候选的完整模型类相同，未比较总逻辑信息、实际取得／验证成本、全部物理前提数量或全局最小性。

## 431. 现有量子公理与全部原来源怎样接回

**定义 431.1（完整条件对应）。** 428.1 使原词卷 425.1 的全部旧消费者适用于 $\mathsf C_{\rm sq}$，准确对应如下。

| 既有量子结构 | 本候选的推导及保留的来源条件 |
| --- | --- |
| 复线性、伴随与同一原乘法 | 425.1 的平方／乘法范数界先给同一 $S$ 实双线性，再由原词卷 400.1 恢复同号同尺度旧 $D$；原三元式给结合，426.1 的原正比较给真正单位，428.1 接回忠实复表示 $\pi:E\to B(H)_{\rm sa}$，$\pi(S(a,b))=(\pi(a)\pi(b)+\pi(b)\pi(a))/2$、$\pi(D(a,b))=\mathrm i[\pi(a),\pi(b)]/2$。原实数结构、复标记方向和两种旧关系读数仍为输入。 |
| 状态、效果、质量和 Born | 沿原词卷 366、358，$\alpha(e)=\langle F\xi_\alpha,\pi(e)F\xi_\alpha\rangle$、$\|F\xi_\alpha\|^2=m_\alpha$，原锥、效果与序单位范数保持，只对正质量归一。数学完成不证明原 $E$ 完备、全部算子可取得或表示满射；原 $q$ 权不替换为 Born 概率。 |
| 实际联合与全部中心 | 同一实际有序联合仍须保持旧 $S,D$、所需交叉零、全部中心对、原生成／分离、实际乘积与全部相关输入；辅助直和或完成不取得实际接线、新准备区分能力或任意 native 跨标签比较。原全部中心、经典与不等维块、完整 CountRead 范围均保留。 |
| 实际过程与 CP | C139 §§50–52 的全部合法前接和原后口先给正次单位回溯；其 §§66–73 的整台实际箭头可再次旁接同源二能级参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件、全部相关正输入仍逐项供应，才得全部有限层 CP。数学单位化、JB 完成及原 $Q$ 正性均不支付下一份真实参考或实际设备。 |
| 仪器、更新与 TP | 每台设备仍供应原全输入运输、完整 typed 菜单和全部输出、细记录、失败与真正分组；原 AC、精确 $N_u$、Xs、平方根词和接受归属保持。CP/TNI、完整测试 TP 及复合按有限维或指定正常前对偶条件采用；Lüders 仍需射线／完整输出校准，同效果不决定更新。 |
| 全历史、遗忘与返回 | 全部原合法顺序、自适应、并行历史和未来评价、原质量及记录加和、真正 typed 遗忘、具名同数两侧及逆向返回、停止、拒绝、销毁和失败保持；$B$ 与 $\mathsf B_{\rm cl}$ 分开，不增加任意右接续。正常性、指定前对偶、非离散记录和无限历史一致性仍各按原来源供应。 |
| 演化与物理刻度 | 实际保比较并保原相位的可逆过程才接入既有酉桥；连续物理钟、Hamiltonian／能量、共同作用量、$\hbar$ 和共同仪器仍分别供应。同一 $\sigma,t_0$、固定 $d$ 相位、resolvent 及 $3s+r\le1$ 的原范围保持。 |

完整 $\Omega$ 实际满足新约束及规范辅助比较与指定 native 身份的识别，仍是具体来源义务。此处在明确前提内发展同一原关系的完整条件理论，不将其升级为无条件的全部物理起源。

## 432. 成熟工具与原接口综合的归属

**定义 432.1（文献与新增范围）。** 原实部双可加极化和三标签方向刚性直接复用原词卷 420.1、400.1／400.2；其代数极化来源准确取该卷 426.1 的 Jun–Kim 引言 (1.1)–(1.2)，不是在尚无实齐次时使用赋范空间极化。代数单位化、幂等元分块、正 Hermitian 型的 Cauchy–Schwarz 和有界可加映射的实线性均为成熟中间工具。

Harald Hanche-Olsen、Erling Størmer，[Jordan Operator Algebras（1984，作者公开版）](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，3.1.3–3.1.4 给完整 JB 范数定义，3.2.4 给单生成等距谱表示，3.3.3 给正锥等于平方集，3.3.6 给全部有符号二次表示保正，3.3.10 给原范数等于单位序范数。这些成熟结论仅作 427.1 的中间工具，不作为新增一般 JB 定理。原范数完成及准确锥返回已逐步给出，不从有限维 Euclidean Jordan 分类外推至不完备无限原响应。

本仓的综合增量限于同一原总映射接口：纯三标签相加合同、单点总事件不动与原效果平方收缩，先在无单位律时恢复乘法范数界和实双线性，再借 $L_u$ 单射及原正比较排除原理想的补角，取得同一旧单位与旧方向中性，最后准确返回原锥并恢复全部旧夹心和完整资料类等价。未重新认领成熟工具、原 GNS、旧辅助有界表示、原过程消费者或全球文献优先权。约束的全来源采纳、尚可删减的其它条件和全局最小性各自未决。

## 433. 一个固定点怎样带回整张量子关系网的完整白话

**定义 433.1（完整直观说明）。** 原世界、每种类型和准备、全部合法过去与未来、质量、原 $q$、正权、所有经典和大小不同的量子街区、原 native 身份以及两种旧二元关系全部留着。先要求任意三个纯响应标签排出的共同表为正，原来“相加后算同一个”的定义差在比较里没有长度；新的缩减只另盯住一件总事件与自身组合不变，以及每个原效果的自组合不超过它本身，不再单独交整族质量校准、预算或任意两份响应的夹心规则。把一个响应放进总事件两侧的正负互补效果，两份平方上界相加先限制它的平方，再用原正比较和原序范数把同一个旧乘法锁成实数线性；已有三标签定理随后恢复旧有向关系的线性。两份上界各自还说明，总事件的乘法作用不可能丢掉任何非零原方向。原三元换括号关系让旧乘法结合；在纯数学上暂时补一个单位后，原比较的正性和读数分离把原关系理想中的三个补角全部消去，所以原总事件本身就是两侧单位，旧有向关系在它那里也归零。这个形式补角不是新事件，形式补单位也没有变成真实准备。此时才取得完整平方范数等式；原乘法的数学完成形成更大的 JB 结构，其平方正锥切回原空间恰是原来的正锥，成熟二次表示定理便把全部有符号夹心保正带回同一个旧关系，已有构造再给复乘法、忠实表示和保原质量的 Born 读数。删掉总事件固定点，零乘法会漏进来；删掉相加，弯曲线会把二等于一加一读出差别；删掉效果平方上界，两份分离评价仍可把不相容的正锥带进来，所以这些都不是空话。两条中心化关系仍能画成三实坐标球，只有正质量和正总方差才归一，三标签不是物理三维，完整大网仍可无限维。真实联合仍要保所有中心对、旧乘法、交叉零、生成分离、实际乘积和全部相关输入；全参考 CP 仍要整台箭头反复旁接同源参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件和全部相关正输入。每台仪器仍须完整输入运输、typed 菜单、全部输出、细记录、失败、真分组以及原 AC、精确 $N_u$、Xs、平方根词和接受归属；CP/TNI、完整测试 TP 和复合仍按有限维或指定正常前对偶条件采用，Lüders 仍要射线／完整输出校准。全部合法顺序、自适应、并行历史、未来、真实质量、遗忘、同数两侧和逆向返回、停止、拒绝、销毁及失败都保持，$B$ 与闭 $\mathsf B_{\rm cl}$ 不混；正常性、非离散与无限历史、保原相位的真实可逆过程、连续物理钟、Hamiltonian 能量、共同作用量、$\hbar$、共同仪器，以及同一 $\sigma,t_0$、固定 $d$、resolvent 和 $3s+r\le1$ 均继续由原来源供应。少的是独立关系检查，没有把原世界删小；固定 native 对应和完整原源为何供应这些约束，仍在同一个量子起源目标里。

## 追加锚 C128423（本行以下为增补区）

## 434. 只在任意固定小效果区间检查的完整候选

**定义 434.1（不缩小原来源的小区间）。** 全部原参数准确沿用定义 424.1：同一完整 $\Omega$、原类型、准备、合法历史和未来、允许无限维且不必完备的原实空间 $E$、全部分离实线性评价 $\mathcal P$、原总事件 $u$、原质量 $m_\alpha=\alpha(u)\ge0$、原锥和统一序单位界。全部原 $q$、正权、中心、经典及不等维块、native、$B$ 与 $\mathsf B_{\rm cl}$、同一 $\sigma,t_0$、实际联合、设备、记录、失败、遗忘、返回和许可范围不变。同一个旧 $S,D:E^2\to E$ 起步仍仅为总映射。

固定任意一个有理数 $0<\theta\le1$，定义原小效果区间

$$
I_\theta=\{e\in E:0\le e\le\theta u\},\qquad
M_\theta=2/\theta-1.
\tag{434.1}
$$

$\theta$ 只指定数学检查域，不是物理作用量、成功率、质量或新参考。选择 $\theta=1/2$ 就只查原半效果；下文一次处理全部正有理选择，不把逐次减小这个常数另算新成果。

**定义 434.2（唯一小效果候选 $\mathsf C_\theta$）。** 保留定义 424.2 的纯响应至多三标签共同正性、仅相加零平方 (424.2)、同一个旧 $S,D$ 的两条三元相容式 (424.3)，以及显式总事件不动点 $S(u,u)=u$。唯一替换是

$$
\boxed{S(e,e)\le e\qquad(e\in I_\theta).}
\tag{434.2}
$$

不再独立检查 $[0,u]\setminus I_\theta$，也不供应质量标签正表、预算、实缩放零平方、单位律或任何 $Q$ 保锥。原实空间、分离评价、原次序、复标记方向和全部实际来源仍是明确输入。目标是在同一原资料上恢复全部 $\mathsf C_{\rm sq}$，不换原锥或旧乘法。

## 435. 小区间先恢复有界乘法与单位作用单射

**引理 435.1（带有限常数的原范数界）。** 候选 $\mathsf C_\theta$ 给同一个旧 $S$ 实对称双线性、同一个旧 $D$ 实交替双线性及全有限纯响应正性。记原序单位范数为 $N$、$a^2=S(a,a)$、$L_u a=S(u,a)$，则

$$
\begin{aligned}
N(a^2)&\le M_\theta N(a)^2,\\
N(S(a,c)),\ N(D(a,c))&\le M_\theta N(a)N(c),\\
N(a-\theta L_u a)&\le(1-\theta/2)N(a).
\end{aligned}
\tag{435.1}
$$

特别 $L_u$ 单射。此处尚不使用乘法单位、结合律、夹心保正或平方范数等式。

证明。准确复用原词卷引理 420.1：前两组共同表条件给同一 $S$ 对称双可加、有理双线性，$D$ 交替；不把三坐标零方向与外部第四标签配对。定义 424.1 的原序界使零质量评价在整个 $E$ 上恒零。$E=0$ 时各式平凡；以下设 $E\ne0$。按 (425.2)，

$$
N(a)=\sup_{m_\alpha>0}|\alpha(a)|/m_\alpha
\tag{435.2}
$$

是有限实范数，$N(u)=1$，这些性质来自原实空间和评价，不来自乘法齐次性。

对正有理数 $r>N(a)$，两份原小效果 $e_\pm=\theta(u\pm a/r)/2$ 均属 $I_\theta$。用有理双线性相加两份收缩，得到

$$
\frac{\theta^2}{2}(u+a^2/r^2)
=S(e_+,e_+)+S(e_-,e_-)
\le\theta u.
\tag{435.3}
$$

原对角正性给 $a^2\ge0$，所以 $0\le a^2\le M_\theta r^2u$。按全部原评价令有理 $r\downarrow N(a)$，得第一式。纯响应二点 Cauchy–Schwarz 给

$$
|g_\alpha(a,c)|\le\sqrt{\alpha(a^2)\alpha(c^2)}
\le M_\theta m_\alpha N(a)N(c).
\tag{435.4}
$$

由原范数公式得同一 $S$ 的乘法界。对实数 $t$ 用有理数 $q\to t$，有

$$
N(S(a,tc)-tS(a,c))
\le2M_\theta|t-q|N(a)N(c)\longrightarrow0.
\tag{435.5}
$$

故旧 $S$ 实双线性，不要求原 $E$ 完备。此时才复用不需要单位律的原词卷 400.1、400.2，取得同一旧 $D$ 实双线性及全有限纯响应正性。(435.4) 的虚部及原分离范数再给 $D$ 的界。

分别展开小效果收缩，保留常数项：

$$
0\le e_\pm-S(e_\pm,e_\pm)
=\frac\theta4\left[(2-\theta)u
\pm\frac{2(a-\theta L_u a)}r
-\frac{\theta a^2}{r^2}\right].
\tag{435.6}
$$

因 $a^2\ge0$，两式给 $N(a-\theta L_u a)\le(1-\theta/2)r$。取极限得最后一式。若 $L_u a=0$，则 $N(a)\le(1-\theta/2)N(a)$；$\theta>0$ 使 $a=0$。没有把含非零常数的二次不等式当成一次项必须消失，也未提前取得 $N(a^2)=N(a)^2$。∎

## 436. 沿同一原理想恢复真正单位

**定理 436.1（小效果同样钉住原单位）。** 候选 $\mathsf C_\theta$ 给同一个旧 $S(u,a)=a$、$D(u,a)=0$ 及另一槽的单位关系；原复化上的 $\mu=S-\mathrm iD$ 是以同一 $u$ 为单位的结合星乘法。

证明。435.1 已供应定理 426.1 的单位恢复证明实际消费的全部前件：旧 $S,D$ 实双线性、全有限纯响应正性、原三元相容、$S(u,u)=u$ 和 $L_u$ 单射。该证明不消费常数为一的平方上界或全部效果收缩，故准确直接复用其原理想分块论证。纯代数单位化中的 $p=u$ 为自伴幂等元，$\varepsilon\mathfrak A\varepsilon=0$ 由 $L_u$ 单射给出，$p\mathfrak A\varepsilon=0$ 由原正型对 $(p,n)$ 的 Cauchy–Schwarz 与分离性给出，取星消去第三角，得到原 $\mathfrak A=p\mathfrak A p$。未评价形式 $1$ 或 $\varepsilon$，未把整个单位化的 $\mathbb C\varepsilon$ 判零；数学补单位也不供应实际参考或准备。∎

## 437. 不借夹心保正的有界预表示

**引理 437.1（Banach 星完成上的平方根界）。** 候选 $\mathsf C_\theta$ 允许构造一个复 Hilbert 空间 $H$、同一原 $E$ 上的忠实实线性映射 $\pi:E\to B(H)_{\rm sa}$ 及每个原正质量评价的向量 $\xi_\alpha$，满足

$$
\begin{gathered}
\pi(u)=I_H,\quad
\pi(S(a,b))=\tfrac12\{\pi(a)\pi(b)+\pi(b)\pi(a)\},\quad
\pi(D(a,b))=\tfrac{\mathrm i}2[\pi(a),\pi(b)],\\
\alpha(a)=\langle\xi_\alpha,\pi(a)\xi_\alpha\rangle,
\qquad\|\xi_\alpha\|^2=m_\alpha,\\
N(a)\le\|\pi(a)\|\le8M_\theta N(a).
\end{gathered}
\tag{437.1}
$$

这是尚未宣告保原锥的预表示；不能仅凭这些原标签上的非负读数就提前写出 $c\in E_+\Rightarrow\pi(c)\ge0$。

证明。零空间取 $H=0$；以下设 $E\ne0$。在原复化 $\mathfrak A=E\oplus\mathrm iE$ 上置

$$
N_{\mathbb C}(a+\mathrm ib)
=\sup_{m_\alpha>0}\frac{|\alpha(a)+\mathrm i\alpha(b)|}{m_\alpha},\qquad
\|z\|_B=8M_\theta N_{\mathbb C}(z).
\tag{437.2}
$$

原评价的复线性延拓和分离性使 $N_{\mathbb C}$ 为真正的复范数，原共轭等距，且 $N_{\mathbb C}(a)=N(a)$。令 $\|a+\mathrm ib\|_1=N(a)+N(b)$ 仅作实辅助范数，则

$$
\max\{N(a),N(b)\}\le N_{\mathbb C}(a+\mathrm ib)
\le\|a+\mathrm ib\|_1\le2N_{\mathbb C}(a+\mathrm ib).
\tag{437.2a}
$$

由 435.1 的两份乘法界，$\|zw\|_1\le2M_\theta\|z\|_1\|w\|_1$，所以 $N_{\mathbb C}(zw)\le8M_\theta N_{\mathbb C}(z)N_{\mathbb C}(w)$，进而 $\|zw\|_B\le\|z\|_B\|w\|_B$。取这一复范数的数学完成 $B$，乘法和星唯一连续延拓，构成含幺 Banach 星代数。这里 $\|u\|_B=8M_\theta$，不要求此辅助范数的单位范数为一。原 $E$ 的完备性没有成为前提。

每个原评价的复线性延拓 $\varphi_\alpha(a+\mathrm ib)=\alpha(a)+\mathrm i\alpha(b)$ 满足 $|\varphi_\alpha(z)|\le m_\alpha N_{\mathbb C}(z)$，故延到 $B$。全有限纯响应正性使它在原 $z^\ast z$ 上非负，乘法连续性将此性质延到全部 $B$ 的星平方。零质量延拓恒零。

现在给出不依赖原 $Q$ 或原锥返回的左作用界。对 $x\in B$ 及实数 $R>\|x\|_B^2$，令 $v=x^\ast x/R$，则 $\|v\|_B<1$。实系数二项式级数

$$
b=\sum_{n=0}^\infty {1/2\choose n}(-v)^n
\tag{437.3}
$$

绝对收敛；$v^\ast=v$ 给 $b^\ast=b$，绝对收敛的 Cauchy 乘积给 $b^2=u-v$。因 $\varphi_\alpha$ 在全部星平方上非负，对任意 $y\in B$，

$$
0\le\varphi_\alpha((by)^\ast by)
=\varphi_\alpha(y^\ast y)
-\frac1R\varphi_\alpha((xy)^\ast xy).
\tag{437.4}
$$

复用成熟正型零空间商与 GNS 机制，令 $\mathcal N_\alpha=\{y:\varphi_\alpha(y^\ast y)=0\}$。(437.4) 先证明 $x\mathcal N_\alpha\subseteq\mathcal N_\alpha$，再给商上的左作用界 $\|\pi_\alpha(x)\|\le\sqrt R$；令 $R\downarrow\|x\|_B^2$ 得 $\|\pi_\alpha(x)\|\le\|x\|_B$。故左作用良定义且延到 Hilbert 完成，保乘法、星和单位，原向量 $\xi_\alpha=[u]$ 的平方范数为 $m_\alpha$，且 $\varphi_\alpha(x)=\langle\xi_\alpha,\pi_\alpha(x)\xi_\alpha\rangle$。没有先假定零空间左稳定，也没有把 $B$ 先称为 $C^*$ 代数。

对全部正质量原评价取 Hilbert 直接和。上述界对评价一致，故直接和左作用有界。限制到原 $E$ 即得 (437.1) 的旧乘法及号尺度；若 $\pi(a)=0$，原全部评价均为零，分离性给 $a=0$。对正质量评价的向量读数有 $|\alpha(a)|\le m_\alpha\|\pi(a)\|$，取上确界得范数下界。此时只得有限常数上界和忠实性，尚未将原锥与算子正锥识别。∎

## 438. 原序预算中的反复削平方排除负谱

**定理 438.1（小效果恢复准确原锥及全部夹心）。** 上述同一预表示满足

$$
\pi(c)\ge0\quad\Longleftrightarrow\quad c\in E_+.
\tag{438.1}
$$

因此 $N(a)=\|\pi(a)\|$、$N(a^2)=N(a)^2$，而同一个旧 $Q_a$ 对全部有符号原 $a$ 保原锥。

证明。反向由原向量读数直接得出，包括原零质量支。证明正向时，取 $c\in E_+$；$c=0$ 平凡。选一个固定实数 $R>N(c)/\theta$，在原 $E$ 内递推

$$
c_0=c,\qquad c_{n+1}=c_n-c_n^2/R.
\tag{438.2}
$$

若 $0\le c_n\le c$，原范数和次序给 $N(c_n)\le N(c)$，所以 $e_n=c_n/R\in I_\theta$。只对这一小效果使用 (434.2)，得 $c_n^2\le R c_n$，因而 $c_{n+1}\ge0$；纯响应平方非负又给 $c_{n+1}\le c_n$。归纳得到

$$
0\le c_n\le c,\qquad
N(c_n)\le N(c),\qquad
\|\pi(c_n)\|\le8M_\theta N(c)
\quad(n\ge0).
\tag{438.3}
$$

固定 $f(t)=t-t^2/R$。437.1 的乘法保持性给 $\pi(c_n)=f^{\circ n}(\pi(c))$。若有 $\lambda\in\operatorname{Sp}(\pi(c))$ 满足 $\lambda<0$，置 $t_n=-f^{\circ n}(\lambda)$。则

$$
t_{n+1}=t_n+t_n^2/R\ge t_0+n t_0^2/R\longrightarrow\infty.
\tag{438.4}
$$

有界自伴算子的多项式谱映射给 $\|\pi(c_n)\|\ge t_n$，与 (438.3) 的同一个有限预算矛盾。因此谱非负，即 $\pi(c)\ge0$。这不把分别可达的极值拼接；全部 $c_n$ 属同一原响应递推，使用同一 $R$、同一原锥和同一预表示。

(438.1) 和 $\pi(u)=I_H$ 使 $-ru\le a\le ru$ 与 $-rI_H\le\pi(a)\le rI_H$ 两向等价，故原序单位范数恰为算子范数，平方等式随之成立。对原 $a\in E,c\in E_+$，结合表示直接给

$$
\pi(Q_a c)=\pi(a)\pi(c)\pi(a)\ge0.
\tag{438.5}
$$

用 (438.1) 返回同一原 $E_+$。这里没有借用要求 $Q$ 保锥的旧表示定理来建立预表示或排除负谱。∎

## 439. 与原完整候选的等价及完成后的较大结构

**定理 439.1（固定原资料的完整等价）。** 对每个固定有理数 $0<\theta\le1$，$\mathsf C_\theta$ 与定义 424.2 的 $\mathsf C_{\rm sq}$ 等价，进而与原词卷 419、414、406 的完整候选及 408 的辅助完整比较存在等价。两向固定同一原 $S,D$，忘去辅助实现，不指定任意 native 跨标签／全词比较身份。

证明。435.1–438.1 已恢复同一 $S,D$ 的实双线性、单位、全有限纯正性及全部有符号旧 $Q$ 保锥。准确复用 (428.1) 的恒等式：对原效果 $e$、$f=u-e$，$Q_e f+Q_f e=e-e^2$；两项均正，故全部原效果均平方收缩。于是取得完整 $\mathsf C_{\rm sq}$，此时才沿 428.1 及原词卷 422、415、408、366、358 接回全部旧接口。反向因 $I_\theta\subseteq[0,u]$，原完整候选直接供应所有小效果条件。∎

437.1 的 $\pi(E)+\mathrm i\pi(E)$ 已是含幺星代数；其算子范数闭包是复 $C^*$ 代数，$\pi(E)$ 在其自伴部稠密。438.1 使原 $E$ 的范数完成为同一 Jordan 乘法的 JB 代数，原正锥准确切回；只有另有原完备性，才把原 $E$ 识别为完成的全部自伴部。数学完成、级数和辅助向量均不增添实际事件、准备、设备或参考。这里先建带常数界的预表示再返回原锥；没有在 435–437 偷用尚未恢复的平方范数等式或 JB 完成结论。

## 440. 小检查域仍排除哪些缺陷

**命题 440.1（删除关系的准确静态后果）。** 定理 429.1、429.2、429.4 的零乘法、可乘弯曲线和 $M_2(\mathbb C)_{\rm sa}$ 的旧 Jordan／$D=0$ 模型，分别继续见证固定点、相加零平方和三元相容不能全删：它们原已满足全部效果收缩，故满足每个 $I_\theta$ 上的收缩，只有被删除的关系失败。

证明。直接复用对应模型的全部已算条件；429.1 的零乘法在全部效果上收缩而不满足固定点，429.2 的 $F(x)=(x+x^3)/2$ 在全部效果上收缩而不保原相加，429.4 的旧 Jordan 模型有全部效果收缩但不满足复结合。这里不另造完整 $\Omega$ 反模型。∎

**命题 440.2（任意小的非零效果仍能检出错误原锥）。** 429.3 的逐坐标 $\mathbb R^2$ 模型保持其它全部条款，但对每个 $\theta>0$ 都失败于 $I_\theta$；$\theta=0$ 的空缩减不能恢复原理论。

证明。保持原 $u=(1,1)$、$\alpha_1(x,y)=x+y$、$\alpha_2(x,y)=2x+y$ 及非负组合，不换原评价族。原 $c=(1,-1)$ 正，取 $e=\theta c$，则

$$
\alpha_1(e)=0,\quad\alpha_2(e)=\theta,
\qquad\alpha_1(\theta u-e)=2\theta,\quad
\alpha_2(\theta u-e)=2\theta.
\tag{440.1}
$$

所以 $e\in I_\theta$；但 $\alpha_1(e^2)=2\theta^2>0=\alpha_1(e)$，小收缩失败。若 $\theta=0$，分离性使 $I_0=\{0\}$，该模型通过这一域的检查而原完整 $Q$ 仍失败；故正比例的条件不能改成零比例。所有这些结论均限于准确静态参数投影，不宣告全部条款独立或完整原来源反模型。∎

## 441. 小效果、负谱逃逸与全网几何

**定义 441.1（简化发生的位置）。** 与 424.2 在同一原接口比较，减少的是平方收缩的独立检查域：从全部 $[0,u]$ 缩到任意一个固定正有理比例 $I_\theta$，未检查的其余效果均在定理 439.1 中恢复。总事件不动点仍显式保留；相加、三标签共同正性和原三元相容没有改名隐藏。模型类等价，不表示总逻辑信息、实际取得或验证成本下降，也不证明有限可认证、全局最小或全部物理前提减少。

几何上，两份小效果之和为 $\theta u$，它们在这个小总量中互补；暂时的 $M_\theta$ 范数常数只为有限有界性付费。原正响应在 (438.2) 中不断削去一小份自身平方，始终留在同一序区间 $[0,c]$。若预表示藏着负谱方向，该方向会越削越负而无界，原区间预算却始终有限，所以这样的方向不能存在。$\theta\downarrow0$ 时临时常数可以增大，证明只用每个固定正 $\theta$ 的有限常数，不交换极限或在 $\theta=0$ 推论。

全效果恢复后，430.1 的 $p_\alpha(e)^2\le v_\alpha(e)\le p_\alpha(e)$、方差带及原词卷 403.2 的中心化三实坐标球继续按原条件成立。正质量、正总方差才可分别归一；零质量和零方差分支不作除法。三标签、三实坐标和辅助谱不是物理三维，原完整网仍可无限维。

## 442. 同一新候选怎样接回现有量子公理

**定义 442.1（完整量子与来源对应）。** $\mathsf C_\theta$ 恢复 431.1 的全部消费者，各项对应为：

| 既有量子结构 | 小效果候选的推导及保留的来源条件 |
| --- | --- |
| 复线性、伴随与同一乘法 | 435.1 先恢复同一 $S,D$ 的实双线性；原三元式和 436.1 给结合、星及原单位；437–438 的忠实表示满足 $\pi(S(a,b))=(\pi(a)\pi(b)+\pi(b)\pi(a))/2$、$\pi(D(a,b))=\mathrm i[\pi(a),\pi(b)]/2$。原实空间、复标记方向和两种旧关系仍是输入。 |
| 状态、效果、质量和 Born | 437.1 保每份原评价的向量读数及质量，438.1 才识别原锥、全部效果与原序单位范数。只对正质量归一；零质量在原界下恒零。完成不证明原 $E$ 完备、表示满射或全部算子可取得；原 $q$ 和不等正权不替换为 Born 概率。 |
| 实际联合与全部中心 | 原实际有序联合仍保持旧 $S,D$、交叉零、全部中心对、原生成／分离、实际乘积和全部相关输入；辅助空间的数学直接和不取得实际接线、准备区分能力或任意 native 跨标签身份。经典、不等维块和完整 CountRead 范围均保留。 |
| 实际过程与 CP | C139 §§50–52 的全部合法前接和原后口先给正次单位回溯；其 §§66–73 的整台箭头再次旁接同源二能级参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件、全部相关正输入继续逐项供应，才得全部有限层 CP。Banach 完成、平方根级数、GNS 及数学 $Q$ 不支付下一份真实参考或实际设备。 |
| 仪器、更新与 TP | 每台设备仍给原全输入运输、完整 typed 菜单和全部输出、细记录、失败及真正分组；原 AC、精确 $N_u$、Xs、平方根词和接受归属不变。CP/TNI、完整测试 TP 与复合仍按有限维或指定正常前对偶条件采用；Lüders 仍需射线／完整输出校准，同效果不决定更新。 |
| 全历史、遗忘与返回 | 全部原合法顺序、自适应、并行历史及未来、原质量、记录加和、真正 typed 遗忘、具名同数两侧及逆向返回、停止、拒绝、销毁和失败保持；$B$ 与 $\mathsf B_{\rm cl}$ 分开，不增加任意右接续。正常性、指定前对偶、非离散记录和无限历史一致性仍分别由原来源供应。 |
| 演化与物理刻度 | 实际保比较并保原相位的可逆过程才接入已有酉桥；连续物理钟、Hamiltonian／能量、共同作用量、$\hbar$ 和共同仪器仍分别供应。同一 $\sigma,t_0$、固定 $d$ 相位、resolvent 和 $3s+r\le1$ 的原范围保持。 |

具体完整 $\Omega$ 为何供应新约束，以及规范辅助比较与预定 native 身份如何识别，仍是具名来源义务；数学条件理论不替代它们。

## 443. 成熟工具与小效果接口增量的归属

**定义 443.1（文献及新增范围）。** 原相加的代数极化、旧方向三标签刚性、全有限纯响应正性和原理想的单位恢复分别直接复用原词卷 420、400 及本卷 426 的实际证明前件。435.1 的有限常数变化、437.1 在无原 $Q$ 前的有界预表示及 438.1 的同一原序预算递推，构成这里的小检查域综合，不把更改 $\theta$ 单独包装成新理论。

成熟正型商、零空间及 Hilbert 完成沿原词卷 358、366、401 的 GNS／正核机制使用；复用的是数学机制，旧定理要求的 $Q$ 前件没有提前调用。437.3–437.4 显式用收敛二项式平方根证明新的接口所需左稳定及一致界，未把一般 GNS、Banach 星代数完成、Cauchy–Schwarz 或二项式公式认作新一般定理。438.4 使用成熟有界自伴谱理论及多项式谱映射，不将负谱排除冒充数值实验。

Hanche-Olsen、Størmer，[Jordan Operator Algebras（1984，作者公开版）](https://hanche.folk.ntnu.no/joa/joa-m.pdf) 1.3 节给 Banach 星代数、表示与 GNS 背景；其 1.3.10 要求正锥已为星平方集，故不在原锥返回前直接套用。其 3.1.3–3.1.4、3.2.4、3.3.3、3.3.6、3.3.10 仍是 427 的成熟 JB 工具；这里的前向小效果证明不把那些带完整范数条件的结论循环放进 435–438。

新增主张限于同一原总映射、原评价和原锥接口上：任意固定正有理小区间的平方收缩，先给足够的有限界和单位单射，再在不预设原夹心保正时构造带统一界的预表示，以留在同一原序预算中的平方递推排除负谱，恢复完整原锥、全部旧夹心及原完整候选等价。未认领成熟一般工具、旧过程理论、全球文献优先权或完整量子起源；全来源采纳和其它尚可删减的独立关系继续未决。

## 444. 只盯一小段效果怎样带回整张量子网的完整白话

**定义 444.1（完整直观说明）。** 原世界、类型、准备、全部合法过去与未来、真实质量、原 $q$、正权、所有中心、经典和大小不同的量子街区、native 身份及两种旧二元关系全部留着。仍要求任意三个纯响应标签的共同表为正、原相加定义差没有比较长度、原三元换括号相容以及总事件与自身组合不变；新的缩减是只检查总事件以下任意一段固定正比例的小效果，看它自组合是否不超过自身，其余大效果、质量校准、预算和全部夹心不再独立交检查。把响应的正负两侧放进小总量的两份互补效果，有限范数界先把同一个旧乘法锁成实数线性，再由旧三标签定理恢复同一个有向关系；两份小上界也使总事件作用不丢方向，原结合关系和正比较随后把原理想的三个补角排掉，原总事件成为真正单位。数学上先完成一个带连续乘法的星代数，用收敛平方根和原正型证明左作用确实有界，得到保原读数与质量的预表示；此时还不能因每份原准备读数非负，就把算子正性当成已经得到。关键是对一份原正响应不断削去一小份自身平方：每次只查仍在那段小效果中的响应，结果始终夹在零和原响应之间；若预表示里藏着负谱方向，它会越削越负而无界，同一原序预算却始终有限，于是负谱被排除。这样原锥准确回到算子正锥，旧有符号夹心、全部大效果、平方范数和已有完整量子候选才一起恢复，数学完成也呈现更大的复 $C^*$ 与 JB 结构。这个小比例可以任意固定地选小，但不能取零，也没有据此得到有限认证或全局最少；三实坐标球仍只在正质量和正总方差时归一，不是物理三维，原网可以无限维。真实联合仍要全部中心对、旧乘法、交叉零、生成分离、实际乘积及全部相关输入；全参考 CP 仍要整台箭头反复旁接同源参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件和全部相关正输入，数学完成、平方根、预表示和 $Q$ 都不是新设备或真实参考。每台仪器仍供应全输入运输、完整 typed 菜单、所有输出、细记录、失败、真分组、AC、精确 $N_u$、Xs、平方根词及接受归属；CP/TNI、完整测试 TP 和复合仍按有限维或指定正常前对偶条件，Lüders 仍需射线／完整输出校准。同一原质量、全部顺序、自适应和并行历史、未来、真正遗忘、同数两侧及逆向返回、停止、拒绝、销毁与失败保持，$B$ 不混为闭 $\mathsf B_{\rm cl}$，不增添任意右接续；正常性、非离散与无限历史、保原相位的实际可逆过程、连续物理钟、Hamiltonian 能量、共同作用量、$\hbar$、共同仪器、同一 $\sigma,t_0$、固定 $d$、resolvent 与 $3s+r\le1$ 仍分别由原来源供应。少的是独立检查域，没有把原世界删小；固定 native 对应和原完整来源为何供应这些关系，仍在同一个量子起源目标内。

## 追加锚 C128423（本行以下为增补区）

## 445. 只保留实部换括号的完整原关系候选

**定义 445.1（同一原资料上的 $\mathsf C_R$）。** 全部原参数、原 $E$ 及其实数作用、分离实线性评价 $\mathcal P$、评价定义的原锥、原 $u$、质量与序单位界，以及同一完整 $\Omega$ 和全部原来源，严格取定义 424.1。同一个旧 $S,D:E^2\to E$ 在入口仍只是总映射，$g_\alpha=\alpha(S)-\mathrm i\alpha(D)$。要求：任意至多三标签、含重复标签的纯 Gram 正性；(424.2) 的原相加零平方；$S(u,u)=u$ 及所有原效果 $0\le e\le u$ 的 $S(e,e)\le e$；以及唯一独立三元式

$$
S(S(a,b),c)-D(D(a,b),c)
=S(a,S(b,c))-D(a,D(b,c))
\qquad(a,b,c\in E).
\tag{445.1}
$$

它与 $\mathsf C_{\rm sq}$ 只有一个差别：删除 (424.3) 的虚部相容式，不增加替代条件。不预设单位律、实双线性、Jordan 律、幂结合、导子律、任意夹心保正、标记质量表、ND、有限维或完备性。证明中的顺序导子指有界实线性算子 $T$ 满足 $e^{tT}X_+=X_+$ 对全部实 $t$ 成立；它起初并不表示保持任何乘法。

## 446. 原效果平方界把两种关系都压在正锥切向内

**定理 446.1（不消费三元式的切向恢复）。** 只用定义 445.1 中除 (445.1) 之外的条件，旧 $S,D$ 已有引理 425.1 的同一原实双线性及全部有限纯表正性。令 $X$ 为原序单位范数 $N$ 的完成，$X_+$ 为 $E_+$ 的范数闭包。两种关系唯一连续延拓到 $X$；对每个 $a\in X$，$L_a c=S(a,c)$ 与 $D_a c=D(a,c)$ 都是该锥的顺序导子。这里尚未取得 Jordan 律或 $D_a u=0$。

证明。直接复用 425.1 的无三元式部分：$N(S(a,b)),N(D(a,b))\le N(a)N(b)$，$0\le a^2=S(a,a)$，$u^2=u$，同一旧关系实对称／交替且双线性。$E=0$ 时取 $X=0$，以下全部结论按零空间解释。非零时 $N(u)=1$；零质量评价由原序界在整个 $E$ 上恒零。原正质量归一评价连续延拓后仍给 $N(x)=\sup_{m_\alpha>0}|\alpha(x)|/m_\alpha$。若全部原延拓评价对 $x\in X$ 非负，以 $a_n\in E$、$N(a_n-x)\le\epsilon_n\downarrow0$ 逼近，则 $a_n+\epsilon_nu\in E_+$，故 $x\in X_+$。反向由连续性成立。因此这个完成仍是同一 Archimedean 序单位空间的完成，且

$$
E\cap X_+=E_+.
\tag{446.1}
$$

若 $e\in[0,u]\subset X$，同样的 $a_n$ 给原效果 $e_n=(a_n+\epsilon_nu)/(1+2\epsilon_n)\to e$，所以 $0\le e^2\le e$ 传到完成。对 $c\in X_+$ 选 $r>0$ 使 $c\le ru$，得到

$$
0\le c^2\le rc.
\tag{446.2}
$$

令 $\varphi$ 是 $X$ 上任意连续正泛函；这些只是证明中的数学泛函，不添入原准备或原评价列表。每个原纯 Gram 的复二次型等于某个原实元素的全部评价，其非负性使该元素在 $E_+$；施加任意正泛函并由稠密性延拓，故 $\varphi(S)-\mathrm i\varphi(D)$ 的全部有限纯表仍正。若 $c\ge0$ 且 $\varphi(c)=0$，(446.2) 给 $\varphi(c^2)=0$；标签 $(c,a)$ 的零对角及 Cauchy–Schwarz 于是给

$$
\varphi(S(a,c))=\varphi(D(a,c))=0.
\tag{446.3}
$$

此处把原锥上的正泛函用于已为原正元素的二次型，没有将原锥偷换成某个先给星代数的正锥。

采用成熟顺序导子的切向判据：有界 $T$ 满足 $\varphi(Tc)=0$ 对每个 $c\ge0,\varphi\ge0,\varphi(c)=0$，便生成双向保锥指数群。所需版本可直接证明。对任意 $c\ge0,\epsilon>0$，解 $y'=Ty+\epsilon u$、$y(0)=c+\epsilon u$。若有有限首次触及边界的时刻 $t_0>0$，支撑泛函可取为 $\varphi_0\ge0$、$\varphi_0(u)=1$、$\varphi_0(y(t_0))=0$。此前 $y(t)$ 在内部，从左侧微分得 $\varphi_0(y'(t_0))\le0$；切向条件却使它等于 $\epsilon>0$，矛盾。令 $\epsilon\downarrow0$ 得 $e^{tT}c\ge0$（$t\ge0$），再对 $-T$ 同证，取逆即得全部实时间。反向对 $\varphi(e^{tT}c)$ 在零点求导即可。由 (446.3) 分别用于 $T=L_a,D_a$，得结论。∎

## 447. 不借结合律恢复总事件的单位作用

**定理 447.1（效果平方界已经恢复同一个对称单位）。** 定理 446.1 的前件已给 $S(u,a)=a$ 对全部原 $a$ 成立，不需要任何三元式。

证明。只在辅助完成 $X$ 中工作，置 $C=L_u$。$Cu=u$。对 $c\ge0$ 取充分小的 $t>0$ 使 $u-tc$ 是效果，平方收缩给

$$
u-2tCc+t^2c^2\le u-tc,
\qquad 2Cc\ge c+tc^2\ge c.
\tag{447.1}
$$

所以 $C$ 是正算子；446.1 又使它为顺序导子。对 $t>0$ 置 $T=e^{-tC}$，则

$$
0\le T\le I,\qquad
I-T=\int_0^tCe^{-sC}\,ds\ge0,\qquad
Tu=e^{-t}u.
\tag{447.2}
$$

只需以下序单位算子计算。若 $0\le T\le I$ 且 $Tu=\lambda u$，$0\le\lambda\le1$，正算子 $P_{n,k}=\binom nkT^k(I-T)^{n-k}$ 满足 $\sum_{k=0}^nP_{n,k}=I$、$\sum_{k=0}^n(k/n)P_{n,k}=T$。正算子的序单位算子范数等于其在 $u$ 上的范数，故 $\|P_{n,k}\|=\binom nk\lambda^k(1-\lambda)^{n-k}$。二项式权重的方差与 Cauchy–Schwarz 给

$$
\|T-\lambda I\|
\le\sum_{k=0}^n\left|\frac{k}{n}-\lambda\right|
\binom nk\lambda^k(1-\lambda)^{n-k}
\le\sqrt{\frac{\lambda(1-\lambda)}n}.
\tag{447.3}
$$

令 $n\to\infty$ 得 $T=\lambda I$。用于 (447.2)，得 $e^{-tC}=e^{-t}I$；在零处作算子范数微分，$C=I$。限制回原 $E$ 即为同一旧 $S(u,a)=a$。这加强 426.1 的对称单位部分：不用其结合代数和补角结论作为前提。辅助指数与二项式算子未被认作实际可调用设备。∎

## 448. 赋范空间等距刚性排除乘法漂移

**定理 448.1（原对称组合对全部保单位顺序导子不变）。** 在 446.1 的前件下，任一 $X$ 上有界顺序导子 $K$ 若 $Ku=0$，则

$$
KS(a,b)=S(Ka,b)+S(a,Kb)
\qquad(a,b\in X).
\tag{448.1}
$$

不预先使用 Jordan 律、幂结合、条件概率唯一性或事件谱张成。

证明。切向判据使全部顺序导子组成范数闭实线性空间；若 $K,T$ 都在其中，$e^{tK}Te^{-tK}$ 仍在其中，在零处作范数微分给 $[K,T]$ 仍是顺序导子。若 $Tu=0$，其指数正逆且保 $u$，因而是原序单位范数的双向线性等距群。

置 $B(a,b)=KS(a,b)-S(Ka,b)-S(a,Kb)$。它有界、对称双线性，且

$$
B_a=[K,L_a]-L_{Ka},\qquad B_a u=Ka-Ka=0.
\tag{448.2}
$$

这里使用 447.1 已得的单位；(448.2) 使每个 $B_a$ 都生成双向等距群。所需刚性在任意实 Banach 空间上成立，证明内应用如下。若连续算子族 $A(t)$ 每一时刻都生成双向等距群，而 $z'=A(t)z$，则 $z(t+h)=e^{hA(t)}z(t)+o(|h|)$，所以 $\|z(t+h)\|-\|z(t)\|=o(|h|)$，范数导数恒零；不需要范数本身可微。

考虑二次向量场 $x'=B(x,x)$。局部存在唯一性来自有界双线性；令 $A(t)=B_{x(t)}$，上式给 $\|x(t)\|$ 恒定。向量场在有界球上有统一 Lipschitz 界和有界性，故解延拓到全部实时间。两个解满足 $(x-y)'=B(x+y,x-y)$，同样给距离恒定。所得流 $\Phi_t$ 是保零的满射等距映射，逆为 $\Phi_{-t}$。成熟 Mazur–Ulam 定理使它实线性；对 $\Phi_t(2x)=2\Phi_t(x)$ 在零时微分得 $4B(x,x)=2B(x,x)$，所以 $B(x,x)=0$。对称双线性极化给 $B=0$，即 (448.1)。若原 $E$ 不完备，流只在辅助 $X$ 上使用；没有据此把指数或流值解释成原合法操作。∎

## 449. 实部相容迫使虚部相容并接回完整理论

**定理 449.1（固定同一旧关系的完整等价）。** 在定义 424.1 的完整原资料上，

$$
\boxed{\mathsf C_R\Longleftrightarrow\mathsf C_{\rm sq}
\Longleftrightarrow\mathsf C_{I,+}
\Longleftrightarrow\mathsf C_I\Longleftrightarrow\mathsf C_3.}
\tag{449.1}
$$

其中后面三项取原词卷的同名候选；本卷 (424.3) 被删的准确虚部式成为推论，同一个 $ab=S(a,b)-\mathrm iD(a,b)$ 是复结合星乘法，原 $u$ 是两侧单位。

证明。446.1–447.1 未用任何三元式，已得 $L_u=I$。现在只把 (445.1) 用于 $(u,u,x)$，得 $D_u^2=0$。交替性给 $D_u u=0$，而 446.1 已给 $D_u$ 为顺序导子，所以 $e^{tD_u}=I+tD_u$ 是双向等距群。若 $D_u x\ne0$，则 $N(x+tD_u x)\ge|t|N(D_u x)-N(x)$ 无界，矛盾。因此

$$
D_u=0,\qquad D_a u=-D_u a=0.
\tag{449.2}
$$

448.1 现在可准确用于 $K=D_a$，给

$$
D(a,S(b,c))=S(D(a,b),c)+S(b,D(a,c)).
\tag{449.3}
$$

再用交替性，$D(S(a,b),c)=S(D(a,c),b)+S(a,D(b,c))$；与 (449.3) 合并，得

$$
D(S(a,b),c)+S(D(a,b),c)
=D(a,S(b,c))+S(a,D(b,c)).
\tag{449.4}
$$

最后一项是 $S(a,D(b,c))$。故 (424.3) 的两式完整恢复，已满足同一原资料上的 $\mathsf C_{\rm sq}$，无需新增条件。反向只删虚部式。直接应用 428.1 即得其余等价，以及 427.1 的原锥准确切回、全部有符号夹心保正和完整旧表示；不重建旧 GNS。辅助存在端仍准确是原词卷 399.1 的恢复前端加 399.3 的 $\mathsf{Cmp}_{385}^{\rm alg}$ 存在，不识别任意先给的 native $K/J$。与[端点闭合卷](AURIC_C128_EFFECT_SANDWICH_CLOSURE_AND_INTERNAL_UNIT.md)18.1–18.2 复合，还等价于同一原资料上的 $\mathsf C_{{\rm nd},+}$。

实部 (445.1) 与 (449.4) 是 $E\oplus\mathrm iE$ 上结合子的两部分，故同一原复化乘法结合；对称／交替性使原共轭反转乘法，(447.1)、(449.2) 给原单位。只有在这些结论后，427.1 的 JB 完成及既有复星表示才被消费。全部恒等式先在原关系的唯一连续延拓上证明，再限制回同一原 $E$。∎

## 450. 删除后果、成对实例与有限三坐标

**命题 450.1（剩余条款的反事实边界）。** 429.1–429.3 的静态删除模型仍分别见证 $\mathsf C_R$ 的固定点、相加与效果平方上界不能直接全删。连 (445.1) 一起删除则仍可能破坏结合律，即使被删的虚部式恰好成立。

证明。前三个模型本已满足两条三元式，所以仍满足保留的实部式：零乘法只违反固定点；$F(x)=(x+x^3)/2$ 的同一可乘弯曲线保留效果收缩而违反原相加零关系；两份评价 $x+y,2x+y$ 的逐坐标乘法模型保留固定点与结合，却以原效果 $(2,-1)$ 的平方读数 $5>1$ 违反收缩。全量词与原锥均取各原命题，不重新选择评价。

对三元式直接复用 429.4 的同一 $M_2(\mathbb C)_{\rm sa}$、通常 Jordan 乘法和 $D=0$ 模型。其全部纯表、相加、固定点、效果平方上界及虚部式成立，但原 $X\circ X=u,X\circ Z=0$ 给 $(X\circ X)\circ Z=Z\ne0=X\circ(X\circ Z)$，实部式失败。这只给准确静态接口的删除见证，不冒充完整实际 $\Omega$ 的反模型，不证明全部条款或三标签数完全独立。

反过来，若 (449.4) 在完整保留入口下失效，(448.2) 将产生非零对称双线性缺陷；其二次流既必须为保零满射等距映射，又必须有非零二次速度，与 448.1 的 Mazur–Ulam 及齐次性计算矛盾。这是该虚部式不能独立漂移的准确后果，不是另加导子公理。∎

**命题 450.2（对称单位已经成立仍可能有有向漂移）。** 不给任何三元式时，定义 445.1 的其余全部静态条件甚至容许 $S$ 已是有单位的 Jordan 乘法，而 $D(u,a)\ne0$。因此 449.1 在恢复有向单位时消费的实部式不能由对称单位代替。

证明。取原 $E=\mathbb R\oplus\mathbb R^2$、$u=(1,0)$，写 $a=(t,x),b=(s,y)$，令 $J(x_1,x_2)=(-x_2,x_1)$，并取

$$
\begin{aligned}
\alpha_{m,n}(t,x)&=m(t+n\cdot x),\qquad m\ge0,\quad\|n\|=1,\\
S(a,b)&=(ts+x\cdot y,\ ty+sx),\\
D(a,b)&=(x\cdot Jy,\ tJy-sJx).
\end{aligned}
\tag{450.1}
$$

全部原评价实线性且分离，其准确原锥为 $t\ge\|x\|$，原序单位范数为 $N(t,x)=|t|+\|x\|$。平方 $a^2=(t^2+\|x\|^2,2tx)$ 原正，$S(u,a)=a$。令 $A_n(a)=t+n\cdot x$、$H_n(a)=(Jn)\cdot x$、$z_n(a)=A_n(a)+\mathrm iH_n(a)$，在正交基 $(n,Jn)$ 中直接展开得

$$
g_{\alpha_{m,n}}(a,b)=m\,\overline{z_n(a)}z_n(b).
\tag{450.2}
$$

所以所有有限纯表正，包含重复标签；$z_n$ 实线性使原相加比较平方恒零。原效果 $e=(t,x)$ 满足 $\rho=\|x\|\le h=\min(t,1-t)$；写 $H=\max(t,1-t)$，则 $e-e^2$ 的标量部分减去向量部分长度为

$$
t(1-t)-\rho^2-|1-2t|\rho=(h-\rho)(H+\rho)\ge0.
\tag{450.3}
$$

故完整效果平方收缩成立。$a^2=2ta+(\|x\|^2-t^2)u$ 又给 $[L_a,L_{a^2}]=0$，所以这里的原 $S$ 确为 Jordan 乘法，不是借不分离或非 Jordan 的假模型留下漂移。

然而取 $v=(0,(1,0))$，$D(u,v)=(0,(0,1))\ne0$。$(u,u,v)$ 上实部式左右分别为 $v,2v$，虚部式左右分别为 $D(u,v),2D(u,v)$。这个三实维圆锥模型只反驳未给三元式时的有向单位推论，明确不满足 $\mathsf C_R$；它与 429.4 的 $D=0$ 模型分别定位单位处的有向漂移和保单位后的对称不结合。未声称它实现完整实际 $\Omega$。∎

**命题 450.3（静态同读数仍不供应实现与更新）。** 全部原复 Gram 读数相同、原评价分离时，两份原 $S,D$ 必相同；但辅助表示重数和实际更新不能由这点读数唯一指定。

证明。取实、虚部并用分离性直接得同一旧 $S,D$。在通常矩阵实例中，$\pi_1(a)=a$ 与 $\pi_2(a)=a\otimes I_k$，评价向量分别为 $v$ 和 $v\otimes\eta$（$\|\eta\|=1$），给全部原静态及乘积读数相同而表示重数不同。对秩一投影测量 $\{p_0,p_1\}$，两份分支映射 $\rho\mapsto p_i\rho p_i$ 与 $\rho\mapsto\operatorname{tr}(p_i\rho)p_0$ 有同一当前效果概率；结果 $i=1$ 后再测 $p_0$，两者分别给零与分支总质量。零质量分支不指定条件态。完整原后续历史会区分它们，故没有把同一当前概率升成同一仪器。∎

**推论 450.4（原双关系的三实坐标与更大结构）。** 对原 $m_\alpha>0$，置 $v_a=\alpha(a^2)-\alpha(a)^2/m_\alpha$、$v_b=\alpha(b^2)-\alpha(b)^2/m_\alpha$、$c=\alpha(S(a,b))-\alpha(a)\alpha(b)/m_\alpha$、$d=\alpha(D(a,b))$，则 $c^2+d^2\le v_av_b$；$v_a+v_b>0$ 时 $(2c,2d,v_a-v_b)/(v_a+v_b)$ 属于闭单位球。

证明。(449.1) 接回 430.1 的同一单位中心化表；零质量评价恒零，零总方差时表零，分别不作除法。更大结构中的两类原作用都先成为原锥完成上的顺序导子；$D_a$ 此后保单位且保持 $S$，而 (445.1) 等价于 $[D_a,D_b]=-[L_a,L_b]$。前者是混合组合规则，后者是两种作用的交换子关系；共同组成复结合结构。三实坐标只描画两份中心化响应的有限截面，不是原 $E$、辅助 $H$ 或物理空间的全局维数，也不供应实际 qubit。∎

## 451. 量子公理的条件对应与成熟工具边界

**定义 451.1（完整消费者）。** 定理 449.1 使定义 431.1 及原词卷 425.1 的全部消费者在同一参数、符号、尺度与原来源下接回：

| 量子结构 | 由新候选恢复的部分及保留条件 |
| --- | --- |
| 复 Hilbert 与可观测量 | 既有忠实有界表示 $\pi:E\to B(H)_{\rm sa}$；$\pi(u)=I$，原 $S$ 映为 Jordan 乘法，原 $D$ 映为 $\mathrm i[\pi(a),\pi(b)]/2$。不预设有限维、原 $E$ 完备或像满射。 |
| 态、效果与 Born 读数 | 原 $\alpha(e)=\langle F\xi_\alpha,\pi(e)F\xi_\alpha\rangle$、$\|F\xi_\alpha\|^2=m_\alpha$；原效果恰映入原响应像内的正收缩。只在正质量时归一，原 $q$ 与中心权不换成 Born 概率；辅助向量不自动是实际准备。 |
| 原 native、全词与真实联合 | 指定比较身份、全部中心对及不等维／经典块、旧乘法、交叉零、生成分离、实际乘积与全部相关输入继续按原合同承担；辅助存在不指定 native 身份。 |
| CP 与完整参考 | 保留全部合法前接及原后口、整台实际箭头反复旁接同源参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件、对全部相关正输入的支配和任意完整有限参考链。 |
| 仪器、记录与更新 | 每台设备的全部输入、typed 菜单与输出、细记录、失败、真分组、原 AC、精确 $N_u$、Xs、平方根词、接受归属及具名返回仍须原来源；Lüders 更新仍需完整输出校准，450.3 不能省略。 |
| 全部历史与极限 | 顺序、自适应、并行及全部合法未来，停止、拒绝、销毁、泄漏、遗忘、同数两侧与逆向返回保持；$B$ 与 $\mathsf B_{\rm cl}$、指定预对偶、正常性、非离散记录和无限历史各按原条件。 |
| 动力学与物理尺度 | 数学 $e^{tD_a}$ 只在辅助完成中证明；是否保持原 $E$、是否为原合法过程、是否保原比较与相位、物理钟和 Hamiltonian／能量、共同作用量及 $\hbar$ 仍须实际来源。同一 $\sigma,t_0$、固定 $d$、resolvent、共同仪器和 $3s+r\le1$ 的范围不扩大。 |

**定义 451.2（来源、简洁性与新增范围）。** 相加极化、原实双线性及全有限表直接复用 425.1 及其原词卷 420.1、400.1 来源。顺序导子切向判据准确见 Niestegge，[arXiv:1402.0158v2，§4 Lemma 3](https://arxiv.org/html/1402.0158v2#S4)；446.1 在本原序单位完成上给出了所需版本的证明。该文 Lemma 4 的 Leibniz 论证另用其事件和条件概率背景，本处没有借入；448.1 用二次流和成熟 Mazur–Ulam 定理补出本入口所缺的桥。后一定理的实赋范空间满射等距版本见 Bogdan Nica，[The Mazur–Ulam theorem，arXiv:1306.2380v1](https://arxiv.org/html/1306.2380v1)；447.3 的二项式矩与方差、指数及常微分方程的 Banach 空间存在唯一性均为证明内成熟工具。

Baez，[arXiv:2006.14741v5，Theorem 7](https://arxiv.org/html/2006.14741v5#S3) 把 Leibniz 与实部结合式共同列作复星代数恢复的前件；Theorem 12 另从含单位 JB 代数及斜顺序导子动力对应出发。本处先在旧总映射入口恢复切向、单位及 (449.3)，其后才适用这类代数识别；不把这些成熟结果的输入当作已经推出的定义。非结合 Vidav–Palmer 的赋范复代数和数值域条件、纯序 JB 识别的锥内反序齐次双射也未作为无偿前提使用。旧 427.1 的 JB 与二次表示来源仍沿 432.1。

此处 `repo-derived` 的承重综合限于同一原 $\mathsf C_{\rm sq}$ 入口：效果平方支配先给两类顺序导子，正顺序导子与总事件固定点恢复原单位，二次等距缺陷排除混合乘法漂移，保留实部三元式遂恢复被删虚部式。减少的是一个独立三元约束族，没有减少原世界或改换旧关系；等价模型类不表示总逻辑信息下降，不主张实际认证成本、文献优先权或全局公理最少。完整实际 $\Omega$ 是否供应入口关系、指定 native 身份、全部真实联合、完整设备历史和物理尺度仍是各自的来源义务。

## 452. 一条三元式如何带回另一条的完整白话

**定义 452.1（完整直观说明）。** 原世界的全部准备、实数比例、评价、质量、记录、失败、合法过去未来、真实联合与设备，以及两张旧二元关系都留下。先让任意三个响应的共同表为正，让原相加的定义差没有长度；总事件与自己组合不变，每个原效果的平方不超过自己。这样，某个正响应在一份正读数中已经为零时，它的平方也只能为零，共同正表便不许它与别的响应组合后偷偷从原正锥边界穿出去。对称组合与有向组合于是都生成数学上的保锥运动；总事件自身的对称作用还保持正方向，二项式平均把它压成真正的单位作用，这一步尚不需要换括号。现在只留一条三元关系，要求两次有向作用的交换子抵消两次对称作用的交换子；它先让单位处的有向漂移只能平方为零，而双向保距离又不允许这样的非零漂移。此后若有向作用还破坏对称组合，就会产生一种对称二次运动，既要弯曲又要保持全部距离；满射等距必须是线性的，二次齐次性又迫使这份运动为零，所以另一条混合换括号关系自动成立。两张原表由此组成同一复结合乘法，旧构造恢复自伴表示、原效果和保原质量的 Born 读数；三实坐标球只是两份中心化关系的截面，整个网仍可无限维。删掉剩余实部式，普通矩阵的 Jordan 乘法配零有向关系就会漏进来，换括号确实失败，因此没有把必要关系凭图画删光。数学保锥群和辅助空间并不替代真实设备；原 native 身份、所有相关参考和完整箭头、每台仪器的输出更新失败、全部历史及遗忘返回、无限历史、物理钟、能量和作用量仍由原来源逐项供应。少掉的是一条可以由整体正几何推出的独立关系，不是原世界的一部分。

## 追加锚 C128REALASSOCIATOR（本行以下为增补区）

## 453. 小效果与单一实部相容的共同候选

**定义 453.1（固定原关系的 $\mathsf C_{R,\theta}$）。** 原资料、总映射 $S,D$、分离评价、原锥、原序单位 $u$ 及全部实际来源取 424.1。固定正有理数 $0<\theta\le1$，只要求至多三标签的纯 Gram 正性（含重复标签）、原相加零平方、$S(u,u)=u$、小效果 $0\le e\le\theta u$ 上的 $S(e,e)\le e$，以及实部三元式 (445.1)。不要求虚部式、全部大效果收缩、单位律、双线性、Jordan、幂结合、导子、夹心保锥、完备性或有限维。

此候选同时保留 434.2 的小检查域与 445.1 的单独实部式；439.1 和 449.1 的两条独立等价本身不能证明这一共同削减充分。以下只补它们缺失的单位桥梁。

## 454. 小效果仍使两类原作用切着同一正锥

**定理 454.1（小区间下的切向恢复）。** 在定义 453.1 中不消费实部三元式，原 $S,D$ 已分别为实对称、实交替双线性；全部有限纯表正，二者有界，且在原序单位范数完成 $X$ 上，每个 $L_a=S(a,\cdot)$ 与 $D_a=D(a,\cdot)$ 都是顺序导子。

证明。准确复用 435.1 的不消费三元式的证明：$M_\theta=2/\theta-1$ 给 $N(a^2)\le M_\theta N(a)^2$ 及两个乘法界。原锥完成、原评价仍为 norming 及 $E\cap X_+=E_+$ 沿 446.1 的评价与稠密逼近证明，不消费全效果收缩。

若 $e\in[0,\theta u]\subset X$，取 $a_n\in E$ 且 $N(a_n-e)\le\epsilon_n\downarrow0$，则

$$
e_n=\frac{a_n+\epsilon_nu}{1+2\epsilon_n/\theta}
\in[0,\theta u]\cap E,\qquad e_n\longrightarrow e.
\tag{454.1}
$$

乘法有界使小区间平方收缩延到完成。每个 $c\in X_+$ 均可选有限 $r>0$ 使 $c/r\in[0,\theta u]$，故 $0\le c^2\le rc$。对任意连续正泛函 $\varphi$，若 $\varphi(c)=0$，则 $\varphi(c^2)=0$。446.1 中以实际原正元素表达复 Gram 二次型的论证，使全部有限纯表正性适用于这些数学正泛函；零对角遂给 $\varphi(L_a c)=\varphi(D_a c)=0$。同一定理已经证明的双向切向判据给结论。原数学正泛函没有被加入实际准备，辅助完成也不要求原 $E$ 完备。∎

## 455. 两种保距离作用的谱把单位偏移压成零

**定理 455.1（小区间与实部式恢复同一原单位）。** 候选 $\mathsf C_{R,\theta}$ 给 $S(u,a)=a$、$D(u,a)=0$ 对全部原 $a$ 成立。

证明。$E=0$ 时平凡。否则在辅助 $X$ 中置

$$
C=L_u,\qquad K=C-I,\qquad H=D_u.
\tag{455.1}
$$

454.1 给 $C,H$ 为顺序导子，$I$ 也是顺序导子，故 $K$ 仍是顺序导子。固定点和交替性给 $Ku=Hu=0$。于是 $e^{tK},e^{tH}$ 是原序单位范数的双向等距群。此时没有断言 $C$ 为正算子，也没有使用大效果 $u-tc$ 的平方收缩。

只把实部式用于 $(u,u,x)$，得 $C-C^2+H^2=0$，即

$$
K+K^2=H^2.
\tag{455.2}
$$

为准确使用成熟 Banach 代数谱工具，在数学复化 $X_{\mathbb C}$ 上取

$$
N_{\mathbb C}(x+\mathrm iy)
=\sup_{t\in\mathbb R}N(x\cos t-y\sin t).
\tag{455.3}
$$

这是复范数，位于 $\max\{N(x),N(y)\}$ 与 $N(x)+N(y)$ 之间，故复化完备；每个原实线性等距的复延拓仍是等距。下文的谱都在 $B(X_{\mathbb C})$ 中取，不宣称这是已恢复的物理复乘法或原合法操作。

有界双向指数群使 $\operatorname{Sp}(K),\operatorname{Sp}(H)\subseteq\mathrm i\mathbb R$。所需事实可由 Laplace resolvent 直接核对：$\operatorname{Re}\lambda>0$ 时 $\int_0^\infty e^{-\lambda t}e^{tK}\,dt$ 是 $\lambda I-K$ 的双侧逆；负实部用负时间同证，$H$ 亦同。多项式谱映射及 (455.2) 给

$$
\{\lambda+\lambda^2:\lambda\in\operatorname{Sp}(K)\}
=\operatorname{Sp}(H^2)\subseteq(-\infty,0].
\tag{455.4}
$$

若 $\lambda=\mathrm ir$，则 $\lambda+\lambda^2=-r^2+\mathrm ir$，故 $r=0$。复 Banach 空间非零时谱非空，因而 $\operatorname{Sp}(K)=\{0\}$。

此处使用成熟 Gelfand 有界双向幂定理：含幺复 Banach 代数中，可逆元 $T$ 若 $\operatorname{Sp}(T)=\{1\}$ 且 $\sup_{n\in\mathbb Z}\|T^n\|<\infty$，则 $T=I$。对每个固定实 $t$，指数谱映射给 $\operatorname{Sp}(e^{tK})=\{1\}$，而所有整数正负幂都是等距，故 $e^{tK}=I$。在零处微分得 $K=0$，即 $C=I$。(455.2) 再给 $H^2=0$；$e^{tH}=I+tH$ 的双向等距排除线性无界漂移，故 $H=0$。限制回同一原 $E$ 得结论。没有使用 Hilbert 自伴性、正常算子、有限维平均或任意 Banach Hermitian 算子的平方仍 Hermitian 等额外断言。∎

## 456. 单位恢复后只消费既有混合刚性与完整理论

**定理 456.1（共同削减与全部原候选等价）。** 在同一原资料上，对每个固定正有理 $0<\theta\le1$，

$$
\boxed{
\mathsf C_{R,\theta}
\Longleftrightarrow\mathsf C_\theta
\Longleftrightarrow\mathsf C_{\rm sq}
\Longleftrightarrow\mathsf C_R.
}
\tag{456.1}
$$

因此同一旧复乘法、原锥、全部效果、有符号夹心和完整原量子消费者沿 439.1、449.1 接回。

证明。454.1 已给全部 $L_a,D_a$ 为顺序导子，455.1 已给原对称单位与 $D_a u=-D_u a=0$。448.1 的证明实际只消费有界对称双线性 $S$、其单位和全部 $L_a$ 为顺序导子：缺陷 $B_K$ 对称且每个 $B_a$ 为保单位顺序导子，二次流等距、全实时间且满射，Mazur–Ulam 与齐次性使它为零。故可直接复用该证明，不提前要求全效果收缩。用于 $K=D_a$ 得 $D_a$ 保持 $S$，交替性给原虚部式，最后一项准确为 $S(a,D(b,c))$。

于是已满足完整小效果候选 $\mathsf C_\theta$。此时才调用 439.1：带有限常数的结合星代数预表示和原序预算中的削平方递推排除负谱，恢复原准确正锥、全部夹心及全部效果收缩。由此得到 $\mathsf C_{\rm sq}$，再用 449.1 接回 $\mathsf C_R$ 及其余旧候选。反向由全效果候选直接限制到 $[0,\theta u]$ 并删去虚部式。辅助比较仍是原词卷 399.1 的恢复前端与 399.3 的 $\mathsf{Cmp}_{385}^{\rm alg}$ 存在，不取得预定 native 比较身份。∎

## 457. 反事实与三坐标几何

**命题 457.1（共同削减不允许再把剩余关系直接抹掉）。** 零乘法、可乘弯曲线及矩阵 Jordan／$D=0$ 的旧静态删除模型，仍分别见证固定点、原相加和实部式不能全删；对任意正 $\theta$，错误评价锥仍被小效果检出，零检查域则不足。

证明。前三者已有全部效果收缩，故满足所有小区间收缩；分别复用 429.1、429.2、429.4 及 450.1 的准确静态模型。错误锥直接复用 440.2 的 $e=\theta(1,-1)$：它是原小效果，但一份零读数的平方读数为 $2\theta^2>0$。$\theta=0$ 失去此约束。450.2 的三实维模型又表明，对称单位已经成立时有向单位仍可漂移，故不能把 455.2 省略为单位的命名。所有模型均限于所声明静态接口，不冒充完整实际 $\Omega$ 的反模型或全部条款独立。∎

**推论 457.2（同一中心化球与谱几何）。** 全部效果恢复后，450.4 的 $(2c,2d,v_a-v_b)/(v_a+v_b)$ 仍落在闭单位球；仅在正质量和正总方差时归一。单位桥中的谱只约束原作用在辅助 Banach 复化上的频率，不改变原网的维数。

证明。456.1 先接回完整原单位中心化表，再直接应用 450.4。455.4 将两种保距离作用的谱联系在同一算子等式中，纯虚数 $\mathrm ir$ 的线性项无法留在非正实谱内，故单位偏移的谱只能为零；Gelfand 刚性再排除零谱而非零的有界漂移。这是共同实现的谱关系，不把两个分别可达的谱点当作同时可达。三标签、三实坐标和辅助谱均不供应实际 qubit 或物理三维。∎

## 458. 现有量子结构与全部来源合同

**定义 458.1（共同削减的完整消费者）。** 按 456.1 接回 451.1 及 442.1 的同一消费者，七项对应准确为：

| 量子结构 | 恢复的数学部分与继续保留的来源 |
| --- | --- |
| 复 Hilbert 与可观测量 | 同一有界忠实自伴表示，原 $S$ 为 Jordan 乘法、原 $D$ 为 $\mathrm i[\pi(a),\pi(b)]/2$；不推出原 $E$ 完备、有限维、像满射或任意算子可取得。 |
| 态、效果与 Born 质量 | 保全部原评价和质量，准确原锥及原效果；只对正质量归一，原 $q$ 与中心正权不改成 Born 概率，辅助向量不自动是实际准备。 |
| native 与实际联合 | 原比较身份、全部中心对及经典／不等维块、旧乘法、交叉零、生成分离、实际乘积及全部相关输入继续由原合同供应；存在表示不指定 native。 |
| CP 与完整参考 | 全部合法前接和后口、整台箭头反复旁接同源参考、忠实交换两腿、共同真支持、三个实际投影及支持内补事件、全部相关正输入和任意完整有限参考链均保留。 |
| 仪器、更新与 TP | 每台原设备的全输入运输、typed 菜单、全部输出、细记录、失败、真分组、AC、精确 $N_u$、Xs、平方根词和接受归属仍供应；TP 依完整测试，Lüders 依完整输出校准，仍分有限维和指定正常前对偶。 |
| 全历史、遗忘与返回 | 全部原顺序、自适应、并行历史及合法未来、停止拒绝销毁泄漏、真遗忘、同数两侧和逆向返回保持；$B$ 不混为 $\mathsf B_{\rm cl}$，正常性、预对偶、非离散记录与无限历史各守原条件。 |
| 动力学与物理尺度 | 辅助指数群、Banach 复化和谱不供应原合法过程；是否保持原 $E$、比较和相位，物理钟、Hamiltonian 能量、共同作用量、$\hbar$ 和共同仪器继续各取原来源。同一 $\sigma,t_0$、固定 $d$、resolvent 及 $3s+r\le1$ 不扩张。 |

## 459. 文献工具与共同削减的准确增量

**定义 459.1（成熟工具与接口综合）。** 小效果有限界取 435.1，原锥完成及正泛函切向取 446.1 的证明，保单位混合刚性取 448.1，完整小效果返回取 439.1；各自在使用时核对实际前件，不把原完整候选免费借回更弱入口。成熟谱映射、指数及 Laplace resolvent、标准实 Banach 复化仅为 455.1 的证明内工具。

Gelfand 双向有界幂的单点谱定理及其成熟一般化，可准确参见 Osamu Hatori、Shiho Oi，[Spectral decomposition of doubly power-bounded elements in Banach algebras，arXiv:2604.08310v2，§1 及 Theorem 4.2](https://arxiv.org/html/2604.08310v2)。取该定理的单点谱 $\{1\}$ 即得 455.1 所用版本；它作用于含幺复 Banach 代数，不要求 $C^*$、Hilbert 或正常算子背景。这里只调用成熟单点谱结论，不认领其一般化。

本处 `repo-derived` 的承重综合是：小效果给原锥切向后，实部式在总事件处把两份保距离生成元锁成 $K+K^2=H^2$，谱映射与双向有界幂排除单位偏移，因而可在大效果和虚部相容尚未恢复时合法消费混合刚性，再由既有小效果定理恢复全体。减少的是同一原接口上同时独立检查的范围与约束族，不是两条独立等价的形式拼接；不声称总逻辑信息下降、实际认证成本更低、全局公理最少或文献优先权。完整原世界供应、native 身份和实际过程合同仍是所列来源义务。

## 460. 小检查域与单一三元式的完整白话

**定义 460.1（完整直观说明）。** 原世界的响应、准备、实数比例、质量、全部过去未来、真实联合、设备、记录和两张旧二元关系都留下。仍让任意三个响应的共同表为正，让原相加的定义差没有长度，让总事件自组合不变；现在只在总事件以下任意一段固定非零的小效果中检查平方不超过自身，并且只保留实部的三元换括号关系。小效果已经足够说明：在一份正读数里落到零的正响应，平方和两种交叉响应也不能偷偷穿出正锥，所以两种原作用都生成数学保锥运动。总事件的对称作用相对真正单位的偏移，以及总事件的有向作用，都固定总量，因而只能保距离；剩余实部式把前者加上自己的平方，锁成后者的平方。非零的转动频率会在前者留下不能落到平方谱里的方向部分，于是偏移只能有零谱；双向保距离又不允许零谱中藏着非零漂移，总事件遂成为真正的对称单位，有向作用也不再漂移。此后若有向作用破坏对称组合，就会产生既二次弯曲又保持全部距离的满射运动，线性等距刚性把这份缺陷压成零，虚部换括号随之恢复。同一个旧复乘法现在才是结合的，已有小效果定理再用同一原正响应不断削去少量平方：它始终困在原序预算里，负谱却会越削越负，所以负谱不能存在。原锥、全部大效果、有符号夹心、自伴表示和保原质量的 Born 读数因此一起接回。三实坐标球仍只是两份中心化响应的有限截面，辅助谱与数学完成也不是实际 qubit、物理空间或新设备；完整 native 身份、所有真实相关联合、整台箭头的全部参考、每台仪器的输出更新失败、全部历史遗忘返回、正常性和无限历史，以及物理钟、能量、共同作用量与 $\hbar$，仍由各自原来源供应。少的是独立检查的范围和一条关系，没有删去原世界，也没有把两个分开成立的简化直接当作可以同时成立。

## 追加锚 C128SMALLREAL（本行以下为增补区）

## 461. 三标签只检查坐标相位与差分面的完整候选

**定义 461.1（固定原关系的 $\mathsf C_{F,\theta}$）。** 原资料、同一个旧总映射 $S,D$、分离实线性评价、原锥、原序单位 $u$、全部实际来源及固定有理 $0<\theta\le1$ 取 453.1。记 $e_j$ 为三坐标中的第 $j$ 个实标准基，置

$$
F_3=\bigcup_{j=1}^3\{x+\mathrm it e_j:x\in\mathbb R^3,\ t\in\mathbb R\}
\ \cup\ \{z\in\mathbb C^3:z_1+z_2+z_3=0\}.
\tag{461.1}
$$

只把 453.1 的纯表条件换成：每个原评价下，至多二标签纯 Gram 表为正；对任意三标签（含重复），只要求 $z^*Gz\in[0,\infty)$ 对 $z\in F_3$ 成立。原相加零平方、$S(u,u)=u$、$[0,\theta u]$ 上平方收缩和唯一实部式全部保持。不另给虚部式、双线性、单位、Jordan、导子、夹心保锥、原完备性或有限维。

这把三标签的独立系数检查限制为实方向中的一份坐标相位，以及闭合差分面；标签范围没有缩小。两类方向须同时保留，不能把第二类悄悄省掉后直接引用跨平面拼接。

## 462. 局部系数检查仍能看见实零方向的全部配对

**引理 462.1（实方向与单坐标的二点压缩）。** 在定义 461.1 下，每个三表 $G$ 为 Hermitian；对任意 $v\in\mathbb R^3$、任意 $j$，其在复线性张成 $\operatorname{span}_{\mathbb C}\{v,e_j\}$ 上的二次型非负。因此 $v^*Gv=0$ 时 $v^*Ge_j=0$ 对全部 $j$ 成立。

证明。至多二标签正性先给每个条目的 Hermitian 对称性。对任意 $\alpha,\beta\in\mathbb C$，若 $\alpha\ne0$，将 $\alpha v+\beta e_j$ 乘一个模一数，使 $\alpha$ 为实数；所得向量属于 (461.1) 第一类，二次型不变。$\alpha=0$ 也在该类中。故压缩二表为正；零对角的 Cauchy–Schwarz 给末句。这里仅对已有三表的同一坐标配对，不引入第四标签。∎

**引理 462.2（实部先恢复原实双线性）。** 候选 $\mathsf C_{F,\theta}$ 已使原 $S$ 实对称双线性，原 $D$ 交替；原序单位范数 $N$ 满足 $N(a^2)\le M_\theta N(a)^2$，且两个逐点读数乘法界成立，其中 $M_\theta=2/\theta-1$。

证明。准确消费原词卷 420.1 的代数极化证明。它把相加表中的实零方向与同表坐标配对，以及把 $(a,-a)$ 的实零方向放入 $(a,-a,c)$；这些步骤均由 462.1 供应。原 $S$ 因而对称双可加、有理双线性，原 $D$ 交替。435.1 中两份小效果 $\theta(u\pm a/r)/2$ 的平方上界只用这个有理双线性、固定点和小效果收缩；得到同一个有限 $M_\theta$。二标签 Cauchy–Schwarz 给

$$
|g_\alpha(a,b)|\le M_\theta m_\alpha N(a)N(b).
\tag{462.1}
$$

所以 $N(S(a,b)),N(D(a,b))\le M_\theta N(a)N(b)$，这里不提前把 $D$ 称为双线性。435.5 的有理逼近只用于已经双可加的 $S$，把同一个旧 $S$ 升为实双线性。原序界仍使零质量评价在整个 $E$ 上恒零；$E=0$ 的分支平凡。没有消费实部式或原单位律。∎

## 463. 差分面补上有向关系的跨平面拼接

**定理 463.1（同一原 $D$ 与全部有限纯表恢复）。** 定义 461.1 使同一个旧 $D$ 实交替双线性，且全部有限纯 Gram 表正。

证明。固定原 $\alpha$，记 $b(a,c)=\alpha(S(a,c))$、$\delta(a,c)=\alpha(D(a,c))$ 及 $p(a)=\sqrt{b(a,a)}$。462.2 已使 $b$ 成为正半定实双线性型。原词卷 400.1 中 (400.3) 的实差方向与单坐标 Cauchy–Schwarz 由 462.1 给出；其 (400.4)–(400.6) 的齐次性及每个实二维平面上的交替双线性，只使用实零方向与同表坐标的配对，也由 462.1 给出。这些步骤均容许半范数退化，不除以质量。

剩下的跨平面步骤另有实际前件。对任意原 $x,y,z$，系数向量

$$
(-\lambda-\mu,\lambda,\mu)\in F_3
\qquad(\lambda,\mu\in\mathbb C)
\tag{463.1}
$$

使差方向 $y-x,z-x$ 的二阶剩余表为正。其实部对角准确为 $p(y-x)^2,p(z-x)^2$，虚部交叉项为

$$
\delta(y,z)-\delta(y,x)-\delta(x,z).
\tag{463.2}
$$

所以原词卷 (400.7) 的整个二点压缩以及其虚部界仍成立。现在只复用该证明的共同平移 $x_R=Rc,y_R=Rc+a,z_R=Rc+b$、平面化简 (400.8) 和由 462.1 供应的 (400.9)。得到同一个

$$
R|\delta(c,b-a)+\delta(c,a)-\delta(c,b)|
\le p(a)\bigl(p(b)+p(b-a)\bigr)
\qquad(R>0).
\tag{463.3}
$$

右端与 $R$ 无关，故绝对值为零。有理、实齐次及交替性遂接回两槽实线性；全部原评价分离使结论属于同一个旧 $D$。没有把两个差方向的复比较改成只查一份坐标相位。

最后任取有限原标签 $a_i$ 和系数 $z_i=x_i+\mathrm iy_i$，令 $A=\sum_i x_i a_i$、$B=\sum_i y_i a_i$。已恢复的双线性给

$$
\sum_{i,j}\overline z_i z_jg_\alpha(a_i,a_j)
=\alpha(A^2+B^2+2D(A,B))\ge0.
\tag{463.4}
$$

最后的不等式只是原二标签 $(A,B)$ 在系数 $(1,\mathrm i)$ 上的正性；符号为 $+2D(A,B)$。因此全部有限纯表恢复，不要求原 $E$ 完备，也不把这些数学聚合响应解释成新实际准备。∎

## 464. 同一完整量子候选及其来源全部接回

**定理 464.1（固定原资料的完整等价）。** 对同一原资料、同一个旧 $S,D$ 和每个固定正有理 $0<\theta\le1$，有

$$
\boxed{
\mathsf C_{F,\theta}\Longleftrightarrow\mathsf C_{R,\theta}
\Longleftrightarrow\mathsf C_\theta
\Longleftrightarrow\mathsf C_{\rm sq}
\Longleftrightarrow\mathsf C_R.
}
\tag{464.1}
$$

证明。462–463 在不消费任何三元式时恢复全部有限纯表正、同一实双线性关系及其有限界。因此此时才满足完整 453.1，直接消费 454–456：小效果锥切向、$K+K^2=H^2$ 的谱单位桥、保单位混合刚性与虚部相容、原序预算排负谱，顺序接回原锥、全部效果、有符号夹心、同一旧复结合星乘法及完整原条件理论。反向只在完整纯表中限制系数到 $F_3$，其余条件没有变。辅助比较仍是原词卷 399.1 的恢复前端加 399.3 的 $\mathsf{Cmp}_{385}^{\rm alg}$ 存在；不指定预定 native 身份。∎

## 465. 局部检查范围严格缩小的有限矩阵见证

**命题 465.1（一张局部通过而整体不正的三表）。** (461.1) 的系数检查本身严格弱于任意复系数正性，即使三表已 Hermitian 且全部二阶主子表正。

证明。在通常欧氏 $\mathbb R^3$ 中取 $w=(2/3,2/3,-2/3)$，令 $Av=w\times v$、$G=I+\mathrm iA$。$A$ 实反对称，故 $G$ Hermitian；其二阶主子式为 $1-4/9=5/9>0$。对第一类 $z=x+\mathrm it e_j$，有

$$
z^*Gz=\|x\|^2+t^2-2t\,x^TAe_j\ge0,
\qquad \|Ae_j\|^2=8/9<1.
\tag{465.1}
$$

对第二类置 $n=(1,1,1)/\sqrt3$。$\sum z_i=0$ 使其实部和虚部都在 $n^\perp$；$A$ 在该平面内的压缩范数为 $|w\cdot n|=2/(3\sqrt3)<1$，同一个二次型仍非负。但

$$
\operatorname{Sp}(G)=\{1,1+2/\sqrt3,1-2/\sqrt3\},
\tag{465.2}
$$

末项为负，故完整三表不正。这个静态矩阵只见证局部系数检查域确实变小；它不满足完整候选的全部关系，也不宣称两份等价完整模型类严格包含或完整 $\Omega$ 已实现。∎

**命题 465.2（其余反事实与三坐标仍按原条件）。** 457.1 的零乘法、可乘弯曲线、矩阵 Jordan／$D=0$ 及错误评价锥，仍给其所声明的删除边界。457.2 的中心化三实坐标球及 458.1 的七项量子对应全部保留。

证明。那些满足完整纯表的静态模型也满足局部系数检查；失败条款仍按各自原模型计算。464.1 恢复完整原表后才消费中心化球及完整消费者，仍只对正质量和正总方差归一。局部检查中的三坐标、差分面和有限矩阵不推导实际 qubit、物理三维或完整世界的条款独立性。∎

## 466. 原量子公理对应、完整来源与准确增量

**定义 466.1（全部消费者与研究边界）。** 本候选完整接回 458.1 的七行：同一有界忠实自伴表示与可观测量；原质量下的态、效果及正质量 Born 归一；原 native 与实际联合；完整参考下的 CP；全输出仪器、更新及 TP；全部历史、遗忘与返回；有原钟及物理尺度的动力学。每一行的原条件均保留：全部中心对与经典／不等维块、相关输入和旧乘法；整台箭头的全部参考与共同真支持、实际投影及支持内补；每台仪器的全输入运输、完整 typed 菜单、所有输出细记录失败、AC、精确 $N_u$、Xs、平方根词及接受归属；全部合法顺序、自适应和并行历史、未来、停止拒绝销毁、真分组遗忘、同数两侧及逆向返回，且 $B$ 与 $\mathsf B_{\rm cl}$ 分开；正常性、指定预对偶、非离散记录与无限历史；原相位、物理钟、Hamiltonian 能量、共同作用量、$\hbar$ 及共同仪器。同一 $\sigma,t_0$、固定 $d$、resolvent 和 $3s+r\le1$ 的范围不扩张。辅助完成、向量、谱与流均不供应原合法操作，存在表示不指定 native。

新增 `repo-derived` 内容限于原接口上对纯三表独立系数检查域的削减，以及 465.1 的准确局部严格性见证。代数极化、实零方向、半范数 Cauchy–Schwarz、共同平移拼接及全有限表聚合直接复用原词卷 420.1、400.1–400.2 的实际证明；462.1 和 (463.1) 逐步核对它们需要的弱入口，不重做旧谱单位桥或 GNS。成熟谱与 Mazur–Ulam 工具及其来源仍取 459.1。没有认领这些成熟一般结果、全局最少、完整量子起源、有限认证、实际取得或验证成本下降；也没有把局部严格性当成完整模型类的逻辑信息下降。全部真实来源为何共同供应这些关系仍是原未决义务。

## 467. 只看坐标相位和差分面怎样接回全表的完整白话

**定义 467.1（完整直观说明）。** 原世界、全部准备与实数比例、质量、历史未来、真实联合、设备记录及两张旧二元关系都留下，仍保留原相加没有长度、总事件自组合不变、小效果的平方不过界和实部的三元换括号。现在三个标签放在一起时，不再独立检查所有复相位组合：只让一个坐标带相位，其余走实方向；另检查三份系数相加为零的差分面。第一类足以让每个实零方向与同表的各个坐标真正脱钩，所以原相加先锁出同一个对称双线性关系，小效果再把它限制在有限预算内。有向关系在每个平面内也被锁住，但跨平面不能靠这一步跳过：第二类让两个差方向仍有共同的正比较；把三个点一起平移得越来越远，有向加法若留下固定缺口，左边会随距离增长，右边的原差分预算却不变，于是缺口只能为零。同一个有向关系因此实数线性，任何长表的复系数现在都能聚合成两份原实响应，原二点正性便恢复整张表。此前的小效果与谱单位桥这时完整适用，再恢复单位、虚部换括号、原锥、大效果、有符号夹心、旧复乘法、自伴表示和保原质量的 Born 读数。一张有限矩阵证明少查的方向确实存在，但完整相加及原关系会把它排掉；所以少的是独立检查的方向，不是把错误表宣成真，也不是总逻辑信息或实际认证成本下降。三坐标和差分面只是响应关系的有限截面，完整 native、所有真实相关联合、全箭头参考、每台仪器的输出更新失败、全部历史遗忘返回、正常性与无限历史以及物理钟能量作用量仍各取原来源，没有被数学辅助结构替代。

## 追加锚 C128RESTRICTEDGRAM（本行以下为增补区）

## 468. 只在相加与近邻三表上检查局部相位的完整候选

**定义 468.1（原序结构先定的标签族）。** 全部原资料、原 $E$ 与其实数比例、分离实线性评价 $\mathcal P$、原锥、原序单位 $u$、原质量、同一个旧总映射 $S,D$ 及所有实际来源取 453.1。原序单位范数 $N$ 只由这些原资料定义，不先依赖乘法。固定数学阈值 $\eta=1/4$，令 $\mathcal T$ 为相加三表 $(a+b,a,b)$，以及满足下式的三表及其排列：存在 $i\ne j$ 和 $\varepsilon\in\{1,-1\}$，使

$$
N(a_i-\varepsilon a_j)
\le\eta\max\{N(a_i),N(a_j)\}.
\tag{468.1}
$$

第三标签任意。$\eta$ 是定义检查族的固定几何阈值，不是正性误差或物理常数。

**定义 468.2（固定原关系的 $\mathsf C_{\mathcal T,F,\theta}$）。** 对固定正有理 $0<\theta\le1$，保留全部原至多二标签（含重复）复纯表正性；只有当原三标签属于 $\mathcal T$ 时，才要求其在 (461.1) 的 $F_3$ 上非负。继续要求全部原相加零平方、$S(u,u)=u$、小效果 $[0,\theta u]$ 上的平方收缩及唯一实部式 (445.1)。不另给单位、双线性、虚部式、Jordan、导子、夹心保锥、原完备性或有限维。相加表已在 $\mathcal T$ 中，故其零平方不是在一张完全未经局部检查的表上使用。

两种削减必须在同一份推导中共同成立。定义 461.1 的系数削减本身不能证明删去其他标签后三表仍足够；只对 $\mathcal T$ 给完整复 PSD 的另一条等价，也不能直接补回此处未检查的系数。

## 469. 相加表与反向表先恢复同一个实部

**引理 469.1（不消费三元式的有限界）。** 在定义 468.2 下，同一个旧 $S$ 已为实对称双线性，原 $D$ 交替且有逐点界

$$
N(S(a,b)),N(D(a,b))\le M_\theta N(a)N(b),
\qquad M_\theta=2/\theta-1.
\tag{469.1}
$$

证明。二表先给 Hermitian、对称／交替。相加 $(0,0,0)$ 的零平方给 $g(0,0)=0$，二表 Cauchy–Schwarz 给 $g(0,c)=0$。相加 $(0,a,-a)$ 的零方向放入 $(a,-a,c)$；后一表因有严格反向标签而属于 $\mathcal T$。462.1 的实方向／单坐标压缩证明只消费该表的 $F_3$ 检查，故取得原词卷 (420.1) 的奇性。其余 420.1 只在本来就属于 $\mathcal T$ 的相加表内配对实零方向。因此先得到同一个 $S$ 对称双可加及有理双线性。

此时才消费 435.1、462.2 的两份有理小效果与二表 Cauchy–Schwarz，取得统一有限 $M_\theta$。有理逼近把已经双可加的 $S$ 升为原实双线性；对 $D$ 此时只报逐点界，不借入其加法或实齐次。零质量评价由原序界在整个 $E$ 上恒零，$E=0$ 的分支平凡。∎

## 470. 五张近邻表消去跨平面的有向缺口

**定理 470.1（局部标签与局部系数共同恢复原 $D$）。** 定义 468.2 使同一个旧 $D$ 实交替双线性，不消费实部三元式。

证明。固定原 $\alpha$，记 $b=\alpha(S)$、$d=\alpha(D)$、$p(a)=\sqrt{b(a,a)}$；469.1 已使 $p$ 为实半范数。固定 $x\ne0$ 和任意原 $y,z$，置

$$
u_t=x+ty,\qquad v_t=x+tz,\qquad w=z-y.
\tag{470.1}
$$

对一切充分小的 $t>0$，以下五张表都属于 $\mathcal T$：

| 同一原三表 | 本证明消费的检查 |
| --- | --- |
| $(x,y,u_t)$ | 实零方向 $(1,t,-1)$ 与同表坐标，给 $d(x,u_t)=t d(x,y)$。 |
| $(x,z,v_t)$ | 同样给 $d(x,v_t)=t d(x,z)$。 |
| $(u_t,w,v_t)$ | 因 $v_t=u_t+tw$，给 $d(u_t,v_t)=t d(u_t,w)$。 |
| $(x,u_t,v_t)$ | 复差分面，控制两个小差方向的整个二点压缩。 |
| $(x,u_t,w)$ | 实差方向与第三坐标的二点压缩。 |

其合法性只用原 $N$：$u_t,v_t\to x\ne0$，每张表都有一对非零近邻，第三标签不受限制。阈值与可用的小 $t$ 不依赖当前评价的半范数。前三行的实零方向因 $b$ 实双线性而平方为零；462.1 只在该已检查三表上用第一类系数，故不先假设 $d$ 齐次，也不把零方向配到外部第四标签。

在第四张表内，令 $r=(-1,1,0)$、$s=(-1,0,1)$。任意 $\lambda r+\mu s=(-\lambda-\mu,\lambda,\mu)$ 都在 $F_3$ 的差分面中，所以压缩二表正；其对角为 $t^2p(y)^2,t^2p(z)^2$。Cauchy–Schwarz 给

$$
|g(u_t,v_t)-g(u_t,x)-g(x,v_t)+g(x,x)|
\le t^2p(y)p(z).
\tag{470.2}
$$

取虚部并消费前三张表的准确关系，除以 $t>0$，得

$$
|d(u_t,w)+d(x,y)-d(x,z)|\le t p(y)p(z).
\tag{470.3}
$$

第五张表使用 462.1 的实方向 $r$ 与第三坐标，不要求这张表在所有复系数上正。它给

$$
|d(u_t,w)-d(x,w)|\le t p(y)p(w).
\tag{470.4}
$$

因此

$$
|d(x,z-y)+d(x,y)-d(x,z)|
\le t p(y)\bigl(p(z)+p(z-y)\bigr).
\tag{470.5}
$$

左侧与 $t$ 无关；仅令足够大的整数 $n$ 对应 $t=1/n$，右侧便趋零。故 $d(x,y+w)=d(x,y)+d(x,w)$。$x=0$ 由零标签成立，交替性给另一槽可加；469.1 的统一界再使有理逼近恢复两槽原实齐次。全部原评价分离，结论属于同一个旧 $D$。未用原 $E$ 完备性，也未把原 $N$ 下的近邻改成某个评价下的近邻。∎

## 471. 全表与完整原量子条件理论恢复

**定理 471.1（固定原资料的共同等价）。** 对同一原 $S,D$、全部原来源及固定正有理 $0<\theta\le1$，

$$
\boxed{
\mathsf C_{\mathcal T,F,\theta}
\Longleftrightarrow\mathsf C_{F,\theta}
\Longleftrightarrow\mathsf C_{R,\theta}
\Longleftrightarrow\mathsf C_\theta
\Longleftrightarrow\mathsf C_{\rm sq}
\Longleftrightarrow\mathsf C_R.
}
\tag{471.1}
$$

证明。469–470 恢复同一个旧实双线性 $S,D$。此时才用 (463.4)：任意有限复系数聚合为两份原实响应 $A,B$，原二表在 $(1,\mathrm i)$ 上的正性给 $\alpha(A^2+B^2+2D(A,B))\ge0$，故全部有限纯表正。于是真正满足完整 453.1，再准确消费 454–456 的锥切向、谱单位桥、混合等距刚性及原序预算排负谱，恢复同一原锥、大效果、夹心、单位、虚部式和旧复结合星乘法，再由 464.1 接回所列等价及完整原消费者。反向仅把完整三表的标签限制到 $\mathcal T$、系数限制到 $F_3$。两个较弱入口的单独等价没有替代 470.1 的共同前件核对。∎

## 472. 原检查域的反事实与有限几何

**命题 472.1（两种独立检查范围确实都缩小）。** $\mathcal T$ 不是全部三标签，逐标签非零缩放、改符号或排列也不把所有被删表重新纳入；$F_3$ 的逐表系数检查仍严格弱于完整复 PSD。

证明。取原序单位空间 $\mathbb R^3$、逐坐标原锥、$u=(1,1,1)$ 与坐标评价，故 $N=\|\cdot\|_\infty$。标准基表 $(e_1,e_2,e_3)$ 及任意非零逐标签缩放均线性独立，不是相加表；每一对的正负差范数都等于二者范数的最大值，比例为 $1>\eta$，所以不在 $\mathcal T$。系数的严格性由 465.1 的同一 Hermitian 矩阵给出；局部测试通过而全谱有负值。两项都只陈述原始检查域，不把它们当成等价完整模型类的严格包含，也不构造满足全部实际 $\Omega$ 合同的反模型。∎

**推论 472.2（不守关系时的准确后果）。** 若某个原 $d_\alpha(x,z-y)+d_\alpha(x,y)-d_\alpha(x,z)\ne0$，则充分小 $t$ 时 470.1 的五张被保留三表中至少有一张失去所用局部正性。若前三张局部实零关系已成立，失败只能发生在后两张共同差分比较中。

证明。否则同一份评价、同一组原标签和同一个 $t$ 给 (470.5)，其右侧趋零，与固定非零缺口矛盾。关键两个近邻元是 $x,x+ty$，外部第三方向是 $z-y$。这说明跨平面一致性需要何种关系，但不证明这些三表在全部保留条件下逻辑独立；单独二标签加其余关系是否充分仍未判定。457.1／465.2 的其他静态删除边界按原范围复用。∎

## 473. 大表背后的一个实度量与一个斜作用

**推论 473.1（每份原评价的辅助几何）。** 恢复后，对每个原 $\alpha$，$E/\ker p_\alpha$ 的实 Hilbert 完成 $H_\alpha$ 上存在唯一有界斜伴随收缩 $J_\alpha$，使

$$
d_\alpha(a,b)=\langle[a],J_\alpha[b]\rangle,
\qquad J_\alpha^*=-J_\alpha,\qquad\|J_\alpha\|\le1.
\tag{473.1}
$$

其辅助复化上的 $I-\mathrm iJ_\alpha$ 为正；不推出 $J_\alpha^2=-I$。

证明。原二表 Cauchy–Schwarz 给 $|d_\alpha(a,b)|\le p_\alpha(a)p_\alpha(b)$，故原交替双线性型降到同一半范数商并连续延拓。成熟实 Hilbert 空间 Riesz 表示给唯一 $J_\alpha$ 及范数界，交替性给斜伴随。复化后 $-\mathrm iJ_\alpha$ 自伴且范数不超过一，故所列算子为正。非零一维实核且 $d_\alpha=0$ 时 $J_\alpha=0$，已经说明正核本身不强制 $J_\alpha^2=-I$。不同评价给不同辅助实现；这些完成向量或 $J_\alpha$ 不自动是实际准备、动力学、共同复结构或新设备。正质量和正总方差条件下，457.2 的三实坐标球仍按原范围成立；三坐标不是物理维数。∎

## 474. 全部量子对应、来源与共同削减的边界

**定义 474.1（完整消费者及来源）。** 471.1 完整接回 466.1、458.1 的七项：同一忠实自伴表示与可观测量；保原质量的态、效果和正质量 Born 归一；原 native 与实际联合；完整参考下的 CP；全输出仪器更新与 TP；全历史遗忘返回；有原物理钟及尺度的动力学。全部中心对、经典与不等维块、旧乘法、交叉零、生成分离、实际乘积和相关输入；整台箭头反复旁接同源参考、忠实交换两腿、共同真支持、实际投影及支持内补、任意完整有限链；每台仪器的全输入运输、typed 菜单、所有输出细记录失败、真分组、AC、精确 $N_u$、Xs、平方根词和接受归属；全部合法过去未来、顺序自适应并行、停止拒绝销毁、真遗忘、同数两侧及逆向返回，$B$ 与 $\mathsf B_{\rm cl}$ 的区分；正常性、指定预对偶、非离散记录与无限历史；原相位、钟、Hamiltonian 能量、共同作用量、$\hbar$ 和共同仪器均保留。原 $\sigma,t_0$、固定 $d$、resolvent 与 $3s+r\le1$ 不扩张。辅助比较仍只给原词卷 399.1 的恢复前端加 399.3 的 $\mathsf{Cmp}_{385}^{\rm alg}$ 存在，不指定 native。

本处 `repo-derived` 增量限于同时只检查局部标签与局部系数的共同恢复：五张近邻表分别消费实零方向、差分面与单坐标压缩，在同一小参数下将跨平面缺口压成零。相加极化与小效果界直接复用 420.1、435.1 和 462；全表归并及后续量子理论直接复用 463–464、454–456。Riesz 表示、有界斜伴随算子的复化及自伴谱界只是成熟证明工具，不认领其一般结论或文献优先权。检查域仍有无限量词和精确关系，不主张有限认证、实际取得或验证成本下降、全局最少或完整量子起源。全部实际来源为何共同供应这些关系仍未由此解决。

## 475. 只看近邻怎样恢复整张关系网的完整白话

**定义 475.1（完整直观说明）。** 原世界、准备、实数比例、质量、历史未来、真实联合、设备记录及两张旧二元关系都留下，仍保留原相加零平方、总事件自组合不变、小效果平方不过界和实部换括号。三个标签不再任意选任意查：只查相加表，或其中两份响应足够接近、或足够接近反向的表；在这些表里也只查一份坐标相位和闭合差分面。相加与反向表先锁出同一个对称双可加关系和有理双线性，小效果的统一有限预算再使它尊重原实数比例。现在让两份响应一起贴近同一非零原响应：一张表要求两个小差分之间的相位配对只能有二阶大小，另一张表把这份小差分接到外部方向，限制它的一阶变化。如果不同平面之间仍藏着固定的加法缺口，就无法同时通过这两个越来越小的预算，所以缺口只能为零。原有向关系因此实数线性，任意长表才可以合法归并成两份原实响应，由二点正性恢复全表；此前的小效果与谱单位桥这时接回单位、虚部相容、原锥、大效果、夹心、旧复乘法、自伴表示和保原质量的 Born 读数。辅助几何可压成每份评价的一张实度量和一个有界斜作用，但它不是实际 qubit、物理三维或原合法过程。少的是独立检查的标签与方向，没有删去真实来源：native 身份、所有相关联合、完整参考、每台仪器的输出更新失败、全历史遗忘返回、正常性与无限历史、物理钟能量和共同作用量仍各取原合同；任意小的精确近邻也没有被冒充成有限精度装置。

## 追加锚 C128NEARBYRESTRICTED（本行以下为增补区）
