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
