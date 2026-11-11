# AURIC：全 PB 原始标定与共同源运输续卷

## 44. 三个原始平方与一个有向关系识别同一正映射

**定义 44.1（同一四维原模型与标定接口）。** 本卷承接[三演员核提升卷定义 41.1、式 (41.2)](AURIC_FULL_PB_THREE_ACTOR_KERNEL_LIFT_AND_AXIS_BLINDNESS.md#411-固定输入完整输出与原量词) 的完整 M4 模型；以下简称“母卷”的条目和公式均指该卷。固定

$$
\begin{gathered}
A=M_4(\mathbb C),\quad P=\operatorname{diag}(1,1,1,0),\quad Q=I-P,\quad J=P-Q,\\
c=\operatorname{diag}(1,2,3,0),\quad q=(q_1,q_2,0)^{\mathsf T},\quad q_1q_2\ne0,\\
t=\begin{pmatrix}0&q\\q^*&0\end{pmatrix},\quad
\sigma\in\{1,-1\}\text{ 分别固定},\quad\iota=\sigma i,\\
K(a,b)=\iota(ab-ba)/2,\qquad a\circ b=(ab+ba)/2,\\
R(x)=R_+(x)=x+K(c,x)-c\circ t\quad(x=x^*=PxP).
\end{gathered}
\tag{44.1}
$$

$q$ 的原复相位和大小任意且不改变；三个演员方向不是物理空间三维。矩阵单位 $E_{ij}$ 按原基编号 $1,2,3,4$，并置

$$
\begin{gathered}
F_{ij}(z)=zE_{ij}+\overline z E_{ji}\quad(i<j),\\
u_1=-q_1/2,\quad u_2=-q_2,\qquad
h_0=-c\circ t=F_{14}(u_1)+F_{24}(u_2),\\
x_0=0,\quad x_1=c,\quad
x_2=F_{12}\left(\frac{-2+4\iota}{5}u_1\overline{u_2}\right)
          +F_{13}\left(\frac{1+\iota}{2}\right),\\
W=F_{12}(\iota u_1\overline{u_2})+F_{13}(1),\qquad
r_j=R(x_j)\quad(j=0,1,2).
\end{gathered}
\tag{44.2}
$$

取正整数 $d$。标定针对同一个复线性、保单位、在整个正锥上为正的映射
$\Phi:M_4(\mathbb C)\to M_d(\mathbb C)$。这里不预给完全正性、任意复输入 Schwarz、保迹或保某一态，不允许按探针更换映射，也不把非保单位原映射正规化后当作它本身。目标中的 $K$ 始终使用同一个 $\iota$。

**定理 44.2（原始三探针的正映射充要标定）。** 在定义 44.1 下，$\Phi$ 是保单位 $*$-同态，当且仅当

$$
\Phi(r_j^2)=\Phi(r_j)^2\quad(j=0,1,2),\qquad
\Phi(K(r_0,r_1))=\frac{\iota}{2}[\Phi(r_0),\Phi(r_1)].
\tag{44.3}
$$

这是三个实际原始 $R_+$ 参数的充分数目，不主张最少探针数。平方输入 $r_j^2$ 与复合输入 $K(r_0,r_1)$ 的可读性是额外接口：没有断言它们也是某个合法演员设置的原始 $R(x)$。特别，本定理不是三次测量、免费相位控制或实际门可得性的结论。结论覆盖全部允许的复 $q_1,q_2$ 和每个分别固定的 $\sigma$；不覆盖 $q_1q_2=0$、一般环境、M5 第三格模型、近似等式或无限维映射。

### 44.1 原始值与平方等号的成熟接口

证明。每个 $x_j$ 自伴且满足 $Px_jP=x_j$。演员内第 $ij$ 格的线性部分 $x+K(c,x)$ 将 $x_{ij}$ 乘以 $1+\iota(c_i-c_j)/2$。准确地，

$$
(1-\iota/2)\frac{-2+4\iota}{5}=\iota,\qquad
(1-\iota)\frac{1+\iota}{2}=1.
$$

且 $K(c,c)=0$，故三个实际原始值为

$$
r_0=h_0,\qquad r_1=h_0+c,\qquad r_2=h_0+W.
\tag{44.4}
$$

没有独立消去或调节仿射环境项 $h_0$。

以下自伴平方步骤复用 [C139 有限返回续卷 (123.6)–(123.9)、定义 127.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)，其成熟来源为 Kadison，*A Generalized Schwarz Inequality and Algebraic Invariants for Operator Algebras*，[DOI 10.2307/1969657](https://doi.org/10.2307/1969657)。这里写出全部所需接口，避免误用复 Schwarz。正复线性映射保伴随：自伴元分解为两个正元之差，像自伴，再复线性延拓。对任意自伴 $a=\sum_k\lambda_k p_k$，置 $A_k=\Phi(p_k)\ge0$，

$$
Vv=(A_k^{1/2}v)_k,\qquad L_a=\operatorname{diag}_k(\lambda_k I_d).
$$

保单位给 $V^*V=I_d$，因此

$$
\Phi(a)=V^*L_aV,\qquad
D(a):=\Phi(a^2)-\Phi(a)^2
 =V^*L_a(I-VV^*)L_aV\ge0.
\tag{44.5}
$$

$V,L_a$ 随这份 $a$ 的谱分解改变，不是任意正映射的 Stinespring 表示。

对自伴 $a,b$ 写 $C(a,b)=\Phi(a\circ b)-\Phi(a)\circ\Phi(b)$。若 $D(a)=0$，则对每个实 $s$，

$$
0\le D(a+sb)=2sC(a,b)+s^2D(b).
\tag{44.6}
$$

在任意目标向量上取二次型，正负小 $s$ 迫使一次项为零；$C(a,b)$ 自伴，故 $C(a,b)=0$。这只给 Jordan 交织，不给左、右结合乘法域。

令 $\mathcal N=\{a=a^*:D(a)=0\}$。由 (44.6)，$\mathcal N$ 是含 $I$ 的实线性空间。还需核对平方闭合：若 $a\in\mathcal N$，(44.5) 给 $(I-VV^*)L_aV=0$，即 $L_aV=V\Phi(a)$。递推得 $L_a^kV=V\Phi(a)^k$，因而对任意实多项式 $f$，

$$
\Phi(f(a))=f(\Phi(a)).
\tag{44.7}
$$

特别，$\Phi(a^4)=\Phi(a)^4$ 与 $\Phi(a^2)=\Phi(a)^2$ 给 $D(a^2)=0$。再由实线性与 $(a+b)^2-a^2-b^2=2a\circ b$，$\mathcal N$ 是含单位的实 Jordan 子代数。以上均为标定证明中的成熟中间步骤，不另立一般正映射定理。

### 44.2 原始三元组生成全部十六个 Hermitian 方向

(44.3) 的三个平方等号使 $r_0,r_1,r_2\in\mathcal N$，故 $h_0,c,W\in\mathcal N$。$c$ 的四个谱值 $1,2,3,0$ 不同，其谱投影由 (44.7) 给

$$
\begin{aligned}
p_1&=c(c-2I)(c-3I)/2,&
p_2&=-c(c-I)(c-3I)/2,\\
p_3&=c(c-I)(c-2I)/6,&
p_4&=-(c-I)(c-2I)(c-3I)/6.
\end{aligned}
\tag{44.8}
$$

它们准确为 $E_{11},E_{22},E_{33},E_{44}$。对 $i\ne j$，$4p_i\circ(p_j\circ a)$ 提取 $a$ 的 Hermitian $ij$ 边。对 $h_0,W$ 提取得

$$
A_1=F_{14}(u_1),\quad A_2=F_{24}(u_2),\quad
Z=F_{12}(\iota u_1\overline{u_2}),\quad H_1=F_{13}(1)\quad\in\mathcal N.
\tag{44.9}
$$

矩阵单位的实际乘法给

$$
2A_1\circ A_2=F_{12}(u_1\overline{u_2}),\qquad
\frac{2}{|u_2|^2}Z\circ A_2=F_{14}(\iota u_1).
\tag{44.10}
$$

分母非零由 $q_2\ne0$ 保证。对任意 $z=r+\iota s\ne0$，

$$
F_{ij}(z)=rF_{ij}(1)+sF_{ij}(\iota),\qquad
F_{ij}(\iota z)=-sF_{ij}(1)+rF_{ij}(\iota).
\tag{44.11}
$$

系数行列式 $r^2+s^2=|z|^2>0$。因此 (44.9)–(44.10) 先给边 $12,14$ 的两个实伴轴。接着

$$
2F_{12}(1)\circ H_1=F_{23}(1),\qquad
2F_{12}(\iota)\circ F_{23}(1)=F_{13}(\iota),
\tag{44.12}
$$

故边 $13$ 也有两个伴轴。最后对 $1<j<k\le4$，

$$
2F_{1j}(z)\circ F_{1k}(w)=F_{jk}(\overline z w).
\tag{44.13}
$$

分别取 $(z,w)=(1,1),(1,\iota)$，得到其余每条边的两个伴轴。四个对角投影与六条边各两个伴轴是 $M_4(\mathbb C)_{\rm sa}$ 的全部 $4+2\cdot6=16$ 个实基方向。故 $\mathcal N=M_4(\mathbb C)_{\rm sa}$，$\Phi$ 保全部自伴 Jordan 乘积；复线性及保伴随使它是复 Jordan $*$-同态。这里使用的是实际非零 $u_1,u_2$，不借助把 $q$ 旋成实数的物理操作。

### 44.3 单个非零有向对消去反同态部分

此时才使用 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，定义 7.4.8、推论 7.4.9，印刷页 163：von Neumann 代数之间的正常 Jordan 同态是一个 $*$-同态与一个 $*$-反同态之和。$M_4,M_d$ 都是 von Neumann 代数，有限维线性映射正常，全部前件满足。因此写

$$
\Phi=\pi+\eta,
\tag{44.14}
$$

其中 $\pi$ 是 $*$-同态，$\eta$ 是复线性 $*$-反同态。不能先把任意嵌入说成全局“非此即彼”。$p=\pi(I)$、$q'=\eta(I)$ 是投影，$p+q'=I$ 使 $pq'=0$；两部分分别落在正交角中，交叉乘积为零。推论 7.4.11 的因子自同构结论不用于这个一般嵌入；也不省略定理 7.4.14 的无一维表示前件来使用它。

由 (44.4) 直接算得

$$
k:=K(r_0,r_1)=F_{14}(-\iota u_1/2)+F_{24}(-\iota u_2)\ne0.
\tag{44.15}
$$

反同态反转乘法次序，故

$$
\Phi(k)=\pi(k)+\eta(k),\qquad
\frac{\iota}{2}[\Phi(r_0),\Phi(r_1)]=\pi(k)-\eta(k).
\tag{44.16}
$$

有向等号给 $\eta(k)=0$。非零 $*$-反同态在简单结合代数 $M_4$ 上必单射：其核是双侧理想，而 $M_4$ 只有零与全代数两个双侧理想。由 $k\ne0$，只能 $\eta=0$，因此 $\Phi=\pi$ 是 $*$-同态。它对全部 $a,b$ 满足 $\Phi(ab)=\Phi(a)\Phi(b)$、$\Phi(a^*)=\Phi(a)^*$。反向保单位 $*$-同态保平方及同一 $\iota$ 的交换子，立即给 (44.3)。定理得证。∎

承重的 repo-derived 内容是 (44.2) 的三个实际仿射原始探针、(44.8)–(44.13) 在全部允许复 $q$ 上的完整生成，以及它们与 (44.15) 单个原始有向对的结合。Kadison、Jordan 分解、简单矩阵代数和 Peirce 公式是明确归属的中间工具；不认领一般工具为新定理或历史优先权。

## 45. 正缺陷的标量检测与同一 omega 的合法词应用

**定理 45.1（原始标定的忠实标量版与共同词版）。** 保持定义 44.1，定义目标中的自伴缺陷

$$
D_j=\Phi(r_j^2)-\Phi(r_j)^2\ge0\quad(j=0,1,2),\qquad
O=\Phi(k)-\frac{\iota}{2}[\Phi(r_0),\Phi(r_1)]=O^*.
\tag{45.1}
$$

若 $f(Y)=\operatorname{Tr}(\rho Y)$，其中目标密度 $\rho>0$、$\operatorname{Tr}\rho=1$，则 $\Phi$ 是 $*$-同态当且仅当

$$
f(D_0)=f(D_1)=f(D_2)=f(O^2)=0.
\tag{45.2}
$$

也可在同一定理中采用以下共同词接口，而不预给忠实目标准备：取一份固定 $\rho_0\ge0$、$\operatorname{Tr}\rho_0=1$ 和 $\omega(Y)=\operatorname{Tr}(\rho_0Y)$，以及同一有限合法酉门族 $(U_\alpha)$。每个有限词 $w$ 的乘积记为 $U_w$，空词为 $I$。要求这些实际词及下列复合缺陷读数在同一个来源合同内可用。若

$$
\mathcal S:=\operatorname{span}\{U_w\operatorname{ran}\rho_0:w\text{ 为合法有限词}\}
   =\mathbb C^d,
\tag{45.3}
$$

则存在有限 $L$，使 (45.2) 可等价地替换为对全部 $|w|\le L$ 的

$$
\omega(U_w^*D_jU_w)=0\quad(j=0,1,2),\qquad
\omega(U_w^*O^2U_w)=0.
\tag{45.4}
$$

这里词族要求所用的全部乘积确为合法；若合法性带类型或历史守卫，就须使用原已许可的同一词族和已成立的可达接口，不能把形式自由词都当作可执行词。$L$ 是存在的有限检测长度，不是免费给定的门深度或测量次数。

证明。由 (44.5)，$D_j\ge0$；$O$ 自伴给 $O^2\ge0$。忠实性使 $f(A)=0,A\ge0$ 蕴含 $A=0$：$\rho\ge\lambda I$ 对某个 $\lambda>0$，所以 $0=\operatorname{Tr}(\rho A)\ge\lambda\operatorname{Tr}A\ge0$。故 (45.2) 给三份算子平方等号及 $O=0$，再用定理 44.2。反向同态使四个正缺陷全零。输入态忠实不代替这里的目标检测条件；在 $d>1$ 时单一纯向量态并不忠实。

共同词版直接应用既有源码
[`PositiveBranchReachableResponse.finite_orbit_support_eq_word_span` 与 `finite_reachable_faithful_sum`](../../../D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.lean)
的有限正轨道结论。其 $K_\alpha$ 在这里取同一 $U_\alpha$，任取固定正权 $c_\alpha>0$，$\rho$ 取同一 $\rho_0$；源码的零长词为单位，新字母左乘。展开其有限轨道和，正是

$$
T_L=\sum_{|w|\le L}\gamma_w U_w\rho_0U_w^*,\qquad
\gamma_w=\prod_{\alpha\text{ 出现在 }w}c_\alpha>0.
\tag{45.5}
$$

已有结论给某个有限 $L$，使 $T_L$ 的支撑恰为 $\mathcal S$，且在该空间上有正下界。若 (45.3) 成立，就有 $T_L\ge\mu I_d$，$\mu>0$。对每个正缺陷 $A\in\{D_0,D_1,D_2,O^2\}$，(45.4) 给

$$
0=\sum_{|w|\le L}\gamma_w\omega(U_w^*AU_w)
  =\operatorname{Tr}(T_LA)\ge\mu\operatorname{Tr}A.
\tag{45.6}
$$

于是 $A=0$，接回定理 44.2。也可以只检查 (45.6) 的正加权和为零；每项非负时这与所有项为零等价。这是既有可达忠实和的模型应用，不另立一般可观测性定理，也不把读取源码说成新 kernel 核验。

若 $\mathcal S\ne\mathbb C^d$，同一推导只给 $A\mathcal S=0$：$\operatorname{Tr}(T_LA)=0$ 迫使 $A^{1/2}T_L^{1/2}=0$。对 $A=O^2$ 得 $O\mathcal S=0$。没有进一步的不变性或全目标可达性时，这不推出全局同态；漏检扇区在下面的 M8 例子中确实存在。

作为有条件的明确门族，若目标 $d$ 维的 Weyl 位移 $X$ 和相位 $Z$ 确为合法控制，取 $U_{ab}=X^aZ^b$，$0\le a,b<d$。复用[《辛预测完成》§6.1](SYMPLECTIC_PREDICTIVE_COMPLETION.md#61-有限-weyl-证书与相互作用) 的矩阵单位几何和，

$$
\frac1{d^2}\sum_{a,b}U_{ab}\rho_0U_{ab}^*=\frac{I_d}{d}.
\tag{45.7}
$$

确实相位平均先消去非对角矩阵单位，位移平均再把每个对角单位送成 $I_d/d$；乘以 $\operatorname{Tr}\rho_0=1$ 即得式子。$d^2$ 个词因而足以检测这四份正缺陷，但并不说明每份复合缺陷只需一次物理读出。$T_L$ 及 (45.7) 都是同一 $\omega$ 的读出设置的加权泛函，不是新准备出来的态或原世界新增的混合能力。整个论证只用

$$
p(w,e)=\omega(U_w^*eU_w),
$$

不要求每个门保持 $\omega$，也不假设 $\omega\circ\operatorname{Ad}_{U_w}=\omega$。源端 $r_j^2,k$、目标端 $\Phi(r_j)^2,O^2$ 及计算这些差所需的复合读出仍须实际共同可用，矩阵公式本身不供应这些接口。∎

在上述证明内，以下成熟反例限定标量条件。转置 $\tau(a)=a^{\mathsf T}$ 复线性、保单位、全锥正，保每个自伴平方、Jordan 运算和忠实归一迹，却有

$$
\tau(K(r_0,r_1))=-K(\tau(r_0),\tau(r_1)),\qquad
O=2k^{\mathsf T}\ne0.
\tag{45.8}
$$

由于 $\operatorname{Tr}k=0$，忠实归一迹仍给 $f(O)=0$。所以未平方的一个有向缺陷期望不足；(45.2) 必须检测 $O^2$，或另有足以识别算子的读出。即使对全部自伴输入而不只三个原始输入都校准平方，并保持一个忠实态，也仍需独立支付有向关系。原始探针带相位不排除转置，因为前件并没有指定它们的像为固定点。

目标非忠实性的具体障碍是

$$
\Phi_8(a)=\operatorname{diag}(a,a^{\mathsf T}),\qquad
\rho_8=\operatorname{diag}(I_4/4,0_4).
\tag{45.9}
$$

$\Phi_8:M_4\to M_8$ 正、复线性、保单位，保所有自伴平方而非同态。其有向缺陷为 $\operatorname{diag}(0,2k^{\mathsf T})$，故同一非忠实目标态满足全部 (45.2)，包括 $f(O^2)=0$，仍漏掉整个反同态扇区。只在第一块内运行的合法门词也不改变这件事。一般可达空间上的检测不能冒称全目标检测。

Johnston–Kribs，[*Generalized Multiplicative Domains and Quantum Error Correction*，arXiv:1004.5112v1，§3 式 (3)、Theorem 3](https://arxiv.org/pdf/1004.5112v1)，[DOI 10.1090/S0002-9939-2010-10556-7](https://doi.org/10.1090/S0002-9939-2010-10556-7)，要求映射完全正且保单位；仓内 [Library note](../../../Library/QuantumChannels/johnston2010generalized.md) 保留这些前件。它不能应用于定理 44.2 的仅正映射。转置在 $z=E_{12}$ 已给

$$
\tau(z^*z)-\tau(z)^*\tau(z)=E_{22}-E_{11}\not\ge0.
\tag{45.10}
$$

如果另外明确加入全部复 $z$ 的 Schwarz 前件 $\Phi(z^*z)\ge\Phi(z)^*\Phi(z)$，则三份平方等号确实已足够：令 $\Gamma(a,b)=\Phi(a^*b)-\Phi(a)^*\Phi(b)$，在 $r+\lambda b$ 上对全部复 $\lambda$ 取正二次型，$\Gamma(r,r)=0$ 迫使 $\Gamma(r,b)=0$；取伴随又得右乘交织。这样的元素构成结合 $*$-代数，(44.8)–(44.13) 已证明原始三元组生成全部 $M_4$，故可得同态。这是更强前件的成熟乘法域论证，未从普通正性推得，也未进入定理 44.2 的证明。

## 46. 保持同一忠实态的分级退相干不运输原始 PB 矩

**命题 46.1（同模型的精确保态粗粒化反例）。** 在定义 44.1 的固定模型内取 $q_1=q_2=1$，$g=K(c,t)$，母卷 (41.2) 的演员设置取 $x=0$。对每个分别固定的 $\iota=\sigma i$，置

$$
v_\iota=(e_1+\iota e_2)/\sqrt2,\qquad
\rho_\iota=I_4/8+v_\iota v_\iota^*/2,\qquad
\omega_\iota(a)=\operatorname{Tr}(\rho_\iota a),
\tag{46.1}
$$

以及同一个分级条件期望

$$
\mathcal E_J(a)=PaP+QaQ=(a+JaJ)/2.
\tag{46.2}
$$

$\mathcal E_J$ 完全正、保单位、保迹，保持忠实态 $\omega_\iota$；但不能把原始 $R_\delta,S_\delta,L$ 的 PB 矩运输成其像的乘积矩。准确地，

$$
\begin{array}{c|ccc|cc}
\delta&\omega_\iota(R_\delta^2)&\omega_\iota(S_\delta^2)&
\omega_\iota(R_\delta\circ S_\delta)&B_{\omega_\iota}(R_\delta,S_\delta)&
B_{\omega_\iota}(\mathcal E_JR_\delta,\mathcal E_JS_\delta)\\\hline
+1&5/8&15/8&-3/4&39/64&0\\
-1&5/8&11/8&3/4&19/64&0
\end{array}
\tag{46.3}
$$

同时 $\mathcal E_J(L)=L$，$\omega_\iota(L)=-1/4$。因此原始 PB 有正预算，而以像的平方和 Jordan 乘积重新计算的两笔预算全零，不能与运输的同一左端配成原 PB。这反驳“一个共同忠实态保持就保证原始矩运输”，不反驳合法测量、遗忘或单一共同 $\omega$。

证明。$\rho_\iota$ 的谱为 $5/8,1/8,1/8,1/8$，迹一且严格正；$v_\iota\in P\mathbb C^4$ 使 $[\rho_\iota,J]=0$。两个 Kraus 算子 $P,Q$ 直接给 (46.2) 的完全正、保单位和保迹性；迹循环给

$$
\omega_\iota(\mathcal E_J(a))=\omega_\iota(a)
\quad(a\in M_4).
\tag{46.4}
$$

写 $k_t=c\circ t=F_{14}(1/2)+F_{24}(1)$，则

$$
R_\delta=-\delta k_t,\qquad
S_\delta=t+\delta K(c,t),\qquad
L=-2t\circ K(c,t)=\frac{\iota}{2}[t^2,c].
\tag{46.5}
$$

$R_\delta,S_\delta$ 都是分级奇元，所以它们的 $\mathcal E_J$ 像为零；$L$ 是分级偶元，所以像为自身。此处

$$
L=F_{12}(\iota/2),\qquad
k_t^2=\begin{pmatrix}
1/4&1/2&0&0\\1/2&1&0&0\\0&0&0&0\\0&0&0&5/4
\end{pmatrix}.
\tag{46.6}
$$

由 $v_\iota^*Lv_\iota=-1/2$ 及 $\operatorname{Tr}L=0$ 得 $\omega_\iota(L)=-1/4$。其余收缩为

$$
\begin{gathered}
\omega_\iota(k_t^2)=5/8,\quad
\omega_\iota(t^2)=1,\quad
\omega_\iota(K(c,t)^2)=5/8,\\
\omega_\iota(t\circ K(c,t))=1/8,\quad
k_t\circ K(c,t)=0,\quad
\omega_\iota(k_t\circ t)=3/4.
\end{gathered}
\tag{46.7}
$$

代入 (46.5) 即得前三个矩；$5\cdot15/64-9/16=39/64$、$5\cdot11/64-9/16=19/64$ 给原预算。原 PB 由母卷定理 41.3 在零残量处已成立，无须重新证明。像预算为零且运输左端绝对值为 $1/4$，故不保持此运输。

保态式 (46.4) 仍给 $\omega_\iota(\mathcal E_J(R_\delta^2))=\omega_\iota(R_\delta^2)$；失效的是把它换成 $\omega_\iota((\mathcal E_JR_\delta)^2)$。同样的区别适用于其余乘积，不是原态的质量损失。特别，这个通道不满足定理 44.2 的原始平方标定：$r_0=-k_t$，

$$
\omega_\iota\bigl(\mathcal E_J(r_0^2)-(\mathcal E_Jr_0)^2\bigr)=5/8>0.
\tag{46.8}
$$

这说明有限标定锁定的是完整源可观测量代数的精确乘法运输，或声明为闭门的代数识别，而不要求每个读出或真遗忘通道都乘法化。

作为证明内的标准 dilation，取二维记录空间 $\mathcal R$、其基向量 $|0\rangle,|1\rangle$，以及交换两向量的 $X_{\mathcal R}$。令

$$
U=P\otimes I_{\mathcal R}+Q\otimes X_{\mathcal R},\qquad
V\psi=U(\psi\otimes|0\rangle).
\tag{46.9}
$$

$U^*U=I$，且

$$
V^*(a\otimes I)V=PaP+QaQ=\mathcal E_J(a).
\tag{46.10}
$$

完整代数中的 $a\mapsto U^*(a\otimes I)U$ 保乘法；压缩到 $|0\rangle$ 的读出一般不保乘法。Schrödinger 图像中追掉记录得到 $P\eta P+Q\eta Q$，保留记录则保留相应环境相关。若要把 (46.1) 写成一个纯共同全局向量态，可在另一个参考空间按其四个正谱值作标准纯化；这不改变任何系统读数。这个成熟 dilation 只解释本反例与全局酉信息保持的相容性，不构造原 native 全词源、原准备接受接口或 active Return。∎

这里的 repo-derived 内容是同一 M4 PB 原始列、忠实保态分级粗粒化和 (46.3)–(46.8) 的精确运输分离。条件期望、Kraus、酉 dilation、纯化与对称/有向结构的区别是成熟中间材料。Jordan 与结合方向的背景可参见 Alfsen–Shultz，[*Orientation in operator algebras*，PNAS 95 (1998), 6596–6601，DOI 10.1073/pnas.95.12.6596](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，不以该文代替本模型的原始探针证明。

## 47. 原来源识别、关系几何与未付的共同实现

**定义 47.1（条件运输与实际原源的不同前件）。** 定理 44.2–45.1 的对象是一个固定完整矩阵源上的同一个正保单位 $\Phi$。它的三平方条件固定全部自伴 Jordan 运算和实谱多项式几何，允许正交的同态与反同态扇区；一个非零原始有向对再选定同一 $\iota$ 的乘法方向。对自伴 $a,b$，$ab=a\circ b-\iota K(a,b)$，故两部分合起来恢复整个结合乘法。一个共同状态相容式如 $f\circ\Phi=\omega_{\rm source}$ 不代替这些乘法条件；定理 45.1 的门词检测也不要求门门保态。命题 46.1 是一种更强保态前件仍不足的反例，未把保态添为单一 $\omega$ 目标的一般必要条件。

原始关系归一化所需的实际连接仍是：在同一原 $\Omega$、同一旧标签、准备、评价、合法门词、完整输出及其每个旧合法未来中，构造并识别一个共同全 $M_4$ 响应 $\Phi$，证明它本身全锥正且保单位，再从同一来源导出三平方与一个有向关系；或严格导出其中某条条件不能由原关系提供。若采用共同词接口，还须支付同一 $\omega$ 的满可达性、全部所用合法词及源/目标复合缺陷的共同读出。这是原模型内的数学来源与操作可用性义务，不被替换为经验实验要求；本卷没有构造该 producer。

母卷 §41 的全输出允许集 $\mathscr P_q$ 是否仅为 $K(c,t)+\mathbb RJ$ 仍为 open。母卷定理 43.1 只将固定零探针边界 (41.16) 扩到全复环境幅度，不决定全部 $x$、全部正泛函；本卷三原始标定则约束运输映射，不分类 $\mathscr P_q$。增加读出能辨识分级参数，并不迫使该参数为零。母卷 §42 的 M5、$B_{33}=0$ 秩二输入结论按其完整原域直接复用，不移作 M4 任意残量的结论。

[C128 原词卷 §§419–427](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 已在其完整原域从同一旧总 $S,D$、三标签正性、相加零关系、效果二点与单位预算、三元相容和正实夹心恢复实双线性及结合 $\mu=S-iD$，并给忠实有界辅助表示。旧 $D$ 的槽位奇性在该域已得，不重立为新结果；同一辅助表示也不自动识别为任意预给的 native $K/J$ 或本卷的 $\Phi$。若另已证明实际 $J$-协变和该同一旧响应奇性的共同适用域，可以在同一轨道比较，不能宣称必须另找不同轨道。C128 §385.2 的完整正 Gram 源本已给二点 P2，不能用它循环宣称从本卷 PB 推出 P2。母卷 §41.3 的分级线恰显示固定输出 PB 单独不支付环境零谱 P2。

[静态 Atlas IV §66](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md#66-去掉交叉正性后的原态几何与有序方向分类) 在其完整有限比较/Jordan 桥、全态全效果、正接合与同一正读回、两条张成、单位切片及全部其余条件下，已经给有限复矩阵直和的原 Born 状态几何；C13 另选择相容的接合取向，并不消去原正权重。其 §66.11 的正保迹读回不推出 C13，§66.12 的静态互反也不使选择性操作交换。这里直接采用这些边界，既不重做分类，也不将 Atlas 的原正滤波器免费改成保单位映射；辅助正规化坐标不等于本卷所要求的实际同一 $\Phi$。

完整原合同严格合取母卷 §41.8、§39.8 及其逐层钉版上游、[C139 有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的全文。原 $\Omega$/native、原 $E,C,u,N,\mathcal P,S,D,q,K/J$、全词、跨评价配对、模式网络及具名接线保持各自身份；局部矩阵 $q,D$、$\rho_0$、$J$ 和 $\Phi$ 不重定义那些原对象。全部原准备、发生、参考/副本、真正相关联合、中央/经典/不等维/静默/无轴块、零/不等/次归一质量、原 parent/ready/flags、全部中间切口、完整菜单、固定支持全质量、环境、完整活动输出、所有成功失败细记录、port/post-port、拒绝、停止、销毁、泄漏、真分组遗忘、两侧与逆向 Return，以及每份完整输出的每个旧合法未来均保留。原精确 $B$ 与闭 $B_{\rm cl}$ 不合并，未定义请求不补零；物理钟、控制、单位、同一 $\sigma,t_0$、固定域/resolvent 和 $3s+r\le1$ 各守原义。

实际旧程序 $\tau;T_P$ 的指定接受族，仍须按 [C139 固定源卷 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 在全部原准备、参考、切口、合法分析词与树、原坐标及完整菜单上，给到同一实际菜单事件 $k_b^\dagger P_{J_0}k_b$ 和原接受端的准备无关接受接口，保持支持、未归一标尺、类型、ready、控制、钟、互补结果、记录和全部合法未来；不加强成整历史双射，也不由矩阵相等、数学菜单、逆门或局部校准代付。[Fourier 卷 §§10.3–10.4](AURIC_C139_FOURIER_OVERLAPS_AND_GLOBAL_FRAMED_BORN_RIGIDITY.md) 的原子归属和指定正校准准备仍守原条件。CountRead 仍需同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及同一整份活动输入保留原参考/控制/钟并对全部旧合法未来的真实 Return；查询表、地址、档案和有限矩阵 dilation 均不供应活动发生标识或未来权限。

母卷 §39.8 已取得且仍适用的条件消费者继续计入：共同全词、共同核及实际相干准备连接 Hilbert/相干；原实际事件、全菜单、固定支持全质量及正质量连接 Born；真正相关共同联合、忠实同向交换腿与共同生成连接张量；整台 typed 接续、递归参考、全环境/输出/记录/失败/后口、相关正输入、真支持和累计运输连接 CP/Kraus；完整仪器、typed 单位分区、AC、$N_u,X,X_s$、平方根词和接受端、正输出质量及各自射线校准连接 TP/更新/Lüders；全历史、真遗忘和全旧未来的实际两侧/逆向返回连接历史/Return；真实连续可逆流、实际逆、强连续实现、生成元域、物理钟/单位/能量及同一正 $\hbar$ 连接 Hamiltonian。定理 44.2 没有删除这些前件，也没有给一般 native 箭头 CP、任意参考份数相容、动力学或物理三维的来源。完整量子起源及原全部成功条件仍未完成。

**开放问题 47.2（有限标定如何由同一原源支付）。** 在不替换旧 $D(c,t)$、原准备接受接口、实际合法控制、完整环境/记录和全部旧合法未来的条件下，原二元关系及其三元相容能否供应定义 47.1 的同一个全锥正保单位响应，并在同一可达读出中强制 (44.3)？须给实际来源识别、复合读出和共同实现的证明，或给保持这些完整合同的严格反例。只保一个态、只保 Jordan 几何、分别给不同 $\Phi$，或用已含 P2 的 Gram 源循环论证，都不结算该问题。三原始探针定理缩小的是这个条件运输接口，不是已经造出完整量子原源。

## 追加锚（本行以下为增补区）
