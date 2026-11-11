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

于是 $A=0$，接回定理 44.2。也可以只检查 (45.6) 的正加权和为零；每项非负时这与所有项为零等价。这是既有可达忠实和的模型应用，不另立一般可观测性定理。

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

[C128 原词卷 §§419–427](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 已在其完整原域从同一旧总 $S,D$、三标签正性、相加零关系、效果二点与单位预算、三元相容和正实夹心恢复实双线性及结合 $\mu=S-iD$，并给忠实有界辅助表示。旧 $D$ 的槽位奇性在该域已得，不重立为新结果；同一辅助表示也不自动识别为任意预给的 native $K/J$ 或本卷的 $\Phi$。若另已证明实际 $J$-协变和该同一旧响应奇性的共同适用域，可以在同一轨道比较，不能宣称必须另找不同轨道。C128 §385 式 (385.2) 的完整正 Gram 源本已给二点 P2，不能用它循环宣称从本卷 PB 推出 P2。母卷 §41.3 的分级线恰显示固定输出 PB 单独不支付环境零谱 P2。

[静态 Atlas IV §66](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md#66-去掉交叉正性后的原态几何与有序方向分类) 在其完整有限比较/Jordan 桥、全态全效果、正接合与同一正读回、两条张成、单位切片及全部其余条件下，已经给有限复矩阵直和的原 Born 状态几何；C13 另选择相容的接合取向，并不消去原正权重。其 §66.11 的正保迹读回不推出 C13，§66.12 的静态互反也不使选择性操作交换。这里直接采用这些边界，既不重做分类，也不将 Atlas 的原正滤波器免费改成保单位映射；辅助正规化坐标不等于本卷所要求的实际同一 $\Phi$。

Atlas IV 定理 67.7 还在其同一 $\mathcal B$ 实际资料上证明 $(W_H\ \&\ N)\Longleftrightarrow(D_H\ \&\ C_{\rm joint})$，其中 $C_{\rm joint}$ 是联合双迹上界，等号刚性固定共同尺度而不换原映射。定义 67.10、定理 67.11 在全部保留前件及预选 Bell 探针的整个输出正性下接回规范张量、原 Born 几何及唯一正保迹读回；推论 67.12 则明确保留未校准的正尺度。该联合校准不删除 Bell 条件，也不提供本卷三个原始复合输入的可用性或原 native 身份；不能把辅助尺度消去当作实际 $\Phi$ 已保单位。

完整原合同严格合取母卷 §41.8、§39.8 及其逐层钉版上游、[C139 有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的全文。原 $\Omega$/native、原 $E,C,u,N,\mathcal P,S,D,q,K/J$、全词、跨评价配对、模式网络及具名接线保持各自身份；局部矩阵 $q,D$、$\rho_0$、$J$ 和 $\Phi$ 不重定义那些原对象。全部原准备、发生、参考/副本、真正相关联合、中央/经典/不等维/静默/无轴块、零/不等/次归一质量、原 parent/ready/flags、全部中间切口、完整菜单、固定支持全质量、环境、完整活动输出、所有成功失败细记录、port/post-port、拒绝、停止、销毁、泄漏、真分组遗忘、两侧与逆向 Return，以及每份完整输出的每个旧合法未来均保留。原精确 $B$ 与闭 $B_{\rm cl}$ 不合并，未定义请求不补零；物理钟、控制、单位、同一 $\sigma,t_0$、固定域/resolvent 和 $3s+r\le1$ 各守原义。

实际旧程序 $\tau;T_P$ 的指定接受族，仍须按 [C139 固定源卷 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 在全部原准备、参考、切口、合法分析词与树、原坐标及完整菜单上，给到同一实际菜单事件 $k_b^\dagger P_{J_0}k_b$ 和原接受端的准备无关接受接口，保持支持、未归一标尺、类型、ready、控制、钟、互补结果、记录和全部合法未来；不加强成整历史双射，也不由矩阵相等、数学菜单、逆门或局部校准代付。[Fourier 卷 §§10.3–10.4](AURIC_C139_FOURIER_OVERLAPS_AND_GLOBAL_FRAMED_BORN_RIGIDITY.md) 的原子归属和指定正校准准备仍守原条件。CountRead 仍需同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及同一整份活动输入保留原参考/控制/钟并对全部旧合法未来的真实 Return；查询表、地址、档案和有限矩阵 dilation 均不供应活动发生标识或未来权限。

母卷 §39.8 已取得且仍适用的条件消费者继续计入：共同全词、共同核及实际相干准备连接 Hilbert/相干；原实际事件、全菜单、固定支持全质量及正质量连接 Born；真正相关共同联合、忠实同向交换腿与共同生成连接张量；整台 typed 接续、递归参考、全环境/输出/记录/失败/后口、相关正输入、真支持和累计运输连接 CP/Kraus；完整仪器、typed 单位分区、AC、$N_u,X,X_s$、平方根词和接受端、正输出质量及各自射线校准连接 TP/更新/Lüders；全历史、真遗忘和全旧未来的实际两侧/逆向返回连接历史/Return；真实连续可逆流、实际逆、强连续实现、生成元域、物理钟/单位/能量及同一正 $\hbar$ 连接 Hamiltonian。定理 44.2 没有删除这些前件，也没有给一般 native 箭头 CP、任意参考份数相容、动力学或物理三维的来源。完整量子起源及原全部成功条件仍未完成。

**开放问题 47.2（有限标定如何由同一原源支付）。** 在不替换旧 $D(c,t)$、原准备接受接口、实际合法控制、完整环境/记录和全部旧合法未来的条件下，原二元关系及其三元相容能否供应定义 47.1 的同一个全锥正保单位响应，并在同一可达读出中强制 (44.3)？须给实际来源识别、复合读出和共同实现的证明，或给保持这些完整合同的严格反例。只保一个态、只保 Jordan 几何、分别给不同 $\Phi$，或用已含 P2 的 Gram 源循环论证，都不结算该问题。三原始探针定理缩小的是这个条件运输接口，不是已经造出完整量子原源。

## 追加锚（本行以下为增补区）

## 48. 同一响应律的有限帧 PB 刚性

**定义 48.1（共同响应与指定帧族）。** 取母卷定义 41.1 的完整四维代数 $A=M_4(\mathbb C)$、实空间 $H_4=\operatorname{Herm}(A)$、$c_0=\operatorname{diag}(1,2,3,0)$、$P_0=\operatorname{diag}(1,1,1,0)$，并分别固定 $\sigma\in\{1,-1\}$、$\iota=\sigma i$、$K_\sigma(a,b)=\iota[a,b]/2$。本节只有一个实双线性交替映射

$$
D:H_4\times H_4\longrightarrow H_4,\qquad D(I_4,a)=0\quad(a\in H_4).
\tag{48.1}
$$

下列整数递推仅定义有限的精确矩阵族，不是随机性假设。令

$$
\begin{gathered}
s_0=1,\qquad s_{n+1}=(1664525s_n+1013904223)\bmod 2^{32},\qquad
z_n=(s_n\bmod5)-2\quad(n\ge1),\\
v_j=(z_{8j+1},\ldots,z_{8j+4})^{\mathsf T}
       +i(z_{8j+5},\ldots,z_{8j+8})^{\mathsf T},\\
d_j=v_j^*v_j,\qquad H_j=I_4-2v_jv_j^*/d_j,\\
U_f=H_{4f}H_{4f+1}H_{4f+2}H_{4f+3},\qquad 0\le f<48.
\end{gathered}
\tag{48.2}
$$

这 192 个 $d_j$ 均在 $[5,26]$，故 $H_j^*=H_j$、$H_j^2=I_4$，全部 $U_f\in M_4(\mathbb Q(i))$ 酉。递推种子跨帧连续，不在每帧重新开始。对每个这样的 $U=U_f$ 和每个 $q=(q_1,q_2,0)^{\mathsf T}$、$q_1q_2\ne0$，记

$$
c=Uc_0U^*,\quad P=UP_0U^*,\quad
 t=U\begin{pmatrix}0_{3\times3}&q\\q^*&0\end{pmatrix}U^*,\quad
 g=D(c,t).
\tag{48.3}
$$

对全部 $x=x^*=PxP$，仍取 $h=K_\sigma(c,x)$、$r=c\circ x$、$k_t=c\circ t$，并逐字使用母卷 (41.2) 的 $R_\delta,S_\delta,L,B_\phi$；没有把 $h$ 改成 $D(c,x)$。共同 PB 条件为

$$
|\phi(L)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}
\quad\text{对全部 }f,q,x,\ \phi\in A_+^*.
\tag{48.4}
$$

$A_+^*$ 指完整 $M_4$ 上的正复线性泛函。每份不等式始终使用同一 $x,\phi,g$；两预算均为原未中心化实 Gram，不删环境行，也不换成复 Gram。零质量、非忠实态及零预算保留。

**定理 48.2（共同响应的充要刚性及共同源适用条件）。** 在定义 48.1 下，(48.4) 当且仅当

$$
D(a,b)=K_\sigma(a,b)\qquad(a,b\in H_4).
\tag{48.5}
$$

这里不另假设 P2、实结合子、导子、切向性、$D$ 的酉协变或演员标定。48 个指定矩阵已足够，不要求在前件中量化所有酉矩阵；每帧的全部复 $q$、全部演员 $x$ 与全部正泛函量词仍不可删除。该数目不表示最少帧数、48 次测量或稳定性结论。结论不分类一个固定 $q$ 上独立选取的任意 $g$。

共同源版本是以下有条件的应用，而非 (48.1)–(48.4) 的来源推导。在完整被测代数 $A$ 的同一忠实表示 $j$ 下，设一份原 $\omega$ 的实际合法词及保留分支供应正泛函族 $\mathcal T_\Omega$，同一 $D$ 和同一套完整标签的原 PB 对该族成立。若

$$
A_+^*\subseteq\overline{\operatorname{cone}(\mathcal T_\Omega)},
\tag{48.6}
$$

则 (48.5) 成立。也可将 (48.6) 替换为对每份固定 $(f,q,x,D)$ 的七矩条件

$$
\begin{gathered}
 m(\phi)=\bigl(\phi(L),\phi(R_+^2),\phi(S_+^2),\phi(R_+\circ S_+),
                    \phi(R_-^2),\phi(S_-^2),\phi(R_-\circ S_-)\bigr),\\
 m(A_+^*)\subseteq\overline{\operatorname{cone}(m(\mathcal T_\Omega))}.
\end{gathered}
\tag{48.7}
$$

闭包取有限维实拓扑。覆盖是充分条件，不断言为该受限 PB 家族的必要条件，也不声称七坐标最少。词、准备、读出、原 native $D$ 身份及全部原合同须由同一来源另行供应；单一 $\omega$ 或满可达支撑本身均不蕴含这些覆盖。证明的算子律部分见 §§49–50，共同源应用与非蕴含见 §51。

## 49. 对角约束、商空间几何与精确有限子式

**定义 49.1（有序的实系数矩阵）。** 令 $V=H_4/\mathbb RI_4$，用无迹代表元识别它，取以下有序实基：

$$
\begin{gathered}
\mathcal B=(E_{11}-E_{44},E_{22}-E_{44},E_{33}-E_{44},
 X_{12},Y_{12},X_{13},Y_{13},X_{14},Y_{14},X_{23},Y_{23},X_{24},Y_{24},X_{34},Y_{34}),\\
 X_{ij}=E_{ij}+E_{ji},\qquad Y_{ij}=i(E_{ij}-E_{ji}).
\end{gathered}
\tag{49.1}
$$

索引从零开始。自伴 $a$ 的坐标 $\chi(a)$ 依次为 $a_{11}-\operatorname{Tr}(a)/4,a_{22}-\operatorname{Tr}(a)/4,a_{33}-\operatorname{Tr}(a)/4$，然后按 $12,13,14,23,24,34$ 顺序取 $\operatorname{Re}a_{ij},\operatorname{Im}a_{ij}$。因此 $\chi(I_4)=0$、$\chi(\mathcal B_k)$ 是第 $k$ 个单位向量。令 $\ell_0,\ldots,\ell_{11}$ 为这个坐标的后十二项，且

$$
(T_0,T_1,T_2,T_3)=(X_{14},Y_{14},X_{24},Y_{24}).
$$

对每个 $f,\nu$，置 $a=\chi(U_fc_0U_f^*)$、$b=\chi(U_fT_\nu U_f^*)$、$w_{ij}=a_ib_j-a_jb_i$。定义 $2304\times1575$ 的有理矩阵

$$
M_{(f,\nu,l),(i,j,k)}
 =w_{ij}\,\ell_l(U_f^*\mathcal B_kU_f),\qquad
\begin{matrix}0\le f<48,\ 0\le\nu<4,\ 0\le l<12,\\0\le i<j<15,\ 0\le k<15.\end{matrix}
\tag{49.2}
$$

行按 $(f,\nu,l)$ 字典序，列先按 $i<j$ 的字典序，再按 $k$，$k$ 变化最快。楔积没有额外 $1/2$。另记 $W_{(f,\nu),(i,j)}=w_{ij}$，其形状为 $192\times105$。全部伴随和实虚坐标均先在 $\mathbb Q(i)$ 中计算，再把有理实坐标约化；不在有限域中另行定义复共轭。

**定理 49.2（指定帧的共同线性核）。** 实双线性交替且满足 $F(I_4,a)=0$ 的 $F:H_4\times H_4\to H_4$，若对全部 $f,\nu$ 有

$$
U_f^*F(U_fc_0U_f^*,U_fT_\nu U_f^*)U_f\text{ 为对角矩阵},
\tag{49.3}
$$

则且仅则存在 $f_0\in(\Lambda^2V)^*$ 使

$$
F(a,b)=f_0([a],[b])I_4.
\tag{49.4}
$$

故共同线性核为 105 维中心值空间；其无迹输出商的核为零。单帧的被求值残量仍只是对角矩阵，通常不在中心。

证明。由单位零与交替性，$F$ 经 $\Lambda^2V$ 分解。去掉输出的中心部分，令 $F_0=F-\operatorname{Tr}(F)I_4/4$。其 1575 个实系数 $A_{ij,k}$ 由

$$
F_0(a,b)=\sum_{i<j,k}
 (\chi_i(a)\chi_j(b)-\chi_j(a)\chi_i(b))A_{ij,k}\mathcal B_k
\tag{49.5}
$$

唯一给出。式 (49.3) 恰给 $M\operatorname{vec}(A)=0$。以下精确子式给 $M$ 的列独立性，因而 $F_0=0$；反向中心值显然在每帧对角。

具体有限数据定义在素数 $p=1009$ 下。依 (48.2)、(49.1)–(49.2) 约化 $M$ 得 $\overline M$，其全部列数为 1575。取 $\operatorname{RREF}(\overline M^{\mathsf T})$ 各非零行的最左主元列，按递增顺序组成 $J$，作为 $\overline M$ 的零起算行号；保留全部列及其原顺序。具体算术结果为

$$
|J|=1575,\qquad
\det\overline M_{J,:}=796\pmod{1009},\qquad
\operatorname{rank}_{1009}\overline W=105.
\tag{49.6}
$$

式 (49.6) 的有序整数数组采用逐行、无符号 16 位小端编码，其 SHA256 标识为：

| 数学数组 | SHA256 |
| --- | --- |
| $\overline M$ | `d1b015669a9df51431a8fa8d7e88a977754f0e624760317f28d8b5a900b0afde` |
| $J$ | `964c5d9faa2479b19edafc7f60b3a9469e5c14da32e7e33b146a6742fbb8f591` |
| $(d_0,\ldots,d_{191})$ | `904c8029c79ccf3dfe0b18ee019645e4b02509ba1907c6b6cab3c70ee10c9cc2` |
| $\overline W$ | `a796686bc0bf9f5ab18a1651cf8491044e5f51197f66bb69b95e148e07994f92` |

数据的不可变数学引文为私有 [trureturing-experiments，commit `651b00b5abcfc10de377ae180bcfde38752bdffd`，`experiments/auric-shared-d-frame-central-pb-precheck/data/`](https://github.com/the-omega-institute/trureturing-experiments/tree/651b00b5abcfc10de377ae180bcfde38752bdffd/experiments/auric-shared-d-frame-central-pb-precheck/data)。该处 `certificate.json` 同时标识定义这些数据的三个来源：`frame_kernel.py` 的 SHA256 为 `8f6224dc5c64959c57d375f82f10f6f6605eec11232b86c0614ae9261b6d0331`，`central_pb.py` 为 `70b4b19feb6d09b1cf8e0186da31ae3848fe90027f42a9399200253a7156c311`，独立有理重构 `independent_precheck.py` 为 `6c9f0fab048b4fbb1e1eea026e802746881891f8138ac9b58129ba80f9d3d6ef`。哈希只标识数据，并不证明秩；承担有限步骤的是 (48.2)、(49.2) 的构造和 (49.6) 指定子式的精确行列式。独立重构与直接模算术共享 FLINT/SymPy 后端，不构成两个不同证明内核；这里未作 Lean kernel 认证。

有理到实的提升如下。每个系数在局部化环 $\mathbb Z[1/(2\prod_jd_j)]$ 中，迹坐标的 $1/4$ 已包含在内。192 个正整数 $d_j$ 的范围为 $5\le d_j\le26$，均不被 1009 整除；1009 的素性只需试除至 31。因此约化是该环到 $\mathbb F_{1009}$ 的环同态。若直接约化 Gaussian 矩阵，可取 $i\mapsto469$，因为 $469^2\equiv-1$；须先计算 $U_f^*$，不能把有限域上的恒等映射当作共轭。式 (49.2) 的最终系数全在有理实部中，不依赖这种直接 Gaussian 求值。非零剩余值 796 迫使对应有理子式非零，继而在 $\mathbb R$ 上非零，故亦排除任意无理实系数 $A$。

空间维数为 $\dim V=15$、$\dim\Lambda^2V=105$、$\dim\operatorname{Hom}_{\mathbb R}(\Lambda^2V,H_4)=1680$。每个中心二形式在 (49.3) 中确实消失，所以不能把 1575 秩解释成完整 1680 维映射空间的零核。输入楔积张成 $\Lambda^2V$ 也直接由列单射性推出：若其张成空间真小于 $\Lambda^2V$，取非零湮灭泛函 $\eta$ 及非零 $B\in V$，则 $\eta\otimes B$ 给非零商映射却被 $M$ 湮灭，矛盾。因而 (49.6) 的 $W$ 秩是同一张成事实的直接算术表达，不是另加的独立逻辑前提。∎

定理 49.2 的几何是共同二形式的取值兼容性：每帧只要求某四个输入楔积的输出落在该帧的对角子空间；所有这些取值必须来自同一个线性映射，才共同消去无迹部分。并非先把各帧残量假定为中心，也并非给 $D$ 加酉协变。

## 50. 原 PB 排除全部中心二形式及充要证明

**引理 50.1（每个非零中心值的完整有限见证）。** 取 $j=1,2$、$a=(c_0)_{jj}\in\{1,2\}$、$\zeta\in\{1,i\}$，令

$$
T=\zeta E_{j4}+\overline\zeta E_{4j},\qquad
g=K_\sigma(c_0,T)+sI_4,\quad s\in\mathbb R\setminus\{0\}.
\tag{50.1}
$$

则存在有限演员 $x=P_0xP_0$ 及完整 $M_4$ 向量泛函 $\phi$，严格违反母卷原 PB，且两预算严格为正。可指定任意有限正质量 $\phi(I_4)=\mu>0$。

证明。若 $|s|>a^2/4$，取 $x=0$、$\xi=(\zeta e_j+e_4)/\sqrt2$、$\phi(A)=\xi^*A\xi$。直接代入母卷 (41.2) 给

$$
\phi(L)=-2s,\qquad B_+=B_-=a^4/16>0,
\tag{50.2}
$$

故 $|\phi(L)|>\sqrt{B_+}+\sqrt{B_-}$。若 $0<|s|\le a^2/4$，取

$$
\lambda=\frac{a(a^2-4s^2)}{4s(a^2+2)},\qquad
x=\lambda E_{jj},\qquad
\xi=\zeta s(1-2\iota/a)e_j+e_4.
\tag{50.3}
$$

为给出恒等式的完整接口，在有序子空间 $(e_j,e_4)$ 内，设 $b=a/2$、$k=K_\sigma(c_0,T)$，则

$$
T=\begin{pmatrix}0&\zeta\\\overline\zeta&0\end{pmatrix},\quad
k=\begin{pmatrix}0&\iota b\zeta\\-\iota b\overline\zeta&0\end{pmatrix},\quad
R_\delta=\begin{pmatrix}\lambda&-\delta b\zeta\\-\delta b\overline\zeta&0\end{pmatrix},\quad
S_\delta=\begin{pmatrix}\delta(a\lambda+s)&(1+\delta\iota b)\zeta\\(1-\delta\iota b)\overline\zeta&\delta s\end{pmatrix}.
\tag{50.4}
$$

另外两行仍留在完整矩阵中；此特定向量在那两行的像为零。$h=K_\sigma(c_0,x)=0$、$r=a\lambda E_{jj}$、$k_t=bT$，且 $T\circ k=0$，故完整算子 $L=-(a\lambda/2+2s)T$。对每个 $\delta$，原预算准确是

$$
B_\delta=\|R_\delta\xi\|^2\|S_\delta\xi\|^2
               -(\operatorname{Re}\langle R_\delta\xi,S_\delta\xi\rangle)^2.
\tag{50.5}
$$

把 (50.3) 代入 (50.4)–(50.5)，得到下表；也可把两列实化为八维实列，用全部二阶小子式平方和展开同一实 Gram 行列式。

| $a$ | $B_+=B_-$ | $\phi(L)$ | $\phi(L)^2-4B_+$ |
| --- | --- | --- | --- |
| $1$ | $(80s^6+12s^4+6s^2+1)/576$ | $-(44s^2+1)/12$ | $s^2(41+962s^2-40s^4)/72$ |
| $2$ | $(2s^6+6s^4+9s^2+1)/9$ | $-2(5s^2+1)/3$ | $4s^2(1+19s^2-2s^4)/9$ |

两预算的常数项严格正，其余系数非负。令 $y=s^2$；$a=1$ 时 $0<y\le1/16$，有 $41+962y-40y^2\ge41+(1919/2)y>0$；$a=2$ 时 $0<y\le1$，有 $1+19y-2y^2\ge1+17y>0$。差分别是 $40y(1/16-y)$、$2y(1-y)$，包括分段端点。因此两种范围覆盖全部非零实 $s$，并对两个分别固定的 $\sigma$ 和两种 $\zeta$ 均严格违反原 PB。

小值见证的质量为 $N=\xi^*\xi=1+s^2(1+4/a^2)>0$，大值见证为 $N=1$。用 $(\mu/N)\xi^*(-)\xi$ 代替 $\phi$，$L$ 读数乘 $\mu/N$、预算乘其平方，严格性不变。每个固定非零 $s$ 的探针有限；不主张 $s\to0$ 时统一有界。质量零的正泛函只有零，不承担排除。∎

证明定理 48.2 的算子律部分。令 $F=D-K_\sigma$，它保持实双线性、交替及单位零。对每帧先将已知 $c,t,x$ 和完整正泛函运输到 $U$ 坐标，直接应用母卷引理 41.2，得到

$$
U^*F(Uc_0U^*,Ut_0(q)U^*)U\text{ 对角}\quad(q_1q_2\ne0).
\tag{50.6}
$$

这里未知输出只是 $D$ 在实际输入上的值；没有使用 $D(UaU^*,UbU^*)=UD(a,b)U^*$。非对角读数是 $\operatorname{Re}q_1,\operatorname{Im}q_1,\operatorname{Re}q_2,\operatorname{Im}q_2$ 的连续实线性函数，故从稠密开集延到全部四个 elementary $T_\nu$。定理 49.2 给 $F=f_0I_4$。

仍须排除中心部分。固定某帧和一个 elementary $T$，若 $s=f_0([Uc_0U^*],[UTU^*])\ne0$，用引理 50.1 的同一有限 $x,\xi$，运输为 $UxU^*$、$U\xi$。取另一腿的实 elementary $T'$，定义

$$
t_\varepsilon=U(T+\varepsilon T')U^*,\qquad
s_\varepsilon=s+\varepsilon f_0([Uc_0U^*],[UT'U^*]).
\tag{50.7}
$$

每个非零实 $\varepsilon$ 均有原合法 $q_1q_2\ne0$，而同一 $D$ 给 $g_\varepsilon=K_\sigma(c,t_\varepsilon)+s_\varepsilon I_4$。不把中心值人为固定为 $s$。对这个固定 $x,\phi$，$L_\varepsilon$ 与两实 Gram 预算连续；预算始终因正泛函而非负，平方根也连续。在 $\varepsilon=0$ 的严格违反及双正预算因而延到充分小的非零 $\varepsilon$，与 (48.4) 矛盾。故 $f_0$ 在全部 192 个输入楔积上为零。定理 49.2 已蕴含它们张成 $\Lambda^2V$，所以 $f_0=0$，也覆盖含标量部分的任意 $a,b$。

反向若 $D=K_\sigma$，母卷定理 41.3 的 $E=0$ 恒等式直接给

$$
K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-)=L.
$$

对同一个完整正泛函用母卷 (41.14) 的复 Schwarz 和三角不等式即得原 PB。它包含混合、非忠实、任意非负质量与零预算，无须从已选见证外推。∎

## 51. 同一 omega 的适用对应、测试边界与保留合同

证明定理 48.2 的共同源部分。对每份固定完整元组，令

$$
G_\delta(\phi)=\begin{pmatrix}
\phi(R_\delta^2)&\phi(R_\delta\circ S_\delta)\\
\phi(R_\delta\circ S_\delta)&\phi(S_\delta^2)
\end{pmatrix}\ge0,\qquad b_\delta(\phi)=\sqrt{\det G_\delta(\phi)}.
\tag{51.1}
$$

正性来自 $\phi((uR_\delta+vS_\delta)^2)\ge0$，$u,v\in\mathbb R$。作为本应用的成熟中间工具，二维 PSD Minkowski 行列式不等式给 $\sqrt{\det(A+B)}\ge\sqrt{\det A}+\sqrt{\det B}$；见 Devi–Aujla–Kian–Moslehian，[arXiv:2302.08127v2，§3 式 (3.1)](https://arxiv.org/pdf/2302.08127v2)，该式引 Bhatia 的 *Matrix Analysis*，Corollary II.3.21。此处可直接对正定 $A$ 白化，化为 $\lambda_1+\lambda_2\ge2\sqrt{\lambda_1\lambda_2}$，再由 $A+\eta I,B+\eta I$ 取极限包含奇异情形。因此 $b_\delta$ 在正泛函锥上连续、正齐次、超可加。

于是 $b_+(\phi)+b_-(\phi)-|\phi(L)|$ 的非负集是闭凸锥，且只依赖 (48.7) 的七个实读数。PB 在 $\mathcal T_\Omega$ 上成立，就在其闭锥包上成立；在七矩像中同理，因为 PSD 的两份二阶矩阵也在极限下保持正性。由 (48.6) 或 (48.7) 得到全部 $A_+^*$ 的同元组 PB，再用已证算子律部分。谱分解特别说明：全部归一纯向量测试足够，因为 $\rho=\sum_j\lambda_jv_jv_j^*$ 时

$$
|\phi_\rho(L)|\le\sum_j\lambda_j|\phi_{v_j}(L)|
 \le\sum_{\delta,j}\lambda_j b_\delta(\phi_{v_j})
 \le\sum_\delta b_\delta(\phi_\rho).
\tag{51.2}
$$

未分别优化两预算，也未除以预算或零质量。这里复用 Gram 提升与谱分解，不另立一般锥检测重构定理。

一份原共同源的非选择性词读数准确为

$$
p(w,e)=\omega(U_w^*eU_w),\qquad
\phi_w(A)=\omega(U_w^*j(A)U_w).
\tag{51.3}
$$

这不要求 $\omega$ 被每个门保持。若被测完整 $M_4$ 上的根态为纯态，且实际合法有限词的纯态轨道在 $\mathbb{CP}^3$ 中稠密，则连续性、(51.2) 供应 (48.6)。选择性路线须使用同一整体词 $V_w$、实际保留记录投影 $\Pi_e$ 形成

$$
\phi_{w,e}(A)=\omega(V_w^*\Pi_e j(A)\Pi_e V_w).
\tag{51.4}
$$

这总是正泛函；若记录与 $j(A)$ 交换，才是通常联合读出的形式。所有成功、失败、零质量及细记录均保留，只在正质量且原来源允许时条件化。足够的来源定理是这些实际分支的归一密度在整个被测代数的纯射线上稠密，或直接证明 (48.7)。全部七个标签、平方、乘积和混合矩须由同一分支泛函忠实读取，不能从不同准备拼成一份 PB。数学上的线性组合与闭包不额外赋予原来源随机化或选择操作。

覆盖与 §45 的满支撑检测不同。下面的精确 raw 控制同时说明其非蕴含。固定

$$
\begin{gathered}
H=\operatorname{diag}(-1/2,1/2,3/2,-3/2),\quad Q=E_{14}+E_{41},\\
f(a,b)=\operatorname{Tr}(Ha)\operatorname{Tr}(Qb)-\operatorname{Tr}(Qa)\operatorname{Tr}(Hb),\qquad
D_\sigma(a,b)=K_\sigma(a,b)+f(a,b)I_4.
\end{gathered}
\tag{51.5}
$$

这是一个固定全域实双线性交替、单位零且非 $K_\sigma$ 的响应。取 $\phi_0=\operatorname{Tr}/4$；对全部同时运输的 $c,t,x$，迹循环性给 $\operatorname{Tr}(xK_\sigma(c,x))=\operatorname{Tr}(tK_\sigma(c,t))=0$，且 $\operatorname{Tr}(x(c\circ t))=\operatorname{Tr}(t(c\circ x))$。又 $\operatorname{Tr}t=0$，所以 $\phi_0(L)=0$；两预算非负，全部这些 trace PB 均成立。其根密度 $I_4/4$ 已满支撑，任意酉词仍只给同一迹泛函，但并未得到全称 PB。

确实取 $U=I$、$q=(1,1,0)$、$x=0$、$\xi=e_1+e_4$，则 $f(c_0,t)=10$，完整读数为

$$
\phi_\xi(L)=-40,\quad
(\phi_\xi(R_+^2),\phi_\xi(S_+^2),\phi_\xi(R_+\circ S_+))=(3/2,489/2,-12),\\
(\phi_\xi(R_-^2),\phi_\xi(S_-^2),\phi_\xi(R_-\circ S_-))=(3/2,329/2,-8).
\tag{51.6}
$$

两预算为 $891/4,731/4>0$，而 $(\sqrt{891/4}+\sqrt{731/4})^2\le811<1600$，严格违反 PB。两个分别固定的 $\sigma$ 均适用。这个 raw tests-only 控制不是完整 native $\Omega$ 反模型；已经有 $\phi_{e_4}(D_\sigma(c_0,t))=10$ 而 $B_{\phi_{e_4}}(c_0,t)=0$，故不满足相应全正泛函 P2。

全局纯也不自动补足局部读数。取 $\Omega=\sum_{j=1}^4e_j\otimes e_j/2$，局部代数为 $A\otimes I_4$，局部词为 $U\otimes I_4$。对所有这些词，读数始终为 $\operatorname{Tr}(A)/4$。具体 Weyl 词 $X^aZ^b\otimes I_4$，$0\le a,b<4$、$Xe_j=e_{j+1\bmod4}$、$Ze_j=i^je_j$（此处下标取 $0,1,2,3$），使 16 个轨道向量正交张成全局 $\mathbb C^{16}$，因为内积等于 $\operatorname{Tr}((X^aZ^b)^*X^cZ^d)/4$。因此一个纯循环全局向量与满轨道支撑仍可只看到局部迹；将 (51.5) 限定为 $D_{\rm loc}(a\otimes I,b\otimes I)=D_\sigma(a,b)\otimes I$，同一局部反控制继续成立。该构造未定义任意全局输入上的 $D$ 或完整全局效果、记录、准备和未来合同，不扩称原模型。

若参考侧全部秩一选择实际可用且保留结果，则同一 Bell 向量又给

$$
\langle\Omega,(A\otimes|\overline\psi\rangle\langle\overline\psi|)\Omega\rangle
       =\langle\psi,A\psi\rangle/4.
\tag{51.7}
$$

这可有条件供应全部局部纯泛函，却不供应那些操作本身，也不覆盖扩大的完整 $M_{16}$ 测试锥。密度矩阵纯射线、Weyl 正交与 Bell 恒等式作为成熟工具参见 Watrous，[*The Theory of Quantum Information*，§1.2、§4.1.2、Example 6.51](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。有限正测试族不能通过正锥组合生成全部 PSD 锥：秩一正矩阵的任何正分解，各项都必须支撑在同一条射线上；有限族只有有限条这样的射线。它的迹一截面是闭多面体，闭包也不能补齐。这不排除受限响应类的有限 PB 专用证书或附加界下的近似检测，亦不把 (48.6) 升为必要条件；例如已知 $D=K_\sigma$ 无论只读取哪一条迹射线都满足全部 PB。有限信息完备的有符号线性重构与正锥覆盖不同，参见 D’Ariano–Perinotti–Sacchi，[arXiv:quant-ph/0310013v2，§2 式 (3)–(8)](https://arxiv.org/pdf/quant-ph/0310013v2)。∎

**定义 51.1（关系几何的来源边界）。** 上述 repo-derived 承重内容是同一 $D$ 的 48 帧共同核、全中心残量排除与 (48.5) 的双向合成；Householder、外幂、模素数非零子式提升、Gram/Schwarz、Minkowski、谱分解及 Bell 几何均为推导内成熟工具。母卷引理 41.2、定理 41.3、§43 及本卷 §§44–47 按其原条件复用；未把逐输入分级族当成一个已存在的全局响应。相关 bilinear-map 文献 Alaminos–Brešar–Extremera–Villena，[*On bilinear maps determined by rank one idempotents*，Theorem 2.2](https://users.fmf.uni-lj.si/bresar/documents/bilmapsid.pdf)，要求全矩阵域上对每对正交秩一幂等元为零，结论为 $\Phi_1(ab)+\Phi_2(ba)$；这些前提不是 (48.4) 的已知后果，不据此套用分类。这里不主张文献优先权或穷尽检索。

[Atlas IV 定义 71.1、定理 71.6、命题 71.8a](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md#71-联合纯局部混的内在边缘关系与统一负值检测) 已在完整 PRE 中给出内在“每个活跃有序块联合纯、边缘混、质量严格正”的非空关系 $\mathfrak E(F)$，并逐成员证明 $\mathrm{C13}\Longleftrightarrow I^{\rm raw}\rho\in E_+$。这里 PRE 保留非零有限实载体的闭尖生成锥、完整态基及全部效应、完整有限比较混合律 $S$ 到 EJA 的条件桥、全锥正 $L,p$、同一个 $p$ 两次与原均匀参考定义的 $M$、两条实张成、$D_J$、覆盖整个 $D_+$ 的 $D_H$ 及全部实方向的 $Z$；仅删除 C13。该结论补回组合相对取向，不提供本节所有非线性 PB 测试或 native $D$ 标定，也不把 PRE 的 $\omega=1_D/\tau_D1_D$ 认作原物理整体态。全局纯／局部混的字样相同，不构成两个来源接口的识别。若准备从该关系取得 (51.4)，仍须证明实际词、选择、完整七矩与同一 native 响应的对应。

本定理严格合取定义 47.1 引用的母卷 §§39.8、41.8、C139 以及全部上游完整合同。原 $\Omega$、原 $E,C,u,N,\mathcal P,S,D,q,K/J$ 与局部矩阵同名字母不自动相同；原准备与接受端、参考/副本、真正相关联合、中央/经典/不等维/静默/无轴块、全部零／不等／次归一质量、parent/ready/flags、全部切口、全菜单及固定支持全质量、完整环境与活动输出、成功失败细记录、port/post-port、拒绝／停止／销毁／泄漏、真遗忘、两侧及逆向 Return、每份完整输出的每个旧合法未来全部保留。原精确 $B$ 与闭 $B_{\rm cl}$、未定义请求、钟／控制／单位、同一 $\sigma,t_0$、固定域／resolvent、$3s+r\le1$ 不重定义。Hilbert、Born、张量、CP/Kraus、TP／更新／Lüders、历史／Return 与 Hamiltonian 的条件消费者按 §47.1 的全文前件继续成立，(48.5) 不独自供应那些前件或物理三维的来源。

**开放问题 51.2（共同源的实际测试与响应识别）。** 在全部这些原合同内，能否从同一 $\Omega$ 的实际有限词／保留分支识别 (48.1) 的同一旧 $D$，供应指定帧及全部原 $q,x$ 的完整七矩，并证明 (48.7)，或给出保留这些完整合同的严格障碍？这条来源桥仍未证明。母卷 §41.7 的单个固定非退化 $q$、任意独立完整输出 $g$ 的全称 PB 分类也仍未解决；母卷 §42 的五维第三格秩二模型与此四维定理各守原域。共同响应刚性缩小的是算子律自由度，不结算完整量子起源。

## 追加锚（本行以下为增补区）

## 52. 忠实非迹轨道上的全部标量响应与正测试锥的分离

**定义 52.1（保持原标定的混合轨道测试）。** 沿用母卷定义 41.1、式 (41.2) 的完整 $M_4(\mathbb C)$ 乘法、演员支持和全部复 $q_1q_2\ne0$，分别固定 $\sigma\in\{1,-1\}$。对任意 $U,V\in U(4)$ 置

$$
\begin{gathered}
c=Uc_0U^*,\quad P=UP_0U^*,\quad t=Ut_0(q)U^*,\quad x=x^*=PxP,\\
0<\epsilon\le1/100,\quad
\rho_\epsilon=I_4/4+\epsilon\operatorname{diag}(1,-1,0,0),\\
\phi_{V,\mu}(A)=\mu\operatorname{Tr}(\rho_\epsilon V^*AV),\qquad 0\le\mu<\infty,\\
D_\alpha(a,b)=\alpha i[a,b]/2\quad(\alpha\in\mathbb R),\qquad
h=K_\sigma(c,x),\quad g=D_\alpha(c,t),\quad r=c\circ x,\quad k=c\circ t.
\end{gathered}
\tag{52.1}
$$

每个 $\alpha$ 定义一个固定全域实双线性交替响应，不随 $U,V,q,x,\mu$ 更换。$h$ 始终是原先指定的 $K_\sigma$ 标签；没有将它换成 $D_\alpha(c,x)$。$R_\delta,S_\delta,L,B_\phi$ 均逐字按母卷 (41.2)，包括完整第四行及未中心化实 Gram。

**定理 52.2（任意标量强度通过同一忠实非迹轨道）。** 对定义 52.1 的每个固定实 $\alpha$，原 PB 对全部上述 $U,V,q,x,\mu$ 成立。与此同时，$\rho_\epsilon$ 的酉轨道实线性张成 $H_4$，但其归一正锥包的闭包中每个密度 $s$ 仍满足

$$
(1/4-\epsilon)I_4\le s\le(1/4+\epsilon)I_4.
\tag{52.2}
$$

特别，取 $\alpha=2$ 时该响应对两个分别固定的 $\sigma$ 都不同于 $K_\sigma$，且有合法 $q$、有限 $x$ 与纯正泛函严格违反原 PB。这是矩阵测试族的分离命题，不是完整 native $\Omega$ 的反模型。

证明。这里 $D_\alpha$ 和 $K_\sigma$ 的显式交换子公式允许将所有矩阵共轭回 $U=I$；这是所选响应的性质，不给一般未知 $D$ 添加协变公理。置

$$
j=K_\sigma(c,t),\qquad \lambda=\alpha\sigma,\qquad g=\lambda j.
$$

在实 Hermitian 空间使用未归一 Hilbert–Schmidt 内积 $\langle a,b\rangle=\operatorname{Tr}(ab)$。令 $\mathcal A$ 是演员支持的子空间，$\mathcal O$ 是演员与第四格间的星形子空间；二者正交，$x,h,r\in\mathcal A$、$t,k,j\in\mathcal O$。迹循环性和 $c_0$ 的谱给

$$
\begin{gathered}
\langle x,h\rangle=\langle h,r\rangle=0,\qquad
\langle t,j\rangle=\langle k,j\rangle=0,\qquad\|k\|=\|j\|,\\
\|x\|\le\|r\|\le3\|x\|,\qquad
\tfrac12\|t\|\le\|k\|=\|j\|\le\tfrac32\|t\|,\\
\langle x,r\rangle=\operatorname{Tr}(cx^2)\ge0,\qquad
\langle t,k\rangle=\operatorname{Tr}(ct^2)\ge0.
\end{gathered}
\tag{52.3}
$$

使用实外幂的标准等距分解
$\Lambda^2(\mathcal A\oplus\mathcal O)=\Lambda^2\mathcal A\oplus\Lambda^2\mathcal O\oplus(\mathcal A\otimes\mathcal O)$，原两列的准确外积为

$$
\begin{aligned}
R_\delta\wedge S_\delta={}&
\delta x\wedge r+h\wedge r-\delta k\wedge t-\lambda k\wedge j\\
&+(x\otimes t+\lambda h\otimes j+r\otimes k)
 +\delta(h\otimes t+\lambda x\otimes j).
\end{aligned}
\tag{52.4}
$$

特别，偶交叉项是 $+r\otimes k$。记
$a_\delta=\sqrt{B_{\operatorname{Tr}}(R_\delta,S_\delta)}$、$T^2=a_+^2+a_-^2$。外积范数平方等于实 Gram 行列式；对 $\delta=\pm1$ 相加，平行四边形恒等式给准确的六平方式

$$
\begin{aligned}
T^2=2\big(&\|x\wedge r\|^2+\|h\wedge r\|^2
 +\|k\wedge t\|^2+\lambda^2\|k\wedge j\|^2\\
&+\|x\otimes t+\lambda h\otimes j+r\otimes k\|^2
 +\|h\otimes t+\lambda x\otimes j\|^2\big).
\end{aligned}
\tag{52.5}
$$

$h\otimes j$ 与 $x\otimes t,r\otimes k$ 均正交，且

$$
\|x\otimes t+r\otimes k\|^2
=\|x\|^2\|t\|^2+\|r\|^2\|k\|^2
 +2\langle x,r\rangle\langle t,k\rangle\ge\|x\|^2\|t\|^2.
$$

因此，置 $u=\|x\|\|h\|$、$v=\|x\|\|t\|$、$z=|\lambda|\|t\|^2$，从 (52.5) 中的 $h\wedge r$、$\lambda k\wedge j$ 和偶张量项得到

$$
T^2\ge2u^2+2v^2+z^2/8.
\tag{52.6}
$$

这一步包含 $\lambda=0$，未除以响应强度或任何面积。另一方面，原左端矩阵准确为

$$
L=-2x\circ h+2x\circ k-2t\circ r-2\lambda t\circ j,\qquad
\operatorname{Tr}L=0.
\tag{52.7}
$$

前后两项零迹由 (52.3)，中间两项由块正交。Frobenius 乘积界和 (52.3) 给

$$
\begin{aligned}
\|L\|&\le2u+9v+3z,\\
\|L\|^2&\le
\left(\frac{2^2}{2}+\frac{9^2}{2}+\frac{3^2}{1/8}\right)
 (2u^2+2v^2+z^2/8)
\le\frac{229}{2}T^2.
\end{aligned}
\tag{52.8}
$$

对任一归一轨道密度 $s$，令 $m=1/4-\epsilon$。由 $s\ge mI$、$\|s-I/4\|=\sqrt2\epsilon$ 及 (52.7)–(52.8)，

$$
|\operatorname{Tr}(sL)|\le\sqrt{229}\epsilon T.
\tag{52.9}
$$

每个原矩阵对 $(R_\delta,S_\delta)$ 的实 Gram 满足
$G_s=mG_{\operatorname{Tr}}+G_{s-mI}$、$G_{s-mI}\ge0$。复用 §51 的二维正 Gram 行列式单调性，得到

$$
\sqrt{B_s(R_\delta,S_\delta)}\ge m a_\delta,\qquad
\sum_\delta\sqrt{B_s(R_\delta,S_\delta)}\ge mT.
\tag{52.10}
$$

因 $229<576$，有
$\sqrt{229}\epsilon\le\sqrt{229}/100<24/100\le m$。
当 $T>0$，(52.9) 严格小于 (52.10) 的下界；当 $T=0$，(52.8) 给 $L=0$，两边非负而 PB 仍成立。有限 $\mu>0$ 同时将左端与两面积根乘以 $\mu$；$\mu=0$ 时泛函为零，给零等式。

轨道张成复用 D’Ariano–Perinotti–Sacchi，[*Informationally complete measurements and groups representation*，arXiv:quant-ph/0310013v1，§4.2 式 (29)–(31)](https://arxiv.org/html/quant-ph/0310013v1)：非 $I/d$ 密度的 $SU(d)$ 共轭轨道信息完备，$U(d)$ 给相同轨道。此处也可直接看见：置 $A=\operatorname{diag}(1,-1,0,0)$，其共轭轨道含有 $\pm(E_{ii}-E_{jj})$ 及每条边的 $X_{ij},Y_{ij}$；这些无迹方向张成 $H_4/\mathbb RI$，而 $\rho_\epsilon$ 与 $I/4-\epsilon A$ 的平均为 $I/4$。故实线性张成全 $H_4$。正组合归一后是轨道密度的凸组合，谱序界 (52.2) 保留到闭包，故不能包含秩一密度；有符号重构不能代付正测试覆盖。

最后取 $U=I$、$q=(1,1,0)^{\mathsf T}$、$x=0$、$\alpha=2$，以及

$$
\xi=(-1+2i,1-i,0,0)^{\mathsf T},\qquad\|\xi\|^2=7.
$$

此时 $h=r=0$，所以两个分别固定的 $\sigma$ 给相同的原列；完整乘法直接给

$$
\begin{gathered}
R_+\xi=-e_4/2,\quad S_+\xi=0,\qquad
R_-\xi=e_4/2,\quad S_-\xi=2ie_4,\\
\xi^*L\xi=2,\qquad (B_{\phi_\xi}(R_+,S_+),B_{\phi_\xi}(R_-,S_-))=(0,1).
\end{gathered}
\tag{52.11}
$$

对 $\phi=(\mu/7)\phi_\xi$、任意 $\mu>0$，原 PB 的两边分别为 $2\mu/7$ 和 $\mu/7$，严格失败。∎

**命题 52.3（同一元组的七矩分离与纯共同根的条件实现）。** 在 (52.11) 的元组上，所有满足 $mI\le s\le MI$ 的混合轨道密度及其非负质量泛函满足

$$
5M\phi(S_+^2)\ge28m\phi(R_+^2),\qquad
m=1/4-\epsilon,\quad M=1/4+\epsilon.
\tag{52.12}
$$

此线性不等式在七矩像的闭正锥包中保持，但 (52.11) 的纯泛函不满足它。另在数学系统 $\mathbb C^4\otimes\mathbb C^4$ 上，一个纯根与全部局部门 $U\otimes I$ 可给定理 52.2 的混合轨道，且轨道向量的复线性张成可以是整个全局空间。

证明。直接完整迹为 $\operatorname{Tr}S_+^2=14$、$\operatorname{Tr}R_+^2=5/2$。因此
$\phi(S_+^2)\ge14\mu m$、$\phi(R_+^2)\le(5/2)\mu M$，即 (52.12)。其两坐标均在 (48.7) 的同一七矩中。纯泛函在这两坐标上为 $0,1/4$，所以严格违反；这排除了该元组的七矩正覆盖，而不只排除整个密度锥覆盖。

纯化是标准中间构造：若 $\rho_\epsilon=\operatorname{diag}(\rho_j)$，取
$\Omega_\epsilon=\sum_j\sqrt{\rho_j}e_j\otimes e_j$，则

$$
\langle\Omega_\epsilon,(U^*AU\otimes I)\Omega_\epsilon\rangle
=\operatorname{Tr}(\rho_\epsilon U^*AU).
$$

所有 $\rho_j>0$，而酉矩阵复线性张成 $M_4$；向量化映射
$A\mapsto(A\otimes I)\Omega_\epsilon$ 因而可逆，给全局循环线性张成。这不扩大局部密度的归一正锥包。纯化及其线性代数背景沿 §51 所引 Watrous；这里只实现这个局部矩阵读数，不构造原 native 准备或任意全局输入上的响应。∎

## 53. 完整环境 PB 的第四行归约与任意旁观块

**定理 53.1（固定完整输出的精确环境归约）。** 取有限 $N\ge4$、$c=\operatorname{diag}(1,2,3,0,\ldots,0)$、$P_3=\sum_{j=1}^3E_{jj}$、$P_4=\sum_{j=1}^4E_{jj}$、$Z=I-P_4$，并取原 $t=q_1E_{14}+q_2E_{24}+\mathrm{h.c.}$、$q_1q_2\ne0$。固定任意 $g=g^*\in M_N$ 和一个 $\sigma$，对全部 $x=x^*=P_3xP_3$ 使用原标定 $h=K_\sigma(c,x)$ 及母卷 (41.2) 的完整 $M_N$ 原列。则对全部这些 $x$ 和全部完整正复线性泛函的原 PB，等价于

$$
[g,P_4]=0,\qquad g=g_4\oplus g_Z,
\qquad g_4\text{ 满足相同 }q,\sigma\text{ 的全称 }M_4\text{ 原 PB},
\tag{53.1}
$$

其中 $g_Z$ 是任意 Hermitian 旁观块。等价式没有要求 $g$ 支撑在 $P_4$，也没有分类全部允许的 $g_4$。

证明。先复用母卷 §41.2 的标量行论证，并核对余空间始终是完整 $\mathbb C^N$。对演员谱格 $l=E_{ii},m=E_{jj}$，$i\ne j\le3$，置

$$
\begin{gathered}
a=(c)_{ii},\ b=(c)_{jj},\quad e=E_{ij}+E_{ji},\quad j_0=\sigma i(l-m)e,\quad n_l=2l,\\
\lambda_0=(a-b)/2\ne0,\quad\mu_0=(a+b)/2,\\
V_l=a n_l\circ t-n_l\circ k,\quad Z_l=t+ak.
\end{gathered}
$$

所有有限实 $T,\beta$ 的 $x=Te+\beta n_l$ 都是原合法演员。完整展开正是母卷 (41.5)。Gram 列消元后令 $|\beta|\to\infty$，得到

$$
\begin{gathered}
2|\phi(\lambda_0Tj_0+V_l)|\le
\sqrt{B_\phi(n_l,C_+)}+\sqrt{B_\phi(n_l,C_-)},\\
C_\pm=Z_l\pm g\mp\lambda_0Te-a\lambda_0Tj_0.
\end{gathered}
\tag{53.2}
$$

这是母卷 (41.6)，首项预算为零仍由连续性包含。对任意单位 $\xi\in(1-l)\mathbb C^N$、$d=\|m\xi\|>0$，令 $\eta=j_0\xi/d$、$\nu=e\xi/d=-\sigma i\eta$。向量 $\xi_\tau=(\xi+\tau\eta)/\sqrt{1+\tau^2}$ 上的完整 Gram 恰为

$$
B_{\phi_{\xi_\tau}}(n_l,W)=
\frac{4\tau^2}{(1+\tau^2)^2}
\|\Pi_\eta(W\xi+\tau W\eta)\|^2,\qquad
\Pi_\eta v=v-\operatorname{Re}\langle\eta,v\rangle\eta.
\tag{53.3}
$$

这里保留 $W\xi$ 的全部环境分量，而非在 $P_4$ 内取范数。令 $\tau\downarrow0$ 后，(53.2) 成为母卷 (41.8)；$T\to+\infty,-\infty$ 的两个渐近式迫使第一实配对等号，第二伴轴 $e'=j_0,j'_0=-e$ 给第二实配对，合为

$$
\langle j_0m\xi,(g-\sigma i V_l)\xi\rangle=0.
\tag{53.4}
$$

$d=0$ 时第一槽为零，不作除法。齐次扩展后在 $\xi=u+z$ 与 $\xi=u$ 上相减，$u\in m\mathbb C^N$、$z\in(1-l-m)\mathbb C^N$，消去整个余块；$z=0$ 时的复二次型极化消去 $m$ 块。由
$lV_l(1-l)=l[c,t](1-l)/2$，得到 $l(g-K_\sigma(c,t))(1-l)=0$。这正是母卷 (41.7)–(41.10)，亦即多项式卷 (28.14)–(28.25) 的固定算子标量接口；未使用该卷更强的未知响应前件或 P2。每个演员选一个不同演员作伴，故

$$
g-K_\sigma(c,t)=\sum_{j=1}^3s_jE_{jj}
 +(I-P_3)(g-K_\sigma(c,t))(I-P_3).
\tag{53.5}
$$

前三行到全部旁观方向已被锁定，第四行还需原 PB 的零预算，而非任意压缩。取

$$
u=2e_1/\overline q_1-e_2/\overline q_2.
$$

准确有 $tu=e_4$、$ku=0$。对任意 $z\in Z\mathbb C^N$，$tz=kz=0$。在 $x=0$、$\psi=u+\gamma z$ 上，两个 $R_\delta\psi$ 都为零，故两笔原预算准确为零，而

$$
\phi_\psi(L)=-2\operatorname{Re}\langle e_4,gu+\gamma gz\rangle.
\tag{53.6}
$$

PB 迫使该值为零。取 $\gamma=0,1,i$ 并相减，得 $\langle e_4,gz\rangle=0$。结合 (53.5) 及 Hermitian 性，得到 $P_4gZ=ZgP_4=0$，即 (53.1) 的交换式。$N=4$ 时 $Z=0$，同式包含空旁观块。

此后才写原列的直和分解

$$
R_\delta=R_{4,\delta}\oplus0,\quad
S_\delta=S_{4,\delta}\oplus\delta g_Z,\quad L=L_4\oplus0.
$$

对任意完整正 $\phi$，令 $\phi_4,\phi_Z$ 为其块限制；完整乘法给精确预算差

$$
\begin{aligned}
B_\phi(R_\delta,S_\delta)
 &=B_{\phi_4}(R_{4,\delta},S_{4,\delta})
   +\phi_4(R_{4,\delta}^2)\phi_Z(g_Z^2),\\
\phi(L)&=\phi_4(L_4).
\end{aligned}
\tag{53.7}
$$

后加两因子非负，故 $M_4$ 原 PB 蕴含完整环境原 PB，任意旁观 $g_Z$ 都允许。反向取任意正 $\phi_4$ 并延为 $A\mapsto\phi_4(J^*AJ)$，$J:\mathbb C^4\to P_4\mathbb C^N$ 为坐标等距嵌入；分块以后才有原三类乘积的准确压缩，故完整 PB 蕴含同一 $g_4$ 的 $M_4$ PB。任意压缩保乘法没有被用作前提，零质量与零预算均保留。∎

## 54. 不预设角单位零的同帧刚性与一个全局响应的拼接

**定理 54.1（完整输入的同一 48 帧）。** 删除定义 48.1 中 $D(I_4,a)=0$ 这一前提，保持其余全部条件：同一个实双线性交替 $D_4:H_4\times H_4\to H_4$、同一 $\sigma$、原 (48.2) 的 48 个 $U_f$、每帧全部合法复 $q$、全部支持演员 $x$、全部完整正泛函，以及原指定 $h=K_\sigma(c,x)$。则 (48.4) 仍当且仅当 $D_4=K_\sigma$。

证明。令 $F=D_4-K_\sigma$。母卷 §41.2 使每个实际合法 $q$ 的 $U_f^*F(c_f,t_{f,q})U_f$ 对角；其非对角坐标是 $q$ 的四个实分量的线性函数，故从合法开稠密集延到四个 elementary 腿。此步骤只延拓矩阵等式，不宣称非法零腿准备可用。

将 (49.1) 的十五个无迹基 $\mathcal B_0,\ldots,\mathcal B_{14}$ 后接 $I_4$，完整输入坐标为

$$
\widetilde\chi(a)=(\chi(a),\operatorname{Tr}(a)/4)\in\mathbb R^{16}.
\tag{54.1}
$$

一般交替映射有 $\binom{16}{2}\cdot16=1920$ 个实系数；去掉输出中心后仍有 $120\cdot15=1800$ 个，未删除含单位的输入楔积。取
$a=\widetilde\chi(U_fc_0U_f^*)$、$b=\widetilde\chi(U_fT_\nu U_f^*)$，定义

$$
\widetilde M_{(f,\nu,l),(i,j,k)}
=(a_ib_j-a_jb_i)\ell_l(U_f^*\mathcal B_kU_f),
\quad\begin{matrix}0\le f<48,\ 0\le\nu<4,\ 0\le l<12,\\
0\le i<j<16,\ 0\le k<15.\end{matrix}
\tag{54.2}
$$

行列顺序与 (49.2) 相同，唯一输入变化是最后的单位坐标及 $i<j<16$。形状为 $2304\times1800$；相应输入楔积矩阵 $\widetilde W$ 的形状是 $192\times120$。在 $p=1009$ 下取
$J$ 为 $\operatorname{RREF}(\overline{\widetilde M}^{\mathsf T})$ 的最左主元列递增表，保留所有原序列，则指定有限算术为

$$
|J|=1800,\qquad
\det\overline{\widetilde M}_{J,:}=20\pmod{1009},\qquad
\operatorname{rank}_{1009}\overline{\widetilde W}=120.
\tag{54.3}
$$

逐行无符号 16 位小端数组的身份是

| 数学数组 | SHA256 |
| --- | --- |
| $\overline{\widetilde M}$ | `f3f2a2584bdf4ce42b289481a46e04f7b9c831ef893f6f672853c0c432668e68` |
| $J$ | `147028df380e6f0dbd40884d9926dd80d277dc6e54c865b6e932f237cbe6b921` |
| $\overline{\widetilde W}$ | `aa03f960a69e8a8622c6ba462af10bad87146d9a8e767233f842ee4016ff3812` |
| $(d_0,\ldots,d_{191})$ | `904c8029c79ccf3dfe0b18ee019645e4b02509ba1907c6b6cab3c70ee10c9cc2` |

其不可变数学数据引文为 [trureturing-experiments，commit `e8f5c2f5bc9f7ae044cd50a4f8b2018172f62e53`，完整输入数组](https://github.com/the-omega-institute/trureturing-experiments/tree/e8f5c2f5bc9f7ae044cd50a4f8b2018172f62e53/experiments/auric-ambient-pb-corner-research)。原 48 帧的来源身份仍是 (49.6) 所引 `651b00b5abcfc10de377ae180bcfde38752bdffd`，没有更换帧、输出基或伴随约定。哈希只标识数组，承担有限推理的是 (48.2)、(54.1)–(54.3) 的矩阵与非零子式。

所有有理系数都在 $\mathbb Z[1/(2\prod_jd_j)]$ 中，$5\le d_j\le26$；1009 素且不除任一分母，故模约化为环同态。非零模子式使有理子式、继而实子式非零，适用于任意实映射系数而非仅有理系数。于是共同对角约束的完整核恰为

$$
F(a,b)=f(a,b)I_4,\qquad f\in(\Lambda^2H_4)^*,
\qquad\dim(\Lambda^2H_4)^*=120.
\tag{54.4}
$$

这里的秩结论是完整输入的新矩阵计算，不能由旧 1575 秩直接推定。中心值在每帧都对角，故上述核既不漏项，也不误报为零核。

现用同一个 $D_4$ 排除全部中心值。若某个 elementary 输入上 $s=f(c_f,t_{f,\nu})\ne0$，引理 50.1 的原有限严格见证在帧坐标中适用；它包含全部非零 $s$、两个 $\sigma$、两条腿及两种相位。取另一臂的 elementary $T'$，同一实际映射在合法扰动上给

$$
\begin{gathered}
t_\eta=U_f(T_\nu+\eta T')U_f^*,\qquad
s_\eta=s+\eta f(c_f,U_fT'U_f^*),\\
g_\eta=K_\sigma(c_f,t_\eta)+s_\eta I_4.
\end{gathered}
\tag{54.5}
$$

对充分小的非零实 $\eta$，原 $q_1q_2\ne0$；固定的有限 $x,\phi$ 的完整七矩连续，原严格失败及两笔正预算保持，矛盾。因此 $f$ 在全部 192 个测试楔积上为零，(54.3) 的 120 秩给 $f=0$，包括含单位的全部输入。没有将 $s_\eta$ 人为固定为 $s$，也未使用 $D_4$ 的协变性。反向直接复用 §50 的零残量交换子恒等式与同一正泛函 Schwarz，包含全部退化预算。∎

**定理 54.2（所有四维角识别同一个完整全局响应）。** 取有限 $N\ge4$、一个实双线性交替映射
$D:H_N\times H_N\to H_N$ 和一个共同 $\sigma$。对每个秩四投影 $P$，选一个等距嵌入 $J_P:\mathbb C^4\to P\mathbb C^N$。假定同一实际 $D$ 对该角的全部 $J_PU_f$ 运输帧、每个原合法 $q$、每个支持于该帧前三格的 $x$、每个完整 $M_N$ 正泛函，都满足原标定 PB，其中

$$
c=J_PU_fc_0U_f^*J_P^*,\quad
 t=J_PU_ft_0(q)U_f^*J_P^*,\quad g=D(c,t),\quad h=K_\sigma(c,x).
\tag{54.6}
$$

则且仅则 $D(a,b)=K_\sigma(a,b)$ 对全部 $a,b\in H_N$ 成立。前件是所有秩四角的连续族，每角 48 帧；不是全局仅 48 个测试。没有预设全局或局部单位零、协变、导子、P2 或压缩乘法性。

证明。每个角内取实际压缩映射

$$
D_P(a,b)=J_P^*D(J_PaJ_P^*,J_PbJ_P^*)J_P.
\tag{54.7}
$$

它实双线性交替；不能从全局单位零推断其单位零，因为
$D_P(I_4,a)=J_P^*D(P,J_PaJ_P^*)J_P$。定理 53.1 对每份测试输出先锁住完整第四行，随后才给同一 $D_P$ 的准确 $M_4$ PB。定理 54.1 无须角单位零，因而 $D_P=K_\sigma$ 对全部角内输入成立。

固定任意秩一投影 $p,q$，保留同一个完整 Hermitian 输出
$E=D(p,q)-K_\sigma(p,q)$。每个包含两条像射线的秩四 $P$ 都给 $PEP=0$。对任意全局向量 $v$，空间
$\operatorname{ran}p+\operatorname{ran}q+\mathbb Cv$ 的维数至多三，可延为秩四空间，故

$$
\langle v,Ev\rangle=\langle v,PEPv\rangle=0.
$$

Hermitian 极化给 $E=0$，没有遗失任何全局输出方向。有限谱分解将任意 Hermitian $a,b$ 写为秩一投影的实线性组合，实双线性遂给全局 $D=K_\sigma$。特别，单位零是结论。这里逐角固定的压缩都来自同一个 $D$，分别拟合的角映射不能替代此前件。反向在完整 $M_N$ 用零残量符号恒等式和正泛函 Schwarz；证明与矩阵维数无关。∎

## 55. 正测试、完整角与原共同源的条件连接

**定义 55.1（原源应用的完整前件）。** 定理 52.2 与 53.1–54.2 分别约束测试锥和同一响应律。若要消费 54.2，须在原共同 $\Omega$ 的同一忠实完整表示中识别同一个旧 native $D$，证明其实际全域实双线性与交替性，供应每个所需角的实际运输帧、原合法 $q,x$ 及同一分支的完整七矩，并证明这些完整正测试的原 PB。非选择性读数仍准确为

$$
p(w,e)=\omega(U_w^*eU_w),
$$

不要求门门保 $\omega$。选择性读数及全部细记录按 (51.4)。全正锥闭包或逐元组七矩闭正锥覆盖按 (48.6)–(48.7) 是充分供应方式，仍不被称为一般必要条件。定理 52.2–52.3 说明即使线性信息完备、忠实非迹、共同根全局纯且向量轨道循环，也不能由这些性质单独取得该覆盖。纯射线稠密只供应固定完整元组的正测试极限，不供应实际帧、$q,x$、角的可用性，也不将指定 $h=K_\sigma(c,x)$ 识别为旧 native $D(c,x)$。

此应用严格合取 §47、定义 51.1 的全文以及其母卷 §§39.8、41.8、C139 全部递归钉版合同：同一旧 $\Omega,E,C,u,N,\mathcal P,S,D,q,K/J$，原准备、接受端、参考／副本和真正相关联合，中央／经典／不等维／静默／无轴块，零／不等／次归一质量，parent／ready／flags，全部切口、完整菜单及固定支持全质量，完整环境／活动输出、成功失败细记录、port／post-port、拒绝／停止／销毁／泄漏、真遗忘、每份完整输出的每个旧合法未来、两侧及逆向 Return、物理钟／控制／单位、同一 $\sigma,t_0$、固定域／resolvent 和 $3s+r\le1$ 均保持原义。原精确 $B$ 与闭 $B_{\rm cl}$ 不合并，未定义请求不补零。原 Hilbert／Born／张量／CP-Kraus／TP-更新-Lüders／历史-Return／Hamiltonian 消费者仍只在 §47 所列完整前件下适用。

本条件连接与[双侧正重置卷 V §73](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md) 的 PRE、NB、正补全和原尺度律分别保留：其同一实际 $L,p$ 的静态归一化不自动识别这里的旧 native $D$。[C128 定理 347.3](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 的条件桥只在其假设 347.1、定理 346.1 的任一充分入口及式 (347.3) 的同一旧响应等式下使用，未将较早的第一槽缺口改称无条件不可能。原较强 $\mathsf H_A(D)$ 中的 P2 和嵌套 exact-$D$ 恒等式不被删除，也不被偷渡到这里的标定 raw PB；未标定响应问题是另一个前件。四维任意完整输出、五维第三格秩二模型与物理三空间仍是三个不同的对象。

**定义 55.2（推导归属与未决边界）。** 本批 `repo-derived` 的承重关系是 (52.5)–(52.10) 对全部标量强度的统一原 PB 估计及其正七矩分离、(53.6)–(53.7) 的第四行补全与精确旁观自由、完整输入的 (54.2)–(54.4) 和同一全局响应的合成。母卷的标量行证明、§50 严格中心见证及 §51 正 Gram 提升直接复用。混合轨道的有限恒等式数据同属 [trureturing-experiments，commit `e8f5c2f5bc9f7ae044cd50a4f8b2018172f62e53`](https://github.com/the-omega-institute/trureturing-experiments/tree/e8f5c2f5bc9f7ae044cd50a4f8b2018172f62e53/experiments/auric-mixed-orbit-pb-research)，不以有限数值样本代替定理 52.2 的全称解析推导。D’Ariano–Perinotti–Sacchi 的轨道信息完备、实外幂／Gram／Cauchy–Schwarz、模素数子式提升、极化与谱分解均是成熟中间工具；Jordan 到结合方向的背景沿 Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，其序导子／动力学对应的前提不由这里的 PB 自动支付。这些引用不宣称本 PB 特定估计已有文献定理，也不主张历史优先权或穷尽检索。

母卷固定单个 $q$、任意独立 $g_4$ 的全称允许集分类仍未由此证明；本结果亦未给稳定性、最少帧数或无限维扩展。尚需证明的是定义 55.1 的同一旧源识别、实际准备／接受、全角与全标签供应、原标定和完整矩读取，而非重新证明已有条件矩阵律。以上为纸面条件数学，不宣称 Lean／kernel 认证、物理源已实现或完整量子起源已导出。

## 追加锚（本行以下为增补区）

## 56. 同一未标定响应的全酉 PB 与两个整体方向

**定义 56.1（未标定的完整四维接口）。** 取 $H_4=\operatorname{Herm}_4(\mathbb C)$，$a\circ b=(ab+ba)/2$，以及一个固定的、任意的实双线性交替映射 $D:H_4\times H_4\to H_4$。不商掉单位输入或中心输出。对每个 $U\in U(4)$，令

$$
\begin{gathered}
c=U\operatorname{diag}(1,2,3,0)U^*,\qquad
P=U\operatorname{diag}(1,1,1,0)U^*,\\
x=x^*=PxP,\qquad
q=(q_1,q_2,0)^{\mathsf T}\in\mathbb C^3,\quad q_1q_2\ne0,\\
t=U\begin{pmatrix}0_{3\times3}&q\\q^*&0\end{pmatrix}U^*,\qquad
h=D(c,x),\quad g=D(c,t),\quad r=c\circ x,\quad k=c\circ t,\\
R_\delta=x+\delta(h-k),\qquad S_\delta=t+\delta(r+g),\qquad \delta\in\{1,-1\},\\
L=-2x\circ(h-k)-2t\circ(r+g).
\end{gathered}
\tag{56.1}
$$

$h,g$ 必须来自同一个 $D$，没有预先标定任何一个标签。对完整 $M_4(\mathbb C)$ 上任意正复线性泛函 $\phi(A)=\operatorname{Tr}(sA)$，$s\ge0$、$0\le\operatorname{Tr}s<\infty$，定义

$$
B_\phi(A,B)=\phi(A^2)\phi(B^2)-\phi(A\circ B)^2,\qquad
|\phi(L)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{56.2}
$$

后一式称为本节的全称 raw PB：它遍及 (56.1) 的全部 $U,x,q$ 与全部上述 $\phi$。平方、乘积、输出和泛函都保留完整第四行列；两笔预算使用同一元组及同一泛函。正性保证两预算非负；非忠实、零质量及零预算均在域内。

**定理 56.2（全部 1920 个系数的未标定充要分类）。** 定义 56.1 的全称 raw PB 当且仅当存在一个整体的 $\sigma\in\{-1,+1\}$，使

$$
D(a,b)=\sigma\,\frac{i}{2}[a,b]\qquad(a,b\in H_4).
\tag{56.3}
$$

整体方向不随输入、角、演员或泛函变化。必要性不以单位零、酉协变、导子／序导子、P2、嵌套恒等式、闭合、已拟合响应族或演员标定为前提。这是所有 $U\in U(4)$ 的定理；§54 的标定 48 帧结论不作为这里未标定必要性的前提。以下 §§57–58 给出证明，包括全部输出分量与双向蕴含。

## 57. 零预算的全核几何与完整系数正规形

**引理 57.1（合法极限留下的全核压缩）。** 若 (56.2) 成立，记 $\Pi$ 为 $r=c\circ x$ 的完整核的正交投影，则

$$
\Pi\bigl(x\circ D(c,x)\bigr)\Pi=0
\qquad\text{对每个 }U,x.
\tag{57.1}
$$

证明。固定 $c,x$，在合法域内取 $q_1=q_2=\epsilon>0$ 并令 $\epsilon\downarrow0$。有限维实双线性使同一固定 $D$ 的 $g=D(c,t)\to0$，而 $h=D(c,x)$ 保持固定。各标签连续趋于

$$
R_\delta\to x+\delta h,\qquad S_\delta\to\delta r,\qquad L\to-2x\circ h.
$$

对任意 $v\in\ker r$ 使用允许的 $\phi_v(A)=v^*Av$。预算是把复向量空间视为实内积空间、内积取 $\operatorname{Re}\langle\ ,\ \rangle$ 后，$R_\delta v,S_\delta v$ 的 Gram 行列式。因 $rv=0$，两笔预算都趋于零；非负平方根连续，故 $v^*(x\circ h)v=0$。对整个复核作 Hermitian 极化，得 (57.1)。这里没有把有限的 $q=0$ 宣称为合法准备；核包含演员外的第四方向。∎

**引理 57.2（共同三角的完整输出块）。** (57.1) 蕴含：对每个三维复子空间 $E\subset\mathbb C^4$、投影 $P_E$ 及所有 $a,b\in H_4$ 满足 $a=P_EaP_E,b=P_EbP_E$，

$$
P_ED(a,b)(I-P_E)=0.
\tag{57.2}
$$

此时尚未令演员外的标量输出为零。

证明。先固定 $E$ 中一个有序正交基和 $c|_E=\Lambda=\operatorname{diag}(1,2,3)$。取

$$
C_{ij}=\frac{2}{\lambda_i+\lambda_j},\quad
X(u)=\operatorname{diag}(u)C\operatorname{diag}(\overline u),\quad
r|_E=uu^*,\qquad u_1u_2u_3\ne0.
\tag{57.3}
$$

$C$ 是 $\sqrt2e^{-\lambda_i s}$ 在 $L^2(0,\infty)$ 中的 Gram 矩阵，故正定；直接有

$$
\det C=\frac1{5400},\qquad C^{-1}\mathbf1=p=(6,-30,30)^{\mathsf T}.
\tag{57.4}
$$

令 $e$ 为 $E^\perp$ 的单位向量，$F(u)=P_ED(c,X(u))e$。在 (57.1) 中保留 $E\cap u^\perp$ 与 $e$ 的交叉压缩，得 $X(u)F(u)\in\mathbb Cu$。$X(u)$ 在 $E$ 上可逆，所以

$$
\frac{\overline u_1F_1(u)}{p_1}
=\frac{\overline u_2F_2(u)}{p_2}
=\frac{\overline u_3F_3(u)}{p_3}.
\tag{57.5}
$$

每个 $F_j$ 是关于 $u,\overline u$ 的双次数 $(1,1)$ 多项式。把 $u=s+it,\overline u=s-it$ 视作独立复变量的可逆线性替换，真实 $s,t$ 上的多项式恒等式即为独立变量环上的恒等式。故 (57.5) 的共同多项式双次数为 $(1,2)$，却同时被三个互素的 $\overline u_j$ 整除，只能为零。于是 $F=0$。由连续性延到坐标为零的 $u$；秩一 $uu^*$ 实张成 $\operatorname{Herm}(E)$，而 $X\mapsto c\circ X$ 在该空间可逆，故 $P_ED(c,x)e=0$ 对全部支持 $x$ 成立。

在任一固定基中，$(1,2,3)$ 的排列实张成三个对角方向；再让基遍及各 Hermitian $a$ 的谱基，所有这样的 $c$ 实张成 $\operatorname{Herm}(E)$。双线性给 (57.2)。Hermitian 输出同时给反向交叉块为零。论证逐个实际 $D$ 进行，未使用 $D$ 的协变性。∎

**引理 57.3（共同角条件的全实正规形）。** 任意实双线性交替 $D:H_4^2\to H_4$ 满足 (57.2)，当且仅当存在实交替二形式 $\eta$、实线性泛函 $\ell$ 和 Hermitian 矩阵 $H$，使

$$
D(a,b)=\eta(a,b)I_4+\ell(a)b-\ell(b)a
       +\frac{i}{2}(aHb-bHa).
\tag{57.6}
$$

参数空间维数为 $120+16+16=152$；这是共同角条件的分类，尚非 PB 的分类。

证明。以下给出一个覆盖完整实系数空间的有限系数证明。按顺序取实基

$$
\mathcal B=(E_{11},E_{22},E_{33},E_{44},
 X_{12},Y_{12},X_{13},Y_{13},X_{14},Y_{14},X_{23},Y_{23},X_{24},Y_{24},X_{34},Y_{34}),
$$

其中 $X_{ij}=E_{ij}+E_{ji},Y_{ij}=i(E_{ij}-E_{ji})$，$i<j$ 按字典序。写
$D(\mathcal B_a,\mathcal B_b)=\sum_\gamma d_{ab,\gamma}\mathcal B_\gamma$，列顺序为 $0\le a<b<16$ 再 $0\le\gamma<16$，共有 $1920$ 个实未知数。

定义一个有限的有理高斯角族。取 $U_0=I_4$，从 $s_0=173$ 连续递推

$$
s_{n+1}=(1664525s_n+1013904223)\bmod2^{32},\qquad z_n=(s_n\bmod5)-2,
$$

并对 $1\le j\le32$ 置

$$
v_j=(z_{8j-7},\ldots,z_{8j-4})^{\mathsf T}
+i(z_{8j-3},\ldots,z_{8j})^{\mathsf T},\quad
 d_j=v_j^*v_j,\quad U_j=I_4-2v_jv_j^*/d_j.
\tag{57.7}
$$

这些 $d_j$ 非零且在 $[7,26]$ 内，$U_j=U_j^*=U_j^{-1}$。令 $\mathcal A$ 为基 $\mathcal B$ 中支持前三格的九个成员，保持原序。对每个角、每个 $A<B\in\mathcal A$ 以及 $l=1,2,3$，取

$$
\operatorname{Re}(U_j^*D(U_jAU_j^*,U_jBU_j^*)U_j)_{l4}=0,
\quad
\operatorname{Im}(U_j^*D(U_jAU_j^*,U_jBU_j^*)U_j)_{l4}=0.
\tag{57.8}
$$

行序依次为 $j$、演员输入对、$l$、实部／虚部。若 $\xi,\zeta$ 是这两个运输输入在 $\mathcal B$ 中的坐标，$\rho$ 是该行的实读出，则约束矩阵的该行该列准确为

$$
A_{(j,A,B,\rho),(ab,\gamma)}
=(\xi_a\zeta_b-\xi_b\zeta_a)\rho(U_j^*\mathcal B_\gamma U_j).
\tag{57.9}
$$

矩阵 $A$ 形状为 $7128\times1920$。再令 $T$ 的 $152$ 列为 (57.6) 中 $\eta$ 的 $120$ 个 elementary 二形式、$\ell$ 的 $16$ 个坐标泛函及 $H$ 的 $16$ 个基矩阵对应的输出系数。每个这种映射都满足所有共同角条件：前三项块对角，$aHb,bHa$ 的两侧支撑都在 $E$，故 $AT=0$。

在素数 $p=1009$ 下，以 $i\mapsto469$ 计算有理高斯表达式，$469^2\equiv-1$；所有最终实坐标有理。令 $J$ 为 $\operatorname{RREF}(\overline A^{\mathsf T})$ 的主元列递增表，$K$ 为 $\operatorname{RREF}(\overline A_{J,:})$ 的主元列递增表。精确有限矩阵给

$$
|J|=|K|=1768,\qquad \det\overline A_{J,K}=551\pmod{1009}.
\tag{57.10}
$$

同样，令 $J_T$ 为 $\operatorname{RREF}(\overline T^{\mathsf T})$ 的主元列递增表，则

$$
|J_T|=152,\qquad \det\overline T_{J_T,:}=556\pmod{1009}.
\tag{57.11}
$$

两个逐行 uint16 小端约化矩阵的身份为

| 矩阵 | SHA256 |
| --- | --- |
| $\overline A$ | `25564a59f91bfe091c4fedf3049c4be9bc99f97ca36f0fda0a8253247c1ec8be` |
| $\overline T$ | `ffc38ef00c59f450bc4ac621d1b65bc4896a7871d1ce0fe1465161f885d78ac9` |

有限参数表、主元表及数学数组见 [trureturing-experiments，commit `6d0281133e817e63ef8de3f2fbe647818c1f1cb5`，complex](https://github.com/the-omega-institute/trureturing-experiments/tree/6d0281133e817e63ef8de3f2fbe647818c1f1cb5/experiments/auric-uncalibrated-complex-real-pb/complex)。决定推理的是 (57.7)–(57.11) 的精确矩阵和非零子式，而非数组哈希。分母只含 $2$ 与各 $d_j$ 的因子，均不被 1009 整除，模约化为相应有理系数环的同态。因此 $\operatorname{rank}_{\mathbb R}A\ge1768$、$\operatorname{rank}_{\mathbb R}T=152$。结合 $AT=0$，有限核已恰为 $\operatorname{im}T$；全称共同角核夹在这个有限核与 $\operatorname{im}T$ 之间，故两者相等。该结论覆盖任意无理实系数，并未只检查有理 $D$。

(57.6) 保留全部中心值和含单位的输入楔积。若把其交叉项在交替化前写成一般乘积形，正确的是 $aMb+bNa$，交替性才给 $N=-M$、Hermitian 性给 $M^*=-M$，即 $M=iH/2$；不能将第二项误写成 $bNb$。这里有限系数证明本身不需要借用任何额外的交换映射分类前提。上述 33 角只是正规形的系数证书，不是 33 份 PB 物理帧，也未证明 33 或旧 48 帧足以替代定义 56.1 的全酉量词。∎

## 58. 正规形的逐项消元、有限严格见证与充分性

**定理 58.1（全称 PB 将正规形压成两个方向）。** 在定义 56.1 下，(57.6) 与全称 PB 共同蕴含 (56.3)。

证明。先消去 $\ell$。取 $H$ 的一组正交特征基，选其中两个向量 $e_i,e_j$，并在其余两个特征向量张成的平面内任取单位 $k$。令 $E=\operatorname{span}(e_i,e_j,k)$，在这三个轴上给 $c$ 互异谱 $1,2,3$，记相应谱值 $\lambda_i,\lambda_j,\lambda_k$。令 $x$ 在这个演员基中对角。虽然 $k$ 不必是 $H$ 的特征向量，$e_i,e_j$ 仍是，故 (57.6) 的 $H$ 项在这两个轴的整列都为零，且

$$
h_i=\eta(c,x)+\ell(c)x_i-\ell(x)\lambda_i,\qquad
h_j=\eta(c,x)+\ell(c)x_j-\ell(x)\lambda_j.
\tag{58.1}
$$

沿引理 57.1 的合法 $q\to0$，$R_\delta e_i,S_\delta e_i$ 均在同一实直线上，两笔极限预算为零，PB 给 $x_ih_i=0$。对 $x_i\ne0$ 得 $h_i=0$，再由线性／连续性扩到全部对角 $x$；$j$ 亦然。相减并置 $x=kk^*$，由 $\lambda_i\ne\lambda_j$ 得 $\ell(kk^*)=0$。所有特征坐标二平面内的秩一投影实张成 $H_4$，所以 $\ell=0$。

再在任意三个 $H$ 特征向量上按序放置谱 $(1,2,3)$，令 $x=C$ 为 (57.3) 的实矩阵，$u=\mathbf1$，并记这三个 $H$ 特征值为 $h_1,h_2,h_3$、$d=\operatorname{diag}(h_1,2h_2,3h_3)$。直接展开得

$$
x\circ D(c,x)=\eta(c,x)C+\frac{i}{4}[d,C^2].
\tag{58.2}
$$

对任意非零实 $y\perp\mathbf1$，实斜矩阵的二次型为零而 $y^{\mathsf T}Cy>0$；(57.1) 因而先给 $\eta(c,C)=0$。保留不同核向量之间的交叉项，继而有

$$
0=(e_1-e_2)^{\mathsf T}[d,C^2](e_1-e_3)
=\frac4{15}(d_1-2d_2+d_3),
\quad h_1-4h_2+3h_3=0.
\tag{58.3}
$$

交换第一、第三个特征向量再作同一测试，得到 $h_3-4h_2+3h_1=0$，故三值全相等。任意三个特征向量均可使用，故 $H=\alpha I_4$，其中 $\alpha\in\mathbb R$ 为同一个常数。

现 (57.6) 只剩 $D(a,b)=\eta(a,b)I_4+\alpha i[a,b]/2$。对每个角与 (57.3) 的全部非零坐标 $u$，$x=X(u)$ 在演员上正定，且

$$
x\circ\frac{i[c,x]}2=\frac{i}{4}[c,x^2]
=\frac{i}{2}[r,x],\qquad \Pi[r,x]\Pi=0.
\tag{58.4}
$$

取 $E\cap u^\perp$ 中非零向量，(57.1) 给 $\eta(c,X(u))=0$。稠密延拓到全部 $u$，再由秩一张成和 $x\mapsto c\circ x$ 可逆，得 $\eta(c,x)=0$ 对每个支持演员成立。按引理 57.2 的 $c$ 轨道张成，$\eta(a,b)=0$ 对所有共同三角内输入成立。任意两份秩一 Hermitian 投影可装入一个共同三角；秩一实张成与双线性遂使 $\eta=0$，包括全部标量／旁观输出。因此

$$
D(a,b)=\alpha\frac{i[a,b]}2\qquad(a,b\in H_4)
\tag{58.5}
$$

已经由 PB 推出，而非预先限制了拟合族。

最后用有限、合法的完整元组排除 $|\alpha|\ne1$。以下均取 $U=I$，$\phi_v(A)=v^*Av$，且两标签都由 (58.5) 给定。
若 $|\alpha|>1$，置 $M=|\alpha|+1$、$x=0$、$q=(1,1)$、
$v=(2iM-2,\,2-iM,\,0,\,0)^{\mathsf T}$。完整乘法给

$$
\phi_v(L)=2\alpha M,\qquad
R_\delta v=-\delta e_4,\quad
S_\delta v=i(M-\delta\alpha)e_4,\quad
B_\delta=(M-\delta\alpha)^2.
\tag{58.6}
$$

所以右侧为 $2M$，左侧为 $2|\alpha|M>2M$，严格失败。这里复向量的实 Gram 保留了同一复直线内的相位面积。

若 $|\alpha|<1$，置 $\tau^2=(1-\alpha^2)/82>0$，$q=(1,\tau)$、$x=E_{11}/\tau^2$、$v=(\tau,0,0,1)^{\mathsf T}$。这是有限非零质量的合法元组，并且

$$
\begin{aligned}
\phi_v(L)&=-1/\tau,\\
R_\delta v&=(1/\tau-\delta/2,\,-\delta\tau,\,0,\,-\delta\tau/2)^{\mathsf T},\\
S_\delta v&=(1+\delta/\tau+\delta i\alpha/2,\,
\tau+\delta i\alpha\tau,\,0,\,\tau-\delta i\alpha\tau/2)^{\mathsf T}.
\end{aligned}
\tag{58.7}
$$

记 $B_\delta=B_{\phi_v}(R_\delta,S_\delta)$。两笔完整实 Gram 中，仅实坐标 $(1,4)$ 的子式就等于 $3/2$，故 $B_\delta\ge9/4$。完整展开给

$$
\begin{aligned}
2(B_++B_-)\tau^2
&=\alpha^2+(25+21\alpha^2/4)\tau^2
 +(1+5\alpha^2/2)\tau^4+(1+25\alpha^2/4)\tau^6\\
&\le\alpha^2+41\tau^2=(1+\alpha^2)/2<1.
\end{aligned}
\tag{58.8}
$$

不等式使用 $\tau^2<1$、$\alpha^2<1$。因 $(\sqrt{B_+}+\sqrt{B_-})^2\le2(B_++B_-)$，PB 再次严格失败。必要性遂只留下 $\alpha=\pm1$，同一个整体 $\sigma=\alpha$。∎

**定理 58.2（两个方向的完整正泛函充分性）。** (56.3) 蕴含 (56.2)，不限制正质量、忠实性或预算是否为零。

证明。记 $K_\sigma(a,b)=\sigma i[a,b]/2$，$Z_\delta=R_\delta+iS_\delta$。原标签直接给

$$
\begin{array}{lll}
\sigma=+1:&Z_\delta=(I+\delta ic)(x+it),&
Z_\delta^*Z_\delta=(x-it)(I+c^2)(x+it),\\
\sigma=-1:&Z_\delta=(x+it)(I+\delta ic),&
Z_\delta Z_\delta^*=(x+it)(I+c^2)(x-it).
\end{array}
\tag{58.9}
$$

右侧与 $\delta$ 无关。不能删掉这些伴随符号而宣称 $Z_\delta Z_\delta$ 不变。另一方面，直接由原定义

$$
(R_+^2+S_+^2)-(R_-^2+S_-^2)=-2L.
$$

把此式代入两种伴随乘积的差，均得到

$$
L=K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-).
\tag{58.10}
$$

对任意 Hermitian $A,B$，正复线性泛函给复 Gram 矩阵

$$
\begin{pmatrix}\phi(A^2)&\phi(AB)\\\phi(BA)&\phi(B^2)\end{pmatrix}\ge0,
\quad \operatorname{Re}\phi(AB)=\phi(A\circ B),\quad
|\phi(K_\sigma(A,B))|^2\le B_\phi(A,B).
\tag{58.11}
$$

这是普通正泛函 Cauchy–Schwarz 的二维形式。对 (58.10) 用三角不等式即得 PB；未除以质量、Gram 或特征值，因而完整包含所有退化情形。结合 58.1，定理 56.2 得证。∎

## 59. 实四维完整接口的全系数障碍

**定义 59.1（域自然的实版本）。** 把定义 56.1 中的 $H_4,U(4),q\in\mathbb C^2,*$ 分别换成 $J=\operatorname{Sym}_4(\mathbb R),O(4),q\in\mathbb R^2,{}^{\mathsf T}$，仍要求 $q_1q_2\ne0$。一个固定的任意实双线性交替 $D:J^2\to J$ 同时给 $h=D(c,x),g=D(c,t)$，其余原 raw 标签逐字不变。泛函取完整实正泛函 $\phi(A)=\operatorname{Tr}(sA)$，$s\ge0$、任意有限非负质量。这里不额外假设单位零、协变、导子、序导子、P2、嵌套或闭合。

**定理 59.2（全核条件只有零映射，原 PB 没有解）。** 在定义 59.1 的全部 $U,x$ 上，令 $\Pi$ 为完整 $\ker(c\circ x)$ 的投影，则

$$
\bigl[\ \Pi(x\circ D(c,x))\Pi=0\ \text{对全部 }U,x\ \bigr]
\quad\Longleftrightarrow\quad D=0.
\tag{59.1}
$$

但 $D=0$ 在一份有限合法元组上严格违反原 PB。因此定义 59.1 的全称 PB 解集为空。

证明。引理 57.1 的合法 $q=(\epsilon,\epsilon)\to0$、Gram 连续性及实极化原样给出必要的全核条件，仍保留演员外核方向。以下直接在全部 $\binom{10}{2}10=450$ 个实系数上求其核。

按顺序取

$$
\mathcal B_{\mathbb R}=(E_{11},E_{22},E_{33},E_{44},
X_{12},X_{13},X_{14},X_{23},X_{24},X_{34}).
\tag{59.2}
$$

若 $c_a,x_a$ 是在此基的实际坐标、$v\in\ker(c\circ x)$，则全核条件的一条必要标量等式为

$$
0=v^{\mathsf T}(x\circ D(c,x))v
=\sum_{a<b,\gamma}(c_ax_b-c_bx_a)(xv)^{\mathsf T}\mathcal B_{\mathbb R,\gamma}v\ d_{ab,\gamma}.
\tag{59.3}
$$

对角输出读出为 $(xv)_iv_i$，非对角输出读出为 $(xv)_iv_j+(xv)_jv_i$，没有另乘二或把坐标替换为迹坐标。

有限矩阵使用以下实际有理角与演员。对非零整数四向量 $a,b$ 及每个坐标非零的整数三向量 $u$，令

$$
\begin{gathered}
H(a)=I-2aa^{\mathsf T}/(a^{\mathsf T}a),\quad U=H(a)H(b),\quad
\Lambda=\operatorname{diag}(1,2,3),\quad C_{ij}=2/(i+j+2)\ (0\le i,j<3),\\
X=\operatorname{diagblock}(\operatorname{diag}(u)C\operatorname{diag}(u),0),\qquad
x=UXU^{\mathsf T},\quad c=U\operatorname{diag}(1,2,3,0)U^{\mathsf T}.
\end{gathered}
\tag{59.4}
$$

$U\in O(4)$、$x=PxP$，且

$$
c\circ x=ww^{\mathsf T},\qquad w=U\begin{pmatrix}u\\0\end{pmatrix}.
\tag{59.5}
$$

置 $w_1=(u_2,-u_1,0,0)^{\mathsf T}$、$w_2=(u_3,0,-u_1,0)^{\mathsf T}$，选核向量

$$
v=Uv_0,\qquad v_0\in\{w_1,w_2,w_1+w_2,w_1+e_4,w_2+e_4\}.
\tag{59.6}
$$

后三种保留交叉极化，尤其含 $e_4$ 的两种没有删除完整输出的混合块。

取 [trureturing-experiments，commit `6d0281133e817e63ef8de3f2fbe647818c1f1cb5`，real 的有限参数表](https://github.com/the-omega-institute/trureturing-experiments/blob/6d0281133e817e63ef8de3f2fbe647818c1f1cb5/experiments/auric-uncalibrated-complex-real-pb/real/kernel_certificate.json) 中 `tests` 的 90 个整数 $(a,b,u)$ 与 `selected_rows` 的 450 个零起始 $(test,selector)$，按给定顺序将 (59.3) 组成方阵 $A_{\mathbb R}$；列依次为 $a<b$ 的字典序与全部十个输出坐标。其约化矩阵逐行紧凑 JSON 的 SHA256 为 `1eb2e5adb48b060d5c67d8fdad589266034c6d67016f359a85841053f66804d2`。全部参数的有理重建满足 (59.4)–(59.6)，所有行分母均与素数 $1000003$ 互素，而且精确消元给

$$
\det\overline {A_{\mathbb R}}=123800\pmod{1000003}\ne0.
\tag{59.7}
$$

该数同时由有限域矩阵消元和独立的逐元素标量消元得到。因模约化是这些分母局部化环上的同态，有理行列式非零，继而实行列式非零。于是 (59.3) 强迫全部 450 个系数为零，包括任意无理系数；反向 $D=0$ 显然满足 (59.1)。这是必要线性约束的有限单射证书，没有从有限 PB 样本外推全称 PB。

实情形不能直接照搬 (57.5) 的复双次数消元：此时 $u_jF_j$ 是三次实多项式，同时被三个 $u_j$ 整除仍可留下 $\gamma u_1u_2u_3$。上述全系数方阵用多个实际角消去包括这一项在内的全部自由度；无需把实斜矩阵当作 Hermitian 矩阵对角化，也未预先删掉中心或标量输入。

最后在实际合法元组

$$
U=I,\qquad q=(1,1/10),\qquad x=100E_{11},\qquad
v=(1/10,0,0,1)^{\mathsf T},\qquad\phi_v(A)=v^{\mathsf T}Av
\tag{59.8}
$$

上检验唯一候选 $D=0$。质量为 $101/100$，两腿均非零，完整乘法给

$$
\begin{aligned}
\phi_v(L)&=-10,\\
R_\delta v&=(10-\delta/2,-\delta/10,0,-\delta/20)^{\mathsf T},\\
S_\delta v&=(1+10\delta,1/10,0,1/10)^{\mathsf T},\\
(R_\delta v\wedge S_\delta v)_{12,14,24}
&=(2+\delta/20,3/2,-\delta/200).
\end{aligned}
\tag{59.9}
$$

其余外积坐标为零。因此同一泛函、同一元组的两笔预算为

$$
B_+=258101/40000,\qquad B_-=242101/40000,\qquad
\sqrt{B_+}+\sqrt{B_-}\le\frac{\sqrt{250101}}{100}<10=|\phi_v(L)|.
\tag{59.10}
$$

最后一式因 $250101<1000000$ 严格成立。由此无一个 $D$ 满足全称实 PB。∎

**定义 59.3（障碍的精确适用域）。** 定理 59.2 只排除完整 $\operatorname{Sym}_4(\mathbb R)$、全 $O(4)$、域自然实 $q$、完整实正泛函以及同一任意实双线性交替响应的 (56.1)–(56.2) 接口。它不排除全部实量子理论、带额外相位参考的实化、全部 EJA、低秩、无限维或不同输出合同。复空间的实化会改变载体、允许操作与相位参考，不能用它冒充定义 59.1 的同一四维模型。该无解结论也不是原共同来源全合同的反模型。

## 60. 未标定分类的共同源消费者与保谱几何

**定义 60.1（同一原响应与完整七矩的条件连接）。** 对每份固定的 (56.1) 未标定元组，仍取 §51 的七矩

$$
m_D(\phi)=\bigl(\phi(L),\phi(R_+^2),\phi(S_+^2),\phi(R_+\circ S_+),
\phi(R_-^2),\phi(S_-^2),\phi(R_-\circ S_-)\bigr).
\tag{60.1}
$$

这里 $h=D(c,x)$ 与 $g=D(c,t)$ 必须共同代入；不能沿用一个已标定 $h$ 的旧标签而只替换 $g$。若同一实际来源、同一完整忠实表示 $j$ 和同一旧 native $D$ 供应全部实际有向角、原合法 $q,x$、准备／效果及保留分支正泛函族 $\mathcal T_\Omega$，其原 PB 在同一分支的全部七矩上成立，并且逐元组有

$$
m_D((M_4(\mathbb C))_+^*)\subseteq
\overline{\operatorname{cone}(m_D(\mathcal T_\Omega))},
\tag{60.2}
$$

则 §51 的同元组闭凸锥运输直接给完整正泛函 PB，定理 56.2 因而识别两份标签中的同一个旧 $D$ 为 (56.3)。较强的全正泛函锥覆盖也是充分条件。七矩的两份 $2\times2$ 实 Gram 正矩阵、行列式平方根的连续性／正齐次／超可加性完全复用 §51；这一步不需要 $h$ 已标定，也不另立一般锥运输定理。对定义 59.1 的实接口，若实际源满足同样完整供应与实七矩覆盖，则会与 59.2 矛盾。

覆盖只是充分的来源条件，不断言为 PB 的必要条件，不声称七坐标最少。非选择性和选择性读数仍准确为

$$
p(w,e)=\omega(U_w^*eU_w),\qquad
\phi_{w,e}(A)=\omega(V_w^*\Pi_ej(A)\Pi_eV_w).
\tag{60.3}
$$

不要求 $\omega$ 对每个门不变。全部矩须由同一分支忠实读取，不能拼接不同准备的边缘最优值；完整输出上的正性也不能用局部演员正性代替。数学 $q\to0$ 仅延拓不等式，矩阵酉门的存在仅属给定模型，均不创造原来源实际可用的准备、门字或选择。§52 的非迹混合轨道与七矩分离已说明线性信息完备、满支撑、共同根纯性及全局循环性本身不供应 (60.2)，此处直接复用其反控制及原边界。

**定义 60.2（比较端的已付关系与尚缺的识别）。** [双侧正重置卷 V，§§74–75，固定版本 `5555e728`](https://github.com/the-omega-institute/trureturing/blob/5555e728b62ed8a7c5aea520bd396cf2c11b08d4/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md) 的 75.4 在同一 $\mathrm{PRE}_0$ 数据上，将两层原全正交条件等价地换成 Jordan 生成的完整框架族上的两份有限正交表；至多三套完整生成框架足够。此处仍保留完整有限混合律 $S$ 及其条件 EJA 桥、$L,p$ 对整个实际锥的正性、两次同一 $p$、两条实张成及全部实方向 $Z$。原混态 H13 单独供应相对取向；75.6 的删除控制与 75.7 的正权重、原归一化和操作预算前件也都保留。

上述三套是完整生成框架，不是三个标量测试或物理三空间；其有限零表不供应 (56.2) 的全部非线性 PB、(60.2) 的正测试覆盖、实际准备或旧 native $D$ 的身份。PRE 的双系统载体 $D_{\rm PRE}$ 不等于这里的响应映射 $D$，其规范参考 $\omega_{\rm PRE}=1_{D_{\rm PRE}}/m$ 不自动等于原物理整体态。若比较端及 PB 端确实由同一原源实现，仍须给出对象、原态、准备／效果、两份响应和完整输出的忠实对应，不能因共享“联合纯／局部混”或“共同态”的名称就识别它们。

**定义 60.3（分类响应的保谱数学流）。** 在已给定的复矩阵模型中，56.2 的结论使每个固定 Hermitian $a$ 的线性算子 $D_a:b\mapsto D(a,b)$ 成为通常内导子，而不是把导子性加入 PB 前件。复用内导子指数的标准恒等式，得到

$$
e^{sD_a}(b)=e^{\sigma isa/2}\,b\,e^{-\sigma isa/2},\qquad s\in\mathbb R.
\tag{60.4}
$$

因此这一数学可逆流保留 $b$ 的全部特征值、多项式谱不变量和算子谱；若对密度矩阵使用同一酉共轭，也保留其谱及由谱定义的熵。这给“信息保持”直觉一个精确的条件消费者：保留的是所述数学流的谱数据，不是所有原记录、全部实际过程或固定态的所有期望都不变。式 (60.4) 不把参数 $s$ 认作物理时间，不指定能量或 $\hbar$，不保证这些酉矩阵是实际合法门，也不要求 $\omega\circ\operatorname{Ad}_{U}=\omega$。在一般 Jordan 框架中由动力学对应恢复复乘积的标准接口仍有自己的序导子与括号前提，不能倒灌成此处未付的来源事实。

**定义 60.4（推导的文献边界）。** §§56–59 的 `repo-derived` 承重内容是：同一未标定 $D$ 的全核压缩如何约束完整 1920 维复系数空间、再由原 PB 逐项消去 $\ell,\eta$ 和非标量 $H$、用有限严格元组固定整体强度，以及实接口全部 450 个系数的精确零核与有限无解见证。§§48–55 的标定响应、旁观补全、同一七矩运输与混合轨道分离按各自原条件复用，不计为新的未标定分类。Gram／Cauchy–Schwarz、Cauchy 矩阵、谱分解、极化、外幂、Householder 及模素数非零子式提升均是成熟中间工具；(60.4) 也是标准内导子结果，不另列新定理。

相关原始文献的前提对应如下，均只作推导内的边界比较：Alaminos–Brešar–Extremera–Villena，[*On bilinear maps determined by rank one idempotents*，Theorem 2.2](https://users.fmf.uni-lj.si/bresar/documents/bilmapsid.pdf)，在全矩阵域假设对每对正交秩一幂等元响应为零，推出 $\Phi_1(ab)+\Phi_2(ba)$；这里由 PB 首先得到的是 (57.1)，不是该文的零乘积前提，故未据它跳过 57.2–58.1。de Seguins Pazzis，[*Range-compatible homomorphisms on spaces of symmetric or alternating matrices*，arXiv:1506.07203v2，Theorem 1.5、Corollary 1.6](https://arxiv.org/pdf/1506.07203v2)，对余维至多 $n-2$ 的对称矩阵子空间上满足 $F(A)\in\operatorname{im}A$ 的线性向量映射给固定向量的局部表示；本题首先出现的是 $XF(c,X)\in\operatorname{im}(c\circ X)$，对象与像空间不同，不能直接替代全核消元。

Alfsen–Shultz，[*Orientation in operator algebras*，Theorem 1](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，[DOI 10.1073/pnas.95.12.6596](https://doi.org/10.1073/pnas.95.12.6596)，在含单位 JB 代数上使用线性指定的斜序导子、$\psi_a(a)=0$ 及 $[\psi_a,\psi_b]=-[L_a,L_b]$ 来刻画相容复乘积；这里从原 PB 推出给定矩阵模型中的内导子，没有假设那套动力学对应，也未从它推出实际物理时间。Barnum–Wilce，[*Local tomography and the Jordan structure of quantum theory*，arXiv:1202.4513v2，Proposition 1](https://arxiv.org/pdf/1202.4513v2)，要求可因子分解的齐性自对偶理论、每对系统在理论内有局部层析复合及一个 qubit；其复型分类不等于 59.2 的单个实四维 raw 接口障碍。上述有界原文比较未找到可直接按同一前提调用的本 raw PB 分类；这不构成穷尽文献或历史首创性主张。

**开放问题 60.5（原目标仍需的来源桥）。** 在定义 55.1、§51 及其递归上游全部原合同内，尚须从原共同 $\Omega$ 的实际合法门字／保留分支识别两份标签中的同一个旧 native $D$，取得所需实际有向角、全部原合法 $q,x$、完整输出的七矩和足够正测试，并证明 (60.2) 或另一足够的忠实来源条件。模型内的实双线性前提不能替代原源双线性的取得；[C128 的原词标定与固定关系](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 中已付的双线性条件桥及其同一旧响应条件仍按全文保留。[RRO 原入口与实际 Plan／Return，§23](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md#23-an-acquired-pending-operand-fibre-at-the-original-plan-entry) 及其[原始 acquired-input 资格](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md) 若被用作上游，同样须保持实际取得、operative Plan 和 Return 的操作资格；较强 P2／嵌套前件不自动供应这里的量子矩阵接口。

本问题完整保留同一旧 $\Omega,E,C,u,N,\mathcal P,S,D,q,K/J$、原准备与接受、参考／副本及真正相关联合，全部中央／经典／不等维／静默／无轴块，失败、零／不等／次归一质量、parent／ready／flags、全部切口与完整菜单／固定支持全质量、完整环境／活动输出与细记录、port／post-port、拒绝／停止／销毁／泄漏、真遗忘、全部历史及每份完整输出的每个旧合法未来、两侧／逆向 Return、原精确 $B$ 与闭 $B_{\rm cl}$、未定义请求、物理钟／控制／单位、同一 $\sigma,t_0$、固定域／resolvent 及 $3s+r\le1$。四维完整输出、五维第三格和物理三空间保持不同。Hilbert／复结构、Born、张量、过程／CP-Kraus／TP-更新-Lüders 及物理动力学的来源仍是原目标的真实义务；已有条件消费者只按其全文前件使用。本批是上述精确接口内的纸面数学，不宣称 Lean／kernel 认证、实际源已实现或完整量子起源已完成。

## 追加锚（本行以下为增补区）
