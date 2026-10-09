# 算术全息量子网络与 Ryu–Takayanagi 研究

本卷以同一个目标组织全部结果：从已有算术窗口和量子编码出发，证明独立定义的边界纠缠熵与几何割之间的关系，并确定这些有限模型能否组成相容的跨尺度量子系统。推理链为：局部完美张量 → 实际纠缠谱 → 单环 RT 与算术亏损 → 熵未记录的多副本结构 → 粗化障碍及可实现的联合操作 → 整个单环的精度通道与局部验证。公开矩阵和随机网络问题用来检验这些接口的迁移能力。

**证明状态。** 本卷新增结论为有限维纸面数学证明及明确标出的计算证书，尚无配套 Lean 内核证明或独立评审。既有形式化、已发表结果、本卷推导和未证接口分别说明。未认领原始引力 RT、物理 AdS/CFT 对偶、完整具名开放问题结算或首次优先权。具体构造的新颖性仍需进一步核对。

## 1. 统一对象与仓库接口

所有对数取自然对数。$S(\rho)=-\operatorname{Tr}(\rho\log\rho)$，零本征值按连续延拓处理。$R_d=\mathbb Z/d\mathbb Z$，通常 $d\ge3$ 为奇数，$\omega_d=e^{2\pi i/d}$。循环环 $\mathbb Z/p^n\mathbb Z$ 与有限域 $\mathbb F_{p^n}$ 始终区分。$\operatorname{Ad}_U(\rho)=U\rho U^*$。

图的内部顶点四价，悬空腿视为接到独立边界顶点的边，每条边承载 $\mathbb C^d$。对边界子集 $C$，$m(C)$ 是在所有内部顶点的二侧分配中将 $C$ 与其补集分开的最少割边数，允许割断边界边。割容量 $m(C)\log d$ 先由图定义，独立于网络态。对四方纯态，AME$(4,d)$ 表示任意二方约化态均为 $I_{d^2}/d^2$；它也称四腿完美张量。

直接使用的既有仓库接口如下，均在提交 `280905f8378cd6ed5c3ba94076853d3814b139be` 已有：

- `D5/S3/Quantum/Entanglement/QutritThresholdSharing.lean`：三 qutrit 编码、单份最大混合与两份恢复。
- `D5/S3/Observer/WindowRegister.lean`、`D5/S3/Quantum/Algebra/WeylPhaseArithmetic.lean`：循环窗口、原始单位根和相位运算。
- `D5/S3/Fourier/FinitePoisson.lean`：有限字符正交性与湮灭子。
- `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.lean`：实际历史系数矩阵、秩和 Schmidt 权重。

[情境时空算术量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) 提供量子记录和相干历史语境；[QUANTUM-RH](QUANTUM-RH.md) 评注 29.4 提供 M2 相容读数与算术全息接口。本卷后续定理尚未由这些 Lean 文件证明。边界重建、谱平坦性、几何面积和跨尺度操作分别承担证明义务。

## 2. 一个局部张量族

**定义 2.1。** 对奇数阶有限交换群 $G$，令

$$
|T_G\rangle=|G|^{-1}\sum_{x,y\in G}|x,y,x+y,x+2y\rangle.
$$

$G=R_d$ 时记为 $T_d$。

## proposition 2.2: 局部完美性和乘积群

$T_G$ 是 AME$(4,|G|)$，任意单方约化态为 $I_{|G|}/|G|$；按参与方重组时，$T_{G\times H}=T_G\otimes T_H$。

**证明。** 乘以 $2$ 是奇数阶群的自同构。四个线性形式 $x,y,x+y,x+2y$ 中任取两个，其系数行列式为 $\pm1$ 或 $\pm2$，因此任意二腿坐标映射都是双射。二对二偏迹消去所有交叉项，得到 $|G|^2$ 个相等对角项；进一步偏迹给出单腿结论。乘积群的求和与坐标逐分量分离。张量视为从至多两腿到其余腿的映射时，乘以适当正常数即为等距。证毕。

仓库编码

$$
V|s\rangle=3^{-1/2}\sum_j|j,j+s,j+2s\rangle
$$

的 Choi 态交换前两腿即为 $T_3$。这是后续网络与已有量子编码的实际对象对应。

## 3. 有限交换群二次历史态的完整谱

## theorem 3.1: 核、双字符与谱

设 $V,X,Y$ 为有限交换群，群同态 $A:V\to X$、$B:V\to Y$ 的联合映射单射。设 $q:V\to U(1)$、$q(0)=1$，且

$$
\beta(u,v)=q(u+v)/[q(u)q(v)]
$$

为双字符。定义

$$
|\psi\rangle=|V|^{-1/2}\sum_{v\in V}q(v)|Av\rangle|Bv\rangle,
\quad K_A=\ker A,\quad K_B=\ker B,
$$

$$
R_B=\{b\in K_B:\beta(a,b)=1\text{ 对所有 }a\in K_A\}.
$$

约化态的非零谱平坦，秩为

$$
r=\frac{|V|}{|K_A||R_B|}
=\frac{|V|}{|K_A||K_B|}
\left|\operatorname{im}\bigl(K_B\to\widehat{K_A},\ b\mapsto\beta(\cdot,b)\bigr)\right|.
$$

因此 $S(\rho_X)=\log r$，所有正阶 Rényi 熵也等于 $\log r$。不要求核为自由模或短正合列分裂。

**证明。** $K_A\cap K_B=0$。将 $V$ 按 $K_A+K_B$ 的陪集分块。不同陪集在两侧局部空间分别正交：例如 $A(v_0)+A(K_B)$ 与 $A(v_1)+A(K_B)$ 相交便推出 $v_0-v_1\in K_A+K_B$。每块唯一写成 $v_0+a+b$，并有

$$
q(v_0+a+b)=q(v_0)q(a)q(b)\beta(v_0,a)\beta(v_0,b)\beta(a,b).
$$

去除分别依赖 $a,b$ 的局部对角相位后，归一化系数矩阵是

$$
M_{a,b}=\beta(a,b)/\sqrt{|K_A||K_B|}.
$$

$A|_{K_B}$、$B|_{K_A}$ 单射，故这些是原态的正交局部基。字符正交性给出

$$
(M^*M)_{b,b'}=|K_B|^{-1}\mathbf1_{b'-b\in R_B}.
$$

按 $K_B/R_B$ 分块，非零本征值为 $|R_B|/|K_B|$，数量为 $|K_B|/|R_B|$。全态有 $N=|V|/(|K_A||K_B|)$ 个等权正交陪集块，得到所述秩和本征值 $1/r$。证毕。

稳定子平坦谱和模算术已有 [Stabilizer]、[ModularClifford] 基础；此处使用实际系数矩阵证明，避免把合数模环的核当作域上线性空间。

## 4. 普通闭环与相位缝合的算术亏损

取 $L\ge3$ 个顶点组成简单环，每个顶点使用 $T_d$。顶点 $i$ 的两条内部腿为 $x_i,x_{i+1}$，外部腿为

$$
a_i=x_i+x_{i+1},\qquad b_i=x_i+2x_{i+1}.
$$

## theorem 4.1: 普通奇环

普通缝合 $x_L=x_0$ 的归一化态为

$$
|\Psi^{\mathrm{id}}_{d,L}\rangle=d^{-L/2}\sum_{x\in R_d^L}
|(I+P)x\rangle_A|(I+2P)x\rangle_B,
\quad(Px)_i=x_{i+1}.
$$

若 $L$ 为奇数，则

$$
S(\rho_A)=L\log d-\log\gcd(d,2^L+1).
$$

非零谱平坦，秩为 $d^L/\gcd(d,2^L+1)$，而 $m(A)=L$。

**证明。** 联合输出单射，因为 $b-a=Px$。奇数 $L$ 时 $\det(I+P)=2$，故 $I+P$ 可逆；偏迹后的 $B$ 态是 $I+2P$ 的均匀像分布。核满足 $x_{i+1}=-2^{-1}x_i$ 及

$$
(2^L+1)x_0=0\pmod d.
$$

核有 $g=\gcd(d,2^L+1)$ 个元素，每个像点有 $g$ 个原像，给出谱。每个顶点各接一个 $A$ 叶和一个 $B$ 叶，任意分配至少割一条边界边，全部内部顶点同侧达到 $L$。证毕。

对 $d=3^n$，亏损是 $\min(n,v_3(2^L+1))\log3$；特别是 $L=3$ 时，熵为 $[3n-\min(n,2)]\log3$。局部完美性不足以排除闭环约束；这不是已建立物理对偶的 RT 反例。

**定义 4.2（单边相位缝合）。** 用幺正矩阵

$$
U_\alpha(u,v)=d^{-1/2}\omega_d^{uv+\alpha v^2},\qquad\alpha\in R_d,
$$

替代一条内部边的指标相等收缩。它是 Fourier 矩阵与对角二次相位的乘积，保持连接维数和最大纠缠性。精确归一化态为

$$
|\Psi^\alpha_{d,L}\rangle=d^{-(L+1)/2}
\sum_{x_0,\ldots,x_L\in R_d}\omega_d^{x_0x_L+\alpha x_0^2}
\bigotimes_{i=0}^{L-1}|x_i+x_{i+1}\rangle_{a_i}|x_i+2x_{i+1}\rangle_{b_i}.
$$

路径到全部输出单射。这里 $\Psi^{\mathrm{id}}$ 与 $\Psi^{\alpha=0}$ 不同，后者仍有 Fourier 缝合。未在邻接张量实施补偿，因此该相位操作改变全局态，并非内部基换名。

## theorem 4.3: 精确相位亏损与全区域判据

令

$$
c_k=2\alpha+(-1)^L(2^{-k}+2^{-(L-k)})\in R_d,\quad0\le k\le L.
$$

若区域 $C$ 在每个顶点恰选一腿，其中 $k$ 条是 $b_i$，则

$$
S(\rho_C)=L\log d-\log\gcd(d,c_k),\qquad
r_C=d^L/\gcd(d,c_k).
$$

最大公因子与整数代表元无关。$\Psi^\alpha_{d,L}$ 对所有边界子集满足 $S(\rho_C)=m(C)\log d$，当且仅当所有 $c_k$ 都为单位。

**证明。** 对上述分腿区域，选腿系数 $w_i\in\{1,2\}$，补集系数 $\bar w_i=3-w_i$。固定 $C$ 输出后，$x_{i+1}=w_i^{-1}(c_i-x_i)$ 只留下 $z=x_0$，并有

$$
x_L=s_Cz+f(c),\qquad s_C=(-1)^L(\prod_iw_i)^{-1}.
$$

保持补集输出不变的差路径由 $t=\delta x_0$ 唯一参数化，$\delta x_L=s_{\bar C}t$。给定两组 $C$ 输出，$t$ 若存在则唯一，因为 $\delta c_0=(w_0-\bar w_0)\delta x_1$ 的系数为单位。相位 $Q(x)=x_0x_L+\alpha x_0^2$ 的差中依赖 $z$ 的部分是

$$
(2\alpha+s_C+s_{\bar C})tz=c_ktz.
$$

两侧核均有 $d$ 个元素、交为零，限制双字符为 $\omega_d^{c_kzt}$，右根基大小为 $\gcd(d,c_k)$。定理 3.1 得完整谱。等价地，交叉项含有 $\sum_z\omega_d^{c_ktz}$；单位时非零 $t$ 全消失，非单位时存在不同输出间绝对值为 $d^{-L}$ 的交叉项。该类区域最小割为 $L$，所以单位条件必要。

任意 $q$ 边割给出秩上界 $d^q$，故所有区域都有 $S(\rho_C)\le m(C)\log d$。其余区域有一个环顶点的两条外腿同侧，将其按命题 2.2 等距吸收到该侧，未吸收图成为森林。森林叶顶点至多连接一个未吸收邻居，至少三腿已被两侧标记，其中至少两腿同侧；继续等距吸收直到结束。单腿上的 $U_\alpha$ 可并入张量而不改变完美性。最终两侧等距映射之间是 $q$ 对最大纠缠连接，既给出实际割又给出 Schmidt 分解。$S=q\log d$、$m(C)\le q$ 与全局上界合起来给出 $q=m(C)$。证毕。

## corollary 4.4: 精度斜率

固定奇素数 $p,L$、整数 $\alpha,k$，把 $c_k$ 视为 $\mathbb Z_p$ 元素，$\nu=v_p(c_k)$，$v_p(0)=\infty$。则

$$
S_n(C)=[Ln-\min(n,\nu)]\log p.
$$

$c_k\ne0$ 时，$n\ge\nu$ 后绝对亏损稳定为 $\nu\log p$，且 $S_n(C)/(n\log p)\to L$；$c_k=0$ 时 $S_n(C)=(L-1)n\log p$。这是谱计数的精度渐近；与态和通道的精度相容关系在第 12 节另行构造。

## 5. 所有奇数维数的全区域 RT 构造

## lemma 5.1: 非剩余证书及其计数

对奇素数 $p$，令 $a=2^{-L}\in\mathbb F_p^\times$。若 $\chi_p(\alpha^2-a)=-1$，则所有 $c_k\ne0\pmod p$。这样的 $\alpha$ 恰有 $(p-\chi_p(a))/2>0$ 个。

**证明。** 若 $c_k=0$，令 $x=2^{-k}$、$t=-2(-1)^L\alpha$，则 $x+a/x=t$。多项式 $X^2-tX+a$ 有根，但判别式 $4(\alpha^2-a)$ 是非平方，矛盾。计数方面，$y^2=x^2-a$ 等价于 $(x-y)(x+y)=a$，共有 $p-1$ 对解，故 $\sum_x\chi_p(x^2-a)=-1$。零点数 $N_0=1+\chi_p(a)$，结合 $N_++N_-+N_0=p$、$N_+-N_-=-1$ 得 $N_-=(p-\chi_p(a))/2$。证毕。非剩余证书是充分条件，未声称它对有限的 $k$ 集合也必要。

## theorem 5.2: 全奇数维数

对任意奇数 $d\ge3$、$L\ge3$，存在一个与边界区域无关的 $\alpha\in R_d$，使 $\Psi^\alpha_{d,L}$ 对全部 $C$ 同时满足

$$
S(\rho_C)=m(C)\log d.
$$

对固定 $p,L$，一个整数 $\alpha$ 可同时用于全部 $d=p^n$。

**证明。** 对每个 $p\mid d$ 用引理 5.1 选 $\alpha_p$，再用 CRT 取 $\alpha\equiv\alpha_p\pmod p$。所有 $c_k$ 不被任何 $p\mid d$ 整除，故在 $R_d$ 中为单位，应用定理 4.3。固定 $p,L$ 时任一整数提升在所有 $p^n$ 中仍满足同一单位判据。证毕。

## corollary 5.3: 三进显式规则

$d=3^n$ 时可取 $L$ 奇数用 $\alpha=1$、$L$ 偶数用 $\alpha=0$。因为模 $3$ 时 $2^{-1}=-1$，奇环的 $c_k=2$，偶环的 $c_k=2(-1)^k$，均为单位。

## corollary 5.4: 附树单环

在环的外部腿上接任意有限树，所有内部顶点仍四价且使用 $T_d$，悬空腿全部作为边界。环顶点保留指定的环内腿，树上腿排列任意固定；保留上述单边缝合，则整个装饰图对全部区域仍满足同一 RT 等式。

**证明。** 从附加树的外叶向内等距吸收。环若被打断，余下按森林处理；若保留完整环，两条已标记外腿同侧时仍可打断，否则核心就是定理 4.3 的逐顶点分腿情形。已分离的最大纠缠连接和两侧等距映射同时保留实际割及 Schmidt 分解。证毕。范围限定一个简单环，$L\ge3$，不含自环、双边环或任意多环图。

## 6. 双侧保留算术余数的尖锐粗化障碍

固定奇素数 $p$、$n\ge1$、$d=p^n$、$D=pd$ 和整数 $\alpha$。缝合连接态为

$$
|\Omega_{D,\alpha}\rangle=D^{-1}\sum_{x,y\in R_D}
 e^{2\pi i(xy+\alpha x^2)/D}|x,y\rangle.
$$

设局部 CPTP 通道 $\Phi_A,\Phi_B:M_D\to M_d$ 对每个计算基态均满足

$$
\Phi_j(|x\rangle\langle x|)=|x\bmod d\rangle\langle x\bmod d|.
$$

不使用通信或额外共享纠缠，输出 $\rho=(\Phi_A\otimes\Phi_B)(|\Omega\rangle\langle\Omega|)$。

## theorem 6.1: 最小输出熵

对每个归一化纯态 $\varphi$，

$$
\lambda_{\max}(\rho)\le p^{-1},\qquad S(\rho)\ge\log p,
\qquad\langle\varphi|\rho|\varphi\rangle\le p^{-1}.
$$

对每个 $p,n,\alpha$ 都有合法通道达到秩 $p$ 的平坦谱，故最大本征值和熵界同时尖锐。

**证明。** 写 $x=a+db,y=c+de$。计算基输出纯性使局部 Stinespring 等距具有形式

$$
V_A|a+db\rangle=|a\rangle|e_{a,b}\rangle,\qquad
V_B|c+de\rangle=|c\rangle|f_{c,e}\rangle.
$$

固定 $a$ 或 $c$ 时环境向量正交归一，不限制不同低位的环境标架。因为 $p\mid d$，

$$
\frac{xy+\alpha x^2}{D}
=\frac{ac+\alpha a^2}{D}+\frac{(c+2\alpha a)b+ae}{p}\pmod{\mathbb Z}.
$$

定义正交 Fourier 标架

$$
\nu_{a,t}=p^{-1/2}\sum_b\omega_p^{tb}e_{a,b},\qquad
\mu_{c,s}=p^{-1/2}\sum_e\omega_p^{se}f_{c,e}.
$$

输出纯化为 $d^{-1}\sum_{a,c}e^{2\pi i(ac+\alpha a^2)/D}|a,c\rangle|\nu_{a,c+2\alpha a}\rangle|\mu_{c,a}\rangle$，环境指标模 $p$。环境约化态是

$$
\tau=d^{-2}\sum_{a,c}|\nu_{a,c+2\alpha a}\rangle\langle\nu_{a,c+2\alpha a}|
\otimes|\mu_{c,a}\rangle\langle\mu_{c,a}|.
$$

固定 $a$，按 $t=c+2\alpha a\pmod p$ 分组，每组 $d/p$ 项，得到

$$
\tau=d^{-1}\sum_a\tau_a,\qquad
\tau_a=p^{-1}\sum_t|\nu_{a,t}\rangle\langle\nu_{a,t}|\otimes\sigma_{a,t},
$$

其中 $\sigma_{a,t}$ 为密度矩阵。因此 $\tau_a\le I/p$、$\tau\le I/p$。互补边缘 $\rho,\tau$ 非零谱相同，推出三个界。

为达到等号，取 $p$ 维环境并指定 $\nu_{a,t}=|t-(2\alpha+1)a\rangle$、$\mu_{c,s}=|c-s\rangle$，逆 Fourier 变换给出合法环境标架。条件环境向量变成 $|c-a\rangle\otimes|c-a\rangle$，其标签均匀分布，故恰有 $p$ 个本征值 $1/p$。证毕。

## corollary 6.2: 普通高位偏迹

若两侧使用 $W|a+db\rangle=|a\rangle|b\rangle$ 后丢弃高位，则输出有 $p^2$ 个本征值 $p^{-2}$，$S=2\log p$、$\operatorname{Tr}\rho^2=p^{-2}$。

**证明。** 环境标架取标准基后，仅依赖 $(c+2\alpha a,a)\pmod p$；该线性变换可逆，$p^2$ 个正交向量等权出现。特别地 $D=9,d=3$ 时输出为 $I_9/9$。证毕。

这只排除双侧普通余数读出的局部纯态粗化，其他读出或联合操作由后续构造分别处理。

## 7. 单条连接的互补读出通道塔

对 $d\mid D$，定义数字粗化

$$
Q_{D,d}(|a+db\rangle\langle a'+db'|)=\delta_{b,b'}|a\rangle\langle a'|.
$$

令 $F_d$ 为正指数归一化 Fourier 矩阵，$D_{d,\alpha}=\operatorname{diag}(\omega_d^{\alpha x^2})$，并定义

$$
\mathcal C^Z_{D,d}=\operatorname{Ad}_{D_{d,\alpha}}\circ Q_{D,d}\circ\operatorname{Ad}_{D_{D,\alpha}^*},\qquad
\mathcal C^F_{D,d}=\operatorname{Ad}_{F_d}\circ Q_{D,d}\circ\operatorname{Ad}_{F_D^*}.
$$

## theorem 7.1: 互补读出通道塔

两族通道 CPTP、满射且非恒定，对 $e\mid d\mid D$ 在全部输入矩阵上严格满足 $\mathcal C^j_{d,e}\mathcal C^j_{D,d}=\mathcal C^j_{D,e}$。此外

$$
(\mathcal C^Z_{D,d}\otimes\mathcal C^F_{D,d})(|\Omega_{D,\alpha}\rangle\langle\Omega_{D,\alpha}|)
=|\Omega_{d,\alpha}\rangle\langle\Omega_{d,\alpha}|.
$$

**证明。** $Q$ 是数字分解后的偏迹。写 $x=a+eb+dc$，先丢弃 $c$ 再丢弃 $b$ 等价于丢弃 $b+(d/e)c$，故 $Q$ 复合律在矩阵单位上成立，中间共轭相消给出两族复合律。由

$$
|\Omega_{D,\alpha}\rangle=(D_{D,\alpha}\otimes F_D)|\Phi_D\rangle,
\qquad |\Phi_D\rangle=D^{-1/2}\sum_x|x,x\rangle,
$$

两侧数字分解把 $\Phi_D$ 化为 $\Phi_d\otimes\Phi_{D/d}$，偏迹后施加低维共轭即得。任意 $\sigma$ 可由输入 $W^*(\sigma\otimes|0\rangle\langle0|)W$ 送到，故满射。证毕。

$\mathcal C^Z$ 保留计算基余数，$\mathcal C^F$ 保留 Fourier 读出中的数字。例如 $\mathcal C^F_{9,3}(|3\rangle\langle3|)=|1\rangle\langle1|$，不满足普通余数条件。独立腿上的相容性受第 9 节约束；第 12 节构造允许块内及缝合邻块操作的全网络通道。

## 8. 二分谱之外的四副本算术不变量

取副本置换像数组

$$
\sigma_1=(0,1,2,3),\quad\sigma_2=(1,0,3,2),\quad
\sigma_3=(2,3,1,0),\quad\sigma_4=(3,2,0,1).
$$

**定义 8.1。** 对归一化四方态，令

$$
I(\psi)=\sum_{(z_{\ell,i})}\prod_{i=0}^3
\psi_{z_{1,i},z_{2,i},z_{3,i},z_{4,i}}
\overline{\psi_{z_{1,\sigma_1(i)},z_{2,\sigma_2(i)},z_{3,\sigma_3(i)},z_{4,\sigma_4(i)}}}.
$$

它等于四组局部副本置换的张量积 $W$ 对 $\rho^{\otimes4}$ 的迹。$W$ 与各 $U_\ell^{\otimes4}$ 交换，故任意四方局部幺正保持 $I$；按参与方重组的张量积满足 $I(\psi\otimes\varphi)=I(\psi)I(\varphi)$。复制不变量的方法背景见 [RRKL23]。

## theorem 8.2: 三挠求值

对 $G[3]=\{a\in G:3a=0\}$，

$$
I(T_G)=|G[3]|^2/|G|^6.
$$

**证明。** 四个 ket 副本用 $(x_i,y_i)$ 表示；前两腿匹配确定 bra 变量为 $(x_i,y_{\sigma_2(i)})$，余下约束为

$$
x_i+y_{\sigma_2(i)}=x_{\sigma_3(i)}+y_{\sigma_3(i)},\qquad
x_i+2y_{\sigma_2(i)}=x_{\sigma_4(i)}+2y_{\sigma_4(i)}.
$$

全部解唯一写为 $s,t\in G$、$a,c\in G[3]$，其中

$$
(x_0,x_1,x_2,x_3)=(s,s+c,s+2a+c,s+a),\quad
(y_0,y_1,y_2,y_3)=(t+a,t+2a+c,t,t+c).
$$

验证：取 $s=x_0,t=y_2,a=y_0-y_2,c=y_3-y_2,b=y_1-y_2$。第一类等式给出 $x_2=s+b,x_3=s+a,x_1=s+c$；第二类给出 $2b=a+2c,b=2a+c,b+2c=2a,a=c+2b$，等价于 $b=2a+c,3a=3c=0$。反向代入全部成立。解数为 $|G|^2|G[3]|^2$，每项有八个振幅 $|G|^{-1}$，得到公式。证毕。

## corollary 8.3: 相同熵、不同局部等价类

$T_9$ 与 $T_3\otimes T_3$ 不局部幺正等价，因为

$$
I(T_9)=3^{-10}=1/59049,\qquad I(T_3\otimes T_3)=3^{-8}=1/6561.
$$

两态都是 AME$(4,9)$，全部子系统谱相同：一方熵 $\log9$，两方熵 $2\log9$，三方非零谱由纯性决定。更一般地，$n\ge2$ 时 $T_{3^n}$ 与 $T_3\otimes T_{3^{n-1}}$ 不局部等价；未据此分类任意高维 AME 因子。

## corollary 8.4: 定量局部分离

对任意四方局部幺正 $U$，两态的迹距离至少 $1/59049$。

**证明。** $\|W\|_\infty=1$ 和张量积望远镜展开给出 $|I(\rho)-I(\tau)|\le4\|\rho-\tau\|_1$。不变量差为 $8/59049$，而迹距离为迹范数的一半。证毕。此界针对局部幺正分解，不是一般近似通道的误差界。

## 9. 顶点纯态粗化：独立操作障碍与联合进位修正

## lemma 9.1: 纯 AME 输出的因子化

设 $D=de$，$\psi$ 为 AME$(4,D)$，$\varphi$ 为 AME$(4,d)$。四个独立局部 CPTP 通道能够把 $\psi$ 精确变成纯态 $\varphi$，当且仅当 $\psi$ 局部幺正等价于按参与方重组的 $\varphi\otimes\eta$，其中 $\eta$ 为某个 AME$(4,e)$。

**证明。** 局部 Stinespring 等距 $V_i$ 给出纯化。纯输出迫使 $(\otimes_iV_i)|\psi\rangle=|\varphi\rangle\otimes|\eta\rangle$。单方约化态满足

$$
V_iV_i^*/D=(I_d/d)\otimes\eta_i.
$$

左侧为秩 $D$ 的归一化投影，故 $\eta_i$ 恰有 $e$ 个本征值 $1/e$。在其支撑内 $V_i$ 成为 $\mathbb C^D\simeq\mathbb C^d\otimes\mathbb C^e$ 的幺正。比较二方最大混合态，得到 $\eta_{ij}=I_{e^2}/e^2$。反向实施局部因子化再丢弃环境即得。证毕。

## theorem 9.2: 九维循环顶点障碍

不存在四个独立局部 CPTP 通道把 $T_9$ 精确变成任意 AME$(4,3)$ 纯态。

**证明。** [RRKL23] Theorem 1 已证明所有 AME$(4,3)$ 局部幺正等价。引理 9.1 因而迫使 $T_9$ 局部等价于 $T_3\otimes T_3$，与推论 8.3 矛盾。证毕。

此处不要求保留余数，也不限制 Fourier 或 Clifford 操作。局部辅助系统和丢弃均含在 CPTP 中。共享经典随机的乘积通道混合也不可能，因为纯输出的每个正权分支必须产生同一纯态。通信、自适应 LOCC、共享纠缠、联合门、混合或近似输出均不在排除范围。第 7 节单边通道塔不能仅靠四条腿独立粗化实现 $T_9\mapsto T_3$；这不是任意整体网络粗化的不存在定理。与 $T_3\otimes T_3$ 可直接丢弃一层相比，也证明全部二分谱不能决定粗化能力。

## theorem 9.3: 联合进位消除

取奇数 $d,e\ge3$、$D=de$。每条腿分解为 $W|a+db\rangle=|a\rangle_d|b\rangle_e$。写 $x=a+db,y=c+df$，并令

$$
r=(a+c)\bmod d,\quad s=(a+2c)\bmod d,\quad
\kappa_1=(a+c-r)/d,\quad\kappa_2=(a+2c-s)/d.
$$

$(r,s)$ 唯一确定 $a=(2r-s)\bmod d,c=(s-r)\bmod d$，故也确定两进位。在第三、第四参与方上取联合置换

$$
C_{d,e}:|r,k\rangle_3|s,h\rangle_4
\mapsto|r,k-\kappa_1(r,s)\rangle_3|s,h-\kappa_2(r,s)\rangle_4,
$$

高位减法取模 $e$。按低、高层重组后，

$$
C_{d,e}W^{\otimes4}|T_{de}\rangle=|T_d\rangle\otimes|T_e\rangle.
$$

**证明。** 两输出高位为 $b+f+\kappa_1,b+2f+\kappa_2$。保留低位并按其平移高位是可逆置换；去进位后低层为 $(a,c,a+c,a+2c)$，高层为 $(b,f,b+f,b+2f)$，振幅 $1/(de)$ 分离。证毕。

$d=e=3$ 时，这个跨两方联合门已足够跨过定理 9.2 的障碍，未声称最少基本门数或通信量。若 $\gcd(d,e)=1$，每方 CRT 基变换就能实现 $T_{de}\mapsto T_d\otimes T_e$，无须联合门；素数幂数字分解不满足该条件。

## 10. 随机修饰单环：精确纯度与谱非平坦性

[TPTN26] 第 5.1 节在完美张量每条腿上施加独立 Haar 幺正；内部相邻变换可以合并成每条边独立的 Haar 幺正。以下使用其单环实例，边界局部幺正不影响区域谱。每个顶点为归一化 AME$(4,d)$，每条环边用

$$
|U\rangle=(U\otimes I)|\Phi_d\rangle,\quad U\sim\mathrm{Haar}(U(d)),\quad
|\Phi_d\rangle=d^{-1/2}\sum_j|j,j\rangle
$$

收缩。记未归一化网络态 $V$、$Z=\langle V|V\rangle$，区域 $A$ 每顶点选一条外腿。

## theorem 10.1: 有限维精确二阶矩

逐个样本 $Z=d^{-2L}$，且

$$
\mathbb E\operatorname{Tr}(\rho_A^2)=2/d^L.
$$

**证明。** 对各顶点外腿偏迹留下环内两腿的 $I_{d^2}/d^2$，每条归一化边态迹为一，故 $Z$ 恒定。令 $F$ 为两副本交换。边的 Haar 二阶矩为

$$
\mathbb E[(|U\rangle\langle U|)^{\otimes2}]
=\frac{I\otimes I+F\otimes F-d^{-1}(I\otimes F+F\otimes I)}{d^2(d^2-1)}.
$$

两端交换子空间由 $I,F$ 张成，四个迹约束为 $1,1/d,1/d,1$，解线性方程即得系数。半边交换标号用 $0,1$，边和顶点矩阵分别为

$$
M=\begin{pmatrix}1&-d^{-1}\\-d^{-1}&1\end{pmatrix},\qquad
V_A=\begin{pmatrix}d^{-1}&d^{-2}\\d^{-2}&d^{-1}\end{pmatrix}.
$$

顶点条目来自选中 $1+s+t$ 条腿的 AME 纯度 $d^{-\min(1+s+t,3-s-t)}$。未归一化纯度分子 $N_A$ 满足

$$
\mathbb E N_A=[d^2(d^2-1)]^{-L}\operatorname{Tr}[(MV_A)^L],\qquad
MV_A=(d^2-1)d^{-3}I_2.
$$

所以 $\mathbb E N_A=2d^{-5L}$，除以常数 $Z^2=d^{-4L}$ 得结论。这里没有用期望之比代替随机比值。证毕。

## corollary 10.2: 明确谱尺度

对 $N=d^L$，

$$
\mathbb E[N\operatorname{Tr}(\rho_A-I_N/N)^2]=1,
$$

而未乘 $N$ 的均方距离为 $1/N$，趋于零。另有

$$
-\log\mathbb E\operatorname{Tr}\rho_A^2=L\log d-\log2,
$$

$$
L\log d-\log2\le\mathbb E S_2(\rho_A)\le\mathbb E S(\rho_A)\le L\log d.
$$

后式来自 Jensen 和 $S\ge S_2$。领先熵斜率与完整谱平坦性不同。该区域至少具有内部顶点全部归左或全部归右两个同容量最小割，不满足 [TPTN26] 第 5.2 节式 (5.23) 前的无领先简并条件。未从二阶平均值推出其他谱距离的概率极限。

## corollary 10.3: 几乎处处非平坦

奇数 $d$、所有顶点取 $T_d$ 时，内部 Haar 乘积测度下 $\rho_A$ 几乎处处满秩且非平坦。

**证明。** 定理 5.2 给出一个参数点使 $\rho_A=I_N/N$，故连通实解析流形 $U(d)^L$ 上的 $\det\rho_A$ 不恒为零。其零集测度为零。定理 10.1 又保证非负实解析函数 $\operatorname{Tr}\rho_A^2-1/N$ 不恒为零，其零集也为零测。两者合起来即得。未声称每个具体参数点都非平坦。证毕。

## proposition 10.4: 六 qutrit 的精确样本

取 $d=L=3$，两条内部边恒等，另一条为 $F_3\operatorname{diag}(1,1,-1)$。归一化态为

$$
|\Psi\rangle=\frac19\sum_{x_0,\ldots,x_3\in R_3}
\omega_3^{x_0x_3}g(x_0)\bigotimes_{i=0}^2|x_i+x_{i+1},x_i+2x_{i+1}\rangle,
\quad g=(1,1,-1).
$$

每顶点选第一输出的区域具有完整谱

$$
\{(1/81)^{\times9},(4/81)^{\times18}\}.
$$

**证明。** 两侧线性输出核各一维、交零，按核之和分为九个局部正交等权块。限制交叉双字符是 $L=3,k=0,\alpha=0$ 的 $c_0=0$。去掉局部相位后每块矩阵为 $H_{ab}=g(a+b+t)/3$，$t$ 只改变循环置换。$g$ 的未归一化 Fourier 模平方为 $1,4,4$，块内 Schmidt 权重为 $1/9,4/9,4/9$，乘块权 $1/9$ 得谱。证毕。

因此

$$
\operatorname{Tr}\rho_A^2=11/243,\quad\operatorname{Tr}\rho_A^3=43/19683,\quad
\operatorname{Tr}\rho_A^3-(\operatorname{Tr}\rho_A^2)^2=8/59049>0,
$$

$$
S(\rho_A)=4\log3-(8/9)\log4<3\log3.
$$

一般地，三阶矩差是以本征值自身为概率权重的本征值方差，非负且仅在非零谱平坦时为零。它可用两副本、三副本循环置换期望表达；未声称已有硬件制备或测量。

## 11. 公开矩阵问题上的精确迁移证书

[BZ24] 第 4 节 Conjecture 1 讨论 $\mathcal H(\boldsymbol\alpha),U_1,U_2,U_3(a)$ 四类 36 阶矩阵，在指定全部参数上两两既不局部幺正等价，也不 Hadamard 等价。$\mathcal H$ 有 19 个参数。两种等价关系不同；四副本不变量只在已证明的四方局部幺正关系下使用。本卷未完成全部参数或 Hadamard 部分。有限文献检索未见完整结算，不等同于穷尽文献。

采用 [BZ24] 式 (10)–(15) 的原始矩阵。固定三代表不可等价性已见 [Rather24] 第 5.2 节；此处是已知结论的精确验证。两文矩阵相差两侧局部 Fourier 因子，不改变局部等价问题。设 $\zeta=e^{i\pi/3}$，$\lambda_j(a,b)$ 为三个长度 36 相位向量按 $6\times6$ 排列后的指数；第三个向量原分母为三，转换时指数乘二。正指数 Fourier 约定下，

$$
(U_j)_{kl,mn}=\frac{\zeta^{lk+nm}}{36}
\sum_{a,b=0}^5\zeta^{a(l-n)-b(k+m)+\lambda_j(a,b)}.
$$

$H_j=6U_j$ 每个元素为六次单位根，对应归一化四方态为 $\psi_j=H_j/36$。

**证书 11.1（固定三代表）。** 对定义 8.1，

$$
I(\psi_1)=35/419904=70/839808,\quad
I(\psi_2)=79/839808,\quad I(\psi_3)=1/15552=54/839808.
$$

它们两两不同。未归一化分子为 $235146240,265379328,181398528$，公共分母 $36^8=2821109907456$。附录 A 在六次单位根整数环中直接收缩，未用优化失败、浮点拟合或秩阈值证明不等价。

**证书 11.2（连续相位精确缺陷）。** 用 $z\in U(1)$ 表示 [BZ24] 式 (15) 实际乘到指定元素上的相位，以避免角度变量的 $a$ 与 $2\pi a$ 记法混淆。对该式零一掩码 $M$ 和 $U_3(z)=U_3\circ z^M$，全部 $|z|=1$ 满足

$$
\|U_3(z)U_3(z)^*-I\|_F^2=0,
$$

$$
\|U_3(z)^R(U_3(z)^R)^*-I\|_F^2
=\|U_3(z)^\Gamma(U_3(z)^\Gamma)^*-I\|_F^2
=17/6-(17/12)(z+z^{-1}).
$$

因此 $z=e^{i\theta}$ 时相应二方纯度为

$$
\operatorname{Tr}\rho_R(z)^2=1/36+(17/7776)(1-\cos\theta).
$$

**验证。** 将 $H_3$ 的掩码内外分成 $A+zB$，逐重排计算 $[(A+zB)(A^*+z^{-1}B^*)-36I]$ 的平方 Frobenius 范数，除以 $36^2$。$z^{-2},z^{-1},1,z,z^2$ 系数对原排列全零，对另两种为 $(0,-17/12,17/6,-17/12,0)$。这是有限 Laurent 多项式的逐系数等式，覆盖整个单位圆。态归一化再除 $36^2$ 即得纯度式。附录 A 给出完整程序。

## corollary 11.3: 连续相位的局部非等价

$z\ne1$ 时 $U_3(z)$ 不与任何二幺正矩阵局部等价，因而不与任何 $\mathcal H(\boldsymbol\alpha),U_1,U_2$ 局部等价。$z=1$ 时与 $U_1,U_2$ 的分离见证书 11.1，与完整 $\mathcal H$ 的关系仍未解决。[BZ24] 表 1 已提示非零相位通常破坏二幺正性；本卷给出全相位恒等式和周期回返边界，不把已知提示或固定代表记为新的开放问题结算。

## 12. 整个单环的块局部精度通道

本节允许每个顶点的两条外部腿组成一个边界块，并允许缝合处两个相邻块之间的联合门。环上块为 $i=0,\ldots,L-1$，块 $0$ 与块 $L-1$ 相邻。这比每条腿独立 CPTP 严格更宽；定理 9.2 仍然有效。

**定义 12.1（显式历史编码）。** 固定 $L\ge3$ 和整数 $\alpha$。解码后每个边界块有寄存器 $(u_i,v_i)$。令

$$
M_d|u,v\rangle=|u+v,u+2v\rangle,\qquad
M_d^{-1}|a,b\rangle=|2a-b,b-a\rangle,
$$

$$
P_d|u_0,v_0,\ldots,u_{L-1},v_{L-1}\rangle
=\omega_d^{u_0v_{L-1}+\alpha u_0^2}|u_0,v_0,\ldots,u_{L-1},v_{L-1}\rangle,
\qquad G_d=M_d^{\otimes L}P_d.
$$

$M_d$ 的行列式为一，故是全边界空间上的置换幺正；$P_d$ 只作用于缝合两块。取 $L+1$ 个逻辑历史寄存器并定义等距

$$
K_d|x_0,\ldots,x_L\rangle=\bigotimes_{i=0}^{L-1}|x_i,x_{i+1}\rangle,
\quad J_d=G_dK_d,\quad\mathcal E_d(\rho)=J_d\rho J_d^*.
$$

$K_d$ 是固定计算基的相干重复编码；不把任意未知量子态复制为两个独立副本。对 $|+_d\rangle=d^{-1/2}\sum_x|x\rangle$，

$$
J_d|+_d\rangle^{\otimes(L+1)}=|\Psi^\alpha_{d,L}\rangle,
$$

恰为定义 4.2 的原网络态。编码定义在整个 $d^{L+1}$ 维历史空间，未把单个参考态当成整个输入空间。

## theorem 12.2: 全输入交换图和严格通道塔

用第 7 节数字通道 $Q_{D,d}$ 定义

$$
\mathcal R_{D,d}=\operatorname{Ad}_{G_d}\circ Q_{D,d}^{\otimes2L}\circ\operatorname{Ad}_{G_D^*},
\qquad\mathcal Q_{D,d}=Q_{D,d}^{\otimes(L+1)}.
$$

它们 CPTP。$\mathcal R_{D,d}$ 在全部边界输入上满射、非恒定，并且

$$
\boxed{\mathcal R_{D,d}\circ\mathcal E_D=\mathcal E_d\circ\mathcal Q_{D,d}.}
$$

对 $f\mid d\mid D$，还在全部边界矩阵上满足

$$
\boxed{\mathcal R_{d,f}\circ\mathcal R_{D,d}=\mathcal R_{D,f}.}
$$

**证明。** 令 $e=D/d$，$W_{D;d,e}|a+db\rangle=|a\rangle|b\rangle$，按低、高层统一重组。直接在每个逻辑基向量上可见

$$
W_{D;d,e}^{\otimes2L}K_D=(K_d\otimes K_e)W_{D;d,e}^{\otimes(L+1)}.
$$

两次出现的同一个历史标签使用同一数字分解，因此共享腿一致。于是全边界幺正层分解

$$
\mathcal V_{D;d,e}=(G_d\otimes G_e)W_{D;d,e}^{\otimes2L}G_D^*
$$

满足等距的算子恒等式

$$
\mathcal V_{D;d,e}J_D=(J_d\otimes J_e)W_{D;d,e}^{\otimes(L+1)}.
$$

该恒等式按线性性覆盖任意逻辑叠加，及与任意外部参考纠缠的输入。对高层偏迹，$G_e$ 不改变偏迹结果，且 $J_e$ 等距，得到所述通道交换图。第 7 节 $Q$ 的全输入复合律与中间 $G_d^*G_d=I$ 给出严格通道塔。$Q^{\otimes2L}$ 满射到全部低层密度矩阵，幺正共轭保持满射性，故通道非恒定。证毕。

**局部性。** 实施顺序是所有块各自解码 $M_D^*$、缝合两块实施 $P_D^*$、块内数字偏迹、同一缝合处实施 $P_d$、所有块各自编码 $M_d$。至多五个宏观操作层，深度不随 $L$ 增长，跨块支持仅为缝合处相邻两块。该计数允许任意所述有限维块门，不声称基本量子门数或精度成本不随 $d,D$ 增长。Heisenberg 读出支持只可能在触及缝合块时增加另一缝合块；精度复合不会扩大这一区域。

## corollary 12.3: 原 RT 参考态的精确层分解

对 $D=de$，

$$
\mathcal V_{D;d,e}|\Psi^\alpha_{D,L}\rangle
=|\Psi^\alpha_{d,L}\rangle\otimes|\Psi^\alpha_{e,L}\rangle,
\qquad
\mathcal R_{D,d}(|\Psi^\alpha_{D,L}\rangle\langle\Psi^\alpha_{D,L}|)
=|\Psi^\alpha_{d,L}\rangle\langle\Psi^\alpha_{d,L}|.
$$

**证明。** 每个 $|+_D\rangle$ 的数字分解恰为 $|+_d\rangle\otimes|+_e\rangle$，代入定理 12.2 的等距恒等式。证毕。对固定 $p,L$ 选择定理 5.2 的同一个整数 $\alpha$，这就给出每一精度都满足全区域 RT 的严格相容参考态塔。

## proposition 12.4: 进位表示及仅一处残余相位

在原边界输出上先逐腿拆数字，再在每个顶点的两条输出腿实施定理 9.3 的进位修正。对路径 $x=a+db$，输出变成低层 $B_da$ 和高层 $B_eb$，其中 $(B_dx)_i=(x_i+x_{i+1},x_i+2x_{i+1})$。只需再施加相位

$$
\exp\left(2\pi i\left[\frac{q(a)}d+\frac{q(b)}e-\frac{q(a+db)}{de}\right]\right),
\qquad q(x)=x_0x_L+\alpha x_0^2,
$$

即得到 $\mathcal V_{D;d,e}$ 在编码子空间上的作用。相位仅依赖两个端点的低、高数字；它们从第一个和最后一个顶点块分别由 $M_d^{-1},M_e^{-1}$ 恢复。

**证明。** 逐顶点点进位修正由定理 9.3 的同一坐标恒等式给出，不要求输入向量在各路径上等幅。原相位为 $e^{2\pi iq(a+db)/(de)}$，乘所列相位后恰为两层相位的乘积。相位函数在所有边界基上可通过各块逆置换定义，故是合法的全空间对角幺正，不只是在态支撑上写一个形式规则。证毕。

至此，单环的共享历史和缝合相位可同时修正；没有把单边相容直接当作网络相容。一般多环、附树边界上的同样有限范围通道尚未由本节证明。

## 13. 显式局部 Hamiltonian 与可检验的 RT 误差界

在解码寄存器上定义互不重叠的 $L$ 条量子连接：$i=0,\ldots,L-2$ 的 $(v_i,u_{i+1})$ 取 $\Phi_d$，缝合 $(u_0,v_{L-1})$ 取 $\Omega_{d,\alpha}$。于是

$$
|\chi_d\rangle=|\Omega_{d,\alpha}\rangle_{u_0,v_{L-1}}
\otimes\bigotimes_{i=0}^{L-2}|\Phi_d\rangle_{v_i,u_{i+1}},
\qquad |\Psi^\alpha_{d,L}\rangle=M_d^{\otimes L}|\chi_d\rangle.
$$

## theorem 13.1: 局部父 Hamiltonian 的全谱

取每项能量系数为一，定义

$$
H_d^0=(I-|\Omega_{d,\alpha}\rangle\langle\Omega_{d,\alpha}|)_{u_0,v_{L-1}}
+\sum_{i=0}^{L-2}(I-|\Phi_d\rangle\langle\Phi_d|)_{v_i,u_{i+1}},
$$

$$
H_d=M_d^{\otimes L}H_d^0(M_d^{\otimes L})^*.
$$

$H_d$ 为 $L$ 个两相邻顶点块上的相互对易投影之和，唯一基态是 $\Psi^\alpha_{d,L}$，基态能量零、谱隙一，全部能量及重数为

$$
E_k=k,\qquad\operatorname{mult}(E_k)=\binom Lk(d^2-1)^k,\quad k=0,\ldots,L.
$$

**证明。** $H_d^0$ 的各项作用于互不重叠的寄存器对，每项有一维零空间和 $d^2-1$ 维一空间。张量积求和给出全谱；所有连接的零空间交为 $\chi_d$ 的一维空间。块内幺正保持谱、对易性与两相邻块支持，得到结论。证毕。

这是明确的 Bell 连接父 Hamiltonian 实例，使用成熟的张量网络和波函数重整化机制 [StateRG05, ER07]；没有把这一一般机制认作新发明。若 $\alpha$ 满足第 5 节判据，其唯一基态同时满足所有边界区域的 RT 等式。

## corollary 13.2: 局部能量认证全部区域

设实际归一化态为 $\sigma$，且

$$
0\le\operatorname{Tr}(H_d\sigma)\le\varepsilon\le1/4.
$$

令 $\psi=|\Psi^\alpha_{d,L}\rangle\langle\Psi^\alpha_{d,L}|$。则

$$
\operatorname{Tr}(\psi\sigma)\ge1-\varepsilon,\qquad
\tfrac12\|\sigma-\psi\|_1\le\sqrt\varepsilon.
$$

若 $\alpha$ 满足全区域 RT 判据，对任意非空的边界腿集合 $A$，$D_A=d^{|A|}$，有

$$
\boxed{|S(\sigma_A)-m(A)\log d|
\le\sqrt\varepsilon\log(D_A-1)+h_2(\sqrt\varepsilon).}
$$

**证明。** 谱隙给出 $H_d\ge I-\psi$，得到重叠界；对纯目标的保真度与迹距离不等式给出全态迹距离界，偏迹不增迹距离。应用 [Aud07] 的熵连续性界；其右侧在 $[0,1-1/D_A]$ 单调，而 $\sqrt\varepsilon\le1/2$ 在该区间内。证毕。

这里需要估计 $L$ 个明确的局部能量项，而无需完整边界态层析。项的数目不是采样次数；有限统计误差须先计入真实能量上界 $\varepsilon$，每个块的维数及门实现成本也未忽略。父 Hamiltonian 能量认证是已有方法，相关可实施框架见 [Cert26]；本卷给出当前 RT 态的具体 Hamiltonian、精确谱隙和误差公式，未进行硬件实验。

## 14. 回接 RT 的统一边界与未证义务

[RT] 连接边界纠缠熵与对偶引力最小面积；[LM] 在引力复制构造下推导相应关系。[HaPPY]、[Harlow] 已建立完美张量、量子纠错和互补恢复中的 RT 型结果。[HMPS] 已处理 Bruhat–Tits 树及 Schottky 商的对偶网络，包括连接与不连接区域；本卷固定四腿循环模环构造与其具体网络不同。秩饱和、平坦谱和面积的识别也分别参照 [QMF]、[FixedArea]。

[TPTN26] 第 7 节的谱问题在本卷获得有限单环精确解，但排除最小割简并后的典型谱极限、其他范数下的收敛和完整体态区域恢复仍未解决。该文 v2（2026-06-03）的式 (5.23) 前仍保留无领先简并条件；第 7 节仍提出严格谱问题。[BZ24] 的全部 19 参数比较和 Hadamard 不等价仍未闭合。[RRKL23] 的三维唯一性作为已发表定理直接复用；[Tan26] 是顶点实际量子操作的相关背景。

第 12 节已对显式历史空间和全部输入闭合

$$
\mathcal R_{D,d}\mathcal E_D=\mathcal E_d\mathcal Q_{D,d}.
$$

这不等于对任意历史输入都证明同一个纯面积公式。一个明确反例是任意计算基历史 $|x\rangle$：$J_d|x\rangle$ 只是一个边界计算基乘积态乘全局相位，因此所有区域熵都为零，即使 $m(A)>0$。全区域 RT 饱和目前针对指定参考态及第 13 节控制的近邻态。该历史编码尚未被识别为具有独立引力意义的体码；其最大区域恢复与零面积结论见第 15 节。

第 12 节降低的是寄存器精度，边界块数不变。它与 [ER07] 的先处理纠缠再截断具有方法联系，但没有构造空间尺度的 MERA 或连续极限。第 13 节还显示，在所选双腿块划分下参考态是局部幺正作用于相邻 Bell 连接的短程模型，有显式非零谱隙；相容精度塔本身不提供临界边界场论。局部窗口精度不自动等于图的径向截断尺度；完整 Bruhat–Tits 边界为 $\mathbb P^1(\mathbb Q_p)$，$\mathbb Z_p$ 是自然紧开部分。

原始引力 RT 仍需独立给定边界理论与态、共同调节下的熵控制、满足同调约束的图割到几何面积的极限、$1/(4G_N)$ 系数及引力动力学。后续应在同一目标下扩展几何和体态结构，而不把任意通道交换图或事后构造的父 Hamiltonian 当作物理对偶的证明。

## 15. 全历史编码的最大区域恢复代数

本节直接计算第 12 节编码的区域信息，而不从参考态面积律推断整个码的性质。一般的可纠正代数判据来自 [BKK07]，代数熵与 RT 关系采用 [Harlow] 的标准分块熵约定。以下陪集坐标、矩阵单位和维数是对当前算术映射的显式求值。

## theorem 15.1: 相干单项编码的完整区域正规形

设 $V,X,Y$ 为有限交换群，$A:V\to X$、$B:V\to Y$ 为群同态，$(A,B)$ 单射。允许任意相位函数 $q:V\to U(1)$，不要求二次。取全历史空间 $\mathbb C[V]$ 上的等距编码

$$
J|v\rangle=q(v)|Av\rangle_X|Bv\rangle_Y.
$$

记 $K_A=\ker A$、$K_B=\ker B$、$Z=V/(K_A+K_B)$。每个 $z\in Z$ 选代表元 $v_z$，则

$$
\mathcal U|z,a,b\rangle=\overline{q(v_z+a+b)}|v_z+a+b\rangle,
\quad a\in K_A,\ b\in K_B
$$

是从 $\bigoplus_z\mathbb C[K_A]\otimes\mathbb C[K_B]$ 到实际历史空间的幺正。两侧在其实际像空间上分别换基后，编码恰为

$$
J\mathcal U|z,a,b\rangle=|z,b\rangle_X|z,a\rangle_Y.
$$

因此从 $X$、$Y$ 可精确恢复的最大含幺逻辑 $*$-代数分别为

$$
\mathcal M_X=\mathcal U\left[\bigoplus_{z\in Z}
 I_{K_A}\otimes\mathcal B(\mathbb C[K_B])\right]\mathcal U^*,
\qquad
\mathcal M_Y=\mathcal U\left[\bigoplus_{z\in Z}
 \mathcal B(\mathbb C[K_A])\otimes I_{K_B}\right]\mathcal U^*.
$$

两者互为交换子代数，交为 $|Z|$ 维中心。这里“恢复”指擦除另一侧后仍能恢复该代数的全部观测统计；不声称恢复全历史态。

**证明。** $K_A\cap K_B=0$，每个历史唯一写成 $v_z+a+b$。$X$ 中的标签是 $A(v_z+b)$；不同 $(z,b)$ 的标签不同，否则两代表元相差 $K_A+K_B$，继而 $b$ 的差同时属于两核，必须为零。$Y$ 的 $(z,a)$ 同理。相位在 $\mathcal U$ 中消除，得到所列正规形，无须任何群扩张分裂假设。

任意块对角 $b$ 算符可在 $X$ 的 $(z,b)$ 标签上直接实施，因此给出可恢复代数。一个显式 CPTP 恢复是读取中心扇区，保留 $b$ 态，并在丢失的 $a$ 因子准备固定态；对像空间外输入可附加固定输出，从而在全输入上定义通道。

最大性由实际错误算符算出：对 $Y$ 的矩阵单位压缩 $J^*(I_X\otimes|z,a\rangle\langle z',a'|)J$，$z\ne z'$ 时为零；$z=z'$ 时恰为经 $\mathcal U$ 共轭的 $|z\rangle\langle z|\otimes|a\rangle\langle a'|\otimes I_{K_B}$。它们张成所列 $\mathcal M_Y$。擦除的可纠正代数必须与全部压缩错误算符交换 [BKK07]，其交换子恰是 $\mathcal M_X$；另一侧对称。证毕。代表元选择只改内部坐标，不改实际可恢复代数。

## corollary 15.2: 全输入熵与相对熵，面积算符为零

对任意历史密度矩阵 $\rho$，令 $\widehat\rho=\mathcal U^*\rho\mathcal U$，$p_z=\operatorname{Tr}\widehat\rho_{zz}$，$\rho_{b,z}=\operatorname{Tr}_{K_A}\widehat\rho_{zz}/p_z$；零权扇区略去。则

$$
\operatorname{Tr}_Y(J\rho J^*)\simeq\bigoplus_zp_z\rho_{b,z},
\qquad
S(\operatorname{Tr}_YJ\rho J^*)=H(p)+\sum_zp_zS(\rho_{b,z}).
$$

右侧正是标准分块代数熵 $S_{\mathcal M_X}(\rho)$，不含冗余因子 $\log|K_A|$。对任意两输入，边界相对熵也精确等于此代数上的相对熵：

$$
D(\rho_X\Vert\sigma_X)=D(p\Vert s)+\sum_zp_zD(\rho_{b,z}\Vert\sigma_{b,z}),
$$

支持不包含时两侧均按 $+\infty$ 处理。因而若固定算符 $\mathcal L_X$ 要对所有 $\rho$ 满足

$$
S(\rho_X)=\operatorname{Tr}(\rho\mathcal L_X)+S_{\mathcal M_X}(\rho),
$$

则唯一可能是 $\mathcal L_X=0$。

**证明。** 对正规形偏迹，$Y$ 标签的正交性消去不同 $z,a$ 的交叉项，得到直和密度矩阵。熵和相对熵由其分块谱直接计算。两种熵已经相等，因此 $\operatorname{Tr}(\rho\mathcal L_X)=0$ 对全部密度矩阵成立，推出算符为零。证毕。结论使用指定的最大可恢复代数和标准代数熵；未排除另行选取受约束码子空间后出现非零面积项。

## corollary 15.3: 单环交错半边的经典与量子信息分解

对第 12 节原编码，取 $V=R_d^{L+1}$、$A,B$ 为两侧真实边界线性输出。当区域每顶点恰选一腿时，两核均由初始值递推参数化，大小各为 $d$，故

$$
|Z|=d^{L-1},\qquad
\mathcal M_A\simeq\bigoplus_{z=1}^{d^{L-1}}M_d(\mathbb C),\qquad
\dim_{\mathbb C}\mathcal M_A=d^{L+1}.
$$

这表示 $d^{L-1}$ 个可区分经典扇区及每扇区一个 $d$ 维量子因子，不表示能恢复 $L$ 个独立量子寄存器。对均匀参考历史及第 4 节二次相位，中心分布均匀，扇区内的 Schmidt 秩为 $d/\gcd(d,c_k)$，所以

$$
S(\rho_A)=(L-1)\log d+
\log\frac d{\gcd(d,c_k)}.
$$

**证明。** 核计数给出代数，扇区内双字符求值直接采用定理 3.1 和 4.3。证毕。单位相位时的 $L\log d$ 全部落在恢复代数的状态熵内；现有全历史码的图割值不能直接识别为 Harlow 公式中的非零中心面积算符。这比第 14 节的单个乘积输入反例更精确：它计算了全部输入、全部区域的恢复信息。

## 16. 空间粗化、相位调整与精度方向的交换

固定奇素数 $p$。对每个 $L\ge3$ 选一个整数 $\alpha_L$，使定理 5.2 的判据对全部 $d=p^n$ 成立。三进情形可取 $\alpha_L=L\bmod2$。记第 12 节相应对象为 $G_{d,L},J_{d,L},\mathcal E_{d,L}$。不同环长允许不同的 $\alpha_L$，同一长度各精度沿用同一整数。

**定义 16.1（真实空间分块）。** 取保留标记缝合的连续分割

$$
0=t_0<t_1<\cdots<t_r=L,\qquad r\ge3.
$$

第 $j$ 个宏块含细顶点 $t_j,\ldots,t_{j+1}-1$。在解码坐标中仅保留 $(u_{t_j},v_{t_{j+1}-1})$，偏迹该宏块内部的其余寄存器。这个全边界偏迹记为 $\operatorname{Ret}_{\Pi}$。逻辑空间上仅保留 $x_{t_0},\ldots,x_{t_r}$ 的偏迹记为 $\operatorname{ret}_{\Pi}$。定义

$$
\mathcal S_{\Pi,d}
=\operatorname{Ad}_{G_{d,r}}\circ\operatorname{Ret}_{\Pi}\circ
\operatorname{Ad}_{G_{d,L}^*}.
$$

这一次空间块数确实由 $L$ 降为 $r$，连接维数 $d$ 保持不变。

## theorem 16.2: 两参数严格相容

空间通道 CPTP、满射且非恒定，并在全部逻辑输入上满足

$$
\mathcal S_{\Pi,d}\mathcal E_{d,L}
=\mathcal E_{d,r}\operatorname{ret}_{\Pi}.
$$

若 $\Sigma$ 是对 $r$ 个宏块的进一步连续分割，则在全部边界输入上

$$
\mathcal S_{\Sigma,d}\mathcal S_{\Pi,d}
=\mathcal S_{\Sigma\circ\Pi,d}.
$$

与第 12 节每个环长上的精度通道还满足

$$
\boxed{\mathcal S_{\Pi,d}\mathcal R^{(L)}_{D,d}
=\mathcal R^{(r)}_{D,d}\mathcal S_{\Pi,D}.}
$$

各等式也适用于与任意外部参考纠缠的输入。原参考态严格送到同一模型的短环参考态：

$$
\mathcal S_{\Pi,d}(|\Psi^{\alpha_L}_{d,L}\rangle\langle\Psi^{\alpha_L}_{d,L}|)
=|\Psi^{\alpha_r}_{d,r}\rangle\langle\Psi^{\alpha_r}_{d,r}|.
$$

**证明。** 在 $K_{d,L}|x\rangle\langle y|K_{d,L}^*$ 中，每个被删历史标签的两份都位于同一宏块内部，偏迹恰好给出对应的 $\delta_{x_i,y_i}$；每个保留标签的两份仍作为相邻宏块端点保留。因此

$$
\operatorname{Ret}_{\Pi}(K_{d,L}\rho K_{d,L}^*)
=K_{d,r}\operatorname{ret}_{\Pi}(\rho)K_{d,r}^*.
$$

共轭给出全输入交换图。嵌套偏迹保留同一组最终端点，中间 $G^*G$ 抵消，得到空间复合律。精度与空间的方形图归结为

$$
\operatorname{Ret}_{\Pi}\,Q_{D,d}^{\otimes2L}
=Q_{D,d}^{\otimes2r}\,\operatorname{Ret}_{\Pi},
$$

因为在被删寄存器上数字通道保迹，在保留寄存器上两操作分属独立因子。满射由偏迹可添加固定辅助态和幺正共轭得出。参考历史是各寄存器 $|+_d\rangle$ 的乘积，丢弃内部历史仍留下相同形式的纯输入。所有证明是在矩阵单位或算子上建立，故包含任意参考系统。证毕。

**局部实现。** 两端的双线性缝合相位 $u_0v_{L-1}$ 在偏迹前后相同且只涉及被保留寄存器，故相消。令 $\delta=\alpha_r-\alpha_L$，实际空间通道可写成

$$
\mathcal S_{\Pi,d}
=\operatorname{Ad}_{M_d^{\otimes r}}
\circ\operatorname{Ad}_{D_{d,\delta}^{(u_0)}}
\circ\operatorname{Ret}_{\Pi}
\circ\operatorname{Ad}_{(M_d^{\otimes L})^*}.
$$

所有解码、丢弃和重新编码都位于各自宏块内；额外二次相位只位于第一个宏块。宏块大小为 $b$ 时门支持可达该宏块的 $2b$ 条细腿，不能称为与分块尺寸无关的细格点操作。空间通道不保持任意细腿区域的原熵；它保持的是所指定编码交换图，并把参考态送到满足各自图割等式的粗态。

## proposition 16.3: 三进相位调整的必要性

对 $d=3^n$，全区域 RT 条件要求：偶环 $\alpha\equiv0\pmod3$，奇环 $\alpha\not\equiv0\pmod3$。故一个不变的 $\alpha$ 不能同时覆盖奇、偶长度。

**证明。** 偶环中 $c_k\equiv2\alpha+2(-1)^k\pmod3$，$k$ 的两种奇偶均出现；同时非零当且仅当 $\alpha=0$。奇环中两幂之和为零，$c_k\equiv2\alpha$，故要求非零。模 $3$ 非零等价于在每个 $3^n$ 中为单位。证毕。

例如四环的 $\alpha=0$ 参考态原本对全部区域饱和；若分块到三环却不改相位，交错半边的熵只剩 $2\log3$，而三环最小割为 $3$。在保留寄存器 $u_0$ 上加 $\omega_3^{u_0^2}$ 后得到 $\alpha=1$ 三环，熵恢复 $3\log3$。修正由真实粗化后的单位判据决定，并非声称普通偏迹自动保持 RT。

## corollary 16.4: 空间固定点的精确限制

对参考态，若区域 $A$ 由完整的双腿顶点块构成，则

$$
S(\rho_A)=|\partial A|\log d,
$$

其中 $\partial A$ 是环上穿过该分区的边集合。对任意三组互不相交完整块 $A,B,C$，忽略其余块后有

$$
I(A:C\mid B)=2|E(A,C)|\log d.
$$

**证明。** 第 13 节将参考态写为块内幺正作用于独立最大纠缠边。每条边独立贡献区域熵：穿过边界贡献 $\log d$，否则为零。将四个区域熵代入条件互信息，只有直接连接 $A,C$ 的边贡献 $2\log d$。证毕。标准量子 Markov 等式的结构背景见 [HJPW04]。

因此任意非空真连续区间的熵恒为 $2\log d$，与区间长度无关；没有直接相邻边的块组满足所述条件互信息为零。与分割匹配的完整宏块区域在空间粗化前后保留这一熵。第 16 节闭合了空间和精度的双参数操作关系，同时证明当前块态仍是短程 Bell 固定点，未生成临界边界理论。

**统一的后续义务。** 第 15 节给出当前全历史编码的完整区域恢复，但其标准面积算符为零。要得到具有非零几何面积项的全输入量子 RT，需选取或构造受约束编码子空间，在独立几何区域间保留固定的辅助纠缠，同时证明该选择与第 16 节的粗化相容。一般 OAQEC 与波函数重整化的原理已有文献基础；这里的算术扇区求值、相位随环长的必要调整及实际交换图尚未完成全面优先权排查，不认领外部猜想结算或原始引力 RT 证明。

## 17. 从有限割到双曲曲面：显式实现与几何非唯一性

本节区分三件事：有限熵向量有几何实现；给定量子码有非零面积算符；量子态具有独立边界场论的引力对偶。[HEC15] 第 3.2 节、Lemma 4 和 Theorem 5 已证明图模型与双曲曲面的熵向量对应，并明确指出扭转不唯一。本节沿用该成熟构造，给出当前单环的具体拓扑、统一领圈尺度和不可识别自由度，不将一般图到几何定理再次认领为新结果。曲率统一采用高斯曲率 $-1$ 的长度约定；领圈宽度采用 [EPV23] Lemma 2.1。

## proposition 17.1: 当前单环的显式双曲实现

固定 $L\ge3$，将原单环的每个四价顶点拆成两个三价顶点，以权重 $\beta=L+1$ 的辅助边连接。每个新顶点接一条原环边和一条原边界边；所有原边权为一。令

$$
\epsilon=\frac1{10(L+1)^2},\qquad
w(\ell)=\operatorname{arsinh}\!\frac1{\sinh(\ell/2)}.
$$

每个三价顶点用一条边界长度为 $\epsilon\beta$、另外两条为 $\epsilon$ 的双曲裤子面替代；按图缝合内部边界，扭转参数任意。未缝合边界可附加半领圈作为实际外边界。所得曲面 $\Sigma$ 有 $2L$ 个标记边界分量、亏格一。对每个标记边界集合 $A$，

$$
\min_{\gamma\sim A}\operatorname{Length}(\gamma)=\epsilon m(A),
$$

其中 $\gamma$ 为与 $A$ 同调的分离多曲线，$m(A)$ 是原单环的图最小割。所有区域由同一个曲面同时实现。

**证明。** 原图任意区域的最小割不超过 $L$，因为可割该区域或其补集全部边界腿。辅助边的单条代价 $\beta>L$，故新图的任何最小割都不割辅助边；收缩辅助边即恢复原图，全部割值不变。

每个内部缝合曲线的长度不超过 $\epsilon\beta$。任意非缝合的简单闭测地线必须穿过一条裤子分解曲线，领圈定理给出长度下界

$$
2w(\epsilon\beta)>\epsilon L.
$$

所选 $\epsilon$ 满足 $\epsilon\beta\le1/40$，故 $2w(\epsilon\beta)>1$，而 $\epsilon L<1/10$，确立严格不等式。另一方面每个区域已有长度至多 $\epsilon L$ 的缝合曲线候选。极小多曲线因此只能由缝合曲线组成。同调约束恰对应由裤子面子集诱导的图割，故得到等式；任意扭转均不影响领圈下界。共有 $2L$ 个裤子面、$2L$ 条内部缝合曲线和 $2L$ 个外边界，Euler 特征为 $-2L$；由 $2-2g-2L=-2L$ 得 $g=1$。证毕。半领圈不改变拓扑；最小曲线位于裤子面的凸核，外部半领圈不产生更短的额外闭测地线。

任取长度换算常数 $\lambda>0$，令

$$
g'=\left(\frac{\lambda\log d}{\epsilon}\right)^2g.
$$

那么定理 5.2 的参考态满足

$$
S(\rho_A)=\frac1\lambda\min_{\gamma\sim A}\operatorname{Length}_{g'}(\gamma).
$$

形式上取 $\lambda=4G_N$ 可写成 RT 的量纲形式，但本构造没有推导 $G_N$，也没有将此曲面的边界场论态识别为该有限张量态。各边界腿在本实现中对应一个完整边界圆，不是一个已给定单圆 CFT 上的空间区间。

## corollary 17.2: 扭转和隐藏把手不可由这些熵唯一恢复

固定上述裤子分解的全部长度，$2L$ 个 Fenchel–Nielsen 扭转参数可独立变化，所有 $m(A)$ 不变。它们给出标记曲面的 $2L$ 维族；除去离散映射类识别后仍有连续的几何不唯一性。这正是 [HEC15] 已指出的扭转盲性在当前图上的维数求值。

还可在保持相同边界长度、曲率和全部最小割熵的同时，实现任意亏格 $g\ge1$。证明是在一条单位权内部边上插入三价顶点，将该边变为两条串联单位边；新顶点再以单位桥边连接到一个带单位自环的三价顶点。无边界的这个附件在最小割时可与连接顶点同侧，代价为零；两个串联边在端点异侧时最小代价仍为一。故边界割函数不变。该操作增加两个裤子面、三个内部缝合参数而不增加外边界，使亏格加一。新最大边权仍为 $\beta$，区域候选上界仍为 $\epsilon L$，原领圈条件对任意次添加统一有效。逐次应用即得。这里的附加图用于几何实现，不改变原量子张量网络。

**相位字典的限制。** $\alpha$ 不能直接等同于仅改变上述曲面扭转、保持裤子边界长度不变的参数。例如 $d=L=3$ 时，$\alpha=0$ 与 $\alpha=1$ 在指定区域产生 $2\log3$ 与 $3\log3$ 的不同熵，而任何这类固定长度扭转都不改变几何最小割。需要同时说明相位如何改变状态的几何适用性、长度数据或体熵项，才能建立这样的字典。

## 18. 在原码内部产生非零面积，并计算容量代价

本节固定一个边界划分 $X|Y$，使用第 15 节同一个正规形及实际逻辑坐标 $\mathcal U$。构造依赖这个划分；没有为不同区域分别选子空间后再将其冒充同一码。固定辅助纠缠产生面积的机制来自 [Harlow]，最大纠缠与固定面积谱的关系见 [AR19]。下面把机制落实到当前全历史码内的明确相干约束，并给出达到容量界的实例。

## theorem 18.1: 共享中心的相干分组子码

将 $Z$ 分成非空不交集合 $Z_t$，大小 $r_t$。取正权概率 $\lambda_{t,z}>0$、$\sum_{z\in Z_t}\lambda_{t,z}=1$，定义受约束历史嵌入

$$
F|t,a,b\rangle=\sum_{z\in Z_t}\sqrt{\lambda_{t,z}}\,\mathcal U|z,a,b\rangle,
\qquad a\in K_A,\quad b\in K_B.
$$

这是进入原历史空间的等距，码维数为 $|T||K_A||K_B|$，其中 $T$ 是分组指标集合。在两侧分别整理真实标签后，物理编码变为

$$
JF|t,a,b\rangle\simeq
|t,b\rangle_X|t,a\rangle_Y\otimes|\chi_t\rangle,
\qquad
|\chi_t\rangle=\sum_{z\in Z_t}\sqrt{\lambda_{t,z}}|z\rangle_X|z\rangle_Y.
$$

因而其最大互补可恢复代数由 $t$ 扇区内的 $b$、$a$ 完全矩阵代数给出，而所有逻辑密度矩阵 $\rho$ 都满足

$$
S(\rho_X)=S_{\mathcal M_X}(\rho)+\operatorname{Tr}(\rho\mathcal L_X),
\qquad
\mathcal L_X=\bigoplus_t H(\lambda_t)I_{K_A\otimes K_B}.
$$

均匀选择时面积特征值为 $\log r_t$；选择不同大小的组可使面积算符非标量。没有增加物理辅助空间，$\chi_t$ 来自对原共享中心施加固定相干约束。

**证明。** $Z_t$ 不交且 $\mathcal U$ 幺正，立即得到 $F$ 等距。将每个标签 $z$ 重排为组号及组内坐标，第 15 节的实际编码 $|z,a,b\rangle\mapsto|z,b\rangle|z,a\rangle$ 给出所列因子化。偏迹后，

$$
\rho_X\simeq\bigoplus_t p_t\rho_{b,t}\otimes\operatorname{diag}(\lambda_t).
$$

这是同一实际边缘态的谱分解，熵为 $H(p)+\sum_t p_t[S(\rho_{b,t})+H(\lambda_t)]$。压缩另一侧矩阵单位张成 $t$ 扇区内的 $a$ 完全矩阵代数，故其交换子恰为所称最大代数。相对熵中固定 $\lambda_t$ 因子相消，也得到边界与逻辑代数相对熵的等式。证毕。这里固定相干方向是子空间定义，不是由只读经典中心标签的后处理自动制备出来的操作。

## proposition 18.2: 精确互补恢复的面积–容量界

对任意有限维、精确互补恢复的码，物理两侧维数为 $N_X,N_Y$。设每个中心扇区的面积特征值至少为 $a\ge0$。则码维数 $K$ 满足

$$
\boxed{\log K+2a\le\log N_X+\log N_Y.}
$$

**证明。** [Harlow] 的互补恢复正规形将每个扇区写为逻辑因子维数 $k_{X,t},k_{Y,t}$ 与固定纯辅助态 $\chi_t$。设后者的 Schmidt 秩为 $R_t$，则 $a\le S(\chi_{X,t})\le\log R_t$。不同扇区的物理支持正交，因此

$$
\sum_t k_{X,t}R_t\le N_X,\qquad
\sum_t k_{Y,t}R_t\le N_Y.
$$

于是

$$
K=\sum_t k_{X,t}k_{Y,t}
\le\left(\sum_t k_{X,t}\right)\left(\sum_t k_{Y,t}\right)
\le N_XN_Ye^{-2a}.
$$

证毕。这是文献正规形的容量推论；下述当前算术码的实现达到等号。

## corollary 18.3: 当前交错半边的饱和实例

单环交错半边满足 $N_X=N_Y=d^L$、$|Z|=d^{L-1}$、$|K_A|=|K_B|=d$。将全部 $Z$ 放进一个组并均匀固定，得到一个 $d^2$ 维子码，非零标量面积为

$$
a=(L-1)\log d,\qquad
S(\rho_X)=(L-1)\log d+S(\rho_b),
$$

对全部输入成立，并精确达到命题 18.2 的容量上界。$d=L=3$ 时，物理两侧各 $27$ 维，码为两个逻辑 qutrit，固定面积 $2\log3$；逻辑 $b$ 的熵最多再贡献 $\log3$。

另一方面，若要求同一平衡划分上的面积在每个码扇区都保持原图割值 $L\log d$，则 $K\le1$。故在当前物理维数下，具有精确互补恢复的非平凡全输入码，不能把这个容量饱和值全用作固定面积，再额外容纳独立逻辑熵。该结论不排除面积随扇区降低、近似恢复、增加物理维数或改变几何划分。

本节闭合的是固定划分上的非零面积子码构造及最优容量，不是一个同时适用于全部几何区域、且被第 16 节粗化保持的共同子码；后者仍须验证相交区域的约束相容性。

## 19. 同一历史码内的几何反例与精确熵距离

[HHM11] 已证明静态纯面积 RT 数据满足互信息单配性，即

$$
I_3(A:B:C)=S_A+S_B+S_C-S_{AB}-S_{AC}-S_{BC}+S_{ABC}\le0.
$$

它是同一几何同时解释多个区域的必要条件；不能未经控制就用于含体熵修正的完整数据。以下给出原历史编码中的明确态，并计算它到几何熵集合的尖锐距离。

## theorem 19.1: 同一码中的四方 GHZ 方向

取 $L\ge4$ 和任意奇数 $d\ge3$。在第 12 节历史空间取

$$
|\eta_p\rangle=\sum_{x\in R_d}\sqrt{p_x}\,|x,x,\ldots,x\rangle,
\qquad H(p)>0.
$$

任意 $\alpha$ 下，实际编码输出为

$$
J_d|\eta_p\rangle=\sum_x\sqrt{p_x}\,\omega_d^{(1+\alpha)x^2}
\bigotimes_{i=0}^{L-1}|2x,3x\rangle_i.
$$

每个块的标签 $x\mapsto(2x,3x)$ 单射，局部基变换与在一个块上消去相位后，此态等价于 $L$ 方 GHZ$(p)$。将所有完整块分成四个非空组 $A,B,C,D$，任意非空真子集的熵都是 $H(p)$，因此 $I_3=H(p)>0$。它不能由一个静态、无体熵修正的 RT 几何同时实现全部七项熵。证毕。该态已经位于原码像空间，故不能对全历史码整体赋予这种几何解释。

## theorem 19.2: 到三方全息熵锥的精确一致误差

令 $h=H(p)$，$s=(h,h,h,h,h,h,h)$ 按 $A,B,C,AB,AC,BC,ABC$ 排列。用 [HEC15] 的静态几何熵锥 $\mathcal C_3$ 约定，有

$$
\boxed{\inf_{g\in\mathcal C_3}\|g-s\|_\infty=h/7.}
$$

**证明。** 若所有七项误差不超过 $\delta$，则 $I_3(g)\ge h-7\delta$。几何单配性要求 $I_3(g)\le0$，故 $\delta\ge h/7$。为达到界，取四个全部为标记边界顶点的完全图 $K_4$，每条边权重 $2h/7$。其单点及三点割值为 $6h/7$，双点割值为 $8h/7$。七项误差全为 $h/7$，且此图熵向量由 [HEC15] 的图–曲面定理属于 $\mathcal C_3$。证毕。此推导未把有限线性规划的最优值当成一般证明；图构造同时给出精确上界。

因此，当前码内即使只有一个相干共同标签，也可能造成不可消去的几何误差。若坚持用纯面积模型，至少一项误差不小于 $H(p)/7$；若要保留全部原熵，则七项组合中的体熵或其他修正至少须补偿 $H(p)$ 的 $I_3$ 缺口。均匀 $p$ 时它随 $\log d$ 增长，不能在增加精度时未经控制就忽略。

**几何主线的下一义务。** 第 17 节解决有限参考熵的曲面存在性，但揭示扭转及拓扑不可由这些读数识别；第 18 节在当前码内产生正面积并给出容量最优解，但依赖单个划分；第 19 节排除了把整个历史码统一解释为纯几何 RT 数据。下一步要找的是一个对多个相交区域共同定义、粗化保持、满足几何熵约束的受约束码，同时明确哪些额外观测能识别有限割数据看不到的测地线和扭转。没有把任意可写成熵分解的面积算符直接认作同一光滑体几何。

## 20. 完整顶点块上的共同正面积子码

本节将第 18 节的单划分构造推进到同一个码上的全部块区域。**区域范围固定为第 12、16 节的完整双腿顶点块的任意并集**，包含相交及不连接区域；不包含从某个块只取一条腿的细分区域。所有子空间在选择观测区域之前定义。固定辅助纠缠和互补恢复的一般机制沿用 [Harlow, BKK07]；本节给出原算术历史编码中的共同实现及准确的容量范围。

**定义 20.1（冻结历史、保留自由连接）。** 取 $\mathsf S\subseteq\{1,\ldots,L-1\}$，允许这些历史寄存器任意取态，并将其余历史寄存器，包括 $x_0,x_L$，固定为 $|+_d\rangle$。记此等距嵌入为 $F_{d,L,\mathsf S}$，受约束编码为

$$
V_{d,L,\mathsf S}=J_{d,L}F_{d,L,\mathsf S},\qquad
\mathcal E^{\mathsf S}_{d,L}(\rho)=V_{d,L,\mathsf S}\rho V_{d,L,\mathsf S}^*.
$$

其逻辑维数是 $K=d^{|\mathsf S|}$，物理边界空间仍为原来的 $2L$ 条 $d$ 维腿。把自由历史 $x_i$ 对应到块边 $e_i=(i-1,i)$，缝合边为 $e_0=(L-1,0)$。令 $\mathsf F=E(C_L)\setminus\mathsf S$，其中 $\mathsf S$ 也表示对应边集。解码各块的 $M_d$ 后，自由边采用重复等距

$$
D_e|x\rangle=|x\rangle_{e,u}|x\rangle_{e,v},
$$

冻结普通边为 $\Phi_d$，冻结缝合边为 $\Omega_{d,\alpha_L}$。由原 $J$ 的振幅直接得到

$$
(M_d^{\otimes L})^*V_{d,L,\mathsf S}|\psi\rangle
=\left(\bigotimes_{e\in\mathsf F}|\phi_e\rangle\right)
\otimes\left(\bigotimes_{e\in\mathsf S}D_e\right)|\psi\rangle.
$$

允许 $\psi$ 在不同自由历史间任意纠缠。等式中各边占据不同的半边寄存器；只有各块 $M_d$ 混合其本地两腿。

## theorem 20.2: 同一码、全部块区域、全部输入

对任意块区域 $A$，把自由边分为两端均在 $A$ 的 $I_A$、仅一端在 $A$ 的 $C_A$ 和两端均在补集的 $O_A$。令 $\Delta_{C_A}$ 为这些自由历史的计算基退相干，

$$
\tau_A=\Delta_{C_A}\operatorname{Tr}_{O_A}\rho,\qquad
f_A=|\mathsf F\cap\delta A|.
$$

忽略区域内固定纯态及在实际支撑上的等距后，边界约化态为

$$
[\mathcal E^{\mathsf S}_{d,L}(\rho)]_A
\simeq\tau_A\otimes I_{d^{f_A}}/d^{f_A}.
$$

其最大可恢复逻辑代数和非零面积项为

$$
\mathcal M_A=\mathcal B(\mathcal H_{I_A})\otimes
\operatorname{Diag}(\mathcal H_{C_A})\otimes I_{O_A},\qquad
\mathcal L_A=f_A\log d\ I_K,
$$

$$
\boxed{S([\mathcal E^{\mathsf S}_{d,L}(\rho)]_A)
=f_A\log d+S_{\mathcal M_A}(\rho).}
$$

两侧代数互为交换子，区域包含关系 $A\subseteq B$ 给出实际逻辑代数包含 $\mathcal M_A\subseteq\mathcal M_B$。对任意两输入，边界相对熵等于该区域代数相对熵，包含无穷值的支持约定。

**证明。** 每条冻结割边在 $A$ 留下独立的 $I_d/d$，冻结内部边留下纯态，冻结外部边被完全丢弃。自由内部边保留重复等距的整个像，可逆恢复该逻辑因子；自由割边偏迹一份给出计算基退相干；自由外部边给出逻辑偏迹。这些操作在不同寄存器因子上作用，故对任意相关的 $\rho$ 仍给出同一个 $\tau_A$，而非仅对乘积输入成立。

在 $I_A,C_A,O_A$ 的逻辑坐标中，补集压缩错误算符张成
$ I_{I_A}\otimes\operatorname{Diag}(\mathcal H_{C_A})\otimes\mathcal B(\mathcal H_{O_A})$。
取交换子并用 [BKK07] 得到最大代数；显式恢复保留 $I_A$ 的量子态、保留 $C_A$ 的经典块，给丢失因子准备固定态。区域增大时单条自由边的可见代数只按标量、对角、全矩阵三个层级增加，故满足包含关系。熵及相对熵由真实边缘态的张量因子计算，固定最大混合因子在相对熵中相消。证毕。

这是一个相交区域共享的量子 RT 熵分解，面积在熵单位下由固定边图的割独立给定。它没有把量子态的全部熵都当作固定面积，也不等同于已指定 CFT 的引力面积。

## proposition 20.3: 本构造类的连通性与尖锐容量

更一般地，取有限连通无自环图 $\Gamma=(V,E)$，每条边两个 $d$ 维半边寄存器，每个顶点允许固定的本地幺正。将边划为固定最大纠缠的 $\mathsf F$ 和独立逻辑重复编码的 $\mathsf S$。定理 20.2 的全部区域结论仍成立。每个非空真块区域的面积严格为正，当且仅当固定边子图 $(V,\mathsf F)$ 连通。在此条件下

$$
\boxed{\log_dK=|\mathsf S|\le |E|-|V|+1=b_1(\Gamma).}
$$

选取固定边为任意生成树即达到该构造类的界。

**证明。** 定理 20.2 的逐边偏迹不使用顶点度数。所有非平凡割都有固定边等价于固定子图连通；连通图至少有 $|V|-1$ 条固定边，减去这些边给出维数界。生成树达到最少固定边数。证毕。该界只适用于明确写出的固定／自由重复连接构造，不是任意图上量子纠错码的容量定理。$b_1$ 是指定网络的环秩，也不是第 17 节无法由熵识别的曲面亏格。

## corollary 20.4: 原单环中的非平凡共同子码

对原单环，选任意一个内部历史 $j\in\{1,\ldots,L-1\}$ 为唯一自由寄存器。其余历史固定为 $|+_d\rangle$。这得到同一 $d$ 维码，对每个非空真完整块区域及所有码内密度矩阵满足定理 20.2，并有 $f_A\ge1$。这是本固定／自由连接类在所有块割均为正面积条件下的最大逻辑维数。它与第 18 节固定细腿交错划分的 $d^2$ 维最优码采用不同区域要求，不能混同。

## 21. 共同子码在原两参数粗化下闭合

本节沿用原 $\mathcal R^{(L)}_{D,d}$ 和 $\mathcal S_{\Pi,d}$，不为各区域重新选择通道。对空间分割 $0=t_0<\cdots<t_r=L$，定义粗自由集

$$
\mathsf S_\Pi=\{j\in\{1,\ldots,r-1\}:t_j\in\mathsf S\}.
$$

令 $\operatorname{tr}^{\mathsf S}_{\Pi}$ 从原自由寄存器中丢弃不在宏块边界的寄存器，并按 $t_j\mapsto j$ 重标。

## theorem 21.1: 受约束码的全输入粗化

对 $d\mid D$ 和所有自由逻辑密度矩阵，

$$
\mathcal R^{(L)}_{D,d}\mathcal E^{\mathsf S}_{D,L}
=\mathcal E^{\mathsf S}_{d,L}Q_{D,d}^{\otimes|\mathsf S|},
$$

$$
\mathcal S_{\Pi,d}\mathcal E^{\mathsf S}_{d,L}
=\mathcal E^{\mathsf S_\Pi}_{d,r}\operatorname{tr}^{\mathsf S}_{\Pi}.
$$

嵌套空间粗化、嵌套精度粗化及二者的交换继续在这些码族上成立，包括与任意外部参考纠缠的输入。若唯一自由边作为宏块边界保留，非平凡的 $d$ 维逻辑系统也被保留；若它落在宏块内部并被丢弃，则粗码退化为相应的一维固定态码。

**证明。** 数字分解精确满足 $W|+_D\rangle=|+_d\rangle\otimes|+_{D/d}\rangle$，故 $Q_{D,d}$ 把每个冻结历史态送到同一冻结态。自由历史上的作用正是 $Q$。空间偏迹对保留的冻结历史维持 $|+_d\rangle$，对被删冻结历史贡献迹一，对被删自由历史执行真实偏迹。因此作为历史通道有

$$
Q^{\otimes(L+1)}\operatorname{Ad}_{F_{D,L,\mathsf S}}
=\operatorname{Ad}_{F_{d,L,\mathsf S}}Q^{\otimes|\mathsf S|},
$$

$$
\operatorname{ret}_\Pi\operatorname{Ad}_{F_{d,L,\mathsf S}}
=\operatorname{Ad}_{F_{d,r,\mathsf S_\Pi}}\operatorname{tr}^{\mathsf S}_{\Pi}.
$$

代入定理 12.2、16.2 已在全输入上证明的交织关系即得。全空间通道的严格复合和交换自动限制到此共同族；这一步使用的是已验证的子空间保持关系。固定边连通性在宏块收缩后仍成立，因为连通固定图的商图仍连通，所以每个非平凡粗块割的面积仍为正。证毕。

这里得到的是一个共同码族，允许空间粗化按其保留的逻辑自由度改变码维数。没有声称任意丢弃自由寄存器的操作还能无损保存该寄存器。三进情况下仍沿用 $\alpha_L=L\bmod2$ 的局部相位调整；其作用只涉及已冻结的缝合历史，不破坏上述子空间保持性。

## 22. 何时全部输入都具有同一分辨率的几何熵表示

精确的面积加代数熵公式，不自动意味着全部边界熵属于纯面积全息熵锥。[CSW25] 将熵不等式的饱和与特定纠错访问结构联系起来；[CS26] 在其收缩法及静态几何假设范围内进一步联系到纠缠楔深度与重整化。本节对定理 20.3 的明确连接码给出全输入几何适用性的充要分类，直接用 [HHM11] 的单配性和 [HEC15] 的非负图表示证明。

记 $W\subseteq V$ 为至少接触一条自由边的顶点集，$w=|W|$。所谓“几何熵表示”只表示全部完整块区域熵由同一个非负加权图的割同时实现，因而属于相应全息熵锥；对混合态允许加一个整体纯化参考终端。图可随输入态变化。此定义不包含微观态等价、体局部动力学或给定 CFT 对偶。

## theorem 22.1: 纯输入与任意混合输入的不同阈值

对固定／自由连接码，

$$
\text{每个纯逻辑输入均有全部块区域的几何熵表示}
\quad\Longleftrightarrow\quad w\le3,
$$

$$
\text{每个逻辑密度矩阵均有该几何熵表示}
\quad\Longleftrightarrow\quad w\le2.
$$

**证明。** 撤去顶点本地幺正后，全部冻结边与自由编码态张量分离。冻结边对任意区域贡献固定图割，对任意三个互不相交区域的 $I_3$ 贡献为零。

若 $w\le3$ 且逻辑输入纯，自由部分只支撑于至多三个块。三方纯态的熵向量由三角图实现：三个顶点的边权取

$$
a_{ij}=(S_i+S_j-S_k)/2\ge0,
$$

其中 $i,j,k$ 不同；非负性来自纯性 $S_{ij}=S_k$ 和次可加性。两方和一方是退化情形。加上冻结边图便同时重现任意块并集的熵。

若 $w\ge4$，在所有自由逻辑寄存器上输入 $\sum_x\sqrt{p_x}|x\rangle^{\otimes|\mathsf S|}$，$H(p)>0$。每个接触自由边的块保留至少一份可区分标签 $x$，故自由输出局部等价于 $w$ 方 GHZ$(p)$。将 $W$ 分成四个非空块组，得到 $I_3=H(p)>0$；冻结边的贡献为零，[HHM11] 排除共同几何表示。这证明纯输入条件必要。

对混合输入，若 $w\le2$，把自由输出连同一个整体参考 $R$ 纯化为三方纯态。同样的非负三角图加冻结图即可表示全部物理区域及其参考补集熵。若 $w\ge3$，取逻辑混合态

$$
\rho=\sum_xp_x\bigl(|x\rangle\langle x|\bigr)^{\otimes|\mathsf S|}.
$$

自由输出在每个接触顶点上都是同一个经典标签。将 $W$ 分成三个非空组，七项熵全部为 $H(p)$，即使取三个组的全集也一样，因此 $I_3=H(p)>0$。加入冻结边不改变该缺口。证毕。

该分类适用于指定连接构造的整个输入空间。它没有将一般纠错码的全息性化为顶点数，也没有用只检查某个参考态的 MMI 代替全输入证明。

## corollary 22.2: 单环最优共同码的显式几何图

定理 20.4 的唯一自由边连接块 $u,v$。对任意逻辑密度矩阵 $\rho$，记

$$
h=S(\Delta\rho),\qquad s=S(\rho),\qquad 0\le s\le h.
$$

全部物理块熵由下列一个图同时实现：冻结边权仍为 $\log d$，另加入三角图

$$
\boxed{w_{uv}=h-s/2,\qquad w_{uR}=w_{vR}=s/2.}
$$

三条权都非负。纯输入时 $s=0$，只需给自由边赋权 $h$，参考终端可去掉；均匀相干输入 $|+_d\rangle$ 时恢复原块环的全部边权 $\log d$。

**证明。** 自由重复编码的单端态为 $\Delta\rho$、双端态与 $\rho$ 等距，因此区域包含零个、一个、两个端点时，自由贡献分别为 $0,h,s$。所列图割逐项相同。$s\le h$ 来自计算基退相干的熵不减。全部区域共用这一个图，而非逐区域拟合权重。证毕。固定面积仍是 $f_A\log d$，上述输入依赖边权表示逻辑熵贡献，不能把两者混称为同一个固定面积算符。

## corollary 22.3: 增加第二条自由连接的受控反例

在四环上释放 $x_1,x_3$ 两个不相邻自由历史，输入 $\sum_x\sqrt{p_x}|x,x\rangle$。自由部分是四块 GHZ，冻结部分是两条 Bell 边，所以聚合后的七项熵为 $b+s$，其中 $b$ 是冻结边割向量，$s$ 是第 19 节的等熵向量。其到 $\mathcal C_3$ 的一致距离仍精确为 $H(p)/7$：下界由 $I_3(b)=0$ 得到，上界由 $b$ 加第 19.2 节的 $K_4$ 图达到。故固定面积子码的任意扩充并不保持几何适用性。

## 23. 共同码的局部认证与边界

## proposition 23.1: 码空间父 Hamiltonian

在定理 20.3 的解码半边寄存器上，冻结边投影为 $P_e=|\phi_e\rangle\langle\phi_e|$，自由边投影为

$$
P_e^{\mathrm{rep}}=\sum_{x=0}^{d-1}|x,x\rangle\langle x,x|.
$$

令 $U$ 为各顶点本地幺正之积，定义

$$
H_{\mathsf S}=U\left[\sum_{e\in\mathsf F}(I-P_e)
+\sum_{e\in\mathsf S}(I-P_e^{\mathrm{rep}})\right]U^*.
$$

各项对易且只作用于相邻顶点块；零能空间恰为共同码，维数 $d^{|\mathsf S|}$，单位系数下谱隙为一。能量 $k$ 的重数由多项式

$$
\sum_k m_k z^k=
[1+(d^2-1)z]^{|\mathsf F|}
[d+(d^2-d)z]^{|\mathsf S|}
$$

给出。

**证明。** 各边半边寄存器互不重叠，冻结投影秩一，自由重复投影秩 $d$。零空间及全谱由独立因子的和直接给出，本地幺正不改变谱及零空间。证毕。对三维三环的一条自由边，重数为 $(3,54,288,384)$，地面简并三重，区别于第 13 节只认证一个纯态的 Hamiltonian。

设实际态 $\sigma$ 的总能量至多 $\varepsilon\le1/4$，码投影为 $P_{\mathsf S}$。则 $\operatorname{Tr}(P_{\mathsf S}\sigma)\ge1-\varepsilon$。取归一化投影态 $\sigma_0=P_{\mathsf S}\sigma P_{\mathsf S}/\operatorname{Tr}(P_{\mathsf S}\sigma)$，存在同一个逻辑态 $\rho$ 使 $\sigma_0=\mathcal E^{\mathsf S}(\rho)$，且 $\tfrac12\|\sigma-\sigma_0\|_1\le\sqrt\varepsilon$。因此对每个非空块区域 $A$，物理维数 $N_A$，同时有

$$
|S(\sigma_A)-f_A\log d-S_{\mathcal M_A}(\rho)|
\le\sqrt\varepsilon\log(N_A-1)+h_2(\sqrt\varepsilon).
$$

该界由谱隙、投影的纯化保真度及 [Aud07] 推出。认证允许未知且混合的逻辑输入；仅测总能量不会给出逻辑熵的数值，还需恢复或估计相关逻辑态。统计误差、测量样本数和高维门成本均需另行控制，未进行硬件验证。

**几何结论的精确范围。** 第 20–22 节在完整双腿块这一固定分辨率上给出同一非平凡子码、全部区域的正面积与互补恢复、全部输入的几何熵表示，以及空间和精度通道保持的共同族。切开本地 $M_d$ 的任意细腿区域需要第 24 节的独立 Weyl 分析，不能沿用逐边偏迹证明。单条自由逻辑边的完整量子态由其两个端点块联合恢复，单端仅见对角信息，故不能把此构造称为保护任意单块擦除或具有深体局域性的码。

固定边面积图是一棵树时已能得到当前单环的容量最优解，全部纯输入的块熵可由成对边权表示，因而各四组的 MMI 饱和。它仍属于短程连接结构，未产生临界 CFT、独立引力动力学或可识别的双曲扭转。[CSW25, CS26] 提醒的深度及访问结构约束不能从几何熵存在性中省略；其一般论断也依赖原文的静态及收缩法等假设。第 24 节计算细腿恢复，第 25 节另用相同局部张量构造深度增长的树码；它们的范围与剩余引力义务集中在第 26 节。固定辅助纠缠、简单图连通性和父 Hamiltonian 属于已有方法；本卷具体共同子码、支持阈值分类及其组合尚未全面排除文献等价形式，不认领具名外部猜想或原始引力 RT 已解决。

## 24. 从完整顶点块到任意细腿：显式 Weyl 恢复计算

本节固定第 20.4 节的一个自由历史 $j\in\{1,\ldots,L-1\}$，其余历史仍为 $|+_d\rangle$。$d\ge3$ 为任意奇数，$n=2L$。区域现在允许为 $n$ 条物理腿的任意子集，因而可以切开原顶点块。整个码、逻辑坐标和区域映射同时固定。稳定子码的互补恢复已有 [PRR22] 基础，任意局部维数下的标量面积限制见 [Cao24]；以下给出当前循环模环的实际生成元、同余算法和完整谱，不把一般稳定子原理认领为新增定理。

**定义 24.1（原振幅的相空间表示）。** 令 $B:R_d^{L+1}\to R_d^{2L}$ 为第 4 节输出矩阵，$B_{2i,i}=B_{2i+1,i}=B_{2i,i+1}=1$、$B_{2i+1,i+1}=2$，其余为零。定义左逆 $T$：第零行在第零块为 $(2,-1)$，第 $i$ 行在第 $i-1$ 块为 $(-1,1)$，$1\le i\le L$，因此 $TB=I$。令对称矩阵 $Q$ 满足 $Q_{00}=2\alpha$、$Q_{0L}=Q_{L0}=1$，其余为零。对 $u,z\in R_d^n$，使用

$$
W(u,z)=\omega_d^{u\cdot z/2}X^uZ^z,
\quad X^u|x\rangle=|x+u\rangle,
\quad Z^z|x\rangle=\omega_d^{z\cdot x}|x\rangle.
$$

$1/2$ 是模 $d$ 的逆元。相空间配对为 $[(u,z),(u',z')]=z\cdot u'-u\cdot z'$。令 $N_i$ 在块 $i-1$ 取 $(-1,1)$、在块 $i$ 取 $(-2,1)$，其余为零，$1\le i<L$。取稳定子标签群

$$
\mathscr S=\operatorname{span}_{R_d}\{(Be_i,T^TQe_i):i\ne j\}
+\operatorname{span}_{R_d}\{(0,N_i):1\le i<L\}.
$$

逻辑 $X,Z$ 的标签可选

$$
\ell_X=(Be_j,0),\qquad \ell_Z=(0,T^Te_j).
$$

## lemma 24.2: 稳定子与正交群

$\mathscr S$ 各向同性，大小为 $d^{n-1}$，其 Weyl 算符的共同 $+1$ 空间恰为原单自由历史码。其正交群为

$$
\mathscr N=\mathscr S^\perp=\mathscr S\oplus R_d\ell_X\oplus R_d\ell_Z.
$$

**证明。** $N_iB=0$，$TB=I$，$Q$ 对称，且 $Qe_j=0$，直接给出所有交换关系。平移 $x_i$、$i\ne j$ 时，原振幅二次相位的变化为 $x^TQe_i+Q_{ii}/2$，正是对应 Weyl 算符的相位；$N_i$ 则检查相邻历史标签的一致性。因此它们实际固定原码。平移生成元经 $T$ 映射到不同的 $e_i$，相位一致性行独立且张成 $\ker B^T$，故稳定子有 $d^{n-1}$ 个元素。其平均为秩 $d$ 的投影，而原编码已是 $d$ 维等距，二者像空间相等。两个逻辑标签与稳定子独立，并具有单位辛配对，给出 $d^{n+1}$ 个正交标签；有限完美配对保证 $|\mathscr S^\perp|=d^{2n}/|\mathscr S|$，故穷尽正交群。证毕。这里使用有限群基数，不把 $R_d$ 当作域。

## theorem 24.3: 任意细腿区域的最大代数与熵

对物理腿集合 $A$，记 $\mathscr F_A$ 为仅在 $A$ 有支撑的相空间标签，定义

$$
\mathscr S_A=\mathscr S\cap\mathscr F_A,\qquad
E_A=\{(a,b)\in R_d^2:\exists s\in\mathscr S,\ s+a\ell_X+b\ell_Z\in\mathscr F_A\}.
$$

令

$$
Z_A=E_A\cap E_A^\perp,\quad c_A=|Z_A|,\quad
r_A=\sqrt{|E_A|/c_A},\quad t_A=\frac d{c_A r_A},
$$

$$
R_A=\frac{d^{|A|}}{|\mathscr S_A|},\qquad
m_A=\frac{R_A}{c_A r_A}.
$$

这些数均为正整数，且 $E_{\bar A}=E_A^\perp$。区域的最大可恢复逻辑代数是实际逻辑 Weyl 算符的线性包

$$
\mathcal M_A=\operatorname{span}\{W_{\rm log}(a,b):(a,b)\in E_A\}
\simeq\bigoplus_{z=1}^{c_A}M_{r_A}(\mathbb C)\otimes I_{t_A}.
$$

对任意逻辑密度矩阵，写其在该代数上的标准分块限制为 $\oplus_zp_z\rho_z$，实际边缘态有区域内的支撑等距正规形

$$
\boxed{\mathcal N_A(\rho)\simeq
\bigoplus_{z=1}^{c_A}p_z\rho_z\otimes I_{m_A}/m_A,}
\qquad\mathcal N_A=\operatorname{Tr}_{\bar A}\circ\mathcal E^{\{j\}}_{d,L}.
$$

因此对所有细腿区域和全部输入，

$$
S(\mathcal N_A\rho)=\log m_A+S_{\mathcal M_A}(\rho),\qquad
\mathcal L_A=(\log m_A)I_d.
$$

互补恢复、区域包含下的逻辑代数包含、以及边界与相应代数相对熵的等式同时成立。正常支持上的完整谱由该正规形给出，不仅是熵数值。

**证明。** 稳定子平均给出

$$
\mathcal N_A(I_d/d)=P_A/R_A,\qquad
P_A=|\mathscr S_A|^{-1}\sum_{s\in\mathscr S_A}W_A(s).
$$

由于非恒等 Weyl 的迹为零，$P_A$ 的秩为 $R_A$。任意局部 Weyl 的码压缩，若标签不在 $\mathscr N$ 则为零；在 $\mathscr N$ 中则为一个逻辑 Weyl。因此实际局部压缩算符恰由 $E_A$ 张成，乘法闭合。有限辛配对给出

$$
(\mathscr N\cap\mathscr F_A)^\perp=\mathscr S+\mathscr F_{\bar A}.
$$

在 $\mathscr N/\mathscr S$ 中取像便得到 $E_{\bar A}=E_A^\perp$。结合 [BKK07] 压缩错误交换子判据，这些就是最大可恢复代数，而非只是一组选出的可恢复算符。

限制 Weyl 乘法的中心是 $Z_A$；商群 $E_A/Z_A$ 的交换配对非退化。有限扭曲群代数因而有 $c_A$ 个简单块，每块维数 $r_A$，其中 $c_A r_A^2=|E_A|$。也可逐个中心特征用正交幂等元直接得到这一分解。逻辑空间和物理支撑 $P_A$ 上，每个非恒等逻辑标签的归一化迹均为零；因此中心特征等权，各简单块的表示重数分别为 $t_A$、$m_A$。两者的整数性由实际表示的维数给出，不依赖核的自由性。局部 Weyl 期望逐项等于同一个逻辑 Weyl 期望，其余压缩项为零，故完整边缘态必须是所列分块态，各重数因子最大混合。熵与相对熵由此直接计算。证毕。

**可执行的精确算法。** 将引理 24.2 的 $n-1$ 个稳定子生成元堆为行矩阵 $S$，末尾加 $\ell_X,\ell_Z$ 得 $H$。解 $H_{\bar A}^T y=0\pmod d$ 并投影到最后两个系数，就得到 $E_A$；解 $S_{\bar A}^Ty=0\pmod d$ 则给出 $|\mathscr S_A|$。这里下标保留补集的位移和相位列。整数 Smith 正规形的非零对角元 $s_i$ 每个贡献 $\gcd(s_i,d)$ 个核选择，零列贡献 $d$，因此复合模数与非自由子群也可精确处理。

## corollary 24.4: 正面积与精确距离

若 $\alpha$ 采用第 5 节全区域参考态饱和规则，则每个非空真细腿区域都有 $\log m_A\ge\log d$。无论 $\alpha$ 如何，当前单自由历史码的距离恰为二：任意一条已知位置物理腿的擦除可精确纠正，但存在两条腿的擦除不能精确恢复完整逻辑态。

**证明。** 每条物理腿都出现于某个 $N_i$，系数为单位 $\pm1$ 或 $\pm2$；因此支撑于单腿并与稳定子交换的 Weyl 必须没有位移部分。该腿至少依赖一个冻结历史，系数为单位，故相位部分也只能为零。所以单腿边缘是 $I_d/d$，与全部逻辑输入及参考纠缠无关。另一方面 $\ell_Z$ 的代表正是第 $j-1$ 块两腿上的 $Z^{-1}\otimes Z$，是支撑二的非标量逻辑算符，给出距离上界。

正面积方面，互补恢复的固定纯辅助态使 $m_A=m_{\bar A}$；也可由有限群阶数直接验证。单腿及其补集面积为 $\log d$。其余非平凡区域在原图的最小割至少为二，因为原环内部边不是桥，单边割只能隔离一个边界叶。均匀逻辑输入纯态 $|+_d\rangle$ 的边界态满足第 5 节参考 RT，而任何一个 $d$ 维逻辑系统的标准代数熵至多为 $\log d$。故 $\log m_A\ge[m(A)-1]\log d\ge\log d$。证毕。这是细分区域的码面积正性；未证明新函数 $A\mapsto\log m_A$ 本身等于原图的同一个几何最小割。

例如 $d=L=3,j=1,\alpha=1$ 时，六条腿的 64 个区域中，20 个只恢复标量，24 个恢复一个经典三维对角代数，20 个恢复整个 $M_3$。六个单腿区域均为第一类，存在两腿经典泄漏，最少四腿可恢复完整量子信息。中间的经典代数可以对应不同 Weyl 基，不能统一替换成同一个计算基标签。环长增加仍保留支撑二的逻辑算符，因此这个原模型不提供随环长增长的纠错距离。

## 25. 用已有局部编码构造随深度增长的精确 RT 树

为越过上一节的固定距离限制，本节改变网络几何，采用已有 `QutritThresholdSharing.lean` 的三份秘密共享编码。它不被冒充成原单环的局部基变换；是以同一个四腿完美张量为节点的另一种可证明模型。量子秘密共享和完美张量全息码的成熟来源为 [CGL99, HaPPY]。以下给出循环奇数模环版本的实际解码、全部叶区域的通道递推及独立树割对应。

**定义 25.1。** 对任意奇数 $d\ge3$，令

$$
W_d|s\rangle=d^{-1/2}\sum_{t\in R_d}|t,t+s,t+2s\rangle.
$$

其 $d=3$ 情形就是所引 Lean 文件的编码。第一、第二输出 $(a,b)$ 的解码为 $(s,c)=(b-a,2b-a)$；第二、第三输出 $(b,c)$ 的解码为 $(s,a)=(c-b,2b-c)$；第一、第三输出 $(a,c)$ 的解码为 $(s,b)=((c-a)/2,(a+c)/2)$。每个都是模环上的置换。将任意一对输出与剩下那一份按此解码，整体恰为原逻辑态与 $\Phi_d$ 的张量积。故单份通道是 $\rho\mapsto I_d\operatorname{Tr}(\rho)/d$，任意两份通道等距于 $\rho\otimes I_d/d$，三份保留原等距编码；这些是矩阵单位上的通道恒等式，包含参考系统。

递归定义 $W_d^{(0)}=I_d$，

$$
W_d^{(h+1)}=(W_d^{(h)})^{\otimes3}W_d.
$$

深度 $h$ 编码一个根逻辑寄存器到 $N_h=3^h$ 条物理叶腿。树的分支数、深度与每条腿的维数是不同参数。

## theorem 25.2: 全部细叶区域的精确量子 RT

对叶区域 $A$，从叶向根定义两个整数 $f(A)\in\{0,1\}$、$a(A)\ge0$。单叶处 $f=1$ 当且仅当该叶在 $A$，且 $a=0$。内部节点的三个子树数据为 $(f_i,a_i)$，令 $m=f_1+f_2+f_3$，递推

$$
f=\mathbf1_{m\ge2},\qquad
a=a_1+a_2+a_3+\min(m,3-m).
$$

对任意根逻辑密度矩阵，区域通道存在与输入无关的区域解码，使其在实际支撑上为

$$
\mathcal N_A^{(h)}(\rho)\simeq
\begin{cases}
I_{d^{a(A)}}/d^{a(A)},&f(A)=0,\\
\rho\otimes I_{d^{a(A)}}/d^{a(A)},&f(A)=1.
\end{cases}
$$

因此同一个树码对全部叶区域、所有输入满足

$$
\boxed{S(\mathcal N_A^{(h)}\rho)=a(A)\log d+f(A)S(\rho).}
$$

$f=0$ 的最大可恢复代数为标量，$f=1$ 为整个 $M_d$。互补区域满足 $f(\bar A)=1-f(A)$、$a(\bar A)=a(A)$，所以精确互补恢复成立，且这里没有仅能恢复一个经典基的中间情况。

**证明。** 对子树应用归纳的通道正规形，包括它与其他子树及参考系统的关联。留下 $m$ 份父节点输出和独立最大混合辅助因子。$m=0,1,2,3$ 时定义 25.1 的精确通道分别提供零份、一份最大混合辅助、根逻辑加一份最大混合辅助、根逻辑等距，得到递推。正规形同时证明最大性及互补关系；后者也直接由 $m\mapsto3-m$ 验证。证毕。因为使用通道恒等式，归纳没有假设父节点的三个份额相互独立。

## theorem 25.3: 与独立定义的最小割严格一致

在根三叉树上给每条几何边权重 $\log d$，叶按 $A,\bar A$ 固定标记，内部顶点自由分侧。则 $a(A)$ 是不附加参考终端时的单位权最小割，$f(A)$ 给出唯一最优的根所在侧。对混合根态另加一个参考终端 $R\in\bar A$，以权重 $S(\rho)$ 的边连接根，整个同一加权树的全部物理叶区域割值恰为

$$
a(A)\log d+f(A)S(\rho).
$$

**证明。** 动态规划中，每个子树经过其父边后向父节点传递的两侧代价，是自身最优代价加 $\mathbf1_{\text{父侧}\ne f_i}$。这是因为三个子代价在最优侧和相反侧的差为奇整数一或三，加入一条单位父边后差被截为一；叶终端同样传递单位错侧代价。父节点取两侧较小值，正是 $\min(m,3-m)$，且三子数为奇数使最优根侧唯一。根的两侧原代价差至少一。新增参考边权除以 $\log d$ 属于 $[0,1]$，因 $S(\rho)\le\log d$，所以最优值只增加 $f(A)S(\rho)$；端点等号可能产生并列极小，但不改变最小值。证毕。几何图及区域一次固定，不逐区域拟合边权；唯一输入依赖边是承载根混合熵的参考边。

## corollary 25.4: 可扩展擦除保护

深度 $h$ 树码的距离恰为 $2^h$，最少 $2^h$ 条叶可以完全恢复根逻辑态，任意少于 $2^h$ 条已知位置叶的擦除均可精确纠正。独立叶擦除概率为 $q$ 时，根恢复失败概率满足

$$
p_0=q,\qquad p_{h+1}=3p_h^2-2p_h^3.
$$

因此 $q<1/2$ 时失败概率随深度趋零，$q>1/2$ 时趋一，$q=1/2$ 为固定点。

**证明。** 最小授权集必须在至少两个子树中各有一个授权集，故大小递推为 $2^h$；反向逐层选两子树达到。互补自对偶性表明一个擦除集不可纠正，当且仅当它本身授权，因此最小不可纠正擦除集也是 $2^h$。相互独立子树的失败多数表决给出概率递推；$3p^2-2p^3-p=-p(1-p)(1-2p)$ 确定极限。证毕。这里纠正的是已知位置擦除；不能将距离二的基础码声称能纠正任意未知位置单粒子错误。

每组三个叶的秘密共享逆通道可作为一个实际空间粗化层，在编码态上把 $W_d^{(h+1)}\rho(W_d^{(h+1)})^*$ 精确送到深度 $h$ 编码态，层间顺次复合也精确。该空间粗化允许同一子树三份联合操作。它没有自动证明原单环的精度通道可逐腿搬到此树；新的空间／循环精度交换关系仍需分别验证。$d=3$ 的有限根三叉树具有自然三进地址层级，与算术树可比较，但没有将地址层级本身等同于一个给定边界 CFT。

## 26. 从严格离散 RT 向引力 RT 的新增边界

第 24 节闭合原单自由历史码的任意细腿恢复与面积加代数熵公式，同时证明其距离固定为二；第 25 节用实际已有的局部秘密共享编码产生随深度增长的恢复和严格树最小割关系。后一结果是秘密共享串联与完美张量方法的明确应用，不作为此前无人证明的物理 RT 或外部开放问题结算。

新增文献约束 [Cao24] Theorem 2.1 已证明：任意局部维数的 Pauli 稳定子码，任何物理二分上的 RT 面积算符都必须与逻辑恒等成比例。非零标量面积允许存在，但不会随逻辑态变化。第 24 节的 $\log m_A I$ 和第 25 节的 $a(A)\log d I$ 都满足此限制。单纯增加稳定子树深度、改变 Clifford 缝合或串联更多稳定子编码，不能产生非标量面积；局部幺正重命名也不能绕过该结果。非平坦边界谱亦不足以绕过它，因为谱变化可以全部来自输入逻辑熵。

因此当前严格结果覆盖固定背景的离散 RT 和一部分区域恢复结构，尚未证明一个预先给定边界理论中的半经典引力公式。继续朝该目标推进时，需要至少分别验证：具有非标量面积或受控近似恢复的共同编码；不同区域的几何相容及同调；独立几何中面积与长度尺度的对应；以及边界态、连续极限和引力动力学。第 18 节的非稳定子相干分组已给出单划分入口，但将它扩展到深树的多区域，不能只保留面积的非标量性而忽略互补恢复和局部性。本卷尚未解决这项组合义务。

一般稳定子互补恢复、辅助纠缠、秘密共享和串联码原理分别归属 [PRR22, Harlow, CGL99, HaPPY, Cao24]。本节对具体循环模环的恢复子群、实际熵正规形和有限树的可执行验证承担结果责任；未完成等价文献形式的全面优先权排查，未作 Lean 内核或独立多模型审查。

## 27. 几何读数的动力学闭合与原码内的同谱反例

本节将本卷的区域熵／恢复结构与 `SYMPLECTIC_PREDICTIVE_COMPLETION.md` 第 1–2 节的预测闭合关系连接。对象保持为既有编码；几何读数、完整量子态和动力学生成元分开定义。所有有限量子公式取 $\hbar=1$；第 30 节恢复有量纲的 $\hbar$。本节没有把静态熵图当作已经闭合的动力学状态。

## proposition 27.1: 观测纤维上的速度条件

设 $q:M\to G$ 为光滑满射次浸没，$X$ 为 $M$ 上的光滑向量场。存在 $G$ 上的光滑向量场 $Y$ 使 $Dq\,X=Y\circ q$，当且仅当 $Dq_xX(x)$ 在每个完整纤维 $q^{-1}(g)$ 上相同。可微区间内的确定性观测演化因此要求同一读数有同一速度。

**证明。** 必要性由等式直接给出。充分性据纤维值定义 $Y(g)$；每点附近的光滑局部截面使 $Y=Dq\,X\circ s$ 光滑，纤维一致性保证局部定义相容。由链式法则，投影后的积分曲线满足该方程。证毕。即使熵映射不是次浸没，同读数不同速度仍足以排除 $\dot g=F(g)$；它是必要性而无需正则秩假设。本条件是线性关系 $OA=KO$ 的非线性对应，属于标准下降条件；当前实例承担下述反例的具体内容。

## theorem 27.2: 全部区域同谱、同一局部生成元、相反熵速度

取第 20、24 节原单自由历史码 $V=V_{3,3,\{1\}}$，$\alpha=1$，六腿依次为 $(a_0,b_0,a_1,b_1,a_2,b_2)$。令逻辑

$$
Z=\operatorname{diag}(1,\omega_3,\omega_3^2),\quad
h=|0\rangle\langle1|+|1\rangle\langle0|,
$$

$$
|\psi\rangle=\frac{\sqrt3}{2}|0\rangle+\frac i2|1\rangle,
\quad \rho=\frac12|\psi\rangle\langle\psi|+\frac16I_3,
\quad\widetilde\rho=Z\rho Z^*.
$$

二者严格正定。对每个物理腿集合 $A$，$[V\rho V^*]_A$ 与 $[V\widetilde\rho V^*]_A$ 的完整谱相同。用同一逻辑演化 $\rho(t)=e^{-ith}\rho e^{ith}$ 及其带波浪版本，对区域 $B_0=\{a_0,b_0\}$，

$$
\left.\frac{dS_{B_0}(\rho(t))}{dt}\right|_0
=\frac{\sqrt3}{4}\log\frac7{13}<0,
\qquad
\left.\frac{dS_{B_0}(\widetilde\rho(t))}{dt}\right|_0
=-\frac{\sqrt3}{8}\log\frac7{13}>0.
$$

该演化可由仅支撑于前两个相邻顶点块的四腿 Hermitian 算符精确实现。

**证明。** 原振幅给出 $\overline Z=Z_0^{-1}Z_1$、$\overline X=X_0X_1^2X_2X_3$ 满足 $\overline ZV=VZ$、$\overline XV=VX$。$\overline Z$ 是单腿幺正的乘积，所以所有区域的边缘态分别局部幺正等价。令

$$
\overline P_0=(I+\overline Z+\overline Z^2)/3,\qquad
\overline H=\overline P_0\overline X^{-1}+\overline X\overline P_0.
$$

它是四腿 Hermitian 算符并满足 $\overline HV=Vh$，故实现同一实际物理演化，不只是给码空间取一个无局部性声明的压缩算符。

由第 20.2 节或直接偏迹，$S_{B_0}(V\rho V^*)=\log3+H(\operatorname{diag}\rho)$。两输入具有相同的对角概率 $(13,7,4)/24$，但 $\rho_{01}=-i\sqrt3/8$，而 $\widetilde\rho_{01}=\omega_3^{-1}\rho_{01}$。$\dot p_0=-2\operatorname{Im}\rho_{01}$、$\dot p_1=-\dot p_0$、$\dot p_2=0$，所以 $\dot H=\dot p_0\log(p_1/p_0)$，代入得结论。证毕。

因此，全部瞬时区域谱组成的读数也不足以定义自治几何速度；只对这些谱再作确定性图重建无法消除这个区别。这里只固定了同一个物理 Hamiltonian，没有同时将 Hamiltonian 作 $\overline Z$ 共轭；这是两种真实初态，不是改变整个实验坐标的规范等价。反例不排除时间历史、额外相位观测、随机动力学或更高阶状态表示。

## corollary 27.3: 可取得的相位电流补全

对上述 $h$，记

$$
r=\rho_{00}+\rho_{11},\quad z=\rho_{00}-\rho_{11},\quad
j=-2\operatorname{Im}\rho_{01},\quad u=2\operatorname{Re}\rho_{01}.
$$

直接交换子计算给出 $\dot r=\dot u=0$、$\dot z=2j$、$\dot j=-2z$。在对角概率正的区间，

$$
\dot S_{B_0}=j\log\frac{r-z}{r+z}.
$$

因此给定 $r$，$(z,j)$ 为该读出的自治振子状态，可采用 $dz\wedge dj$ 和 Hamilton 函数 $z^2+j^2$。它不是完整任意 qutrit 状态的最小坐标证明，也不宣称所有区域熵只由这两个数决定。$j$ 是明确的逻辑 Hermitian 观测期望，可通过第 24 节的授权区域恢复取得。任意有限维线性量子动力学还可对所选观测取交换子迭代线性包，得到至多 $d^2$ 维的预测闭包；这是统一预测卷的有限可观测性接口。

## 28. 面积变化、区域自治和精度相容的共同限制

## proposition 28.1: 保持区域代数的连续流固定中心面积

固定有限维逻辑 $*$-代数 $\mathcal M$ 及其中心内的自伴面积算符 $\mathcal L$。若 $U_t$ 为从恒等出发的连续单参数幺正群，且对全部 $t$ 有 $U_t^*\mathcal M U_t=\mathcal M$，则 $U_t^*\mathcal L U_t=\mathcal L$。

**证明。** 共轭必须将有限集合中的最小中心投影置换到同一集合。连续路径不能改变离散置换，且起点为恒等，因此每个最小中心投影分别固定。中心算符是这些投影的线性组合，结论成立。证毕。该命题不要求稳定子；“面积非标量”本身还不足以在区域观测自治的连续闭系统中获得面积变化。时间依赖码、变化的区域代数、开放演化不在本命题的假设中。

若对一个 qutrit 同时要求 $Z$ 基与互补 $W$ 基的完整对角代数各自被连续幺正流保持，生成元必须在两个代数中同时对角。互补基下，第一组对角算符的另一组对角元都是同一平均值，故这样的生成元只能是标量。此处约束的是两个区域的观测代数自治，不是单独的静态可恢复性。

## corollary 28.2: 现有深树在根幺正下的几何盲性

第 25 节根分享树对任意区域有通道正规形，谱由固定最大混合因子及零份或一份根密度矩阵构成。因此任意根逻辑幺正演化保持全部叶区域的完整谱。深度和擦除距离的增长本身不改变这一结论。它是该树正规形的直接应用；不认领一般“幺正演化不能改变纠缠”的错误命题。根输入更改、不同逻辑子系统耦合或编码变化需另行研究。

## proposition 28.3: 原精度塔的自治生成元条件

在数字分解 $W:\mathbb C^D\to\mathbb C^d\otimes\mathbb C^e$、$D=de$ 下，令 $Q=\operatorname{Tr}_e\operatorname{Ad}_W$。给定自伴 $H_D,H_d$，以下关系对所有输入矩阵成立，当且仅当存在自伴 $K_e$ 使

$$
Q(-i[H_D,\rho])=-i[H_d,Q\rho],
\qquad
WH_DW^*=H_d\otimes I_e+I_d\otimes K_e.
$$

**证明。** 对偶关系要求 $[WH_DW^*,O\otimes I]=[H_d,O]\otimes I$ 对所有 $O$ 成立。故差算符位于完整矩阵代数 $M_d\otimes I$ 的交换子 $I\otimes M_e$ 中；反向代入即可。证毕。这是统一预测卷完整子系统闭合条件的实际数字分解应用，不是新的一般无相互作用定理。对 $p$ 进的每级精度同时实施该条件，迭代得到各数字层生成元之和。因而真正跨层相互作用需要改变当前粗化规则、放松全输入幺正自治或保留记忆。

例如一般线性分块系统 $\dot x=Ax+Bh,\dot h=Cx+Dh$ 精确消去隐藏变量后为

$$
\dot x(t)=Ax(t)+Be^{Dt}h(0)+\int_0^tBe^{D(t-s)}Cx(s)\,ds.
$$

隐藏初态与卷积不可省略。仓库已形式化的 Schur 结合律约束分层消元的一致性；它不自动为无界场算子、噪声或任意初始相关提供额外物理性质。

**构造 28.4（原中心子码中的面积–相位动力学）。** 取第 18 节三维三角环的 $|Z|=9$，分为大小 $3$ 与 $6$ 的两组，均匀固定组内相干并将 $a,b$ 因子固定到一个计算基向量。所得二维子码仍在原物理空间内。其实际支撑坐标可写成

$$
J_c|0\rangle=3^{-1/2}\sum_{z=0}^{2}|z,z\rangle,\qquad
J_c|1\rangle=6^{-1/2}\sum_{z=3}^{8}|z,z\rangle.
$$

这仅使用第 18 节的两侧局部支撑等距，不添加物理维数。对任意逻辑输入，$p=\rho_{11}$，有

$$
S_X=h_2(p)+a(p),\qquad
\mathcal L=\operatorname{diag}(\log3,\log6),\qquad
 a(p)=\log3+p\log2.
$$

取 $h=(\Omega/2)\sigma_x$。对纯态 $\sqrt{1-p}|0\rangle+e^{i\phi}\sqrt p|1\rangle$、$0<p<1$，Schrödinger 方程等价于

$$
\dot p=-\Omega\sqrt{p(1-p)}\sin\phi,\qquad
\dot\phi=-\frac{\Omega(1-2p)}{2\sqrt{p(1-p)}}\cos\phi,
\qquad\dot a=(\log2)\dot p.
$$

**证明。** 边缘态两组支持正交，谱为 $(1-p)/3$ 的三重值和 $p/6$ 的六重值。直接计算熵得到第一式。将两振幅代入 Schrödinger 方程，概率导数及相位比导数给出后式。它也是 $dp\wedge d\phi$ 与 $E=\Omega\sqrt{p(1-p)}\cos\phi$ 的 Hamilton 流，采用 $\iota_{X_E}\omega=dE$。证毕。

这是非标量面积期望真实变化的有限模型。相同 $p$、不同 $\phi$ 可有不同面积速度，加入相位后闭合。生成元混合中心扇区，因而不保持两侧的对角恢复代数自治，符合命题 28.1。物理实现 $J_chJ_c^*$ 一般跨该划分非局部，未证明几何局域性或多区域动力学。非稳定子算子代数码可以有这种中心面积，并不与 [Magic26] 明确限定的子系统码近似恢复论证冲突。

## 29. 几何相空间、移动编码与真实曲率的区分

### 29.1 双曲模空间提供真实的几何共轭变量

对第 17 节固定拓扑、固定外边界长度的曲面，在标记的 Fenchel–Nielsen 图册中使用内部长度 $\ell_e$ 与扭转 $\tau_e$。标准 Weil–Petersson 辛形式取归一化为

$$
\omega_{\rm WP}=\sum_e d\ell_e\wedge d\tau_e.
$$

这是 Wolpert 的既有公式。本节扭转采用 $\tau_e=-\tau_e^{\rm WP25}$，因为 [WP25] 式 (1) 写为 $\sum_e d\tau_e^{\rm WP25}\wedge d\ell_e$；这样上式及随后的 Hamilton 方程使用同一符号约定。[WP25] 给出一个新的证明，固定测地边界的模空间参照 [Do10]。带固定测地边界的情形使用对应的固定边界长度辛叶，不把可变外边界参数误当已配对的自由度。

在第 17 节的短领圈开区间内，全部选定边界熵读数为 $s_A=\lambda^{-1}\min_C\sum_{e\in C}\ell_e$，与扭转无关。固定极小割组合的光滑子区间中，若自行选择的 Hamilton 函数仅依赖这些读数，即 $H=F((s_A))$，则

$$
\dot\ell_e=\partial_{\tau_e}H=0,
\qquad\dot\tau_e=-\partial_{\ell_e}H,
\qquad\dot s_A=0.
$$

这是 Hamilton 方程的直接后果，说明单靠这些面积读数作为能量函数不能生成长度变化。若选择 $H=\tfrac12\tau^TM^{-1}\tau+U(\ell)$，其中 $M>0$，则 $\dot\ell=M^{-1}\tau$，同一长度纤维上不同扭转可有不同速度。该几何 Hamilton 模型是一种明确选择，未从边界量子理论推导，也不能把 WP 扭转无证明地识别为量子态相位、Lorentz 时空的外曲率或 ADM 正则动量。

### 29.2 移动码的无泄漏输运必须含连接项

## theorem 29.1: 移动编码的精确生成元

令 $V(t):\mathbb C^k\to\mathbb C^N$ 为光滑等距，$P=VV^*$、$Q=I-P$，给定物理自伴 $H_B(t)$。所有码内初态保持在随时间移动的码空间，当且仅当

$$
Q(H_BV-i\dot V)=0,
$$

等价地 $\dot P=-i[H_B,P]$。此时逻辑生成元是

$$
h(t)=V^*H_BV-iV^*\dot V.
$$

指定任意逻辑自伴 $h(t)$ 时，一个实际物理实现为

$$
H_B=i[\dot P,P]+V\bigl(h+iV^*\dot V\bigr)V^*+QH_\perp Q,
$$

其中 $H_\perp$ 自伴。

**证明。** 对 $|\Psi\rangle=V|\psi\rangle$ 将 Schrödinger 方程分解到 $P,Q$ 两块，得到法向条件及逻辑生成元。由 $P^2=P$ 可知 $\dot P$ 纯为两侧非对角块；法向条件及其共轭恰等价于投影演化方程。$i[\dot P,P]V=iQ\dot V$，另有 $V(iV^*\dot V)=iP\dot V$，故所列 $H_BV=Vh+i\dot V$，实现全方程。证毕。忽略 $iV^*\dot V$ 只在平行框架中正确。

连接 $\mathcal A=iV^*dV$ 的曲率为

$$
\mathcal F=d\mathcal A-i\mathcal A\wedge\mathcal A
=i\,dV^*Q\wedge dV.
$$

这与 #8340 的局部观察子丛关系相同；存在环境连接时必须加 $V^*F^{\rm ambient}V$，不能省掉该项。反绝热输运原理有 [Berry09] 等已有基础。连接描述码子空间及基的运输，其曲率不自动等于物理时空的 Riemann 曲率。换局部框 $V\mapsto Vg$ 时，$h\mapsto g^*hg-i g^*\dot g$、$\mathcal A\mapsto g^*\mathcal A g+i g^*dg$，曲率协变。因此非平凡 Chern 类应沿用 #8340 的局部图册，不要求存在一个全局等距框。给定 $V(t)$ 后构造输运不等于推导了决定 $V$ 的动力学。法向耦合的不可避免强度为 $\|QH_BV\|=\|Q\dot V\|$，单位恢复后右侧乘 $\hbar$。

### 29.3 真实几何与预测几何之间还需要变分字典

量子态射影空间的辛结构与 Schrödinger 流是 [AS97] 的几何量子力学；双曲模空间的 WP 辛结构是另一个载体。把二者相连至少需给出一个明确映射 $\Phi$，检验 $D\Phi\,X_h=X_{H_g}\circ\Phi$ 及指定的 Poisson／辛配对相容。单凭面积数值、维数、相位外形或投影连接，均不能省略该映射。若目标是物理引力，相空间应由所选引力作用量、约束及边界条件决定，不能先指定任意 WP Hamilton 函数再宣称得到 Einstein 动力学。

## 30. 因果记忆如何真正进入度量方程与面积系数

本节吸收此前未写回远端的《因果记忆、质量矩阵相对熵与诱导曲率项》中的模型，重新列出必要前提。相关基础是正常双曲算子的因果 Green 理论、共同热核正规化及锥形变分 [Bar15, HK03, Cone95]。这里讨论四维低导数有效场论的相对系数，不是当前有限码已经具有该场论对偶。

### 30.1 隐藏变量的传播和度量作用不能只留一个

给定全局双曲 Lorentz 背景，正常双曲块算子及零阶局部耦合 $B$ 满足

$$
P_Vv+Bh=f,\qquad P_Hh+B^Tv=0.
$$

在指定源／初值函数空间，$h=h_{\rm hom}-G_H^RB^Tv$，所以精确可见方程为

$$
(P_V-BG_H^RB^T)v=f-Bh_{\rm hom}.
$$

记忆核保持延迟因果支持，隐藏初值项也保留。另一方面，在同一个有限模式 Euclidean 正定正规化中，Gaussian 积分同时产生 Schur 算子及隐藏行列式：

$$
\log\det\begin{pmatrix}P&B\\B^T&Q\end{pmatrix}
=\log\det Q+\log\det(P-BQ^{-1}B^T).
$$

度量若进入 $Q$，隐藏行列式就参与度量变分。只保留可见传播而丢弃此项不能定义相同的几何反作用。连续作用量必须用共同正规化和反项；实时耗散需要闭时路径与初态，不能把 Euclidean 行列式直接当延迟影响泛函。

### 30.2 同一个谱差控制相对曲率项与局部锥熵

## proposition 30.1: 相对面积系数的有限谱公式

考虑四维有限实标量场，恒定严格正定质量平方矩阵

$$
\mathsf M=\begin{pmatrix}A&B\\B^T&C\end{pmatrix},\qquad
\mathsf M_0=A\oplus C,
\qquad D_g=-\nabla_g^2I+\xi RI+\mathsf M.
$$

比较模型具有同样的场、曲率耦合、正规化与有限重整化处方，仅将跨块质量耦合关闭。设 Euclidean 作用量线性曲率项为 $\Gamma_{E,R}=-\kappa\int\sqrt g R$。在低曲率、低导数展开的这一项中，

$$
\Delta\kappa=\frac{\hbar}{32\pi^2}(1/6-\xi)\,\mathcal I,
\quad
\mathcal I=\operatorname{tr}(\mathsf M\log\mathsf M-\mathsf M_0\log\mathsf M_0)
=\operatorname{tr}(\mathsf M)\,D\left(\frac{\mathsf M}{\operatorname{tr}\mathsf M}\middle\|\frac{\mathsf M_0}{\operatorname{tr}\mathsf M}\right).
$$

对一个有适当平滑锥正规化的静态分岔视界截面 $\Sigma$，只取同一局部曲率项的复制熵，则

$$
\boxed{\Delta S^{(R)}_\Sigma
=\frac{4\pi}{\hbar}\Delta\kappa\,\operatorname{Area}(\Sigma)
=\frac{1/6-\xi}{8\pi}\operatorname{Area}(\Sigma)\,\mathcal I.}
$$

**证明。** 标量热核线性项为 $(4\pi s)^{-2}e^{-s\mathsf M}[1+s(1/6-\xi)R]$。两谱的维数与迹相同，故差的 $s^{-2}$ 积分在紫外有限，正质量保证红外收敛，逐谱积分得 $\mathcal I$。块对角 $\log\mathsf M_0$ 使 $\operatorname{tr}(\mathsf M\log\mathsf M_0)=\operatorname{tr}(\mathsf M_0\log\mathsf M_0)$，得到相对熵式。

复制角为 $2\pi n$ 的锥在一阶有 $\int R_n=n\int R_1+4\pi(1-n)\operatorname{Area}(\Sigma)+O((n-1)^2)$。对 $S=(n\partial_n-1)\Gamma_E/\hbar|_{n=1}$ 代入局部项，得到最后两式。证毕。$\mathcal I$ 的对数可统一写为 $\log(\mathsf M/\mu^2)$，迹相同使 $\mu$ 抵消。

此为局部复制／Wald 型贡献，尤其当 $\xi\ne0$ 时含非最小耦合接触项，不能无条件等同于正的普通物质 von Neumann 纠缠熵。[Cone95, NonMin97] 的比较边界适用。归一化质量矩阵亦不是实际物质场密度态。完整真空能、高曲率项、非局域项和引力子圈未被该有限相对系数决定。

## corollary 30.2: 可计算的耦合响应

对两场 $\mathsf M(b)=\left(\begin{smallmatrix}\mu&b\\b&\mu\end{smallmatrix}\right)$，$\mu=m^2>|b|$，有

$$
\mathcal I(b)=(\mu+b)\log(\mu+b)+(\mu-b)\log(\mu-b)-2\mu\log\mu,
$$

$$
\mathcal I'(b)=\log\frac{\mu+b}{\mu-b},\qquad
\mathcal I''(b)=\frac{2\mu}{\mu^2-b^2}>0.
$$

对 $b>0$，$\xi<1/6$ 时相对曲率系数严格递增；$\xi=1/6$ 时仅此线性曲率差为零。上述等式直接微分得到。慢变 $b$ 作为局域系数时，变化率需要同时计入面积形变和 $b$ 的变化，不能把二者合并为一项“观察产生曲率”。

### 30.3 纳入控制器后才是一个自洽的几何动力学模型

取上述耦合为实际标量控制场 $b(x)$，在低导数截断中另给定已重整化的 $Z(b)>0,U(b)$、基础引力系数及边界条件。考虑明确的 Lorentz 有效作用量

$$
S_{\rm eff}=\int\sqrt{-g}\left[\kappa(b)R-\frac12Z(b)(\nabla b)^2-U(b)\right]+S_{\rm probe}[g,b],
$$

其中 $\kappa(b)$ 的相对物质圈贡献由命题 30.1 决定，其他有限系数是模型输入，未由该谱差推导。对这一定义的局部模型，变分给出

$$
\kappa G_{\mu\nu}+(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu)\kappa
=\tfrac12(T^{(b)}_{\mu\nu}+T^{\rm probe}_{\mu\nu}),
$$

$$
Z\Box b+\tfrac12Z'(\nabla b)^2-U'+\kappa'R+\mathcal O_b^{\rm probe}=0.
$$

这里 $T^{(b)}_{\mu\nu}=Z\nabla_\mu b\nabla_\nu b-g_{\mu\nu}[Z(\nabla b)^2/2+U]$，$\mathcal O_b^{\rm probe}=(\sqrt{-g})^{-1}\delta S_{\rm probe}/\delta b$。这些是所选标量–张量作用量的 Euler–Lagrange 方程，不是从 RT 静态熵独立推出 Einstein 方程。

**一致性检查。** 在其他探针变量在壳、无微分同胚异常时，$\nabla_\mu T^{\rm probe\,\mu}{}_{\nu}=\mathcal O_b^{\rm probe}\partial_\nu b$。$b$ 方程给出完整右侧散度 $-R\partial_\nu\kappa/2$，恰与左侧由 Bianchi 恒等式计算的散度相同。若只外部规定 $b(t)$ 而丢弃其控制器应力能，这个一致性就不自动成立。局部视界熵的相应系数为 $(4\pi/\hbar)\int_\Sigma\kappa(b)dA$。超出低导数／近平衡范围必须恢复因果非局域有效作用量，不能沿用截断方程宣称完整 UV 理论。

### 30.4 回接现有时空模型的真实义务

已有共同传播锥与内部钟可以约束因果结构和尺度；已有 Schur 记忆约束有效传播；本节说明物质消元的行列式可以改变几何作用系数。它们分别提供输入，尚没有证明与有限 RT 码属于同一个微观物理实现。平直响应不识别 $\xi$，因而不能单靠平直观察确定曲背景反作用。

[FGHMR14] 在已有半经典全息 CFT、AdS 真空邻域、全部球形区域和适当熵泛函等假设下，证明纠缠第一定律对应线性化引力方程。[LVR16] 将相对熵二阶变分与相应引力正则能量联系。当前有限码还缺少这些连续区域、应力能字典和统一几何响应映射。将参数空间 Berry 曲率、WP 辛形式或有限态 Fisher 度量直接改名为时空曲率会遗漏这些前提。

本轮的新落点是：原码的同谱动力学反例；受既有区域代数与粗化约束的动态条件；原非稳定子中心子码的闭合面积–相位流；以及同一质量谱差进入局部几何作用和锥熵的条件化连接。下一步应在一个独立给定的微观模型中共同检验传播、应力能响应、相位／记忆预测和面积变分，之后再争取从这些共同关系推出几何方程。这里没有结算原始引力 RT，也没有认领通用的几何量子力学、反绝热驱动、WP 公式或诱导引力机制为新发现。

## 31. 当前区域读数的最优预测误差

本节沿用构造 28.4 的同一个中心分组码，不另换物理载体。取 $\mathcal H_X=\mathbb C^3\oplus\mathbb C^6$ 为该区域的实际支撑，$\tau_0=I_3/3$、$\tau_1=I_6/6$ 放在两个正交块上。区域通道、面积算符及面积跨度为

$$
\mathcal N(\rho)=\rho_{00}\tau_0+\rho_{11}\tau_1,
\qquad \mathcal L=\operatorname{diag}(\log3,\log6),\qquad \Delta a=\log2.
$$

令 $\Delta$ 为逻辑计算基退相干，$\mathcal E$ 为将两个经典标签准备成 $\tau_i$ 的通道，$\mathcal M$ 为读取两个正交支持的测量通道。因此 $\mathcal N=\mathcal E\Delta$，$\mathcal M\mathcal N=\Delta$。实际区域空间更大时，将 $\mathcal M$ 在支撑外任意保迹补全即可。钻石范数 $\|\cdot\|_\diamond$ 采用**不含二分之一**的完全有界迹范数，包含任意被动参考系统 [Wat09]。

**定义 31.1（当前区域预测任务）。** 对已知逻辑信道 $\Phi_t$，仅允许预测器读取时刻零的区域态，定义

$$
\delta(t)=\inf_{\mathcal C\ {\rm CPTP}}
\|\mathcal N\Phi_t-\mathcal C\mathcal N\|_\diamond,
$$

其中 $\mathcal C$ 作用于该区域，可依赖已知的 $t$ 和生成元，但不能访问丢失的逻辑相干、未来读数或先前历史。此量不等于全码的静态擦除恢复误差；静态中心代数仍能被精确恢复。它也不是 [BO10] 采用最坏纠缠保真度的近似纠错优化量。

## lemma 31.2: 秩一映射的完全范数

若 $B=B^*$、$Y$ 为有限矩阵，$\Xi(X)=\operatorname{Tr}(BX)Y$，则

$$
\|\Xi\|_\diamond=\|B\|_\infty\|Y\|_1.
$$

**证明。** 对 $B$ 作谱分解。先测量其谱投影并保留参考系统，得到直和块 $X_i$；该保迹完全正映射的完全迹范数为一。随后 $\|\sum_i\lambda_iX_i\|_1\le\max_i|\lambda_i|\sum_i\|X_i\|_1$，再张量乘 $Y$ 给出上界。输入最大绝对本征值的单位本征向量投影达到下界。证毕。完全范数框架采用 [Wat09]，这个具体计算在这里直接证明。

## theorem 31.3: 同一中心码的精确预测缺陷

设 $\Phi_t$ 是一个保单位的逻辑信道，且它的区域可见坐标满足

$$
z_t=\alpha_tz_0+\beta_ty_0,
\quad z=\operatorname{Tr}(\sigma_z\rho),\quad
 y=\operatorname{Tr}(\sigma_y\rho)=-2\operatorname{Im}\rho_{01}.
$$

则 $|\alpha_t|\le1$，并且

$$
\boxed{\delta(t)=|\beta_t|.}
$$

一个达到下确界的实际预测器是 $\mathcal C_t=\mathcal E T_{\alpha_t}\mathcal M$，其中对角二态信道

$$
T_c=\frac12\begin{pmatrix}1+c&1-c\\1-c&1+c\end{pmatrix}
\qquad(-1\le c\le1)
$$

采用列概率约定。在给定当前 $p=\rho_{11}$ 的全部相容逻辑密度矩阵中，仅依赖 $p$ 的实数面积预测器的精确 minimax 绝对风险是

$$
\boxed{\mathcal R_t(p)=\Delta a\,\sqrt{p(1-p)}\,|\beta_t|.}
$$

**证明。** 正性应用于两种 $\sigma_z$ 本征态给出 $|\alpha_t|\le1$，所以 $T_{\alpha_t}$ 是合法随机信道。直接计算差映射为

$$
(\mathcal N\Phi_t-\mathcal C_t\mathcal N)(X)
=\beta_t\operatorname{Tr}(\sigma_yX)\frac{\tau_0-\tau_1}{2}.
$$

两块正交，$\|(\tau_0-\tau_1)/2\|_1=1$，引理 31.2 给出上界 $|\beta_t|$，包括任意参考纠缠。反向取 $\rho_\pm=(I\pm\sigma_y)/2$；当前区域态完全相同，未来区域态的迹范数距离为 $2|\beta_t|$。任意同输入预测器输出相同，三角不等式强迫至少一个误差不小于 $|\beta_t|$。

固定 $p$ 时，正性等价于 $|\rho_{01}|\le\sqrt{p(1-p)}$，所以 $y_0$ 的准确范围是 $[-2\sqrt{p(1-p)},2\sqrt{p(1-p)}]$。未来 $p_t$ 的范围以 $[1-\alpha_t(1-2p)]/2$ 为中心、半径为 $\sqrt{p(1-p)}|\beta_t|$。纯态的两种相反虚相干达到端点。面积是 $\log3+\Delta a p_t$，区间中点给出上界，两端共同当前读数给出匹配下界。证毕。此任务提供了完整当前区域密度矩阵；只知道其熵不会改善下界。

对于第 28.4 节的闭系统 $h=(\Omega/2)\sigma_x$，$\alpha_t=\cos\Omega t$、$\beta_t=\sin\Omega t$。因此当前面积或中心概率在某些时间可完全不足以预测未来区域态，虽然全局编码和时间演化都是精确的。

## 32. 同一面积模型的因果记忆与受控自治极限

**定义 32.1（明确的开放演化）。** 保持上述码，取 $\Omega>0$、$\gamma\ge0$，指定逻辑 Lindblad 生成元

$$
\mathcal G_\gamma(\rho)
=-i[(\Omega/2)\sigma_x,\rho]
+\frac\gamma2(\sigma_z\rho\sigma_z-\rho).
$$

这是一项额外的物理噪声假设，不由静态 RT 公式推出。令 $P_c=J_cJ_c^*$，取 $H_B=J_c(\Omega\sigma_x/2)J_c^*$ 和 Hermitian involution $Z_B=J_c\sigma_zJ_c^*+(I-P_c)$，即给出在原物理空间上保持该子码的实际生成元。它一般跨原区域划分非局部，不声称几何局域性。

## proposition 32.2: 完整记忆与相位缺陷

该流满足

$$
\dot z=\Omega y,\qquad\dot y=-\Omega z-\gamma y,
$$

$$
\binom{z_t}{y_t}
=\begin{pmatrix}\alpha_t&\beta_t\\-\beta_t&\eta_t\end{pmatrix}
\binom{z_0}{y_0}
=\exp\!\left[t\begin{pmatrix}0&\Omega\\-\Omega&-\gamma\end{pmatrix}\right]
\binom{z_0}{y_0}.
$$

精确消元为

$$
\boxed{\dot z(t)=\Omega e^{-\gamma t}y_0
-\Omega^2\int_0^te^{-\gamma(t-s)}z(s)\,ds.}
$$

当前区域的最优完整预测缺陷和面积 minimax 风险仍分别为 $|\beta_t|$ 与定理 31.3 的值。若 $\gamma>0$，则

$$
|\beta_t|\le\min(1,\Omega/\gamma)\qquad(t\ge0).
$$

**证明。** Pauli 交换子给出两个实方程，变参数公式给出带隐藏初值的卷积。二维生成矩阵的对称部是 $\operatorname{diag}(0,-\gamma)$，故传播矩阵的欧氏范数不超过一，特别是 $|\alpha_t|,|\beta_t|\le1$。从初态 $(z_0,y_0)=(1,0)$ 得 $y_t=-\beta_t$，其第二式给出 $\beta_t=\Omega\int_0^te^{-\gamma(t-s)}\alpha_sds$，因此 $|\beta_t|\le\Omega/\gamma$。代入定理 31.3 即得全部操作结论。证毕。

## corollary 32.3: 逐时最优预测器不组成半群

对该固定生成元，

$$
\alpha_{t+s}=\alpha_t\alpha_s-\beta_t\beta_s,
\qquad
\|T_{\alpha_{t+s}}-T_{\alpha_t}T_{\alpha_s}\|_\diamond
=|\beta_t\beta_s|.
$$

这里经典信道通过计算基测量扩展到量子输入。因此最优预测器的复合缺陷恰是两步隐藏相位缺陷的乘积。由于 $\alpha_u=1-\Omega^2u^2/2+O(u^3)$，固定 $t$ 时 $(\alpha_{t/n})^n\to1$。反复只保存当前概率的这套离散预测复合会冻结概率，而非恢复原来的真实有限时演化。

**证明。** 传播矩阵半群的第一行第一列给出恒等式；两个二态信道的参数相乘，它们之差的完全迹范数等于参数差的绝对值，可用引理 31.2 验证。指数的二阶展开及极限给出最后结论。证毕。这里比较预测器复合，不把它与未经实际干预的原量子轨道混同。

## theorem 32.4: 全时间、带参考系统的 Markov 近似

假设 $\gamma\ge4\Omega$，记 $\epsilon=\Omega/\gamma\le1/4$、$k=\Omega^2/\gamma$。则对所有 $t\ge0$，

$$
|\alpha_t-e^{-kt}|\le2\epsilon^2,
$$

$$
\boxed{
\|\mathcal N e^{t\mathcal G_\gamma}
-\mathcal E T_{e^{-kt}}\Delta\|_\diamond
=\sqrt{(\alpha_t-e^{-kt})^2+\beta_t^2}
\le\epsilon\sqrt{1+4\epsilon^2}.}
$$

若初态在逻辑计算基上已退相干，包括与参考系统相关的经典-量子态，则相应完整误差至多 $2\epsilon^2$。一般输入的面积期望误差至多为右侧钻石界乘 $\Delta a/2$。

**证明。** 设 $q=\sqrt{1-4\epsilon^2}$、$r_-=(\gamma-\sqrt{\gamma^2-4\Omega^2})/2$、$r_+=(\gamma+\sqrt{\gamma^2-4\Omega^2})/2$。解二阶方程得

$$
\alpha_t=\frac{r_+e^{-r_-t}-r_-e^{-r_+t}}{r_+-r_-},\qquad
\beta_t=\frac{\Omega(e^{-r_-t}-e^{-r_+t})}{r_+-r_-}.
$$

$k=r_-r_+/\gamma$，且 $r_->k$。写 $\alpha_t=e^{-r_-t}+\frac{r_-}{r_+-r_-}(e^{-r_-t}-e^{-r_+t})$，再用 $te^{-kt}\le1/(\exp(1)k)$，得到

$$
|\alpha_t-e^{-kt}|
\le\frac{r_-}{r_+-r_-}+\frac{r_--k}{\exp(1)k}
=\epsilon^2\left[\frac2{q(1+q)}+\frac4{\exp(1)(1+q)^2}\right].
$$

$q\ge5/6$、$\exp(1)\ge5/2$ 将括号控制在 $72/55+288/605=216/121<2$。差通道恰为

$$
X\longmapsto\operatorname{Tr}\!\left([ (\alpha_t-e^{-kt})\sigma_z+\beta_t\sigma_y]X\right)
\frac{\tau_0-\tau_1}{2}.
$$

两 Pauli 反对易，其系数矩阵的算子范数为所列平方根，引理 31.2 给出精确钻石范数。命题 32.2 给出最终上界。先作用 $\Delta$ 时 $\sigma_y$ 项消失。区域面积读数可用 $A_X=(\log3)P_0+(\log6)P_1$ 实现，减去谱区间中点后范数为 $\Delta a/2$；两输出迹相同，迹对偶界给出面积误差。证毕。这里没有用有限时间网格代替 $\sup_{t\ge0}$ 的证明。

在慢时间 $\tau=kt$ 上，有效方程是 $dp/d\tau=1/2-p$，从而

$$
\frac{d\bar a}{d\tau}=a_{\rm mid}-\bar a,
\qquad a_{\rm mid}=\log3+\tfrac12\log2.
$$

这条自治面积方程来自同一中心量子模型的受控极限。若只令 $\gamma\to\infty$ 却固定原始时间，得到的是冻结，不能误报为非平凡的耗散几何。开放量子系统的绝热消元与 CP/TP 保持已有 [ASR16] 等研究；其任意阶的一般 Lindblad 断言在该文为猜想，本节仅证明上面这个指定模型的精确有限时间结果。#8330 已有同类驱动二能级传播与完全相对熵收缩；这里的新增目标是当前区域因子化的最优钻石误差、固定面积预测风险与统一时间 Markov 比较，不再次认领二阶阻尼方程本身。

## 33. 预测自治、静态 RT 与热平衡的区别

## proposition 33.1: 有效面积变化不等于面积单调增加

在定理 32.4 的有效二态流中，$\dot p=k(1/2-p)$。当前区域熵和相对给定平衡态的缺陷分别为

$$
S_X=h_2(p)+\log3+p\log2,
\qquad D(\mathcal N\rho\Vert\mathcal N(I_2/2))=\log2-h_2(p).
$$

对 $0<p<1$，

$$
\dot S_X=k(1/2-p)\left[\log\frac{1-p}{p}+\log2\right],
\qquad
\frac d{dt}D=k(1/2-p)\log\frac p{1-p}\le0.
$$

特别是 $1/2<p<2/3$ 时区域熵与面积期望都下降。固定码平衡态的扇区概率是 $(1/2,1/2)$，它不等于整个九维区域的最大混合态，后者对应 $(1/3,2/3)$。

**证明。** 正交块谱给出两式，随后直接求导；函数 $\log(p/(1-p))$ 与 $p-1/2$ 同号，得到相对熵耗散。整体九维最大混合态按块维数分配权重，故其第二扇区概率为六除九。证毕。没有引入独立视界条件或重力能量条件，因此不能从本有效流宣称广义第二定律或物理视界面积定理。

**统一边界。** 同一个固定子码在整个演化中仍满足精确的面积加中心代数熵公式；动态预测误差非零不表示该静态身份失效。当前区域无法自治的原因是相位被该区域通道消去。强退相干使这部分影响可被量化地忽略，但没有恢复被噪声丢弃的完整逻辑量子信息。噪声率、控制 Hamiltonian、环境及时间尺度都是模型前提，多区域几何局域性、连续 CFT 字典和 Einstein 动力学仍未由本结果推出。

上述结论为普通纸面推导。来源说明和相应 Library 引用区分已有几何量子力学、Wolpert 公式、反绝热驱动、热核及诱导曲率机制、钻石范数和绝热消元，与本卷指定编码中的计算。没有 Lean 声明、内核验证、独立审查或具名开放问题结算。具体结果的文献优先权未作穷尽排查。

## 34. 多面积扇区的共同最优相干粗化

这里的任务是有限维操作问题，不把面积扇区的代数标签直接认作连续 CFT 谱。令逻辑基为 $|s\rangle$，两侧物理空间按 $s$ 作正交直和。源编码 $J_r$ 在第 $s$ 扇区制备 Schmidt 秩 $r_s$ 的平坦纯态，目标编码 $J_d$ 同理，$r_s,d_s$ 均为正整数。允许两侧各自作一个 CPTP 映射，不允许通信、后选择或额外共享纠缠；每个基扇区的输出必须**精确**等于目标纯态。跨扇区相干可以受损。把编码视为输入逻辑矩阵到双侧输出的信道，误差采用包含任意被动参考且不除以二的钻石范数。

## theorem 34.1: 有限多个面积扇区的共同最优误差

上述任务可行，当且仅当每个 $m_s=r_s/d_s$ 为正整数。把不同的 $\ell_s=\log m_s$ 排为 $\ell_1<\cdots<\ell_k$，令

$$
T=\sum_{i=1}^{k-1}\tanh\frac{\ell_{i+1}-\ell_i}{4}.
$$

对全部允许的两侧局部信道，精确最优值为

$$
\boxed{\inf_{\Lambda_X,\Lambda_Y}
\| (\Lambda_X\otimes\Lambda_Y)J_r-J_d\|_\diamond
=\frac{2T}{1+T}.}
$$

这里的 $J_r,J_d$ 代表等距编码诱导的信道。同一对局部等距在所有扇区同时达到最优：每侧按 $|s,a+d_sb\rangle\mapsto|s,a\rangle|b\rangle$ 拆分，再丢弃环境。环境态是前 $m_s$ 个标签上的最大纠缠态，故诱导的逻辑信道是 Schur 乘子，Gram 核为

$$
K_{st}=\sqrt{\frac{\min(m_s,m_t)}{\max(m_s,m_t)}}
=e^{-|\ell_s-\ell_t|/2}.
$$

**证明。** 对任意可行局部信道取 Stinespring 等距。每个扇区的目标输出为纯态，故总输出在该扇区必分解成目标纯态与一个环境态的张量积。局部等距保持两侧的非零 Schmidt 谱：源谱有 $r_s$ 个 $1/r_s$，目标谱有 $d_s$ 个 $1/d_s$。环境谱只能有 $m_s=r_s/d_s$ 个 $1/m_s$，所以 $m_s$ 必为整数，环境态最大纠缠。任意两环境态的重叠 $C_{st}$ 受归一化部分等距的奇异值迹界约束，$|C_{st}|\le K_{st}$。上述嵌套环境构造同时取等所有这些界，证明可行性的充分性。

候选通道与理想通道之差作用在任意带参考的纯输入 $\sum_s|s\rangle|v_s\rangle$ 上。令 $p_s=\|v_s\|^2$；由于不同逻辑标签正交，输出差的非零谱等于矩阵 $B_p=D_{\sqrt p}(\mathbf1\mathbf1^T-K)D_{\sqrt p}$ 的谱。$B_p$ 是秩一正矩阵减去正半定矩阵，迹为零，因而迹范数为其最大正本征值的两倍。$\mathbf1\mathbf1^T-K$ 逐项非负，最大 Rayleigh 向量可取非负。写 $y_s=\sqrt{p_s}x_s$，Cauchy 给出 $\sum_s y_s\le1$；反向取 $p_s=y_s,x_s=\sqrt{y_s}$ 可取等。于是包含任意参考的候选钻石误差为

$$
2\left(1-\min_{p_s\ge0,\,\sum p_s=1}p^TKp\right).
$$

相同 $\ell$ 的标签只通过其总概率进入二次型。对不同的 $\ell_i$，设 $\kappa_i=e^{-(\ell_{i+1}-\ell_i)/2}$。指数核的逆满足

$$
x^TK^{-1}x=x_1^2+\sum_{i=1}^{k-1}
\frac{(x_{i+1}-\kappa_i x_i)^2}{1-\kappa_i^2}.
$$

代入 $x=\mathbf1$ 得 $Z=\mathbf1^TK^{-1}\mathbf1=1+T$。$v=K^{-1}\mathbf1$ 的端点分量为 $1/(1+\kappa_i)$，内部第 $i$ 分量为 $1/(1+\kappa_{i-1})+1/(1+\kappa_i)-1$，均严格正。正定 Cauchy 给 $p^TKp\ge1/Z$，概率向量 $p_*=v/Z$ 取等。只有一个不同秩时 $K=\mathbf1\mathbf1^T$，误差为零。

最后须证明候选也在全部允许操作中最优。对所有允许的环境 Gram 核 $C$，同一个输入 $|\psi_*\rangle=\sum_s\sqrt{p_{*,s}}|s\rangle$ 的理想输出投影成功概率至多 $p_*^TKp_*=1/Z$，因为 $\operatorname{Re}C_{st}\le K_{st}$。这个二元投影测试给出迹距离下界 $2(1-1/Z)$；候选通道已经达到相同上界。故单个共同输入与投影证明全操作下界，并且被动参考不能增大该最优值。证毕。

例如 $d=(3,3,3)$、$r=(3,12,48)$ 时 $m=(1,4,16)$，$K$ 的相邻非对角元为 $1/2$、端点元为 $1/4$。$p_*=(2/5,1/5,2/5)$、$T=2/3$，误差为 $4/5$；只看任意一对扇区得到的最大界为 $3/4$。这是一个共同物理构造和联合测试，不能用逐对可达性替代。

## corollary 34.2: 维数无关的稳定性判据

设 $R=\max_s\ell_s-\min_s\ell_s$，则

$$
1-e^{-R/2}\le\delta_*\le\frac{2R}{4+R}.
$$

因此，扇区数可随精度变化时，$\delta_*\to0$ 当且仅当损失面积算符 $\operatorname{diag}(\ell_s)$ 在算子范数下趋近某个公共标量。对 $\epsilon<2$，精确误差预算为 $T\le\epsilon/(2-\epsilon)$。两端点扇区给左界；$\tanh x\le x$ 给 $T\le R/4$ 和右界。平均损失面积不足以决定该误差。

## theorem 34.3: 整数秩塔的最优尺度半群

若 $r_s(n)=b_s^n$、$b_s\ge2$ 为整数，令 $a_s=\log b_s$，则从层 $n$ 到 $j\le n$ 的上述最优粗化在逻辑矩阵单位上乘以 $e^{-(n-j)|a_s-a_t|/2}$。顺次从 $n$ 到 $j$ 再到 $h$ 与直接从 $n$ 到 $h$ 严格相同，且每段均达到定理 34.1 的最优值。把相邻不同 $a_i$ 之间的阈值投影记为 $P_i$，连续尺度延拓的生成元为

$$
\mathcal G_{\rm scale}(\rho)=\sum_i(a_{i+1}-a_i)
\left(P_i\rho P_i-\frac{P_i\rho+\rho P_i}{2}\right).
$$

每个矩阵单位只受分开其两个 $a$ 值的阈值项作用，速率总和为 $|a_s-a_t|/2$；系数非负给出 CPTP 半群。该连续参数是**尺度**，并非物理时间；非整数尺度不代表一个非整数 Schmidt 秩的有限编码。若有固定 $k$ 个不同的 $b_s$，从 $n$ 降至 $\lfloor\lambda n\rfloor$、$0\le\lambda<1$，误差趋于 $2(k-1)/k$。单侧端点约化通道始终精确正确，联合相干误差却可非零，因此静态面积或端点熵的吻合不能认证整个粗化信道。

## 35. 与 Virasoro 面积密度的条件化接口

Lin 的式 (1.3) 取 $S(P)=4\sinh(2\pi bP)\sinh(2\pi P/b)$、$Q=b+b^{-1}$、$c=1+6Q^2$，其中 $b,P>0$ [Lin26]。此处额外假设有限实现已满足定理 34.1 的全部局部操作条件，而且实际**整数**损失秩存在共同常数 $C_0$ 及误差 $\eta\ge0$，满足 $|\log m_s-\log S(P_s)-C_0|\le\eta$。这项秩匹配尚未从 CFT 证明，连续谱密度不能直接当作有限维数。

## corollary 35.1: 条件化动量窗口的必要预算

令 $\Delta P=\max_sP_s-\min_sP_s$。在上述额外前提下，

$$
\delta_*\ge1-\exp[-\max(0,\pi Q\Delta P-\eta)].
$$

若要求 $\delta_*\le\epsilon<1$，则必须有 $\Delta P\le[\eta-\log(1-\epsilon)]/(\pi Q)$。证明是 $d\log S(P)/dP=2\pi b\coth(2\pi bP)+2\pi b^{-1}\coth(2\pi P/b)\ge2\pi Q$。取动量两端点，并计入各自的匹配误差，得到 $R\ge\max(0,2\pi Q\Delta P-2\eta)$；代入推论 34.2 左界并反解。固定误差和匹配预算时，窗口上界按 $c^{-1/2}$ 缩小。

这并未证明未知共形块的主导性、准概率正性、实际 CFT 粗化的两侧独立 CPTP 实现、连续引力字典或原始引力 RT。定理 34.1 和这些条件推论目前是纸面证明，尚未由 Lean kernel 验证。

## 参考文献

[RT] S. Ryu, T. Takayanagi. Holographic Derivation of Entanglement Entropy from AdS/CFT. Phys. Rev. Lett. 96 (2006), 181602. arXiv:hep-th/0603001.

[Lin26] J. Lin. Ryu-Takayanagi area from Virasoro modular data. arXiv:2606.30723v1 (2026). 式 (1.3) 用作第 35 节的条件性密度输入；有限维秩匹配另作假设。

[LM] A. Lewkowycz, J. Maldacena. Generalized gravitational entropy. JHEP 08 (2013), 090. arXiv:1304.4926.

[HaPPY] F. Pastawski, B. Yoshida, D. Harlow, J. Preskill. Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence. JHEP 06 (2015), 149. arXiv:1503.06237.

[Harlow] D. Harlow. The Ryu–Takayanagi Formula from Quantum Error Correction. Commun. Math. Phys. 354 (2017), 865–912. arXiv:1607.03901.

[HMPS] M. Heydeman, M. Marcolli, S. Parikh, I. Saberi. Nonarchimedean Holographic Entropy from Networks of Perfect Tensors. Adv. Theor. Math. Phys. 25 (2021), 591–721. arXiv:1812.04057.

[QMF] S. X. Cui, M. H. Freedman, O. Sattath, R. Stong, G. Minton. Quantum Max-flow/Min-cut. J. Math. Phys. 57 (2016), 062206. arXiv:1508.04644.

[FixedArea] X. Dong, D. Harlow, D. Marolf. Flat entanglement spectra in fixed-area states of quantum gravity. JHEP 10 (2019), 240. arXiv:1811.05382.

[Stabilizer] D. Fattal, T. S. Cubitt, Y. Yamamoto, S. Bravyi, I. L. Chuang. Entanglement in the stabilizer formalism. arXiv:quant-ph/0406168.

[ModularClifford] E. Hostens, J. Dehaene, B. De Moor. Stabilizer states and Clifford operations for systems of arbitrary dimensions, and modular arithmetic. Phys. Rev. A 71 (2005), 042315. arXiv:quant-ph/0408190v2.

[RRKL23] S. A. Rather, N. Ramadas, V. Kodiyalam, A. Lakshminarayan. Absolutely maximally entangled state equivalence and the construction of infinite quantum solutions to the problem of 36 officers of Euler. Phys. Rev. A 108 (2023), 032412. DOI: 10.1103/PhysRevA.108.032412. arXiv:2212.06737v2. 使用 Theorem 1。

[TPTN26] G. Arora, M. Headrick, A. Lawrence, M. Sasieta, B. Swingle, C. Wolfe. Twirled Perfect Tensor Networks: Computationally covariant holographic tensor networks. arXiv:2605.23670v2 (2026-06-03). 使用第 5.1、5.2、7 节，保持预印本身份。

[BZ24] W. Bruzda, K. Życzkowski. Two-unitary complex Hadamard matrices of order 36. Special Matrices 12 (2024), 20240010. DOI: 10.1515/spma-2024-0010. 使用第 4 节 Conjecture 1 和式 (10)–(15)。

[Tan26] I. Tan. Transversal gates of the ((3,3,2)) qutrit code and local symmetries of the absolutely maximally entangled state of four qutrits. arXiv:2601.19677 (2026)。

[Rather24] S. A. Rather. Construction of perfect tensors using biunimodular vectors. Quantum 8 (2024), 1528. DOI: 10.22331/q-2024-11-20-1528. arXiv:2309.01504v2. 第 5.2 节已有固定三个代表的局部不等价性。

[StateRG05] F. Verstraete, J. I. Cirac, J. I. Latorre, E. Rico, M. M. Wolf. Renormalization-Group Transformations on Quantum States. Phys. Rev. Lett. 94 (2005), 140601. arXiv:quant-ph/0410227.

[ER07] G. Vidal. Entanglement renormalization. Phys. Rev. Lett. 99 (2007), 220405. arXiv:cond-mat/0512165v2.

[Aud07] K. M. R. Audenaert. A sharp continuity estimate for the von Neumann entropy. J. Phys. A 40 (2007), 8127–8136. arXiv:quant-ph/0610146. 标准界亦见 arXiv:2408.15306v4 式 (1)。

[Cert26] G.-P. Nadon et al. Quantum State Certification via Effective Parent Hamiltonians from Local Measurement Data. arXiv:2603.04499 (2026). 仅作为局部能量认证方法的相关来源。

[BKK07] C. Bény, A. Kempf, D. W. Kribs. Quantum Error Correction of Observables. Phys. Rev. A 76 (2007), 042303. arXiv:0705.1574. 使用可纠正代数的压缩错误算符交换子判据；较早简报为 Phys. Rev. Lett. 98 (2007), 100502，arXiv:quant-ph/0608071。

[HJPW04] P. Hayden, R. Jozsa, D. Petz, A. Winter. Structure of states which satisfy strong subadditivity of quantum entropy with equality. Commun. Math. Phys. 246 (2004), 359–374. arXiv:quant-ph/0304007. 仅作为零条件互信息与短量子 Markov 结构的背景，式中当前网络的值由逐边计算得出。

[HEC15] N. Bao, S. Nezami, H. Ooguri, B. Stoica, J. Sully, M. Walter. The Holographic Entropy Cone. JHEP 09 (2015), 130. arXiv:1505.07839. 使用第 3.2 节、Lemma 4、Theorem 5；扭转不唯一性亦已明确见于该节。

[EPV23] M. Ebbens, H. Parlier, G. Vegter. Minimal Delaunay Triangulations of Hyperbolic Surfaces. Discrete Comput. Geom. 69 (2023), 568–592. DOI: 10.1007/s00454-022-00373-0. 使用第 2 节 Fenchel–Nielsen 坐标及 Lemma 2.1 的曲率 $-1$ 领圈宽度。

[AR19] C. Akers, P. Rath. Holographic Renyi Entropy from Quantum Error Correction. JHEP 05 (2019), 052. arXiv:1811.05171v2. 使用固定辅助纠缠、面积扇区与 Rényi 谱的解释，不作为当前子码原创性证明。

[HHM11] P. Hayden, M. Headrick, A. Maloney. Holographic Mutual Information is Monogamous. Phys. Rev. D 87 (2013), 046003. arXiv:1107.2940v2，初稿 2011 年。使用静态 RT 熵的 $I_3\le0$ 定理。

[CSW25] B. Czech, S. Shuai, Y. Wang. Entropy Inequalities Constrain Holographic Erasure Correction. Phys. Rev. Lett. 135 (2025), 141603. DOI: 10.1103/dl3c-h3hg. arXiv:2502.12246. 使用熵不等式饱和对特定访问结构的约束作为比较背景。

[CS26] B. Czech, S. Shuai. Renormalization group is the principle behind the holographic entropy cone. JHEP 07 (2026), 165. DOI: 10.1007/JHEP07(2026)165. arXiv:2601.02472v2. 核对第 2.1、2.2、4 节；文中饱和推导的收缩法范围及所讨论猜想的状态不省略。

[PRR22] J. Pollack, P. Rall, A. Rocchetto. Understanding holographic error correction via unique algebras and atomic examples. JHEP 06 (2022), 056. DOI: 10.1007/JHEP06(2022)056. arXiv:2110.14691v2. 使用构造性可恢复代数与稳定子互补恢复的背景，不将一般结果重复认领。

[Cao24] C. Cao. Non-trivial Area Operators Require Non-local Magic. JHEP 11 (2024), 105. DOI: 10.1007/JHEP11(2024)105. arXiv:2306.14996v2. 使用 Theorem 2.1 及局部幺正变换、稳定子串联的适用边界；“非平凡面积”在此指不与逻辑恒等成比例，而不是仅指非零。

[CGL99] R. Cleve, D. Gottesman, H.-K. Lo. How to share a quantum secret. Phys. Rev. Lett. 83 (1999), 648–651. DOI: 10.1103/PhysRevLett.83.648. arXiv:quant-ph/9901025. 使用三份量子秘密共享及其纠错背景，奇数循环模环的具体解码在第 25 节直接给出。

[AS97] A. Ashtekar, T. A. Schilling. Geometrical Formulation of Quantum Mechanics. arXiv:gr-qc/9706069 (1997). 使用射影量子态的 Kähler／Hamilton 表述背景。

[WP25] N. Kawazumi. A topological proof of Wolpert's formula for the Weil-Petersson symplectic form in terms of the Fenchel-Nielsen coordinates. Geometriae Dedicata 219 (2025), 56. DOI:10.1007/s10711-025-01016-3. arXiv:2408.04937v2. 公式本身归于 Wolpert；本卷扭转坐标相对该文式 (1) 换号，固定测地边界的应用保持边界长度不变。

[Berry09] M. V. Berry. Transitionless quantum driving. J. Phys. A 42 (2009), 365303. DOI:10.1088/1751-8113/42/36/365303. 使用既有无跃迁输运背景；本卷明确写出一般框架的连接项。

[Magic26] C. Cao, G. Cheng, K. Karthikeyan, C. Li, J. Preskill. State-dependent geometries from magic-enriched quantum codes. arXiv:2603.13475v2 (2026-06-27), §1–2. 本文子系统码论证的范围不包括一般算子代数码；正文脚注明确保留后者的非平凡中心面积。

[Bar15] C. Bär. Green-hyperbolic operators on globally hyperbolic spacetimes. Commun. Math. Phys. 333 (2015), 1585–1615. arXiv:1310.0738. 连续 Green 算子的函数空间与因果性不由有限矩阵 Schur 恒等式替代。

[HK03] D. V. Vassilevich. Heat kernel expansion: user's manual. Phys. Rep. 388 (2003), 279–360. arXiv:hep-th/0306138v3. 使用标量线性曲率热核及共同正规化背景。

[Cone95] S. N. Solodukhin. Conical singularity and quantum corrections to the entropy of a black hole. Phys. Rev. D 51 (1995), 609. DOI:10.1103/PhysRevD.51.609. 使用平滑锥几何与局部作用量熵变分。

[NonMin97] S. N. Solodukhin. Nonminimal coupling and quantum entropy of a black hole. Phys. Rev. D 56 (1997), 4968. DOI:10.1103/PhysRevD.56.4968. 接触项与统计熵的解释须区分。

[FGHMR14] T. Faulkner, M. Guica, T. Hartman, R. C. Myers, M. Van Raamsdonk. Gravitation from Entanglement in Holographic CFTs. JHEP 03 (2014), 051. arXiv:1312.7856v2. 使用 AdS 真空邻域、全体球区域和既定全息熵字典的限定推导。

[LVR16] N. Lashkari, M. Van Raamsdonk. Canonical Energy is Quantum Fisher Information. JHEP 04 (2016), 153. arXiv:1508.00897. 使用全息真空附近相对熵 Hessian 与正则能量的条件化关系。

[Do10] N. Do. The asymptotic Weil-Petersson form and intersection theory on M_{g,n}. arXiv:1010.4126 (2010). 固定测地边界长度的模空间辛结构背景。

[Wat09] J. Watrous. Semidefinite Programs for Completely Bounded Norms. Theory of Computing 5 (2009), 217–238. DOI:10.4086/toc.2009.v005a011. 使用完全有界迹范数与带参考系统的信道距离框架；本卷不含二分之一。

[ASR16] R. Azouit, A. Sarlette, P. Rouchon. Adiabatic elimination for open quantum systems with effective Lindblad master equations. arXiv:1603.04630v1 (2016). 使用开放系统约化的比较背景，保留其无退相干子空间前件及任意阶断言的猜想身份。

[BO10] C. Bény, O. Oreshkov. General conditions for approximate quantum error correction and near-optimal recovery channels. Phys. Rev. Lett. 104 (2010), 120501. DOI:10.1103/PhysRevLett.104.120501. arXiv:0907.5391. 用于区分其最坏纠缠保真度恢复任务与第 31 节当前区域预测任务。

第 27–35 节的来源条目分别存入 `Library/notes`。这些文献记录不指向尚不存在的 Lean 声明；本卷新增的纸面结果尚无 Lean 真源。

## 附录 A. 36 阶矩阵的精确整数重放

程序依赖 NumPy 和 opt_einsum，后者仅决定收缩顺序。根环元写为 $a+b\zeta$，$\zeta^2-\zeta+1=0$，乘法为 $(ac-bd)+(ad+bc+bd)\zeta$，共轭为 $(a+b)-b\zeta$。承重数组均为有符号 64 位整数；完整收缩最多 $6^{16}$ 个单位根项，分量中间运算保守界 $3\cdot6^{16}<2^{63}$。原始向量和掩码来自 [BZ24]。这是有限等式计算证书，不是 Lean 检查。

```python
import itertools
from fractions import Fraction
import numpy as np
import opt_einsum as oe

perms = ((0,1,2,3),(1,0,3,2),(2,3,1,0),(3,2,0,1))
units = np.array([(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)], dtype=np.int64)
vectors = [
 [0,1,0,1,3,3,3,3,1,5,2,4,2,1,3,1,2,3,1,1,2,0,3,5,5,3,2,3,2,5,4,4,1,5,5,1],
 [0,2,3,3,2,0,0,3,2,2,0,4,2,0,3,5,0,0,0,5,0,0,2,0,2,2,5,3,2,4,2,3,0,2,0,0],
 [0,2,2,0,0,1,0,1,1,1,2,1,0,2,0,2,2,2,2,0,2,2,2,1,1,1,2,0,2,2,0,1,2,2,1,0]
]

def conj(a,b):
    return a+b, -b

def mm(a,b,c,d):
    return a@c-b@d, a@d+b@c+b@d

def make_h(j):
    lam = np.array(vectors[j]).reshape(6,6)*(2 if j == 2 else 1)
    a = np.zeros((6,)*4, dtype=np.int64)
    b = a.copy()
    for k,l,m,n in itertools.product(range(6), repeat=4):
        v = sum((units[(x*(l-n)-y*(k+m)+int(lam[x,y]))%6]
                 for x,y in itertools.product(range(6), repeat=2)),
                np.zeros(2,dtype=np.int64))
        assert np.all(v%6 == 0)
        c,d = v//6
        e,f = units[(l*k+n*m)%6]
        value = (e*c-f*d, e*d+f*c+f*d)
        assert value in [tuple(u) for u in units]
        a[k,l,m,n], b[k,l,m,n] = value
    return a,b

def invariant(a,b):
    labels = [[4*l+i for l in range(4)] for i in range(4)]
    labels += [[4*l+perms[l][i] for l in range(4)] for i in range(4)]
    expr = ','.join(''.join(oe.get_symbol(v) for v in ds) for ds in labels)+'->'
    ac,bc = conj(a,b)
    work = [(a,b)]*4+[(ac,bc)]*4
    _,info = oe.contract_path(expr,*([a]*8),optimize='auto-hq')
    for ids,_,eq,_,_ in info.contraction_list:
        assert len(ids) == 2
        (a,b),(c,d) = [work.pop(i) for i in ids]
        ac = oe.contract(eq,a,c,optimize=False)
        bd = oe.contract(eq,b,d,optimize=False)
        ad = oe.contract(eq,a,d,optimize=False)
        bc = oe.contract(eq,b,c,optimize=False)
        work.append((ac-bd,ad+bc+bd))
    assert len(work) == 1 and int(work[0][1]) == 0
    return Fraction(int(work[0][0]),36**8)

expected = [Fraction(35,419904),Fraction(79,839808),Fraction(1,15552)]
axes_list = [(0,1,2,3),(0,2,1,3),(0,3,2,1)]
for j in range(3):
    a,b = make_h(j)
    for axes in axes_list:
        x = a.transpose(axes).reshape(36,36)
        y = b.transpose(axes).reshape(36,36)
        c,d = conj(x.T,y.T)
        g,h = mm(x,y,c,d)
        assert np.array_equal(g,36*np.eye(36,dtype=np.int64)) and not np.any(h)
    assert invariant(a,b) == expected[j]
    print('fixed invariant',j+1,expected[j])

mask = np.zeros((36,36),dtype=np.int64)
mask[[1,13,25],:] = [0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,0,
                     0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,0]
a,b = make_h(2)
for index,axes in enumerate(axes_list):
    x = a.transpose(axes).reshape(36,36)
    y = b.transpose(axes).reshape(36,36)
    m = mask.reshape((6,)*4).transpose(axes).reshape(36,36)
    parts = [(x*(1-m),y*(1-m)),(x*m,y*m)]
    coeff = {k:(np.zeros((36,36),np.int64),np.zeros((36,36),np.int64))
             for k in (-1,0,1)}
    for k,(x,y) in enumerate(parts):
        for l,(v,w) in enumerate(parts):
            v,w = conj(v.T,w.T)
            value = mm(x,y,v,w)
            coeff[k-l] = tuple(u+v for u,v in zip(coeff[k-l],value))
    coeff[0] = (coeff[0][0]-36*np.eye(36,dtype=np.int64),coeff[0][1])
    poly = {k:np.zeros(2,np.int64) for k in range(-2,3)}
    for k,(x,y) in coeff.items():
        for l,(v,w) in coeff.items():
            v,w = conj(v,w)
            poly[k-l] += [np.sum(x*v-y*w),np.sum(x*w+y*v+y*w)]
    assert all(v[1] == 0 for v in poly.values())
    values = [Fraction(int(poly[k][0]),36**2) for k in range(-2,3)]
    target = [Fraction(0)]*5 if index == 0 else [0,Fraction(-17,12),Fraction(17,6),Fraction(-17,12),0]
    assert values == target
    print('Laurent coefficients',index,values)
```
## 36. 任意输出下的最优谱粗化与非平坦扇区

### 36.1 模型和精确最优值

逻辑空间有正交扇区标签 $s=1,\ldots,N$。给定正整数 $d_s$ 和有限概率谱
$\lambda_s=(\lambda_{sj})_j$，谱项按非增序排列并按需补零。源与目标等距编码分别为
\[
J_\lambda|s\rangle
=\sum_{a=1}^{d_s}\sum_j\sqrt{\lambda_{sj}/d_s}\,
 |s,a,j\rangle_X|s,a,j\rangle_Y,
\qquad
J_d|s\rangle=d_s^{-1/2}\sum_{a=1}^{d_s}|s,a\rangle_X|s,a\rangle_Y.
\tag{36.1}
\]
不同 $s$ 的物理输出旗标正交。源的 Schmidt 概率谱把每个
$\lambda_{sj}/d_s$ 重复 $d_s$ 次；目标扇区平坦。设
$v_s=(\sqrt{\lambda_{sj}})_j$，$K_{st}=\langle v_s,v_t\rangle$，以及
\[
q_*:=\min_{p\in\Delta_N}p^{\mathsf T}Kp.
\tag{36.2}
\]
允许两侧各自执行任意局部 CPTP 映射、添加并丢弃局部辅助系统，且允许
乘积映射的共享经典随机混合。不允许通信、后选择或额外共享纠缠；输出不必
保持旗标、纯度或任何基扇区的目标态。误差是包含任意被动参考、未除以二的
钻石范数。任意已知的局部基变换可吸收到映射中。

**定理 36.1（全操作最优谱粗化）。** 在上述有限模型中，
\[
\begin{aligned}
\delta_{\rm prod}&:=\inf_{\Lambda_X,\Lambda_Y}
\| (\Lambda_X\otimes\Lambda_Y)\circ\mathcal J_\lambda
       -\mathcal J_d\|_\diamond,\\
\delta_{\rm mix}&:=\inf_{\Phi\in\operatorname{conv}_{\rm fin}
\{\Lambda_X\otimes\Lambda_Y:\Lambda_X,\Lambda_Y\text{ are CPTP}\}}
\|\Phi\circ\mathcal J_\lambda-\mathcal J_d\|_\diamond,\\
&\boxed{\delta_{\rm prod}=\delta_{\rm mix}=2(1-q_*).}
\end{aligned}
\tag{36.3}
\]
一对同时适用于全部扇区的局部拆分映射达到下确界。允许乘积映射的共享
经典随机混合不降低最优值。这个模型不包含任意非平坦目标、一般 LOCC 或
可分操作的全分类。

**证明。** 任取竞争映射的局部 Stinespring 等距，记源态 $J_\lambda|s\rangle$
的扩张输出为 $\Xi_s$。它相对于
$X_{\rm out}E_X\mid Y_{\rm out}E_Y$ 的非零 Schmidt 系数仍为
$\sqrt{\lambda_{sj}/d_s}$，每项重复 $d_s$ 次。只为分析而投影到该扇区的
理想目标，得到未必归一的环境向量
\[
\zeta_s=(\langle J_d s|\otimes I_{E_XE_Y})\Xi_s.
\tag{36.4}
\]
此投影不属于允许的实现协议。令 $Z_s$ 为 $\zeta_s$ 的环境系数矩阵，
$Q_s$ 为 $\Xi_s$ 的系数矩阵在目标扇区两侧物理支撑上的压缩。按目标
物理索引分块，有
$Z_s=d_s^{-1/2}\sum_{a=1}^{d_s}(Q_s)_{aa}$。对环境空间中任意秩 $k$
部分等距 $W$，奇异值迹不等式和压缩的奇异值界依次给出
\[
|\operatorname{Tr}(W^*Z_s)|
=d_s^{-1/2}|\operatorname{Tr}((I_{d_s}\otimes W)^*Q_s)|
\le d_s^{-1/2}\sum_{i=1}^{d_sk}\sigma_i(Q_s)
\le\sum_{j=1}^k\sqrt{\lambda_{sj}}.
\tag{36.5}
\]
最后一步保留了每个源 Schmidt 系数恰重复 $d_s$ 次的结构。Ky Fan 变分
公式遂给 $\sigma(Z_s)\prec_w v_s$。若非负递减向量 $a\prec_w b$，则对
任意非负递减权重 $w$，前缀和的分部求和给 $a\cdot w\le b\cdot w$。
式 (36.5) 的部分迹 Ky Fan 前缀界是 Rastegin 的有限维不等式
(Proposition 1, $p=1$，式 (3.8)) 的归一化矩形情形；矩形算子可嵌入
方阵，压缩与重复 Schmidt 谱再给出本式的最后一项。
先后对两侧使用，再用奇异值迹界，得到无需精确基输出假设的交叉界
\[
|\langle\zeta_t,\zeta_s\rangle|
\le\sigma(Z_t)\cdot\sigma(Z_s)
\le v_t\cdot v_s=K_{st}.
\tag{36.6}
\]

任取 $p\in\Delta_N$，加入被动参考标签，输入
$|\Omega_p\rangle=\sum_s\sqrt{p_s}|s\rangle_R|s\rangle_L$。理想联合输出
$|\Theta_p\rangle=\sum_s\sqrt{p_s}|s\rangle_RJ_d|s\rangle$。实际输出
通过理想纯态投影测试的概率为
\[
F_p=\bigl\|\sum_s p_s\zeta_s\bigr\|^2
\le\sum_{s,t}p_sp_tK_{st}=p^{\mathsf T}Kp.
\tag{36.7}
\]
参考标签使两次振幅匹配产生 $p_s$，所以错误旗标不能在另一逻辑标签下
补偿。理想输出的该测试成功率为一；二元测试和迹距离收缩给竞争信道
的钻石误差至少 $2(1-p^{\mathsf T}Kp)$。取 (36.2) 的最小点即得
(36.3) 的下界。同一个测试对每个竞争乘积信道有效，对其共享经典
随机混合也有效。

为达到下界，两侧同时对所有扇区实行
$|s,a,j\rangle\mapsto|s,a\rangle_{\rm out}|j\rangle_E$，再丢弃环境。
环境态 $\eta_s=\sum_j\sqrt{\lambda_{sj}}|j,j\rangle$ 的 Gram 矩阵
正是 $K$；诱导的逻辑信道为 $\rho\mapsto K\circ\rho$，随后作目标
编码。带参考纯输入 $\sum_s|s\rangle|w_s\rangle$ 的各标签概率为
$p_s=\|w_s\|^2$。输出差的非零谱等于
\[
B_p=D_{\sqrt p}(\mathbf1\mathbf1^{\mathsf T}-K)D_{\sqrt p}.
\tag{36.8}
\]
$B_p$ 是秩一正矩阵减去正半定矩阵，迹为零且至多有一个正本征值，
故 $\|B_p\|_1=2\lambda_{\max}(B_p)$。由于
$\mathbf1\mathbf1^{\mathsf T}-K$ 逐项非负，最大 Rayleigh 向量可取
非负。写 $y_s=\sqrt{p_s}x_s$，则 $\sum_s y_s\le1$；反过来对任意
$y\in\Delta_N$ 取 $p=y$、$x_s=\sqrt{y_s}$ 可取等。因此
\[
\max_p\|B_p\|_1
=2\max_{y\in\Delta_N}y^{\mathsf T}
  (\mathbf1\mathbf1^{\mathsf T}-K)y
=2(1-q_*).
\tag{36.9}
\]
迹范数的最大化覆盖被动参考：混合输入可纯化到参考中，而上述计算
对任意纯输入及其标签向量成立。这一共同局部构造达到下界。证明不需要
$K$ 可逆。有限凸规划的最优性证书可写作
$Kp\ge q\mathbf1$，在 $p_s>0$ 的支撑上取等，且 $q=p^{\mathsf T}Kp$。

### 36.2 平坦秩比与条件性面积窗口

若 $\lambda_s$ 是正整数 $m_s=r_s/d_s$ 项上的均匀谱，则
$K_{st}=\sqrt{\min(m_s,m_t)/\max(m_s,m_t)}$。§34 的指数核计算与
定理 36.1 合用，说明即使基扇区可以输出错误、混态或其他旗标，最优
误差仍为
\[
\delta_*={2T\over1+T},\qquad
T=\sum_i\tanh\bigl((\ell_{i+1}-\ell_i)/4\bigr).
\tag{36.10}
\]
例如 $d=(3,3,3)$、$r=(3,12,48)$ 给
$p_*=(2/5,1/5,2/5)$、$q_*=3/5$、$\delta_*=4/5$。
§35 的条件性动量窗口必要界可在上述全操作模型下使用，而不再要求
竞争映射精确输出每个基扇区；有限调节器、平坦且为整数的实际秩比、
秩匹配 $|\log m_s-\log\mathsf S(P_s)-C_0|\le\eta$ 与两侧独立局部操作仍
必须保留。由这些条件得到同一必要界
$\delta_*\ge1-\exp[-\max(0,\pi Q\Delta P-\eta)]$。
连续 Virasoro 密度不是整数 Hilbert 空间维数；这里没有构造这些
物理匹配条件，也没有解决原始引力 RT。

### 36.3 非平坦稳定量与等熵反例

定义排序平方根谱直径 $D_H=\max_{s,t}\|v_s-v_t\|_2$。由
$\|v_s\|_2=1$ 和 (36.3)，
\[
\delta_*=\max_{p\in\Delta_N}\sum_{s,t}p_sp_t\|v_s-v_t\|_2^2,
\qquad \tfrac12D_H^2\le\delta_*\le D_H^2.
\tag{36.11}
\]
下界在最远两谱上各置一半概率，故即使扇区数和谱维数增长，误差趋零
当且仅当全部排序平方根谱的直径趋零。精确零误差当且仅当这些谱
全部相同；熵相等不满足这个条件。

例如
$\lambda=(1/2,1/8,1/8,1/8,1/8)$ 与
$\mu=(1/4,1/4,1/4,1/4,0)$ 的熵都为 $\log4$，而
$K_{12}=5/(4\sqrt2)$，所以两扇区最优误差为
\[
\delta_*=1-{5\over4\sqrt2}>0.
\tag{36.12}
\]
取两个目标扇区 $d_s=3$，则源、目标面积熵分别同为 $\log12$、
$\log3$，损失面积算符恰为 $(\log4)I$，联合相干粗化仍有正误差。
更强地，偶数 $D\ge4$、$R=D^2/4$ 时，取
$\lambda=(1/2,1/(2R),\ldots,1/(2R))$（末项重复 $R$ 次），
$\mu$ 为秩 $D$ 的均匀谱。两者熵都为 $\log D$，但
\[
K_{12}={3-2/D\over\sqrt{2D}},\qquad
\delta_*=1-{3-2/D\over\sqrt{2D}}\longrightarrow1.
\tag{36.13}
\]
共同拆分构造的任一单侧约化信道仍与理想目标相同，包括与参考的
关联；逻辑非对角项在单侧偏迹中消失。因此单侧熵或中心面积等式
不能认证联合粗化。

现有 `CoherentHistorySchmidt.lean` 的合法词 Schmidt 分解还给出一个
实际谱来源：两个零、两个一的四字母均匀历史，在第一位置和第二位置
切分所得排序谱分别为 $(1/2,1/2)$ 与 $(2/3,1/6,1/6)$。将这两个
实例放入正交标签的源扇区并各自张量平坦目标因子，谱重叠为
$\sqrt3/2$，(36.3) 给最优误差 $1-\sqrt3/2$。这构造了两个带标签
实例，不把同一个四腿系统的不同切分自动识别成一个码。

### 36.4 来源与边界

第 36.1 节的无限制输出优化是本卷指定有限模型中的书面推导；仓内
`CoherentHistorySchmidt.lean` 只证明上述合法历史的振幅和谱权重，
尚未证明 (36.3)--(36.13) 的信道优化、Ky Fan 投影界或误差公式。
Harrow, *Entanglement spread and clean resource inequalities* (2010),
arXiv:0909.1557；Watrous, *Semidefinite Programs for Completely Bounded
Norms*, Theory of Computing 5 (2009), 217--238，分别提供纠缠扩散与
完全有界范数的既有背景。Rastegin, *Relations for Certain Symmetric Norms
and Anti-norms Before and After Partial Trace*, Journal of Statistical
Physics 148 (2012), 1040--1053，Proposition 1 的 $p=1$ 情形给出上述
部分迹 Ky Fan 前缀界。Lin, *Ryu-Takayanagi area from Virasoro modular
data*, arXiv:2606.30723v1，及 Cao--Cheng--Karthikeyan--Li--Preskill,
*State-dependent geometries from magic-enriched quantum codes*,
arXiv:2603.13475v2，讨论不同的物理构造与恢复条件；本节没有把它们的
条件或结论替换为本模型的全操作最优值。

## 追加锚（本行以下为增补区）

### 36.5 有限单纯形变分支配：既有证明的完整应用

令 $I$ 为任意宇宙中的非空有限指标型，$A:I\times I\to\mathbb R$
逐项非负；不要求 $A$ 对称或正半定。定义

$$
\begin{aligned}
\Delta_I&=\{p:I\to\mathbb R:p_i\ge0,\ \sum_i p_i=1\},\\
Q_A(w)&=\sum_{i,j}A_{ij}w_iw_j,\\
R_A(p,x)&=\sum_{i,j}\sqrt{p_i}\sqrt{p_j}A_{ij}
                 \operatorname{Re}(\overline{x_i}x_j).
\end{aligned}
$$

存在同一个 $r\in\Delta_I$，同时满足

$$
\begin{aligned}
&\forall w\in\Delta_I,\quad Q_A(w)\le Q_A(r),\\
&\forall p\in\Delta_I\ \forall x:I\to\mathbb C,\quad
 \sum_i|x_i|^2=1\ \Longrightarrow\ R_A(p,x)\le Q_A(r).
\end{aligned}
$$

$r$ 的存在量词在两组全称量词之前，因而不随 $w,p,x$ 改变。单指标、
零矩阵、$p$ 的零坐标及非对称非负矩阵都在范围内。由非空紧单纯形
上的连续多项式取最大点 $r$。对任意允许的 $p,x$，置
$y_i=\sqrt{p_i}|x_i|$、$m=\sum_i y_i$；Cauchy--Schwarz 给出

$$
0\le m,\qquad
m^2\le\left(\sum_i(\sqrt{p_i})^2\right)
       \left(\sum_i|x_i|^2\right)=1,
\qquad m\le1.
$$

固定 $i_0\in I$，令 $w_i=y_i+(1-m)\mathbf1_{i=i_0}$。则
$w\ge y\ge0$ 且 $\sum_iw_i=1$。逐项使用
$\operatorname{Re}(\overline{x_i}x_j)\le|x_i||x_j|$，乘以非负系数
$\sqrt{p_i}\sqrt{p_j}A_{ij}$ 后求和，得到完整链

$$
R_A(p,x)\le Q_A(y)\le Q_A(w)\le Q_A(r).
$$

这是既有 `FiniteSectorSchurUpper.lean` 的 `schur_upper` 证明中，
局部 `hSchurPureUpper` 内 `hRayleighMax` 的 `hRayleigh` 推导的应用。
任意 $A$ 的范围来自这段局部证明；公开 `schur_upper` 的残余重叠
核假设不能直接替代该范围。紧性、相位界和亏缺填补均沿既有证明
使用，不增加独立的绑定声明。此步骤提供有限扇区被动参考估计的
变分上界，不将 §36.1 的全信道优化或连续引力 RT 当作其结论。

### 36.6 实际有限相位、取向覆盖胶合与隐藏层边界

`https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/fib-canonical-budget/certificate.py` 的 `weight_orbit`
使用初值 $(2,3)$ 及以下模 $m>0$ 递推：

$$
T_m(u,v)=((u+2v)\bmod m,(2u+3v)\bmod m),\qquad
 a_m(0)=(2\bmod m,3\bmod m),\quad a_m(k+1)=T_ma_m(k).
$$

模 $5040=16\cdot9\cdot5\cdot7$ 的最小正返回时间为 80；模
$7,16,9,5$ 的最小正返回时间分别为 $16,8,8,20$。这些是实际
残余对的周期。各表的初行是 $(2,3)$，末行是 $(0,1)$；所有行
在 $[0,m)^2$ 内且互异，逐行递推成立，末行经 $T_m$ 回到初行。
因此递推归纳给出实际迭代，互异性排除更早返回。例如模 7 的
完整 16 行依次为

$$
\begin{aligned}
&(2,3),(1,6),(6,6),(4,2),(1,0),(1,2),(5,1),(0,6),\\
&(5,4),(6,1),(1,1),(3,5),(6,0),(6,5),(2,6),(0,1).
\end{aligned}
$$

记各最小周期为 $N_m$。共同表的第 $k$ 行逐坐标模 $m$ 等于
$a_m(k\bmod N_m)$，给出与递推及闭合边相容的共同到局部投影。

对任意正偶数 $N$，取有限环 $C_N=\{0,\ldots,N-1\}$，
$s_N(i)=(i+1)\bmod N$。两层总空间是 $C_N\times\{0,1\}$，
投影 $\pi(i,b)=i$，提升后继 $F_N(i,b)=(s_N(i),b\mathbin\oplus1)$；
$\oplus$ 表示 Boolean XOR。令 $\epsilon(i)=i\bmod2$，定义

$$
G_N(i,b)=(i,b\mathbin\oplus\epsilon(i)),\qquad
H_N(i,b)=(s_N(i),b).
$$

$G_N$ 为自身的逆，保留投影。普通边的指标奇偶性翻转；闭合边上
$N-1$ 为奇数而 $s_N(N-1)=0$，奇偶性同样翻转。因此

$$
G_NF_N=H_NG_N,\qquad
G_N(0,b\mathbin\oplus1)
=(0,b\mathbin\oplus1)=H_N(G_N(N-1,b)).
$$

这给出包含闭合胶合的等变平凡化，不仅是抽象集合间的双射或偶数
步取向返回。以 $B_m=\{a_m(i):0\le i<N_m\}$ 为实际残余基底，
互异性给出 $O_m:C_{N_m}\to B_m$ 的双射，$O_m(i)=a_m(i)$，且
$T_mO_m=O_ms_{N_m}$。令 $P_m(i,b)=(O_m(i),b)$ 并运输得到
$E_m=P_mG_{N_m}P_m^{-1}$。在实际基底上，
$F_m(q,b)=(T_mq,b\mathbin\oplus1)$、$H_m(q,b)=(T_mq,b)$，则
$E_m$ 保留残余投影，满足 $E_mF_m=H_mE_m$，并有明确闭合方程

$$
E_m(O_m(0),b\mathbin\oplus1)
=(O_m(0),b\mathbin\oplus1)
=H_m(E_m(O_m(N_m-1),b)).
$$

这涵盖实际共同 80 环、局部 16 环及局部 8、8、20 环。共同到局部
投影保留 $b$ 并与提升后继相容；各局部周期为偶数，也与上述奇偶
规范变换相容。

既有 `GoldenScaleHelix.lean` 中状态为 $(\ell,t,b)$，其中
$\ell\in\mathbb N$ 是隐藏层，$t\in\mathbb R$ 是尺度提升；一步为
$S(\ell,t,b)=(\ell+1,t+L,b\mathbin\oplus1)$，$L=2\log\varphi>0$。
有限读出定义为

$$
f_m(\ell,t,b)=(a_m(\ell\bmod N_m),b).
$$

每个 $(O_m(i),b)$ 有原像 $(i,0,b)$，故读出满射；递推及闭合方程
给出 $f_mS=F_mf_m$。有限相位模型由完整螺旋状态的实际等变读出
得到，丢弃尺度提升，仅保留层数模 $N_m$ 与取向。另一方面，归纳
给出 $\operatorname{level}(S^nz)=\operatorname{level}(z)+n$，所以
对每个状态及每个 $n>0$，$S^nz\ne z$。完整隐藏层从无正周期。
既有 `GoldenHelixParityReadout.lean` 的
`golden_helix_even_orientation_completion` 供应任意偶数步取向
返回，特别包括 80 与 16；奇数步取向翻转由其既有奇数定理供应。

此处的平凡覆盖专指所定义的有限有向环与 Boolean 提升。没有独立
定义的几何 Möbius/Klein 覆盖、连续投影或同胚，也不把有限群轨道
解释为瓶面拓扑。奇数翻转环会有非平凡取向单值性，但不是上述
选定的偶数相位环。无关几何实现和连续引力 RT 不由这些应用判定。
完整英文定义与论证见
[有限变分与相位取向说明](../../../Library/QuantumBounds/codex2026finitertvariation.md)。

## 追加锚（本行以下为增补区）

## 37. 原指数权重递推的任意损失坐标

本节沿用第 34 节的相邻指数系数和同一个递推向量，讨论无需排序的坐标恒等式。损失序列可以取任意实值；这扩大的是递推恒等式的适用范围，不把无序向量解释为概率。

## theorem 37.1: 任意长度递推权重的完整坐标

给定任意 $\ell:\mathbb N\to\mathbb R$，令 $a_i=\exp(-(\ell_{i+1}-\ell_i)/2)$。使用原递推 $w^{(m)}=\operatorname{equilibriumWeight}(m,\ell)$，其指标集合是 $\{0,\ldots,m\}$：$w^{(0)}_0=1$，而

$$
w^{(m+1)}_{m+1}=\frac{1}{1+a_m},\qquad
w^{(m+1)}_j=w^{(m)}_j-
\begin{cases}
 a_m/(1+a_m),&j=m,\\
 0,&0\le j<m.
\end{cases}
$$

对所有 $n\in\mathbb N$，阶段 $n+1$ 有 $n+2$ 个坐标，且三个坐标断言同时成立：

$$
w^{(n+1)}_0=\frac{1}{1+a_0},\qquad
w^{(n+1)}_{n+1}=\frac{1}{1+a_n},\qquad
\forall i\in\{0,\ldots,n-1\},\quad
w^{(n+1)}_{i+1}=\frac{1}{1+a_i}+\frac{1}{1+a_{i+1}}-1.
$$

$n=0$ 指两个位置而非单点；这时两个端点都等于 $1/(1+a_0)$，内部指标集合为空。不添加损失单调、严格排序、逆矩阵或权重正性前提。

证明：每个 $a_i$ 都严格正，故 $1+a_i$ 非零。两个位置的第一分量为 $1-a_0/(1+a_0)=1/(1+a_0)$。以后第一位置不再是旧末位，递推保持它。末位公式直接来自递推。旧末位成为内部位置时，其上一阶段值 $1/(1+a_i)$ 减去 $a_{i+1}/(1+a_{i+1})$，得到内部公式；更早的内部位置则保持不变。对阶段作归纳同时得到任意长度的第一和内部关系。

### 37.2 第 34 节有序严格前提下的联系

第 34 节对不同损失排序为 $\ell_1<\cdots<\ell_k$。这里取 $k=n+2$、$\ell_{j+1}=\ell(j)$，则 $a_j=\kappa_{j+1}$，本节的内部位置 $i+1$ 对应原来的一基位置 $i+2$。严格有序时 $0<a_j<1$，所以端点和内部公式都严格正。相同有序指数核的既有平衡行等式给 $Kw^{(n+1)}=\mathbf1$；结合第 34 节在不同位置上的逆核，得到 $w^{(n+1)}=K^{-1}\mathbf1$。这保留了原来有序、不同位置的条件，不给任意损失附加可逆或正概率结论。

命题 37.1 的新内容是同一递推中任意早期坐标经过无界多次增添位置后仍保持其相邻系数公式，属于仓内推导。行等式、有序正性和逆核联系在这里复用；本节不主张文献原创性。完整的物理操作、共同局部实现、参考系统和最优误差仍分别需要第 34—36 节原来的条件及论证。

## 追加锚（本行以下为增补区）

## 38. 最优粗化信道的唯一性与单测试稳健认证

**定义 38.1（编码后信道与共同测试）。** 沿用第 36.1 节的有限谱模型，令扇区集合为非空有限集 $S$，$N=|S|$，目标向量为 $T_s=J_d|s\rangle$，目标信道为 $\mathcal T(X)=J_dXJ_d^*$。残余平方根谱及其核仍记为 $v_s$、$K_{st}=\langle v_t,v_s\rangle$。允许的物理操作仍是两侧局部 CPTP 映射的乘积或有限共享经典随机混合，无通信、后选择或额外共享纠缠。其编码后信道记为 $\mathcal F=\Phi\circ\mathcal J_\lambda$，不要求任何基扇区输出正确。定义

$$
q=\min_{p\in\Delta_S}p^{\mathsf T}Kp,
\qquad \delta_*=2(1-q),
\qquad \mathcal F_K(X)=J_d(K\circ X)J_d^*.
$$

对任一最小点 $p$，取同一个参考输入和理想输出

$$
|\Omega_p\rangle=\sum_s\sqrt{p_s}|s\rangle_R|s\rangle_L,
\qquad |\Theta_p\rangle=\sum_s\sqrt{p_s}|s\rangle_RT_s,
$$

并记二元投影测试的成功概率为

$$
f_p(\mathcal F)=\langle\Theta_p|
(\operatorname{id}_R\otimes\mathcal F)
(|\Omega_p\rangle\langle\Omega_p|)|\Theta_p\rangle.
$$

本节钻石范数均不含二分之一。第 36.1 节给出 $f_p(\mathcal F)\le q$ 及共同最优误差 $\delta_*$；下面研究哪些信道能够达到等号，以及接近等号迫使什么。

**定理 38.2（满支撑测试暴露唯一编码后信道，repo-derived）。** 设 $p$ 为上述二次型的任意最小点，$A=\{s:p_s>0\}$。若 $\|\mathcal F-\mathcal T\|_\diamond=\delta_*$，则

$$
\mathcal F(|s\rangle\langle t|)=K_{st}|T_s\rangle\langle T_t|
\qquad(s,t\in A).
$$

在任一有限乘积混合分解 $\mathcal F=\sum_z w_z\mathcal F_z$ 中，每个 $w_z>0$ 的分量也满足这个矩阵单位等式。若存在满支撑最小点，则在允许类内

$$
f_p(\mathcal F)=q
\quad\Longleftrightarrow\quad
\mathcal F=\mathcal F_K
\quad\Longleftrightarrow\quad
\|\mathcal F-\mathcal T\|_\diamond=\delta_*.
$$

因此 $\mathcal F_K$ 是允许编码后信道凸集的暴露点。这里只断言源编码后的作用唯一，不断言物理局部信道、Kraus 表示、环境等距或编码算符空间之外的作用唯一。满支撑最小点只须存在，不须是唯一最小点。

**证明。** 对每个乘积分量取局部 Stinespring 等距，记第 $s$ 编码基向量的扩张输出为 $\Xi_{zs}$，并置

$$
\zeta_{zs}=(\langle T_s|\otimes I)\Xi_{zs},\qquad
C^z_{st}=\langle\zeta_{zt},\zeta_{zs}\rangle,\qquad
D^z_{st}=K_{st}-\operatorname{Re}C^z_{st}.
$$

第 36.1 节的投影环境 Ky Fan 界给出 $|C^z_{st}|\le K_{st}$，故所有 $D^z_{st}\ge0$。沿同一个参考测试展开，得到

$$
f_p(\mathcal F)=\sum_{z,s,t}w_zp_sp_t\operatorname{Re}C^z_{st},
\qquad q-f_p(\mathcal F)=\sum_{z,s,t}w_zp_sp_tD^z_{st}.
$$

二元测试给出 $\|\mathcal F-\mathcal T\|_\diamond\ge2(1-f_p(\mathcal F))$。达到最优值因而迫使 $f_p(\mathcal F)=q$。非负和为零，故 $w_z>0$ 且 $s,t\in A$ 时 $D^z_{st}=0$。对角项给出 $\|\zeta_{zs}\|^2=1$；$\Xi_{zs}$ 本来是单位向量，正交投影的勾股等式遂给出

$$
\Xi_{zs}=T_s\otimes\zeta_{zs}.
$$

非对角项满足 $\operatorname{Re}C^z_{st}=K_{st}$ 及 $|C^z_{st}|\le K_{st}$，所以 $C^z_{st}=K_{st}$，包括 $K_{st}=0$ 的情形。对 $|\Xi_{zs}\rangle\langle\Xi_{zt}|$ 作环境偏迹即得矩阵单位等式。此推导只用测试等号，故满支撑时 $f_p=q$ 已迫使整个编码后信道为 $\mathcal F_K$。反向由共同达到构造与其范数公式成立。证毕。

**推论 38.3（平坦整数秩的最优性强迫精确基输出，repo-derived）。** 对第 34 节的正整数残余秩 $m_s$，每个最优允许编码后信道都严格等于

$$
X\longmapsto J_d\left(
\bigl(e^{-|\log m_s-\log m_t|/2}\bigr)_{st}\circ X
\right)J_d^*.
$$

特别地，精确输出每个基扇区的目标纯态是最优性的结论，无须作为竞争操作的前提。任意共享经典混合的正权重乘积分量具有同一个编码后作用。

**证明。** 合并相同的 $\log m_s$，在不同的有序值上使用第 34.1 节的严格正平衡概率，再将每个组的质量正地分配给该组所有原标签。核只依赖组标签，所以这仍是最小点，且在原集合上满支撑。只有一个不同秩时，任意满支撑概率都最小。应用定理 38.2。证毕。

**定理 38.4（测试亏缺的平方根认证，repo-derived）。** 固定满支撑最小点 $p$，令 $a=\min_s p_s>0$、$\eta=q-f_p(\mathcal F)\ge0$。则

$$
\boxed{\quad
\|\mathcal F-\mathcal F_K\|_\diamond
\le\min\left\{2,\frac{2+\sqrt{2N}}a\sqrt\eta\right\}.
\quad}
$$

若仅已知 $\|\mathcal F-\mathcal T\|_\diamond\le\delta_*+\epsilon$，其中 $\epsilon\ge0$，则 $\eta\le\epsilon/2$，从而

$$
\|\mathcal F-\mathcal F_K\|_\diamond
\le\min\left\{2,\frac{\sqrt2+\sqrt N}a\sqrt\epsilon\right\}.
$$

此外，第 $s$ 个基输出的目标失败概率 $l_s$ 满足

$$
\sum_s p_s^2l_s\le\eta,\qquad
l_s\le\frac{\eta}{p_s^2}.
$$

任一正权重分量的对应失败概率满足 $l_{zs}\le\eta/(w_zp_s^2)$。结论依赖指定局部操作类和已知模型；这不是对未知全局操作的设备无关认证。

**证明。** 令 $C=\sum_z w_zC^z$、$D_{st}=K_{st}-\operatorname{Re}C_{st}$。上一定理的恒等式给出

$$
D_{st}\ge0,\qquad
\sum_{s,t}p_sp_tD_{st}=\eta,\qquad |C_{st}|\le K_{st}.
$$

对角项就是 $D_{ss}=1-\langle T_s|\mathcal F(|s\rangle\langle s|)|T_s\rangle=l_s$。取非负和的对角子和得 $\sum_sp_s^2l_s\le\eta$，所以 $\sum_s l_s\le\eta/a^2$。对分量不先求和即得 $w_zp_s^2l_{zs}\le\eta$。

将各分量扩张输出放入带正交标记的环境直和，得到编码后信道的一个等距 $V$，以及

$$
\zeta_s=\bigoplus_z\sqrt{w_z}\zeta_{zs},
\qquad W|s\rangle=T_s\otimes\zeta_s.
$$

目标向量正交，且 $\|\zeta_s\|\le1$，故 $\|W\|\le1$。$V-W$ 第 $s$ 列的范数平方为 $l_s$，于是

$$
\|V-W\|^2\le\sum_s l_s\le\eta/a^2.
$$

记 $W$ 给出的完全正、迹不增映射为 $\mathcal F_C(X)=J_d(C\circ X)J_d^*$。展开 $VXV^*-WXW^*$ 为两项并使用迹范数的理想性质，得到

$$
\|\mathcal F-\mathcal F_C\|_\diamond
\le(\|V\|+\|W\|)\|V-W\|
\le 2\sqrt\eta/a.
$$

这里偏迹对任意算子的迹范数收缩可直接由对偶性核对：对任意酉 $U$，$|\operatorname{Tr}(U\operatorname{Tr}_E Y)|=|\operatorname{Tr}((U\otimes I_E)Y)|\le\|Y\|_1$。同一论证保留任意参考因子，不把迹不增的 $W$ 映射冒作信道。

另一方面，$|C_{st}|\le K_{st}\le1$ 给出

$$
|C_{st}-K_{st}|^2\le2K_{st}D_{st}\le2D_{st}.
$$

置 $H=D_{\sqrt p}(C-K)D_{\sqrt p}$，其 Hilbert–Schmidt 范数满足 $\|H\|_{\rm HS}^2\le2\eta$，故 $\|H\|_1\le\sqrt{2N\eta}$。任一归一化纯参考输入可写成 $\sum_s|s\rangle|u_s\rangle$。定义 $B|s\rangle=T_s\otimes u_s/\sqrt{p_s}$；其列因 $T_s$ 正交而正交，所以 $\|B\|^2\le1/a$。这两个 Schur 映射在该输入上的输出差是 $BHB^*$，因而其迹范数不超过 $\sqrt{2N\eta}/a$。

混合密度输入由凸性处理。为覆盖钻石范数中的任意算子，先将 Hermitian 输入作正负谱分解；再对任意 $X$ 添加一个参考二能级系统，使用 Hermitian 块矩阵 $\frac12\left(\begin{smallmatrix}0&X\\X^*&0\end{smallmatrix}\right)$。它的迹范数为 $\|X\|_1$；保 Hermitian 映射后的同形块矩阵具有对应输出的迹范数。这说明上述密度输入界也适用于 $\mathcal F_C-\mathcal F_K$，即使 $\mathcal F_C$ 未必保迹。三角不等式给出所列常数，两个信道的距离另有上界二。最后二元测试界给 $2(1-f_p)\le2(1-q)+\epsilon$，故 $\eta\le\epsilon/2$。证毕。

**命题 38.5（固定两扇区模型中的最优指数，repo-derived）。** 即使固定两个不同的平坦残余秩，定理 38.4 中的平方根指数也不能统一改为任何大于 $1/2$ 的指数。

**证明。** 此时 $K=\left(\begin{smallmatrix}1&k\\k&1\end{smallmatrix}\right)$，$0<k<1$，$\delta_*=1-k$。共同拆分后，在一侧输出旗标施加相位酉 $\operatorname{diag}(1,e^{i\theta})$，得到允许的乘积操作，其编码后信道 $\mathcal F_\theta$ 的非对角系数为 $ke^{i\theta}$，相位符号不影响以下量。

两个标签上，对角为零、非对角系数为 $b$ 的保 Hermitian Schur 差，其不除二钻石范数是 $|b|$：纯参考输入的输出差是非对角块矩阵，迹范数为 $2|b|\sqrt{p_1p_2}\le|b|$，等质量达到。因此

$$
\delta_\theta=\|\mathcal F_\theta-\mathcal T\|_\diamond
=|1-ke^{i\theta}|,
\qquad d_\theta=\|\mathcal F_\theta-\mathcal F_K\|_\diamond
=k|e^{i\theta}-1|.
$$

令 $\epsilon_\theta=\delta_\theta-(1-k)$，直接平方得到

$$
d_\theta^2=k\bigl(2(1-k)\epsilon_\theta+\epsilon_\theta^2\bigr).
$$

故 $\theta\to0$ 时 $d_\theta/\sqrt{\epsilon_\theta}\to\sqrt{2k(1-k)}>0$。对等质量测试，$q=(1+k)/2$ 且 $\eta_\theta=k(1-\cos\theta)/2$，更有精确等式 $d_\theta=2\sqrt{k\eta_\theta}$。两种认证参数都不允许更大的统一指数；这不声称定理 38.4 的常数最优。证毕。

**命题 38.6（无满支撑最小点时的非唯一最优信道，repo-derived）。** 第 36.1 节的允许模型中存在三个扇区、每个目标秩为一的实例，具有两个不同的最优编码后信道。

**证明。** 取排序的平方根谱

$$
v_1=(1,0),\quad v_2=(1/\sqrt2,1/\sqrt2),\quad
v_3=(\cos(\pi/8),\sin(\pi/8)).
$$

令 $k=1/\sqrt2$、$c=\cos(\pi/8)$、$q=(1+k)/2=c^2$。于是

$$
K=\begin{pmatrix}1&k&c\\k&1&c\\c&c&1\end{pmatrix},
\qquad p=(1/2,1/2,0),\qquad Kp=(q,q,c)^{\mathsf T}.
$$

$K\succeq0$ 且 $c>q$，所以单纯形最优性条件证明 $p$ 最小、值为 $q$。对任一概率 $x$，二次型展开中的线性项为 $2(c-q)x_3$，余项非负，因此任何最小点必须有 $x_3=0$；余下两标签二次型的唯一最小点是等质量。故不存在满支撑最小点。

共同拆分给出 $\mathcal F_K$。再在一侧对第三输出旗标施加退相干，使第三标签与前两者的相干乘以 $c$，前两者间相干不变。这是一个 CPTP Schur 映射：其核是两个相同单位向量和另一个与它们重叠为 $c$ 的单位向量之 Gram 矩阵。所得乘积协议的核为

$$
C=\begin{pmatrix}1&k&q\\k&1&q\\q&q&1\end{pmatrix},
\qquad Cp=q\mathbf1.
$$

$C$ 是两个正半定核的 Schur 乘积，正半定且对角为一，所有元素属于 $[0,1]$。对任一概率 $x$，$x^{\mathsf T}Cx=q+(x-p)^{\mathsf T}C(x-p)\ge q$。第 36.1 节的 Schur 范数推导适用于此核，故 $\|\mathcal F_C-\mathcal T\|_\diamond=2(1-q)$。然而 $C_{13}=q<c=K_{13}$，所以两个编码后信道不同。它们在活跃标签 $\{1,2\}$ 上完全相同，保留定理 38.2 的精确范围。证毕。

**来源与适用范围。** 本节复用第 36.1 节的全操作最优值、共同拆分及投影环境界，以及第 34.1 节的正平衡概率；这些前置不作为新增结果。新增的等号分类、完整编码后信道的测试认证、指数最优性和满支撑边界属于本仓推导。Stinespring 表示、完全有界迹范数和一般通道优化的对偶条件属于已有量子信息理论；比较文献为 Watrous, *The Theory of Quantum Information* (2018)，以及 Coutts–Girard–Watrous, *Certifying optimality for convex quantum channel optimization problems*, Quantum 5, 448 (2021), [arXiv:1810.13295](https://arxiv.org/abs/1810.13295)。后者的全信道最优性条件不替代本节局部乘积混合类的投影环境界。本节不分类局部信道在未使用物理输入上的自由度，不包括通信、共享纠缠或任意全局操作，也不建立连续 CFT 与引力 RT 的实现字典。

## 追加锚（本行以下为增补区）

## 39. 任意源谱与平坦目标的共同随机粗化

**定义 39.1（源谱的目标尺寸分块）。** 令 $S$ 为非空有限扇区集，$r_s,d_s$ 为正整数，$\lambda_s=(\lambda_{si})_{0\le i<r_s}$ 为非增概率向量，允许零项。两侧源空间为 $A=\bigoplus_s\mathbb C^{r_s}$，输出空间为 $B=\bigoplus_s\mathbb C^{d_s}$。定义源、目标等距

$$
J|s\rangle=\sum_{i<r_s}\sqrt{\lambda_{si}}|s,i\rangle_X|s,i\rangle_Y,
\qquad T_s=T|s\rangle=\frac1{\sqrt{d_s}}\sum_{a<d_s}|s,a\rangle_X|s,a\rangle_Y.
$$

记相应编码信道为 $\mathcal J$、$\mathcal T$。允许两侧独立 CPTP 映射以及有限共享经典随机混合，不允许通信、后选择或额外共享纠缠，竞争输出不必保持旗标或基扇区纯态。误差仍为包含任意被动参考且不除以二的钻石范数。

置 $M=\max_s\lceil r_s/d_s\rceil$，将每个 $\lambda_s$ 补零到 $d_sM$ 项，并定义

$$
\alpha_{saj}=\sqrt{\lambda_{s,d_sj+a}},\qquad
b_{sj}=\frac1{\sqrt{d_s}}\sum_{a<d_s}\alpha_{saj},\qquad
G_{st}=\sum_{j<M}b_{sj}b_{tj},\qquad
q=\min_{p\in\Delta_S}p^{\mathsf T}Gp.
$$

每个 $b_s$ 非负且非增。分块 Cauchy–Schwarz 给 $\|b_s\|_2^2\le1$，所以 $G\succeq0$、$0\le G_{st}\le1$；此处一般只有 $G_{ss}\le1$。

单扇区的最佳纯目标保真度 $\sum_jb_{sj}^2$ 是 George–Chitambar 的已有结果：其定理 8 的递减分块系数优化经 Cauchy–Schwarz 达到于与 $b_{sj}^2$ 成比例的辅助概率。定理 4 同时给出该保真度目标下 LO 与 LOSR 的等价性。以下结论研究同一个相干多扇区信道与被动参考，不把这一单态公式认作新增结果。精确来源见 [零通信纯态转化](../../../Library/QuantumChannels/george2024zerocommunication.md)。

**定理 39.2（任意源谱的共同 LOSR 最优值，repo-derived）。** 对定义 39.1 的模型，

$$
\boxed{\inf_{\Phi\in\operatorname{conv}_{\rm fin}
\{\Lambda_X\otimes\Lambda_Y:\Lambda_X,\Lambda_Y\ {
m CPTP}\}}
\|\Phi\circ\mathcal J-\mathcal T\|_\diamond=2(1-q).}
$$

一个同时作用于全部扇区的局部坐标拆分，加上至多 $\prod_s d_s$ 个共享循环移位分支，达到此值。不要求源系数恰好重复 $d_s$ 次，也不要求 $r_s/d_s$ 是整数。此值是乘积信道的共同下界，但不声称乘积类总能达到它。

**证明。** 先固定任意乘积竞争操作及其局部 Stinespring 等距。令 $\Xi_s$ 为源列 $J|s\rangle$ 的扩张输出，$\zeta_s=(\langle T_s|\otimes I)\Xi_s$ 为分析用的投影环境向量，$Z_s$ 为其系数矩阵。跨 $X_{\rm out}E_X\mid Y_{\rm out}E_Y$，$\Xi_s$ 的非零奇异值仍为 $\sqrt{\lambda_{si}}$。将系数矩阵压缩到两侧目标 $s$ 旗标得到 $Q'_s$，则

$$
Z_s=\frac1{\sqrt{d_s}}\sum_{a<d_s}(Q'_s)_{aa}.
$$

对环境中的秩 $k$ 部分等距 $W$，$I_{d_s}\otimes W$ 的非零奇异值是一、秩为 $d_sk$。von Neumann 奇异值迹界及压缩不增奇异值给出

$$
|\operatorname{Tr}(W^*Z_s)|
\le\frac1{\sqrt{d_s}}\sum_{i<d_sk}\sigma_i(Q'_s)
\le\frac1{\sqrt{d_s}}\sum_{i<d_sk}\sqrt{\lambda_{si}}
=\sum_{j<k}b_{sj}.
$$

所有序列按需补零。Ky Fan 变分公式给出 $\sigma(Z_s)\prec_w b_s$。对非负递减权重作前缀和的分部求和，先后用于两侧，再用奇异值迹界，得到

$$
|\langle\zeta_t,\zeta_s\rangle|
\le\sigma(Z_t)\mathbin{\cdot}\sigma(Z_s)
\le b_t\mathbin{\cdot}b_s=G_{st}.
$$

这是第 36.1 节同一投影机制在一般源谱上的应用；不把投影当作实现中的后选择。输入 $|\Omega_p\rangle=\sum_s\sqrt{p_s}|s\rangle_R|s\rangle_L$，对理想输出 $|\Theta_p\rangle=\sum_s\sqrt{p_s}|s\rangle_RT_s$ 作投影，成功概率至多 $p^{\mathsf T}Gp$。二元测试给钻石误差至少 $2(1-p^{\mathsf T}Gp)$。取最小点即得 $2(1-q)$。同一个输入与测试对所有竞争乘积操作有效，成功概率又对输出线性，故下界覆盖有限共享混合。

下面构造共同达到操作。每侧在实际源基上定义

$$
E|s,i\rangle=|s,i\bmod d_s\rangle_{
m out}
|\lfloor i/d_s\rfloor\rangle_E.
$$

不同 $(s,i)$ 映到不同 $(s,a,j)$，故 $E^*E=I$，丢弃环境得到局部 CPTP 映射。补零只是系数约定，不添加待输入的物理基向量。令

$$
\psi_{sj}=\sum_{a<d_s}\alpha_{saj}|s,a\rangle_X|s,a\rangle_Y.
$$

两侧拆分后的矩阵单位作用为 $|s\rangle\langle t|\mapsto\sum_j|\psi_{sj}\rangle\langle\psi_{tj}|$。

对每个 $s$ 令 $X_s$ 为 $d_s$ 个输出坐标的循环移位，均匀选择有限随机变量 $h\in\prod_s\mathbb Z/d_s\mathbb Z$。两侧使用同一个 $h$，各自在丢弃环境后施加 $U_h=\bigoplus_sX_s^{h_s}$。这是至多 $\prod_sd_s$ 个乘积 CPTP 映射的有限混合，各分支对所有逻辑输入相同。

取 $\omega_s=e^{2\pi i/d_s}$，定义相关子空间的正交 Fourier 基

$$
T_{sk}=\frac1{\sqrt{d_s}}\sum_a\omega_s^{ka}|s,a\rangle_X|s,a\rangle_Y,
\qquad
c_{sjk}=\frac1{\sqrt{d_s}}\sum_a\alpha_{saj}\omega_s^{-ka}.
$$

这里 $T_{s0}=T_s$、$c_{sj0}=b_{sj}$。$X_s^{h_s}\otimes X_s^{h_s}$ 在 $T_{sk}$ 上乘以 $\omega_s^{-kh_s}$。同扇区平均只保留相同 Fourier 指标；不同扇区的独立 $h_s,h_t$ 平均只保留两者均为零的指标。因此最终编码后信道严格为

$$
\mathcal F_G(X)=T(G\circ X)T^*+\sum_sX_{ss}L_s,
\qquad
L_s=\sum_{k\ne0}\left(\sum_j|c_{sjk}|^2\right)|T_{sk}\rangle\langle T_{sk}|.
$$

$L_s\succeq0$，与全部理想向量 $T_t$ 正交，且 $\operatorname{Tr}L_s=1-G_{ss}$。$d_s=1$ 时非零 Fourier 模集合为空，$L_s=0$、$G_{ss}=1$。整个构造没有连续随机平均或无穷共享随机性。

对任意纯参考输入 $\sum_s|s\rangle|u_s\rangle$，令 $p_s=\|u_s\|^2$。理想减实际输出的理想子空间块等距于

$$
B_p=D_{\sqrt p}(\mathbf1\mathbf1^{\mathsf T}-G)D_{\sqrt p},
$$

其余是正交的负半定泄漏块 $-\sum_s|u_s\rangle\langle u_s|\otimes L_s$，泄漏迹为

$$
\ell_p=\sum_sp_s(1-G_{ss})=\operatorname{Tr}B_p\ge0.
$$

$B_p$ 是秩一正矩阵减正半定矩阵，至多有一个正本征值；其迹非负，所以包括零情形在内，完整输出差的迹范数是

$$
\|B_p\|_1+\ell_p
=2\lambda_{\max}(B_p)-\operatorname{Tr}B_p+\ell_p
=2\lambda_{\max}(B_p).
$$

此处不能将 $B_p$ 当作迹零矩阵。记 $A=\mathbf1\mathbf1^{\mathsf T}-G$，它逐项非负，最大 Rayleigh 向量可取非负。置 $y_s=\sqrt{p_s}x_s$，$\|x\|_2=1$，则 $\sum_sy_s\le1$，填补概率质量不会降低 $y^{\mathsf T}Ay$。反向对任意 $z\in\Delta_S$ 取 $p=z$、$x=\sqrt z$，于是

$$
\max_p\lambda_{\max}(B_p)=\max_{z\in\Delta_S}z^{\mathsf T}Az=1-q.
$$

混合参考输入由凸性处理；任意算子输入先作 Hermitian 正负谱分解，再对 $\frac12\left(\begin{smallmatrix}0&X\\X^*&0\end{smallmatrix}\right)$ 加一个参考二能级系统即可归约到该界，保持对应迹范数。因此任意有限被动参考均已覆盖，候选钻石误差恰为 $2(1-q)$，达到下界。证毕。

**推论 39.3（非整数平坦秩比，repo-derived）。** 若每个源谱在 $r_s$ 项上均匀，写 $r_s=d_sm_s+k_s$、$0\le k_s<d_s$，则定理 39.2 的核由

$$
b_{sj}=\begin{cases}
\sqrt{d_s/r_s},&j<m_s,\\
k_s/\sqrt{d_sr_s},&j=m_s,\\
0,&j>m_s
\end{cases}
$$

直接计算。单扇区的有限混合最优误差为 $2k(d-k)/(rd)$。若所有 $k_s=0$，则恢复第 34—36 节的残余 Gram 核，全部 $L_s$ 消失，达到操作可取原来的单个乘积信道。

**证明。** 将均匀源幅度代入分块定义。单扇区 $q=(md^2+k^2)/(rd)$，代入定理 39.2。所有余数为零时，各有效块内幅度相等，非零 Fourier 模全部为零。证毕。单态保真度部分仍归属 George–Chitambar 定理 8；这里的非整数多扇区公式是共同信道定理的应用。

**命题 39.4（共享随机性可以严格改善粗化，repo-derived）。** 允许模型中存在共享随机混合最优误差严格小于乘积最优误差的实例；这种严格差异也存在于满 Schmidt 秩三的源到平坦秩二目标之间。

**证明。** 先取单扇区积态源及 Bell 二维目标。定理 39.2 给混合误差一；显式两分支制备 $(|00\rangle\langle00|+|11\rangle\langle11|)/2$ 达到它。乘积操作只能输出 $\tau\otimes\sigma$。密度矩阵对构成紧集，迹距离连续，故乘积最小值 $\mu$ 达到。若 $\mu=1$，理想投影测试迫使

$$
\frac12\operatorname{Tr}(\tau\sigma^{\mathsf T})\ge\frac12.
$$

但 $\operatorname{Tr}(\tau\sigma^{\mathsf T})\le\lambda_{\max}(\sigma)\le1$。等号迫使 $\sigma$ 为纯态，且 $\tau$ 支撑于 $\sigma^{\mathsf T}$ 的同一一维空间。输出因而为纯的对齐积态，与 Bell 态的平方重叠为 $1/2$，其不除二迹距离是 $\sqrt2>1$，矛盾。因此 $\mu>1$。

在固定三维源空间中，以

$$
|\psi_\epsilon\rangle=\sqrt{1-\epsilon}|00\rangle
+\sqrt{\epsilon/2}|11\rangle+\sqrt{\epsilon/2}|22\rangle,
\qquad 0<\epsilon<2/3
$$

替换积态。它具有满 Schmidt 秩三，与积态的迹距离为 $2\sqrt\epsilon$。任意乘积信道的迹距离收缩及三角不等式给 $\delta_{\rm prod}(\epsilon)\ge\mu-2\sqrt\epsilon$；分块公式则给

$$
\delta_{\rm mix}(\epsilon)=1-\sqrt{2\epsilon(1-\epsilon)}<1.
$$

所以 $0<\epsilon<\min\{2/3,((\mu-1)/2)^2\}$ 时，源秩三大于目标秩二，严格差异仍在。此为由紧性正差给出的存在区间，不声称已求出 $\mu$ 或区间的显式有理端点。它不与 LO、LOSR 最佳纯目标保真度相等矛盾：纯目标保真度是线性目标，迹距离一般不是。证毕。

**来源与范围。** 单态分块保真度、Stinespring 表示、Ky Fan 与 von Neumann 奇异值界、有限 Fourier 正交性均复用已有结果。新增的承重内容是一个共同相干多扇区实现、正交泄漏的迹补偿及包含任意被动参考的精确混合最优值。目标仍须逐扇区平坦；任意非平坦目标、混合源、一般 LOCC 或额外纠缠辅助的优化不在结论内。单扇区 trace-distance 值也可由已有保真度及保持目标的相关酉平均得到，不作为独立文献原创性主张。本节不建立连续 CFT 或引力 RT 字典。

## 追加锚（本行以下为增补区）

## 40. 有限共享随机性的分支压缩与精确障碍

**定理 40.1（受控循环移位的精确判据）。** 沿用定理 39.2 的共同块拆分。令每个扇区 $s$ 的目标维数为 $d_s$，并考虑一个均匀分布的单循环共享随机变量 $h\in\mathbb Z/L\mathbb Z$，其中 $d_s\mid L$，两侧在扇区 $s$ 上同时施加坐标循环移位 $h\bmod d_s$。若要求该有限混合对**每一种允许的源谱**都在所有编码矩阵单位上产生定理 39.2 的目标信道 $\mathcal F_G$（包括消除不同扇区之间全部非零 Fourier 模），则当且仅当

$$
\gcd(d_s,d_t)=1\qquad\text{for every }s\ne t.
$$

在这一情形，取 $L=\operatorname{lcm}_s d_s=\prod_s d_s$ 即可；所以原来的随机支撑可由一个循环表述而不增加分支数。若某一对 $d_s,d_t$ 有公因子 $g>1$，任意这样的单循环平均都保留一项跨扇区 Fourier 模；因此对某个允许源谱（且该碰撞模的两个系数非零）不能实现定理 39.2 的 $\mathcal F_G$。对一个固定的特殊源谱，碰撞模的系数可能恰为零，此时不能从 gcd 单独推出失败。

**证明。** 扇区 $s$ 的 Fourier 模 $k\in\mathbb Z/d_s\mathbb Z$ 在移位下获得特征值 $\exp(2\pi i kh/d_s)$。平均跨扇区 $(s,t)$ 的模 $(k,l)$ 时，所得系数为

$$
\frac1L\sum_{h=0}^{L-1}
\exp\!\left(2\pi i h\left(\frac{k}{d_s}-\frac{l}{d_t}\right)\right),
$$

等于 $1$ 当且仅当 $k/d_s-l/d_t\in\mathbb Z$，否则为零。因为 $0\le k/d_s,l/d_t<1$，这里只可能相等。若 $\gcd(d_s,d_t)=1$，两个分数的最小分母互质，故相等只在 $k=l=0$。这保留正是 $b_{sj}b_{tj}|T_s\rangle\langle T_t|$ 的目标项。

反之，若 $g>1$，令 $k=d_s/g$、$l=d_t/g$。二者均为合法非零模且 $k/d_s=l/d_t=1/g$，所以该跨扇区项平均后系数为 $1$。取各自首个目标块内具有两个不等幅坐标的源谱，使该碰撞模的 Fourier 系数均非零；该项不为零，故单循环不能对所有源谱给出 $\mathcal F_G$。证毕。

**推论 40.2（两扇区受控移位族的最小支撑）。** 对两个扇区 $s,t$，令 $H$ 为有限群，并令控制移位由满射同态 $\pi_s:H\twoheadrightarrow\mathbb Z/d_s\mathbb Z$、$\pi_t:H\twoheadrightarrow\mathbb Z/d_t\mathbb Z$ 给出。若 $H$ 平均必须消灭所有非零跨扇区 Fourier 模，则联合同态

$$
\Pi:H\longrightarrow\mathbb Z/d_s\mathbb Z\times\mathbb Z/d_t\mathbb Z
$$

必须满射。因此 $|H|\ge d_sd_t$，且 $H=\mathbb Z/d_s\mathbb Z\times\mathbb Z/d_t\mathbb Z$ 达到下界。

**证明。** 若 $\Pi(H)$ 是真子群，其湮灭子中存在非平凡角色 $(k,l)$。满射性排除了 $k=0$ 或 $l=0$ 的情形，所以 $k,l$ 都非零；该角色正是一个非零跨扇区 Fourier 模，并在 $H$ 上恒为一，矛盾。故 $\Pi$ 满射，按基数得到下界。证毕。

For three or more sectors, the analogous statement requires an explicit hypothesis that the joint map is surjective onto the full product (or an equivalent annihilator condition for every nonempty multi-coordinate support). Pair-supported character cancellation alone is insufficient: for example $H=\{(x,y,z)\in(\mathbb Z/2)^3:x+y+z=0\}$ has order $4<8$.

**范围。** 这是 §39 任意源谱相干信道的有限特征实现定理。它不对任意乘积信道的分支数给出下界，也不改变精确钻石范数最优值；不增加 CFT、引力、通信辅助或共享纠缠的解释。

## 41. 全多坐标特征湮灭下的多扇区最小支撑

**定理 41.1（完整多坐标正交性的充要条件）。** 设 $S$ 为有限扇区集，$d_s\ge2$，$H$ 为有限阿贝尔群。每个扇区的受控循环移位由满射同态
$$
\pi_s:H\twoheadrightarrow\mathbb Z/d_s\mathbb Z
$$
给出，并令联合同态为 $\Pi=(\pi_s)_s:H\to A:=\prod_{s\in S}\mathbb Z/d_s\mathbb Z$。令 $h$ 在 $H$ 上均匀分布。对 $A$ 的角色 $\chi=(\chi_s)_s\in\widehat A=\prod_s\widehat{\mathbb Z/d_s\mathbb Z}$，定义 $\operatorname{supp}\chi=\{s:\chi_s\ne1\}$。则对给定的 $(H,\Pi)$，下列两条件等价：
1. 对每个 $\chi\in\widehat A$ 满足 $|\operatorname{supp}\chi|\ge2$，有 $|H|^{-1}\sum_{h\in H}\chi(\Pi(h))=0$；
2. $\Pi$ 满射。
此外，任一满足这些条件的实现都有 $|H|\ge|A|=\prod_s d_s$，且下界由 $H=A$、$\Pi=\mathrm{id}_A$ 达到。

因此，对于 §39 的任意源谱，若要求一个有限受控移位混合消灭全部非零多坐标 Fourier 模，而不仅是两坐标模，则乘积群既是充分实现，也是该实现类中的最小支撑。若各 $d_s$ 两两互质，Chinese remainder theorem 将这个乘积群识别为单个循环群 $\mathbb Z/\prod_s d_s\mathbb Z$；若存在公因子，单循环方案仍受定理 40.1 的碰撞障碍约束。

**证明。** $1\Rightarrow2$：若 $\Pi(H)$ 是直积 $A$ 的真子群，则有限阿贝尔群的角色分离性给出一个非平凡角色 $\chi\in\widehat A$，在 $\Pi(H)$ 上恒等于 $1$。由于每个 $\pi_s$ 满射，$\chi$ 不可能只在一个坐标上非平凡：若其唯一非平凡坐标为 $s$，则 $\chi_s\circ\pi_s$ 仍是 $\mathbb Z/d_s\mathbb Z$ 上的非平凡角色，不能在 $H$ 上恒为 $1$。所以 $|\operatorname{supp}\chi|\ge2$，与条件 1 矛盾。$2\Rightarrow1$：满射时 $\Pi(h)$ 在 $A$ 上均匀，非平凡角色的均匀 Haar 平均为零。满射还给出 $|H|\ge|A|$；取 $H=A$ 与恒等联合同态达到下界。证毕。

**推论 41.2（§39 的多扇区充分条件）。** 若 $d_s$ 两两互质，则对任意有限源谱族，取 $H=\mathbb Z/L\mathbb Z$、$L=\prod_sd_s$，并令扇区 $s$ 的移位参数为 $h\bmod d_s$。均匀循环混合消灭全部非零多坐标 Fourier 模，故严格复现 §39 的共同信道 $\mathcal F_G$。其共享随机分支数为 $L$，并且在完整多坐标正交条件下达到定理 41.1 的支撑下界。

**范围。** 这里的最小性只针对受控移位与完整多坐标特征湮灭条件，不是对任意 LOSR 或一般乘积信道分支数的下界。结论保持 §39 的平坦逐扇区目标与有限维模型，不引入 CFT、引力或通信辅助解释。

## 42. 控制器商的精确分支资源

**定理 42.1（去重控制与商群资源）。** 设 $H$ 为有限阿贝尔控制器，$A=\prod_{s\in S}\mathbb Z/d_s\mathbb Z$，且 $\Pi:H\to A$ 为各扇区循环移位参数的联合同态。记 $K=\operatorname{im}\Pi$、$N=\ker\Pi$。令 $\{\Lambda_h\}_{h\in H}$ 为由 $h$ 控制的乘积 CPTP 映射，其中 $\Lambda_h$ 只通过 $\Pi(h)$ 作用。则：

1. 控制器标签按 $\Pi(h)$ 去重后恰有 $|K|$ 个不同的受控移位标签；若记由标签诱导的 CPTP 表示为 $\rho:K\to\operatorname{CPTP}$，则实际不同通道数为 $|\rho(K)|\le|K|$。在标准全输出循环移位且各 $d_s\ge2$ 的忠实表示下，$|\rho(K)|=|K|$。
在下式中记 $\Lambda_k:=\rho(k)$。
2. $h\mapsto\Pi(h)$ 将 $H$ 的均匀分布推前为 $K$ 上的均匀分布，故
   $$|H|^{-1}\sum_{h\in H}\Lambda_h=|K|^{-1}\sum_{k\in K}\Lambda_k.$$
3. 由 $H/N\cong K$，用商控制器 $H/N$ 实现同一混合且恰有 $|K|$ 个控制标签；实际通道分支数为 $|\rho(K)|$。于是原始控制器大小 $|H|$ 不是该受控移位表示的资源成本：标签成本是 $|K|$，通道成本是 $|\rho(K)|$。

若每个坐标投影 $\pi_s$ 满射且要求湮灭全部支撑至少两个坐标的角色，则 $K=A$，从而精确成本为 $|K|=\prod_s d_s$。这与 §41 的最小支撑结论一致，同时允许 $|H|>|K|$ 的冗余控制器。

**证明。** 同态的纤维均为 $N$ 的陪集，故每个 $k\in K$ 有恰好 $|N|$ 个原像；这给出均匀推前公式。控制作用只依赖 $\Pi(h)$，故标签去重和逐项合并成立。第一同构定理给出 $H/N\cong K$，把每个陪集标记为其像即得商控制器。最后，在满射坐标投影与全多坐标角色湮灭条件下，§41.1 的 (1)⇔(2) 应用于 $K\hookrightarrow A$，得到 $K=A$；因此 $|K|=\prod_s d_s$。本定理只计算受控移位表示的分支资源，不给任意 LOSR 分支数下界。

**范围。** 结论针对有限共享经典控制与受控循环移位的表示成本；不扩展 §39 的钻石范数最优性，不涉及一般 LOSR、通信或共享纠缠，也不引入 CFT/引力解释。

## 43. 未湮灭特征的可审计误差下界

**定理 43.1（受控移位残余特征的钻石下界）。** 令 $A$ 为有限阿贝尔群，$K\le A$，$\widehat A$ 为其角色群，且在 $\mathcal H=\ell^2(\widehat A)$ 上定义
$$
U_u|\chi\rangle=\chi(u)|\chi\rangle,\qquad
\mathcal D_K(X)=|K|^{-1}\sum_{u\in K}U_uXU_u^* .
$$
记 $m_K(\eta)=|K|^{-1}\sum_{u\in K}\eta(u)$。则
$$
\mathcal D_K(|\chi\rangle\langle\psi|)
 =m_K(\chi\psi^{-1})|\chi\rangle\langle\psi|.
$$
若 $\eta=\chi\psi^{-1}\in K^\perp\setminus\{1\}$，则对理想全群平均 $\mathcal D_A$，
$$
\|\mathcal D_K-\mathcal D_A\|_\diamond\ge1 .
$$
更一般地，若在某个编码子空间上实际通道与 $\mathcal D_K$ 的该矩阵单位系数为 $h$（理想通道系数为零），则相同二维测试给出钻石距离下界 $|h|$。

**证明。** 角色正交性给出 $m_K(\eta)=1$ 当且仅当 $\eta\in K^\perp$，否则为零；对 $A$ 则 $m_A(\eta)=0$ 对每个非平凡 $\eta$。取归一化输入
$$
|v\rangle=(|\chi\rangle+|\psi\rangle)/\sqrt2,qquad \rho_v=|v\rangle\langle v|.
$$
当 $\eta\in K^\perp\setminus\{1\}$ 时，$(\mathcal D_K-\mathcal D_A)(\rho_v)=\tfrac12(|\chi\rangle\langle\psi|+|\psi\rangle\langle\chi|)$。其在 $\operatorname{span}\{|\chi\rangle,|\psi\rangle\}$ 上本征值为 $+1/2,-1/2$，故迹范数为 $1$；输入归一化，遂钻石范数至少为 $1$。若该 surviving coefficient 为 $h$，同一计算的两个本征值为 $\pm|h|/2$，得到下界 $|h|$。被动参考系统不改变下界，因钻石范数取所有参考输入的上确界。证毕。

**与 §39--§42 的接口。** 共同受控移位混合在 Fourier 矩阵单位上恰以 $m_K(\eta)$ 乘法。故 $K^\perp$ 中任一支撑至少两个扇区的角色给出一个可直接测试的残余相干；固定源谱时 $h$ 是相应实际编码系数，不能无条件替换为 $1$。普适任意源谱的失败需另取一个允许谱使 $h\ne0$；定理 40.1 的 universal 量词正是这一额外步骤。结论只给受控移位表示的误差证书，不给任意 LOSR 下界。

## 44. 受控移位层叠的残余特征单调性

**定理 44.1（多层平均的精确合成）。** 对有限阿贝尔群 $A$ 的子群 $K_1,\ldots,K_m$，令 $\mathcal D_K$ 如定理 43.1。则
$$
\mathcal D_{K_m}\circ\cdots\circ\mathcal D_{K_1}
=\mathcal D_{K_1+\cdots+K_m}.
$$
在角色矩阵单位上，合成乘子为
$$
\prod_{j=1}^m m_{K_j}(\eta)
=\mathbf 1_{(K_1+\cdots+K_m)^\perp}(\eta).
$$
因此残余特征集合为 $(K_1+\cdots+K_m)^\perp=\bigcap_jK_j^\perp$，随层数增加单调缩小；当且仅当 $K_1+\cdots+K_m=A$ 时，合成等于理想全群平均 $\mathcal D_A$。

**证明。** 对 $E_{\chi,\psi}$，定理 43.1 给出每层乘子 $m_{K_j}(\chi\psi^{-1})$。角色在 $K_j$ 上的均匀平均是 $1$（当且仅当 $\chi\psi^{-1}\in K_j^\perp$）或 $0$，故乘积是交集指标。有限阿贝尔群对偶性给出 $(\sum_jK_j)^\perp=\cap_jK_j^\perp$；矩阵单位构成全矩阵代数基，遂得通道恒等式。

**推论 44.2（误差证书的层叠单调性）。** 若某个编码相干矩阵单位在第 $j$ 层的实际系数为 $h_\eta$，则经过这些平均层后，其相对 $\mathcal D_A$ 的系数为
$$
h_\eta\mathbf 1_{(\sum_jK_j)^\perp}(\eta).
$$
定理 43.1 的二维输入因此给出下界 $|h_\eta|$，但仅对仍在交集中的角色成立。增加一层只能删除残余证书，不能增加该类下界；若和为 $A$，所有残余证书同时消失。

**范围与非可加性。** 这是受控移位 Schur 平均的精确组合律，不是任意 LOSR 通道的误差可加定理。重复同一层满足 $\mathcal D_K^2=\mathcal D_K$，故即使每层距理想通道的钻石范数为 $1$，总误差仍为 $1$ 而非累加。结论只针对角色支撑及相应 $h_\eta$ 证书。

## 追加锚（本行以下为增补区）
