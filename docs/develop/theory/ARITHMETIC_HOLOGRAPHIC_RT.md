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

**命题 2.2（局部完美性和乘积群）。** $T_G$ 是 AME$(4,|G|)$，任意单方约化态为 $I_{|G|}/|G|$；按参与方重组时，$T_{G\times H}=T_G\otimes T_H$。

**证明。** 乘以 $2$ 是奇数阶群的自同构。四个线性形式 $x,y,x+y,x+2y$ 中任取两个，其系数行列式为 $\pm1$ 或 $\pm2$，因此任意二腿坐标映射都是双射。二对二偏迹消去所有交叉项，得到 $|G|^2$ 个相等对角项；进一步偏迹给出单腿结论。乘积群的求和与坐标逐分量分离。张量视为从至多两腿到其余腿的映射时，乘以适当正常数即为等距。证毕。

仓库编码

$$
V|s\rangle=3^{-1/2}\sum_j|j,j+s,j+2s\rangle
$$

的 Choi 态交换前两腿即为 $T_3$。这是后续网络与已有量子编码的实际对象对应。

## 3. 有限交换群二次历史态的完整谱

**定理 3.1（核、双字符与谱）。** 设 $V,X,Y$ 为有限交换群，群同态 $A:V\to X$、$B:V\to Y$ 的联合映射单射。设 $q:V\to U(1)$、$q(0)=1$，且

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

**定理 4.1（普通奇环）。** 普通缝合 $x_L=x_0$ 的归一化态为

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

**定理 4.3（精确相位亏损与全区域判据）。** 令

$$
c_k=2\alpha+(-1)^L(2^{-k}+2^{-(L-k)})\in R_d,\quad0\le k\le L.
$$

若区域 $C$ 在每个顶点恰选一条外腿，其中 $k$ 条是 $b_i$，则

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

**推论 4.4（精度斜率）。** 固定奇素数 $p,L$、整数 $\alpha,k$，把 $c_k$ 视为 $\mathbb Z_p$ 元素，$\nu=v_p(c_k)$，$v_p(0)=\infty$。则

$$
S_n(C)=[Ln-\min(n,\nu)]\log p.
$$

$c_k\ne0$ 时，$n\ge\nu$ 后绝对亏损稳定为 $\nu\log p$，且 $S_n(C)/(n\log p)\to L$；$c_k=0$ 时 $S_n(C)=(L-1)n\log p$。这是谱计数的精度渐近；与态和通道的精度相容关系在第 12 节另行构造。

## 5. 所有奇数维数的全区域 RT 构造

**引理 5.1（非剩余证书及其计数）。** 对奇素数 $p$，令 $a=2^{-L}\in\mathbb F_p^\times$。若 $\chi_p(\alpha^2-a)=-1$，则所有 $c_k\ne0\pmod p$。这样的 $\alpha$ 恰有 $(p-\chi_p(a))/2>0$ 个。

**证明。** 若 $c_k=0$，令 $x=2^{-k}$、$t=-2(-1)^L\alpha$，则 $x+a/x=t$。多项式 $X^2-tX+a$ 有根，但判别式 $4(\alpha^2-a)$ 是非平方，矛盾。计数方面，$y^2=x^2-a$ 等价于 $(x-y)(x+y)=a$，共有 $p-1$ 对解，故 $\sum_x\chi_p(x^2-a)=-1$。零点数 $N_0=1+\chi_p(a)$，结合 $N_++N_-+N_0=p$、$N_+-N_-=-1$ 得 $N_-=(p-\chi_p(a))/2$。证毕。非剩余证书是充分条件，未声称它对有限的 $k$ 集合也必要。

**定理 5.2（全奇数维数）。** 对任意奇数 $d\ge3$、$L\ge3$，存在一个与边界区域无关的 $\alpha\in R_d$，使 $\Psi^\alpha_{d,L}$ 对全部 $C$ 同时满足

$$
S(\rho_C)=m(C)\log d.
$$

对固定 $p,L$，一个整数 $\alpha$ 可同时用于全部 $d=p^n$。

**证明。** 对每个 $p\mid d$ 用引理 5.1 选 $\alpha_p$，再用 CRT 取 $\alpha\equiv\alpha_p\pmod p$。所有 $c_k$ 不被任何 $p\mid d$ 整除，故在 $R_d$ 中为单位，应用定理 4.3。固定 $p,L$ 时任一整数提升在所有 $p^n$ 中仍满足同一单位判据。证毕。

**推论 5.3（三进显式规则）。** $d=3^n$ 时可取 $L$ 奇数用 $\alpha=1$、$L$ 偶数用 $\alpha=0$。因为模 $3$ 时 $2^{-1}=-1$，奇环的 $c_k=2$，偶环的 $c_k=2(-1)^k$，均为单位。

**推论 5.4（附树单环）。** 在环的外部腿上接任意有限树，所有内部顶点仍四价且使用 $T_d$，悬空腿全部作为边界。环顶点保留指定的环内腿，树上腿排列任意固定；保留上述单边缝合，则整个装饰图对全部区域仍满足同一 RT 等式。

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

**定理 6.1（最小输出熵）。** 对每个归一化纯态 $\varphi$，

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

**推论 6.2（普通高位偏迹）。** 若两侧使用 $W|a+db\rangle=|a\rangle|b\rangle$ 后丢弃高位，则输出有 $p^2$ 个本征值 $p^{-2}$，$S=2\log p$、$\operatorname{Tr}\rho^2=p^{-2}$。

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

**定理 7.1。** 两族通道 CPTP、满射且非恒定，对 $e\mid d\mid D$ 在全部输入矩阵上严格满足 $\mathcal C^j_{d,e}\mathcal C^j_{D,d}=\mathcal C^j_{D,e}$。此外

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

**定理 8.2（三挠求值）。** 对 $G[3]=\{a\in G:3a=0\}$，

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

**推论 8.3（相同熵、不同局部等价类）。** $T_9$ 与 $T_3\otimes T_3$ 不局部幺正等价，因为

$$
I(T_9)=3^{-10}=1/59049,\qquad I(T_3\otimes T_3)=3^{-8}=1/6561.
$$

两态都是 AME$(4,9)$，全部子系统谱相同：一方熵 $\log9$，两方熵 $2\log9$，三方非零谱由纯性决定。更一般地，$n\ge2$ 时 $T_{3^n}$ 与 $T_3\otimes T_{3^{n-1}}$ 不局部等价；未据此分类任意高维 AME 因子。

**推论 8.4（定量局部分离）。** 对任意四方局部幺正 $U$，两态的迹距离至少 $1/59049$。

**证明。** $\|W\|_\infty=1$ 和张量积望远镜展开给出 $|I(\rho)-I(\tau)|\le4\|\rho-\tau\|_1$。不变量差为 $8/59049$，而迹距离为迹范数的一半。证毕。此界针对局部幺正分解，不是一般近似通道的误差界。

## 9. 顶点纯态粗化：独立操作障碍与联合进位修正

**引理 9.1（纯 AME 输出的因子化）。** 设 $D=de$，$\psi$ 为 AME$(4,D)$，$\varphi$ 为 AME$(4,d)$。四个独立局部 CPTP 通道能够把 $\psi$ 精确变成纯态 $\varphi$，当且仅当 $\psi$ 局部幺正等价于按参与方重组的 $\varphi\otimes\eta$，其中 $\eta$ 为某个 AME$(4,e)$。

**证明。** 局部 Stinespring 等距 $V_i$ 给出纯化。纯输出迫使 $(\otimes_iV_i)|\psi\rangle=|\varphi\rangle\otimes|\eta\rangle$。单方约化态满足

$$
V_iV_i^*/D=(I_d/d)\otimes\eta_i.
$$

左侧为秩 $D$ 的归一化投影，故 $\eta_i$ 恰有 $e$ 个本征值 $1/e$。在其支撑内 $V_i$ 成为 $\mathbb C^D\simeq\mathbb C^d\otimes\mathbb C^e$ 的幺正。比较二方最大混合态，得到 $\eta_{ij}=I_{e^2}/e^2$。反向实施局部因子化再丢弃环境即得。证毕。

**定理 9.2（九维循环顶点障碍）。** 不存在四个独立局部 CPTP 通道把 $T_9$ 精确变成任意 AME$(4,3)$ 纯态。

**证明。** [RRKL23] Theorem 1 已证明所有 AME$(4,3)$ 局部幺正等价。引理 9.1 因而迫使 $T_9$ 局部等价于 $T_3\otimes T_3$，与推论 8.3 矛盾。证毕。

此处不要求保留余数，也不限制 Fourier 或 Clifford 操作。局部辅助系统和丢弃均含在 CPTP 中。共享经典随机的乘积通道混合也不可能，因为纯输出的每个正权分支必须输出同一纯态。通信、自适应 LOCC、共享纠缠、联合门、混合或近似输出均不在排除范围。第 7 节单边通道塔不能仅靠四条腿独立粗化实现 $T_9\mapsto T_3$；这不是任意整体网络粗化的不存在定理。与 $T_3\otimes T_3$ 可直接丢弃一层相比，也证明全部二分谱不能决定粗化能力。

**定理 9.3（联合进位消除）。** 取奇数 $d,e\ge3$、$D=de$。每条腿分解为 $W|a+db\rangle=|a\rangle_d|b\rangle_e$。写 $x=a+db,y=c+df$，并令

$$
r=(a+c)\bmod d,\quad s=(a+2c)\bmod d,\quad
\kappa_1=(a+c-r)/d,\quad\kappa_2=(a+2c-s)/d.
$$

$(r,s)$ 唯一确定 $a=(2r-s)\bmod d,c=(s-r)\bmod d$，故也确定两进位。在第三、第四参与方上取联合置换

$$
C_{d,e}:|r,k\rangle_3|s,h\rangle_4
\mapsto|r,k-\kappa_1(r,s)\rangle_3|s,h-\kappa_2(r,s)\rangle_4,
$$

高位取模 $e$。按低、高层重组后，

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

**定理 10.1（有限维精确二阶矩）。** 逐个样本 $Z=d^{-2L}$，且

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

所以 $\mathbb E N_A=2d^{-5L}$，除以常数 $Z^2=d^{-4L}$ 得结论。这里没有用期望之比替代随机比值。证毕。

**推论 10.2（明确谱尺度）。** 对 $N=d^L$，

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

后式来自 Jensen 和 $S\ge S_2$。领先熵斜率与完整谱平坦性不同。该区域至少有内部顶点全部归左或全部归右两个同容量最小割，不满足 [TPTN26] 第 5.2 节式 (5.23) 前的无领先简并条件。未从二阶平均值推出其他谱距离的概率极限。

**推论 10.3（几乎处处非平坦）。** 奇数 $d$、所有顶点取 $T_d$ 时，内部 Haar 乘积测度下 $\rho_A$ 几乎处处满秩且非平坦。

**证明。** 定理 5.2 给出一个参数点使 $\rho_A=I_N/N$，故连通实解析流形 $U(d)^L$ 上的 $\det\rho_A$ 不恒为零。其零集测度为零。定理 10.1 又保证非负实解析函数 $\operatorname{Tr}\rho_A^2-1/N$ 不恒为零，其零集也为零测。两者合起来即得。未声称每个具体参数点都非平坦。证毕。

**命题 10.4（六 qutrit 的精确样本）。** 取 $d=L=3$，两条内部边恒等，另一条为 $F_3\operatorname{diag}(1,1,-1)$。归一化态为

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

**推论 11.3。** $z\ne1$ 时 $U_3(z)$ 不与任何二幺正矩阵局部等价，因而不与任何 $\mathcal H(\boldsymbol\alpha),U_1,U_2$ 局部等价。$z=1$ 时与 $U_1,U_2$ 的分离见证书 11.1，与完整 $\mathcal H$ 的关系仍未解决。[BZ24] 表 1 已提示非零相位通常破坏二幺正性；本卷给出全相位恒等式和周期回返边界，不把已知提示或固定代表记为新的开放问题结算。

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

**定理 12.2（全输入交换图和严格通道塔）。** 用第 7 节数字通道 $Q_{D,d}$ 定义

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

**推论 12.3（原 RT 参考态的精确层分解）。** 对 $D=de$，

$$
\mathcal V_{D;d,e}|\Psi^\alpha_{D,L}\rangle
=|\Psi^\alpha_{d,L}\rangle\otimes|\Psi^\alpha_{e,L}\rangle,
\qquad
\mathcal R_{D,d}(|\Psi^\alpha_{D,L}\rangle\langle\Psi^\alpha_{D,L}|)
=|\Psi^\alpha_{d,L}\rangle\langle\Psi^\alpha_{d,L}|.
$$

**证明。** 每个 $|+_D\rangle$ 的数字分解恰为 $|+_d\rangle\otimes|+_e\rangle$，代入定理 12.2 的等距恒等式。证毕。对固定 $p,L$ 选择定理 5.2 的同一个整数 $\alpha$，这就给出每一精度都满足全区域 RT 的严格相容参考态塔。

**命题 12.4（进位表示及仅一处残余相位）。** 在原边界输出上先逐腿拆数字，再在每个顶点的两条输出腿实施定理 9.3 的进位修正。对路径 $x=a+db$，输出变成低层 $B_da$ 和高层 $B_eb$，其中 $(B_dx)_i=(x_i+x_{i+1},x_i+2x_{i+1})$。只需再施加相位

$$
\exp\left(2\pi i\left[\frac{q(a)}d+\frac{q(b)}e-\frac{q(a+db)}{de}\right]\right),
\qquad q(x)=x_0x_L+\alpha x_0^2,
$$

即得到 $\mathcal V_{D;d,e}$ 在编码子空间上的作用。相位仅依赖两个端点的低、高数字；它们从第一个和最后一个顶点块分别由 $M_d^{-1},M_e^{-1}$ 恢复。

**证明。** 逐顶点进位修正由定理 9.3 的同一坐标恒等式给出，不要求输入向量在各路径上等幅。原相位为 $e^{2\pi iq(a+db)/(de)}$，乘所列相位后恰为两层相位的乘积。相位函数在所有边界基上可通过各块逆置换定义，故是合法的全空间对角幺正，不只是在态支撑上写一个形式规则。证毕。

至此，单环的共享历史和缝合相位可同时修正；没有把单边相容直接当作网络相容。一般多环、附树边界上的同样有限范围通道尚未由本节证明。

## 13. 显式局部 Hamiltonian 与可检验的 RT 误差界

在解码寄存器上定义互不重叠的 $L$ 条量子连接：$i=0,\ldots,L-2$ 的 $(v_i,u_{i+1})$ 取 $\Phi_d$，缝合 $(u_0,v_{L-1})$ 取 $\Omega_{d,\alpha}$。于是

$$
|\chi_d\rangle=|\Omega_{d,\alpha}\rangle_{u_0,v_{L-1}}
\otimes\bigotimes_{i=0}^{L-2}|\Phi_d\rangle_{v_i,u_{i+1}},
\qquad |\Psi^\alpha_{d,L}\rangle=M_d^{\otimes L}|\chi_d\rangle.
$$

**定理 13.1（局部父 Hamiltonian 的全谱）。** 取每项能量系数为一，定义

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

**推论 13.2（局部能量认证全部区域）。** 设实际归一化态为 $\sigma$，且

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

这不等于对任意历史输入都证明同一个纯面积公式。一个明确反例是任意计算基历史 $|x\rangle$：$J_d|x\rangle$ 只是一个边界计算基乘积态乘全局相位，因此所有区域熵都为零，即使 $m(A)>0$。全区域 RT 饱和目前针对指定参考态及第 13 节控制的近邻态。该历史编码尚未被识别为具有独立引力意义的体码，也未证明任意体态的互补区域恢复或量子修正 RT。

第 12 节降低的是寄存器精度，边界块数不变。它与 [ER07] 的先处理纠缠再截断具有方法联系，但没有构造空间尺度的 MERA 或连续极限。第 13 节还显示，在所选双腿块划分下参考态是局部幺正作用于相邻 Bell 连接的短程模型，有显式非零谱隙；相容精度塔本身不提供临界边界场论。局部窗口精度不自动等于图的径向截断尺度；完整 Bruhat–Tits 边界为 $\mathbb P^1(\mathbb Q_p)$，$\mathbb Z_p$ 是自然紧开部分。

原始引力 RT 仍需独立给定边界理论与态、共同调节下的熵控制、满足同调约束的图割到几何面积的极限、$1/(4G_N)$ 系数及引力动力学。后续应在同一目标下扩展几何和体态结构，而不把任意通道交换图或事后构造的父 Hamiltonian 当作物理对偶的证明。

## 参考文献

[RT] S. Ryu, T. Takayanagi. Holographic Derivation of Entanglement Entropy from AdS/CFT. Phys. Rev. Lett. 96 (2006), 181602. arXiv:hep-th/0603001.

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

[Tan26] I. Tan. Transversal gates of the ((3,3,2)) qutrit code and local symmetries of the absolutely maximally entangled state of four qutrits. arXiv:2601.19677 (2026).

[Rather24] S. A. Rather. Construction of perfect tensors using biunimodular vectors. Quantum 8 (2024), 1528. DOI: 10.22331/q-2024-11-20-1528. arXiv:2309.01504v2. 第 5.2 节已有固定三个代表的局部不等价性。

[StateRG05] F. Verstraete, J. I. Cirac, J. I. Latorre, E. Rico, M. M. Wolf. Renormalization-Group Transformations on Quantum States. Phys. Rev. Lett. 94 (2005), 140601. arXiv:quant-ph/0410227.

[ER07] G. Vidal. Entanglement renormalization. Phys. Rev. Lett. 99 (2007), 220405. arXiv:cond-mat/0512165v2.

[Aud07] K. M. R. Audenaert. A sharp continuity estimate for the von Neumann entropy. J. Phys. A 40 (2007), 8127–8136. arXiv:quant-ph/0610146. 标准界亦见 arXiv:2408.15306v4 式 (1)。

[Cert26] G.-P. Nadon et al. Quantum State Certification via Effective Parent Hamiltonians from Local Measurement Data. arXiv:2603.04499 (2026). 仅作为局部能量认证方法的相关来源。

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
