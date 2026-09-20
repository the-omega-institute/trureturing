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

此处不要求保留余数，也不限制 Fourier 或 Clifford 操作。局部辅助系统和丢弃均含在 CPTP 中。共享经典随机的乘积通道混合也不可能，因为纯输出的每个正权分支必须产生同一纯态。通信、自适应 LOCC、共享纠缠、联合门、混合或近似输出均不在排除范围。第 7 节单边通道塔不能仅靠四条腿独立粗化实现 $T_9\mapsto T_3$；这不是任意整体网络粗化的不存在定理。与 $T_3\otimes T_3$ 可直接丢弃一层相比，也证明全部二分谱不能决定粗化能力。

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

后式来自 Jensen 和 $S\ge S_2$。领先熵斜率与完整谱平坦性不同。该区域至少具有内部顶点全部归左或全部归右两个同容量最小割，不满足 [TPTN26] 第 5.2 节式 (5.23) 前的无领先简并条件。未从二阶平均值推出其他谱距离的概率极限。

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

## 15. 全历史编码的最大区域恢复代数

本节直接计算第 12 节编码的区域信息，而不从参考态面积律推断整个码的性质。一般的可纠正代数判据来自 [BKK07]，代数熵与 RT 关系采用 [Harlow] 的标准分块熵约定。以下陪集坐标、矩阵单位和维数是对当前算术映射的显式求值。

**定理 15.1（相干单项编码的完整区域正规形）。** 设 $V,X,Y$ 为有限交换群，$A:V\to X$、$B:V\to Y$ 为群同态，$(A,B)$ 单射。允许任意相位函数 $q:V\to U(1)$，不要求二次。取全历史空间 $\mathbb C[V]$ 上的等距编码

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

**推论 15.2（全输入熵与相对熵，面积算符为零）。** 对任意历史密度矩阵 $\rho$，令 $\widehat\rho=\mathcal U^*\rho\mathcal U$，$p_z=\operatorname{Tr}\widehat\rho_{zz}$，$\rho_{b,z}=\operatorname{Tr}_{K_A}\widehat\rho_{zz}/p_z$；零权扇区略去。则

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

**推论 15.3（单环交错半边的经典与量子信息分解）。** 对第 12 节原编码，取 $V=R_d^{L+1}$、$A,B$ 为两侧真实边界线性输出。当区域每顶点恰选一腿时，两核均由初始值递推参数化，大小各为 $d$，故

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

**定理 16.2（两参数严格相容）。** 空间通道 CPTP、满射且非恒定，并在全部逻辑输入上满足

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

**命题 16.3（三进相位调整的必要性）。** 对 $d=3^n$，全区域 RT 条件要求：偶环 $\alpha\equiv0\pmod3$，奇环 $\alpha\not\equiv0\pmod3$。故一个不变的 $\alpha$ 不能同时覆盖奇、偶长度。

**证明。** 偶环中 $c_k\equiv2\alpha+2(-1)^k\pmod3$，$k$ 的两种奇偶均出现；同时非零当且仅当 $\alpha=0$。奇环中两幂之和为零，$c_k\equiv2\alpha$，故要求非零。模 $3$ 非零等价于在每个 $3^n$ 中为单位。证毕。

例如四环的 $\alpha=0$ 参考态原本对全部区域饱和；若分块到三环却不改相位，交错半边的熵只剩 $2\log3$，而三环最小割为 $3$。在保留寄存器 $u_0$ 上加 $\omega_3^{u_0^2}$ 后得到 $\alpha=1$ 三环，熵恢复 $3\log3$。修正由真实粗化后的单位判据决定，并非声称普通偏迹自动保持 RT。

**推论 16.4（空间固定点的精确限制）。** 对参考态，若区域 $A$ 由完整的双腿顶点块构成，则

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

**命题 17.1（当前单环的显式双曲实现）。** 固定 $L\ge3$，将原单环的每个四价顶点拆成两个三价顶点，以权重 $\beta=L+1$ 的辅助边连接。每个新顶点接一条原环边和一条原边界边；所有原边权为一。令

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

**推论 17.2（扭转和隐藏把手不可由这些熵唯一恢复）。** 固定上述裤子分解的全部长度，$2L$ 个 Fenchel–Nielsen 扭转参数可独立变化，所有 $m(A)$ 不变。它们给出标记曲面的 $2L$ 维族；除去离散映射类识别后仍有连续的几何不唯一性。这正是 [HEC15] 已指出的扭转盲性在当前图上的维数求值。

还可在保持相同边界长度、曲率和全部最小割熵的同时，实现任意亏格 $g\ge1$。证明是在一条单位权内部边上插入三价顶点，将该边变为两条串联单位边；新顶点再以单位桥边连接到一个带单位自环的三价顶点。无边界的这个附件在最小割时可与连接顶点同侧，代价为零；两个串联边在端点异侧时最小代价仍为一。故边界割函数不变。该操作增加两个裤子面、三个内部缝合参数而不增加外边界，使亏格加一。新最大边权仍为 $\beta$，区域候选上界仍为 $\epsilon L$，原领圈条件对任意次添加统一有效。逐次应用即得。这里的附加图用于几何实现，不改变原量子张量网络。

**相位字典的限制。** $\alpha$ 不能直接等同于仅改变上述曲面扭转、保持裤子边界长度不变的参数。例如 $d=L=3$ 时，$\alpha=0$ 与 $\alpha=1$ 在指定区域产生 $2\log3$ 与 $3\log3$ 的不同熵，而任何这类固定长度扭转都不改变几何最小割。需要同时说明相位如何改变状态的几何适用性、长度数据或体熵项，才能建立这样的字典。

## 18. 在原码内部产生非零面积，并计算容量代价

本节固定一个边界划分 $X|Y$，使用第 15 节同一个正规形及实际逻辑坐标 $\mathcal U$。构造依赖这个划分；没有为不同区域分别选子空间后再将其冒充同一码。固定辅助纠缠产生面积的机制来自 [Harlow]，最大纠缠与固定面积谱的关系见 [AR19]。下面把机制落实到当前全历史码内的明确相干约束，并给出达到容量界的实例。

**定理 18.1（共享中心的相干分组子码）。** 将 $Z$ 分成非空不交集合 $Z_t$，大小 $r_t$。取正权概率 $\lambda_{t,z}>0$、$\sum_{z\in Z_t}\lambda_{t,z}=1$，定义受约束历史嵌入

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

这是同一实际边缘态的谱分解，熵为 $H(p)+\sum_t p_t[S(\rho_{b,t})+H(\lambda_t)]$。压缩另一侧矩阵单位张成 $t$ 扇区内的 $a$ 完全矩阵代数，故其交换子恰是所称最大代数。相对熵中固定 $\lambda_t$ 因子相消，也得到边界与逻辑代数相对熵的等式。证毕。这里固定相干方向是子空间定义，不是由只读经典中心标签的后处理自动制备出来的操作。

**命题 18.2（精确互补恢复的面积–容量界）。** 对任意有限维、精确互补恢复的码，物理两侧维数为 $N_X,N_Y$。设每个中心扇区的面积特征值至少为 $a\ge0$。则码维数 $K$ 满足

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

**推论 18.3（当前交错半边的饱和实例）。** 单环交错半边满足 $N_X=N_Y=d^L$、$|Z|=d^{L-1}$、$|K_A|=|K_B|=d$。将全部 $Z$ 放进一个组并均匀固定，得到一个 $d^2$ 维子码，非零标量面积为

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

**定理 19.1（同一码中的四方 GHZ 方向）。** 取 $L\ge4$ 和任意奇数 $d\ge3$。在第 12 节历史空间取

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

**定理 19.2（到三方全息熵锥的精确一致误差）。** 令 $h=H(p)$，$s=(h,h,h,h,h,h,h)$ 按 $A,B,C,AB,AC,BC,ABC$ 排列。用 [HEC15] 的静态几何熵锥 $\mathcal C_3$ 约定，有

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

**定理 20.2（同一码、全部块区域、全部输入）。** 对任意块区域 $A$，把自由边分为两端均在 $A$ 的 $I_A$、仅一端在 $A$ 的 $C_A$ 和两端均在补集的 $O_A$。令 $\Delta_{C_A}$ 为这些自由历史的计算基退相干，

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

**命题 20.3（本构造类的连通性与尖锐容量）。** 更一般地，取有限连通无自环图 $\Gamma=(V,E)$，每条边两个 $d$ 维半边寄存器，每个顶点允许固定的本地幺正。将边划为固定最大纠缠的 $\mathsf F$ 和独立逻辑重复编码的 $\mathsf S$。定理 20.2 的全部区域结论仍成立。每个非空真块区域的面积严格为正，当且仅当固定边子图 $(V,\mathsf F)$ 连通。在此条件下

$$
\boxed{\log_dK=|\mathsf S|\le |E|-|V|+1=b_1(\Gamma).}
$$

选取固定边为任意生成树即达到该构造类的界。

**证明。** 定理 20.2 的逐边偏迹不使用顶点度数。所有非平凡割都有固定边等价于固定子图连通；连通图至少有 $|V|-1$ 条固定边，减去这些边给出维数界。生成树达到最少固定边数。证毕。该界只适用于明确写出的固定／自由重复连接构造，不是任意图上量子纠错码的容量定理。$b_1$ 是指定网络的环秩，也不是第 17 节无法由熵识别的曲面亏格。

**推论 20.4（原单环中的非平凡共同子码）。** 对原单环，选任意一个内部历史 $j\in\{1,\ldots,L-1\}$ 为唯一自由寄存器。其余历史固定为 $|+_d\rangle$。这得到同一 $d$ 维码，对每个非空真完整块区域及所有码内密度矩阵满足定理 20.2，并有 $f_A\ge1$。这是本固定／自由连接类在所有块割均为正面积条件下的最大逻辑维数。它与第 18 节固定细腿交错划分的 $d^2$ 维最优码采用不同区域要求，不能混同。

## 21. 共同子码在原两参数粗化下闭合

本节沿用原 $\mathcal R^{(L)}_{D,d}$ 和 $\mathcal S_{\Pi,d}$，不为各区域重新选择通道。对空间分割 $0=t_0<\cdots<t_r=L$，定义粗自由集

$$
\mathsf S_\Pi=\{j\in\{1,\ldots,r-1\}:t_j\in\mathsf S\}.
$$

令 $\operatorname{tr}^{\mathsf S}_{\Pi}$ 从原自由寄存器中丢弃不在宏块边界的寄存器，并按 $t_j\mapsto j$ 重标。

**定理 21.1（受约束码的全输入粗化）。** 对 $d\mid D$ 和所有自由逻辑密度矩阵，

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

**定理 22.1（纯输入与任意混合输入的不同阈值）。** 对固定／自由连接码，

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

**推论 22.2（单环最优共同码的显式几何图）。** 定理 20.4 的唯一自由边连接块 $u,v$。对任意逻辑密度矩阵 $\rho$，记

$$
h=S(\Delta\rho),\qquad s=S(\rho),\qquad 0\le s\le h.
$$

全部物理块熵由下列一个图同时实现：冻结边权仍为 $\log d$，另加入三角图

$$
\boxed{w_{uv}=h-s/2,\qquad w_{uR}=w_{vR}=s/2.}
$$

三条权都非负。纯输入时 $s=0$，只需给自由边赋权 $h$，参考终端可去掉；均匀相干输入 $|+_d\rangle$ 时恢复原块环的全部边权 $\log d$。

**证明。** 自由重复编码的单端态为 $\Delta\rho$、双端态与 $\rho$ 等距，因此区域包含零个、一个、两个端点时，自由贡献分别为 $0,h,s$。所列图割逐项相同。$s\le h$ 来自计算基退相干的熵不减。全部区域共用这一个图，而非逐区域拟合权重。证毕。固定面积仍是 $f_A\log d$，上述输入依赖边权表示逻辑熵贡献，不能把两者混称为同一个固定面积算符。

**推论 22.3（增加第二条自由连接的受控反例）。** 在四环上释放 $x_1,x_3$ 两个不相邻自由历史，输入 $\sum_x\sqrt{p_x}|x,x\rangle$。自由部分是四块 GHZ，冻结部分是两条 Bell 边，所以聚合后的七项熵为 $b+s$，其中 $b$ 是冻结边割向量，$s$ 是第 19 节的等熵向量。其到 $\mathcal C_3$ 的一致距离仍精确为 $H(p)/7$：下界由 $I_3(b)=0$ 得到，上界由 $b$ 加第 19.2 节的 $K_4$ 图达到。故固定面积子码的任意扩充并不保持几何适用性。

## 23. 共同码的局部认证与边界

**命题 23.1（码空间父 Hamiltonian）。** 在定理 20.3 的解码半边寄存器上，冻结边投影为 $P_e=|\phi_e\rangle\langle\phi_e|$，自由边投影为

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

**几何结论的精确范围。** 第 20–22 节已在完整双腿块这一固定分辨率上给出同一非平凡子码、全部区域的正面积与互补恢复、全部输入的几何熵表示，以及空间和精度通道保持的共同族。它没有解决任意单腿细分区域的同样要求；这些区域会切开 $M_d$ 的本地作用，不能沿用逐边偏迹证明。单条自由逻辑边的完整量子态由其两个端点块联合恢复，单端仅见对角信息，故不能把此构造称为保护任意单块擦除或具有深体局域性的码。

固定边面积图是一棵树时已能得到当前单环的容量最优解，全部纯输入的块熵可由成对边权表示，因而各四组的 MMI 饱和。它仍属于短程连接结构，未产生临界 CFT、独立引力动力学或可识别的双曲扭转。[CSW25, CS26] 提醒的深度及访问结构约束不能从几何熵存在性中省略；其一般论断也依赖原文的静态及收缩法等假设。下一实质义务是对切开顶点块的区域建立共同恢复与几何解释，或在明确模型中获得超出成对连接的非平凡楔结构，同时维持已证明的粗化关系。固定辅助纠缠、简单图连通性和父 Hamiltonian 属于已有方法；本卷具体共同子码、支持阈值分类及其组合尚未全面排除文献等价形式，不认领具名外部猜想或原始引力 RT 已解决。

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

[BKK07] C. Bény, A. Kempf, D. W. Kribs. Quantum Error Correction of Observables. Phys. Rev. A 76 (2007), 042303. arXiv:0705.1574. 使用可纠正代数的压缩错误算符交换子判据；较早简报为 Phys. Rev. Lett. 98 (2007), 100502，arXiv:quant-ph/0608071。

[HJPW04] P. Hayden, R. Jozsa, D. Petz, A. Winter. Structure of states which satisfy strong subadditivity of quantum entropy with equality. Commun. Math. Phys. 246 (2004), 359–374. arXiv:quant-ph/0304007. 仅作为零条件互信息与短量子 Markov 结构的背景，式中当前网络的值由逐边计算得出。

[HEC15] N. Bao, S. Nezami, H. Ooguri, B. Stoica, J. Sully, M. Walter. The Holographic Entropy Cone. JHEP 09 (2015), 130. arXiv:1505.07839. 使用第 3.2 节、Lemma 4、Theorem 5；扭转不唯一性亦已明确见于该节。

[EPV23] M. Ebbens, H. Parlier, G. Vegter. Minimal Delaunay Triangulations of Hyperbolic Surfaces. Discrete Comput. Geom. 69 (2023), 568–592. DOI: 10.1007/s00454-022-00373-0. 使用第 2 节 Fenchel–Nielsen 坐标及 Lemma 2.1 的曲率 $-1$ 领圈宽度。

[AR19] C. Akers, P. Rath. Holographic Renyi Entropy from Quantum Error Correction. JHEP 05 (2019), 052. arXiv:1811.05171v2. 使用固定辅助纠缠、面积扇区与 Rényi 谱的解释，不作为当前子码原创性证明。

[HHM11] P. Hayden, M. Headrick, A. Maloney. Holographic Mutual Information is Monogamous. Phys. Rev. D 87 (2013), 046003. arXiv:1107.2940v2，初稿 2011 年。使用静态 RT 熵的 $I_3\le0$ 定理。

[CSW25] B. Czech, S. Shuai, Y. Wang. Entropy Inequalities Constrain Holographic Erasure Correction. Phys. Rev. Lett. 135 (2025), 141603. DOI: 10.1103/dl3c-h3hg. arXiv:2502.12246. 使用熵不等式饱和对特定访问结构的约束作为比较背景。

[CS26] B. Czech, S. Shuai. Renormalization group is the principle behind the holographic entropy cone. JHEP 07 (2026), 165. DOI: 10.1007/JHEP07(2026)165. arXiv:2601.02472v2. 核对第 2.1、2.2、4 节；文中饱和推导的收缩法范围及所讨论猜想的状态不省略。

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
