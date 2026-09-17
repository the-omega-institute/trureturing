
---

<a id="string-observer-leakage-global-geometry"></a>

# 非零漏出、投影代数与全局观察者几何

## 接续 ST0–ST18 的理论增订 ST19–ST26

**数学范围。** 除显式的向量丛命题外，本文工作在有限维、正定内积的复 Hilbert 空间上。连续场、无界算子、弦 ghost 空间、量子 BV 积分与 Einstein 动力学须另行给出实现。本文的证明是普通数学证明，尚未编译为 Lean。ST19–ST21把已有ST13的零漏出判据推广为可量化的仪器近似；ST22–ST26把已有ST15–ST17的局部图几何推广到带全局障碍的图册。普遍的温和测量界、子丛曲率公式和量子度量拓扑界各有既有来源，文中明确归属，不作全球首次发现声明。

## ST19．保持单步结果概率的量子仪器补全

### 定义 ST19.1：输入与输出编码、仪器漏出

设 $U:V\to\mathcal H$、$W:V'\to\mathcal H'$ 为等距映射，$V,V'$ 非零。允许输入与输出编码不同，记 $P'=WW^\dagger$。完整有限仪器为

$$
\mathcal I_a(\omega)=\sum_\ell K_{a\ell}\omega K_{a\ell}^\dagger,
\qquad \sum_{a,\ell}K_{a\ell}^\dagger K_{a\ell}=I_{\mathcal H}.
$$

定义压缩算子与漏出算子

$$
k_{a\ell}=W^\dagger K_{a\ell}U,\qquad
R_{a\ell}=(I-P')K_{a\ell}U,
$$

$$
\Lambda_a=\sum_\ell R_{a\ell}^\dagger R_{a\ell},\qquad
\Lambda=\sum_a\Lambda_a,\qquad \lambda=\|\Lambda\|.
\tag{ST19.1}
$$

块分解立即给出 $0\le\Lambda\le I_V$，所以 $0\le\lambda\le1$。该量是在给定输入编码上的最坏单步漏出概率；它没有预设真实多轮状态始终留在编码内。

### 定理 ST19.2：按结果复位的 CPTP 补全

为每个结果选择一个固定密度矩阵 $\tau_a$ 于 $V'$，令

$$
\boxed{
\widehat{\mathcal I}_a(\rho)
=\sum_\ell k_{a\ell}\rho k_{a\ell}^\dagger
+\operatorname{tr}(\Lambda_a\rho)\tau_a.
}
\tag{ST19.2}
$$

则这是一个归一量子仪器，且对所有输入态逐结果满足

$$
\operatorname{tr}\widehat{\mathcal I}_a(\rho)
=\operatorname{tr}\mathcal I_a(U\rho U^\dagger).
\tag{ST19.3}
$$

**证明。** $\rho\mapsto\operatorname{tr}(\Lambda_a\rho)\tau_a$ 完全正：若 $\Lambda_a=\sum_j s_j|v_j\rangle\langle v_j|$、$\tau_a=\sum_i t_i|w_i\rangle\langle w_i|$，其 Kraus 家族为 $\sqrt{s_jt_i}|w_i\rangle\langle v_j|$。又有

$$
\sum_\ell k_{a\ell}^\dagger k_{a\ell}+\Lambda_a
=U^\dagger\Bigl(\sum_\ell K_{a\ell}^\dagger K_{a\ell}\Bigr)U.
$$

取迹得到(ST19.3)，再对 $a$ 求和得到保迹性。∎

补全是一个明确的近似模型：漏出的后态被替换为指定复位态。它只承诺精确保留单步结果效果；没有承诺完整未来。数学上的 CPTP 构造也不说明物理复位或控制资源免费。

## ST20．带参考系统的尖锐单步误差界

记 $\mathcal E_U(\rho)=U\rho U^\dagger$。用一个正交经典寄存器保留结果，定义通道

$$
\mathfrak I\mathcal E_U(\rho)
=\sum_a|a\rangle\langle a|\otimes\mathcal I_a(U\rho U^\dagger),
$$

$$
\mathcal E_W\widehat{\mathfrak I}(\rho)
=\sum_a|a\rangle\langle a|\otimes
W\widehat{\mathcal I}_a(\rho)W^\dagger.
$$

### 定理 ST20.1：仪器补全的钻石距离界

定义

$$
\boxed{b(q)=\frac{q+\sqrt{q(4-3q)}}2,\qquad0\le q\le1.}
\tag{ST20.1}
$$

对任意参考系统 $R$ 及输入密度态 $\rho_{VR}$，令
$q=\operatorname{tr}[(\Lambda\otimes I_R)\rho_{VR}]$。则

$$
\frac12\left\|[(\mathfrak I\mathcal E_U-\mathcal E_W\widehat{\mathfrak I})
\otimes\mathrm{id}_R](\rho_{VR})\right\|_1
\le b(q)\le b(\lambda).
\tag{ST20.2}
$$

因而

$$
\boxed{
\frac12\|\mathfrak I\mathcal E_U-\mathcal E_W\widehat{\mathfrak I}\|_\diamond
\le b(\lambda)\le \sqrt\lambda+\lambda/2.
}
\tag{ST20.3}
$$

标量函数 $b$ 与 Regula–Lami–Datta 的加强温和测量引理中广义迹距离的尖锐函数一致；该函数的普遍改进归于其2026年论文。以下给出投影特例的自含证明，再把它接到保持结果的仪器补全。[ST19-RLD]

**证明。** 先纯化输入，并对带结果仪器作保留 Kraus 标签的 Stinespring 等距扩张。其输出为单位向量 $|\Psi\rangle$。在输出系统上投影到 $P'$，并在参考和环境上张量恒等，记投影后的向量为 $|v\rangle$，被删去向量为 $|w\rangle$。于是

$$
\langle v,w\rangle=0,\quad\|v\|^2=1-q,\quad\|w\|^2=q.
$$

在 $v,w$ 张成的至多二维空间中，算子
$|\Psi\rangle\langle\Psi|-|v\rangle\langle v|$ 的迹为 $q$，行列式为 $-q(1-q)$，所以

$$
\bigl\||\Psi\rangle\langle\Psi|-|v\rangle\langle v|\bigr\|_1
=\sqrt{q(4-3q)}.
$$

偏迹及经典化保持迹范数收缩。补全中额外加入的复位项是一个迹为 $q$ 的正算子，即使输入与参考纠缠也成立。因此三角不等式给出 $b(q)$。端点直接连续延拓；在 $0<q<1$ 上

$$
b''(q)=-\frac{2}{[q(4-3q)]^{3/2}}<0,\qquad b'(1)=0,
$$

故 $b$ 单调递增，且 $q\le\lambda$。这个论证对所有参考系统成立，给出通道差的钻石范数界。最后 $\sqrt{q(4-3q)}\le2\sqrt q$。∎

### 例 ST20.2：此复位补全家族的界可达到

取完整空间的正交基 $|0\rangle,|1\rangle,|e\rangle$，输入和输出编码均保留前两维。完整操作为酉矩阵：

$$
K_q|0\rangle=\sqrt{1-q}|0\rangle+\sqrt q|e\rangle,
\quad K_q|e\rangle=-\sqrt q|0\rangle+\sqrt{1-q}|e\rangle,
\quad K_q|1\rangle=|1\rangle.
$$

选择复位态 $|1\rangle\langle1|$。此时 $\lambda=q$。输入 $|0\rangle$ 时，补全输出为
$(1-q)|0\rangle\langle0|+q|1\rangle\langle1|$，与真实输出的迹距离恰为 $b(q)$。二维块的范数贡献为 $\sqrt{q(4-3q)}$，独立的复位块贡献为 $q$。这证明(ST20.3)作为所述补全家族的统一界是尖锐的；它没有声称这种复位在所有可选模拟方法中最优。

只保留一维编码时，真实输出 $\sqrt{1-q}|0\rangle+\sqrt q|e\rangle$ 与任何归一编码输出的迹距离为 $\sqrt q$。因此无法对所有模型以固定常数把最坏误差改成 $O(q)$。

## ST21．非零漏出的多时刻误差与相干反例

### 定理 ST21.1：有限自适应记录的误差累加

固定有限轮协议。第 $j$ 步的仪器、输入/输出编码和复位态可依赖既往经典记录 $h$，并满足 ST19。设相应漏出上界为 $\lambda_j(h)$。从同一初始编码态出发，比较真实协议与逐步补全的有效协议，并实施相同的最终实验。则全部联合记录分布满足

$$
\boxed{
\operatorname{TV}(p_{\rm full},p_{\rm eff})
\le\min\left\{1,\sum_{j=1}^N\sup_h b(\lambda_j(h))\right\}.
}
\tag{ST21.1}
$$

该界允许初态带参考系统，并保留所有分支，不做后选择。

**证明。** 按顺序构造混合协议：前 $j$ 步使用补全后重新编码的操作，后续步骤仍使用真实操作。相邻混合协议在第 $j$ 步之前共享编码内输入，故可用(ST20.3)。之后双方共用真实 CPTP 过程，误差不会增加。对分支控制通道取 $\sup_h$，再对各次替换用三角不等式，最后读出经典记录。证明没有假设真实协议在每一步自动留在编码中。∎

若各段演化另有 ST14 的等距交织误差 $\varepsilon_j(h)$，可在同一替换证明中使用

$$
\min\left\{1,\sum_j\sup_h[b(\lambda_j(h))+\varepsilon_j(h)]\right\}.
\tag{ST21.2}
$$

### 反例 ST21.2：未监测的相干漏出不能用概率并集界控制

在 $\mathbb C^2$ 中只保留 $|0\rangle$，重复真实酉旋转

$$
R_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{pmatrix}.
$$

每一步在编码输入上的漏出参数为 $\lambda=\sin^2\theta$。一维归一补全只能留在 $|0\rangle$。取 $\theta=\pi/(2N)$，真实演化满足

$$
R_\theta^N|0\rangle=|1\rangle,
\qquad
N\lambda=N\sin^2\frac{\pi}{2N}\longrightarrow0.
$$

最终测量 $|1\rangle\langle1|$ 的概率差却等于1。相反，$N b(\lambda)$ 的小角主项趋于 $\pi/2$，与(ST21.1)的截断上界相容。若每一步真的测量是否漏出，实验本身会改变；本反例中没有偷偷加入该测量。

### 命题 ST21.3：输入输出换框不改变预算

在同一个物理编码像内取 $U'=Ug_{\rm in}$、$W'=Wg_{\rm out}$，其中 $g$ 酉。则

$$
k'_{a\ell}=g_{\rm out}^\dagger k_{a\ell}g_{\rm in},\quad
\Lambda'_a=g_{\rm in}^\dagger\Lambda_a g_{\rm in}.
$$

若同时运输 $\tau'_a=g_{\rm out}^\dagger\tau_a g_{\rm out}$，补全通道也协变，$\lambda$ 和全部误差界保持不变。证明由代入定义和酉范数不变性。改变物理编码像属于另一个问题，不在此换框命题内。

## ST22．压缩后的非交换性由相同的法向块控制

### 定理 ST22.1：投影乘法与交换子缺陷

固定等距编码 $U$，$P=UU^\dagger$。对完整空间上的 Hermitian 算子 $A,B$，令

$$
a=U^\dagger AU,\quad b=U^\dagger BU,\quad
L_A=(I-P)AU,\quad L_B=(I-P)BU.
$$

有

$$
U^\dagger ABU-ab=L_A^\dagger L_B,
$$

$$
\boxed{[a,b]=U^\dagger[A,B]U-L_A^\dagger L_B+L_B^\dagger L_A,}
\tag{ST22.1}
$$

以及

$$
\|[a,b]-U^\dagger[A,B]U\|\le2\|L_A\|\|L_B\|.
\tag{ST22.2}
$$

**证明。** 在 $AB$ 中插入 $I=P+(I-P)$，利用自伴性得到第一式，交换 $A,B$ 后相减，最后用次乘性。∎

同时，对短时控制 $e^{-itA/\hbar}$，有

$$
U^\dagger e^{itA/\hbar}(I-P)e^{-itA/\hbar}U
=\frac{t^2}{\hbar^2}L_A^\dagger L_A+O(t^3).
\tag{ST22.3}
$$

该式由有限矩阵指数展开得到。于是压缩代数的缺陷与操作把态带出编码的倾向由同一批矩阵元控制。这里的 $A$ 只有在确实作为控制 Hamiltonian 时才具有该动力学解释。

### 例 ST22.2：可交换完整观测量的压缩可以不交换

取 $A=\operatorname{diag}(1,0,0)$、$B=\operatorname{diag}(0,1,0)$，并以

$$
u_1=(1,1,0)^{\mathsf T}/\sqrt2,\quad
u_2=(1,-1,2)^{\mathsf T}/\sqrt6
$$

为 $U$ 的两列。则 $[A,B]=0$，但

$$
[a,b]=\frac1{3\sqrt3}\begin{pmatrix}0&-1\\1&0\end{pmatrix}\ne0.
$$

这是一项压缩代数结论；完整构造已经使用量子 Hilbert 空间，不能据此声称从经典概率独自推出量子力学。有限维交换子迹为零，也不能成为非零常数乘恒等的精确 Heisenberg 关系。

Palumbo 在2026年发表的延展对象量子 Hall 模型中，研究了假定各向同性、有隙内部扇区上的投影代数。其普适性依赖具体扇区与平滑化条件。[ST19-GMP] 上述有限恒等式提供一个可用于检查相邻约化问题的接口，并未重新证明该文的连续 GMP 代数、gerbe 或完整弦模型。

## ST23．非零 Chern 数阻止单一全局图编码

### 假设 ST23.1

令 $\Sigma$ 为紧致、无边界、定向光滑曲面，$P(x)$ 是固定平凡丛 $\Sigma\times\mathbb C^n$ 上的光滑秩 $r$ 正交投影，$1\le r<n$。记 $E_x=\operatorname{Ran}P(x)$。本文采用物理连接规范

$$
\mathcal A=iU^\dagger dU,\qquad
\mathcal F=d\mathcal A-i\mathcal A\wedge\mathcal A,\qquad
C_1(E)=\frac1{2\pi}\int_\Sigma\operatorname{tr}\mathcal F.
$$

标准第一 Chern 数的整数性作为向量丛背景使用；下述障碍证明实际只需要这个积分非零。度量拓扑界的既有讨论见[ST19-MO]。

### 定理 ST23.2：单一固定可见空间的障碍

若 $C_1(E)\ne0$，则对每个固定秩 $r$ 投影 $P_0$，存在 $x\in\Sigma$ 与单位向量 $v\in E_x$，使 $P_0v=0$。特别地，

$$
\boxed{\max_{x\in\Sigma}\|(I-P_0)P(x)\|=1.}
\tag{ST23.1}
$$

**证明。** 若 $P_0:E_x\to\operatorname{Ran}P_0$ 处处单射，则因秩相同而处处可逆。局部矩阵求逆说明其逆光滑，把固定目标基拉回就得到 $E$ 的全局框，正交化后得到全局等距 $U$。此时 $\operatorname{tr}\mathcal F=d\operatorname{tr}\mathcal A$，因为交换子迹为零。由 Stokes 定理积分为零，矛盾。存在被完全消去的单位向量时范数至少为1，而正交投影范数至多为1。∎

在横截的图坐标区域，$U=(I,X)^{\mathsf T}(I+X^\dagger X)^{-1/2}$，所以

$$
\lambda_{\min}(U^\dagger P_0U)=\frac1{1+\|X\|^2}.
\tag{ST23.2}
$$

因此全局障碍可表现为图坐标发散。它不要求完整 Hamiltonian 的物理能隙闭合。这里 $\|(I-P_0)P(x)\|^2$ 是不同子空间间的丢失量，应与 ST19 的一次实际仪器漏出参数分别命名。

### 定理 ST23.3：有限图册与一致的局部模型

每个 $x_\alpha\in\Sigma$ 处选择 $E_{x_\alpha}$ 的等距基 $W_\alpha$。在
$W_\alpha^\dagger P(x)W_\alpha>0$ 的邻域内定义

$$
U_\alpha(x)=P(x)W_\alpha
[W_\alpha^\dagger P(x)W_\alpha]^{-1/2}.
\tag{ST23.3}
$$

这些是光滑局部等距框，紧致性给出有限子覆盖。在交叠区，

$$
g_{\alpha\beta}=U_\alpha^\dagger U_\beta,\quad
U_\beta=U_\alpha g_{\alpha\beta},\quad
g_{\alpha\beta}g_{\beta\gamma}=g_{\alpha\gamma}.
$$

**证明。** 基点处括号内为恒等矩阵，正定性在邻域中保持；直接计算 $U_\alpha^\dagger U_\alpha=I$，其像为 $E_x$。交叠区用 $U_\alpha U_\alpha^\dagger=P$ 验证三式。∎

局部态、Hamiltonian、仪器和连接必须使用同一过渡函数。ST21.3保证仪器预算不依赖局部框。沿路径切换图册时，精确的过渡函数是坐标运输，不是额外物理投影；实际重新测量并丢弃结果则是另一种有扰动的操作。

## ST24．全局拓扑约束法向混合与控制强度

### 假设 ST24.1

现在允许环境本身是带相容 Hermitian 连接的向量丛；内积仍正定。参数曲面带一个固定 Riemann 度量，取局部定向正交切向框 $e_1,e_2$。沿用 ST17 的定义

$$
N_a=(I-P)\nabla_{e_a}U,\qquad
\mathcal F_{12}=U^\dagger F^{\rm full}_{12}U
+i(N_1^\dagger N_2-N_2^\dagger N_1).
$$

该曲率分解来自相容连接的子丛几何，一般形式明确归于已有几何及2026年的系统研究。[ST19-OMP] 定义

$$
\mathscr E_N=\int_\Sigma(\|N_1\|_F^2+\|N_2\|_F^2)\,dA,
\quad
\mathscr B=\int_\Sigma\operatorname{tr}(U^\dagger F^{\rm full}_{12}U)\,dA.
$$

二者在局部酉换框下不变，故为全局量。参数度量在比较中固定，并不预先识别为物理时空度量。

### 定理 ST24.2：带环境曲率扣除的拓扑界

有

$$
\boxed{\mathscr E_N\ge|2\pi C_1(E)-\mathscr B|.}
\tag{ST24.1}
$$

**证明。** 逐点使用 Frobenius Cauchy–Schwarz 与 $2ab\le a^2+b^2$：

$$
\left|\operatorname{tr}i(N_1^\dagger N_2-N_2^\dagger N_1)\right|
\le2\|N_1\|_F\|N_2\|_F
\le\|N_1\|_F^2+\|N_2\|_F^2.
$$

由曲率分解积分并使用三角不等式。∎

环境平直时，$\mathscr B=0$，得到 $\mathscr E_N\ge2\pi|C_1|$。这一平直形式与已有量子度量拓扑界相容。[ST19-MO] 非平直环境中若漏掉 $\mathscr B$，结论一般错误，ST25给出等式见证。

### 推论 ST24.3：无跃迁生成元的面积积分界

定义每个单位参数方向上的法向控制生成元

$$
H_{{\rm cd},a}=i\hbar[\nabla_{e_a}P,P].
$$

则

$$
\sum_a\|H_{{\rm cd},a}\|_F^2
=2\hbar^2\sum_a\|N_a\|_F^2,
$$

从而

$$
\boxed{
\mathscr C_2:=\int_\Sigma\sum_a\|H_{{\rm cd},a}\|_F^2dA
\ge2\hbar^2|2\pi C_1(E)-\mathscr B|.
}
\tag{ST24.2}
$$

**证明。** 对 $E\oplus E^\perp$ 分块，$\nabla P$ 只有互为伴随的非对角块 $N_a,N_a^\dagger$。交换子改变一个块的符号，故 Frobenius 范数平方为 $2\hbar^2\|N_a\|_F^2$。再用(ST24.1)。∎

它是给定参数度量下、两个单位方向的生成元平方强度积分。它不是任意单条路径的热力学功下界，也没有推导最短物理时间。真正沿路径运动时，控制还乘以参数速度并受到可实现性限制。无跃迁驱动的一般机制见[ST19-Berry]。

## ST25．恒定物理能隙下的完整二图册例子

### 定理 ST25.1：单图发散、Chern 数与拓扑界同时可算

取单位球面参数 $\boldsymbol n=(\sin\theta\cos\phi,\sin\theta\sin\phi,\cos\theta)$，

$$
H(\boldsymbol n)=\Delta\,\boldsymbol n\cdot\boldsymbol\sigma,\qquad
\Delta>0,\qquad P=(I+\boldsymbol n\cdot\boldsymbol\sigma)/2.
$$

这是正能级 $+\Delta$ 的投影，完整能隙恒为 $2\Delta$。北、南局部框分别为

$$
U_N=\begin{pmatrix}\cos(\theta/2)\\e^{i\phi}\sin(\theta/2)\end{pmatrix},
\qquad
U_S=e^{-i\phi}U_N.
$$

它们分别在去掉南极、去掉北极的区域光滑。北图相对于 $|0\rangle$ 的图坐标为

$$
X_N=e^{i\phi}\tan(\theta/2),\quad
G_N=\sec^2(\theta/2),\quad Z_N=\cos^2(\theta/2).
$$

所以南极处 $Z_N=0$、$X_N$ 发散，同时完整物理能隙不变。局部连接、曲率为

$$
\mathcal A_N=-\sin^2(\theta/2)d\phi,\quad
\mathcal A_S=\cos^2(\theta/2)d\phi,
$$

$$
\mathcal F=-\tfrac12\sin\theta\,d\theta\wedge d\phi,
\qquad C_1=-1.
$$

**证明。** Pauli 恒等式 $(\boldsymbol n\cdot\boldsymbol\sigma)^2=I$ 给出能谱。直接乘法验证 $PU=U$、$U^\dagger U=1$。微分两个框得到连接；过渡函数 $e^{-i\phi}$ 恰好给出 $\mathcal A_S=\mathcal A_N+d\phi$。积分曲率得到 $-2\pi$，图坐标由上下分量相除得到。∎

平直环境下，参数量子度量为

$$
g_{\theta\theta}=\frac14,\qquad g_{\phi\phi}=\frac14\sin^2\theta,
\qquad g_{\theta\phi}=0.
$$

采用单位球面的标准参数度量，得到

$$
\boxed{\mathscr E_N=2\pi,\qquad\mathscr C_2=4\pi\hbar^2.}
\tag{ST25.1}
$$

它达到ST24的平直界。

### 定理 ST25.2：同一投影的曲率可以由环境运输承担

在同一个平凡秩二环境丛上，指定全局光滑连接

$$
\Gamma_\kappa=\kappa(\boldsymbol n\times d\boldsymbol n)\cdot\boldsymbol\sigma,
\quad\nabla=d-i\Gamma_\kappa,\quad\kappa\in\mathbb R.
$$

上述 $P$ 与能谱均不变。则

$$
N^{(\kappa)}=(1+2\kappa)N^{(0)},\quad
F^{\rm full}_{\theta\phi}
=2\kappa(1+\kappa)\sin\theta\,\boldsymbol n\cdot\boldsymbol\sigma,
$$

$$
\mathscr E_N=2\pi(1+2\kappa)^2,\quad
\mathscr B=8\pi\kappa(1+\kappa),\quad C_1=-1.
\tag{ST25.2}
$$

因此对全部 $\kappa$，ST24.1 都取等号。特别地，$\kappa=-1/2$ 时

$$
\boxed{N=0,\quad\mathscr E_N=0,\quad C_1=-1,\quad\mathscr B=-2\pi.}
\tag{ST25.3}
$$

**证明。** 用 $[\boldsymbol a\cdot\boldsymbol\sigma,\boldsymbol b\cdot\boldsymbol\sigma]=2i(\boldsymbol a\times\boldsymbol b)\cdot\boldsymbol\sigma$ 和 $\boldsymbol n\cdot d\boldsymbol n=0$，得到 $\nabla P=(1+2\kappa)dP$，故法向项具有该缩放。连接外微分贡献 $2\kappa\sin\theta\,\boldsymbol n\cdot\boldsymbol\sigma$，交换子贡献 $2\kappa^2\sin\theta\,\boldsymbol n\cdot\boldsymbol\sigma$。又 $U^\dagger\Gamma_\kappa U=0$，有效连接仍等于前式，因此Chern数不变。逐项积分即可。∎

这说明同一个有效 Berry 曲率与同一能谱，不能单独识别几何来自环境运输还是保留空间的法向变化。改变 $\Gamma_\kappa$ 是改变物理上所指定的比较/运输规则；若它只是某个表示变换，其他动力学与探针项必须一起运输。本命题没有把这种参数连接直接认作引力时空。

## ST26．跨图册、带漏出的有效理论命题

### 定理 ST26.1：全局协议的图册相容近似

设一个有限维正态空间模型提供光滑等秩物理子空间丛、其局部等距编码和相容过渡函数，并指定完整有限实验协议。每次操作依ST19转移并补全；每段近似演化有ST14意义的误差预算。若局部态、仪器、复位态和运输连接在交叠区同时按过渡函数变换，则有效协议在不同图册计算中的全部联合记录相同，而且与完整协议的记录差满足(ST21.2)。非零第一Chern数与该全局有效理论相容，但排除ST23意义下的单一固定秩图坐标。

**证明。** 局部补全与误差预算由ST19–ST21给出。ST21.3及ST23的过渡函数余循环律保证任一有限操作词在换框时只在首尾留下互相抵消的酉坐标变化，最终迹与记录不变；时变段还须使用ST15的连接生成元。各步与真实过程比较时使用ST21的混合协议证明。最后由ST23.2得到单图障碍。∎

### 条件性推论 ST26.2：弦模型和相对论量子模型的应用边界

若某个给定的弦有效构造、曲时空场论或投影物态，已给出上述正内积物理态空间、实验语言和运输结构，则可用本命题审计它在允许协议下的约化。规范相容有效作用量可以由适当的BV/同伦转移结构提供，但仍不能替代非零漏出和全局过渡函数的检验。[ST19-Sen]

本文把三个对象分开：完整微观规范的一致性、实际记录的操作误差、量子态丛的参数曲率。时空因果性、Lorentz协变和引力反作用仍需原物理模型另行满足。有限空间上的钻石范数界没有无条件覆盖无限弦塔；处理无界生成元或连续场时，需要能量约束与定义域证明。这里的拓扑障碍与成本界也不独自决定时空维数、Newton常数或Einstein方程。

## ST19–ST26 参考文献与归属

[ST19-RLD]: https://arxiv.org/html/2501.12447v5 "Bartosz Regula, Ludovico Lami, Nilanjana Datta, Tight relations and equivalences between smooth relative entropies, IEEE Transactions on Information Theory 72(5), 3051–3073 (2026), DOI 10.1109/TIT.2026.3661711. Lemma 6 and Appendix C, especially the generalized trace-distance expression in Eq. (175)."
[ST19-OMP]: https://arxiv.org/abs/2503.17163 "Marius A. Oancea, Thomas B. Mieling, Giandomenico Palumbo, Quantum geometric tensors from sub-bundle geometry, Quantum 10, 1965 (2026), DOI 10.22331/q-2026-01-14-1965. Sections 3.2–3.3, equations (3.13), (3.34)–(3.35). The original paper allows a more general Hermitian pseudo-metric; this supplement restricts to a positive metric where norm inequalities apply."
[ST19-MO]: https://arxiv.org/abs/2103.11583 "Bruno Mera and Tomoki Ozawa, Kähler geometry and Chern insulators: Relations between topology and the quantum metric, Physical Review B 104, 045104 (2021), DOI 10.1103/PhysRevB.104.045104. Existing quantum-volume and Chern-number geometry; not a novelty claim for the flat-background bound."
[ST19-GMP]: https://doi.org/10.1103/d76r-nzwm "Giandomenico Palumbo, Noncommutative Geometry and GMP-type algebra for three-dimensional quantum Hall fluids of extended objects, Physical Review D 114, 046021 (24 August 2026). Published abstract retains the assumed isotropic gapped internal sector and suitably smeared collective operators. The inspected arXiv:2602.15664v1 uses the earlier title Generalized GMP Algebra for Three-Dimensional Quantum Hall Fluids of Extended Objects; it is not treated as an identical revision of the published text."
[ST19-Berry]: https://doi.org/10.1088/1751-8113/42/36/365303 "M. V. Berry, Transitionless quantum driving, Journal of Physics A 42, 365303 (2009). Classical source for the counterdiabatic mechanism; here only the explicitly stated finite-dimensional projector identity is used."
[ST19-Sen]: https://arxiv.org/abs/1609.00459 "Ashoke Sen, Wilsonian Effective Action of Superstring Theory, JHEP 01 (2017) 108, DOI 10.1007/JHEP01(2017)108. External BV-consistency input, not a proof of the additional instrument hypotheses."

---
