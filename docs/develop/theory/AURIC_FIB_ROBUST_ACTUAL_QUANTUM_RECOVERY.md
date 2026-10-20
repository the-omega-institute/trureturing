# AURIC FIB：实际仪器保留量子输出的稳健恢复障碍

## 1. 模型、共同实现与误差目标

本文研究一个固定有限忠实态族通过一个实际量子仪器之后的恢复问题。解码器取得全部实际结果记录及保留下来的量子系统，可以使用整个联合输出代数上的任意共同 CPTP 映射。主结论有两条：一般忠实族的实际条件输出在加权意义下接近族内经典因子化；对具有对易正传输的固定族，联合谱块上的稳健平稳平方差给出显式的恢复误差下界。两条结论都以同一实际仪器的根保真缺陷为参数。

全文只给出可错的、未经执行的条件符号数学。来源 S、E、C 和推导接口 R 的内容身份及标准工具归属见 §12。C 的三态经典极小极大定理作为既有结果直接使用；本文给出它向全部实际量子输出解码器的定量接合。没有外部来源认证、经验结论或最优速率断言。原来的普适近似协议与资源桥梁保持 OPEN。

**定义 1.1（输入、范数与实际有限仪器）。** 固定 $A=\mathbb C^d$、$d\ge2$、$r\ge3$，以及忠实密度矩阵 $\boldsymbol\rho=(\rho_0,\ldots,\rho_{r-1})$。密度矩阵半正定且迹一，忠实指正定。所有空间均为有限维复 Hilbert 空间，信道指复线性、完全正、保迹映射，简称 CPTP。记

$$
\|X\|_F^2=\operatorname{Tr}(X^\dagger X),\qquad
\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X},\qquad
\|X\|_{\rm op}=\sup_{\|v\|=1}\|Xv\|,\qquad [X,Y]=XY-YX.
$$

令 $B$ 是任意正有限维的保留输出空间。实际仪器及其全部记录为

$$
\begin{aligned}
\mathcal I_x(X)&=\sum_a K_{xa}XK_{xa}^\dagger,
&K_{xa}&:A\longrightarrow B,\\
E_x&=\sum_aK_{xa}^\dagger K_{xa}\succeq0,
&\sum_xE_x&=I_A,\\
\mathcal N(X)&=\sum_x|x\rangle\langle x|\otimes\mathcal I_x(X),
&C_{\rm rec}&=\mathbb C^m.
\end{aligned}
\tag{1.1}
$$

$x$ 遍历实际有限结果集，未记录的 Kraus 指标 $a$ 与丢弃环境不在解码输入内。$B$ 和结果数可以任意大但有限；输入族和仪器固定以后，不能换用另一实现来回答该仪器的恢复问题。

**定义 1.2（同一实际效应上的根保真缺陷）。** 令 $q=\binom r2$，并定义

$$
\begin{aligned}
p_i(x)&=\operatorname{Tr}(E_x\rho_i),&
F(\rho,\sigma)&=\|\sqrt\rho\sqrt\sigma\|_1,\\
C_{ij}(E)&=\sum_x\sqrt{p_i(x)p_j(x)},&
\delta_{ij}(E)&=C_{ij}(E)-F(\rho_i,\rho_j),\\
F_U(\boldsymbol\rho)&=q^{-1}\sum_{i<j}F(\rho_i,\rho_j),&
G&=G_{\boldsymbol\rho}(E)=q^{-1}\sum_{i<j}\delta_{ij}(E).
\end{aligned}
\tag{1.2}
$$

沿用 S 的根保真测量表示：包括奇异态在内，$F$ 为全部有限 POVM 的经典根保真度下确界，并在 CPTP 映射下不减。因此 $\delta_{ij}\ge0$。若记

$$
F_M(\boldsymbol\rho)=\inf_{F\text{ 为有限 POVM}}q^{-1}\sum_{i<j}C_{ij}(F),
\qquad \Delta=F_M-F_U,
$$

则 $0\le\Delta\le G$。$\Delta=0$ 是输入族存在共同等号测量的性质；$G=0$ 要求此处实际的 $E$ 在每一对上都等号成立。一般的最小化测量与实际等号测量并不同义。下文每个概率、残差与 $G$ 都来自 (1.1) 的同一 $E$。

**定义 1.3（全部共同解码器上的族误差与经典基准）。** 对整个 $M(C_{\rm rec}\otimes B)$ 上的任意 CPTP 映射 $\mathcal R$，令

$$
\varepsilon(\mathcal R,\mathcal N)
=\max_{0\le i<r}\frac12\|\mathcal R\mathcal N(\rho_i)-\rho_i\|_1,
\qquad
\varepsilon_\star(\mathcal N)=\inf_{\mathcal R\text{ CPTP}}
\varepsilon(\mathcal R,\mathcal N).
\tag{1.3}
$$

解码器共同且不依赖未知族成员，误差在所有实际分支平均后比较。允许读取 $B$ 的全部量子信息，没有经典解码器限制。另定义数学比较量

$$
Q(\boldsymbol\rho)=
\inf_{\substack{(F_y)\text{ 任意有限 POVM}\\
\eta_y\text{ 任意输入空间密度矩阵}}}
\max_i\frac12\left\|\sum_y\operatorname{Tr}(F_y\rho_i)\eta_y-\rho_i\right\|_1.
\tag{1.4}
$$

结果数不预设上限，混合制备和零效应均允许。正泛函制备 $X\mapsto\operatorname{Tr}(FX)\eta$ 完全正：对 $F=\sum_j f_j|u_j\rangle\langle u_j|$、$\eta=\sum_k s_k|v_k\rangle\langle v_k|$，可取 Kraus 算子 $\sqrt{f_js_k}|v_k\rangle\langle u_j|$。伴随乘积和为 $F$，故 POVM 后接制备保迹。

(1.3) 是指定有限态族的半迹极小极大目标。更强的全输入与参考目标，例如

$$
\inf_{\mathcal R}\sup_{\substack{Z\text{ 有限}\\
\xi\text{ 为 }A\otimes Z\text{ 上密度矩阵}}}
\frac12\|((\mathcal R\mathcal N-\operatorname{id}_{M(A)})\otimes
\operatorname{id}_Z)(\xi)\|_1,
\tag{1.5}
$$

包含 (1.3) 的测试态，却不能由有限族误差小推出它也小。本文的近似结论只针对 (1.3)。$Q$ 是数学基准，不是获准替换实际仪器的最优化实现。

## 2. 矩形 Kraus 范数与正传输残差

**引理 2.1（基本范数工具）。** 对任意同型矩形矩阵 $U,V$，有

$$
\|UV^\dagger\|_1\le\|U\|_F\|V\|_F,\qquad
\|UU^\dagger-VV^\dagger\|_1
\le(\|U\|_F+\|V\|_F)\|U-V\|_F.
\tag{2.1}
$$

CPTP 映射在 Hermitian 输入上收缩迹范数。若 $\eta$ 为密度矩阵、$P$ 为正交投影、$u=\operatorname{Tr}((I-P)\eta)$，则

$$
\|\eta-P\eta P\|_1\le2\sqrt u.
\tag{2.2}
$$

证明。由奇异值分解得到的迹范数对偶式以及 Frobenius Cauchy–Schwarz，

$$
\|UV^\dagger\|_1
=\sup_{\|Z\|_{\rm op}\le1}|\operatorname{Tr}(ZUV^\dagger)|
\le\sup_{\|Z\|_{\rm op}\le1}\|ZU\|_F\|V\|_F
\le\|U\|_F\|V\|_F.
$$

再用 $UU^\dagger-VV^\dagger=(U-V)U^\dagger+V(U-V)^\dagger$ 即得第二式。若 $H=H_+-H_-$ 是 Hermitian 正负部分分解，则正性、保迹性和三角不等式给出

$$
\|\Phi(H)\|_1\le\operatorname{Tr}\Phi(H_+)+\operatorname{Tr}\Phi(H_-)=\|H\|_1.
$$

最后，取 $\eta$ 的单位向量纯化 $\psi$，令 $\phi=(P\otimes I)\psi$。有 $\|\psi-\phi\|=\sqrt u$、$\|\phi\|\le1$；将 (2.1) 应用于向量外积，再作部分迹的收缩，得到 (2.2)。不要求 $\eta$ 忠实。记录块对角矩阵的迹范数是各块迹范数之和，因为其绝对值也逐块直和。$\square$

**引理 2.2（唯一正传输及精确残差）。** 定义

$$
T_i=\rho_0^{-1/2}(\rho_0^{1/2}\rho_i\rho_0^{1/2})^{1/2}\rho_0^{-1/2},
\qquad T_0=I_A.
\tag{2.3}
$$

则 $T_i>0$ 是 $T_i\rho_0T_i=\rho_i$ 的唯一正解，且
$\operatorname{Tr}(\rho_0T_i)=F(\rho_0,\rho_i)$。删除零效应后，令

$$
t_{ix}=\sqrt{p_i(x)/p_0(x)}>0,\qquad
r_{ix}=\|\sqrt{E_x}(T_i-t_{ix}I_A)\sqrt{\rho_0}\|_F.
$$

有

$$
\delta_{0i}(E)=\sum_x\frac{r_{ix}^2}{2t_{ix}}.
\tag{2.4}
$$

证明。以 $\sqrt{\rho_0}$ 合同变换传输方程，其正解必须满足 $\sqrt{\rho_0}T_i\sqrt{\rho_0}=(\sqrt{\rho_0}\rho_i\sqrt{\rho_0})^{1/2}$，给出存在、唯一及保真迹式。非零正效应在忠实输入上的概率严格正。设

$$
A_x=\sqrt{E_x}\sqrt{\rho_0},\qquad
B_{ix}=\sqrt{E_x}T_i\sqrt{\rho_0}.
$$

其 Frobenius 范数平方分别为 $p_0(x),p_i(x)$，故

$$
\frac{\|B_{ix}-t_{ix}A_x\|_F^2}{2t_{ix}}
=\sqrt{p_0(x)p_i(x)}-\operatorname{Re}\operatorname{Tr}(A_x^\dagger B_{ix}).
$$

最后迹项求和为 $\operatorname{Tr}(\rho_0\sum_xE_xT_i)=F(\rho_0,\rho_i)$，即得 (2.4)。这是 S 定理 2.1 与 E 引理 2.1 的接口，传输方向与概率比方向保持一致。$\square$

零效应不带隐藏分支：若 $E_x=0$，则对每个 $v$ 有 $\sum_a\|K_{xa}v\|^2=0$，逐项非负迫使所有 $K_{xa}=0$。以后涉及比值时删除这些分支；全输出解码器在这些未使用记录扇区上仍可任意 CPTP 补全。

## 3. 无需传输相容性的实际条件输出提升

**定理 3.1（加权条件因子化与经典基准下界）。** 不假定 $T_i$ 对易。只选择锚下界及各态上界

$$
\rho_0\succeq\mu_{\rm a}I_A,\qquad \mu_{\rm a}>0,\qquad
L_i\ge\|\rho_i\|_{\rm op},\qquad
M_i=\sqrt{L_i/\mu_{\rm a}},\qquad M_{\rm a}=\max_{i\ge1}M_i.
\tag{3.1}
$$

对非零实际结果，定义实际条件密度矩阵和比较态

$$
\tau_x=\frac{\mathcal I_x(\rho_0)}{p_0(x)},\qquad
\Omega_i=\sum_xp_i(x)|x\rangle\langle x|\otimes\tau_x.
\tag{3.2}
$$

则 $\Omega_0=\mathcal N(\rho_0)$，并且

$$
\begin{aligned}
\frac12\|\mathcal N(\rho_i)-\Omega_i\|_1
&=\sum_xp_i(x)\frac12\left\|
\frac{\mathcal I_x(\rho_i)}{p_i(x)}-\tau_x\right\|_1\\
&\le\sqrt{2M_i\delta_{0i}(E)}\qquad (i\ge1).
\end{aligned}
\tag{3.3}
$$

因此，对全部共同完整输出解码器取下确界，

$$
\begin{aligned}
\varepsilon_\star(\mathcal N)
&\ge\max\left\{0,Q(\boldsymbol\rho)-\max_{i\ge1}\sqrt{2M_i\delta_{0i}(E)}\right\}\\
&\ge\max\left\{0,Q(\boldsymbol\rho)-\sqrt{2M_{\rm a}qG}\right\}.
\end{aligned}
\tag{3.4}
$$

证明。迹比较给出 $p_i(x)\le L_i\operatorname{Tr}E_x$ 与 $p_0(x)\ge\mu_{\rm a}\operatorname{Tr}E_x$，所以 $t_{ix}\le M_i$。没有交换任何不对易矩阵因子。把实际 Kraus 按列横向拼成矩形矩阵

$$
U_{ix}=[K_{xa}T_i\sqrt{\rho_0}]_a,\qquad
V_{ix}=t_{ix}[K_{xa}\sqrt{\rho_0}]_a.
$$

它们的外积、范数及差满足

$$
\begin{aligned}
U_{ix}U_{ix}^\dagger&=\mathcal I_x(\rho_i),&
V_{ix}V_{ix}^\dagger&=p_i(x)\tau_x,\\
\|U_{ix}\|_F&=\|V_{ix}\|_F=\sqrt{p_i(x)},&
\|U_{ix}-V_{ix}\|_F^2&=r_{ix}^2.
\end{aligned}
$$

末式逐 $a$ 求平方后使用 $\sum_aK_{xa}^\dagger K_{xa}=E_x$。横向矩阵只是证明工具，解码器未获准读取 $a$。引理 2.1 给出分支迹差至多 $2\sqrt{p_i(x)}r_{ix}$。对 $x$ 求和并用 Cauchy–Schwarz、$\sum_xp_i(x)=1$ 与 (2.4)，得到

$$
\frac12\|\mathcal N(\rho_i)-\Omega_i\|_1
\le\sum_x\sqrt{p_i(x)}r_{ix}
\le\sqrt{\sum_xr_{ix}^2}
\le\sqrt{2M_i\delta_{0i}(E)}.
$$

块对角迹范数恒等式也给出 (3.3) 的等号部分。这是实际概率加权估计，不是逐个稀有分支的统一条件误差估计。$\tau_x$ 可以奇异。

现在固定任意一个实际 $\mathcal R$，记 $\varepsilon=\varepsilon(\mathcal R,\mathcal N)$，定义

$$
\eta_x=\mathcal R(|x\rangle\langle x|\otimes\tau_x).
$$

每个 $\eta_x$ 是密度矩阵，因而同一实际 POVM $E$ 后制备 $\eta_x$ 给出合法有限经典链。其在第 $i$ 个态上的输出为

$$
\sum_xp_i(x)\eta_x=\mathcal R(\Omega_i).
$$

迹范数收缩和三角不等式使其误差至多 $\varepsilon+\sqrt{2M_i\delta_{0i}}$；锚误差至多 $\varepsilon$。按 $Q$ 的定义，任何一个这样的链的最大误差都不小于 $Q$，故

$$
Q\le\varepsilon+\max_{i\ge1}\sqrt{2M_i\delta_{0i}}.
$$

又有 $\delta_{0i}\le\sum_{j<k}\delta_{jk}=qG$。取 $\mathcal R$ 的下确界并结合误差非负性，即得 (3.4)，不要求下确界达到。构造比较链不改变用于恢复的实际 $\mathcal N$ 或竞争解码器类。$\square$

特别在 $G=0$ 时，(3.3) 给出实际族内精确条件因子化，即使不预先假定传输相容性也成立；该等号条件本身再由 S 的分类迫使相容。正 $G$ 的结论只涉及指定族，绝不宣称 $\mathcal N$ 在全部输入上是测量制备信道。

## 4. 固定相容族、典范联合块与显式常数

**定义 4.1（相容性与联合几何）。** 以后至 §8 假设锚定正传输两两对易。这是 S 定理 3.1 的精确相容性条件，等价于忠实族的 $\Delta=0$。令 $P_\alpha\ne0$ 为其联合谱投影，按完整不同元组

$$
\lambda_\alpha=(\lambda_{1\alpha},\ldots,\lambda_{r-1,\alpha}),\qquad
T_iP_\alpha=\lambda_{i\alpha}P_\alpha,\quad \lambda_{i\alpha}>0
\tag{4.1}
$$

编号。相同元组必须合并，不能人为细分简并块以制造间隙。定义

$$
\mathcal D(X)=\sum_\alpha P_\alpha XP_\alpha,\qquad
h=\|\rho_0-\mathcal D(\rho_0)\|_F.
\tag{4.2}
$$

$\mathcal D$ 为 CPTP 钳制映射，也是 Frobenius 内积的正交投影。不同有序矩阵块彼此正交，故该断言及 $I-\mathcal D$ 的 Frobenius 收缩性直接成立。

选择共同输入下界

$$
0<\mu\le1/d,\qquad \rho_i\succeq\mu I_A\ (0\le i<r),\qquad
L=1-(d-1)\mu,\qquad M=\sqrt{L/\mu}.
\tag{4.3}
$$

迹归一给出 $\rho_i\preceq LI_A$。由

$$
\mu T_i^2\preceq\rho_i\preceq LI_A,
\qquad \mu I_A\preceq\rho_i\preceq LT_i^2
$$

得 $M^{-1}I_A\preceq T_i\preceq MI_A$；同一迹比较给出 $t_{ix}\le M$。

**命题 4.2（单块边界）。** 如果只有一个联合块，则全部输入态相同，任意实际仪器都有 $G=0$ 与 $\varepsilon_\star=0$。

证明。此时 $T_i=\lambda_iI_A$，$\rho_i=\lambda_i^2\rho_0$。归一性迫使 $\lambda_i=1$。全部经典分布相同，根保真均为一，因此每对缺陷为零。常值解码器 $Y\mapsto\operatorname{Tr}(Y)\rho_0$ CPTP 且恢复全部相同目标。$\square$

以下仅在至少两个不同联合块时定义

$$
\begin{aligned}
\gamma^2&=\min_{\alpha\ne\beta}\sum_{i=1}^{r-1}
(\lambda_{i\alpha}-\lambda_{i\beta})^2>0,\\
v_{i\alpha}&=\lambda_{i\alpha}^2,\qquad
\Gamma^2=\min_{\alpha\ne\beta}\sum_{i=1}^{r-1}
(v_{i\alpha}-v_{i\beta})^2>0,\\
a_i&=\max_\alpha v_{i\alpha}^2-\min_\alpha v_{i\alpha}^2,
\qquad b_i=\max_\alpha v_{i\alpha}-\min_\alpha v_{i\alpha},\\
K_{\rm sp}&=\sum_{i=1}^{r-1}(a_i+2b_i)>0,\\
b_\star&=\min\left\{\frac h4,\frac{\Gamma^2h^2}{16K_{\rm sp}}\right\},
\qquad
\kappa=\sqrt{\frac{32LMq}{\mu\gamma^2}}.
\end{aligned}
\tag{4.4}
$$

不同正元组的平方仍不同，有限性给出两个正间隙；至少一个 $v_i$ 不常值，故 $K_{\rm sp}>0$。$h$ 可为零，此时 $b_\star=0$，其余常数仍良定义。

**定理 4.3（固定相容族的显式实际恢复障碍）。** 对每个 (1.1) 的实际仪器及每个完整联合输出解码器，有

$$
\varepsilon(\mathcal R,\mathcal N)\ge
\max\{0,b_\star-\kappa\sqrt G\},\qquad
\varepsilon_\star(\mathcal N)\ge
\max\{0,b_\star-\kappa\sqrt G\}.
\tag{4.5}
$$

更强的隐式不等式为

$$
h\le2e+\frac2\Gamma\sqrt{K_{\rm sp}e},
\qquad e=\varepsilon(\mathcal R,\mathcal N)+\kappa\sqrt G.
\tag{4.6}
$$

常数只依赖此固定输入族及所选合法输入界，不依赖实际结果数与 $\dim B$。证明由以下两节完整给出。它不要求 C 定理 3.1 的非零块概率消失关系。

## 5. 实际 Kraus 泄漏及回到同一仪器的比较

**引理 5.1（最近联合元组与泄漏）。** 对每个非零实际结果 $x$，令 $\alpha(x)$ 为使 $\|\lambda_\alpha-t_x\|_2$ 最小的块，其中 $t_x=(t_{1x},\ldots,t_{r-1,x})$；平局可任意选择。则

$$
\ell:=\sum_x\operatorname{Tr}(E_x(I-P_{\alpha(x)}))
\le\frac{8Mq}{\mu\gamma^2}G.
\tag{5.1}
$$

证明。置

$$
S_i=\sum_x\|\sqrt{E_x}(T_i-t_{ix}I_A)\|_F^2.
$$

对任意 $Z$ 有 $\|Z\sqrt{\rho_0}\|_F^2\ge\mu\|Z\|_F^2$。引理 2.2 及 $t_{ix}\le M$ 因此给出

$$
S_i\le\frac{2M}{\mu}\delta_{0i}.
\tag{5.2}
$$

谱展开不要求 $E_x$ 块对角：利用迹循环及 $T_i-tI$ 的谱平方，

$$
S_i=\sum_{x,\alpha}\operatorname{Tr}(E_xP_\alpha)
(\lambda_{i\alpha}-t_{ix})^2.
$$

若 $\beta\ne\alpha(x)$，最近点性质和三角不等式给出

$$
\gamma\le\|\lambda_\beta-\lambda_{\alpha(x)}\|_2
\le\|\lambda_\beta-t_x\|_2+\|t_x-\lambda_{\alpha(x)}\|_2
\le2\|\lambda_\beta-t_x\|_2.
$$

因此

$$
\sum_iS_i\ge\frac{\gamma^2}{4}
\sum_x\sum_{\beta\ne\alpha(x)}\operatorname{Tr}(E_xP_\beta)
=\frac{\gamma^2}{4}\ell.
$$

结合 (5.2) 及 $\sum_{i\ge1}\delta_{0i}\le qG$ 即得 (5.1)。求和消除了结果数，没有逐结果正概率下界。$\square$

**引理 5.2（代数辅助子信道和实际范数比较）。** 只为证明定义

$$
K'_{xa}=K_{xa}P_{\alpha(x)},\qquad
\mathcal N'(X)=\sum_x|x\rangle\langle x|\otimes
\sum_aK'_{xa}XK_{xa}^{\prime\dagger}.
\tag{5.3}
$$

则 $\mathcal N'$ 完全正且迹不增，$\mathcal N'\mathcal D=\mathcal N'$。对每个 $i$，实际原信道满足

$$
\frac12\|\mathcal N(\rho_i)-\mathcal N\mathcal D(\rho_i)\|_1
\le2\sqrt{L\ell}\le\kappa\sqrt G.
\tag{5.4}
$$

证明。辅助 Kraus 的效应和为

$$
F'=\sum_xP_{\alpha(x)}E_xP_{\alpha(x)}.
$$

它是块对角矩阵；在第 $\alpha$ 块上等于
$P_\alpha(\sum_{x:\alpha(x)=\alpha}E_x)P_\alpha\preceq P_\alpha$，因为括号内只是实际 POVM 的一个子和。因此 $0\preceq F'\preceq I_A$，证明迹不增。每个辅助 Kraus 只含一个输入块，故钳制前后输出相同，即 $\mathcal N'\mathcal D=\mathcal N'$。

对任意密度矩阵 $\omega\preceq LI_A$，令

$$
U_x=[K_{xa}\sqrt\omega]_a,\qquad
V_x=[K_{xa}P_{\alpha(x)}\sqrt\omega]_a.
$$

直接由实际保迹性和 $F'\preceq I_A$ 得

$$
\sum_x\|U_x\|_F^2=1,\qquad
\sum_x\|V_x\|_F^2=\operatorname{Tr}(F'\omega)\le1.
$$

差的平方和为

$$
\begin{aligned}
\sum_x\|U_x-V_x\|_F^2
&=\operatorname{Tr}\left(\omega\sum_x
(I-P_{\alpha(x)})E_x(I-P_{\alpha(x)})\right)\\
&\le L\sum_x\operatorname{Tr}((I-P_{\alpha(x)})E_x(I-P_{\alpha(x)}))
=L\ell.
\end{aligned}
$$

被比较的矩阵在迹内均为正，故此上界合法。由 (2.1) 和对 $x$ 的 Cauchy–Schwarz，

$$
\begin{aligned}
\|\mathcal N(\omega)-\mathcal N'(\omega)\|_1
&\le\sum_x(\|U_x\|_F+\|V_x\|_F)\|U_x-V_x\|_F\\
&\le2\sqrt{L\ell}.
\end{aligned}
\tag{5.5}
$$

第二步也可把含 $U_x$ 与含 $V_x$ 的和分别估计，各自至多 $\sqrt{L\ell}$。$\rho_i$ 与 $\mathcal D(\rho_i)$ 都是密度矩阵且不超过 $LI_A$。分别代入 (5.5)，用 $\mathcal N'\mathcal D=\mathcal N'$ 消去中间差，再由三角不等式得全迹差至多 $4\sqrt{L\ell}$。除以二并代入 (5.1) 就是 (5.4) 与 (4.4) 的 $\kappa$。$\square$

$\mathcal N'$ 只是同型输出中的代数辅助对象，通常不保迹；它没有被装入实际恢复协议，也没有被补全后当成新仪器。最终 (5.4) 两端使用的都是原来的 $\mathcal N$。

**命题 5.3（同一实际解码器的联合块比较族）。** 定义

$$
A_\alpha=P_\alpha\rho_0P_\alpha,\quad
\pi_0(\alpha)=\operatorname{Tr}A_\alpha>0,\quad
\sigma_\alpha=A_\alpha/\pi_0(\alpha),\quad
\pi_i(\alpha)=v_{i\alpha}\pi_0(\alpha).
\tag{5.6}
$$

则 $\pi_i$ 为概率列向量，且

$$
\mathcal D(\rho_i)=\sum_\alpha\pi_i(\alpha)\sigma_\alpha.
$$

固定同一个实际 $\mathcal R$，令

$$
\eta_\alpha=\mathcal R\mathcal N(\sigma_\alpha),\qquad
\omega_i=\mathcal R\mathcal N\mathcal D(\rho_i)
=\sum_\alpha\pi_i(\alpha)\eta_\alpha,
\qquad e_i=\tfrac12\|\omega_i-\rho_i\|_1.
\tag{5.7}
$$

则每个 $\eta_\alpha$ 为密度矩阵，并且 $e_i\le\varepsilon(\mathcal R,\mathcal N)+\kappa\sqrt G$。

证明。忠实性使 $\pi_0(\alpha)\ge\mu\operatorname{Tr}P_\alpha>0$。传输在块上为标量，所以 $P_\alpha\rho_iP_\alpha=v_{i\alpha}A_\alpha$，给出各分解与归一性。原来的 $\mathcal N,\mathcal R$ 都 CPTP，故 $\eta_\alpha$ 正且迹一。将 (5.4) 交给同一个 $\mathcal R$ 作迹范数收缩，再与实际重建误差作三角比较即得结论。$\square$

## 6. 稳健平稳平方差与精确对易检测

**引理 6.1（允许不平稳的平方差恒等式）。** 对任意一组密度矩阵 $\eta_\alpha$，按 (5.7) 定义 $\omega_i,e_i$，则

$$
h\le2e_0+\frac2\Gamma
\sqrt{\left(\sum_i a_i\right)e_0+2\sum_i b_i e_i}.
\tag{6.1}
$$

这里求和均为 $1\le i<r$；不要求 $\pi_i$ 线性独立，也不要求随机矩阵可逆、不可约或满足详细平衡。

证明。令列随机矩阵、测量误差及非负权重为

$$
S_{\beta\alpha}=\operatorname{Tr}(P_\beta\eta_\alpha),\qquad
d_i=S\pi_i-\pi_i,\qquad
W_{\beta\alpha}=S_{\beta\alpha}\pi_0(\alpha).
$$

用同一个联合 PVM 测量 $\omega_i$ 和 $\rho_i$，迹范数收缩给出
$\|d_i\|_1\le2e_i$、$\sum_\beta d_i(\beta)=0$。权重的列和、行和与加权行和精确为

$$
\begin{aligned}
\sum_\beta W_{\beta\alpha}&=\pi_0(\alpha),\\
\sum_\alpha W_{\beta\alpha}&=\pi_0(\beta)+d_0(\beta),\\
\sum_\alpha W_{\beta\alpha}v_{i\alpha}&=\pi_i(\beta)+d_i(\beta).
\end{aligned}
\tag{6.2}
$$

完全展开非负平方差，使用 $\pi_i(\beta)=\pi_0(\beta)v_{i\beta}$，得到

$$
\begin{aligned}
H_i&:=\sum_{\beta,\alpha}W_{\beta\alpha}(v_{i\alpha}-v_{i\beta})^2\\
&=\sum_\alpha\pi_0(\alpha)v_{i\alpha}^2
 +\sum_\beta(\pi_0(\beta)+d_0(\beta))v_{i\beta}^2
 -2\sum_\beta(\pi_i(\beta)+d_i(\beta))v_{i\beta}\\
&=\sum_\beta d_0(\beta)v_{i\beta}^2
 -2\sum_\beta d_i(\beta)v_{i\beta}.
\end{aligned}
\tag{6.3}
$$

这是近似平稳情形的精确代数式，没有把 $d_i$ 静默设成零。对于任何实零和向量 $d$ 与实向量 $f$，从 $f$ 中减去最大值和最小值的中点，得

$$
\left|\sum_\beta d(\beta)f(\beta)\right|
\le\frac{\max f-\min f}{2}\|d\|_1.
$$

因此 $H_i\le a_i e_0+2b_i e_i$。记跨块流量

$$
\ell_S=\sum_{\alpha\ne\beta}W_{\beta\alpha}
=\sum_\alpha\pi_0(\alpha)\operatorname{Tr}((I-P_\alpha)\eta_\alpha).
$$

不同联合平方元组的间隙给出

$$
\Gamma^2\ell_S\le\sum_iH_i
\le\left(\sum_i a_i\right)e_0+2\sum_i b_i e_i.
\tag{6.4}
$$

令 $Z=\sum_\alpha\pi_0(\alpha)P_\alpha\eta_\alpha P_\alpha$。此矩阵块对角，不必迹一。引理 2.1 的投影估计和加权 Cauchy–Schwarz 给出

$$
\|\omega_0-Z\|_1
\le2\sum_\alpha\pi_0(\alpha)
\sqrt{\operatorname{Tr}((I-P_\alpha)\eta_\alpha)}
\le2\sqrt{\ell_S}.
$$

因 $(I-\mathcal D)Z=0$、$I-\mathcal D$ 的 Frobenius 收缩性及 $\|X\|_F\le\|X\|_1$，

$$
\begin{aligned}
h&=\|(I-\mathcal D)(\rho_0-Z)\|_F\\
&\le\|\rho_0-\omega_0\|_1+\|\omega_0-Z\|_1
\le2e_0+2\sqrt{\ell_S}.
\end{aligned}
$$

结合 (6.4) 就是 (6.1)。该论证允许奇异 $\eta_\alpha$，也允许块内任意简并。$\square$

**定理 4.3 的证明。** 命题 5.3 使所有 $e_i\le e=\varepsilon(\mathcal R,\mathcal N)+\kappa\sqrt G$。代入 (6.1) 得 (4.6)。若 $e<b_\star$ 且 $h>0$，则 $2e<h/2$ 且 $(2/\Gamma)\sqrt{K_{\rm sp}e}<h/2$，与 (4.6) 矛盾。故 $e\ge b_\star$。$h=0$ 时这个结论由非负性直接成立。移项，结合误差非负性，再取全部实际 $\mathcal R$ 的下确界得 (4.5)。$\square$

**命题 6.2（相容族的精确对易检测）。** 在定义 4.1 下，$h=0$ 当且仅当原态两两对易；当至少两块时，$b_\star>0$ 当且仅当原态不两两对易。

证明。若 $h=0$，各态的第 $\alpha$ 块都是同一 $A_\alpha$ 的标量倍数 $v_{i\alpha}A_\alpha$，因此在每块内和跨块都两两对易。反向，若全部忠实态两两对易，可在同一基中对角化；唯一正传输在该基中的对角元为 $\sqrt{\rho_{i,k}/\rho_{0,k}}$，故每个 $T_i$ 与 $\rho_0$ 对易。另一方面，

$$
P_\alpha[\rho_0,T_i]P_\beta
=(\lambda_{i\beta}-\lambda_{i\alpha})P_\alpha\rho_0P_\beta.
$$

不同联合元组总有一个分量不同，故这些交换子全零迫使跨块矩阵元全零，即 $h=0$。$b_\star$ 的两个分支具有正有限系数，给出最后断言。$\square$

**推论 6.3（实际等号分类的精确极限）。** 对每个实际 $G=0$ 仪器，存在零误差共同解码器当且仅当原态两两对易。

证明。必要性由 (4.6) 在 $\varepsilon=G=0$ 得 $h=0$，再用命题 6.2；单块已由命题 4.2 处理。充分性可给出实际全代数解码器。零残差强制 $\sqrt{E_x}T_i=t_{ix}\sqrt{E_x}$ 及其伴随，所以每个非零 $E_x$ 支撑于一个联合块，且 $\sum_{x:\alpha(x)=\alpha}E_x=P_\alpha$。效应支撑再强制每个实际 $K_{xa}=K_{xa}P_{\alpha(x)}$：对补空间向量取 $\sum_a\|K_{xa}v\|^2=0$ 即得。由此实际条件输出族内因子化，且概率块和为 $\pi_i(\alpha)$。

若 $h=0$，在整个输出代数上定义

$$
\mathcal R(Y)=\sum_x\operatorname{Tr}(Y_{xx})\sigma_{\alpha(x)},\qquad
Y_{xx}=(\langle x|\otimes I_B)Y(|x\rangle\otimes I_B).
\tag{6.5}
$$

它由记录基测量和正泛函制备构成，故 CP；每个制备迹一使其保迹。零效应扇区任选密度矩阵补全。于是
$\mathcal R\mathcal N(\rho_i)=\sum_\alpha\pi_i(\alpha)\sigma_\alpha=\rho_i$。这是允许忽略 $B$ 的一个解码器选择，未限制其他解码器。此精确分类与 E 定理 3.1 一致；正缺陷下的最优解码器分类并未由它给出。$\square$

## 7. 带全部前提的统一类推论

**推论 7.1（固定维数、忠实性、联合间隙及非对易幅度）。** 先固定整数 $d\ge2,r\ge3$，并选择

$$
0<\mu_0<1/d,\qquad \gamma_0>0,\qquad h_0>0.
\tag{7.1}
$$

只考虑如下族：输入忠实且 $\rho_i\succeq\mu_0I_A$；锚定正传输两两对易；按不同完整元组合并的联合分解至少有两块；其 $\gamma\ge\gamma_0$ 且 $h\ge h_0$。此时才定义

$$
\begin{aligned}
q&=r(r-1)/2,\qquad L_0=1-(d-1)\mu_0,\qquad M_0=\sqrt{L_0/\mu_0},\\
\overline K&=(r-1)(M_0^4+2M_0^2),\\
b_0&=\min\left\{\frac{h_0}{4},
\frac{\gamma_0^2h_0^2}{4M_0^2\overline K}\right\}>0,\\
\kappa_0&=\sqrt{\frac{32L_0M_0q}{\mu_0\gamma_0^2}}.
\end{aligned}
\tag{7.2}
$$

对这类中每个输入族的每个实际有限仪器，

$$
\varepsilon_\star(\mathcal N)\ge\max\{0,b_0-\kappa_0\sqrt G\}.
\tag{7.3}
$$

证明。以 $\mu=\mu_0$ 应用主定理，所有 $\lambda_{i\alpha}\in[M_0^{-1},M_0]$，故

$$
|\lambda_{i\alpha}^2-\lambda_{i\beta}^2|
=|\lambda_{i\alpha}-\lambda_{i\beta}|(\lambda_{i\alpha}+\lambda_{i\beta})
\ge\frac2{M_0}|\lambda_{i\alpha}-\lambda_{i\beta}|.
$$

逐分量平方求和再取最小值得 $\Gamma^2\ge4\gamma^2/M_0^2$。另有 $a_i\le M_0^4$、$b_i\le M_0^2$，所以 $K_{\rm sp}\le\overline K$。于是

$$
b_\star\ge b_0,\qquad \kappa\le\kappa_0,
$$

代入 (4.5) 即得结论。$h_0>0$ 是非对易幅度条件，不能只改写为“态不对易”。若取 $\mu_0=1/d$，迹一与下界迫使所有态为 $I_A/d$，其 $h=0$，不可能满足 $h\ge h_0>0$；更大的 $\mu_0$ 连迹一都不允许。因此 (7.1) 在定义根号常数之前排除端点。其他参数若使类为空，推论只是空类上的条件命题，不附加存在性。$\square$

这是一组明确有限输入参数上的统一界，并在该类内对结果数和输出维数统一。它不是任意输入维数、任意族大小、任意忠实性或任意资源权限的无参数正下界。

## 8. 无块概率消失关系的 qutrit 实际应用

**命题 8.1（相容而非对易、概率独立的三态）。** 取 $0<c<1$、$0<t<1$，令

$$
\begin{gathered}
\rho_0=\frac13\begin{pmatrix}1&c&0\\c&1&0\\0&0&1\end{pmatrix},
\qquad u=\sqrt{1+t},\quad v=\sqrt{1-t},\\
T_1=\operatorname{diag}(u,v,1),\qquad
T_2=\operatorname{diag}(1,u,v),\qquad
\rho_i=T_i\rho_0T_i\quad(i=1,2).
\end{gathered}
\tag{8.1}
$$

这些态忠实、迹一，正传输相容，且有三个不同的一维联合块。其三个块概率向量线性独立；因此 C 定理 3.1 所需的非零块概率消失关系在此不存在，而定理 4.3 给出严格正的零缺陷恢复障碍。

证明及常数。$\rho_0$ 的特征值为 $(1+c)/3,(1-c)/3,1/3$。因为 $T_i^2\succeq(1-t)I_3$，

$$
\rho_i\succeq\frac{1-c}{3}T_i^2\succeq\mu I_3,
\qquad \mu=\frac{(1-c)(1-t)}3>0.
\tag{8.2}
$$

这个 $\mu$ 也适用于锚。三个对角和均为一，故是密度矩阵；$T_i$ 正且满足传输方程，唯一性认定其为锚定正传输。二者对角因而对易。其联合元组按坐标依次为 $(u,1),(v,u),(1,v)$，因 $u>1>v>0$ 而互异。

相应概率为

$$
\pi_0=\tfrac13(1,1,1),\quad
\pi_1=\tfrac13(1+t,1-t,1),\quad
\pi_2=\tfrac13(1,1+t,1-t).
\tag{8.3}
$$

若 $z_0\pi_0+z_1\pi_1+z_2\pi_2=0$，先对坐标求和得 $z_0+z_1+z_2=0$；消去锚后，
$z_1(t,-t,0)+z_2(0,t,-t)=0$，第一和第三坐标迫使 $z_1=z_2=0$，继而 $z_0=0$。这排除所有非零实或复系数的块概率消失关系。

另一方面，

$$
[\rho_0,\rho_1]_{12}=-\frac{2ct}{9}\ne0,
\qquad h=\frac{c\sqrt2}{3}.
\tag{8.4}
$$

交换子条目由 $\rho_0$ 前两项相等的对角元、$\rho_1$ 的对角差 $-2t/3$ 及 $\rho_{0,12}=c/3$ 得到。$h$ 由两个非零共轭跨块元的平方和得到。因此不是仅有传输相容而无实际非对易障碍的族。

三对联合传输距离平方为

$$
(u-v)^2+(u-1)^2,\qquad
(u-1)^2+(1-v)^2,\qquad
(1-v)^2+(u-v)^2.
$$

由于 $u-v=(u-1)+(1-v)$ 严格大于两个正加数，最小者为中项，故

$$
\gamma^2=(\sqrt{1+t}-1)^2+(1-\sqrt{1-t})^2>0.
\tag{8.5}
$$

平方元组的三对距离平方分别为 $5t^2,2t^2,5t^2$，所以 $\Gamma^2=2t^2$。每个 $v_i$ 的取值集为 $\{1+t,1-t,1\}$，有 $a_i=4t$、$b_i=2t$，从而

$$
K_{\rm sp}=16t,\qquad
b_\star=\min\left\{\frac{c\sqrt2}{12},\frac{c^2t}{576}\right\}>0.
\tag{8.6}
$$

取 $d=r=3,q=3$，所有剩余常数明确为

$$
L=1-2\mu,\qquad M=\sqrt{L/\mu},\qquad
\kappa=\sqrt{\frac{96LM}{\mu[(\sqrt{1+t}-1)^2+(1-\sqrt{1-t})^2]}}.
\tag{8.7}
$$

这完整指定了 (4.5) 在本例中的参数，无需概率关系证书。$\square$

**命题 8.2（同一实际正缺陷仪器与达到的上误差）。** 令 $B=A=\mathbb C^3$、$P_j=|j\rangle\langle j|$，取 $0<\zeta<1$ 的四记录实际仪器

$$
K_j=\sqrt{1-\zeta}\,P_j\quad(j=1,2,3),\qquad
K_*=\sqrt\zeta\,I_3.
\tag{8.8}
$$

令

$$
g_0=1-F_U(\boldsymbol\rho)
=1-\frac{2+3u+3v+uv}{9}>0.
\tag{8.9}
$$

则此实际仪器有 $G=\zeta g_0>0$，且

$$
\max\{0,b_\star-\kappa\sqrt{\zeta g_0}\}
\le\varepsilon_\star(\mathcal N_\zeta)
\le(1-\zeta)\frac{c\sqrt{1+t}}3.
\tag{8.10}
$$

特别当 $0<\zeta<\min\{1,b_\star^2/(\kappa^2g_0)\}$ 时左边严格正。

证明。实际效应和为 $(1-\zeta)\sum_jP_j+\zeta I_3=I_3$，所以确为保留量子 $B$ 和全部四记录的仪器。共同联合谱 PVM 使每对经典根保真等于 $F_{ij}$。新增 $*$ 分支对所有密度矩阵的概率都是 $\zeta$，于是

$$
C_{ij}(E_{\rm actual})=(1-\zeta)F_{ij}+\zeta,
\qquad \delta_{ij}=\zeta(1-F_{ij}).
\tag{8.11}
$$

相容性给出成对正传输 $T_jT_i^{-1}$，所以
$F_{ij}=\operatorname{Tr}(\rho_0T_iT_j)$。$\rho_0$ 对角元均为 $1/3$，从而

$$
F_{01}=F_{02}=\frac{1+u+v}{3},\qquad
F_{12}=\frac{u+uv+v}{3},
$$

得到 (8.9)。$\pi_0\ne\pi_1$，两者都是概率向量，严格 Cauchy–Schwarz 使其根重叠 $F_{01}<1$；其余根保真至多一，所以 $g_0>0$。对 (8.11) 求平均得实际 $G=\zeta g_0$。

给出整个联合代数上的一个共同解码器：在 $*$ 记录上使用恒等，在 $j$ 记录上制备 $P_j$，即

$$
\mathcal R_\zeta(Y)=Y_{**}+\sum_{j=1}^3\operatorname{Tr}(Y_{jj})P_j.
\tag{8.12}
$$

记录压缩到对角块、恒等分支和制备分支均 CP，输出迹之和等于 $\operatorname{Tr}Y$，故此映射 CPTP。其实际重建为 $\zeta\rho_i+(1-\zeta)\mathcal D(\rho_i)$。三态仅有前两坐标的非零跨块元，模依次为

$$
\frac c3,\qquad \frac{c\sqrt{1-t^2}}3,\qquad \frac{c\sqrt{1+t}}3.
$$

仅含一对共轭非对角元 $z,\bar z$ 的 Hermitian 矩阵特征值为 $|z|,-|z|,0$，故半迹范数等于 $|z|$。第三项最大，给出 (8.10) 的实际达到上界；下界是主定理对同一仪器的全部竞争解码器的结论。$*$ 分支真实保留量子态且被解码使用，没有以另一个测量替换正缺陷实际实现。$\square$

## 9. 既有三态经典精确值的完整量子输出延伸

**来源接口 9.1（直接复用 C 定理 2.1）。** 使用 C §1 的同一三个态

$$
\begin{aligned}
\sigma_0&=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},\\
\sigma_+&=\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix},\qquad
\sigma_- =\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix}.
\end{aligned}
\tag{9.1}
$$

C 的参数对应为 $u=w=1/2,v=\sqrt3/4$；其 $h=u-v$ 是该源的 Bloch 参数，与本文 (4.2) 的 Frobenius 块相干量含义不同。令 $t_\star$ 是区间 $(\sqrt3/4,1/2)$ 内唯一满足

$$
\frac12-t_\star=
\sqrt{(t_\star-\sqrt3/4)^2+\frac14(1-\sqrt{1-t_\star^2})^2}
\tag{9.2}
$$

的正根。该既有定理已经对任意有限测量和任意共同制备证明

$$
Q=Q(\sigma_0,\sigma_+,\sigma_-)=\frac{1/2-t_\star}{2},
\qquad
\frac{4-\sqrt{13}}{16}<Q<\frac{2-\sqrt3}{8}.
\tag{9.3}
$$

其达到方案为 $P_\pm=(I_2\pm Z)/2$ 后制备

$$
\omega_\pm=\frac{I_2+t_\star X\pm\sqrt{1-t_\star^2}Z}{2},
\tag{9.4}
$$

三个半迹误差都等于 $Q$。$X,Z$ 是标准 Pauli 矩阵。本文直接调用该全有限测量精确极小极大结果，不重做其对称化、全局支撑泛函与最优化证明，也不将该证明计作本文新增内容。

**定理 9.2（任意实际有限仪器的稳健下界及每个等号实现的精确值）。** 对 (9.1) 的任何实际有限仪器，无论有限 $B$ 和实际结果数如何，

$$
\varepsilon_\star(\mathcal N)\ge\max\{0,Q-\sqrt{12G}\}.
\tag{9.5}
$$

若该实际仪器 $G=0$，则每一个这样的实现都满足精确等式

$$
\varepsilon_\star(\mathcal N)=Q.
\tag{9.6}
$$

证明。锚 $\sigma_0$ 的特征值为 $3/4,1/4$，故 (3.1) 可取 $\mu_{\rm a}=1/4$。另外两个密度矩阵都不超过 $I_2$，可取 $L_+=L_-=1$，于是 $M_i=2$、$q=3$。定理 3.1 给出 $\sqrt{2M_{\rm a}qG}=\sqrt{12G}$，证明 (9.5)。这里只使用锚下界；$1/4$ 不是共同下界。事实上 $\sigma_\pm$ 的最小特征值是 $(4-\sqrt7)/8<1/4$，因为其 Bloch 长度为 $\sqrt7/4$。

现在固定任意实际 $G=0$ 实现。正传输为

$$
D_+=\operatorname{diag}(\sqrt{3/2},1/\sqrt2),\qquad
D_-=\operatorname{diag}(1/\sqrt2,\sqrt{3/2}).
$$

它们对易，两个不同联合块正是 $P_+,P_-$。引理 2.2 的零残差使每个非零实际效应支撑在其中一轴，且各轴效应和等于相应 $P_\pm$。因此实际记录可按该轴聚合，其概率和精确为 $\operatorname{Tr}(P_\pm\sigma_i)$。在全输出代数上使用

$$
\mathcal R(Y)=\sum_x\operatorname{Tr}(Y_{xx})\omega_{\alpha(x)},
\qquad \alpha(x)\in\{+,-\},
\tag{9.7}
$$

零效应扇区任意补全。它是合法 CPTP 解码器，虽可忽略 $B$，仍属于允许的全部量子输出解码器类。实际输出经它恢复成

$$
\sum_xp_i(x)\omega_{\alpha(x)}
=\sum_{\alpha=\pm}\operatorname{Tr}(P_\alpha\sigma_i)\omega_\alpha.
$$

这是既有达到方案的同一重建，最大误差为 $Q$，故 $\varepsilon_\star\le Q$。下界由 (9.5) 在 $G=0$ 给出。任意实际保留量子输出都已包含在下界量词中，所以没有假设“所有解码器必为经典”。$\square$

**命题 9.3（实际正缺陷的双侧例）。** 令 $B=\mathbb C^2$，实际三记录 Kraus 为

$$
K_\pm=\sqrt{1-\zeta}P_\pm,\qquad K_*=\sqrt\zeta I_2,
\qquad 0<\zeta<1.
\tag{9.8}
$$

定义明确正数

$$
g_\sigma=1-F_U(\sigma_0,\sigma_+,\sigma_-)
=1-\frac13\left(\frac{\sqrt3+1}{\sqrt2}+\frac{\sqrt3}{2}\right)>0.
\tag{9.9}
$$

则实际 $G=\zeta g_\sigma$，且

$$
\max\{0,Q-\sqrt{12\zeta g_\sigma}\}
\le\varepsilon_\star(\mathcal N_\zeta)
\le(1-\zeta)Q.
\tag{9.10}
$$

对 $0<\zeta<\min\{1,Q^2/(12g_\sigma)\}$，左界严格正。

证明。效应和为 $I_2$。坐标 PVM 是共同等号测量，所以同命题 8.2 的分支概率代数给出 $\delta_{ij}=\zeta(1-F_{ij})$。相容正传输给出

$$
F_{0+}=F_{0-}=\frac{\sqrt3+1}{2\sqrt2},\qquad
F_{+-}=\operatorname{Tr}(\sigma_0D_+D_-)=\frac{\sqrt3}{2},
$$

得到 (9.9)。锚与 $+$ 态的坐标分布不同，根重叠严格小于一，故平均也严格小于一。

具体共同解码器为

$$
\mathcal R(Y)=Y_{**}
+\operatorname{Tr}(Y_{++})\omega_+
+\operatorname{Tr}(Y_{--})\omega_-.
\tag{9.11}
$$

各分支 CP，迹相加等于总输入迹，因此全联合代数上 CPTP。其重建为
$\zeta\sigma_i+(1-\zeta)\Lambda_\star(\sigma_i)$，其中 $\Lambda_\star$ 是来源接口 9.1 的达到经典信道。与目标的差等于 $(1-\zeta)(\Lambda_\star(\sigma_i)-\sigma_i)$；由迹范数齐次性以及三个源误差均为 $Q$，该实际解码器的最大误差精确为 $(1-\zeta)Q$。下界对同一正缺陷仪器应用 (9.5) 即得。它未求出正缺陷下的精确最优值，也未证明平方根系数或阶数最优。$\square$

## 10. 两个实际统一性反例及退化边界

**命题 10.1（缺少非对易幅度时不存在统一正障碍）。** 即使固定 $d=2,r=3$、正的共同忠实下界以及正的联合传输间隙，仅要求每个族不对易，也不能在全部实际 $G=0$ 仪器上得到统一的严格正恢复误差下界。

证明。固定 $0<a<b<1$ 和 $0<k_{\max}<1$。对每个 $0<k\le k_{\max}$，取 $s\in\{0,a,b\}$ 的三态

$$
\rho_s(k)=\frac12\begin{pmatrix}
1+s&k\sqrt{1-s^2}\\k\sqrt{1-s^2}&1-s
\end{pmatrix}.
\tag{10.1}
$$

它们均为 $T_s\rho_0(k)T_s$，其中 $T_s=\operatorname{diag}(\sqrt{1+s},\sqrt{1-s})$；锚的最小特征值为 $(1-k)/2$。因此统一地

$$
\rho_s(k)\succeq\frac{1-k_{\max}}2T_s^2
\succeq\mu_0I_2,
\qquad \mu_0=\frac{(1-k_{\max})(1-b)}2>0.
$$

迹一显然，故全族忠实；传输相容。两个不同联合元组的距离平方为固定正数

$$
\gamma^2=(\sqrt{1+a}-\sqrt{1-a})^2
+(\sqrt{1+b}-\sqrt{1-b})^2.
\tag{10.2}
$$

对所有 $k>0$，

$$
[\rho_0(k),\rho_a(k)]
=\begin{pmatrix}0&-ka/2\\ka/2&0\end{pmatrix}\ne0,
\qquad h=\frac{k}{\sqrt2}.
$$

固定实际 $B=\mathbb C^2$、Kraus $P_0,P_1$，完整保留其两个实际记录和量子输出。其效应是联合谱 PVM，故实际 $G=0$。一个共同全输出解码器由记录 $j$ 制备 $P_j$，重建 $\mathcal D(\rho_s(k))$；其误差为 $k\sqrt{1-s^2}/2$，在锚上达到最大值 $k/2$。所以 $0\le\varepsilon_\star\le k/2\longrightarrow0$。

由此，对这些固定 $d,r,\mu_0,\gamma$ 的整个非对易相容类，不存在一个 $b>0$ 使所有实际零缺陷仪器都满足 $\varepsilon_\star\ge b$。特别是仅以维数、忠实性、间隙和“不对易”这个布尔性质为参数的正零缺陷截距被此类反驳。主定理保留幅度 $h\to0$，不受反驳。$\square$

**命题 10.2（联合间隙合并时，固定正块相干量也不够）。** 即使有固定的正共同忠实下界及每个族的 $h\ge h_0>0$，若不要求联合间隙远离零，也不能在全部实际零缺陷仪器上得到统一正恢复障碍。

证明。固定 $0<k<1$、$0<a<b<1$，在 (10.1) 中用 $s\in\{0,a\tau,b\tau\}$，$0<\tau\le1$。共同下界可固定为 $(1-k)(1-b)/2$。对每个 $\tau>0$，正传输仍相容且有两个不同坐标联合块，$h=k/\sqrt2$ 不变，交换子在 $s=a\tau$ 时为非零的 $\begin{pmatrix}0&-ka\tau/2\\ka\tau/2&0\end{pmatrix}$。间隙为

$$
\gamma(\tau)^2=
(\sqrt{1+a\tau}-\sqrt{1-a\tau})^2
+(\sqrt{1+b\tau}-\sqrt{1-b\tau})^2\longrightarrow0.
$$

仍用实际 $P_0,P_1$ 仪器，实际 $G=0$。这次使用合法常值共同解码器 $Y\mapsto\operatorname{Tr}(Y)\rho_0(k)$。对 $s\in\{a\tau,b\tau\}$，差的半迹范数精确为

$$
\frac12\|\rho_s(k)-\rho_0(k)\|_1
=\frac12\sqrt{s^2+k^2(1-\sqrt{1-s^2})^2}.
\tag{10.3}
$$

证明此式只需将迹零二阶 Hermitian 差矩阵平方，得到对应标量倍恒等。又因
$1-\sqrt{1-s^2}=s^2/(1+\sqrt{1-s^2})\le s^2$，最大误差不超过
$\tfrac12\sqrt{b^2\tau^2+k^2b^4\tau^4}\to0$。因而在固定上述忠实性和固定 $h$、仅允许间隙闭合的类上，不存在统一正的零缺陷截距。

当 $\tau=0$，全部 $T_s=I_2$，不同元组合并成一个典范联合块，所有态相同；此时按定义 4.1 计算的 $h=0$。继续把两个坐标轴标作不同联合块，会人为保留一个已经不存在的元组区别，不符合定义。反例只反驳省去间隙条件的特定统一界，不反驳固定族定理。$\square$

**边界 10.3（重复、简并、零效应与奇异性）。** 族中允许重复态；重复成员使某些缺陷和传输分量重复，不影响证明。若所有态相同，命题 4.2 适用；有重复成员而仍有至少两个不同联合元组时，$\gamma,\Gamma,K_{\rm sp}$ 按完整元组定义即可。简并联合块不能为了套用一维图景而再拆分；平方差论证处理整个块，完全未假定概率向量独立。§8 的独立性只是排除 C 的特定关系证书，不是本主定理的假设。

零效应的实际 Kraus 全零，已在 §2 处理。忠实输入在每个非零效应上有正概率，但不提供与结果数无关的逐分支概率下界；定理 3.1 使用实际权重避免了这个要求。实际条件量子态、重建态和块比较态都可奇异；证明没有对它们求逆。奇异输入则不同：本文未给出其完整正传输分类。$\mu\downarrow0$、维数或族大小无界、联合元组合并时，这里的常数不提供额外统一结论；这不等于证明所有其他形式的定理都不可能。

## 11. 任务解释与保留的普适近似桥梁

**解释 11.1（面向机器学习的条件性研究路线）。** 若一个表示或学习模型能够明确对应到本文的输入族、实际观察、被保留的系统和共同可允许解码器，(3.3) 可以用来研究：选定根保真读数接近等号时，哪些族内条件区别仍被保留；(4.5) 则在额外相容性、间隙和非对易幅度条件下给出特定恢复任务的不可逆误差。相同的读数需要结合实际联合关系和解码能力解释，不能仅凭一个标量判断全部任务信息是否可恢复。

这只是一条需要核对对象映射的条件性研究建议。没有关于经验改进、全部神经网络、普遍白盒认证、训练效果或最优近似速率的结论。数学比较链存在也不等于可取得、可高效实施或具有某个资源成本的实际算法。

**定义 11.2（OPEN：原来的全输入、参考、协议与资源义务）。** 保留 E §10、S §10 和 C §5 的原问题接口。令 $H$ 为实际保留系统，$b:\mathbb C^3\to H$ 是指定等距嵌入，$\iota(X)=bXb^\dagger$。固定公平仪器在码上的一步限制为 $bQ_j/\sqrt2$，$Q_j$ 酉；已知时长 $n$，历史按时间顺序写为 $h=(h_1,\ldots,h_n)$，$Q_h=Q_{h_n}\cdots Q_{h_1}$，空词为恒等。对实际输入无关压缩核及完整视图 $y$，

$$
r_s(y\mid h)\ge0,\qquad\sum_y r_s(y\mid h)=1,
$$

允许协议的实际信道为

$$
\mathcal C(X)=\int 2^{-n}\sum_{h,y}r_s(y\mid h)
\mathcal D_{s,y}(bQ_hXQ_h^\dagger b^\dagger)\,d\nu(s).
\tag{11.1}
$$

$\mathcal D_{s,y}$ 是可测 CPTP 终端解码器，仍接收实际量子 $H$；$s$ 是显式免费且独立的共享种子，没有种子时取单点空间。每步新环境、固定交互和固定所选环境测量基，只有实际标签更新记录；没有中间量子反馈、自适应仪器、参考读取、保留环境、额外量子摘要、输入相关旁信息或成功后选择。完整被计数视图包括全部历史相关可见程序、控制选择、时钟变化、相关种子、存档和缓冲；丢弃的私有随机性在核内平均。非原子视图不能因为每个单点概率为零就算作有限字母表。

例如选定全输入和全部未触有限参考上的误差

$$
\operatorname{err}(\mathcal C)=
\sup_{\substack{Z\text{ 有限}\\
\xi\text{ 为 }\mathbb C^3\otimes Z\text{ 上密度矩阵}}}
\frac12\|((\mathcal C-\iota)\otimes\operatorname{id}_Z)(\xi)\|_1.
\tag{11.2}
$$

原义务仍是：对每一个符合这些权限、时长为 $n$、完整保留视图规模为 $W$ 且 $\operatorname{err}\le\epsilon$ 的实际协议，构造一个合法有限共同 POVM $E_{\mathcal C}$ 和明确实际态族 $\boldsymbol\eta_{\mathcal C}$，并证明

$$
0\le\Delta(\boldsymbol\eta_{\mathcal C})
\le G_{\boldsymbol\eta_{\mathcal C}}(E_{\mathcal C})
\le g(W,n,\epsilon).
\tag{11.3}
$$

须给出共同实现映射、全部常数及足以沿所需方向结合缺陷下界的资源依赖。本文没有构造这个 $g$，没有近似存储计数或近似寄存器下界。定理 3.1 提供的是指定态族上的加权比较，定理 4.3 还固定相容输入几何；两者都未把所有 (11.1) 映成满足 (11.3) 的共同测量。

为说明不能偷换实际输入类型，完整细标签的允许精确逆作用在任意 qutrit 及参考上为 $\iota\otimes\operatorname{id}$，而任意全输入经典测量制备映射在最大纠缠态的一半作用后都产生

$$
\frac13\sum_y\eta_y\otimes F_y^{\mathsf T},
$$

是正乘积算子之和，因而可分。目标纯态 $(b\otimes I)|\Omega_3\rangle$ 的 Schmidt 秩为三。故该精确全输入信道不能用纯经典因子化替换。这一论证不阻止 (3.3) 的有限族比较，却阻止把它擅自升级为全输入操作恒等式。

E 的精确忠实归一化代数迁移依赖 $\Lambda(\rho_0)=\rho_0$、归一化映射严格含幺、忠实不变泛函以及 Schwarz 等号；近似恢复不提供这些等号。本文没有近似含幺性、近似生成代数固定或任意参考近似迁移定理。类似地，精确种子平均的纯 Choi 论证不提供相同误差的逐种子近似结论：以概率 $1-\delta$ 使用允许的细标签精确逆，以概率 $\delta\in(0,1)$ 使用常值纯态制备，平均的全输入参考半迹误差恰为 $\delta$，而坏种子的误差为一。上界由态间半迹距离至多一得出，下界在与所制备纯态正交的码输入上达到。因此平均误差不能被换成几乎处处同误差。

分别最优的成对测量、独立边缘、优化替代仪器或删除实际量子输出均不完成 (11.3)。这些具体缺口也不证明所有未来协议敏感桥梁不可能。本文没有新的近似资源下界；已有精确记录事实仍只保留源接口的权限。记录值数、量子维数、取得标签、环境准备、通信、精度、控制合成和运行时间不是同一种资源，本文没有物理或总成本结论。

## 12. 来源、标准工具与证据边界

S 指《AURIC FIB common-measurement compatibility, defect and recovery separation》，固定内容 SHA256 为 `220c4122d70761d158e7683572e937e62b0487127c53d950fb850f47c51cdcfe`。其定义 1.2–1.3、定理 2.1、3.1 提供根保真、正传输残差、相容性与等号效应接口；§§7–10 提供实际协议权限及未决普适桥梁。

E 指《AURIC FIB：共同保真等号测量与保留量子输出的精确恢复》，固定内容 SHA256 为 `5dd69526923614ba73b45d7500e560811ad22816fafaef444211c2c832f3b5ae`。其定义 1.2、定理 3.1 与 §§8–10 提供实际完整联合输出、精确族恢复分类、忠实加权代数和种子边界。本文 §6 的精确极限与该分类衔接。

C 指《AURIC FIB：零保真缺陷下的严格正经典恢复间隙》，固定内容 SHA256 为 `d072e0b54577a2d44e107b43c006f190e4f2bfde690b4bc0dfee09e162271a7f`。本文 §9 精确复用其命题 1.3、定理 2.1 的三态、参数、$Q$ 和达到制备；其定理 3.1 仅用于比较非零块概率关系证书的适用范围，§8 的独立概率向量不满足该假设。

R 指结构化数学文本《Explicit actual-instrument recovery tradeoffs from fidelity residuals and robust joint-block stationarity》，其完整 JSON 内容 SHA256 为 `7621d7a2e05b0d5123567a787183dec77b371a7c436f078131f1e7ec6a564fa6`。本文的实际条件输出提升、Kraus 泄漏、稳健平方差、两类应用和统一性反例将其中的条件符号推导组织为自足伴卷。该来源身份不增加其数学证据强度。

原始文献归属按 S、E、C 的明确转述使用：Nuradha、Mishra、Leditzky、Wilde 的 *Multivariate Fidelities* 承担根保真测量表示和共同测量定义；Fuchs、Caves 的 *Mathematical Techniques for Quantum Communication Theory* 承担成对最优测量及效应本征空间条件；Gregoratti、Werner 的 *Quantum Lost and Found* 与 Knill、Laflamme 的 *A Theory of Quantum Error-Correcting Codes* 承担标准精确纠错接口。此处没有独立核对其链接、原文、版本或文献查全性。矩阵谱分解、矩形 Schatten 范数对偶、Kraus 表示、迹范数收缩、投影纯化估计、Cauchy–Schwarz、联合谱钳制和有限随机矩阵平方差都是标准工具，不附加发明权或世界优先权。

本文的结论仅在所列模型、假设、误差量词和共同实际实现下成立。一般族的精确 $Q$、正缺陷最优解码器、最优常数或指数、奇异输入的完整分类，以及 (11.3) 的普适操作和资源构造均未解决。来源引用、普通符号证明和可实施协议是不同证据对象；本文只承担前两者在已列边界内的条件数学陈述。

## 追加锚（本行以下为增补区）
