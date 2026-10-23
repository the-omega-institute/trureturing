# AURIC FIB：零缺陷三态经典恢复的最优实现分类与全信道刚性

## 1. 固定任务、父卷接口与新增结论

本文讨论一个固定三态、纯经典中间变量的恢复模型，给出所有最优有限实现的分类、对整个复矩阵代数的信道唯一性，以及显式的辅助系统一致稳定性界。这里的证明是尚未形式化、未执行数学计算核验的普通条件符号数学，不构成 Lean kernel 证书、实验结论或世界优先权认证。

[父卷《AURIC FIB：零保真缺陷下的严格正经典恢复间隙》][PARENT]的定理 2.1 及其证明已经给出精确极小极大值、根的唯一性、达到方案、通用可行约束和支撑仿射式。本文直接复用这些接口，不把它们列为新增成果。[源卷《AURIC FIB common-measurement compatibility, defect and recovery separation》][OWNER]给出共同测量相容性及保留量子系统的记录恢复接口。本文新增的推导是原始结果逐项的严格松弛分解、每一个最优实现的分类、显式全信道稳定性、排除更强指数的实际方案族，以及精确测试响应下的 CPTP 边界引理。引用均相对于这两卷给出的来源，不表示已认证其外部文献或链接。

**定义 1.1（态、有限经典实现与误差）。** 令 $M_2=M_2(\mathbb C)$，取

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\rho_s=\frac{I+s_xX+s_yY+s_zZ}{2}.
$$

$\rho_s$ 是密度矩阵当且仅当 $s\in\mathbb R^3$ 且 $|s|\le1$。固定

$$
\begin{gathered}
u=w=\frac12,\qquad v=\frac{\sqrt3}{4},\qquad
h=u-v=\frac{2-\sqrt3}{4}>0,\\
\sigma_0=\frac{I+uX}{2}
=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},\\
\sigma_+=\frac{I+vX+wZ}{2}
=\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix},\qquad
\sigma_-=\frac{I+vX-wZ}{2}
=\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix}.
\end{gathered}
\tag{1.1}
$$

三态严格正，其行列式依次为 $3/16,9/64,9/64$。考虑所有实际映射

$$
\Lambda(A)=\sum_{j=1}^m\operatorname{Tr}(E_jA)\omega_j,
\qquad E_j\succeq0,\quad \sum_jE_j=I,\quad
\omega_j\succeq0,\quad\operatorname{Tr}\omega_j=1,
\qquad 1\le m<\infty.
\tag{1.2}
$$

即一次有限 POVM 后接一个固定的经典到量子 CPTP 制备。任意上述密度矩阵族都允许：在经典基上测量并制备相应态即给出 CPTP 扩张。中间没有随行量子系统。量词涵盖任意有限结果数、零效应、混合效应、混合制备及任意 $y$ 分量。定义

$$
\varepsilon(\Lambda)=\max_{i\in\{0,+,-\}}
\frac12\|\Lambda(\sigma_i)-\sigma_i\|_1,
\qquad Q=\inf_{\Lambda\text{ 满足 }(1.2)}\varepsilon(\Lambda).
\tag{1.3}
$$

这里 $\|\cdot\|_1$ 是迹范数，$\|\cdot\|_{\mathrm{op}}$ 是算子范数。Bloch 差的两个特征值为 $\pm|s-r|/2$，所以

$$
\|\rho_s-\rho_r\|_1=|s-r|.
\tag{1.4}
$$

目标 (1.3) 因而是三个欧氏误差长度之最大值的一半，没有任意输入或参考系统的优化量词。

共同测量缺陷是另一对象。若 $F(\rho,\tau)=\|\sqrt\rho\sqrt\tau\|_1$，对三态共用一个有限 POVM $F_x$，置 $p_i(x)=\operatorname{Tr}(F_x\sigma_i)$，则

$$
\Delta=\inf_{(F_x)}\frac13\sum_{i<k}\sum_x\sqrt{p_i(x)p_k(x)}
-\frac13\sum_{i<k}F(\sigma_i,\sigma_k).
$$

源卷定理 6.1 与父卷命题 1.3 给出本三态 $\Delta=0$；这不把 (1.3) 的恢复误差变成零。

**约定 1.2（复用的精确根与支撑数据）。** 按父卷定理 2.1，$T$ 是区间 $(v,u)$ 内的唯一正根

$$
u-T=\sqrt{(T-v)^2+w^2\bigl(1-\sqrt{1-T^2}\bigr)^2}.
\tag{1.5}
$$

定义

$$
\begin{gathered}
C=\sqrt{1-T^2},\qquad E=u-T,\qquad D=T-v,\\
E,D>0,\quad E+D=h,\quad 0<T,C<1,\quad
T^2+C^2=1,\quad E^2=D^2+w^2(1-C)^2,\\
\beta=\frac{w^2(1-C)}C,\qquad L=h+\beta T,\qquad
\alpha=\frac{D+\beta T}{L},\qquad
\kappa=\frac\beta L,\qquad
\eta=uT+\frac{hD}{\beta}.
\end{gathered}
\tag{1.6}
$$

父卷的同一接口保证 $\beta,L,\kappa>0$、$1-\alpha=E/L$、$0<\alpha<1$ 及 $0<\eta<1$；特别是各分母严格为正。父卷还给出最小值及其严格正界

$$
Q=\frac E2,\qquad
0<\frac{4-\sqrt{13}}{16}<Q<\frac{2-\sqrt3}{8}.
\tag{1.7}
$$

记 $e\in\{+1,-1\}$，定义

$$
\begin{gathered}
P_e=\frac{I+eZ}{2},\qquad s^e=(T,0,eC),\qquad
\omega_e=\rho_{s^e},\qquad \rho_T=\frac{I+TX}{2},\\
\Lambda_\star(A)=\sum_{e=\pm1}\operatorname{Tr}(P_eA)\omega_e
=\operatorname{Tr}(A)\rho_T+\frac C2\operatorname{Tr}(ZA)Z,
\qquad A\in M_2.
\end{gathered}
\tag{1.8}
$$

这是全复代数上的复线性定义，其 Bloch 作用为 $(x,y,z)\mapsto(T,0,Cz)$。父卷已经证明它是实际达到方案，三个半迹误差全部为 $E/2$。$T^2+C^2=1$ 还说明两制备态是纯态。

为固定将被转移的父卷支撑式，写任意实际信道的实仿射 Bloch 作用为 $r\mapsto b+Ar$，并令

$$
t=b_x,\qquad a=A_{xx},\qquad c=A_{zz}.
$$

父卷证明中的通用约束为 $|a|+\sqrt{t^2+c^2}\le1$，对未经平均的实现也成立。对作用为 $(x,y,z)\mapsto(t+ax,b_y y,cz)$ 的信道，父卷的支撑接口是

$$
\begin{aligned}
R&=\max\left\{|t+ua-u|,
\sqrt{(t+va-v)^2+w^2(c-1)^2}\right\},\\
L_0&=u-ua-t,\\
L_1&=\frac{D(t+va-v)+w^2(1-C)(1-c)}E,\\
R&\ge\alpha L_0+(1-\alpha)L_1
=E+\kappa(1-\eta a-Tt-Cc).
\end{aligned}
\tag{1.9}
$$

本文使用该精确仿射式，不重新证明父卷的整个极小极大定理。

## 2. 原信道上的支撑与逐结果松弛

**引理 2.1（支撑式保留原系数）。** 对任意满足 (1.2) 的原信道，置

$$
g=1-\eta a-Tt-Cc.
\tag{2.1}
$$

则 $2\varepsilon(\Lambda)\ge E+\kappa g$，这里的 $a,t,c$ 始终是原信道的系数。

证明。考虑两个信道变换

$$
\Lambda^{X}(A)=X\Lambda(XAX)X,\qquad
\Lambda^{K}(A)=\bigl[\Lambda(A^{\mathsf T})\bigr]^{\mathsf T}.
$$

它们分别由实际效应、制备对 $(XE_jX,X\omega_jX)$ 及 $(E_j^{\mathsf T},\omega_j^{\mathsf T})$ 实现，故仍属 (1.2)。第二个公式使用 $\operatorname{Tr}(E_jA^{\mathsf T})=\operatorname{Tr}(E_j^{\mathsf T}A)$，没有将单独的转置当作 CP 操作。$X$ 共轭固定 $\sigma_0$ 并交换 $\sigma_\pm$；转置固定三个态。两种操作均保持迹范数，故各自保持 $\varepsilon$。由于 $X$ 为实矩阵，两变换对易。

把恒等变换及这两变换生成的四个像等权平均。把各像的所有效应乘 $1/4$，保留对应制备并将群标记并入结果，就得到一个有限实现 $\overline\Lambda$。迹范数的凸性给出 $\varepsilon(\overline\Lambda)\le\varepsilon(\Lambda)$。两种 Bloch 符号矩阵为

$$
S_X=\operatorname{diag}(1,-1,-1),\qquad
S_K=\operatorname{diag}(1,-1,1).
$$

它们作用为 $b\mapsto S b$、$A\mapsto SAS$，所以均保留原来的 $b_x,A_{xx},A_{zz}$。三个坐标的联合符号不同，平均会消去交叉系数及其余平移，留下 $(t+ax,b_y y,cz)$。因此 (1.9) 中的 $R$ 正是 $2\varepsilon(\overline\Lambda)$，且仍使用原 $t,a,c$。代入 (1.9) 即得

$$
2\varepsilon(\Lambda)\ge2\varepsilon(\overline\Lambda)
\ge E+\kappa g.
$$

这是支撑泛函的转移，不是从平均信道唯一性反推原信道唯一性。$\square$

**引理 2.2（任意原实现的非负松弛与严格控制）。** 对任意一个实际有限实现，先删去零效应，再唯一写成

$$
\begin{gathered}
E_j=q_j(I+m_j\cdot(X,Y,Z)),\qquad
q_j>0,\quad |m_j|\le1,\quad
\sum_jq_j=1,\quad\sum_jq_jm_j=0,\\
\omega_j=\rho_{s_j},\qquad |s_j|\le1.
\end{gathered}
\tag{2.2}
$$

令

$$
\begin{gathered}
k_j=1+\eta Tm_{j,x},\qquad
p_j=(T+\eta m_{j,x},0,Cm_{j,z}),\qquad
d_j=k_j-s_j\cdot p_j,\\
k_0=1-\eta T>0,\qquad K=1+\eta T,\qquad
A_0=\frac{C^2(1-\eta^2)}{2K}>0.
\end{gathered}
\tag{2.3}
$$

则对每一个非零结果及整个原实现都有

$$
\begin{gathered}
k_0\le k_j\le K,\qquad d_j\ge0,\qquad
\sum_jq_jd_j=g,\\
d_j\ge A_0(1-m_{j,z}^2),\qquad
\left|s_j-\frac{p_j}{k_j}\right|^2\le\frac{2d_j}{k_0}.
\end{gathered}
\tag{2.4}
$$

因而，若 $\xi=\varepsilon(\Lambda)-Q$ 是实际半迹超额，则

$$
0\le g\le\frac{2\xi}{\kappa}.
\tag{2.5}
$$

证明。对任意输入 Bloch 向量 $r$，结果概率为 $q_j(1+m_j\cdot r)$。于是原系数满足

$$
t=\sum_jq_js_{j,x},\qquad
a=\sum_jq_js_{j,x}m_{j,x},\qquad
c=\sum_jq_js_{j,z}m_{j,z}.
\tag{2.6}
$$

这里只是展开同一个原实现，不需要它具有任何对称性。由 $0<\eta,T<1$ 得 $k_j\in[k_0,K]$。用 $T^2+C^2=1$ 展开平方差，得到

$$
\begin{aligned}
k_j^2-|p_j|^2
&=C^2(1-m_{j,z}^2-\eta^2m_{j,x}^2)\\
&\ge C^2(1-\eta^2)(1-m_{j,z}^2)\ge0.
\end{aligned}
\tag{2.7}
$$

第二行只用了 $m_{j,x}^2\le1-m_{j,z}^2$；原来的 $y$ 分量仍被完整 Bloch 球约束涵盖。$k_j>0$ 保证 $|p_j|\le k_j$，于是 $|s_j|\le1$ 给出 $d_j\ge k_j-|p_j|\ge0$。求和时，$\sum_jq_jm_{j,x}=0$ 消去 $k_j$ 中的线性项，而 (2.6) 给出

$$
\sum_jq_jd_j=1-Tt-\eta a-Cc=g.
\tag{2.8}
$$

分母 $k_j+|p_j|$ 至少为 $k_0$，至多为 $2K$，故差平方恒等式与 (2.7) 推出

$$
d_j\ge k_j-|p_j|
=\frac{k_j^2-|p_j|^2}{k_j+|p_j|}
\ge A_0(1-m_{j,z}^2).
$$

另一方面，$|p_j/k_j|\le1$，所以

$$
\begin{aligned}
\left|s_j-\frac{p_j}{k_j}\right|^2
&=|s_j|^2+\left|\frac{p_j}{k_j}\right|^2
-\frac{2s_j\cdot p_j}{k_j}\\
&\le2-\frac{2s_j\cdot p_j}{k_j}
=\frac{2d_j}{k_j}\le\frac{2d_j}{k_0}.
\end{aligned}
$$

即使 $p_j=0$，所有分母仍严格为正，无须除以 $|p_j|$；混合制备、非秩一效应和任意 $y$ 分量均被这些不等式覆盖。删去零效应只是避免对它定义归一化 Bloch 向量，零效应的任意制备不贡献任何项。

最后 (2.8) 给出 $g\ge0$，引理 2.1 与 $2Q=E$ 给出 $\kappa g\le2\varepsilon-E=2\xi$，即 (2.5)。这些等式与界均使用同一个实际实现。$\square$

## 3. 全复信道唯一性与每一个有限最优实现

**定理 3.1（所有最优实现的充要分类）。** 对 (1.2) 中的任意实际信道，以下条件等价：其误差等于 $Q$；它在全部 $M_2(\mathbb C)$ 上等于 $\Lambda_\star$；它的每一个有限实现删去零效应后，均有两个非空符号类 $J_+,J_-$，并满足

$$
E_j=\lambda_jP_e,\qquad \omega_j=\omega_e
\quad(j\in J_e),\qquad
\lambda_j>0,\qquad \sum_{j\in J_e}\lambda_j=1
\quad(e=+1,-1).
\tag{3.1}
$$

特别地，分类包括未经测试的 $Y$ 方向：最优信道必有

$$
\Lambda(I)=I+TX,\qquad \Lambda(X)=0,\qquad
\Lambda(Y)=0,\qquad \Lambda(Z)=CZ.
\tag{3.2}
$$

证明。先取任意一个最优信道的任意有限实现。由 (2.5)，$g=0$。式 (2.8) 是有限个非负数的正权和，故每个非零结果都有 $d_j=0$。$A_0>0$ 与 (2.4) 强制 $m_{j,z}^2=1$；再由 $|m_j|\le1$，得 $m_{j,x}=m_{j,y}=0$。令 $e=m_{j,z}\in\{+1,-1\}$，此时

$$
k_j=1,\qquad p_j=(T,0,eC),\qquad |p_j|=1.
$$

制备控制式 (2.4) 又强制 $s_j=p_j$。因此 $E_j=2q_jP_e$，而 $\omega_j$ 恰是纯态 $\omega_e$。归一性与 $z$ 分量的完备性给出

$$
\sum_{j\in J_+}q_j+\sum_{j\in J_-}q_j=1,\qquad
\sum_{j\in J_+}q_j-\sum_{j\in J_-}q_j=0.
$$

所以两类的 $q$ 总权重都为 $1/2$，两类均非空；取 $\lambda_j=2q_j$ 即得 (3.1)。逐类求和，对每一个复矩阵 $A$ 均有

$$
\Lambda(A)=\sum_{e=\pm1}\left(\sum_{j\in J_e}\lambda_j\right)
\operatorname{Tr}(P_eA)\omega_e=\Lambda_\star(A).
$$

因此并非仅在三个测试输入或实对称子空间上相等，(3.2) 也随之成立。

反过来，任意具有 (3.1) 形状的效应正且和为 $I$，按符号合并后给出的映射就是 (1.8)，从而误差等于父卷已给出的 $Q$。若某个任意实现表示 $\Lambda_\star$，它的实际误差同样为 $Q$，上述必要性便适用于这个实现本身。这样得到每一个实现的量词，而非仅找到一种方便的最优表示。$\square$

**推论 3.2（允许的实现冗余）。** 非零结果只能在同一符号内任意正权拆分或逆向合并，可以重标记，也可插入附带任意制备的零效应。除这些操作及相同纯态的平凡制备随机化外，没有其他活跃的经典测量制备自由度。

证明。式 (3.1) 的每个符号权重只要求总和为一，故所列拆分、合并与重标记均保留实际映射。零效应不贡献映射。跨符号的正结果不能合并为另一个最优实现的一个活跃结果，否则该结果违反定理 3.1 的必要形状；非零秩二效应、错配制备或混合活跃制备同样被排除。

若一个活跃制备被表示为密度矩阵的凸组合且平均为 $\omega_e=|\psi_e\rangle\langle\psi_e|$，取与 $\psi_e$ 正交的单位向量 $\phi$，其平均期望为零。各项 $\langle\phi|\rho|\phi\rangle$ 非负，所以每个正权项的该期望为零。正性意味着 $\sqrt\rho\,\phi=0$，故该密度矩阵的支撑在 $\mathbb C\psi_e$ 中；迹为一又使它等于 $\omega_e$。对制备随机化的概率积分，同一非负积分论证给出几乎处处相同的结论。$\square$

这里的唯一性是指定实际输入输出映射的唯一性与 (1.2) 内活跃表示的分类。结果标签数仍可任意有限拆分，制备在从未取得的零效应标签上的行为不被测得；这些都不等于任意网络内部参数唯一。若另行赋予制备整个量子标签代数上的扩张，那是额外接口，其未用数据不在本分类的断言内。

## 4. 精确测试响应的 CPTP 边界

**引理 4.1（三个基准响应强制整个 CPTP 映射）。** 若任意复线性 CPTP 映射 $\Gamma:M_2\to M_2$ 满足

$$
\Gamma(\sigma_i)=\Lambda_\star(\sigma_i)
\qquad(i=0,+,-),
\tag{4.1}
$$

则 $\Gamma=\Lambda_\star$，即使不预设它具有经典中间变量。

证明。三个输入的实线性关系为

$$
\sigma_0-\frac{\sigma_++\sigma_-}{2}=\frac h2X,\qquad
\sigma_+-\sigma_-=wZ.
\tag{4.2}
$$

因 $h,w>0$，它们张成 $\operatorname{span}_{\mathbb R}\{I,X,Z\}$。条件 (4.1) 与 (1.8) 因而给出

$$
\Gamma(X)=0,\qquad \Gamma(Z)=CZ,\qquad \Gamma(I)=I+TX.
\tag{4.3}
$$

这些线性关系本身没有指定 $Y$。但 (4.3) 还给出 $\Gamma(P_e)=\omega_e$，是两个纯输出。取归一向量 $\psi_e$ 表示 $\omega_e$。其重叠满足

$$
|\langle\psi_+|\psi_-\rangle|^2
=\operatorname{Tr}(\omega_+\omega_-)
=\frac{1+T^2-C^2}{2}=T^2>0.
\tag{4.4}
$$

取 Kraus 表示 $\Gamma(A)=\sum_\ell K_\ell A K_\ell^\dagger$。纯输出意味着每一列都在相应纯态支撑内：若 $\phi\perp\psi_e$，则

$$
0=\langle\phi|\Gamma(P_e)|\phi\rangle
=\sum_\ell|\langle\phi|K_\ell|e_z\rangle|^2,
$$

故存在复数 $c_{\ell,e}$ 使 $K_\ell|e_z\rangle=c_{\ell,e}\psi_e$。保迹的非对角矩阵元为

$$
0=\langle+_z|\sum_\ell K_\ell^\dagger K_\ell|-_z\rangle
=\langle\psi_+|\psi_-\rangle S,\qquad
S=\sum_\ell\overline{c_{\ell,+}}c_{\ell,-}.
\tag{4.5}
$$

由 (4.4) 得 $S=0$。需要明确区分保迹系数与映像系数：后者是前者的复共轭，具体为

$$
\begin{aligned}
\Gamma(|+_z\rangle\langle-_z|)
&=\left(\sum_\ell c_{\ell,+}\overline{c_{\ell,-}}\right)
|\psi_+\rangle\langle\psi_-|\\
&=\overline S\,|\psi_+\rangle\langle\psi_-|=0.
\end{aligned}
\tag{4.6}
$$

其伴随矩阵元也映为零，故 $\Gamma(Y)=0$。结合 (4.3) 及复线性，得到整个 $M_2$ 上的等式。$\square$

这个引理从精确基准响应出发。它没有给出任意 CPTP 信道的正恢复误差：恒等信道本身就是 CPTP，并以零误差保持三个测试态，所以扩大到全部 CPTP 后极小极大值为零。正值 $Q$ 与最优响应的确定依赖经典中间变量限制；纯输出的 CP、TP 边界是在已确定响应后补全 $Y$ 的另一条论证。

## 5. 显式且与结果数无关的全信道稳定性

本节的 diamond 范数不除以二。对任意复线性映射 $\Phi$，定义

$$
\|\Phi\|_\diamond
=\sup_{k\ge1}\ \sup_{0\ne W\in M_2\otimes M_k}
\frac{\|(\Phi\otimes\operatorname{id}_k)(W)\|_1}{\|W\|_1}.
\tag{5.1}
$$

$W$ 可以是任意复矩阵，不限于态或 Hermitian 矩阵。该范数用于比较实际信道和基准信道，并不改变 (1.3) 的半迹目标。

**引理 5.1（秩一线性映射的辅助范数）。** 若 $H=H^\dagger$、$B$ 为任意输出矩阵，则

$$
\Phi_{H,B}(A)=\operatorname{Tr}(HA)B
\quad\Longrightarrow\quad
\|\Phi_{H,B}\|_\diamond=\|H\|_{\mathrm{op}}\|B\|_1.
\tag{5.2}
$$

证明。对任意辅助维数与任意复矩阵 $W$，置 $R_W=\operatorname{Tr}_{\rm in}[(H\otimes I)W]$。放大后的输出是 $B\otimes R_W$，至多相差一个固定的张量顺序变换。迹范数对偶性给出

$$
\begin{aligned}
\|R_W\|_1
&=\sup_{\|U\|_{\mathrm{op}}\le1}
\left|\operatorname{Tr}(U^\dagger R_W)\right|\\
&=\sup_{\|U\|_{\mathrm{op}}\le1}
\left|\operatorname{Tr}[(H\otimes U^\dagger)W]\right|\\
&\le\|H\|_{\mathrm{op}}\|W\|_1.
\end{aligned}
$$

张量积迹范数的乘法性证明不等号方向的上界。选取 $H$ 中绝对值最大的特征值对应单位特征向量，以其秩一投影为输入，取一维辅助系统，即达到反向界。$H=0$ 或 $B=0$ 时两边同为零。这证明 (5.2)，没有对辅助输入作正性限制。$\square$

**定理 5.2（显式稳健全信道刚性）。** 使用 (1.6)、(2.3) 的固定正常数，并定义

$$
B_0=\frac{C(1+\eta)}{k_0},\qquad
C_1=2\sqrt{\frac2{k_0}}+\frac{2B_0+\sqrt2}{\sqrt{A_0}},\qquad
C_2=\frac{1+C}{A_0}.
\tag{5.3}
$$

这些常数有限、严格正，且不依赖实际有限结果数。对每一个 (1.2) 中的实际信道，若 $\xi=\varepsilon(\Lambda)-Q$，则

$$
\|\Lambda-\Lambda_\star\|_\diamond
\le C_1\sqrt{\frac{2\xi}{\kappa}}
+C_2\frac{2\xi}{\kappa}.
\tag{5.4}
$$

此式对所有实际超额都成立，其自然范围是 $0\le\xi\le1-Q$；如果仅给定 $\varepsilon(\Lambda)\le Q+\xi$、$\xi\ge0$，同一式也成立。特别地，在 $0\le\xi\le\kappa/2$ 时，

$$
\|\Lambda-\Lambda_\star\|_\diamond
\le(C_1+C_2)\sqrt{\frac2\kappa}\sqrt\xi.
\tag{5.5}
$$

对实际超额，该小范围可与 $[0,1-Q]$ 取交。这里不宣称常数最优。

证明。固定一个任意实际实现，并使用引理 2.2 的原始坐标。对每个非零结果，把 $m_{j,z}$ 舍入为符号

$$
e_j=\begin{cases}+1,&m_{j,z}\ge0,\\-1,&m_{j,z}<0,\end{cases}
\qquad n^e=(0,0,e),\qquad s^e=(T,0,eC),\qquad
V_z=\sum_jq_j(1-m_{j,z}^2).
\tag{5.6}
$$

零处的符号约定已固定，不引入分母。由 (2.4)、(2.8)，$V_z\le g/A_0$。效应向量的距离满足

$$
\begin{aligned}
|m_j-n^{e_j}|^2
&=|m_j|^2+1-2|m_{j,z}|\\
&\le2(1-|m_{j,z}|)\le2(1-m_{j,z}^2).
\end{aligned}
$$

以 $\sum_jq_j=1$ 作加权 Cauchy–Schwarz，得到

$$
\sum_jq_j|m_j-n^{e_j}|\le\sqrt{2V_z}
\le\sqrt{\frac2{A_0}}\sqrt g.
\tag{5.7}
$$

接着控制整个制备向量。暂略下标，写 $x=m_x,z=m_z,k=k_j,p=p_j,e=e_j$。精确恒等式为

$$
\frac pk-s^e
=\frac{\eta x}{k}(C^2,0,-eCT)
+\frac1k(0,0,C(z-e)).
\tag{5.8}
$$

第一个向量的长度是 $\eta C|x|/k$，第二个的长度是 $C(1-|z|)/k$，因为 $T^2+C^2=1$ 且 $|z-e|=1-|z|$，包括所定的零处符号。由 $|x|\le\sqrt{1-z^2}$、$1-|z|\le\sqrt{1-z^2}$ 及 $k\ge k_0$，

$$
\left|\frac pk-s^e\right|\le B_0\sqrt{1-z^2}.
$$

加上 (2.4) 的制备松弛界，再分别对 $d_j$ 与 $1-m_{j,z}^2$ 作加权 Cauchy–Schwarz，便有

$$
\begin{aligned}
\sum_jq_j|s_j-s^{e_j}|
&\le\sqrt{\frac2{k_0}}\sqrt{\sum_jq_jd_j}
+B_0\sqrt{V_z}\\
&\le\left(\sqrt{\frac2{k_0}}+\frac{B_0}{\sqrt{A_0}}\right)\sqrt g.
\end{aligned}
\tag{5.9}
$$

这一步同时控制任意制备的 $y$ 分量和混合性，没有先将它们投影消去。

舍入后的符号权重不一定平衡。令 $b_0=\sum_jq_je_j$；其两类总权重为 $(1+b_0)/2$、$(1-b_0)/2$。原 POVM 的完备性保证 $\sum_jq_jm_{j,z}=0$，所以

$$
|b_0|=\left|\sum_jq_j(e_j-m_{j,z})\right|
\le\sum_jq_j(1-|m_{j,z}|)\le V_z\le\frac g{A_0}.
\tag{5.10}
$$

定义线性比较映射

$$
\Psi(A)=\sum_jq_j\operatorname{Tr}[(I+e_jZ)A]\rho_{s^{e_j}}.
\tag{5.11}
$$

其效应和为 $I+b_0Z$，故不保证保迹；这里不将 $\Psi$ 称为信道，也不对它使用信道收缩性。逐项作恒等拆分，

$$
\begin{aligned}
(\Lambda-\Psi)(A)
=\sum_jq_j\bigl\{&\operatorname{Tr}[(I+m_j\cdot(X,Y,Z))A]
(\rho_{s_j}-\rho_{s^{e_j}})\\
&+\operatorname{Tr}[((m_j-n^{e_j})\cdot(X,Y,Z))A]
\rho_{s^{e_j}}\bigr\}.
\end{aligned}
\tag{5.12}
$$

由 (5.2)、(1.4) 及

$$
\|I+m_j\cdot(X,Y,Z)\|_{\mathrm{op}}=1+|m_j|\le2,\qquad
\|(m_j-n^{e_j})\cdot(X,Y,Z)\|_{\mathrm{op}}=|m_j-n^{e_j}|,
$$

每一项都有完整辅助系统上的范数控制。结合 (5.7)、(5.9)，

$$
\begin{aligned}
\|\Lambda-\Psi\|_\diamond
&\le2\sum_jq_j|s_j-s^{e_j}|+\sum_jq_j|m_j-n^{e_j}|\\
&\le\left[2\sqrt{\frac2{k_0}}
+\frac{2B_0+\sqrt2}{\sqrt{A_0}}\right]\sqrt g
=C_1\sqrt g.
\end{aligned}
\tag{5.13}
$$

再用 $\rho_{s^e}=\rho_T+eCZ/2$ 展开 (5.11)，得到完整的失衡修正

$$
\Psi(A)-\Lambda_\star(A)
=b_0\left[\rho_T\operatorname{Tr}(ZA)
+\frac C2Z\operatorname{Tr}(A)\right].
\tag{5.14}
$$

因 $\|\rho_T\|_1=1$、$\|Z\|_{\mathrm{op}}=\|I\|_{\mathrm{op}}=1$、$\|CZ/2\|_1=C$，再次应用 (5.2) 与 (5.10)，

$$
\|\Psi-\Lambda_\star\|_\diamond
\le(1+C)|b_0|\le C_2g.
\tag{5.15}
$$

三角不等式合成出 $\|\Lambda-\Lambda_\star\|_\diamond\le C_1\sqrt g+C_2g$；再用 (2.5) 的原信道超额控制，就得 (5.4)。若 $2\xi/\kappa\le1$，则 $2\xi/\kappa\le\sqrt{2\xi/\kappa}$，故得 (5.5)。当 $\varepsilon\le Q+\xi$ 时，(2.5) 的证明直接给出同样的 $g$ 上界，因此结论仍成立。

所有坐标、松弛、符号与失衡均来自同一个实际实现；没有把近最优实现替换成两结果实现，没有组合分别最优的边缘。结果数因子由归一化加权不等式吸收，而非通过限制结果数消失。所有 diamond 范数均未减半；从 (1.3) 来的半迹约定只在 $2\xi/\kappa$ 中出现。$\square$

## 6. 实际旋转族与平方根指数的必要性

**定理 6.1（排除一切大于二分之一的统一指数）。** 保持两个实际效应 $P_+,P_-$，对任意实数 $\theta$ 制备纯态

$$
s_\theta^e=(T\cos\theta,T\sin\theta,eC),\qquad
\omega_{\theta,e}=\rho_{s_\theta^e}.
\tag{6.1}
$$

其信道 $\Lambda_\theta$ 满足：若 $\xi_\theta=\varepsilon(\Lambda_\theta)-Q$、$d_\theta=\|\Lambda_\theta-\Lambda_\star\|_\diamond$，则

$$
\begin{gathered}
\xi_\theta=\frac{\sqrt{E^2+2uT(1-\cos\theta)}-E}{2},\\
d_\theta=2T|\sin(\theta/2)|,\qquad
d_\theta^2=\frac{4T}{u}\xi_\theta(E+\xi_\theta).
\end{gathered}
\tag{6.2}
$$

因此任何 $p>1/2$ 都不存在有限常数在所有充分小的实际超额上统一给出 $\|\Lambda-\Lambda_\star\|_\diamond\le K_{\rm rate}\xi^p$。结合定理 5.2，平方根指数在这个固定类中最优，但未确定最佳前因子或精确最坏刚性模量。

证明。向量 (6.1) 的长度平方是 $T^2+C^2=1$，所以每个 $\theta$ 都给出实际两结果、纯制备的 (1.2) 型 CPTP 映射。其 Bloch 作用是

$$
(x,y,z)\longmapsto(T\cos\theta,T\sin\theta,Cz).
$$

这也可视为对基准输出作 $e^{-i\theta Z/2}$ 酉共轭。三个测试的全部半迹误差为

$$
\begin{aligned}
\frac12\|\Lambda_\theta(\sigma_0)-\sigma_0\|_1
&=\frac12\sqrt{(T\cos\theta-u)^2+T^2\sin^2\theta}
=\frac12\sqrt{E^2+2uT(1-\cos\theta)},\\
\frac12\|\Lambda_\theta(\sigma_+)-\sigma_+\|_1
&=\frac12\sqrt{(T\cos\theta-v)^2+T^2\sin^2\theta+w^2(C-1)^2}
=\frac12\sqrt{E^2+2vT(1-\cos\theta)},\\
\frac12\|\Lambda_\theta(\sigma_-)-\sigma_-\|_1
&=\frac12\sqrt{E^2+2vT(1-\cos\theta)}.
\end{aligned}
\tag{6.3}
$$

因为 $u>v>0$ 且 $1-\cos\theta\ge0$，第一行给出最大值。这证明超额公式；在 $0<|\theta|<2\pi$ 时超额严格正，且 $\theta\to0$ 时趋于零。

整个复线性信道差恰是替换映射

$$
(\Lambda_\theta-\Lambda_\star)(A)=\operatorname{Tr}(A)B_\theta,
\qquad
B_\theta=\frac T2[(\cos\theta-1)X+\sin\theta Y].
$$

引理 5.1 以 $H=I$ 给出精确的全辅助范数

$$
d_\theta=\|B_\theta\|_1
=T\sqrt{2(1-\cos\theta)}=2T|\sin(\theta/2)|.
\tag{6.4}
$$

对超额等式中的 $E+2\xi_\theta$ 平方，得到

$$
4\xi_\theta(E+\xi_\theta)=2uT(1-\cos\theta).
$$

结合 $d_\theta^2=2T^2(1-\cos\theta)$ 即得 (6.2) 的精确恒等式。对小的非零 $\theta$，

$$
\frac{d_\theta}{\sqrt{\xi_\theta}}
=2\sqrt{\frac Tu(E+\xi_\theta)}
\ge2\sqrt{\frac{TE}{u}}>0,
\qquad
\lim_{\theta\to0,\ \theta\ne0}\frac{d_\theta}{\sqrt{\xi_\theta}}
=2\sqrt{\frac{TE}{u}}.
\tag{6.5}
$$

若统一 $p>1/2$ 的界存在，就会有

$$
K_{\rm rate}\ge\frac{d_\theta}{\xi_\theta^p}
\ge2\sqrt{\frac{TE}{u}}\,\xi_\theta^{1/2-p},
$$

但右侧随 $\theta\to0$ 发散，矛盾。该族反驳更强的统一率，不反驳零超额时的唯一性，也没有证明上界 (5.4) 的常数尖锐。$\square$

## 7. 操作边界、方法归属与条件性解释

本卷的全信道控制来自固定三态测试加上特定的测量制备限制。测试张成的只有 $I,X,Z$，而逐结果严格松弛或精确纯输出边界补上其余作用。diamond 结论控制实际映射与 $\Lambda_\star$ 的差，包括任意有限辅助系统，却不把 $\Lambda_\star$ 改成恒等信道，也不把三态极小极大目标改成任意输入恢复。一般三态族、其他权重与损失、无限结果测量、一般或 Pauli 态族的共同测量保真最小值及其正缺陷最优实现、完整奇异态传输分类均不在本文的结论内。最佳稳定常数与精确刚性模量仍未确定。

源卷 §§7–10 的终端解码器收到实际量子系统 $H=\mathbb C^5$ 和保留记录，目标是嵌入 $B:\mathbb C^3\to H$ 的所有 qutrit 输入及其未触参考。其实际细标签联合映射为

$$
\mathcal J_n(A)=2^{-n}\sum_h|h\rangle\langle h|\otimes BQ_hAQ_h^\dagger B^\dagger,
$$

源卷定理 8.1 已给出其全输出 CPTP 字面左逆。标签边缘单独可以无输入信息，量子系统与标签的联合输出仍能精确恢复。与之相对，任何 (1.2) 型纯经典中间映射作用在最大纠缠态的一半后，得到正乘积算子之和，故是可分态，不能实现嵌入的 qutrit 恒等映射。这是接口差异，不能通过丢弃实际保留的量子系统来套用本卷的 $Q$ 或稳定性界。

源卷定义 10.3 的普适协议敏感桥梁仍为 **OPEN**。它要求从每一个实际压缩核、量子终端解码器及独立种子积分的协议，构造一个共同实际 POVM 与态族，在固定全部输入和参考上的近似误差定义下，证明

$$
0\le\Delta(\boldsymbol\eta_{\mathcal C})
\le G_{\boldsymbol\eta_{\mathcal C}}(E_{\mathcal C})
\le f(W,n,\varepsilon).
$$

其中 $G$ 是该态族所有态对的共同测量根保真缺陷平均，$W$ 是完整被计数的实际可见记录规模。该构造须保留仪器、时间顺序、实际量子解码输入、所有未触参考、相关可见信息的计数与独立种子积分，并给出有用方向的资源依赖及全部常数。本卷未给出此构造，也未给出近似保留记录下界。积分信道的小误差不自动成为几乎处处同样的种子条件误差。相同标签边缘、相同平均信道、一个共同保真标量或这里的经典恢复刚性都不能替代该联合义务；这些限制也没有证明所有未来桥梁不可能。

方法归属上，Bloch 与 Pauli 表示、有限凸对称平均、Cauchy–Schwarz、全局支撑泛函、迹范数对偶与纯输出 Kraus 列论证均为标准工具。源卷对根保真及共同测量保真接口的归属为 Nuradha、Mishra、Leditzky、Wilde，对成对最优测量接口的归属为 Fuchs–Caves，对记录纠正相关接口的归属包括 Gregoratti–Werner、Knill–Laflamme 及其所引 REC。这里保留这些源相对归属，不认证外部来源，不声称文献搜索完备或取得世界优先权。新增成果的范围是上述固定接口内的综合推导。

达到方案与指数障碍族各使用两个数学测量结果及两个纯制备态。最优表示可作任意有限符号内拆分；近最优界的常数与有限结果数无关。这里没有运行时间、数值精度、获取、存储、通信、校准、控制合成、物理实现、训练或总成本的测量与界。

若一个学习或压缩模型具有经证明忠实的对象、测试、损失与解码器类别对应，那么本例提供一种条件性判断：近最佳测试分数可以约束整个实际行为，前提是已经证明该类别的全信道刚性；内部表示的讨论还须保留定理 3.1 的拆分与重标记冗余。本文不把这种条件性解释变成神经网络泛化、训练成功、经验改善、任意架构参数唯一性或物理真实性的结论。

[PARENT]: https://github.com/the-omega-institute/trureturing/blob/d9d94b8ea2cb8b0f9d5eb541e3f6ab36a657ae04/docs/develop/theory/AURIC_FIB_ZERO_DEFECT_CLASSICAL_RECOVERY_GAP.md
[OWNER]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_COMMON_MEASUREMENT_COMPATIBILITY.md

## 追加锚（本行以下为增补区）
