# AURIC 相容预测波与关系谱 V：同一原生历史的正实现与实记忆

## 54. 全复相容集合与精确预测实现

**定义 54.1（原对象及忠实相容集合）。** 本卷沿用[第一卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) §17.1、§35 和[第二卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_II.md) §§39–42 的对象。物理空间为 $H=\mathbb C^5$，正交基为 $(e_0,\ldots,e_4)$，并置

$$
\begin{gathered}
u_H=(e_0+e_3)/\sqrt2,\quad v_H=(e_1+e_4)/\sqrt2,\quad z_H=e_2,
\qquad B=(u_H,v_H,z_H),\\
K_0=u_He_0^\dagger+v_He_2^\dagger/\sqrt2+z_He_4^\dagger,
\quad K_1=u_He_1^\dagger+v_He_2^\dagger/\sqrt2+z_He_3^\dagger,\\
U=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad P_+=(I_3+W)/2,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\quad f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
q=(\xi+e)/\sqrt2,\quad r=(\xi-e)/\sqrt2,\quad E=qq^\dagger,\quad P=BEB^\dagger,\\
(a,h_{\rm out},g)=(Uq,Ur,Uf),\quad
C=(a+h_{\rm out})(a+h_{\rm out})^\dagger=2\xi\xi^\dagger,\\
\ell=(0,1,0)^{\mathsf T},\quad N=\ell^\perp,\quad
\tau=3-2\sqrt2,\quad c_\ell=(2+\sqrt2)/\sqrt{12},\quad
\ell=c_\ell(h_{\rm out}-\tau a).
\end{gathered}
\tag{54.1}
$$

固定 $0<d<1$，记 $\beta=1-d$、$e_d=(6-5d)/16$。本卷的初始集合是全部复正矩阵组成的原集合

$$
\begin{split}
\mathcal K_d=\{\rho=A+D:\;&A,D\succeq0,\quad D\ell=0,\quad
\operatorname{Tr}\rho=1,\\
&a^\dagger Aa=d,\quad\operatorname{Tr}(C\rho)=d,\quad
\operatorname{Tr}(E\rho)=e_d\}.
\end{split}
\tag{54.2}
$$

这里的 $A,D$ 仅为集合定义中的存在量词；不要求它们是可取得的制备分解。引用第一卷定理 35.4、35.6，(54.2) 等价于以下六实参数表示，基为 $(a,h_{\rm out},g)$：

$$
\rho=
\begin{pmatrix}
d+s&-(s+y)/2+\mathrm i v&(4s-3w+\mathrm i m)/\sqrt6\\
-(s+y)/2-\mathrm i v&y&(w+\mathrm i n)/\sqrt6\\
(4s-3w-\mathrm i m)/\sqrt6&(w-\mathrm i n)/\sqrt6&1-d-s-y
\end{pmatrix},
\tag{54.3}
$$

$$
\rho\succeq0,\qquad s\ge0,\qquad
v^2+\frac{[y+(1+2\tau)s]^2}{4}\le d(y-\tau^2s).
\tag{54.4}
$$

也可把最后一个条件写为

$$
B_d(\rho)=
\begin{pmatrix}d&a^\dagger\rho\ell\\\ell^\dagger\rho a&\ell^\dagger\rho\ell\end{pmatrix}\succeq0.
\tag{54.5}
$$

不将人口上界或实对称截面替代 (54.2)。原复通道纤维为第一卷 (35.1) 的 $\mathcal F_{\sqrt d}$；每个 $\rho\in\mathcal K_d$ 对应实际后继

$$
S_\rho(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho]B^\dagger
\tag{54.6}
$$

及至少一个 $T\in\mathcal F_{\sqrt d}$，使 $\mathcal GT=S_\rho$，其中 $\mathcal G(Y)=\sum_jK_jYK_j^\dagger$。这一路径保留原输入域、五维输出和不受限的 Kraus 秩。

**假设 54.2（一个固定角度的完整原生记录）。** 固定任意已知实数 $\theta$，实际分支为

$$
A_0=\cos\theta K_0+\mathrm i\sin\theta K_1,
\qquad A_1=\mathrm i\sin\theta K_0+\cos\theta K_1.
\tag{54.7}
$$

允许按第二卷假设 39.2 的合同重复这同一个仪器，保留所有标签，在预先给定的有限终点测 $(P,I_5-P)$。不在随机分支之间加入控制。记

$$
\begin{gathered}
V_0=U\exp(\mathrm i\theta W),\quad V_1=V_0W,\quad
h=(j_1,\ldots,j_n),\quad V_h=V_{j_n}\cdots V_{j_1},\\
M_h=V_h^\dagger EV_h,\qquad V_\varnothing=I_3,\\
p_\rho(h,1)=2^{-n}\operatorname{Tr}(\rho M_h),\qquad
p_\rho(h,0)=2^{-n}[1-\operatorname{Tr}(\rho M_h)].
\end{gathered}
\tag{54.8}
$$

最左标签最早作用。这些是原始联合概率，包括空词和两种终端结果；其和为 $2^{-n}$。第二卷定理 39.3 供应实际桥 $A_hB=2^{-n/2}BV_h$。所以 (54.8) 是在 $B\rho B^\dagger$ 上执行原仪器的记录，也是在原输入 $ff^\dagger$ 上先经过 $S_\rho$ 的记录。精确概率是比较的数学前提，不表示有限样本已经给出这些实数。

复 Hilbert 空间、Born 配对、CPTP 组合和所述环境就绪、测量及丢弃合同均处于前提侧。比较全部 $\rho$ 的实现，不授予实际制备整个 $\mathcal K_d$、新效果、独立副本、相位参考、环境访问、选支、逆或可调角度的权限。

**定义 54.3（经典正实现与实 CP 实现）。** 一个 $k$ 状态经典实现由固定矩阵 $T_0,T_1\in\mathbb R_+^{k\times k}$、固定列向量 $f_{\rm cl}\in[0,1]^k$ 和每个 $\rho$ 的概率列向量 $p(\rho)$ 组成，满足

$$
\mathbf1^{\mathsf T}(T_0+T_1)=\mathbf1^{\mathsf T},\qquad
\begin{cases}
f_{\rm cl}^{\mathsf T}T_hp(\rho)=p_\rho(h,1),\\
(\mathbf1-f_{\rm cl})^{\mathsf T}T_hp(\rho)=p_\rho(h,0).
\end{cases}
\tag{54.9}
$$

$T_h=T_{j_n}\cdots T_{j_1}$；每个分支非负且列次随机。默认不要求 $p(\rho)$ 仿射，允许不可达状态、不可观察状态、任意隐藏纤维及依赖隐藏状态的分支质量。最小状态数记 $k_{\min}(\theta,d)$，没有有限实现时记为 $\infty$。

一个实维数 $m$ 的实现由仿射映射 $\rho\mapsto\sigma(\rho)\in\operatorname{Sym}_m(\mathbb R)$、$\sigma(\rho)\succeq0$、$\operatorname{Tr}\sigma(\rho)=1$，固定效果 $0\preceq F\preceq I_m$，以及固定实 Kraus 分支

$$
\Phi_j(X)=\sum_\alpha L_{j\alpha}XL_{j\alpha}^{\mathsf T},\qquad
\sum_{j,\alpha}L_{j\alpha}^{\mathsf T}L_{j\alpha}=I_m
\tag{54.10}
$$

组成。要求 $\operatorname{Tr}(F\Phi_h(\sigma(\rho)))=p_\rho(h,1)$，补效果给 $p_\rho(h,0)$，对全部 $\rho\in\mathcal K_d$ 和全部有限词成立。仿射性作用于完整复凸集合；既不假设编码单射，也不预设分支为正交共轭。最小实维数记 $m_{\min}(\theta,d)$。

## 55. 所有角度的有限经典实现判据

**引理 55.1（原纤维内的严格双世界及其可见频率）。** 对每个 $0<d<1$，存在严格正的 $\rho_+,\rho_-\in\mathcal K_d$ 及其原域 CPTP 提升，使

$$
2^n[p_{\rho_+}(0^n,1)-p_{\rho_-}(0^n,1)]
=2t\,\Im(e^\dagger B_\zeta^ne),\qquad
B_\zeta=\begin{pmatrix}-1/2&\sqrt3\zeta/2\\\sqrt3/2&\zeta/2\end{pmatrix},
\quad\zeta=e^{-2\mathrm i\theta},
\tag{55.1}
$$

其中 $t>0$，$e$ 在右端表示 $(e,f)$ 子空间的第一个基向量。若 $\theta\notin(\pi/2)\mathbb Z$，右端的有限指数展开含有系数非零的、不是单位根的单位模频率。

证明。第二卷定理 42.4 已供应严格相容点

$$
\varepsilon=d(1-d)/100,\qquad
\rho_*=
\begin{pmatrix}
d+\varepsilon&-\varepsilon&4\varepsilon/\sqrt6\\
-\varepsilon&\varepsilon&0\\
4\varepsilon/\sqrt6&0&\beta-2\varepsilon
\end{pmatrix}_{(a,h_{\rm out},g)}.
\tag{55.2}
$$

它满足 $\rho_*\succ0$、$s=\varepsilon>0$、$B_d(\rho_*)\succ0$。置

$$
\Delta=\mathrm i(\xi e^\dagger-e\xi^\dagger),\qquad
t=\frac14\min\{\lambda_{\min}(\rho_*),\lambda_{\min}(B_d(\rho_*))\},
\qquad\rho_\pm=\rho_*\pm t\Delta.
\tag{55.3}
$$

所有约束向量为实，而 $\Delta$ 是纯虚 Hermitian 反对称矩阵。因此迹、$C,E$ 矩和 $aa$ 人口均不变。$\|\Delta\|=1$；$B_d$ 的变化只有非对角项，模至多 $t$，其对角项不变。两个正定条件均保留，故这是两个实际正世界。

原域提升可明确取自第一卷定理 35.4 的构造。对每个世界置

$$
\begin{gathered}
L=\ell^\dagger\rho\ell>0,\qquad
A_{\min}=\rho\ell\ell^\dagger\rho/L,\\
\alpha=\frac{d-a^\dagger A_{\min}a}{a^\dagger\rho a-a^\dagger A_{\min}a},\qquad
A=(1-\alpha)A_{\min}+\alpha\rho,\qquad D=\rho-A.
\end{gathered}
\tag{55.4}
$$

严格条件给 $0<\alpha<1$、$A,D\succeq0$、$D\ell=0$、$a^\dagger Aa=d$。原五维算子为

$$
\begin{gathered}
D_+=\frac1{\sqrt2}\begin{pmatrix}1&1&0&0&0\\0&0&\sqrt2&0&0\\0&0&0&1&1\end{pmatrix},\qquad
D_-=\frac1{\sqrt2}\begin{pmatrix}1&-1&0&0&0\\0&0&0&0&0\\0&0&0&-1&1\end{pmatrix},\\
\omega=D_+^\dagger AD_++D_-^\dagger DD_-,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\end{gathered}
\tag{55.5}
$$

$x\mapsto(D_+x,D_-x)$ 是 $H\to\mathbb C^3\oplus N$ 的酉识别，故 $\omega$ 为密度矩阵。若 $\omega=\sum_r\lambda_rw_rw_r^\dagger$，$T_\omega$ 的 Kraus 算子为 $BP_+$ 和 $\sqrt{\lambda_r}w_rf^\dagger$，其伴随平方和为 $I_3$。原 $P,J_1,J_2$ 的完整响应分别是第一卷 (35.3) 的 $Y_0,Y_1,Y_2$；其中 $ff$ 条目为 $d,e_d,(6+11d)/32$。原递推 $J_{j+2}=(J_j+J_{j+1})/2$ 对 $j\ge1$ 延续到所有深度。因此 (55.5) 属于原纤维，且 $\mathcal GT_\omega=S_\rho$，没有仅在某个输入上拟合矩。

在 $(\xi,e,f)$ 基中，去掉 $V_0$ 的公共标量相位后恰为 $1\oplus B_\zeta$，而 $E=(\xi+e)(\xi+e)^\dagger/2$。直接迹配对给

$$
\operatorname{Tr}\!\left[\Delta(1\oplus G)^\dagger E(1\oplus G)\right]
=\Im G_{11}
\tag{55.6}
$$

对任意二阶复矩阵 $G$ 成立。令 $G=B_\zeta^n$，得到 (55.1)。补终端结果的差为其负数。

下面确认频率在所有非例外角度都存在。$B_\zeta$ 酉，且

$$
\det B_\zeta=-\zeta,\qquad\operatorname{Tr}B_\zeta=(\zeta-1)/2.
\tag{55.7}
$$

若 $B_\zeta$ 有限阶，则两个本征值是单位根，所以 $\zeta$ 是单位根，$(\zeta-1)/2$ 是代数整数。设 $\zeta$ 的阶 $N>2$。它在 $\mathbb Q(\zeta)$ 中每个共轭 $(\zeta^a-1)/2$ 都非零且模严格小于一，因为原始 $N$ 次单位根既不是 $1$ 也不是 $-1$。它们的积应为非零整数，绝对值却小于一，矛盾。反之 $B_1^2=I_2$、$B_{-1}^3=I_2$。所以

$$
B_\zeta\text{ 有限阶}\quad\Longleftrightarrow\quad
\zeta\in\{1,-1\}\quad\Longleftrightarrow\quad\theta\in(\pi/2)\mathbb Z.
\tag{55.8}
$$

特别地，这个论证包含 $\theta/\pi$ 为有理数但非例外的情形。

$B_\zeta$ 是非标量正规矩阵，两个本征值 $\lambda_1,\lambda_2$ 不同。$e$ 不是本征向量，因为 $(B_\zeta)_{21}=\sqrt3/2$。其谱权重因而满足

$$
e^\dagger B_\zeta^ne=w_1\lambda_1^n+w_2\lambda_2^n,
\qquad w_1,w_2>0,\quad w_1+w_2=1.
\tag{55.9}
$$

非例外时至少一个 $\lambda_i$ 不是单位根。它不可能等于自身共轭；若与另一频率的共轭抵消，必须有 $\lambda_1\lambda_2=1$，即 $\zeta=-1$，也被排除。故其在虚部中的系数不为零。∎

**定理 55.2（C1：有限经典精确实现的充要角度）。** 对每个固定已知实角度 $\theta$ 和每个 $0<d<1$，在定义 54.3 的全部经典模型中，

$$
k_{\min}(\theta,d)<\infty\quad\Longleftrightarrow\quad
\theta\in(\pi/2)\mathbb Z.
\tag{55.10}
$$

非例外情形仅匹配引理 55.1 的两个世界就已不可能；这一下界不要求经典制备映射仿射。

证明。假设存在非例外角度的有限模型。置 $A=2T_0$，取双世界制备 $p_+,p_-$。由两个终端结果之和，对所有 $n,r\ge0$，

$$
\mathbf1^{\mathsf T}A^{n+r}p_\pm=1.
\tag{55.11}
$$

令 $S$ 为所有 $A^rp_\pm$ 的支持并集。非负性使 $S$ 向前不变。它是有限集合；从这些可达概率向量中取有限个，使其支持覆盖 $S$，再取严格正权凸组合 $\eta$。则 $\eta_j>0$ 对每个 $j\in S$ 成立，且

$$
\mathbf1^{\mathsf T}A^n\eta=1,\qquad
\sum_{i\in S}(A^n)_{ij}\le\eta_j^{-1}
\quad(n\ge0,j\in S).
\tag{55.12}
$$

因此 $A|_S$ 幂有界。质量恒为一还排除谱半径小于一，所以其谱半径为一。这个推导没有对各隐藏状态假设 $\mathbf1^{\mathsf T}T_0=\mathbf1^{\mathsf T}/2$；不可达的高增长块根本不参与。

对 $A|_S$ 作不可约对角块的上三角分解。每个单位模本征值来自 Perron 根为一的不可约块。以该块的严格正 Perron 向量作对角相似变换，得到不可约行随机矩阵。对其单位模本征向量，在最大模坐标的三角不等式中必须处处等号，沿每条正边的相位乘子固定为该本征值。沿长度 $l$ 的有向圈返回便给 $\lambda^l=1$。于是即使整体可约，每个外围本征值仍是单位根。

幂有界性排除外围非平凡 Jordan 块；内部 Jordan 项是衰减的多项式乘指数。因此

$$
f_{\rm cl}^{\mathsf T}A^n(p_+-p_-)
\tag{55.13}
$$

的非衰减频率只能是单位根。引理 55.1 则要求它等于含非单位根频率的 (55.1)。若选取其中一个未抵消频率 $\lambda$，将两端乘 $\lambda^{-n}$ 后对 $0\le n<N$ 作 Cesàro 平均：经典端所有单位根频率与衰减项均趋零，量子端趋向该非零系数。矛盾。乘 $2^n$ 只是对给定联合表作算术，不是物理选支。

例外角度的有限实现由定理 57.1 给出，至多六状态，故反向成立。

此证明使用成熟的正实现、Perron–Frobenius 和指数展开唯一性方法。相关先例是 Monras–Winter，[*Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*](https://arxiv.org/html/1412.3634)，定理 6、9，以及 Fanizza–Lumbreras–Winter，[*Quantum theory in finite dimension cannot explain every general process with finite memory*](https://arxiv.org/html/2209.11225v2)，定理 5 后的外围谱讨论。前者的多面锥条件同时要求初始向量属于锥、动态保持锥及终端泛函属于对偶锥；最小商的同构不保证隐藏载体本身同构。后者的 FRDN 过程、平稳制备及角度条件不同。(55.8)、真实原域双世界和 (55.12) 是本源承担的对应，未借用其过程或噪声结论。∎

## 56. 有限终点的经典记忆发散

**定理 56.1（C2：见证线段上的非定量发散）。** 固定 $\theta\notin(\pi/2)\mathbb Z$ 和 $0<d<1$。令 $\mathcal L_d=\{(1-u)\rho_-+u\rho_+:0\le u\le1\}$，双世界取引理 55.1。只要求匹配所有 $|h|\le H$ 的两种联合终端结果时，$\mathcal L_d$ 的有限经典最小状态数 $k_H$ 满足

$$
\lim_{H\to\infty}k_H=\infty,
\qquad k_H\le2(2^{H+1}-1).
\tag{56.1}
$$

上界可用在线段上仿射的制备实现；这里不主张完整 $\mathcal K_d$ 的仿射树实现，也不给发散率。

证明。固定 $k$。两个单纯形制备 $p_\pm$、$f_{\rm cl}\in[0,1]^k$、非负 $T_0,T_1$ 及列随机和的参数空间紧：各条目在 $[0,1]$，约束闭。每个有限历史的两个匹配条件均为这些参数的多项式等式。令 $\mathcal C_H$ 为匹配到长度 $H$ 的闭子集，则 $\mathcal C_{H+1}\subseteq\mathcal C_H$。若任意大 $H$ 都有 $k$ 状态模型，有限交性质给 $\bigcap_H\mathcal C_H\ne\varnothing$，产生双世界的全历史模型，违反定理 55.2。允许至多 $k$ 状态可用零制备的隐藏状态填充为恰 $k$ 状态。因此对每个 $k$ 存在有限 $H(k)$，此后均有 $k_H>k$。

为给有限上界，取状态 $(\pm,h)$，其中 $h$ 为长度至多 $H$ 的二元前缀。非叶节点在标签 $j$ 下以质量 $1/2$ 转移至 $(\pm,hj)$；叶节点的两个分支均取质量 $1/2$ 的自环。终端效果在 $(\pm,h)$ 上取 $\operatorname{Tr}(\rho_\pm M_h)$，介于零一之间。两棵树的根给端点制备；按 $u$ 混合两个根。每个前缀的实际质量为 $2^{-|h|}$，所以是、否两种记录都精确，制备在线段上仿射。总节点数为 (56.1) 的上界。

紧性只给 $H(k)$ 的存在。它不提供记忆增长率、噪声容限、有限样本证书或取得精确概率的成本；尤其不能去掉 (54.8) 中指数小的联合权重。∎

## 57. 例外角度的经典三角形与严格混合见证

**定理 57.1（C3：例外角度的全族经典界）。** 对全部 $\theta\in(\pi/2)\mathbb Z$ 和 $0<d<1$，

$$
k_{\min}(\theta,d)=3\quad(0<d\le2/3),\qquad
4\le k_{\min}(\theta,d)\le6\quad(2/3<d<1).
\tag{57.1}
$$

三状态和六状态上构造均在整个复 $\mathcal K_d$ 上具有单一仿射制备映射；下界允许任意制备和隐藏状态。

证明。引用第二卷 (40.14)–(40.15) 的实际轨道，令

$$
E_1=E,\quad E_2=aa^\dagger,\quad E_3=Waa^\dagger W,\qquad
\Sigma=(6+3d)/8,
\tag{57.2}
$$

则全部初始响应是

$$
b(s)=(\operatorname{Tr}(\rho E_i))_{i=1}^3
=(e_d,d+s,e_d-s),\qquad \sum_i b_i=\Sigma.
\tag{57.3}
$$

当 $\theta/(\pi/2)$ 为偶数，两个归一化前向响应更新分别为

$$
\pi_0(b)=(b_2,b_1,b_3),\qquad
\pi_1(b)=(b_3,b_1,b_2).
\tag{57.4}
$$

奇数时两个标签互换。实际分支仍乘 $1/2$。两个置换生成 $S_3$，每个续词的终端效果是三个投影之一。可行 $s$ 的像为紧区间 $[0,s_{\max}]$：紧凸性来自 (54.2)，$s=0$ 由第一卷的相位世界达到，(55.2) 给 $s_{\max}>0$。三者都是合法投影响应，故 $b(s)\in[0,1]^3$。

当 $d\le2/3$ 时，$\Sigma\le1$。取

$$
p(\rho)=b(s)/\Sigma,\qquad
f_{\rm cl}=(\Sigma,0,0)^{\mathsf T},\qquad T_j=P_j/2,
\tag{57.5}
$$

其中 $P_j$ 实现 (57.4)，按奇偶交换标签。每步的质量为 $1/2$，响应向量按同一规则置换，故全部联合记录相等。$s=\rho_{aa}-d$ 是仿射泛函，所以制备对完整复集合仿射。

当 $d>2/3$ 时，$1<\Sigma<9/8$。立方体截面

$$
Q_\Sigma=[0,1]^3\cap\{x_1+x_2+x_3=\Sigma\}
\tag{57.6}
$$

恰有六个顶点，即 $(1,\Sigma-1,0)$ 的全部置换。为 $b(0)$ 和 $b(s_{\max})$ 分别固定顶点凸分解，按 $s/s_{\max}$ 线性插值其六个权重。取这些权重作制备概率；每个 $P_j$ 作用于六个顶点，取 $T_j=P_j/2$；每个顶点的第一坐标作 $f_{\rm cl}$。这是固定六状态模型，且制备在全部 $\mathcal K_d$ 上仿射。

下面证明下界而不预设隐藏动态是置换。取 (55.2) 的一个非恒定 $b(s)$，其三个坐标不全相等，因为 $s>0$。其 $S_3$ 轨道张成非零常数方向及标准二维平面，故可达续响应的线性维数为三。对任何模型，令 $A_j=2T_j$；在可达隐藏向量 $2^{|h|}T_hp(\rho)$ 的实线性张成上定义 $L(x)=(f_{\rm cl}^{\mathsf T}x,f_{\rm cl}^{\mathsf T}A_{j_*}x,f_{\rm cl}^{\mathsf T}A_{1-j_*}x)$，其中 $j_*=\theta/(\pi/2)\bmod2$。这三个坐标依次对应空续词、效果 $E_2$ 的单步续词及效果 $E_3$ 的单步续词。匹配全部历史保证 $L A_j=\pi_j L$，且其像包含上述三维轨道。因此 $k\ge3$。

若 $k=3$，可达隐藏张成已经是 $\mathbb R^3$，$L$ 为同构。只有在这一步后，完整记录的质量等式才推出 $2T_j$ 在整个隐藏空间列随机；$S_3$ 的关系也在整个空间成立。因此各归一化分支具有非负随机逆，分别由其有限次幂给出。单纯形的随机自同构必置换其极点，所以这些动态必为置换。忠实的三点 $S_3$ 作用经重标号为标准作用，而不是先假设某种最小编码。

固定 $E_1$ 的二阶稳定子迫使终端效果为 $(u,v,v)$，其中

$$
u+2v=\Sigma,\qquad0\le u,v\le1.
\tag{57.7}
$$

这里和式可由可达张成上 $\sum_i b_i=\Sigma\mathbf1^{\mathsf T}p$ 推至整个空间。所有可达响应必须在 $(u,v,v)$ 的置换三角形中。两种取向分别给必要条件

$$
\begin{cases}
\min_i b_i\ge\max\{0,(\Sigma-1)/2\},&u\ge v,\\
\max_i b_i\le\Sigma/2,&u\le v.
\end{cases}
\tag{57.8}
$$

第一式来自 $v\ge0$、$u=\Sigma-2v\le1$；第二式来自 $v=(\Sigma-u)/2\le\Sigma/2$。当 $d>2/3$，$b_2\ge d>\Sigma/2$，已排除第二种取向。

为在整个 $2/3<d<1$ 排除第一种取向，取明确的严格混合世界

$$
\begin{gathered}
\delta=\frac{(1-d)(3d-2)}{100}>0,\qquad
s=\beta/2+\delta,\qquad y=\beta/6,\\
H=\begin{pmatrix}d+s&-(s+y)/2\\-(s+y)/2&y\end{pmatrix},\quad
c_0=(1,3)^{\mathsf T},\quad L=c_0^{\mathsf T}Hc_0=d-2\delta,\\
b_{\rm col}=\frac{4s}{\sqrt6}\frac{Hc_0}{L},\qquad
g_0=\beta-s-y,\qquad
\rho_{\rm mix}=\begin{pmatrix}H&b_{\rm col}\\b_{\rm col}^{\mathsf T}&g_0\end{pmatrix}_{(a,h_{\rm out},g)}.
\end{gathered}
\tag{57.9}
$$

迹为一、$\operatorname{Tr}(C\rho_{\rm mix})=d$；由 $c_0^{\mathsf T}b_{\rm col}=4s/\sqrt6$ 和第二卷 (40.17) 的 $q=(a+3h_{\rm out}+\sqrt6g)/4$，有 $\operatorname{Tr}(E\rho_{\rm mix})=e_d$。为证明全区间正性，令

$$
x=\frac{3d-2}{3(1-d)}>0,\qquad d=\frac{3x+2}{3x+3}.
\tag{57.10}
$$

直接展开 (57.9) 得

$$
\begin{aligned}
H_{11}&=\frac{300x^2+551x+250}{300(x+1)^2}>0,\\
\det H&=\frac{180000x^3+469391x^2+399400x+110000}{3240000(x+1)^4}>0,\\
L&=\frac{150x^2+249x+100}{150(x+1)^2}>0,\qquad
g_0=\frac{97x+100}{900(x+1)^2}>0,\\
g_0L-\frac83s^2
&=\frac{x(14550x^2+28749x+14200)}{135000(x+1)^4}>0.
\end{aligned}
\tag{57.11}
$$

因为 $b_{\rm col}^{\mathsf T}H^{-1}b_{\rm col}=8s^2/(3L)$，这些等式给 $\rho_{\rm mix}\succ0$。最后的相容松弛

$$
Q=d(y-\tau^2s)-[y+(1+2\tau)s]^2/4
=\frac{A_3x^3+A_2x^2+A_1x+A_0}{3240000(x+1)^4}
\tag{57.12}
$$

中的系数为

$$
\begin{aligned}
A_3&=6609600\sqrt2-9183600,\\
A_2&=18868104\sqrt2-26311729,\\
A_1&=17898000\sqrt2-25057400,\\
A_0&=5640000\sqrt2-7930000.
\end{aligned}
\tag{57.13}
$$

每个系数严格正：对各 $b\sqrt2-a$，整数 $2b^2-a^2$ 依次为 $3035115360000$、$19703614140191$、$12803513240000$、$734300000000$，且 $a,b>0$。这给整个开区间的 $Q>0$，不是有限点正性。故 $B_d\succ0$，(57.9) 是严格实际相容世界；(55.4)–(55.5) 同时给它的原通道提升。

此世界满足

$$
b_3=e_d-s=(\Sigma-1)/2-\delta<(\Sigma-1)/2,
\tag{57.14}
$$

违反剩余取向的必要条件。于是 $k=3$ 在每个 $d>2/3$ 均不可能，证明 (57.1)。这里没有确定上区间内 $4,5,6$ 哪一个达到最小。∎

## 58. 例外角度的任意实二维实现与圆盘判据

**定理 58.1（原响应的实二维充要几何）。** 固定 $\theta\in(\pi/2)\mathbb Z$ 和 $0<d<1$。令

$$
\begin{gathered}
\mu=\Sigma/3=(2+d)/8,\qquad
v(s)=(d+s-\mu,s/\sqrt3),\qquad R(s)=\|v(s)\|_2,\\
n_1=(-1/2,\sqrt3/2),\quad n_2=(1,0),\quad
n_3=(-1/2,-\sqrt3/2).
\end{gathered}
\tag{58.1}
$$

则定义 54.3 中允许任意实 Kraus、任意效果和隐藏纤维的实二维模型存在，当且仅当

$$
R(s)\le\mu\qquad\text{对每个 }\rho\in\mathcal K_d.
\tag{58.2}
$$

实一维模型不存在。若 (58.2) 成立，实二维模型可取仿射制备及两个单 Kraus 分支。

证明。(57.3) 可写为 $b_i(s)=\mu+n_i\cdot v(s)$。先证明对任意二维实现的必要性。取所有初始 $\sigma(\rho)$ 及其归一化可达矩阵

$$
2^{|h|}\Phi_h(\sigma(\rho)).
\tag{58.3}
$$

它们为迹一正矩阵，因为完整记录的两种终端结果之和恰为 $2^{-|h|}$。定理 57.1 证明中的三维续响应轨道，使这些矩阵的实线性张成至少三维。由于 $\dim\operatorname{Sym}_2(\mathbb R)=3$，张成必等于整个 $\operatorname{Sym}_2$；续响应映射 $L$ 的秩也为三，故为同构。这一步先排除了隐藏纤维，未假设编码是同构。

记 $\mathcal A_j=2\Phi_j$。在 (58.3) 上 $\mathcal A_j$ 保迹，故在线性张成的整个 $\operatorname{Sym}_2$ 上保迹。若其 Kraus 算子为 $\sqrt2L_{j\alpha}$，这一结论等价于

$$
2\sum_\alpha L_{j\alpha}^{\mathsf T}L_{j\alpha}=I_2.
\tag{58.4}
$$

所以它的实 Kraus 延拓在所有实矩阵上确实 TP。由 $L\mathcal A_j=\pi_jL$，$S_3$ 关系在整个 $\operatorname{Sym}_2$ 上成立，且各归一化分支在这个空间上的逆是 CP 幂。

为补足从对称矩阵到完整矩阵的逆关系，考虑任一这样的逆复合，写成 $\Psi(X)=\sum_\alpha K_\alpha XK_\alpha^{\mathsf T}$。它在每个实纯态 $xx^{\mathsf T}$ 上为恒等。对任意 $y\perp x$，

$$
0=y^{\mathsf T}\Psi(xx^{\mathsf T})y
=\sum_\alpha|y^{\mathsf T}K_\alpha x|^2.
\tag{58.5}
$$

于是每个 $K_\alpha x$ 平行于 $x$。取 $x=e_1,e_2$ 使每个 $K_\alpha$ 对角，再取 $x=e_1+e_2$ 使两对角元相等，故 $K_\alpha=c_\alpha I_2$。保迹给 $\sum c_\alpha^2=1$，从而 $\Psi$ 在所有实矩阵上恒等。其复线性延拓也在所有复矩阵上恒等。全局 CP 可逆性因此是达到维数饱和之后的结论。

现在 $\mathcal A_j$ 及其逆把整个迹一实正矩阵圆盘双射到自身。写

$$
\sigma(r)=\tfrac12(I_2+r_xZ+r_yX),\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad\|r\|\le1.
\tag{58.6}
$$

圆盘的仿射自同构固定其唯一中心，线性部分正交。平面的每个旋转由一个实二阶正交矩阵的共轭实现，其角度为原矩阵旋转角的两倍；反射亦由实正交共轭实现。故此处的实密度圆盘作用是正交共轭，其忠实 $S_3$ 作用在无迹平面上为标准二维表示。

令 $F_i$ 是三个续效果，它们由 $F$ 在这些全局 TP 分支的对偶下取得，因而全都满足 $0\preceq F_i\preceq I_2$。在可达张成上三效果之和为 $\Sigma I_2$，故在整个空间上也是如此。标准表示的固定无迹向量只有零，三效果可写为

$$
F_i=\mu I_2+a\,\widetilde n_i\cdot(Z,X),\qquad
\widetilde n_i\cdot\widetilde n_j=-1/2\ (i\ne j),
\quad 0\le a\le\mu,
\tag{58.7}
$$

其中方向可经统一正交变换与 (58.1) 对齐。幅度上界来自效果的最小本征值 $\mu-a\ge0$；此处 $\mu<1/2$，另一端 $\mu+a\le1$ 不更紧。三个等角方向满足 $\sum_i n_i n_i^{\mathsf T}=3I_2/2$，对 $\widetilde n_i$ 亦然。因此对任意制备 $\sigma(r)$，

$$
R(s)^2=\frac23\sum_{i=1}^3(b_i(s)-\mu)^2
=a^2\|r\|^2\le\mu^2.
\tag{58.8}
$$

这给任意编码的必要性。实一维的对称空间只有一维，不可能承载已证明的三维续响应。

充分性由以下完整模型给出：

$$
\begin{gathered}
\sigma(\rho)=\tfrac12\left[I_2+\frac{d+s-\mu}{\mu}Z+\frac{s}{\sqrt3\mu}X\right],\\
F_i=\mu[I_2+n_i\cdot(Z,X)],\\
O_0=\frac12\begin{pmatrix}1&\sqrt3\\\sqrt3&-1\end{pmatrix},\qquad
O_1=\frac12\begin{pmatrix}1&\sqrt3\\-\sqrt3&1\end{pmatrix},\qquad
\Phi_j(Y)=O_jYO_j^{\mathsf T}/2.
\end{gathered}
\tag{58.9}
$$

(58.2) 使 $\sigma(\rho)\succeq0$；$\sigma$ 对完整 $\mathcal K_d$ 仿射，三效果的谱为 $\{0,2\mu\}\subset[0,1]$。直接共轭得

$$
\begin{aligned}
(O_0^{\mathsf T}F_1O_0,O_0^{\mathsf T}F_2O_0,O_0^{\mathsf T}F_3O_0)&=(F_2,F_1,F_3),\\
(O_1^{\mathsf T}F_1O_1,O_1^{\mathsf T}F_2O_1,O_1^{\mathsf T}F_3O_1)&=(F_3,F_1,F_2),\\
\operatorname{Tr}(\sigma(\rho)F_i)&=b_i(s).
\end{aligned}
\tag{58.10}
$$

终端取 $F_1$，按例外角度的奇偶交换两个标签；每个分支质量为 $1/2$，和 TP，故匹配所有原联合记录及补终端结果。

可逆通道的成熟背景见 Nayak–Sen，[*Invertible Quantum Operations and Perfect Encryption of Quantum States*](https://arxiv.org/html/quant-ph/0605041v1)，定理 2.1。它假设复 CPTP 映射具有在所有密度矩阵上为左逆的 CPTP 映射，再推出酉与固定辅助态表示。该定理不能仅从可达子空间上的关系直接用于本题；这里由 (58.3) 的维数饱和、(58.5) 的实 Kraus 延拓和圆盘几何补足了所需桥梁。∎

## 59. 全族实二维阈值与每个上区间的实际见证

**定理 59.1（R1：例外角度的精确实最小维数）。** 令

$$
d_*=\frac{6(11+2\sqrt2)}{169+66\sqrt2}.
\tag{59.1}
$$

对全部固定 $\theta\in(\pi/2)\mathbb Z$ 和 $0<d<1$，

$$
m_{\min}(\theta,d)=
\begin{cases}
2,&0<d\le d_*,\\
3,&d_*<d<1.
\end{cases}
\tag{59.2}
$$

阈值端点属于二维区间。上区间的二维不可能性适用于任意定义 54.3 的实 CP 实现。

证明。由第一卷 (35.10)，全部相容态均满足

$$
0\le s\le\eta d,\qquad
\eta=\frac{3+2\sqrt2}{8}=\frac1{(1+\tau)^2}.
\tag{59.3}
$$

这是全复集合的必要界，不是忽略正性后的集合替代。(58.1) 给

$$
\begin{aligned}
R(s)^2&=(d+s-\mu)^2+s^2/3,\\
R(0)^2-\mu^2&=d(3d-2)/4,\\
R(\eta d)^2-\mu^2
&=\frac{d[(169+66\sqrt2)d-66-12\sqrt2]}{96}.
\end{aligned}
\tag{59.4}
$$

这是关于 $s$ 的凸二次式。在区间 (59.3) 上，其最大值由两个端点控制。$d_*<2/3$，所以 $d\le d_*$ 时两端均不超过 $\mu^2$。定理 58.1 的仿射二维构造因此覆盖全部复 $\mathcal K_d$，包括 $d=d_*$。

为证明该外界的接触点确实相容，置

$$
\begin{gathered}
\kappa=(11-2\sqrt2)/8,\quad M=17/2-2\sqrt2,\quad
d_{\rm cap}=\frac{6(17-4\sqrt2)}{289-60\sqrt2},\\
s=\eta d,\quad y=\kappa d,\quad
H_{\rm cap}=\begin{pmatrix}d+s&-7d/8\\-7d/8&y\end{pmatrix},\\
b_{\rm cap}=\frac{4s}{\sqrt6}\frac{H_{\rm cap}c_0}{Md},\qquad
g_{\rm cap}=1-11d/4,\qquad
\rho_{\rm cap}(d)=\begin{pmatrix}H_{\rm cap}&b_{\rm cap}\\b_{\rm cap}^{\mathsf T}&g_{\rm cap}\end{pmatrix}.
\end{gathered}
\tag{59.5}
$$

矩阵均在 $(a,h_{\rm out},g)$ 基中。代入得到以下精确等式：

$$
\begin{gathered}
\det H_{\rm cap}=d^2,\qquad c_0^{\mathsf T}H_{\rm cap}c_0=Md,\\
\operatorname{Tr}\rho_{\rm cap}=1,\quad
\operatorname{Tr}(C\rho_{\rm cap})=d,\quad
\operatorname{Tr}(E\rho_{\rm cap})=e_d,\\
d(y-\tau^2s)-[y+(1+2\tau)s]^2/4=0,\\
g_{\rm cap}-b_{\rm cap}^{\mathsf T}H_{\rm cap}^{-1}b_{\rm cap}
=1-d/d_{\rm cap}.
\end{gathered}
\tag{59.6}
$$

因 $H_{\rm cap}\succ0$，当 $0<d<d_{\rm cap}$ 时 $\rho_{\rm cap}\succ0$，且 $B_d\succeq0$。比较阈值，

$$
d_{\rm cap}-d_*=\frac{396(407774\sqrt2-511233)}{1514895529}>0;
\tag{59.7}
$$

正号可由 $2\cdot407774^2>511233^2$ 得到。因此

$$
\rho_*=\rho_{\rm cap}(d_*)\in\mathcal K_{d_*},\qquad
\rho_*\succ0,\quad s_*=eta d_*>0,\quad R(s_*)=\mu_*.
\tag{59.8}
$$

此处 $\rho_*$ 专指本节接触态，$\mu_*=(2+d_*)/8$。其 $B_{d_*}$ 可能奇异，但 (54.2) 的分解存在；可在 (55.4) 取 $\alpha=0$。分母仍正，因为 $s_*>0$，故 (55.5) 给实际原域提升。

对每个 $d>d_*$，令

$$
t=\frac{d-d_*}{1-d_*}\in(0,1),\qquad
\rho_t=(1-t)\rho_*+t aa^\dagger.
\tag{59.9}
$$

这里 $aa^\dagger$ 仅作为参数 $d=1$ 的闭端点数学对象：它满足迹、$C,E$ 矩及分解 $A=aa^\dagger,D=0$。将它与 $\rho_*$ 的 $A,D$ 分解分别取同一凸组合，直接得到 (54.2) 在参数 $d$ 的分解，故 $\rho_t\in\mathcal K_d$。这是跨参数的数学相容性证明，没有跨 $d$ 的物理制备授权。

更具体地，$\rho_t\succ0$、$s_t=(1-t)\eta d_*>0$，并且

$$
\det B_d(\rho_t)=t(1-t)d_*c_\ell^2>0.
\tag{59.10}
$$

为见此等式，$B_{d_*}(\rho_*)$ 是行列式为零的正矩阵；端点块为

$$
B_1(aa^\dagger)=
\begin{pmatrix}1&-\tau c_\ell\\-\tau c_\ell&\tau^2c_\ell^2\end{pmatrix}.
\tag{59.11}
$$

展开两者凸组合的行列式，交叉项为 $t(1-t)d_*c_\ell^2$，各自的纯二次项为零。因此所有上区间见证都严格满足完整相容条件，(55.4)–(55.5) 也为每个见证给原域提升。

令 $v_*=v(s_*)$，$n_*=v_*/\mu_*$。由 (59.4) 有 $\|n_*\|=1$，并且

$$
5v_{*,x}>3\mu_*
\quad\Longleftrightarrow\quad(47+10\sqrt2)d_*>16.
\tag{59.12}
$$

后一差的精确值为 $(85646-13716\sqrt2)/19849>0$。在端点 $d=1,s=0$，$v_1=(5/8,0)$、$\mu_1=3/8$，所以 $n_*\cdot v_1>\mu_1$。$v,\mu$ 都对参数 $(d,s)$ 仿射，故对每个 $t>0$，

$$
n_*\cdot v_t=(1-t)\mu_*+t\,n_*\cdot v_1
>(1-t)\mu_*+t\mu_1=\mu_t.
\tag{59.13}
$$

从而 $R(s_t)>\mu_t$。定理 58.1 排除所有实二维实现，而不仅是 (58.9) 的某种坐标选择。

最后给实三维上界：例外时去掉公共相位后的 $V_j$ 是实正交的 $U$ 或 $UW$，按奇偶交换标签。取制备 $\sigma(\rho)=\Re\rho$，终端效果 $E$，分支 $Y\mapsto V'_jY(V'_j)^{\mathsf T}/2$。对任意实向量 $x$，$x^{\mathsf T}\Re\rho\,x=x^\dagger\rho x\ge0$，故制备为实密度矩阵。所有实际词效果为实，因而此仿射模型保留全部复初始态的两种联合记录。实一维已被排除，得到 (59.2)。∎

## 60. 非例外角度的实维数界与一个五维编码的失败

**定理 60.1（R2 的一般实界）。** 固定 $\sin(2\theta)\ne0$ 和 $0<d<1$。定义 54.3 的一般实实现满足

$$
4\le m_{\min}(\theta,d)\le6.
\tag{60.1}
$$

这里不确定 $4,5,6$ 中哪一个为最小值。

证明。第二卷定理 40.1、41.1 已给实际词

$$
\mathcal H=(\varnothing,0,1,00,10,000,010,100)
\tag{60.2}
$$

的全 Hermitian 张成；它们的联合效果 $2^{-|h|}M_h$ 连同 $I_3$ 的行列式为

$$
\frac{6561}{2^{36}}\sin^7(2\theta)\ne0.
\tag{60.3}
$$

该供应使用原时间次序、所有实际 $2^{-|h|}$ 权重和全复矩阵，而非假设可自由调用任意酉。若两个初始态编码成同一个实态，全部记录必相等，(60.3) 迫使两个复态相同。因此任意允许的仿射编码在 $\mathcal K_d$ 上单射。

(55.2) 的 $\rho\succ0$、$s>0$ 和严格 $B_d$ 条件，使 (54.3) 的六参数在一个开邻域内均可变化。所以 $\mathcal K_d$ 的仿射维数为六。实 $m$ 维密度矩阵的仿射维数为 $m(m+1)/2-1$，故

$$
m(m+1)/2-1\ge6,
\tag{60.4}
$$

推出 $m\ge4$。这一下界使用已声明的全族仿射性；不把只对线段仿射的树当成反例。

上界复用标准实化，记

$$
\mathfrak R(X)=\begin{pmatrix}\Re X&-\Im X\\\Im X&\Re X\end{pmatrix}.
\tag{60.5}
$$

这正是 McKague–Mosca–Gisin，[*Simulating quantum systems using real Hilbert spaces*](https://arxiv.org/html/0810.1923v1)，§§II.1–II.2 式 (1)–(3) 的算子实化，按基重排得到 (60.5)。该供应保持乘法、伴随、正性、酉性及 POVM 概率，也适用于 Kraus 算子。用于本源的混合态接口为

$$
\sigma(\rho)=\mathfrak R(\rho)/2,\quad F=\mathfrak R(E),\qquad
\Phi_j(Y)=\mathfrak R(V_j)Y\mathfrak R(V_j)^{\mathsf T}/2.
\tag{60.6}
$$

迹归一化因子来自 $\operatorname{Tr}\mathfrak R(\rho)=2$；效果仍在零和一之间，分支和 TP，制备对完整复集合仿射。供应的迹关系给

$$
\operatorname{Tr}\!\left[\frac{\mathfrak R(\rho)}2
\mathfrak R(M_h)\right]=\operatorname{Tr}(\rho M_h).
\tag{60.7}
$$

故 (60.6) 匹配实际 $2^{-|h|}$ 联合权重及两种终端结果。实化是成熟上构造，不以它作为本源新定理，也不把增加的实寄存器当成已取得的原生资源。∎

**定义 60.2（指定协变的五维编码）。** 在 $(\xi,e,f)$ 基中写

$$
\rho=\begin{pmatrix}c&z^\dagger\\z&Q\end{pmatrix},\qquad
c=d/2>0,\quad z\in\mathbb C^2,\quad Q\in\operatorname{Herm}_2(\mathbb C),
\quad z_R=(\Re z,\Im z)^{\mathsf T}.
\tag{60.8}
$$

指定编码与其动态为

$$
\mathcal P_5(\rho)=
\begin{pmatrix}c&z_R^{\mathsf T}/\sqrt2\\z_R/\sqrt2&\mathfrak R(Q)/2\end{pmatrix},
\qquad
\widehat V_j=\operatorname{diag}(1,\mathfrak R(B_j)),\quad
\widehat\Phi_j(Y)=\widehat V_jY\widehat V_j^{\mathsf T}/2,
\tag{60.9}
$$

其中 $B_0=B_\zeta$、$B_1=B_\zeta\operatorname{diag}(1,-1)$，故去掉公共相位后的 $V_j=1\oplus B_j$。这一指定包括初始编码及此后每一步的协变编码；不允许另换一个后继轨迹仍称为同一编码。

**命题 60.3（指定 $\mathcal P_5$ 的正性、协变性及合法效果障碍）。** 对每个 $\sin(2\theta)\ne0$ 和每个 $0<d<1$，(60.9) 是正的仿射迹一编码，指定分支为实 CP 且其和 TP，并与原动态协变；但是不存在 $0\preceq F_5\preceq I_5$，使这个指定编码和动态匹配全部原历史的终端是概率。因此它不是定义 54.3 的一个完整实现。

证明。令

$$
J=\begin{pmatrix}0&-I_2\\I_2&0\end{pmatrix}.
\tag{60.10}
$$

由 $\mathfrak R(zz^\dagger)=z_Rz_R^{\mathsf T}+(Jz_R)(Jz_R)^{\mathsf T}$，$\mathcal P_5$ 对首条目的 Schur 补为

$$
\frac12\mathfrak R(Q-zz^\dagger/c)
+\frac1{2c}(Jz_R)(Jz_R)^{\mathsf T}\succeq0.
\tag{60.11}
$$

其迹为 $c+\operatorname{Tr}Q=1$。编码对固定 $c=d/2$ 的完整初始集合仿射。$z\mapsto B_jz$、$Q\mapsto B_jQB_j^\dagger$ 与 (60.9) 的正交共轭相接，所以协变性成立，分支和 TP。

要排除终端效果，必须使用实际可达差空间，而不是把 $\mathcal K_d$ 外的纯相干方向擅作制备。在 (55.2) 的严格邻域内，迹、$C,E$ 三个线性约束的切空间包含 $\xi$–$e$ 的纯虚相干、$\xi$–$f$ 的纯虚相干以及 $\xi$–$f$ 的纯实相干。这三个方向既不改变 $\rho_{\xi\xi}=d/2$，也不改变 $E$ 的实配对；小的正负扰动均为实际相容初始态。因此其编码差确实属于可达差的线性张成。

把纯虚 $\xi$–$f$ 相干经 $V_0$ 推进，其交叉列是

$$
B_\zeta\begin{pmatrix}0\\\mathrm i\end{pmatrix}
=\begin{pmatrix}\mathrm i\sqrt3\zeta/2\\\mathrm i\zeta/2\end{pmatrix}.
\tag{60.12}
$$

其 $e$ 实部为 $-\sqrt3\Im\zeta/2\ne0$。减去已经有的两个虚方向及实 $\xi$–$f$ 方向，即在可达差张成中得到纯实 $\xi$–$e$ 相干。此论证只用一步实际分支与线性组合，不要求生成群稠密，也不授权实际制备这些线性组合。

对一个交叉列变化 $z=(x,0)^{\mathsf T}$，原效果 $E$ 的 Born 响应变化恰为 $x$。指定编码的对应交叉项为 $x/\sqrt2$，效果响应变化为 $\sqrt2(F_5)_{\xi,e_R}x$。由刚得到的可达方向，匹配全部历史迫使

$$
(F_5)_{\xi,e_R}=1/\sqrt2.
\tag{60.13}
$$

但每个合法效果满足 $\|F_5-I_5/2\|_{\rm op}\le1/2$，从而每个非对角条目的模至多 $1/2$，与 (60.13) 矛盾。

矛盾依赖指定的后继协变编码和终端效果权利。它不排除另一种实四维或五维初始编码、一般多 Kraus 动态、不同可达轨迹或额外隐藏纤维。正态编码和协变动态本身都不足以完成一个概率实现。∎

## 61. 文献归属、条件综合与未决边界

**定义 61.1（源特定内容与成熟工具的区分）。** 本卷的 `repo-derived` 内容是原完整复 $\mathcal K_d$、原标签与两终端联合表上的以下条件综合：定理 55.2 的全角度经典判据，定理 56.1 的见证线段有限终点发散，定理 57.1 的经典阈值界及严格混合见证，定理 58.1–59.1 的任意实二维必要性与精确例外阈值，以及命题 60.3 的指定五维编码障碍。这里不主张这些工具的发明权或全域文献优先权。

源接口的对应为：第一卷定理 35.2、35.4、35.6 供应实际全复集合、原域提升、完整输入响应和六参数约束；第二卷定理 39.3–39.4 供应时间词、两终端原始联合概率与后继对应；第二卷定理 40.1 的实际有限张成和例外投影轨道分别供 (60.3)、(57.3)–(57.4)；第二卷定理 42.4 供应严格可行点。这里引用这些供应而不重作其全词张成证明。

作为 `literature-attested` 的中间工具，Monras–Winter 的正实现多面锥条件与最小商，Fanizza–Lumbreras–Winter 的非单位根外围频率障碍，Nayak–Sen 的完整 CPTP 左逆定理，以及 McKague–Mosca–Gisin 的实化，均按前文列明的假设使用。紧空间的有限交性质、可约 Perron–Frobenius、随机单纯形自同构和实圆盘几何也只作中间工具。实际频率是否出现、隐藏支持是否幂有界、最小商何时饱和及哪些接触态属于原集合，由本卷的原对象对应承担。

**假设 61.2（其他实复分离结果的适用前提）。** Fawzi、Gouveia、Parrilo、Robinson、Thomas，[*Positive Semidefinite Rank*](https://arxiv.org/html/1407.4095v1)，§2.2 的实复 psd 秩比较，研究有限非负表的静态半正定因子分解。若以它推出本题更强维数下界，需另给实际历史子表、所需秩下证书以及从动态实现到该因子的明确映射；反向上界还需固定 CP 动态与全族仿射制备。静态分解本身不供应这些接口。

Renou 等，[*Quantum theory based on real numbers can be experimentally falsified*](https://arxiv.org/html/2101.10873v2)，使用两个来源、三方张量结构、纠缠交换和多种局域测量选择。把该结果用于本题，需证明这里的单一原生历史合同供应其来源独立性、子系统分解和测量菜单；本卷不作此假设。其任意维数实模型排除不直接成为本题的实四维或五维排除。

**定义 61.3（仍未确定的问题）。** 在本卷的精确比较模型中，以下问题保留为未决：非例外角度的一般实最小维数在 $4,5,6$ 中的取值；例外角度 $d>2/3$ 的经典最小值在 $4,5,6$ 中的取值；定理 56.1 的定量记忆增长、噪声或有限样本界；完整 $\mathcal K_d$ 上具有指定仿射规则的无限状态经典构造及其额外正则性。指定 $\mathcal P_5$ 失败不是这些问题的解答。

原擦除标签菜单的全参数最小最大问题仍是第一卷定义 38.3 的原问题；扩大标签记录的实现分类不确定其中心。精确概率的取得、未知关系与实际资源之间的桥梁也保留原合同。跨 $d$ 的凸组合、归一化可达状态、推导出的逆和证明中的线性组合均是数学对象，不构成新的原生操作菜单。

这些条件结果以当前复 Hilbert/Born/CP 结构为前提，没有从信息守恒、共同整体来源或确定到不确定的层级直觉推出该结构，也没有确定物理原则的起源。相关本体或经验性命题需要另给明确模型关系、可观察后果与相应证据。

## 追加锚（本行以下为增补区）

## 62. 非例外角度的一般实最小维数

**定理 62.1（完整原生联合表的精确实维数）。** 对每个 $0<d<1$ 和每个满足 $\sin(2\theta)\ne0$ 的实角度，在定义 54.3 的原合同下，

$$
m_{\min}(\theta,d)=6.
\tag{62.1}
$$

量词包括任意实 Kraus CP 分支、分支和 TP、完整复集合 $\mathcal K_d$ 上的同一个仿射制备、同一个合法效果、所有原时间词和两种终端结果及其 $2^{-|h|}$ 联合权重。没有预设编码忠实、分支分别公平、动态可逆、制备协变或不存在隐藏纤维。

此等式细化定理 60.1 的 $4\le m_{\min}\le6$，并确定定义 61.3 中非例外角度的一般实维数问题。上界直接取既有 (60.6)，不另作上界构造。下界由 §§63–70 的证明给出：先由实际记录将任意 $m\le5$ 模型约化到匹配的 $1\oplus\mathbb R^4$ 正交作用，再用原集合中的纯曲线排除所有仿射制备和合法效果。这里的数学闭包只延续精确表的等式，不授予闭包点或逆的操作权限。

**定义 62.2（证明中的固定源与记号）。** 以下固定定理 62.1 的参数，置 $c=d/2\in(0,1/2)$。在 $(\xi,e,f)$ 基中，去掉不影响共轭作用的公共相位，原生成元为

$$
\begin{gathered}
V'_j=1\oplus B_j,\qquad z_\theta=e^{-2\mathrm i\theta},\qquad
R=\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\\
D_\theta=\operatorname{diag}(1,z_\theta),\qquad
B_0=RD_\theta,\quad B_1=B_0Z.
\end{gathered}
\tag{62.2}
$$

当一个实模型被假定存在时，记 $T_j=2\Phi_j$、$T_h=T_{j_n}\cdots T_{j_1}$、$X_{h,\rho}=T_h\sigma(\rho)$。由两终端等式而非额外公平性假设，

$$
\operatorname{Tr}X_{h,\rho}=1,\qquad
\operatorname{Tr}(F X_{h,\rho})=
\operatorname{Tr}(E V_h\rho V_h^\dagger).
\tag{62.3}
$$

$V_h$ 与 $V'_h$ 在此处有同一共轭作用。所有闭包均取有限维线性映射的通常范数拓扑；实 CP 映射始终指在完整实矩阵代数上的实 Kraus 映射，而非只在对称矩阵锥上为正的映射。

## 63. 实际生成元的紧闭包与真实 SU(2) 子群

**引理 63.1（所有非例外角度的源闭包）。** (62.2) 的正词酉闭包是紧群，其下二阶块包含实际 $SU(2)$。特别地，源共轭闭包包含 $\operatorname{Ad}(1\oplus u)$、$u\in SU(2)$；此作用保留中心元 $u=-I_2$ 对交叉相干的非平凡作用。

证明。在紧酉群中，对每个酉矩阵 $Q$，其有限个本征相位有同时回归的正整数子列，故 $Q^{n_\nu}\to I$，$Q^{n_\nu-1}\to Q^{-1}$。这证明正词闭包是群，而不要求原菜单可执行逆。由原矩阵得到

$$
Z=B_0^{-1}B_1,\qquad
R=Z(B_0ZB_0^{-1})Z,\qquad
D_\theta=RB_0.
\tag{63.1}
$$

第二式只用 $Z R Z R Z=R$，以及 $D_\theta Z=ZD_\theta$。因此下块闭包包含 $R,D_\theta$。

先证其在 $PU(2)\simeq SO(3)$ 中的像无限。若 $z_\theta$ 不是单位根，$D_\theta$ 的投影已有无限阶。若 $z_\theta$ 是单位根，假设投影群有限。选取平方根 $z_\theta^{1/2}$，则

$$
Q=(\mathrm iR)(z_\theta^{-1/2}D_\theta)\in SU(2),\qquad
\kappa=\operatorname{Tr}Q=
\frac{\mathrm i}{2}(z_\theta^{1/2}-z_\theta^{-1/2}).
\tag{63.2}
$$

有限投影群在 $SU(2)$ 的双覆盖原像有限，故 $Q$ 有限阶，$\kappa$ 必为代数整数。在包含 $\mathrm i,z_\theta^{1/2}$ 的圆分域中，每个共轭将这两个根映到同阶单位根；因而 $\kappa$ 的每个共轭都是实数，模至多一。非例外性给 $z_\theta\notin\{1,-1\}$，所以原共轭满足 $0<|\kappa|<1$。所有共轭均非零，非零代数整数的域范数于是是绝对值严格小于一的非零整数，矛盾。这覆盖 $\theta/\pi$ 为有理数的全部非例外角度，没有用无理角稠密性替代它们。

再排除无限真闭子群。这里使用闭矩阵子群的 Lie 结构和局部指数映射，参见 Hall，[*An Elementary Introduction to Groups and Representations*](https://arxiv.org/html/math-ph/0005032v1)，定理 3.23 及其连通群由指数生成的推论。适用对象是已经取闭的紧矩阵群。$\mathfrak{so}(3)$ 的非零真子代数只能是一维：在 $\mathbb R^3$ 的叉积模型中，两个独立向量的叉积不在其二维张成内。因此无限真闭子群的单位分支是一条轴的旋转环面，整个子群正规化该轴。角度既非零也非 $\pi$ 的 $D_\theta$ 在这种正规化子中只能绕该轴旋转，故轴必须是第三坐标轴。但 $R$ 的投影是绕 $(\sqrt3/2,0,-1/2)$ 的半转，将第三轴的单位向量送到

$$
(-\sqrt3/2,0,-1/2)^{\mathsf T},
\tag{63.3}
$$

不是第三轴或其相反轴。故投影闭包只能是整个 $SO(3)$。

设下块闭群为 $G_2\subseteq U(2)$。其 Lie 代数到 $\mathfrak{so}(3)$ 的投影满射，交换子代数落在 $\mathfrak{su}(2)$，又满射到 $\mathfrak{so}(3)$，故等于 $\mathfrak{su}(2)$。由指数生成，$G_2$ 包含实际 $SU(2)$，不只是其投影像。相应源作用为 $1\oplus u$；$u=-I_2$ 把 $\xi$–下块交叉列变号，故不能在后续表示论中将它换成仅有整数自旋的 $SO(3)$。∎

## 64. 可达支持、完整矩阵幂界与正确的观察商

**引理 64.1（任意隐藏模型的可达压缩与有界 CP 半群）。** 假定定义 54.3 的实模型存在。可将它限制到全部 $X_{h,\rho}$ 的联合实支持 $H_{\rm r}$，保留仿射制备、合法效果、原分支和 TP 及全部记录。在该支持上，$T_h$ 在完整实矩阵代数及其复化的所有矩阵层上一致有界；其闭包 $\mathscr S$ 是紧实 CP 半群。

证明。由 (62.3)，每个 $X_{h,\rho}$ 都是正的迹一矩阵。令 $H_{\rm r}$ 为这些矩阵像空间的实线性张成。有限维性允许选取有限多个可达密度矩阵及正权重，使其凸组合 $\Omega$ 满足

$$
\Omega\succ0\text{ 于 }H_{\rm r},\qquad
\operatorname{Tr}\Omega=1,\qquad
\operatorname{Tr}(T_h\Omega)=1\quad(\text{全部 }h).
\tag{64.1}
$$

最后一式由词的拼接和两终端总质量推出。

逐个原 Kraus 算子都保持 $H_{\rm r}$。事实上，若 $v\perp H_{\rm r}$，则对可达 $X$，$T_j(X)$ 也可达，并且

$$
0=v^{\mathsf T}T_j(X)v
=2\sum_\alpha\|X^{1/2}L_{j\alpha}^{\mathsf T}v\|^2.
\tag{64.2}
$$

各项非负，故每个 $L_{j\alpha}$ 将 $\operatorname{ran}X$ 送入 $H_{\rm r}$；这些像空间张成整个 $H_{\rm r}$。因而限制后的 Kraus 平方和仍是 $I_{H_{\rm r}}$，效果压缩仍在零与一之间，所有实际等式原样保留。未被到达的块在此之前没有受到任何限制。

选 $\varepsilon>0$ 使 $\Omega\succeq\varepsilon I_{H_{\rm r}}$。正性给

$$
0\preceq T_h(I_{H_{\rm r}})
\preceq\varepsilon^{-1}T_h(\Omega),\qquad
\|T_h(I_{H_{\rm r}})\|_{\rm op}\le\varepsilon^{-1}.
\tag{64.3}
$$

实 Kraus 复化是 $M_{\dim H_{\rm r}}(\mathbb C)$ 上的 CP 映射。使用 CP 映射的成熟范数恒等式 $\|T\|_{\rm cb}=\|T(I)\|$：对任意矩阵层的收缩 $X$，正块矩阵 $\left(\begin{smallmatrix}I&X\\X^\dagger&I\end{smallmatrix}\right)$ 经放大映射后仍正，其非对角块范数至多 $\|T(I)\|$；$X=I$ 给反向不等式。因此

$$
\sup_h\|T_h\|_{\rm cb}\le\varepsilon^{-1}.
\tag{64.4}
$$

这同时控制对称和反对称实矩阵，不能只以对称可达空间上的幂界代替。有限维下，有界闭集紧，实 Choi 正锥闭，故完整线性映射闭包 $\mathscr S=\overline{\{T_h\}}$ 是紧实 CP 半群。此时只证明了可达态上的质量等式，尚未证明任何 $T_j$ 在整个支持上 TP。∎

**引理 64.2（八维源空间上的良定义商）。** 令

$$
\begin{gathered}
\mathscr R=\operatorname{span}_{\mathbb R}\{X_{h,\rho}:h\in\{0,1\}^{<\infty},\ \rho\in\mathcal K_d\},\\
\mathscr V=\operatorname{span}_{\mathbb R}\{V_h\rho V_h^\dagger:h\in\{0,1\}^{<\infty},\ \rho\in\mathcal K_d\},\qquad
\mathscr S_c=\{X\in\operatorname{Herm}_3(\mathbb C):
X_{\xi\xi}=c\operatorname{Tr}X\}.
\end{gathered}
\tag{64.5}
$$

其中 $h$ 遍历所有有限词。则 $\mathscr V=\mathscr S_c$，实维数为八，且

$$
L(X_{h,\rho})=V_h\rho V_h^\dagger
\tag{64.6}
$$

唯一延伸为良定义满射 $L:\mathscr R\to\mathscr S_c$。它给出连续满射半群同态

$$
\pi:\mathscr S\longrightarrow G,
\tag{64.7}
$$

其中 $G$ 是实际源词作用在 $\mathscr S_c$ 上的紧群闭包；$LT_j=\operatorname{Ad}(V_j)L$。

证明。首先精确区分效果空间与状态空间。第二卷定理 40.1 供应的是

$$
\{I_3\}\cup\{2^{-|k|}M_k:k\in\mathcal H\},\qquad
\mathcal H=(\varnothing,0,1,00,10,000,010,100),
\tag{64.8}
$$

这九个元素的行列式是 (60.3)，非零。八个词效果单独不是九维基；$I_3$ 必须由两终端总质量或迹配对另行供应。

若 $\sum_\nu a_\nu X_{h_\nu,\rho_\nu}=0$，将关系与每个继续词的 $F T_k$ 配对，得到

$$
\operatorname{Tr}\!\left(M_k\sum_\nu a_\nu
V_{h_\nu}\rho_\nu V_{h_\nu}^\dagger\right)=0.
\tag{64.9}
$$

将原关系取迹，又给源关系与 $I_3$ 的配对为零，因为两边的每个生成矩阵迹均为一。由 (64.8)，源关系为零。因此 (64.6) 良定义、满射到 $\mathscr V$，且词的拼接给交织关系。没有假设 $\sigma$ 单射，也没有先删除不可观察的隐藏纤维。

每个源可达矩阵满足 $X_{\xi\xi}=c\operatorname{Tr}X$，所以 $\mathscr V\subseteq\mathscr S_c$。为证反向，只需一个实际合法纯态

$$
\psi_0=\sqrt d\,a+\mathrm i\sqrt{1-d}\,g,\qquad
\rho_0=\psi_0\psi_0^\dagger.
\tag{64.10}
$$

它范数为一，$\rho_{0,aa}=d$、$\operatorname{Tr}(C\rho_0)=d$、$\operatorname{Tr}(E\rho_0)=(6-5d)/16$。取分解 $A=\rho_0,D=0$，即属于原 (54.2)。由引理 63.1，源词闭包包含它的 $SU(2)$ 轨道；有限维线性张成闭，故该轨道位于 $\mathscr V$。写成

$$
\rho_0=\begin{pmatrix}c&z_0^\dagger\\z_0&Q_0\end{pmatrix}_{(\xi,e,f)}.
\tag{64.11}
$$

纯性给 $\|z_0\|^2=c(1-c)>0$，$Q_0$ 是迹 $1-c$ 的秩一矩阵，故其无迹部分非零。$\mathscr S_c$ 在 $SU(2)$ 下分解为互不同构的

$$
\mathbb R\operatorname{diag}(c,(1-c)I_2/2)
\ \oplus\ \mathbb R^4_{\rm fund}
\ \oplus\ \mathbb R^3_{\rm ad}.
\tag{64.12}
$$

第一个分量来自群平均；交叉列给实四维基本表示，$Q_0$ 的无迹部分给三维伴随表示，两者都不可约且非零。紧群完全可约性或相应等型投影表明该轨道张成所有三个分量。因此 $\mathscr V=\mathscr S_c$，而非九维的全部 $\operatorname{Herm}_3(\mathbb C)$。这里没有说初始 $\mathcal K_d$ 是八维；其仿射维数仍为六。

最后，$\mathscr R$ 和 $\ker L$ 对每个 $T_h$ 不变，故对其闭包不变。选任意线性右逆 $J:\mathscr S_c\to\mathscr R$，定义

$$
\pi(s)=L s J.
\tag{64.13}
$$

因 $\ker L$ 不变，此式与 $J$ 无关，且 $Ls=\pi(s)L$。它连续并保持乘法。每个 $s$ 是词映射的极限，故 $\pi(s)$ 是源词作用的极限；反过来任意源极限可借 $\mathscr S$ 的紧性选择同一词子列的映射极限。因此像恰为 $G$。同一极限也保持 $\operatorname{Tr}(F s\sigma(\rho))=\operatorname{Tr}(E\pi(s)\rho)$，其中 $\pi(s)$ 按源共轭作用解释。其 $SU(2)$ 子群在 (64.12) 上忠实：基本表示使 $-I_2$ 也可见。∎

## 65. 最小全矩阵秩幂等元与实完全序收缩

**引理 65.1（紧闭包内的角群和自伴观察商）。** 在引理 64.1 的紧闭包中，存在按完整实矩阵映射秩取最小值的 CP 幂等元 $P$。角半群

$$
\mathscr K=P\mathscr S P
\tag{65.1}
$$

是以 $P$ 为单位的紧群，群逆仍由 CP 映射表示，$\pi(\mathscr K)=G$，并且 $LP=L$ 于 $\mathscr R$。其像经过忠实序单位的合同变换，成为一个有限维实 $C^*$ 代数 $\mathcal A$；$\mathscr K$ 在 $\mathcal A$ 上作用为实 $*$ 自同构。

证明。这里以成熟的有限维紧半群最小秩与角群方法为中间工具；所需假设是完整矩阵映射组成乘法封闭的紧集，已由引理 64.1 给出。先在已经闭合的 $\mathscr S$ 中选一个最小秩元素 $a$，记此秩为 $r$，秩是在 $M_{\dim H_{\rm r}}(\mathbb R)$ 全空间上计算。因 $a^2\in\mathscr S$，$\operatorname{rank}(a^2)=r$，所以零本征值处没有非平凡幂零 Jordan 块。有界幂排除模大于一的本征值及单位圆上的非平凡 Jordan 块。若非零本征值有模严格小于一者，取所有单位模本征值同时回归一的幂子列；其极限的秩严格小于 $r$，矛盾。因此同一回归过程给

$$
a^{n_\nu}\longrightarrow P,\qquad P^2=P,\quad
\operatorname{rank}P=r.
\tag{65.2}
$$

闭性给 $P$ 为实 CP。$\pi(P)$ 是群中的幂等元，必为单位。故 $LP=L$ 于 $\mathscr R$，$L:P\mathscr R\to\mathscr S_c$ 仍满射。

每个 $PsP$ 的秩至多 $r$，又因它在 $\mathscr S$ 中而至少为 $r$；限制到 $\operatorname{ran}P$ 后便是可逆线性变换。$P\mathscr S P$ 紧，且限制映射忠实：角元素由其在 $\operatorname{ran}P$ 上的值确定。紧的可逆矩阵半群是群；具体地，对任意元素，同时回归的正幂趋于单位，前一幂趋于其逆，紧性将逆留在该半群内。因此 (65.1) 是紧群，逆代表也 CP。$\pi(PsP)=\pi(s)$ 给满射性。此时 $P\mathscr R$ 对角群不变，后续的源表示正是此自伴不变子空间的商。

再作支持约化。置

$$
H_1=\operatorname{supp}(P\Omega).
\tag{65.3}
$$

因 $\Omega$ 在 $H_{\rm r}$ 上忠实，$\operatorname{supp}(P\Omega)=\operatorname{supp}(P I)$。若 $P(X)=\sum_\alpha W_\alpha XW_\alpha^{\mathsf T}$，此支持等于所有 $W_\alpha$ 像空间的张成。因此每个完整矩阵 $P(X)$ 的左右支持都在 $H_1$，包括反对称矩阵。仅用正矩阵张成对称部分不足以推出这一全矩阵结论。

$P\Omega$ 是 $\operatorname{ran}P$ 的序单位：若 $Y\succeq0$ 且 $P(Y)=Y$，由 $Y\preceq b\Omega$ 得 $Y\preceq bP\Omega$。对 $k\in\mathscr K$，$k(P\Omega)$ 仍在该正锥内，且由 $k^{-1}(P\Omega)\preceq bP\Omega$ 得

$$
P\Omega\preceq b\,k(P\Omega).
\tag{65.4}
$$

故每个 $k(P\Omega)$ 在 $H_1$ 上忠实。用紧群的归一化 Haar 测度置

$$
\Omega_1=\int_{\mathscr K}k(P\Omega)\,dk\succ0
\quad\text{于 }H_1.
\tag{65.5}
$$

它被角群逐点固定。将 $P$ 及角群限制到 $H_1$ 保持其全部像与群恒等式。此处只对 $P$ 和 $\mathscr K$ 使用 $H_1$；没有假设原 $T_j$ 保持这个较小支持，也没有假设 $P$ 是忠实映射。

记 $D_1=\Omega_1^{1/2}$、$n_1=\dim H_1$，在 $M_{n_1}(\mathbb R)$ 上置

$$
\widetilde P(X)=D_1^{-1}P(D_1XD_1)D_1^{-1},\qquad
\widetilde k(X)=D_1^{-1}k(D_1XD_1)D_1^{-1}.
\tag{65.6}
$$

$\widetilde P$ 是保单位的 CP 幂等映射，$\widetilde k$ 与其角群逆在像上是互逆的保单位 CP 映射。实 Kraus 复化使 $\widetilde P_{\mathbb C}$ 成为 $M_{n_1}(\mathbb C)$ 上保单位、CP、幂等的线性映射；保单位性又给收缩性。

在此准确使用 Choi–Effros 乘法定理，采用 Prunaru，[*On the Choi–Effros multiplication*](https://arxiv.org/html/1304.6664v2)，定理 1 的表述：复 $C^*$ 代数上的完全正、收缩、幂等线性映射之像，以

$$
x\star y=\widetilde P_{\mathbb C}(xy)
\tag{65.7}
$$

为乘法、原伴随为 involution，并继承完整矩阵序，成为与该像完全序同构的 $C^*$ 代数。这里的代数是 $M_{n_1}(\mathbb C)$，映射是 (65.6) 的复化，三个假设均已给出。逐项复共轭与实 Kraus 映射交换，且保持 (65.7)，其不动实形就是所需实代数 $\mathcal A$。这不是声称像在环境通常乘法下已经封闭。

在 $\mathcal A$ 上，$\widetilde k$ 和其逆都是保单位 CP。两次 Kadison–Schwarz 不等式给对每个 $a$ 的等号，从而 $\widetilde k(a^*\star a)=\widetilde k(a)^*\star\widetilde k(a)$，也给 $a\star a^*$ 的等号；成熟的乘法域判据于是给 $*$ 乘法性。故角群作用为实 $*$ 自同构。∎

## 66. 抽象收缩的表示成本与低维刚性

**引理 66.1（源基本表示迫使五维全实矩阵代数）。** 假定原模型 $m\le5$。引理 65.1 的代数必为 $\mathcal A\simeq M_5(\mathbb R)$；$m=\dim H_{\rm r}=\dim H_1=5$，且 $P=I$ 是完整矩阵映射。相应共同源 $SU(2)$ 的正交提升在底层五维实空间上等价于 $1\oplus\mathbb R^4_{\rm fund}$。因此 $m\le4$ 已不可能。

证明。先给必须用于比较物理维数的表示成本，而不把完全序嵌入误认为代数嵌入。记

$$
i:\mathcal A\longrightarrow M_{n_1}(\mathbb R),\qquad
r=i^{-1}\widetilde P:M_{n_1}(\mathbb R)\longrightarrow\mathcal A.
\tag{66.1}
$$

$i$ 是完全序包含，$r$ 是到抽象代数的保单位 CP 收缩，$ri=\operatorname{id}_{\mathcal A}$。对任意 $a\in\mathcal A$，先对 $i$ 用 Schwarz、再作用 $r$，以及直接对 $r$ 用 Schwarz，分别给

$$
r(i(a)^*i(a))\preceq a^*\star a,
\qquad
a^*\star a\preceq r(i(a)^*i(a)).
\tag{66.2}
$$

同样有 $aa^*$ 的等号。因此 $i(a)$ 属于抽象收缩 $r$ 的乘法域。由乘法域的左右乘法恒等式，$r$ 限制到

$$
\mathcal D=C^*_{\mathbb R}(i(\mathcal A))\subseteq M_{n_1}(\mathbb R)
\tag{66.3}
$$

是满射实 $*$ 同态到 $\mathcal A$。此论断的余域是带 $\star$ 乘法的 $\mathcal A$；不声称 $i$ 保持通常乘法，也不声称环境投影 $\widetilde P$ 的通常乘法域等于其像。

有限维实 $C^*$ 结构定理把 $\mathcal D$ 分解为 $M_s(\mathbb R)$、$M_s(\mathbb C)$、$M_s(\mathbb H)$ 因子的直和。实不可约表示的三种交换子类型参见 Rosenberg，[*Structure and applications of real C*-algebras*](https://arxiv.org/html/1505.04091)，定理 1.3、推论 1.4；其假设是实 Hilbert 空间上的不可约 $*$ 表示，这里施于各简单因子的不可约矩阵模。各因子的最小忠实实表示维数为

$$
\operatorname{cost}_{\mathbb R}M_s(\mathbb R)=s,\qquad
\operatorname{cost}_{\mathbb R}M_s(\mathbb C)=2s,\qquad
\operatorname{cost}_{\mathbb R}M_s(\mathbb H)=4s.
\tag{66.4}
$$

这些数是各除环上的列模的实维数。不同因子的中心投影要求互相正交的非零模，故直和成本相加。有限维理想是若干整因子的直和；由 (66.3) 的核丢弃相应因子，并在 $\mathbb R^{n_1}$ 的忠实表示中保留剩余中心投影的物理子空间，便得到 $\mathcal A$ 的忠实实表示。因此

$$
\operatorname{cost}_{\mathbb R}\mathcal A\le n_1\le m.
\tag{66.5}
$$

下一步把源基本表示放入这个代数的自伴部分。$\mathscr K$ 在 $\operatorname{ran}P$ 上忠实地是紧矩阵群，故为紧 Lie 群；$\pi:\mathscr K\to G$ 是连续满射。紧 Lie 群的分支数有限，故 $G/\pi(\mathscr K^0)$ 有限，而 $G^0$ 连通，得到 $\pi(\mathscr K^0)=G^0$；相应 Lie 代数映射满射。用紧 Lie 代数上的 Ad 不变正内积，将核理想取正交补；该正交补仍是理想，并同构于 $\operatorname{Lie}(G)$。在补理想中提升源的实际 $\mathfrak{su}(2)$，再从单连通 $SU(2)$ 积分，得到

$$
\lambda:SU(2)\longrightarrow\mathscr K,
\qquad \pi\lambda(u)=\operatorname{Ad}(1\oplus u)|_{\mathscr S_c}.
\tag{66.6}
$$

这里使用的是紧 Lie 代数理想分裂与单连通群的 Lie 同态积分；参数域确为单连通 $SU(2)$，不是 $SO(3)$。两个同态的微分一致且域连通，故它们在整个群上一致。

$P\mathscr R$ 在该作用下不变，$L:P\mathscr R\to\mathscr S_c$ 满射。Haar 平均内积给紧群完全可约性，所以 (64.12) 中的实四维基本表示必须出现在 $\mathcal A_{\rm sa}$ 中。它在中心 $-I_2$ 下变号。

现在逐因子排除成本至多五的其他可能。连通 $SU(2)$ 不能置换有限个简单因子，也不能进入离散外自同构分支。对于 $M_s(\mathbb R)$，实 $*$ 自同构为正交内自同构；从单连通 $SU(2)$ 到投影正交群的作用可提升到 $O(s)$。低维实不可约 $SU(2)$ 模只有维数 $1,3,4,5$。具体地，复最高权 $k$ 的模 $\operatorname{Sym}^k\mathbb C^2$ 有复维数 $k+1$，中心作用为 $(-1)^k$，不变反线性结构的平方为 $(-1)^k$；偶 $k$ 为实型、奇 $k$ 为四元数型。因此维数至多五时，唯一中心非平凡的实不可约模是四维基本模。对于 $s\le4$，底层模不是全由中心为正的模组成，就是恰为实四维基本模；两种情形中心都是标量，故共轭在 $\operatorname{Sym}_s(\mathbb R)$ 上中心平凡，不能产生所需基本分量。

成本至多五的非实非交换因子只有 $M_2(\mathbb C)$ 和 $\mathbb H$。前者的自伴部分是 $1\oplus\mathbb R^3_{\rm ad}$，连通实 $*$ 自同构群为 $PU(2)\simeq SO(3)$；从 $SU(2)$ 的同态在中心上平凡。$\mathbb C$ 的额外共轭自同构离散，不能改变结论。$\mathbb H$ 的自伴部分只有实标量。其余复、四元数矩阵因子成本超过五。不同直和因子间不存在交叉矩阵条目，不能拼出一个中心非平凡的基本分量。

所以总成本至多五时，唯一余项是 $\mathcal A=M_5(\mathbb R)$，底层实表示必须为 $1\oplus\mathbb R^4_{\rm fund}$；整数自旋五维或 $3\oplus1\oplus1$ 的中心平凡，均不合要求。相应自伴分解为

$$
\operatorname{Sym}^2(\mathbb R^4_{\rm fund})
=1\oplus3\,\mathbb R^3_{\rm ad},\qquad
\operatorname{Sym}^2(1\oplus\mathbb R^4_{\rm fund})
=2\cdot1\oplus\mathbb R^4_{\rm fund}\oplus3\,\mathbb R^3_{\rm ad}.
\tag{66.7}
$$

最后用的是全矩阵维数，不是自伴维数：$\dim_{\mathbb R}M_5(\mathbb R)=25$，而

$$
25=\dim_{\mathbb R}\operatorname{ran}P
\le (\dim H_1)^2\le (\dim H_{\rm r})^2\le m^2\le25.
\tag{66.8}
$$

全部等号成立，$H_1=H_{\rm r}=\mathbb R^5$，$P$ 为满秩幂等线性映射，故 $P=I$。因最小秩已经是全秩，每个 $s\in\mathscr S$ 都可逆，紧半群本身成为群。至此才消除了原支持与角支持之间的区别。∎

## 67. 原分支和 TP 迫使逐支正交

**引理 67.1（从任意 CP 分支导出的匹配正交五维模型）。** 若原模型 $m\le5$，则在原五维实空间上，存在正交矩阵 $O_0,O_1$ 使

$$
T_j(X)=O_jXO_j^{\mathsf T},\qquad
\Phi_j(X)=\tfrac12O_jXO_j^{\mathsf T}.
\tag{67.1}
$$

同一紧闭包内的 (66.6) 在固定正交坐标中作用为 $O(u)=1\oplus\mathcal R(u)$，其中 $\mathcal R$ 是复二维基本表示的实四维形式。原来的 $\sigma$ 与 $F$ 仍满足全族仿射性和合法性。

证明。由引理 66.1，$P=I$，$\mathscr S$ 是完整矩阵 CP 映射的紧群，逆也 CP。每个实 CP 序同构是可逆实合同

$$
T_j(X)=A_jXA_j^{\mathsf T}.
\tag{67.2}
$$

其成熟完全序证明在此可直接适配：先用 $T_j(I)^{1/2}$ 保单位化，再对保单位映射及其 CP 逆使用两次 Schwarz，得到实全矩阵 $*$ 自同构；该自同构是正交内自同构，再还原合同。转置仅是反自同构，不能作为此 CP 双向同构的替代。

从紧群 Haar 平均 $I_5$ 得到被整个 $\mathscr S$ 固定的 $\Omega_2\succ0$。定义

$$
B_j=\Omega_2^{-1/2}A_j\Omega_2^{1/2}.
\tag{67.3}
$$

由 $A_j\Omega_2A_j^{\mathsf T}=\Omega_2$ 得 $B_j$ 正交。仅此不能推出原 $A_j$ 正交；必须使用原仪器的 TP 和。现在 $H_1=H_{\rm r}$ 已经成立，(54.10) 在这个完整支持上给

$$
A_0^{\mathsf T}A_0+A_1^{\mathsf T}A_1=2I_5,
\qquad
B_0^{\mathsf T}\Omega_2B_0+B_1^{\mathsf T}\Omega_2B_1=2\Omega_2.
\tag{67.4}
$$

置 $D_j=B_j^{\mathsf T}\Omega_2B_j$。正交共轭保持 Hilbert–Schmidt 范数，故严格凸性的精确等号式为

$$
\sum_{j=0}^1\|D_j-\Omega_2\|_{\rm HS}^2
=\sum_{j=0}^1\|D_j\|_{\rm HS}^2-2\|\Omega_2\|_{\rm HS}^2=0.
\tag{67.5}
$$

所以 $D_j=\Omega_2$，$B_j$ 与 $\Omega_2$ 交换，(67.3) 还原为 $A_j=B_j$。这才导出每个 $T_j$ 全局 TP 和原坐标中的正交性，而不是从可达公平性预设它们。

$\mathscr S$ 因而是正交共轭群的闭子群；(66.6) 的 $SU(2)$ 作用从投影正交群提升到 $O(5)$，由单连通性可选连续群提升。引理 66.1 的表示分类将它正交共轭成 $1\oplus\mathcal R(u)$。此最后坐标变换为正交变换，故只将 $\sigma,F$ 一同正交共轭，保持密度、迹一、仿射性和 $0\preceq F\preceq I$。原制备上的所有隐藏分量在这一证明之前一直被允许；这里没有以制备协变替换原概率合同。∎

## 68. 任意纯制备的零圆与秩约束

**引理 68.1（不指定编码的纯态响应与零圆）。** 在引理 67.1 导出的匹配正交表示中，设 $\rho\in\mathcal K_d$ 为任意纯态，$\Sigma=\sigma(\rho)$。则固定合法效果必有 $\operatorname{rank}F\le2$；若 $\operatorname{rank}F=2$，则 $\operatorname{rank}\Sigma=1$。结论不假定 $\mathcal P_5$、制备协变或下块无隐藏分量。

证明。由 (62.3) 及共同紧闭包，对每个 $u\in SU(2)$，同一个源状态与同一个编码状态的响应等式仍成立。因 $\rho_{\xi\xi}=c$，选其不影响密度矩阵的总体相位，可写

$$
\psi=\sqrt c\,\xi+\sqrt{1-c}\,r_0,
\qquad r_0\in\xi^\perp,\quad\|r_0\|=1.
\tag{68.1}
$$

$SU(2)$ 在复二维单位球上传递。选 $H\in SU(2)$ 使 $He=r_0$，将群变量写为 $g=uH^{-1}$。在编码侧只把本次响应式中的 $\Sigma$ 换成 $O(H^{-1})\Sigma O(H^{-1})^{\mathsf T}$，保持其正性、迹和秩。这是等式的变量代换，不是对源集合添加制备，也不改变固定效果。于是要研究的响应为

$$
\begin{gathered}
u=(u_1,u_2)\in\mathbb C^2,\quad |u_1|^2+|u_2|^2=1,\qquad
U(u)=\begin{pmatrix}u_1&-\bar u_2\\u_2&\bar u_1\end{pmatrix},\\
\operatorname{Tr}\bigl(F O(u)\Sigma O(u)^{\mathsf T}\bigr)
=f_c(u):=\tfrac12|\sqrt c+\sqrt{1-c}\,u_1|^2.
\end{gathered}
\tag{68.2}
$$

此处实下块按 $(\Re z_1,\Im z_1,\Re z_2,\Im z_2)$ 排列。令

$$
\alpha=\sqrt{c/(1-c)}\in(0,1),\qquad
R_c=\sqrt{1-\alpha^2}>0.
\tag{68.3}
$$

目标响应在整个圆 $u_1=-\alpha$、$u_2=R_c e^{\mathrm i\varphi}$ 上为零。

若两个正矩阵的迹配对为零，则它们的支持正交。因此把 $F,\Sigma$ 作任意实秩一谱分解，零圆上的每个幅度分别为零；等价地，对所有 $w\in\operatorname{ran}F$、$v\in\operatorname{ran}\Sigma$，

$$
w_0v_0+\Re\bigl(w_{\rm low}^\dagger U(u)v_{\rm low}\bigr)=0
\quad(u_1=-\alpha,\ u_2=R_ce^{\mathrm i\varphi}).
\tag{68.4}
$$

$f_c(u)-f_c(-u)$ 的非零一次项要求 $\Sigma$ 的标量–下块交叉非零。因此可选 $v\in\operatorname{ran}\Sigma$，其标量 $s$ 和下块范数 $r$ 均非零。把实四维基本模看作左四元数模；单位右四元数变换与每个 $U(u)$ 交换，并在下块单位球上传递。用这种固定正交变换可令 $v=(s,r,0)$，下块复坐标为 $(r,0)$，且不改变 (68.2) 的同一个 $u$。

对 $w=(w_0,w_1,w_2)$，(68.4) 变为

$$
sw_0-\alpha r\Re w_1+
 rR_c\Re(\bar w_2e^{\mathrm i\varphi})=0
\quad(\text{所有 }\varphi).
\tag{68.5}
$$

故 $w_2=0$、$w_0=(\alpha r/s)\Re w_1$。所有 $w$ 位于一个实二维平面，得到 $\operatorname{rank}F\le2$。

若秩恰为二，$w_1$ 在该支持上遍历整个 $\mathbb C$。对任意其他支持向量 $v'=(s',x+\mathrm iy,z+\mathrm it)$，代回 (68.4)。$e^{-\mathrm i\varphi}$ 系数对所有 $w_1$ 为零，给 $z=t=0$；剩余常数式为

$$
\frac{\alpha r}{s}s'\Re w_1
-\alpha\Re\bigl(\bar w_1(x+\mathrm iy)\bigr)=0
\quad(\text{所有 }w_1\in\mathbb C).
\tag{68.6}
$$

所以 $y=0$、$x=(r/s)s'$。全部 $v'$ 均在同一实直线上，$\operatorname{rank}\Sigma=1$。这些约束覆盖原任意下块；没有删除伴随表示或其他中心偶分量。∎

**引理 68.2（秩一效果的完整排除）。** (68.2) 对 $0<c<1/2$ 不可能由任意实密度矩阵 $\Sigma$ 与合法秩一效果 $F$ 实现。因此在假定的实五维模型中，$F$ 恰为秩二，每个合法源纯态的编码均为秩一密度矩阵。

证明。若 $F=ww^{\mathsf T}$，合法性给 $\|w\|^2\le1$。标量或下块任一为零都会消去 (68.2) 的中心奇一次项，故两者非零。以不影响 $F$ 的整体符号、标量轴的符号及交换的右四元数变换，写

$$
w=(a,b,0),\qquad a,b>0,\qquad a^2+b^2\le1,
\qquad
\Sigma=\begin{pmatrix}p&h^{\mathsf T}\\h&M\end{pmatrix}.
\tag{68.7}
$$

令 $u_1=\lambda_0+\mathrm i\lambda_1$、$u_2=\lambda_2+\mathrm i\lambda_3$，$\lambda\in S^3$。此时 $w^{\mathsf T}O(u)=(a,b\lambda_0,-b\lambda_1,-b\lambda_2,-b\lambda_3)$；目标多项式是 $c/2+(1-c)(\lambda_0^2+\lambda_1^2)/2+\sqrt{c(1-c)}\lambda_0$。匹配一次、二次及常数系数，得到

$$
\begin{gathered}
h=\left(\frac{\sqrt{c(1-c)}}{2ab},0,0,0\right)^{\mathsf T},\qquad
t_c=\frac{1-c}{2b^2},\\
M=\operatorname{diag}(t_c+\beta,t_c+\beta,\beta,\beta),\qquad
a^2p+b^2\beta=c/2.
\end{gathered}
\tag{68.8}
$$

这里不能将 $\beta$ 擅自置零：两个次数至多二的实多项式在单位球面相等，其二次差允许是 $\beta b^2(\|u\|^2-1)$。具体地，先在 $u$ 与 $-u$ 比较确定一次项；在各坐标单位向量上比较得到所有对角差相同；在 $(e_i\pm e_j)/\sqrt2$ 上比较则所有非对角项为零。这正好留下 (68.8) 的一个标量球面歧义，并把相应常数吸收到最后一式。

正性给 $p\ge0$、$\beta\ge0$。迹一则要求

$$
1=p+\frac{1-c}{b^2}+4\beta.
\tag{68.9}
$$

置 $x=a^2>0$、$y=b^2>0$，$x+y\le1$。由 $xp+y\beta=c/2$，

$$
p+4\beta\ge\frac{c/2}{\max\{x,y/4\}}.
\tag{68.10}
$$

若最大值为 $x$，Cauchy–Schwarz 给

$$
\begin{aligned}
1&\ge\frac{1-c}{y}+\frac{c}{2x}\\
&\ge\frac{(\sqrt{1-c}+\sqrt{c/2})^2}{x+y}
\ge(\sqrt{1-c}+\sqrt{c/2})^2>1.
\end{aligned}
\tag{68.11}
$$

最后严格不等式等价于 $\sqrt{2c(1-c)}>c/2$，平方后的差为 $c(8-9c)/4>0$。若最大值为 $y/4$，则

$$
1\ge\frac{1-c}{y}+\frac{2c}{y}=\frac{1+c}{y}>1.
\tag{68.12}
$$

并列最大值同时落入上述两种论证。$x=0$ 或 $y=0$ 已由非零奇响应排除；$p=0$ 或 $\beta=0$ 并未被除掉，仍包含于 (68.10)；秩零效果因目标不恒零也不可能。于是 $F$ 必秩二，再由引理 68.1 对每个合法纯态得到编码秩一。∎

## 69. 固定效果迫使同一个交叉映射

**引理 69.1（无协变前提的交叉刚性）。** 在匹配正交五维模型中，以固定源下块坐标写

$$
\rho=\begin{pmatrix}c&z^\dagger\\z&Q_{\rm src}\end{pmatrix},\qquad
\sigma(\rho)=\begin{pmatrix}p(\rho)&h(\rho)^{\mathsf T}\\h(\rho)&M(\rho)\end{pmatrix},
\quad
F=\begin{pmatrix}F_{00}&b^{\mathsf T}\\b&F_{\rm low}\end{pmatrix}.
\tag{69.1}
$$

存在与 $\rho$ 无关的 $k>0$ 和正交实矩阵 $Q_*$，使对全部 $\rho\in\mathcal K_d$，

$$
h(\rho)=kQ_*z_R.
\tag{69.2}
$$

此结论不要求整个制备对群作用协变，也不要求初始源仿射包络为全部 Hermitian 空间。

证明。先说明表示结构。源中心 $\operatorname{Ad}(1\oplus(-I_2))$ 的奇部分恰是 $z_R$ 的实四维交叉块；编码侧 $\operatorname{Ad}(1\oplus(-I_4))$ 的奇部分恰是 $h$。由 (66.7)，两边都只有一个基本模，其他对角块均为中心偶。$L$ 在可达线性空间上的交织、满射及该基本模的不可约性，迫使这一交叉对应为非零同构。

此处实 Schur 引理只给非零交织的可逆性，不能把实四维基本模的交换子误写成 $\mathbb R$；它是右四元数代数 $\mathbb H$。其对称交换子却只有实标量：任何交换的对称矩阵的本征子空间均不变，而基本模不可约。故任意非零交织 $T$ 的 $T^{\mathsf T}T$ 为正标量，$T$ 是正标量乘正交矩阵。这里使用 Hall 定理 5.28(1) 的实版本，而不套用仅对复不可约表示成立的标量交换子部分。

还可直接由固定效果系数推出 (69.2)，以避免在这一步隐含制备协变。设 $m\in\mathbb R^4$ 是源读出 $E=(\xi+e)(\xi+e)^\dagger/2$ 的单位下块向量；更换固定下块基后仍有 $\|m\|=1$。分别比较群元 $u$ 和 $-u$，所有中心偶块消去，留下

$$
2b^{\mathsf T}\mathcal R(u)h(\rho)
=m^{\mathsf T}\mathcal R(u)z_R
\quad(\text{全部 }u\in SU(2),\ \rho\in\mathcal K_d).
\tag{69.3}
$$

合法纯态给非零源交叉列；其 $SU(2)$ 轨道的右端不恒零，故 $b\ne0$。

将单位四元数参数写为 $u=(u_0,u_1,u_2,u_3)\in S^3$，并写

$$
\mathcal R(u)=\sum_{\nu=0}^3u_\nu M_\nu,\qquad M_0=I_4,
\qquad K(v)_{\nu,\cdot}=v^{\mathsf T}M_\nu.
\tag{69.4}
$$

在 (68.2) 的坐标约定下，该实矩阵明确为

$$
\mathcal R(u)=\begin{pmatrix}
u_0&-u_1&-u_2&-u_3\\
u_1&u_0&u_3&-u_2\\
u_2&-u_3&u_0&u_1\\
u_3&u_2&-u_1&u_0
\end{pmatrix}.
$$

左四元数乘法的矩阵满足 $M_\nu M_\mu^{\mathsf T}+M_\mu M_\nu^{\mathsf T}=2\delta_{\nu\mu}I$，所以

$$
K(v)K(v)^{\mathsf T}=\|v\|^2I_4.
\tag{69.5}
$$

比较 (69.3) 的四个一次系数，得到 $2K(b)h=K(m)z_R$，从而

$$
h=\frac{K(b)^{\mathsf T}K(m)}{2\|b\|^2}z_R,
\qquad
k=\frac1{2\|b\|},\qquad
Q_*=\frac{K(b)^{\mathsf T}K(m)}{\|b\|}\in O(4).
\tag{69.6}
$$

同一个 $b,m$ 用于整个原集合，故不存在依赖输入的坐标选择、仿射常数偏移或来自下对角块的混入。由 (69.3) 对群变量的平移及解的唯一性，$Q_*$ 也与相应基本作用交织。这个直接推导只使用每个实际初始态在共同闭包下的响应；即使初始仿射包络是恰当子空间，系数等式仍逐态成立。∎

## 70. 原完整集合中的开纯曲线与仿射矛盾

**引理 70.1（对每个内点参数的实际纯曲线及原五维提升）。** 令

$$
\begin{gathered}
\delta_d=\min\left\{1,\sqrt{\frac{1-d}{2d}}\right\}>0,
\qquad |t|<\delta_d,\\
f_d(t)=\sqrt{\frac{1-3d+2d\cos t}{13-12\cos t}},\\
\psi_t=\sqrt d\,a+\sqrt d(e^{\mathrm it}-1)h_{\rm out}
+\mathrm i(3e^{\mathrm it}-2)f_d(t)g,\qquad
\rho_t=\psi_t\psi_t^\dagger.
\end{gathered}
\tag{70.1}
$$

则每个 $\rho_t$ 属于原完整 $\mathcal K_d$，并有原五维 CPTP 提升 $\mathcal T_t\in\mathcal F_{\sqrt d}$，其后继为 $S_{\rho_t}$。特别地，这不是仅满足松弛人口界或两个矩的曲线。

证明。由 $1-\cos t\le t^2/2$，

$$
1-3d+2d\cos t=1-d-2d(1-\cos t)
>\frac{1-d}{2}>0,
\qquad 13-12\cos t\ge1.
\tag{70.2}
$$

因此区间对每个 $0<d<1$ 非空，$f_d$ 正、偶且连续。在 $(a,h_{\rm out},g)$ 正交基中，置 $x=\cos t$，直接得

$$
\begin{gathered}
\|\psi_t\|^2=d+2d(1-x)+(13-12x)f_d(t)^2=1,
\qquad (\rho_t)_{aa}=d,\\
\operatorname{Tr}(C\rho_t)=|\sqrt d+\sqrt d(e^{\mathrm it}-1)|^2=d,\\
\operatorname{Tr}(E\rho_t)
=\frac{d(13-12x)+6(1-3d+2dx)}{16}
=\frac{6-5d}{16}.
\end{gathered}
\tag{70.3}
$$

最后一式也可由 $q^\dagger\psi_t=(3e^{\mathrm it}-2)(\sqrt d+\mathrm i\sqrt6 f_d(t))/4$ 直接读出。取 $A=\rho_t,D=0$，即满足 (54.2) 的原分解；此时 $s=0$，$B_d(\rho_t)$ 是 $a,\ell$ 振幅的正秩一 Gram 矩阵。

明确给出原物理提升。为区别于证明中的实支持，仍以 $H=\mathbb C^5$ 表示 (54.1) 的物理空间，置

$$
\begin{gathered}
p_{\rm phys}=Bq,\qquad
c_{\rm phys}=(e_0+e_1-e_3-e_4)/2,\\
\eta_t=\sqrt d\,p_{\rm phys}
+\sqrt d(e^{\mathrm it}-1)Br
+\mathrm i(3e^{\mathrm it}-2)f_d(t)c_{\rm phys}.
\end{gathered}
\tag{70.4}
$$

三个物理向量 $p_{\rm phys},Br,c_{\rm phys}$ 正交归一，故 $\|\eta_t\|=1$。用原 $K_0,K_1$，而非重选仪器，有

$$
\begin{gathered}
K_jp_{\rm phys}=Ba/\sqrt2,
\qquad K_jBr=Bh_{\rm out}/\sqrt2,
\qquad K_jc_{\rm phys}=Bg/\sqrt2\quad(j=0,1),\\
K_0\eta_t=K_1\eta_t=B\psi_t/\sqrt2.
\end{gathered}
\tag{70.5}
$$

因此取两个 Kraus 算子 $BP_+$、$\eta_tf^\dagger$，得到

$$
\mathcal T_t(X)=BP_+XP_+B^\dagger
+(f^\dagger Xf)\eta_t\eta_t^\dagger,
\qquad P_++\|\eta_t\|^2ff^\dagger=I_3.
\tag{70.6}
$$

它是原域 $M_3(\mathbb C)\to M_5(\mathbb C)$ 的 CPTP 通道，(70.5) 给 $\mathcal G\mathcal T_t=S_{\rho_t}$。

再核对完整原效果，而不只核对 $ff^\dagger$ 上的输出。第一卷 (35.3) 的原 $J_0=P,J_1,J_2$ 在 $(q,r,f)$ 输入基中的供应值为

$$
\begin{gathered}
Y_0=\operatorname{diag}(1,0,d),\qquad
Y_1=\frac1{16}\begin{pmatrix}1&3&0\\3&9&0\\0&0&6-5d\end{pmatrix},\\
Y_2=\frac1{32}\begin{pmatrix}17&3&0\\3&9&0\\0&0&6+11d\end{pmatrix}.
\end{gathered}
\tag{70.7}
$$

(70.6) 的伴随为 $P_+B^\dagger J_jBP_++\langle\eta_t,J_j\eta_t\rangle ff^\dagger$，故跨扇区条目全部为零，$q,r$ 块是同一个原供应块。标量条目分别是 $d$、$\operatorname{Tr}(E\rho_t)=e_d$、$\operatorname{Tr}(F_{\rm src}\rho_t)=(6+11d)/32$，其中 $F_{\rm src}=B^\dagger J_1B$ 是第一卷的原 qutrit 效果，满足 $E+2F_{\rm src}=3I/4+3C/8$。前者来自 $|p_{\rm phys}^\dagger\eta_t|^2=d$；由 $J_1=\mathcal G^\dagger(P)$、$J_2=\mathcal G^\dagger(J_1)$ 和 (70.5)，后两者分别是 $\psi_t^\dagger E\psi_t$ 与 $\psi_t^\dagger F_{\rm src}\psi_t$。这给 $\mathcal T_t^\dagger(J_j)=Y_j$，$j=0,1,2$，作为完整矩阵的等式。原递推 $J_{j+2}=(J_j+J_{j+1})/2$ 对 $j\ge1$ 将它们延续到全部深度。因此 $\mathcal T_t\in\mathcal F_{\sqrt d}$。此处复用第一卷的原提升接口与递推，只把当前曲线的所有参数明确代入。∎

**引理 70.2（纯曲线上的完整仿射函数空间）。** 令 $x=\cos t$、$y=\sin t$、$f=f_d(t)$。当实仿射泛函 $\Lambda$ 遍历 $\mathcal K_d$ 的仿射包络上的所有泛函时，$\Lambda(\rho_t)$ 所成的实函数空间恰为

$$
\operatorname{span}_{\mathbb R}\{1,x,y,f,xf,yf\}.
\tag{70.8}
$$

证明。有限维仿射泛函可延伸到环境 Hermitian 空间。各矩阵条目直接为

$$
\begin{gathered}
(\rho_t)_{aa}=d,\qquad
(\rho_t)_{h_{\rm out}h_{\rm out}}=2d(1-x),\qquad
(\rho_t)_{gg}=1-3d+2dx,\\
(\rho_t)_{a h_{\rm out}}=d(x-1)-\mathrm i d y,\\
(\rho_t)_{ag}=-3\sqrt d\,yf-\mathrm i\sqrt d(3x-2)f,\\
(\rho_t)_{h_{\rm out}g}=\sqrt d\,yf+5\mathrm i\sqrt d(x-1)f.
\end{gathered}
\tag{70.9}
$$

因此每个仿射泛函均在 (70.8) 中。反向，常函数由迹得到，而

$$
\begin{aligned}
x&=1-\frac{(\rho_t)_{h_{\rm out}h_{\rm out}}}{2d},
&y&=-\frac{\Im(\rho_t)_{a h_{\rm out}}}{d},\\
yf&=\frac{\Re(\rho_t)_{h_{\rm out}g}}{\sqrt d},
&f&=-\frac{\Im(\rho_t)_{ag}+(3/5)\Im(\rho_t)_{h_{\rm out}g}}{\sqrt d},\\
xf&=f+\frac{\Im(\rho_t)_{h_{\rm out}g}}{5\sqrt d}.
\end{aligned}
\tag{70.10}
$$

所以六个生成函数全部都是矩阵条目的实仿射组合。结论是函数空间的张成等式，不需要先假定它们线性独立。∎

**定理 70.3（所有仿射正交五维实现均不可能）。** 对任意 $0<d<1$，不存在一个完整 $\mathcal K_d$ 上的仿射密度制备和固定合法效果，在匹配的 $1\oplus\mathbb R^4_{\rm fund}$ 正交作用下满足全部原精确响应。因此定理 62.1 的任意实 CP 实现必须有 $m\ge6$。

证明。反设存在。由引理 68.2，每个 $\sigma(\rho_t)$ 都秩一。令

$$
v=(a-h_{\rm out})/\sqrt2,
\qquad \xi=(a+h_{\rm out})/\sqrt2,
\tag{70.11}
$$

并在固定 $(\xi,v,g)$ 基中取源交叉列 $z_t$。这是源下块的固定基变换，仍用引理 69.1 的固定 $k,Q_*$。直接由 (70.1)，

$$
(\rho_t)_{\xi\xi}=c,\qquad
(\rho_t)_{v\xi}=c(2e^{-\mathrm it}-1),\qquad
\|(z_t)_R\|^2=c(1-c)>0.
\tag{70.12}
$$

把编码写成 (69.1)。秩一、正性、迹一及 $h_t=kQ_*(z_t)_R$ 给

$$
p(t)(1-p(t))=\|h_t\|^2=k^2c(1-c)>0.
\tag{70.13}
$$

若右端大于 $1/4$，已经矛盾；否则该方程至多有两个实根，且都在 $(0,1)$。一个保持全部凸组合的有限维仿射映射在其仿射包络上有唯一仿射延伸，因而连续；证明可在凸集的相对内点附近取一组仿射基，凸组合恒等式先给局部线性，再沿线段延伸。这里的包络可以是恰当仿射子空间，无需假定全 Hermitian 制备域。故 $p(t)$ 在连通开区间上连续，只能恒为一个 $p_0\in(0,1)$；重根 $p_0=1/2$ 同样包含。

秩一的 Schur 等号于是给整个编码下块

$$
M(t)=\frac{h_th_t^{\mathsf T}}{p_0}
=\frac{k^2}{p_0}Q_*(z_t)_R(z_t)_R^{\mathsf T}Q_*^{\mathsf T}.
\tag{70.14}
$$

取源下块实协向量 $e_{v,\Re}$，并在编码侧取固定 $Q_*e_{v,\Re}$。由于 $M(\rho)$ 是同一个仿射制备的下块，(70.14) 迫使

$$
\bigl(\Re(\rho_t)_{v\xi}\bigr)^2
=c^2(2\cos t-1)^2
\tag{70.15}
$$

是 $\rho_t$ 的一个实仿射泛函，比例常数 $k^2/p_0$ 非零。

由引理 70.2 并取 $t\leftrightarrow-t$ 的偶部，存在实常数 $A,B,C,D$ 使

$$
c^2(2x-1)^2=A+Bx+(C+Dx)
\sqrt{\frac{1-3d+2dx}{13-12x}}
\quad(\cos\delta_d<x<1).
\tag{70.16}
$$

分母在该非空开区间为正。移项、平方并乘分母，得到区间上的多项式恒等式

$$
\bigl[c^2(2x-1)^2-A-Bx\bigr]^2(13-12x)
=(C+Dx)^2(1-3d+2dx).
\tag{70.17}
$$

左边的 $x^5$ 系数为 $-12(4c^2)^2=-12d^4\ne0$；右边次数至多三。多项式不可能在开区间相等，矛盾。平方只作为必要条件使用，未由平方后等式反推原根式，故没有符号分支遗漏。

此排除适用于每个 $d\in(0,1)$，包括 (70.13) 的两根合并情形；没有将特定 $d$ 或一小段参数区间代替全域。引理 64.1–67.1 已从一般实 CP 合同导出这一正交模型，故所有 $m\le5$ 都被排除。与既有 (60.6) 的六维上界合用，得 (62.1)。∎

## 71. 条件综合、供应工具与剩余问题

**定义 71.1（本源综合的数学归属）。** 定理 62.1 及其原对象对应属于 `repo-derived` 的源特定综合，不主张全域新颖性或优先权。承重差额是：从原完整联合表的可达公平性，经过全矩阵紧 CP 半群、抽象完全序收缩的实表示成本及原 TP 和，约化所有隐藏实五维模型；再以原 $\mathcal K_d$ 的实际纯曲线，排除所有仿射制备及合法效果。命题 60.3 的指定编码失败仍只是其原限制结论，不能代替这一全称排除。

原供应分别为：定义 54.1 和第一卷定理 35.4 的完整集合与原域提升；假设 54.2 和第二卷定理 39.3–39.4 的原标签、两终端与全部联合权重；第二卷定理 40.1 的 $I_3$ 加八个实际词效果；以及 (60.6) 的成熟六维实化上界。它们在证明中按这些接口被消费，没有作为新的独立结果重述。

成熟中间工具包括紧矩阵群的回归、紧半群最小秩角群、Haar 平均、闭子群与 Lie 代数提升、实 $SU(2)$ 表示分类、CP Schwarz 与乘法域、Choi–Effros 乘法以及有限维实 $C^*$ 结构。Prunaru 定理 1 的三个假设在 (65.6) 的复化上满足；Rosenberg 的三种实不可约类型给 (66.4) 的参数成本；Hall 的实 Schur 及闭矩阵群条件分别用于 (69.2) 和 (63.3)。这些是中间供应，不是本源所发明的工具。表示成本使用抽象 $r$ 的乘法域；较小支持只先用于角群；原分支的逐支 TP 只在全支持及原 TP 和共同给出后成立。

**定义 71.2（等式的适用边界）。** 定理 62.1 精确解决定义 61.3 所列的非例外角度实维数部分；定理 60.1 的旧界仍为其成立的弱推论。它没有确定例外角度 $d>2/3$ 的经典最小状态数，没有给定理 56.1 的固定噪声或有限样本记忆增长律，没有提供完整集合的无限状态经典构造，也没有解决第一卷定义 38.3 的原全参数最小最大中心。端点 $d=0,1$、非仿射制备、近似表及不同操作菜单不在此等式的量词内。

本合同以复 Hilbert 空间、Born 概率、原 CPTP 通道及仪器组合为前提，比较者还以实 Kraus CP、一个全族仿射制备和一个合法固定效果为前提。真实 $SU(2)$、逆、角群及 Haar 平均都是由精确表导出的数学约束，没有获得任意控制、选支、独立副本、相位参考或环境访问。精确表等式也不等同于有限样本已经取得这些概率。因此实维数六的必要性并不从信息守恒、共同整体来源或确定到不确定的层级本身导出量子原则；物理起源与取得这些结构的桥梁仍需各自的模型及证据。

## 追加锚（本行以下为增补区）

## 72. 有限完整记录的加权误差与任意正比较器

**定义 72.1（相同原对象上的有限比较）。** 沿用定义 54.1、假设 54.2 的全部复相容集合、五维仪器和固定终端测量。特别地，初始域仍为

$$
\begin{split}
\mathcal K_d=\{\rho=A+D:\;&A,D\succeq0,\quad D\ell=0,\quad
\operatorname{Tr}\rho=1,\\
&a^\dagger Aa=d,\quad \operatorname{Tr}(C\rho)=d,\quad
\operatorname{Tr}(E\rho)=e_d\},\qquad 0<d<1,
\end{split}
\tag{72.1}
$$

其中 $C=2\xi\xi^\dagger$、$e_d=(6-5d)/16$，各向量及矩阵取 (54.1)，不限制为实态或纯态。对每个 $\rho$，第一卷定理 35.4 供应原域 $T\in\mathcal F_{\sqrt d}$，其后继为 (54.6) 的 $S_\rho$。第二卷定理 39.3–39.4 供应实际五维桥

$$
\begin{gathered}
h=(j_1,\ldots,j_n),\quad
A_h=A_{j_n}\cdots A_{j_1},\quad V_h=V_{j_n}\cdots V_{j_1},\\
V_0=Ue^{\mathrm i\theta W},\quad V_1=V_0W,\quad
A_hB=2^{-n/2}BV_h,\quad M_h=V_h^\dagger EV_h,\\
p_\rho(h,1)=2^{-n}\operatorname{Tr}(\rho M_h),\qquad
p_\rho(h,0)=2^{-n}[1-\operatorname{Tr}(\rho M_h)].
\end{gathered}
\tag{72.2}
$$

最左字母最早作用；空词取单位矩阵。概率表可以理解为在 $B\rho B^\dagger$ 上执行原仪器，也可以理解为原输入 $ff^\dagger$ 经 $S_\rho$ 后执行同一仪器。两种终端结果和全部历史均保留；每个历史的总质量是 $2^{-n}$。

令 $\mathcal D\subseteq\mathcal K_d$ 非空。一个 $k\ge1$ 状态比较器 $q$ 取固定的

$$
T_0,T_1\in\mathbb R_+^{k\times k},\qquad
\mathbf1^{\mathsf T}(T_0+T_1)=\mathbf1^{\mathsf T},\qquad
f_{\rm cl}\in[0,1]^k,
\tag{72.3}
$$

以及任意函数 $\rho\mapsto p(\rho)\in\Delta_{k-1}$，并置

$$
\begin{aligned}
q_\rho(h,1)&=f_{\rm cl}^{\mathsf T}T_hp(\rho),\\
q_\rho(h,0)&=(\mathbf1-f_{\rm cl})^{\mathsf T}T_hp(\rho),
\qquad T_h=T_{j_n}\cdots T_{j_1}.
\end{aligned}
\tag{72.4}
$$

对整数 $H\ge0$，定义实际完整记录误差

$$
\Delta_H(\mathcal D;q)
=\sup_{\rho\in\mathcal D}\ \max_{0\le n\le H}
\frac12\sum_{h\in\{0,1\}^n}\sum_{b=0}^1
|p_\rho(h,b)-q_\rho(h,b)|.
\tag{72.5}
$$

记 $k_{\mathcal D}(H,\varepsilon)$ 为满足 $\Delta_H\le\varepsilon$ 的最小正整数状态数，没有有限比较器时为 $\infty$；$k(H,\varepsilon)$ 专指 $\mathcal D=\mathcal K_d$。角度及 $d$ 在这些记号中固定。

这里不要求制备函数仿射，不要求隐藏状态逐支公平、最小、可达、可观察或不可约。只有分支和列随机；单独的 $2T_0$ 或 $2T_1$ 不预设随机性。固定矩阵和效果必须同时用于全部深度与全部 $\rho$。在每个深度，两张完整表都是概率分布：对经典表求和使用 $\mathbf1^{\mathsf T}(T_0+T_1)^n p=1$。

后文使用 TV 的标准事件不等式在本源上的对应。若 $\rho_+,\rho_-\in\mathcal D$ 且 $\Delta_H(\mathcal D;q)\le\varepsilon$，则对每个 $0\le n\le H$，令 $p_\pm=p(\rho_\pm)$，有

$$
\begin{aligned}
|\mathbf1^{\mathsf T}T_0^np_\pm-2^{-n}|&\le\varepsilon,\\
|f_{\rm cl}^{\mathsf T}T_0^np_\pm-p_{\rho_\pm}(0^n,1)|&\le\varepsilon,\\
|f_{\rm cl}^{\mathsf T}T_0^n(p_+-p_-)
 -[p_{\rho_+}(0^n,1)-p_{\rho_-}(0^n,1)]|&\le2\varepsilon.
\end{aligned}
\tag{72.6}
$$

证明。两个归一化概率分布的任一事件概率差不超过它们的 TV。第一行的事件是“全部标签为零”，包含两个终端结果；第二行是其中终端为是的联合事件。分别对两个制备使用第二行，再取差，得第三行。这些界没有除以 $2^{-n}$；归一化稀有词会把绝对误差放大，不能保留同一个 $\varepsilon$。∎

## 73. 一个有显式余量的原域双世界及其四阶递推

**定理 73.1（实际见证的统一半径与正号对比）。** 在 (55.2) 的严格相容点取

$$
\begin{gathered}
\eta=\frac{d(1-d)}{100},\qquad t=\frac\eta{16}
 =\frac{d(1-d)}{1600},\\
\rho_*=
\begin{pmatrix}
d+\eta&-\eta&4\eta/\sqrt6\\
-\eta&\eta&0\\
4\eta/\sqrt6&0&1-d-2\eta
\end{pmatrix}_{(a,h_{\rm out},g)},\\
D_0=\mathrm i(\xi e^\dagger-e\xi^\dagger),\qquad
\rho_\pm=\rho_*\pm tD_0.
\end{gathered}
\tag{73.1}
$$

这里 $t$ 是双世界的扰动幅度，不是第一卷原通道参数 $\sqrt d$。两个世界属于引理 55.1 已有的见证线段，均严格满足完整复 $\mathcal K_d$ 的条件，并有原五维通道提升。

置 $\zeta=e^{-2\mathrm i\theta}$、$c=\cos(2\theta)$、$s_\theta=\sin(2\theta)$，以及

$$
B_\zeta=
\begin{pmatrix}-1/2&\sqrt3\zeta/2\\\sqrt3/2&\zeta/2\end{pmatrix},
\qquad u_n=\Im(B_\zeta^n)_{11}.
\tag{73.2}
$$

实际加权终端对比恰为

$$
a_n:=p_{\rho_+}(0^n,1)-p_{\rho_-}(0^n,1)
=2t\,2^{-n}u_n.
\tag{73.3}
$$

其符号为正的 $2t$，补终端结果的对比是 $-a_n$。未加权序列 $u_n$ 的一个首一消去多项式是

$$
Q_\theta(x)=x^4+(1-c)x^3+\frac{1-5c}{2}x^2+(1-c)x+1.
\tag{73.4}
$$

因此 $a_n$ 的相应首一消去多项式是 $Q_\theta(2x)/16$，而不是直接用 $Q_\theta(x)$。

证明。先给严格正性的显式下界。对 $z=(z_a,z_h,z_g)$，用

$$
\begin{aligned}
2\eta|z_a z_h|&\le2\eta|z_a|^2+\frac\eta2|z_h|^2,\\
\frac{8\eta}{\sqrt6}|z_a z_g|
&\le\frac d4|z_a|^2+\frac{32\eta^2}{3d}|z_g|^2
\end{aligned}
\tag{73.5}
$$

估计二次型，得到

$$
z^\dagger\rho_*z\ge
\left(\frac{3d}4-\eta\right)|z_a|^2
+\frac\eta2|z_h|^2
+\left(1-d-2\eta-\frac{32\eta^2}{3d}\right)|z_g|^2
\ge\frac\eta2\|z\|^2.
\tag{73.6}
$$

最后一步只用 $\eta\le d/100$、$\eta\le(1-d)/100$：第三个系数至少为 $(100-2-8/75)\eta>\eta/2$，第一个也大于 $\eta/2$。另由 (54.5)，

$$
\begin{aligned}
\det B_d(\rho_*)&=\frac43\eta\left(\frac d{\sqrt2}-\eta\right),\\
\operatorname{Tr}B_d(\rho_*)&=d(1+\tau/6)+\frac43\eta,
\qquad \tau=3-2\sqrt2.
\end{aligned}
\tag{73.7}
$$

两对角条目正、行列式正，故此二阶块正定。使用 $1/\sqrt2>7/10$、$\tau<1/5$ 及 $\eta\le d/100$，其最小本征值满足

$$
\lambda_{\min}(B_d(\rho_*))
\ge\frac{\det B_d(\rho_*)}{\operatorname{Tr}B_d(\rho_*)}
>\frac{138}{157}\eta>\frac\eta2.
\tag{73.8}
$$

也可直接用 Sylvester 判据表达同一余量。写 $d=x/(1+x)$、$x>0$，则 $\rho_*-\eta I_3/2$ 的三个顺序主子式为

$$
\frac{x(200x+201)}{200(1+x)^2},\qquad
\frac{x^2(200x+197)}{40000(1+x)^4},\qquad
\frac{x^2(117000x^2+235213x+118200)}{24000000(1+x)^6},
\tag{73.9}
$$

均严格正；而

$$
\det(B_d(\rho_*)-\eta I_2/2)
=\frac{d^2(1-d)(21d-921+1000\sqrt2)}{120000}>0
\tag{73.10}
$$

且首对角元 $d-\eta/2>0$。这也给两个严格本征值下界。

矩阵 $D_0$ 的范数为一，且在全部实向量上的二次型为零。因此迹、$C,E$ 矩和 $aa$ 人口不变；$s=\rho_{aa}-d=\eta>0$ 不变。$B_d$ 的扰动仅有共轭非对角条目，范数至多 $t$，因为 $a,\ell$ 为单位向量。(73.6)、(73.8) 和 $t=\eta/16$ 保留两个正定条件。引理 55.1 的线段半径是两个最小本征值的较小者的四分之一，至少 $\eta/8$，故本定理的两个端点均在该线段内。

原域提升具体复用 (55.4)–(55.5)：令

$$
\begin{gathered}
L_\rho=\ell^\dagger\rho\ell,\quad
A_{\min,\rho}=\rho\ell\ell^\dagger\rho/L_\rho,\quad
\alpha_\rho=\frac{d-a^\dagger A_{\min,\rho}a}
 {a^\dagger\rho a-a^\dagger A_{\min,\rho}a},\\
A_\rho=(1-\alpha_\rho)A_{\min,\rho}+\alpha_\rho\rho,
\quad D_\rho=\rho-A_\rho,\\
\omega_\rho=D_+^\dagger A_\rho D_++D_-^\dagger D_\rho D_-,\qquad
T_{\omega_\rho}(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega_\rho.
\end{gathered}
\tag{73.11}
$$

其中 $D_\pm:\mathbb C^5\to\mathbb C^3$ 是 (55.5) 的原矩阵。严格条件保证分母正、$0<\alpha_\rho<1$；供应定理给 $T_{\omega_\rho}\in\mathcal F_{\sqrt d}$ 及 $\mathcal GT_{\omega_\rho}=S_\rho$。因此这里的双世界并非只满足部分人口约束的替代态。

在 $(\xi,e,f)$ 基中，$V_0$ 去掉公共相位后是 $1\oplus B_\zeta$，而 $E=(\xi+e)(\xi+e)^\dagger/2$。对任意二阶 $G$，直接配对得

$$
\operatorname{Tr}\bigl[D_0(1\oplus G)^\dagger E(1\oplus G)\bigr]
=\mathrm i(\overline{G_{11}}-G_{11})/2=\Im G_{11}.
\tag{73.12}
$$

取 $G=B_\zeta^n$ 并保留联合权重，得到 (73.3)。由

$$
\det(xI_2-B_\zeta)=x^2+\frac{1-\zeta}{2}x-\zeta,
\qquad
Q_\theta(x)=\det(xI_2-B_\zeta)\det(xI_2-\overline{B_\zeta}),
\tag{73.13}
$$

Cayley–Hamilton 给 (73.4)。为明确随后有限矩阵的全部条目，前七项为

$$
\begin{aligned}
u_0&=u_1=0,\qquad u_2=-3s_\theta/4,\\
u_3&=3(1-c)s_\theta/4,\\
u_4&=-3(1+c+2c^2)s_\theta/8,\\
u_5&=3(1-c)(c^2+3c+1)s_\theta/4,\\
u_6&=3(-4c^4-14c^3+9c^2-3)s_\theta/16.
\end{aligned}
\tag{73.14}
$$

这些式子也可由 $u_{n+4}+(1-c)u_{n+3}+(1-5c)u_{n+2}/2+(1-c)u_{n+1}+u_n=0$ 逐项得到。∎

## 74. 精确有限终点的线性状态下界

**定理 74.1（只转移全零词质量与对比的有限判据）。** 固定 $0<d<1$、$\sin(2\theta)\ne0$ 及 (73.1) 的两个实际制备。若一个 $k$ 状态比较器满足

$$
\begin{aligned}
\mathbf1^{\mathsf T}T_0^np_\pm&=2^{-n},\\
f_{\rm cl}^{\mathsf T}T_0^n(p_+-p_-)&=a_n
\end{aligned}
\qquad(0\le n\le k+3),
\tag{74.1}
$$

则产生矛盾。这里不要求其他词的匹配，也不声称有限匹配迫使全部无限历史匹配。

证明。令 $A=2T_0$，$\chi_A(x)=\det(xI_k-A)$。Cayley–Hamilton 使序列 $\mathbf1^{\mathsf T}A^np_\pm$ 及 $f_{\rm cl}^{\mathsf T}A^n(p_+-p_-)$ 均被 $\chi_A$ 消去。因常数序列被 $x-1$ 消去，质量误差

$$
m_n^\pm=\mathbf1^{\mathsf T}A^np_\pm-1
\tag{74.2}
$$

被首一多项式 $\chi_A(x)(x-1)$ 消去，其次数为 $k+1$。(74.1) 给 $m_0^\pm,\ldots,m_k^\pm=0$，恰足以用首一递推向前推出全部 $m_n^\pm=0$。

同理，(73.4) 使对比误差

$$
z_n=f_{\rm cl}^{\mathsf T}A^n(p_+-p_-)-2tu_n
\tag{74.3}
$$

被首一多项式 $\chi_A(x)Q_\theta(x)$ 消去，次数为 $k+4$。有限数据恰给 $z_0,\ldots,z_{k+3}=0$，故全部 $z_n=0$。这一步没有把四阶递推误当为 $k$ 阶递推，也没有把加权序列的递推直接用于 $A$。

所得无限恒等式正是定理 55.2 证明中的全零词障碍所需的质量与对比恒等式。该已证障碍只使用这些恒等式：质量使两个制备的可达支持并集上的 $A$ 幂有界；该非负有限矩阵的外围频率为单位根；引理 55.1 的 $u_n$ 有可见的非单位根频率。故 (74.2)–(74.3) 不可能同时恒零。这里直接复用这一障碍，不另作 C1 的全角度分类。∎

**定理 74.2（实际双世界已迫使线性精确界）。** 对每个整数 $H\ge0$，若 $\mathcal D\subseteq\mathcal K_d$ 包含 (73.1) 的两个世界，且 $\sin(2\theta)\ne0$，则

$$
k_{\mathcal D}(H,0)\ge\max\{1,H-2\}.
\tag{74.4}
$$

特别地，原完整复集合的 $k(H,0)$ 满足同一界。

证明。状态数至少为一。若 $H\ge k+3$，精确完整记录匹配会给 (74.1)，违反定理 74.1。因此任一有限匹配模型均有 $k>H-3$，即 $k\ge H-2$。对 $H\le3$ 只保留正整数下界。这将定理 56.1 中未指定的排除终点具体化为 $H(k)\le k+3$；使用的无限正实现障碍仍是 §55 的供应结果。∎

## 75. 不归一化稀有词的四状态噪声证书

**定理 75.1（实际完整 TV 中的四状态障碍）。** 固定 $0<d<1$、$\sin(2\theta)\ne0$，$\mathcal D\subseteq\mathcal K_d$ 包含 (73.1) 的两个世界。若 $H\ge6$ 且

$$
\Delta_H(\mathcal D;q)\le\varepsilon
<\frac{d(1-d)|\sin(2\theta)|}{1638400},
\tag{75.1}
$$

则比较器至少需要四个状态。特别地，在 $\theta=\pi/4$，更强的充分条件为

$$
\varepsilon<\frac{3d(1-d)}{2867200};
\qquad d=1/2\text{ 时为 }\varepsilon<\frac3{11468800}.
\tag{75.2}
$$

证明。保留 (73.3) 的原始联合权重，构造完整四阶 Hankel 矩阵

$$
J=(a_{i+j})_{i,j=0}^3=
\begin{pmatrix}
a_0&a_1&a_2&a_3\\
a_1&a_2&a_3&a_4\\
a_2&a_3&a_4&a_5\\
a_3&a_4&a_5&a_6
\end{pmatrix},\qquad a_n=2t\,2^{-n}u_n.
\tag{75.3}
$$

式 (73.14) 指定了它的每一个条目。代入并展开行列式，得到

$$
\det J=\frac{81t^4s_\theta^4}{65536},\qquad
J^{-1}=\frac{M(c)}{ts_\theta},
\tag{75.4}
$$

其中完整逆矩阵的分子为

$$
M(c)=\frac13
\begin{pmatrix}
2c^2+c+1&10c^2-8c-2&8c^2-16c&16-16c\\
10c^2-8c-2&50c^2-20c-6&40c^2-48c+8&16-80c\\
8c^2-16c&40c^2-48c+8&32(c-1)^2&64(1-c)\\
16-16c&16-80c&64(1-c)&128
\end{pmatrix}.
\tag{75.5}
$$

这些是多项式恒等式：将 (73.14) 代入 $J$，在 (73.4) 的递推下相乘，得 $JM(c)=ts_\theta I_4$；行列式展开给 (75.4)。它们只要求 $s_\theta\ne0$，没有非共振常数或一般位置假设。

对任意经典比较器，令

$$
y_n=f_{\rm cl}^{\mathsf T}T_0^n(p_+-p_-),\qquad
Y=(y_{i+j})_{i,j=0}^3.
\tag{75.6}
$$

矩阵 $Y$ 分解为四行 $f_{\rm cl}^{\mathsf T}T_0^i$ 与四列 $T_0^j(p_+-p_-)$ 的乘积，故 $\operatorname{rank}Y\le k$。式 (72.6) 的事件误差界给 $|y_n-a_n|\le2\varepsilon$，并且 $i+j\le6$，于是

$$
\|J-Y\|_2\le\|J-Y\|_{\rm F}\le8\varepsilon.
\tag{75.7}
$$

对 $|c|\le1$，对 (75.5) 各项的系数绝对值求和，四行依次给

$$
\sum_j|M_{1j}(c)|\le80/3,\quad
\sum_j|M_{2j}(c)|\le96,\quad
\sum_j|M_{3j}(c)|\le376/3,\quad
\sum_j|M_{4j}(c)|\le128.
\tag{75.8}
$$

$M(c)$ 对称，故 $\|J^{-1}\|_1=\|J^{-1}\|_\infty$，从而

$$
\|J^{-1}\|_2\le\|J^{-1}\|_\infty
\le\frac{128}{t|s_\theta|}.
\tag{75.9}
$$

若 $\varepsilon<t|s_\theta|/1024$，则 $\|J^{-1}(Y-J)\|_2<1$，Neumann 逆级数使 $Y$ 可逆。因此 $k\ge4$。代入 $t=d(1-d)/1600$，恰得 (75.1)。

当 $\theta=\pi/4$ 时 $c=0$、$s_\theta=1$，(75.5) 四行的实际绝对值和分别为

$$
19/3,\qquad32/3,\qquad104/3,\qquad224/3.
\tag{75.10}
$$

于是 $\|J^{-1}\|_2\le224/(3t)$，严格条件 $8\varepsilon\cdot224/(3t)<1$ 等价于 $\varepsilon<3t/1792$，给 (75.2)。全程比较的都是实际联合事件；没有把 $a_n$ 除以 $2^{-n}$。这证明一个固定的四状态下界，并不证明在同一个正误差下随 $H$ 发散。∎

## 76. 有理源数据的任意状态数多项式

**定义 76.1（有理坐标子族与全部常数）。** 另加源数据条件

$$
\begin{gathered}
d=u/v,\qquad 0<u<v,\quad \gcd(u,v)=1,\\
\zeta=e^{-2\mathrm i\theta}=(a+\mathrm ib)/C,\quad
 a,b\in\mathbb Z,\quad C\in\mathbb Z_{\ge1},\quad
 a^2+b^2=C^2,\quad b\ne0.
\end{gathered}
\tag{76.1}
$$

这里 $a,b$ 是整数坐标，不是 (54.1) 的基向量或终端结果记号。条件是 $\zeta$ 的两个坐标有理，不是 $\theta/\pi$ 有理。此前的定理 74.2、75.1 没有这一有理性限制。

对每个整数 $k\ge1$，定义

$$
\begin{gathered}
N=k+3,\qquad \nu=k^2+3k,\qquad m=k^2+5k+2,\qquad D=2N+4,\\
Q=800v^2(4C)^N,\qquad
L=32(N+1)Q^2k^{2N+4},\qquad
\widetilde L=\max\{L,2\nu+2m\}.
\end{gathered}
\tag{76.2}
$$

这些都是明确整数；$D$ 为正偶数，$\nu\ge4$。$Q$ 是共同清分母数，不要求是最小公分母。

**定义 76.2（任意比较器的紧参数多面体）。** 取变量

$$
R=(R_{ij})\in\mathbb R^{k\times k},\qquad
f_{\rm cl},p_+,p_-\in\mathbb R^k
\tag{76.3}
$$

及多面体 $\mathcal P_k$，其完整约束为

$$
\begin{gathered}
\sum_i(p_+)_i-1=0,\qquad \sum_i(p_-)_i-1=0,\\
R_{ij}\ge0\ (1\le i,j\le k),\qquad
1-\sum_iR_{ij}\ge0\ (1\le j\le k),\\
(f_{\rm cl})_i\ge0,\quad 1-(f_{\rm cl})_i\ge0,\quad
(p_+)_i\ge0,\quad(p_-)_i\ge0\ (1\le i\le k).
\end{gathered}
\tag{76.4}
$$

有 $k^2+3k=\nu$ 个变量、两个等式和 $k^2+5k$ 个不等式，共 $m$ 个约束多项式，次数及整数系数绝对值均至多一。非负性和列和界使 $R$ 的各项在 $[0,1]$，两个制备为概率向量；效果亦在 $[0,1]^k$。故 $\mathcal P_k$ 非空、闭、有界且凸，是其自身唯一的紧连通分支。等式约束造成的空内部不妨碍这些性质。

每个 (72.3) 的比较器给 $R=T_0$ 及 $\mathcal P_k$ 中一点。反之，每个 $\mathcal P_k$ 中一点都可取

$$
T_0=R,\qquad
T_1=\operatorname{diag}\left(1-\sum_iR_{i1},\ldots,1-\sum_iR_{ik}\right)
\tag{76.5}
$$

完成为合法分支和。因此这一参数域没有加入逐支公平性，也没有删去不可约性失败、不可达状态或隐藏冗余。

在此域上定义实际目标多项式

$$
\begin{split}
g(R,f_{\rm cl},p_+,p_-)=Q^2\sum_{n=0}^N\big[&
 (\mathbf1^{\mathsf T}R^np_+-2^{-n})^2
 +(\mathbf1^{\mathsf T}R^np_--2^{-n})^2\\
 &+(f_{\rm cl}^{\mathsf T}R^n(p_+-p_-)-a_n)^2\big],
\end{split}
\tag{76.6}
$$

其中 $a_n$ 是同一实际双世界 (73.1) 的加权对比，$R^0=I_k$。

## 77. 源分母、减去目标后的高度与严格正最小值

**定理 77.1（实际目标的整数性、次数和系数界）。** 在 (76.1)–(76.6) 下，$g$ 为 $\nu$ 变量整数多项式，次数恰为 $D$，每个系数的绝对值严格小于 $L$，并且

$$
g_*:=\min_{\mathcal P_k}g>0.
\tag{77.1}
$$

证明。令 $b_n=(B_\zeta^n)_{11}$。二阶特征多项式给

$$
b_0=1,\qquad b_1=-1/2,\qquad
b_n=\frac{\zeta-1}{2}b_{n-1}+\zeta b_{n-2}\quad(n\ge2).
\tag{77.2}
$$

由归纳 $(2C)^nb_n\in\mathbb Z[\mathrm i]$。特别地，$u_n=\Im b_n$ 为有理数，分母整除 $(2C)^n$。又

$$
2t=\frac{u(v-u)}{800v^2},\qquad
 a_n=\frac{u(v-u)}{800v^2}\,2^{-n}\Im b_n,
\tag{77.3}
$$

故 $a_n$ 的分母整除 $800v^2(4C)^n$；$Q$ 对全部 $0\le n\le N$ 同时清除它们和 $2^{-n}$ 的分母。尽管 $B_\zeta$ 含 $\sqrt3$，实际所需的对角元通过 (77.2) 没有引入该无理数。每个 $Q$ 倍残差均为整数多项式，因此 (76.6) 是整数多项式。

写 $\|P\|_{\rm coeff,1}$ 为多项式全部系数绝对值之和。尚未减去目标的预测多项式满足

$$
\begin{aligned}
\|\mathbf1^{\mathsf T}R^np_\pm\|_{\rm coeff,1}&\le k^{n+1},\\
\|f_{\rm cl}^{\mathsf T}R^n(p_+-p_-)\|_{\rm coeff,1}&\le2k^{n+2}.
\end{aligned}
\tag{77.4}
$$

前者由 $n$ 次转移的路径求和计数，后者还保留效果变量和两个制备的符号；重复单项式合并不会增大系数绝对值之和。由于 $|2^{-n}|\le1$、$|a_n|\le1$，减去目标以后必须使用

$$
\begin{aligned}
\|\mathbf1^{\mathsf T}R^np_\pm-2^{-n}\|_{\rm coeff,1}&\le2k^{n+1},\\
\|f_{\rm cl}^{\mathsf T}R^n(p_+-p_-)-a_n\|_{\rm coeff,1}&\le3k^{n+2}.
\end{aligned}
\tag{77.5}
$$

未减目标的 (77.4) 不能直接充当残差界。系数范数的次乘性于是给

$$
\begin{aligned}
\|g\|_{\rm coeff,1}
&\le Q^2\sum_{n=0}^N
 \big[8k^{2n+2}+9k^{2n+4}\big]\\
&\le17(N+1)Q^2k^{2N+4}<L.
\end{aligned}
\tag{77.6}
$$

这逐项控制整数系数高度，包括 $k=1$。质量残差次数至多 $n+1$，对比残差次数至多 $n+2$，所以 $\deg g\le2N+4=D$。在 $n=N$ 的对比中，最高次齐次多项式 $f_{\rm cl}^{\mathsf T}R^N(p_+-p_-)$ 非零；它的平方是 (76.6) 中唯一次数 $2N+4$ 的项，故次数实际等于 $D$。这里的次数是环境变量多项式的次数，不是在等式约束商环中约去变量后的次数。

若 $g$ 在 $\mathcal P_k$ 上有零点，平方和迫使 $0\le n\le k+3$ 的两个质量及对比残差同时为零。使用 (76.5) 完成分支，便得到定理 74.1 所排除的 (74.1)。所以处处 $g>0$；紧性和连续性给正的达到最小值 (77.1)。这个论证没有用其他历史的零误差，也没有要求制备来自任何仿射映射。∎

## 78. 任意状态数的显式消失误差下界

**定理 78.1（有理数据的实际完整记录阈值）。** 固定 (76.1) 的源数据，对每个 $k\ge1$ 定义

$$
\varepsilon_k=
\frac{(16\widetilde L D^\nu)^{-\nu 2^{\nu-1}D^\nu}}
 {Q\sqrt{6(N+1)}},
\tag{78.1}
$$

全部常数取 (76.2)。若 $\mathcal D\subseteq\mathcal K_d$ 包含 (73.1) 的双世界，且

$$
H\ge k+3,\qquad
\Delta_H(\mathcal D;q)\le\varepsilon<\varepsilon_k,
\tag{78.2}
$$

则比较器不能只有至多 $k$ 个状态。因而对全部整数 $H\ge0$，

$$
k_{\mathcal D}(H,\varepsilon)\ge
1+\max\left(\{k\in\mathbb Z:1\le k\le H-3,\quad
 \varepsilon<\varepsilon_k\}\cup\{0\}\right).
\tag{78.3}
$$

证明。这里作为中间工具使用 Jeronimo–Perrucci–Tsigaridas，[*On the minimum of a polynomial function on a basic closed semialgebraic set and applications*](https://arxiv.org/html/1112.0544v1)，Theorem 1。其原定理的条件是：$n$ 变量整数约束多项式定义的基本闭半代数集，一个紧连通分支 $\mathscr C$，全部约束次数由正偶数 $d_{\rm J}$ 控制、系数绝对值由 $H_{\rm J}$ 控制；整数目标的次数 $d_0\le d_{\rm J}$、高度 $H_0\le H_{\rm J}$。若目标在 $\mathscr C$ 上的最小值非零，其绝对值至少为

$$
\left(2^{4-n/2}\max\{H_{\rm J},2n+2m_{\rm J}\}
 d_{\rm J}^{\,n}\right)^{-n2^n d_{\rm J}^{\,n}},
\tag{78.4}
$$

并且该最小值的代数次数至多 $2^{n-1}d_{\rm J}^{\,n}$。$m_{\rm J}$ 计等式与不等式的总数。此定理不要求紧连通分支有内部，不要求约束正则或极小点孤立。

在本源中的逐项对应为

$$
\begin{gathered}
n=\nu,\qquad m_{\rm J}=m,\qquad d_{\rm J}=D,\qquad
H_{\rm J}=L,\qquad d_0=D,\quad H_0<L,\\
\mathscr C=\mathcal P_k,\qquad \text{目标}=g,\qquad
\min_{\mathscr C}g=g_*>0.
\end{gathered}
\tag{78.5}
$$

定义 76.2 给整数、次数一、高度一的全部 $m$ 个约束，及整个域的唯一紧连通分支；定理 77.1 给目标整数性、次数、高度及非零最小值。因此没有把只在数值样本上为正当作定理的非零前提。由于 $2^{4-\nu/2}\le16$，用更大的底数弱化 (78.4)，得到

$$
g_*\ge(16\widetilde L D^\nu)^{-\nu2^\nu D^\nu}.
\tag{78.6}
$$

另一方面，假设有 $k$ 状态比较器满足 (78.2)，取 $R=T_0$ 及它的两个实际制备。式 (72.6) 的事件误差界给每个质量残差至多 $\varepsilon$、对比残差至多 $2\varepsilon$，故

$$
g\le Q^2(N+1)(\varepsilon^2+\varepsilon^2+4\varepsilon^2)
=6Q^2(N+1)\varepsilon^2.
\tag{78.7}
$$

由 (78.1) 的严格不等式，(78.7) 小于 (78.6)，矛盾。较少状态的模型可补上零制备、互不相连的隐藏状态，使总状态数为 $k$；给新增状态任选合法分支和效果不会改变记录。因此排除涵盖“至多 $k$”，再取最大值即得 (78.3)。阈值处的等号没有被排除。∎

**定理 78.2（仅在固定有理源数据下的误差反演）。** 固定 (76.1) 中的 $u,v,a,b,C$，令 $k\to\infty$，则 (78.1) 满足

$$
\log\log(1/\varepsilon_k)=\Theta(k^2\log k).
\tag{78.8}
$$

因此存在仅依赖这些固定数据的 $c_0>0$，使充分小的 $\varepsilon>0$ 对应

$$
K(\varepsilon)=\left\lfloor c_0
\sqrt{\frac{\log\log(1/\varepsilon)}
 {\log\log\log(1/\varepsilon)}}\right\rfloor\ge1,
\tag{78.9}
$$

且在 $H\ge K(\varepsilon)+3$ 时，
$k_{\mathcal D}(H,\varepsilon)\ge K(\varepsilon)+1$。

证明。写 $B_k=16\widetilde L D^\nu$ 和 $E_k=\nu2^{\nu-1}D^\nu$，则

$$
\log(1/\varepsilon_k)
=E_k\log B_k+\log Q+\tfrac12\log(6(N+1)).
\tag{78.10}
$$

固定数据给 $\log Q=O(k)$、$\log L=\Theta(k\log k)$，且充分大时 $\widetilde L=L$。又 $\nu=\Theta(k^2)$、$D=\Theta(k)$，所以 $\log B_k=\Theta(k^2\log k)$，而

$$
\log E_k=\log\nu+(\nu-1)\log2+\nu\log D
=\Theta(k^2\log k).
\tag{78.11}
$$

在 (78.10) 再取对数即得 (78.8)。用其上界选取充分小的常数 $c_0$，使 $k=K(\varepsilon)$ 时 $\varepsilon<\varepsilon_k$，再用定理 78.1。这一反演让误差趋零，并要求相应终点足够长；它不是固定正误差下关于 $H$ 的发散定理，也不给一般实角度的统一有效常数。上述双重指数阈值只承担明确的存在与排除量，不承担实用精度或采样成本保证。∎

## 79. 完整相容集合上靠近例外角度的共同小模型

**定理 79.1（原始联合记录的全角度连续上界）。** 对任意 $0<d<1$、任意 $\theta\in\mathbb R$，写

$$
\theta=\theta_*+\delta,\qquad \theta_*=m\pi/2,\quad m\in\mathbb Z.
\tag{79.1}
$$

用定理 57.1 在例外角度 $\theta_*$ 的同一个全 $\mathcal K_d$ 模型作为比较器 $q^{(*)}$，则其状态数为三（$d\le2/3$）或六（$d>2/3$），并且对全部整数 $H\ge0$，

$$
\Delta_H(\mathcal K_d;q^{(*)})
\le\min\{1,2H|\sin(\delta/2)|\}
\le\min\{1,H|\delta|\}.
\tag{79.2}
$$

这些分支、效果和全族制备固定，既不随终点改变，也不按实际随机词选择。

证明。先具体指定所复用的比较器。置 $\Sigma=(6+3d)/8$、$s_\rho=\rho_{aa}-d$ 和

$$
b(\rho)=(e_d,d+s_\rho,e_d-s_\rho)^{\mathsf T},\qquad
P_0b=(b_2,b_1,b_3)^{\mathsf T},\quad
P_1b=(b_3,b_1,b_2)^{\mathsf T}.
\tag{79.3}
$$

当 $d\le2/3$ 时，取

$$
p^{(*)}(\rho)=b(\rho)/\Sigma,\qquad
f_{\rm cl}^{(*)}=(\Sigma,0,0)^{\mathsf T},\qquad
T_0^{(*)}=P_0/2,\quad T_1^{(*)}=P_1/2.
\tag{79.4}
$$

当 $m$ 为奇数时交换两个标签；偶数时不交换。定理 57.1 保证这是全部复 $\mathcal K_d$ 上的合法仿射制备与固定效果，并精确匹配 $\theta_*$ 的两种终端联合记录。

当 $d>2/3$ 时，使用该定理的六顶点构造：顶点是 $(1,\Sigma-1,0)$ 的全部置换，动态是 (79.3) 在这些顶点上诱导的两个置换各乘 $1/2$，效果为顶点的第一坐标。为 $s_\rho$ 的可行区间 $[0,s_{\max}]$ 的两个端点各固定一个顶点凸分解，再按 $s_\rho/s_{\max}$ 插值其权重，得到整个 $\mathcal K_d$ 上同一个仿射制备。奇数 $m$ 同样交换标签。此处只复用合法上构造，不断言六状态最小。

现在比较两角度的实际酉。对 $j=0,1$，

$$
\|V_j(\theta)-V_j(\theta_*)\|_{\rm op}
=\|e^{\mathrm i\delta W}-I_3\|_{\rm op}
=2|\sin(\delta/2)|.
\tag{79.5}
$$

长度 $n$ 的相同时间词逐项望远镜展开，所有其他因子均酉，故

$$
\|V_h(\theta)-V_h(\theta_*)\|_{\rm op}
\le2n|\sin(\delta/2)|.
\tag{79.6}
$$

对任意密度 $\rho$ 和两个酉 $V,V'$，由二元测量的迹距离收缩及乘积差展开，

$$
\begin{aligned}
|\operatorname{Tr}(E[V\rho V^\dagger-V'\rho(V')^\dagger])|
&\le\tfrac12\|V\rho V^\dagger-V'\rho(V')^\dagger\|_1\\
&\le\|V-V'\|_{\rm op}.
\end{aligned}
\tag{79.7}
$$

每个词的两个概率差互为负数，两角度的词质量又都为 $2^{-n}$，所以完整 TV 恰为

$$
\begin{split}
&\frac12\sum_{h,b}|p_\rho^{(\theta)}(h,b)
 -q_\rho^{(*)}(h,b)|\\
&\quad=2^{-n}\sum_{h\in\{0,1\}^n}
|\operatorname{Tr}(E[V_h(\theta)\rho V_h(\theta)^\dagger
 -V_h(\theta_*)\rho V_h(\theta_*)^\dagger])|\\
&\quad\le\min\{1,2n|\sin(\delta/2)|\}.
\end{split}
\tag{79.8}
$$

这是均匀平均而非对某个稀有词的条件化。对 $\rho$ 和 $n\le H$ 取上确界，得到 (79.2)。选择另一个例外角度或改变 $\delta$ 的正负都不改变证明；比较器始终使用其规定的标签交换。∎

**定理 79.2（正误差不能照搬原线性精确界）。** 对实际源

$$
d=1/2,\qquad \theta=10^{-6},\qquad H=10000,
\tag{79.9}
$$

存在一个在整个复 $\mathcal K_{1/2}$ 上共同的三状态比较器，使 $\Delta_H\le0.01$，而精确匹配至少需要 $9998$ 个状态。

证明。在定理 79.1 取 $\theta_*=0$，则 $H|\delta|=0.01$。其三状态模型对整个相容集合合法。实际角度满足 $\sin(2\theta)\ne0$，定理 74.2 给 $H-2=9998$。这是解析上界与精确下界的同一实例。该例排除将 (74.4) 在所有非例外角度上原样搬到正误差；它不给这个固定非零角度下同一小误差的全 $H$ 有界模型。∎

## 80. 对全部终点统一的一状态大误差上界

**定理 80.1（完整复集合上的共同常数预测）。** 对任意实角度、任意 $0<d<1$，置

$$
r=d/2,\qquad
U_d=\frac12+\sqrt{r(1-r)}
=\frac12+\sqrt{(d/2)(1-d/2)}.
\tag{80.1}
$$

共同的一状态模型

$$
T_0=T_1=1/2,\qquad p(\rho)=1,\qquad f_{\rm cl}=U_d/2
\tag{80.2}
$$

满足

$$
\sup_{H\ge0}\Delta_H(\mathcal K_d;q)
\le\frac{U_d}{2}
=\frac14+\frac12\sqrt{(d/2)(1-d/2)}<\frac12.
\tag{80.3}
$$

证明。由 $C=2\xi\xi^\dagger$ 和 (72.1)，每个初始态的 $\xi$ 人口恰为 $r$。又 $V_j\xi=e^{\mathrm i\theta}\xi$，所以每个词后的归一化数学态 $\rho_h=V_h\rho V_h^\dagger$ 仍有相同人口。写 $x_h=e^\dagger\rho_he$，则

$$
0\le x_h\le1-r,\qquad
|\xi^\dagger\rho_he|\le\sqrt{rx_h}
\tag{80.4}
$$

来自迹一和正的二阶主子块。因此

$$
\begin{aligned}
0\le\operatorname{Tr}(\rho_h E)
&=\tfrac12\big[r+x_h+2\Re(\xi^\dagger\rho_he)\big]\\
&\le\tfrac12+\sqrt{r(1-r)}=U_d.
\end{aligned}
\tag{80.5}
$$

一状态模型同样保留每词 $2^{-|h|}$ 的质量，且终端是的条件参数恒为 $U_d/2$。区间 $[0,U_d]$ 中任意数与其中点相差至多 $U_d/2$；对全部词按原权重平均，得到每深度 TV 的同一界，因而得到 (80.3)。最后 $0<r<1/2$ 使 $\sqrt{r(1-r)}<1/2$。

这是仅在相对大误差区间 $\varepsilon\ge U_d/2$ 供应的全终点模型。它否定“每一个正误差都必迫使状态数发散”这一全称断言；它不解决比该区间小的一个固定正误差。∎

## 81. 有限精度结论的量词、文献接口与物理前提

**定义 81.1（同一源上的结论域）。** 定理 74.2 对全部非例外角度给精确有限终点的线性下界；定理 75.1 对同一全部角度给实际加权 TV 中的四状态严格阈值；定理 78.1 在有理坐标条件 (76.1) 下给任意 $k$ 的明确正阈值，定理 78.2 的反演固定这些有理数据并让误差趋零。定理 79.1、80.1 则对全部角度和完整复 $\mathcal K_d$ 给共同模型上界。这些陈述的 $T_j,f_{\rm cl}$ 均在各自模型内固定；下界允许任意制备函数，上界恰好具有共同仿射制备。

特别地，固定某个 $\sin(2\theta)\ne0$，再固定一个小正数 $\varepsilon$，是否有

$$
\lim_{H\to\infty}k(H,\varepsilon)=\infty,
\quad\text{或存在 }k<\infty\text{ 及同一个 }q
\text{ 使 }\sup_H\Delta_H(\mathcal K_d;q)\le\varepsilon,
\tag{81.1}
$$

在上述小误差范围内仍未确定。这里“小误差范围”指没有被 (80.3) 的大误差模型直接覆盖的正误差；四状态排除并不排除更大的固定状态数。(78.1) 随 $k$ 缩小，不能把“每个 $k$ 存在正阈值”交换成“存在一个正阈值适用于全部 $k$”。(79.2) 对固定非零 $\delta$ 随 $H$ 增长，不能交换成对全部 $H$ 的同一小误差。精确递推转移 (74.1) 也不能在正误差下任意放大稀有事件。

**定义 81.2（成熟工具与源特定对应）。** 本增补的 `repo-derived` 内容是：(73.1) 在真实原纤维中的明确半径与加权对比，(74.1) 的有限转移终点，(75.3)–(75.10) 的实际有限矩阵证书，(76.4)–(78.7) 对有理源数据的整数优化对应，以及 (79.2)、(80.3) 的同一全复相容集合上界。Cayley–Hamilton、有限序列的 Hankel 分解、矩阵逆扰动、紧性、迹距离收缩及多项式最小值下界均是成熟工具，不以其一般定理为本源的新结果，也不作文献优先权主张。

源接口的对应为：第一卷 §17.1 固定原五维 $K_j$、$U,W,E$；第一卷定理 35.2、35.4、35.6 供应全部复输入上的后继约化、忠实 $\mathcal K_d$ 与五维 CPTP 提升；第二卷定理 39.3–39.4 供应时间词、全部原始联合权重和两种终端结果；第二卷定理 42.4 与本卷引理 55.1 供应严格见证点及其可见对比；定理 55.2 证明中的正实现障碍只在 §74 所列两个无限恒等式处调用；定理 57.1 供应 §79 的共同例外模型。§§62–71 的实实现结论不参与这些有限经典误差界。

Jeronimo–Perrucci–Tsigaridas 的上述 Theorem 1 是 `literature-attested` 的有效实代数中间工具，完整参数对应为 (78.5)，不是仅凭“半代数”一词借用其结论。§55 已引用的 Monras–Winter 与 Fanizza–Lumbreras–Winter 供应正实现及外围谱方法；后者 Theorem 6 对其 FRDN 动态加入指定退极化混合，并在变化角度上给精确实现的最坏情形界。改变后的精确过程不是本源固定过程的有限完整 TV 邻域，故其噪声参数不直接成为本卷的 $\varepsilon$。

其他鲁棒性工具与本源的对应条件也须明确。[arXiv:2608.23669v1](https://arxiv.org/html/2608.23669v1) 的 Result 11 使用素数模数 $p$ 的承诺分类、每个类中选取的单一一元代表词，以及长度 $np$ 的随机填充，其分布为 $\alpha(1-\alpha)^n$。在该输入分布下，少于 $p$ 个状态的经典代理损失至少为 $1-1/K-\epsilon_{\mathcal A}(\alpha)$，其中 $\epsilon_{\mathcal A}(\alpha)\to0$ 随 $\alpha\to0$，收敛依赖代理。选定代表词、填充分布和分类终端不是 (72.2) 的固定独立公平二元标签及 Born 终端；没有这些接口的已证映射，不能把该损失界直接换成 (72.5)。

[*Approximation of stationary processes by Hidden Markov Models*](https://arxiv.org/html/math/0606591) 的 Theorem 4.2 假设两个输出过程平稳、候选过程 $Q$ 的每个有限块相对于 HMM 过程 $P$ 绝对连续、存在所述不变测度，并满足几何遍历条件，结论为有限 KL 散度率的存在。本源的制备索引终端实验没有被这些假设识别为该平稳过程；即使另给识别，每时间 KL 率也不自行给各深度最大 TV。静态 Hankel 分解的存在又不自行给同一组动态矩阵。

[*Some upper and lower bounds on PSD-rank*](https://arxiv.org/html/1407.4308v1) 的 Theorem 43 对非负 $n\times n$ 表要求对角元恰为一、非对角元至多 $\gamma$，得到 psd 秩至少 $n/[1+\gamma(n-1)]$。用于本源前，需从实际联合事件得到这种近单位表，并证明原始误差如何进入它；对稀有词作行列放大不保持 (72.5)。本卷的 (75.3) 是直接保留权重的对比矩阵，使用的是普通秩分解和显式逆，而不是借用一个尚未构造的近单位非负表。

[*On the Spectral Region of n-Cycle Stochastic Matrices*](https://arxiv.org/html/2606.10143v2) 的 Theorem 1.1 分类的是支持于单一有向 $n$ 圈并允许自环、各圈边严格为正的行随机矩阵。本源允许任意可约正比较器，$2T_0$ 本身甚至不预设随机性；该支撑类的谱区域不能替代这些比较器的通用有限误差界。

[arXiv:2411.15724v1](https://arxiv.org/html/2411.15724v1) 的 Theorem 1.1 使用整数独立同分布增量、满足全部 $q\ge1$ 上 $\|q\alpha\|\ge C_0q^{-\gamma}$ 的无理 $\alpha$，以及特征函数在零邻域的下界 $|1-\varphi(x)|\ge c_0|x|^\beta$，其中 $\gamma\ge1$、$C_0,c_0>0$、$0<\beta\le2$；它控制 $1\le p<\infty$ 的圆上经验测度期望 Wasserstein 距离。本源未供应相应本征相位的这些常数，二元非交换词也没有被识别为该可交换圆游走；Wasserstein 距离更不是完整记录 TV。这些成熟结果的条件及指标不能仅由无理性或正实现术语省略。

**假设 81.3（概率、取得与量子结构的分层）。** 全部比较以 (72.2) 的概率函数和完整相容集合为数学对象，沿用原合同实际供应的环境就绪、重复仪器、固定测量及丢弃规则。对整个集合取上确界，或在证明中取两个指定端点，不授予制备这些态、独立重复这些制备、取得副本、改变角度、插入控制、读取环境、选支或取得精确实概率的操作权。若另行供应独立重复制备与相应终端实验，有限事件概率才可在该额外采样模型内讨论统计估计；现有 TV 阈值本身不是样本数或置信度结论。

复 Hilbert 空间、Born 配对、CP 分支、CPTP 组合及五维物理提升均为这些条件定理的前提。完整预测表中的正实现障碍说明在这些前提下某些有限经典表示不足，并未从信息守恒、共同整体来源或确定到不确定的连续层级推出 Hilbert、Born 或 CP 原则。原擦除标签菜单的全参数最小最大问题、实际资源取得与量子结构的物理起源均保持其各自的问题域。

## 追加锚（本行以下为增补区）

