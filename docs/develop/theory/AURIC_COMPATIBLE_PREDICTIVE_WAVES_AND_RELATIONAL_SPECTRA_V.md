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

**定理 78.2（仅在固定有理源数据下的误差反演）。** 沿用定理 78.1 的全部源数据与制备域假设：固定满足 (76.1) 的 $u,v,a,b,C$，并令 $\mathcal D\subseteq\mathcal K_d$ 包含 (73.1) 的两个实际制备 $\rho_+,\rho_-$。令 $k\to\infty$，则 (78.1) 满足

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
$k_{\mathcal D}(H,\varepsilon)\ge K(\varepsilon)+1$。特别地，完整复集合 $\mathcal D=\mathcal K_d$ 满足这一制备域条件。

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

在 (78.10) 再取对数即得 (78.8)。用其上界选取充分小的常数 $c_0$，使 $k=K(\varepsilon)$ 时 $\varepsilon<\varepsilon_k$，再用定理 78.1。这一反演在上述包含双世界的制备域上让误差趋零，并要求相应终点足够长；它不是固定正误差下关于 $H$ 的发散定理，也不给一般实角度的统一有效常数。上述双重指数阈值只承担明确的存在与排除量，不承担实用精度或采样成本保证。∎

**命题 78.3（非空制备域的平稳边界）。** 在 $d=2/7$、$\theta=\pi/4$ 时，存在合法的非空制备域 $\mathcal D_{\rm st}\subseteq\mathcal K_{2/7}$，其全部有限终点的完整联合记录由同一个一状态比较器精确实现，且对每个整数 $H\ge0$、每个 $\varepsilon\ge0$ 均有 $k_{\mathcal D_{\rm st}}(H,\varepsilon)=1$。

证明。取 $d=2/7$、$\theta=\pi/4$，其 (76.1) 的整数数据为 $(u,v,a,b,C)=(2,7,0,-1,1)$。置

$$
\rho_{\rm st}=\frac{\xi\xi^\dagger+3ee^\dagger+3ff^\dagger}{7}
=\frac37 I_3-\frac27\xi\xi^\dagger.
$$

其本征值为 $1/7,3/7,3/7$。取 $A=\rho_{\rm st}$、$D=0$，则 $A,D\succeq0$、$D\ell=0$、$\operatorname{Tr}\rho_{\rm st}=1$。由 (54.1) 的 $a=Uq$、$U\xi=\xi$ 和 $q=(\xi+e)/\sqrt2$，有

$$
a^\dagger Aa=\operatorname{Tr}(C\rho_{\rm st})
=\operatorname{Tr}(E\rho_{\rm st})=\frac27=e_{2/7}.
$$

故 $\rho_{\rm st}$ 属于完整原集合 $\mathcal K_{2/7}$，并由第一卷定理 35.4 具有原五维通道提升。又 $U\xi=W\xi=\xi$，所以 $\rho_{\rm st}$ 与 $U,W$ 对易，$V_j\rho_{\rm st}V_j^\dagger=\rho_{\rm st}$，继而每个时间词均保持此态。原始联合概率于是恰为

$$
p_{\rho_{\rm st}}(h,1)=2^{-|h|}\frac27,\qquad
p_{\rho_{\rm st}}(h,0)=2^{-|h|}\frac57.
$$

合法的一状态比较器 $T_0=T_1=[1/2]$、$f_{\rm cl}=[2/7]$、$p(\rho_{\rm st})=[1]$ 精确实现全部历史和两种终端结果。因此单点域 $\mathcal D_{\rm st}=\{\rho_{\rm st}\}$ 对每个 $H\ge0$、$\varepsilon\ge0$ 都有 $k_{\mathcal D_{\rm st}}(H,\varepsilon)=1$。此域不包含 (73.1) 的双世界；非空性本身不足以支持 (78.3) 或定理 78.2 的状态下界。∎

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

**定义 81.1（同一源上的结论域）。** 定理 74.2 对全部非例外角度给精确有限终点的线性下界；定理 75.1 对同一全部角度给实际加权 TV 中的四状态严格阈值；定理 78.1 在有理坐标条件 (76.1) 下给任意 $k$ 的明确正阈值，定理 78.2 的反演固定这些有理数据并让误差趋零；这两个下界均要求 $\mathcal D$ 包含 (73.1) 的两个实际制备，特别适用于完整复 $\mathcal K_d$。定理 79.1、80.1 则对全部角度和完整复 $\mathcal K_d$ 给共同模型上界。这些陈述的 $T_j,f_{\rm cl}$ 均在各自模型内固定；下界允许任意制备函数，上界恰好具有共同仿射制备。

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


## 82. 原完整复集合的全部三维复实现

**定义 82.1（复三维比较合同与固定坐标）。** 固定任意 $0<d<1$ 和任意实 $\theta$ 满足 $\sin(2\theta)\ne0$，令 $c=d/2$。对象、存在分解 $\rho=A+D$、负扇区 $N=\ell^\perp$ 和完整集合 $\mathcal K_d$ 均取 (54.1)–(54.5)，不将它替换为仅有 $\rho_{\xi\xi}=c$ 的密度矩阵集合。在 $(\xi,e,f)$ 基中置

$$
P_\xi=\xi\xi^\dagger,\quad E=\frac12(\xi+e)(\xi+e)^\dagger,
\quad V_0=Ue^{\mathrm i\theta W},\quad V_1=V_0W,
\quad \operatorname{Ad}_Q(X)=QXQ^\dagger.
\tag{82.1}
$$

一个复三维实现由同一个保持全部凸组合的映射 $\sigma:\mathcal K_d\to\mathcal D(\mathbb C^3)$、同一个合法效果 $0\preceq F\preceq I_3$ 和两个固定的复 Kraus CP 映射组成：

$$
\Phi_j(X)=\sum_\alpha L_{j\alpha}XL_{j\alpha}^\dagger,
\qquad \sum_{j,\alpha}L_{j\alpha}^\dagger L_{j\alpha}=I_3.
\tag{82.2}
$$

对每个 $\rho\in\mathcal K_d$、每个有限时间词 $h=(j_1,\ldots,j_n)$ 和两种终端结果，要求

$$
\begin{aligned}
\operatorname{Tr}(F\Phi_h(\sigma(\rho)))
 &=2^{-n}\operatorname{Tr}(EV_h\rho V_h^\dagger),\\
\operatorname{Tr}((I_3-F)\Phi_h(\sigma(\rho)))
 &=2^{-n}[1-\operatorname{Tr}(EV_h\rho V_h^\dagger)].
\end{aligned}
\tag{82.3}
$$

$\Phi_h=\Phi_{j_n}\cdots\Phi_{j_1}$，$V_h=V_{j_n}\cdots V_{j_1}$，最左标签最早作用，空词也包括在内。允许不可达支持、不可观察方向、任意隐藏纤维、任意 Kraus 表示和初始依赖状态的分支质量；不预设逐支公平、可逆、协变或效果信息完备。此定义是 (54.10) 的复矩阵版本，沿用 (54.8) 的原始联合概率及第二卷 (39.5) 的五维桥。

**定理 82.2（全称复三维实现的过滤分类）。** 定义 82.1 的全部实现恰为以下族。存在唯一参数 $p\in[c,1/2]$，一个固定酉 $R\in U(3)$ 和一个共同选择 $\varepsilon\in\{0,1\}$，令 $\mathcal C_0(X)=X$、$\mathcal C_1(X)=\bar X$，其中共轭取固定源基，及

$$
\begin{gathered}
G_p=\sqrt{p/c}\,P_\xi+
\sqrt{(1-p)/(1-c)}\,(I_3-P_\xi),\\
\sigma_p(\rho)=G_p\rho G_p,\qquad
F_p=G_p^{-1}EG_p^{-1},\qquad
\Phi_{p,j}=\tfrac12\operatorname{Ad}_{V_j}.
\end{gathered}
\tag{82.4}
$$

则对全部实际初始态和全部复输入矩阵，

$$
\begin{gathered}
\sigma(\rho)=R\mathcal C_\varepsilon(\sigma_p(\rho))R^\dagger,
\qquad F=R\mathcal C_\varepsilon(F_p)R^\dagger,\\
\Phi_j(X)=\tfrac12 U_jXU_j^\dagger,
\qquad U_j=R\mathcal C_\varepsilon(V_j)R^\dagger.
\end{gathered}
\tag{82.5}
$$

反之，每个这样的 $p,R,\varepsilon$ 都满足原合同。分类的对象是分支 CP 映射；给两个 $U_j$ 分别乘任意标量相位不改变它。每个分支的任意 Kraus 表只是 $\alpha_{j\alpha}U_j$ 的共线表，$\sum_\alpha|\alpha_{j\alpha}|^2=1/2$。共同复共轭比较全部表示资料，不是一个取得的 CP 转置操作。

这里分类 $\sigma$ 在实际 $\mathcal K_d$ 上的值、$F$ 在整个三维空间上的值以及 $\Phi_j$ 在整个 $M_3(\mathbb C)$ 上的值；不把离开制备域后任意延伸且在原域恒为零的仿射项算作另一个实现。复最小维数三的既有下界由六维仿射单射及 $m^2-1\ge6$ 给出，标准 qutrit 实现给上界；这一最小值是供应，分类不重复计作新的维数发现。必要性由 §§83–86 给出，充分性及参数唯一性见定理 86.2。

## 83. 任意复 CP 竞争者的完整矩阵收缩与维数饱和

**定理 83.1（三维合同迫使全矩阵 CP 群）。** 每个定义 82.1 的实现，其全部可达支持就是 $\mathbb C^3$；归一化分支 $T_j=2\Phi_j$ 在完整矩阵空间上的词闭包是具有 CP 逆的紧群。

证明。将 (82.3) 两种结果相加，得

$$
X_{h,\rho}=T_h\sigma(\rho)\succeq0,
\qquad \operatorname{Tr}X_{h,\rho}=1.
\tag{83.1}
$$

令 $H_{\rm r}$ 为这些矩阵支持的复线性张成，$n=\dim H_{\rm r}\le3$。若 $v\perp H_{\rm r}$，则

$$
0=v^\dagger T_j(X_{h,\rho})v
=2\sum_\alpha\|X_{h,\rho}^{1/2}L_{j\alpha}^\dagger v\|^2.
\tag{83.2}
$$

逐项非负性使每个原 Kraus 算子保持 $H_{\rm r}$。因此压缩到它仍为复 CP，原仪器和仍 TP，效果压缩合法，制备仿射且保留所有记录。取有限个支持张成的可达密度矩阵的严格正权凸组合 $\Omega\succ0$ 于 $H_{\rm r}$，并取 $\eta>0$ 使 $\Omega\succeq\eta I$。词拼接给 $\operatorname{Tr}(T_h\Omega)=1$，从而

$$
0\preceq T_h(I)\preceq\eta^{-1}T_h(\Omega),
\qquad \|T_h\|_{\rm cb}=\|T_h(I)\|\le\eta^{-1}.
\tag{83.3}
$$

CP 范数等式也可由正的二乘二算子块在每个矩阵层推出。因此有界的是完整 $M_n(\mathbb C)$ 上的映射，并非仅可达 Hermitian 子空间。其范数闭包 $\mathscr S$ 是紧 CP 半群。

令 $\mathscr R=\operatorname{span}_{\mathbb R}\{X_{h,\rho}\}$。源的两个不同供应是：第二卷定理 40.1 的 $I_3$ 加八个加权效果张成九维 $\operatorname{Herm}_3(\mathbb C)$；本卷 (64.10)–(64.12) 的源可达空间恰为

$$
\mathscr S_c=\{X\in\operatorname{Herm}_3(\mathbb C):
 X_{\xi\xi}=c\operatorname{Tr}X\},\qquad \dim_{\mathbb R}\mathscr S_c=8.
\tag{83.4}
$$

后一个供应使用原合法纯态 $\sqrt d\,a+\mathrm i\sqrt{1-d}\,g$ 和引理 63.1 的实际下块 $SU(2)$，并非假设初始集合张成全部状态空间。该引理适用于每个 $e^{-2\mathrm i\theta}\notin\{1,-1\}$，包括单位根情形；其下块生成元就是 (62.2) 的 $B_0,B_1$，无实竞争者前提。

定义

$$
L(X_{h,\rho})=V_h\rho V_h^\dagger.
\tag{83.5}
$$

若编码侧有线性关系，将它与迹及每个继续词的 $FT_k$ 配对，便使相应源关系与 $I_3$ 及八个 $M_k$ 配对为零。源效果基非退化，故源关系为零。这证明 $L$ 良定义、满射到 $\mathscr S_c$ 且 $LT_j=\operatorname{Ad}_{V_j}L$，同时 $\operatorname{Tr}X=\operatorname{Tr}LX$ 和 $\operatorname{Tr}(FX)=\operatorname{Tr}(ELX)$ 于 $\mathscr R$。没有假设竞争者自己的效果张成九维。

$\mathscr R,\ker L$ 对闭包不变。选线性截面 $J_L$，则 $\pi(s)=LsJ_L$ 与截面无关，是到源词闭群 $G$ 的连续半群同态；它满射，因为每个源极限可沿同一词子列借 $\mathscr S$ 紧性取得编码极限。源正词闭包是群，所需逆来自紧酉群中的同时回归，而不是新的操作权限。

在已经闭合的 $\mathscr S$ 中取完整复线性映射秩最小的 $a$，秩记为 $r$。$\operatorname{rank}a^2=r$ 排除零处的非平凡 Jordan 块；有界幂排除模大于一的本征值及单位圆上的非平凡 Jordan 块。若非零本征值有模小于一者，令所有单位模本征值同时回归一，幂的极限会有更小秩，矛盾。同一回归遂给 CP 幂等元 $P$，$\operatorname{rank}_{\mathbb C}P=r$。因 $\pi(P)$ 为群中幂等元，$\pi(P)=1$、$LP=L$ 于 $\mathscr R$。

角 $\mathscr K=P\mathscr S P$ 中每个元素的秩都是 $r$，在 $\operatorname{ran}P$ 上可逆；此限制忠实，且其像为紧的可逆矩阵半群。紧性给奇异值的统一正下界；同时回归的正幂给单位与逆。因此 $\mathscr K$ 是单位为 $P$ 的紧群，逆仍有完整矩阵 CP 代表。

置 $H_1=\operatorname{supp}(P\Omega)=\operatorname{supp}P(I)$。在 $P$ 的 Kraus 表中，它等于所有 Kraus 像的张成，所以 $P$ 的整个复矩阵像左右均支持于 $H_1$。只将 $P,\mathscr K$ 限制到 $H_1$，此时不声称原 $T_j$ 保持它。对正的像元素 $Y$，由 $Y\preceq b\Omega$ 再作用 $P$ 得 $Y\preceq bP\Omega$；故 $P\Omega$ 是像锥序单位。对 $k^{-1}(P\Omega)$ 应用该界，给 $P\Omega\preceq b k(P\Omega)$。于是角群的 Haar 平均

$$
\Omega_1=\int_{\mathscr K}k(P\Omega)\,dk\succ0
\quad\text{于 }H_1
\tag{83.6}
$$

被全角群固定。以 $D_1=\Omega_1^{1/2}$ 作合同，得到完整 $M_{n_1}(\mathbb C)$ 上的 UCP 幂等元

$$
\widetilde P=\operatorname{Ad}_{D_1^{-1}}P\operatorname{Ad}_{D_1},
\qquad n_1=\dim H_1\le n.
\tag{83.7}
$$

在此消费 Choi–Effros 乘法定理，采用 Prunaru，[*On the Choi–Effros multiplication*](https://arxiv.org/html/1304.6664v2)，定理 1：CP、收缩、幂等映射的像，带乘法 $x\star y=\widetilde P(xy)$、原伴随及继承的完整矩阵序，是复 $C^*$ 代数 $\mathcal A$。这里 CP 与幂等已经成立，保单位 CP 给收缩；并未假设 $P$ 忠实或其像在通常乘法下封闭。角群及其逆在此抽象代数上 UCP，两次 Schwarz 使它们为 $*$ 自同构。

比较物理维数须使用抽象收缩。令 $i:\mathcal A\to M_{n_1}(\mathbb C)$ 是完全序包含，$r_0=i^{-1}\widetilde P$ 是到抽象 $\mathcal A$ 的 UCP 收缩，$r_0i=1$。对 $x\in\mathcal A$，Schwarz 先施于 $i$ 再施 $r_0$，以及直接施于 $r_0$，分别给

$$
r_0(i(x)^\dagger i(x))\preceq x^*\star x
\preceq r_0(i(x)^\dagger i(x)).
\tag{83.8}
$$

同理有 $xx^*$ 的等号。因此 $i(x)$ 属于抽象 $r_0$ 的乘法域，$r_0:C^*(i(\mathcal A))\to\mathcal A$ 是满射 $*$ 同态。此处不能改称环境投影 $\widetilde P$ 的像全属于其通常乘法域。

有限维具体代数 $C^*(i(\mathcal A))$ 忠实作用于 $\mathbb C^{n_1}$。其核是若干完整简单因子的直和；去掉这些因子的中心物理子空间，便得到 $\mathcal A$ 的维数至多 $n_1$ 的忠实复表示。写 $\mathcal A=\bigoplus_\ell M_{n_\ell}(\mathbb C)$，则

$$
\sum_\ell n_\ell\le n_1\le n\le3.
\tag{83.9}
$$

由于 $LP=L$，$P$ 的自伴像满射到八维 $\mathscr S_c$。保持伴随的复线性映射之复像维数等于其自伴像的实维数。故 $\dim_{\mathbb R}\mathcal A_{\rm sa}\ge8$。成本至多三的复代数中，除 $M_3(\mathbb C)$ 外，只有 $\mathbb C$、$\mathbb C^2$、$M_2(\mathbb C)$、$\mathbb C^3$、$\mathbb C\oplus M_2(\mathbb C)$，自伴维数至多五。因此 $\mathcal A=M_3(\mathbb C)$，$n_1=n=3$，$\operatorname{rank}_{\mathbb C}P=9$，满秩幂等元 $P=I$。这里使用复因子成本，没有把实六维结论移植成复分类。$\mathscr K=\mathscr S$ 遂是所述全矩阵 CP 群。∎

## 84. 原 TP 和、匹配表示与两个生成元的四元数消去

**定理 84.1（所有原归一化分支全局酉且公平）。** 每个定义 82.1 的实现有酉 $U_0,U_1$，使 $T_j=\operatorname{Ad}_{U_j}$ 于整个 $M_3(\mathbb C)$。其紧群到源 $G$ 的 $\pi$ 是同构；一个固定酉坐标使匹配的源 $SU(2)$ 作用为 $1\oplus S$。

证明。定理 83.1 给每个 $T\in\mathscr S$ 完整 CP 逆。$T(I)$ 是序单位；令 $Q_T=T(I)^{1/2}$，则 $\operatorname{Ad}_{Q_T^{-1}}T$ 和其逆 $T^{-1}\operatorname{Ad}_{Q_T}$ 都 UCP。两次 Schwarz 给乘法性，复全矩阵 $*$ 自同构为酉内自同构，故还原后 $T_j=\operatorname{Ad}_{A_j}$，$A_j$ 可逆。

Haar 平均 $T(I)$ 得整个群固定的 $\Omega_2\succ0$。令 $B'_j=\Omega_2^{-1/2}A_j\Omega_2^{1/2}$，则 $B'_j$ 酉。原仪器和 TP 此时在整个已饱和的三维支持上给

$$
A_0^\dagger A_0+A_1^\dagger A_1=2I,
\qquad \sum_{j=0}^1(B'_j)^\dagger\Omega_2B'_j=2\Omega_2.
\tag{84.1}
$$

置 $D_j=(B'_j)^\dagger\Omega_2B'_j$，酉共轭保持 Hilbert–Schmidt 范数，所以

$$
\sum_j\|D_j-\Omega_2\|_{\rm HS}^2
=\sum_j\|D_j\|_{\rm HS}^2-2\|\Omega_2\|_{\rm HS}^2=0.
\tag{84.2}
$$

故每个 $B'_j$ 与 $\Omega_2$ 交换，$A_j=B'_j$ 酉。这是从实际 TP 和导出的全局公平性，不是从可达态上的迹一直接推出逐支 TP。Nayak–Sen，[*Invertible Quantum Operations and Perfect Encryption of Quantum States*](https://arxiv.org/html/quant-ph/0605041v4)，定理 2.1 的假设为全输入域上的 CPTP 映射和 CPTP 左逆；只在此时其等维结论适用。上面的完整 CP 逆、保单位化和原 TP 和论证给出此前缺少的桥。

现在 $\mathscr S,G$ 都是闭的紧矩阵 Lie 群。满射 $\pi$ 的微分满射：单位分支之像为 $G^0$，因为紧 Lie 群只有有限多个分支。取紧 Lie 代数上的 Ad 不变内积，$\ker d\pi$ 的正交补仍为理想，且同构于 $\operatorname{Lie}G$。在此补理想中提升源的实际 $\mathfrak{su}(2)$，从单连通 $SU(2)$ 积分，得到 $\lambda:SU(2)\to\mathscr S$，$\pi\lambda(S)=\operatorname{Ad}_{1\oplus S}|_{\mathscr S_c}$。积分定理的域确为 $SU(2)$ 而非 $SO(3)$；参见 Hall 的矩阵群与单连通积分工具，文献对应见 §90。

到 $PU(3)$ 的这个作用经覆盖 $SU(3)\to PU(3)$ 提升为三维复酉表示。三维复 $SU(2)$ 表示只有自旋一、$1\oplus2$ 或三个平凡线。前后两种的中心 $-I_2$ 在共轭上平凡，不能供应源 $\mathscr S_c$ 中中心变号的基本实四维模。因此一个固定酉把提升写成 $1\oplus S$。

在 $\operatorname{Herm}_3$ 中，这个作用分解为两个平凡线、唯一的交叉基本实四维模和唯一下块无迹伴随实三维模。紧群完全可约性及重数一表明这两个非平凡模都完整位于 $\mathscr R$，$L$ 在它们上为同构。故 $\dim\mathscr R\in\{8,9\}$，$\ker L$ 为零或一条平凡线。

若 $k\in\ker\pi$，它是酉共轭，所以在 Hilbert–Schmidt 内积下正交；它保持 $\mathscr R$、$\ker L$ 及 $\mathscr W=\mathscr R\cap(\ker L)^\perp$。对 $X\in\mathscr W$，$(k-I)X$ 同时在 $\ker L$ 和 $\mathscr W$，故为零。全部交叉四维模属于 $\mathscr W$，其 Hermitian 矩阵的复 $*$ 代数生成全部 $M_3$：两种实虚交叉矩阵给 $E_{0r},E_{r0}$，再相乘给所有矩阵单位。因此固定它们的酉共轭只能是恒等，$\ker\pi=1$。此证同时覆盖八维与九维可达空间。源下块 $SU(2)$ 正规于 $G\subseteq\operatorname{Ad}(1\oplus U(2))$，同构 $\pi$ 因而使匹配的 $SU(2)$ 也正规于竞争者群。∎

**定理 84.2（完整生成元匹配与全部待定仿射项）。** 在一个固定酉或共同复共轭坐标中，两个 $T_j$ 同时等于原 $\operatorname{Ad}_{V_j}$。存在 $k>0$、实数 $b\ne0$、实数 $A_F,t_F$ 和一个实仿射函数 $p(\rho)$，使全部实际准备满足

$$
\begin{gathered}
\rho=\begin{pmatrix}c&z^\dagger\\z&Q\end{pmatrix},\quad
Q_0=Q-\frac{1-c}{2}I_2,\\
\sigma(\rho)=\begin{pmatrix}
p(\rho)&kz^\dagger\\kz&bQ_0+\frac{1-p(\rho)}2I_2
\end{pmatrix},\\
F=\begin{pmatrix}
A_F&e_1^\dagger/(2k)\\
e_1/(2k)&t_F I_2+(e_1e_1^\dagger/2-I_2/4)/b
\end{pmatrix},\quad e_1=(1,0)^{\mathsf T},\\
A_Fp(\rho)+t_F(1-p(\rho))=(1+c)/4.
\end{gathered}
\tag{84.3}
$$

证明。正规性使每个原竞争者酉保持唯一平凡线及其双维补空间；除去各自无关的标量相位后，写为 $1\oplus D_j$。与匹配 $SU(2)$ 的共轭关系相同，故 $D_j=\chi_j B_j$，$|\chi_j|=1$，其中 $B_j$ 是 (62.2) 的实际下块。

$L$ 的交叉模逆映射是一个非零实交织 $T$。这里复二维基本表示视作实表示的交换子是四元数代数，不能仅取复标量。明确地，

$$
T=\alpha I+\beta\mathcal Q,\quad \alpha,\beta\in\mathbb C,
\qquad \mathcal Q(v)=\epsilon_2\bar v,
\quad \epsilon_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
\quad \det_{\mathbb R}T=(|\alpha|^2+|\beta|^2)^2.
\tag{84.4}
$$

对 $B\in U(2)$，$\mathcal QB=(\det B)^{-1}B\mathcal Q$。于是两个原生成元的交织 $TB_j=D_jT$ 分别给

$$
\alpha=\chi_j\alpha,\qquad
\beta/(\det B_j)=\chi_j\beta,
\qquad \det B_0=-z_\theta,\quad\det B_1=z_\theta.
\tag{84.5}
$$

若 $\alpha\beta\ne0$，两个行列式都必须为一，与其相反符号矛盾。因此 $T$ 纯复线性或纯反线性；只匹配 $SU(2)$ 并不足以排除混合项。线性情形 $\chi_j=1$，固定标量扇区相位使 $T=kI$、$k>0$。反线性情形 $D_j=\epsilon_2\bar B_j\epsilon_2^{-1}$；一个固定下块 $\epsilon_2^{-1}$ 酉及共同共轭把它归入线性情形。此变换同时作用于所有初始态、效果和两个分支。下块伴随系数可变号，因此此阶段仍只要求 $b$ 为非零实数。

源及竞争者的交叉和伴随模都重数一。交叉逆已为 $kI$，伴随实不可约模的交换子为实标量，故其逆为 $bI$。$L$ 在整个可达空间上的线性关系遂逐态给 (84.3) 的制备式；没有要求轨道点仍在初始制备域，也没有额外假设制备协变。迹一给唯一剩余标量函数 $p(\rho)$。它由仿射 $\sigma$ 的一个固定条目给出，因而在原仿射包络上仿射。

将 $\operatorname{Tr}(FX)=\operatorname{Tr}(ELX)$ 配对到完整交叉模和伴随模，分别固定 $F$ 的交叉列及下块无迹部分；余下两个标量为 $A_F,t_F$。源标量部分的 $E$ 配对是 $c/2+(1-c)/4=(1+c)/4$，给最后一式。如果 $\dim\mathscr R=9$，隐藏核方向只能为 $H=\operatorname{diag}(1,-1/2,-1/2)$，且 $\operatorname{Tr}(FH)=A_F-t_F=0$；这个可能性仍保留到原域正性检验。∎

## 85. 复零响应圆、纯态秩与原纯曲线的仿射张成

**定理 85.1（每个实际纯输入的秩一约束）。** 在 (84.3) 中，$F$ 秩一，且每个属于原 $\mathcal K_d$ 的纯态都有秩一编码。存在一个对所有实际纯输入共同的 $p_*\in[c,1/2]$，使

$$
b=\frac{1-p_*}{1-c},\quad
k^2=\frac{p_*(1-p_*)}{c(1-c)},\quad
A_F=\frac{c}{2p_*},\quad t_F=\frac{1-c}{4(1-p_*)}.
\tag{85.1}
$$

证明。任取实际纯态，因其 $\xi$ 人口为 $c$，固定无关总体相位后写为 $\sqrt c\,\xi+\sqrt{1-c}\,r_0$。下块 $SU(2)$ 在单位球上传递；对精确群响应恒等式右平移变量，使源向量的下块变成 $e_1$。编码侧相应酉变换 $\Sigma=\sigma(\rho)$ 保持其正性、秩和迹，固定效果不变。只是等式坐标代换，不添加初始态或控制。

令

$$
S(u)=\begin{pmatrix}u_1&-\bar u_2\\u_2&\bar u_1\end{pmatrix},
\quad |u_1|^2+|u_2|^2=1,
\qquad f_c(u)=\frac12|\sqrt c+\sqrt{1-c}\,u_1|^2.
\tag{85.2}
$$

响应 $\operatorname{Tr}[F(1\oplus S(u))\Sigma(1\oplus S(u))^\dagger]$ 等于 $f_c(u)$。它在整个圆

$$
u_1=-a_0,\qquad u_2=r_0'e^{\mathrm i\varphi},
\quad a_0=\sqrt{c/(1-c)}>0,\quad r_0'=\sqrt{1-a_0^2}>0
\tag{85.3}
$$

上为零。正矩阵迹配对等于 $\|F^{1/2}(1\oplus S(u))\Sigma^{1/2}\|_{\rm HS}^2$，所以每个支持幅度分别为零。对 $v=(s_0,x,y)\in\operatorname{ran}\Sigma$、$w=(a_0',b_0,t_0)\in\operatorname{ran}F$，其幅度恒等式完整为

$$
\bar a_0's_0-a_0(\bar b_0x+\bar t_0y)
+r_0'\bar t_0x e^{\mathrm i\varphi}
-r_0'\bar b_0y e^{-\mathrm i\varphi}=0.
$$

比较常数项及两个非零频率的 Laurent 系数，给

$$
\bar t_0x=0,\qquad \bar b_0y=0,\qquad
\bar a_0's_0=a_0(\bar b_0x+\bar t_0y).
\tag{85.4}
$$

非零源交叉响应及 $kz\ne0$ 使编码交叉非零，故可选一个 $v$ 同时有 $s_0\ne0$ 和 $(x,y)\ne0$。若 $x,y$ 都非零，(85.4) 迫使全部 $w=0$，与响应非零矛盾。若 $x\ne0,y=0$，则每个 $w$ 有 $t_0=0$，且 $\bar a_0's_0=a_0\bar b_0x$，故全部 $w$ 在同一非零复直线；非零 $w$ 的 $a_0',b_0$ 都非零。固定该 $w$ 再作用于任意支持向量，得到 $y=0$ 及相同的 $s_0/x$ 比，全部 $v$ 也在一条复直线。$x=0,y\ne0$ 对称。因此 $\operatorname{rank}F=\operatorname{rank}\Sigma=1$。此论证逐个覆盖全部实际纯态，不指定它们的编码。

回到固定源坐标，$F$ 的非零交叉列沿 $e_1$。秩一正性使它的下块支持恰沿 $e_1$，故

$$
t_F-1/(4b)=0,\qquad 1/(2b)>0,\qquad
A_F/(2b)=1/(4k^2).
\tag{85.5}
$$

于是 $b>0$、$t_F=1/(4b)$、$A_F=b/(2k^2)$。源纯性给 $Q=zz^\dagger/c$、$\|z\|^2=c(1-c)$。编码秩一及非零交叉使其下块垂直于 $z$ 的本征值为零，故 $1-p(\rho)=b(1-c)$；它对所有纯输入都是同一个 $p_*=1-b(1-c)\in(0,1)$。余下二乘二行列式给 $k^2c(1-c)=p_*(1-p_*)$，即 (85.1)。效果唯一非零本征值及其合法性余量是

$$
\lambda(p)=\frac{c}{2p}+\frac{1-c}{2(1-p)},\qquad
1-\lambda(p)=\frac{(p-c)(1-2p)}{2p(1-p)}.
\tag{85.6}
$$

在 $0<c<1/2$、$0<p<1$ 中，$F\preceq I$ 恰要求 $p\in[c,1/2]$。两端都保留，且都是秩一投影。∎

**定理 85.2（原域仿射自由度至多为一个真实混合坐标）。** (84.3) 中必有

$$
p(\rho)=p_*+\nu s(\rho),\qquad
s(\rho)=\rho_{aa}-d,\quad \nu\in\mathbb R.
\tag{85.7}
$$

若 $A_F\ne t_F$，则 $\nu=0$。唯一仍须正性排除的校准是

$$
p_*=\frac{2c}{1+c},\qquad c\le1/3.
\tag{85.8}
$$

证明。复用引理 70.1 的实际纯曲线 $\rho_t=\psi_t\psi_t^\dagger$、$|t|<\delta_d$，及其原五维提升，明确参数为

$$
\begin{gathered}
\delta_d=\min\{1,\sqrt{(1-d)/(2d)}\},\qquad
f_d(t)=\sqrt{\frac{1-3d+2d\cos t}{13-12\cos t}},\\
\psi_t=\sqrt d\,a+\sqrt d(e^{\mathrm it}-1)h_{\rm out}
 +\mathrm i(3e^{\mathrm it}-2)f_d(t)g.
\end{gathered}
\tag{85.9}
$$

其合法性是原 $A=\rho_t,D=0$ 分解，不仅是固定人口矩条件。引理 70.2 的逐条矩阵提取 (70.9)–(70.10) 供应仿射函数空间恰为 $\operatorname{span}\{1,x,y,f,xf,yf\}$，$x=\cos t,y=\sin t,f=f_d(t)$。现在证明这六个函数线性独立，从而确定该曲线的精确仿射张成。

奇部关系为 $y(a+bf)=0$。$f^2=(1-3d+2dx)/(13-12x)$ 非常数，因为分子在分母根 $13/12$ 的值为 $1-5d/6>0$，故奇部两个系数为零。偶部关系形如 $A+Bx+(C+Dx)f=0$。若 $C+Dx$ 不恒零，则 $f$ 在开区间上为有理函数，其平方将使上述有理函数成为有理平方；但它有互异的简单零与简单极点，次数奇偶矛盾。若 $C+Dx=0$，其余系数也零。开区间上的等式乘分母后是多项式恒等式，不需要在区间外实现任何状态。

故曲线仿射维数五，恰张成 $\operatorname{Tr}\rho=1$、$C,E$ 两矩及 $\rho_{aa}=d$ 的五维仿射平面。原 $\mathcal K_d$ 的仿射维数六由 (55.2) 的严格正点、$s>0$ 和 $B_d\succ0$ 供应；$s$ 不在整个集合上恒零。由于 $p-p_*$ 在该五维平面上为零，只能为 $\nu s$。将它代入 (84.3) 的标量等式，$A_F\ne t_F$ 时立刻得 $\nu=0$。(85.1) 给 $A_F=t_F$ 当且仅当 $p_*=2c/(1+c)$，而它在合法区间内当且仅当 $c\le1/3$。此时必须继续使用实际混合态，不能以信息完备性排除该合法校准。∎

## 86. 原混合边界消去隐藏项及分类的充分性

**定理 86.1（包括奇异校准的全部仿射项消去）。** 在 (85.8) 及整个 $0<d<1$ 的适用域内，原集合上的正性迫使 $\nu=0$；特别包括 $d=2/3,p_*=1/2$。

证明。在该校准，

$$
G_*^2=\frac{\operatorname{diag}(2,1,1)}{1+c},\qquad
\sigma(\rho)=G_*\rho G_*+\nu sH,\quad
H=\operatorname{diag}(1,-1/2,-1/2).
\tag{86.1}
$$

对其作 $G_*^{-1}$ 合同，正性等价于

$$
\rho+\eta sJ\succeq0,\qquad
\eta=\nu(1+c)/2,\qquad
J=\operatorname{diag}(1,-1,-1)=C-I.
\tag{86.2}
$$

在 $(a,h_{\rm out},g)$ 基中，$J=\left(\begin{smallmatrix}0&1&0\\1&0&0\\0&0&-1\end{smallmatrix}\right)$。置 $\beta=1-d$、$\alpha=(2+\sqrt2)/\sqrt{12}$、$\gamma=(2-\sqrt2)/\sqrt{12}$；原 $\ell=(-\gamma,\alpha,0)^{\mathsf T}$，$N=\operatorname{span}\{(\alpha,\gamma,0)^{\mathsf T},g\}$。对实数 $v$ 取

$$
\begin{gathered}
\psi_0=(\sqrt d,0,\mathrm i\sqrt\beta)^{\mathsf T},\quad
n_v=(\sqrt\beta,v,-\mathrm i\sqrt d)^{\mathsf T},\\
w_v=(\alpha,\gamma,
\mathrm i(\alpha\sqrt\beta+\gamma v)/\sqrt d)^{\mathsf T}.
\end{gathered}
\tag{86.3}
$$

直接内积给 $\psi_0^\dagger n_v=w_v^\dagger n_v=0$、$w_v\in N$，且

$$
n_v^\dagger Jn_v=2\sqrt\beta v-d.
\tag{86.4}
$$

选 $v_-=0$、$v_+=d/\sqrt\beta$，符号分别为 $-d,+d$。固定任一选择及对应 $w=w_v$。以 $u=(x,r+\mathrm i h,\mathrm i g_0)^{\mathsf T}$ 的四个实坐标 $(x,h,r,g_0)$，在 $(\sqrt d,0,0,\sqrt\beta)$ 附近对约束

$$
\begin{pmatrix}
\|u\|^2+\epsilon\|w\|^2\\ |u_a|^2\\
\operatorname{Tr}(C[uu^\dagger+\epsilon ww^\dagger])\\
\operatorname{Tr}(E[uu^\dagger+\epsilon ww^\dagger])
\end{pmatrix}
=\begin{pmatrix}1\\d\\d\\(6-5d)/16\end{pmatrix}
\tag{86.5}
$$

应用实隐函数定理。基点导数完整为

$$
\begin{pmatrix}
2\sqrt d&0&0&2\sqrt\beta\\
2\sqrt d&0&0&0\\
2\sqrt d&0&2\sqrt d&0\\
\sqrt d/8&3\sqrt6\sqrt\beta/8&3\sqrt d/8&3\sqrt\beta/4
\end{pmatrix},\qquad
\det=3\sqrt6\,\beta d\ne0.
\tag{86.6}
$$

故对各选择及所有足够小的 $\epsilon>0$，有 $u_\epsilon\to\psi_0$ 满足全部等式。令

$$
A_\epsilon=u_\epsilon u_\epsilon^\dagger,\quad
D_\epsilon=\epsilon w_vw_v^\dagger,\quad
\rho_\epsilon=A_\epsilon+D_\epsilon,
\qquad s(\rho_\epsilon)=\epsilon\alpha^2>0.
\tag{86.7}
$$

$A_\epsilon,D_\epsilon\succeq0$、$D_\epsilon\ell=0$、$(A_\epsilon)_{aa}=d$，加上 (86.5) 证明这是原 (54.2) 中的态。$\ell^\dagger\psi_0=-\gamma\sqrt d\ne0$ 而 $w_v\in N$，所以两列 $(\psi_0,w_v)$ 独立，且 $(u_\epsilon,w_v)$ 对小 $\epsilon$ 保持秩二。$\rho_\epsilon$ 秩二，其核可取连续非零向量 $n_\epsilon\to n_v$。这里连续的是两列支持矩阵的核；虽极限密度矩阵降为秩一，两列支持矩阵在 $\epsilon=0$ 并未降秩。

将 (86.2) 在 $n_\epsilon$ 上求值，给

$$
0\le\eta\,\epsilon\alpha^2 n_\epsilon^\dagger Jn_\epsilon.
\tag{86.8}
$$

两个选择的严格相反符号在足够小正 $\epsilon$ 保留，分别迫使 $\eta\le0$ 和 $\eta\ge0$。因此 $\eta=\nu=0$。没有使用放松集合，也没有要求一个对所有 $d$ 一致的 $\epsilon$ 邻域。$d=2/3$ 时 $\beta d>0$、$G_*$ 可逆，(86.6) 不退化，故端点校准 $p_*=1/2$ 同样包含。∎

**定理 86.2（全词充分性、闭区间及参数唯一性）。** (82.4)–(82.5) 满足定义 82.1，且不同 $p$ 不被其中的固定酉或共同共轭等同。因此定理 82.2 的必要充分性成立。

证明。定理 84.2、85.1、85.2、86.1 给必要性：$p(\rho)=p_*$ 于整个原集合，(84.3) 的各块恰为 $G_{p_*}\rho G_{p_*}$，效果为 $G_{p_*}^{-1}EG_{p_*}^{-1}$，两个分支为原酉共轭的一半。

反向，对每个 $c\le p\le1/2$，$G_p$ 严格正、可逆并与两个实际 $V_j$ 交换。全部原态有 $\rho_{\xi\xi}=c$，故

$$
\operatorname{Tr}(G_p\rho G_p)=p+(1-p)=1.
\tag{86.9}
$$

合同保持正性和原集合上的仿射性。(85.6) 给合法效果；$V_j/\sqrt2$ 的伴随平方和为 $I$。对每个有限词，归纳给

$$
\Phi_h(\sigma_p(\rho))
=2^{-|h|}G_pV_h\rho V_h^\dagger G_p.
\tag{86.10}
$$

以 $F_p$ 配对恰得 (82.3) 第一式；其迹为 $2^{-|h|}$，所以补效果给第二式，空词也成立。固定酉同时变换保持全部配对；共同共轭保持实迹概率，并把分支变成 $\operatorname{Ad}_{\bar V_j}/2$，仍 CP。

源 $SU(2)$ 动态在 Hilbert 空间上只有一条平凡线，故任何两实现之间的固定酉或共同共轭等价必须保持这条动态选出的线。其初始人口就是 $p$，所以不同 $p$ 不等价。最后，$\Phi_j$ 的 Choi 矩阵秩一；其任意 Kraus 向量化都是该 Choi 支持上的向量，故任意表只能共线，平方系数和固定为 $1/2$。这不鉴别各自标量相位。∎

## 追加锚（本行以下为增补区）

## 87. 合法奇异校准、效果效率与被预测确定的量

**定理 87.1（八维效果跨度是分类中的合法点）。** 定理 82.2 的每个标准代表，其可达状态线性空间都是

$$
\mathscr S_p=\{X\in\operatorname{Herm}_3:X_{\xi\xi}=p\operatorname{Tr}X\},
\qquad \dim\mathscr S_p=8.
\tag{87.1}
$$

但 $I_3$ 加全部原生联合效果的实张成维数为

$$
\dim\operatorname{span}_{\mathbb R}
\bigl(\{I_3\}\cup\{\Phi_h^*(F_p):h\text{ 有限}\}\bigr)
=\begin{cases}
8,&p=2c/(1+c),\ c\le1/3,\\
9,&\text{其余合法 }p.
\end{cases}
\tag{87.2}
$$

在八维情形，其迹配对消去子恰为 $\mathbb RH$，其中 $H=\operatorname{diag}(1,-1/2,-1/2)$。此点及两个投影端点不使 $G_p$ 奇异。

证明。$G_p$ 与源群交换，$\operatorname{Ad}_{G_p}$ 把八维 $\mathscr S_c$ 双射到 $\mathscr S_p$，给 (87.1)。$SU(2)$ 效果轨道分解为一个非零固定标量分量 $\operatorname{diag}(A_F,t_F,t_F)$、一个非零交叉基本四维分量和一个非零下块伴随三维分量。两个非平凡分量不可约且不同构，完整位于轨道张成。添加 $I_3$ 时，两个标量方向独立恰在 $A_F\ne t_F$。用 (85.1) 解得相等恰在 (85.8)。当 $A_F=t_F$，两标量方向重合，唯一正交标量为 $H$；所有词效果都消去它。非零词权重不改变张成维数。

这说明在定理 84.2 阶段添加 $\nu sH$ 确实可能在所有读数下不可见；定理 86.1 使用整个原集合的正性才排除它。源的九维效果基不能被误当作竞争者的信息完备前提。在 $c=1/3$，奇异校准恰与 $p=1/2$ 投影端点重合，效果跨度仍八维，正性排除仍成立。所有推导只除以 $c,1-c,p,1-p$ 及非零的 $k,b$，从未除以 $1-2p$；因此 $p=1/2$ 的纯度方程重根也未被遗漏。$p=c$ 不满足 $A_F=t_F$，因为 $c<1$。若 $c>1/3$，特殊值不合法，所有合法校准的跨度都是九维。∎

**定理 87.2（效率全区间与秩、谱的不同地位）。** 在同一个原生预测表的全部复三维实现内，效果秩固定为一，但其效率 $\|F\|=\operatorname{Tr}F$ 的值恰遍历

$$
\left[\frac12+\sqrt{c(1-c)},1\right].
\tag{87.3}
$$

每个原态的编码秩固定，而一般混态的谱、纯度和 von Neumann 熵不由原生表唯一确定。具体写 $a_p=p/c$、$b_p=(1-p)/(1-c)$，有

$$
\begin{gathered}
\operatorname{rank}\sigma_p(\rho)=\operatorname{rank}\rho,\qquad
\det\sigma_p(\rho)=a_pb_p^2\det\rho,\\
\operatorname{Tr}(\sigma_p(\rho)^2)
=p^2+2a_pb_p\|z\|^2+b_p^2\operatorname{Tr}(Q^2),
\quad \rho=\begin{pmatrix}c&z^\dagger\\z&Q\end{pmatrix}.
\end{gathered}
\tag{87.4}
$$

证明。效率是 (85.6) 的 $\lambda(p)$。其导数为 $-c/(2p^2)+(1-c)/(2(1-p)^2)$，唯一最小点

$$
p_{\rm eff}=\frac{\sqrt c}{\sqrt c+\sqrt{1-c}}\in[c,1/2]
\tag{87.5}
$$

给 (87.3) 下端；两个区间端点给一，连续性给整个区间。$G_p$ 可逆，合同保持秩，行列式相乘和分块平方给 (87.4)。在内部 $c<p<1/2$ 时效果是严格小于其支撑投影的秩一效果；投影恰在两个端点。混态谱与熵确实可变的原域实例见定理 88.2。

第二卷的源效果基从精确表确定源 $\rho$；定理 82.2 则使所有允许的三维实现具有相同的编码秩、同一对分支通道（取固定酉或共同共轭等价）及同一完整词动力学。分支的 Choi 秩、各词超算子谱和酉相对本征相位因此在该等价意义下固定；标量 Kraus 相位仍不属于通道。任何表示量在这次实验中可识别，当且仅当它在所列 $p$ 族及其固定坐标等价上恒定。这是给定模型类内的精确判断，未涉及更大载体的隐藏自由度。∎

## 88. 全部例子的原五维来源与精确半参数反例

**定理 88.1（分类所用纯、混合态都对应原通道）。** 定理 85.2 的曲线、定理 86.1 的两支混合边界以及下述 $d=1/2$ 的实例，均属于原完整 $\mathcal K_d$ 并有原域 $M_3\to M_5$ CPTP 提升，具有原全部完整输入效果 $Y_j$ 和后继 $S_\rho$。

证明。复用第一卷定理 35.4 和本卷 (55.5) 的一般提升，明确为

$$
\begin{gathered}
D_+=\frac1{\sqrt2}\begin{pmatrix}1&1&0&0&0\\0&0&\sqrt2&0&0\\0&0&0&1&1\end{pmatrix},\quad
D_-=\frac1{\sqrt2}\begin{pmatrix}1&-1&0&0&0\\0&0&0&0&0\\0&0&0&-1&1\end{pmatrix},\\
\omega=D_+^\dagger AD_++D_-^\dagger DD_-,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\end{gathered}
\tag{88.1}
$$

$x\mapsto(D_+x,D_-x)$ 是 $\mathbb C^5\to\mathbb C^3\oplus N$ 的酉识别；$A,D$ 是 (54.2) 中实际正分解，故 $\omega$ 正且迹一。$T_\omega$ 的 Kraus 表为 $BP_+$ 及 $\sqrt{\lambda_r}w_rf^\dagger$，其中 $\omega=\sum_r\lambda_rw_rw_r^\dagger$；伴随平方和为 $P_++ff^\dagger=I_3$。第一卷 (35.3)、(35.6) 给

$$
\begin{gathered}
T_\omega^*(J_0)=\operatorname{diag}(1,0,d),\\
T_\omega^*(J_1)=\frac1{16}\begin{pmatrix}1&3&0\\3&9&0\\0&0&6-5d\end{pmatrix},\qquad
T_\omega^*(J_2)=\frac1{32}\begin{pmatrix}17&3&0\\3&9&0\\0&0&6+11d\end{pmatrix},\\
\mathcal GT_\omega(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho]B^\dagger=S_\rho(X).
\end{gathered}
\tag{88.2}
$$

三个 $Y_j$ 是 $(q,r,f)$ 输入基中的完整矩阵，含全部跨条目，不只是 $ff$ 上的三个数；原递推 $J_{j+2}=(J_j+J_{j+1})/2$、$j\ge1$ 延续到所有深度。故这是原纤维提升而非矩拟合。第二卷 (39.5)、(39.7) 再给同一时间词下的两个原始联合终端响应。

对纯曲线取 $A=\psi_t\psi_t^\dagger,D=0$，其物理纯向量正是 (70.4) 的

$$
\eta_t=\sqrt d\,p_H+\sqrt d(e^{\mathrm it}-1)Br
+\mathrm i(3e^{\mathrm it}-2)f_d(t)c_H,
\quad p_H=Bq,\quad c_H=(e_0+e_1-e_3-e_4)/2.
\tag{88.3}
$$

供应恒等式 $D_+^\dagger(a,h_{\rm out},g)=(p_H,Br,c_H)$、$K_j\eta_t=B\psi_t/\sqrt2$ 保留实际五维仪器。对 (86.7)，取 $u_+=D_+^\dagger u_\epsilon$、$w_-=D_-^\dagger w_v$，则 $\omega=u_+u_+^\dagger+\epsilon w_-w_-^\dagger$。其每个参数来自已证的原正分解，因而直接消费相同的 (88.1)–(88.2)。这些提升的存在没有增加实际制备分解或访问其环境的权限。∎

**定理 88.2（$d=1/2$ 的相同预测、不同混谱与效果）。** 对任意允许的 $\theta$，原态

$$
\rho_{\rm mix}=\tfrac12(aa^\dagger+gg^\dagger)
\tag{88.4}
$$

在 $p=1/4,3/8,1/2$ 三个实现中的谱分别为

$$
\{1/2,1/2,0\},\qquad\{7/12,5/12,0\},\qquad\{2/3,1/3,0\},
\tag{88.5}
$$

纯度分别为 $1/2,37/72,5/9$。首末两者的熵分别为 $\log2$ 和 $-\frac23\log\frac23-\frac13\log\frac13$；三者的全部原生联合表相同。两个端点效果为投影，$p=3/8$ 的效率为 $14/15$。另一个合法校准 $p=2/5$ 的效率为 $15/16$、效果跨度为八。

证明。$a_{\xi}=1/\sqrt2$、$g_{\xi}=0$、$a\perp g$。$\rho_{\rm mix}$ 的迹、$aa$ 人口和 $C,E$ 两矩为 $1,1/2,1/2,7/32$，取 $A=\rho_{\rm mix},D=0$ 即为实际集合分解。其原提升为 (88.1)，$\omega=(p_Hp_H^\dagger+c_Hc_H^\dagger)/2$，不替换原后继。

$G_pa$ 与 $G_pg$ 仍正交；其平方范数为 $2p+2(1-p)/3$ 和 $4(1-p)/3$。故两个非零本征值为 $(1+2p)/3$、$2(1-p)/3$，代入给 (88.5) 及纯度、熵。用 (85.6) 给效果数值；$c=1/4$ 时 (85.8) 为 $p=2/5$，定理 87.1 给八维跨度。所有表相同直接由 (86.10)，不是只相同于某个有限终点。∎

**定理 88.3（原纯对的无限制区分性仍依校准而变）。** 在 $d=1/2$，取原纯态及其原五维提升

$$
\psi_\pm=(a\pm\mathrm i g)/\sqrt2,\qquad
\eta_\pm=(p_H\pm\mathrm i c_H)/\sqrt2.
\tag{88.6}
$$

$p=1/4$ 时两个编码正交，迹范数距离为二；$p=1/2$ 时重叠模为 $1/3$，距离为 $4\sqrt2/3$。两种表示对各个原世界仍给相同的全部原生联合表，但不存在将后一对编码同时送回前一对的 CPTP 映射。

证明。$\psi_\pm$ 是 (85.9) 在 $t=0$ 的两个原相位符号，或直接取 $A=\psi_\pm\psi_\pm^\dagger,D=0$ 检验原约束。(88.1) 的 $\omega=\eta_\pm\eta_\pm^\dagger$ 给同一个原域提升。编码纯向量 $G_p\psi_\pm$ 已归一化，其内积为

$$
\langle G_p\psi_+,G_p\psi_-\rangle=(4p-1)/3.
\tag{88.7}
$$

两纯态的迹范数距离为 $2\sqrt{1-|\langle\varphi,\chi\rangle|^2}$，代入得到所列值。CPTP 迹距离收缩排除从 $4\sqrt2/3$ 到二的同时映射。它没有说两个不同原世界的原生表彼此相等；相等的是同一世界在不同校准中的表。因而受限原生表等价没有供应所有量子决策、任意效果或带辅助系统统计实验的等价。∎

## 89. 条件酉守恒、擦除记录与相干记录的三个对象

**定理 89.1（每个固定校准内的守恒及其适用对象）。** 对定理 82.2 中任意固定的实现，每个给定历史的归一化后继都是酉共轭。因此它保持该实现内的整个密度谱、熵以及成对态的迹距离和保真度。两个分支共同固定的可观察量代数为

$$
\{X:U_j^\dagger XU_j=X\ (j=0,1)\}
=\operatorname{span}_{\mathbb C}\{I_3,P_{\rm singlet}\}.
\tag{89.1}
$$

其准备人口 $\operatorname{Tr}(P_{\rm singlet}\sigma(\rho))=p$ 对原态不变，却在预测等价校准之间变化。擦除分支标签的通道一般不保持记忆熵。

证明。这里 $S(X)=-\operatorname{Tr}(X\log X)$，约定 $0\log0=0$；成对保真度取 $\operatorname{Fid}(X,Y)=\|\sqrt X\sqrt Y\|_1^2$，迹范数距离不除以二。每个历史总质量为 $2^{-|h|}>0$，归一化后继为 $\operatorname{Ad}_{U_h}$，酉不变量遂给第一项。这是给定历史的数学后继，不授予选支操作。固定量等价于与两个酉交换，因而与其紧闭群交换。该群包含 $1\oplus SU(2)$，其单态与双态不等价，双态复不可约；Schur 引理给块标量，反向这两个块标量确实与实际两个生成元交换。故有 (89.1)，其人口值由 (82.4) 给出。

标准代表的非选择通道为

$$
\Lambda(X)=\tfrac12(V_0XV_0^\dagger+V_1XV_1^\dagger)
=\operatorname{Ad}_{V_0}\left(\frac{X+WXW}{2}\right).
\tag{89.2}
$$

它为随机酉通道，熵凹性给 $S(\Lambda(X))\ge S(X)$，但不保证等号。对原 $d=1/2$、标准校准 $p=c$ 的纯 $\psi_+$，其 $f$ 人口为 $5/16$，$W$ 的正扇区人口为 $11/16$；去相干后两块纯向量正交，故输出谱为 $\{11/16,5/16,0\}$，熵严格大于输入的零。额外酉 $V_0$ 不改变该谱。因此不能把条件酉守恒写成擦除标签后的无条件熵守恒。∎

**定理 89.2（相干记录等距的存在及输出谱）。** 对每个固定实现，数学映射

$$
\mathcal V:\mathbb C^3\longrightarrow\mathbb C^3\otimes\mathbb C^2,
\qquad \mathcal Vx=\frac1{\sqrt2}\sum_{j=0}^1U_jx\otimes|j\rangle
\tag{89.3}
$$

是等距；保留其整个输出时，$\mathcal VX\mathcal V^\dagger$ 与 $X$ 有相同非零谱及熵。若记录被去相干，联合输出熵为 $S(X)+\log2$；若再丢弃记录，记忆输出为 $\Lambda(X)$。等距的存在不推出原生合同提供相干环境、记录相位或逆向控制访问。

证明。$\mathcal V^\dagger\mathcal V=\frac12\sum_jU_j^\dagger U_j=I_3$，谱结论来自等距嵌入。记录去相干后是两个正交块 $\frac12U_jXU_j^\dagger$，其本征值为 $X$ 每个本征值的一半各重复两次，所以熵为所列值；偏迹给 (89.2) 的相应坐标版本。给 $U_j$ 独立乘相位不改变分支 CP 映射，却可改变 (89.3) 的记录间相位；原合同没有辨别这些相位的记录测量。因此这个数学扩张也没有补出原合同未取得的操作权利。∎

## 90. 本源对应、成熟工具与尚待取得的校准关系

**定义 90.1（分类的数学归属及精确供应）。** 定理 82.2 的 `repo-derived` 内容是：在原全部复 $\mathcal K_d$ 及全词双终端合同中，对全部三维复 CP 竞争者给出唯一残余参数的闭区间、同时匹配两个生成元、并用原混合边界排除不被原生读数看到的仿射偏移。这是源特定综合，不主张工具发明权或全域文献优先权。既有复三维最小值、原集合与提升、实六维最小值和有限记录结果是供应，不作为这项分类的新发现。

原对象的参数对应为：第一卷 §17.1 的五维 $K_0,K_1,B$ 及 $U,W,E$ 固定 (82.1)；第一卷定理 35.2、35.4、35.6 固定全复输入、完整 $\mathcal K_d$、原 $N$ 及全部提升；第二卷定理 39.3–39.4 固定时间顺序、双终端及 $2^{-|h|}$ 权重，定理 40.1 固定源 $I_3$ 加八个实际加权效果；本卷引理 63.1 及 (64.10)–(64.12) 固定实际 $SU(2)$ 和八维源可达空间；引理 70.1–70.2 固定原纯曲线、五维提升和矩阵条目函数空间。这里没有重作实五维排除或把实因子成本当成复因子成本。

作为 `literature-attested` 的中间工具，Choi–Effros，*Injectivity and operator spaces*，J. Functional Analysis **24**, 156–209，定理 3.1，及 [Prunaru 定理 1](https://arxiv.org/html/1304.6664v2)，只在 (83.7) 的完整复 UCP 幂等元处消费。保单位性给收缩性，像继承的是完整矩阵序；(83.8) 的乘法域属于抽象余域的收缩。有限维复 $C^*$ 直和结构、Schwarz 及乘法域都是成熟工具，物理维数约束由 (83.9) 的实际忠实表示桥承担。

[Nayak–Sen 定理 2.1–2.2](https://arxiv.org/html/quant-ph/0605041v4) 的全域逆条件不能从初始可达公平性省略：定理 83.1 先给全矩阵 CP 逆，(84.1)–(84.2) 再使用原 TP 和得到逐支 TP，此后其等维 CPTP 逆特例才适用。没有把预测商上的可逆性代替一个 CP 全域逆。

[Hall，*An Elementary Introduction to Groups and Representations*](https://arxiv.org/html/math-ph/0005032v1)，命题 2.12、定理 3.23、5.33 及有限维 $SU(2)$ 表示部分，分别供应 $SU(2)$ 单连通性、闭矩阵群的局部指数及单连通域的 Lie 同态积分；对象是已证明紧闭的矩阵群，核理想以 Ad 不变内积显式分裂。Schur 引理的实版本只给非零交织可逆，复标量交换子部分不能用于实四维基本模；(84.4) 明确保留其完整四元数交换子，(84.5) 用两个原生成元而非仅 $SU(2)$ 排除混合交织。隐函数定理只在 (86.6) 非零的四实坐标导数处使用；局部解经 (86.7) 回到原正分解和实际五维提升。

[Monras–Winter，*Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*](https://arxiv.org/html/1412.3634v1) 供应可达／零观察商及 CP 正实现的成熟背景，其平稳过程与锥合同不直接等于本源带制备索引和双终端的合同。(83.5) 的商、可达支持及复成本逐项由原记录建立。[Jenčová，*Comparison of quantum channels and statistical experiments*](https://arxiv.org/html/1512.07016v2)，定理 4 的随机化判据要求相应量子决策空间或辅助系统检验；受限原生词效果未供应这些测试，故不能由原生表等价直接推出 CPTP 统计等价，定理 88.3 给出本源的实际障碍。Lin 等 [arXiv:1810.05631v2](https://arxiv.org/abs/1810.05631v2) 的制备／门／读出共同规范自由度是已有背景；本源的新增负担是整个原集合上的穷尽分类和隐藏仿射项消去，而非重新命名一般规范例子。

**定义 90.2（条件重建与具体的取得问题）。** 定理 82.2 是在给定复 Hilbert 载体、Born 配对、复 Kraus CP、仿射混合语义、仪器组合以及 (54.2)、(54.8) 的实际源／取得合同内的条件重建。它没有分类更大维复实现，没有给噪声或有限样本分类，没有确定原擦除菜单的全 $d$ 最小最大中心，没有确立量子原则的物理起源或一组逻辑最小公设，也没有无条件信息守恒或经验物理结论。$d=0,1$ 或 $\sin(2\theta)=0$ 不属于该定理；零圆半径、源维数及导数在这些被排除边界须另行分析。

剩余的起源侧问题可以具体表为：原环境就绪、重复仪器和终端记录之外，哪一个实际取得的共同关系使兼容表示族上的 $p$ 及仍存坐标自由度成为可认证量？若另供应动态单态投影 $P_{\rm singlet}$ 的已标定读出，其概率就是 $p$，因此会固定这一个参数；但 (89.1) 中该算子的数学存在及守恒没有供应测量它的权限。原生表不变时，没有只对它后处理的函数能区分不同 $p$。单独取得 $F$ 是投影仍留下 $p=c$ 与 $p=1/2$ 两个不同端点；单独取得效果效率也一般留下最小值两侧的两个校准。这些正是待补的关系辨识义务，而非把某个额外操作直接加入既有合同。

若目标还包括固定共同酉坐标或共轭方向，新增关系须相应打破该共同等价，例如经实际供应的相干参考及其联合校准；只是宣称有共同来源或可以写出一个复坐标并不完成它。紧闭包、Haar 平均、群逆和正过滤在证明中约束全部精确兼容实现，始终不增加控制、选支、独立副本、环境或相位访问。精确概率等式亦不等于有限实验已取得这些实数。原全参数最小最大、有限噪声和取得问题保持各自原目标与量词，不能被此三维分类替换。

## 追加锚（本行以下为增补区）

## 91. 单个原纯制备与固定混合控制的比较合同

**定义 91.1（固定源、时间词与一个控制类型）。** 保留 (54.1) 的五维 $H$、等距 $B$、$U,W,\xi,e,f,q,r$ 及 $E=qq^\dagger$。在本节以后，$N$ 专指一个酉矩阵，不指 (54.1) 的子空间 $\ell^\perp$。固定

$$
\begin{gathered}
0<d<1,\qquad c=d/2,\qquad \sin(2\theta)\ne0,\qquad P_\xi=\xi\xi^\dagger,\\
a=Uq,\quad g=Uf,\quad
\psi=\sqrt d\,a+\mathrm i\sqrt{1-d}\,g,\quad
\rho_0=\psi\psi^\dagger,\\
V_j=U\exp(\mathrm i\theta W)W^j,\qquad
A_j=\tfrac12\operatorname{Ad}_{V_j}\quad(j=0,1),\\
N\in U(3),\qquad [N,P_\xi]\ne0,\qquad A_N=\operatorname{Ad}_N.
\end{gathered}
\tag{91.1}
$$

这里 $A_j$ 是 qutrit 上的 CP 分支映射；(54.7) 的五维 Kraus 算子在本增补中记为 $\widehat K_{\theta,j}$，避免把算子与超算子混同。$N$ 是额外给定、已安装且可重复的同一个确定性控制类型；其存在和取得是合同前提。两个原生随机分支仍是原来的同一个仪器，角度始终固定。

对字母表 $\{0,1,N\}$ 上的时间词 $w=b_1\cdots b_n$，最左字母最早作用，置

$$
\begin{gathered}
U_0=V_0,\quad U_1=V_1,\quad U_N=N,\qquad
U_w=U_{b_n}\cdots U_{b_1},\\
A_w=A_{b_n}\cdots A_{b_1}
=2^{-k(w)}\operatorname{Ad}_{U_w},\qquad
k(w)=\#\{t:b_t\in\{0,1\}\},\\
p(w,1)=\operatorname{Tr}(EA_w\rho_0),\qquad
p(w,0)=\operatorname{Tr}((I_3-E)A_w\rho_0).
\end{gathered}
\tag{91.2}
$$

空词的 $U_\varnothing=I_3$、$A_\varnothing=\mathrm{id}$、$k(\varnothing)=0$。每个词的原始总质量为

$$
p(w,0)+p(w,1)=2^{-k(w)}.
\tag{91.3}
$$

词中的 $0,1$ 指预定仪器时序中实际保留的标签事件，不是可强迫发生的操作。某个位置的 $N$ 在该次仪器使用数之后固定执行，与此前出现的随机标签无关；比较一个词的坐标不丢弃同一时序中的其他历史。

**假设 91.2（唯一竞争制备和完整矩阵域的合法性）。** 竞争者只已知其载体为 $\mathbb C^3$，由一个任意密度矩阵 $\sigma_0$、一个固定效果 $F$ 和三个固定复线性映射组成：

$$
\begin{gathered}
\sigma_0\succeq0,\quad \operatorname{Tr}\sigma_0=1,\qquad
0\preceq F\preceq I_3,\\
B_0,B_1:M_3(\mathbb C)\longrightarrow M_3(\mathbb C)\ \text{CP},
\qquad B_0+B_1\ \text{TP},\\
B_N:M_3(\mathbb C)\longrightarrow M_3(\mathbb C)\ \text{CPTP}.
\end{gathered}
\tag{91.4}
$$

这些条件从一开始作用于全部矩阵域。每个时间词使用同一组映射，$B_w=B_{b_n}\cdots B_{b_1}$，竞争联合概率为

$$
\widetilde p(w,1)=\operatorname{Tr}(FB_w\sigma_0),\qquad
\widetilde p(w,0)=\operatorname{Tr}((I_3-F)B_w\sigma_0).
\tag{91.5}
$$

不假设 $\sigma_0$ 纯、$F$ 投影、可达或效果信息完备、逐支公平、分支酉、逆为 CP、表示之间有正合同，亦不给整个 $\mathcal K_d$ 指派任何竞争制备。精确概率等式是数学前提，不是有限样本已获得精确实数的断言。已知复维数、Born 迹配对、CP 合法性和固定时间齐次组合均保留为前提。

**命题 91.3（这一制备的原五维提升及完整矩映射）。** (91.1) 只用一个原相容纯后继；其原域 CPTP 提升可以取 (55.5)、(88.1) 在 $A=\rho_0,D=0$ 时的构造。该提升保留第一卷 (35.3) 的完整源矩映射，并与 $S_{\rho_0}$ 在全部复矩阵及任意有限未触动参考上一致。

证明。$a,g$ 正交归一，$U\xi=\xi$，且

$$
\langle \xi,a\rangle=1/\sqrt2,\quad
\langle \xi,g\rangle=0,\quad
\langle q,a\rangle=1/4,\quad
\langle q,g\rangle=\sqrt6/4.
$$

所以 $\rho_0$ 纯且迹一，$a^\dagger\rho_0a=d$，并有

$$
\operatorname{Tr}(P_\xi\rho_0)=c,\qquad
\operatorname{Tr}(C\rho_0)=d,\qquad
\operatorname{Tr}(E\rho_0)=\frac{6-5d}{16}=e_d,
\quad C=2P_\xi.
\tag{91.6}
$$

最后一个等式使用实重叠与 $\mathrm i$ 的相对相位，交叉实部为零。故 $A=\rho_0,D=0$ 满足 (54.2) 的全部条件；这仅证明这一点有原域来源。

令 $D_+$ 为 (55.5) 的原 $3\times5$ 余等距，置

$$
\eta=D_+^\dagger\psi,\qquad
\omega=\eta\eta^\dagger,\qquad
\mathcal T_0(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\tag{91.7}
$$

$D_+D_+^\dagger=I_3$ 使 $\|\eta\|=1$。两项的 Kraus 算子 $BP_+$、$\eta f^\dagger$ 的伴随平方和为 $P_++ff^\dagger=I_3$，因此 $\mathcal T_0$ 是原 $M_3\to M_5$ CPTP 映射。(88.2) 的假设正是本处的正分解及 (91.6)，所以在输入基 $(q,r,f)$ 中，其原完整响应是

$$
\begin{aligned}
\mathcal T_0^*(J_0)&=\operatorname{diag}(1,0,d),\\
\mathcal T_0^*(J_1)&=\frac1{16}
 \begin{pmatrix}1&3&0\\3&9&0\\0&0&6-5d\end{pmatrix},\\
\mathcal T_0^*(J_2)&=\frac1{32}
 \begin{pmatrix}17&3&0\\3&9&0\\0&0&6+11d\end{pmatrix}.
\end{aligned}
\tag{91.8}
$$

这里 $J_0=P=BEB^\dagger$，$J_j=(\mathcal G^*)^j(P)$，$\mathcal G(Y)=\sum_{j=0}^1K_jYK_j^\dagger$；$K_j$ 是 (54.1) 的原 Kraus 算子。原递推 $J_{j+2}=(J_j+J_{j+1})/2$、$j\ge1$ 使 (91.8) 延伸到全部原深度。因此没有用单个输入的三个标量替代源的完整矩映射。

由 $D_+B=UP_+$、$D_-B=UP_-$、$D_-D_+^\dagger=0$，直接对任意 $X\in M_3(\mathbb C)$ 得

$$
\mathcal G\mathcal T_0(X)
=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho_0]B^\dagger
=S_{\rho_0}(X).
\tag{91.9}
$$

对任意 $r\ge1$ 和 $X\in M_r\otimes M_3$，令
$X_{ff}=(I_r\otimes f^\dagger)X(I_r\otimes f)$。其完整参考形式为

$$
\begin{aligned}
(\mathrm{id}_{M_r}\otimes S_{\rho_0})(X)
={}&(I_r\otimes BUP_+)X(I_r\otimes P_+U^\dagger B^\dagger)\\
&+X_{ff}\otimes B\rho_0B^\dagger .
\end{aligned}
\tag{91.10}
$$

这是所有复矩阵上的恒等式，故包括纠缠参考，不要求参考为独立副本。第二卷 (39.5) 给
$\widehat K_{\theta,h}B=2^{-|h|/2}BV_h$。对于给定 $N$，数学上的五维角块延伸
$\widetilde N=BNB^\dagger+(I_5-BB^\dagger)$ 是酉且满足 $\widetilde NB=BN$。逐次复合于是保留 (91.2) 的两种终端结果、联合权重及未触动参考对应。这个延伸公式只说明给定控制的表示相容性；它不从原无控制菜单推出 $N$ 已被取得。后面的辨识只使用合同所给的一个 $\rho_0$、原随机仪器及已安装 $N$，不使用整个 $\mathcal K_d$ 的制备或仿射编码。∎

## 92. 实际单态的八维原生跨度和每个混合控制的第九列

**定理 92.1（全角度原生跨度及有限达到深度）。** 对 (91.1) 的源，定义

$$
\mathscr S_c=\{X\in\operatorname{Herm}_3:
 \operatorname{Tr}(P_\xi X)=c\operatorname{Tr}X\},\qquad
\mathscr R_\ell=\operatorname{span}_{\mathbb R}
 \{A_u\rho_0:u\in\{0,1\}^*,\ |u|\le\ell\}.
\tag{92.1}
$$

则原生有限词列的完整实跨度恰为八维 $\mathscr S_c$，且 $\mathscr R_7=\mathscr S_c$。可以选出 $u_1,\ldots,u_8$，各长至多七，令 $u_1=\varnothing$，使 $r_i=A_{u_i}\rho_0$ 成为其基。

证明。在 $(\xi,e,f)$ 中去掉每个 $V_j$ 的共同标量相位后，

$$
\begin{gathered}
V'_0=1\oplus B_z,\qquad V'_1=V'_0(1\oplus J),\qquad
z=e^{-2\mathrm i\theta},\\
B_z=L D_z,\quad
L=\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\quad
D_z=\operatorname{diag}(1,z),\quad J=\operatorname{diag}(1,-1).
\end{gathered}
\tag{92.2}
$$

这与引理 63.1 的 $R,D_\theta,Z$ 分别对应为 $L,D_z,J$，而不是另一个全族分类的表示。其假设恰为 $z\notin\{1,-1\}$。引理 63.1 因而给实际 $1\oplus SU(2)$ 位于原生正词闭包内；对有理 $\theta/\pi$ 同样成立。该引理的有限投影群排除使用代数整数的域范数，(55.7)–(55.8) 给相同源矩阵的迹／行列式障碍；这里不以无理角论证替代有理角情形。

每个原生酉与 $P_\xi$ 交换，故每个 $r_u$ 都在 $\mathscr S_c$。由 (91.6) 可将
$\psi=\sqrt c\,\xi+\eta_0$，其中 $\eta_0\perp\xi$、$\|\eta_0\|^2=1-c$。$SU(2)$ 在 $\mathbb C^2$ 单位球面上传递，所以原生纯态轨道闭包包含

$$
Q(v)=|\sqrt c\,\xi+\sqrt{1-c}\,v\rangle
       \langle\sqrt c\,\xi+\sqrt{1-c}\,v|,
\qquad v\perp\xi,\quad \|v\|=1.
\tag{92.3}
$$

有限词的实线性跨度在有限维中是闭的；$A_u\rho_0$ 与
$U_u\rho_0U_u^\dagger$ 只差非零标量，故这些轨道极限也在同一跨度内。

$Q(v)-Q(-v)$ 等于
$2\sqrt{c(1-c)}(\xi v^\dagger+v\xi^\dagger)$。令 $v$ 依次取 $e,\mathrm i e,f,\mathrm i f$，得到四个独立交叉方向。又

$$
Q(v)+Q(-v)=2cP_\xi+2(1-c)vv^\dagger .
\tag{92.4}
$$

对下块的两条正交单位向量求和，得到非零迹方向
$H_c=\operatorname{diag}(c,(1-c)/2,(1-c)/2)$。将 (92.4) 减去 $2H_c$，下块为
$2(1-c)(vv^\dagger-I_2/2)$；取 Pauli 三个轴的纯投影给下块全部三个无迹 Hermitian 方向。四个交叉方向、三个下块无迹方向及 $H_c$ 独立，共八维，恰张成 (92.1) 的超平面。

最后，

$$
\mathscr R_{\ell+1}
=\mathscr R_\ell+A_0\mathscr R_\ell+A_1\mathscr R_\ell.
\tag{92.5}
$$

若某一步在维数八以前停滞，则该空间已对两个生成元不变，以后永不再增长，与刚证得的完整跨度矛盾。从 $\dim\mathscr R_0=1$ 开始，至多七次严格增长即达到八。因此可以在深度七内从空词起扩充成基。∎

**定理 92.2（每个混合 $N$ 都使任意原生基逃逸）。** 对定理 92.1 的任意上述基，总有 $k\in\{1,\ldots,8\}$ 使

$$
r_9=Nr_kN^\dagger\notin\mathscr S_c.
\tag{92.6}
$$

置 $u_9=u_kN$，则 $r_i=A_{u_i}\rho_0$、$1\le i\le9$ 是 $\operatorname{Herm}_3$ 的基，$|u_9|\le8$。结论包括 $d=2/3$ 和 $N\xi$ 完全位于下双态空间的情形。

证明。$\mathscr S_c$ 的迹配对法向量为 $D_c=P_\xi-cI_3$。若
$\operatorname{Ad}_N\mathscr S_c\subseteq\mathscr S_c$，维数相同使二者相等，取正交补得到

$$
N^\dagger D_cN=\lambda D_c,\qquad
\lambda\in\mathbb R\setminus\{0\}.
\tag{92.7}
$$

但

$$
\det D_c=(1-c)(-c)^2=c^2(1-c)>0,
$$

故取行列式给 $\lambda^3=1$，实数 $\lambda$ 必为一。于是
$N^\dagger P_\xi N=P_\xi$，与混合假设矛盾。若八个基向量都不逃逸，整个 $\mathscr S_c$ 会满足上述包含，故至少一个逃逸。添加该列使秩为九。

此证明不除以 $\operatorname{Tr}D_c=1-3c$；在 $c=1/3$ 即 $d=2/3$ 仍有非零行列式。它也没有对 $\langle\xi,N\xi\rangle$ 的非零性或大小作假设。∎

## 93. 四张有限加权表与全矩阵迹保持相似

**定义 93.1（原生效果行、插入块与精确标量）。** 固定按定理 92.1–92.2 选择的九个前缀，仍保留 $u_1=\varnothing$。八个后缀按以下顺序固定：

$$
(h_1,\ldots,h_8)=(\varnothing,0,1,00,10,000,010,100).
\tag{93.1}
$$

置

$$
e_0=I_3,\qquad
e_m=Z_{h_m}=2^{-|h_m|}V_{h_m}^\dagger EV_{h_m}\quad(1\le m\le8).
\tag{93.2}
$$

定义四个 $9\times9$ 实矩阵，行标 $m=0,\ldots,8$、列标 $i=1,\ldots,9$：

$$
H_{mi}=\operatorname{Tr}(e_mr_i),\qquad
H^a_{mi}=\operatorname{Tr}(e_mA_a(r_i)),
\quad a=0,1,N.
\tag{93.3}
$$

非迹行的条目恰为原事件

$$
H_{mi}=p(u_i h_m,1),\qquad
H^a_{mi}=p(u_i a h_m,1)\quad(m\ge1).
\tag{93.4}
$$

迹行的条目则是没有后缀的两个终端结果之和：

$$
\begin{aligned}
H_{0i}&=p(u_i,0)+p(u_i,1),\\
H^a_{0i}&=p(u_i a,0)+p(u_i a,1).
\end{aligned}
\tag{93.5}
$$

例如 $u_kN$ 的列是先执行 $u_k$ 再执行 $N$；绝不是先在 $\rho_0$ 上执行 $N$。竞争表 $\widetilde H,\widetilde H^a$ 用同一时序和 (91.5) 定义。其非迹行包括完整的竞争后缀映射 $B_{h_m}$，没有假设其公平性。

**定理 93.2（有限表强制的完整相似接口）。** 在假设 91.2 下，只要求四张有限表逐项相等：

$$
\widetilde H=H,\qquad
\widetilde H^a=H^a\quad(a=0,1,N).
\tag{93.6}
$$

则存在唯一可逆实线性 $T:\operatorname{Herm}_3\to\operatorname{Herm}_3$，满足

$$
\begin{gathered}
\operatorname{Tr}(TX)=\operatorname{Tr}X,\qquad
T\rho_0=\sigma_0,\qquad T^*F=E,\\
B_jT=TA_j=\tfrac12T\operatorname{Ad}_{V_j}\quad(j=0,1),\qquad
B_NT=T\operatorname{Ad}_N.
\end{gathered}
\tag{93.7}
$$

所有恒等式作用于全部 $\operatorname{Herm}_3$，并通过唯一复线性延伸作用于全部 $M_3(\mathbb C)$。$T^{-1}$ 也保迹。此阶段不预设或断言 $T$ 正、CP 或保单位。

证明。先按第二卷定理 40.1 使用确切的效果基，其假设映射为同一 $U,W,E$、同一 $\theta$、同一最早标签在左的 $V_h$ 和 (93.1) 的词序。对于实坐标

$$
x(X)=(X_{00},X_{11},X_{22},
 \Re X_{01},\Re X_{02},\Re X_{12},
 \Im X_{01},\Im X_{02},\Im X_{12})^{\mathsf T},
\tag{93.8}
$$

以 $x(e_0),\ldots,x(e_8)$ 为列的矩阵 $\mathcal E$ 满足

$$
\det\mathcal E=\frac{6561}{2^{36}}\sin^7(2\theta)\ne0.
\tag{93.9}
$$

供应 (40.4) 的权重没有删掉；八个词长之和为十五，故相对于不加权效果的 (40.12)，行列式恰多 $2^{-15}$。迹配对不是 (93.8) 的普通点积，而是

$$
\operatorname{Tr}(XY)=x(X)^{\mathsf T}J_{\rm tr}x(Y),\qquad
J_{\rm tr}=\operatorname{diag}(1,1,1,2,2,2,2,2,2).
\tag{93.10}
$$

因此实际行泛函矩阵为 $\mathcal E^{\mathsf T}J_{\rm tr}$，其行列式为
$64\det\mathcal E\ne0$。坐标行列式与真实迹配对的度量因子在此分别保留。

用无坐标形式定义四个线性映射

$$
\begin{aligned}
R:\mathbb R^9\to\operatorname{Herm}_3,\quad&R\delta_i=r_i,\\
L:\operatorname{Herm}_3\to\mathbb R^9,\quad&(LX)_m=\operatorname{Tr}(e_mX),\\
S:\mathbb R^9\to\operatorname{Herm}_3,\quad&S\delta_i=s_i:=B_{u_i}\sigma_0,\\
M:\operatorname{Herm}_3\to\mathbb R^9,\quad&
(MX)_0=\operatorname{Tr}X,\quad
(MX)_m=\operatorname{Tr}(F B_{h_m}(X))\ (m\ge1).
\end{aligned}
\tag{93.11}
$$

定理 92.2 使 $R$ 可逆，(93.9)–(93.10) 使 $L$ 可逆。由 (93.6) 和完整时间顺序，

$$
LR=H=MS.
\tag{93.12}
$$

故 $\operatorname{rank}H=9$。竞争 Hermitian 空间也恰为九维，因此 $M,S$ 均可逆；竞争的可达性与可观察性由此推出，不能作为额外承诺输入。取

$$
T=SR^{-1},\qquad MT=L.
\tag{93.13}
$$

插入块的等式给

$$
MB_aS=H^a=LA_aR,\qquad a=0,1,N.
\tag{93.14}
$$

将 $S=TR$、$L=MT$ 代入并消去可逆的 $M,R$，得到三个完整空间的交织恒等式。$MT=L$ 的迹行给 $\operatorname{Tr}(TX)=\operatorname{Tr}X$；$h_1=\varnothing$ 的行给 $T^*F=E$；$u_1=\varnothing$ 的列给 $T\rho_0=\sigma_0$。$R$ 是基，故满足这些列匹配的 $T$ 唯一。

每个复矩阵唯一写成 $X+\mathrm iY$、$X,Y$ Hermitian。定义
$T(X+\mathrm iY)=TX+\mathrm iTY$，得到可逆复线性、保持伴随的延伸；全部恒等式随之延伸。由 $T$ 可逆且保迹，令 $Y=TX$ 便得 $\operatorname{Tr}(T^{-1}Y)=\operatorname{Tr}Y$。

(93.12)–(93.14) 使用成熟的有限 Hankel／最小线性实现相似方法；可达／零观察商及最小实现相似的文献背景见 Monras–Winter，[*Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*](https://arxiv.org/html/1412.3634v1)，§4、定理 9。该文的平稳过程合同不是本题的单制备、外定时序和双终端合同；这里有限四表的推导由 (93.11)–(93.14) 直接承担，没有从该一般背景借入平稳性、全词已知或额外控制。九个列是一个制备的次归一化历史事件，也没有成为九个独立可制备状态。∎

## 94. 插入质量、全域 CPTP 逆与固定映射的全词后果

**定理 94.1（有限表强制公平、可逆酉分支和所有数学词）。** 在定理 93.2 的条件下，

$$
C_0=2B_0,\qquad C_1=2B_1,\qquad C_N=B_N
\tag{94.1}
$$

都是完整 $M_3(\mathbb C)$ 上的 CPTP 映射，并各有完整 CPTP 逆，因而各自为酉共轭。它们通过同一个 $T$ 满足

$$
C_a=T\operatorname{Ad}_{U_a}T^{-1},\qquad
C_w=T\operatorname{Ad}_{U_w}T^{-1},\qquad
B_w=2^{-k(w)}C_w
\tag{94.2}
$$

对每个字母和每个有限正向词成立。这尚未选定三个酉代表的共同坐标；该共同性由后面的单态／单效果论证确定。

证明。插入质量行逐列给

$$
\operatorname{Tr}(B_js_i)
=H^j_{0i}
=\operatorname{Tr}(A_jr_i)
=\tfrac12\operatorname{Tr}r_i
=\tfrac12\operatorname{Tr}s_i,\qquad j=0,1.
\tag{94.3}
$$

$s_i$ 是整个竞争 Hermitian 空间的基，故
$B_j^*(I_3)=I_3/2$ 在全矩阵域成立。CP 由假设 91.2 给出，故 $2B_j$ CPTP。$C_N$ 的全域 CPTP 性本来就是前提。这一步使用插入的质量和秩九；原先只假设 $B_0+B_1$ TP 并不能推出逐支公平。因子二是证明中映射的代数缩放，没有对实验分支条件化或给予强迫标签的操作。

由 (93.7) 立即得字母层的 (94.2)，然后按实际时间顺序复合得每个词的恒等式。固定映射在所有词上复用是前提；这里不把有限数据拟合到任意时间相关竞争者。

对每个 $a$，$\operatorname{Ad}_{U_a}$ 属于紧酉共轭群。有限个本征相位的同时回归给 $n_\nu\to\infty$，且

$$
\operatorname{Ad}_{U_a}^{\,n_\nu}\longrightarrow\mathrm{id},\qquad
C_a^{\,n_\nu-1}\longrightarrow
T\operatorname{Ad}_{U_a}^{-1}T^{-1}=C_a^{-1}.
\tag{94.4}
$$

可选 $n_\nu\ge2$；若阶有限，则取其阶的正倍数。每个 $C_a^{n_\nu-1}$ 都是全域 CPTP。有限维中 Choi 正锥及 TP 线性约束均闭，故其超算子极限 $C_a^{-1}$ 也是全域 CPTP。这在使用任何逆分类以前，已经给出
$C_a^{-1}C_a=\mathrm{id}$ 对所有复矩阵成立，特别包括所有密度矩阵，而不只包括已制备轨道。

此时才应用 Nayak–Sen，[*Invertible Quantum Operations and Perfect Encryption of Quantum States*](https://arxiv.org/html/quant-ph/0605041v4)，定理 2.1：其输入为 CPTP
$\mathcal E:M_p\to M_q$ 及 CPTP 左逆 $\mathcal D$，满足
$\mathcal D\mathcal E(\rho)=\rho$ 对每个输入密度矩阵成立。本处
$\mathcal E=C_a$、$\mathcal D=C_a^{-1}$、$p=q=3$，辅助维数
$\lfloor q/p\rfloor=1$，所以 $C_a$ 为酉共轭。实线性可逆、预测商可逆或一个轨道上的逆均不足以单独调用该结果；(94.4) 补足的正是完整矩阵逆条件。

(93.7) 与 (94.2) 还直接给

$$
\begin{aligned}
T(\operatorname{Ad}_{U_w}\rho_0)&=C_w\sigma_0,\\
C_w^*F&=(T^{-1})^*(U_w^\dagger EU_w).
\end{aligned}
\tag{94.5}
$$

因此对所有有限词，

$$
\operatorname{Tr}(FB_w\sigma_0)=\operatorname{Tr}(EA_w\rho_0),\qquad
\operatorname{Tr}(B_w\sigma_0)=2^{-k(w)}.
\tag{94.6}
$$

相减给补终端结果也相等。这些未测词等式是固定全域模型和有限秩九数据的数学后果，不是额外假定已观测的无限表。(94.4) 中的极限、归一化证明映射及逆均不授予新的物理控制。∎

## 95. 任意一个混合控制把实际原生闭包扩到 PU(3)

**定理 95.1（无一般位置例外的实际控制闭包）。** 对 (91.1) 的每个允许角度和每个 $[N,P_\xi]\ne0$，实际三个酉共轭的正词闭包恰为 $\operatorname{Ad}(PU(3))$。这包括 $\langle\xi,N\xi\rangle=0$；不要求 $N$ 接近恒等或单态／双态之间的重叠非零。

证明。由 (92.2) 和引理 63.1，去公共相位的原生酉闭群包含
$K=\{1\oplus u:u\in SU(2)\}$。令 $G\subseteq U(3)$ 为这些代表和 $N$ 生成的闭群，$\mathfrak g$ 为其 Lie 代数；它包含
$\mathfrak k=0\oplus\mathfrak{su}(2)$。闭矩阵群的 Lie 结构及连通分支由指数生成的事实，按引理 63.1 已列明的 Hall 定理 3.23 使用。单位分支在 $G$ 中正规，因此即使 $N$ 不在单位分支，也有

$$
N\mathfrak kN^\dagger\subseteq\mathfrak g.
\tag{95.1}
$$

以下直接验证其中一定存在交叉块，包含完全送入下双态的边界。写

$$
N^\dagger\xi=\alpha\xi+b,\qquad b\perp\xi,\qquad
s=\|b\|^2=1-|\langle\xi,N\xi\rangle|^2\in(0,1].
\tag{95.2}
$$

$s>0$ 与混合条件等价。令 $\sigma_1,\sigma_2,\sigma_3$ 为下双态标准 Pauli 矩阵，
$A_i=0\oplus\mathrm i\sigma_i\in\mathfrak k$，
$X_i=NA_iN^\dagger\in\mathfrak g$。则

$$
\begin{aligned}
\|(I_3-P_\xi)X_i\xi\|^2
&=\|A_iN^\dagger\xi\|^2
 -|\xi^\dagger X_i\xi|^2\\
&=s-|b^\dagger\sigma_i b|^2.
\end{aligned}
\tag{95.3}
$$

若 $b=(b_1,b_2)^{\mathsf T}$，三个实数
$b^\dagger\sigma_i b$ 为
$2\Re(\bar b_1b_2)$、$2\Im(\bar b_1b_2)$、
$|b_1|^2-|b_2|^2$，所以其平方和为
$(|b_1|^2+|b_2|^2)^2=s^2$。于是

$$
\sum_{i=1}^3\|(I_3-P_\xi)X_i\xi\|^2
=3s-s^2>0.
\tag{95.4}
$$

故有某个 $X\in\mathfrak g$ 的交叉块非零；当 $N\xi$ 完全在下双态空间时 $s=1$，右端为二，仍严格非零。

$Q=\operatorname{diag}(1,-1,-1)\in K$，$\mathfrak g$ 对其共轭不变。因此
$(X-QXQ)/2\in\mathfrak g$ 提取出纯交叉块

$$
K(z)=\begin{pmatrix}0&-z^\dagger\\z&0_{2\times2}\end{pmatrix},
\qquad 0\ne z\in\mathbb C^2.
\tag{95.5}
$$

$K$ 的共轭把 $K(z)$ 送到 $K(uz)$。$SU(2)$ 在该复二维球面上传递，球面的实跨度是整个 $\mathbb C^2$，故 $\mathfrak g$ 包含所有四个实交叉方向
$K(e_1),K(\mathrm i e_1),K(e_2),K(\mathrm i e_2)$。又

$$
[K(e_1),K(\mathrm i e_1)]
=\operatorname{diag}(-2\mathrm i,2\mathrm i,0).
\tag{95.6}
$$

此方向不在 $\mathfrak k$ 中。它与 $\mathfrak k$ 的三个方向及四个交叉方向共同给出八个独立无迹反 Hermitian 矩阵，恰为 $\mathfrak{su}(3)$。所以
$\mathfrak{su}(3)\subseteq\mathfrak g$，从指数生成和 $SU(3)$ 连通性得
$SU(3)\subseteq G$。所有酉共轭的像都在 $PU(3)$ 中，其像又包含整个 $PU(3)$，故共轭闭包恰为该群；无需主张额外标量 $U(1)$ 相位也被生成。

最后，在紧酉群中每个生成元的逆都是其正幂的极限，正词半群闭包因而等于所生成群的闭包。去掉公共标量相位从未改变任何共轭。故结论适用于实际三个正向映射，不需要安装逆，也不把闭包中的任意酉当成可在有限时间精确调用的控制。∎

## 96. 单态和单效果的两个锥约束及共同表示

**定理 96.1（有限单制备数据的同时酉／共同共轭分类）。** 对每个 (91.1) 的源及每个假设 91.2 的竞争者，四表等式 (93.6) 当且仅当存在一个固定 $R_0\in U(3)$ 和一个共同选择
$\kappa\in\{\mathrm{id},\text{逐项复共轭}\}$，使

$$
\begin{gathered}
\sigma_0=R_0\kappa(\rho_0)R_0^\dagger,\qquad
F=R_0\kappa(E)R_0^\dagger,\\
B_j=\tfrac12\operatorname{Ad}_{R_0\kappa(V_j)R_0^\dagger}\quad(j=0,1),
\qquad
B_N=\operatorname{Ad}_{R_0\kappa(N)R_0^\dagger}.
\end{gathered}
\tag{96.1}
$$

各分支恒等式作用于全部 $M_3(\mathbb C)$。同一个 $R_0$ 和同一个 $\kappa$ 同时作用于制备、效果及全部标签映射，不允许逐映射独立换基、独立共轭或交换标签。此时所有有限正向历史、两种终端结果及其完整联合质量均相等。$\sigma_0$ 的纯性、$F$ 的投影性及分支的公平／酉性均为结论。

证明。必要性先由定理 93.2、94.1 给一个可逆保迹 $T$、状态／效果恒等式及 (94.5)。到此还没有赋予 $T$ 或 $T^{-1}$ 正性。现分别使用源的一个纯制备和一个纯效果。

由竞争者的 $\sigma_0\succeq0$ 和每个正向 $C_w$ 的 CP 性，

$$
T(U_w\rho_0U_w^\dagger)=C_w\sigma_0\succeq0.
\tag{96.2}
$$

定理 95.1 使左端输入的闭包包含每个秩一投影：$PU(3)$ 在完整纯态射线空间上传递，且 $\rho_0$ 本身秩一。$T$ 有限维连续、正锥闭，故 $T(P)\succeq0$ 对每个秩一投影 $P$ 成立。任意正矩阵是这些投影的非负谱和，所以 $T$ 在整个正锥上为正。这里没有新给任何其他制备；轨道和极限只用于限制一个固定线性映射。

另由竞争效果 $F\succeq0$，(94.5) 独立给

$$
(T^{-1})^*(U_w^\dagger EU_w)=C_w^*F\succeq0.
\tag{96.3}
$$

正向群闭包为全部 $PU(3)$，取逆是紧群的同胚，故
$\{U_w^\dagger EU_w\}$ 的闭包也包含每个秩一投影。$E$ 的秩一性在此是源前提；竞争 $F$ 无此先验承诺。连续性和谱和给
$(T^{-1})^*$ 在全部正锥上为正。对任意 $X,Y\succeq0$，

$$
\operatorname{Tr}(Y T^{-1}X)
=\operatorname{Tr}(((T^{-1})^*Y)X)\ge0.
\tag{96.4}
$$

Hermitian 正锥对迹配对自对偶，故 $T^{-1}X\succeq0$。自对偶性也可直接看出：若某个 Hermitian 矩阵有负本征值，取该本征向量的秩一投影配对即为负。至此 $T$ 和 $T^{-1}$ 都全局正且保迹。

因此 $T$ 是整个 qutrit 密度矩阵凸集的仿射双射，双射地映射极端点，即完整纯态投影集合。它也保持所有 Hermitian 差的迹范数。确实，写谱分解
$X=X_+-X_-$，正性及保迹性给

$$
\|TX\|_1
\le\|TX_+\|_1+\|TX_-\|_1
=\operatorname{Tr}X_++\operatorname{Tr}X_-=\|X\|_1.
\tag{96.5}
$$

对 $T^{-1}$ 应用同一不等式，得到反向不等式，故恒有等号。这是全局迹距离保持，并非只在有限制备对上的数值保持。

对任意秩一投影 $P,Q$，$P-Q$ 的非零本征值为
$\pm\sqrt{1-\operatorname{Tr}(PQ)}$：在它们的至多二维张成内，迹为零，平方迹为
$2(1-\operatorname{Tr}(PQ))$；正交补上为零。重合和正交端点也符合该公式。于是 (96.5) 给

$$
\operatorname{Tr}(T(P)T(Q))=\operatorname{Tr}(PQ)
\quad\text{对全部纯态对 }P,Q.
\tag{96.6}
$$

现在恰满足 Wigner 定理的完整假设：复维数三的全部射线空间上，一个一一且满的映射，保持每一对射线的转移概率。所用明确版本见 Simon–Mukunda–Chaturvedi–Srinivasan，
[*Two elementary proofs of the Wigner theorem on symmetry in quantum mechanics*](https://arxiv.org/html/0808.0779v2)，§II 式 (8) 及其后的定理陈述。故有一个固定酉 $R_0$，使所有纯态投影同时满足

$$
T(P)=R_0PR_0^\dagger
\quad\text{或同时满足}\quad
T(P)=R_0P^{\mathsf T}R_0^\dagger.
\tag{96.7}
$$

纯态投影实张成 $\operatorname{Herm}_3$，所以同一公式延伸到整个 $T$。在 Hermitian 矩阵上转置就是逐项复共轭；其在全部复矩阵上的复线性延伸仍为转置，不是反线性映射 $X\mapsto\bar X$。

(96.7) 的两种映射都保持 Hermitian 迹配对，故 $T^*=T^{-1}$。由
$T^*F=E$、$T\rho_0=\sigma_0$ 得 $F=T(E)$ 和第一行 (96.1)。将同一个 $T$ 代入

$$
B_a=TA_aT^{-1}
\tag{96.8}
$$

得其余公式；在转置情形，$\mathsf t\operatorname{Ad}_V\mathsf t=\operatorname{Ad}_{\bar V}$，故每个酉代表都使用同一个复共轭选择。Nayak–Sen 已给出的各自酉性在此被提升为全部资料的同一坐标关系。

反之，共同酉变换保持 Born 迹，整体共轭把每个实概率变为自身。将 (96.1) 按时间顺序复合，保留每个 $1/2$ 权重，便得所有词的两种终端概率相等，特别给 (93.6)。每个酉代表的标量相位不可由共轭通道辨认；这是相位代表的自由，不是独立的物理转置通道。定理既未假设也未取得这样一个转置 CP 操作。∎

## 97. 非混合边界上的直接合法单态反模型

**命题 97.1（保留原分支而改变效果效率）。** 保持 (91.1) 的 $d,\theta,\rho_0,E,V_j$，将 $N$ 的条件改为 $[N,P_\xi]=0$。对每个

$$
c<p<1/2,\qquad
G_p=\sqrt{p/c}\,P_\xi+
       \sqrt{(1-p)/(1-c)}\,(I_3-P_\xi)
\tag{97.1}
$$

有一个满足假设 91.2 全部合法性条件的单制备竞争者

$$
\sigma_0^{(p)}=G_p\rho_0G_p,\qquad
F^{(p)}=G_p^{-1}EG_p^{-1},\qquad
B_j^{(p)}=A_j,\qquad B_N^{(p)}=\operatorname{Ad}_N.
\tag{97.2}
$$

它匹配所有有限历史、两种终端结果及精确质量，但不存在将整个源同时送到它的酉或反酉共同规范。此结论是单态直接构造，不使用定理 82.2 的全族分类。

证明。$G_p$ 正且可逆，与两个实际 $V_j$ 以及此处的 $N$ 都交换。$\rho_0$ 的 $P_\xi$ 人口为 $c$，所以 $\sigma_0^{(p)}$ 正、秩一，且

$$
\operatorname{Tr}(G_p\rho_0G_p)
=(p/c)c+\frac{1-p}{1-c}(1-c)=1.
\tag{97.3}
$$

$F^{(p)}$ 是正秩一矩阵，其唯一非零本征值为
$\|G_p^{-1}q\|^2$。由 $q=(\xi+e)/\sqrt2$ 得

$$
\lambda_p=\frac{c}{2p}+\frac{1-c}{2(1-p)},\qquad
\lambda_p-1=\frac{(p-c)(p-1/2)}{p(1-p)}<0.
\tag{97.4}
$$

因此 $0\preceq F^{(p)}\preceq I_3$，其支撑上的效果效率严格小于一。未改变的两个 $A_j$ 仍是 CP 且其和 TP；$B_N^{(p)}$ 仍是 CPTP。合法性都作用于完整矩阵域，无须把 $G_p$ 本身解释为全域 TP 通道。

对每个含 $N$ 的时间词，由交换性，

$$
B_w^{(p)}\sigma_0^{(p)}
=2^{-k(w)}G_pU_w\rho_0U_w^\dagger G_p.
\tag{97.5}
$$

全部 $U_w$ 保持 $P_\xi$ 人口 $c$，故 (97.3) 同样给此式的迹恰为 $2^{-k(w)}$。迹循环性消去两个 $G_p^{-1}$：

$$
\operatorname{Tr}(F^{(p)}B_w^{(p)}\sigma_0^{(p)})
=2^{-k(w)}\operatorname{Tr}(EU_w\rho_0U_w^\dagger).
\tag{97.6}
$$

总质量相同，因而补终端概率也相同，且所有标签和联合权重保留。原 $E$ 的唯一非零本征值为一，$F^{(p)}$ 的为 $\lambda_p<1$；酉或反酉不改变该谱，所以共同规范不可能存在。

例如 $d=2/3$、$c=1/3$、$p=5/12$ 给 $\lambda_p=34/35$。任意固定下双态酉都可作这里的非混合 $N$。这同时显示该反模型没有在 $d=2/3$ 失效。源原生列和其非混合 $N$ 后继仍留在八维 $\mathscr S_c$，故并不满足定理 92.2 的第九列条件。∎

## 98. 有限标量数、时序及全族前提的准确替换

**定理 98.1（单制备辨识的精确有限资源界）。** 对每个指定的允许源和每个指定混合 $N$，存在定义 93.1 的前缀选择，使恰好四张 $9\times9$ 表的 $324$ 个索引标量足以推出定理 96.1。这 $324$ 个位置由 $36$ 个粗粒化质量事件和 $288$ 个选定是事件条目组成；所用时序深度至多十二，每个时序至多使用两次同一个 $N$ 类型，不使用逆、第二种新增控制或可调角度。

证明。每张表有九列、一个迹行和八个实际后缀行。故四张表共

$$
4\cdot9\cdot9=324,\qquad
4\cdot9=36\ \text{个质量位置},\qquad
4\cdot9\cdot8=288\ \text{个是条目}.
\tag{98.1}
$$

质量位置按 (93.5) 加总两个终端结果；其中没有对保留标签求条件概率。非迹条目由 (93.4) 的真实联合事件给出。八个原生前缀各长至多七，第九个为 $u_kN$，长至多八；插入块再用一个字母；后缀长至多三。因此最大时序深度为

$$
8+1+3=12.
\tag{98.2}
$$

$N$ 只可能出现于第九前缀末尾和插入字母 $a=N$，后缀全部原生，故至多两次，且都是同一个已给控制。迹行用较短的无后缀时序。定理 93.2–96.1 此后只作固定映射的数学推论，不需要再测轨道极限、逆、其他制备或无限多词。

量词是“对每个指定源和 $N$，存在这些前缀”，因为定理 92.1 的基及定理 92.2 的逃逸下标可依赖源参数。它不是一个对未知 $d,\theta,N$ 都使用同一组前缀的通用设计。每个 $0,1$ 仍选取实际标签事件；$u_kN$ 的 $N$ 安排在固定的第 $|u_k|$ 次原生使用之后，对其他标签历史也执行相同安排。所有其他历史和两个终端结果仍属于完整记录，没有反馈授权。

(98.1) 计数的是带表位置的选定标量。不同位置可以是相同事件、同值概率或重叠时序；一个质量标量又是两个终端事件的和。故这不是 $324$ 个原始是／否结果格、互异概率值、样本、实验次数或总记录数的断言，也不声称这些实数已被有限实验精确取得。此界没有使用全族问题的任何更少原始格归约。∎

**定义 98.2（与全族校准分类的逻辑关系）。** 定理 82.2 的合同包含整个原 $\mathcal K_d$ 上同一个仿射制备映射。定理 96.1 的合同只给一个真实纯 $\rho_0$ 和一个任意竞争密度 $\sigma_0$，没有该映射，亦不假设未知制备与凸组合的对应；同时它明确额外供应一个固定、可重复、混合 $P_\xi$ 的 $N$。

这个替换有两个不同作用：实际单制备的原生轨道先给八维跨度，一次 $N$ 后继给第九列，有限质量／效果／插入数据由此确定全局线性相似；同一个 $N$ 又使真实正词共轭闭包成为 $PU(3)$，让一个纯制备和一个纯效果分别约束正锥的两侧。正性没有从全族仿射制备继承，而是在 (96.2)–(96.4) 中推出。

定理 97.1 在非混合边界直接实现仍存的合法过滤，不借全族分类反向添加已去掉的前提。定理 96.1 也不由既有全族加控制分类的结论代入：它的全矩阵相似、两侧锥约束和共同规范由这里的有限单态合同独立承担。原全族分类在其原域内仍有自己的用途；两者均是额外量子与取得前提下的条件识别。

## 99. 本源定理的供应、量子前提和未决关系

**定义 99.1（数学归属及成熟中间工具的参数域）。** §§91–98 的内容为源特定的 repo-derived 条件综合：实际原纯制备的深度七基、任意混合 $N$ 的深度八第九列、原权重的四张有限表、全域公平／CP 逆、任意混合边界的 $PU(3)$ 闭包，以及只用一个制备和一个效果得到的共同规范。它不主张文献优先权，也不把一般最小实现相似、可逆量子通道或 Wigner 定理列为新的一般结果。

精确供应与使用域为：第一卷定理 35.2、35.4 及本卷 (55.5)、(88.1)–(88.2) 给 (91.7)–(91.10) 的原输入、五维输出、完整源矩映射和任意有限未触动参考；第二卷定理 39.3–39.4 给时间顺序和两个终端的完整联合权重；第二卷定理 40.1、(40.4)、(40.12) 给同一八后缀的加权效果行列式；本卷引理 63.1 给实际原生 $1\oplus SU(2)$，其全角度域包含非例外有理角。这些供应分别只在上述明确域内使用，§§82–90 的全族仿射分类不属于单态主定理的前提。

一般实现背景按定理 93.2 所引 Monras–Winter §4 使用，但四张有限表的非平稳、双终端、外定时序合同由 (93.11)–(93.14) 自身证明。Nayak–Sen 定理 2.1 只在 (94.4) 已有完整 CPTP 逆之后，以 $p=q=3$ 使用。闭矩阵群及指数生成按引理 63.1 所引 Hall 的原假设用于已取闭的紧酉群；(95.3)–(95.6) 承担本源每个混合 $N$ 的具体 Lie 代数扩张。Wigner 的射线双射与所有转移概率假设逐项由 (96.2)–(96.6) 建立，再按所引主文献应用。谱分解、正锥自对偶和有限维闭性只作为这些新应用中的成熟中间步骤。

**定义 99.2（参数边界、取得边界和剩余目标）。** 定理 96.1 的参数域保持 $0<d<1$、$\sin(2\theta)\ne0$ 和 $[N,P_\xi]\ne0$。$d=2/3$ 及完全送入下双态的混合控制均在域内。$d=0,1$ 不在此合同内；$\sin(2\theta)=0$ 时所用效果行列式为零，不能用此四表证明；非混合 $N$ 有定理 97.1 的全词合法反模型。没有用“几乎处处”排除内部特殊值，也没有把被排除边界的分类当成已完成。

所去掉的是实际整个制备族的仿射对应前提；仍承重的是已知复维数三、Born 配对、完整复 CP、固定时间齐次组合、精确数据、所指定真实纯态与真实秩一效果，以及一个已取得的固定混合酉控制。竞争者更大维数、一般正锥、非复载体、时间相关映射、混合真实制备或内部真实效果均不属于这一定理的结论域。结论中的转置是共同表示关系，不是原生物理通道。

原五维／qutrit 桥和任意有限未触动参考等式不增添可复制制备、独立副本、相干环境访问、相位参考、主动反馈或新测量。固定一个实角度的已知值不供应其标定或可调控制；紧群闭包和全矩阵逆的存在不供应其精确有限实现。$324$ 个索引标量的精确等式也没有给有限样本恢复、非零噪声容忍、统一条件数或有限精度辨识保证；接近例外角度、非混合控制或源端点时，精确秩不提供统计资源界。

这仍是条件校准识别，不是量子起源推导，也不是一般锥重建。原擦除菜单的全 $d$ 精确最小最大中心、有限噪声完整记录的记忆问题、控制与概率的实际取得、共同来源和独立复合的物理桥均保留原目标。具体的下一层关系问题是：由原环境就绪、固定随机仪器和终端任务，哪些可取得且可认证的操作条件能够供应这里的一个混合控制及其精确比较接口，并在有限噪声下仍给有效识别？本定理把这些条件留在前提侧，没有从预测表的数学唯一性中推出它们。共同酉坐标、共同共轭方向和不可见的标量相位也仍各受实际参考资源所限。

## 追加锚（本行以下为增补区）

## 100. 同一个单制备源的一般实有序竞争类

**定义 100.1（指定真实源及其有限供应）。** 本节固定定义 91.1 的同一个源。
记 $Q=\operatorname{Herm}_3(\mathbb C)$，将它视为九维实向量空间，
以 $\langle X,Y\rangle=\operatorname{Tr}(XY)$ 为实非退化配对，
并记 $\mathrm{PSD}_3=\{X\in Q:X\succeq0\}$。
在原正交基 $(\xi,e,f)$ 中，源矩阵和一个制备为

$$
\begin{gathered}
U=\begin{pmatrix}1&0&0\\0&-1/2&\sqrt3/2\\0&\sqrt3/2&1/2\end{pmatrix},
\qquad W=\operatorname{diag}(1,1,-1),\qquad q=(\xi+e)/\sqrt2,\\
0<d<1,\quad c=d/2,\quad \sin(2\theta)\ne0,\quad
P_\xi=\xi\xi^\dagger,\quad E=qq^\dagger,\\
\psi=\sqrt d\,Uq+\mathrm i\sqrt{1-d}\,Uf,
\qquad \rho_0=\psi\psi^\dagger,\\
V_j=U\exp(\mathrm i\theta W)W^j,\qquad
A_j(X)=\tfrac12V_jXV_j^\dagger\quad(j=0,1),\\
N\in U(3),\qquad [N,P_\xi]\ne0,\qquad A_N(X)=NXN^\dagger.
\end{gathered}
\tag{100.1}
$$

$\rho_0$ 是所指定的纯迹一矩阵，$E$ 是所指定的秩一投影，
且 $\operatorname{Tr}(E\rho_0)=(6-5d)/16$，见命题 91.3。
这些是目标侧的具体性质。$N$ 仍为一个已给定、可重复的确定性控制类型。
对时间词 $w=a_1\cdots a_n$，最左字母最早作用，置

$$
\begin{gathered}
\mathcal W=\{0,1,N\}^{*},\qquad
U_0=V_0,\quad U_1=V_1,\quad U_N=N,\\
U_w=U_{a_n}\cdots U_{a_1},\qquad
A_w=A_{a_n}\cdots A_{a_1}=\alpha_w\operatorname{Ad}_{U_w},\\
\alpha_w=2^{-n_{\rm nat}(w)}>0,\qquad
n_{\rm nat}(w)=\#\{t:a_t\in\{0,1\}\}.
\end{gathered}
\tag{100.2}
$$

空词取恒等映射和权重一。时间拼接满足 $A_{vw}=A_wA_v$。
原二元仪器的两个标签仍为随机记录事件；所比较的量为未条件化联合权重。
目标的两种终端权重分别为 $\operatorname{Tr}(EA_w\rho_0)$ 和
$\operatorname{Tr}((I_3-E)A_w\rho_0)$，总质量为 $\alpha_w$。
第二卷定理 39.3–39.4 及本卷 (91.7)–(91.10) 给它们与同一原五维源的对应。
此处只使用这个 $\rho_0$，没有给出整个 $\mathcal K_d$ 的制备映射。

本源的两个供应按其原量词使用：定理 92.1–92.2 给深度七的八个原生基列及
一次 $N$ 后的第九列；定理 95.1 给

$$
\overline{\{\operatorname{Ad}_{U_w}:w\in\mathcal W\}}
=\operatorname{Ad}(PU(3)).
\tag{100.3}
$$

两项对每个允许的 $d,\theta$ 和每一个混合 $N$ 成立。
引理 63.1 的实际原生 $1\oplus SU(2)$ 闭包是这些供应的同源前提，
其中非例外有理角、$d=2/3$ 和 $\langle\xi,N\xi\rangle=0$ 均按原结果保留。
(100.3) 是正向词共轭的数学闭包，不指定额外可执行的逆或连续控制。

**假设 100.2（任意实有序载体上的固定模型）。** 竞争者由

$$
(V,K,u,s_0,e,B_0,B_1,B_N)
\tag{100.4}
$$

组成，其中 $V$ 是实向量空间，$\dim_{\mathbb R}V\le9$；
$K\subset V$ 是闭凸锥，满足 $K\cap(-K)=\{0\}$ 和 $K-K=V$。
$u\in V^{*}$ 在 $K\setminus\{0\}$ 上严格为正，归一化基

$$
\mathcal B_K=\{x\in K:u(x)=1\}
\tag{100.5}
$$

紧致。一个固定制备满足 $s_0\in K$、$u(s_0)=1$。
一个固定二元效果满足 $e\in V^{*}$ 和 $0\le e(x)\le u(x)$ 对所有 $x\in K$。
三个固定实线性映射在整个 $V$ 上定义，并满足

$$
B_a(K)\subseteq K\quad(a=0,1,N),\qquad
u\circ(B_0+B_1)=u,\qquad u\circ B_N=u.
\tag{100.6}
$$

(100.6) 的归一化等式意味着 $u(B_0x)+u(B_1x)=u(x)$ 对每个 $x\in V$ 成立。
每个有限时间词使用同一组三个映射，$B_w=B_{a_n}\cdots B_{a_1}$。
竞争权重为 $e(B_ws_0)$、$(u-e)(B_ws_0)$，质量为 $u(B_ws_0)$。

$V$ 上没有预置复 Hilbert 空间、Born 配对、CP、纯性、酉性、
自对偶、全部数学效果可取得、逆操作或张量结构。
全域固定实线性正映射、维数上限、合法性与精确比较数据是保留的条件。
此类与假设 91.2 的区别在竞争者侧；指定真实目标仍是 (100.1)。

## 101. 原来的四块多输出有限数据

**定义 101.1（列、行及同一事件表）。** 按定理 92.1 任取
$p_1,\ldots,p_8\in\{0,1\}^{*}$，各长至多七，$p_1=\varnothing$，
使 $r_i=A_{p_i}\rho_0$ 为下列八维空间的基：

$$
\mathscr S_c=\{X\in Q:\operatorname{Tr}(P_\xi X)=c\operatorname{Tr}X\}.
\tag{101.1}
$$

按定理 92.2 选择任意一个使 $A_Nr_k\notin\mathscr S_c$ 的 $k$，
置 $p_9=p_kN$、$r_9=A_Nr_k$。
于是 $r_1,\ldots,r_9$ 为整个 $Q$ 的基，$|p_9|\le8$。
这些选择可依赖指定的真实源和 $N$。
固定第二卷定理 40.1 的八个实际原生后缀

$$
(h_1,\ldots,h_8)=(\varnothing,0,1,00,10,000,010,100).
\tag{101.2}
$$

定义九个目标读出及九个竞争读出

$$
\begin{aligned}
\ell_0(X)&=\operatorname{Tr}X,&m_0(x)&=u(x),\\
\ell_m(X)&=\operatorname{Tr}(EA_{h_m}X),&
m_m(x)&=e(B_{h_m}x)\quad(1\le m\le8),\\
x_i&=B_{p_i}s_0&& (1\le i\le9).
\end{aligned}
\tag{101.3}
$$

$h_1=\varnothing$ 给 $\ell_1(X)=\operatorname{Tr}(EX)$、$m_1=e$。
第零行是质量，与八个是读出共同构成多输出系统；
它不是第九个是后缀。目标的四个实矩阵为

$$
H_{mi}=\ell_m(r_i),\qquad
H^a_{mi}=\ell_m(A_ar_i),\quad a=0,1,N,
\quad 0\le m\le8,\quad1\le i\le9.
\tag{101.4}
$$

假设的精确比较只有同样四块：

$$
m_m(x_i)=H_{mi},\qquad m_m(B_ax_i)=H^a_{mi}
\quad\text{对所有上述 }m,i,a.
\tag{101.5}
$$

对 $m\ge1$，时间顺序分别是 $p_i h_m$ 和 $p_i a h_m$，例如

$$
H^a_{mi}=\operatorname{Tr}(EA_{h_m}A_aA_{p_i}\rho_0),\qquad
m_m(B_ax_i)=e(B_{h_m}B_aB_{p_i}s_0).
\tag{101.6}
$$

质量行分别为

$$
\begin{aligned}
H_{0i}&=\operatorname{Tr}(EA_{p_i}\rho_0)
       +\operatorname{Tr}((I_3-E)A_{p_i}\rho_0),\\
H^a_{0i}&=\operatorname{Tr}(EA_aA_{p_i}\rho_0)
       +\operatorname{Tr}((I_3-E)A_aA_{p_i}\rho_0),\\
m_0(x_i)&=e(x_i)+(u-e)(x_i),\\
m_0(B_ax_i)&=e(B_ax_i)+(u-e)(B_ax_i).
\end{aligned}
\tag{101.7}
$$

所以质量来自同一空后缀的两个终端结果；没有把其一省略。
$N$ 在时序中是替代控制，$0,1$ 是一次原生仪器的互斥结果。
对选定标签词取联合事件，不把 $0$ 或 $1$ 改成可强迫发生的门。
对同一预定时序中的其他随机标签历史，控制位置仍相同。

第二卷 (40.4) 与本卷 (93.8)–(93.10) 给九个 $\ell_m$ 独立。
具体地，$Z_h=2^{-|h|}U_h^\dagger EU_h$；按原坐标，
以 $I_3,Z_{h_1},\ldots,Z_{h_8}$ 为列的矩阵 $\mathcal E$ 满足

$$
\det\mathcal E=\frac{6561}{2^{36}}\sin^7(2\theta)\ne0.
\tag{101.8}
$$

真实迹配对的坐标度量为
$J_{\rm tr}=\operatorname{diag}(1,1,1,2,2,2,2,2,2)$，
故泛函矩阵为 $\mathcal E^{\mathsf T}J_{\rm tr}$，也可逆。
这个供应保留了后缀的全部 $2^{-|h|}$ 权重。
它与九个 $r_i$ 的独立性都是指定目标的事实，不是竞争者的先验承诺。

## 102. 有限单源数据强制完整有序坐标的应用定理

**定理 102.1（原四表在任意实九维上限类中的完整锥识别）。**
对每个 (100.1) 的 $d,\theta$、每一个混合 $N$，
以及定义 101.1 的每一种合法前缀选择，
任意满足假设 100.2 的竞争者满足 (101.5)，当且仅当它是目标的一个
共同的实线性有序坐标副本。具体地，必要性方向有 $\dim_{\mathbb R}V=9$，
存在一个实线性双射 $S:V\to Q$，使

$$
\begin{gathered}
S(K)=\mathrm{PSD}_3,\qquad S(s_0)=\rho_0,\\
u(x)=\operatorname{Tr}(Sx),\qquad e(x)=\operatorname{Tr}(ESx)
\quad(x\in V),\\
S(B_ax)=A_a(Sx)\quad(a=0,1,N,\ x\in V).
\end{gathered}
\tag{102.1}
$$

$S$ 与 $S^{-1}$ 对各自完整锥均为正，且是同一个归一化保持的有序同构。
它同时运输唯一给定制备、唯一给定二元效果、归一化及全部三个标签映射；
映射等式作用于每个 $x\in V$，不只作用于已到达向量或归一化切片。

这样的共同标号运输在固定竞争模型上唯一。
完整数学对偶锥还满足

$$
\begin{gathered}
K^{*}=S^{*}(\mathrm{PSD}_3),\qquad
(S^{*}Y)(x)=\operatorname{Tr}(YSx),\\
\forall f\in V^{*},\quad f\in K^{*}
\ \Longleftrightarrow\ 
\exists!Y\in\mathrm{PSD}_3\ 
\forall x\in V,\ f(x)=\operatorname{Tr}(YSx).
\end{gathered}
\tag{102.2}
$$

同一 $S$ 进一步给每个有限 $w\in\mathcal W$ 的未测权重

$$
\begin{aligned}
u(B_ws_0)&=\alpha_w,\\
e(B_ws_0)&=\operatorname{Tr}(EA_w\rho_0),\\
(u-e)(B_ws_0)&=\alpha_w-\operatorname{Tr}(EA_w\rho_0).
\end{aligned}
\tag{102.3}
$$

这仅从四表和固定全域映射推出，
没有再假设所有词已被观测。
反向构造对每个九维实载体和每个到 $Q$ 的实线性双射成立，见 §107。

定理所要求的原选定量恰为 $324$ 个索引标量，
其中 $36$ 个质量、$288$ 个是条目，深度至多十二、每个时序至多两次 $N$，
只用一种给定新增控制类型。索引标量不等于样本、原始结果格或互异时序。
量词是指定源的前缀选择，不是未知源的统一可取得方案。
这些精确条件以及更大维数与非闭锥的边界分别在 §§108–110 保留。

证明由 §§103–107 给出。其新增结论是对 (100.1) 的原单源、原四表，
把竞争类从假设 91.2 扩到假设 100.2 后，仍识别整个载体与整个有序锥。
定理 92.1–92.2、95.1、第二卷定理 40.1 为目标侧供应；
一般线性实现与不变锥方法只作为这个源特定结论的中间步骤。

## 103. 定理 102.1 的秩九饱和与一个全域运输

证明（有限载体部分）。用 $\delta_i$ 表示 $\mathbb R^9$ 的列标准基，定义

$$
\begin{aligned}
R:\mathbb R^9\to Q,&\quad R\delta_i=r_i,\\
L:Q\to\mathbb R^9,&\quad (LX)_m=\ell_m(X),\\
P:\mathbb R^9\to V,&\quad P\delta_i=x_i,\\
M:V\to\mathbb R^9,&\quad (Mx)_m=m_m(x).
\end{aligned}
\tag{103.1}
$$

这里 $P$ 是列映射，不是原终端投影；$S$ 专指即将构造的 $V\to Q$。
目标的基列和泛函基使 $R,L$ 均为同构。
(101.4)–(101.6) 的实际因子分解为

$$
\begin{gathered}
H=LR=MP,\\
H^0=LA_0R=MB_0P,\qquad
H^1=LA_1R=MB_1P,\\
H^N=LA_NR=MB_NP.
\end{gathered}
\tag{103.2}
$$

四块共同使用同一个 $M$ 和同一个 $P$。
首先 $H$ 可逆、秩为九，而

$$
9=\operatorname{rank}(MP)\le\dim_{\mathbb R}V\le9.
\tag{103.3}
$$

故 $\dim_{\mathbb R}V=9$。
$\operatorname{rank}P\ge9$ 与 $\operatorname{rank}M\ge9$，
两者源域和目标域均九维，所以 $P$ 和 $M$ 分别都是同构。
这同时证明已到达的九个 $x_i$ 张成全部 $V$，及九个读出分离全部 $V$。
没有在合同中预置可达性、可观察性或竞争者的任何 Hilbert 结构。

定义唯一候选运输

$$
S=RP^{-1}:V\longrightarrow Q.
\tag{103.4}
$$

由 $MP=LR$ 得

$$
M=LRP^{-1}=LS.
\tag{103.5}
$$

对于每个 $a=0,1,N$，插入块给

$$
LSB_aP=MB_aP=LA_aR=LA_aSP.
\tag{103.6}
$$

消去左边可逆 $L$ 和右边可逆 $P$，即有

$$
SB_a=A_aS\quad\text{在整个 }V\text{ 上成立}.
\tag{103.7}
$$

$M=LS$ 的第零行给 $u=\operatorname{Tr}\circ S$；
第一是行因 $h_1=\varnothing$ 给 $e(x)=\operatorname{Tr}(ESx)$ 对所有 $x$。
$p_1=\varnothing$ 给 $x_1=s_0$、$r_1=\rho_0$，所以 $Ss_0=\rho_0$。
至此 (102.1) 除锥等式外的每个恒等式均由同一个 $S$ 给出。
此时尚未证明 $S(K)=\mathrm{PSD}_3$，也未假设 $S$ 或其逆正。

§93 的相似方法在已知复三维竞争者上有其原应用；
这里 (103.3) 把同样的有限因子分解用于任意实 $V$，
通过维数上限取得完整载体的两个同构。
它不调用 §94 的完整 CP 逆或 §96 的 Wigner 论证。

## 104. 定理 102.1 的时间列坐标与所有未测词

证明（固定映射及实现对应）。(103.2) 还直接给每个字母的列坐标

$$
G_a=H^{-1}H^a
=P^{-1}B_aP=R^{-1}A_aR,\qquad a=0,1,N.
\tag{104.1}
$$

例如 $(MP)^{-1}(MB_aP)=P^{-1}B_aP$，这里必须使用 $M$ 的同构性。
初始列为 $P^{-1}s_0=\delta_1$，因为 $p_1=\varnothing$。
若 $w=a_1\cdots a_n$ 按实际时间排列，令

$$
G_w=G_{a_n}\cdots G_{a_1},\qquad G_\varnothing=I_9.
\tag{104.2}
$$

于是所有词的质量、是权重和否权重分别为

$$
(HG_w\delta_1)_0,\qquad
(HG_w\delta_1)_1,\qquad
(HG_w\delta_1)_0-(HG_w\delta_1)_1.
\tag{104.3}
$$

质量行和第一是行的含义由 $m_0=u$、$h_1=\varnothing$ 保证。
这不是九个是后缀的标量 Hankel 块。

所用一般实现所有者为
[WordHankelRealization](../../../D5/S3/Observer/Hankel/WordHankelRealization.lean)。
其中 `residualSpace` 是一个标量响应 $f$ 的全部有限词残差的跨度；
`finite_hankel_realization` 给有限全残差维数与矩阵实现及其最小维数关系。
`recoveredRealization`、`full_rank_block_recovery` 的实际前提包含
$r>0$、整个标量残差空间的有限维性，以及
$\operatorname{finrank}(\operatorname{residualSpace}f)=r$，
然后才对可逆的 $r\times r$ 前缀／后缀块给全词恢复。
单个有限块可逆本身不替代这个全残差秩前提。

该所有者使用前缀行、后缀列和行状态的左到右矩阵乘积。
与本处列状态约定的代数转换为

$$
H_{\rm row}=H^{\mathsf T},\quad
H^a_{\rm row}=(H^a)^{\mathsf T},\quad
H^a_{\rm row}H_{\rm row}^{-1}=G_a^{\mathsf T},\quad
G_{a_1}^{\mathsf T}\cdots G_{a_n}^{\mathsf T}=G_w^{\mathsf T}.
\tag{104.4}
$$

转置说明乘积方向，并不把本题的质量加八是多输出块变成该标量定理的直接实例。
这里所需的推断由 (103.2)–(104.1) 在有限载体上直接承担。
若定义多输出残差映射

$$
J:V\longrightarrow\mathbb R^{\mathcal W\times\{0,\ldots,8\}},
\qquad J(x)(w,m)=m_m(B_wx),
\tag{104.5}
$$

则它因子通过九维 $V$；空词评价就是同构 $M$，故 $J$ 单射。
又 $x_i$ 张成 $V$，故全部前缀的多输出残差跨度恰为九维。
这个全多输出秩是有限载体和四表的后果，不是新观察前提。

由 (103.7) 对词长归纳，$SB_w=A_wS$ 对所有 $w$、所有 $x\in V$ 成立。
配合 $Ss_0=\rho_0$、$u=\operatorname{Tr}\circ S$ 与效果恒等式，
即得 (102.3)，包括两个终端及完整质量。
还对每个 $x\in V$ 有

$$
u(B_jx)=\tfrac12u(x)\quad(j=0,1),\qquad u(B_Nx)=u(x).
\tag{104.6}
$$

所以 $2B_0,2B_1,B_N$ 在数学上为保持 $u$ 的正映射。
这些等式不是只在 $s_0$ 的轨道上成立。
因子二的代数缩放没有改变原记录的权重，也没有供给可选择的随机分支。
所有未测词的结论依赖固定全域映射复用；时间相关或非线性替代模型不在此合同中。

## 105. 定理 102.1 的完整运输锥及两侧约束

证明（整个锥的夹逼）。令

$$
C=S(K)\subset Q,\qquad
C^{*}=\{Y\in Q:\operatorname{Tr}(YX)\ge0\ \text{对所有 }X\in C\}.
\tag{105.1}
$$

实线性双射在有限维中是同胚，故 $C$ 是闭、尖、生成的凸锥。
$\operatorname{Tr}$ 在其非零元素上严格为正，迹一基紧致，
$\rho_0\in C$，且 $0\le\operatorname{Tr}(EX)\le\operatorname{Tr}X$ 对所有 $X\in C$。
特别地 $E\in C^{*}$，并由 (103.7) 得

$$
A_a(C)\subseteq C\quad(a=0,1,N),\qquad
A_w(C)\subseteq C\quad(w\in\mathcal W).
\tag{105.2}
$$

定义本源的状态内锥与效果外约束

$$
\begin{aligned}
L_{\rm in}&=\overline{\operatorname{cone}\{A_w\rho_0:w\in\mathcal W\}},\\
O_{\rm out}&=\{X\in Q:\operatorname{Tr}(EA_wX)\ge0
                       \ \text{对所有 }w\in\mathcal W\}.
\end{aligned}
\tag{105.3}
$$

$\operatorname{cone}$ 表示有限非负线性组合，横线表示通常有限维拓扑闭包。
由 $\rho_0\in C$、(105.2) 及 $C$ 闭，得到 $L_{\rm in}\subseteq C$。
对 $X\in C$，每个 $A_wX\in C$，再用 $E\in C^{*}$，得到 $C\subseteq O_{\rm out}$。
所以这些是完整 $Q$ 上的约束

$$
L_{\rm in}\subseteq C\subseteq O_{\rm out}.
\tag{105.4}
$$

它们既非仅在原生八维超平面，也非仅在某个归一化轨道上。

更明确地，定义效果的闭有限词轨道锥

$$
Z_w=\alpha_wU_w^\dagger EU_w,\qquad
D=\overline{\operatorname{cone}\{Z_w:w\in\mathcal W\}}.
\tag{105.5}
$$

$\operatorname{Tr}(Z_wX)=\operatorname{Tr}(EA_wX)$，
故每个 $Z_w\in C^{*}$。对偶锥闭，因此正确方向是

$$
D\subseteq C^{*},\qquad C=C^{**}\subseteq D^{*},\qquad
O_{\rm out}=D^{*}.
\tag{105.6}
$$

对偶反转包含关系；不能将第一式倒置。
外锥的等式成立，因为非负配对在有限和及闭包下保持。
$D$ 明确包含闭包，不是原可数词的未经闭包的锥包。

## 106. 定理 102.1 的实际纯轨道使两侧相合

证明（目标轨道部分）。对每个有限词单独使用 $\alpha_w>0$，先得到

$$
\operatorname{cone}\{A_w\rho_0:w\in\mathcal W\}
=\operatorname{cone}\{U_w\rho_0U_w^\dagger:w\in\mathcal W\}.
\tag{106.1}
$$

这是逐射线的正倍数消去：
$U_w\rho_0U_w^\dagger=\alpha_w^{-1}A_w\rho_0$。
必须在取轨道极限以前消掉每个词自己的权重，
因为词长增加时 $\alpha_w$ 可以趋于零。
(106.1) 只在锥中乘正实数，没有对观察记录作条件化。

定理 95.1 的 (100.3) 与实际纯 $\rho_0$ 给

$$
\overline{\{U_w\rho_0U_w^\dagger:w\in\mathcal W\}}
=\{vv^\dagger:v\in\mathbb C^3,\ \|v\|=1\}.
\tag{106.2}
$$

确实，给任意单位 $v$，可取一个酉将 $\psi$ 送到 $v$，
再取正向词的共轭趋于该酉共轭；轨道作用连续。
故每个复秩一投影都属于 $L_{\rm in}$。
每个 PSD 矩阵由谱分解是至多三个这样的投影的非负线性组合；
反之，所有 $A_w\rho_0$ 都为 PSD，而 PSD 锥闭。
作为本源夹逼中的中间步骤，得到

$$
L_{\rm in}=\mathrm{PSD}_3\subseteq C.
\tag{106.3}
$$

效果一侧也须先消去权重。由 (105.5)，

$$
U_w^\dagger EU_w=\alpha_w^{-1}Z_w\in D\subseteq C^{*},
\qquad
D=\overline{\operatorname{cone}\{U_w^\dagger EU_w:w\in\mathcal W\}}.
\tag{106.4}
$$

然后才取 $w$ 的序列极限。
$E$ 是本源的秩一迹一投影，且 $g\mapsto g^\dagger Eg$ 在 $PU(3)$ 上连续，
其像为全部复秩一投影。由 (100.3)，每个这样的投影都是 (106.4) 的极限。
因此谱分解与闭性同样给

$$
D=\mathrm{PSD}_3.
\tag{106.5}
$$

此论证只使用正向词的数学对偶作用；写 $U_w^\dagger$ 不意味着已取得逆控制。
未经闭包的可数有限词锥不必等于 PSD 锥，不能从 (106.5) 删去横线。

也可直接检验外约束的充分强度。若 $X\in O_{\rm out}$，则对每个有限词

$$
0\le\alpha_w^{-1}\operatorname{Tr}(EA_wX)
=\operatorname{Tr}(U_w^\dagger EU_wX).
\tag{106.6}
$$

先除正权重，再由 (100.3) 与连续性，得到
$\operatorname{Tr}(vv^\dagger X)=v^\dagger Xv\ge0$ 对每个复单位向量 $v$ 成立。
这正是 Hermitian 矩阵 $X\succeq0$ 的判据。
若有负本征值，选对应的复单位本征向量立即矛盾。
反之 PSD $X$ 与所有 PSD $Z_w$ 的配对非负。
所以

$$
O_{\rm out}=\mathrm{PSD}_3.
\tag{106.7}
$$

这里只测实单位向量不足以代替全部复向量。
结合 (105.4)、(106.3)、(106.7) 得

$$
\mathrm{PSD}_3=L_{\rm in}\subseteq S(K)
\subseteq O_{\rm out}=\mathrm{PSD}_3.
\tag{106.8}
$$

故 $S(K)=\mathrm{PSD}_3$，同一个 $S$ 与其逆都为正。
由 §103 已有的归一化、制备、效果及三个全域映射恒等式，
这正给 (102.1) 的完整有序同构。
整个推断对每个允许角度、每个 $d$ 和每一个混合 $N$ 成立，
没有一般位置条件或对 $N\xi$ 重叠的额外限制。

## 107. 定理 102.1 的全对偶、标号唯一性与实际坐标副本

证明（对偶及反向部分）。记完整数学对偶锥为
$K^{*}=\{f\in V^{*}:f(x)\ge0\ \text{对所有 }x\in K\}$。
先取任意 $f\in V^{*}$。
实迹配对非退化，故 $X\mapsto f(S^{-1}X)$ 唯一表示为 $\operatorname{Tr}(YX)$，
其中 $Y\in Q$ 唯一。于是

$$
\begin{aligned}
f\in K^{*}
&\Longleftrightarrow \operatorname{Tr}(YX)\ge0
                       \quad\text{对所有 }X\in\mathrm{PSD}_3\\
&\Longleftrightarrow Y\in\mathrm{PSD}_3.
\end{aligned}
\tag{107.1}
$$

第二个等价仍可通过全部秩一投影判定，反向由 PSD 的谱和成立。
因而 $K^{*}=S^{*}(\mathrm{PSD}_3)$，并得到 (102.2) 的存在唯一性及其全域量词。
这在 $V^{*}$ 中是拉回公式；没有在 $V$ 上偷偷选内积并宣称 $K=K^{*}$。
它识别完整数学对偶，不宣称其中每个泛函或每个 $0\le f\le u$ 都可作为物理效果取得。
实际用到的是固定 $e$、其正向词拉回和两个终端结果的质量恒等式。

再设 $T:V\to Q$ 为另一个实线性双射，满足同一制备和三个标号映射的恒等式。
对每个前缀都有

$$
Tx_i=TB_{p_i}s_0=A_{p_i}Ts_0=A_{p_i}\rho_0=r_i=Sx_i.
\tag{107.2}
$$

$x_i$ 是整个 $V$ 的基，所以 $T=S$。
这甚至只需要制备和三个全域交织恒等式，故亦给完整 (102.1) 下的唯一性。
固定全部标签是必要的；锥本身有许多自同构，
唯一性不指未标号锥有一个特权坐标，也不允许各个映射分别选规范。

反之，对任意九维实 $V$ 和任意实线性双射 $T:V\to Q$，定义

$$
\begin{gathered}
K=T^{-1}(\mathrm{PSD}_3),\qquad s_0=T^{-1}\rho_0,\qquad
u=\operatorname{Tr}\circ T,\\
e(x)=\operatorname{Tr}(ETx),\qquad
B_a=T^{-1}A_aT\quad(a=0,1,N).
\end{gathered}
\tag{107.3}
$$

PSD 锥闭、尖且生成，故 $K$ 也如此。
迹在非零 PSD 矩阵上严格为正；密度矩阵基紧致，
其经 $T^{-1}$ 的像就是 $K$ 的紧归一化基。
$0\preceq E\preceq I_3$ 给 $0\le e\le u$，且 $s_0\in K$、$u(s_0)=1$。
三个 $A_a$ 保持 PSD 锥，故三个 $B_a$ 都为 $K$ 正。
目标迹恒等式给

$$
u\circ(B_0+B_1)=u,\qquad u\circ B_N=u.
\tag{107.4}
$$

由时间顺序逐词复合得 $B_ws_0=T^{-1}A_w\rho_0$。
全部原索引条目、两种终端权重及所有词质量因此一致，特别满足 (101.5)。
这是真实目标的坐标副本构造，不要求 $V$ 上预置 CP 定义。
必要性和充分性均已证明。∎

## 108. 同一有序重建应用的精确资源与量词

**命题 108.1（不增加观察格的资源对应）。** 定理 102.1 使用的比较量仍严格为
定义 93.1、101.1 的四张 $9\times9$ 表，其索引计数为

$$
324=4\cdot9\cdot9=36+288,
\qquad36=4\cdot9,\qquad288=4\cdot8\cdot9.
\tag{108.1}
$$

其深度上界为十二，单个时序的 $N$ 使用数至多二，新增控制类型恰为已给定的一个 $N$。

证明。每块的第零行有九个质量，其余八行各有九个是条目。
(101.7) 明确用两个终端结果加总质量，所以质量数不是另一组是概率。
八个原生前缀长至多七，第九个长至多八且含一个 $N$；
插入字母增加至多一步和至多一个 $N$；后缀长至多三且没有 $N$。
因此最长选定时序至多 $8+1+3=12$，其中至多两次同一 $N$。
迹行使用空后缀的较短时序。

索引位置允许重叠、同值和重复事件，故 (108.1) 不计互异概率、互异时序、
原始结果格、样本数或实验次数。
每个原生标签的 $1/2$ 权重保持不动；含控制词仍为 $2^{-n_{\rm nat}(w)}$。
证明中对锥生成元除正因子与坐标恢复均不把这些概率改成条件概率。

前缀的量词为：对每个指定源和每个指定混合 $N$，
任取满足定理 92.1–92.2 的基及逃逸列；对所有匹配其四表的竞争者有结论。
它没有提供一个未知源、未知参数下统一可取得的前缀选择程序。
§§104–107 的所有词、全部纯投影和闭包仅限制已经固定的全域模型，
不增加一个观察格或一个控制类型，也不假设一张无限实测表。∎

## 109. 原目标的维数与闭基条件的两个边界应用

**命题 109.1（原源的十维不可达扩展）。** 对每个 (100.1) 的目标，
包括每个允许角度和每一个混合 $N$，置

$$
\begin{gathered}
V_{10}=Q\oplus\mathbb R,\quad K_{10}=\mathrm{PSD}_3\times\mathbb R_+,\\
u_{10}(X,t)=\operatorname{Tr}X+t,\quad
s_{10}=(\rho_0,0),\quad e_{10}(X,t)=\operatorname{Tr}(EX),\\
B_j^{10}(X,t)=(A_jX,t/2)\quad(j=0,1),\qquad
B_N^{10}(X,t)=(A_NX,t).
\end{gathered}
\tag{109.1}
$$

该模型保留假设 100.2 的所有有序合法性和全部原词概率，
但实维数为十，故在原维数上限之外，不能与九维 $Q$ 全载体同构。

证明。乘积锥闭、尖且生成。$u_{10}$ 在其非零元素上严格为正；
迹一基由 $X\succeq0$、$t\ge0$、$\operatorname{Tr}X+t=1$ 给出，闭且有界，故紧。
$0\le e_{10}\le u_{10}$，且每个固定映射为正。
两个原生分支的第二坐标之和为 $t$，第一坐标总迹为 $\operatorname{Tr}X$，
故 $u_{10}(B_0^{10}+B_1^{10})=u_{10}$；$B_N^{10}$ 也保持 $u_{10}$。
对每个有限词直接归纳得

$$
B_w^{10}s_{10}=(A_w\rho_0,0).
\tag{109.2}
$$

所以全部词的质量、是／否权重及全部 $324$ 个索引格与原目标相同。
新增方向永不到达；不能由秩九的数据识别它。
这是同一个原目标的维数边界，未改变定理 102.1 的上限，
也不是上限内的反例。∎

**命题 109.2（同时去掉闭性与紧基的原正向轨道模型）。**
对每个同样的目标，若同时不要求锥闭及归一化基紧致，
保持 $V=Q$、原 $\rho_0,E,A_0,A_1,A_N$、归一化 $u=\operatorname{Tr}$，置

$$
K_0=\operatorname{cone}\{U_w\rho_0U_w^\dagger:w\in\mathcal W\}.
\tag{109.3}
$$

这个由可数有限词射线生成的未闭锥为尖生成凸锥，严格归一化、效果和固定映射均合法，
全部原有限词权重一致，但 $K_0\ne\mathrm{PSD}_3$、$\overline{K_0}=\mathrm{PSD}_3$，
其迹一基不紧致。

证明。$K_0\subseteq\mathrm{PSD}_3$ 给尖性和迹严格正。
九个独立 $r_i$ 只是其轨道射线的正倍数，故 $K_0-K_0=Q$。
追加任意字母仍是一个正向词，$A_a$ 将每条生成射线送到正倍的另一条射线，
所以全部三个映射保持 $K_0$。$0\le E\le I_3$ 给效果合法，
原迹恒等式给原生分支和与 $N$ 的归一化条件。
所有制备及映射均与目标相同，故每个有限词的两个终端权重和质量相同。
由 (106.1)–(106.3) 得 $\overline{K_0}=\mathrm{PSD}_3$。

有限词可数，而复秩一投影射线不可数。
有限正和不能制造一个缺失的秩一射线：若
$X=\sum_{j=1}^k t_jv_jv_j^\dagger$ 为秩一，$t_j>0$，
对每个与其值域正交的 $z$ 都有

$$
0=z^\dagger Xz=\sum_{j=1}^k t_j|v_j^\dagger z|^2.
\tag{109.4}
$$

每项非负，故所有 $v_j$ 都在 $X$ 的同一维值域中。
因此 $K_0$ 的秩一射线只可能是已有词射线；某些纯射线缺失。
(106.2) 却给归一化词投影趋于这些缺失投影，
所以 $K_0$ 不闭，迹一基也不闭，因而不紧。

在命题 109.2 的应用中，“同时”不能删掉。
事实上，若保留有限维、$u$ 在 $K\setminus\{0\}$ 上严格正及紧的归一化基，
则闭性已经自动成立。作为该边界的中间论证，取任意 $x_n\in K$、$x_n\to x$。
置 $t_n=u(x_n)\ge0$，则 $t_n\to u(x)\ge0$。非零项写成 $x_n=t_nb_n$，$b_n\in\mathcal B_K$。
若 $u(x)>0$，则 $b_n=x_n/t_n\to x/u(x)$，紧基包含此极限，故 $x\in K$。
若 $u(x)=0$，紧基有界，$t_n\to0$ 迫使 $x=0\in K$。
零项或其子序列也给相同结论。因此锥闭。
仅从假设 100.2 中删去“闭”而保留紧基及严格归一化，
不会允许 (109.3)；这个模型只说明同时放松两项的边界。∎

## 110. 不变锥文献对应与本源结论的精确范围

**定义 110.1（代数供应及时间约定的对应）。**
§105 的夹逼使用不变锥的成熟代数方法，主文献为 Fanizza–Lumbreras–Winter，
[*Quantum theory in finite dimension cannot explain every general process with finite memory*](https://arxiv.org/html/2209.11225v2)，
§2.1、命题 2–3、式 (5)–(7)。
其式 (6) 的 $\mathcal C_{\min}$ 是原有限词锥包，并未加闭包；
命题 2 后的闭包说明容许在闭不变锥中取其闭包。
其式 (7) 对效果锥取对偶，闭包不改变该对偶。

本源的具体代数对应为

$$
\mathcal V_{\rm FLW}=Q,\qquad \tau=\rho_0,\qquad
\pi(X)=\operatorname{Tr}(EX),\qquad
D^{(w)}=A_{\operatorname{rev}(w)},\qquad \mathcal C=C=S(K).
\tag{110.1}
$$

因为 $A_{vw}=A_wA_v$，反转词使
$D^{(vw)}=D^{(v)}D^{(w)}$，符合该文式 (2) 的半群约定。
反转遍历全部词，故不改变式 (6)–(7) 的轨道集合。
这只是文献词约定的转换，实际四表仍按 $p_i a h_m$ 的原时间顺序。

$\tau\in C$、$D^{(w)}C\subseteq C$、$\pi\in C^{*}$
逐项由 §105 的完整运输得到。
因此其代数内外包含恰对应 $L_{\rm in}\subseteq C\subseteq O_{\rm out}$；
按迹配对识别其协向量并取闭包，式 (7) 中的生成锥得到 (105.5) 的 $D$；
取此闭包不改变外锥，且有 $D\subseteq C^{*}$ 及反向的 $C\subseteq D^{*}$。
该文可将其载体锥解释为效果、对偶解释为状态；
这里采用这些代数条件作用于实际运输后的状态锥，不借入该物理解读。

**命题 110.2（本源四表不是该文的平稳过程实例）。**
(110.1) 不满足该文定义 1 的归一化平稳过程合同，
所以命题 2 的随机测度结论和该文的平稳最小实现结论不用于定理 102.1。

证明。首先，空词给

$$
\pi(\tau)=\operatorname{Tr}(E\rho_0)=\frac{6-5d}{16}
\in(1/16,3/8),
\tag{110.2}
$$

并非平稳概率柱集的空词质量一。
其次 $N$ 是替代控制，不是与原生 $0,1$ 并列的第三个互斥仪器结果。
若将三者强行相加，实际映射满足

$$
\operatorname{Tr}\circ(A_0+A_1+A_N)=2\operatorname{Tr},\qquad
(A_0+A_1+A_N)(I_3)=2I_3.
\tag{110.3}
$$

故其和不固定迹一的 $\tau$；左固定点条件也失败，
因为 $\pi((A_0+A_1+A_N)(I_3))=2\ne1=\pi(I_3)$。
该文定义 1 式 (3) 的两个平稳固定点条件均不能由本源数据取得。
本处直接证明所需的代数不变锥包含，未把平稳性或无限观察放入合同。∎

**定义 110.3（源特定综合与识别边界）。**
定理 102.1 是仓内导出的源特定应用：
原单制备的九列、原加权八是加一质量的行、原四表、每个混合 $N$ 的正向闭包，
共同迫使任意实维数不超过九的合法有序竞争者成为同一完整有序坐标副本。
一般 Hankel 实现、FLW 不变锥包含、连续轨道及 Hermitian 谱分解
仅为此应用的中间供应，不作为新增独立一般定理，也不据此主张文献或物理优先权。

此合同对竞争者不要求 Hilbert／Born／CP 结构，也不要求自对偶、纯性或酉性。
仍承重的是指定真实目标的纯 $\rho_0$、秩一 $E$、原生矩阵与给定混合酉 $N$，
固定全域实线性正映射、严格归一化、闭紧基条件、维数上限及精确四表等式。
整个原仿射制备族没有供应；全部物理效果的可取得性没有推出。

$0<d<1$、$\sin(2\theta)\ne0$、每个 $[N,P_\xi]\ne0$ 的量词完整保留。
端点、例外角、非混合控制、混合真实初态或内部真实效果不由本应用扩展分类。
更大载体有命题 109.1 的具体不可达扩展；
闭紧基条件的同时放松有命题 109.2 的原轨道模型。
精确秩和闭包结论不提供非零误差容忍、有限精度恢复、样本复杂度或统一稳定常数。

数学上的所有词预测一致，来自同一组固定全域映射，
不来自额外观察、可执行逆、稠密控制的物理取得或整族独立制备。
一个已给定控制的作用不推导该控制如何从原菜单取得。
有序坐标识别也不规定复合系统的张量规则、独立副本或参考操作，
不从有限预测表推出量子本体或量子起源。
原完整最小最大中心、有限噪声记忆、操作取得和共同来源到复合的桥梁
仍是与此精确单系统应用不同的数学与物理问题。

## 追加锚（本行以下为增补区）
