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

