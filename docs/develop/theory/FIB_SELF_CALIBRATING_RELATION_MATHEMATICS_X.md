# FIB 自校准关系数学 X

## 1. 中央参数段的实际 JJ 接续

**定义 1.1（完整世界与同一父的源坐标）。** 完整世界域、原时钟、立即读数、一条不可复制不可重置轨迹及含早停的任意确定性策略，均取自 [VI，定义1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md)。父历史取 VI (8.3) 的同一个字面历史

$$
H^-_{\theta,\xi}
=(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta+\xi)).
\tag{1.1}
$$

以下 $u,n,a,h,\ell,\Phi,\Delta$ 及唯一源逆 $P(u,n,a)$，分别沿用 VI (8.1) 和 [V (29.1)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)。令

$$
\begin{gathered}
I=[13/8,5/3],\qquad r=\theta n-a,\qquad
K_\theta=5a\ell+(5-20\theta)h,\\
V=10u^2+19u-36,\qquad X=20u^2+34u-70,\\
L=4(n+a)X-35a\ell-171h,\qquad C_\theta=210(1+\theta).
\end{gathered}
\tag{1.2}
$$

在 $\Delta\ne0$ 的源域上定义实函数

$$
\begin{aligned}
F_\theta(P)&=\frac{r\Phi}{5\Delta},\\
Z_\theta(P)&=24\{hr+(1+2n)(K_\theta+rV)\},\\
z_\theta(P)&=\frac{Z_\theta(P)}{\Delta},\qquad
j_\theta(P)=C_\theta+\frac{6rL}{\Delta}.
\end{aligned}
\tag{1.3}
$$

字母 $F_\theta$ 是源函数，$\mathcal F(H)$ 仍表示完整实际纤维。$z_\theta,j_\theta$ 只表示先在原时钟六选择 $J$、随后在原时钟七选择 $J$ 的两个实际读数。

**定理 1.2（中央闭参数段的统一非零偏离桥）。** 存在 $\varepsilon_J>0$，使对每个 $\theta\in I$ 和每个 $|\xi|<\varepsilon_J$，固定接续 $J,J$ 的响应映射

$$
W\longmapsto
\bigl(r_J^{(6)}(W),r_{JJ}^{(7)}(W)\bigr)
\quad\text{在整个 }\mathcal F(H^-_{\theta,\xi})\text{ 上单射}.
\tag{1.4}
$$

因而每个实际第六 $J$ 子纤维的末 $J$ 响应单射，对其任意已知子集 $K\subseteq\mathcal F(H^-_{\theta,\xi})$ 都有 $\neg L_2(K,H^-_{\theta,\xi})$。这里保留两臂各自选择实际第六响应、每臂的两种末动作分别使用不同碰撞对的原量词。

进一步，取 VI 定理27.3的任意 $B\ge539$，存在

$$
0<\varepsilon_*\le\frac1{10^{20}B}
\tag{1.5}
$$

使原共同父失败关联满足新的必要父约束

$$
\begin{gathered}
0<|\xi|<\varepsilon_*,\qquad
(\theta,\xi)\in\mathcal P_M\cap\mathcal P_J\\
\Longrightarrow\qquad
\theta\in(11/10,13/8)\ \cup\ (5/3,181/100).
\end{gathered}
\tag{1.6}
$$

证明。先建立整个原域的坐标，再处理闭源边界、局部反解及全部非紧方向。

对于任意 $\xi$，VI 定理8.2给出没有除 $\Delta$ 的父方程

$$
d\Delta=24hr,\qquad d\Phi=120h\xi.
\tag{1.7}
$$

若一个实际世界满足 $\Delta=0$，则 $h>0$ 迫使 $r=0$。V 定理30.2中排除 $\Delta=r=0$ 的推导仅使用源正性和 $\theta\in I$，未使用 $\xi=0$；故仍可直接应用。具体地，令 $a=\theta n$，V (30.6) 给 $1<u<2,n<3,0<\ell/h<1$，从而

$$
\frac{\Delta}{nh}=1+\theta\frac{n\ell}{h}-4\theta
<1-\theta<0.
\tag{1.8}
$$

所以本参数段的任何实际世界均有 $\Delta\ne0$，不是额外删去这一退化层。在此域中，(1.7)等价于

$$
F_\theta(P)=\xi,\qquad d=24hr/\Delta.
\tag{1.9}
$$

再以 VI (8.2) 在原时钟 $0,1,2,3$ 的四个值作唯一至多三次插值，就恢复整个增益。不同的零、三读数排除零多项式。V (30.5)中不要求 $\Phi=0$ 的恒等式直接给(1.3)的实际 $JJ$ 响应。故严格正来源上的(1.9)与整个实际父纤维双射；它包括 $r=0$、$d=0$、$\Phi=0$ 在各自合法参数处的接合。

现在只把非负秩一迹一来源作为极限空间，记

$$
\overline{\mathscr S}
=\left\{P=\begin{pmatrix}p&b\\c&1-p\end{pmatrix}:
0\le p\le1,\ b,c\ge0,\ bc=p(1-p)\right\}.
\tag{1.10}
$$

其边界不是新增合法世界。$\det P=0,\operatorname{tr}P=1$ 的实曲面在这些点附近光滑：方程 $bc-p(1-p)=0$ 的梯度为 $(2p-1,c,b)$，不可能同时为零。

在 $r=0$ 上，正来源及其全部非负极限恰为 V (30.6) 的闭弧。用该式的 $s\in[0,\infty]$ 参数，置 $\lambda=s/(1+s)\in[0,1]$，则

$$
\begin{gathered}
n(s)=\frac{1+5s+5s^2}{(2-\theta)+2s+(2\theta-1)s^2},\\
D_\lambda=(2-\theta)(1-\lambda)^2
 +2\lambda(1-\lambda)+(2\theta-1)\lambda^2,\\
\frac{dn}{d\lambda}
=\frac{(8-5\theta)(1-\lambda)^2
 +(22-14\theta)\lambda(1-\lambda)
 +(15-10\theta)\lambda^2}{D_\lambda^2}<0.
\end{gathered}
\tag{1.11}
$$

分母严格正；三个分子系数在 $I$ 上分别至多为 $-1/8,-3/4,-5/4$。因此 $z_\theta=240+120/n$ 在这条整个闭弧上导数非零、严格递增，而 $j_\theta=C_\theta$。两个边界端点分别是

$$
\begin{pmatrix}1&(\theta-1)/(2-\theta)\\0&0\end{pmatrix},
\qquad
\begin{pmatrix}0&0\\(3-\theta)/(2\theta-1)&1\end{pmatrix}.
\tag{1.12}
$$

没有额外的非负 $r=0$ 分量：在 $0<p<1$ 时 $bc>0$，即为原正来源；在 $p=0,1$ 时直接解 $r=0$ 给(1.12)，其余两种零非对角元选择要求另一非对角元为负。V (30.6)—(30.7)在这条闭弧上以弱界 $1\le u\le2,n\le3,\ell/h\le1$ 仍给 $\Delta/(nh)\le1-\theta<0$。

非负来源上的 $\Phi=0$ 层恰为 V 定理29.3两条正弧的闭包；这一边界穷尽及 $\Phi$ 的正则坐标已由 VI (27.16)—(27.17)供应。沿这些闭弧记导数为 $d/du$。其唯一 $\Delta=0$ 点仍是 V (29.12) 的 $P_\sigma$，其余点按 $\mathcal S_-,\mathcal S_+^{<},\mathcal S_+^{>}$ 三段分开。

需在四个端点补足 V 定理30.3的严格分离。以下是精确有理区间包含；端点的 $u$ 隔离区间沿用 VI (26.11)，$n_\pm,a_\pm$ 沿用 V (29.9)。表中导数取 $\xi=0$ 的 $j_\theta$ 在 $\Phi=0$ 弧上的导数，$z$ 一列同时覆盖两个显示参数。

$$
\begin{array}{c|c|c|c|c|c}
\text{端点}&\Delta&L&z\ (\theta=13/8,5/3)
 &(dj_{13/8}/du)&(dj_{5/3}/du)\\ \hline
\alpha_0&(14,15)&(38,39)&(455,464)&(1065,1067)&(1116,1118)\\
\beta_0&(-17,-16)&(216,217)&(280,283)&(175,176)&(189,190)\\
\gamma_0&(-10,-9)&(224,225)&(274,276)&(1221,1223)&(1313,1315)\\
\eta_0&(-49,-48)&(417,418)&(248,251)&(256,258)&(269,270)
\end{array}
\tag{1.13}
$$

这里及下文的有限包含均可由如下有理规则重算。对 V (29.9) 的 $A,c_i,\mathcal Q$ 作 Horner 区间运算，以分母 $10^{40}$ 的整数平方比较包围 $\sqrt{\mathcal Q}$，再代入 $n_\pm,a_\pm$。以 V (29.9) 的多项式 $F(u,n)$ 计算 $n'=-F_u/F_n$，并用

$$
a'=\frac{23(2u+1)-(16u+18)n-B_1n'-(6u+3)a}{A},
\quad B_1=8u^2+18u-30,
\tag{1.14}
$$

对(1.2)—(1.3)求导；全部除数区间不含零。最后仅作有理端点比较。V (30.10)—(30.12)已供应弧内部的无零点及严格符号，不在这里重新建立内部根计数。(1.13)使那些严格界在新增端点也成立；$\theta$ 的仿射性延伸到整个 $I$。

于是 V (30.8)的分支间分离在闭弧上仍成立：$\mathcal S_-$ 有 $z<300$，左 $\mathcal S_+$ 有 $z>400,j>C_\theta$，右 $\mathcal S_+$ 有 $z<279,j<C_\theta$；若 $\mathcal S_-$ 有 $j<C_\theta$，则 $u<48/25,z>279$。每段内部的 $j$ 导数严格正，包括其非负端点。$L$ 在全部闭弧上严格正，且 $a/n<3/2$ 在整个闭 $\mathcal S_+$ 上成立；后一界的端点可用同一规则得到 $0.616<a/n<0.617$ 和 $1.359<a/n<1.360$。

由这些界，V 定理30.4的分支分离证明可直接用于闭弧。它也分开 $r=0$ 闭弧：若一条 $\Phi=0$ 弧的世界有 $j=C_\theta$，则由 $L>0,\Delta\ne0$ 得 $r=0$，同一个 $z$ 再由(1.11)恢复同一个来源。故对每个 $\theta\in I$，

$$
P\longmapsto(z_\theta(P),j_\theta(P))
\quad\text{在 }
\{P\in\overline{\mathscr S}:r\Phi=0,\ \Delta\ne0\}
\text{ 上单射}.
\tag{1.15}
$$

接着证明这个零层在每个有限响应点都有局部反解。所有微分在上述光滑实源曲面上取。

在 $r=0,\Phi\ne0$ 处，$dF_\theta=(\Phi/(5\Delta))dr$。$r=0$ 是正则曲线：在有限 $s$ 的 $P(s,t)$ 图上，$r$ 的分子关于 $t$ 的系数是 $-((2-\theta)+(3-\theta)s)\ne0$；无穷端点改用 $1/s$ 图，同一系数在端点为 $-(3-\theta)\ne0$。沿这条曲线的 $z$ 导数由(1.11)非零。因此 $(F_\theta,z_\theta)$ 的源微分秩为二。

在 $\Phi=0,r\ne0,\Delta\ne0$ 处，$dF_\theta=(r/(5\Delta))d\Phi$；VI (27.17)的 $(u,\Phi)$ 坐标及闭弧上 $dj_\theta/du>0$，给 $(F_\theta,j_\theta)$ 的源微分秩为二。

在 $r=\Phi=0$ 处不能沿用上述任一非零系数。此时(1.3)却给

$$
dj_\theta=\frac{6L}{\Delta}\,dr,
\tag{1.16}
$$

系数非零，而沿 $r=0$ 曲线的 $z$ 导数仍非零。因此 $(z_\theta,j_\theta)$ 的源微分秩为二。这个情形保留了两条零层分支的接合，不把同一来源重复计成碰撞，也不依赖 $dF_\theta\ne0$。

由参数形式的逆函数定理，在以上每一点附近，三个量 $(F_\theta,z_\theta,j_\theta)$ 中至少两个量连同 $\theta$ 唯一确定邻近来源。这一局部结论在非负边界点的完整实曲面邻域上先成立，再限制回原严格正域，故也适用于任意趋近对角的不同源对。

还须控制唯一漂移极点。对 $u\in[18383242777/10^{10},18383242778/10^{10}]$ 的 $n_+$ 分支，(1.14)的同一有理区间规则给

$$
\begin{gathered}
-86<\left.\frac{d\Delta}{du}\right|_{\Phi=0}<-85,\qquad
11/10<a/n<111/100,\\
2<1+(1+2n)(V/h-20/n)<3.
\end{gathered}
\tag{1.17}
$$

因此 $d\Phi,d\Delta$ 在 $P_\sigma$ 线性无关；前者的正则性来自 VI (27.17)，后者沿其零弧的导数由(1.17)非零。在 $\Delta=0$ 上代入 $K_\theta=-20hr/n$，得到

$$
Z_\theta(P_\sigma)
=24hr\{1+(1+2n)(V/h-20/n)\}>0
\quad(\theta\in I).
\tag{1.18}
$$

这里 $r>0$，因为 $a/n<111/100<13/8$。若来源趋于该点且 $\theta\in I$，实际 $z=Z_\theta/\Delta$ 必趋向带符号的无穷。

在每个 $(\theta_0,P_\sigma)$ 附近，使用未知来源和参数 $(\theta,\xi,t)$ 的两条光滑方程

$$
r\Phi-5\xi\Delta=0,\qquad
\Delta-tZ_\theta=0.
\tag{1.19}
$$

在 $(\theta_0,0,0,P_\sigma)$ 处，关于来源的两行微分为 $r\,d\Phi,d\Delta$，线性无关。隐函数定理给参数附近唯一的来源解。对于原实际世界，$t=1/z$；当来源逼近极点时，此值有定义且趋于零。故同一个 $\theta,\xi,z$ 已在极点邻域唯一确定来源，正、负无穷方向同时包括。没有把未定义的 $F_\theta$ 在极点处误作连续函数。

最后排除来源逃逸。写(1.10)的 $u=b+c+1-p,n=1+b+2c,a=1+2u-c$。若一列非负来源无界，则 $bc\le1/4$ 使其有子列属于 $b\to\infty,c\to0$ 或 $c\to\infty,b\to0$。对任意 $\theta_j\to\theta_0\in I$，分别有

$$
\begin{array}{c|c|c|c|c}
\text{尾部}&n/u&a/u&\Phi/u^3&\Delta/u^4\\ \hline
b\to\infty&1&2&14&2\\
c\to\infty&2&1&19&2
\end{array}
\tag{1.20}
$$

所以两类尾部的 $F_{\theta_j}$ 极限分别为

$$
\frac75(\theta_0-2)\ne0,\qquad
\frac{19}{10}(2\theta_0-1)\ne0.
\tag{1.21}
$$

若有界来源趋向 $u=0$，则只能趋向 $\operatorname{diag}(1,0)$；那里 $n=a=1,\Phi=-40,\Delta=-4$，故 $F_{\theta_j}\to2(\theta_0-1)\ne0$。因此 $F_{\theta_j}(P_j)\to0$ 的来源列必有有界子列，且其极限 $u>0$。这些结论不预设漂移有界。

反设不存在(1.4)所需的统一 $\varepsilon_J$。可取 $\theta_j\in I,\xi_j\to0$ 及每个父上两个不同世界，使其实际 $JJ$ 响应相同。由(1.9)记其不同来源为 $P_j,Q_j$。取子列，令 $\theta_j\to\theta_0\in I$。由(1.20)—(1.21)，再取子列有 $P_j\to P_*,Q_j\to Q_*$，两极限属于非负源曲面且 $u>0$。

若 $\Delta(P_*)=0$，把(1.9)清分母后取极限，得 $r(P_*)\Phi(P_*)=0$。由(1.8)的闭弧版本，$\Delta=r=0$ 不可能，故 $\Phi(P_*)=0$。VI (27.16)及 V 定理29.3遂给 $P_*=P_\sigma$。由(1.18)，共同 $z$ 无界，因此 $\Delta(Q_*)$ 也必须为零，同理 $Q_*=P_\sigma$。但两来源最终同处(1.19)的唯一解邻域，并有相同的 $\theta_j,\xi_j,t_j=1/z_j$，强制 $P_j=Q_j$，矛盾。反向交换 $P,Q$ 同理。

若两个极限的 $\Delta$ 均非零，则 $r\Phi=0$；连续性给相同的极限 $z,j$，(1.15)给 $P_*=Q_*$。在此共同有限响应点，上述三种局部反解之一适用。两来源最终在同一逆函数邻域内，又有相同的 $\theta_j,F_{\theta_j}=\xi_j,z_j,j_j$，仍迫使 $P_j=Q_j$，矛盾。所有可能的极限至此穷尽，证明(1.4)。

源相同即由(1.9)及原四节点插值恢复同一完整世界。固定实际第六 $J$ 的读数后，末 $J$ 单射，所以原 $L_1$ 所需的末 $J$ 碰撞不存在；原 $L_2$ 的第六 $J$ 条款因而失败。这个推导不约束末 $M$ 的见证对，也不将 M 臂的任何锚定对或界赋给 J 臂。

取 $\varepsilon_*=\min\{\varepsilon_J,1/(10^{20}B)\}$。VI 定理32.1直接排除 $\theta\le11/10$ 与 $\theta\ge181/100$ 的外侧走廊，(1.4)排除整个 $I$，得到(1.6)，不重证 VI 的 MM 排除。

本证明只除原正迹及已证明非零的 $\Delta$；极点的倒读数仅在 $z$ 无界、最终非零的邻域使用。不除 $\Phi$、$r$、漂移、采样增益或最高次系数。故全部非零至多三次实多项式、任意符号、降次、采样根和重根均保留。$\Delta=0$ 的排除由(1.7)—(1.8)推出，未作为额外承诺；漂移的全部非紧尾部由(1.18)—(1.19)处理。原第六、第七时钟上的两个 J 均立即读取；连同父历史的初读共至多八读。

新增承重结论是(1.4)的全源统一参数延拓及(1.6)的原共同父消费者，属于仓内推导（repo-derived）。零轴内部的分支穷尽、响应分离和正则源坐标分别复用 V 定理29.3、30.3—30.4及 VI (27.16)—(27.17)；新增部分补齐非负端点、接合处的秩二反解、极点反解及两类非紧源尾部。逆函数定理、隐函数定理、紧性和有理区间四则运算均是这些既有证明已使用的成熟中间工具，不申领外部优先权。

本结论是精确实响应合同中的数学单射性；存在性常数 $\varepsilon_J$ 未赋予数值，局部反解不提供统一有限位算法、误差界或稳定性。剩余的两个中央间隙、较大非零偏离、完整的 $\mathcal P_M\cap\mathcal P_J$ 判定、与更早祖先的接合、原根八读／九读判别及九读上界均未由本定理结清。历史始终为 $MMJMM$；VI 第28—31章的 $MJMM$ 不作供应。∎

## 追加锚（本行以下为增补区）

## 2. 同一实际 M 子纤维的共享响应桥

**定义 2.1（不除极层的父与子响应坐标）。** 保持定义1.1的整个世界域和字面父历史。对严格正来源 $P$ 及任意实漂移 $d$，令

$$
\begin{aligned}
\Theta(P,d)&=\frac an+\frac{d\Delta}{24hn},\\
\Xi(P,d)&=\frac{d\Phi}{120h},\qquad
\Omega(P,d)=\frac{d\Psi_6}{h},\\
\mathscr J(P,d)&=d+(4n-u+1)
 \left\{\frac{210}{n}+d\left(\frac Xh-\frac{35}{n}\right)\right\}.
\end{aligned}
\tag{2.1}
$$

$\Psi_6$ 取 VI (8.6)，其余源量取本卷(1.2)。仅有的分母是原本严格正的 $h,n$。令 $g_{P,d}$ 是 VI (8.2)的唯一四节点插值，$W(P,d)=(P,g_{P,d},d)$。VI 定理8.2的无除数恒等式给

$$
\begin{gathered}
W(P,d)\in\mathcal F(H^-_{\theta,\xi})
\quad\Longleftrightarrow\quad
\Theta(P,d)=\theta,\quad\Xi(P,d)=\xi,\\
r_M^{(6)}(W)=120(1+2\theta)+\Omega(P,d),\qquad
r_{MJ}^{(7)}(W)=\mathscr J(P,d).
\end{gathered}
\tag{2.2}
$$

因此 $\Omega$ 是同一实际第六 $M$ 读数相对父基线的残差。定义不把两个互择末动作的响应视作共同取得的读数。四节点插值总是非零多项式，因为原时钟零与三的实际读数分别为零与六。

**定理 2.2（两个完整间隙上的统一共享响应桥）。** 置

$$
\mathcal U=[11/10,13/8)\ \cup\ (5/3,181/100].
\tag{2.3}
$$

对每个紧集 $E\subseteq\mathcal U$，存在 $\delta_E>0$，使对所有 $\theta\in E$、$|\xi|<\delta_E$ 及 $|\omega|<\delta_E$，末 $J$ 的原时钟七响应在整个实际子纤维

$$
\mathcal K_{\theta,\xi,\omega}
=\mathcal F\bigl(H^-_{\theta,\xi},M,
                    120(1+2\theta)+\omega\bigr)
\tag{2.4}
$$

上对完整世界单射。这里不要求该子纤维的所有世界属于 VI (27.1)的重复 MM 签名域，也不限制漂移或增益符号。

证明。先确定可作为极限的闭源与完整世界，再建立邻近不同世界的分离。以下非负来源仅是严格正来源的极限，不扩大合法世界域。

复用 V (27.5)—(27.6)的固定来源 $P_*$，并将其源量加下标 $*$。VI 定理26.2及(27.16)—(27.18)给出整个非负来源域内的等价式和简单零点性质

$$
\begin{gathered}
\Phi=\Psi_6=0\quad\Longleftrightarrow\quad P=P_*,\\
\Psi_{7,*}\ne0,\qquad
\left.\frac{d\Psi_6}{du}\right|_{\Phi=0,P_*}\ne0,\\
\Delta_*=h_*n_*S_*>0,\qquad 3/4<k_*<4/5.
\end{gathered}
\tag{2.5}
$$

说明这些供应之间的对应：V 定理28.2的非零漂移固定源在基线第六 $M$ 子纤维中，故无除数式给 $\Phi_* =\Psi_{6,*}=0$。VI 定理26.2的唯一 $\Psi_6$ 零点及 VI (27.16)的闭源穷尽将它识别为同一个 $P_*$，没有附加边界解。该点的 Wronskian (27.18)非零，而 $\Psi_{7,*}\ne0$，所以沿 $\Phi=0$ 有 $d\Psi_6/du\ne0$。最后两项由 V (27.6)、(28.12)供应。这个识别不将固定源的其他参数赋给任意来源。

取任意 $\theta_i\in E$、$\xi_i\to0$、$\omega_i\to0$，以及任意满足

$$
\Theta(P_i,d_i)=\theta_i,\qquad
\Xi(P_i,d_i)=\xi_i,\qquad
\Omega(P_i,d_i)=\omega_i
\tag{2.6}
$$

的合法世界序列。证明来源和漂移都不能逃逸。先取子列使 $\theta_i\to\theta_0\in E$。写

$$
P_i=\begin{pmatrix}p_i&b_i\\c_i&1-p_i\end{pmatrix},\qquad
b_ic_i=p_i(1-p_i)\le1/4,
\qquad u_i=b_i+c_i+1-p_i.
\tag{2.7}
$$

若 $u_i\to\infty$，再取子列后只有两种尾部：$b_i\to\infty,c_i\to0$ 或 $c_i\to\infty,b_i\to0$。VI (27.12)—(27.14)在整个 $u\ge3$ 尾部给 $\Phi>0$、$h/\Phi\le1/9$ 及 $|5\Delta/(n\Phi)|<12$；这些尾部界不要求签名重复。因此

$$
d_i\longrightarrow0,\qquad
\theta_i-\frac{a_i}{n_i}
 =\xi_i\frac{5\Delta_i}{n_i\Phi_i}\longrightarrow0.
\tag{2.8}
$$

两类尾部的 $a_i/n_i$ 分别趋于 $2$ 和 $1/2$，与 $\theta_0\in E$ 矛盾。若 $u_i\to0$，则 $P_i\to\operatorname{diag}(1,0)$，那里 $n=a=1,\Phi=-40,\Delta=-4$。由 $d_i/h_i=120\xi_i/\Phi_i\to0$，(2.1)给 $\theta_i\to1$，也矛盾。故 $u_i$ 有统一正下界与有限上界；(2.7)遂使来源落在某个紧的非负集合内。

若 $|d_i|\to\infty$，取来源极限 $P_0$。因 $h_i$ 有界且有正下界，(2.6)迫使 $\Phi(P_0)=\Psi_6(P_0)=0$，于是 $P_0=P_*$。另一方面，$\theta_i-a_i/n_i=d_i\Delta_i/(24h_in_i)$ 有界，便要求 $\Delta(P_*)=0$，违反(2.5)。因此漂移也有界。再取子列有

$$
(P_i,d_i)\longrightarrow(P_0,d_0),\qquad u(P_0)>0.
\tag{2.9}
$$

在此域内(2.1)连续，故极限世界的来源和漂移必属于下列两个部分：

$$
\begin{array}{c|c}
\text{零漂移部分}&d_0=0,\quad a(P_0)/n(P_0)=\theta_0\\
\text{固定源部分}&P_0=P_*,\quad
 d_0=d_{\theta_0}=24(\theta_0-k_*)/S_*.
\end{array}
\tag{2.10}
$$

第二行的漂移严格正，因为 $\theta_0\ge11/10>k_*$。除共同父条件及 $\xi_i\to0$ 外，这个紧性结论对实际子纤维额外只用了共同的 $\omega_i\to0$，没有将任何锚定 MM 对的 $q,\eta$ 或漂移界传给本列世界。

为同时处理零漂移源的全部非负端点，给出闭弧坐标。对 $1<k<2$、$1/2\le x\le1$，置

$$
\begin{gathered}
D_k(x)=(3-2k)x^2+k-1,\\
\mathsf P(k,x)=\frac1{D_k(x)}
\begin{pmatrix}
(2x-1)(1+x-kx)&(2x-1)(k-x)\\
(1-x)(1+x-kx)&(1-x)(k-x)
\end{pmatrix}.
\end{gathered}
\tag{2.11}
$$

分母严格正，且这些矩阵恰为 $a/n=k$ 的全部非负秩一迹一来源。确实，$D_k$ 在 $[1/2,1]$ 上单调或恒定，两个端点值为 $(2k-1)/4$ 和 $2-k$，均正；显示矩阵直接满足秩一与迹一。反向，对非负来源写 $x=(p+c)/(p+2c)$，便有 $1/2\le x\le1$，四迹逆给(2.11)。若 $p+2c=0$，则 $p=c=0$，进而 $a/n=(3+2b)/(1+b)>2$，不在这里的范围。故反向没有遗漏分母零层。该有理逆也说明 $(k,x)$ 是这些闭弧各点附近完整实源曲面的光滑局部坐标，包括 $x=1/2,1$。

在零漂移部分，V (28.9)、(28.13)或直接代入(2.1)给

$$
\begin{aligned}
\frac{\mathscr J(\mathsf P(\theta,x),0)}{210}
 &=f_\theta(x)
 =\frac{2+4x+x^2+\theta(1-3x^2)}{1+x-x^2},\\
\partial_x f_\theta(x)
 &=\frac{5x^2+6x+2-\theta(3x^2+4x+1)}{(1+x-x^2)^2}.
\end{aligned}
\tag{2.12}
$$

V (28.13)的临界比值在 $[1/2,1]$ 上从 $5/3$ 严格递减至 $13/8$。故对每个 $\theta\in E$，(2.12)的导数在整个闭弧上严格同号且不为零；其响应严格单调，像的两个端点为

$$
f_\theta(1/2)=\frac{17+\theta}{5},\qquad
f_\theta(1)=7-2\theta.
\tag{2.13}
$$

固定源部分的响应由 V (28.11)—(28.12)给

$$
\frac{\mathscr J(P_*,d_\theta)}{210}=\alpha+\beta\theta,
\qquad \frac{903}{1000}<\alpha<\frac{904}{1000},\quad
\frac{3737}{1000}<\beta<\frac{3738}{1000}.
\tag{2.14}
$$

对于所有 $\theta\ge11/10$，精确有理比较给

$$
\begin{aligned}
\alpha+\beta\theta-(7-2\theta)&>2137/10000,\\
\alpha+\beta\theta-(17+\theta)/5&>13937/10000.
\end{aligned}
\tag{2.15}
$$

因此固定源响应严格高于零漂移闭弧的全部响应。由(2.12)—(2.15)，$\mathscr J$ 在(2.10)的整个极限集上单射。

还须防止两个不同世界趋向同一个极限世界。先在零漂移点使用 $(k,x,d)$ 坐标。此时 $d\Theta=dk+(\Delta/(24hn))\,dd$，而 $d\Xi=(\Phi/(120h))\,dd$、$d\Omega=(\Psi_6/h)\,dd$。由(2.5)及 $k=\theta\ge11/10$，$\Phi,\Psi_6$ 至少有一个非零。选择相应的三分量映射

$$
(\Theta,\Xi,\mathscr J/210)
\quad\text{或}\quad
(\Theta,\Omega,\mathscr J/210).
\tag{2.16}
$$

在该点，其关于 $(k,x,d)$ 的 Jacobian 行列式分别为

$$
-\frac{\Phi}{120h}\partial_x f_\theta(x),\qquad
-\frac{\Psi_6}{h}\partial_x f_\theta(x).
\tag{2.17}
$$

所选择的行列式非零。逆函数定理给完整实曲面邻域上的单射，再限制回严格正世界即可；这同时处理所有闭源端点与趋近对角的不同世界。

在固定源点 $(P_*,d_\theta)$，使用 VI (27.17)的局部源坐标 $(u,v)$，其中 $v=\Phi$。在 $v=0$ 上记 $\Psi_{6,u}=d\Psi_6/du$。由于 $\Phi_* =\Psi_{6,*}=0$，三分量映射 $(\Theta,\Xi,\Omega)$ 关于 $(u,v,d)$ 的行列式为

$$
\det\frac{\partial(\Theta,\Xi,\Omega)}{\partial(u,v,d)}
 =-\frac{d_\theta^2\Delta_*\Psi_{6,u}}
               {2880h_*^3n_*}\ne0.
\tag{2.18}
$$

这里 $\Theta_d=\Delta_*/(24h_*n_*)$、$\Xi_v=d_\theta/(120h_*)$、$\Omega_u=d_\theta\Psi_{6,u}/h_*$，其余影响行列式的项因 $v=\Psi_6=0$ 消失。(2.5)保证所有因子非零。因此仅同一个父及共同实际第六读数，已在这个邻域唯一确定完整世界，无须再比较末 $J$。$\Delta=0$ 没有作为一般除数被删除；固定源的 $\Delta_*>0$ 是已证性质。两极限部分的同源接合只可能在 $\theta=k_*$，严格在 $E$ 外；不是把一个世界重复计成碰撞。

反设不存在所需的 $\delta_E$。可取 $\theta_i\in E$、$|\xi_i|,|\omega_i|<1/i$，以及(2.4)中两个不同完整世界，使末 $J$ 响应相同。对两列同时应用(2.6)—(2.10)，取共同子列得到同一 $\theta_0$ 上的两个极限世界。末响应连续，(2.12)—(2.15)迫使这两个极限相同。在该共同极限处，(2.16)或(2.18)给一个单射邻域。两世界最终同处该邻域，又有相同的 $\Theta,\Xi,\Omega,\mathscr J$，必有相同的来源与漂移；唯一四节点插值再给相同的整个 $g$，矛盾。

这证明(2.4)上的统一单射，既不要求碰撞对与任何 MM 锚定对相同，也不限制 $\xi$ 的正负或排除零值。紧性、闭源分离与局部反解共同承担扰动结论；仅零轴上的单射不被用来直接推出邻域单射。∎

## 3. 中央闭段的端点接合

**定理 3.1（中央 JJ 的统一参数厚度）。** 存在 $0<\eta<1/100$ 与 $\varepsilon_C>0$，使对所有

$$
13/8-\eta\le\theta\le5/3+\eta,\qquad
|\xi|<\varepsilon_C,
\tag{3.1}
$$

固定原时钟六、七接续 $J,J$ 在整个 $\mathcal F(H^-_{\theta,\xi})$ 上对完整世界单射。

证明。须使用定理1.2证明中的闭源分离与局部秩，不能仅由其闭参数段上的单射性推断(3.1)。反设没有任何正的参数厚度与偏离半径。则可取

$$
\operatorname{dist}(\theta_i,I)\longrightarrow0,\qquad
\xi_i\longrightarrow0,
\tag{3.2}
$$

以及每个父上两个不同完整世界，具有相同的实际 $JJ$ 响应。取子列使 $\theta_i\to\theta_0\in I$。

先排除这列实际世界中的 $\Delta=0$。无除数父方程仍为(1.7)，故 $\Delta=0$ 迫使 $r=0$，即 $k=\theta_i$。对于 $k$ 在 $I$ 的一个固定小邻域内，(2.11)把 $k=\theta_i$ 的全部来源置于 $x\in[1/2,1]$ 的一个紧闭弧族，且 $h,n$ 都有正下界。若存在无穷多个这样的零点，取来源极限就有 $k=\theta_0,\Delta=0$。但(1.8)的闭弧版本给

$$
\frac{\Delta}{nh}\le1-\theta_0<0,
\tag{3.3}
$$

矛盾。因此对于充分大的 $i$，两世界均有 $\Delta\ne0$，可以使用(1.3)的源函数与实际响应，并有 $F_{\theta_i}(P_i)=\xi_i$。

(1.20)—(1.21)的两个来源尾部极限只要求 $\theta_i\to\theta_0\in I$，不要求每个 $\theta_i\in I$：其极限分别为 $7(\theta_0-2)/5$ 和 $19(2\theta_0-1)/10$，均非零。$u\to0$ 的极限仍为 $2(\theta_0-1)\ne0$。故两列来源均不能逃逸，也不能趋向 $u=0$。再取子列，两来源分别趋于非负来源 $P_0,Q_0$，且 $u>0$。

若 $\Delta(P_0)=0$，清分母父方程给 $r(P_0)\Phi(P_0)=0$。(3.3)排除 $r=0$，故 $\Phi(P_0)=0$。VI (27.16)及 V 定理29.3给 $P_0=P_\sigma$。此时(1.17)—(1.18)在 $\theta_0\in I$ 给 $Z_{\theta_0}(P_\sigma)>0$，所以共同的第六 $J$ 响应 $z_i$ 无界，迫使 $\Delta(Q_0)=0$，继而 $Q_0=P_\sigma$。在这个极点邻域使用(1.19)的两条方程；关于来源的 Jacobian 在 $(\theta_0,0,0,P_\sigma)$ 可逆，参数邻域允许 $\theta$ 从 $I$ 外趋近。两来源有相同的参数 $\theta_i,\xi_i,t_i=1/z_i$，故由隐函数定理的局部唯一性相同，矛盾。交换 $P,Q$ 覆盖另一零分母情形。

若两个极限的 $\Delta$ 均非零，连续性给 $r\Phi=0$ 及相同的极限 $z,j$。(1.15)在整个非负极限集上单射，故 $P_0=Q_0$。在共同点处，定理1.2证明给出的三种局部反解仍适用：$r=0,\Phi\ne0$ 时用 $(F_\theta,z_\theta)$；$\Phi=0,r\ne0$ 时用 $(F_\theta,j_\theta)$；$r=\Phi=0$ 时用 $(z_\theta,j_\theta)$。每个所选源微分均为秩二，包括闭源端点。在把 $\theta$ 同时作为输入、输出参数后，逆函数定理给包含 $(\theta_0,P_0)$ 的完整实邻域上的单射，不限制参数从哪侧趋近。于是两来源最终有相同的局部逆像，再次矛盾。

这些情形穷尽来源边界、漂移极点、同源接合和趋近对角。来源相同后，(1.9)及原四节点插值恢复相同完整世界。因此不存在(3.2)的碰撞列，必有正的厚度与偏离半径；缩小厚度使 $\eta<1/100$，再在所获开邻域内取闭带即得(3.1)。这是有完整局部反解与逃逸排除支持的端点接合，不是对闭区间单射性的一般延拓断言。∎

## 4. 全参数统一小偏离的实际两读消费者

**定理 4.1（所有实父参数的统一小偏离带）。** 存在 $\varepsilon_0>0$，使在定义1.1的整个原模型中

$$
\forall\theta\in\mathbb R\quad\forall\xi\in\mathbb R,
\quad |\xi|<\varepsilon_0
\quad\Longrightarrow\quad
\forall K\subseteq\mathcal F(H^-_{\theta,\xi}),\qquad
\neg L_2(K,H^-_{\theta,\xi}).
\tag{4.1}
$$

即整个字面 $MMJMM$ 父族在这一统一带内，均有只在原时钟六、七至多再读两次的确定性完整恢复策略。此结论不要求同臂两种末动作使用同一碰撞对，也不要求两个第六臂共享响应或来源。

证明。取定理3.1的 $\eta,\varepsilon_C$，令

$$
E=[11/10,13/8-\eta]\ \cup\ [5/3+\eta,181/100],
\tag{4.2}
$$

它是定理2.2所允许的紧集。取其 $\delta_E>0$，以及 VI 定理27.3中任意满足(27.9)的存在性常数 $B\ge539$。定义

$$
\varepsilon_0=
\min\left\{\frac1{10^{20}B},\ \varepsilon_C,
                      \frac{\delta_E}{120B+1}\right\}>0.
\tag{4.3}
$$

这里没有以数值 $539$ 代替未知的充分上界 $B$。

先设 $0<|\xi|<\varepsilon_0$。当 $\theta\le11/10$ 或 $\theta\ge181/100$，VI 定理32.1供应整个父纤维的固定 $MM$ 单射；当 $13/8-\eta\le\theta\le5/3+\eta$，定理3.1供应整个父纤维的固定 $JJ$ 单射。这两类参数均立即满足(4.1)。余下参数属于(4.2)，对它们先在原时钟六实际选择 $M$，取得 $w$，置

$$
\omega=w-120(1+2\theta).
\tag{4.4}
$$

若 $|\omega|<\delta_E$，定理2.2给同一个整个实际子纤维上的末 $J$ 单射。若 $|\omega|\ge\delta_E$，末 $M$ 也必在这个整个实际子纤维上单射：否则取两个不同世界的实际 $MM$ 碰撞，仅对这对应用 VI 定理27.3，即得

$$
|\omega|\le120B|\xi|<\delta_E,
\tag{4.5}
$$

矛盾。因此在 $E$ 上可以用同一条实际轨迹执行

$$
E_6=M,\qquad
E_7=\begin{cases}
J,&|w-120(1+2\theta)|<\delta_E,\\
M,&|w-120(1+2\theta)|\ge\delta_E.
\end{cases}
\tag{4.6}
$$

每个所选末动作在其整个实际子纤维上单射，故在实际响应像上取唯一完整世界的逆即恢复整个父纤维。空子纤维没有实际路径，单点纤维允许早停。

也可直接保留失败递归的独立碰撞量词：若某个 $K\subseteq\mathcal F(H^-_{\theta,\xi})$ 有 $L_2$，其第六 $M$ 条款供应某个实际 $w$ 子纤维的 $L_1$。该 $L_1$ 的末 $M$ 碰撞对给(4.5)，所以共同的实际 $w$ 落入定理2.2的响应窗口；于是该同一子纤维上的末 $J$ 单射，排除其末 $J$ 碰撞对。两对完全可以不同，推导只传递它们共同的 $w$。未对第二对套用第一对的 $q,\eta,d$ 界，也未对第六 $J$ 臂套用 MM 锚定界。这个矛盾证明(4.1)在整个非零偏离带内成立。

若 $\xi=0$，对全部实 $\theta$ 直接复用 VI 定理26.4的原两读策略及任意子集消费者。因此(4.1)包含整个零轴，并与非零偏离使用同一个 $\varepsilon_0$。

外侧闭走廊、(4.2)的两个完整闭间隙与中央厚闭段覆盖全部实 $\theta$，各端点均在已证明的参数域内。定理2.2的来源与漂移紧性、闭源单调分离及局部反解，定理3.1的两类来源尾部、闭源分离、同源接合与极点图，分别承担其所用的全部极限情形；未以正源内部的单射性替代这些边界义务。定义2.1不除 $\Phi,\Delta,d$，中央段对 $\Delta=0$ 的排除由无除数父方程证明，极点图仅在响应无界且非零的邻域取倒响应。没有除任何采样增益或最高次系数。因此任意符号、降次、采样根、重根及任意常漂移全部保留。

承重增量是同一实际第六 $M$ 响应对独立末动作碰撞对的连接、两个完整参数间隙上的统一响应窗口、中央闭段的端点厚度，以及它们消费为(4.1)的全参数带，属于仓内推导（repo-derived）。V 定理28.2—28.4及 VI 定理26.2、27.3、32.1分别供应固定源与零漂移相图、闭极层结构、实际 MM 锚定界和外侧消费者；定理1.2的证明供应中央闭段的边界与极点图。四节点插值、隐函数定理、逆函数定理与紧性是这些既有来源已使用的成熟中间工具，不单列为新增理论。Li、Lee、Bresler，[定义2.7、定理2.8](https://arxiv.org/html/1501.06120v1)的双线性变换群可识别性条件，以及 Breiding、Gesmundo、Michałek、Vannieuwenhoven，[*Algebraic compressed sensing*，Answer 9](https://arxiv.org/html/2108.13208v2)的泛型线性映射条件，都不提供本字面原时钟、三次增益与加性漂移的共享实际响应桥；本证明不从它们导入固定词的单射性，也不申领外部优先权。

(4.1)是精确实读数合同内的存在性恢复结论；$\eta,\delta_E,\varepsilon_C,\varepsilon_0,B$ 不被赋予数值充分性或有限位实现含义，(4.6)不声称可计算性、稳定性或误差界。$|\xi|\ge\varepsilon_0$ 的共同父交集、全父参数平面、更早祖先接合、其他字面历史以及原根八读／九读判别和九读上界，均不由本定理结清。特别地，VI 第28—31章的 $MJMM$ 不作为供应，也不与这里的 $MMJMM$ 认同。∎

## 追加锚（本行以下为增补区）
