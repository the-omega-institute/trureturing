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
