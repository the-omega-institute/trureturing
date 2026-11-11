# AURIC 全部探针与环境耦合的固定输出延续 II：零模耦合为零的可行闭区间

本卷承接[前卷 §17](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#17-全部原探针的共同六维读取支撑) 的共同读取与全正泛函提升、[§27](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#27-全有限类的联合探针与环境系数判据) 的原联合二次型、[§27A](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#27a-满行秩原四维族的线性尺度正预算排除域) 的四维排除域、[§28](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#28-原输入的齐次核与环境零模像上的值域障碍) 的核与值域条件、[§29](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#29-平衡零模像线的有限核反例与整类残量刚性) 和 [§30A](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30a-非零零模像上全部原-pb-消去两个独立对角残量) 的非零零模像结论，以及 [§30](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30-零模耦合为零的三矩实现与最小真实环境) 的零模耦合为零分支。下文编号为 §32；未加前缀的旧式号均指前卷。这里在 (30.30) 的可实现三矩域中给出一条固定矩族：一个与 Schur 块小扰动无关的 PB 半径包含该族的整个原 P2 闭区间。

## 32. 同一四维实际环境的全部原 PB 与精确 P2 交

**定义 32.1（固定三矩的四维族）。** 在完整 $M_4(\mathbb C)$ 上取演员与环境各为 $\mathbb C^2$，固定

$$
\begin{gathered}
C=\operatorname{diag}(1,2),\qquad T_A=\operatorname{diag}(1,-2),
\qquad J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
c=C\oplus0_2,\qquad P=I_2\oplus0_2,\qquad V=D_{\rm env}=C,\\
H_h=2C+hJ_A,\qquad B_h=H_h+C,\qquad
t_h=\begin{pmatrix}B_h&C\\C&C\end{pmatrix},\qquad
s=\rho T_A\oplus0_2,\qquad h,\rho\in\mathbb R .
\end{gathered}
\tag{32.1}
$$

沿用 (1.1)–(1.2)、(17.1) 的原 P2、原 PB 与全部实际探针 $x=X\oplus0_2$，其中 $X=X^*$。取向 $\sigma$ 的输出仍为 $g_\sigma=\sigma i[c,t_h]/2+s$。因 $D_{\rm env}$ 可逆，$W=V|_{\ker D_{\rm env}}=0$。按 (30.2) 有 $F=C$、$G=I_2$，故原三矩恰为 $(M_0,M_1,M_2)=(C^2,C,I_2)$，Schur 块恰为 $H_h$。环境块与三个矩在全族中固定。

**定理 32.2（统一 PB 半径与闭区间的两个端点）。** 存在 $h_*,\rho_*>0$，使对每个 $|h|<h_*$，同一 (32.1) 输入在每个 $|\rho|<\rho_*$ 时满足两个取向的全部原 PB。对每个 $0<h<h_*$ 以及任意实 $\rho$，以下结论等价：该输入在两个取向均满足原 P2 与全部原 PB；该输入在任一个分别固定的取向满足原 P2 与全部原 PB；以及

$$
\boxed{\quad -\frac{\sqrt2\,h}{3}\ \le \rho\le\ \frac{\sqrt2\,h}{3}.\quad}
\tag{32.2}
$$

这里所有预算都在完整原代数上对全部正复线性泛函成立，包括任意指定正有限质量与零质量。区间的两个非零端点均严格位于 $|\rho|<\rho_*$ 内。特别地，可固定 $h=h_*/2$ 和 $\rho=\sqrt2\,h/3$，在同一份 $t_h,s$ 上同时得到两个取向的非零残量解。

**证明：原带符号二次型。** 暂写 $B=B_h$、$H=H_h$、$t=t_h$，并记 $\iota=\sigma i$。对复数 $z$ 定义 $\operatorname{Im}_\iota z$ 为 $z$ 在基 $1,\iota$ 下的虚系数。固定 (27.6) 的任意索引 $\theta$，即单位演员 $u$、绝对值符号 $\epsilon\in\{1,-1\}$ 及两对有限参数 $\alpha_\delta>0,\ \beta_\delta\in\mathbb R$。在同一原向量 $\xi=(u,y)$、同一实际 $X=X^*$ 上写 $\mathbf R_\delta=R_\delta\xi$、$\mathbf S_\delta=S_\delta\xi$，其中 $S_\delta=t+\delta(r+g_\sigma)$ 是 (27.10) 的原算子。置

$$
\begin{aligned}
\zeta_\delta&=\beta_\delta-\delta\epsilon\iota\alpha_\delta
             =\iota+\nu+\delta\ell,\qquad
E_\delta=\mathbf S_\delta-\zeta_\delta\mathbf R_\delta,\qquad
S_0=\sum_{\delta=\pm1}\alpha_\delta^{-1}\|E_\delta\|^2,\\
\mathcal D_\rho&=\sum_{\delta=\pm1}
  \left(\alpha_\delta\|\mathbf R_\delta\|^2+
        \alpha_\delta^{-1}\|\mathbf S_\delta-\beta_\delta\mathbf R_\delta\|^2\right)
        -2\epsilon\phi_\xi(L).
\end{aligned}
\tag{32.3}
$$

$S_0$ 是同一输入在当前 $\rho$ 上的平方和。把平方展开，其交叉项为
$2\delta\epsilon\operatorname{Im}_\iota(\mathbf R_\delta^*\mathbf S_\delta)$，即 $-2\delta\epsilon\phi_\xi(K_\sigma(R_\delta,S_\delta))$。因此

$$
\mathcal D_\rho-S_0
=2\epsilon\,\phi_\xi\!\left(\sum_\delta\delta K_\sigma(R_\delta,S_\delta)-L\right).
$$

前卷 §1 的原换位恒等式给括号内的零残量部分为零。写 $a=Bu+Vy$、$p=Xu$、$v=a-\iota p$。加入 $s$ 使 $S_\delta$ 增加 $\delta s$、使 $L$ 减去 $2t\circ s$，而 $R_++R_-=2x$。故括号内的改变量是 $2K_\sigma(x,s)+2t\circ s$。其向量读数为 $2\rho\operatorname{Re}(v^*T_Au)$，因为 $\phi_\xi(K_\sigma(x,s))=\rho\operatorname{Re}(\iota p^*T_Au)$。这给出原二次型的精确恒等式

$$
\mathcal D_\rho=S_0+4\epsilon\rho\operatorname{Re}(v^*T_Au).
\tag{32.4}
$$

**证明：实际作用列与加权方差。** 记 $q=XCu$、$d=Fu+D_{\rm env}y$、$U=\iota q+BCu+Cv$。按 (27.4)–(27.5) 在 $\tau=1$ 的原作用列，$\mathbf R_\delta$ 的两块为 $p-\delta U/2$、$-\delta FCu/2$；$\mathbf S_\delta$ 的两块为

$$
a+\delta\left(\frac{Cp+q+\iota Ca-\iota BCu}{2}+\rho T_Au\right),
\qquad d-\frac{\delta\iota}{2}FCu .
$$

代入 $\zeta_\delta$ 后，$E_\delta$ 的演员与环境块分别是

$$
\begin{aligned}
(E_\delta)_{\rm act}&=\mathsf P+\delta\mathsf Q,\qquad
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\\
(E_\delta)_{\rm env}&=d+(\ell+\delta\nu)FCu/2 .
\end{aligned}
\tag{32.5}
$$

令 $r_\ell=|\ell|$、$n=|\nu|$、$A=(\alpha_++\alpha_-)/2$。两条 $\zeta_\delta$ 的虚系数给出

$$
|1+\operatorname{Im}_\iota\nu|<A=-\epsilon\operatorname{Im}_\iota\ell\le r_\ell,
\qquad r_\ell+n\ge1 .
\tag{32.6}
$$

反过来，给定满足 (32.6) 首行的 $\nu,\ell,A$，取 $\alpha_\delta=A-\delta\epsilon(1+\operatorname{Im}_\iota\nu)$、$\beta_\delta=\operatorname{Re}(\nu+\delta\ell)$ 即还原原参数。特别地 $r_\ell>0$。记 $w_\delta=\alpha_\delta^{-1}$、$\omega=(w_+-w_-)/(w_++w_-)$ 及 $e=d+(\ell+\omega\nu)FCu/2$。以 $e$ 为同一对环境列的加权平均，交叉项相消，且 $w_+w_-/(w_++w_-)=1/(2A)$，故

$$
\begin{aligned}
\sum_\delta w_\delta\|(E_\delta)_{\rm env}\|^2
 &=(w_++w_-)\|e\|^2+\frac{n^2}{2A}\|FCu\|^2,\\
a&=Hu+G^*e-\frac{\ell+\omega\nu}{2}\,C^2u .
\end{aligned}
\tag{32.7}
$$

第二行用 $a=Hu+G^*d$、$G^*F=C$。由加权 Cauchy–Schwarz 对 $\mathsf P$ 和 $\mathsf Q$ 的半和、半差分别估计，每项范数至多 $\sqrt{2AS_0}/2$。又 $w_++w_-\ge2/A$，故 $\|e\|\le\sqrt{AS_0/2}$。于是

$$
\|\mathsf P\|+\|\mathsf Q\|+\|e\|\le3\sqrt{r_\ell S_0},
\qquad
\|a\|\le K(1+r_\ell+n+\sqrt{r_\ell S_0}).
\tag{32.8}
$$

下文的 $K$ 可逐式增大，均只依赖固定矩阵与一个预先固定的有界邻域 $\|H-2C\|\le1$，与取向、符号及整个探针索引无关。这里用到 $|\omega|\le1$，没有给任何单个 $\alpha_\delta$ 加正下界。

**证明：一个分离坐标控制残量配对。** 令 $\kappa=\nu/\ell$、$z_0=\ell(1-\kappa^2)-\iota\kappa$、$Z=z_0 I_2-C$。由 (32.5) 消去 $U$ 并代入 $v=a-\iota p$，得到

$$
\mathsf Q-\kappa\mathsf P=(\iota C-\kappa I_2)a-Zp+\rho T_Au.
\tag{32.9}
$$

记 $c_1=1,c_2=2$。至少一个 $j$ 有 $|z_0-c_j|\ge1/2$；只在该坐标上除法。(32.8)–(32.9) 给

$$
|p_j|\le K\left[\left(1+\frac{n}{r_\ell}\right)
 (1+r_\ell+n+\sqrt{r_\ell S_0})+|\rho|\right].
$$

设 $z_j'=\overline{p_j}u_j$。由 $u^*p=u^*Xu\in\mathbb R$，两项 $\operatorname{Im}_\iota z_j'$ 互为相反数，故任取其中一个坐标都有
$|\operatorname{Re}(\iota p^*T_Au)|=3|\operatorname{Im}_\iota z_j'|\le3|p_j||u_j|$。
因此 $|\operatorname{Re}(v^*T_Au)|\le2\|a\|+3|p_j||u_j|$，包括 $u_j=0$。另一个坐标即使恰好共振，也不必估计其幅值。

置 $b_\theta=(r_\ell+n)^2/r_\ell$。由 (32.6)，$b_\theta\ge1$，且

$$
\left(1+\frac{n}{r_\ell}\right)(1+r_\ell+n)\le2b_\theta,
\qquad
\left(1+\frac{n}{r_\ell}\right)\sqrt{r_\ell S_0}=\sqrt{b_\theta S_0}.
$$

以上给 $|\operatorname{Re}(v^*T_Au)|\le K(b_\theta+\sqrt{b_\theta S_0}+|\rho|)$。在 (32.4) 中对 $4K|\rho|\sqrt{b_\theta S_0}$ 用 Young 不等式，耗去至多 $S_0/2+8K^2\rho^2 b_\theta$。由 $b_\theta\ge1$，增大常数后得到

$$
\mathcal D_\rho\ \ge\ \frac{S_0}{2}-K(|\rho|+\rho^2)b_\theta .
\tag{32.10}
$$

**证明：近零比率的大尺度下界。** 先在 $\|H-2C\|\le1,\ |\rho|\le1$ 内取常数。设 $|\kappa|\le\eta_{\rm tail}\le1/2$，记 $\lambda=\ell(1-\kappa^2)$。有 $|\lambda|\ge3r_\ell/4$、$\|C+\iota\kappa I_2\|\le5/2$。当 $r_\ell\ge8$ 时，$Z=\lambda I_2-C-\iota\kappa I_2$ 可逆，$\|Z^{-1}\|\le4/r_\ell$。由 $Z^{-1}-\lambda^{-1}I_2=\lambda^{-1}Z^{-1}(C+\iota\kappa I_2)$，两逆的差范数至多 $K/r_\ell^2$。将 (32.7) 代入 (32.9)，得到

$$
p=-\frac{1+\omega\kappa}{2(1-\kappa^2)}(\iota C-\kappa I_2)C^2u+\mathsf E,
\qquad
\|\mathsf E\|\le K\left(\frac{1+|\rho|}{r_\ell}+\sqrt{S_0/r_\ell}\right).
\tag{32.11}
$$

确切地，$Z^{-1}$ 作用于 $(\iota C-\kappa I_2)(Hu+G^*e)+\rho T_Au-(\mathsf Q-\kappa\mathsf P)$ 的贡献由 (32.8) 给右侧界；用 $\lambda^{-1}I_2$ 替换 $Z^{-1}$ 作用于剩下的 $\ell$ 倍项，误差至多 $K/r_\ell$。主项在 $\kappa=0$ 时为 $-\iota C^3u/2$。在 $|\kappa|\le1/2$ 上，由 $|1-\kappa^2|\ge3/4$ 和 $|\omega|\le1$，主项与 $-\iota C^3u/2$ 的差范数至多 $K|\kappa|$。由于 $u^*C^3u\ge1$，该基准主项与 $u$ 配对的 $\iota$ 虚系数至多 $-1/2$；实际 $u^*p$ 的虚系数为零。先选 $\eta_{\rm tail}>0$ 使 $K\eta_{\rm tail}\le1/8$，再选 $R\ge8$ 使 $2K/R\le1/8$，则 (32.11) 给 $1/4\le K\sqrt{S_0/r_\ell}$。因此某个 $c_{\rm tail}>0$ 满足

$$
S_0\ge c_{\rm tail} r_\ell
\qquad(r_\ell\ge R,\ n\le\eta_{\rm tail}r_\ell).
\tag{32.12}
$$

**证明：有界尺度的基准方程。** 考察 $H=2C,\ \rho=\nu=0$ 的极限方程 $\mathsf P=\mathsf Q=e=0$，允许 $|\operatorname{Im}_\iota\ell|\ge1$，含等号边界。由 $\mathsf Q=0$ 得 $v=-\iota\ell C^{-1}p$；$\mathsf P=0$ 给 $U=2\iota C^{-1}p$。再用 $U$ 的定义、$B=3C$ 以及 (32.7)，得到

$$
q=(\ell I_2+2C^{-1})p+3\iota C^2u,\qquad
a=(2C-\ell C^2/2)u=\iota(I_2-\ell C^{-1})p.
$$

此处 $I_2-\ell C^{-1}$ 可逆。于是逐坐标

$$
p_j=-\iota A_j u_j,\qquad
A_1=\frac{2-\ell/2}{1-\ell}=\frac12+\frac{3}{2(1-\ell)},\qquad A_2=4.
\tag{32.13}
$$

若两坐标均非零，实际探针恒满足 $c_l p_j-q_j=(c_l-c_j)X_{jj}u_j$，其中 $l\ne j$。实对角元 $X_{jj}$ 要求 $(c_l p_j-q_j)/u_j$ 为实数。将 $q_j,p_j$ 的上式代入，利用 $c_l=2/c_j$，恰得 $\operatorname{Re}(\ell A_j)=3c_j^2$。第二坐标强制 $\operatorname{Re}\ell=3$；写 $\ell=3+\iota t_0$，则 $\operatorname{Re}(\ell A_1)=-3/(4+t_0^2)$，与第一坐标所需的 $3$ 矛盾。

在第二轴，(32.13) 使 $u^*p=-4\iota$，违背 Hermitian 条件。在第一轴，$q=p$，故 $(\ell+1)A_1=3$，即 $\ell^2-9\ell+2=0$。两根均为实数，与 $|\operatorname{Im}_\iota\ell|\ge1$ 矛盾。

**证明：有界尺度的一致正下界。** 对 (32.12) 固定的 $R$，存在 $\eta_{\rm comp},\delta_H,\delta_\rho,c_{\rm comp}>0$，使

$$
S_0\ge c_{\rm comp}\qquad
(r_\ell\le R,\ n\le\eta_{\rm comp}r_\ell,\
\|H-2C\|\le\delta_H,\ |\rho|\le\delta_\rho).
\tag{32.14}
$$

否则令四个候选正常数都趋于零，取对应反例序列，则 $H\to2C,\ \rho\to0,\ n/r_\ell\to0,\ S_0\to0$。因 $r_\ell\le R$，有 $\nu\to0$。取子列固定 $\sigma,\epsilon$，使单位 $u$ 和有界 $\ell$ 收敛；(32.6) 给极限 $|\operatorname{Im}_\iota\ell|\ge1$。式 (32.8) 给 $\mathsf P,\mathsf Q,e\to0$；(32.7) 给 $a\to(2C-\ell C^2/2)u$，其中右侧取极限值。由 $\kappa\to0$，(32.9) 中 $Z$ 趋于可逆的 $\ell I_2-C$，故 $p$ 有界；(32.5) 的 $\mathsf P$ 等式在 $\ell$ 远离零时控制 $U$，继而 $U$ 的定义控制 $q$。取收敛子列后，极限满足前述基准方程。

非轴极限上，两条实对角元条件按 $(c_l p_j-q_j)/u_j\in\mathbb R$ 直接取极限，故已被排除。轴向极限上，(32.13) 和基准 $q$ 公式都把极限的 $p,q$ 留在同一轴上。原 Hermitian 探针的两个连续条件 $u^*p\in\mathbb R$ 与 $u^*q=p^*Cu$ 在极限保持；在第 $j$ 轴，它们给 $p=x_0u,\ q=c_jp$，其中 $x_0\in\mathbb R$。这正是上面排除两轴所用的条件。整个论证只对可见的 $p,q$ 取极限，未假设 $X$ 有界；未被读到的对角元可以发散。也未要求 $\alpha_\delta$ 在极限仍为正。矛盾证明 (32.14)。

**证明：统一半径与原全正泛函。** 取 $\eta=\min(\eta_{\rm tail},\eta_{\rm comp})>0$，并把 $\delta_H,\delta_\rho$ 缩到不超过 $1$。在 $n\le\eta r_\ell$ 时有 $b_\theta\le(1+\eta)^2 r_\ell$，故 (32.12) 在 $r_\ell\ge R$ 控制 $b_\theta$，(32.14) 在 $r_\ell\le R$ 以 $b_\theta\le(1+\eta)^2R$ 控制它。余下 $n>\eta r_\ell$ 时，直接由 (32.7) 中的方差，及 $A\le r_\ell$、$\|FCu\|=\|C^2u\|\ge1$，得到

$$
S_0\ \ge\ \frac{n^2}{2r_\ell}
  \ \ge\ \frac{\eta^2}{2(1+\eta)^2}\,b_\theta.
$$

三域给出同一常数 $\gamma>0$，例如取 $c_{\rm tail}/(1+\eta)^2$、$c_{\rm comp}/((1+\eta)^2R)$ 和 $\eta^2/(2(1+\eta)^2)$ 的最小值。在整个原索引域有 $S_0\ge\gamma b_\theta$。选 $0<\rho_*\le\delta_\rho$，使 $K(\rho_*+\rho_*^2)\le\gamma/4$。于是在 $\|H-2C\|\le\delta_H,\ |\rho|<\rho_*$ 下，(32.10) 给

$$
\mathcal D_\rho\ge \frac{S_0}{4}\ge\frac{\gamma b_\theta}{4}>0.
\tag{32.15}
$$

这些常数对两个取向和两个绝对值符号共同有效。参数范围由 (32.6) 完整保留，既没有限制两 $\alpha_\delta$ 的比值，也没有排除一项趋零或 $\beta_\delta$ 无界的序列。

对每个固定的同一 $X,\xi$，将 (32.15) 对全部有限变分参数取下确界，按 (27.12)–(27.13) 得原向量 PB。一般向量若演员分量非零，提取其范数为共同尺度，并同比缩放环境分量，原预算两侧按同一因子变化。若演员分量为零，$\xi=(0,y)$ 给 $x\xi=h_{\rm PB}\xi=r\xi=s\xi=0$，其中 $h_{\rm PB}=K_\sigma(c,x)$。原 $L$ 的读数是 $-2\operatorname{Re}((Vy)^*\iota C Vy/2)=0$，故 PB 自动成立，包括零向量。最后用定理 17.2 的 (17.14)–(17.16) 将同一实际 $X$ 的向量 PB 提升到原全正泛函：谱和的两份预算各用原二阶 Gram 行列式根不等式，左端用三角不等式。谱和保留给定总质量，未将 $\phi$ 归一，也未丢弃环境密度块；零质量仅有零泛函。由 $\|H_h-2C\|=|h|$，半径 $\rho_*$ 可在同一 $h$ 邻域使用。

**证明：原 P2 的精确闭区间。** 对 $h>0$，(30.27)–(30.28) 的对应为

$$
\mathcal A=C^{-1/2}H_hC^{-1/2}=2I_2+\frac{h}{\sqrt2}J_A,\qquad
(\alpha,\beta)=(2,h/\sqrt2),\qquad
U_0=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

原残量参数就是 (30.29) 所用的 $\rho$。以 $M_2=I_2$ 代入 (30.29)，得

$$
Q_M=U_0^*\operatorname{diag}(1/2,1)U_0
=\begin{pmatrix}3/4&-1/4\\-1/4&3/4\end{pmatrix},
\qquad
\omega_{\rm P2}=1,\quad J=0,\quad R_{\rm P2}=3/4,\quad\Delta=1/2 .
$$

这里 $\omega_{\rm P2}$ 和 $R_{\rm P2}$ 分别是 (30.29) 的 $\omega$ 和 $R$，与上面的方差权重及尺度截断无关。于是 $I_+(B_h,M)=I_-(B_h,M)$，共同值正是 (32.2)。取 $h_*=\min(\delta_H,3\rho_*/(2\sqrt2))$。若 $0<h<h_*$，则 $\sqrt2\,h/3<\rho_*$，所以闭区间的每个点，包括两个端点，都满足 (32.15) 的全部原 PB 测试。在区间外，(30.29) 的必要性使原 P2 对每个取向都失败；正有限质量上的失败随原 P2 的二次齐次性保留。由此得到精确的 P2 与 PB 交及所述固定非零例。∎

本节的 `repo-derived` 结论是固定三矩 $(C^2,C,I_2)$ 的一致 PB 半径及其对整个原 P2 闭区间的覆盖。原 P2 区间直接复用 (30.29)，原正泛函、实／复 Gram 与行列式根的归属沿前卷 §§17、27 及其中所引运输卷 (9.28)–(9.30)。加权方差、Cauchy–Schwarz、Young 不等式及有限维紧性均按其通常形式使用。结论仅分类 (32.1) 在 $0<h<h_*$ 上的 P2 与 PB 之交；不确定该族的最大 PB 半径，也不分类任意 $W=0$ 输入或给出物理实现。

## 追加锚（本行以下为增补区）

## 33. 两矩近邻的一致反二阶矩 PB 半径与实单线极限

本节沿用 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A$、两个取向及原 P2、PB 标签。旧式号 (17.x)、(27.x)、(30.x)、(30A.x)、(31.x) 均指[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)。所有平方、Jordan 乘积及正泛函均取同一个完整原矩阵代数；实际探针仍遍取全部 $x=X\oplus0_m$、$X=X^\ast$。本节只取平衡残量 $s=\rho T_A\oplus0_m$，不增加原泛函的归一或环境密度限制。

### 33.1 任意有限环境维数上的共同半径

**定理 33.1（两矩近邻与统一反二阶矩尺度）。** 存在常数 $\delta_0,c>0$，与环境维数和 $L$ 无关，使下述断言成立。任取有限 $m\ge0$、实际 Hermitian 输入
$t=\left(\begin{smallmatrix}B&V\\V^\ast&D_{\rm env}\end{smallmatrix}\right)$，并令

$$
\begin{gathered}
W=V|_{\ker D_{\rm env}}=0,\qquad
F=V^\ast,\qquad G=D_{\rm env}^{\dagger}F,\\
M_0=F^\ast F,\qquad M_1=G^\ast F=F^\ast G,\qquad
M_2=G^\ast G,\qquad H=B-M_1.
\end{gathered}
\tag{33.1}
$$

若 $L\ge1$ 且

$$
\|H-2C\|<\delta_0,\qquad
\|M_1-C\|<\delta_0,\qquad
\|M_2\|\le L,
\tag{33.2}
$$

则同一输入对每个 $|\rho|\le c/L$ 同时满足两个取向的全部原 PB。这里包括每个实际 Hermitian 角探针和完整 $M_{m+2}(\mathbb C)$ 上全部正复线性泛函；在任一指定正有限质量上全称检验也成立，零质量给零等式。

不对 $M_0$ 另加接近性、正下界或上界假设。等价地，任意满足前卷 (30.3) 的兼容三矩，在取 $B=H+M_1$ 后，只要满足 (33.2)，其每份实际实现都有上述结论。兼容性不能删除：本定理不把任意三个形式矩阵当作实际来源。

证明。先在 $\|H-2C\|,\|M_1-C\|\le1$ 内取常数，随后缩小邻域。固定任意原单位演员 $u$、同一 $X=X^\ast$ 和环境向量 $y$；原索引中的 $\sigma,\epsilon=\pm1$、$0<\alpha_\pm<\infty$、$\beta_\pm\in\mathbb R$ 均任意。使用 §32 的 $\iota=\sigma i$、$\nu,\ell,A,w_\pm,\omega$、$\mathsf P,\mathsf Q$、$S_0,\mathcal D_\rho$，并置

$$
r_\ell=|\ell|,\qquad n_0=|\nu|,\qquad
b_\theta=\frac{(r_\ell+n_0)^2}{r_\ell},\qquad
\mathcal S=L S_0.
\tag{33.3}
$$

式 (32.6) 仍给
$|1+\operatorname{Im}_\iota\nu|<A=-\epsilon\operatorname{Im}_\iota\ell\le r_\ell$、
$r_\ell+n_0\ge1$，因而 $r_\ell>0$、$b_\theta\ge1$。没有限制 $\alpha_+/\alpha_-$，也没有对任何单个 $\alpha_\pm$ 取正下界。

在实际环境内令 $d=Fu+D_{\rm env}y$、
$a=Bu+Vy$、
$e=d+(\ell+\omega\nu)FCu/2$。由 $W=0$ 得 $a=Hu+G^\ast d$。因此 (32.4)–(32.5)、(32.9) 保持原式；(32.7) 的准确替换是

$$
\begin{aligned}
\sum_{\tau=\pm1}w_\tau
 \|(E_\tau)_{\rm env}\|^2
 &=(w_++w_-)\|e\|^2+\frac{n_0^2}{2A}\|FCu\|^2,\\
a&=Hu+G^\ast e-\frac{\ell+\omega\nu}{2}M_1Cu,\\
\mathcal D_\rho
 &=S_0+4\epsilon\rho\operatorname{Re}(v^\ast T_Au),
 \qquad v=a-\iota p,\quad p=Xu.
\end{aligned}
\tag{33.4}
$$

这里 $\tau$ 只标两笔原预算。第一行是同一对环境列的加权方差，第二行使用实际恒等式 $G^\ast F=M_1$；没有替换环境度量。

取 $\|M_1-C\|\le1/2$。因 $\|G\|^2\le L$，对任意演员向量 $z$ 有

$$
\|M_1z\|^2=\|G^\ast Fz\|^2\le L\|Fz\|^2,
\qquad
M_0\succeq L^{-1}M_1^2\succeq\frac1{4L}I_2.
\tag{33.5}
$$

特别地 $L\|FCu\|^2\ge1/4$。这就是所需的 $M_0$ 下界，其来源是实际因子而非额外假设。由 (33.4) 的方差及两份演员列的加权半和、半差，得到

$$
\begin{gathered}
\mathcal S\ge\frac{n_0^2}{8r_\ell},\\
\|\mathsf P\|+\|\mathsf Q\|+\|G^\ast e\|
 \le3\sqrt{r_\ell\mathcal S},\\
\|a\|\le K\bigl(1+r_\ell+n_0+\sqrt{r_\ell\mathcal S}\bigr).
\end{gathered}
\tag{33.6}
$$

例如 $\|\mathsf P\|,\|\mathsf Q\|\le\sqrt{AS_0/2}$、
$\|e\|\le\sqrt{AS_0/2}$，而
$\|G^\ast e\|\le\sqrt{L}\|e\|$；这说明 $K$ 不依赖 $m,L$ 或 $\|F\|$。

先证明存在共同的 $\eta_H,\eta_M,\eta_\rho,\gamma_0>0$，使

$$
\mathcal S\ge\gamma_0 b_\theta
\quad\text{当}\quad
\|H-2C\|<\eta_H,\quad
\|M_1-C\|<\eta_M,\quad |\rho|\le\eta_\rho,
\tag{33.7}
$$

对所有 $L\ge1$、所有实际环境及全部原索引成立。这里的强制性只在所列局部 $\rho$ 邻域断言。

若不存在这样的四个常数，就有一列实际输入和原测试，允许其环境维数及 $L$ 变化，使
$H\to2C$、$M_1\to C$、$\rho\to0$ 且
$\mathcal S/b_\theta\to0$。取子列固定 $\sigma,\epsilon$。由 (33.6)，

$$
\frac{\mathcal S}{b_\theta}
 \ge\frac{n_0^2}{8(r_\ell+n_0)^2}
\quad\Longrightarrow\quad
\frac{\nu}{\ell}\to0,\qquad
\liminf r_\ell\ge1,\qquad
\frac{\mathcal S}{r_\ell}\to0.
\tag{33.8}
$$

设 $\kappa=\nu/\ell$，
$Z=[\ell(1-\kappa^2)-\iota\kappa]I_2-C$。原消元式仍是

$$
\mathsf Q-\kappa\mathsf P
 =(\iota C-\kappa I_2)a-Zp+\rho T_Au.
\tag{33.9}
$$

若 $r_\ell\to\infty$，(33.6) 使
$\|\mathsf P\|+\|\mathsf Q\|+\|G^\ast e\|=o(r_\ell)$。
式 (33.4) 给
$a/\ell+C^2u/2\to0$；同时 $Z/\ell\to I_2$。将 (33.9) 除以 $\ell$ 并解出 $p$，得到

$$
p+\frac{\iota}{2}C^3u\longrightarrow0.
\tag{33.10}
$$

但 $u^\ast p=u^\ast Xu$ 必为实数，而
$u^\ast C^3u\ge1$，故 (33.10) 不可能。这一分支没有对发散探针取紧性极限。

若 $r_\ell$ 有界，则 (33.8) 给 $\nu\to0$、$\mathcal S\to0$；
$\mathsf P,\mathsf Q,G^\ast e\to0$。只对单位演员 $u$、有界 $\ell$ 取子列。极限满足
$|\operatorname{Im}_\iota\ell|\ge1$，故 $\ell I_2-C$ 可逆。(33.9) 控制可见列 $p$，再由
$\mathsf P=v-\nu p+\ell U/2$、
$U=\iota q+BCu+Cv$ 控制可见列 $q=XCu$。在极限中 $B\to3C$，恰得到 §32 已排除的基准接触系统：

$$
\begin{gathered}
a=(2C-\ell C^2/2)u=\iota(I_2-\ell C^{-1})p,\\
q=(\ell I_2+2C^{-1})p+3\iota C^2u,\qquad
p_j=-\iota A_j u_j,\\
A_1=\frac{2-\ell/2}{1-\ell}
 =\frac12+\frac{3}{2(1-\ell)},\qquad A_2=4.
\end{gathered}
\tag{33.11}
$$

为明确极限边界，若两个演员坐标均非零，实际 Hermitian 探针给
$(c_l p_j-q_j)/u_j\in\mathbb R$，其中 $c_1=1,c_2=2,l\ne j$。
代入 (33.11) 得
$\operatorname{Re}(\ell A_j)=3c_j^2$。
第二坐标迫使 $\operatorname{Re}\ell=3$；写 $\ell=3+\iota t_0$，第一坐标却给
$\operatorname{Re}(\ell A_1)=-3/(4+t_0^2)$，不能等于 $3$。
在第二演员轴，$u^\ast p=-4\iota$，也不可能。
在第一轴，可见极限列均在该轴，连续恒等式
$u^\ast p\in\mathbb R$、$u^\ast q=p^\ast Cu$ 给 $q=p$。
于是 $(\ell+1)A_1=3$，即 $\ell^2-9\ell+2=0$，其根均为实数，仍矛盾。
这些排除包括 $A=1$ 的极限；不要求极限的两个 $\alpha_\pm$ 仍严格正。整个紧性步骤只涉及演员空间的 $u,p,q,\ell$，不要求 $X$、$y$ 或环境空间有共同紧集。这证明 (33.7)。

最后控制残量项。至少一个 $j$ 满足
$|\ell(1-\kappa^2)-\iota\kappa-c_j|\ge1/2$。
在该坐标上使用 (33.9) 和 (33.6)，按 §32 的同一 Hermitian 实性关系得到

$$
\begin{aligned}
|\operatorname{Re}(v^\ast T_Au)|
 &\le K\bigl(b_\theta+\sqrt{b_\theta\mathcal S}+|\rho|\bigr),\\
\mathcal D_\rho
 &\ge\frac{S_0}{2}
       -K\bigl(|\rho|+L\rho^2\bigr)b_\theta.
\end{aligned}
\tag{33.12}
$$

具体地，$u^\ast p\in\mathbb R$ 使两个
$\operatorname{Im}_\iota(\overline{p_j}u_j)$ 互为相反数，故任选一个坐标都有
$|\operatorname{Re}(\iota p^\ast T_Au)|\le3|p_j||u_j|$。
只需控制上述分离坐标，即使另一坐标共振也无妨。
此外
$(1+n_0/r_\ell)(1+r_\ell+n_0)\le2b_\theta$、
$(1+n_0/r_\ell)\sqrt{r_\ell\mathcal S}=\sqrt{b_\theta\mathcal S}$。
第一行因而成立，包括 $u_j=0$。
第二行对 $4K|\rho|\sqrt{b_\theta L S_0}$ 使用 Young 不等式，并用 $L,b_\theta\ge1$ 吸收余项。

取 $\delta_0\le\min(1/2,\eta_H,\eta_M)$，再取
$0<c\le\eta_\rho$ 使 $K(c+c^2)\le\gamma_0/4$。
当 $|\rho|\le c/L$ 时，(33.7)、(33.12) 给

$$
\mathcal D_\rho
 \ge\frac{S_0}{2}-\frac{\gamma_0b_\theta}{4L}
 \ge\frac{S_0}{4}
 \ge\frac{\gamma_0b_\theta}{4L}>0.
\tag{33.13}
$$

所有常数对两个取向、两个绝对值符号及全部有限变分参数共同有效。对固定的同一 $X,\xi=(u,y)$，用 (27.12) 对四个参数取下确界，即得原向量 PB；退化 Gram 不要求下确界达到。一般非零演员分量按其范数同比缩放，演员分量为零时原 $L$ 的读取为零，PB 自动成立。

对完整原代数上的任意正泛函，取原空间谱分解
$\phi=\sum_j\phi_{\xi_j}$，分别对同一 $R_+,S_+$ 和同一 $R_-,S_-$ 使用 (17.15) 的二阶正 Gram 行列式根不等式，再对左端使用三角不等式，正好得到 (17.16)。这一步保留环境密度块及给定总质量；零质量只有零泛函。证明完成。∎

### 33.2 正定环境中的上阶见证

**命题 33.2（PB 单独的反二阶矩阶最优性）。** 定理 33.1 的共同保证尺度在 $L\to\infty$ 时不能统一改成比 $L^{-1}$ 更大的阶。更准确地，对每个 $L>64/7$，有一份三维环境上的实际完整 $M_5(\mathbb C)$ 输入，且 $D_{\rm env}\succ0$，满足
$H=2C$、$M_1=C$、$W=0$、$\|M_2\|=L$，却在 $\rho=4/L$ 严格违反原 PB。两个取向分别都有同一实际探针上的见证；每份见证的两笔原预算均严格正，并可取得任一指定正有限质量。

证明。在固定两维演员和三维环境上，记 $e_1,e_2$ 为演员标准基，取

$$
\begin{gathered}
D_{\rm env}=\operatorname{diag}(1,2,L^{-2}),\qquad B=3C,\\
V=\left[\sqrt{\frac{L}{L+1}}\,e_1,\ 2e_2,\ \frac{1}{L\sqrt{L+1}}\,e_1\right].
\end{gathered}
\tag{33.14}
$$

环境正定，故 $W=0$。由 $F=V^\ast$、$G=D_{\rm env}^{-1}F$，

$$
M_1=\operatorname{diag}\left(\frac{L}{L+1}+\frac1{L+1},2\right)=C,\qquad
M_2=\operatorname{diag}\left(\frac{L}{L+1}+\frac{L^2}{L+1},1\right)
     =\operatorname{diag}(L,1),\qquad
H=B-M_1=2C.
\tag{33.15}
$$

先取 $\sigma=1$、$\iota=i$、$\epsilon=1$，并取

$$
\begin{gathered}
u=e_1,\qquad X=\operatorname{diag}(3/2,0),\qquad
p=q=\tfrac32e_1,\\
\nu=0,\qquad \ell=-1-2i,\qquad
(\alpha_+,\alpha_-)=(1,3),\qquad
(\beta_+,\beta_-)=(-1,1),\\
a_{\rm act}=(-3+3i)e_1,\qquad
v=(-3+\tfrac32i)e_1,\qquad U=3i e_1.
\end{gathered}
\tag{33.16}
$$

这些参数满足原 (32.6)，且
$\zeta_\tau=i+\tau\ell=\beta_\tau-\tau i\alpha_\tau$。
令

$$
\begin{gathered}
d_0=a_{\rm act}-Hu+\ell M_1Cu/2=(-11/2+2i)e_1,\\
e=GM_2^{-1}d_0,\qquad
G^\ast e=d_0,\qquad \|e\|^2=\frac{137}{4L},\\
y=D_{\rm env}^{-1}\bigl(e-\ell FCu/2-Fu\bigr),\qquad
\xi=(u,y).
\end{gathered}
\tag{33.17}
$$

所有量均有限；此 $X,\xi$ 不依赖 $\rho$。
由 $d=Fu+D_{\rm env}y=e-\ell FCu/2$ 得
$Bu+Vy=Hu+G^\ast d=a_{\rm act}$，故 (33.16) 的演员列由这同一个实际向量精确实现，而不是另行指定的自由列。

逐项代入 (32.5)，有

$$
\mathsf P=v+\ell U/2=0,\qquad
\mathsf Q=iCv-\ell p+\rho T_Au=\rho e_1,\qquad
(E_\tau)_{\rm env}=e.
\tag{33.18}
$$

因而同一实际二次型在全部实 $\rho$ 上恰为

$$
\boxed{\quad
\mathcal D_\rho
 =\frac43\rho^2-12\rho+\frac{137}{3L}.
\quad}
\tag{33.19}
$$

这里 $S_0=(1+1/3)(\rho^2+\|e\|^2)$，
$\operatorname{Re}(v^\ast T_Au)=-3$，故一次项的符号由原 (32.4) 确定。在 $\rho=4/L$，

$$
\mathcal D_{4/L}=\frac{64-7L}{3L^2}<0.
\tag{33.20}
$$

原两笔预算的变分上界之和已经小于
$2\phi_\xi(L)$；由 (27.12)，对参数取下确界只会进一步减小这个上界。因此这是原 PB 的严格违反。

还可直接验证两笔预算严格正。$FCu$ 与 $e$ 分别平行于 $Fe_1$ 与 $Ge_1$，两者的第一、第三环境分量均非零；乘 $D_{\rm env}^{-1}$ 将第三分量与第一分量的比值放大 $L^2$。因此这两个环境列复线性无关。对每个 $\tau$，
$(R_\tau\xi)_{\rm env}=-\tau FCu/2$，
$(S_\tau\xi-\zeta_\tau R_\tau\xi)_{\rm env}=e$；
所以 $R_\tau\xi,S_\tau\xi$ 复线性无关。复 Gram 行列式严格正，其实 Gram 行列式不小于它，故
$B_{\phi_\xi}(R_\tau,S_\tau)>0$。
所有输入和 $X$ 均为实矩阵，对作用列及 $y$ 取复共轭便给 $\sigma=-1$ 的同样见证。最后把 $\phi_\xi$ 乘以 $\mu/\|\xi\|^2$，即可取得任意指定 $\mu>0$，严格违反和两笔严格正预算均保留。∎

当 $L\to\infty$，(33.14) 的原矩阵趋于 (32.1) 在 $h=0$ 添一条未耦合零模的输入。此时 $M_0\to C^2$，而 $H,M_1$ 在整条路径上精确固定。它说明的是整个所列近邻类的 PB 单独共同半径具有 $L^{-1}$ 阶，不确定最优常数。这里 $C^{-1/2}HC^{-1/2}=2I_2$，原 P2 已迫使 $\rho=0$；故 (33.20) 不是 P2 与 PB 联合分类的锐性见证。

### 33.3 同一五维载体上的实单线族

**定义 33.3（实单线正则化）。** 在同一完整 $M_5(\mathbb C)$、分块 $\mathbb C^2\oplus\mathbb C^2\oplus\mathbb C$ 上，取

$$
\begin{gathered}
n=\frac1{\sqrt2}(1,1)^{\mathsf T},\qquad
a=C^{1/2}n=(1/\sqrt2,1)^{\mathsf T},\qquad \|a\|^2=3/2,\\
H_h=2C+hJ_A,\qquad h,\gamma\in\mathbb R,\quad\delta>0,\quad
\lambda=\gamma/\delta,\\
D_{\rm env}=C\oplus\delta,\qquad
V=[C,\gamma a],\qquad
B=3C+hJ_A+\frac{\gamma^2}{\delta}aa^\ast,\\
t_{h,\gamma,\delta}=
\begin{pmatrix}
3C+hJ_A+\gamma^2aa^\ast/\delta&C&\gamma a\\
C&C&0\\
\gamma a^\ast&0&\delta
\end{pmatrix},\qquad
t_h^0=
\begin{pmatrix}
3C+hJ_A&C&0\\
C&C&0\\
0&0&0
\end{pmatrix}.
\end{gathered}
\tag{33.21}
$$

原 $c,P,s$ 分别是 $C\oplus0_3$、$I_2\oplus0_3$、$\rho T_A\oplus0_3$。环境可逆，故 $W=0$，实际矩为

$$
\begin{gathered}
M_0=C^2+\gamma^2aa^\ast,\qquad
M_1=C+\frac{\gamma^2}{\delta}aa^\ast
   =C+\delta\lambda^2aa^\ast,\\
M_2=I_2+\lambda^2aa^\ast,\qquad H=H_h,\qquad
L_\lambda:=\|M_2\|=1+\frac32\lambda^2.
\end{gathered}
\tag{33.22}
$$

**定理 33.4（精确 P2 区间与共同 PB 覆盖条件）。** 对定义 33.3 的每个实 $h,\gamma$ 和每个 $\delta>0$，两个取向各自的原全正 P2 区间均为

$$
I_\lambda(h)=[-r_\lambda(h),r_\lambda(h)],\qquad
r_\lambda(h)=
\frac{\sqrt2\,|h|}{3\sqrt{1+2\lambda^2/3}}.
\tag{33.23}
$$

令 $\mathcal J_\sigma(h,\gamma,\delta)$ 为该同一输入在取向 $\sigma$ 下满足原 P2 与全部原 PB 的实 $\rho$ 集合。若

$$
|h|<\delta_0,\qquad \frac32\delta\lambda^2<\delta_0,
\tag{33.24}
$$

则对每个 $\sigma$ 有

$$
\left[-\min\left(r_\lambda(h),\frac{c}{L_\lambda}\right),
       \min\left(r_\lambda(h),\frac{c}{L_\lambda}\right)\right]
\subseteq\mathcal J_\sigma(h,\gamma,\delta)
\subseteq I_\lambda(h).
\tag{33.25}
$$

特别地，若另外满足

$$
|h|\le
\frac{3c}{\sqrt2}\,
\frac{\sqrt{1+2\lambda^2/3}}{1+3\lambda^2/2},
\tag{33.26}
$$

则 $\mathcal J_+=\mathcal J_-=I_\lambda(h)$，两个取向的联合允许集也等于此闭区间，包括两端点。这里的全正泛函量词可分别限制到任一指定正有限质量；零质量仍是零等式。

证明。先直接消费 (30.29) 的原 P2 判据。对 $h>0$，
$\mathcal A=2I_2+(h/\sqrt2)J_A$ 的有序谱基为 §32 的 $U_0$，第一列恰为 $n$。由 (33.22)，

$$
\begin{aligned}
U_0^\ast C^{-1/2}(I_2+M_2)C^{-1/2}U_0
 &=\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix},\\
Q_M&=\frac1{d_\lambda}
 \begin{pmatrix}3/2&-1/2\\-1/2&3/2+\lambda^2\end{pmatrix},
 \qquad d_\lambda=2+\frac32\lambda^2,\\
\Delta&=\frac1{d_\lambda},\qquad
R=\frac{\sqrt{(3/2)(3/2+\lambda^2)}}{d_\lambda},\qquad
J=0,\qquad \beta=\frac{h}{\sqrt2}.
\end{aligned}
\tag{33.27}
$$

因此 $\beta\Delta/R$ 正是 (33.23)。
当 $h<0$，交换两个谱列不改变 $R,\Delta$，仍有 $J=0$，只把 $\beta$ 改为 $|h|/\sqrt2$。
当 $h=0$，归一化 Schur 矩阵为标量，(30.27)–(30.28) 直接给 $\rho=0$，也与 (33.23) 相符。这里保留原 P2 的必要性、充分性及闭端点，没有以 PB 估计替代它。

另一方面，
$\|H_h-2C\|=|h|$、
$\|M_1-C\|=3\delta\lambda^2/2$。
定理 33.1 于是保证 $|\rho|\le c/L_\lambda$ 的全部原 PB，给出 (33.25) 左包含；右包含仅用 P2。式 (33.26) 准确等价于
$r_\lambda(h)\le c/L_\lambda$，故此时两包含合成所述等式。∎

对任意固定有限 $\Lambda\ge0$，可取

$$
\delta_\Lambda=\frac{\delta_0}{3(1+\Lambda^2)},\qquad
h_\Lambda=
\min\left\{\frac{\delta_0}{2},
 \frac{3c}{2\sqrt2(1+3\Lambda^2/2)}\right\}.
\tag{33.28}
$$

于是所有 $|\lambda|\le\Lambda$、
$0<\delta<\delta_\Lambda$、
$|h|<h_\Lambda$ 的原输入都有
$\mathcal J_+=\mathcal J_-=I_\lambda(h)$。
这是同一有界比率族的共同覆盖，不随某个探针或泛函改选输入。

式 (33.26) 还给出无界比率可用的双重缩放条件。事实上

$$
\frac{L_\lambda}{\sqrt{1+2\lambda^2/3}}
 \le\frac32\sqrt{\frac32}(1+|\lambda|).
\tag{33.29}
$$

因此可固定
$c'=\min\{\delta_0/2,c\}>0$；
只要 $0<|h|\le c'/(1+|\lambda|)$ 以及
$3\delta\lambda^2/2<\delta_0$，就有 (33.24)、(33.26)，整个 P2 闭区间均被 PB 覆盖。这个充分条件允许 $|\lambda|\to\infty$，但同时要求 $h$ 缩小；它不确定固定非零 $h$、无界比率时的精确有限阶段联合半径。

### 33.4 原源距离、不同有界比率极限与无界比率挤压

**推论 33.5（同一源极限上的不同联合区间）。** 定义 33.3 的原源距离精确为

$$
\begin{gathered}
t_{h,\gamma,\delta}-t_h^0
 =\delta
 \begin{bmatrix}\lambda a\\0_2\\1\end{bmatrix}
 \begin{bmatrix}\lambda a\\0_2\\1\end{bmatrix}^{\!\ast},\\
\boxed{\quad
\|t_{h,\gamma,\delta}-t_h^0\|
 =\delta\left(1+\frac32\lambda^2\right)
 =\delta+\frac{3\gamma^2}{2\delta}.
\quad}
\end{gathered}
\tag{33.30}
$$

任取两个有限实数 $\lambda_1,\lambda_2$，满足
$|\lambda_1|\ne|\lambda_2|$。取
$\Lambda\ge\max(|\lambda_1|,|\lambda_2|)$，
并固定任一 $0<|h|<h_\Lambda$。
沿 $\gamma=\lambda_j\delta$、$\delta\downarrow0$ 的两条路径，原输入均趋于同一个 $t_h^0$，
$M_0\to C^2$、$M_1\to C$，但两个取向的联合允许集分别等于不同的非退化闭区间
$I_{\lambda_j}(h)$。其相对种子半径为

$$
\frac{r_{\lambda_j}(h)}{r_0(h)}
 =\left(1+\frac23\lambda_j^2\right)^{-1/2}.
\tag{33.31}
$$

更一般地，在同一个有界比率范围内，若 $\lambda\to\lambda_\ast$、$\delta\to0$，则联合区间趋于 $I_{\lambda_\ast}(h)$。

证明。式 (33.30) 是同一个实际矩阵差的秩一展开；因 $\delta>0$，其算子范数等于 $\delta$ 乘该列的平方范数。矩的极限由 (33.22) 得到，联合区间由 (33.28) 得到。式 (33.31) 由 (33.23) 相除；固定非零 $h$ 时，它随 $|\lambda_j|$ 严格减小，故两个绝对比率不同就给不同区间。对收敛有界比率使用同一个共同覆盖及半径公式的连续性即得最后断言。∎

上述路径中，$M_2$ 的路径极限是
$I_2+\lambda_\ast^2aa^\ast$，而极限原输入 $t_h^0$ 自身按谱伪逆计算的第二矩是 $I_2$。因此原源与第一矩收敛并不推出第二矩收敛到极限源的第二矩。仅在定义 33.3 这一单线族内，额外标量记录

$$
n^\ast C^{-1/2}(M_2-I_2)C^{-1/2}n=\lambda^2
\tag{33.32}
$$

对固定的 $h$，已经足以通过 (33.23) 确定 P2 半径。在满足 (33.24) 和 (33.26) 的覆盖条件时，该半径也是联合半径；满足 (33.28) 的有界比率路径已经具备这些条件。这不声称该标量恢复任意来源的 $M_2$，也不声称它是一般输入的最小记录。

现固定非零 $h$，取任意满足

$$
\delta_k\downarrow0,\qquad
|\lambda_k|=|\gamma_k|/\delta_k\to\infty,\qquad
\gamma_k^2/\delta_k\to0
\tag{33.33}
$$

的实单线路径。例如 $\gamma_k=\delta_k^{3/4}$ 满足这些条件。式 (33.30) 仍使原源趋于 $t_h^0$，第一矩仍趋于 $C$。无须假设这一范围的全部 PB 已有精确分类，就有

$$
0\in\mathcal J_\sigma(h,\gamma_k,\delta_k)
 \subseteq I_{\lambda_k}(h),\qquad
\sup_{\rho\in\mathcal J_\sigma(h,\gamma_k,\delta_k)}|\rho|
 \le r_{\lambda_k}(h)\longrightarrow0.
\tag{33.34}
$$

第一项使用标准零残量的 P2 与全部 PB，第二项只使用精确 P2 必要性。因此两个取向的联合允许集及其交都被挤向 $\{0\}$。这里没有断言每个有限 $k$ 的联合集等于 P2 区间，也没有由这个挤压结论分类 PB 单独的允许集。若同时让 $h_k$ 满足 (33.29) 后的双重缩放条件，则定理 33.4 才进一步给每个满足邻域条件的有限阶段的精确联合区间。

### 33.5 真正零模连线的比较

**命题 33.6（同一实方向上的非零零模比较）。** 在同一 $M_5(\mathbb C)$ 上另取

$$
\widehat t_{h,\gamma}=
\begin{pmatrix}
3C+hJ_A&C&\gamma a\\
C&C&0\\
\gamma a^\ast&0&0
\end{pmatrix},
\qquad h\in\mathbb R,\quad\gamma\in\mathbb R\setminus\{0\}.
\tag{33.35}
$$

则 $W\ne0$，两个取向各自的全正 P2 区间恰为

$$
\widehat I_+=\widehat I_-=
[-|\gamma|/\sqrt6,\ |\gamma|/\sqrt6],
\tag{33.36}
$$

但全部原 PB 在任一取向都当且仅当 $\rho=0$。
每个非零 $\rho$ 的 PB 失败均可在任意指定正有限质量上取得同一原泛函下的两笔严格正预算见证。

证明。此时
$D_{\rm env}=C\oplus0$、
$V=[C,\gamma a]$、
$H=2C+hJ_A$，零模连线的归一化演员方向是平衡方向 $n$。
在 (13.5) 取 $e=(1,-1)^{\mathsf T}/\sqrt2$；因 $e,n$ 都是
$C^{-1/2}HC^{-1/2}$ 的特征向量，其交叉元 $b=0$。
按 (13.6) 的原空间两行，第一行的平方范数为
$2e^\ast C^{-1}e=3/2$，第二行的平方范数为 $\gamma^{-2}$，两行正交。故该处的矩阵为

$$
GG^\ast=\operatorname{diag}(3/2,\gamma^{-2}),\qquad
Q=\operatorname{diag}(2/3,\gamma^2),\qquad
R=|\gamma|\sqrt{2/3},\qquad
\Delta=2\gamma^2/3,\qquad J=0.
\tag{33.37}
$$

这里 $G$ 仅指 (13.6) 的两行矩阵，不是 (33.1) 的矩因子。
代入 (13.9) 得 (33.36)，包括闭端点。PB 的单独刚性及正预算见证直接由定理 30A.2 给出，不以 P2 为前件。∎

当 $\gamma\to0$，$\widehat t_{h,\gamma}\to t_h^0$。所以同一个原源极限附近，真正的非零零模连线具有非退化 P2 区间，却在所有非零 $\rho$ 上被全部 PB 排除；正则化单线的有界比率路径则在所列小 $h$ 条件下具有非退化联合区间。两者属于不同的实际环境分支，不能用删除零模连线的伪逆操作互相替代。

### 33.6 数学来源与准确范围

原 PB 的同一向量变分恒等式与完整正泛函提升分别复用前卷 (27.12)–(27.13)、(17.14)–(17.16)；兼容三矩和实际实现沿定理 30.1，原加权环境补偿沿 (31.9)–(31.13)。本节使用 §32 的原列代数及基准接触排除，将其扩展为 (33.7) 的维数无关缩放下界，再得到 (33.13)。加权方差、Cauchy–Schwarz、Young 不等式、有限维谱分解和可见演员列的紧性均为成熟工具。原 P2 分类直接沿 (30.29) 和定理 13.1；零模 PB 比较直接沿定理 30A.2。

有限矩阵的秩变化与 Moore–Penrose 逆连续性的背景可参见 J. J. Koliha，[*Continuity and differentiability of the Moore–Penrose inverse in C*-algebras*](https://journals.msp.org/mscand/article/download/885/884/916)，Corollary 1.8，p. 157。该文在这里仅承担常秩与伪逆连续性的背景归属；PB 下界、同一实际五维正定环境见证和本节各条区间极限由上列推导承担。谱伪逆和广义 Schur 工具的归属仍沿前卷所引 Penrose 与 Higham，不把这些成熟工具计作新增结果，也不作外部文献穷尽或历史优先权主张。

本节的仓内综合结论是：无单独 $M_0$ 假设的共同反二阶矩 PB 半径及其 PB 单独阶最优性，和该半径对实单线族精确 P2 区间的覆盖与源极限比较。它们是有限矩阵的纸面数学陈述，不承载 Lean／kernel 认证。这里没有一般 $W=0$ 联合分类、每份输入的最大 PB 半径、最优半径常数、更高演员秩分类或物理实现结论；前卷保留的未知总响应、完整 $\mathsf H$ 和原实际来源义务维持原范围。

## 追加锚（本行以下为增补区）

## 34. 固定非零 Schur 耦合下，全部原 PB 缩小正定环境的原 P2 允许范围

沿用 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，以及[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)的原 P2、原 PB 与有限变分记号。设 $n=(1,1)^{\mathsf T}/\sqrt2$、$a=C^{1/2}n=(1,\sqrt2)^{\mathsf T}/\sqrt2$、$\beta=h/\sqrt2$。下文在同一个完整 $M_5(\mathbb C)$ 上工作：演员为 $\mathbb C^2$，环境为 $\mathbb C^2\oplus\mathbb C$，原探针是 $x=X\oplus0_3$，其中 $X=X^*$；原输出为 $g_\sigma=\sigma i[c,t_\lambda]/2+s$，其中 $c=C\oplus0_3$、$s=\rho T_A\oplus0_3$。

**命题 34.1（固定 $h$ 的两种尺度）。** 对每个固定的充分小的 $h>0$，存在下文给出的实际输入族，参数为 $\lambda\to+\infty$，满足 $D_{\rm env}\succ0$、$W=0$、$M_1=C$、$H=2C+hJ_A$。写 $L_\lambda=\|M_2\|$，则 $L_\lambda=\tfrac32\lambda^2+O(1)$。两个取向的原 P2 允许区间均为 $[-R_\lambda,R_\lambda]$，其中 $R_\lambda\sim\beta\sqrt{2/3}/\lambda\sim\beta/\sqrt{L_\lambda}$。存在常数 $K_*>0$，使充分大的 $\lambda$ 上，每个 $K_*/\lambda^2\le|\rho|\le R_\lambda$ 都在两个取向分别有严格违反原 PB 的有限见证，每份见证的两笔原预算均严格正。

再取 $h$ 落在定理 33.1 的邻域内，应用其一致反二阶矩下界，则存在 $c'>0$，使充分大的 $\lambda$ 上，两个取向各自的原 P2 与全部原 PB 的联合允许集，以及要求两个取向同时成立的联合允许集 $\mathcal J_\lambda$，均满足同样的双包含。对 $\mathcal J_\lambda$，即
$$
[-c'/\lambda^2,c'/\lambda^2]\ \subseteq\ \mathcal J_\lambda\
\subseteq\ [-K_*/\lambda^2,K_*/\lambda^2].
\tag{34.1}
$$
故在上述 $h$ 范围内，联合允许范围的内外尺度均为 $L_\lambda^{-1}$。

### 34.1 基准演员接触

先固定取向 $\iota=i$，绝对值符号 $\epsilon=1$，并取 $\nu=0$、$\ell=b-it_*$，其中 $b\in\mathbb R$、$t_*=\sqrt6$。这样 $\zeta_\tau=i+\tau\ell=\beta_\tau-\tau i\alpha_\tau$，其中 $\tau=\pm1$，$\beta_\tau=\tau b$、$\alpha_\tau=t_*-\tau>0$。记 $B=3C+hJ_A$、$H=2C+hJ_A$、$p=Xu$、$q=XCu$，以 $a_{\rm act}$ 表示待实现的演员作用列，令 $v=a_{\rm act}-ip$、$U=iq+BCu+Cv$。

为看清接触条件，在实际输入上写 $d=Fu+D_{\rm env}y$、$\xi=(u,y)$、$a_{\rm act}=Bu+Vy$，其中 $F=V^*$。前卷 (27.4)–(27.5) 的原列 $R_\tau\xi$ 的两块为 $p-\tau U/2$、$-\tau FCu/2$；$S_\tau\xi$ 的两块为 $a_{\rm act}+\tau[(Cp+q+iCa_{\rm act}-iBCu)/2+\rho T_Au]$、$d-\tau iFCu/2$。减去 $\zeta_\tau R_\tau\xi$ 后，演员常项为 $a_{\rm act}-ip+\ell U/2$，演员的 $\tau$ 项为 $iCv-\ell p+\rho T_Au$，环境项中的 $\tau iFCu/2$ 抵消。因此 §32 的原缺陷写成
$$
\begin{aligned}
E_\tau&=S_\tau\xi-\zeta_\tau R_\tau\xi
       =(\mathsf P+\tau\mathsf Q,\ d+\ell FCu/2),\\
\mathsf P&=v+\ell U/2,\qquad
\mathsf Q=iCv-\ell p+\rho T_Au .
\end{aligned}
\tag{34.2}
$$
在 $\rho=0$，先由 $\mathsf Q=0$ 解出 $v$，再由 $\mathsf P=0$ 得 $U=-2v/\ell=2iC^{-1}p$，故接触条件等价于
$$
v=-i\ell C^{-1}p,\qquad
a_{\rm act}=i(I_2-\ell C^{-1})p,\qquad
q=(\ell I_2+2C^{-1})p+iBCu .
\tag{34.3}
$$

为使两列由同一个 Hermitian $X$ 产生，取
$$
u=\frac{(\sqrt r,e^{i\theta})^{\mathsf T}}{\sqrt{1+r}},\qquad
r>0,\qquad p_j=z_j u_j,\qquad z_1\in\mathbb R,\ z_2\in\mathbb C .
$$
因 $c_1=1,c_2=2$，从 $p=Xu$、$q=XCu$ 逐行消去非对角元得到
$$
x_{11}=(2p_1-q_1)/u_1,\qquad x_{22}=(q_2-p_2)/u_2 .
$$
这两列可由一个 Hermitian $X$ 实现，当且仅当 $x_{11},x_{22}$ 都为实数，且
$$
r(z_1-x_{11})=\overline{z_2-x_{22}}.
\tag{34.4}
$$
确实，取 $X_{12}=(z_1-x_{11})u_1/u_2$，取 $X_{21}=\overline{X_{12}}$，再代入第二行 $p$ 即得 (34.4)；对角定义随后给回 $q$ 的两行。

在 $h=0$，(34.3) 给 $x_{11}=-\ell z_1-3i$、$x_{22}=\ell z_2+12i$。写 $z_2=B_2+iD_2'$。对角虚部条件是 $t_*z_1-3=0$、$bD_2'-t_*B_2+12=0$。施加这两式后，(34.4) 的虚部给 $D_2'=0$，实部给 $r(1+b)z_1=(1-b)B_2$。故在 $0<b<1$ 上，四个 Hermitian 条件给出
$$
z_j=\frac{3c_j^2}{t_*},\qquad r=\frac{4(1-b)}{1+b}.
\tag{34.5}
$$

接着令 $d_0=a_{\rm act}-Hu+\ell C^2u/2$，要求 $d_0$ 与 $a$ 共线。写 $D_j=(d_0)_j/u_j$；在基准 $h=0$，由 (34.3)、(34.5) 和 $t_*^2=6$ 得
$$
D_j=-5c_j+\frac{b c_j^2}{2}-i\frac{3b c_j}{t_*}.
\tag{34.6}
$$
两实部在 $0<b<1$ 上均严格为负。条件 $(d_0)_2=\sqrt2(d_0)_1$ 的模长方程为 $|D_2|^2=2r|D_1|^2$。由 (34.6)，
$$
\begin{aligned}
|D_1|^2&=25-5b+\tfrac74 b^2,\qquad |D_2|^2=100-40b+10b^2,\\
f(b)&=(1+b)|D_2|^2-8(1-b)|D_1|^2
     =-100+300b-84b^2+24b^3 .
\end{aligned}
\tag{34.7}
$$
$f(0)=-100$、$f(1)=140$，且 $f'(b)=300-168b+72b^2>0$ 于 $[0,1]$，故唯一根 $b_0$ 在 $(0,1)$。在此根取相位 $\theta_0$，使 $e^{i\theta_0}D_2/(\sqrt r D_1)=\sqrt2$。此时 $d_0=\eta a$，其中 $\eta=\sqrt2(d_0)_1\ne0$。又由 (34.3) 得 $\operatorname{Re}(v_j/u_j)=-3c_j$，从而
$$
\zeta:=\operatorname{Re}(v^*T_Au)=\frac{3(4-r)}{1+r}>0 ,
\tag{34.8}
$$
因为 (34.5) 在 $b_0$ 处给 $0<r<4$。这里 $\zeta$ 是实配对，与变分系数 $\zeta_\tau$ 分开。

### 34.2 用实隐函数定理延续到固定非零 $h$

在基准解附近，对实变量 $(z_1,\operatorname{Re}z_2,\operatorname{Im}z_2,r,b,\theta)$，保留两条对角虚部方程、(34.4) 的实部与虚部，以及 $(d_0)_2-\sqrt2(d_0)_1=0$ 的两个实分量。所有方程在 $r>0$ 的局部坐标中光滑；最后一对也可写成 $(d_0)_2/(d_0)_1-\sqrt2=0$，因为基准解的 $(d_0)_1\ne0$。固定 $(b,\theta)$，基准的前四式按 (34.5) 的顺序消元：取对角虚部、左边减右边的非对角虚部与实部，主元依次为 $t_*,-t_*,1,(1+b_0)z_1$，均非零。

消去这四个变量后，在 $h=0$，最后一对方程的复读数为 $Z-\sqrt2$，其中 $Z=e^{i\theta}D_2/(\sqrt r D_1)$。沿消元所得的解，
$$
|Z|^2-2=\frac{f(b)}{(1+b)r|D_1|^2}.
$$
在根处，对 $b$ 的导数非零，所以 $\partial_b Z$ 有非零径向分量；而 $\partial_\theta Z=i\sqrt2$ 是非零切向分量。这给出可逆的剩余实 $2\times2$ 雅可比块，从而全六维实雅可比可逆。有限维实隐函数定理遂给出每个充分小 $h$ 的局部解。用 (34.4) 的构造恢复实际 $X=X^*$，由 (34.3) 得对应作用列。缩小 $h$ 的邻域后，$r>0$、$\eta\ne0$ 和 $\zeta>0$ 由连续性保留。下文固定其中任一 $h>0$；这些演员数据不随 $\lambda$ 或 $\rho$ 变化。

### 34.3 固定 $H,M_1$ 的实际正定环境

对 $\lambda>1$，取
$$
\begin{gathered}
\delta_\lambda=\lambda^{-3},\qquad
P_\lambda=C-\delta_\lambda\lambda^2aa^*,\qquad
D_{\rm env}=C\oplus\delta_\lambda,\\
F=\begin{bmatrix}C^{1/2}P_\lambda^{1/2}\\ \delta_\lambda\lambda a^*\end{bmatrix},
\qquad
V=F^*,\qquad
t_\lambda=\begin{pmatrix}3C+hJ_A&V\\ F&D_{\rm env}\end{pmatrix}.
\end{gathered}
\tag{34.9}
$$
$C^{-1/2}P_\lambda C^{-1/2}=I_2-\lambda^{-1}nn^*\succ0$，所以正平方根存在，且 $F$ 的首块可逆。各输入块为实矩阵；$D_{\rm env}\succ0$ 给 $W=0$。取 $G=D_{\rm env}^{-1}F$，其首块为 $C^{-1/2}P_\lambda^{1/2}$、末行为 $\lambda a^*$。逐块相乘得到
$$
\begin{aligned}
M_1&=G^*F=P_\lambda+\delta_\lambda\lambda^2aa^*=C,\qquad
H=B-M_1=2C+hJ_A,\\
M_2&=G^*G=P_\lambda^{1/2}C^{-1}P_\lambda^{1/2}+\lambda^2aa^* .
\end{aligned}
\tag{34.10}
$$
随 $\lambda\to+\infty$，$P_\lambda\to C$，由正平方根的连续性，$M_2$ 的第一项趋于 $I_2$。由算子范数的三角不等式与反向三角不等式，$L_\lambda=\lambda^2\|a\|^2+O(1)=\tfrac32\lambda^2+O(1)$。同时 $F$ 的首块趋于 $C$，末行趋于零，$D_{\rm env}\to C\oplus0$，所以 $t_\lambda$ 在范数中趋于同一固定 $h$ 的 §32 输入添一条不耦合零模所得的矩阵。这个输入极限不要求探针向量的环境分量有界。

### 34.4 原 P2 的精确读取

$C^{-1/2}HC^{-1/2}=2I_2+(h/\sqrt2)J_A$。取 $n_-=(1,-1)^{\mathsf T}/\sqrt2$，则 $U_0=[n,n_-]$ 按 $2+\beta,2-\beta$ 排列归一化 Schur 矩阵的特征值。前卷 (30.29) 的 $\omega=1$。令 $K=Q_M^{-1}$；由 $C^{-1/2}a=n$，
$$
K=K_{\rm base}+\lambda^2 e_1e_1^*,\qquad
K_{\rm base}\longrightarrow U_0^*\operatorname{diag}(2,1)U_0
 =\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix},
\tag{34.11}
$$
其中 $e_1=(1,0)^{\mathsf T}$ 是谱坐标中的首轴。$K$ 为实正定矩阵，故 (30.29) 的 $J=0$；又 $d_1=K_{22}/\det K$、$d_2=K_{11}/\det K$、$\Delta=1/\det K$。因此两个取向的精确原 P2 半径相同：
$$
R_\lambda=\frac{\beta}{\sqrt{K_{11}K_{22}}}
 \ \sim\ \frac{\beta\sqrt{2/3}}{\lambda}.
\tag{34.12}
$$

### 34.5 同一实际输入上的两侧原 PB 见证

在 (34.9) 的环境中，使用延续后的 $u,X,\ell,\eta$，取
$$
e=(0,0,\eta/\lambda)^{\mathsf T},\qquad
y=D_{\rm env}^{-1}(e-\ell FCu/2-Fu),\qquad \xi=(u,y).
\tag{34.13}
$$
由 $G$ 的末行，$G^*e=\eta a=d_0$。同一实际向量给出 $d=Fu+D_{\rm env}y=e-\ell FCu/2$，于是
$$
Bu+Vy=Hu+G^*d=Hu+d_0-\ell C^2u/2=a_{\rm act}.
$$
这里用到 $G^*D_{\rm env}=V$、$G^*F=C$。因此演员接触与两条环境缺陷在同一个 $x=X\oplus0_3$、$\xi$ 上实现。由 (34.2)–(34.3)，$\mathsf P=0$、$\mathsf Q=\rho T_Au$，两条环境缺陷都为 $e$。对每个有限 $\lambda$，(34.13) 的向量有限。

写 $\phi_\xi(A)=\xi^*A\xi$，将原 PB 左侧的算子暂记为 $L_{\rm PB}$，以区别于 $L_\lambda$。式 (32.3)–(32.4) 的带符号有限代价，是两笔 (27.12) 的所选变分值之和减去 $2\epsilon\phi_\xi(L_{\rm PB})$。展开 $E_\tau$ 的平方时，虚交叉项按 §32 的原换位恒等式消去零残量部分；加入 $s$ 后，剩余改变量为 $4\epsilon\rho\operatorname{Re}(v^*T_Au)$。这里该恒等式只用原作用列，对 (34.9) 仍适用。设 $N=\|T_Au\|^2$、$w=(t_*-1)^{-1}+(t_*+1)^{-1}=2t_* /(t_*^2-1)$，则当前 $\iota=i,\epsilon=1$ 的有限代价恰为
$$
\mathcal D_\rho=w\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)+4\rho\zeta .
\tag{34.14}
$$
这组选取用于 $\rho<0$。对于 $\rho>0$，保持 $\iota=i$ 和同一份实输入及同一个 $\rho$，改取 $(u,\ell,X,\epsilon)=(\overline u,\overline\ell,-\overline X,-1)$，其中右侧为前一组数据。此时 $p,q$ 变为 $-\overline p,-\overline q$，由 (34.3)，$v,a_{\rm act},d_0$ 变为各自的共轭，(34.13) 的 $e,y$ 也随之共轭。新的 $\alpha_\tau=t_*+\tau$ 交换两个正权，$\beta_\tau$ 不变；$\zeta,N,|\eta|$ 都不变。故对正、负两侧分别使用所选见证，统一得到
$$
\mathcal D_\rho=w\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)-4\zeta|\rho|.
\tag{34.15}
$$
另一取向 $\iota=-i$ 由对每侧的全部原列取复共轭得到，同时将 $\iota,\ell$ 共轭，保留该侧的 $\epsilon,\alpha_\tau,\beta_\tau$；原输入和 $\rho$ 为实，范数及实配对不变，故仍为 (34.15)。

由 (34.12)，充分大的 $\lambda$ 满足 $wN R_\lambda\le2\zeta$。取 $K_*=1+w|\eta|^2/(2\zeta)$；在 $K_*/\lambda^2\le|\rho|\le R_\lambda$ 时，
$$
\mathcal D_\rho\le \frac{w|\eta|^2}{\lambda^2}-2\zeta|\rho|
 \le -\frac{2\zeta}{\lambda^2}<0.
\tag{34.16}
$$
按前卷 (27.12)–(27.13)，每笔原预算根的两倍至多为所选的有限变分值。因此 (34.16) 给同一实际 $x,\phi_\xi$ 的严格原 PB 违反，无需让变分参数取极限。

两笔原预算均严格正：对每个 $\tau$，$(R_\tau\xi)_{\rm env}=-\tau FCu/2$，而 $(E_\tau)_{\rm env}=e$。$FCu$ 的首两坐标非零（作为一个二元列），因为 $C^{1/2}P_\lambda^{1/2}$ 可逆且 $Cu\ne0$；$e$ 的首两坐标为零、末坐标非零，因为 $\eta$ 在基准和延续后都非零。故这两条环境列复线性无关，进而 $R_\tau\xi$ 与 $S_\tau\xi=E_\tau+\zeta_\tau R_\tau\xi$ 复线性无关。原预算是这两条原像的实 Gram 行列式，因而严格正。取共轭或更换上述符号时，同一论证成立。向量 $\xi$ 的演员分量为单位向量，故将同一泛函乘以 $\mu/\|\xi\|^2$ 即可取得任一指定正有限质量 $\mu$；严格违反与预算正性均保留。

### 34.6 条件下界与结论范围

两侧排除已经由 (34.16) 给出，区间外则由原 P2 排除。对于内含界，应用定理 33.1：在 $\|H-2C\|,\|M_1-C\|<\delta_0$、$W=0$ 且 $\|M_2\|\le L$、$L\ge1$ 时，$|\rho|\le c/L$ 保证同一输入在两个取向满足全部原 PB。这里 $\|H-2C\|=h$、$M_1=C$、$W=0$；固定 $0<h<\delta_0$ 并取 $L=L_\lambda$，充分大的 $\lambda$ 有 $1\le L_\lambda\le2\lambda^2$。于是可取 $c'=\min(c/2,K_*/2)>0$，得到 $|\rho|\le c'/\lambda^2$ 的全部原 PB；由 (34.12)，这些点最终严格在两个原 P2 区间之内。这就给出 (34.1)，含原下界所覆盖的全部正有限质量及零质量。

本节按通常形式使用实隐函数定理、正平方根的连续性及实 Gram 行列式的变分公式；原列和原 P2 读取分别沿 §32 与前卷 (30.29)，零模与伪逆连续性的背景沿 §33 已列归属。这里给出的是该正定族的两侧排除与依赖 §33.1 的阶数比较，不判定联合允许集的形状或最优常数。

## 追加锚（本行以下为增补区）

## 35. 固定零阶矩的正定环境、临界相位与全部原预算的共同尺度

本节及 §36 固定 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A$ 和 $U_0=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。旧式号 (17.x)、(27.x)、(30.x)、(31.x) 指[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)。§32 与前卷的引用取共同钉版 `315e167044afd2593b851f6546a82470ca16d446`；§34 的演员接触是本卷纸面前提。以下反二阶矩 PB 下界只使用 §32，不使用 §33.1 的两矩近邻定理。各节陈述均属纸面推导，不构成 Lean／kernel 认证。

### 35.1 原全称条件与固定零阶矩实现

**定义 35.1（同一实际来源上的允许集）。** 在演员为 $\mathbb C^2$、环境为 $\mathbb C^m$ 的完整原代数上，令

$$
\begin{gathered}
t=\begin{pmatrix}B&V\\V^*&D\end{pmatrix}=t^*,\qquad
c=C\oplus0_m,\qquad s_\rho=\rho T_A\oplus0_m,\qquad
x=X\oplus0_m,\quad X=X^*,\\
A\circ B=(AB+BA)/2,\qquad K_\sigma(A,B)=\sigma i[A,B]/2,\qquad
g_{\sigma,\rho}=K_\sigma(c,t)+s_\rho,\\
h_x=K_\sigma(c,x),\quad k=c\circ t,\quad r=c\circ x,\qquad
R_\tau=x+\tau(h_x-k),\quad S_\tau=t+\tau(r+g_{\sigma,\rho}),\quad\tau=\pm1,\\
L_{\rm PB}=-2x\circ(h_x-k)-2t\circ(r+g_{\sigma,\rho}),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{35.1}
$$

这里 $D=D_{\rm env}$。沿前卷的三矩记号，$F=V^*$、$G=D^\dagger F$、$M_0=F^*F$、$M_1=G^*F$、$M_2=G^*G$、$H=B-M_1$、$W=V|_{\ker D}$，其中 $D^\dagger$ 是 Hermitian 矩阵的谱 Moore–Penrose 逆。符号 $h_x$ 不表示 Schur 扰动参数 $h$。原 P2 是对完整代数的每个正复线性泛函 $\phi$ 都有

$$
\phi(g_{\sigma,\rho})^2\le
\phi(c^2)\phi(t^2)-\phi(c\circ t)^2;
\tag{35.2}
$$

原全部 PB 是对每个这样的 $\phi$ 及每个实际 Hermitian $X$ 都有

$$
|\phi(L_{\rm PB})|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{35.3}
$$

分别以 $I_\sigma(t)$、$\mathcal B_\sigma(t)$ 记满足原 P2、全部原 PB 的实参数 $\rho$ 集，定义

$$
\mathcal J_\sigma(t)=I_\sigma(t)\cap\mathcal B_\sigma(t),\qquad
\mathcal J_{\rm both}(t)=\mathcal J_+(t)\cap\mathcal J_-(t).
\tag{35.4}
$$

所有乘积、平方、原像和泛函都属于同一个完整原代数。固定任意正有限质量 $\mu$ 而量化全部 $\phi(I)=\mu$，得到相同允许集；这是前卷 (17.14)–(17.16) 及正齐次性的应用。若只取质量零，则只有零泛函，(35.2)–(35.3) 都是零等式，不能单独定义上述非平凡允许集。

**命题 35.2（固定 $M_0$ 的实际正定实现）。** 给定 $a\in\mathbb C^2\setminus\{0\}$、$\lambda>0$ 和实 $h$，在同一个完整 $M_5(\mathbb C)$ 中取

$$
\begin{gathered}
\delta=\lambda^{-3},\qquad F=\begin{bmatrix}C\\0\end{bmatrix},\qquad V=F^*,\qquad
D=\begin{pmatrix}
C+\delta\lambda^2aa^*&-\delta\lambda a\\
-\delta\lambda a^*&\delta
\end{pmatrix},\\
B=3C+hJ_A,\qquad
t_{h,\lambda,a}=\begin{pmatrix}B&V\\F&D\end{pmatrix},\qquad
G=\begin{bmatrix}I_2\\\lambda a^*\end{bmatrix}.
\end{gathered}
\tag{35.5}
$$

则 $D\succ0$、$DG=F$，并且

$$
\boxed{\quad W=0,\quad M_0=F^*F=C^2,\quad
M_1=G^*F=C,\quad M_2=G^*G=I_2+\lambda^2aa^*,\quad
H=B-M_1=2C+hJ_A.\quad}
\tag{35.6}
$$

若 $|h|<2\sqrt2$，则整个 $t_{h,\lambda,a}\succ0$。设 $t_h^0$ 为 §32 的 $t_h$ 添一条不耦合零模，在环境排序 $\mathbb C^2\oplus\mathbb C$ 下与 (35.5) 比较，则

$$
\|t_{h,\lambda,a}-t_h^0\|=\frac{\|a\|^2}{\lambda}+\lambda^{-3},\qquad
\|t_{h,\lambda,a}-t_0^0\|
=\max\left(|h|,\frac{\|a\|^2}{\lambda}+\lambda^{-3}\right).
\tag{35.7}
$$

证明。对 $D$ 的右下正标量 $\delta$ 作 Schur 补，所得恰为 $C\succ0$，不要求 $\lambda>1$。直接块乘法给 $DG=(C,0)^{\mathsf T}=F$，继而给出全部矩恒等式。对整个 $t$ 作 $D$ 的 Schur 补得到 $H$；它的首主子式为 $2$，行列式为 $8-h^2$，故在所列范围内正定。环境差准确为

$$
D-(C\oplus0)=\delta
\begin{bmatrix}\lambda a\\-1\end{bmatrix}
\begin{bmatrix}\lambda a\\-1\end{bmatrix}^{\!*}.
$$

它是秩一正矩阵，范数为 $\delta(\lambda^2\|a\|^2+1)$。$B,F$ 在同一 $h$ 下不变，给第一式；相对 $h=0$ 的差由演员上的 $hJ_A$ 与该环境差正交直和，给第二式。∎

### 35.2 不共轭环境的同源取向反射

**引理 35.3（同一实际来源上的精确反射）。** 对任一固定实际 $t$ 及 (35.1) 的残量族，

$$
I_-(t)=-I_+(t),\qquad
\mathcal B_-(t)=-\mathcal B_+(t),\qquad
\mathcal J_-(t)=-\mathcal J_+(t).
\tag{35.8}
$$

此结论保留同一个环境、同一个完整正泛函和同一个原向量，不要求 $t$ 为实矩阵。

证明。在同一个 $t$ 上作 $(\sigma,\rho,X)\mapsto(-\sigma,-\rho,-X)$，则 $g'=-g$、$h'_x=h_x$、$k'=k$、$r'=-r$。于是作为完整原算子有

$$
R'_\tau=-R_{-\tau},\qquad S'_\tau=S_{-\tau},\qquad
L'_{\rm PB}=-L_{\rm PB}.
\tag{35.9}
$$

两笔实 Gram 预算交换，左端绝对值不变；$X\mapsto-X$ 是全部 Hermitian 探针的双射，故全部 PB 等价。P2 中仅 $g$ 变号，故亦等价。

为核对后文有限见证，令 $\iota=\sigma i$，采用 (32.3) 的 $\zeta_\tau=\iota+\nu+\tau\ell=\beta_\tau-\tau\epsilon\iota\alpha_\tau$。同步取

$$
(\iota,\epsilon,\rho,X,\nu,\ell)
\mapsto(-\iota,-\epsilon,-\rho,-X,-\nu,\ell),\qquad
\alpha'_\tau=\alpha_{-\tau}>0,\quad\beta'_\tau=-\beta_{-\tau}.
\tag{35.10}
$$

则 $\zeta'_\tau=-\zeta_{-\tau}$，故 $E'_\tau=E_{-\tau}$。在同一 $\xi=(u,y)$ 上，$a_{\rm act}=Bu+Vy$ 不变，$p'= -p$、$q'=-q$，而 $v=a_{\rm act}-\iota p$、$U=\iota q+BCu+Cv$ 均不变。有限带符号代价亦完全不变。这是对原算子对称性的复用；它比较的是不同取向下的 $\rho$ 与 $-\rho$，不把同一个非零 $\rho$ 的两个取向混为一谈。∎

### 35.3 精确 $M_1=C$ 下独立于 §33 的 PB 运输

**定理 35.4（保留全部原探针的 $c_{\rm PB}/L$ 下界）。** 存在 $h_0,c_{\rm PB}>0$，使每份有限实际 $W=0$ 输入，只要

$$
M_1=C,\qquad H=2C+hJ_A,\qquad |h|<h_0,\qquad
\|M_2\|\le L,\quad L\ge1,
\tag{35.11}
$$

就在每个 $|\rho|\le c_{\rm PB}/L$ 满足两个取向的全部原 PB。结论不要求 $M_0$ 的额外界，也不要求 $D$ 可逆；在 (35.5) 中当然适用。

证明。以 $G=D^\dagger F$ 记实际环境映射；$W=0$ 保证 $DG=F$、$G^*D=V$。固定任意原 $X=X^*$、单位演员 $u$、任意环境向量 $y$、两个符号和全部有限参数 $\alpha_\tau>0,\beta_\tau\in\mathbb R$。不优化或更换这份实际测试。令

$$
\begin{gathered}
p=Xu,\quad q=XCu,\quad a_{\rm act}=Bu+Vy,\quad v=a_{\rm act}-\iota p,\quad
d=Fu+Dy,\quad U=\iota q+BCu+Cv,\\
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\\
\chi_\tau=\alpha_\tau^{-1},\quad s_\alpha=\chi_++\chi_-,\quad
\omega_\chi=(\chi_+-\chi_-)/s_\alpha,\quad
\bar b=(\ell+\omega_\chi\nu)/2,\quad e=d+\bar b FCu,\\
\kappa=\frac{|\nu|^2\chi_+\chi_-}{s_\alpha}\ge0,\qquad
A_{\rm act}=\sum_{\tau=\pm1}\chi_\tau\|\mathsf P+\tau\mathsf Q\|^2.
\end{gathered}
\tag{35.12}
$$

注意 $\bar b$ 只是加权复系数的名称，不表示取共轭。由 (32.5)、(31.9)–(31.10) 的原列与加权方差，实际缺陷平方和及配对准确为

$$
S=A_{\rm act}+s_\alpha\|e\|^2+\kappa\|FCu\|^2,\qquad
\mathcal D_\rho=S+4\epsilon\rho R,\quad
R=\operatorname{Re}(v^*T_Au),\quad
a_{\rm act}=Hu+G^*e-\bar b C^2u.
\tag{35.13}
$$

在 §32 的基准环境 $F_b=C,G_b=I_2,D_b=C$ 中，取同一 $B,H,X,u,\rho$ 及全部变分参数，仅定义用于比较的

$$
e_b=G^*e,\qquad d_b=e_b-\bar b C^2u,\qquad
y_b=C^{-1}(d_b-Cu).
\tag{35.14}
$$

则 $Bu+Cy_b=Hu+d_b=a_{\rm act}$。所以演员原列、$\mathsf P,\mathsf Q$ 和 $R$ 完全相同。该基准测试的平方和为

$$
S_b=A_{\rm act}+s_\alpha\|G^*e\|^2+\kappa\|C^2u\|^2\le LS.
\tag{35.15}
$$

最后一步只用三条逐项不等式：$A_{\rm act}\le LA_{\rm act}$、$\|G^*e\|^2\le L\|e\|^2$，以及
$\|C^2u\|^2=\|G^*FCu\|^2\le L\|FCu\|^2$，其中 $\|G\|^2=\|M_2\|\le L$。这不是为不同预算各选一个最优环境：同一个 $e_b,y_b$ 同时比较两条原缺陷。

现明确使用 §32 的常数范围。在其 (32.9)–(32.14) 及 (32.15) 前的统一下界中，存在 $\gamma,K_0,h_0,r_0>0$，可取 $r_0\le1$，使对每个基准测试和 $|h|<h_0,|\rho|\le r_0$ 有

$$
S_b\ge\gamma b_\vartheta,\qquad
|R|\le K_0\bigl(b_\vartheta+\sqrt{b_\vartheta S_b}+|\rho|\bigr),\qquad
b_\vartheta=\frac{(|\ell|+|\nu|)^2}{|\ell|}\ge1.
\tag{35.16}
$$

这里参数合法性正是 (32.6)，$|\ell|>0$；$\vartheta$ 是原变分索引，不是下文外部相位。§32 的大尺度、紧域和方差三域下界对两个取向、两个绝对值符号以及全部有限参数共同成立；配对界是在 (32.10) 之前取得。取闭的较小 $r_0$ 即可保留上述端点。由 $|\rho|\le1\le b_\vartheta$，

$$
|R|\le A_0S_b\le A_0LS,\qquad
A_0=K_0\left(\frac2\gamma+\frac1{\sqrt\gamma}\right),\qquad
c_{\rm PB}=\min\left(r_0,\frac1{8A_0}\right)>0.
\tag{35.17}
$$

于是 $|\rho|\le c_{\rm PB}/L$ 时原有限代价满足

$$
\mathcal D_\rho\ge(1-4A_0L|\rho|)S\ge S/2\ge0.
\tag{35.18}
$$

对固定的同一个实际 $X,\xi$，在全部有限变分参数上取 (27.12) 的下确界，即得原向量 PB，包括下确界不取到的退化 Gram。演员分量非单位时同比缩放整个向量；演员分量为零时，$x\xi=h_x\xi=r\xi=s_\rho\xi=0$，且 $\phi_\xi(L_{\rm PB})=-2\operatorname{Re}((Vy)^*\iota CVy/2)=0$，所以 PB 自动成立。

最后，任意完整原代数正泛函都有 (17.14) 的谱和 $\phi=\sum_j\phi_{\xi_j}$。把 (17.15) 分别用于原两笔实 Gram，结合 $|\sum_j\phi_{\xi_j}(L_{\rm PB})|\le\sum_j|\phi_{\xi_j}(L_{\rm PB})|$，正是 (17.16) 的全正泛函提升。所有环境密度块、全部原 $X$ 和同一实际 $t$ 均保留，任意给定正有限总质量不变，零泛函亦满足零等式。∎

### 35.4 精确临界相位与两个分别取向的 P2 边界

**定理 35.5（固定 $M_0$ 相位族的精确 P2）。** 在 (35.5) 中令

$$
\begin{gathered}
w_\theta=\frac1{\sqrt2}(1,i e^{i\theta})^{\mathsf T},\qquad
a_\theta=C^{1/2}U_0w_\theta
=\frac12(1+i e^{i\theta},\sqrt2(1-i e^{i\theta}))^{\mathsf T},\\
s(\theta)=\|a_\theta\|^2=\frac{3+\sin\theta}{2},\qquad
L_{\lambda,\theta}=\|M_2\|=1+s(\theta)\lambda^2,\qquad
0<h<2\sqrt2,\quad\beta=h/\sqrt2.
\end{gathered}
\tag{35.19}
$$

对每个实 $\theta$、每个 $\lambda>0$，有精确公式

$$
\begin{gathered}
K=Q_M^{-1}=K_0+\lambda^2w_\theta w_\theta^*,\qquad
K_0=\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix},\qquad
\det K=L_{\lambda,\theta}+1,\\
T=\sqrt{K_{11}K_{22}}=\frac32+\frac{\lambda^2}{2},\qquad
q=\operatorname{Im}K_{12}=-\frac{\lambda^2\cos\theta}{2},\\
d_{\rm w}=T+q=\frac32+\frac{\lambda^2(1-\cos\theta)}2,\qquad
d_{\rm s}=T-q=\frac32+\frac{\lambda^2(1+\cos\theta)}2,\\
\boxed{\quad I_+(t_{h,\lambda,a_\theta})=[-\beta/d_{\rm w},\beta/d_{\rm s}],\qquad
I_-(t_{h,\lambda,a_\theta})=[-\beta/d_{\rm s},\beta/d_{\rm w}].\quad}
\end{gathered}
\tag{35.20}
$$

其中下标 w、s 仅在 $\cos\theta\ge0$ 时分别表示宽侧、短侧。两个取向同时满足 P2 的集合总是

$$
I_+(t)\cap I_-(t)=\left[-\frac\beta{T+|q|},\frac\beta{T+|q|}\right].
\tag{35.21}
$$

固定 $h>0$，若 $\lambda\to\infty$、$\theta_\lambda\to0$ 且扩展实极限
$\lambda^2(1-\cos\theta_\lambda)\to\gamma\in[0,\infty]$ 存在，则分别取向的闭区间按 Hausdorff 距离收敛为

$$
I_+\longrightarrow[-A_\gamma,0],\qquad
I_-\longrightarrow[0,A_\gamma],\qquad
A_\gamma=\frac\beta{3/2+\gamma/2},\quad A_\infty=0.
\tag{35.22}
$$

所有 $A_\gamma\in[0,2\beta/3]$ 都能实现：有限 $\gamma$ 可取 $\theta_\lambda=\sqrt{2\gamma}/\lambda$，无穷 $\gamma$ 可取 $\theta_\lambda=\lambda^{-1/2}$。特别地 $\theta_\lambda=s_*/\lambda$ 给 $A_\gamma=\beta/(3/2+s_*^2/4)$。

证明。归一化 Schur 块为 $2I_2+\beta J_A$，有序谱基为上述实 $U_0$，(30.29) 中 $\omega=1$。由 (35.6)，直接得到
$K=U_0^*C^{-1/2}(2I_2+\lambda^2a_\theta a_\theta^*)C^{-1/2}U_0$，即 (35.20) 的第一式。其非对角元为 $1/2-\lambda^2(\sin\theta+i\cos\theta)/2$；展开二阶行列式得 $\det K=2+s(\theta)\lambda^2$。在 (30.29) 中 $R=T/\det K$、$\Delta=1/\det K$、$J=q/\det K$，于是得到两个精确闭区间及其交。正定性保证分母严格正；这里两分母也都直接不小于 $3/2$。

沿所列相位路径，$d_{\rm w}\to3/2+\gamma/2$，而 $d_{\rm s}\sim\lambda^2$，逐端点给出闭区间极限和实现路径。每个有限阶段的端点都包含在 P2 内；极限端点本身是否最终属于有限阶段的区间，不能由区间收敛自动推出。与此同时 (35.21) 的半径渐近于 $\beta/\lambda^2$，所以两个取向同时满足 P2 的集合已经趋于 $\{0\}$。∎

### 35.5 区分外部相位与演员相位的统一接触延续

**引理 35.6（复相位方向上的有限演员接触）。** 存在 $h_c,\theta_c,\zeta_{\min},\eta_{\min},\eta_{\max}>0$，其中可取 $h_c<2\sqrt2$、$\theta_c\le\pi/6$，以及关于 $(h,\theta)$ 光滑的有限演员数据
$u,X,p,q,a_{\rm act},v,\ell,\eta$，使在 $|h|\le h_c,|\theta|\le\theta_c$ 上

$$
\begin{gathered}
\|u\|=1,\quad u_1u_2\ne0,\quad X=X^*,\quad p=Xu,\quad q=XCu,\qquad
\ell=b-i\sqrt6,\quad b\in\mathbb R,\\
v=-i\ell C^{-1}p,\quad a_{\rm act}=i(I_2-\ell C^{-1})p,\quad
q=(\ell I_2+2C^{-1})p+iBCu,\quad B=3C+hJ_A,\\
d_0:=a_{\rm act}-Hu+\ell C^2u/2=\eta a_\theta,\qquad
\eta_{\min}\le|\eta|\le\eta_{\max},\qquad
\zeta:=\operatorname{Re}(v^*T_Au)\ge\zeta_{\min},\qquad
N:=\|T_Au\|^2\le4.
\end{gathered}
\tag{35.23}
$$

这些数据不依赖 $\lambda$ 或 $\rho$。它们满足原有限参数 $\nu=0$、$\iota=i$、$\epsilon=1$、$\alpha_\tau=\sqrt6-\tau>0$、$\beta_\tau=\tau b$ 下的演员接触 $\mathsf P=\mathsf Q|_{\rho=0}=0$。

证明。沿 §34.1–§34.2 的接触方程，但以 $\varphi$ 记演员相位，保留 $\theta$ 专指外部方向 $a_\theta$。写

$$
u=\frac{(\sqrt r,e^{i\varphi})^{\mathsf T}}{\sqrt{1+r}},\quad
p_j=z_ju_j,\quad z_1\in\mathbb R,\quad z_2\in\mathbb C,\quad r>0,
\tag{35.24}
$$

并由 (35.23) 的前三个接触等式定义 $v,a_{\rm act},q$。两列由同一 Hermitian $X$ 实现的充要条件仍为

$$
x_{11}=(2p_1-q_1)/u_1\in\mathbb R,\quad
x_{22}=(q_2-p_2)/u_2\in\mathbb R,\quad
r(z_1-x_{11})=\overline{z_2-x_{22}}.
\tag{35.25}
$$

这是四个实方程。满足时定义 $X_{12}=(z_1-x_{11})u_1/u_2$、$X_{21}=\overline{X_{12}}$，便同时恢复 $p=Xu,q=XCu$。

在 $h=0$ 时，这四式不依赖 $\varphi$。记 $t_*=\sqrt6$，先由第一条对角虚部得 $z_1=3/t_*$；施加两对角实条件后，非对角方程的虚部给 $\operatorname{Im}z_2=0$；第二条对角虚部给 $\operatorname{Re}z_2=12/t_*$；最后的实部给

$$
z_j=3c_j^2/t_*,\qquad r=4(1-b)/(1+b),\quad 0<b<1.
\tag{35.26}
$$

这些消元的非零系数分别可取 $t_*,1,-t_*,(1+b)z_1$，所以前四式对四变量 $(z_1,\operatorname{Im}z_2,\operatorname{Re}z_2,r)$ 的实雅可比可逆。

如 §34 的 (34.6)–(34.7)，在这条基准解上

$$
\begin{gathered}
D_j=(d_0)_j/u_j=-5c_j+bc_j^2/2-i\,3bc_j/t_*,\\
|D_1|^2=25-5b+7b^2/4,\qquad |D_2|^2=100-40b+10b^2,\\
f(b)=-100+300b-84b^2+24b^3.
\end{gathered}
\tag{35.27}
$$

$f(0)<0<f(1)$ 且 $f'(b)>0$ 于 $[0,1]$，故唯一 $b_0\in(0,1)$ 给 $|D_2|^2=2r|D_1|^2$。两 $D_j$ 的实部均为负，特别地 $D_1\ne0$。此处目标方向是

$$
k(\theta)=\frac{(a_\theta)_2}{(a_\theta)_1}
=\sqrt2\frac{1-i e^{i\theta}}{1+i e^{i\theta}},\qquad k(0)=-i\sqrt2.
\tag{35.28}
$$

分母在零附近非零。选演员相位 $\varphi_0$ 使
$Z=e^{i\varphi}D_2/(\sqrt rD_1)$ 在 $(b_0,\varphi_0)$ 等于 $-i\sqrt2$；相对于 §34 的实方向基准，只是将演员相位减去 $\pi/2$。这不改变前四式、$r$ 或配对
$\zeta=3(4-r)/(1+r)>0$。

将后两个实方程取为 $Z-k(\theta)=0$。沿前四式消元的基准解，有

$$
|Z|^2-2=\frac{f(b)}{(1+b)r|D_1|^2}.
\tag{35.29}
$$

在 $b_0$ 处其 $b$ 导数非零，故 $\partial_bZ$ 有非零径向分量；$\partial_\varphi Z=iZ$ 则是非零切向向量。剩余实 $2\times2$ 块可逆，与前四式组成的六维实雅可比因而可逆。对参数 $(h,\theta)$ 应用有限维实隐函数定理，得到全部接触数据。这里外部相位是参数，演员相位是待解变量，两者没有被设为相同。

取一个闭参数盒，严格位于上述存在邻域内；连续性及紧性给 $r>0$、$u_1u_2\ne0$、$\eta=(d_0)_1/(a_\theta)_1\ne0$ 和 $\zeta>0$ 的共同上下界。最后 $N\le\|T_A\|^2=4$。原参数合法性由 $\alpha_\tau=t_*-\tau>0$ 直接保证。∎

### 35.6 接回固定 $M_0$ 的同一有限原见证

**定理 35.7（宽侧尾部的严格原 PB 排除与两笔正预算）。** 缩小引理 35.6 的正 $h$ 邻域后，存在 $h_U>0$ 及常数 $K_{\rm tail}>0$，使每个固定 $0<h<h_U$、每个 $|\theta|\le\theta_c$、每个 $\lambda\ge2$ 上，(35.5) 的同一来源满足：凡

$$
\rho\in I_+(t),\qquad \rho<0,\qquad |\rho|\ge K_{\rm tail}/\lambda^2,
\tag{35.30}
$$

都有一个有限实际原探针和向量泛函严格违反取向 $+$ 的 PB，且两笔原预算均严格正。取向 $-$ 的对应排除是 $\rho>0$、$\rho\in I_-(t)$、$\rho\ge K_{\rm tail}/\lambda^2$。两取向的对应见证保留同一环境与同一向量，按引理 35.3 反射。

证明。使用引理 35.6 的数据，在固定 $M_0$ 的 (35.5) 中明确取

$$
e=(0,0,\eta/\lambda)^{\mathsf T},\qquad
y=D^{-1}(e-\ell FCu/2-Fu),\qquad \xi=(u,y).
\tag{35.31}
$$

这里 $F$ 的首块是 $C$、末行是零，$G$ 的首块是 $I_2$、末行是 $\lambda a_\theta^*$，所以

$$
G^*e=\eta a_\theta=d_0,\qquad
d=Fu+Dy=e-\ell FCu/2,\qquad
Bu+Vy=Hu+G^*d=a_{\rm act}.
\tag{35.32}
$$

最后一式用 $G^*F=C$，从而 $G^*FCu=C^2u$。这三式把演员接触与两份环境缺陷接到同一个实际 $X,\xi,t$；不需要 §34.3 的可变 $F$ 实现。每个有限 $\lambda$ 的 $D^{-1},y$ 都有限，不对其随 $\lambda$ 的范数作有界假设。

原 (32.5) 于是给 $E_\tau=(\tau\rho T_Au,e)$。由 (31.9) 或 (32.4) 的精确带符号恒等式，当前 $\iota=i,\epsilon=1$ 的所选有限变分代价准确为

$$
\mathcal D_\rho=w_\alpha\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)+4\rho\zeta,
\qquad w_\alpha=(\sqrt6-1)^{-1}+(\sqrt6+1)^{-1}=2\sqrt6/5.
\tag{35.33}
$$

因负侧 P2 总有 $|\rho|\le2\beta/3$，可选 $0<h_U\le h_c$ 使
$8w_\alpha(h_U/\sqrt2)/3\le2\zeta_{\min}$。于是每个所列 $h,\theta,\rho<0$ 都有 $w_\alpha N|\rho|\le2\zeta_{\min}\le2\zeta$。取

$$
K_{\rm tail}=1+\frac{w_\alpha\eta_{\max}^2}{2\zeta_{\min}}.
$$

则在 (35.30) 内

$$
\mathcal D_\rho\le
\frac{w_\alpha\eta_{\max}^2}{\lambda^2}-2\zeta_{\min}|\rho|
\le-\frac{2\zeta_{\min}}{\lambda^2}<0.
\tag{35.34}
$$

所选有限变分和不小于原两笔预算根之和的两倍，正是 (27.12)。因此 $\mathcal D_\rho<0$ 推出同一个 $x,\phi_\xi$ 的原 PB 严格失败，无需达到任何下确界。另一取向用 (35.10)，即 $\rho'=-\rho$、$X'=-X$、$\epsilon'=-1$，保持 $u,y,\ell$ 与复环境不变，代价仍为同一负数。

现在量化两笔原预算的严格正性。在本实现中

$$
(R_\tau\xi)_{\rm env}=-\tau(C^2u,0)^{\mathsf T}/2,\qquad
(E_\tau)_{\rm env}=e=(0,0,\eta/\lambda)^{\mathsf T}.
\tag{35.35}
$$

这两列正交且非零。$S_\tau\xi=E_\tau+\zeta_\tau R_\tau\xi$，故其环境复 Gram 行列式是 $\|C^2u\|^2|\eta|^2/(4\lambda^2)$。加入演员块使复 Gram 矩阵增加半正定矩阵，其二阶行列式不减；实 Gram 行列式又等于复 Gram 行列式加上内积虚部的平方。因此两个原预算逐一满足

$$
B_{\phi_\xi}(R_\tau,S_\tau)\ge
\frac{\|C^2u\|^2|\eta|^2}{4\lambda^2}>0,\qquad \tau=\pm1.
\tag{35.36}
$$

反射只交换两笔预算和一个列的符号，严格正性保留。由于 $\|u\|=1$，将同一 $\phi_\xi$ 乘以 $\mu/\|\xi\|^2$ 即得每个指定正有限质量 $\mu$，严格违反与两笔正预算一同保留。∎

### 35.7 联合允许集的共同尺度与奇异极限边界

**推论 35.8（无 §33 前提的双包含与分别取向比较）。** 固定
$0<h<\min(h_U,h_0,2\sqrt2)$，令 $\beta=h/\sqrt2$。对全部 $|\theta|\le\theta_c$、$\lambda\ge2$，记 $L=L_{\lambda,\theta}$，则存在仅依赖这些固定数据的正常数 $c_{\rm in}(h),K_{\rm out}(h)$，使

$$
\begin{gathered}
[-c_{\rm in}/L,c_{\rm in}/L]\subseteq\mathcal J_\sigma(t)
\subseteq[-K_{\rm out}/L,K_{\rm out}/L],\qquad\sigma=\pm1,\\
[-c_{\rm in}/L,c_{\rm in}/L]\subseteq\mathcal J_{\rm both}(t)
\subseteq[-K_{\rm out}/L,K_{\rm out}/L].
\end{gathered}
\tag{35.37}
$$

特别地，在定理 35.5 的每条临界相位路径上，两个分别取向的联合允许集及同时取向的联合允许集都按 Hausdorff 距离趋于 $\{0\}$。若 $\gamma<\infty$ 且 $0<r_*<A_\gamma$，则充分大的每个有限 $\lambda$ 上，同一实际来源的 $\rho=-r_*$ 属于 $I_+$ 却严格违反该取向 PB；$\rho=r_*$ 对取向 $-$ 有反射后的同一结论，每个违反的两笔原预算均严格正。

证明。由 $\theta_c\le\pi/6$、$\lambda\ge2$，有

$$
\lambda^2\le L\le2\lambda^2,\qquad
\frac\beta{d_{\rm s}}\ge\frac\beta{2\lambda^2}\ge\frac\beta{2L},\qquad
\frac\beta{d_{\rm s}}\le\frac{2\beta}{\lambda^2}.
\tag{35.38}
$$

取 $c_{\rm in}(h)=\min(c_{\rm PB},\beta/2)>0$，定理 35.4 及精确 P2 的短端点共同给内含界。定理 35.7 排除 $+$ 的宽负尾，P2 自身控制其短正尾；取向 $-$ 反射。因此

$$
\mathcal J_+(t)\subseteq[-K_{\rm tail}/\lambda^2,2\beta/\lambda^2],\qquad
\mathcal J_-(t)\subseteq[-2\beta/\lambda^2,K_{\rm tail}/\lambda^2].
\tag{35.39}
$$

可取 $K_{\rm out}(h)=2\max(K_{\rm tail},2\beta)$。这是集合包含，不宣称分别取向的集合是区间或已经找出其宽侧精确端点。

每个原 P2、PB 测试对 $\rho$ 的余量连续，故这些允许集是闭集；它们包含零，且由 (35.37) 有界，遂得上述 Hausdorff 极限。固定严格内点 $-r_*$ 的 P2 成员身份来自 (35.22)，而 $r_*\ge K_{\rm tail}/\lambda^2$ 最终成立，给原有限 PB 排除；反射给另一取向。∎

这里分别取向的比较是实质区别：当 $\gamma<\infty$ 时，各自 P2 保留非零的一侧极限，加入全部 PB 才使该联合集合趋于零。要求两个取向同时成立时，P2 的交本来就已按 $\lambda^{-2}$ 缩小，不能把这种收缩再计作 PB 的额外排除。$h\downarrow0$ 时不存在由本推导支持的、独立于 $h$ 的正常数 $c_{\rm in}$；短 P2 端点本身正比于 $\beta$。在 $h=0$，归一化 Schur 块为标量，前卷 (30.27)–(30.28) 直接迫使 $\rho=0$。

由 (35.7) 与 $1\le s(\theta)\le2$，所有相位路径的实际正定来源均趋于同一个 $t_h^0$。若再固定 $h$ 位于定理 32.2 的范围内，则奇异极限来源本身的两个联合允许集都是 $[-2\beta/3,2\beta/3]$。因此正定路径上联合集趋于零，并不等于极限来源的联合集。没有在原全称量词、变分下确界与奇异来源极限之间交换极限；反例见证始终在有限阶段取得，其环境向量范数可以发散。

### 35.8 可复用的必要接触检验

**命题 35.9（最小范数缺陷给出的有限必要条件）。** 对固定的 $h,a$，若已有一组与 $\lambda$ 无关的合法有限 $\nu=0$ 演员接触数据，使 $\|u\|=1$、$\mathsf P=\mathsf Q|_{\rho=0}=0$、$d_0=\eta a$、$\eta\ne0$，记 $\alpha_a=\|a\|^2$、$s_\alpha=\sum_\tau\alpha_\tau^{-1}$、$N=\|T_Au\|^2$、$\zeta=\operatorname{Re}((a_{\rm act}-\iota Xu)^*T_Au)$。则 (35.5) 的全部 PB 成立的必要条件，是对每组这样的接触都有

$$
s_\alpha\left(N\rho^2+\frac{|\eta|^2\alpha_a}{1+\lambda^2\alpha_a}\right)
+4\epsilon\rho\zeta\ge0.
\tag{35.40}
$$

若某一组使左端严格负，它给同一来源的有限原 PB 违反，且两笔原预算严格正。若沿 $\rho_\lambda=k/\lambda^2$ 全部 PB 最终成立，其中接触数据和 $k$ 固定，则必有

$$
s_\alpha|\eta|^2+4\epsilon k\zeta\ge0.
\tag{35.41}
$$

证明。复用 (31.12) 的实际最小范数缺陷，令

$$
e_{\min}=GM_2^{-1}d_0
=\frac\eta{1+\lambda^2\alpha_a}
\begin{bmatrix}a\\\lambda\alpha_a\end{bmatrix},\qquad
\|e_{\min}\|^2=\frac{|\eta|^2\alpha_a}{1+\lambda^2\alpha_a}.
\tag{35.42}
$$

取 $y=D^{-1}(e_{\min}-\ell FCu/2-Fu)$，仍由 $G^*e_{\min}=d_0$ 给 $Bu+Vy=a_{\rm act}$。两份演员缺陷是 $\tau\rho T_Au$，两环境缺陷都是 $e_{\min}$，故原有限代价正是 (35.40) 左端。它若负，即按 (27.12) 严格违反 PB。$e_{\min}$ 的末坐标为非零数 $\eta\lambda\alpha_a/(1+\lambda^2\alpha_a)$，而 $FCu=(C^2u,0)^{\mathsf T}$；故两条环境列复线性无关，两笔原实 Gram 预算严格正。将 (35.40) 乘以 $\lambda^2$ 取极限即得 (35.41)；若极限严格负，充分大的有限阶段已经失败。∎

本必要检验不保证某个指定方向一定存在接触，也不把全部已测接触代价非负提升成全部 PB 的充分条件。尤其不能由此宣称两个同谱来源在共同 P2 内有相反 PB 结果。

## 36. 同谱正定来源的精确双取向联合区间与相位不可识别性

本节继续用 (35.5) 的固定 $M_0=C^2$ 实现。只有 $D$ 随相位与谱匹配参数变化；演员块 $B=3C+hJ_A$、耦合 $F=(C,0)^{\mathsf T}$ 与 Schur 块 $H$ 始终相同。以下有限阶段结论仅需定理 35.4 和精确 P2，不依赖接触引理的相位邻域大小。

### 36.1 同一全二阶谱下的非共轭相位对

**定理 36.1（精确而严格嵌套的双取向联合区间）。** 固定一次

$$
0<h<\min(h_0,2\sqrt2,c_{\rm PB}/\sqrt2),\qquad\beta=h/\sqrt2,
\tag{36.1}
$$

其中 $h_0,c_{\rm PB}$ 取自定理 35.4，故 $2\beta<c_{\rm PB}$。对任意实 $L\ge16$ 及任意 $\theta\in(0,\pi/6]$，令

$$
\theta_0=0,\quad\theta_1=\theta,\qquad
s_j=(3+\sin\theta_j)/2,\quad
\lambda_j^2=(L-1)/s_j,\quad
t_j=t_{h,\lambda_j,a_{\theta_j}},\quad j=0,1.
\tag{36.2}
$$

该族包含 $\theta=L^{-1/4}$：当 $L\ge16$ 时，$0<L^{-1/4}\le1/2<\pi/6$。这两份实际输入都严格正定、$D_j\succ0$，在同一个完整 $M_5(\mathbb C)$ 上满足相同的

$$
B,\ F,\ H,\ M_0=C^2,\ M_1=C,\ W=0,\qquad
\operatorname{spec}(M_{2,j})=\{1,L\}.
\tag{36.3}
$$

记

$$
b_j=\frac\beta{\displaystyle 3/2+
\frac{(L-1)(1+\cos\theta_j)}{3+\sin\theta_j}}.
\tag{36.4}
$$

则有精确不等式和精确集合等式

$$
\begin{gathered}
b_0=\frac{6\beta}{4L+5}<b_1<\frac{2\beta}{L}<\frac{c_{\rm PB}}L,\\
\boxed{\quad\mathcal J_{\rm both}(t_j)=[-b_j,b_j],\quad j=0,1,\qquad
\mathcal J_{\rm both}(t_0)\subsetneq\mathcal J_{\rm both}(t_1).\quad}
\end{gathered}
\tag{36.5}
$$

两个分别取向的相应短侧也完全确定：

$$
\mathcal J_+(t_j)\cap[0,\infty)=[0,b_j],\qquad
\mathcal J_-(t_j)\cap(-\infty,0]=[-b_j,0].
\tag{36.6}
$$

所有闭端点都属于原全正泛函、全部原探针的联合允许集。

证明。由 $M_{2,j}=I_2+\lambda_j^2a_{\theta_j}a_{\theta_j}^*$，其两个特征值准确为 $1,1+\lambda_j^2s_j= L$，不涉及渐近匹配。其余共享量来自命题 35.2。$3/2\le s_j\le7/4$ 给 $\lambda_j^2\ge60/7>4$；$0\le\theta_j\le\pi/6$ 给 $\cos\theta_j>0$。定理 35.5 因而给两取向 P2 的交正是 $[-b_j,b_j]$。

在 $[0,\pi/6]$ 上，

$$
\frac{d}{d\theta}\frac{1+\cos\theta}{3+\sin\theta}
=-\frac{1+\cos\theta+3\sin\theta}{(3+\sin\theta)^2}<0.
\tag{36.7}
$$

所以 $b_1>b_0$。取 $\theta=0$ 直接得到 $b_0$ 的值。对整个相位范围，$\sin\theta_j\le1/2$、$\cos\theta_j\ge\sqrt3/2$，故 (36.4) 的短侧分母满足

$$
d_{{\rm s},j}\ge\frac32+\frac{2+\sqrt3}{7}(L-1)>\frac L2,
\tag{36.8}
$$

其中 $(2+\sqrt3)/7>1/2$，且 $L-1>0$。从而 $b_j<2\beta/L<c_{\rm PB}/L$。由定理 35.4，整个 $[-b_j,b_j]$ 在两份输入各自的两个取向都满足全部原 PB；P2 的必要性排除其外的双取向联合成员，故得 (36.5)。相同理由在 $+$ 的非负半轴及 $-$ 的非正半轴给 (36.6)。这里无需知道分别取向宽侧的 PB 边界。∎

**推论 36.2（同一个带符号参数的成员与排除）。** 对定理 36.1 的每个 $L\ge16$，取

$$
\rho_L=(b_0+b_1)/2>0.
\tag{36.9}
$$

则同一个 $\rho_L$ 在两份实际输入、两个取向都通过全部原 PB，但在取向 $+$，$t_0$ 不满足原 P2，$t_1$ 满足原 P2；$t_1$ 还同时属于另一个取向的联合允许集。因此相同 $H,M_0,M_1,W$ 及整个 $M_2$ 谱，不能识别双取向联合允许集，也不能识别分别取向的上述短侧联合端点。

证明。$b_0<\rho_L<b_1<c_{\rm PB}/L$ 给两输入、两取向的全部 PB。对 $+$，精确正端点分别是 $b_0,b_1$，而 $\rho_L\in[-b_1,b_1]$ 给 $t_1$ 的双取向成员身份。∎

这一对的全部差异由实际关系而非标量谱决定：归一化 Schur 的有序谱基固定，而 $K$ 的虚非对角读数随方向改变。两份 $M_2$ 不是同一个矩阵；若固定 $H$ 并把 $M_2$ 本身也固定，前卷 (30.29) 就固定了 P2，不能再使用本证明的 P2 分离。

两个分别取向的整个 P2 区间并无这里的严格嵌套。具体地，对 $+$，$\theta_0$ 的负端点为 $-2\beta/3$，$\theta_1$ 的负端点因 $1-\cos\theta_1>0$ 严格向零移动，而正端点由 $b_0$ 严格增至 $b_1$；两区间因而互不包含。(36.5) 的严格嵌套只针对双取向联合集；(36.6) 则只确定各自指定的半轴。

作为本相位支上的相对校准，若在 $L$ 之外再给出关系读数

$$
\tau=\operatorname{tr}\bigl(C^{-1}(M_2-I_2)\bigr)=\lambda^2,
\qquad
\sin\theta=\frac{2(L-1)}\tau-3,
\tag{36.9a}
$$

则 $\theta\in[0,\pi/6]$ 唯一确定，继而由 (36.4) 恢复精确的 $b(\theta)$。第一式用 $a_\theta^*C^{-1}a_\theta=\|w_\theta\|^2=1$，第二式用 $L-1=\lambda^2s(\theta)$。这是相对于固定 $C$ 和所声明相位支的数学恢复；不声称该读数已有物理取得方式，也不声称它是一般来源的最小充分摘要。

### 36.2 任意相位路径的共同来源与固定相位的重标度极限

**命题 36.3（任意相位路径的共同来源极限与不同的重标度联合极限）。** 在 (36.2) 中允许 $\theta_1=\theta(L)$ 为任意取值于 $(0,\pi/6]$ 的相位函数，不要求相位趋于零。两份实际来源在 $L\to\infty$ 时均在范数中趋于同一个固定 $h$ 的 $t_h^0$，并有精确式

$$
\|t_j-t_h^0\|=s_j/\lambda_j+\lambda_j^{-3}\longrightarrow0,
\qquad j=0,1.
\tag{36.10}
$$

逐有限 $L$，两份精确双取向联合区间仍满足 (36.5) 的严格嵌套；两区间都按 Hausdorff 距离趋于 $\{0\}$。若相位固定为任意 $\theta_*\in(0,\pi/6]$，令

$$
R_{\theta_*}=\frac{\beta(3+\sin\theta_*)}{1+\cos\theta_*}>
R_0=\frac{3\beta}{2}.
$$

则重标度后的联合区间有不同的 Hausdorff 极限：这里 $L A=\{L\rho:\rho\in A\}$，且

$$
\begin{gathered}
L b_0\longrightarrow R_0,\qquad L b_1\longrightarrow R_{\theta_*},\\
L\mathcal J_{\rm both}(t_0)\longrightarrow[-R_0,R_0],\qquad
L\mathcal J_{\rm both}(t_1)\longrightarrow[-R_{\theta_*},R_{\theta_*}].
\end{gathered}
\tag{36.10a}
$$

特别地，固定 $\theta_1=\pi/6$ 时，每个有限 $L\ge16$ 都有

$$
\begin{gathered}
s_1=7/4,\qquad\lambda_1^2=4(L-1)/7,\\
b_0=\frac\beta{3/2+2(L-1)/3},\qquad
b_1=\frac\beta{3/2+(L-1)(2+\sqrt3)/7},
\end{gathered}
\tag{36.10b}
$$

因而

$$
\begin{gathered}
L b_0\longrightarrow\frac{3\beta}{2},\qquad
L b_1\longrightarrow\frac{7\beta}{2+\sqrt3}>\frac{3\beta}{2},\\
L\mathcal J_{\rm both}(t_0)\longrightarrow
[-3\beta/2,3\beta/2],\\
L\mathcal J_{\rm both}(t_1)\longrightarrow
\left[-\frac{7\beta}{2+\sqrt3},\frac{7\beta}{2+\sqrt3}\right].
\end{gathered}
\tag{36.10c}
$$

这些不同的重标度极限与相同实际来源极限相容；每个有限 $L$ 上两输入仍共享 $H,M_0,M_1,W$ 及 $\operatorname{spec}(M_2)=\{1,L\}$。固定正相位的两个分别取向 P2 区间均趋于 $\{0\}$，零相位则保留非零的单侧极限：

$$
\begin{gathered}
I_+(t_0)\longrightarrow[-2\beta/3,0],\qquad
I_-(t_0)\longrightarrow[0,2\beta/3],\\
I_+(t_1)\longrightarrow\{0\},\qquad
I_-(t_1)\longrightarrow\{0\}\quad(\theta_1=\theta_*>0).
\end{gathered}
\tag{36.10d}
$$

证明。由 $3/2\le s_j\le7/4$ 及 $\lambda_j^2=(L-1)/s_j$，无论相位函数是否收敛，两份 $\lambda_j$ 都趋于无穷，且 (35.7) 的右侧一致趋于零。这就在同一固定的实际载体与固定演员、耦合块上给出 (36.10)，不需要让探针向量或变分参数有界。由 (36.5)，双取向联合区间半径都小于 $2\beta/L$，故未重标度的极限均为 $\{0\}$。

若 $\theta_1=\theta_*$ 固定，将 (36.4) 的分子分母同除以 $L$，得到 (36.10a) 的端点极限；(36.7) 说明 $R_{\theta_*}>R_0$。闭区间的端点收敛即给所列 Hausdorff 极限。在 $\theta_* =\pi/6$ 代入 $\sin\theta_*=1/2$、$\cos\theta_*=\sqrt3/2$，即得 (36.10b)–(36.10c)。此结论没有把极限来源的允许集代入有限来源的全称条件。

对分别取向的 P2，直接用 (35.20)。零相位有 $d_{\rm w}=3/2$、$d_{\rm s}=3/2+\lambda_0^2$；每个固定正相位有 $1-\cos\theta_*>0$，所以 $d_{\rm w},d_{\rm s}$ 都趋于无穷。这给出 (36.10d)，无需把只适用于趋零相位的 (35.22) 用在固定正相位上。

保留的趋零相位例（$\theta_1=L^{-1/4}$ 的临界相位对照）。该例的共同来源收敛已由上面的任意相位论证覆盖。其临界参数满足

$$
\lambda_0^2(1-\cos\theta_0)=0,\qquad
\lambda_1^2(1-\cos\theta_1)
\sim\frac{L}{3/2}\frac{L^{-1/2}}2
=\frac{\sqrt L}{3}\longrightarrow\infty.
$$

此时可以应用 (35.22)：零相位的两个 P2 极限仍是 (36.10d) 的非零单侧区间，趋零正相位的两个 P2 极限则都是 $\{0\}$。精确双取向联合区间逐有限 $L$ 仍严格不同；但 $L b_0,L b_1$ 都趋于 $3\beta/2$，所以该趋零例的两个重标度联合极限相同。固定正相位族正好给出 (36.10a) 中仍然不同的极限。任意振荡相位函数的共同来源收敛不额外保证其分别取向 P2 区间存在极限。∎

### 36.3 更强谱匹配的共轭对及其限制

**命题 36.4（全来源同谱仍可分离一个取向，但不分离双取向交）。** 仍取 (36.1) 的 $h$。对每个 $L\ge16$，改取

$$
w^\pm=(1,\pm i)^{\mathsf T}/\sqrt2,\qquad
a^\pm=C^{1/2}U_0w^\pm,\qquad
\lambda^2=2(L-1)/3,\qquad t^\pm=t_{h,\lambda,a^\pm}.
\tag{36.11}
$$

则 $t^-=\overline{t^+}$、$D^-=\overline{D^+}$；不仅共享 (36.3) 的数据，整个实际 $t$ 的谱与环境 $D$ 的谱也分别完全相同。$M_0$ 本身固定；两份 $M_2$ 的对角元与逐项实部也相同。对取向 $+$，

$$
I_+(t^+)=[-2\beta/3,b_0],\qquad
I_+(t^-)=[-b_0,2\beta/3],\qquad b_0=6\beta/(4L+5).
\tag{36.12}
$$

同一个 $\rho=2\beta/L$ 在两输入、两取向都通过全部原 PB，属于 $\mathcal J_+(t^-)$ 却不属于 $I_+(t^+)$。然而

$$
\mathcal J_{\rm both}(t^+)=\mathcal J_{\rm both}(t^-)=[-b_0,b_0].
\tag{36.13}
$$

证明。$C,U_0,B,F$ 均为实矩阵，$a^-=\overline{a^+}$，由 (35.5) 直接得到来源与环境的共轭关系；Hermitian 矩阵的共轭具有相同实特征值。此时 $\|a^\pm\|^2=3/2$，故 $M_2$ 谱均为 $\{1,L\}$。其实际演员坐标矩阵为

$$
M_2^\pm=\begin{pmatrix}
1+\lambda^2/2&\ \pm i\lambda^2/\sqrt2\\
\mp i\lambda^2/\sqrt2&1+\lambda^2
\end{pmatrix}.
\tag{36.14}
$$

对应谱坐标的 $q$ 分别是 $-\lambda^2/2,+\lambda^2/2$，给 (36.12)。$b_0<2\beta/L<2\beta/3$，且 $2\beta/L<c_{\rm PB}/L$，分别给取向 $+$ 的成员与排除以及全部 PB。两取向的 P2 交均为 $[-b_0,b_0]$，又完全落入定理 35.4 的 PB 半径，故 (36.13) 精确成立。∎

共轭对中，来源共轭交换取向；这与引理 35.3 在同一来源上反射 $\rho$ 的操作不同。不能从 (36.12) 的一个取向分离推出双取向交的分离；非共轭相位对 (36.2) 才给 (36.5) 的严格嵌套。

### 36.4 数学归属、原量词与未决边界

原 P2 端点读取直接复用前卷 (30.29)。实际原列、有限变分和同一实际环境的缺陷补偿，分别沿 (27.4)–(27.13)、(31.4)–(31.14)；完整正泛函提升沿 (17.14)–(17.16)。定理 35.4 只消费 §32 在整个原索引集上的两条一致估计，不使用 §33.1 的近邻推广。引理 35.6 消费本卷 §34 的演员接触多项式与 Hermitian 重构，并在复目标比值上给出完整的两参数雅可比检验；§34 是该接触延续的纸面数学依赖。在 (35.5) 的实际实现下，§36 的精确同谱联合区间仅用定理 35.4 和定理 35.5 的精确 P2，不依赖接触延续，也不把其局部相位邻域扩大到全部相位。

Schur 补、秩一矩阵范数、加权方差、Cauchy–Schwarz、有限维实隐函数定理、Gram 行列式和正密度谱分解均是复用的成熟数学。Schur 补的来源范围沿前卷 §31 所引 Higham；最小范数缺陷沿同处所引 Penrose 及 (31.12) 的显式证明；实隐函数方法沿 §34 的既定使用。对称性引理 35.3 和单纯端点换算只作证明支撑，不计作独立新理论。本文的 `repo-derived` 增量是固定 $M_0$ 的实际来源构造及其原全称后果：独立于 §33 的精确 $M_1=C$ PB 运输、复临界相位的同源有限正预算排除，以及共享全 $M_2$ 谱时双取向联合集的精确差异。这里没有文献穷尽或历史优先权主张。

所有 PB 包含都遍历原全部实际 Hermitian 探针及完整代数的所有正复线性泛函，没有删去环境密度块。每个声称的 PB 违反均由同一有限实际探针与同一正泛函承担，且同时验证两笔原预算严格正；其质量可取任意指定有限 $\mu>0$。没有用各自可达但不能共同实现的极值替代同源推导，也没有用 $M_2$ 的标量谱代替相对于固定 $H,C$ 的矩阵方向。

尚未建立的是：在一个共同 P2 允许参数上，两份匹配谱的实际来源具有相反的全部 PB 结果。定理 36.1 与命题 36.4 的公共分离参数在两输入都通过全部 PB，排除完全来自其中一份输入的 P2；对共享 P2 区间内的 PB 单独分离不构成证据。一般相位下分别取向联合集的宽侧精确端点、整个集合是否为区间、最优 PB 常数以及任意预先给定较大 $h$ 的对应分类，也都不由本文得到。接触检验的非负只提供必要检验，不能反推全称充分性。本文既无 Lean／kernel 认证，也不作物理实现或外部原创性认证。

## 追加锚（本行以下为增补区）

## 37. 单位演员归一的全部原探针接触闭包极限定理

本节固定式 (35.5) 的来源，使用 §32 的基准强制估计，将 §35.8 的有限接触必要检验扩展为可见列闭包上的序列下极限与恢复定理。数值变分域只对演员分量作单位归一；原 PB 的全部探针、完整正泛函及任意正有限质量均保留。来源方向 $a$、演员作用 $a_{\rm act}$、残量尺度系数 $k$ 与原加权方差系数分别记号。旧式号 (17.x)、(27.x)、(30.x)、(31.x) 取前卷在本卷所引钉版 `315e167044afd2593b851f6546a82470ca16d446` 的含义。

### 37.1 精确来源与完整原条件

固定 $a\in\mathbb C^2\setminus\{0\}$，记 $m=\|a\|^2>0$。固定实数 $h$，使 $H=2C+hJ_A\succ0$ 且 $h$ 位于 §32、(35.16) 的强制估计邻域内。这里

$$
C=\operatorname{diag}(1,2),\qquad
T_A=\operatorname{diag}(1,-2),\qquad
J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad B=H+C.
\tag{37.1}
$$

对每个有限 $\lambda>0$，在同一演员、环境分解 $\mathbb C^2\oplus(\mathbb C^2\oplus\mathbb C)$ 中，来源准确为

$$
\begin{gathered}
\delta_\lambda=\lambda^{-3},\qquad
F=\begin{bmatrix}C\\0\end{bmatrix},\quad V=F^*,\quad
G_\lambda=\begin{bmatrix}I_2\\\lambda a^*\end{bmatrix},\\
D_\lambda^{\rm env}=
\begin{pmatrix}
C+\delta_\lambda\lambda^2aa^*&-\delta_\lambda\lambda a\\
-\delta_\lambda\lambda a^*&\delta_\lambda
\end{pmatrix},\qquad
t_\lambda^{\rm src}=\begin{pmatrix}B&V\\F&D_\lambda^{\rm env}\end{pmatrix}.
\end{gathered}
\tag{37.2}
$$

这正是命题 35.2 的式 (35.5)。对 $v\in\mathbb C^2,z\in\mathbb C$，环境二次型是

$$
v^*Cv+\delta_\lambda|z-\lambda a^*v|^2,
$$

故 $D_\lambda^{\rm env}\succ0$。块乘法及 Schur 补逐一给出

$$
\begin{gathered}
D_\lambda^{\rm env}G_\lambda=F,\qquad
G_\lambda=(D_\lambda^{\rm env})^{-1}F,\qquad
F^*F=C^2,\qquad G_\lambda^*F=C,\\
G_\lambda^*G_\lambda=I_2+\lambda^2aa^*,\qquad
B-F^*(D_\lambda^{\rm env})^{-1}F=H,\qquad t_\lambda^{\rm src}\succ0,\\
F_{3\cdot}=0,\qquad (G_\lambda)_{3\cdot}=\lambda a^*.
\end{gathered}
\tag{37.3}
$$

特别地 $M_0=C^2,M_1=C,M_2=I_2+\lambda^2aa^*$ 精确成立，环境零模像 $W=0$。这些等式只归属于 (37.2)，不使用 §34 的另一条环境实现。

固定一个取向 $\iota=\sigma i$，$\sigma\in\{1,-1\}$；整节对每个取向分别成立。以 $A\circ B=(AB+BA)/2$、$K_\sigma(A,B)=\iota[A,B]/2$ 定义原运算。在完整 $M_5(\mathbb C)$ 中取

$$
\begin{gathered}
c=C\oplus0_3,\quad s_\rho=\rho T_A\oplus0_3,\quad
x=X\oplus0_3,\quad X=X^*,\quad
g=K_\sigma(c,t_\lambda^{\rm src})+s_\rho,\\
h_x=K_\sigma(c,x),\quad k_c=c\circ t_\lambda^{\rm src},\quad r_x=c\circ x,\\
R_\tau=x+\tau(h_x-k_c),\qquad
S_\tau=t_\lambda^{\rm src}+\tau(r_x+g),\quad \tau=\pm1,\\
L_{\rm PB}=-2x\circ(h_x-k_c)-2t_\lambda^{\rm src}\circ(r_x+g),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{37.4}
$$

原 PB 指：对每个 $X=X^*$ 及完整代数上每个正复线性泛函 $\phi$，

$$
|\phi(L_{\rm PB})|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{37.5}
$$

原 P2 指 $\phi(g)^2\le\phi(c^2)\phi((t_\lambda^{\rm src})^2)-\phi(c\circ t_\lambda^{\rm src})^2$，量化相同的完整正泛函。本节的接触定理首先判原 PB；涉及 P2 时另列其实际区间。

### 37.2 单位演员变分域与环境的精确消元

**定义 37.1（归一原域及有限代价）。** 归一原测试遍取

$$
\begin{gathered}
\xi=(u,y),\qquad \|u\|=1,\quad y\in\mathbb C^3,\quad X=X^*\in M_2(\mathbb C),\\
\epsilon\in\{1,-1\},\qquad
\alpha_+,\alpha_->0,\quad \beta_+,\beta_-\in\mathbb R.
\end{gathered}
\tag{37.6}
$$

除 $\|u\|=1$ 外，没有范数、参数比值或预算非退化限制。所有参数在每个有限阶段均有限，但可随 $\lambda$ 逃逸。固定实数 $k$，以后始终令 $\rho=k/\lambda^2$。对 $\phi_\xi(A)=\xi^*A\xi$，定义带符号原有限代价

$$
\mathcal D_\lambda^{\rm orig}=
\sum_{\tau=\pm1}\left(
\alpha_\tau\|R_\tau\xi\|^2+
\alpha_\tau^{-1}\|(S_\tau-\beta_\tau R_\tau)\xi\|^2\right)
-2\epsilon\phi_\xi(L_{\rm PB}).
\tag{37.7}
$$

前卷 (27.12) 的原二列变分恒等式说明：对同一 $X,\xi$，(37.7) 在所有有限参数与两个 $\epsilon$ 上非负，当且仅当该向量满足 PB。恒等式包括 Gram 退化及下确界不取到的情形；某个有限 (37.7) 严格负已经足以给出 PB 严格失败。

为列出精确消元，写

$$
\begin{gathered}
z_\tau=\beta_\tau-\tau\epsilon\iota\alpha_\tau
       =\iota+\nu+\tau\ell,\qquad
A=(\alpha_++\alpha_-)/2=-\epsilon\operatorname{Im}_\iota\ell,\\
A>|1+\operatorname{Im}_\iota\nu|,\qquad
\alpha_\tau=A-\tau\epsilon(1+\operatorname{Im}_\iota\nu),\qquad
\beta_\tau=\operatorname{Re}(\nu+\tau\ell),\\
r=|\ell|>0,\quad n=|\nu|,\quad r+n\ge1,\quad
b=(r+n)^2/r\ge1,\\
w_\tau=\alpha_\tau^{-1},\quad s_\alpha=w_++w_-,\quad
\omega=(w_+-w_-)/s_\alpha\in(-1,1).
\end{gathered}
\tag{37.8}
$$

这里 $\operatorname{Im}_\iota$ 是基 $1,\iota$ 下的虚系数。反过来，上述严格合法性条件与实部公式恰好恢复全部原 $\alpha_\tau,\beta_\tau$，并未缩小变分域。置

$$
\begin{gathered}
p=Xu,\quad q=XCu,\quad a_{\rm act}=Bu+Vy,\quad v=a_{\rm act}-\iota p,\quad
U=\iota q+BCu+Cv,\\
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\qquad
\zeta=\operatorname{Re}(v^*T_Au),\\
t_{\rm req}=a_{\rm act}-Hu+(\ell+\omega\nu)C^2u/2,\qquad
\mathcal A=\sum_{\tau=\pm1}w_\tau\|\mathsf P+\tau\mathsf Q\|^2,\qquad
v_{\rm var}=\frac{|\nu|^2}{2A}.
\end{gathered}
\tag{37.9}
$$

$v_{\rm var}$ 是 (31.10) 的非负方差系数，不是残量系数 $k$。原环境列令 $d=Fu+D_\lambda^{\rm env}y$，$e=d+(\ell+\omega\nu)FCu/2$。由 (37.3) 有 $G_\lambda^*e=t_{\rm req}$。原 (32.5)、(35.13) 的列展开与加权方差恒等式给

$$
\begin{aligned}
((S_\tau-z_\tau R_\tau)\xi)_{\rm act}&=\mathsf P+\tau\mathsf Q,\\
((S_\tau-z_\tau R_\tau)\xi)_{\rm env}
 &=e+(\tau-\omega)\nu FCu/2,\\
\mathcal D_\lambda^{\rm orig}
 &=\mathcal A+s_\alpha\|e\|^2+v_{\rm var}\|C^2u\|^2
   +4\epsilon k\lambda^{-2}\zeta.
\end{aligned}
\tag{37.10}
$$

令 $R_\lambda=(I_2+\lambda^2aa^*)^{-1}$。约束 $G_\lambda^*e=t_{\rm req}$ 的全部解及范数分解是

$$
e=G_\lambda R_\lambda t_{\rm req}+e_0,\qquad
G_\lambda^*e_0=0,\qquad
\|e\|^2=t_{\rm req}^*R_\lambda t_{\rm req}+\|e_0\|^2.
\tag{37.11}
$$

这是正定二次型的正交最小范数公式，直接复用 (31.12)。据此定义

$$
\begin{aligned}
S_\lambda&=\mathcal A+s_\alpha t_{\rm req}^*R_\lambda t_{\rm req}
                    +v_{\rm var}\|C^2u\|^2,\\
\mathcal D_\lambda^{\rm red}&=S_\lambda+4\epsilon k\lambda^{-2}\zeta,\\
\mathcal D_\lambda^{\rm orig}
 &=\mathcal D_\lambda^{\rm red}+s_\alpha\|e_0\|^2.
\end{aligned}
\tag{37.12}
$$

约化域是 (37.6) 去掉 $y$，改让 $a_{\rm act}\in\mathbb C^2$ 任意。这个改变精确保留原域：给定任意约化测试，取 $e=G_\lambda R_\lambda t_{\rm req}$ 及

$$
y=(D_\lambda^{\rm env})^{-1}
\left(e-(\ell+\omega\nu)FCu/2-Fu\right).
\tag{37.13}
$$

于是 $Bu+Vy=Hu+G_\lambda^*e-(\ell+\omega\nu)C^2u/2=a_{\rm act}$。因此同一来源上的两个归一数值下确界精确相同：

$$
f_\lambda(k)=\inf_{\text{归一原测试}}\lambda^2\mathcal D_\lambda^{\rm orig}
            =\inf_{\text{归一约化测试}}\lambda^2\mathcal D_\lambda^{\rm red}.
\tag{37.14}
$$

此时暂允许下确界为 $-\infty$；§37.7 将先证明尾部一致下有界。

### 37.3 可见 Hermitian 图的闭包与零需求排除

**引理 37.2（包括演员轴的可见图闭包）。** 在 $\|u\|=1$ 的有限维空间中，实际图 $(u,Xu,XCu)$、$X=X^*$ 的闭包 $\overline{\mathcal G}$，恰由

$$
u^*p\in\mathbb R,\qquad (Cu)^*q\in\mathbb R,\qquad u^*q=p^*Cu
\tag{37.15}
$$

定义。若 $u_1u_2\ne0$，唯一实际矩阵为 $X=[p\ q][u\ Cu]^{-1}$。若 $u=z e_j$，$|z|=1$，$l\ne j$，则条件恰为 $p_j/z\in\mathbb R$、$q_j=c_jp_j$；$p_l,q_l$ 无额外限制，其中 $c_1=1,c_2=2$。

证明。三条件就是 $[u\ Cu]^*[p\ q]$ 为 Hermitian，故对实际图成立并在极限保留；非轴时反乘可逆矩阵证明充分性。在轴上逐项代入即得所列条件。为证明每个轴点都在闭包，设

$$
d=c_l-c_j,\qquad
s_{\rm ax}=(c_lp_l-q_l)/d,\qquad
t_{\rm ax}=(q_l-c_jp_l)/d.
\tag{37.17}
$$

若 $t_{\rm ax}=0$，令 $X_{lj}=p_l/z$、$X_{jl}=\overline{X_{lj}}$、$X_{jj}=p_j/z$，另一对角元任取实数，即实际实现原列。若 $t_{\rm ax}\ne0$，对 $0<\tau<1$ 取

$$
\begin{gathered}
u_{l,\tau}=\tau t_{\rm ax}/|t_{\rm ax}|,\qquad
u_{j,\tau}=z\sqrt{1-\tau^2},\\
X_{lj,\tau}=s_{\rm ax}/u_{j,\tau},\quad
X_{jl,\tau}=\overline{X_{lj,\tau}},\quad
X_{ll,\tau}=|t_{\rm ax}|/\tau,\quad X_{jj,\tau}=p_j/z.
\end{gathered}
\tag{37.18}
$$

所得 $X_\tau$ Hermitian、$\|u_\tau\|=1$，且

$$
(X_\tau u_\tau)_l=s_{\rm ax}+t_{\rm ax}=p_l,\qquad
(X_\tau Cu_\tau)_l=c_js_{\rm ax}+c_lt_{\rm ax}=q_l.
$$

另两个可见列坐标及 $u_\tau-u$ 都是 $O(\tau)$。这证明闭包描述；没有删除发散的 $X_{ll,\tau}$。∎

**定义 37.3（增广接触与极限代价）。** 对固定 $a,h,\iota$，$\mathcal C_\iota(a)$ 遍取 $\epsilon=\pm1$、$(u,p,q)\in\overline{\mathcal G}$、$\ell\in\mathbb C$、$a_{\rm act}\in\mathbb C^2$、$\eta\in\mathbb C$，满足

$$
\begin{gathered}
A=-\epsilon\operatorname{Im}_\iota\ell>1,\qquad
s(A)=\frac{2A}{A^2-1},\\
a_{\rm act}=\iota(I_2-\ell C^{-1})p,\qquad
q=(\ell I_2+2C^{-1})p+\iota BCu,\\
a_{\rm act}-Hu+\ell C^2u/2=\eta a.
\end{gathered}
\tag{37.19}
$$

保留两个 $\epsilon$。定义

$$
\zeta(c)=\operatorname{Re}((a_{\rm act}-\iota p)^*T_Au),\qquad
J_k(c)=s(A)|\eta|^2+4\epsilon k\zeta(c),\qquad
j(k)=\inf_{c\in\mathcal C_\iota(a)}J_k(c),
\tag{37.20}
$$

空集下确界约定为 $+\infty$。这些定义尚不宣称接触由一个有限轴上 $X$ 精确实现。

**引理 37.4（闭包上的零需求不可能）。** 将 (37.19) 的 $A>1$ 放宽到 $A\ge1$，仍要求其中两条演员接触等式；则

$$
a_{\rm act}-Hu+\ell C^2u/2\ne0.
\tag{37.21}
$$

特别地，每个 $\mathcal C_\iota(a)$ 中的 $\eta$ 非零。

证明。反设需求为零。用引理 37.2 取实际图 $(u_\delta,p_\delta,q_\delta)$ 逼近给定闭包点，误差 $o(\delta)$；实际点可保持不动。令

$$
\ell_\delta=\ell-\epsilon\iota\delta,\quad
A_\delta=A+\delta>1,\quad \nu_\delta=\rho_\delta=0,\quad
\alpha_{\tau,\delta}=A_\delta-\tau\epsilon,\quad
a_{{\rm act},\delta}=Hu_\delta-\ell_\delta C^2u_\delta/2.
$$

在 §32 基准来源 $F_b=D_b=C,G_b=I_2$ 上，这些是合法实际测试，环境需求恰为零，演员缺陷 $\mathsf P_\delta,\mathsf Q_\delta=O(\delta)$。若 $A=1$，较大权重为 $O(\delta^{-1})$；若 $A>1$，权重有界。因此基准平方和 $S_b=O(\delta)$ 趋零。可是 (35.16) 给 $S_b\ge\gamma b_\delta\ge\gamma>0$，矛盾。此论证同时覆盖演员轴和一个 $\alpha_\tau\to0$ 的边界。∎

### 37.4 每个缩放上子水平集的紧性

**定理 37.5（全部归一原测试的序列紧性与下极限）。** 固定上述 $a,h,\iota$ 及任意实 $k,M$。对每个 $\lambda_j\to\infty$ 和归一原测试序列，若

$$
\lambda_j^2\mathcal D_{\lambda_j}^{\rm orig}\le M,
\tag{37.22}
$$

则约化可见数据 $(\epsilon,u,p,q,a_{\rm act},\ell,\nu,\alpha_\pm,\beta_\pm)$ 有收敛子列。每个这样的收敛子列的极限满足 $\nu=0$，并通过 (37.19) 确定一个 $c\in\mathcal C_\iota(a)$；沿该子列都有

$$
\liminf_j\lambda_j^2\mathcal D_{\lambda_j}^{\rm orig}\ge J_k(c).
\tag{37.23}
$$

同一结论对 $\mathcal D^{\rm red}$ 成立。所有尾部上界、正下界和误差常数可依赖固定 $C,H,a,h,k,M$，不依赖 $\lambda_j$ 或所选测试。没有对无界 $k$ 的一致性结论，也不要求 $X_j$ 或 $y_j$ 有界。

证明先控制残量抵消。由 (37.12)，只需处理约化代价。用同一 $u,X,a_{\rm act}$ 和原有限参数在 §32 基准来源上取环境需求 $t_{\rm req}$，其平方和为

$$
S_b=\mathcal A+s_\alpha\|t_{\rm req}\|^2
               +\frac{n^2}{2A}\|C^2u\|^2.
\tag{37.24}
$$

这确实是一个原基准测试：取 $d_b=t_{\rm req}-(\ell+\omega\nu)C^2u/2$，$y_b=C^{-1}(d_b-Cu)$，即可使 $Bu+Cy_b=a_{\rm act}$。由 (35.16) 和秩一逆矩阵的最小特征值，尾部 $|\rho|\le r_0$ 上有

$$
\begin{gathered}
S_b\ge\gamma b,\qquad
|\zeta|\le K\bigl(b+\sqrt{bS_b}+|\rho|\bigr),\\
S_b\le L_\lambda S_\lambda,\qquad L_\lambda=1+\lambda^2m.
\end{gathered}
\tag{37.25}
$$

将 $M$ 增至 $\max(M,0)$，置 $x_b=S_b/b$。从 $\lambda^2S_\lambda\le M+4|k||\zeta|$ 得到准确的不等式

$$
x_b\le(m+\lambda^{-2})
\left[M+4K|k|\left(1+\sqrt{x_b}+|\rho|/b\right)\right].
\tag{37.26}
$$

因 $b\ge1$ 且尾部 $|\rho|\le1$，这是 $\sqrt{x_b}$ 的二次上界，故 $x_b$ 一致有界。重新代回即得

$$
S_b\le Cb,\qquad S_\lambda\le Cb/\lambda^2.
\tag{37.27}
$$

这里没有把有符号代价的上界误作正平方和的上界，而是先控制了允许的抵消。

方差项与 $\|C^2u\|\ge1$ 给

$$
\frac{n^2}{2A}\le S_\lambda,\qquad
\frac{n}{r+n}\le C/\lambda,\qquad
\frac nr\le C'/\lambda,\qquad \liminf r\ge1.
\tag{37.28}
$$

最后一步使用 $r+n\ge1$。半和、半差的加权 Cauchy–Schwarz，以及 $s_\alpha\ge2/A$，又给

$$
\|\mathsf P\|+\|\mathsf Q\|\le Cr/\lambda,\qquad
\|t_{\rm req}\|\le Cr,\qquad \|a_{\rm act}\|\le Cr.
\tag{37.29}
$$

例如 $\|t_{\rm req}\|^2\le L_\lambda S_\lambda/s_\alpha\le Cr^2$；这里已由 (37.28) 使 $b/r$ 有界。

现在排除 $r\to\infty$。若存在这种子列，置 $\chi=\nu/\ell$、$e_\ell=\ell/r$，$|e_\ell|=1$。原演员列的准确消元是

$$
\mathsf Q-\chi\mathsf P=(\iota C-\chi I_2)a_{\rm act}-Zp+\rho T_Au,
\qquad
Z=\bigl[\ell(1-\chi^2)-\iota\chi\bigr]I_2-C.
\tag{37.30}
$$

由 $\chi=O(\lambda^{-1})$，尾部 $\|Z^{-1}\|\le C/r$；结合 (37.29) 得 $p=O(1)$。再由 $\mathsf P=v-\nu p+\ell U/2$ 得 $U=O(1)$。用 $U$ 的定义和 $\mathsf Q$ 的等式，分别得到

$$
\frac qr-e_\ell p=O(\lambda^{-1}+r^{-1}),\qquad
\frac{a_{\rm act}}r+\iota e_\ell C^{-1}p
                  =O(\lambda^{-1}+r^{-1}).
\tag{37.31}
$$

实际 Hermitian 图的 $u^*q=p^*Cu$ 与 $p=O(1)$ 使
$u^*p=O(\lambda^{-1}+r^{-1})$；它本来是实数。另一个 Hermitian 条件 $(Cu)^*q\in\mathbb R$ 使

$$
\operatorname{Im}_\iota\bigl(e_\ell(Cu)^*p\bigr)
                  =O(\lambda^{-1}+r^{-1}).
\tag{37.32}
$$

准确使用 $C^{-1}T_A=3I_2-2C$，(37.31) 给

$$
\frac\zeta r=
\operatorname{Re}\!\left(\iota\overline{e_\ell}
       [3p^*u-2p^*Cu]\right)+O(\lambda^{-1}+r^{-1})
       =O(\lambda^{-1}+r^{-1}).
\tag{37.33}
$$

最后一个等号同时用了上述两个 Hermitian 配对；仅控制 $u^*p$ 不足以得此消失。另一方面，(37.25) 给

$$
\frac{\lambda^2S_\lambda}{r}
\ge\frac{\gamma b}{r(m+\lambda^{-2})}
\ge\frac\gamma{m+\lambda^{-2}}.
\tag{37.34}
$$

(37.33)–(37.34) 与
$\lambda^2\mathcal D_\lambda^{\rm red}/r\le M/r\to0$ 矛盾，因其左侧下极限至少为 $\gamma/m>0$。所以 $r$ 有界；此排除没有除以可能为零的 $\zeta$。

现在 $n=O(\lambda^{-1})$，$a_{\rm act}$ 有界，$\mathsf P,\mathsf Q\to0$。合法性给 $\liminf A\ge1$，故 (37.30) 中 $Z$ 尾部具有一致有界逆：其极限是虚系数绝对值至少 $1$ 的 $\ell I_2-C$。因而 $p$ 有界；由 $\mathsf P$ 得 $U$ 有界，再由其定义得 $q$ 有界。所有可见数据于是可取收敛子列，图极限属于 $\overline{\mathcal G}$，原 $\beta_\tau=\operatorname{Re}(\nu+\tau\ell)$ 也有界。

还须排除 $A\to1$，不能预设两权重的正下界。由 (37.27) 及 $r$ 有界，

$$
s_\alpha\|t_{\rm req}\|^2
\le(m+\lambda^{-2})\lambda^2S_\lambda\le C.
\tag{37.35}
$$

若 $A\to1$，则 $\nu\to0$ 使一个 $\alpha_\tau\to0$，故 $s_\alpha\to\infty$，进而 $t_{\rm req}\to0$。在 $\mathsf P=\mathsf Q=0,\nu=\rho=0$ 的极限中，先由 $\mathsf Q=0$ 得 $v=-\iota\ell C^{-1}p$，再由 $\mathsf P=0$ 得 $U=2\iota C^{-1}p$。这些正是 (37.19) 的两条演员接触等式，给出了被引理 37.4 排除的 $A=1$ 零需求。故尾部 $A\ge1+\delta$，$\delta>0$；两 $\alpha_\tau$ 均离零且有上界。

最后令 $\Pi_a=aa^*/m$、$\Pi_a^\perp=I_2-\Pi_a$。有

$$
R_\lambda=\Pi_a^\perp+(1+\lambda^2m)^{-1}\Pi_a.
\tag{37.36}
$$

$\lambda^2S_\lambda\le C$ 使 $\Pi_a^\perp t_{\rm req}=O(\lambda^{-1})$。因此每个可见收敛子列都满足 $t_{\rm req}\to\eta a$，并由引理 37.4 得 $\eta\ne0$。此子列的极限就是 (37.19) 的一个增广接触。设 $\eta_\lambda=a^*t_{\rm req}/m\to\eta$，则

$$
\liminf \lambda^2s_\alpha t_{\rm req}^*R_\lambda t_{\rm req}
\ge\lim s_\alpha\frac{\lambda^2m}{1+\lambda^2m}|\eta_\lambda|^2
=s(A)|\eta|^2.
\tag{37.37}
$$

其余缺陷平方与方差非负，$\zeta$ 连续收敛；原环境剩余项也非负。这证明每个收敛子列上的 (37.23)。当需要整列的下极限时，先取实现该下极限的子列，再用已经证明的紧性取子列；并不声称任意极限接触都实现整列下极限。∎

### 37.5 同一实际来源上的逐接触恢复

**定理 37.6（包括非实际轴接触的恢复）。** 对每个 $c\in\mathcal C_\iota(a)$、每个固定实数 $k$，存在对所有充分大有限 $\lambda$ 定义的归一原测试，使可见数据趋于 $c$，且

$$
\lambda^2\mathcal D_\lambda^{\rm orig}\longrightarrow J_k(c).
\tag{37.38}
$$

恢复使用 (37.2) 的同一实际 $D_\lambda^{\rm env},F,G_\lambda$；不改变源的三个矩。

证明。若接触有实际 $X$，保持 $u,X$。否则它是引理 37.2 的轴点，用 (37.18) 并取 $\tau_\lambda=\lambda^{-3}$，得到实际 $u_\lambda,X_\lambda$，且

$$
\|u_\lambda-u\|+\|X_\lambda u_\lambda-p\|
 +\|X_\lambda Cu_\lambda-q\|=O(\lambda^{-3}).
\tag{37.39}
$$

保持接触的 $a_{\rm act},\ell,\epsilon$，令

$$
\nu_\lambda=0,\qquad
\alpha_{\tau,\lambda}=A-\tau\epsilon>0,\qquad
\beta_{\tau,\lambda}=\tau\operatorname{Re}\ell,\qquad
\rho_\lambda=k/\lambda^2.
\tag{37.40}
$$

此时 $\mathsf P_\lambda=O(\lambda^{-3})$，$\mathsf Q_\lambda=O(\lambda^{-3})+O(\lambda^{-2})$，方差恰为零。令

$$
\begin{gathered}
t_\lambda=a_{\rm act}-Hu_\lambda+\ell C^2u_\lambda/2
             =\eta a+O(\lambda^{-3}),\\
e_\lambda=G_\lambda R_\lambda t_\lambda,\qquad
y_\lambda=(D_\lambda^{\rm env})^{-1}
       (e_\lambda-\ell FCu_\lambda/2-Fu_\lambda).
\end{gathered}
\tag{37.41}
$$

原矩阵 $D_\lambda^{\rm env}$ 在每个有限阶段可逆，故这个 $y_\lambda$ 有限，且直接由 (37.3) 得 $Bu_\lambda+Vy_\lambda=a_{\rm act}$。所用环境列正是原最小范数列，$e_0=0$。因此

$$
\lambda^2\mathcal A_\lambda=O(\lambda^{-2})\to0,\qquad
\lambda^2s_\alpha t_\lambda^*R_\lambda t_\lambda
             \to s(A)|\eta|^2,\qquad \zeta_\lambda\to\zeta(c).
\tag{37.42}
$$

例如垂直误差贡献为 $O(\lambda^2\lambda^{-6})$，平行项由 (37.36) 计算；这证明 (37.38)。恢复列可以由发散的 Hermitian 对角元产生，但每个有限阶段都是原来允许的探针。∎

**推论 37.7（严格负接触的原失败、两笔正预算与任意质量）。** 若 $J_k(c)<0$，定理 37.6 的原测试对所有充分大有限 $\lambda$ 严格违反 (37.5)，且两笔原预算严格正。对任意指定 $\mu\in(0,\infty)$ 都有质量 $\phi(I)=\mu$ 的这样的反例。

证明。(37.38) 给 (37.7) 严格负，(27.12) 即给原 PB 严格失败。还须检查预算本身，而不能仅由代价为负推断预算正性。由同一来源的精确末行，

$$
(e_\lambda)_3=\frac{\lambda a^*t_\lambda}{1+\lambda^2m}
               =\frac\eta\lambda+O(\lambda^{-3})\ne0.
\tag{37.43}
$$

同时 $FCu_\lambda=(C^2u_\lambda,0)^{\mathsf T}$，末坐标恰为零，首块非零。原 $R_\tau\xi_\lambda$ 的环境块是 $-\tau FCu_\lambda/2$，而 $E_\tau=(S_\tau-z_\tau R_\tau)\xi_\lambda$ 的环境块恰是 $e_\lambda$。两列复线性独立，对每个 $\tau$ 都有

$$
B_{\phi_{\xi_\lambda}}(R_\tau,S_\tau)
\ge\frac{\|C^2u_\lambda\|^2|(e_\lambda)_3|^2}{4}>0.
\tag{37.44}
$$

该下界先来自环境复 Gram 行列式，加入演员块只增加半正定 Gram 矩阵；原实 Gram 行列式又不小于复 Gram 行列式。$\eta\ne0$ 已由引理 37.4 证明。最后用 $\mu/\|\xi_\lambda\|^2$ 正倍缩放同一向量泛函，严格失败和两笔正预算一起保留。∎

### 37.6 从单位演员域回到全部正泛函

若任意原向量 $\xi=(w,y)$ 的演员分量 $w\ne0$，令 $b_w=\|w\|$，则

$$
\xi=b_w(u,y/b_w),\qquad u=w/b_w,\quad \|u\|=1.
\tag{37.45}
$$

同一 $X$ 与所有变分参数保持不动，(37.7) 和 PB 的两侧都按 $b_w^2$ 缩放。故归一对符号判定充分，即使 $b_w$ 任意小。若 $w=0$，直接由原列有 $x\xi=h_x\xi=r_x\xi=s_\rho\xi=0$，并且

$$
\phi_\xi(L_{\rm PB})=-2\operatorname{Re}((Vy)^*\iota CVy/2)=0;
\tag{37.46}
$$

因此 PB 自动成立，包括零向量。

完整正泛函具有有限谱和 $\phi=\sum_j\phi_{\xi_j}$。对每个固定 $X$，分别把 (17.15) 的二阶实 Gram 行列式根超可加性用于两笔预算，得到

$$
\sqrt{B_\phi(R_\tau,S_\tau)}\ge
\sum_j\sqrt{B_{\phi_{\xi_j}}(R_\tau,S_\tau)},\qquad \tau=\pm1.
\tag{37.47}
$$

这是 (17.14)–(17.16) 的谱和提升；结合左侧的三角不等式即可从全部向量 PB 得到 (37.5)。反向只需取向量泛函。环境密度及演员、环境混合块始终留在完整原代数中。固定任意正有限质量的全称条件等价，因为正倍缩放使 PB 两侧同阶齐次；零质量只有零泛函。两个取向的结论分别应用，要求双取向时两份全称条件同时保留。

这个符号等价不赋予未归一域相同的数值下确界。本节的 (37.14) 不得改成全部 $\xi$ 上的数值下确界：例如 $k=0$ 时，未归一域含零向量而代价非负，其下确界恰为零；归一域却由 (37.25) 得 $\lambda^2\mathcal D_\lambda\ge\gamma/(m+\lambda^{-2})$。以下下确界定理只指单位演员域。

### 37.7 下有界性与全局归一下确界极限

**定理 37.8（先下有界，再取全局极限）。** 对每个固定 $a,h,\iota,k$，存在有限 $C_0,\lambda_0$，使对所有 $\lambda\ge\lambda_0$ 和全部归一原或约化测试，

$$
\lambda^2\mathcal D_\lambda\ge-C_0.
\tag{37.48}
$$

非空接触域上的 $j(k)>-\infty$；若接触域非空则 $j(k)\in\mathbb R$，若为空则 $j(k)=+\infty$。且在扩展实数意义下

$$
\boxed{\ \lim_{\lambda\to\infty}f_\lambda(k)
       =\inf_{c\in\mathcal C_\iota(a)}J_k(c).\ }
\tag{37.49}
$$

证明。若 (37.48) 不成立，可选 $\lambda_n\ge n$ 和归一测试，使 $\lambda_n^2\mathcal D_{\lambda_n}\le-n$。定理 37.5 对上界 $M=0$ 适用，给一个收敛可见子列及有限接触值 $J_k(c)$，并给其下极限至少为 $J_k(c)>-\infty$，与趋于 $-\infty$ 矛盾。这既排除尾部任何 $f_\lambda=-\infty$，也建立统一有限下界。每个有限 $\lambda$ 有有限参数的归一测试，故 $f_\lambda<+\infty$。

若接触值无下界，可取 $c_n$ 满足 $J_k(c_n)\le-2n$，再对每个 $c_n$ 用定理 37.6 选充分大的 $\lambda_n\ge n$，使恢复值不大于 $-n$。这又违反 (37.48)。因此在引用近极小列以前，归一下确界及接触下确界的下有界性都已建立。

接触域非空时，每个固定接触的恢复给 $\limsup f_\lambda(k)\le J_k(c)$；对 $c$ 取下确界得上极限不超过有限的 $j(k)$。取实现 $\liminf_{\lambda\to\infty}f_\lambda(k)$ 的 $\lambda_n\to\infty$，再取有限近极小测试，使其值在 $[f_{\lambda_n},f_{\lambda_n}+1/n]$ 内。已有上下界使这些值具有共同有限上界。定理 37.5 给子列与接触 $c$，从而

$$
\liminf_{\lambda\to\infty}f_\lambda(k)
\ge J_k(c)\ge j(k).
$$

上下极限相合。若接触域为空，而 $f_\lambda$ 不趋于 $+\infty$，则存在 $\lambda_n\to\infty$ 和有限 $M$，使 $f_{\lambda_n}\le M$。取误差至多 $1$ 的近极小测试，定理 37.5 就会产生一个接触，矛盾。因此空域时极限确为 $+\infty$。整个证明使用序列紧性和实际恢复，没有交换未经证明的下确界与极限。∎

### 37.8 全称 PB 的严格阈值及临界边界

**推论 37.9（逐接触的必要性与严格充分性）。** 固定实 $k$。若 (37.2) 在 $\rho=k/\lambda^2$ 对所有充分大 $\lambda$ 满足全部原 PB，则每个 $c\in\mathcal C_\iota(a)$ 有 $J_k(c)\ge0$。若每个接触都有 $J_k(c)>0$，则对所有充分大 $\lambda$ 满足全部原 PB。

证明。负接触由推论 37.7 给尾部失败，证明必要性。反之，若存在 $\lambda_n\to\infty$ 上的失败，由 §37.6 的全正泛函提升及 (27.12) 选出归一原有限测试使 $\mathcal D_{\lambda_n}^{\rm orig}<0$。定理 37.5 对 $M=0$ 给一个接触，且

$$
J_k(c)\le\liminf_n\lambda_n^2\mathcal D_{\lambda_n}^{\rm orig}\le0,
$$

矛盾。此处逐接触严格正已经足够，不额外假设一个统一正间隙。空接触域也由同一矛盾论证给充分性。∎

对当前固定取向，定义两个带方向的阈值；其 $h,\iota$ 依赖在记号中省略：

$$
\begin{aligned}
K_{\rm positive}(a)
 &=\inf_{c\in\mathcal C_\iota(a):\ \epsilon\zeta(c)<0}
       \frac{s(A)|\eta|^2}{-4\epsilon\zeta(c)},\\
K_{\rm negative}(a)
 &=\inf_{c\in\mathcal C_\iota(a):\ \epsilon\zeta(c)>0}
       \frac{s(A)|\eta|^2}{4\epsilon\zeta(c)}.
\end{aligned}
\tag{37.50}
$$

空下确界仍为 $+\infty$。对每个固定 $k\ge0$，$k<K_{\rm positive}(a)$ 时 $\rho=k/\lambda^2$ 最终通过全部原 PB；$k>K_{\rm positive}(a)$ 时最终严格失败。理由是前一范围使每个 $J_k>0$，后一范围由下确界定义找到一个 $J_k<0$。对 $\rho=-k/\lambda^2$，用 $K_{\rm negative}(a)$ 得相同的严格两侧结论。要求两个取向时，分别检查各自的阈值。

在有限阈值等号处，定义只保证所有接触的领先值非负；若有零接触，(37.38) 不决定有限 $\lambda$ 的次阶符号。即使阈值下确界不取到，也必须按实际 $J_k$ 检查：若它们仍逐点严格正，推论 37.9 可用。本文不把非负替换为严格正，不宣称一般的临界等号分类。

### 37.9 一个可恢复而非实际的轴接触

取 $\iota=i$、$0<h$ 充分小，仍处于 §32 邻域。固定实际方向及接触数据

$$
\begin{gathered}
a=(1,\sqrt2)^{\mathsf T}/\sqrt2,\quad m=3/2,\quad
\epsilon=1,\quad u=e_1,\quad \ell=-1-2\iota,\quad A=2,\\
\eta=\sqrt2(-11/2+2\iota),\qquad p_1=q_1=3/2,\\
p_2=\frac{h+\eta}{-1+3\iota/2},\qquad
q_2=-2\iota p_2+\iota h,\qquad
a_{\rm act}=(-3+3\iota,h+\eta)^{\mathsf T}.
\end{gathered}
\tag{37.51}
$$

三个 Hermitian 闭包条件在第一轴只要求 $p_1$ 实且 $q_1=p_1$，故满足。第一接触等式的坐标为
$\iota(1-\ell)(3/2)=-3+3\iota$ 和
$\iota(1-\ell/2)p_2=(-1+3\iota/2)p_2=h+\eta$。
第二接触等式的第一坐标是 $(\ell+2)(3/2)+3\iota=3/2$，第二坐标恰是所给 $q_2$。最后需求的两个坐标分别为 $-11/2+2\iota=\eta/\sqrt2$ 和 $\eta$。所以 (37.19) 全部成立，且

$$
\zeta=-3,\qquad |\eta|^2=137/2,\qquad s(A)=4/3,\qquad
J_k=274/3-12k.
\tag{37.52}
$$

在 $h=0$，$q_2-p_2=(-1-2\iota)\eta/(-1+3\iota/2)\ne0$，故固定充分小正 $h$ 后仍非零。实际第一轴探针却必有 $q=p$，所以这是一个没有有限轴上实现的接触。引理 37.2 的发散对角元恢复给实际趋轴探针；它表明闭包不可直接删去。

每个固定 $k>137/18$ 由此给同源有限阶段的严格 PB 排除与两笔正预算。它们也最终通过两个取向的原 P2：令 $\beta=h/\sqrt2$、$U_0=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。这里 $U_0^*C^{-1/2}a=e_1$，实际 P2 的逆坐标矩阵为

$$
\mathsf K=\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix}.
$$

由 (30.29)，其精确双取向半径为

$$
\frac{h/\sqrt2}{\sqrt{(3/2+\lambda^2)(3/2)}}.
\tag{37.53}
$$

它为正的 $\lambda^{-1}$ 阶，故支配每个固定 $k/\lambda^2$。例子不声称 $137/18$ 锐，也不声称此轴值低于全部精确有限 $\nu=0$ 接触的下确界。

### 37.10 同谱比较所需的共同尺度与未决边界

若要比较两个实际方向在共同 $M_2$ 谱 $(1,L)$ 下的 PB 阈值，必须分别令

$$
\lambda^2=(L-1)/m,\qquad \rho=q_{\rm shared}/(L-1),\qquad k=q_{\rm shared}/m.
\tag{37.54}
$$

这里 $q_{\rm shared}\in\mathbb R$ 是共同残量尺度。正方向应比较 $mK_{\rm positive}(a)$，负方向应比较 $mK_{\rm negative}(a)$。只比较未乘 $m$ 的阈值不能推出共同 $\rho$ 的差异。

每份来源还必须独立通过实际 P2。若 $a=C^{1/2}U_0w$，$w\in\mathbb C^2\setminus\{0\}$，$h>0$，令

$$
\mathsf K=\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix}
          +\frac{L-1}{m}ww^*,\qquad z=\mathsf K_{12},\qquad
\beta=h/\sqrt2.
\tag{37.55}
$$

这是该来源的实际逆矩阵坐标。前卷 (30.29) 对取向 $\sigma$ 给精确闭区间

$$
I_\sigma=
\left[
-\frac{\beta}{\sqrt{\mathsf K_{11}\mathsf K_{22}}+\sigma\operatorname{Im}z},\quad
 \frac{\beta}{\sqrt{\mathsf K_{11}\mathsf K_{22}}-\sigma\operatorname{Im}z}
\right].
\tag{37.56}
$$

正定性使两分母严格正。任何拟议的共同 $\rho=q_{\rm shared}/(L-1)$ 都须代入两份实际区间；要求双取向则还须分别取两取向的交。

本节尚未给出两个方向具有严格不同的 $mK_{\rm positive}(a)$ 或 $mK_{\rm negative}(a)$ 的证明，也没有给出共同 P2 允许的 $q_{\rm shared}$ 上一份全部 PB 成立、另一份 PB 失败的成对见证。§36 的共轭相位对不被提升为这种 PB 分离。

本节的 `repo-derived` 纸面增量是同一固定 $M_0$ 来源、单位演员域上的全部上子水平紧性、可见图轴闭包恢复及由此得到的归一下确界极限与严格阈值。原列、变分和完整正泛函提升复用 §§17、27、31 及 (32.4)–(32.7)、(35.13)；全部参数上的基准强制估计复用 §32、(35.16)。正交最小范数、加权方差、Schur 补、Cauchy–Schwarz、有限维序列紧性和谱和 Gram 根不等式均按成熟数学直接使用。本文没有外部文献穷尽或历史优先权主张，没有 Lean／kernel 核验，也不主张物理实现。

增广接触下确界与精确有限 $\nu=0$ 接触下确界是否相同，需要另外的密度或等价论证；本节只恢复近接触的实际原测试，不假设该等式。临界零值的次阶符号、阈值的显式最优值及共同 P2 内的成对 PB 分离仍未解决。

## 追加锚（本行以下为增补区）

## 38. 共同完整 P2 区间内的更强实际有限轴恢复排除

本节固定 (35.5)、(37.2) 的两个实来源方向 $a_\tau=(1/\sqrt2,\tau)^{\mathsf T}$，$\tau=\pm1$。两份来源的完整原 P2 区间完全相同，但在该区间的严格内部，每个固定 $k>809/480$、$\rho=k/\lambda^2$ 都在充分大的有限阶段违反原 PB。这里的界严格加强 §37.9 的 $k>137/18$：

$$
\frac{809}{480}<\frac{137}{18}.
$$

证明直接构造有限 Hermitian 探针及同一来源上的环境向量，并保留两笔严格正的原预算。原残量矩阵始终是 $T_A=\operatorname{diag}(1,-2)$；本节不将它替换成归一化后的 $\operatorname{diag}(1,-1)$。前卷式号仍取 §37 所引钉版的含义。

### 38.1 两个实际来源、原条件与排除定理

在 $\mathbb C^2\oplus(\mathbb C^2\oplus\mathbb C)$ 上置

$$
\begin{gathered}
C=\operatorname{diag}(1,2),\qquad T_A=\operatorname{diag}(1,-2),\qquad
J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
a_\tau=(1/\sqrt2,\tau)^{\mathsf T},\qquad b=\|a_\tau\|^2=3/2,\qquad
H=2C+hJ_A,\qquad B=H+C,\\
\delta_\lambda=\lambda^{-3},\qquad
F=\begin{bmatrix}C\\0\end{bmatrix},\qquad
G_{\tau,\lambda}=\begin{bmatrix}I_2\\\lambda a_\tau^*\end{bmatrix},\\
D_{\tau,\lambda}=\begin{pmatrix}
C+\delta_\lambda\lambda^2a_\tau a_\tau^*&-\delta_\lambda\lambda a_\tau\\
-\delta_\lambda\lambda a_\tau^*&\delta_\lambda
\end{pmatrix},\qquad
t_{\tau,\lambda}=\begin{pmatrix}B&F^*\\F&D_{\tau,\lambda}\end{pmatrix}.
\end{gathered}
\tag{38.1}
$$

这就是 (35.5) 的原实际实现。固定一份来源后，简写 $D=D_{\tau,\lambda}$、$G=G_{\tau,\lambda}$、$t=t_{\tau,\lambda}$。环境正二次型及精确矩恒等式为

$$
\begin{gathered}
(v,z)^*D(v,z)=v^*Cv+\delta_\lambda|z-\lambda a_\tau^*v|^2,\\
DG=F,\qquad F^*F=C^2,\qquad F^*G=G^*F=C,\qquad
M_2=G^*G=I_2+\lambda^2a_\tau a_\tau^*,\\
B-F^*D^{-1}F=H.
\end{gathered}
\tag{38.2}
$$

因此每个有限 $\lambda>0$ 上 $D\succ0$；当 $0<h<2\sqrt2$ 时，$H$ 的首主子式为 $2$、行列式为 $8-h^2>0$，从而 $t\succ0$。两份来源共享 $H,M_0=C^2,M_1=C,W=0$ 及 $M_2$ 的整个谱 $\{1,1+(3/2)\lambda^2\}$，并各自保留自己的实际环境。

为区分来源符号 $\tau$ 与两笔预算，用 $d=\pm1$ 标记原列。给定取向 $\iota=\sigma i$、$\sigma=\pm1$，在完整 $M_5(\mathbb C)$ 上定义

$$
\begin{gathered}
A\circ B=(AB+BA)/2,\qquad K_\sigma(A,B)=\sigma i[A,B]/2,\\
c=C\oplus0_3,\quad s_\rho=\rho T_A\oplus0_3,\quad
x=X\oplus0_3,\quad X=X^*,\quad g=K_\sigma(c,t)+s_\rho,\\
h_x=K_\sigma(c,x),\qquad k_c=c\circ t,\qquad r_x=c\circ x,\\
R_d=x+d(h_x-k_c),\qquad S_d=t+d(r_x+g),\\
L_{\rm PB}=-2x\circ(h_x-k_c)-2t\circ(r_x+g),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{38.3}
$$

完整原 P2 要求每个正复线性泛函 $\phi$ 满足

$$
\phi(g)^2\le\phi(c^2)\phi(t^2)-\phi(c\circ t)^2.
\tag{38.4}
$$

全部原 PB 要求每个实际 $X=X^*$ 及每个这样的 $\phi$ 满足

$$
|\phi(L_{\rm PB})|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{38.5}
$$

所有平方、乘积与泛函均在 (38.1) 的完整原代数中计算。

**定理 38.1（$809/480$ 的实际有限恢复排除）。** 固定 $0<h<2\sqrt2$、有限实数 $k>809/480$ 及任意指定质量 $\mu\in(0,\infty)$。存在有限 $\Lambda(h,k)>1$，使每个有限 $\lambda>\Lambda(h,k)$、每份 $\tau=\pm1$ 来源、每个取向 $\sigma=\pm1$ 都满足：

1. 其完整原 P2 的精确允许集均为同一个闭区间

   $$
   I_{\tau,\sigma}=\left[-\frac{h/\sqrt2}{T_\lambda},\frac{h/\sqrt2}{T_\lambda}\right],
   \qquad T_\lambda=\sqrt{\frac32\left(\frac32+\lambda^2\right)},
   \tag{38.6}
   $$

   且 $\rho=k/\lambda^2$ 严格位于其内部。
2. 存在有限实际 Hermitian 探针 $x=X\oplus0_3$ 和同一来源上的一个向量正泛函 $\phi$，$\phi(I)=\mu$，使 (38.5) 严格失败，并且

   $$
   B_\phi(R_+,S_+)>0,\qquad B_\phi(R_-,S_-)>0.
   \tag{38.7}
   $$

见证可随来源与取向变化；每份输入内的两笔预算使用同一 $x$、同一 $\phi$ 和该输入自己的 $D,F,G$。固定 $h$ 后，对任意紧区间 $k\in[m,M]$、$m>809/480$，可选共同的有限截止 $\Lambda(h,[m,M])$。特别地，结论适用于 §37 所需的充分小固定正 $h$；以下证明本身只用 $0<h<2\sqrt2$。

### 38.2 精确轴接触与常数

先取 $\sigma=+1$。固定合法有限变分参数

$$
\begin{gathered}
\epsilon=1,\qquad \ell=-1-9i,\qquad \nu=0,\\
\alpha_+=8,\quad\alpha_-=10,\quad\beta_+=-1,\quad\beta_-=1,\\
z_d=\beta_d-di\alpha_d=i+d\ell,\qquad
s_\alpha=\alpha_+^{-1}+\alpha_-^{-1}=9/40.
\end{gathered}
\tag{38.8}
$$

令 $u=e_1$，并定义目标可见列

$$
\begin{gathered}
p_1=q_1=1/3,\qquad (a_{\rm act})_1=-3+2i/3,\\
d_{01}=-11/2-23i/6,\qquad\eta=\sqrt2\,d_{01},\qquad
(a_{\rm act})_2=h+\eta\tau,\\
p_2=\frac{h+\eta\tau}{i(1-\ell/2)},\qquad
q_2=(\ell+1)p_2+ih,\qquad
i(1-\ell/2)=-9/2+3i/2\ne0,\\
v=a_{\rm act}-ip,\qquad U=iq+BCu+Cv.
\end{gathered}
\tag{38.9}
$$

逐坐标代入给出

$$
v_1=-3+i/3=-i\ell/3,\quad U_1=2i/3,\qquad
v_2=-i\ell p_2/2,\quad U_2=ip_2.
$$

所以两条零残量演员接触恰为

$$
P_0=v+\ell U/2=0,\qquad Q_0=iCv-\ell p=0.
\tag{38.10}
$$

需求列及残量配对也完全确定：

$$
\begin{gathered}
d_0=a_{\rm act}-Hu+\ell C^2u/2=(d_{01},\eta\tau)^{\mathsf T}
      =\eta a_\tau,\\
|d_{01}|^2=\frac{121}{4}+\frac{529}{36}=\frac{809}{18},\qquad
|\eta|^2=\frac{809}{9},\qquad
\operatorname{Re}(v^*T_Au)=-3.
\end{gathered}
\tag{38.11}
$$

在 $u=e_1$ 上实际探针必须有 $q=p$；(38.9) 不以 $q_2=p_2$ 为前提。因此必须先恢复实际有限列，才能把这些接触数据用于原 PB。

### 38.3 包括零差分支的有限 Hermitian 恢复

记

$$
s_{\rm vis}=2p_2-q_2,\qquad t_{\rm vis}=q_2-p_2.
$$

若 $t_{\rm vis}\ne0$，对每个有限 $\lambda>1$ 置

$$
\begin{gathered}
\varepsilon_\lambda=\lambda^{-3},\qquad
(u_\lambda)_2=\varepsilon_\lambda\frac{t_{\rm vis}}{|t_{\rm vis}|},\qquad
(u_\lambda)_1=\sqrt{1-\varepsilon_\lambda^2},\\
X_\lambda=\begin{pmatrix}
1/3&\overline{s_{\rm vis}}/(u_\lambda)_1\\
s_{\rm vis}/(u_\lambda)_1&|t_{\rm vis}|/\varepsilon_\lambda
\end{pmatrix},\qquad
p_\lambda=X_\lambda u_\lambda,\qquad q_\lambda=X_\lambda Cu_\lambda.
\end{gathered}
\tag{38.12}
$$

矩阵逐项有限且 Hermitian，$\|u_\lambda\|=1$，所有分母非零。直接相乘，第二坐标精确为

$$
(p_\lambda)_2=s_{\rm vis}+t_{\rm vis}=p_2,\qquad
(q_\lambda)_2=s_{\rm vis}+2t_{\rm vis}=q_2.
$$

第一坐标分别为

$$
(p_\lambda)_1=\frac{(u_\lambda)_1}{3}
 +\frac{\overline{s_{\rm vis}}(u_\lambda)_2}{(u_\lambda)_1},\qquad
(q_\lambda)_1=\frac{(u_\lambda)_1}{3}
 +\frac{2\overline{s_{\rm vis}}(u_\lambda)_2}{(u_\lambda)_1}.
$$

若 $t_{\rm vis}=0$，则 $q=p$，改取

$$
u_\lambda=e_1,\qquad
X_\lambda=\begin{pmatrix}1/3&\overline{p_2}\\p_2&0\end{pmatrix},
\qquad p_\lambda=p,\quad q_\lambda=q.
\tag{38.13}
$$

此分支不除以 $t_{\rm vis}$，也不除以零演员坐标。两种情形共同给出实际 $x_\lambda=X_\lambda\oplus0_3$，以及

$$
u_\lambda-u=O(\lambda^{-3}),\qquad
p_\lambda-p=O(\lambda^{-3}),\qquad q_\lambda-q=O(\lambda^{-3}).
\tag{38.14}
$$

这些是可见列估计，不要求 $X_\lambda$ 一致有界。

### 38.4 同一来源上的精确环境提升

保持 $a_{\rm act},\ell$ 及 (38.8) 固定。对刚构造的实际 $u_\lambda,X_\lambda$ 定义

$$
\begin{gathered}
d_\lambda=a_{\rm act}-Hu_\lambda+\ell C^2u_\lambda/2,\qquad
w_\lambda=FCu_\lambda=(C^2u_\lambda,0)^{\mathsf T},\\
e_\lambda=GM_2^{-1}d_\lambda,\qquad
y_\lambda=D^{-1}(e_\lambda-\ell w_\lambda/2-Fu_\lambda),\qquad
\xi_\lambda=(u_\lambda,y_\lambda).
\end{gathered}
\tag{38.15}
$$

全部量在每个有限 $\lambda>1$ 上有限。由 (38.2) 有 $G^*e_\lambda=d_\lambda$，故

$$
\begin{gathered}
Fu_\lambda+Dy_\lambda=e_\lambda-\ell w_\lambda/2,\\
Bu_\lambda+F^*y_\lambda
 =Hu_\lambda+d_\lambda-\ell C^2u_\lambda/2=a_{\rm act}.
\end{gathered}
\tag{38.16}
$$

因此演员列及两条环境缺陷确由同一原向量 $\xi_\lambda$ 同时实现。

由 (38.11)、(38.14)，$d_\lambda=\eta a_\tau+\Delta_\lambda$，其中 $\Delta_\lambda=O(\lambda^{-3})$。令 $L_\lambda=1+b\lambda^2$，则

$$
\begin{gathered}
M_2^{-1}=I_2-\frac{\lambda^2a_\tau a_\tau^*}{L_\lambda},\qquad
M_2^{-1}a_\tau=\frac{a_\tau}{L_\lambda},\qquad
\|GM_2^{-1}\|\le1,\\
\|e_\lambda\|^2=d_\lambda^*M_2^{-1}d_\lambda
 =\frac{|\eta|^2b}{L_\lambda}+O(\lambda^{-4}),\qquad
\lambda^2\|e_\lambda\|^2\longrightarrow\frac{809}{9}.
\end{gathered}
\tag{38.17}
$$

这里算子范数界来自 $(GM_2^{-1})^*(GM_2^{-1})=M_2^{-1}\le I_2$；主环境列范数为 $O(\lambda^{-1})$，扰动列为 $O(\lambda^{-3})$，给出所列误差。尤其，原环境的最后坐标满足精确公式

$$
(e_\lambda)_3=\frac{\lambda a_\tau^*d_\lambda}{L_\lambda}
 =\frac{\eta}{\lambda}+O(\lambda^{-3})\ne0
\quad\text{对所有充分大有限 }\lambda.
\tag{38.18}
$$

### 38.5 原作用列与严格负缺陷

以下所有 $R_d,S_d,L_{\rm PB}$ 均取当前实际 $x_\lambda,t_{\tau,\lambda},\rho$。置

$$
\begin{gathered}
v_\lambda=a_{\rm act}-ip_\lambda,\qquad
U_\lambda=iq_\lambda+BCu_\lambda+Cv_\lambda,\\
P_\lambda=v_\lambda+\ell U_\lambda/2,\qquad
Q_\lambda=iCv_\lambda-\ell p_\lambda+\rho T_Au_\lambda.
\end{gathered}
\tag{38.19}
$$

前卷 (31.6)–(31.7) 的原列，在此记号下直接成为

$$
\begin{aligned}
R_d\xi_\lambda&=(p_\lambda-dU_\lambda/2,-dw_\lambda/2),\\
S_d\xi_\lambda&=\left(a_{\rm act}
 +d\left(\frac{Cp_\lambda+q_\lambda+iCa_{\rm act}-iBCu_\lambda}{2}
                +\rho T_Au_\lambda\right),\,
 Fu_\lambda+Dy_\lambda-di w_\lambda/2\right).
\end{aligned}
\tag{38.20}
$$

由 $z_d=i+d\ell$ 及 (38.16)，其完成列精确为

$$
E_d=(S_d-z_dR_d)\xi_\lambda=(P_\lambda+dQ_\lambda,e_\lambda).
\tag{38.21}
$$

对同一个原正向量泛函 $\phi_\lambda(A)=\xi_\lambda^*A\xi_\lambda$ 定义所选有限变分缺陷

$$
\mathcal D_\lambda=
\sum_{d=\pm1}\left(\alpha_d\|R_d\xi_\lambda\|^2
 +\alpha_d^{-1}\|(S_d-\beta_dR_d)\xi_\lambda\|^2\right)
 -2\phi_\lambda(L_{\rm PB}).
\tag{38.22}
$$

原恒等式 (31.9)，等价于 (32.4)，对 (38.20)–(38.21) 给出精确等式

$$
\mathcal D_\lambda=
\sum_{d=\pm1}\alpha_d^{-1}\|P_\lambda+dQ_\lambda\|^2
 +\frac9{40}\|e_\lambda\|^2
 +4\rho\operatorname{Re}(v_\lambda^*T_Au_\lambda).
\tag{38.23}
$$

它保留实际演员误差与实际环境误差。由 (38.10)、(38.14) 有

$$
P_\lambda=O(\lambda^{-3}),\qquad
Q_\lambda=\rho T_Au_\lambda+O(\lambda^{-3}),\qquad
\operatorname{Re}(v_\lambda^*T_Au_\lambda)=-3+O(\lambda^{-3}).
$$

取 $\rho=k/\lambda^2$，演员平方和为 $O(\lambda^{-4})$。结合 (38.17) 得

$$
\lambda^2\mathcal D_\lambda\longrightarrow
\frac9{40}\frac{809}{9}-12k=\frac{809}{40}-12k<0
\qquad(k>809/480).
\tag{38.24}
$$

因而每个充分大的有限阶段都有 $\mathcal D_\lambda<0$。前卷 (27.12) 的实 Gram 变分不等式，对这里同一对实际原列分别给

$$
2\sqrt{B_{\phi_\lambda}(R_d,S_d)}\le
\alpha_d\|R_d\xi_\lambda\|^2
 +\alpha_d^{-1}\|(S_d-\beta_dR_d)\xi_\lambda\|^2.
$$

相加并用 (38.22)，得到

$$
\phi_\lambda(L_{\rm PB})>
\sqrt{B_{\phi_\lambda}(R_+,S_+)}+
\sqrt{B_{\phi_\lambda}(R_-,S_-)}\ge0.
\tag{38.25}
$$

这严格违反原绝对值 PB，不要求所选变分参数达到任一 Gram 根的下确界。两份来源只有有限个 $\tau$ 值；各误差对有界 $k$ 一致，故 (38.24) 在每个 $[m,M]$、$m>809/480$ 上一致严格为负。

### 38.6 两笔实际预算同时严格正

由 (38.20)，$R_d\xi_\lambda$ 的最后环境坐标恰为零，而 $E_d$ 的该坐标由 (38.18) 非零。又 $R_d\xi_\lambda$ 的环境首块为 $-dC^2u_\lambda/2\ne0$。因此 $R_d\xi_\lambda$ 与 $E_d$ 复线性独立；$S_d\xi_\lambda=z_dR_d\xi_\lambda+E_d$，故 $R_d\xi_\lambda,S_d\xi_\lambda$ 也复线性独立。

更明确地，复 Gram 行列式的二坐标子式展开，只取最后环境坐标与其余两个环境坐标，就给

$$
\begin{aligned}
B_{\phi_\lambda}(R_d,S_d)
&=\|R_d\xi_\lambda\|^2\|S_d\xi_\lambda\|^2
 -\bigl[\operatorname{Re}((R_d\xi_\lambda)^*S_d\xi_\lambda)\bigr]^2\\
&\ge\|R_d\xi_\lambda\|^2\|S_d\xi_\lambda\|^2
 -|(R_d\xi_\lambda)^*S_d\xi_\lambda|^2\\
&\ge\frac{\|C^2u_\lambda\|^2|(e_\lambda)_3|^2}{4}>0,
\qquad d=\pm1.
\end{aligned}
\tag{38.26}
$$

第二个不等式也可直接对 $R_d\xi_\lambda,E_d$ 作同一子式展开，因为增加 $z_dR_d\xi_\lambda$ 不改变这些子式。这个原预算下界适用于实际随 $\lambda$ 变化的全部列，无须另加探针扰动。

### 38.7 完整 P2 的精确共同区间与严格内点

归一化 Schur 矩阵及其有序谱基为

$$
C^{-1/2}HC^{-1/2}=2I_2+\beta J_A,\qquad
\beta=h/\sqrt2>0,\qquad
U_0=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

有 $U_0^*C^{-1/2}a_+=e_1$、$U_0^*C^{-1/2}a_-=e_2$。故原 P2 的精确逆矩阵坐标为

$$
\begin{aligned}
\mathsf K_+&=U_0^*C^{-1/2}(I_2+M_{2,+})C^{-1/2}U_0
 =\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix},\\
\mathsf K_-&=\begin{pmatrix}3/2&1/2\\1/2&3/2+\lambda^2\end{pmatrix},\qquad
\mathfrak d_\lambda=\det\mathsf K_\tau=2+(3/2)\lambda^2.
\end{aligned}
\tag{38.27}
$$

前卷 (30.29) 中 $\omega=1$，$Q_M=\mathsf K_\tau^{-1}$ 的非对角元是实数 $-1/(2\mathfrak d_\lambda)$。因此两份来源、两个取向都准确满足

$$
J=0,\qquad \Delta=\frac1{\mathfrak d_\lambda},\qquad
R=\frac{T_\lambda}{\mathfrak d_\lambda}.
$$

代入该完整原 P2 判据，所得恰是 (38.6)，包括两个端点。这是对完整正泛函的允许集，并非只检验所构造的向量泛函。

对于 $k>0$，$\rho=k/\lambda^2$ 严格在 (38.6) 内的充要条件为

$$
h^2\lambda^4>3k^2(\lambda^2+3/2).
\tag{38.28}
$$

固定 $h,k$ 后此式最终成立。具体地，$\lambda^2\ge3/2$ 时 $T_\lambda\le\sqrt3\lambda$，所以再取 $\lambda>\sqrt6\,k/h$ 就足够；对 $k\in[m,M]$ 将此界中的 $k$ 换成 $M$。P2 端点的非零尺度为 $\lambda^{-1}$，严格内点的残量尺度为 $\lambda^{-2}$。

### 38.8 两个取向、指定质量及结论边界

(38.1) 的两份来源和原 $T_A$ 全为实矩阵。逐项复共轭将 $\sigma=+1$ 的 $X_\lambda,\xi_\lambda$ 送到 $\sigma=-1$ 的实际 Hermitian 探针与实际向量，同时将 $i,\ell,a_{\rm act}$ 共轭，保持 $\alpha_d,\beta_d,\epsilon$ 不变。原 $R_d,S_d,L_{\rm PB}$ 的作用列也逐项共轭，所以 (38.25) 的实数值与 (38.26) 的两笔预算均保持不变。因此每份来源在两个取向都具有所需严格失败。

又 $\|u_\lambda\|=1$，故 $\xi_\lambda\ne0$。对任意指定 $\mu\in(0,\infty)$，取

$$
\widehat\xi_\lambda=\frac{\sqrt\mu}{\|\xi_\lambda\|}\xi_\lambda,\qquad
\widehat\phi_\lambda(A)=\widehat\xi_\lambda^*A\widehat\xi_\lambda.
\tag{38.29}
$$

则 $\widehat\phi_\lambda(I)=\mu$。正倍缩放使 PB 两端同倍变化、两笔预算同一个正数平方倍变化，故严格失败与两笔正预算同时保留。P2 的完整泛函判据不受此见证质量的选择影响。将有限个来源、取向及严格内点所需截止取最大值，完成定理 38.1 的全部量词；紧 $k$ 区间的统一版本由 (38.24)、(38.28) 给出。

实 Gram 变分、正交最小范数及 Schur 补沿前卷 §§27、30、31 的成熟背景使用；本节的显式接触 (38.8)–(38.11) 与原来源代入 (38.12)–(38.29) 给出具体的纸面加强。结论只把 $809/480$ 作为这组恢复轴见证的充分最终排除界，不判等号，不给必要性、最优常数或全部 PB 分类。它没有给出较小 $k$ 的 PB 成功证书，也没有给出共同 P2 内一份来源全部 PB 成功、另一份失败的成对分离。这里每个违反均属于有限矩阵、有限实际探针与同一实际正泛函；不涉及物理实现结论。

## 追加锚（本行以下为增补区）

## 39. 全接触矩消元、无界条带排除与增广轴扇区的完整分类

本节在 (37.19) 的完整可见图闭包中工作，保留 §38 的两份实际来源及其共同完整 P2 区间。所得结果是全闭包上的残量矩恒等式、一个不限制虚参数大小的条带下界、全部增广轴接触的参数化与最小阈值，以及条带外非轴接触的唯一可见列重构。这些结果把同一完整 P2 内的两来源 PB 分离问题缩到一个明确的非轴比较；该比较仍未解决。

### 39.1 原来源、接触约定与共同完整 P2

用 $r\in\{+1,-1\}$ 标来源符号，用 $d\in\{+1,-1\}$ 标两笔原预算。固定

$$
\begin{gathered}
C=\operatorname{diag}(1,2),\qquad T_A=\operatorname{diag}(1,-2),\qquad
J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
a_r=(1/\sqrt2,r)^{\mathsf T},\qquad
H=2C+hJ_A,\qquad B=H+C,\qquad \iota=\sigma i,\quad\sigma=\pm1.
\end{gathered}
\tag{39.1}
$$

除明确只谈代数恒等式的地方外，$h>0$ 始终固定在 §37.1 所要求的强制估计邻域中，因而 $H\succ0$，引理 37.4、定理 37.6 和推论 37.7、37.9 均可应用。条带定理另外要求 $h\le1/1000$；这项充分范围不改变其外的原问题。

对每个有限 $\lambda>0$，$D_{r,\lambda},F,G_{r,\lambda},t_{r,\lambda}$ 精确取 (38.1) 的实际矩阵，仅将来源下标 $\tau$ 改记为 $r$；特别地，仍有

$$
\delta_\lambda=\lambda^{-3},\qquad
G_{r,\lambda}=\begin{bmatrix}I_2\\\lambda a_r^*\end{bmatrix},\qquad
\rho=\frac{k}{\lambda^2}.
\tag{39.2}
$$

原 P2、PB、实际探针 $x=X\oplus0_3$ 和两笔预算准确取 (37.4)–(37.7)、(38.3)–(38.5) 的含义：$X=X^*$ 任意，正复线性泛函遍取完整 $M_5(\mathbb C)$，不删除环境或混合密度块。实际恒等式 (37.3)、(38.2) 给

$$
\begin{gathered}
D_{r,\lambda}\succ0,\qquad D_{r,\lambda}G_{r,\lambda}=F,\qquad W=0,\\
M_0=C^2,\qquad M_1=C,\qquad M_{2,r}=I_2+\lambda^2a_ra_r^*,\\
\|a_r\|^2=3/2,\qquad
\operatorname{spec}(M_{2,r})=\{1,1+(3/2)\lambda^2\}.
\end{gathered}
\tag{39.3}
$$

两份来源使用同一个 $\lambda$ 和同一个 $\rho$；不借重标度制造阈值差异。若改用 (37.54) 的共同全谱坐标，则两份来源的因子 $m=3/2$ 相同。

**定义 39.1（本节的完整接触域）。** 写

$$
\ell=b+\iota t,\qquad b,t\in\mathbb R,\qquad
A=|t|>1,\qquad \epsilon=-\operatorname{sign}(t).
$$

接触遍取 $u,p,q,a_{\rm act}\in\mathbb C^2$、$\eta\in\mathbb C$，其中 $\|u\|=1$，并要求

$$
\begin{gathered}
u^*p\in\mathbb R,\qquad (Cu)^*q\in\mathbb R,\qquad u^*q=p^*Cu,\\
a_{\rm act}=\iota(I_2-\ell C^{-1})p,\qquad
q=(\ell I_2+2C^{-1})p+\iota BCu,\\
\mathbf d_{\rm src}:=a_{\rm act}-Hu+\ell C^2u/2=\eta a_r.
\end{gathered}
\tag{39.4}
$$

这正是 (37.15)、(37.19)，包括两条演员轴；$A=-\epsilon\operatorname{Im}_\iota\ell$。向量 $\mathbf d_{\rm src}$ 专指来源需求，不用它的记号表示矩差。置

$$
\begin{gathered}
v=a_{\rm act}-\iota p=-\iota\ell C^{-1}p,\qquad
\zeta=\operatorname{Re}(v^*T_Au),\qquad s(A)=\frac{2A}{A^2-1},\\
J_k=s(A)|\eta|^2+4\epsilon k\zeta,\qquad
\mathcal R(c)=\frac{s(A)|\eta|^2}{4|\zeta|}\quad(\zeta\ne0).
\end{gathered}
\tag{39.5}
$$

比值 $\mathcal R$ 是无符号量。它在 $k>0$ 下只有对 $\epsilon\zeta<0$ 的接触才是失效阈值；$\epsilon\zeta>0$ 时一次项为正。由引理 37.4，所有这些接触均有 $\eta\ne0$。

共同 P2 在这里仍是完整泛函判据的结果。具体地，令 $\beta=h/\sqrt2$、$U_0=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。由于 $U_0^*C^{-1/2}a_+=e_1$、$U_0^*C^{-1/2}a_-=e_2$，原钉版前卷 (30.29) 的逆坐标矩阵恰为

$$
\mathsf K_+=\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix},\qquad
\mathsf K_-=\begin{pmatrix}3/2&1/2\\1/2&3/2+\lambda^2\end{pmatrix}.
\tag{39.6}
$$

其共同行列式为 $\mathfrak d_\lambda=2+(3/2)\lambda^2$，逆矩阵的非对角元为实数。在 (30.29) 中，$\omega=1$、$J=0$、$\Delta=1/\mathfrak d_\lambda$、$R=T_\lambda/\mathfrak d_\lambda$，其中 $T_\lambda=\sqrt{(3/2)(3/2+\lambda^2)}$。因此两来源、两取向的完整原 P2 集合均为

$$
I_{r,\sigma}=\left[-\frac{\beta}{T_\lambda},\frac{\beta}{T_\lambda}\right].
\qquad
\frac{k}{\lambda^2}\in\operatorname{int}I_{r,\sigma}
\quad\Longleftrightarrow\quad
h^2\lambda^4>3k^2(\lambda^2+3/2).
\tag{39.7}
$$

此处等价式适用于任意实 $k$；固定 $h>0,k$ 后最终成立。以上直接复用 (38.27)–(38.28) 及其完整 P2 来源，不用 $M_2$ 的谱或某一个向量测试代替它。

### 39.2 包括两轴的全闭包矩消元

**引理 39.2（残量配对的全闭包恒等式）。** 对每个 (39.4) 接触，定义实矩

$$
\begin{gathered}
m_j=|u_j|^2,\qquad \overline{u_1}u_2=x+\iota y,\qquad
m_1+m_2=1,\quad x^2+y^2=m_1m_2,\\
\overline{u_1}p_1=P_1+\iota Z,\qquad
\overline{u_2}p_2=P_2-\iota Z,\qquad
S=P_1+P_2,\qquad \Delta_P=P_1-P_2,\\
L=m_1+4m_2+hx,\qquad N=3m_1+24m_2+4hx.
\end{gathered}
\tag{39.8}
$$

同一个实数 $Z$ 存在，因为 $u^*p$ 为实数。则

$$
\boxed{\quad
 tS=-3L,\qquad \Delta_P=hy-bS,\qquad
 bZ=t(P_1+2P_2)+N.\quad}
\tag{39.9}
$$

特别地，原残量配对准确消去可见列，成为

$$
\boxed{\quad
\zeta=t\Delta_P+2bZ=3tS+2N
      =-3m_1+12m_2-hx
      =2bZ+3bL+thy.\quad}
\tag{39.10}
$$

这些恒等式不要求 $b\ne0$ 或 $u_1u_2\ne0$。它们消去的是配对值中的列变量；哪些 $u,\ell$ 真正满足来源条件，仍受 (39.4) 限制。

证明。由 $B=3C+hJ_A$ 直接有

$$
 u^*BCu=3m_1+12m_2+3hx+\iota hy=3L+\iota hy,
 \qquad (Cu)^*BCu=N.
$$

对第二条演员接触等式分别左乘 $u^*$、$(Cu)^*$。第一式给

$$
\begin{aligned}
u^*q
 &=\ell S+2P_1+P_2+\iota Z+3\iota L-hy,\\
p^*Cu&=P_1+2P_2+\iota Z.
\end{aligned}
$$

比较实部与 $\iota$ 虚系数，即得 $\Delta_P=hy-bS$ 和 $tS=-3L$。第二式给

$$
(Cu)^*q=\ell(P_1+2P_2-\iota Z)+2S+\iota N.
$$

其虚系数为零，正是 $bZ=t(P_1+2P_2)+N$。

最后，$C^{-1}T_A=\operatorname{diag}(1,-1)$，而
$p^*C^{-1}T_Au=\Delta_P-2\iota Z$。所以

$$
\zeta=\operatorname{Re}\bigl(\iota\overline\ell
          (\Delta_P-2\iota Z)\bigr)=t\Delta_P+2bZ.
$$

把 (39.9) 代入，先得 $3tS+2N=-9L+2N=-3m_1+12m_2-hx$；另用 $t\Delta_P=thy-tbS=thy+3bL$，得到最后一种表达。整个推导没有除以演员坐标，故同时覆盖增广轴点。∎

### 39.3 不限制虚参数的整个条带下界

**定理 39.3（全接触的无界条带排除）。** 在 §37 的上述 $h$ 邻域中再取

$$
0<h\le\frac1{1000},\qquad |b|\le\frac1{2000},\qquad A=|t|>1.
\tag{39.11}
$$

对任一来源 $r=\pm1$、任一取向和相应合法符号的每个接触，若 $\zeta\ne0$，则

$$
\mathcal R(c)>\frac{50}{27}>\frac{809}{480}.
\tag{39.12}
$$

包括 $\zeta=0$ 的全部此类接触，都在 $0\le k\le809/480$ 上满足 $J_k>0$。这里没有对 $A$ 设置上界。

证明。只用第一条演员接触和来源需求，令

$$
E=H-C^3/2=\operatorname{diag}(3/2,0)+hJ_A,\qquad
R=C(C-\ell I_2)^{-1}.
$$

由于 $|t|>1$，每个 $c_j-\ell$ 都非零，其中 $c_1=1,c_2=2$。求解 $\iota(I_2-\ell C^{-1})p=Hu-\ell C^2u/2+\eta a_r$，准确得到

$$
p=-\frac{\iota}{2}C^3u-\iota R(Eu+\eta a_r).
\tag{39.13}
$$

所用分解是 $R(H-\ell C^2/2)=C^3/2+RE$。取 $u^*p$ 的虚系数为零，得

$$
\operatorname{Re}(\eta u^*Ra_r)
 =-\frac12u^*C^3u-\operatorname{Re}(u^*REu).
\tag{39.14}
$$

下文的向量范数为 Euclidean 范数，矩阵范数为其算子范数。对 $|b|\le1/2000$，

$$
\operatorname{Re}\frac{c_j}{c_j-b-\iota t}
 =\frac{c_j(c_j-b)}{(c_j-b)^2+t^2}>0,\qquad
\|R\|\le\frac2A.
$$

因此 $E$ 的对角部分对 $\operatorname{Re}(u^*REu)$ 的贡献非负，非对角部分则不小于 $-h\|R\|\|u\|\|J_Au\|\ge-2h/A$。又 $u^*C^3u/2\ge1/2$。由 (39.14)，其右侧严格为负，并有

$$
\begin{gathered}
|\eta|\,|u^*Ra_r|\ge\frac12-\frac{2h}{A}\ge\frac12-2h,\\
|u^*Ra_r|\le\|Ra_r\|\le\frac{\|Ca_r\|}{A}
 =\frac{3}{\sqrt2 A},\\
v_\eta:=\frac{|\eta|}{A}
 \ge\frac{\sqrt2}{3}\left(\frac12-2h\right)
 \ge\frac{83\sqrt2}{500}>\frac15.
\end{gathered}
\tag{39.15}
$$

这里 $\|Ca_r\|^2=1/2+4=9/2$ 对两个来源相同；最后的严格不等式等价于 $2\cdot83^2>100^2$。式 (39.15) 对所有 $A>1$ 有效，没有先把 $A$ 限在紧区间。

同一精确列恒等式 (39.13) 还给

$$
\begin{aligned}
\|p\|
&\le\frac12\|C^3\|+\|R\|\|E\|
        +|\eta|\,\|Ra_r\|\\
&\le4+\frac{2(3/2+h)}{A}+\frac{3}{\sqrt2}v_\eta
 \le7+2h+3v_\eta.
\end{aligned}
\tag{39.16}
$$

由 (39.8)，$|x|,|y|\le1/2$、$|L|\le4+h/2$，并且

$$
2|Z|\le|\overline{u_1}p_1|+|\overline{u_2}p_2|
 \le\|u\|\|p\|=\|p\|.
$$

将这些界用于 (39.10) 的最后一式，得到

$$
\begin{aligned}
|\zeta|
&\le\frac{Ah}{2}+|b|\bigl(\|p\|+3|L|\bigr)\\
&\le\frac{Ah}{2}+|b|\left(19+\frac72h+3v_\eta\right)\\
&\le\frac{Ah}{2}+|b|(20+3v_\eta)\\
&\le A\left[\frac h2+|b|(20+3v_\eta)\right].
\end{aligned}
\tag{39.17}
$$

倒数使用时，方括号严格正，因为 $h>0$。对 $\zeta\ne0$，由 $|\eta|=Av_\eta$ 得

$$
\mathcal R(c)
 \ge\frac{A^2v_\eta^2}
 {2(A^2-1)[h/2+|b|(20+3v_\eta)]}
 >\frac{v_\eta^2}{2[h/2+|b|(20+3v_\eta)]}.
\tag{39.18}
$$

为合法代入 $v_\eta>1/5$，置 $c_0=h/2+20|b|>0$、$d_0=3|b|\ge0$。函数 $v^2/(c_0+d_0v)$ 在 $v>0$ 上严格递增，因为其导数是 $v(2c_0+d_0v)/(c_0+d_0v)^2>0$。再对 $h,|b|$ 用各自上界，得

$$
\mathcal R(c)>
\frac{1/25}{2[1/2000+(1/2000)(20+3/5)]}
 =\frac{1/25}{2[1/2000+103/10000]}
 =\frac{50}{27}.
\tag{39.19}
$$

由于 $50\cdot480=24000>21843=809\cdot27$，(39.12) 成立。对任意合法 $\epsilon$ 及 $0\le k\le809/480$，
$J_k\ge4|\zeta|(\mathcal R(c)-k)>0$。若 $\zeta=0$，不能用比值，但引理 37.4 给 $\eta\ne0$，故 $J_k=s(A)|\eta|^2>0$。这完成包括零配对分支的证明。∎

该定理对一个完整无界条带给下界，而非从选定接触给阈值上界。它只排除条带内的接触作为所列 $k$ 范围的失效原因，不能把条带外未验的接触一起判为正。

### 39.4 全部增广轴接触及实际轴子集

**定理 39.4（两条增广轴的完整参数化）。** 固定 $j\in\{1,2\}$、$l\ne j$，写 $u=ze_j$、$|z|=1$。对每个 $t\in\mathbb R$、$|t|>1$，该轴上的全部 (39.4) 接触准确由下列公式给出：

$$
\begin{gathered}
b=c_j-2/c_j=2c_j-3,\qquad \ell=b+\iota t,\qquad
\epsilon=-\operatorname{sign}(t),\\
p_j=-\frac{3c_j^2}{t}z,\qquad q_j=c_jp_j,\\
\delta_j(t)=-5c_j+\frac{(2c_j-3)c_j^2}{2}
       +\iota\left(\frac{tc_j^2}{2}-\frac6t\right),\qquad
\eta=\frac{z\delta_j(t)}{(a_r)_j},\\
p_l=\frac{hz+\eta(a_r)_l}{\iota(1-\ell/c_l)},\qquad
q_l=(\ell+2/c_l)p_l+\iota h c_jz,\qquad
a_{\rm act}=\iota(I_2-\ell C^{-1})p.
\end{gathered}
\tag{39.20}
$$

在两轴上分别有

$$
\begin{gathered}
j=1:\quad b=-1,\quad
\delta_1(t)=-11/2+\iota(t/2-6/t),\quad\zeta=-3,\\
j=2:\quad b=1,\quad
\delta_2(t)=-8+\iota(2t-6/t),\quad\zeta=12.
\end{gathered}
\tag{39.21}
$$

参数化包括每个来源符号和每个取向。所有分母非零：$t\ne0$、$(a_r)_j\ne0$，且 $1-\ell/c_l\ne0$ 由 $t\ne0$ 保证。

证明。引理 37.2 在 $u=ze_j$ 上恰要求 $w=p_j/z\in\mathbb R$、$q_j=c_jp_j$，对 $p_l,q_l$ 不另加限制。接触的第 $j$ 个 $q$ 坐标成为

$$
(\ell+2/c_j-c_j)w+3\iota c_j^2=0.
$$

其虚系数给 $tw=-3c_j^2$，所以 $w\ne0$；实部遂给 $b=c_j-2/c_j$。在 $c_j=1,2$ 上，这正是 $b=2c_j-3$。第 $j$ 个需求坐标除以 $z$ 为

$$
\iota(1-\ell/c_j)w-2c_j+\ell c_j^2/2
=-5c_j+bc_j^2/2+\iota(tc_j^2/2-6/t),
$$

给出 $\delta_j$ 和 $\eta$。在另一坐标，$u_l=0$、$(Hu)_l=hz$，需求等式准确给出 (39.20) 的 $p_l$；再用第二条演员接触给 $q_l$。这是必要性。

反之，取任意所列 $t,z$ 并按公式定义。第 $j$ 个接触方程由上面的实、虚等式成立；两需求坐标分别为 $z\delta_j=\eta(a_r)_j$ 和 $\eta(a_r)_l$。$p_j/z$ 为实数且 $q_j=c_jp_j$，所以全部闭包条件成立；其余接触等式按定义成立。这证明充分性。最后把 $m_j=1$、$x=0$ 代入 (39.10)，得到两个 $\zeta$ 值。∎

增广轴与实际轴仍须区分。对同一个有限实际 $X$，$Cu=c_ju$ 强制整列 $q=c_jp$；闭包只强制该等式的第 $j$ 个坐标。因此 (39.20) 给实际轴接触当且仅当

$$
q_l=c_jp_l
\quad\Longleftrightarrow\quad
\ell p_l+\iota h c_jz=0.
\tag{39.22}
$$

这里用了 $2/c_l=c_j$。此条件也充分：取 $X_{jj}=p_j/z\in\mathbb R$、$X_{lj}=p_l/z$、$X_{jl}=\overline{X_{lj}}$，令 $X_{ll}$ 任意实数，便有 $Xu=p$、$XCu=q$。没有通过 (39.22) 的增广轴点依然由定理 37.6 恢复为实际趋轴探针；不能把它们删出接触比较，也不能称它们本身为有限实际轴探针。

### 39.5 整个轴扇区的代价、唯一尺度极小值与公共排除界

**定理 39.5（完整增广轴阈值）。** 在任一来源与取向下，(39.20) 的无符号比值分别为

$$
\mathcal R_1(A)=\frac{A^4+97A^2+144}{12A(A^2-1)},\qquad
\mathcal R_2(A)=\frac{A^4+10A^2+9}{6A(A^2-1)},\qquad A>1.
\tag{39.23}
$$

它们不依赖 $h,r,z$。对两个合法符号，各自准确的代价为

$$
J_k\big|_{e_1}=12[\mathcal R_1(A)-\epsilon k],\qquad
J_k\big|_{e_2}=48[\mathcal R_2(A)+\epsilon k].
\tag{39.24}
$$

令 $\xi>1$ 是多项式

$$
P(X)=X^3-13X^2-37X+9
\tag{39.25}
$$

的唯一大于 $1$ 的根，则整个增广轴扇区对正残量的阈值为

$$
\boxed{\quad
K_{\rm ax}=\min_{A>1}\mathcal R_2(A)
 =\frac{\xi^2+10\xi+9}{6\sqrt\xi(\xi-1)}
 <\frac{85}{72}<\frac32.\quad}
\tag{39.26}
$$

唯一的极小尺度是第二轴上的 $A=\sqrt\xi$；轴相位 $z$ 仍可任取。对 $k\ge0$，第一轴的不利符号是 $\epsilon=+1,t=-A$，第二轴是不利符号 $\epsilon=-1,t=A$；相反符号的代价严格正。故 $0\le k<K_{\rm ax}$ 时全部轴接触严格正；$k=K_{\rm ax}$ 时全部轴接触非负，零值恰在第二轴不利符号与该极小尺度；$k>K_{\rm ax}$ 时已有严格负轴接触。这是轴扇区分类，不是完整接触域的最优值断言。

证明。由 (39.20)–(39.21)，

$$
\begin{aligned}
|\eta|^2\big|_{e_1}
 &=2\left[\frac{121}{4}+(t/2-6/t)^2\right]
 =\frac12\left(A^2+97+\frac{144}{A^2}\right),\\
|\eta|^2\big|_{e_2}
 &=64+(2t-6/t)^2
 =4A^2+40+\frac{36}{A^2}.
\end{aligned}
$$

将其代入 $s(A)|\eta|^2/(4|\zeta|)$ 就是 (39.23)；再用 $\zeta=-3,12$ 得 (39.24)。因此符号选择和正斜率分支也全部确定。

第一轴在所有尺度都高于 $3/2$，因为

$$
\begin{aligned}
&A^4+97A^2+144-18A(A^2-1)\\
&\qquad=A^2(A-9)^2+16A^2+18A+144>0.
\end{aligned}
\tag{39.27}
$$

第二轴满足 $\mathcal R_2(4)=85/72<3/2$，所以整个轴扇区的最低值只能来自第二轴。为确定全部尺度而非仅选一个见证，直接求导：

$$
\mathcal R_2'(A)=
\frac{A^6-13A^4-37A^2+9}{6(A^3-A)^2}
=\frac{P(A^2)}{6(A^3-A)^2}.
\tag{39.28}
$$

$P(1)=-40$，而 $P(X)\to+\infty$。其导数 $P'(X)=3X^2-26X-37$ 的两个根为 $(13\pm2\sqrt{70})/3$；一根为负，另一根 $X_0>1$。所以 $P$ 在 $(1,X_0)$ 严格递减，从负值出发；在 $(X_0,\infty)$ 严格递增到正无穷。由连续性，恰有一个根 $\xi>1$。又 $P(16)=185>0$，故 $\xi<16$。式 (39.28) 于是说明 $\mathcal R_2$ 在 $(1,\sqrt\xi)$ 严格递减，在 $(\sqrt\xi,\infty)$ 严格递增；其在 $A\downarrow1$ 与 $A\to\infty$ 两端都趋于正无穷。唯一全局极小尺度及公式 (39.26) 得证。由于 $\sqrt\xi<4$，极小值严格小于 $\mathcal R_2(4)=85/72$。结合第一轴的严格下界和 (39.24)，便得全部轴代价的符号分类。∎

对负 $k$，(39.24) 同样给阈值 $K_{\rm ax}$，不利符号同时反转。在临界 $|k|=K_{\rm ax}$，这里仅得零领先代价；恢复定理没有判定其有限 $\lambda$ 次阶符号。

### 39.6 非轴且实部非零时的唯一可见列与来源残余方程

**命题 39.6（列重构的必要性与充分性）。** 给定任意 $\|u\|=1$、$u_1u_2\ne0$、$\ell=b+\iota t$，其中 $|t|>1,b\ne0$。从 $u$ 定义 (39.8) 的 $m_j,x,y,L,N$，然后依次置

$$
\begin{gathered}
S=-\frac{3L}{t},\qquad
\Delta_P=hy-bS,\qquad
P_1=\frac{S+\Delta_P}{2},\qquad P_2=\frac{S-\Delta_P}{2},\\
Z=\frac{-3(3+b)L-thy+2N}{2b},\\
p_1=\frac{P_1+\iota Z}{\overline{u_1}},\qquad
p_2=\frac{P_2-\iota Z}{\overline{u_2}},\\
q=(\ell I_2+2C^{-1})p+\iota BCu,\qquad
a_{\rm act}=\iota(I_2-\ell C^{-1})p,\\
\mathbf d_{\rm src}=\iota(I_2-\ell C^{-1})p-Hu+\ell C^2u/2.
\end{gathered}
\tag{39.29}
$$

则这是一对满足可见图条件和两条演员接触等式的唯一列 $p,q$。它们来自唯一实际 Hermitian 矩阵

$$
X=[p\ q][u\ Cu]^{-1}.
\tag{39.30}
$$

对于指定来源 $a_r$，剩余条件准确是单个复标量方程

$$
\boxed{\quad
(\mathbf d_{\rm src})_2=r\sqrt2(\mathbf d_{\rm src})_1,\qquad
\eta=\sqrt2(\mathbf d_{\rm src})_1.\quad}
\tag{39.31}
$$

第一个等式等价于两个实方程，不因列消元而自动成立。满足它当且仅当 (39.29) 产生该来源的接触，此时 $\eta\ne0$，合法符号是 $\epsilon=-\operatorname{sign}(t)$。

证明。$t\ne0$、$b\ne0$、$u_1u_2\ne0$ 逐一保证了 (39.29) 的所有除法合法。若一个接触存在，引理 39.2 先唯一确定 $S,\Delta_P,P_1,P_2$，再由

$$
\begin{aligned}
2bZ
 &=3tS-t\Delta_P+2N\\
 &=3tS-thy+tbS+2N
 =-3(3+b)L-thy+2N
\end{aligned}
$$

唯一确定 $Z$，继而唯一确定 $p$ 和 $q$。这证明必要性及唯一性。

反向地，按 (39.29) 定义后，$u^*p=S\in\mathbb R$。上面的 $Z$ 公式给回第三条 (39.9)，其余两条按定义成立。引理 39.2 证明中关于 $u^*q-p^*Cu$ 的实部、虚系数及 $(Cu)^*q$ 虚系数的计算均可逆，因此这三式正好给回全部 (39.4) 的图条件。非轴时 $[u\ Cu]$ 可逆；引理 37.2 于是给 (39.30) 的 Hermitian 性和两列的实际实现。两条演员接触由 $q,a_{\rm act}$ 的定义成立。

最后，$\mathbf d_{\rm src}=\eta(1/\sqrt2,r)^{\mathsf T}$ 等价于 (39.31)，因为第一来源坐标 $1/\sqrt2$ 非零。若满足 (39.31) 却有 $\eta=0$，两个需求坐标都为零，与引理 37.4 在这些图条件和演员接触下的零需求排除矛盾。所以它准确给出来源条件，没有引入伪零需求解。∎

列重构去掉了自由的 $p,q,X$，并未求解 (39.31)，也未给所有满足该方程的 $u,b,t$ 上的代价下界。定理 39.3 的作用是：在其 $h$ 范围及原定 $k$ 范围内，可能影响符号的接触不在 $|b|\le1/2000$，因而非轴部分可合法使用这里的 $1/b$ 公式。未满足条带定理的 $h$ 不因此排除 $b=0$。

### 39.7 同一实来源的两种对称性

**命题 39.7（取向等价与正负残量阈值等价）。** 对每个固定 $a_r,h$，两个取向的 (37.50) 阈值相同；同一取向的正、负残量阈值也相同。记其共同值为 $K_r(h)$。这些等价保持来源符号 $r$，不建立 $K_+(h)=K_-(h)$。

证明。首先同时取复共轭，并将 $\iota$ 改为 $-\iota$：

$$
(\iota,u,p,q,\ell,a_{\rm act},\eta,\epsilon)
\longmapsto
(-\iota,\overline u,\overline p,\overline q,
 \overline\ell,\overline{a_{\rm act}},\overline\eta,\epsilon).
\tag{39.32}
$$

由于 $C,H,B,T_A,a_r$ 均为实矩阵或实向量，(39.4) 逐项共轭后仍为同一来源在另一取向的接触。$\operatorname{Im}_{-\iota}\overline\ell=\operatorname{Im}_\iota\ell=t$，故 $A,\epsilon$ 保留；$v$ 变为 $\overline v$，从而 $|\eta|,\zeta,J_k$ 全部保留。此双射给两取向的阈值等价。

其次，固定 $\iota$，作

$$
(u,p,q,\ell,a_{\rm act},\eta,\epsilon)
\longmapsto
(\overline u,-\overline p,-\overline q,
 \overline\ell,\overline{a_{\rm act}},\overline\eta,-\epsilon).
\tag{39.33}
$$

图的两个实配对成为原实配对的负共轭，交叉等式两边也同取负共轭，所以图条件保留。第一演员等式满足
$\iota(I_2-\overline\ell C^{-1})(-\overline p)=\overline{a_{\rm act}}$；第二演员等式满足
$-\overline q=(\overline\ell I_2+2C^{-1})(-\overline p)+\iota BC\overline u$；需求等式是原式的共轭。$t$ 和 $\epsilon$ 同时反号，故 $A$ 保留，且 $v$ 再次变为 $\overline v$。因此 $|\eta|,\zeta$ 保留，但新的 $J_k$ 是原来的 $J_{-k}$。它在 (37.50) 的两个带方向接触集合之间给保持比值的双射，证明正负阈值相同。两种操作都没有将 $a_r$ 变为 $a_{-r}$；不能将同源对称性用作来源对之间的等价证明。∎

### 39.8 原有限阶段后果与剩余的同完整 P2 比较

**推论 39.8（公共更强排除与必要搜索范围）。** 对每个固定的 §37 合法 $h>0$、每个固定 $k>K_{\rm ax}$，(39.2) 的两个来源在两个取向都于所有充分大的有限 $\lambda$ 上严格违反原 PB，且同一个 $\rho=k/\lambda^2$ 严格处于它们共同完整 P2 区间内。每个失败都有同一实际探针与同一原正泛函承担的两笔严格正预算，且质量可任取指定有限 $\mu>0$。因此

$$
K_r(h)\le K_{\rm ax}<\frac{85}{72}<\frac{809}{480},\qquad r=\pm1.
\tag{39.34}
$$

所以对于这对来源，固定正 $k$ 的最终 PB 成功／失败分离只能继续在

$$
0<k\le K_{\rm ax}
\tag{39.35}
$$

寻找。这是必要搜索范围，不是成功区域。

证明。固定 $k>K_{\rm ax}$，在任一来源及取向上取定理 39.4 的第二轴接触，令 $t=\sqrt\xi$、$\epsilon=-1$、任取 $|z|=1$。定理 39.5 给
$J_k=48(K_{\rm ax}-k)<0$。如果该轴接触不满足 (39.22)，仍可直接应用定理 37.6 的趋轴恢复；若它已有实际轴实现，则用该定理的实际分支。因此推论 37.7 精确给 (39.2) 上最终的有限实际 PB 失败、两笔严格正预算及任意指定正有限质量。它不要求增广轴点本身有有限轴上实现。两个来源、两个取向只有有限种选择，可将各自有限截止取最大值。

完整 P2 的严格内部身份由 (39.7) 给出，固定 $h,k$ 后再扩大有限截止即可。阈值上界亦可直接由第二轴极小接触代入 (37.50) 得到；$85/72<809/480$ 由交叉相乘成立。因此超过 $K_{\rm ax}$ 的每个固定正 $k$ 都使两来源最终失败，不能支持一成一败的目标。没有对随 $\lambda$ 变动的 $k$ 或临界等号给出额外结论。∎

若再有 $0<h\le1/1000$，则对 (39.35) 的每个固定 $k$，定理 39.3 排除了整个 $|b|\le1/2000$ 条带。定理 39.5 已经完整结算轴扇区的领先代价。除显式保留的 $k=K_{\rm ax}$ 轴零值外，剩余的来源差异比较准确落在

$$
\begin{gathered}
\|u\|=1,\qquad u_1u_2\ne0,\qquad
|b|>1/2000,\qquad |t|>1,\qquad
\epsilon=-\operatorname{sign}(t),\\
(\mathbf d_{\rm src}(u,b,t;h))_2
   =r\sqrt2(\mathbf d_{\rm src}(u,b,t;h))_1,
\end{gathered}
\tag{39.36}
$$

其中所有列和 $\eta$ 按 (39.29)–(39.31) 唯一恢复，$\zeta=-3|u_1|^2+12|u_2|^2-h\operatorname{Re}(\overline{u_1}u_2)$。没有对剩余的 $b,t$ 施加有界性假设。

沿推论 37.9 的严格接触路线得到原目标中的分离，需要在同一固定 $h$ 和同一固定 $k$ 上，对某一来源的每个剩余接触证明 $J_k>0$，同时对另一来源给出 $J_k<0$ 的接触；前者与已处理扇区一起给全部原 PB 的最终成功，后者经推论 37.7 给最终失败。这是足够的严格判据；含零领先值时须另证有限阶段符号。对 $k<K_{\rm ax}$，轴接触已经逐点严格正；在 $k=K_{\rm ax}$，轴零值另有有限阶段次阶义务，不能直接用严格充分性。另一条可能路线是证明两个完整阈值相等；本节未建立这样的等式。只控制若干接触、只求出列、或只验证 (39.31) 的部分解，均不支付前述全称下界。

原目标仍是同一完整 P2 允许参数上的全部 PB 成功／失败分离，而不是仅同谱、仅必要接触检验或仅充分失败。本节没有给任一来源的新全称成功证书，没有证明两来源阈值严格不等或相等，也没有证明这对来源的结构性不可能。原问题在 §37 合法而不满足 $h\le1/1000$ 的范围内保持原样；本节的数值条带排除不外推到那里。阈值等号和 $J_k=0$ 的有限 $\lambda$ 次阶符号仍未解决。

### 39.9 数学引用与适用边界

实际来源、完整原量词和原带符号代价取 (35.5)、(37.2)–(37.7)、(38.1)–(38.5)；可见图和零需求排除分别用引理 37.2、37.4；从增广接触到原有限探针、两笔正预算和任意正有限质量的桥梁为定理 37.6、推论 37.7。推论 37.9 的前提仍是每个接触严格正。共同完整 P2 的代入见[前卷 §30](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30-零模耦合为零的三矩实现与最小真实环境) 在钉版 `315e167044afd2593b851f6546a82470ca16d446` 的 (30.29) 及本卷 (38.27)–(38.28)，其判据保留必要性与充分性。

(39.9)–(39.10) 的矩消元、定理 39.3 的无界条带估计、定理 39.4–39.5 的完整轴分类和命题 39.6 的非轴列重构使用基本 Hermitian 线性代数、Cauchy–Schwarz、算子范数、正定 Schur 补和一元微分。轴最优值只属于轴扇区，条带排除只在 (39.11) 的范围内成立；完整非轴来源比较与临界零值的有限阶段符号仍为未解问题。

## 追加锚（本行以下为增补区）

## 40. 两个固定实来源的精确有限接触稠密性

本节区分两种恢复。定理 37.6 在同一实际来源上恢复趋于接触的有限原测试；这里则在每一步精确满足来源需求及两条演员接触等式，并精确保留可见 Hermitian 图条件。允许 $\ell,\eta$ 随恢复变化，来源 $a_r$、$h$、取向和绝对值符号均固定。有限矩阵 $X$ 不要求一致有界。

### 40.1 接触域、拓扑与结论

**定义 40.1（精确有限接触子集）。** 固定 $r\in\{+1,-1\}$、$0<h<2\sqrt2$ 和 $\iota\in\{i,-i\}$，取 (39.1) 的 $C,H,B,T_A,a_r$。令 $\mathcal C_\iota(a_r;h)$ 为 (39.4) 的全部接触，仍要求 $\|u\|=1$、$A=-\epsilon\operatorname{Im}_\iota\ell>1$；令

$$
\mathcal C^{\rm fin}_\iota(a_r;h)=
\{c\in\mathcal C_\iota(a_r;h):\quad
 p=Xu,\ q=XCu\ \text{对某个有限 }X=X^*\in M_2(\mathbb C)\}.
\tag{40.1}
$$

拓扑为 $(u,p,q,a_{\rm act},\ell,\eta)$ 的通常有限维拓扑和 $\epsilon$ 的离散拓扑。代价 $J_k$ 仍取 (39.5)，$k\in\mathbb R$。本节的 $h$ 范围只保证原来源的 $H\succ0$，不要求 §37 的强制估计邻域；以下稠密性证明不使用引理 37.4 或定理 37.5。

**定理 40.2（同来源、同符号的精确接触稠密性）。** 对定义 40.1 的每个固定来源、$h$ 和取向：

1. 每个没有有限 Hermitian 实现的增广轴接触 $c_0$ 都是一条实解析曲线 $c(s)$ 的极限，其中 $c(0)=c_0$，且对所有充分小的非零实 $s$，$c(s)\in\mathcal C^{\rm fin}_\iota(a_r;h)$、$u_1(s)u_2(s)\ne0$。曲线上 $a_r,h,\epsilon,\iota$ 固定，全部 (39.4) 方程精确成立；$\ell(s),\eta(s)$ 及全部可见列趋于其指定值。
2. 每个增广接触或已属于 $\mathcal C^{\rm fin}_\iota(a_r;h)$，或具有第 1 项的恢复。因此在接触域的相对拓扑中，

   $$
   \overline{\mathcal C^{\rm fin}_\iota(a_r;h)}^{\,\mathcal C_\iota(a_r;h)}
    =\mathcal C_\iota(a_r;h),\qquad
   \inf_{\mathcal C^{\rm fin}_\iota(a_r;h)}J_k
    =\inf_{\mathcal C_\iota(a_r;h)}J_k
    \quad(k\in\mathbb R).
   \tag{40.2}
   $$

   下确界按扩展实数解释，空集下确界为 $+\infty$。
3. 在第 1 项的恢复中，若 $j$ 是原轴、$l\ne j$、$d=c_l-c_j$，$c_1=1,c_2=2$，则可取参数使

   $$
   X_{ll}(s)=\frac1{ds}+O(1)\qquad(s\to0,\ s\ne0).
   \tag{40.3}
   $$

   每个 $X(s)$ 有限而其范数无一致上界。已具有有限实现的退化轴点只需保持原接触；本定理不要求在这些点作非轴恢复。

### 40.2 轴坐标、相位与退化分支

先证 $\iota=i$。用 (39.4) 消去 $q,a_{\rm act}$，将来源方程写成两个复方程

$$
E=i(I_2-\ell C^{-1})p-Hu+\ell C^2u/2-\eta a_r=0,
\qquad q=(\ell I_2+2C^{-1})p+iBCu.
\tag{40.4}
$$

它们与 (37.15) 的四个实图条件共为八个实方程。若轴点为 $u=z_0e_j$、$|z_0|=1$，同时将 $u,p,q,a_{\rm act},\eta$ 乘以 $\overline{z_0}$，而保持 $\ell,\epsilon$，即可化为 $u=e_j$。此操作逐项保留来源方程、全部接触和 $J_k$，也保留实际矩阵 $X$；构造完成后乘回 $z_0$。因此只需在 $e_j$ 附近处理。

固定 $l\ne j$，在轴附近取实解析坐标

$$
u_j=\sqrt{1-|z|^2},\qquad u_l=z,\qquad |z|<1.
\tag{40.5}
$$

这里固定的是全局相位；$z$ 为横向复坐标。在基点用下标 $0$ 标记 $\ell_0,\eta_0$，并写

$$
p_j=x\in\mathbb R,\qquad q_j=c_jx,\qquad
p_l=\pi,\qquad q_l=\chi,\qquad w=\chi-c_j\pi.
\tag{40.6}
$$

这些轴图条件正是引理 37.2 的代数结论，不使用小 $h$ 估计。由 $q$ 的占据坐标公式，

$$
(\ell_0+2/c_j-c_j)x+3ic_j^2=0.
\tag{40.7}
$$

故 $x\ne0$。写 $t_0=\operatorname{Im}\ell_0$，则

$$
\operatorname{Re}\ell_0=c_j-2/c_j,\qquad
|t_0|>1,\qquad x=-3c_j^2/t_0,\qquad
D_m:=i(1-\ell_0/c_m)\ne0\quad(m=j,l).
\tag{40.8}
$$

最后一个非零性由 $t_0\ne0$ 得到，且 $a_j:=(a_r)_j\ne0$、$a_l:=(a_r)_l\ne0$。

若 $w=0$，则 $q=c_jp$，直接取

$$
X_{jj}=x,\qquad X_{lj}=\pi,\qquad
X_{jl}=\overline\pi,\qquad X_{ll}\in\mathbb R
\tag{40.9}
$$

便有 $X=X^*$、$Xu=p$、$XCu=q$。反过来，在轴上 $Cu=c_ju$ 使任一实际矩阵都必须满足 $q=c_jp$，即 $w=0$。因此 $w=0$ 恰是已经实际的轴分支，以下只须恢复 $w\ne0$ 的点。

### 40.3 固定实际来源后的完整导数

将十个实未知量写成五个复变量 $(z,p_j,p_l,\ell,\eta)$。在基点的变化记为

$$
Z=\dot z,\qquad P=\dot p_j,\qquad T=\dot p_l,
\qquad m=\dot\ell,\qquad n=\dot\eta.
\tag{40.10}
$$

由于 $\sqrt{1-|z|^2}$ 在 $z=0$ 的导数为零，固定同一 $a_r,h$ 后，来源方程的导数精确是

$$
\begin{aligned}
D_jP+(c_j^2/2-ix/c_j)m-hZ-a_jn&=0,\\
D_lT-i\pi m/c_l+(\ell_0c_l^2/2-2c_l)Z-a_ln&=0.
\end{aligned}
\tag{40.11}
$$

对任意 $(Z,P,m)$，第一式因 $a_j\ne0$ 唯一确定 $n$；第二式因 $D_l\ne0$ 唯一确定 $T$。所以 $\dot E=0$ 的空间恰为六实维，以 $(Z,P,m)$ 为坐标。这一步使用了实际来源坐标，而没有把来源需求当成自由向量。

记 $Q=\dot q_j$。由 (40.4) 的占据坐标得

$$
Q=(\ell_0+2/c_j)P+x m+ihc_lZ.
\tag{40.12}
$$

四个实图方程的导数为

$$
\begin{gathered}
\operatorname{Im}(P+\overline Z\pi)=0,\qquad
\operatorname{Im}(c_jQ+c_l\overline Z\chi)=0,\\
Q+\overline Z\chi-c_j\overline P-c_l\overline\pi Z=0.
\end{gathered}
\tag{40.13}
$$

最后一式为一个复方程。令 $d=c_l-c_j\ne0$。第一式给 $\operatorname{Im}P=\operatorname{Im}(Z\overline\pi)$，从而最后一式可逆地化为
$Q-c_jP=d\overline\pi Z-\overline Zw$。将它代入第二式，该式的虚部变为 $-d\operatorname{Im}(Z\overline w)=0$。因此 (40.13) 准确等价于

$$
\begin{gathered}
\operatorname{Im}P=\operatorname{Im}(Z\overline\pi),\qquad
\operatorname{Im}(Z\overline w)=0,\\
(\ell_0+2/c_j-c_j)P+x m
 +(ihc_l-d\overline\pi)Z+\overline Zw=0.
\end{gathered}
\tag{40.14}
$$

若 $w\ne0$，第二个实条件恰要求 $Z=bw$、$b\in\mathbb R$。于是八方程导数的全部核向量唯一由 $(R,b)\in\mathbb R^2$ 给出：

$$
\begin{aligned}
Z&=bw,\\
P&=R+i\operatorname{Im}(Z\overline\pi),\\
m&=-\bigl[(\ell_0+2/c_j-c_j)P
 +(ihc_l-d\overline\pi)Z+\overline Zw\bigr]/x,\\
n&=\bigl[D_jP+(c_j^2/2-ix/c_j)m-hZ\bigr]/a_j,\\
T&=\bigl[i\pi m/c_l-(\ell_0c_l^2/2-2c_l)Z+a_ln\bigr]/D_l.
\end{aligned}
\tag{40.15}
$$

各步都有唯一逆解，故没有遗漏核向量。十实维定义域上的导数核恰为二维，因而八实方程的导数满秩八。取 $R=0,b=1$ 可得横向非零切向量 $\dot z=w$。

若 $w=0$，(40.14) 的第二个实条件恒等消失，第一条件唯一确定 $\operatorname{Im}P$，最后的复条件因 $x\ne0$ 唯一确定 $m$；$Z\in\mathbb C$ 和 $\operatorname{Re}P\in\mathbb R$ 自由。再由 (40.11) 唯一确定 $n,T$，故核为三维，导数秩恰为七。这一退化正对应 (40.9) 的已经实际轴分支，不在其上错误使用满秩八。

### 40.4 实解析隐函数定理与精确横向恢复

现在固定 $w\ne0$ 的轴接触及其常数 $x,w$。在八个实方程外添加两个实方程

$$
\operatorname{Re}p_j=x,\qquad
\frac{\operatorname{Re}(z\overline w)}{|w|^2}=s,
\qquad s\in\mathbb R.
\tag{40.16}
$$

在核 (40.15) 上，新增左边的导数分别为 $R$ 和 $b$。所以十方程对十未知量的导数核为零，确为可逆线性映射。方程的实、虚部及坐标 (40.5) 在基点邻域实解析；(40.8) 给出的非零分母都保持非零。有限维实解析隐函数定理于是给出对充分小实 $s$ 唯一的局部实解析解曲线，基点为指定接触，并有

$$
z(s)=s w+O(s^2).
\tag{40.17}
$$

这证明实际来源条件在整条曲线上精确成立，而非只在导数或极限中成立。由于 $w\ne0$，对所有充分小 $s\ne0$ 有 $z(s)\ne0$；又 $u_j(s)>0$，所以两演员坐标都非零。由连续性，缩小参数区间后 $A(s)=-\epsilon\operatorname{Im}\ell(s)>1$，$\epsilon$ 保持原值。原有限变分参数可取

$$
\nu(s)=0,\qquad
\alpha_d(s)=A(s)-d\epsilon>0,\qquad
\beta_d(s)=d\operatorname{Re}\ell(s),\qquad d=\pm1.
\tag{40.18}
$$

定义

$$
V(s)=[u(s)\ Cu(s)],\qquad W(s)=[p(s)\ q(s)],\qquad
X(s)=W(s)V(s)^{-1}.
\tag{40.19}
$$

非轴时 $\det V(s)=(c_2-c_1)u_1(s)u_2(s)\ne0$。图条件使 $V(s)^*W(s)$ 为 Hermitian，亦即 $V(s)^*X(s)V(s)$ 为 Hermitian；左右乘可逆矩阵得到 $X(s)=X(s)^*$。每个非零 $s$ 上它是有限矩阵，且精确给 $Xu=p$、$XCu=q$。

此外，令 $w(s)=q_l(s)-c_jp_l(s)=w+O(s)$，逐列相减给出精确等式

$$
w(s)=(c_l-c_j)X_{ll}(s)u_l(s)=dX_{ll}(s)z(s).
\tag{40.20}
$$

结合 (40.17) 即得 $X_{ll}(s)=1/(ds)+O(1)$。恢复任意原相位 $z_0$ 时，$w(s)$ 和 $u_l(s)$ 同乘 $z_0$，比值和矩阵 $X(s)$ 不变。因此相位不影响 (40.3)。

所用实解析隐函数定理是成熟工具，参见 S. G. Krantz 与 H. R. Parks, *The Implicit Function Theorem: History, Theory, and Applications*（Birkhäuser）。这里的十变量方程、实际来源消元、满秩与横向切向量分别由 (40.4)–(40.16) 给出，不从抽象工具直接假定。

### 40.5 全接触域的穷尽与下确界相等

若一个接触满足 $u_1u_2\ne0$，直接用 (40.19) 即有唯一有限 Hermitian 实现。若在轴上，则 $w=0$ 时由 (40.9) 已经实际，$w\ne0$ 时由 (40.16)–(40.20) 精确恢复。这穷尽所有单位演员，并对每个固定 $\epsilon$ 给出稠密性。

对固定实 $k$，$J_k$ 在每个合法接触点连续，因为 $A>1$。实际子集包含于增广域，故 $\inf_{\mathcal C}J_k\le\inf_{\mathcal C^{\rm fin}}J_k$；另一方面，对任一 $c\in\mathcal C$，或保持它，或取上述实际恢复曲线，均得 $\inf_{\mathcal C^{\rm fin}}J_k\le J_k(c)$。因此实际下确界是全部增广代价值的下界，给反向不等式。若增广下确界为 $-\infty$，则对每个实数 $M$ 都有接触 $c$ 使 $J_k(c)<M$，连续恢复给出同样满足 $J_k<M$ 的实际接触，故实际下确界也为 $-\infty$；若增广域为空，子集也为空，双方为 $+\infty$。这证明 (40.2) 的扩展实数等式，不需要下确界被取到。

最后，$C,H,B,T_A,a_r$ 都为实矩阵或实向量，故 (39.32) 的复共轭将每个 $i$ 接触及其恢复曲线送到 $-i$ 接触及其恢复曲线。它保持 $A,\epsilon,J_k$，且将 $X(s)$ 送到有限 Hermitian 矩阵 $\overline{X(s)}$。实解析性、横向非零性和 (40.3) 均保留，完成定理 40.2 对两取向的证明。∎

### 40.6 同一原来源上的有限环境与指定质量

对任意一个精确有限接触，取其有限矩阵 $X$，并在任意固定有限 $\lambda>0$ 上使用 (38.1) 的同一来源 $D=D_{r,\lambda},F,G=G_{r,\lambda}$。令

$$
\begin{gathered}
R_\lambda=(I_2+\lambda^2a_ra_r^*)^{-1},\qquad
e=GR_\lambda\eta a_r,\\
y=D^{-1}(e-\ell FCu/2-Fu),\qquad
\xi=(u,y),\qquad x_{\rm probe}=X\oplus0_3.
\end{gathered}
\tag{40.21}
$$

由 (38.2) 的 $DG=F$、$G^*G=R_\lambda^{-1}$、$F^*G=C$ 和 $B-F^*D^{-1}F=H$，精确有

$$
\begin{aligned}
Fu+Dy&=e-\ell FCu/2,\qquad G^*e=\eta a_r,\\
Bu+F^*y&=Hu+\eta a_r-\ell C^2u/2=a_{\rm act}.
\end{aligned}
\tag{40.22}
$$

所以演员列和环境列来自同一原向量及同一实际来源，$D,F,G$ 没有被替换。$\|u\|=1$ 保证 $\xi\ne0$。任意指定有限质量 $\mu>0$ 可由

$$
\widehat\xi=\frac{\sqrt\mu}{\|\xi\|}\xi,\qquad
\widehat\phi(M)=\widehat\xi^*M\widehat\xi,
\qquad \widehat\phi(I_5)=\mu
\tag{40.23}
$$

实现；原探针仍为 $x_{\rm probe}$，两笔原预算均使用这个同一泛函。这只是同一原域上的精确提升，并不赋予任意接触一个 PB 成功或失败结论。

“精确接触”专指 (39.4)。有限 $\lambda$ 上的环境列 $e$ 一般不为零；即使演员接触成立，在 $\rho=k/\lambda^2$ 时仍保留原有限残量项。故这里既不把接触方程等同于全部有限阶段缺陷消失，也不把 (40.2) 等同于有限阶段 PB 变分的取到性。

### 40.7 显式 $809/480$ 接触的横向非退化性

**推论 40.3（两份显式轴接触的精确非轴恢复）。** 对每个固定 $0<h<2\sqrt2$，(38.8)–(38.11) 的两个来源接触及另一取向的共轭接触均满足定理 40.2 第 1 项。其基点具有 $A=9$、$\epsilon=1$、$|\eta|^2=809/9$，并且

$$
J_k=\frac{809}{40}-12k.
\tag{40.24}
$$

证明。先在 $\iota=i$ 取 $j=1,l=2$，直接沿用 (38.8)–(38.11) 的原常数，记

$$
\begin{gathered}
\ell_0=-1-9i,\qquad x=1/3,\qquad
\eta_0=\sqrt2(-33-23i)/6,\qquad D_2=(-9+3i)/2,\\
\pi=(h+r\eta_0)/D_2,\qquad
\chi=(\ell_0+1)\pi+ih,\qquad
w=\chi-\pi=\ell_0\pi+ih.
\end{gathered}
\tag{40.25}
$$

不改来源归一化，直接乘出

$$
D_2w=r\sqrt2\,(-87+160i)/3-(5+27i)h/2.
\tag{40.26}
$$

若 $r=+1$，其实部为 $-29\sqrt2-5h/2<0$；若 $r=-1$，其虚部为 $-160\sqrt2/3-27h/2<0$。故对每个 $h>0$、每个来源都有 $w\ne0$，适用 (40.15)–(40.20)。再由 $s(9)=9/40$、$|\eta_0|^2=809/9$ 和 $\zeta=-3$ 得 (40.24)。复共轭给另一取向的同一结论。∎

这里的恢复加强的是接触方程的精确性；它不把 $809/480$ 升格为最优完整阈值。§39 的更小公共轴阈值和本推论描述的是不同的数学性质。

### 40.8 来源、工具与未解比较

本节的接触与图条件来自 (37.15)、(37.19)、(39.4)，代价来自 (37.20)、(39.5)，原实际环境为 (38.1)–(38.2)，显式轴点为 (38.8)–(38.11)。实解析隐函数定理和可逆基下的 Hermitian 判据分别用于 (40.16)–(40.19)；实际来源导数的核、退化分支和横向恢复由 (40.11)–(40.20) 确定。

(40.2) 解决这两个固定实来源在 $0<h<2\sqrt2$ 内的增广接触与精确有限接触下确界等价，不限制恢复矩阵的大小，也不保持 $\ell,\eta$ 固定。§37 的全原测试渐近判据仍只在其原强制估计邻域使用；§39 的无界条带排除另有 $h\le1/1000$ 的条件。稠密性不扩大这两个范围。

完整来源阈值的等值或严格不等值、非轴接触的全称代价下界、临界零值的有限 $\lambda$ 次阶符号，以及同一完整 P2 内一份来源全部 PB 成功而另一份失败的比较仍未解决。下确界相等不证明取到性，不给最优完整阈值，也不提供任一来源的全称成功证书。

## 追加锚（本行以下为增补区）


## 41. 全接触的保源约化、共同正性与联合紧性

**约定 41.1（原域、参数与引用）。** 本节至 §43 是一条普通纸面数学推导，数学归属为 `repo-derived`；不赋予形式化或物理实现状态。原实际来源、全部探针、完整正泛函及两笔预算沿用 [§37](#37-单位演员归一的全部原探针接触闭包极限定理)、[§39](#39-全接触矩消元无界条带排除与增广轴扇区的完整分类)。特别地，固定来源始终是

$$
a_r=(1/\sqrt2,r)^{\mathsf T},\qquad r\in\{+1,-1\},
$$

$C,H_h,B_h,T_A$ 取 (39.1)，完整实际环境取 (38.1)。接触域精确取 (39.4)，包括增广轴点。先固定取向 $\iota=i$，写

$$
\ell=x+iy,\qquad A=|y|>1,\qquad \epsilon=-\operatorname{sgn}y.
$$

两个 $y$ 符号均保留；另一取向由 (39.32) 运输。原量始终为

$$
\zeta=\operatorname{Re}((a_{\rm act}-ip)^*T_Au),\qquad
J_k=\frac{2A}{A^2-1}|\eta|^2+4\epsilon k\zeta.
\tag{41.1}
$$

不利接触指 $\epsilon\zeta<0$，等价于 $y\zeta>0$。其比值及完整正残量阈值为

$$
\mathscr R=\frac{A|\eta|^2}{2(A^2-1)|\zeta|},\qquad
K_r(h)=\inf_{\epsilon\zeta<0}\mathscr R.
\tag{41.2}
$$

$\mathscr R$ 也可用于任意 $\zeta\ne0$ 的接触，但此时不自动是正残量失效阈值。同源的取向等价与正负残量阈值等价直接引用命题 39.7。

本节的接触代数允许实 $|h|\le10^{-3}$，并在需要时放宽至 $|h|<1$。有限原 PB 的桥梁另需强制估计：记 $h_{\rm coer}>0$ 为使 §37.1 所引用的 §32、(35.16) 估计对当前两来源成立的一个共同充分半径，并缩小它使 $H_h\succ0$。凡使用有限 PB 后果，均要求

$$
0<h<h_{\rm coer},\qquad h\le10^{-3}.
\tag{41.3}
$$

这里没有确定 $h_{\rm coer}$ 的数值；$10^{-3}$ 只是以下接触估计的半径。

### 41.1 不消失的源读数与四实参数约化

**定理 41.2（全域保源约化及定量非消失）。** 对 $|h|<1$，置

$$
\begin{gathered}
s=|u_1|^2,\quad t=|u_2|^2,\quad
\overline{u_1}u_2=v+id,\quad s+t=1,\quad |v+id|\le1/2,\\
\beta=3s+12t+3hv,\qquad \gamma=3s+24t+4hv,\qquad
m=u^*p,\quad n=u^*Cp.
\end{gathered}
\tag{41.4}
$$

引理 39.2 的四个实图条件，在两条演员接触等式下，等价于

$$
m=-\frac{\beta}{y},\qquad
2\operatorname{Re}n+\frac{(x+3)\beta}{y}+hd=0,\qquad
\operatorname{Im}(\ell n)+\gamma=0.
\tag{41.5}
$$

这里第一式为复数等式，包含 $\operatorname{Im}m=0$，故共计四个实条件。沿用 (39.10) 的消元，

$$
\zeta=-3s+12t-hv=u^*Z_hu,\qquad
Z_h=\begin{pmatrix}-3&-h/2\\-h/2&12\end{pmatrix}.
\tag{41.6}
$$

定义新的源读数

$$
\begin{gathered}
R_\ell=(C-\ell I_2)^{-1},\qquad
\mathsf E_h=CH_h-C^4/2=\begin{pmatrix}3/2&h\\2h&0\end{pmatrix},\\
c_3=s+8t,\qquad D_r=u^*R_\ell Ca_r,\\
N=-c_3/2-u^*R_\ell\mathsf E_hu-i\beta/y.
\end{gathered}
\tag{41.7}
$$

每个接触满足

$$
\begin{gathered}
p=-i\left[(C^3/2+R_\ell\mathsf E_h)u+\eta R_\ell Ca_r\right],\qquad
\eta D_r=N,\\
-y\operatorname{Im}N\ge3+9t-3|h|>0,\\
D_r\ne0,\qquad
|\eta|\ge\sqrt2(1+3t-|h|)\ge\sqrt2(1-|h|)>0.
\end{gathered}
\tag{41.8}
$$

反之，任取 $\ell=x+iy$、$|y|>1$ 和 $[u]\in\mathbb {CP}^1$ 的单位代表，若 $D_r\ne0$，令 $\eta=N/D_r$，按 (41.8) 定义 $p$，再按 (39.4) 定义 $q,a_{\rm act}$。这些数据是完整接触，当且仅当 (41.5) 的后两条实方程成立。这是四个实参数、两个实方程的精确约化，未除以 $x,u_1,u_2$。

证明。(41.5) 只是 (39.9) 的等价写法，(41.6) 直接取 (39.10)，这里不另立矩消元结论。为核对四个实条件的计数，$2C^{-1}=3I_2-C$ 给

$$
u^*q=(\ell+3)m-n+i(\beta+ihd),\qquad
(Cu)^*q=\ell n+2m+i\gamma.
$$

要求 $m$ 实、第一式等于 $\overline n$、第二式实，即得 (41.5)，且每一步可逆。

来源方程左乘 $C$，再用

$$
CH_h-\ell C^3/2=(C-\ell I_2)C^3/2+\mathsf E_h,
$$

即可解出 (41.8) 的 $p$。所有逆矩阵存在，因为 $y\ne0$。将 $u^*p=-\beta/y$ 代回，恰得 $\eta D_r=N$。

令 $R_j=(j-\ell)^{-1}$。有

$$
u^*R_\ell\mathsf E_hu=\tfrac32R_1s+hR_1(v+id)+2hR_2(v-id),
\qquad |yR_j|\le1,\quad y\operatorname{Im}R_1\ge0.
$$

故

$$
\begin{aligned}
-y\operatorname{Im}N
 &=\beta+y\operatorname{Im}(u^*R_\ell\mathsf E_hu)\\
 &\ge3s+12t-6|h||u_1u_2|\\
 &\ge3+9t-3|h|>0.
\end{aligned}
$$

又 $A|D_r|\le\|Ca_r\|=3/\sqrt2$，因而 $A|\eta||D_r|=A|N|\ge3+9t-3|h|$ 给出幅度下界及 $D_r\ne0$。反向构造中，$\eta D_r=N$ 精确强制第一条复等式 $m=-\beta/y$；剩下两条就是尚待满足的全部图条件。来源等式已由逆式成立，因此必要性与充分性均得证。

同时将 $u,p,q,a_{\rm act},\eta$ 乘以单位复数，保持来源向量 $a_r$ 固定，全部方程和比值不变；$N$ 不变，$D_r$ 乘该相位的共轭。因此 $[u]$ 是精确的相位商。该约化含两轴及 $x=0$；有限 Hermitian 实现与轴核条件仍按引理 37.2、(39.22) 区分。∎

### 41.2 共同的严格正区间

**定理 41.3（两来源的全接触正性）。** 对所有实 $|h|\le10^{-3}$、两个来源及两个取向，任一 $\zeta\ne0$ 的接触均有 $\mathscr R>1/40$。因此

$$
0<k\le1/40\quad\Longrightarrow\quad J_k(c)>0
\quad\text{对每个完整接触 }c.
\tag{41.9}
$$

证明。记 $q_h=|h|$、$L=|\ell|$。由 (41.6)，

$$
|\zeta|\le12+q_h/2<13,\qquad
\zeta<0\ \Longrightarrow\ |\zeta|\le3+q_h/2.
$$

当 $L>2$，$\|R_\ell\|\le(L-2)^{-1}$、$\|\mathsf E_h\|\le3/2+2q_h$。取 $\eta D_r=N$ 的实部，使用 $|D_r|\le(3/\sqrt2)/(L-2)$，得到

$$
\frac3{\sqrt2}|\eta|
\ge\frac{c_3}{2}(L-2)-(3/2+2q_h).
\tag{41.10}
$$

特别在右边为正时，$|\eta|\ge(L-5-4q_h)/(3\sqrt2)$。由于 $A\le L$，任何 $\zeta\ne0$ 的接触都满足

$$
\mathscr R>\frac{|\eta|^2}{2L|\zeta|}.
\tag{41.11}
$$

若 $\zeta<0$，有 $|\zeta|<31/10$、$|\eta|^2>199/100$。当 $L\le11$，(41.11) 给 $\mathscr R>199/6820>1/40$。当 $L\ge11$，(41.10) 给 $|\eta|^2>(L-51/10)^2/18$，故

$$
\mathscr R>
\frac{(L-51/10)^2}{36(31/10)L}
\ge\frac{3481}{122760}>\frac1{40}.
\tag{41.12}
$$

最后的单调性来自 $\frac{d}{dL}[(L-a)^2/L]=1-a^2/L^2>0$，$L>a$。

若 $\zeta>0$，(41.6) 强制 $t>1/5-q_h/30$。于是 $c_3>239/100$，(41.8) 还给 $|\eta|^2>5$；同时 $|\zeta|<121/10$。当 $L\le8$，有 $\mathscr R>25/968>1/40$。当 $L\ge8$，(41.10) 给

$$
|\eta|^2>\frac{(239L-780)^2}{180000},\qquad
\mathscr R>
\frac{(239L-780)^2}{360000(121/10)L}
\ge\frac{1281424}{34848000}>\frac1{40}.
\tag{41.13}
$$

此处仍用同一单调性，起点 $8>780/239$。两个符号穷尽 $\zeta\ne0$。不利接触有 $J_k=4|\zeta|(\mathscr R-k)>0$；其余接触包括 $\zeta=0$，由 $\eta\ne0$ 使 (41.1) 严格正。另一取向由命题 39.7 保留此结论。∎

### 41.3 无界条带与联合低子水平集

**定理 41.4（扩大的条带排除与联合紧性）。** 对 $|h|\le10^{-3}$、$r=\pm1$，若接触满足 $|x|\le1/100$、$\zeta\ne0$，则 $\mathscr R>6/5$。所有不利接触的低子水平集

$$
\mathcal L=\{(h,r,c): |h|\le10^{-3},\ c\in\mathcal C_i(a_r;h),
\epsilon\zeta<0,\ \mathscr R\le6/5\}
\tag{41.14}
$$

在完整可见变量及 $h,r,\epsilon$ 的乘积拓扑中紧，且每个固定 $h,r$ 的纤维非空。其中一致成立

$$
\begin{gathered}
A>103/100,\quad |\ell|<600,\quad |x|>1/100,\quad
|\eta|<140,\quad |\zeta|>1/1000,\\
\|p\|<426,\qquad |D_r|>1/30000,
\end{gathered}
\tag{41.15}
$$

$q,a_{\rm act}$ 也一致有界。于是每个 $|h|\le10^{-3}$ 都有

$$
K_r(h)=\min_{c\in\mathcal L_{h,r}}\mathscr R,
\qquad \frac1{40}<K_r(h)\le\frac{85}{72}<\frac65.
\tag{41.16}
$$

这里首先是增广接触域上的达到性。

证明。以下全用 $q_h=|h|$，所以包含 $h=0$ 及负 $h$。写

$$
\overline{u_1}p_1=\alpha+ib,\qquad
\overline{u_2}p_2=\chi-ib.
$$

由 (39.10) 或 (41.5)，有不除以 $x$ 的恒等式

$$
\zeta=x\beta+2xb+yhd.
\tag{41.17}
$$

另将需求 $\eta a_r=i(I_2-\ell C^{-1})p-H_hu+\ell C^2u/2$ 分别左乘 $u^*$、$(Cu)^*$。用 (41.5) 消去 $m,n$ 后，得到

$$
\begin{aligned}
\operatorname{Re}(\eta u^*a_r)
 &=\tfrac{x}{2}(s+4t)-5(s+2t)-\tfrac92hv,\\
2\operatorname{Im}(\eta(Cu)^*a_r)
 &=y(s+8t)-\frac{(3-x)\beta}{y}+hd.
\end{aligned}
\tag{41.18}
$$

第一式可直接由 $u^*C^{-1}p=(3m-n)/2$ 及 $\operatorname{Im}(\ell n)=-\gamma$ 得到；第二式用 $(Cu)^*C^{-1}p=m$、$2\operatorname{Re}n=-(x+3)\beta/y-hd$ 得到，故保留了原来源的两个读数。

设 $|x|\le1/100$，$e=|\eta|$。第一读数给

$$
-\operatorname{Re}(\eta u^*a_r)
\ge5-2/100-9/4000>49/10>4\sqrt{3/2},
$$

因 $\|a_r\|=\sqrt{3/2}$，故 $e>4$。第二读数、$s+8t\ge1$ 和 $0<\beta<13$ 给

$$
A\le3\sqrt2\,e+\frac{(301/100)13}{A}+1/2000.
$$

当 $A\ge7$，后两项小于 $6$，故 $A<(17/4)e+6<6e$；当 $A<7$，由 $e>4$ 也有 $A<6e$。来源逆式给 $\|p\|<4+(2+3e)/A$，而 $2|b|\le\|p\|$。由 (41.17)，

$$
|\zeta|<\frac1{100}\left(17+\frac{2+3e}{A}\right)+\frac A{2000}.
$$

若同时 $\mathscr R\le6/5$，则 $e^2<(12/5)A|\zeta|$，从而

$$
\begin{aligned}
e^2
 &<\frac{12}{500}(17A+2+3e)+\frac{12}{10000}A^2\\
 &<\frac{12}{500}(105e+2)+\frac{216}{5000}e^2\\
 &<\left(\frac{63}{100}+\frac3{1000}+\frac{216}{5000}\right)e^2
 =\frac{3381}{5000}e^2<e^2.
\end{aligned}
$$

矛盾。这证明整个无界条带的排除，没有预设 $A$ 或列有界。

再设任一接触有 $\mathscr R\le6/5$。若 $L\ge600$，(41.10)–(41.11) 给

$$
\mathscr R>\frac{(L-6)^2}{468L}
\ge\frac{594^2}{468\cdot600}>\frac65,
$$

矛盾，故 $L<600$。由幅度下界及 $|\zeta|<13$，

$$
\mathscr R>\frac{A(1-q_h)^2}{13(A^2-1)}.
$$

右边在 $A>1$ 递减；在 $A=103/100$、$q_h=1/1000$ 仍大于 $6/5$，故 $A>103/100$。同一子水平条件给

$$
\begin{aligned}
e^2&\le\frac{12}{5}\frac{A^2-1}{A}|\zeta|
 <\frac{12}{5}\,600\cdot13<140^2,\\
|\zeta|&\ge\frac{5Ae^2}{12(A^2-1)}
 >\frac{(999/1000)^2}{720}>\frac1{1000}.
\end{aligned}
$$

(41.8) 给 $\|p\|<4+(2+3e)/A<426$。原 $q,a_{\rm act}$ 的定义以有界 $\ell,u,p$ 一致界住它们。又

$$
|D_r|=|N|/e\ge\frac{3(1-q_h)}{Ae}
>\frac{3(999/1000)}{600\cdot140}>\frac1{30000}.
$$

这证明全部所列界，条带排除另给 $|x|>1/100$。

非空性直接引用定理 39.4 的第二轴 $y=4$ 接触：其 $\zeta=12$、$|\eta|^2=425/4$，比值 $85/72$，为不利接触；轴公式对实 $h$ 的代数不变。没有重新把轴值当作完整最优值。

所有变量现已一致有界。任何收敛序列的极限保留原图、演员及来源等式；$A\ge103/100>1$、$|\zeta|\ge1/1000>0$，且 $y\zeta>0$ 的符号不会在极限丢失。比值连续，保留 $\mathscr R\le6/5$。所以 $\mathcal L$ 闭而有界，因而紧；这也说明严格定义域边界没有破坏闭性。每个纤维内的最小值存在，其外比值大于 $6/5$，而纤维内已有 $85/72$，故它就是全域下确界。定理 41.3 在取到的点上严格大于 $1/40$，给出 (41.16)。没有从增广紧性推断整个有限实际接触集闭合。∎

### 41.4 完整原 PB 与 P2 的同参数后果

**定理 41.5（共同成功区间及严格阈值桥梁）。** 固定同一对正数 $h,k$，满足 (41.3)。若 $0<k\le1/40$，则两来源在两取向上，对所有充分大的有限 $\lambda$ 均满足全部原 PB，并且同一个 $\rho=k/\lambda^2$ 严格位于共同完整 P2 区间内。更一般地，对任一固定来源，$0<k<K_r(h)$ 给最终全部 PB 成功，$k>K_r(h)$ 给最终严格 PB 失败；失败可由两笔严格正预算及任意指定有限质量 $\mu>0$ 的同一原正泛函见证。

证明。定理 41.3 使每个完整接触的 $J_k>0$，推论 37.9 及 §37.6 的谱和提升给全部原 PB。这里探针仍遍取每个有限 $X=X^*$，泛函仍遍取完整 $M_5(\mathbb C)$ 上全部正复线性泛函，包括环境和混合块；不对预算、参数比值或演员质量另加限制。对一般 $k<K_r(h)$，不利接触满足 $J_k=4|\zeta|(\mathscr R-k)>0$，其余由 $\eta\ne0$ 给严格正，故用同一桥梁。对 $k>K_r(h)$，存在负接触，定理 37.6、推论 37.7 给所述有限原失败、正预算及质量归一。

共同完整 P2 直接引用 (39.7)，其来源为[前卷 §30 的 (30.29)](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30-零模耦合为零的三矩实现与最小真实环境)：

$$
\rho=k/\lambda^2,\qquad
h^2\lambda^4>3k^2(\lambda^2+3/2).
\tag{41.19}
$$

固定同一正 $h,k$ 后该不等式最终成立。将有限个来源及取向的截止与 P2 截止取最大值，即得共同有限截止。接触估计的 $h\le10^{-3}$ 未支付强制估计条件；(41.3) 在这里始终保留。阈值等号处不应用严格充分性。∎

## 42. 固定来源的精确下降与全部极小接触的有界实际性

### 42.1 保持两来源坐标的下降分支

**定理 42.1（严格轴间隙及统一实际达到）。** 存在共同常数

$$
0<h_0\le10^{-3},\qquad \gamma_0>0,\qquad c_0>0,\qquad M_0<\infty,
$$

使对每个实 $|h|\le h_0$、$r=\pm1$ 及两个取向，均有

$$
K_r(h)\le K_{\rm ax}-\gamma_0.
\tag{42.1}
$$

每个不利接触若 $\mathscr R\le K_{\rm ax}-\gamma_0$，则 $|u_1u_2|\ge c_0$。特别地，每个全局极小接触都有唯一有限 Hermitian 实现

$$
X=[p,q][u,Cu]^{-1}=X^*,\qquad \|X\|\le M_0.
\tag{42.2}
$$

实际有限 Hermitian 接触阈值与增广阈值相同，且两者均取到。这是接触阈值达到性。

证明。$K_{\rm ax}$ 及其唯一第二轴极小尺度 $A_*>1$ 直接取定理 39.5，故 $K_{\rm ax}<85/72<6/5$；完整轴分类仍取定理 39.4。以下构造在固定 $A>1$ 下给出轴外严格下降。

令

$$
\ell=1+\delta+iA,\qquad u=(\omega,c),\qquad
c=\sqrt{1-|\omega|^2}>0,
\tag{42.3}
$$

其中 $\delta$ 实、$\omega$ 复，均在零附近。沿用 (41.4) 的 $\beta,d$ 和 (41.6) 的 $\zeta$，并令 $x=1+\delta$。由命题 39.6 的唯一列重构，置

$$
\begin{gathered}
\alpha=\frac{(x-1)\beta/A+hd}{2},\qquad
\chi=-\frac{(x+1)\beta/A+hd}{2},\\
b=\frac{\zeta-x\beta-Ahd}{2x},\qquad
p_2=(\chi-ib)/c.
\end{gathered}
\tag{42.4}
$$

先用来源第二坐标固定幅度，再用第一坐标固定 $p_1$：

$$
\begin{aligned}
\eta&=r\left[i(1-\ell/2)p_2-(4-2\ell)c-h\omega\right],\\
p_1&=\frac{\eta/\sqrt2+(2-\ell/2)\omega+hc}{i(1-\ell)}.
\end{aligned}
\tag{42.5}
$$

这精确强制两个来源坐标为 $\eta/\sqrt2,\eta r$，只剩一个复方程

$$
\Psi_r(h,\delta,\omega):=\overline\omega p_1-(\alpha+ib)=0.
\tag{42.6}
$$

因为 $\overline u_2p_2=\chi-ib$ 已成立，(42.6) 精确给回全部四实图条件。$q,a_{\rm act}$ 按原定义重建。

当 $\delta=\omega=0$ 时，$\beta=\zeta=12$、$\alpha=b=0$、$\chi=-12/A$，且

$$
\eta=r g_A,\qquad g_A=-8+i(2A-6/A),\qquad
p_1=(h+rg_A/\sqrt2)/A.
$$

故对所有小 $h$ 均有 $\Psi_r(h,0,0)=0$。在 $h=0$，对 $\omega=\omega_R+i\omega_I$ 求导，实 Jacobian 为

$$
\begin{pmatrix}\operatorname{Re}P_r&\operatorname{Im}P_r\\
\operatorname{Im}P_r&-\operatorname{Re}P_r\end{pmatrix},\qquad
P_r=\frac{rg_A}{\sqrt2 A},\qquad
\det=-\frac{|g_A|^2}{2A^2}<0.
\tag{42.7}
$$

这里 $\beta,\zeta$ 在 $h=\omega=0$ 的 $\omega$ 导数为零，所以 (42.7) 来自 $\overline\omega P_r$，没有遗漏图约束的导数。实解析隐函数定理给精确分支 $\omega_r(h,\delta)$，并由局部唯一性有 $\omega_r(h,0)=0$。在 $h=\delta=0$，

$$
\overline{\omega_\delta}P_r=6/A-6i\ne0.
$$

因而缩小共同邻域后，$\omega_r(h,\delta)/\delta$ 连续且非零，所有非零小 $\delta$ 的接触均非轴。这里两来源只有两个，可取共同邻域。

在基点，沿此精确分支有

$$
\beta_\delta=\zeta_\delta=0,\quad
\alpha_\delta=6/A,\quad\chi_\delta=-6/A,\quad b_\delta=-6,
$$

因此 $(p_2)_\delta=-6/A+6i$，由 (42.5) 得

$$
(\eta r)_\delta=-4+i(3A+3/A).
$$

由于 $A$ 固定，代入原比值得

$$
\left.\partial_\delta\mathscr R_r\right|_{h=\delta=0}
=D(A):=\frac{3A^4+10A^2-9}{6A(A^2-1)}>0.
\tag{42.8}
$$

分子在 $A^2>1$ 上递增且在 $A=1$ 为 $4$，故正性覆盖全部 $A>1$，不是数值猜测。现在取 $A=A_*$。轴值对所有 $h,r$ 都是 $K_{\rm ax}$。分支的 $\zeta$ 仍为正，$y=A_*>1$，故附近比值均属不利接触。

由解析性，选共同闭矩形 $|h|\le h_0$、$\delta_0\le\delta\le0$，其中 $\delta_0<0$、$h_0>0$，使 $\partial_\delta\mathscr R_r\ge D(A_*)/2$；同时保持所有上述分母非零、$c>0$ 及非轴性质。于是

$$
\mathscr R_r(h,\delta_0)
\le K_{\rm ax}+\delta_0 D(A_*)/2
=K_{\rm ax}-\gamma_0,\qquad
\gamma_0=-\delta_0D(A_*)/2>0.
\tag{42.9}
$$

这给的是固定来源方程上的真实有限下降，并由导数在矩形上的下界控制了余项。它直接证明 (42.1)。

### 42.2 从下降到全部极小点的统一界

将 $h_0$ 缩至不超过 $10^{-3}$。定理 41.4 的联合紧集内，取 $|h|\le h_0$、$\mathscr R\le K_{\rm ax}-\gamma_0$ 的闭子集。由 (42.9) 其每个 $h,r$ 纤维非空。定理 39.5 的全部轴值至少为 $K_{\rm ax}$；其轴公式对这些实 $h$ 不变，所以该联合闭子集不含任一轴。连续函数 $|u_1u_2|$ 在其上取得共同正下界 $c_0$。

定理 41.4 已保证每个全局极小值取到，且 (42.1) 使所有极小接触都在这个闭子集内。非轴可见列重构及其 Hermitian 性直接沿用引理 37.2、(39.30)，而现在还有统一范数估计。若 $V=[u,Cu]$，则

$$
\det V=u_1u_2,\qquad
\|V^{-1}\|\le\frac{\|V\|_{\rm F}}{|u_1u_2|}
\le\frac{\sqrt5}{c_0}.
$$

结合联合紧性给出的 $p,q$ 一致界，得到共同 $M_0$ 及 (42.2)。实际接触域是增广域的子集，又包含每个增广极小点，所以其比值下确界相同并且实际取到。另一取向由 (39.32) 共轭运输，范数界不变。∎

[§40 的精确同源接触稠密性](#40-两个固定实来源的精确有限接触稠密性) 已经比较了实际与增广下确界，但允许矩阵发散；定理 42.1 的新增结论是全部全局极小接触同时非轴并有共同有界实际矩阵。它不主张有限 $\lambda$ 原 PB 变分问题有极小探针。同时使用达到性与有限桥梁时，参数交是 $0<h\le h_0$、$h<h_{\rm coer}$、固定 $k>0$，并按定理 41.5 的严格阈值条件取满足 (41.19) 的充分大有限 $\lambda$。

## 43. 完整非轴接触的三次方程与有条件的全极小集微扰

### 43.1 源对齐坐标中的精确方程

**定义 43.1（源对齐图及标量函数）。** 以下仍固定取向 $i$，$\ell=x+iy$，$x\ne0$、$|y|>1$。固定整体相位后，将非轴演员写成

$$
U=(1,r\tau)^{\mathsf T},\qquad
\tau=v+id\ne0,\qquad t=|\tau|^2>0,\qquad
u=U/n,\quad n=\sqrt{1+t},\quad g=rh.
\tag{43.1}
$$

此处 $t$ 是非轴坐标的模平方，代替 §41 中的第二演员质量记号。$g$ 只作源对齐后的参数，原来源仍是 $a_r=(1/\sqrt2,r)^{\mathsf T}$。置

$$
\begin{gathered}
\beta_0=3+12t,\qquad Z_0=-3+12t,\\
\alpha_0=\frac{(x-1)\beta_0}{2y},\qquad
\chi_0=-\frac{(x+1)\beta_0}{2y},\qquad
\kappa_0=\frac{Z_0-x\beta_0}{2x},\\
F(t)=i(1-\ell)(\alpha_0+i\kappa_0)-(2-\ell/2)=f_0+f_1t,\\
G(t)=i(1-\ell/2)(\chi_0-i\kappa_0)-(4-2\ell)t=g_0+g_1t.
\end{gathered}
\tag{43.2}
$$

$f_j,g_j$ 是固定 $\ell$ 的复系数，$g_j$ 不表示参数 $g$。再置

$$
\begin{gathered}
\alpha_1=\tfrac12[3(x-1)v/y+d],\qquad
\chi_1=-\tfrac12[3(x+1)v/y+d],\\
\kappa_1=\frac{-(1+3x)v-yd}{2x},\\
L_1(\tau)=i(1-\ell)(\alpha_1+i\kappa_1)-\tau,\\
L_2(\tau)=i(1-\ell/2)(\chi_1-i\kappa_1)-\overline\tau,\\
E_0(\tau)=\sqrt2F(t)\overline\tau-G(t),\qquad
E_1(\tau)=\sqrt2L_1(\tau)\overline\tau-L_2(\tau),\\
E_g(\tau)=E_0(\tau)+gE_1(\tau).
\end{gathered}
\tag{43.3}
$$

所有函数还依赖固定或变化的 $x,y$；$E_g=E_0+rhE_1$ 是精确等式。

**定理 43.2（全部四实图条件与两来源坐标的等价方程）。** 对 $|h|<1$，(43.1) 图中的完整接触与 $E_{rh}(\tau)=0$ 一一对应，差别仅为整体相位。其源幅度及不利比值为

$$
\widehat\eta=\sqrt2(F+gL_1),\qquad \eta=\widehat\eta/n,
\qquad
\mathcal R_g=\frac{A|F+gL_1|^2}{(A^2-1)|Z_0-gv|},
\tag{43.4}
$$

不利过滤条件精确为 $y(Z_0-gv)>0$。所有这些接触均有 $\eta\ne0$ 且有有限 Hermitian 实现。

证明。为保持归一化清晰，将可见列先写成 $P=np$、$Q=nq$、$A_{\rm act}=na_{\rm act}$。对一般未归一演员 $U$，设

$$
\begin{gathered}
\beta=3|U_1|^2+12|U_2|^2+3h\operatorname{Re}(\overline U_1U_2),\\
Z=-3|U_1|^2+12|U_2|^2-h\operatorname{Re}(\overline U_1U_2),\qquad
d_U=\operatorname{Im}(\overline U_1U_2).
\end{gathered}
$$

命题 39.6 的重构等价地说，全部四个实图条件是

$$
\begin{gathered}
\overline U_1P_1=\alpha+i\kappa,\qquad
\overline U_2P_2=\chi-i\kappa,\\
\alpha=\frac{(x-1)\beta/y+hd_U}{2},\qquad
\chi=-\frac{(x+1)\beta/y+hd_U}{2},\qquad
\kappa=\frac{Z-x\beta-yhd_U}{2x}.
\end{gathered}
\tag{43.5}
$$

这里没有舍弃交叉条件的实部或虚部：$m=U^*P=-\beta/y$，$\operatorname{Re}(U^*CP)=-[(x+3)\beta/y+hd_U]/2$，$\operatorname{Im}(\ell U^*CP)=-\gamma$，其中 $\gamma=3|U_1|^2+24|U_2|^2+4h\operatorname{Re}(\overline U_1U_2)$，正是 (41.5) 的齐次版本。

代入 $U=(1,r\tau)$，得到

$$
\beta=\beta_0+3gv,\qquad Z=Z_0-gv,\qquad hd_U=gd,
$$

故 $\alpha=\alpha_0+g\alpha_1$、$\chi=\chi_0+g\chi_1$、$\kappa=\kappa_0+g\kappa_1$。据 (43.5) 取

$$
P=\left(\alpha+i\kappa,\ \frac{r(\chi-i\kappa)}{\overline\tau}\right)^{\mathsf T},\quad
Q=(\ell I_2+2C^{-1})P+iB_hCU,\quad
A_{\rm act}=i(I_2-\ell C^{-1})P.
$$

所有图条件和两演员接触已成立。把实际来源需求记为

$$
\mathbf D=A_{\rm act}-H_hU+\ell C^2U/2.
$$

其两个坐标分别满足

$$
D_1=F+gL_1,\qquad
r\overline\tau D_2=G+gL_2.
\tag{43.6}
$$

第一来源坐标 $D_1=\widehat\eta/\sqrt2$ 固定了 $\widehat\eta$。第二来源坐标 $D_2=r\widehat\eta$ 因 $\tau\ne0$ 等价于

$$
G+gL_2=\sqrt2(F+gL_1)\overline\tau,
$$

即 $E_g=0$。除以 $n$ 恢复原归一接触；逆过程唯一给回全部数据，故是必要且充分的精确方程。定理 41.2 的齐次非消失估计给 $\eta\ne0$，非轴有限 Hermitian 重构沿用 (39.30)。最后

$$
\zeta=(Z_0-gv)/(1+t),\qquad
|\eta|^2=2|F+gL_1|^2/(1+t),
$$

代入原比值及 $y\zeta>0$ 即得 (43.4) 及过滤条件。两个实际来源坐标始终都在等价链中。∎

### 43.2 零阶接触的穷尽三次枚举

**定理 43.3（固定 $\ell$ 的非零实三次多项式）。** 对每个固定 $x\ne0$、$|y|>1$，定义

$$
\begin{aligned}
P(t)&=2t|F(t)|^2-|G(t)|^2\\
 &=2|f_1|^2t^3+
 [4\operatorname{Re}(f_0\overline f_1)-|g_1|^2]t^2\\
 &\quad+[2|f_0|^2-2\operatorname{Re}(g_0\overline g_1)]t-|g_0|^2.
\end{aligned}
\tag{43.7}
$$

它是非零、实系数、次数至多三的多项式。$h=0$ 时，所有非轴接触精确由每个正根 $t$ 及唯一源对齐相位

$$
\tau=\overline{\frac{G(t)}{\sqrt2F(t)}}
\tag{43.8}
$$

给出。每个正根都有 $F(t)G(t)\ne0$；重根也全部保留。正残量不利接触须另保留

$$
y(4t-1)>0,\qquad
\mathcal R_0(x,y,t)=\frac{A|F(t)|^2}{3(A^2-1)|4t-1|}.
\tag{43.9}
$$

证明。在 $g=0$，完整接触等式是 $\sqrt2F(t)\overline\tau=G(t)$。取模平方给 $P(t)=0$。若正根上 $F=0$，则 $G=0$；任取模为 $\sqrt t$ 的 $\tau$ 都满足 $E_0=0$，由定理 43.2 重构的需求却为零，与定理 41.2 的非消失估计矛盾。故 $F\ne0$，模平方等式和 $t>0$ 又给 $G\ne0$。于是 (43.8) 唯一，其模平方正好为 $t$，并满足完整复等式。此论证不要求 $P'(t)\ne0$，故不丢弃任何正重根。反向每个接触已给一个正根，枚举穷尽。

展开两个仿射函数的模平方给 (43.7)。由 (43.2) 的实部直接得到

$$
\operatorname{Re}f_1=\frac{6(x-1)}x,\qquad
\operatorname{Re}g_0=-\frac{3(x+1)}{2x}.
\tag{43.10}
$$

两者不可能同时为零。因此若 $f_1\ne0$，最高次系数 $2|f_1|^2$ 非零；若 $f_1=0$，则 $g_0\ne0$，常数项非零。$P$ 永不恒等为零，每个固定 $\ell$ 至多有三个不同正根。最后 $Z_0=3(4t-1)$，(43.4) 给过滤条件与原比值。若 $t=1/4$，仍是可能的接触根，但 $\zeta=0$，不进入不利比值枚举。此处固定来源后的演员是 $(1,r\tau)$，没有改成另一个归一来源。∎

### 43.3 精确源奇平衡与全部极小点的统一坐标控制

**定理 43.4（完整约束的源奇恒等式）。** 每个 (43.3) 图中的精确接触都满足

$$
P(t)+2rh\operatorname{Re}(\overline{G(t)}E_1(\tau))
=h^2|E_1(\tau)|^2.
\tag{43.11}
$$

存在共同 $0<h_*\le h_0$、$C_*<\infty$，使对所有 $|h|\le h_*$、两来源的每一个全局极小接触，可选唯一整体相位规范 $u_1>0$，落入 (43.1) 图，且

$$
0\le P(t)+2rh\operatorname{Re}(\overline G E_1)\le C_*h^2.
\tag{43.12}
$$

这些接触的 $x,y,\tau$ 处于共同紧集，$|x|$、$|y|-1$、$|\tau|$ 均有共同正下界，$|\tau|$ 有共同上界，且 $|Z_0|$ 有共同正下界。这些结论不要求唯一极小点、单根或非零源奇系数。

证明。$E_g=0$ 等价于 $\sqrt2F\overline\tau=G-gE_1$。取模平方并减去 $|G|^2$，得到

$$
P(t)=-2g\operatorname{Re}(\overline GE_1)+g^2|E_1|^2,
$$

即 (43.11)，符号及非负二次余项均为精确等式。

取 $h_*\le h_0$。定理 42.1 的低子水平集包含每个全局极小接触，并使 $|u_1u_2|\ge c_0$。因为 $|u_j|\le1$，两个 $|u_j|$ 各自至少为 $c_0$，所以 $\tau=ru_2/u_1$ 在共同闭环带内，整体相位规范合法。定理 41.4 另给 $|x|>1/100$、$|y|>103/100$ 及全部变量上界。故该图覆盖所有小 $|h|$ 全局极小点，未选择某一个根或某一 $y$ 符号。

也可直接看见实部不能退化的原因：(41.17) 中 $\beta,b,y$ 在此联合紧集有界，$|\zeta|\ge1/1000$；项 $yhd$ 的绝对值至多 $|yh|/2$。缩小 $h_*$ 使该项小于 $1/2000$，便由 $\zeta=x(\beta+2b)+yhd$ 得 $|x|$ 的共同正下界。这与已证明的条带排除相容，不假设 $x\ne0$ 来证明自身。

(43.2)–(43.3) 的所有分母因此远离零，$E_1$ 在共同紧图上有界，给 (43.12)。又

$$
|Z_0-gv|=(1+t)|\zeta|\ge1/1000.
$$

$|v|$ 一致有界，进一步缩小 $h_*$ 使 $|gv|\le1/2000$，便有 $|Z_0|\ge1/2000$。再缩小一次使 $|gv/Z_0|\le1/2$。所有缩小均取两来源共同值。

在这个图上，原值函数还具有一致展开

$$
\mathcal R_g=\mathcal R_0+g\mathcal S+O(h^2),\qquad
\mathcal S=\frac{A}{(A^2-1)|Z_0|}
\left[2\operatorname{Re}(\overline F L_1)+\frac{|F|^2v}{Z_0}\right].
\tag{43.13}
$$

这是在实际移动坐标处的展开：用 $|Z_0-gv|=|Z_0|(1-gv/Z_0)$，再用

$$
(1-a)^{-1}=1+a+\frac{a^2}{1-a},\qquad |a|\le1/2,
$$

与 $|F+gL_1|^2=|F|^2+2g\operatorname{Re}(\overline F L_1)+g^2|L_1|^2$ 即得一致二次余项。$\mathcal S$ 本身还没有计入可行根的移动。∎

### 43.4 强制根运动与全极小集的条件包络

**定理 43.5（简单根条件下的完整阈值一阶公式）。** 在 $h=0$ 的接触上写 $\tau=\sqrt t\,e^{i\theta}$。$E_0$ 的实 Jacobian 以 $(t,\theta)$ 为列变量时，行列式精确为

$$
\det D_{(t,\theta)}(\operatorname{Re}E_0,\operatorname{Im}E_0)
=-\tfrac12P'(t).
\tag{43.14}
$$

若 $P'(t)\ne0$，固定 $\ell$ 的实解析延续对参数 $g$ 有

$$
\left.\frac{dt}{dg}\right|_0
=-\frac{2\operatorname{Re}(\overline GE_1)}{P'(t)},\qquad
\mathcal D=\mathcal S-
\frac{2\operatorname{Re}(\overline GE_1)}{P'(t)}\,\partial_t\mathcal R_0.
\tag{43.15}
$$

$\mathcal D$ 是完整受约束值的导数；$\partial_t$ 固定 $x,y$。令 $\mathcal M$ 为源对齐、整体相位商后的整个 $h=0$ 全局极小接触集，两个 $y$ 符号均包括在内。作如下明确的附加假设：

$$
P'(t)\ne0\qquad\text{对每个 }(x,y,t,\theta)\in\mathcal M.
\tag{43.16}
$$

则当 $h\downarrow0$，

$$
K_+(h)-K_-(h)
=h\left(\min_{\mathcal M}\mathcal D+\max_{\mathcal M}\mathcal D\right)+o(h).
\tag{43.17}
$$

(43.16) 尚未为当前问题证成；(43.17) 的系数也未确定符号或是否为零。

证明。在零阶根上，$G=\sqrt2F\overline\tau$，所以

$$
\partial_\theta E_0=-iG,\qquad
\partial_tE_0=\sqrt2(F'+F/(2t))\overline\tau-G'.
$$

实 Jacobian 的行列式是

$$
\begin{aligned}
\operatorname{Im}(\overline{\partial_tE_0}\,\partial_\theta E_0)
 &=-\operatorname{Re}(\overline{\partial_tE_0}G)\\
 &=-\left[2t\operatorname{Re}(\overline{F'}F)+|F|^2
             -\operatorname{Re}(\overline{G'}G)\right]
 =-P'(t)/2.
\end{aligned}
$$

这也精确标出特殊集 $P=P'=0$，没有把它从三次枚举中删除。若 $P'\ne0$，实解析隐函数定理以 $x,y,g$ 为外参数，给唯一局部 $t,\theta$ 分支；$y(Z_0-gv)>0$ 是开条件，在不利基点附近保留。对 (43.11) 关于 $g$ 在零处求导，二次右边导数为零，立即给 (43.15) 的根运动。零阶值 $\mathcal R_0$ 不依赖 $\theta$，所以将 (43.13) 沿分支求导，得恰为 $\mathcal D$，包括强制根运动项。

源反射令 $S=\operatorname{diag}(1,-1)$。由 $SH_hS=H_{-h}$、$SB_hS=B_{-h}$、$Sa_r=a_{-r}$，将 $u,p,q,a_{\rm act}$ 同时左乘 $S$，其余参数不变，给保持 $A,|\eta|,\zeta,\mathscr R$ 及不利条件的双射。因此

$$
K_r(h)=K_{-r}(-h).
\tag{43.18}
$$

设 $\mathcal K(g)=K_+(g)$，则 $K_-(h)=\mathcal K(-h)$；源对齐图中的方程和值函数只依赖 $g$。这个反射改变 $h$ 的符号，并不比较同一正 $h$ 的两个阈值。

在假设 (43.16) 下，$\mathcal M$ 非空且紧：非空及全部极小点的存在由定理 42.1 给出，联合紧性和相位商保证紧性。连续函数 $|P'|$ 在它上面有正下界。有限个隐函数图因而覆盖 $\mathcal M$，每个图都以 $x,y$ 为自由参数、$g$ 为微扰参数；缩小邻域后所有值展开有一致 $o(|g|)$ 余项。$\mathcal D$ 连续，故在整个 $\mathcal M$ 上取到最小值和最大值。

延续任一 $\mathcal M$ 成员即给 $\mathcal K(g)\le\mathcal K(0)+O(|g|)$。另一方面，对任何 $g_j\to0$ 的全局极小接触列，联合紧性给收敛子列；其极限是零阶完整接触，比值极限不超过 $\mathcal K(0)$，又不能小于零阶下确界，故属于 $\mathcal M$。因此全部小 $g$ 极小点到 $\mathcal M$ 的距离趋于零，并最终落在上述有限图内。

对每个实际移动极小点，沿它所在的图将 $g$ 置零、保持其 $x,y$，得到零阶完整不利接触 $c^0_g$，其值至少为 $\mathcal K(0)$。这些零阶对应点也趋于 $\mathcal M$。局部值展开给

$$
\mathcal K(g)=\mathcal R_0(c^0_g)+g\mathcal D(c^0_g)+o(|g|),
$$

余项一致；所以对 $g>0$，下界为 $\mathcal K(0)+g\min_{\mathcal M}\mathcal D+o(g)$，对 $g<0$，下界为 $\mathcal K(0)+g\max_{\mathcal M}\mathcal D+o(|g|)$。上界分别由延续取得 $\min\mathcal D$、$\max\mathcal D$ 的成员给出。于是

$$
\begin{aligned}
\mathcal K(g)&=\mathcal K(0)+g\min_{\mathcal M}\mathcal D+o(g),&&g\downarrow0,\\
\mathcal K(g)&=\mathcal K(0)+g\max_{\mathcal M}\mathcal D+o(|g|),&&g\uparrow0.
\end{aligned}
\tag{43.19}
$$

两式相减并用 (43.18) 得 (43.17)。此证明不要求唯一极小点或二次增长，却必须在整个零阶极小集上有 (43.16)。∎

### 43.5 数学来源与尚未解决的比较

本链的数学来源为《full-contact-positive-side-answer》的全接触约化、非消失、共同正性与紧性推导，《supported-B-only》的定理 1 及其 (1)–(22)、源反射式 (60)，以及《supported-C-artifact》的完整图方程、三次枚举与条件微扰推导。这里保留它们的承重条件并给出普通证明；文献状态为 `repo-derived`，不作全球原创性主张。既有矩消元、完整轴分类、非轴重构、同源取向对称性、全部正泛函 PB/P2 桥梁与精确接触稠密性，分别直接引用引理 39.2、定理 39.4–39.5、命题 39.6–39.7、§37 及定理 40.2。实解析隐函数定理的成熟工具出处沿 §40.4 所引 Krantz–Parks；有限维紧性、Cauchy–Schwarz 及算子范数估计用其通常形式。

仍需在整个零阶三次根轨迹

$$
P(x,y,t)=0,\qquad x\ne0,\quad |y|>1,\quad t>0,\quad y(4t-1)>0
$$

上确定全局最小值和全部极小根；固定 $\ell$ 至多三根并未完成这个连续参数的全局问题。对简单根上的内部极小候选，必要条件还包括

$$
(\partial_x\mathcal R_0)P_t-(\partial_t\mathcal R_0)P_x=0,\qquad
(\partial_y\mathcal R_0)P_t-(\partial_t\mathcal R_0)P_y=0.
$$

它们由 $P=0$ 上 $t_x=-P_x/P_t$、$t_y=-P_y/P_t$ 及受约束值的一阶必要条件得到；不声称该系统已解、解孤立或穷尽重根。特殊集 $P=P_t=0$ 必须另行保留，尤其不能排除它含有全局极小点；若有这样的点，定理 43.5 的全极小集假设不成立，需要分析其完整奇异分支与单侧持续性。

即使 (43.16) 成立，还须计算包含强制根运动的 $\min\mathcal D+\max\mathcal D$；若为零，一阶式不能决定来源差异。单独的 $\operatorname{Re}(\overline GE_1)$ 或 $\mathcal S$ 的符号均不能替代完整系数。$K_+(h)=K_-(h)$ 或同一固定正 $h$ 下的严格排序、同一正 $h,k$ 且共同完整 P2 内的一成一败比较，仍未解决。

由定理 41.4、42.1，$k=K_r(h)$ 时有实际接触使 $J_k=0$；这仍只给零领先值。临界有限 $\lambda$ 的次阶符号、有限 PB 变分取到性及物理实现均不由接触达到性推出。有限原结论始终保留 (41.3)、(41.19) 的参数交，并使用全部原探针与完整正泛函范围。

## 追加锚（本行以下为增补区）

## 44. 两异常系数切片、完整正则性与多重根包络

本节继续使用 §§39–43 的固定实际来源
$a_r=(1/\sqrt2,r)^{\mathsf T}$、全部原探针、完整正泛函、两笔预算、两取向及共同完整 P2 参数交。所有接触仍由定理 43.2 的四实图条件和两个来源坐标重构；本节只细化零阶多项式的异常系数、完整约束的正则性以及其条件微扰包络。

### 44.1 两个系数零集

**引理 44.1（首项和常数项的精确零集）。** 令 $q=y^2>1$。在定理 43.3 的固定 $\ell=x+iy$ 图中，

$$
\begin{aligned}
f_1&=\frac{6(x-1)}x\left[1-i\frac{q+x^2-x}{y}\right],\\
g_0&=-\frac{3(x+1)}{2x}\left[1-i\frac{q+x^2-2x}{2y}\right].
\end{aligned}
\tag{44.1}
$$

因此 $f_1=0$ 当且仅当 $x=1$，而 $g_0=0$ 当且仅当 $x=-1$。在 $x=1$ 上 $P$ 恰为二次式；在 $x=-1$ 上 $P$ 仍为三次式但有根 $t=0$。

**证明。** 由 (43.2)，
$\partial_t\alpha_0=6(x-1)/y$ 和 $\partial_t\kappa_0=-6(x-1)/x$。代入 $F=i(1-\ell)(\alpha_0+i\kappa_0)-(2-\ell/2)$，并用
$i(1-\ell)\overline\ell=y-i(q+x^2-x)$，得到第一式。对 $t=0$，$\chi_0=-3(x+1)/(2y)$、$\kappa_0=-3(x+1)/(2x)$；代入 $G=i(1-\ell/2)(\chi_0-i\kappa_0)-(4-2\ell)t$，得到第二式。两方括号的实部都是 $1$，而 $x\ne0$，故零集恰如所述。又 $2|f_1|^2$ 是 $P$ 的三次首项，$-|g_0|^2$ 是常数项，所以两条结论同时成立。∎

### 44.2 降阶线 $x=1$ 的全部正根

**定理 44.2（降阶线的判别式、正根和代价）。** 固定 $x=1$，置 $q=y^2>1$、$M_+=(q+1)(q+9)$、$B_+=13q^2-39q-36$。则

$$
\begin{aligned}
F(t)&=-\frac{3+5iy}{2},\\
G(t)&=-3-8t+i\frac{3(q-1)+4(q-3)t}{2y},\\
4qP(t)&=-16M_+t^2+2B_+t-9(q+1)^2.
\end{aligned}
\tag{44.2}
$$

令

$$
H_+(q)=25q^3-2742q^2-3735q-1224.
\tag{44.3}
$$

则

$$
B_+^2-144(q+1)^3(q+9)=qH_+(q).
\tag{44.4}
$$

$H_+$ 恰有一个正根 $q_+$，且 $100<q_+<120$。当 $1<q<q_+$ 时没有正根；当 $q=q_+$ 时只有一个不同正根

$$
t_+=\frac{B_+}{16M_+},
\tag{44.5}
$$

且其重数为二；当 $q>q_+$ 时有两个不同正根

$$
t_{\pm}=\frac{B_+\pm\sqrt{qH_+(q)}}{16M_+}.
\tag{44.6}
$$

所有这些正根都满足

$$
\frac14<t<\frac{13}{8}.
\tag{44.7}
$$

所以它们只有在 $y>0$ 时通过不利过滤。每个不利根的零阶代价满足

$$
\mathcal R_0(1,y,t)
=\frac{\sqrt q(9+25q)}{12(q-1)(4t-1)}>\frac{125}{33}>\frac65.
\tag{44.8}
$$

**证明。** 将 $x=1$ 代入 (43.2) 得到 (44.2)。二次判别式为
$H_+(q)/(4q)$，而 (44.4) 是直接展开后的恒等式。函数

$$
\frac{H_+(q)}{q^2}=25q-2742-\frac{3735}{q}-\frac{1224}{q^2}
$$

在 $q>0$ 上严格递增；并且
$H_+(100)=-2794724<0$、$H_+(120)=3265776>0$，故正根唯一且落在所给区间。对 $q\ge q_+>100$，$B_+>0$，二次式的根的和与积均为正，故两个根均为正。又

$$
B_+-4M_+=9q^2-79q-72>0,
$$

所以顶点 $B_+/(16M_+)>1/4$。由于 $P(1/4)=-(7q^2+95q+72)/(8q)<0$，两根都在 $1/4$ 的右侧。根的和为 $B_+/(8M_+)<13/8$，得到 (44.7)。最后 $4t-1<11/2$，且 $q>100$，所以

$$
\mathcal R_0>\frac{25q^{3/2}}{66(q-1)}>\frac{125}{33}.
$$

当 $q=q_+$ 时取 $\ell=1+i\sqrt{q_+}$、$t=t_+$，由 (43.8) 唯一恢复 $\tau$，再由定理 43.2 恢复 $P,Q,a_{\rm act}$ 和两个实际来源坐标。这是完整四实图条件下的合法正双根；但二次式没有另一不同有限正根。它只反驳无条件的固定 $\ell$ 换根断言，不反驳低代价全局极小集的受限问题。∎

### 44.3 常数项零线 $x=-1$ 的三次分类

**定理 44.3（零常数项线的全部正根与统一代价排除）。** 固定 $x=-1$，置 $q=y^2>1$、$M_-=(q+1)(q+4)$、$B_-=11q^2+75q-72$、$C_-=q^2+97q+144$。则

$$
\begin{aligned}
F(t)&=-\frac{11}{2}+12t+i\left(\frac{q-12}{2y}-\frac{12(q+2)}y t\right),\\
G(t)&=(-24+8iy)t,\\
P(t)&=\frac{t}{2q}Q(t),\\
Q(t)&=576M_-t^2-16B_-t+C_-.
\end{aligned}
\tag{44.9}
$$

令

$$
H_-(q)=28q^3+183q^2-414q-5193.
\tag{44.10}
$$

则

$$
B_-^2-9M_-C_-=4qH_-(q).
\tag{44.11}
$$

$H_-$ 恰有一个正根 $q_-$，且 $4<q_-<5$。当 $1<q<q_-$ 时 $Q$ 无实根；当 $q=q_-$ 时 $Q$ 有唯一不同正根

$$
t_-^{\rm dbl}=\frac{B_-}{72M_-},
\tag{44.12}
$$

且其重数为二；当 $q>q_-$ 时 $Q$ 有两个不同正根

$$
t_\pm=\frac{B_-\pm2\sqrt{qH_-(q)}}{72M_-}.
\tag{44.13}
$$

所有正根 $t\ne1/4$ 的代价都满足

$$
\mathcal R_0(-1,y,t)>\frac65.
\tag{44.14}
$$

特别地，取 $y=-\sqrt{q_-}$ 和 (44.12)，则 $0<t_-^{\rm dbl}<1/4$，它是一个真正三次的唯一不同正根；$t=0$ 是被非轴图排除的根，且该双根通过不利过滤。

**证明。** 代入 $x=-1$ 直接得到 (44.9)。判别式恒等式为 (44.11)。函数

$$
\frac{H_-(q)}q=28q^2+183q-414-\frac{5193}{q}
$$

在 $q>0$ 上严格递增，且 $H_-(4)=-2129<0$、$H_-(5)=812>0$，故正根唯一。对 $q\ge q_->4$，$B_->0$，根的和与积为正，因而 (44.13) 的两个根均为正。并且

$$
18M_--B_-=7q^2+15q+144>0,
$$

所以 (44.12) 严格小于 $1/4$。

若 $t>1/4$，由 $P(t)=0$ 得 $|F(t)|^2=32(q+9)t$，故

$$
\mathcal R_0(-1,y,t)
=\frac{32\sqrt q(q+9)t}{3(q-1)(4t-1)}
>\frac{8\sqrt q(q+9)}{3(q-1)}>\frac83.
\tag{44.15}
$$

若 $0<t<1/4$，由 $Q(t)=0$ 得
$C_-=16B_-t-576M_-t^2<16B_-t$，从而

$$
\mathcal R_0(-1,y,t)>L(q):=\frac{2\sqrt q(q+9)C_-}{3(q-1)B_-}.
\tag{44.16}
$$

写 $z=\sqrt q>1$。交叉相乘后 $L(q)>6/5$ 等价于 $S(z)>0$，其中

$$
\begin{aligned}
S(z)&=5z(z^2+9)(z^4+97z^2+144)\\
&\quad-9(z^2-1)(11z^4+75z^2-72)\\
&=5z^5(z-10)^2+z^6+30z^3\left(z-\frac{48}{5}\right)^2\\
&\quad+\frac{11601}{5}z^3+1323z^2+6480z-648.
\end{aligned}
\tag{44.17}
$$

最后一行在 $z>1$ 上严格为正，故 (44.14) 成立。这里 $t=1/4$ 的 $\zeta$ 为零，不属于不利代价。双根处 $G=(-24+8iy)t_-^{\rm dbl}\ne0$，而 $P=0$ 又给 $F\ne0$，所以 (43.8) 和定理 43.2 确实恢复完整接触。由于 $P=tQ/(2q)$，该点没有另一不同正根；这修正了把“首项非零”误当作“常数项严格负”的推理。∎

### 44.4 低代价极小集远离两个异常切片

**定理 44.4（统一分离与剩余三次域）。** 存在 $0<\bar h\le h_0$、$\delta>0$ 和 $b_*>0$，使对 $r=\pm1$、两个取向以及所有 $|h|\le\bar h$ 的完整不利接触，只要

$$
\mathcal R\le K_{\rm ax}-\gamma_0,
\tag{44.18}
$$

就有

$$
|x-1|\ge\delta,\qquad |x+1|\ge\delta,\qquad
|f_1|\ge b_*,\qquad |g_0|\ge b_*.
\tag{44.19}
$$

特别地，定理 42.1 的全部零阶全局极小点满足 (44.19)。在这些点上 $P$ 是真正三次，首项 $2|f_1|^2$ 为正、常数项 $-|g_0|^2$ 为负。若此 $P$ 有正的二重根 $t_0$，则

$$
P(t)=2|f_1|^2(t-t_0)^2(t-s),\qquad s>0;
\tag{44.20}
$$

若为三重根，则 $s=t_0$。这只保证另一根的正性，不保证其不利过滤或代价严格更低。

**证明。** 定理 41.4 的低子水平集在共同变量、来源和取向上紧，且定理 42.1 给出的全局极小值均落入其中。若不存在统一的第一条分离，可取 $h_n\to0$ 的接触列并令 $x_n\to1$；紧性给出零阶极限，其代价不超过 $6/5$，但定理 44.2 给出的整个 $x=1$ 非轴切片不利代价大于 $125/33$，矛盾。令 $x_n\to-1$ 同理与定理 44.3 的 $6/5$ 严格下界矛盾。故得到某个 $\delta>0$。在定理 41.4 的统一界 $|x|<600$ 下，(44.1) 给出

$$
|f_1|\ge\frac{|x-1|}{100},\qquad
|g_0|\ge\frac{|x+1|}{400};
$$

减小 $b_*$ 即得 (44.19)。于是 $f_1g_0\ne0$，多项式的次数和常数项符号如述。对正二重根作因式分解并比较常数项，得到
$-|g_0|^2=-2|f_1|^2t_0^2s$，故 $s>0$。三重根是同一因式分解的 $s=t_0$ 情形，没有被排除。∎

### 44.5 根投影正则性与完整接触正则性

令 $z=(x,y,t)$、$\tau=\sqrt t\,e^{i\theta}$，并在零阶接触处定义

$$
C_0(z,\theta)=\bigl(\operatorname{Re}E_0(\tau),\operatorname{Im}E_0(\tau)\bigr)\in\mathbb R^2.
\tag{44.21}
$$

**定理 44.5（完整 Jacobian 的精确判据）。** 在任一零阶非轴接触处，

$$
\operatorname{rank}D_{(x,y,t,\theta)}C_0=2
\quad\Longleftrightarrow\quad
\nabla_{x,y,t}P\ne0.
\tag{44.22}
$$

所以 $P_t=0$ 只表示以 $t$ 为投影坐标的根轨迹奇异；只要 $P_x$ 或 $P_y$ 非零，完整四实接触约束仍然正则。

**证明。** 定理 43.3 给出 $G\ne0$，而在接触上

$$
\partial_\theta E_0=-iG\ne0.
\tag{44.23}
$$

对 $j=x,y,t$ 直接微分 $P=2t|F|^2-|G|^2$，并使用 $G=\sqrt2F\overline\tau$，得到

$$
P_j=2\operatorname{Re}\bigl(\overline G\,\partial_jE_0\bigr).
\tag{44.24}
$$

对 $j=t$，$\partial_t\overline\tau=\overline\tau/(2t)$ 产生的附加项正好给出 $2|F|^2$，故 (44.24) 仍成立；这是不能把 $t$ 当作常数的关键。令 $w_\theta=\partial_\theta E_0=-iG$，则

$$
P_j=2\operatorname{Im}\bigl(\overline{w_\theta}\,\partial_jE_0\bigr).
\tag{44.25}
$$

右侧是 $\partial_jE_0$ 在 $w_\theta$ 的实正交方向上的坐标。由于 $w_\theta\ne0$，四个实列向量的秩为一，当且仅当三个 $z$ 列都与 $w_\theta$ 实平行；由 (44.25) 这又当且仅当 $P_x=P_y=P_t=0$。秩只能为一或二，故 (44.22) 成立。∎

### 44.6 完整约束下的全极小集一阶包络

令

$$
\mathcal C_g(z,\theta)=\bigl(\operatorname{Re}E_g(\sqrt t e^{i\theta}),
\operatorname{Im}E_g(\sqrt t e^{i\theta})\bigr),
$$

令 $\mathcal R_g(z,\theta)$ 表示 (43.4) 的原比值，且令 $\mathcal M$ 为 $g=0$ 的整个不利零阶全局极小集（两个 $y$ 符号均包含）。

**定理 44.6（完整正则条件下的双侧全局包络）。** 假设对每个 $c\in\mathcal M$，

$$
\operatorname{rank}D_{(z,\theta)}\mathcal C_0(c)=2.
\tag{44.26}
$$

由于 $c$ 是严格过滤条件下约束流形上的全局极小点，约束一阶必要条件给出唯一的 $\lambda(c)=(\lambda_1,\lambda_2)\in\mathbb R^2$，满足

$$
D_{(z,\theta)}\mathcal C_0(c)^{\mathsf T}\lambda(c)
=\nabla_{(z,\theta)}\mathcal R_0(c).
\tag{44.27}
$$

唯一性来自 (44.26) 的满行秩。

定义

$$
\Phi(c)=\partial_g\mathcal R_g(c)|_{g=0}
-\lambda_1(c)\operatorname{Re}E_1(c)
-\lambda_2(c)\operatorname{Im}E_1(c).
\tag{44.28}
$$

则 $\lambda$ 和 $\Phi$ 在 $\mathcal M$ 上连续，并且

$$
\begin{aligned}
K_+(h)&=K_+(0)+h\min_{c\in\mathcal M}\Phi(c)+o(h),&&h\downarrow0,\\
K_+(g)&=K_+(0)+g\max_{c\in\mathcal M}\Phi(c)+o(|g|),&&g\uparrow0.
\end{aligned}
\tag{44.29}
$$

特别地，由既有源反射 (43.18)，

$$
K_+(h)-K_-(h)
=h\left(\min_{c\in\mathcal M}\Phi(c)+\max_{c\in\mathcal M}\Phi(c)\right)+o(h),
\qquad h\downarrow0.
\tag{44.30}
$$

在 (43.13) 的记号下，$\partial_g\mathcal R_g|_0=\mathcal S$，所以 (44.28) 是包含全部强制根运动的完整系数。由 (44.31)，$\Phi(c)$ 等于通过 $c$ 的可行延续的点值导数，乘子修正可以为零；(44.29)–(44.30) 的全局包络依赖整个 $\mathcal M$ 上的 $\Phi$，不能由单独的 $\mathcal S$ 或任选一根的导数替代。

**证明。** 由 (44.26)，每个 $c\in\mathcal M$ 有一个隐函数坐标图：在保留两个自由坐标的同时，用两个接触坐标解出 $\mathcal C_g=0$。沿任一这样的可行曲线 $w(g)$ 有

$$
D_w\mathcal C_0(c)w'(0)+\partial_g\mathcal C_g(c)|_0=0.
$$

(44.27) 因而给出

$$
\frac d{dg}\mathcal R_g(w(g))\bigg|_{0}
=\partial_g\mathcal R_g|_0+\nabla\mathcal R_0\cdot w'(0)
=\Phi(c).
\tag{44.31}
$$

秩条件、紧性和连续性使 $\mathcal M$ 有限个这样的图覆盖，并使 (44.31) 的一阶余项一致。每个图给出相应的可行延续，故正 $g$ 的上界由 $\min_{\mathcal M}\Phi$ 给出，负 $g$ 的上界由 $\max_{\mathcal M}\Phi$ 给出。反过来，取任意 $g_n\to0$ 的全局极小接触列；定理 41.4 的联合紧性给出收敛子列，其极限属于 $\mathcal M$。把移动点投回 $g=0$ 的同一图，零阶值不低于 $K_+(0)$，而 (44.31) 给出统一下界。上下界相合，得到 (44.29)。最后用 (43.18) 把 $K_-(h)$ 写成 $K_+(-h)$，即得 (44.30)。此证明只要求完整接触秩条件，不要求 $P_t\ne0$、根简单、极小点唯一或二次增长。∎

### 44.7 合法下降、固定参数凸性与真正剩余的奇异系统

在一个固定的 $\ell=x+iy$ 和不利符号扇区内，令

$$
C_y=\frac{|y|}{3(y^2-1)},\qquad \sigma=\operatorname{sgn}(y),\qquad z_t=4t-1,
$$

并置 $B=F(1/4)$、$w=|f_1|^2/16$、$c_B=|B|^2$。则在 $\sigma z_t>0$ 时有精确恒等式

$$
\mathcal R_0
=C_y\sigma\left[wz_t+\frac12\operatorname{Re}(\overline Bf_1)+\frac{c_B}{z_t}\right],
\qquad
\partial_t\mathcal R_0=4C_y\sigma\left(w-\frac{c_B}{z_t^2}\right).
\tag{44.32}
$$

若 $Bf_1\ne0$，则第二导数为 $32C_y\sigma c_B/z_t^3>0$。因此固定 $\ell$ 的每个内部临界点是该不利扇区中固定参数值的唯一全局极小点；这不能推出另一合法根存在，也不能推出另一根的值更低。

**命题 44.7（重根的实际下降判据）。** 若零阶不利接触满足

$$
P=P_t=0,\qquad (P_x,P_y)\ne(0,0),\qquad \partial_t\mathcal R_0\ne0,
\tag{44.33}
$$

则存在保持两个实际来源坐标、四实图条件和不利过滤的精确接触曲线，使 $\mathcal R_0$ 严格下降。因此任何重根全局极小点必须满足

$$
\nabla P=0,
\quad\text{或}\quad
(P_x,P_y)\ne(0,0),\ \partial_t\mathcal R_0=0.
\tag{44.34}
$$

在第二种情形，受约束一阶必要条件还给出

$$
P=0,\quad P_t=0,\quad \partial_t\mathcal R_0=0,\quad
(\partial_x\mathcal R_0)P_y-(\partial_y\mathcal R_0)P_x=0.
\tag{44.35}
$$

**证明。** 若 $P_x\ne0$，由隐函数定理在保持 $y$ 不变时解出 $x=x(t)$；若 $P_y\ne0$，交换 $x,y$。在基点 $x'(t)=-P_t/P_x=0$（或 $-P_t/P_y=0$），故曲线上的值导数就是 $\partial_t\mathcal R_0$。取 $t$ 的相反方向即可得到严格下降；所有不利条件是开条件，相位由 (43.8) 唯一连续恢复。第二种情形若为局部极小，完整梯度条件 $\nabla\mathcal R_0=\mu\nabla P$ 给出 (44.35)。∎

真正尚未支付的完整约束奇异集合是

$$
P=P_x=P_y=P_t=0.
\tag{44.36}
$$

(44.36) 与三重根或普通重根并不等价：$P_t=0$ 而 $P_x\ne0$ 的点由定理 44.5 仍是完整正则接触；反之，(44.36) 才需要奇异分层和单侧持续性分析。定理 44.4 保留低代价真三次域中的三重根可能性，定理 44.6 则把来源比较准确缩到 (44.26) 或 (44.36) 的两种分支。

## 45. 数学来源、适用条件与未解边界

引理 44.1、定理 44.2–44.6 以及命题 44.7 是基于 §§39–43 的模型特定推导（`repo-derived`）。所用的成熟工具是二次判别式与根的符号、实解析隐函数定理、紧集一致展开、等式约束的一阶必要条件和有限维正性分解。式 (44.17) 是给 $x=-1$ 切片的显式正性证书，式 (44.22) 是原复接触方程的完整实 Jacobian 判据，式 (44.28) 是完整来源约束下的条件包络系数。

模型条件仍包括轴、两取向、两来源坐标、完整正泛函、两笔预算和共同完整 P2 参数交。尚未证明 (44.26) 在整个 $\mathcal M$ 上成立，尚未排除 (44.36)，尚未确定 (44.30) 的符号或同一正 $h$ 下的严格来源排序。$x=1$ 与 $x=-1$ 的反例只否定无条件的固定参数换根命题；定理 44.4 只把它们从足够小参数的低子水平全局极小集中排除，不能替代一般 $x\ne\pm1$ 的重根分析。

同一正 $h,k$、共同完整 P2 内一成一败的比较，以及阈值等号的有限 $\lambda$ 次阶符号、有限 PB 变分达到性和物理取得，均仍未解决。所有有限 PB 结论继续受 (41.3)、(41.19) 及原全部探针和正泛函量词约束；接触达到性不能推出有限 PB 变分达到性或物理取得，源反射也不能替代同一正 $h$ 下的来源排序。

## 追加锚（本行以下为增补区）
