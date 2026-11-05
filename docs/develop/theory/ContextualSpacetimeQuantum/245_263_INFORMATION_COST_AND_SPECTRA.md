# 情境时空算术的量子扩展：信息代价、变化界与谱隙

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](225_244_REAL_AND_COMPLEX_PROGRAMS.md) · [续卷](264_283_REAL_SYMMETRY_AND_RECOVERY.md)


<a id="entry-838"></a>

## 追加锚（本行以下为增补区）

<a id="section-245"></a>

## 245. 同一准备的端点代价上界与区间积分阶

**定理 245.1（尾窗发散阶的共同达到）。** 沿用第243、244节的实际任务、内部窗口、两个全域资源及尾窗 $T_s=T_s(\delta_s)$。给定任意 $0<e_s=o(s)$ 和任意预算分配

$$
\delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,
\qquad \Delta_s=h_3(s)-p_{\delta_s},
\tag{245.1}
$$

存在同一族解析准备，使 $K_s$ 上的 Fisher 峰值和积分一致有界，并且

$$
\sup_{T_s}I_Q=O(e_s^{-2}),
\qquad
\int_{T_s}I_Q\,du=O(s/e_s).
\tag{245.2}
$$

在完整的两个指定节点之间，同一族还满足

$$
\sup_{[u_1,u_3]}I_Q=O(e_s^{-2}),
\qquad
\int_{u_1}^{u_3}I_Q\,du
=O\!\left(\frac{s}{e_s}+\log\frac1s\right).
\tag{245.3}
$$

上界保持实际支持四、全输入精确性、完整尖锐集合、普通最优双侧曲率及任意预先指定的有限阶实规范节点数据，并可取每点秩至多二。两个零预算边精确保持纯性或实性；常数对预算分配方向一致。不要求预算随 $s$ 解析或连续，也不要求解析逼近次数、延拓半径对 $s,e_s$ 一致。本节只匹配发散阶，不主张达到第244节的下界常数。

证明。 先构造纯准备，再作固定权重共轭混合。以下均在第225.2式的同一个处理器中工作；$a=a_{\rm c}(s)$，$k_s,B_s$ 与前节相同。

在 $K_s$ 右侧选两个固定位置 $p_A<p_B<1$，都处于靠近一的共同正则实圆区域。在这个固定区间上沿实矩圆，把第一规范分支连接到实单位相位基底 $v_s(p)$，后者满足

$$
k_s^{\mathsf T}v_s(p)=0,
\qquad p\,v_s(p)^{\mathsf T}B_sv_s(p)=a_s,
\qquad \|v_s(p)\|=1.
\tag{245.4}
$$

选择其符号，使 $-v_s$ 与第三规范分支具有相同的极限 $z,w$ 符号。两个实圆以 $w$ 符号区分，故这一基底属于第一规范分支所在的圆，其相反数属于第三支所在的圆。固定区间内的连接和足够平坦的拼接具有统一有界的一阶导数，且位于 $K_s$ 之外。

在整个 $[p_B,h_3(s)]$，式（245.4）的两条独立实方程及单位球面给出含参正则解，满足

$$
\|\partial_pv_s(p)\|\le C.
\tag{245.5}
$$

其定义方程不含 $\sqrt{1-p}$；极限解由 $y=0$、$p(z^2-w^2)=\alpha$ 给出，所取符号下 $z,w$ 都有正的绝对值下界。故该导数控制一直保持到移动第三节点。

还需量化从 $-v_s$ 到第三规范分支的短实臂。以 $v_{3,s}(p)$ 表示第三规范纯态的非核单位部分。其实际不变三维空间由 $V_s$ 的 $0,\mu,-r$ 三条特征线张成，非核坐标满足

$$
y=
\frac{s_\lambda s_\mu}{\mu-\lambda}\,z+
\frac{s_\lambda s_r(1-\lambda\mu)}
{(\mu-\lambda)(r+\lambda)}\,w.
\tag{245.6}
$$

这里 $s_t=\sqrt{1-t^2}$。例如 $\mu$ 特征向量满足 $y=s_\lambda s_\mu z/(\mu-\lambda)$；$-r$ 特征向量满足 $z=-s_\mu s_rw/(\mu+r)$，代入第二行即可得到（245.6）的另一个系数。核向量 $q$ 不改变这一非核关系。

由于 $\lambda\to2\alpha<1$、$\mu,r\to1$，式（245.6）的两个系数都是 $O(s)$。所以 $y=O(s)$、$k_s^{\mathsf T}v_{3,s}=O(s)$ 一致成立。在同一 $z,w$ 符号图中，归一化与实矩方程的 Jacobian 有统一正下界。微分实矩时，唯一可能变大的系数来自 $\partial_p\sqrt{p(1-p)}$，但其乘子 $k_s^{\mathsf T}v_{3,s}=O(s)$，且 $\sqrt{1-p}\ge\sqrt{1-h_3(s)}\ge c s$。于是

$$
\|\partial_pv_{3,s}(p)\|\le C,
\qquad
\|v_{3,s}(p)+v_s(p)\|\le Cs
\quad(p_B\le p\le h_3(s)).
\tag{245.7}
$$

第二个估计也可直接由两组方程作比较：两者的 $y$ 坐标均为 $O(s)$，目标矩中剩余差别为 $O(s)$，同一个实隐函数图将它们变为 $O(s)$ 的 $z,w$ 差。

在端点短臂中以 $y$ 为自由坐标，解归一化和实矩方程得到 $z,w$。此处 $z,w$ 有统一的非零下界，$|y|=O(s)$。在宽度与 $\Delta_s$ 可比的窗口内，以固定平坦函数插值两端 $y$ 值；两端之差为 $O(s)$，两端随 $p$ 的导数有界，因此该实精确臂满足

$$
\|\partial_pv_{\rm arm}\|
\le C\left(1+\frac{s}{\Delta_s}\right).
\tag{245.8}
$$

接着分配实际尾窗。将半相位圆 $e^{i\theta}v_s(p)$ 放在

$$
p_{\delta_s}+\frac{\Delta_s}{4}
\le p\le
p_{\delta_s}+\frac{\Delta_s}{2},
\tag{245.9}
$$

以固定平坦调度令 $\theta$ 从零变到 $\pi$，故 $|\partial_p\theta|\le C/\Delta_s$。下一四分之一尾窗用于（245.8）的实短臂，最后四分之一保持第三规范分支。整个半相位圆的矩精确性由（245.4）保证。

资源预算需要一个相对于 $e_s$ 的严格余量。令 $f(p)=2\sqrt{p(1-p)}$。在 $T_s$ 内，$|f'(p)|$ 与 $1/s$ 一致可比；又由第244.12式的精确差商，$\Delta_s\asymp s e_s$。中值定理因而给出

$$
\delta_s-
 f\left(p_{\delta_s}+\frac{\Delta_s}{4}\right)
\ge c e_s>0.
\tag{245.10}
$$

实背景和实短臂的虚性为零；半相位圆的虚性为 $f(p)|\sin\theta|$。故整个背景具有至少 $c e_s$ 的资源余量。这一估计不将一个 $s$ 的渐近余项与任意小的 $e_s$ 相减。

下面核对信息量的实际参数。对
$\psi(p)=\sqrt{1-p}\,q+\sqrt p\,e^{i\theta(p)}v_s(p)$，以撇号表示 $p$ 导数，而 Fisher 信息仍针对 $u=2p-1$，纯态公式直接给出

$$
I_Q(\psi\psi^\dagger)
=\frac1{4p(1-p)}
+p(1-p)(\theta')^2+p\|v_s'\|^2.
\tag{245.11}
$$

实单位向量 $v_s$ 与其导数正交，故相位与实方向的交叉项为零；$u$ 与 $p$ 的导数因子已包含在式中。实准备对应 $\theta'=0$。由（245.5）、（245.8）和（245.9），整个尾窗上有

$$
\begin{aligned}
\sup_{T_s}I_Q
&\le C\left(s^{-2}+\frac{s^2}{\Delta_s^2}\right),\\
\int_{T_s}I_Q\,du
&\le C\left(\frac{\Delta_s}{s^2}
+\frac{s^2}{\Delta_s}\right).
\end{aligned}
\tag{245.12}
$$

因为 $\Delta_s\asymp s e_s$ 且 $e_s=o(s)$，（245.12）给出（245.2）。

在尾窗之前，固定区间的实连接代价为 $O(1)$；相位基底的实延伸由（245.5）、（245.11）给出 $I_Q\le I_r+C$。第一规范分支在 $[u_1,2p_A-1]$ 上有统一导数界。故整个节点区间的峰值为 $O(e_s^{-2})$，积分除尾窗外至多增加 $O(1+\log(1/s))$，得到（245.3）的背景界。

最后完成全域解析化。半相位圆和实臂的完整复矩微分由第243节的精确核恒等式保证处处正则；规范尾部在紧化端点的正则性也按该节保持。对每个固定任务和预算，选择足够精细的多项式逼近、有限 Hermite 匹配、归一化及解析二矩修正，使全域资源误差小于（245.10）的一半，同时使整个 $[u_1,u_3]$ 上密度一阶导数的迹范数误差至多一。节点附近保持预定规范有限阶数据。

纯态的 $I_Q=\|\rho'\|_1^2$ 因而给出最终峰值不超过背景平方根峰值加一后的平方；积分可用 $I_Q^{\rm final}\le2I_Q^{\rm bg}+2$ 控制。这同时保留尾窗和完整节点区间的所有阶上界。$K_s$ 的背景始终是第一规范分支，故其两个代价继续一致有界。全输入矩精确性、规范节点数据、谱必要性及曲率夹逼分别保持所列全部任务条件。

取固定参数 $\tau_s=\eta_s/\delta_s$，将最终纯态按第240.8式作共轭混合。其精确资源公式分别给出 $I_R^C\le\eta_s$、$J\le\zeta_s$；点态 SLD 凸性同时保留（245.2）、（245.3）和 $K_s$ 的两个界。混合秩至多二；零预算边、实际支持四、完整尖锐集合及有限节点数据均按第240、243节保持。证毕。

**推论 245.2（低内部代价族的完整区间积分阶）。** 在定理245.1的预算尺度下，每一族满足第244.9式任一低内部代价条件的允许准备都满足

$$
\sup_{[u_1,u_3]}I_Q=\Omega(e_s^{-2}),
\qquad
\int_{u_1}^{u_3}I_Q\,du
=\Omega\!\left(\frac{s}{e_s}+\log\frac1s\right).
\tag{245.13}
$$

定理245.1的同一准备族达到相反方向的阶上界。因此在这类准备中，最优可达到的尾窗峰值与积分阶分别为 $e_s^{-2}$、$s/e_s$，最优可达到的完整节点区间积分阶为 $s/e_s+\log(1/s)$。此处阶匹配不表示两个有限任务下确界由同一个极小元取得。

证明。 第244节给出尾窗的两个必要下界，尾窗包含于节点区间。每个精确准备还满足固定读出界 $I_Q(u)\ge I_r(u)=1/(1-u^2)$，因而

$$
\begin{aligned}
\int_{u_1}^{u_3}I_Q(u)\,du
&\ge\frac12\log
\frac{h_3(s)(1-h_1(s))}{h_1(s)(1-h_3(s))}\\
&=\log\frac1s+O(1).
\end{aligned}
\tag{245.14}
$$

这里使用 $h_1(s)\to c_*\in(0,1)$、$1-h_3(s)=D_*s^2+O(s^3)$。两个下界针对同一个准备同时成立，故其最大值至少为和的一半，给出（245.13）。上界已由定理245.1的同一族提供。证毕。

**注记 245.3（读出背景与端点集中分别计量）。** 尾窗集中贡献 $s/e_s$ 阶积分，整个节点区间的读出背景还贡献 $\log(1/s)$ 阶。两者哪一项占主导取决于实际余量；例如 $e_s=s/\sqrt{\log(1/s)}$ 时，读出背景更大，不能把完整区间积分统一写成 $O(s/e_s)$。

本节量化的是第243节同一实际相位桥的调度和第244节同一尾窗的代价，未改变资源或目标。纯态 Fisher 公式、固定权重凸性、实隐函数图和 Hermite 解析逼近都是前节已使用的工具。尚未确定的是最优领先系数及其对两种预算分配的依赖；阶上界不作这些主张。

<a id="entry-840"></a>

## 追加锚（本行以下为增补区）

<a id="section-246"></a>

## 246. 全实准备的尾窗最优领先系数

**定理 246.1（两个端点代价常数的共同达到）。** 沿用第243—245节的实际任务及尾窗。令 $s\downarrow0$，给定任意 $0<e_s=o(s)$，并固定在全实预算边

$$
\eta_s=0,\qquad \zeta_s=\delta_s=F_s+e_s.
\tag{246.1}
$$

存在同一族全域实解析的实准备，满足所有实际任务条件，且 $K_s$ 上的 Fisher 峰值与积分一致有界，同时

$$
\begin{aligned}
\lim_{s\downarrow0}e_s^2\sup_{T_s(\delta_s)}I_Q
&=\frac{\pi^2}{4},\\
\lim_{s\downarrow0}\frac{e_s}{s}
\int_{T_s(\delta_s)}I_Q\,du
&=\frac{\pi^2\sqrt{D_*}}2.
\end{aligned}
\tag{246.2}
$$

每点秩可取至多二；实际联合支持为四，完整尖锐集合、普通最优双侧曲率及任意预先指定的有限阶实规范节点数据均保持。因此在全实预算边上，第244节两个必要常数均为渐近最优，而且由同一准备族共同达到。结论不主张固定任务的下确界取得，也不主张有正虚性预算时仍有相同最优常数。

证明。 记 $p=(1+u)/2$、$x=\sqrt{1-p}$，并继续在第225.2式的同一处理器中工作。对实单位向量 $\phi\perp q$ 和实角 $\theta$，使用具有下列特定形状的实密度矩阵：

$$
\begin{aligned}
\rho(p)&=x^2qq^{\mathsf T}+p\phi\phi^{\mathsf T}
+x\sqrt p\cos\theta
 (q\phi^{\mathsf T}+\phi q^{\mathsf T}),\\
M_s(p,\phi,\theta)
&=p\phi^{\mathsf T}B_s\phi
+x\sqrt p\cos\theta\,k_s^{\mathsf T}\phi=a_s.
\end{aligned}
\tag{246.3}
$$

其在 $\{q,\phi\}$ 中的矩阵为

$$
\mathcal B=
\begin{pmatrix}
1-p&\sqrt{p(1-p)}\cos\theta\\
\sqrt{p(1-p)}\cos\theta&p
\end{pmatrix}.
\tag{246.4}
$$

所以任意实 $\theta$ 都给出正性、迹一及秩至多二，并且精确有

$$
I_R^C(\rho)=0,\qquad
J(\rho)=2\sqrt{p(1-p)}\,|\sin\theta|.
\tag{246.5}
$$

式（246.3）的唯一标量矩条件与固定 $P$ 矩一起，保证全部复信号输入上的精确性。实密度与实处理器的矩没有额外虚部条件。

先给出保持实际矩的方向选择。在 $K_s$ 右侧选固定的 $p_A<p_B<1$，处于第245节的共同正则实圆区域。对 $p_B\le p\le h_3(s)$，将 $\phi=(y,z,w)$ 的 $y$ 坐标固定为实际第三规范方向 $v_{3,s}(p)$ 的 $y$ 坐标，同时解单位范数和（246.3）。选择与 $v_{3,s}$ 相同的 $z,w$ 符号。第245.6式给出 $y=O(s)$，且由第245.7式其 $p$ 导数有界。在 $s=0$ 极限，两条待解方程为

$$
z^2+w^2=1,\qquad p(z^2-w^2)=\alpha,
\tag{246.6}
$$

其关于 $z,w$ 的 Jacobian 行列式为 $-8pzw$，在这个固定符号图中绝对值有统一正下界。含参实隐函数定理因而对全部 $\theta\in[0,\pi]$ 给出同一实际解 $\phi_s(p,\theta)$。

这里 $k_s^{\mathsf T}\phi_s=O(s)$ 一致成立。对矩方程求 $\theta$ 导数，只产生 $x\sqrt p\sin\theta\,k_s^{\mathsf T}\phi_s$；求 $p$ 偏导时，可能变大的平方根导数乘上 $O(s)$，而 $x\ge\sqrt{1-h_3(s)}\ge cs$。同一个可逆 Jacobian 遂给出

$$
\|\partial_\theta\phi_s\|\le Cxs,
\qquad \|\partial_p\phi_s\|\le C.
\tag{246.7}
$$

在 $\theta=0$ 时，唯一性给出 $\phi_s(p,0)=v_{3,s}(p)$。在 $\theta=\pi$ 时，密度对应的实纯向量为 $xq-\sqrt p\,\phi_s(p,\pi)$。下面明确验证它与第一规范分支之间的实际实弧。

令 $b=2\alpha$、$\sigma=\sqrt{1-b^2}$。在 $s=0$、$\theta=\pi$ 的单位球面上，消去 $w^2$ 后，实矩纤维为

$$
(1+b)y^2+2z^2-\sigma\sqrt{\frac{1-p}{p}}\,y
=1+\frac\alpha p,\qquad w^2=1-y^2-z^2.
\tag{246.7a}
$$

在 $p=1$，椭圆上的 $y^2+z^2$ 至多为 $(1+\alpha)/(1+2\alpha)<1$，所以 $w^2\ge\alpha/(1+2\alpha)>0$。取足够接近一的固定 $p_A<p_B<1$ 后，在整个 $[p_A,p_B]$ 上仍有一个可能更小的一致正下界，例如 $w^2\ge\alpha/[2(1+2\alpha)]$。配方可将（246.7a）的椭圆光滑参数化为
$y=c(p)+A(p)\cos t$、$z=B(p)\sin t$，其中 $A,B>0$；再分别取 $w=\pm\sqrt{1-y^2-z^2}$，得到两个光滑圆。它们各自正则，且恰由 $w$ 符号区分。

实际小 $s$ 的矩函数在这个紧参数区间一致光滑趋近极限。沿极限圆的球面法向作标量隐函数修正，便得到实际圆的光滑参数化，导数一致有界；圆外固定管状邻域的补集上，极限矩残差有正下界，所以充分小扰动不会另生分支。第225、232节的实际规范符号表明 $-v_{1,s}$ 与 $\phi_s(p,\pi)$ 的 $w$ 符号相同。它们因此落在同一个实际圆上，其圆参数可在 $[p_A,p_B]$ 上选连续的实数提升。用固定的平坦函数插值两端参数，给出保持 $\theta=\pi$ 的精确实弧；各段正则，拼接处也在同一正则圆上。固定区间的宽度与一致参数导数界保证这条弧的方向导数一致有界。

在 $K_s$ 及第一节点邻域，背景仍取第一规范分支，表示为 $\theta=\pi$、$\phi=-v_{1,s}$。上述连接严格位于 $K_s$ 右侧。

下面安排相干角，始终使用实际预算而不将渐近误差从 $e_s$ 中扣除。记

$$
f(p)=2\sqrt{p(1-p)},\qquad
\kappa_s=\frac{e_s}{s}\longrightarrow0,\qquad
\Delta_s=h_3(s)-p_{\delta_s}.
\tag{246.8}
$$

在尾窗之前，$f(p)\ge\delta_s$。因而曲线

$$
\theta_{\rm env}(p)
=\pi-\arcsin\frac{(1-\kappa_s)\delta_s}{f(p)}
\tag{246.9}
$$

位于 $(\pi/2,\pi)$，严格递减，且资源恰为 $(1-\kappa_s)\delta_s$。在固定早期区间从 $\pi$ 光滑接入此曲线，可将角始终选在 $[\theta_{\rm env},\pi]$，所以预算保持严格余量。

在 $p_{\delta_s}$ 之前一个长度为 $o(\Delta_s)$ 的窗口，将（246.9）平坦接为常角 $\theta_{0,s}$。具体可把其中的参数替换为光滑不减函数 $\chi(p)\le p$，使 $\chi=p$ 于窗口左侧，$\chi$ 在窗口右侧为常数，且 $p-\chi=o(\Delta_s)$。因为 $\theta_{\rm env}$ 递减，角增大而正弦减小，预算继续成立。用 $|f'|\asymp1/s$、$\Delta_s\asymp s e_s$ 及（246.9），得到

$$
\theta_{0,s}=\frac\pi2+O(\sqrt{\kappa_s})
=\frac\pi2+o(1).
\tag{246.10}
$$

这里可先令窗口相对宽度为 $\kappa_s^{1/4}$；参数冻结造成的 $f$ 增量为 $o(e_s)$，故（246.10）成立。常角区间跨过尾窗左端，且该处仍有严格资源余量。

在 $p\in[p_{\delta_s},h_3(s)]$ 内，选择一个光滑、非负、在两端邻域为零的速度函数，使角从 $\theta_{0,s}$ 降至零。速度在占比 $1-o(1)$ 的中间区间为常数，两个平坦过渡区间的总长度为 $o(\Delta_s)$。归一化其积分为 $\theta_{0,s}$ 后，有

$$
\sup|\theta_p|
\le\frac{\pi/2+o(1)}{\Delta_s},\qquad
\int_{p_{\delta_s}}^{h_3(s)}\theta_p^2\,dp
\le\frac{\pi^2/4+o(1)}{\Delta_s}.
\tag{246.11}
$$

在尾窗内部 $p>p_{\delta_s}$，严格有 $f(p)<\delta_s$，故任何角都满足资源约束；在左端则由（246.10）所构造的严格不等式保证余量。到达零角后，方向就是第三规范分支；保持一个非空的规范节点邻域，再接原规范尾部。因此整个闭紧化背景的资源具有正的逐任务余量。这一余量允许随 $s,e_s$ 任意退化。

为估计实际信息，须同时计入二维密度块与支撑方向的运动。对（246.4），既有 Bloch 公式给出块内度量

$$
\frac{dp^2}{p(1-p)}+4p(1-p)\,d\theta^2.
\tag{246.12}
$$

此处采用 Zhong 等，*Fisher information under decoherence in Bloch representation*，Phys. Rev. A **87**, 022337（2013），arXiv:1212.0917，式（11）的混态公式；该公式及下述 SLD 谱表达式都是已有工具，不是本节的新定理。

由于 $q$ 固定、$\phi$ 实且为单位向量，$\phi_u'$ 与 $q,\phi$ 均正交，活动基底内部没有附加连接项。对 $\mathcal B$ 的正特征对 $(\lambda_i,e_i)$，支撑外的导数列为
$\lambda_i\langle\phi,e_i\rangle\phi_u'$。SLD 谱式中相应的两组交叉项之和为

$$
4\sum_i\lambda_i|\langle\phi,e_i\rangle|^2
\|\phi_u'\|^2=4p\|\phi_u'\|^2.
\tag{246.13}
$$

它们与块内导数位于不同矩阵块，故无交叉项。于是，当 $\sin\theta\ne0$ 时，实际 $u$ 信息精确等于

$$
I_Q=\mathcal E_s(p):=
\frac1{4p(1-p)}
+p(1-p)\theta_p^2
+p\left\|\frac{d\phi}{dp}\right\|^2.
\tag{246.14}
$$

在 $\sin\theta=0$ 的秩一下降点，密度的一阶导数不含 $\theta_p$ 项；直接用纯态谱式可见 $I_Q\le\mathcal E_s$ 仍成立。这里没有假定点态 SLD 在秩变化处连续。

整个尾窗内，由精确宽度式244.12及 $e_s=o(s)$，一致有

$$
p(1-p)=D_*s^2(1+o(1)),\qquad
\frac{\Delta_s}{s e_s}\longrightarrow\sqrt{D_*}.
\tag{246.15}
$$

又由（246.7）、$x=O(s)$ 和（246.11），

$$
\left\|\frac{d\phi}{dp}\right\|
\le C\left(1+\frac{s^2}{\Delta_s}\right).
\tag{246.16}
$$

所以（246.14）的方向项相对于角项只贡献低阶误差。将（246.11）代入，并注意 $du=2\,dp$，得到背景的共同上界

$$
\begin{aligned}
\sup_{T_s}\mathcal E_s
&\le\frac{\pi^2D_*s^2}{4\Delta_s^2}(1+o(1))
+O\!\left(s^{-2}+1+\frac{s^4}{\Delta_s^2}\right),\\
\int_{T_s}\mathcal E_s\,du
&\le\frac{\pi^2D_*s^2}{2\Delta_s}(1+o(1))
+O\!\left(\frac{\Delta_s}{s^2}+\Delta_s+
\frac{s^4}{\Delta_s}\right).
\end{aligned}
\tag{246.17}
$$

分别乘 $e_s^2$ 与 $e_s/s$，两个余项均趋零。式（246.15）便给出（246.2）中相应的两个上极限。

最后须在保持（246.3）结构的条件下完成解析化。先固定任务、预算及一个包含所需节点阶数的有限 $N\ge2$。早期实弧的球面矩梯度由（246.7a）的正则扰动保持非零；角桥由（246.6）的 Jacobian 保持非零；规范段由第211.31式根处的严格正角导数保持非零，两个紧化端点使用第225节已经验证的闭端点正则性。各拼接邻域都包含在这些正则段中。故在 $x=\sqrt{1-p}$ 的闭紧化区间上，完整背景的球面标量梯度具有逐任务的正下界 $\gamma_{s,e}>0$。

分别用实多项式逼近 $\theta(x)$ 和 $\phi(x)$ 的三个实坐标，作 $N$ 阶 Hermite 节点匹配，再归一化方向，记所得角与方向为 $\bar\theta,\bar v$。写 $Q_s=(B_s+B_s^{\mathsf T})/2$，并令

$$
\begin{aligned}
g(x)&=(I-\bar v\bar v^{\mathsf T})
 \bigl(2pQ_s\bar v+x\sqrt p\cos\bar\theta\,k_s\bigr),\\
\widehat v(x,t)&=
\frac{\bar v+t g}{\sqrt{1+t^2\|g\|^2}}.
\end{aligned}
\tag{246.17a}
$$

因 $g\perp\bar v$，后式始终是实单位向量；角保持 $\bar\theta$ 不变。在 $t=0$，标量矩残差对 $t$ 的导数精确为 $\|g\|^2$。足够精细的逼近使它在整个紧区间大于 $\gamma_{s,e}^2/4$。解析隐函数定理因而给出唯一的小解析修正 $t(x)$，局部解由唯一性拼成全区间的解，精确恢复（246.3）。这个修正及其有限阶导数可随预备逼近误差任意趋零。节点的矩残差具有零 $N$ 阶数据，逐次微分隐式方程便知 $t$ 的相应阶数据也为零，故原 Hermite 数据完整保留。

设背景全域资源余量的最小值为 $m_{s,e}>0$。角逼近误差可小于 $m_{s,e}/2$；式（246.5）及正弦的 Lipschitz 界遂保留全域预算，而方向修正不改变该资源公式。对每个固定任务，$\partial_p=-(2x)^{-1}\partial_x$，且在完整节点区间有 $x\ge\sqrt{1-h_3(s)}>0$。因此同一次足够精细的逼近还能使角与方向的 $p$ 一阶导数误差任意小。这里使用的是逐任务的正容差，不要求 $m_{s,e}$、$\gamma_{s,e}$ 或误差放大系数对 $s,e_s$ 一致。

这一做法始终保持实性、正性及秩至多二；它不以一般密度的 $C^1$ 接近代替 Fisher 控制。具体在完整节点区间上，令

$$
W_s(p)=\left(
\frac1{2\sqrt{p(1-p)}},
\sqrt{p(1-p)}\,\theta_p,
\sqrt p\,\phi_p
\right),\qquad \mathcal E_s=\|W_s\|^2.
\tag{246.18}
$$

可选择逐任务的逼近精度，同时保持全域资源余量，并使最终与背景的 $W_s$ 差的范数一致不超过一。因此

$$
\sqrt{\mathcal E_s^{\rm final}}
\le\sqrt{\mathcal E_s^{\rm bg}}+1.
\tag{246.19}
$$

背景尾窗的峰值为 $O(e_s^{-2})$、积分为 $O(s/e_s)$，长度为 $2\Delta_s=O(se_s)$。式（246.19）给出的归一化峰值附加量趋零；积分附加量至多
$2\sqrt{2\Delta_s\int_{T_s}\mathcal E_s^{\rm bg}\,du}+2\Delta_s=O(s)$，乘 $e_s/s$ 后同样趋零。$K_s$ 上的背景为固定规范分支、角为常数，故同一控制也保持两个内部代价一致有界。

在两个指定节点，角匹配到至少二阶，并保留方向的所需有限阶规范数据。于是节点的 $\theta_p,\theta_{pp}$ 为零，方向的一阶导数为零，二阶数据为原规范值。节点处的纯态谱式给出精确校准；角对信息上界的附加项为节点距离的四阶，方向项保留原二阶首项。式（246.14）的连续上界与第211节的普适下曲率界夹逼，给出原普通最优双侧曲率。

若最终混态曲线还有其它尖锐点，第215、216节的谱必要性将要求其正签名为同一个实际处理器的 $\lambda$ 或 $\mu$；正签名关于节点参数的严格单调性只允许原来的 $h_1,h_3$。实际 $r<1$ 排除了负单位特征值的特殊情形。两个保留节点又要求不同的零、正、负签名 $0,\lambda,\mu,-r$，所以实际联合支持至少四维，而构造始终在这四维空间内。由此分别得到完整尖锐集合与实际支持恰为四。任意预先指定的有限阶节点数据只要求把 Hermite 匹配阶数相应提高，不要求逼近次数或延拓半径对任务一致。

所得解析准备因此满足第244.9式的两个条件。第244.10式给出同一族的两个下极限，与已证的两个上极限相等，完成（246.2）。证毕。

**注记 246.2（余量决定窗口，相干角决定领先系数）。** 在全实预算边上，超额 $e_s$ 将剩余参数长度压到 $2\sqrt{D_*}s e_s(1+o(1))$；允许的实混态先把相干角带到 $\pi/2+o(1)$，再在尾窗恢复到规范纯态的零角。矩约束需要的方向运动只有低阶代价，因此近似匀速的这段角运动共同给出两个最优领先系数。

这不是把一般混态的 Fisher 度量当作密度的连续函数，也不是从第245节的纯相位桥直接读出最优常数。结论使用了满足实际矩约束的特定实秩二结构；有正虚性预算的分配方向仍需另行确定其最优度量代价。

<a id="entry-842"></a>

## 追加锚（本行以下为增补区）

<a id="section-247"></a>

## 247. 纯态尾窗的额外方向距离

**定义 247.1（纯预算边的几何常数）。** 沿用第243—246节的实际任务，置

$$
b=2\alpha,\qquad \sigma=\sqrt{1-b^2},\qquad
d=\sqrt{D_*},\qquad r_0=\frac{bd}{\sigma},\qquad
C_{\rm pure}=\left(\frac\pi2+\frac b\sigma\right)^2.
\tag{247.1}
$$

以下所称纯预算边为 $\zeta_s=0$、$\eta_s=\delta_s=F_s+e_s$，其中 $0<e_s=o(s)$。候选准备因此处处为纯态，仍满足原全输入精确性与全部节点要求。

**定理 247.2（纯态领先代价与全实混态的严格分离）。** 对纯预算边上的任意允许准备族，只要满足第244.9式任一低内部代价条件，就有

$$
\begin{aligned}
\liminf e_s^2\sup_{T_s}I_Q&\ge C_{\rm pure},\\
\liminf\frac{e_s}{s}\int_{T_s}I_Q\,du
&\ge2\sqrt{D_*}\,C_{\rm pure}.
\end{aligned}
\tag{247.2}
$$

存在同一族解析纯准备，保持 $K_s$ 上两个代价一致有界，并将（247.2）的两个下极限同时达到为极限。实际联合支持四、完整尖锐集合、普通最优双侧曲率及任意预先指定的有限阶实规范节点数据均保持。

因此两个零预算边具有相同的精确端点低内部代价阈值，却有不同的最优尾窗领先系数：纯边的峰值系数严格大于第246节全实边的 $\pi^2/4$，积分系数严格大于 $\pi^2\sqrt{D_*}/2$。这不判定中间预算分配，也不主张固定任务极小元存在。

证明。 先确定实际第三节点及相位基底在端点尺度中的方向。由第241.16式，

$$
\sqrt{1-\mu(s)^2}=\nu s+O(s^2),\qquad
\nu=\frac{\sqrt2(1+b)}{1-b}
\sqrt{\frac{1-\alpha}{1+\alpha}}.
\tag{247.3}
$$

在第225.2式的固定坐标 $q,e_y,e_z,e_w$ 中，第三规范态的主方向为

$$
v_*=(0,z_*,w_*),\qquad
z_*=\sqrt{\frac{1+\alpha}{2}},\quad
w_*=-\sqrt{\frac{1-\alpha}{2}}.
\tag{247.4}
$$

这里符号由实际正 $q$ 规范决定。将 $-r$ 特征向量按 $q$ 坐标为一归一，其 $w$ 坐标为负，故第225.19—225.20式中第三节点的正投影对应 $w_*<0$。在尖锐节点非核方向的一阶导数为零，对规范矩求导得到 $k_s^{\mathsf T}v_{3,s}=2a_s\sqrt{(1-h_3)/h_3}$。将不变平面式245.6代入其左侧，再除以 $s$，得到 $\nu z_*+\sqrt2w_*=bd$，故 $z_*>0$。直接代入给出

$$
\nu z_*-\sqrt2w_*=d,
\qquad \nu z_*+\sqrt2w_*=bd.
\tag{247.5}
$$

第245.6式的实际不变平面因而在第三节点给出

$$
\frac{y_3(s)}s\longrightarrow
\sigma\left(\frac{\nu z_*}{1-b}
+\frac{\sqrt2w_*}{1+b}\right)
=\frac{2bd}{\sigma}=2r_0.
\tag{247.6}
$$

相反，取与第三节点相同 $z,w$ 符号的相位基底 $v_{0,s}(p)$，满足 $k_s^{\mathsf T}v_{0,s}=0$ 与 $p v_{0,s}^{\mathsf T}B_sv_{0,s}=a_s$。由 $k_s=(\sigma+O(s),-b\nu s+O(s^2),b\sqrt2s+O(s^2))$，在整个尾窗内一致有

$$
\frac{(v_{0,s})_y}s\longrightarrow r_0.
\tag{247.7}
$$

下面证明额外距离的必要性。第244节已保证首次远端分隔面过零在尾窗内，记为 $u_\times$。令该点至第三节点的纯态 Fisher 长度为

$$
\mathcal L_s=\int_{u_\times}^{u_3}\sqrt{I_Q}\,du.
\tag{247.8}
$$

只须考虑 $\mathcal L_s=O(s)$ 的子列；若所需长度下界失败，必有这样的子列。由纯态迹速度界，整个剩余区间的密度都与第三规范投影相距 $O(s)$。选取实单位向量 $v_*$ 的规范，使代表向量 $\psi$ 满足 $\langle v_*,\psi\rangle>0$ 为实数。于是全区间一致有 $\psi=v_*+O(s)$。写

$$
\psi_q=s d_s(p)e^{-i\theta},\qquad
\psi_y=s(R+iB),\qquad
d_s(p)=\frac{\sqrt{1-p}}s\longrightarrow d.
\tag{247.9}
$$

其余坐标为 $(z_*,w_*)+O(s)$；$R,B$ 一致有界。这里 $d_s\to d$ 在实际尾窗上一致成立，且不要求 $e_s$ 大于任何给定的 $s$ 次幂。

取实际复矩的虚部。对角项为实数；$y,z$ 与 $y,w$ 的非对角系数为 $\sigma\nu s+O(s^2)$ 与 $-\sigma\sqrt2s+O(s^2)$，$z,w$ 的非对角系数为 $O(s^2)$。结合（247.5）及核列，将虚矩除以 $\sigma d s^2$，得到全区间一致的必要关系

$$
(1-\cos\theta)B-(R-r_0)\sin\theta
=O(s+e_s/s)=o(1).
\tag{247.10}
$$

例如核耦合的领先虚部为
$-\sigma d s^2[(R-r_0)\sin\theta+B\cos\theta]$，非核耦合的领先虚部为 $\sigma d s^2B$。其余 $z,w$ 扰动对虚部只贡献 $o(s^2)$，因为非核对角项恒实，而非对角项已带一个或两个 $s$ 因子。用 $d_s$ 替换其极限 $d$ 所产生的归一化误差为 $O(s+e_s/s)$，不能统一简写为 $O(s)$。这说明（247.10）适用于任意候选纯曲线，而不限于相位基底。

在分隔面过零点，$\operatorname{Re}(\psi_q\overline{\psi_n})=0$；实际法向满足 $\langle n_s,v_*\rangle\to c\ne0$，所以 $\psi_n=c+O(s)$。由（247.9）可知此时 $\cos\theta=o(1)$。第三节点的 $q$ 坐标则为正实数，角为零模 $2\pi$，且由（247.6）有 $R\to2r_0$。

固定任意小的 $\varepsilon>0$。从过零点起，取相位首次进入正实方向的 $\varepsilon$ 邻域之时；在其边界有 $\theta=\pm\varepsilon$ 模 $2\pi$。角的连续提升若绕圈，只会增加所需的变化量。在该时刻，由（247.10）及有界的 $B$，先令 $s\to0$ 得

$$
|R-r_0|\le C_M\varepsilon+
C_M\frac{s+e_s/s}{\sin\varepsilon}.
\tag{247.11}
$$

这里 $M$ 是所考察子列上 $\mathcal L_s/s$ 的统一上界，常数 $C_M$ 可以依赖它；先固定 $\varepsilon$ 再令 $s\to0$，右侧第二项才趋零。

过零至这一时刻，核坐标沿半径 $s(d+o(1))$ 的圆至少变化角 $\pi/2-\varepsilon-o(1)$，其欧氏弧长至少为 $s d(\pi/2-\varepsilon-o(1))$。此后至节点，$y$ 坐标的实部至少移动 $s(r_0-O(\varepsilon)-o(1))$。这两段发生在互不重叠的参数区间，故其长度相加。

所取规范也允许将这条欧氏下界转成纯态 Fisher 下界。因为 $\operatorname{Im}\langle v_*,\psi'\rangle=0$ 且 $\psi-v_*=O(s)$，有
$|\langle\psi,\psi'\rangle|\le Cs\|\psi'\|$。纯态公式遂给出

$$
\sqrt{I_Q}=2\sqrt{\|\psi'\|^2-|\langle\psi,\psi'\rangle|^2}
\ge2(1-O(s^2))\|\psi'\|.
\tag{247.12}
$$

因此先令 $s\to0$ 再令 $\varepsilon\downarrow0$，得到

$$
\liminf\frac{\mathcal L_s}{2s}
\ge\frac{\pi d}{2}+r_0.
\tag{247.13}
$$

剩余区间长度至多 $2\Delta_s$，且 $\Delta_s/(s e_s)\to d$。用长度对峰值的界及 Cauchy–Schwarz，便得到（247.2）。此处相加的是同一候选曲线在先后两个区间上的长度，不是把分别达到的两个最优值视为共同实现。

上界使用实际相位基底与实际短实臂。在尾窗之前，先在固定区间把第一规范支连接到 $xq-\sqrt p\,v_{0,s}$，使 $K_s$ 背景保持第一规范支。再取
$\psi=xq+\sqrt p\,e^{i\theta}v_{0,s}$，从 $\theta=\pi$ 沿第246节的严格可行角包络接近 $\pi/2+o(1)$，在尾窗左端附近平坦化。相位基底的 $k_s$ 矩为零，故所有角都保持完整复矩；其虚性精确为 $f(p)|\sin\theta|$。

尾窗内先将角从 $\pi/2+o(1)$ 降至零，再沿实矩圆从 $v_{0,s}$ 接到第三规范方向。前一段的纯态信息由第245.11式给出，其 Fisher 平方根以 $p$ 积分为 $s\pi d/2+o(s)$；因为 $du=2\,dp$，实际 Fisher 长度是它的两倍。后一段以 $y$ 为坐标，由（247.6）、（247.7）其总变化为 $s r_0(1+o(1))$。归一化及实矩方程对 $y$ 的偏导均为 $O(s)$，而关于 $z,w$ 的 Jacobian 一致可逆，所以

$$
\left\|\frac{\partial v}{\partial y}\right\|=1+o(1)
\tag{247.14}
$$

在整条短实臂上一致成立。实际 $p$ 变化所贡献的规范导数及核概率变化为低阶项。因此实臂的 Fisher 平方根以 $p$ 积分为 $s r_0+o(s)$。

把两段分配到尾窗的比例分别取为

$$
\frac{\pi d/2}{\pi d/2+r_0},\qquad
\frac{r_0}{\pi d/2+r_0}.
\tag{247.15}
$$

在各段采用近似常速，并用总宽度 $o(\Delta_s)$ 的平坦区间完成拼接及规范节点匹配。两段的领先 Fisher 平方根于是共同等于 $s(\pi d/2+r_0)/\Delta_s$，给出

$$
\begin{aligned}
\sup_{T_s}I_Q
&\le\frac{s^2(\pi d/2+r_0)^2}{\Delta_s^2}(1+o(1)),\\
\int_{T_s}I_Q\,du
&\le\frac{2s^2(\pi d/2+r_0)^2}{\Delta_s}(1+o(1)).
\end{aligned}
\tag{247.16}
$$

尾窗内的相位非平坦点位于 $p>p_{\delta_s}$，故 $f(p)<\delta_s$ 留有严格逐任务余量；尾窗左端使用严格包络余量，实臂的虚性为零。第243节的完整复矩正则性覆盖相位桥、实臂与紧化规范尾部。逐任务完成纯向量的解析 Hermite 逼近与两矩修正，可同时保持资源余量，并使完整节点区间内纯密度一阶导数的迹范数误差不超过一。由纯态迹速度恒等式，最终与背景的 Fisher 平方根之差至多一。因此尾窗积分增加至多 $2\int_{T_s}\sqrt{I_Q^{\rm bg}}\,du+2\Delta_s=O(s)$，峰值的平方根增加至多一；分别归一化后这些误差趋零。这保持（247.16）的两个领先系数和有界的 $K_s$ 代价，而不使用会放大领先系数的二倍积分估计。

按任意预定有限阶保留规范节点数据，其余全输入精确性、实际支持、完整尖锐集合及普通曲率按第243、245节的同一论证保持。式（247.2）与（247.16）合并给出所述共同极限。证毕。

**注记 247.3（相同容量不保证相同恢复距离）。** 两个零预算边都在 $F_s$ 处发生相同的端点低内部代价转变。全实混态允许在维持第三规范方向的同时改变相干角；纯态的完整复矩则在小非零相位处把方向拉回 $y/s\to r_0$，而节点要求 $y/s\to2r_0$。额外的实方向恢复距离导致严格更大的领先系数。此处比较的是同一参数任务的 Fisher 几何代价，不将其解释为物理耗时或能量。

<a id="entry-844"></a>

## 追加锚（本行以下为增补区）

<a id="section-248"></a>

## 248. 消失的虚性份额与非消失的恢复距离

**定义 248.1（分别受限的近实预算）。** 沿用第243—247节的实际任务及 $b,\sigma,d,r_0$，其中 $d=\sqrt{D_*}$、$r_0=bd/\sigma$。本节始终分别要求两个全域预算

$$
I_R^C(\rho_u)\le\eta_s,\qquad J(\rho_u)\le\zeta_s,
\qquad \delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,
\tag{248.1}
$$

并考察尺度

$$
0<e_s=o(s),\qquad \eta_s=o(s),\qquad
\frac{\eta_s}{\sqrt{s e_s}}\longrightarrow\infty.
\tag{248.2}
$$

定义

$$
C_{\rm near}=\frac{\pi^2}{4}+\frac{b^2}{\sigma^2}.
\tag{248.3}
$$

这里总预算只是两项给定预算的合成读数；不能把两个分别成立的不等式替换为单个合成约束。

**定理 248.2（近实分配的两个共同最优系数）。** 满足（248.1）—（248.2）的任意允许准备族，只要满足第244.9式任一低内部代价条件，就有

$$
\begin{aligned}
\liminf_{s\downarrow0}e_s^2\sup_{T_s}I_Q&\ge C_{\rm near},\\
\liminf_{s\downarrow0}\frac{e_s}{s}\int_{T_s}I_Q\,du
&\ge2dC_{\rm near}.
\end{aligned}
\tag{248.4}
$$

下界允许任意点态秩。存在同一族全域实解析、每点秩至多二的准备，将两项下界同时达到为极限，保持 $K_s$ 上两个代价一致有界，以及全输入精确性、实际联合支持四、完整尖锐集合、普通最优双侧曲率和任意预先指定的有限阶实规范节点数据。

因此虚性预算相对于 $s$ 的份额虽然趋零，两个系数仍严格大于全实边的系数，并严格小于纯边的相应系数：

$$
\frac{\pi^2}{4}<C_{\rm near}
<\left(\frac\pi2+\frac b\sigma\right)^2.
\tag{248.5}
$$

证明。 先证明过零处的方向约束。写 $S=\operatorname{Re}\rho$、$\rho=S+iK$，其中 $K$ 为实反对称矩阵。第242节的同一实部归约给出

$$
J(S)^2\le I_R^C(\rho)^2+J(\rho)^2\le\eta_s^2+\zeta_s^2=\delta_s^2,
\qquad I_Q(S)\le I_Q(\rho).
\tag{248.5a}
$$

第243—244节因此保证低内部代价族的首次远端分隔面过零位于 $T_s$。在该点记 $x^2=1-p$，并分块

$$
S=\begin{pmatrix}x^2&\beta^{\mathsf T}\\ \beta&W\end{pmatrix},
\quad \operatorname{Tr}W=p,\quad
n_s^{\mathsf T}\beta=0,\quad n_s^{\mathsf T}Wn_s\ge c_0>0.
\tag{248.6}
$$

置 $H_s=\delta_s^2-F_s^2=2F_se_s+e_s^2=O(se_s)$。第243节的精确压缩估计给出 $\lambda_1(S)\le p$、$\lambda_2(S)\ge x^2$。若 $\lambda_1(S)=p-t$，其余特征值的和为 $x^2+t$，所以

$$
J(S)^2-4px^2\ge4t(2p-1-t).
\tag{248.7}
$$

近纯性先给出 $t=O(s^2)$。又因 $4px^2\ge F_s^2$、$J(S)\le\delta_s$，式（248.7）改进为 $t=O(H_s)$。故

$$
\lambda_1(S)=p-O(H_s),\quad
\lambda_2(S)=x^2+O(H_s),\quad
\lambda_3(S)+\lambda_4(S)=O(H_s).
\tag{248.8}
$$

还须控制这些小谱方向的位置。将非核块写为

$$
W=\mu\phi\phi^{\mathsf T}+E,\qquad
E\ge0,\quad E\phi=0,\quad T:=\operatorname{Tr}E=p-\mu.
\tag{248.9}
$$

先明确这个块的初步近纯性。正性给出 $\|\beta\|^2\le x^2p=O(s^2)$，而 $\mu\ge p/3$ 使 $\mu-x^2$ 有正下界。对 $W\le\mu I$ 的二阶 Rayleigh 上界有

$$
\lambda_1(S)\le
\frac{x^2+\mu+\sqrt{(\mu-x^2)^2+4\|\beta\|^2}}2
\le\mu+\frac{\|\beta\|^2}{\mu-x^2}.
\tag{248.9a}
$$

因此 $\lambda_1(S)=1-O(s^2)$ 蕴含 $\mu=1-O(s^2)$、$T=O(s^2)$。由（248.6），$|n_s^{\mathsf T}\phi|$ 有正下界。正性在 $q\oplus\phi^\perp$ 压缩上给出 $\|\beta_{\phi^\perp}\|^2\le x^2T$，而过零条件给出 $|\beta_\phi|\le C\|\beta_{\phi^\perp}\|$。因为 $\mu-x^2$ 有正下界，块矩阵的最大特征值估计遂给出

$$
\lambda_1(S)\le\mu+C\|\beta\|^2
\le p-T+Cs^2T.
\tag{248.10}
$$

结合（248.8），得到 $T=O(H_s)$ 和 $\|\beta\|=O(s\sqrt{H_s})$。这一步没有引入一个与 $e_s$ 无关的 $O(s^4)$ 余项。

在实正交分解 $q\oplus\phi\oplus\{q,\phi\}^\perp$ 中，原复密度的正性控制虚部：

$$
K_{q,\phi^\perp}=O(s\sqrt{H_s}),\qquad
K_{\phi,\phi^\perp}=O(\sqrt{H_s}),\qquad
K_{\phi^\perp,\phi^\perp}=O(H_s).
\tag{248.11}
$$

这里 $\phi^\perp$ 的块指标均指 $\{q,\phi\}^\perp$。记 $\kappa=K_{q\phi}$。实部谱下界及分别成立的混合预算给出

$$
\begin{aligned}
2\|K\|_F^2
&=J(S)^2-J(\rho)^2\\
&\ge F_s^2-\zeta_s^2=\eta_s^2-H_s,\\
2\|K\|_F^2&=4\kappa^2+O(H_s),
\end{aligned}
\tag{248.11a}
$$

其中最后一式来自（248.11）。于是 $4\kappa^2\ge\eta_s^2-O(H_s)$。将 $iK$ 压缩到 $\{q,\phi\}$，又有 $2|\kappa|\le\|K\|_1=I_R^C(\rho)\le\eta_s$。因此

$$
2|\kappa|=\eta_s(1+o(1)).
\tag{248.12}
$$

实际处理器的非核反对称部分为 $O(s)$。将（248.11）代入完整虚矩条件，主项为 $\kappa k_s^{\mathsf T}\phi$，其余项至多 $Cs\sqrt{H_s}$，所以

$$
|k_s^{\mathsf T}\phi|\le
Cs\frac{\sqrt{H_s}}{\eta_s}=o(s).
\tag{248.13}
$$

为确定方向的符号，只须考察剩余 Fisher 长度
$\mathcal L_s=\int_{u_\times}^{u_3}\sqrt{I_Q}\,du=O(s)$ 的子列；违反所需长度下界的子列必属于此类。迹速度界及实部归约使剩余路径与实际第三节点投影相距 $O(s)$，从而可选 $\phi=v_*+O(s)$，其中 $v_*$ 为第247.4式的实际带符号极限方向。由实际 $k_s$ 的展开和第247.5式，写 $\phi_y=sR$ 后有

$$
k_s^{\mathsf T}\phi=\sigma s(R-r_0)+O(s^2).
\tag{248.14}
$$

式（248.13）因此强制

$$
\frac{\phi_y}{s}\longrightarrow r_0,
\qquad \langle e_y,S_\times v_*\rangle=sr_0+o(s).
\tag{248.15}
$$

谱余量给出的是（248.13）；实际节点与有界长度一起才确定（248.15）的符号。

下面将两个方向的变化合为一个长度下界，并避免假定原秩变化曲线有光滑最小净化。取 $\varepsilon_s=s^6$，定义正定实密度

$$
S^\varepsilon=\frac{S+\varepsilon_sI_4}{1+4\varepsilon_s}.
\tag{248.16}
$$

SLD 凸性给出 $I_Q(S^\varepsilon)\le I_Q(S)/(1+4\varepsilon_s)\le I_Q(\rho)$。对这个正定曲线，解实对称 Sylvester 方程
$S^\varepsilon L+LS^\varepsilon=2(S^\varepsilon)'$，再从终点反向解 $A'=LA/2$。终点因子可取第一列为 $\sqrt{(1+\varepsilon_s)/(1+4\varepsilon_s)}\,\psi_3$，其余列为 $\sqrt{\varepsilon_s/(1+4\varepsilon_s)}$ 乘 $\psi_3^\perp$ 的实正交基。线性方程的唯一性和直接求迹给出

$$
AA^{\mathsf T}=S^\varepsilon,\qquad
4\|A'\|_F^2=I_Q(S^\varepsilon),\qquad
A(u_3)=\psi_3e_0^{\mathsf T}+O(s^3).
\tag{248.17}
$$

在 $\mathcal L_s=O(s)$ 的子列上，积分速度界使整个因子路径满足 $A(u)=\psi_3e_0^{\mathsf T}+O(s)$。

令 $a_q,a_y$ 为该同一因子的物理 $q,y$ 两行。整个剩余区间都有
$\|a_q\|=\sqrt{(1-p+\varepsilon_s)/(1+4\varepsilon_s)}=sd(1+o(1))$。过零处 $a_q\cdot a_n=0$ 仍精确成立，而 $a_n=ce_0+O(s)$、$c\ne0$。所以归一化的 $q$ 行从近似垂直于 $e_0$ 的方向走到 $e_0+o(1)$。变半径曲线的长度至少等于最小半径乘单位球面上的角距离，故

$$
\int\|a_q'\|\,du\ge sd\left(\frac\pi2-o(1)\right).
\tag{248.18}
$$

同时 $v_*$ 行为 $e_0+O(s)$。由整段因子控制和节点坐标 $(\psi_3)_y=O(s)$，有 $a_y=(\psi_3)_ye_0+O(s)=O(s)$；故 $a_y\cdot a_{v_*}=a_y\cdot e_0+O(s^2)$。式（248.15）因此使过零处 $a_y\cdot e_0=sr_0+o(s)$，而实际终点由第247.6式给出 $a_y(u_3)\cdot e_0=2sr_0+o(s)$。于是 $\int\|a_y'\|\,du\ge sr_0+o(s)$。这两个估计属于同一因子的不同物理行，积分 Minkowski 不等式给出

$$
\mathcal L_s\ge2\int\|A'\|_F\,du
\ge2s\sqrt{\left(\frac{\pi d}{2}\right)^2+r_0^2}+o(s).
\tag{248.19}
$$

以剩余区间长度 $2\Delta_s$ 控制峰值及积分，并使用精确差商 $\Delta_s/(se_s)\to d$，即得（248.4）。正定扰动在这里仅用于证明长度下界，不要求它仍满足原任务矩条件。

上界使用实际相位基底与一个可变相干块。令 $U=(q,\phi)$ 为实正交框架，并写

$$
\rho=U\mathcal B U^\dagger,\qquad
\mathcal B=
\begin{pmatrix}
1-p&\sqrt{p(1-p)}\,c\\
\sqrt{p(1-p)}\,\overline c&p
\end{pmatrix},\qquad
c=\cos\theta+i t\sin\theta.
\tag{248.20}
$$

当 $\phi=\phi_{0,s}(p)$ 满足 $k_s^{\mathsf T}\phi=0$ 时，完整复矩对任意 $\theta,t$ 都精确成立，并有

$$
I_R^C=f(p)|t\sin\theta|,\qquad
J=f(p)\sqrt{1-t^2}|\sin\theta|,\qquad
f(p)=2\sqrt{p(1-p)}.
\tag{248.21}
$$

置 $\tau_s=\eta_s/\delta_s$、$\epsilon_s=e_s/s$。由（248.2），$\tau_s\to0$ 且 $\sqrt{\epsilon_s}=o(\tau_s)$。在尾窗之前取 $t=\tau_s$，使用第246节的严格包络
$\theta_{\rm env}=\pi-\arcsin((1-\epsilon_s)\delta_s/f(p))$，并在尾窗入口附近将其平坦化。入口角为 $\pi/2+O(\sqrt{\epsilon_s})=\pi/2+o(\tau_s)$，两个预算都有严格余量。固定早期实弧和相位基底的连接按第246、247节完成，$K_s$ 背景仍为第一规范支。

在严格位于尾窗左端之后、占总宽度 $O(\beta_s)$ 的两段上，取 $\beta_s=\sqrt{\tau_s}$，先保持 $t=\tau_s$ 将角降至 $\theta_c=\arccos(2\tau_s)$，再保持 $\theta=\theta_c$ 将 $t$ 降为零。第一段由 $f(p)<\delta_s$ 满足两个预算；第二段精确满足

$$
J\le\delta_s\sqrt{1-4\tau_s^2}
<\delta_s\sqrt{1-\tau_s^2}=\zeta_s,\qquad
I_R^C<\eta_s.
\tag{248.22}
$$

可变混合权重的导数必须计入。将（248.20）的 Bloch 向量代入 Zhong 等，*Fisher information under decoherence in Bloch representation*，Phys. Rev. A **87**, 022337（2013），arXiv:1212.0917，式（11）的混态公式，得到块内精确线元

$$
\frac{dp^2}{p(1-p)}+
4p(1-p)\left(d\theta^2+
\frac{\sin^2\theta}{1-t^2}\,dt^2\right).
\tag{248.23}
$$

实支撑运动另加 $4p\|d\phi\|^2$，因为 $U^\dagger dU=0$。上述两段各自的控制变化为 $O(\tau_s)$，故 Fisher 长度为 $O(s\tau_s)+o(s)$；选择平坦端点的近似常速后，归一化峰值和积分分别至多为
$O(\tau_s^2/\beta_s^2)+o(1)$ 与 $O(\tau_s^2/\beta_s)+o(1)$，均趋零。这里没有对可变权重误用固定权重的凸性。

在余下占比 $1-o(1)$ 的尾窗上取 $t=0$，用实坐标 $y$ 与角 $\theta$ 解单位范数和实际实矩，选第三节点的 $z,w$ 符号。与第246、247节相同的可逆 Jacobian 一致给出

$$
\partial_y\phi=e_y+O(s),\qquad
\partial_\theta\phi=O(s^2),\qquad
\partial_p\phi\big|_{y,\theta}=O(1).
\tag{248.24}
$$

用同一个近似线性进度 $\chi$ 令
$\theta=(1-\chi)\theta_c$、
$y=(1-\chi)(\phi_{0,s})_y+\chi(v_{3,s})_y$，两端保留平坦邻域。实际两个 $y$ 坐标的差为 $sr_0(1+o(1))$，而 $p$ 导数为 $O(s)$。故同一次运动的领先度量速度是
$s\sqrt{d^2\theta_c^2+r_0^2}\,|\chi_p|$。核概率导数的 $O(s^{-1})$ 项相对于 $O(e_s^{-1})$ 为低阶，式（248.24）的其余项同样只给低阶贡献。因此同一个光滑背景满足

$$
\begin{aligned}
\sup_{T_s}I_Q
&\le\frac{s^2[(\pi d/2)^2+r_0^2]}{\Delta_s^2}(1+o(1)),\\
\int_{T_s}I_Q\,du
&\le\frac{2s^2[(\pi d/2)^2+r_0^2]}{\Delta_s}(1+o(1)).
\end{aligned}
\tag{248.25}
$$

实段的 $0\le\theta\le\theta_c$ 继续保留（248.22）的严格预算余量。接回第三规范支后，完整紧化背景的两项资源均有逐任务的正余量。

最后以完整的秩二因子完成解析化。不能直接将（248.20）的实方向与复相干分别解析拼接，因为解析恒等式 $\operatorname{Im}c\,k_s^{\mathsf T}\phi=0$ 会强制其中一因子恒零。下面允许最终因子的全部复坐标变化。

记 $h=\sqrt{1-|c|^2}=\sqrt{1-t^2}\sin\theta\ge0$，令

$$
H=\frac{\mathcal B+x\sqrt p\,hI_2}
{\sqrt{1+2x\sqrt p\,h}},\qquad x=\sqrt{1-p}.
\tag{248.26}
$$

则 $H^2=\mathcal B$。控制在秩变化处取平坦拼接，使 $H$ 在整个闭紧化 $x$ 区间光滑。以下求导可先对 $x$ 进行。置 $K_H=[H,H']$，解酉矩阵方程 $R'=-K_HR$ 并令 $A=UHR$。在 $H$ 的特征基中，交换子的对角项为零，非对角项与 $\mathcal B$ 作反交换时乘以 $\operatorname{Tr}\mathcal B=1$，所以

$$
\{\mathcal B,K_H\}=K_H,\qquad A^\dagger A'=(A^\dagger A')^\dagger.
\tag{248.27}
$$

在秩二段，这是水平净化，满足 $4\|A'_u\|_F^2=I_Q(\rho)$。所用水平净化与 SLD 度量的关系是既有工具，见 Dittmann、Uhlmann，*Connections and metrics respecting purification of quantum states*，J. Math. Phys. **40**, 3246–3267（1999），DOI:10.1063/1.532884，arXiv:quant-ph/9806028，第3—4节。该文也区分了秩退化处的中性切向量，不能据此直接假定跨秩连续性。

本背景的纯实区间上 $H=\mathcal B$，平坦拼接在过渡点还使 $H'=\mathcal B'$。投影恒等式 $\mathcal B^2=\mathcal B$ 给出 $\mathcal B'=\mathcal B\mathcal B'+\mathcal B'\mathcal B$ 及 $\mathcal B\mathcal B'\mathcal B=0$。代入（248.27）得到
$A'=(U'\mathcal B+U\mathcal B'\mathcal B)R$，其在因子核上为零，因而没有中性导数分量。纯实段上可写 $A=\psi a^\dagger$，水平条件和 $\psi^{\mathsf T}\psi'=0$ 强制辅助单位向量 $a$ 为常数，所以 $4\|A'_u\|_F^2=4\|\psi'_u\|^2=I_Q$；过渡点的同一一阶导数计算也给出该等式。这是对实际平坦秩变化的直接核对。

因子的归一化行坐标为

$$
A_q=x\xi,\qquad A_{q^\perp}=\sqrt p\,W,\qquad
\|\xi\|=1,\qquad \|W\|_F=1.
\tag{248.28}
$$

其中 $x=0$ 的表观除法可消去：
$\xi=(x+\sqrt p\,h,\sqrt p\,c)R/\sqrt{1+2x\sqrt p\,h}$，所以这两个球面坐标均光滑至紧化端点。

完整复矩在该球面乘积上的两个实微分处处独立。实密度的实因子与当前因子相差一个右侧酉变换；在 $x>0$ 的实背景点，可用常数辅助酉变换将两列写成 $\alpha=xq+v$、$\beta=w$，其中 $v,w$ 实且垂直于 $q$。允许的虚切变分 $\delta\alpha=i\Omega$ 给出

$$
D\operatorname{Im}M=
\bigl((B_s^{\mathsf T}-B_s)v-xk_s\bigr)^{\mathsf T}\Omega.
\tag{248.29}
$$

取第243.15式的精确核向量，导数为 $-xk_s^{\mathsf T}\Omega\ne0$；实方向上的独立微分由实际实矩图提供。复相位段在 $t>0$ 且 $0<\theta<\pi$ 时，改变底层纯向量使完整矩的两个微分变为 $(D\operatorname{Re}M,tD\operatorname{Im}M)$，由第243节独立。$t=0$ 或 $\theta=0,\pi$ 时，密度为实矩阵，直接使用（248.29）及独立实方向，因而也覆盖这些秩一下降点。

紧化右端 $x=0$ 则单独计算。第三规范方向 $v=(y,z,w)$ 在这个端点仍有 $z>0,w<0$，由实际矩阵（243.14）得到

$$
\bigl((B_s^{\mathsf T}-B_s)v\bigr)_y
=s_\lambda(s_\mu z-\mu s_r w)>0.
\tag{248.29a}
$$

所以虚切方向 $i e_y$ 给出非零虚矩微分；这些虚切方向对实单位向量自动满足球面一阶范数条件。实微分也非零，因为端点矩值 $a_s$ 与 $Q_s$ 的谱保持分离，后者趋于 $2\alpha,1,-1$。两种方向的另一个矩微分分别为零，故两行独立。它们都可提升为 $W$ 球面中的纯因子变分；$\xi$ 在 $x=0$ 不参与这个论证。紧化左端有 $x>0$，其独立实方向由第211节规范实矩根的严格正导数提供，虚方向仍由（248.29）给出。

具体完成如下。固定任务后，令 $Z=(\xi,W)$，以复坐标上的实内积定义两个矩残差 $F=(\operatorname{Re}\operatorname{Tr}(T_sAA^\dagger)-a_s,\operatorname{Im}\operatorname{Tr}(T_sAA^\dagger))$。上述正则性与紧性给出背景微分的正最小奇异值 $\gamma_{s,e,\eta}>0$。对 $Z(x)$ 作足够高阶的实多项式逼近与 Hermite 匹配，归一化两球面，记为 $\bar Z$。令 $g_1,g_2$ 为 $F$ 的两个球面乘积梯度，并分别记它们在两个球面中的分量为 $g_{iq},g_{iP}$。用两个实小参数 $v_1,v_2$ 定义

$$
\widehat Z_j(x,v)=
\frac{\bar Z_j+v_1g_{1j}+v_2g_{2j}}
{\sqrt{1+\|v_1g_{1j}+v_2g_{2j}\|^2}},
\qquad j=q,P.
\tag{248.29b}
$$

每个梯度分量都与相应 $\bar Z_j$ 实正交，故这个表达式精确保持两个单位范数。在 $v=0$，$F$ 对 $v$ 的 Jacobian 为梯度 Gram 矩阵 $G_{ij}=\langle g_i,g_j\rangle_{\mathbb R}$。足够精细的预备逼近使它的最小特征值在整个紧区间至少为 $\gamma_{s,e,\eta}^2/2$。解析隐函数定理给出唯一的小解析修正 $v(x)$；覆盖紧区间的有限个隐函数邻域由唯一性拼合。修正及其任意指定的有限阶导数随预备误差趋零。节点残差具有零 Hermite 数据，逐次微分隐式方程使修正的对应数据也为零。

归一化、固定 $P$ 矩、正性及秩至多二始终由因子坐标保持。设背景两项全域资源余量的正最小值为 $m_R,m_J$。对两列因子 $A=(a_1,a_2)$，恒有 $J(AA^\dagger)=2\|a_1\wedge a_2\|$，而虚性由迹范数控制；两者在归一化因子上均有局部 Lipschitz 控制。于是预备误差可取得足够小，使修正后的全域误差小于两项余量的一半，同时在完整节点区间使 $\|(A_{\rm final})'_u-(A_{\rm bg})'_u\|_F\le1/2$。这里 $\partial_u=-(4x)^{-1}\partial_x$，该区间有 $x\ge\sqrt{1-h_3(s)}>0$，所以所需误差放大常数对每个固定任务有限。$\gamma_{s,e,\eta}$、$m_R,m_J$ 及这些常数都允许随任务退化，不要求误差大于某个固定的 $s$ 次幂。

在完整节点区间，因子及其 $u$ 一阶导数的逼近精度可选到使

$$
\sqrt{I_Q(\rho_{\rm final})}
\le2\|(A_{\rm final})'_u\|_F
\le\sqrt{I_Q(\rho_{\rm bg})}+1.
\tag{248.30}
$$

第一步是纯净化的信息上界，不需要最终密度的 SLD 连续性。式（248.25）的归一化峰值附加误差趋零；积分附加量至多 $2\int_{T_s}\sqrt{I_Q(\rho_{\rm bg})}\,du+2\Delta_s=O(s)$，归一化后也趋零。$K_s$ 的两个有界代价同样保持。

取 Hermite 阶数至少为四，并不低于任何预先指定的阶数。在节点附近背景为纯规范支，水平辅助方向为常数；因子导数修正为节点距离的至少四阶，故（248.30）所用因子信息上界与背景的差为 $o((u-u_i)^2)$。结合任务的普适下曲率界，保持普通最优双侧曲率与精确校准。保留的两个节点及既有谱必要性又强制完整尖锐集合和实际联合支持恰为四。任意逐任务的逼近次数与常数均允许退化，不要求统一解析延拓半径。

最终准备遂达到（248.25）的两个上极限，与（248.4）合并得到同一族的共同极限。证毕。

**注记 248.3（份额趋零不等于几何影响趋零）。** 在（248.2）的尺度中，单独的实混合预算比全实过零所需的量少了一个大于端点余量的量。虚性因此必须参与过零，并由完整复矩把实主方向限制在 $y/s\to r_0$；终点仍要求 $y/s\to2r_0$。混态允许角运动与方向恢复同时进行，故这两项距离按平方和合成；纯边的完整复矩则使它们先后发生，得到第247节的距离之和。

本节没有确定 $\eta_s\asymp\sqrt{se_s}$ 的过渡区、其他分配尺度或固定任务极小元。若只保留单个合成预算而不分别限制两项资源，全实构造已给出第246节较小的系数，（248.4）便不能套用。

<a id="entry-846"></a>

## 追加锚（本行以下为增补区）

<a id="section-249"></a>

## 249. 有限虚性过渡区的峰值与累计代价分离

**定义 249.1（分别受限的有限过渡尺度）。** 沿用第243—248节的实际任务、共同处理器及两个分别成立的全域预算。记 $d=\sqrt{D_*}$、$h=r_0/d=b/\sigma>0$，并设

$$
\delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,\qquad
0<e_s=o(s),\qquad
\gamma_s=\frac{\eta_s^2}{4dse_s}\longrightarrow\gamma\in(0,\infty).
\tag{249.1}
$$

此时自动有 $\eta_s=o(s)$。在第244节的实际尾窗上，定义两个归一化代价

$$
\mathcal P_s=e_s^2\sup_{T_s}I_Q,\qquad
\mathcal E_s=\frac{e_s}{s}\int_{T_s}I_Q\,du.
\tag{249.2}
$$

设

$$
\begin{aligned}
A(z)&=\frac{\pi^2}{4}+(h-z)^2,\\
g(z)&=1+\frac{z^2-\sqrt{z^4+4}}2,\\
D_\gamma(z)&=1-\gamma g(z),\\
\mathcal Z_\gamma&=\{z\in[0,h]:D_\gamma(z)>0\}.
\end{aligned}
\tag{249.3}
$$

这里 $g(0)=0$，$g$ 在正半轴严格递增。记

$$
P_\gamma=\min_{z\in\mathcal Z_\gamma}\frac{A(z)}{D_\gamma(z)^2},
\qquad
E_\gamma=2d\min_{z\in\mathcal Z_\gamma}\frac{A(z)}{D_\gamma(z)}.
\tag{249.4}
$$

**定理 249.2（两个最优代价及其不能共同收敛达到的性质）。** 任意满足（249.1）及第244.9式任一低内部代价条件的允许准备族，均有

$$
\liminf_{s\downarrow0}\mathcal P_s\ge P_\gamma,\qquad
\liminf_{s\downarrow0}\mathcal E_s\ge E_\gamma.
\tag{249.5}
$$

下界允许任意点态秩。两项最小值分别由全域实解析、每点秩至多二的允许准备族达到为极限；每族均保持 $K_s$ 上两个代价一致有界、全输入精确性、实际联合支持四、完整尖锐集合、普通最优双侧曲率及任意预先指定的有限阶实规范节点数据。

但不存在一个满足（249.1）及第244.9式任一低内部代价条件的允许准备族，使 $\mathcal P_s\to P_\gamma$ 与 $\mathcal E_s\to E_\gamma$ 同时成立。更精确地，置

$$
G_\gamma=
\min_{z\in\mathcal Z_\gamma}
\left(\frac{A(z)}{D_\gamma(z)^2}
+\frac{A(z)}{D_\gamma(z)}\right)
-P_\gamma-\frac{E_\gamma}{2d}.
\tag{249.6}
$$

则 $G_\gamma>0$，且

$$
\liminf_{s\downarrow0}
\left(\mathcal P_s+\frac{\mathcal E_s}{2d}\right)
\ge P_\gamma+\frac{E_\gamma}{2d}+G_\gamma.
\tag{249.7}
$$

这不排除两个分别取的下极限同时最小：沿不同子列交替采用两类最优准备，确实可以得到这种情况。不能共同达到的断言针对两个完整极限。

证明。 先推导任意秩的过零约束。设 $v_s=\sqrt{se_s}$、$\epsilon_s=e_s/s$，于是 $v_s=s\sqrt{\epsilon_s}=o(s)$。令 $p_\times$ 为首次远端分隔面过零位置，记

$$
t_s=\frac{p_\times-p_{\delta_s}}{\Delta_s}\in[0,1],
\qquad
\Delta_s=h_3(s)-p_{\delta_s},\qquad
\frac{\Delta_s}{se_s}\longrightarrow d.
\tag{249.8}
$$

低内部代价条件与第243—244节保证该过零确实位于尾窗。分别证明两个下界时，只须考察相应归一化代价有界的子列；若证明（249.7），只须考察其左边和式有界的子列。Cauchy–Schwarz 使每一种情况下过零后的 Fisher 长度均为 $O(s)$。由迹速度界，实部路径距实际第三节点投影为 $O(s)$。

写 $\rho=S+iK$，在过零点将 $S$ 的非核块分解为

$$
S=\begin{pmatrix}x^2&\beta^{\mathsf T}\\ \beta&W\end{pmatrix},
\quad
W=\mu\phi\phi^{\mathsf T}+E,\quad
E\ge0,\quad E\phi=0,\quad
\mu=p-\operatorname{Tr}E,\quad x^2=1-p.
\tag{249.9}
$$

第248.6—248.10式的精确谱余量论证在本尺度仍成立，给出

$$
\operatorname{Tr}E=O(v_s^2),\qquad
\|\beta\|=O(sv_s),\qquad
\phi=v_*+O(s).
\tag{249.10}
$$

这里 $v_*$ 为第三节点实际带符号极限方向。这个论证先从实部预算推出 $\lambda_1(S)=p-O(\delta_s^2-F_s^2)$，再用正性与分隔面条件得到 $\|\beta\|^2\le Cs^2\operatorname{Tr}E$，最后以
$\lambda_1(S)\le p-\operatorname{Tr}E+Cs^2\operatorname{Tr}E$
闭合；故余量始终为 $O(se_s)$，不会另生一个压过极小 $e_s$ 的独立 $s$ 次幂误差。

在实分解 $q\oplus\phi\oplus\{q,\phi\}^{\perp}$ 中记
$\kappa=K_{q\phi}$、$\ell=K_{\phi,\phi^\perp}$、$m=K_{q,\phi^\perp}$。正性及虚性预算给出

$$
\kappa=O(v_s),\quad \ell=O(v_s),\quad
m=O(sv_s),\quad K_{\phi^\perp,\phi^\perp}=O(v_s^2).
\tag{249.11}
$$

其中 $2|\kappa|\le I_R^C(\rho)\le\eta_s=O(v_s)$；其他块由正性控制。消去主方向 $\phi$ 的 Schur 补进一步给出联合估计

$$
\operatorname{Tr}E\ge
\frac{\|\ell\|^2}{\mu}
+\frac{
\|\beta_\perp+\kappa\ell/\mu\|^2+
\|m-\beta_\phi\ell/\mu\|^2}
{x^2-(\beta_\phi^2+\kappa^2)/\mu}
\ge \|\ell\|^2+\frac{\|m\|^2}{x^2}+o(v_s^2).
\tag{249.12}
$$

分母为 $x^2(1+o(1))$，因为 $\kappa^2/x^2=O(\epsilon_s)$。虚部的领先项是以 $\phi$ 为中心的反对称星形块，其迹范数为 $2\sqrt{\kappa^2+\|\ell\|^2}$，其余块为 $o(v_s)$。同时，直接展开纯度并保留精确的 $f(p)^2=4p(1-p)$，有

$$
\begin{aligned}
[I_R^C(\rho)]^2
 &=4(\kappa^2+\|\ell\|^2)+o(v_s^2),\\
J(\rho)^2
 &=f(p)^2+
4\bigl(\operatorname{Tr}E-\kappa^2-\|\ell\|^2\bigr)
+o(v_s^2).
\end{aligned}
\tag{249.13}
$$

例如纯度展开中被舍去的项为 $O(s^2v_s^2+v_s^4)$，均含实际的小噪声。

令 $Y$ 为 $e_y$ 在 $\phi^\perp$ 上投影的单位化，写

$$
\phi_y=sR,\qquad z=\frac{R-r_0}{d},\qquad
k=\frac{\kappa}{v_s},\qquad l=\frac{\ell_Y}{v_s}.
\tag{249.14}
$$

有界剩余长度保证 $R,z$ 有界。实际处理器满足

$$
\begin{aligned}
k_s^{\mathsf T}\phi&=\sigma sd\,z+O(s^2),\\
k_s^{\mathsf T}Y&=\sigma+O(s),\\
\phi^{\mathsf T}(B_s^{\mathsf T}-B_s)Y
&=-\sigma ds+O(s^2).
\end{aligned}
\tag{249.15}
$$

完整虚矩因此给出
$m_Y/(sv_s)=d(l-kz)+o(1)$。代入（249.12）—（249.13），分别使用两项预算，得到

$$
\begin{aligned}
k^2+l^2&\le d\gamma_s+o(1),\\
J(\rho)^2&\ge
f(p)^2+4se_s\bigl((l-kz)^2-k^2\bigr)+o(se_s).
\end{aligned}
\tag{249.16}
$$

其他横向虚部在正性所需的 $\operatorname{Tr}E$ 中至少支付自己的平方，抵消纯度式中的相应负项，并继续占用虚性预算，所以不能改善这个下界。式（249.15）的系数误差始终乘以 $v_s$ 或 $sv_s$。

先作精确差再取极限：

$$
\delta_s^2-f(p_\times)^2
=4(p_\times-p_{\delta_s})(p_\times+p_{\delta_s}-1),
\qquad
\frac{\delta_s^2-f(p_\times)^2}{4dse_s}=t_s+o(1).
\tag{249.17}
$$

由于 $\zeta_s^2=\delta_s^2-\eta_s^2$，混合预算要求
$(l-kz)^2-k^2\le d(t_s-\gamma_s)+o(1)$。左边二次型的矩阵为

$$
M(z)=\begin{pmatrix}z^2-1&-z\\-z&1\end{pmatrix},
\qquad
\lambda_-(z)=\frac{z^2-\sqrt{z^4+4}}2=g(z)-1<0.
\tag{249.18}
$$

在预算圆盘上最小化该二次型，遂得

$$
t_s\ge\gamma_s g(z)+o(1).
\tag{249.19}
$$

接着将此过零约束与同一路径的剩余长度结合。按第248.16—248.19式，先作正定实部扰动，再用实 Sylvester 方程获得同一个水平因子。其 $q$ 行至少走过半径 $sd(1+o(1))$ 上的直角距离；其 $y$ 行沿终端辅助方向从 $sR+o(s)$ 变到 $2sr_0+o(s)$。两条不同物理行的积分 Minkowski 不等式给出

$$
\mathcal L_s\ge
2sd\sqrt{\frac{\pi^2}{4}+(h-z)^2}+o(s).
\tag{249.20}
$$

剩余时段为 $2\Delta_s(1-t_s)$，故

$$
\mathcal P_s\ge\frac{A(z)+o(1)}{(1-t_s)^2},
\qquad
\mathcal E_s\ge2d\frac{A(z)+o(1)}{1-t_s}.
\tag{249.21}
$$

有界代价使 $1-t_s$ 有正下界。任意实 $z$ 投影到 $[0,h]$，均使 $A(z)$ 与偶函数 $g(z)$ 不增；所以过零方向无需事先限于该区间。结合（249.19）后沿收敛子列取极限，即得（249.5）及（249.7）的非严格部分。这是对同一实际准备的联合限制。

下面证明可达性，而不将点态过零可行性当成全域可续接性。固定 $z\in\mathcal Z_\gamma$，令 $R=r_0+dz$。在实基 $(q,\phi,Y)$ 中固定 $\phi_y=sR$，并引入实控制 $a,\kappa,\ell,m,w$。设

$$
\mu=p-w,\qquad
Q_0^2=x^2-\frac{a^2+\kappa^2}{\mu},
\qquad
A=(\alpha,\beta),
\tag{249.22}
$$

其中两列为

$$
\alpha=
\begin{pmatrix}
(a+i\kappa)/\sqrt\mu\\ \sqrt\mu\\ -i\ell/\sqrt\mu
\end{pmatrix},
\qquad
\beta=
\begin{pmatrix}
Q_0\\0\\
[\kappa\ell/\mu-i(m-a\ell/\mu)]/Q_0
\end{pmatrix}.
\tag{249.23}
$$

直接相乘得到
$\rho_{q\phi}=a+i\kappa$、$\rho_{\phi Y}=i\ell$、$\rho_{qY}=im$。对角元及完整复矩恰由以下方程控制：

$$
\begin{aligned}
w&=\frac{\ell^2}{\mu}
+\frac{(\kappa\ell/\mu)^2+(m-a\ell/\mu)^2}{Q_0^2},\\
m&=-\frac{\kappa k_s^{\mathsf T}\phi+
\ell\phi^{\mathsf T}(B_s^{\mathsf T}-B_s)Y}
{k_s^{\mathsf T}Y},\\
\mu\phi^{\mathsf T}Q_s\phi+
wY^{\mathsf T}Q_sY+a k_s^{\mathsf T}\phi&=a_s,
\qquad Q_s=(B_s+B_s^{\mathsf T})/2,\\
\|\phi\|^2&=1.
\end{aligned}
\tag{249.24}
$$

因此 $\rho=AA^\dagger$ 精确正、迹为一、秩至多二，两个矩均精确。其实部的核—非核相干为 $a\phi$，所以所需分隔面在 $a=0$ 精确穿过。

为说明解和误差在任意极小 $e_s$ 下仍可控，使用缩放

$$
a=v_sa_0,\quad \kappa=v_sk,\quad \ell=v_sl,\quad
m=sv_sm_0,\quad w=v_s^2w_0.
\tag{249.25}
$$

在有界控制及有界尾窗坐标上，$Q_0^2/s^2$ 趋于 $d^2>0$。消去 $m_0$ 后，对 $\phi_z,\phi_w,w_0$ 的三条方程在极限化为

$$
\phi_z^2+\phi_w^2=1,\qquad
\phi_z^2-\phi_w^2=\alpha,\qquad
w_0=l^2+(l-kz)^2.
\tag{249.26}
$$

取实际第三节点的 $\phi_z>0,\phi_w<0$。其 Jacobian 为对角块可逆的下三角矩阵：前两行对 $w_0$ 的导数为零，二维范数—矩 Jacobian 非零，末行对 $w_0$ 的导数为一。缩放后的隐函数定理遂给出实际解及有界控制导数，并有
$w_0=l^2+(l-kz)^2+O(s+\sqrt{\epsilon_s})$。
这个步骤将可能的 $1/s$ 因子先吸收进坐标；误差不会在最后再除以一个任意小的 $se_s$。

在该精确图上，两项资源满足

$$
\begin{aligned}
[I_R^C]^2&=4(\kappa^2+\ell^2+m^2),\\
J^2&=f(p)^2+4pw-4w^2
-4(a^2+\kappa^2+\ell^2+m^2)\\
&=f(p)^2+
4se_s\bigl((l-kz)^2-k^2-a_0^2\bigr)+o(se_s).
\end{aligned}
\tag{249.27}
$$

第一式使用实三维反对称矩阵的两个非零奇异值相等。所有余项连同所需控制导数均在缩放后趋零。

取 $M(z)$ 的负特征值单位特征向量 $v_-(z)$。选择
$\omega_s\downarrow0$、$s+\sqrt{\epsilon_s}=o(\omega_s)$，令

$$
(k,l)=(1-\omega_s)\sqrt{d\gamma_s}\,v_-(z),\quad
q_s=(l-kz)^2-k^2,\quad
t_{{\rm req},s}=\gamma_s+\frac{q_s}{d},\quad
t_{c,s}=t_{{\rm req},s}+2\omega_s.
\tag{249.28}
$$

则 $t_{c,s}\to\gamma g(z)<1$，虚性预算和过零处混合预算均保有阶为 $\omega_sse_s$ 的平方余量。

先在尾窗之前建立可行入口。保持 $K_s$ 上的第一规范支，用第246节的实际实圆连接进入 $\phi_y=sR$、核—非核实相干为负的实矩图；其极限方向位于同一实圆分支，范数—矩 Jacobian 仍可逆。实混合段满足 $J^2=f(p)^2-4a^2$。在可行下界
$a^2\ge(f(p)^2-\zeta_s^2)/4$
与纯态上界 $a^2\le f(p)^2/4$ 之间选有严格余量的光滑曲线，从纯实支接到 $a=-Lv_s$，其中固定 $L$ 足够大。秩一接点的互补因子坐标取平坦值。

在严格位于 $p_{\delta_s}$ 左边、距离为 $O(\Delta_s)$ 的窗口内保持这个负相干，开启 $\kappa,\ell$，并由（249.24）精确跟随其余坐标。项 $-4L^2se_s$ 给整个有界控制路径提供混合预算余量，收缩系数 $1-\omega_s$ 保证虚性预算余量。再在尾窗之前平滑接入下述入口值。这些操作均在 $T_s$ 和 $K_s$ 之外；其矩及资源仍逐点满足原任务，只是不将这段的 Fisher 代价计入（249.2）。

在尾窗内直到首次过零，保持 $k,l,R$，使用平滑平方根包络

$$
a_0(t)=-\sqrt d\,F_{\omega_s}(t_{c,s}-t).
\tag{249.29}
$$

这里 $F_\omega(w)>0$ 对 $w>0$ 成立，在 $w=0$ 平坦为零，且可选为

$$
F_\omega(w)^2\ge\max(w-\omega,0),\qquad
F_\omega(w)=\sqrt w\quad(w\ge2\omega),\qquad
|F_\omega'(w)|\le C/\sqrt\omega.
\tag{249.30}
$$

例如令 $F_\omega(w)=\sqrt w\,\chi(w/\omega)$，其中光滑 $\chi$ 在零点平坦为零、对每个 $r>0$ 严格为正，并在 $r\ge1$ 恒为一，即得到这些性质。此时

$$
d(t_{{\rm req},s}-t)-a_0(t)^2\le-d\omega_s.
\tag{249.31}
$$

故缩放误差被严格余量吸收。平方根包络在剩余预算缺口降为零之前保留足够的实相干；任意线性减小相干不具备这个保证。显式因子的导数满足
$\|\partial_tA\|_F\le C(v_s/\sqrt{\omega_s}+e_s)$，
因此这一等待段的归一化峰值与积分均趋零。

过零后在占比 $\beta_s=\epsilon_s^{1/4}$ 的尾窗内，先将 $a$ 提至 $+Lv_s$，再用同一个从一平坦降到零的因子关闭 $\kappa,\ell$。前一步的 $-4a^2$ 增加预算余量，后一步只需取 $L^2>d\sup_{s<s_0}\gamma_s+1$ 并留固定余量，便由（249.27）覆盖关闭虚部的混合成本。实际因子仅改变 $O(v_s)$；其归一化峰值及积分分别为 $O(\epsilon_s/\beta_s^2)$ 与 $O(\epsilon_s/\beta_s)$，均趋零。控制皆取平坦端点。

关闭虚部后，（249.24）精确给出 $m=w=0$。在上述 $O(\beta_s\Delta_s)$ 清理宽度中再留一个实缓冲段。设其左端为 $p_e$，用两端平坦的切换 $\chi$ 取

$$
a(p)=Lv_s\left(1-\chi(p)+\chi(p)\frac{f(p)}{f(p_e)}\right).
\tag{249.31a}
$$

这使左端的常数 $a$ 光滑接到右端的常数角
$\cos\theta=2Lv_s/f(p_e)$，并在同一实图中解矩方程。因 $f'/f=O(s^{-2})$，该缓冲相对于 $Lv_s$ 的修正为 $O(v_s\beta_s\epsilon_s)$，保留严格资源余量，归一化信息代价仍趋零。其后因子成为

$$
A=\phi(\sqrt p,0)+q(x\cos\theta,x\sin\theta),
\qquad \theta=\frac{\pi}{2}-o(1).
\tag{249.32}
$$

在余下尾窗内，用同一近似线性进度 $\chi$ 将 $\theta$ 降至零，并取
$y(p)=(1-\chi(p))sR+\chi(p)(v_{3,s}(p))_y$，
使右端平坦部分精确等于实际第三规范支。以实际范数—矩图解其余两个坐标。该图满足
$\partial_y\phi=e_y+O(s)$、
$\partial_\theta\phi=O(s^2)$、
$\partial_p\phi|_{y,\theta}=O(1)$。
资源为 $J=f(p)\sin\theta$；两因子继续下降，保持清理段留下的严格余量。

直接对（249.32）求导，使用 $u=2p-1$，有

$$
4\|A'_u\|_F^2
=\frac1{4p(1-p)}
+(1-p)\theta_p^2+p\|\phi_p\|^2.
\tag{249.33}
$$

其中角项与实际 SLD 角项 $p(1-p)\theta_p^2$ 只差相对 $O(s^2)$。因此这个具体因子的信息上界已足够达到领先常数，不需要假定任意跨秩路径存在光滑的最小净化。主运动的领先平方长度为 $4s^2d^2A(z)$，可用时段为
$2\Delta_s(1-\gamma g(z)+o(1))$。
取趋于常速的进度并留趋零比例的平坦端部，遂得

$$
\limsup\mathcal P_s\le\frac{A(z)}{D_\gamma(z)^2},\qquad
\limsup\mathcal E_s\le2d\frac{A(z)}{D_\gamma(z)}.
\tag{249.34}
$$

还须把这个光滑背景完成为全域解析准备。所需的完整矩正则性可在实际处理器上精确证明。第223节的缺陷向量关系给出

$$
B_sB_s^\dagger+k_sk_s^\dagger=I_3,\qquad
B_s^\dagger e_j=\lambda_je_j,\qquad
k_s^\dagger e_j=1,
\tag{249.35}
$$

其中 $\lambda_j$ 为三个互异非零实稳定特征值，$e_j$ 构成一组基。于是 $\lambda_jB_se_j=e_j-k_s$。置
$H_\theta=(e^{-i\theta}B_s+e^{i\theta}B_s^\dagger)/2$，有精确恒等式

$$
\bigl(I-2\lambda_je^{i\theta}H_\theta+
\lambda_j^2e^{2i\theta}I\bigr)e_j=k_s.
\tag{249.36}
$$

若 $H_\theta v=\lambda v$ 且 $k_s^\dagger v=0$，与该式配对后得到
$[1-2\lambda z+z^2]v^\dagger e_j=0$，其中 $z=\lambda_je^{i\theta}$。因为 $\|H_\theta\|\le1$，该二次多项式的根都在单位圆上，而 $|z|<1$，所以 $v^\dagger e_j=0$ 对所有 $j$ 成立，故 $v=0$。因此 $H_\theta$ 的每个特征空间都一维，且不与 $k_s$ 正交。

对于完整 Hermitian 矩阵束

$$
G_{\theta,\nu}=\operatorname{Re}_{H}(e^{-i\theta}T_s)-\nu P,
\qquad \operatorname{Re}_{H}X=(X+X^\dagger)/2,
\tag{249.37}
$$

不存在与 $q$ 正交的特征向量：其非核部分否则给出 $H_\theta$ 中与 $k_s$ 正交的特征向量。任何重特征空间都能取一个与 $q$ 正交的向量，所以 $G_{\theta,\nu}$ 对全部实 $\theta,\nu$ 具有单重谱。

现在固定 $p\in(0,1)$。若完整矩的两个实微分在
$\|A_q\|^2=1-p$、$\|A_{q^\perp}\|_F^2=p$
上不独立，实 Lagrange 乘子给出非零 Hermitian 组合 $H$ 和两个实数 $\lambda,\mu$，使
$(H-\lambda qq^\dagger-\mu P)A=0$。
缩放 $H$ 后，$A$ 的所有列都属于（249.37）的同一特征空间，故 $\operatorname{rank}A\le1$。因此在每个秩至少二的因子上，两个矩微分都独立，不需要假定小特征值有统一正下界。

背景的纯实连接和规范段由第243、248节的直接实、虚切向量论证覆盖；紧化右端 $x=0$ 的非零虚矩微分使用第248.29a式，实矩微分使用实际谱间隔。故归一化因子坐标

$$
A_q=x\xi,\qquad A_{q^\perp}=\sqrt p\,W,\qquad
\|\xi\|=\|W\|_F=1
\tag{249.38}
$$

在闭紧化区间光滑，且两个矩微分处处独立。因子在右端已接回规范纯支，所以 $A_q/x$ 在该端可消去，不造成坐标奇性。这里对每个固定任务的最小奇异值为正，允许其随 $s,e_s,\eta_s$ 退化。

按第248.29b式进行高阶多项式逼近、Hermite 匹配、两个球面的归一化及两个实解析参数的矩修正。梯度 Gram 矩阵一致正定，解析隐函数的局部解由唯一性拼合。每个固定任务的两个资源均有严格全域余量，故可把逼近精度选到同时保持两项预算，并在完整节点区间达到

$$
\sqrt{I_Q(\rho_{\rm final})}
\le2\|(A_{\rm final})'_u\|_F
\le2\|(A_{\rm bg})'_u\|_F+1.
\tag{249.39}
$$

这使用净化信息上界，不要求最终 SLD 在秩下降处连续。平方及积分后，（249.34）的两项归一化附加误差均趋零；$K_s$ 上的两个有界代价保持。纯规范段的辅助方向为常数，因子信息恰为纯态信息；保留至少四阶及所有指定的更高阶节点数据，再结合普适下曲率界，即保留普通最优双侧曲率。实际节点及谱必要性同时保留完整尖锐集合和联合支持四。

另外可令 $C^0$ 误差足够小，使最终路径的首次分隔面过零仍在 $t_{c,s}$ 的一个趋零邻域内，过零方向仍趋于同一 $R$。原背景在该邻域以外的紧集上分隔面符号严格；邻域以内的实际图则给出方向控制。对最终路径使用（249.21），便使（249.34）两项均成为等式极限。故对每个固定 $z\in\mathcal Z_\gamma$，存在同一解析族满足

$$
\mathcal P_s\longrightarrow\frac{A(z)}{D_\gamma(z)^2},
\qquad
\mathcal E_s\longrightarrow2d\frac{A(z)}{D_\gamma(z)}.
\tag{249.40}
$$

全过程的容差与逼近次数均在固定任务之后选取，不要求统一解析半径或以 $s$ 的某个幂为精度下限。

最后证明两类极小点不同。令 $F_j(z)=A(z)/D_\gamma(z)^j$，$j=1,2$。在 $z=0$ 有 $F_j'(0)=-2h<0$；若 $h$ 可行，则 $F_j'(h)>0$；若可行域在 $h$ 之前终止，则接近其边界时 $F_j\to\infty$。因此每一个极小点都在 $0<z<h$ 且 $D_\gamma(z)>0$ 的内部，最小值实际取得。

峰值极小点与累计极小点分别必须满足

$$
\begin{aligned}
(h-z)D_\gamma(z)&=\gamma g'(z)A(z)
&&\text{（峰值）},\\
2(h-z)D_\gamma(z)&=\gamma g'(z)A(z)
&&\text{（累计）}.
\end{aligned}
\tag{249.41}
$$

由于内部 $g'(z)>0$、$h-z>0$，两个方程不可能在同一点成立。无需证明各自极小点唯一：适当紧子水平集上的连续性和无共同极小点，已经给出（249.6）的严格正间隙。分别取两类极小点代入（249.40），即证明各自可达性；（249.7）排除两个最优值共同作为完整极限。证毕。

**注记 249.3（距离与可用时段共同组成代价）。** 参数 $z$ 增大时，终端方向恢复距离 $d(h-z)$ 减少，但（249.19）要求更晚过零，剩余时段比例变为 $D_\gamma(z)$。峰值代价除以这个比例的平方，累计代价只除以一次。两种评价因此选择不同的关系路径。第246、248节在各自的尺度中给出两项代价共同最优的准备族；本节有限过渡尺度保留了这个不能同时优化的内部选择。

这里的 $u$ 仍是原任务参数，$I_Q$ 积分是本节定义的累计 Fisher 代价；本节未把它识别为实验室时间上的能耗。结论依赖两个分别限制的全域预算及既定低内部代价条件，不能只保留一个合成预算后照搬。

缺陷一收缩的数值域背景可参见 Gau、Wu，*Numerical ranges and compressions of $S_n$-matrices*，Operators and Matrices **7**(2), 465–476（2013），DOI:10.7153/oam-07-28，尤其其定义及定理2.2。按该文约定，实际 $B_s^\dagger,T_s^\dagger$ 分别属于 $S_3,S_4$；上面的带 $\nu P$ 矩阵束与因子正则性由（249.35）—（249.38）直接证明。SLD、净化、Schur 补及解析逼近均为既有工具；本节的新组合结论是实际任务的过零约束、可达代价公式及两个目标的严格分离，不主张这些工具的原创性或已经取得 Lean 认证。

<a id="entry-848"></a>

## 追加锚（本行以下为增补区）

<a id="section-250"></a>

## 250. 过渡区的唯一最优过零方向与严格凸代价边界

**定义 250.1（固定过渡比值的两个无量纲坐标）。** 固定第249节中的 $\gamma>0$。记
$c=\pi^2/4$、$h=b/\sigma$、
$A(z)=c+(h-z)^2$、
$D(z)=1-\gamma g(z)$，
并置

$$
F_j(z)=\frac{A(z)}{D(z)^j},\qquad j=1,2,\qquad
0\le z\le h,\quad D(z)>0.
\tag{250.1}
$$

比较的代价对是 $(\mathcal P_s,\mathcal E_s/(2d))$。其有限极限或有限聚点都仍取自第249节的同一实际任务、分别成立的两项全域预算和低内部代价条件。Pareto 最优指不存在另一个可达聚点，使两坐标均不增且至少一个严格下降。

**定理 250.2（唯一性、顺序及完整 Pareto 边界）。** 对每个有限 $\gamma>0$，$F_2,F_1$ 各有唯一极小点，分别记为 $z_2,z_1$，且

$$
0<z_2<z_1<h.
\tag{250.2}
$$

两个极小点随 $\gamma$ 严格递减。所有有限可达代价聚点的 Pareto 边界恰为

$$
\left\{\bigl(F_2(z),F_1(z)\bigr):z_2\le z\le z_1\right\}.
\tag{250.3}
$$

每个边界点均由保持第249节全部全域条件的一族解析准备达到为极限。将第二坐标写为第一坐标的函数，这条边界在开弧上严格凸，左端斜率为 $-\infty$，右端斜率为零。因此对任意正权重 $w$，$w\mathcal P+\mathcal E/(2d)$ 有唯一的边界最优点。这里的唯一性针对缩放过零方向和代价点，不要求实现它们的完整准备曲线唯一。

证明。 令 $r=h-z>0$，定义

$$
H_j(z)=g(z)+\frac j2\,\frac{A(z)g'(z)}r.
\tag{250.4}
$$

直接求导有

$$
F_j'(z)=2rD(z)^{-j-1}\bigl(\gamma H_j(z)-1\bigr).
\tag{250.5}
$$

以下关键是实际 $h$ 的范围，而非对任意 $h$ 作无条件主张。参数 $\alpha=a_*$ 满足 $4\alpha^2(1+\alpha)=1$。在 $\alpha=21/50$ 时左边为 $125244/125000>1$，故

$$
h^2=\frac{4\alpha^2}{1-4\alpha^2}
<\frac{441}{184}<\frac{961}{400},
\qquad h<\frac{31}{20},\qquad c>\frac{12}{5}.
\tag{250.6}
$$

令 $v=z^2/\sqrt{z^4+4}$。精确地，

$$
\begin{aligned}
g'(z)&=z(1-v),\\
g''(z)&=(1-v)(1-2v-2v^2),\\
H_2'(z)&=\frac{cg'(z)}{r^2}
+\left(r+\frac cr\right)g''(z),\\
H_1'(z)&=\frac{g'(z)+H_2'(z)}2.
\end{aligned}
\tag{250.7}
$$

要证 $H_2'>0$，除去正因子后，只须证

$$
z+r\left(1+\frac{r^2}{c}\right)(1-2v-2v^2)>0.
\tag{250.8}
$$

在 $0<z\le4/5$，$v\le z^2/2\le8/25$，所以第二项中的最后因子为正。其余区间中，若该因子仍非负便无需估计；为负时记 $K=2v+2v^2-1$，使用以下有理界：

- 若 $4/5\le z\le1$，则 $v\le1/\sqrt5<9/20$、$K<1/3$、$r<3/4$，于是
  $r(1+r^2/c)K<(3/4)(1+(9/16)/(12/5))/3<4/5\le z$。
- 若 $1\le z\le6/5$，则 $v\le36/\sqrt{3796}<3/5$、$K<1$、$r<11/20$，于是
  $r(1+r^2/c)K<(11/20)(1+(121/400)/(12/5))<1\le z$。
- 若 $6/5\le z<h$，则 $v<1$、$K<3$、$r<7/20$，于是
  $r(1+r^2/c)K<3(7/20)(1+(49/400)/(12/5))<6/5\le z$。

因此 $H_2'>0$，也有 $H_1'>0$。两者在零点为零，在 $z\uparrow h$ 时趋于无穷。方程

$$
H_j(z_j)=\frac1\gamma
\tag{250.9}
$$

各有唯一解；因 $H_j(z)>g(z)$，这个解自动满足 $D(z_j)>0$。式（250.5）给出极小点两侧的严格单调性。又因 $H_2(z)>H_1(z)$，故 $z_2<z_1$。对（250.9）求导，
$dz_j/d\gamma=-1/(\gamma^2H_j'(z_j))<0$。

第249节的联合过零下界意味着：任一有限代价聚点 $(P,Q)$，都对至少一个 $z$ 满足 $P\ge F_2(z)$、$Q\ge F_1(z)$；该节同时给出每一个这样的曲线点的实际解析达到。当 $z<z_2$ 时，两函数都随 $z$ 下降；当 $z>z_1$ 时，两函数都上升。在 $[z_2,z_1]$ 上，第一坐标严格上升，第二坐标严格下降。因此外部曲线点被这段弧上的点支配，弧内互不支配。若某个可达聚点能改善一个弧内点，则它逐坐标不小于的那个曲线点也会改善该弧内点，与上述单调性矛盾。于是（250.3）恰为完整 Pareto 边界。

在开弧上，记 $P=F_2(z)$、$Q=F_1(z)$。由（250.5），

$$
-\frac{dQ}{dP}
=D(z)\,
\frac{1-\gamma H_1(z)}{\gamma H_2(z)-1}.
\tag{250.10}
$$

右边三个正因子中，$D$ 严格下降，分子严格下降，分母严格上升。对右边乘积求导，每一贡献非正且 $D$ 的贡献严格为负，故 $d(dQ/dP)/dz>0$；又 $dP/dz>0$，所以 $d^2Q/dP^2>0$。两个端部的极限直接给出所述斜率，正权线斜率 $-w$ 与此弧恰有一个切点。证毕。

**定理 250.3（两个端部的过零方向与共同最优间隙）。** 记
$g_h=g(h)$、$p_h=g'(h)>0$、$C=c+h^2$，
以及 $m_j(\gamma)=\min F_j$。在已取过 $s\downarrow0$ 的限制问题中，$\gamma\downarrow0$ 时

$$
\begin{aligned}
h-z_j&=\frac j2\,c p_h\gamma+O(\gamma^2),\\
m_j(\gamma)
&=c+jcg_h\gamma+
\left[\frac{j(j+1)}2cg_h^2-\frac{j^2}{4}c^2p_h^2\right]\gamma^2
+O(\gamma^3),\\
G_\gamma&=\frac{c^2p_h^2}{8}\gamma^2+O(\gamma^3).
\end{aligned}
\tag{250.11}
$$

而 $\gamma\to\infty$ 时

$$
\begin{aligned}
z_j&=\frac{2h}{jC\gamma}+O(\gamma^{-2}),\\
m_j(\gamma)&=C-\frac{2h^2}{jC\gamma}+O(\gamma^{-2}),\\
G_\gamma&=\frac{h^2}{3C\gamma}+O(\gamma^{-2}).
\end{aligned}
\tag{250.12}
$$

其中 $G_\gamma$ 正是第249.6式的共同最优间隙。

证明。 小 $\gamma$ 时，极小点的唯一性及（250.9）使 $z_j\to h$。在 $r=h-z$ 中将驻点条件写成
$rD=(j/2)\gamma A g'$，其在 $(r,\gamma)=(0,0)$ 对 $r$ 的导数为一。因此解关于 $\gamma$ 解析，首阶为 $r=(j/2)cp_h\gamma$。展开

$$
A=c+r^2,\qquad
D=1-\gamma g_h+\gamma p_h r+O(\gamma r^2)
\tag{250.13}
$$

并代回 $A/D^j$，得到（250.11）的前两行。对于 $F_1+F_2$，其唯一最优点由定理250.2的等权切线给出，同一局部解析计算得到
$r=(3/4)cp_h\gamma+O(\gamma^2)$，
以及

$$
\min(F_1+F_2)
=2c+3cg_h\gamma+
\left(4cg_h^2-\frac98c^2p_h^2\right)\gamma^2
+O(\gamma^3).
\tag{250.14}
$$

减去 $m_1+m_2$，得到间隙系数 $1/8$。

大 $\gamma$ 时，令 $\varepsilon=1/\gamma$。由（250.9），$z_j\to0$；而
$g(z)=z^2/2+O(z^4)$、
$H_j'(0)=jC/(2h)>0$。
隐函数定理给出 $z_j=2h\varepsilon/(jC)+O(\varepsilon^2)$。用

$$
A=C-2hz+z^2,\qquad
D=1-\frac{z^2}{2\varepsilon}
+O(z^4/\varepsilon)
\tag{250.15}
$$

代入，便得（250.12）的前两行。对等权和式，同一计算给出
$z=4h\varepsilon/(3C)+O(\varepsilon^2)$，
其最小值为 $2C-8h^2\varepsilon/(3C)+O(\varepsilon^2)$。减去两项独立最小值之和 $2C-3h^2\varepsilon/C+O(\varepsilon^2)$，即得第三行。证毕。

**注记 250.4（有限尺度中的严格权衡）。** 峰值最优点 $z_2$ 小于累计最优点 $z_1$：前者保留较多恢复距离，以换取较长的剩余时段；后者容许更晚过零，缩短恢复距离。每个有限 $\gamma$ 都有严格正的共同最优间隙，但这一间隙在两个端部以不同的速率消失。

本节仅确定可达聚点的 Pareto 边界及支配关系，未断言该边界上方每一点都实际可达。式（250.11）—（250.12）先使用第249节固定 $\gamma$ 的极限问题，再令 $\gamma$ 移动；它们没有交换两个极限，也未给出 $\gamma_s\to0$ 或 $\gamma_s\to\infty$ 时一致的原任务误差界。所用 Pareto 次序、驻点法、隐函数定理和 Taylor 展开是既有工具。量子多目标控制的既有背景可参见 Chakrabarti、Wu、Rabitz，*Quantum Pareto optimal control*，Phys. Rev. A **78**, 033414（2008），DOI:10.1103/PhysRevA.78.033414，第II节：该文讨论受控 Schrödinger 演化下的终端可观察量期望及正权标量化。本节的两个目标是第249节定义的 Fisher 代价，其严格凸性、唯一缩放方向及间隙系数由上面的实际公式推导，不从该文转移这些结论，也不作 Lean 认证或文献优先权主张。

<a id="entry-850"></a>

## 追加锚（本行以下为增补区）

<a id="section-251"></a>

## 251. 小于过渡尺度的虚性预算与完整领先系数分界

**定理 251.1（次过渡尺度保持全实最优系数）。** 沿用第243—250节的实际任务、分别成立的全域预算及尾窗。设

$$
\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,\qquad
0<e_s=o(s),\qquad
\frac{\eta_s^2}{se_s}\longrightarrow0.
\tag{251.1}
$$

任意满足第244.9式任一低内部代价条件的允许准备族，均有

$$
\liminf e_s^2\sup_{T_s}I_Q\ge\frac{\pi^2}{4},\qquad
\liminf\frac{e_s}{s}\int_{T_s}I_Q\,du\ge\frac{\pi^2d}{2}.
\tag{251.2}
$$

存在同一族全域实解析、每点秩至多二的完全实准备，将两项下界同时达到为极限，并保持 $K_s$ 上两个代价一致有界及原任务的全部精确性、支持、尖锐集合、普通最优双侧曲率和指定有限阶实规范节点数据。这个构造也适用于 $\eta_s$ 在任意子列精确为零。

证明。 下界就是第244节。由于 $\eta_s^2=o(se_s)$，最终 $\zeta_s>F_s$；但直接在 $\zeta_s$ 的较短尾窗应用第246节不足以控制原来的整个 $T_s(F_s+e_s)$。下面在原尾窗上构造。

仍记 $v_s=\sqrt{se_s}$、$\epsilon_s=e_s/s$、
$\gamma_s=\eta_s^2/(4dse_s)\to0$、
$t=(p-p_{\delta_s})/\Delta_s$。选择
$\omega_s\downarrow0$ 且 $s+\sqrt{\epsilon_s}=o(\omega_s)$，置
$t_{c,s}=\gamma_s+2\omega_s\to0$。
使用第249节完全实的因子支：令 $\kappa=\ell=m=w=0$，固定方向坐标 $\phi_y=2sr_0$，使

$$
A=\phi(\sqrt p,0)+q(x\cos\theta,x\sin\theta),
\qquad a=x\sqrt p\cos\theta.
\tag{251.3}
$$

实际范数和实矩确定另外两个坐标，使用第三规范支的符号。这一图保持精确性、正性及秩至多二，并精确满足

$$
I_R^C(AA^{\mathsf T})=0,\qquad
J(AA^{\mathsf T})^2=f(p)^2-4a^2.
\tag{251.4}
$$

在原尾窗入口至过零点之间，取

$$
a(t)=-\sqrt d\,v_s F_{\omega_s}(t_{c,s}-t),
\tag{251.5}
$$

其中 $F_\omega$ 为第249.30式的平滑平方根包络。由实际差式249.17及 $\Delta_s/(se_s)=d+O(s+\epsilon_s)$，

$$
\frac{f(p)^2-\zeta_s^2}{4se_s}
=d(\gamma_s-t)+O(s+\epsilon_s)
\tag{251.6}
$$

在整个尾窗一致成立。误差是除去精确基线后的系数误差，未引入独立于 $e_s$ 的加性幂次项。包络给出
$d(\gamma_s-t)-a(t)^2/(se_s)\le-d\omega_s$，
所以 $J<\zeta_s$ 具有严格余量。虚性恒为零。

负相干的可行入口由第246、249节的实际实圆及实矩图在尾窗之前建立，$K_s$ 上保持第一规范支。可以将（251.5）向左延长到一个固定负的 $t$ 值，在那里 $a=O(v_s)$；再沿
$(f(p)^2-\zeta_s^2)/4<a^2\le f(p)^2/4$
的严格可行区域平滑接回纯实支。所有这些前置连接都在原尾窗与 $K_s$ 外，仍逐点保持矩与资源。

等待段的显式因子导数满足

$$
\|\partial_tA\|_F\le
C\left(\frac{v_s}{\sqrt{\omega_s}}+e_s\right).
\tag{251.7}
$$

于是其归一化峰值与积分均为
$O(\epsilon_s/\omega_s+\epsilon_s^2)=o(1)$。
在 $t=t_{c,s}$，$a=0$ 且所有控制导数平坦，故 $\theta=\pi/2$。之后用同一个近似常速且两端平坦的进度 $\chi$，取

$$
\theta=\frac{\pi}{2}(1-\chi),\qquad
\phi_y(p)=(1-\chi)2sr_0+\chi(v_{3,s}(p))_y.
\tag{251.8}
$$

右端平坦部分精确等于第三规范支。实际第三方向满足
$(v_{3,s}(p))_y=2sr_0+O(s^2)$，
所以这一段的方向恢复总量为 $O(s^2)$；其领先长度只来自角运动。进入本段时 $f(p)^2<\zeta_s^2$ 已有严格余量，之后 $f(p)$ 和 $\sin\theta$ 均下降，故预算持续成立。

实际实矩图的导数估计与第249.33式的同一因子信息上界给出领先平方长度 $\pi^2s^2d^2$。可用时段为
$2\Delta_s(1-t_{c,s})=2dse_s(1+o(1))$。
将端部平坦区占比选到趋零，遂得

$$
\limsup e_s^2\sup_{T_s}I_Q\le\frac{\pi^2}{4},
\qquad
\limsup\frac{e_s}{s}\int_{T_s}I_Q\,du
\le\frac{\pi^2d}{2}.
\tag{251.9}
$$

最终解析化保持整个因子实。使用实的归一化行坐标 $A_q=x\xi$、$A_{q^\perp}=\sqrt p\,W$，在两个实球面上逼近并匹配节点数据。秩二点的实矩梯度非零：若为零，实 Lagrange 乘子将使因子两列落在第249.37式 $\theta=0$ 矩阵束的同一单重特征空间，矛盾。纯实段及紧化端点沿用第246、248节的实际实矩正则性。

因此对每个固定任务，实矩梯度具有正最小模长。沿此梯度作一个实解析小参数修正，可精确恢复实矩；虚矩因整个因子实而恒为零。因子结构保持迹一、正性、固定读出矩及秩至多二，足够细的逼近保持 $J$ 的严格全域余量，且 $I_R^C$ 仍精确为零，不需从 $\eta_s$ 借出正的误差容限。

令节点匹配阶数至少四，并使整个节点区间的因子一阶误差足够小，便按第249.39式保持（251.9）与有界的 $K_s$ 代价。纯规范邻域的常数辅助方向、普适曲率下界与匹配数据保留普通最优双侧曲率；两个节点及谱必要性保留完整尖锐集合和实际联合支持四。结合（251.2）即得同一族的共同极限。证毕。

**推论 251.2（趋零虚性份额中的三个领先系数区间）。** 在 $\eta_s=o(s)$、$0<e_s=o(s)$ 及原任务条件下，若
$\gamma_s=\eta_s^2/(4dse_s)$
在扩充区间 $[0,\infty]$ 有极限，则两项最优领先系数分为：

| $\gamma_s$ 的极限 | 峰值系数 | 积分系数 | 两个最优系数能否由同一族作为完整极限达到 |
| --- | --- | --- | --- |
| 251.2a · $0$ | $\pi^2/4$ | $\pi^2d/2$ | 能，定理251.1 |
| 251.2b · $\gamma\in(0,\infty)$ | $P_\gamma$ | $E_\gamma$ | 不能，第249节 |
| 251.2c · $\infty$ | $\pi^2/4+h^2$ | $2d(\pi^2/4+h^2)$ | 能，第248节 |

证明。 第一行为本节。第二行为第249节的实际固定比值结论。第三行中
$\eta_s/\sqrt{se_s}=\sqrt{4d\gamma_s}\to\infty$，
配合 $\eta_s=o(s)$ 恰满足第248节。三行都使用原尾窗和同一个低内部代价类别。证毕。

**注记 251.3（量子资源须与剩余可行余量一同计量）。** 三行都允许虚性相对于 $s$ 的份额趋零，但不能据此把几何代价统一压成全实系数。决定这三个区间的是虚性平方与 $se_s$ 的相对大小：小于过渡尺度时可完全使用实准备；在过渡尺度上，过零位置与恢复距离构成严格权衡；大于它而仍满足 $\eta_s=o(s)$ 时，方向恢复距离保留非零的归一化贡献。

表格只分类有极限的 $\gamma_s$。对无极限的预算分配可在相应收敛子列上使用下界，未据此宣告一个统一最优构造。第250节的间隙修正率仍为先取任务极限再移动 $\gamma$ 的结果，本节没有将其提升成同时极限的余项估计。上述结论属于该实际准备任务；未将参数 $u$ 认作物理时间，也未将累计 Fisher 代价认作能耗。

<a id="entry-852"></a>

## 追加锚（本行以下为增补区）

<a id="section-252"></a>

## 252. 振荡预算的自适应最优值与共同追踪判据

**定义 252.1（没有比值极限时的移动基准）。** 保持第248—251节的实际任务、两个分别成立的全域预算、指定有限阶实规范节点数据和原尾窗。设

$$
\delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,
\qquad 0<e_s=o(s),\qquad \eta_s=o(s),
\qquad \gamma_s=\frac{\eta_s^2}{4dse_s}.
\tag{252.1}
$$

不要求 $\gamma_s$ 有极限，也不要求预算关于 $s$ 连续；每个固定任务中的准备仍须关于原输入参数全域实解析。记

$$
P_s=e_s^2\sup_{T_s}I_Q,
\qquad Q_s=\frac{e_s}{2ds}\int_{T_s}I_Q\,du,
\qquad c=\frac{\pi^2}{4},\qquad C=c+h^2.
\tag{252.2}
$$

对 $0<\gamma<\infty$ 使用第250节的 $F_j(z;\gamma)$，置

$$
\begin{aligned}
m_j(\gamma)&=\min_z F_j(z;\gamma),\qquad j=1,2,\\
V_w(\gamma)&=\min_z\bigl(wF_2(z;\gamma)+F_1(z;\gamma)\bigr),
\qquad w>0,\\
G(\gamma)&=V_1(\gamma)-m_2(\gamma)-m_1(\gamma).
\end{aligned}
\tag{252.3}
$$

所有极小值均取于 $0\le z\le h$、$1-\gamma g(z)>0$。在紧化区间 $[0,\infty]$ 的两端定义

$$
\begin{aligned}
m_j(0)&=c,&m_j(\infty)&=C,\\
V_w(0)&=(w+1)c,&V_w(\infty)&=(w+1)C,\\
G(0)&=0,&G(\infty)&=0.
\end{aligned}
\tag{252.4}
$$

**定理 252.2（振荡预算下的实际最优值追踪）。** 对任一满足第244.9式任一低内部代价条件的允许准备族，以及每个固定 $w>0$，有

$$
\begin{aligned}
\liminf_{s\downarrow0}\bigl(P_s-m_2(\gamma_s)\bigr)&\ge0,\\
\liminf_{s\downarrow0}\bigl(Q_s-m_1(\gamma_s)\bigr)&\ge0,\\
\liminf_{s\downarrow0}\bigl(wP_s+Q_s-V_w(\gamma_s)\bigr)&\ge0.
\end{aligned}
\tag{252.5}
$$

每一行都分别存在全域实解析、每点秩至多二的允许准备族，将该行括号内的差达到零极限。这些族保持原任务全部精确性、联合支持四、完整尖锐集合、普通最优双侧曲率及指定有限阶节点数据。存在一个不依赖预算比值的常数 $M$，使所选各族最终都满足

$$
\sup_{K_s}I_Q\le M,
\qquad \int_{K_s}I_Q\,du\le M.
\tag{252.6}
$$

三行的达到族可不同；这不是固定任务下确界必取到的断言。

证明。 先核对基准的连续性。由于 $g\ge0$、$0<D\le1$，有 $F_j\ge c$；取 $z=0$ 给出 $F_1=F_2=C$。在有限正 $\gamma_0$ 附近，任一有界目标子水平集上的 $D$ 有一致正下界：例如 $F_j\le L$ 蕴含 $D\ge(c/L)^{1/j}$。对正权和式分别使用 $wF_2\le L$ 和 $F_1\le L$。因此极小点不能趋向极点；抽取 $z$ 的收敛子列给出值函数的下半连续性，而固定 $\gamma_0$ 的一个极小点在附近仍可行，给出上半连续性。

当 $\gamma\downarrow0$ 时，取 $z=h$，并用普遍下界 $c$，得到 $m_j\to c$、$V_w\to(w+1)c$。当 $\gamma\to\infty$ 时，可行点满足 $g(z)<1/\gamma$；$g$ 在 $[0,h]$ 只于零点为零，故任何可行点序列均有 $z\to0$，从而 $A(z)\to C$。由 $D\le1$ 得下界，取 $z=0$ 得上界，遂得（252.4）中的另一端极限。所以 $m_j,V_w,G$ 在整个紧化区间连续；$G$ 在有限正点严格为正。

若（252.5）的某行失败，取一列 $s_n\downarrow0$，使该差至多为某个固定负数。相应代价沿此列有界，因为基准有界。紧化后的 $\gamma_{s_n}$ 有收敛子列。当极限为有限正数时，使用第249节同一过零方向的联合下界；当极限为零时，使用第251节；当极限为无穷时，使用第248节。端点的两项下界可相加，有限正点则必须使用共同方向，不能只把两个分别最优值相加。结合基准的连续性，三种情形都与所选负差矛盾，证明（252.5）。

为建立达到族，先给出三个区间共用的内部界。第239节已经从第一规范支的含参实矩根和紧性得到常数 $B<\infty$，使充分小 $s$ 时

$$
\sup_{K_s}I_Q(\rho_{1,s})\le B.
\tag{252.7}
$$

这里 $K_s$ 的长度为固定的 $\ell$；其 $p$ 坐标位于远离两紧化端点的共同紧区间，嵌入共同处理器的等距映射对 $p$ 恒定。因此 $B$ 只由该规范族与 $\ell$ 决定，不依赖 $e_s,\eta_s,\zeta_s$。

第248、249、251节的三个构造，在 $K_s$ 上都保持同一第一规范背景；其纯实因子可以取常数辅助方向，故 $2\|(A_{\rm bg})'_u\|_F=\sqrt{I_Q(\rho_{1,s})}$。三个解析化都可在保留资源余量和节点数据的同时，逐任务选到

$$
\|(A_{\rm final})'_u-(A_{\rm bg})'_u\|_F\le\tfrac12
\quad\text{于 }K_s.
\tag{252.8}
$$

第251节在零虚性预算时保持因子完全实，因而这里也包含 $\eta_s=0$。净化信息上界给出
$\sqrt{I_Q(\rho_{\rm final})}\le\sqrt B+1$。
所以三种构造均可使用同一个

$$
M=(1+\ell)(\sqrt B+1)^2.
\tag{252.9}
$$

逼近次数、允许误差与开始成立的阈值仍可依赖实际任务及预算；统一的只是（252.9）的内部代价界。

对每个固定任务，令 $\mathcal A_s^M$ 为满足全部原任务条件、两项全域预算、每点秩至多二、全域实解析及（252.6）的准备集合。先允许这个集合为空。对任一目标
$H_s\in\{P_s,Q_s,wP_s+Q_s\}$，记其对应基准为
$h(\gamma)\in\{m_2(\gamma),m_1(\gamma),V_w(\gamma)\}$，并定义

$$
q_H(s)=\inf_{\rho\in\mathcal A_s^M}H_s(\rho),
\qquad \inf\varnothing=+\infty.
\tag{252.10}
$$

取任意一列 $s_n\downarrow0$，再抽取使 $\gamma_{s_n}$ 在紧化区间收敛的子列。三种实际构造均适用于这样的任务序列：有限正极限时，在第249节取限制目标的一个最优方向；两个端点则分别取第251、248节的共同达到族。它们逐任务满足同一个 $M$，并使相应 $H_{s_n}$ 收敛于该端点或内部极限的 $h$ 值。因此 $\mathcal A_{s_n}^M$ 最终非空，且

$$
\limsup_n\bigl(q_H(s_n)-h(\gamma_{s_n})\bigr)\le0.
\tag{252.11}
$$

这些构造只要求每条曲线关于输入参数解析，不要求所选任务序列之间具有正则性。

若集合在任意小的任务处为空，取空集任务序列并作同样的紧化抽取，便与刚才的最终非空性矛盾。故对全部充分小 $s$，该集合非空。若（252.11）的结论在完整振荡路径上失败，也可抽取一条正偏差序列，再按同一论证矛盾。因此其完整路径的上极限至多零。

下极限由（252.5）给出：若 $q_H(s)-h(\gamma_s)$ 在一列任务上低于某个固定负数，逐任务选取足够接近下确界的准备。这些准备都满足同一个 $M$，因而同时满足两项低内部代价条件。沿该序列应用（252.5）的证明即得矛盾。于是

$$
q_H(s)-h(\gamma_s)\longrightarrow0.
\tag{252.12}
$$

最后对每个充分小 $s$ 选取 $\rho_s\in\mathcal A_s^M$，使
$H_s(\rho_s)\le q_H(s)+s$。下确界定义保证这种近极小选择存在；无需假设固定任务的极小元存在，也无需给这些选择添加关于 $s$ 的连续性。由（252.5）和（252.12）得到对应差的零极限。证毕。

**定理 252.3（两个移动最优值可共同追踪的充要条件）。** 在（252.1）下，存在同一个允许准备族满足任一低内部代价条件，并且

$$
P_s-m_2(\gamma_s)\longrightarrow0,
\qquad Q_s-m_1(\gamma_s)\longrightarrow0,
\tag{252.13}
$$

当且仅当

$$
\frac{\gamma_s}{1+\gamma_s^2}\longrightarrow0.
\tag{252.14}
$$

条件成立时，可取定理252.2中的全域实解析秩二上界族，并保留同一内部界 $M$ 与全部原任务条件。

证明。 条件（252.14）等价于 $\gamma_s$ 最终离开 $(0,\infty)$ 中每个紧子区间。若它失败，则存在 $s_n\downarrow0$，使 $\gamma_{s_n}\to\gamma_*\in(0,\infty)$。定理252.2在 $w=1$ 时给出

$$
\liminf\left[(P_s-m_2(\gamma_s))+(Q_s-m_1(\gamma_s))-G(\gamma_s)\right]\ge0.
\tag{252.15}
$$

沿上述子列，$G(\gamma_{s_n})\to G(\gamma_*)>0$，与（252.13）矛盾。

反之，若（252.14）成立，紧化区间上的连续性与两个端点的零值给出 $G(\gamma_s)\to0$。取定理252.2在 $w=1$ 的达到族，则两个差之和为 $G(\gamma_s)+o(1)\to0$。各差的下极限均非负，故任一差的负部趋零；与和式一起推出两个差分别趋零。证毕。

**注记 252.4（共同追踪不要求一个固定极限）。** 条件（252.14）允许预算比值在趋零与趋无穷的子列之间反复切换；相应最优系数也可在 $c$ 与 $C$ 之间切换。因此共同追踪移动基准不同于两个代价具有共同最优的固定极限，也不同于分别在不同子列取得最优下极限。有限正比值中的严格间隙是共同追踪的唯一渐近障碍，而两端之间的振荡本身不增加领先系数。

本节使用顺序紧性、连续值函数和近极小选择这些既有方法，新的适用范围是保留全套实际任务约束及统一内部界的无极限预算分配。没有给出关于 $s$ 的统一解析延拓半径、显式逼近复杂度或追踪速度；尤其没有将第250节的迭代间隙展开变成同时极限的余项估计。累计 Fisher 代价仍按原参数定义，不在此识别为物理时间中的能耗。

<a id="entry-854"></a>

## 追加锚（本行以下为增补区）

<a id="section-253"></a>

## 253. 相同分项预算下的实准备损失与复相干优势

**定义 253.1（固定共轭下的完全实比较类）。** 沿用第249节的实际任务、两个分别成立的全域预算和原尾窗，设

$$
\delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,
\quad 0<e_s=o(s),\quad \eta_s=o(s),
\quad \gamma_s=\frac{\eta_s^2}{4dse_s}\longrightarrow\gamma\in[0,\infty].
\tag{253.1}
$$

使用第252.2式的无量纲代价 $P_s,Q_s$。完全实比较类额外要求 $C\rho_u C=\rho_u$ 于整个输入域成立；处理器、共轭 $C$、任务、两项预算及所计费的原尾窗都保持相同。这个条件使实际虚性恒为零，但不允许将未使用的虚性额度转移到混合预算。完全实密度仍可混合；此比较不把实量子态等同于经典随机模型。

**定理 253.2（完全实类的共同最优系数）。** 若 $0\le\gamma<1$，任一完全实且满足第244.9式任一低内部代价条件的允许准备族都满足

$$
\liminf P_s\ge\frac{c}{(1-\gamma)^2},
\qquad
\liminf Q_s\ge\frac{c}{1-\gamma},
\qquad c=\frac{\pi^2}{4}.
\tag{253.2}
$$

同一族完全实、全域实解析、每点秩至多二的准备将这两个界同时达到为极限；其内部窗口两个代价一致有界，并保留全输入精确性、实际支持四、完整尖锐集合、普通最优双侧曲率及指定有限阶实规范节点数据。

证明。 令 $e_s^{\rm R}=\zeta_s-F_s$。精确差商给出

$$
\frac{e_s^{\rm R}}{e_s}
=\frac{2F_s+e_s-\eta_s^2/e_s}{\zeta_s+F_s}
=\frac{2F_s+e_s-4ds\gamma_s}{\zeta_s+F_s}
\longrightarrow1-\gamma.
\tag{253.3}
$$

这里用 $F_s/s\to2d$、$e_s/s\to0$、$\eta_s/s\to0$ 推出 $\zeta_s/s\to2d$；未用端点首项替代精确差值。因此当 $\gamma<1$ 时，最终 $e_s^{\rm R}>0$ 且 $e_s^{\rm R}=o(s)$。

完全实准备可视为虚性预算为零、混合预算为 $\zeta_s$ 的同一任务候选。其较短预算尾窗满足

$$
T_s(\zeta_s)\subseteq T_s(\delta_s).
\tag{253.4}
$$

第244节在 $e_s^{\rm R}$ 上的下界，结合峰值与非负积分对区间包含的单调性，以及（253.3），即给出（253.2）。这一步只给下界；不能把较短尾窗上的上界直接当成原尾窗上界。

为在原尾窗达到两个常数，推广第251节的完全实等待构造。仍令
$v_s=\sqrt{se_s}$、$\epsilon_s=e_s/s$、
$t=(p-p_{\delta_s})/\Delta_s$，选取
$\omega_s\downarrow0$ 且 $s+\sqrt{\epsilon_s}=o(\omega_s)$，并置

$$
t_{c,s}=\gamma_s+2\omega_s\longrightarrow\gamma<1.
\tag{253.5}
$$

取第251.3式的实际实因子图，保持 $\phi_y=2sr_0$，在原入口至 $t_{c,s}$ 使用

$$
a(t)=-\sqrt d\,v_s F_{\omega_s}(t_{c,s}-t).
\tag{253.6}
$$

第251.6式的精确基线差商在有界 $\gamma_s$ 和 $t$ 下仍给出

$$
\frac{f(p)^2-\zeta_s^2}{4se_s}
=d(\gamma_s-t)+O(s+\epsilon_s).
\tag{253.7}
$$

平方根包络于是保持严格混合余量，虚性精确为零。此前的负相干入口仍由第246、251节的实圆与正则实矩图在原尾窗和内部窗口之外连接。对有界 $\gamma_s$，控制 $a/v_s$ 一致有界，实际范数—实矩 Jacobian 仍有非零极限。等待因子的导数界（251.7）因此保持，其两个归一化代价为 $O(\epsilon_s/\omega_s+\epsilon_s^2)=o(1)$。

过零之后沿第251.8式同时回收实角和方向，以同一个近似常速、两端平坦的进度连接到实际第三规范支。方向变化仍为 $O(s^2)$，领先平方长度仍为 $\pi^2d^2s^2$，但这次可用参数时段为

$$
2\Delta_s(1-t_{c,s})
=2dse_s(1-\gamma+o(1)).
\tag{253.8}
$$

第249.33式的实际因子信息上界给出

$$
\limsup P_s\le\frac{c}{(1-\gamma)^2},
\qquad
\limsup Q_s\le\frac{c}{1-\gamma}.
\tag{253.9}
$$

固定 $\gamma<1$ 保证剩余比例有正下界，故平坦端部、径向项、$O(s^2)$ 的方向回收及等待项均为低阶。随后使用第251节完全实的因子逼近和一个实矩梯度修正，精确保留零虚性、全部任务条件、节点数据和两个代价；所需逼近精度逐任务选择。内部背景仍为第一规范支，亦可采用第252.9式同一个内部界。上下界合并，得到同一族的两个极限。证毕。

**定理 253.3（实类的临界与超临界障碍）。** 若 $\gamma>1$，包括 $\gamma=\infty$，不存在满足第244.9式任一低内部代价条件的完全实允许准备族。若 $\gamma=1$ 且这样的完全实族存在，则最终 $e_s^{\rm R}>0$，并且

$$
P_s\longrightarrow+\infty,
\qquad Q_s\longrightarrow+\infty.
\tag{253.10}
$$

这不排除支付较高内部代价的完全实准备。

证明。 任一满足低内部代价条件的完全实族都必须最终满足 $\zeta_s>F_s$。否则取一列 $\zeta_s\le F_s$，将其视为总预算 $\zeta_s$ 的完全实任务。第243节的内部下界给出

$$
\liminf \zeta_s^4\sup_{K_s}I_Q\ge A_*>0,
\qquad
\liminf \zeta_s^2\int_{K_s}I_Q\,du\ge B_*>0.
\tag{253.11}
$$

由 $\zeta_s/s\to2d$，无论选第244.9式哪个条件，都与（253.11）矛盾。

若 $1<\gamma<\infty$，（253.3）给出 $e_s^{\rm R}<0$ 最终成立。若 $\gamma_s\to\infty$，其精确分子
$2F_s+e_s-4ds\gamma_s$
最终也为负。这两种情形都与刚才的必要条件冲突。

若 $\gamma=1$ 且低内部代价完全实族存在，则（253.3）和必要条件给出
$0<e_s^{\rm R}=o(e_s)$。在较短的 $T_s(\zeta_s)$ 应用第244节，得到

$$
\liminf (e_s^{\rm R})^2\sup_{T_s(\zeta_s)}I_Q\ge c,
\qquad
\liminf\frac{e_s^{\rm R}}{2ds}
\int_{T_s(\zeta_s)}I_Q\,du\ge c.
\tag{253.12}
$$

再使用（253.4）及 $e_s/e_s^{\rm R}\to\infty$，便得到（253.10）。因此临界比值本身不决定 $\zeta_s-F_s$ 的精确符号；符号决定低内部代价实族是否被立即排除，正余量趋于零的相对速度则迫使其原尾窗归一化代价发散。证毕。

**推论 253.4（消失虚性额度仍有严格最优值优势）。** 对任意固定 $0<\gamma<1$，在完全相同的两项预算下，允许复准备的两个分别最优系数严格小于完全实类对应系数。更具体地，令 $g_h=g(h)\in(0,1)$，则

$$
\begin{aligned}
m_2(\gamma)&\le\frac{c}{(1-\gamma g_h)^2}
<\frac{c}{(1-\gamma)^2},\\
m_1(\gamma)&\le\frac{c}{1-\gamma g_h}
<\frac{c}{1-\gamma}.
\end{aligned}
\tag{253.13}
$$

事实上，取 $z=h$ 的同一族复准备便可同时严格改善（253.2）的两个实最优系数；这不要求它同时达到两个各自的复最优值。对固定 $1\le\gamma<\infty$，复准备仍有有限的两项最优系数及有限代价的共同实现点，完全实类则受到定理253.3的障碍。

证明。 在第249节的曲线中取 $z=h$。当 $\gamma<1$ 时它可行，且 $A(h)=c$、$0<g_h<1$，立即得到（253.13）。各最优值的实际达到由第249节保证。对任意有限正 $\gamma$，$z=0$ 都可行，且
$F_2(0)=F_1(0)=c+h^2$，所以同一复准备族具有有限代价的共同实现；不把这个共同曲线点冒充两个分别最优点。定理253.3完成实类比较。证毕。

**注记 253.5（相干资源改变的是可用关系路径）。** 此处的复准备优势发生在 $\eta_s=o(s)$，因此预算允许的虚性本身趋零。完全实类不能使用这份额度，其过零必须等待混合预算单独允许的较短尾窗；复相干则通过第249节的耦合矩条件改变可行过零位置。优势是固定处理器、固定共轭和固定分项预算下的实际代价差，不是对任意实数表述或增加维数后的模拟作普遍不可能性断言。

虚性具有操作用途的既有背景可见 Wu 等，*Operational Resource Theory of Imaginarity*，Phys. Rev. Lett. **126**, 090401（2021），DOI:10.1103/PhysRevLett.126.090401，arXiv:2007.14847，关于虚性资源、态变换及局域态区分的论述。该文不提供这里的尾窗最优常数、分项预算阈值或曲率保持构造；本节的比较来自实际尾窗长度、完全实全域达到族和第249节的复矩几何。上述领先系数仍先取固定比值的任务极限，未声称在 $\gamma\uparrow1$ 时有统一余项，也未把累计 Fisher 代价识别为能耗。

<a id="entry-856"></a>

## 追加锚（本行以下为增补区）

<a id="section-254"></a>

## 254. 用额外混合预算替代复相干的精确领先补偿量

**定义 254.1（原尾窗上的混合预算补偿）。** 保持第253节的实际任务，固定有限正极限 $\gamma_s\to\gamma\in(0,\infty)$。允许将混合预算由 $\zeta_s$ 增加到 $\widetilde\zeta_s$，但要求

$$
\zeta_s\le\widetilde\zeta_s\le\delta_s=F_s+e_s,
\qquad
\frac{\widetilde\zeta_s-\zeta_s}{e_s}\longrightarrow r.
\tag{254.1}
$$

原虚性预算 $\eta_s$ 保持不变；所选准备额外要求完全实。代价 $P_s,Q_s$ 仍在原来的 $T_s(\delta_s)$ 上计量，不改用放宽后合成预算的尾窗。原任务的精确矩、固定处理器和共轭、支持、尖锐集合、曲率及节点数据也都保持。称 $r$ 为领先混合补偿量。

**定理 254.2（同时达到两项代价上限的最小补偿）。** 给定有限常数 $p\ge c$、$q\ge c$，其中 $c=\pi^2/4$。对任一满足（254.1）的预算族，存在满足任一低内部代价条件的完全实允许准备族，使

$$
\limsup P_s\le p,
\qquad \limsup Q_s\le q,
\tag{254.2}
$$

当且仅当

$$
r\ge r_{\min}(\gamma;p,q)
:=\left[\gamma-1+
\max\left\{\sqrt{\frac cp},\frac cq\right\}\right]_+.
\tag{254.3}
$$

这里 $[x]_+=\max\{x,0\}$，且 $0\le r_{\min}\le\gamma$。所需预算族可实现每个 $r\in[0,\gamma]$。条件成立时，可选择全域实解析、每点秩至多二、内部两个代价一致有界且保持全部原任务条件的同一个准备族。

证明。 由精确差商

$$
\frac{\delta_s-\zeta_s}{e_s}
=\frac{\eta_s^2}{e_s(\delta_s+\zeta_s)}
\longrightarrow\gamma,
\tag{254.4}
$$

（254.1）必有 $0\le r\le\gamma$。定义只用于分析的有效虚性额度

$$
\widehat\eta_s=\sqrt{\delta_s^2-\widetilde\zeta_s^2},
\qquad
\widehat\gamma_s=\frac{\widehat\eta_s^2}{4dse_s}.
\tag{254.5}
$$

因为 $\widetilde\zeta_s\ge\zeta_s$，有 $0\le\widehat\eta_s\le\eta_s=o(s)$。完全实准备的虚性为零，所以它同时满足这一辅助额度和原额度。其混合约束始终是实际的 $J\le\widetilde\zeta_s$。又有

$$
\gamma_s-\widehat\gamma_s
=\frac{(\widetilde\zeta_s-\zeta_s)
(\widetilde\zeta_s+\zeta_s)}{4dse_s}
\longrightarrow r,
\quad
\widehat\gamma_s\longrightarrow\gamma-r.
\tag{254.6}
$$

这里 $\widetilde\zeta_s/s\to2d$，由两侧 $\zeta_s\le\widetilde\zeta_s\le\delta_s$ 夹逼得到。辅助两项预算的合成值精确为原 $\delta_s$，故应用第253节不会改变计费尾窗。

若 $\gamma-r<1$，第253节给出完全实类的共同最优系数

$$
P_{\rm R}=\frac{c}{(1-\gamma+r)^2},
\qquad Q_{\rm R}=\frac{c}{1-\gamma+r}.
\tag{254.7}
$$

若 $\gamma-r=1$，低内部代价实族即使存在，两项原尾窗归一化代价也都发散；若 $\gamma-r>1$，这样的实族不存在。因为 $p,q$ 有限，条件（254.2）因此等价于

$$
1-\gamma+r\ge
\max\left\{\sqrt{c/p},c/q\right\}>0.
\tag{254.8}
$$

结合 $r\ge0$ 即得（254.3）。由于 $p,q\ge c$，右侧的最大值至多一，故 $r_{\min}\le\gamma$。充分性使用第253节在（254.7）的同一族共同达到，保留全部任务条件；必要性使用其任意秩下界和临界障碍，而非假设固定任务最小元存在。

最后验证补偿量不是仅有形式的变量。对任意固定 $r\in[0,\gamma]$，定义

$$
\widehat\eta_s^2=4dse_s\max\{\gamma_s-r,0\},
\qquad
\widetilde\zeta_s=\sqrt{\delta_s^2-\widehat\eta_s^2}.
\tag{254.9}
$$

有 $0\le\widehat\eta_s^2\le\eta_s^2\le\delta_s^2$，所以根式合法且满足（254.1）的逐点顺序。又由

$$
\frac{\widetilde\zeta_s-\zeta_s}{e_s}
=\frac{4ds\min\{\gamma_s,r\}}
{\widetilde\zeta_s+\zeta_s}
\longrightarrow r,
\tag{254.10}
$$

实现了指定补偿量，包括 $r=\gamma$。证毕。

**定理 254.3（两个复最优值所需的实补偿及其严格凸性）。** 若把两项上限分别取为原复允许类的独立最优值
$p=m_2(\gamma)$、$q=m_1(\gamma)$，则最小补偿为

$$
R(\gamma)=\gamma-1+\sqrt{\frac{c}{m_2(\gamma)}},
\qquad 0<R(\gamma)<\gamma.
\tag{254.11}
$$

达到这个补偿后，存在同一个完全实允许准备族满足

$$
P_s\longrightarrow m_2(\gamma),
\qquad
Q_s\longrightarrow\sqrt{c\,m_2(\gamma)}<m_1(\gamma).
\tag{254.12}
$$

函数 $R$ 在 $(0,\infty)$ 上光滑、严格递增且严格凸。以第250节的峰值最优方向 $z_2(\gamma)$ 表示，其导数为

$$
R'(\gamma)
=1-\sqrt{\frac{c}{A(z_2(\gamma))}}\,g(z_2(\gamma)),
\qquad
1-g(h)<R'(\gamma)<1.
\tag{254.13}
$$

在先取固定比值任务极限后的参数极限中，

$$
\begin{aligned}
R(\gamma)&=(1-g(h))\gamma+O(\gamma^2)
&& (\gamma\downarrow0),\\
R(\gamma)&=\gamma-1+\sqrt{c/C}+O(\gamma^{-1})
&& (\gamma\to\infty),
\qquad C=c+h^2.
\end{aligned}
\tag{254.14}
$$

证明。 设 $z_1$ 为累计代价的唯一极小方向。由第250节 $0<z_1<h$，所以 $A(z_1)>c$。精确地，

$$
m_1(\gamma)^2
=A(z_1)F_2(z_1;\gamma)
>c\,m_2(\gamma).
\tag{254.15}
$$

因此（254.3）中的两项要求满足
$c/m_1<\sqrt{c/m_2}$，峰值上限决定最小补偿。有限正 $\gamma$ 下有 $m_2>c$：$A\ge c$、$D\le1$，等号若成立必须同时有 $z=h$ 和 $D=1$，与 $g(h)>0$ 矛盾；极小值确实取到，故严格大于 $c$。这证明（254.11）的上界。

若 $\gamma\ge1$，（254.11）的表达式显然为正。若 $0<\gamma<1$，第253.13式给出
$m_2<c/(1-\gamma)^2$，所以
$\sqrt{c/m_2}>1-\gamma$，同样为正。因此无需取正部。将（254.11）代入（254.7）就得到（254.12），严格积分改进来自（254.15）。它使用增加后的混合预算，不与原预算下第249节禁止共同达到两项独立最优值的结论冲突。

唯一驻点方程和第250节的 $H_2'>0$ 给出 $z_2(\gamma)$ 光滑且严格递减。对
$m_2=A(z_2)/D(z_2)^2$
求导，驻点使方向导数项消失，于是

$$
m_2'(\gamma)
=\frac{2A(z_2)g(z_2)}{D(z_2)^3}.
\tag{254.16}
$$

再对（254.11）求导，便得到（254.13）。因为 $0<z_2<h$、$A(z_2)>c$，且 $g$ 在正区间严格递增，有
$0<\sqrt{c/A(z_2)}g(z_2)<g(h)<1$，故导数界严格成立。

令 $f(z)=\sqrt c\,g(z)/\sqrt{A(z)}$。在 $0<z<h$，

$$
f'(z)=\sqrt c\left(
\frac{g'(z)}{\sqrt{A(z)}}
+\frac{g(z)(h-z)}{A(z)^{3/2}}\right)>0.
\tag{254.17}
$$

由 $R'=1-f(z_2)$、$z_2'<0$，得 $R''=-f'(z_2)z_2'>0$。最后用第250节
$m_2=c+2cg(h)\gamma+O(\gamma^2)$
和 $m_2=C+O(\gamma^{-1})$，展开（254.11）即得（254.14）。证毕。

**注记 254.4（替代的是两项任务代价约束）。** 补偿量衡量完全实准备为满足给定的两项渐近代价上限所需的最小额外混合额度。它不是逐点把任意复准备转成实准备的转换定理，也不要求保留原复曲线的所有读数。原任务的精确矩及节点结构被保留，优化对象是整个准备族的两个尾窗代价。

对两项原复独立最优上限，峰值要求独自决定最小补偿；达到它后，同一实族的累计代价还严格低于对应上限。此结论来自放宽后的可行关系集合，不把不同预算下的结果说成原可行集合里的共同最优。完全实条件始终相对于固定共轭，未等同于经典性，也未将 Fisher 积分解释为物理能耗。式（254.14）仍是先取固定比值任务极限的参数展开，不提供同时极限的统一误差。

<a id="entry-858"></a>

## 追加锚（本行以下为增补区）
<a id="section-255"></a>

## 255. 精确任务纤维内的代价注入与完整联合可达区域

**定义 255.1（原尾窗上的联合极限）。** 固定 $\gamma\in(0,\infty)$，沿用第249节的实际任务、处理器、共轭及两个分别成立的全域预算，令

$$
\delta_s=\sqrt{\eta_s^2+\zeta_s^2}=F_s+e_s,
\qquad 0<e_s=o(s),\qquad
\frac{\eta_s^2}{4dse_s}\longrightarrow\gamma.
\tag{255.1}
$$

令 $c=\pi^2/4$，并沿用

$$
A(z)=c+(h-z)^2,\quad
g(z)=1+\frac{z^2-\sqrt{z^4+4}}2,\quad
D_\gamma(z)=1-\gamma g(z),\quad
\mathcal Z_\gamma=\{z\in[0,h]:D_\gamma(z)>0\}.
\tag{255.2}
$$

两项代价仍在原尾窗 $T_s(\delta_s)$ 上计算：

$$
P_s=e_s^2\sup_{T_s(\delta_s)}I_Q,\qquad
Q_s=\frac{e_s}{2ds}\int_{T_s(\delta_s)}I_Q\,du.
\tag{255.3}
$$

对满足第244.9式任一低内部代价条件的允许准备族，考察 $(P_s,Q_s)$ 的有限共同极限及有限共同聚点。这里同一个 $s$ 的两项读数必须来自同一个准备；不将不同族的两个分别最优值拼成一个实现。

**定理 255.2（完整的有限联合代价区域）。** 对每条满足（255.1）的实际预算路径，有限共同极限的全体恰为

$$
\boxed{
\mathcal C_\gamma=
\left\{(P,Q):\ 0\le Q\le P<\infty,\quad
\exists z\in\mathcal Z_\gamma:\quad
P\ge\frac{A(z)}{D_\gamma(z)^2},\quad
Q\ge\frac{A(z)}{D_\gamma(z)}\right\}.
}
\tag{255.4}
$$

有限共同聚点的全体也是这个集合。必要性允许任意点态秩；每个点的充分性都可由全域实解析、每点秩至多二的同一准备族实现，保持全输入精确性、实际联合支持四、完整尖锐集合、普通最优双侧曲率、任意指定的有限阶实规范节点数据及两项一致有界的内部代价。不要求族关于 $s$ 连续，不声称每个固定任务存在极小元。

证明。 先记

$$
\Delta_s=h_3(s)-p_{\delta_s},\qquad
\kappa_s=\frac{\Delta_s}{dse_s}\longrightarrow1,
\qquad
t=\frac{p-p_{\delta_s}}{\Delta_s}\in[0,1].
\tag{255.5}
$$

因 $u=2p-1$，原尾窗长度为 $2\Delta_s$。置 $i_s(t)=e_s^2I_Q(u(t))$，则精确地有

$$
P_s=\sup_{[0,1]}i_s,\qquad
Q_s=\kappa_s\int_0^1i_s(t)\,dt,\qquad
Q_s\le\kappa_s P_s.
\tag{255.6}
$$

故任何有限共同聚点满足 $Q\le P$。沿得到该聚点的子列，第249.19—249.21式的共同过零方向论证给出某个 $z\in\mathcal Z_\gamma$，使（255.4）中的两个下界同时成立。代价有界保证剩余尾窗比例有正下界，因而所取方向确实可行。这证明必要性。

充分性需要在精确任务纤维内增加实际信息，而不只增加净化因子的导数。下面分步给出这个构造。

**第一步：带严格预算余量的实际背景。** 固定（255.4）的一个见证 $z$，记

$$
D=D_\gamma(z),\qquad p_0=A(z)/D^2,\qquad q_0=A(z)/D.
\tag{255.7}
$$

取第249节解析化之前的光滑因子背景 $\mathsf A_s^0$，令 $\rho_s^0=\mathsf A_s^0(\mathsf A_s^0)^\dagger$，以及

$$
i_s^0=e_s^2I_Q(\rho_s^0),\qquad
\bar i_s^0=4e_s^2\|(\mathsf A_s^0)'_u\|_F^2.
\tag{255.8}
$$

它保持全部精确矩和两项严格资源余量，并满足

$$
i_s^0\le\bar i_s^0,\qquad
\sup\bar i_s^0\le p_0+o(1),\qquad
\sup i_s^0\to p_0,\qquad
\kappa_s\int_0^1i_s^0\,dt\to q_0.
\tag{255.9}
$$

这些也是光滑背景本身的实际 SLD 结论。实主段的精确信息由第246.14式给出：

$$
I_Q=\frac1{4p(1-p)}+p(1-p)\theta_p^2+p\|\phi_p\|^2.
\tag{255.10}
$$

它与第249.33式因子上界只差 $(1-p)^2\theta_p^2$，其归一化峰值为 $O(s^2)$。近似常速主运动给出（255.9）的两个极限；等待和清理段的归一化贡献趋零。这里不使用 SLD 在秩变化处连续的断言。

可以选紧集 $E_s\subset(0,1)$，每个是有限个闭区间之并，使

$$
|[0,1]\setminus E_s|\longrightarrow0.
\tag{255.11}
$$

其上背景秩恰为二，并具有下面的二维精确矩图。所排除的是趋零比例的清理段、纯态平坦端部及任意窄的连接领圈；若等待段占据正的极限比例，它必须保留在 $E_s$ 中。

**第二步：等待段与实主段都具有两个物理纤维方向。** 在第249.22—249.24式的复等待图中，让 $a$ 与 $y=\phi_y$ 自由，固定当前 $p,\kappa,\ell$；其余两个 $\phi$ 分量、$w,m$ 由原精确方程求解。为避免与代价 $Q_s$ 混淆，此处记矩阵 $\mathcal Q_s=(B_s+B_s^{\mathsf T})/2$。所解方程为

$$
\begin{aligned}
\mu&=p-w,\qquad H=1-p-(a^2+\kappa^2)/\mu,\\
Y&=(e_y-y\phi)/\sqrt{1-y^2},\\
m&=-\frac{\kappa k_s^{\mathsf T}\phi+
\ell\phi^{\mathsf T}(B_s^{\mathsf T}-B_s)Y}{k_s^{\mathsf T}Y},\\
w&=\frac{\ell^2}{\mu}
+\frac{(\kappa\ell/\mu)^2+(m-a\ell/\mu)^2}{H},\\
\mu\phi^{\mathsf T}\mathcal Q_s\phi
+wY^{\mathsf T}\mathcal Q_sY+a k_s^{\mathsf T}\phi&=a_s,
\qquad \|\phi\|^2=1.
\end{aligned}
\tag{255.12}
$$

置 $v=\sqrt{se_s}$。在有界等待控制的邻域内，原缩放隐函数论证给出

$$
a,\kappa,\ell=O(v),\quad y=O(s),\quad
m=O(sv),\quad w=O(v^2),\quad H\asymp s^2,
\quad \phi=v_*+O(s),
\tag{255.13}
$$

其中 $v_*$ 为实际带符号的第三极限方向，$(v_*)_y=0$，另两分量非零；$\mu\to1$，$k_s^{\mathsf T}Y\to\sigma>0$。

需要核实控制的导数，不能只对（255.13）的零阶近似求导。令 $\mathscr S$ 为（255.12）中 $w$ 方程的残差，先消去 $m$，将 $\phi$ 暂视作独立变量。直接求导得到

$$
\mathscr S_w=1+o(1),\qquad
\mathscr S_{\phi_j}=O(v^2/s)=O(e_s),\qquad
\mathscr S_a=O(e_s+v^3/s^2)=O(v).
\tag{255.14}
$$

例如 $m_{\phi_j}=O(v)$、$m-a\ell/\mu=O(sv)$，两者乘积除以 $H\asymp s^2$ 给出 $O(e_s)$。范数—实矩对两个剩余 $\phi$ 分量的 Jacobian 趋于行向量为
$(2(v_*)_2,2(v_*)_3)$ 与 $(2(v_*)_2,-2(v_*)_3)$ 的可逆矩阵；其 $a,y$ 迫动项均为 $O(s)$，$w$ 系数有界。结合（255.14）隐式求导得到足够的界

$$
\partial_a\phi=O(s),\qquad
\partial_y\phi=e_y+O(s),\qquad
\partial_aw=O(v),\qquad \partial_yw=O(e_s).
\tag{255.15}
$$

这里仅使用 $v/s=\sqrt{e_s/s}\to0$，不添加 $e_s$ 的幂次下界。

取两个固定的实际密度读数

$$
r_1(\rho)=\operatorname{Re}\langle q,\rho v_*\rangle,
\qquad
r_2(\rho)=\operatorname{Re}\langle e_y,\rho v_*\rangle.
\tag{255.16}
$$

记 $S=\langle\phi,v_*\rangle$。由精确因子及 $\langle Y,v_*\rangle=-yS/\sqrt{1-y^2}$，有

$$
r_1=aS,\qquad r_2=(p-2w)yS,
\qquad D_{(a,y)}(r_1,r_2)=I_2+o(1).
\tag{255.17}
$$

故 $\partial_a\rho,\partial_y\rho$ 是两个独立的密度切向量，不能解释成净化规范的变化。原因子第一列有非零 $\phi$ 分量，第二列 $\phi$ 分量为零而 $q$ 分量为 $\sqrt H>0$，所以局部秩恰为二。这些性质在每个固定任务的足够小管状邻域保持，包括 $a=0$ 附近。

实主段使用不同的自由坐标 $(\theta,y)$，因子为

$$
\mathsf A=\phi(\sqrt p,0)+q(\sqrt{1-p}\cos\theta,
\sqrt{1-p}\sin\theta).
\tag{255.18}
$$

范数和实矩仍解其余方向坐标。当 $0<p<1$、$\sin\theta\ne0$ 时，其活动块行列式为 $p(1-p)\sin^2\theta>0$。若固定 $p$ 的一个纤维变分使 $d\rho=0$，非核块先给出
$p(d\phi\,\phi^{\mathsf T}+\phi\,d\phi^{\mathsf T})=0$，结合 $\phi^{\mathsf T}d\phi=0$ 推出 $d\phi=0$，从而 $dy=0$；核—非核块再给出 $\sin\theta\,d\theta=0$。所以这也是二维物理纤维图。其精确 SLD 线元为

$$
ds_{\rm SLD}^2=
\frac{dp^2}{p(1-p)}+4p(1-p)d\theta^2+4p\|d\phi\|^2,
\tag{255.19}
$$

在纤维上正定。该图不延伸到纯态角端点；在 $\theta=0$，实际 $\partial_\theta\rho$ 可以为零，不能用非纯处线元的极限替代该点的信息。

**第三步：恒秩区域中的实际信息注入。** 对恒秩密度及其切向量，SLD 二次型为

$$
G_\rho(X,X)=2\sum_{\lambda_i+\lambda_j>0}
\frac{|X_{ij}|^2}{\lambda_i+\lambda_j}.
\tag{255.20}
$$

切向量的核—核块为零，因而这个型在非零密度切向量上正定。其局部光滑性也不要求正特征值互异：恒秩支撑投影光滑，且算子

$$
\mathscr A_\rho(Z)=\rho Z+Z\rho+N_\rho ZN_\rho,
\qquad N_\rho=\Pi_{\ker\rho},
\tag{255.21}
$$

可逆；$G_\rho(X,Y)=2\operatorname{Re}\operatorname{Tr}(X\mathscr A_\rho^{-1}(Y))$。对于满列秩因子，支撑投影是
$\mathsf A(\mathsf A^\dagger\mathsf A)^{-1}\mathsf A^\dagger$。于是每个固定任务的紧秩二区域内，实际信息对曲线的 $C^1$ 扰动连续；相关常数允许随任务退化。

现在固定一个任务及一个精确纤维图 $\rho=\Phi(t,x)$，$x\in\mathbb R^2$。背景为 $x_0(t)$。在归一化度量

$$
\widehat G=\left(\frac{e_s}{2\Delta_s}\right)^2G
\tag{255.22}
$$

下，背景总速度 $\dot\rho^0$ 的平方就是 $i_s^0$。纤维有两个独立方向，所以在每个点可选单位纤维向量，正交于这个总速度。总速度包括 $p$ 随 $t$ 的被迫变化，不能只使用自由坐标的速度。

把所选向量在局部坐标中延拓并沿背景归一化，则在足够小区间上得到光滑场 $V$，满足

$$
\widehat G(V,V)=1,\qquad
|\widehat G(\dot\rho^0,V)|<\varepsilon.
\tag{255.23}
$$

紧性允许有限分割；各段之间留总长度任意小的领圈，并让扰动在那里平坦归零。这避免了假设一个全域连续的精确正交方向：当背景速度的纤维投影趋零时，其正交线可能无限旋转。有限局部选择仍适用，整个零投影区间也无需丢弃。

给定光滑平方剖面 $b=w^2\ge0$，在一个分割区间中令 $v(t)$ 为 $V$ 的纤维坐标，取满足 $0\le\chi\le1$、领圈外等于一的截断 $\chi$。选周期为一的光滑圆角三角波 $\xi$，使

$$
|\xi'|\le1,\qquad \|\xi\|_\infty\le C,
\qquad \int_0^1|\xi'(r)|^2\,dr\ge1-\varepsilon.
\tag{255.24}
$$

可令其导数除任意小的圆角区外等于 $\pm1$。在已经求解的精确纤维坐标内作扰动

$$
x_\alpha(t)=x_0(t)+\alpha\chi(t)w(t)v(t)
\xi\!\left(\frac{t-t_0}{\alpha}\right).
\tag{255.25}
$$

它的振幅趋零，主要新增速度为 $\chi wV\xi'$，其余速度误差对固定任务一致趋零。由实际度量的光滑性，

$$
i_\alpha=i_s^0+\chi^2b\,\xi'^2
+2\chi w\xi'\widehat G(\dot\rho^0,V)+o(1).
\tag{255.26}
$$

因此峰值不超过 $\sup(i_s^0+b)+o(1)+O(\varepsilon\|w\|_\infty)$。具体地，记 $m_\xi=\int_0^1|\xi'|^2$，在每个分割区间 $J$ 有

$$
\begin{aligned}
\left|\int_J(i_\alpha-i_s^0)\,dt-\int_Jb\,dt\right|
\le{}&\int_J(1-\chi^2)b\,dt
+(1-m_\xi)\int_J\chi^2b\,dt\\
&+2\varepsilon\int_J|\chi w|\,dt+o_\alpha(1).
\end{aligned}
$$

对有限分割求和后，先把领圈损失、圆角损失和近似正交误差分别压到指定容差，最后取足够小 $\alpha$。仅减小周期不能消去固定的领圈或圆角损失。由两个资源函数的连续性，先选图内管径，使资源变化分别小于各自严格余量，再令振幅位于该管径内。所有矩始终精确。

还可在指定内点精确实现所需的峰值。让该段向量在该点精确正交，选波形相位使 $\xi(0)=0,\xi'(0)=1$，并令截断在那里等于一。则该点的密度不变，新增速度恰为 $wV$，其信息恰为 $i_s^0+b$。本步骤控制的是实际 SLD；三角波的平均平方斜率趋于一，因此没有正弦波附带的二分之一损失。有限任务的硬峰值上限若要严格成立，须另留误差余量；这里要求的是极限上限。

**第四步：为每个目标配出峰值与积分。** 给定（255.4）中的 $(P,Q)$ 及见证 $z$，有 $P\ge p_0$、$q_0\le Q\le P$。因为 $D\le1$，$p_0\ge q_0$。若 $P=q_0$，则 $P=Q=p_0=q_0$，原背景族即够。其余情形置

$$
\lambda=\frac{Q-q_0}{P-q_0}\in[0,1],\qquad
H_s=\max\{P,\sup\bar i_s^0\}+\varepsilon_s\longrightarrow P,
\quad \varepsilon_s\downarrow0.
\tag{255.27}
$$

在 $E_s$ 上选一个光滑峰包 $0\le\psi_s\le1$，其支撑紧含于 $\operatorname{int}E_s$，于某内点 $t_s^*$ 等于一，支撑的相对长度趋零。令

$$
b_s(t)=\bigl[\lambda+(1-\lambda)\psi_s(t)^2\bigr]
\bigl(H_s-i_s^0(t)\bigr).
\tag{255.28}
$$

于是 $0\le b_s\le H_s-i_s^0$，且 $b_s(t_s^*)=H_s-i_s^0(t_s^*)$。因为 $H_s-i_s^0>0$，它有所需光滑平方表示：$\lambda>0$ 时直接取正平方根；$\lambda=0$ 时取 $w_s=\psi_s\sqrt{H_s-i_s^0}$。

在 $E_s$ 的各个紧区间使用第三步，并将分割领圈的总长度选到趋零，保留 $t_s^*$。在 $E_s$ 外不作扰动。背景与剖面的一致峰值界、指定点的信息值给出

$$
\sup\widetilde i_s\longrightarrow P.
\tag{255.29}
$$

由（255.9）、（255.11）和背景因子上界，

$$
\kappa_s\int_{E_s}i_s^0\,dt\to q_0,\qquad
\kappa_s\int_{E_s}b_s\,dt\to\lambda(P-q_0).
\tag{255.30}
$$

峰包支撑与各领圈的积分贡献趋零，故最终光滑准备满足

$$
\kappa_s\int_0^1\widetilde i_s\,dt
\longrightarrow q_0+\lambda(P-q_0)=Q.
\tag{255.31}
$$

这同时覆盖两个端面。若 $Q=q_0<P$，只需在趋零宽度内制造峰值；若 $Q=P$，取 $\lambda=1$，在占比趋于一的区域填满信息余量，包括占正比例的等待段。这里没有把等待段误作免费而不可改变的固定间隔。

**第五步：保持实际代价的全域解析化。** 改后的光滑因子在 $K_s$、规范节点、紧化端点和图连接处邻域等于原背景，保有严格全域资源余量。其秩二部分的两个实矩微分由第249.35—249.38式的实际单重谱论证保证独立；纯段与紧化端点保留原有正则性。因而在

$$
\mathsf A_q=x\xi,\qquad
\mathsf A_{q^\perp}=\sqrt p\,W,\qquad
\|\xi\|=\|W\|_F=1
\tag{255.32}
$$

的归一化坐标中，仍能逐任务分别对因子的实、虚分量作实多项式逼近，再作有限 Hermite 匹配、两个球面归一化及解析二矩修正；因子本身仍允许为复数。

解析化的代价控制须分开两处。在紧集 $E_s$ 上，改后因子的最小奇异值有逐任务正下界。选足够细的 $C^1$ 逼近，使最终秩仍为二，并由（255.20）—（255.21）保证

$$
\sup_{E_s}\left|e_s^2I_Q^{\rm final}-\widetilde i_s\right|
\le\varepsilon_s.
\tag{255.33}
$$

这同时保住新增积分和指定点的峰值下界。在 $E_s$ 外，光滑因子仍是原背景；再把完整节点区间上的因子导数误差控制在 $1/2$ 内，便有

$$
\sqrt{e_s^2I_Q^{\rm final}}
\le\sqrt{\bar i_s^0}+e_s
\le\sqrt{H_s}+e_s.
\tag{255.34}
$$

故排除区域不会产生过大的峰值，其归一化积分由（255.11）趋零。由（255.29）—（255.34），最终解析准备实际满足 $P_s\to P$、$Q_s\to Q$。

逼近的零阶容差同时保持两项分别成立的预算。因子结构保持正性、迹、读出及秩上界，二矩修正保持完整复矩和全输入精确性。节点处至少四阶、并覆盖所有指定更高阶的 Hermite 匹配，结合规范纯段的常辅助方向、因子上界及普适下曲率界，保留普通最优双侧曲率。两个原节点和谱必要性保持完整尖锐集合与实际联合支持恰为四。在 $K_s$ 上，背景始终是第一规范支，同一因子导数误差界保持两项一致有界的内部代价。

所有振幅、频率、图管径和解析逼近精度都在固定任务之后选择；不要求统一解析半径、频率上限或关于 $s$ 的正则性。充分性成立。每个点既然已作为完整极限实现，而任何有限聚点又满足必要条件，聚点区域亦为（255.4）。证毕。

**注记 255.3（边界读数固定，内部速度仍有自由）。** 第250节确定最优代价边界，本节进一步确定整个有限可达区域。任务矩和资源预算约束每个输入位置允许出现什么密度；纤维内的小振幅快速往返还可以改变这些密度如何随输入移动。其幅度可以任意小，信息代价却可保有有限的归一化增量。另一方面，尾窗的有限长度始终强制 $Q\le P$，所以不能把最优曲线之上的整个二维上闭包都当成可达区域。

SLD 谱式、净化几何及恒秩限制沿用 Dittmann—Uhlmann（1999）和 Zhong 等（2013）的既有工具及第246、249节的来源范围。快速往返与松弛方法的既有背景，可参见 Ingalls、Sontag、Wang，*A Relaxation Theorem for Differential Inclusions with Applications to Stability Properties*，arXiv:math/0206251，特别是引理2.4与定理3.1；后者的无限区间结论允许初值扰动，不能直接提供本任务的固定节点、有限阶数据或信息峰值保证。本节的纤维振荡、原尾窗剖面及保持代价的解析化均由上面的实际构造证明，没有从该文移入这些额外结论。以上为纯理论文本，未声称 Lean 认证、穷尽文献后的优先权、统一频率复杂度或物理能耗解释。

<a id="entry-860"></a>

## 追加锚（本行以下为增补区）
<a id="section-256"></a>

## 256. 有限精确读数无法封住隐藏的信息代价

**定义 256.1（固定参考与有限采样档案）。** 固定第255节中的预算路径、有限正比值 $\gamma$、可行方向 $z$，以及原任务所要求的有限阶规范节点数据。记

$$
p_0=\frac{A(z)}{D_\gamma(z)^2},\qquad
q_0=\frac{A(z)}{D_\gamma(z)}.
\tag{256.1}
$$

每个任务的输入域为 $J_{a_s}=(2a_s-1,1)$。有限采样档案给定有限集合 $\mathcal F_s\subset J_{a_s}$，以及每个 $u\in\mathcal F_s$ 的非负整数 $N_s(u)$，并读取完整密度矩阵及其关于 $u$ 的导数直到该阶。采样点数、位置和阶数都允许随 $s$ 任意变化，但每个任务中必须有限。

这些读数强于只读取原处理器的输出；后者已由全输入精确性固定。下文仍不施加统一频率、导数阶界、逼近次数或解析延拓半径。

**定理 256.2（同一参考的任意有限数据保持）。** 存在一族全域实解析的允许参考准备 $\rho_s^{\rm ref}$，具有每点秩至多二和一致有界的内部代价，且

$$
P_s(\rho_s^{\rm ref})\longrightarrow p_0,
\qquad Q_s(\rho_s^{\rm ref})\longrightarrow q_0.
\tag{256.2}
$$

参考族可在以下所有数据之前选定。对任意有限采样档案、任意正容差 $\tau_s>0$，以及任意有限目标

$$
P\ge p_0,\qquad q_0\le Q\le P,
\tag{256.3}
$$

存在另一允许准备族 $\rho_s$，保持全部原任务条件及一致有界的内部代价，并同时满足

$$
\sup_{u\in J_{a_s}}
\|\rho_s(u)-\rho_s^{\rm ref}(u)\|_1<\tau_s,
\tag{256.4}
$$

$$
\partial_u^k\rho_s(u)=\partial_u^k\rho_s^{\rm ref}(u)
\quad
(u\in\mathcal F_s,\ 0\le k\le N_s(u)),
\tag{256.5}
$$

以及

$$
P_s(\rho_s)\longrightarrow P,\qquad
Q_s(\rho_s)\longrightarrow Q.
\tag{256.6}
$$

所有曲线仍每点秩至多二、全域实解析，保持分别成立的两项预算、共同处理器及共轭、全输入精确性、实际联合支持四、完整尖锐集合和普通最优双侧曲率。式（256.5）在规范节点读取的是预先选定参考曲线的有限数据；没有要求同一参考曲线在一个节点匹配规范支的所有阶。

证明。 首先构造不依赖采样的解析参考，并核实它附近仍有可用的物理纤维。取第255节第一步的光滑因子背景及紧秩二集合 $E_s$，满足 $|[0,1]\setminus E_s|\to0$。为给后续微小扰动留空间，必要时先把每个紧区间放进稍大的同图紧区间；所加领圈的总长度仍可趋零。

在固定 $p\in(0,1)$ 处，因子的两行归一化约束定义实流形

$$
\mathcal N_p=
\{\mathsf A\in\mathbb C^{4\times2}:\ \|\mathsf A_q\|^2=1-p,
\ \|\mathsf A_{q^\perp}\|_F^2=p\}.
\tag{256.7}
$$

它同胚于相应半径的 $S^3\times S^{11}$，实维数为十四。令 $F_p$ 是两个实际实矩残差。第249.35—249.37式已证明实际 Hermitian 矩阵束具有单重谱；若两个矩微分在秩二因子上相关，Lagrange 乘子会迫使其两列落在同一个一维特征空间，矛盾。因此 $D F_p$ 在每个秩二因子上满行秩，精确因子纤维的实维数为十二。

再看密度映射 $\pi(\mathsf A)=\mathsf A\mathsf A^\dagger$。对满列秩因子，其微分的核恰为

$$
\ker D\pi_{\mathsf A}
=\{\mathsf A\Omega:\ \Omega^\dagger=-\Omega\},
\qquad
\dim_{\mathbb R}\mathcal F_{\rm density}=14-2-4=8.
\tag{256.8}
$$

确实，若 $U\mathsf A^\dagger+\mathsf AU^\dagger=0$，向 $\operatorname{ran}\mathsf A$ 的正交补投影便知 $U=\mathsf AC$，再由满列秩知 $C+C^\dagger=0$。这些四维的酉规范方向保持全部密度约束，故也位于因子纤维的切空间中；商去它们后，局部实际密度纤维有八个实切向维度。在严格预算余量内，不等式约束保留一个开邻域。

因而任一秩二参考准备附近都有至少两个独立的物理纤维方向。含参下沉映射定理给出完整纤维的局部坐标；选择前两个坐标方向的密度像独立，并固定其余自由坐标，便得到随 $p$ 光滑、以参考因子为中心的二维局部切片。这不要求任意事先选择的二维切向分布可积，也不要求解析化之后仍逐字落在原显式等待或主段坐标中。秩二和矩正则性在每个固定任务的紧因子管状邻域保持。

现在按第255节第五步完成背景的解析化，预先把误差选到保持 $E_s$ 上的秩二管状邻域、严格资源余量、全域矩正则性及两个代价极限。在 $E_s$ 上控制实际 SLD 的 $C^1$ 误差；其余区域用因子上界。还可令完整节点区间上的因子导数误差不超过 $1/4$。所得解析因子记为 $\mathsf A_s^{\rm ref}$。它的两个实际代价满足（256.2），并具有

$$
\sup_{[0,1]}4e_s^2\|(\mathsf A_s^{\rm ref})'_u\|_F^2
\le p_0+o(1).
\tag{256.9}
$$

参考的所有选择均已完成，尚未使用 $\mathcal F_s,N_s,\tau_s,P,Q$。

现在给定这些数据。把采样点映射到尾窗坐标 $t$。从 $E_s$ 中删去这些点的开邻域，以及有限图分割的连接领圈，使删除的总相对长度小于任意预定的 $\varepsilon_s\downarrow0$。点数虽可很大，但在每个固定任务中有限，所以可逐点分配例如 $\varepsilon_s/(2\max(1,\#\mathcal F_s))$ 的长度预算。留下有限个紧区间之并 $E_s'$，满足

$$
|[0,1]\setminus E_s'|\longrightarrow0.
\tag{256.10}
$$

参考在 $E_s'$ 上仍具有二维精确矩图。用参考的实际信息 $i_s^{\rm ref}$ 代替第255节的 $i_s^0$，并用（256.9）的因子上界选择 $H_s\to P$。第255.27—255.31式的剖面构造原样适用。指定峰点取在 $E_s'$ 的内点，因而不是采样点。局部振荡全部支撑于这些区间内部；等待段若占正比例，仍只损失趋零的相对长度。因此 $Q=P$ 的填满构造和 $Q=q_0<P$ 的窄峰构造都保留。

振幅可在固定任务后任意缩小，不改变它的领先速度。选到新光滑因子与参考因子的全域 Frobenius 距离小于 $\tau_s/8$，同时保留两个预算的严格余量与图条件。光滑曲线在每个采样点的一个真邻域内等于参考，所以在那里具有完全相同的所有有限阶因子数据。它也在 $K_s$、紧化端点及原节点邻域等于参考。

最后再作一次解析化。对归一化因子坐标的实部和虚部分别作多项式逼近，并在有限集合 $\mathcal F_s$ 及原规范节点同时施加 Hermite 条件。每个输入采样点都位于开域内部，故 $x=\sqrt{(1-u)/2}$ 与 $u$ 的局部坐标变换可逆；在 $x$ 中匹配足够阶数即保持所需 $u$ 导数。取阶数至少为每点的 $N_s(u)$，并保留原曲率所需至少四阶以及预定规范数据。有限点间距可任意小，条件数可以很大。具体可先在足够高的 $C^m$ 范数中作多项式逼近，再用有限 Hermite 基多项式修正各点的有限阶误差。固定档案下，这个有限维修正算子的范数有限；把初始误差相应缩小，便能兼得任意精度和精确插值。还可在指定的未采样峰点匹配振荡后因子的一阶数据，使该点的实际信息精确保留。这里不要求任务间统一次数或精度。

两球面归一化保持这些有限数据，因为待逼近因子在各采样点已经满足归一化。其后作两个矩的解析修正。每个插值点（包括可选的未采样峰点）的矩残差及所需导数为零，修正参数的零值由局部唯一性确定；逐阶微分隐函数方程，其首阶及后续阶的齐次线性方程都具有同一个可逆参数 Jacobian。因此修正参数在这些点的所需各阶导数仍为零，最终因子保留参考的全部所要求数据，遂得到（256.5）。这一步保持的是有限阶数据，不使用解析函数的局部支撑。

将这次全域因子逼近误差取到小于 $\tau_s/8$。因归一化因子 $A,B$ 满足

$$
\|AA^\dagger-BB^\dagger\|_1
\le(\|A\|_F+\|B\|_F)\|A-B\|_F
=2\|A-B\|_F,
\tag{256.11}
$$

结合振荡振幅界便得（256.4），且有严格余量。再将 $E_s'$ 上的因子 $C^1$ 误差取到保证实际归一化 SLD 误差趋零，并在其余节点区间令因子导数误差不超过 $1/4$。前者保持注入的峰值和积分；后者与（256.9）保持排除区域的峰值上界，其积分因（256.10）趋零。于是（256.6）成立。

同一次误差选择保持全域预算、矩正则性及全部原任务条件。$K_s$ 上两次解析化的总因子导数误差不超过 $1/2$，所以相对于原第一规范背景，信息平方根增加至多一；与第252节相同的统一内部界仍可使用。各项容差在固定任务后取最小值即可，无需给 $\tau_s$ 或采样间距增加下界。证毕。

**命题 256.3（固定任务也无有限的隐藏代价上界）。** 对定理256.2选定的任一充分小固定任务、任意有限采样档案及任意 $\tau>0$，满足（256.4）—（256.5）和全部原条件的准备，其原尾窗峰值与累计 Fisher 代价都没有有限共同上界。两者可以由同一准备同时超过任意指定的两个有限阈值，同时保留同一统一内部界。

证明。 固定任务后，选一个不含采样点的非空紧子区间 $J\subset\operatorname{int}E_s$，再取非零的光滑函数 $w$ 紧支撑于其内。在参考的精确纤维图中使用第255节第三步，以新增剖面 $L^2w^2$ 作振荡。先取有限的 $L$ 任意大，再选近似正交误差、领圈和圆角损失足够小，最后取周期小到同时满足全域 $C^0$ 容差及严格预算。于是实际新增积分至少为 $L^2\int_Jw^2/2$，指定内点的信息可至少为 $L^2\max_Jw^2/2$；常数归一化在固定任务中均为严格正的有限数。

同前证明，解析化匹配所有采样数据，并把 $J$ 上实际信息的误差控制到小于一，把 $K_s$ 的因子导数误差控制在固定界内。让 $L$ 足够大即可超过两个阈值。这里只对每个有限 $L$ 构造一条曲线，不需要先交换 $L\to\infty$ 和任务极限。证毕。

**推论 256.4（有限自适应精确查询不能认证统一上界）。** 设一个确定性查询程序可在输入域内自适应选择位置，每次取得该处完整密度及任意有限阶导数，并在参考准备上经过有限次查询停止。若它只使用这些读数和原允许类的条件，则不能据此返回一个对所有与该档案相容的准备都有效的有限尾窗峰值上界，或有限累计代价上界。

证明。 在参考上运行后，所查询位置与最高阶数形成一个有限档案。命题256.3给出同一档案下超过任意候选上界的另一准备。由于每步答复相同，归纳可知查询程序在这条准备上的所有后续查询和最终答复也相同，故所报有限上界不能对整个相容类有效。该结论允许程序不返回有限上界，也不排除附加正则性先验后的认证。证毕。

**命题 256.5（有限份实际实验的稳定不可区分性）。** 若两条准备曲线在整个输入域满足 $\sup_u\|\rho_u-\sigma_u\|_1\le\tau$，考虑至多调用 $n$ 次准备接口的实验：每次以经典输入 $u$ 请求一份新的无记忆准备，可根据既有测量结果自适应选择输入，也可保留量子记忆、辅助系统并最终作联合测量。比较同一实验及与接口选择无关的相同初始状态；最终输出为保留测量、失败和停机标志的无条件量子—经典状态，不在成功后选择事件上重新归一化。则两种准备产生的最终输出满足

$$
\|\Omega_\rho-\Omega_\sigma\|_1\le n\tau,
\qquad
\operatorname{TV}(p_\rho,p_\sigma)\le\frac{n\tau}{2}.
\tag{256.12}
$$

证明。 在相同的前置量子—经典状态上替换一次接口，对每个经典输入分支，新增因子从 $\rho_u$ 变为 $\sigma_u$。迹范数的张量乘性给出该分支差不超过其概率权重乘 $\tau$；求和或积分后仍不超过 $\tau$。所有后续处理均为同一 CPTP 操作，其迹范数收缩性保持这个界。逐次替换 $n$ 个接口并用三角不等式，即得第一式；提前停机可通过保留停机标志并在余下轮次使用恒等操作处理。最终测量再给出第二式。该接口假定每次提供新份准备，不包含对输入标签的相干量子查询或额外的导数接口。证毕。

结合定理256.2，对任意有限查询预算 $n_s$ 都可取 $\tau_s=o(1/\max(1,n_s))$，使两种实验的最终读数分布差趋零，而两条准备的归一化 Fisher 代价分别趋于 $(p_0,q_0)$ 和任意给定的（256.3）中目标。若要求目标代价随任务无界，须逐任务使用命题256.3，不能仅从固定目标的极限定理交换量词得出。

**注记 256.6（需要补入边界的是速度控制）。** 有限节点上的完整状态及有限阶变化资料，并不能控制节点之间发生多快的微小往返。解析性保证无限精确信息的唯一延拓，却不提供统一解析半径或导数上界；有限档案因而不能替代这些约束。若要用复解析延拓给出 Cauchy 导数界，除延拓域外还须控制该域中的函数大小。这里的障碍来自允许类中实际存在的光滑物理纤维和无限制的频率，并不是只有量子系统才具有的现象，也不说明任意具体实验都无法估计 Fisher 信息。

SLD 对局部变化的度量解释可参见 Liu、Yuan、Lu、Wang，*Quantum Fisher information matrix and multiparameter estimation*，J. Phys. A: Math. Theor. **53**, 023001（2020），DOI:10.1088/1751-8121/ab5d4d，arXiv:1907.08037，第2.4.2节及式（75）—（77）。其 Bures 无穷小关系明确限制在秩不变的情形；本节继续只在紧恒秩区域使用该连续几何。有限 Hermite 插值、隐函数修正、迹距离收缩及逐次替换是既有工具；本节的实际任务保持与量词次序由上述构造承担，没有将有限差分读数等同于未受正则性控制的精确导数，也未声称 Lean 认证或穷尽文献后的原创优先权。

<a id="entry-862"></a>

## 追加锚（本行以下为增补区）

<a id="section-257"></a>

## 257. 正性与二阶导数如何恢复信息代价上界

第256节允许曲线的高阶变化任意快。本节给出一种相反的定量条件：若在目标窗口周围知道密度二阶导数的统一界，正性本身就能给出 Fisher 信息上界。这个论证允许秩变化，不需要正特征值具有统一谱隙。

**引理 257.1（有限邻域中的正函数导数界）。** 设 $f\in C^2([-r,r])$，$r>0$，$f\ge0$，且 $f''\le L$，其中 $L\ge0$。若 $f(0)=a>0$，则

$$
\frac{f'(0)^2}{a}
\le 2L+\frac{(a-Lr^2/2)_+^2}{ar^2}
\le 2L+\frac{a}{r^2}.
\tag{257.1}
$$

若 $a=0$，则 $f'(0)=0$。

证明。 零点结论由内点非负性得到。若 $a>0$，向 $f'(0)$ 的相反方向取步长 $0<h\le r$。Taylor 公式与正性给出

$$
0\le f(-h\operatorname{sgn}f'(0))
\le a-h|f'(0)|+\frac{Lh^2}{2},
\qquad
|f'(0)|\le\frac ah+\frac{Lh}{2}.
\tag{257.2}
$$

若 $L=0$，取 $h=r$ 即得更强的 $f'(0)^2/a\le a/r^2$。若 $L>0$ 且 $a\le Lr^2/2$，取 $h=\sqrt{2a/L}$，得到 $f'(0)^2/a\le2L$。其余情形取 $h=r$，有

$$
\frac{f'(0)^2}{a}
\le\frac a{r^2}+L+\frac{L^2r^2}{4a}
\le\frac a{r^2}+\frac{3L}{2}
\le\frac a{r^2}+2L.
\tag{257.3}
$$

前两个 $L>0$ 分段的精确界统一为（257.1）的第一个不等式；$L=0$ 时同式亦成立，故三种情形合并即证。这里实际只需 $f''$ 的上界，不需其绝对值上界。

**定理 257.2（允许秩变化的局部 SLD 上界）。** 设 $\rho(v)$ 是 $n$ 维空间中的 $C^2$ 密度曲线，定义在含 $[u-r,u+r]$ 的区间内，且

$$
\sup_{|v-u|\le r}\|\rho''(v)\|_{\rm op}\le L.
\tag{257.4}
$$

则其点态 SLD 信息满足

$$
\boxed{
I_Q(\rho_u)\le2nL+
\frac{(1-Lr^2/2)_+^2}{r^2}
\le2nL+\frac1{r^2}.
}
\tag{257.5}
$$

不要求 $\rho_u$ 满秩、附近秩恒定，或对非零特征值给出统一下界。

证明。 对 $\rho_u$ 核中的任意向量 $w$，函数 $v\mapsto\langle w,\rho(v)w\rangle$ 非负且在 $u$ 为零，所以其一阶导数为零。极化恒等式遂给出 $\rho'_u$ 的核—核块为零。因此存在有限 Hermitian SLD $S$，满足

$$
\rho'_u=\frac{\rho_u S+S\rho_u}{2},\qquad
I_Q(\rho_u)=\operatorname{Tr}(\rho_uS^2).
\tag{257.6}
$$

例如在 $\rho_u$ 的特征基中，对 $\lambda_i+\lambda_j>0$ 取
$S_{ij}=2(\rho'_u)_{ij}/(\lambda_i+\lambda_j)$，核—核块取零。这是逐点的有限维定义，不要求 $S$ 随 $u$ 连续。

取这个固定 $S$ 的一个正交特征基 $\{e_j\}_{j=1}^n$，特征值为 $\ell_j$。在整个邻域中保持基不变，令

$$
p_j(v)=\langle e_j,\rho(v)e_j\rangle\ge0.
\tag{257.7}
$$

它们的和恒为一，由（257.4）有 $p_j''(v)\le L$。又由 SLD 方程，

$$
p_j'(u)=\ell_j p_j(u),\qquad
I_Q(\rho_u)=\sum_{p_j(u)>0}\frac{p_j'(u)^2}{p_j(u)}.
\tag{257.8}
$$

零概率项的导数为零，不参与和式。逐项使用引理257.1，记 $a_0=Lr^2/2$；因每个正概率 $p_j\le1$，有

$$
\sum_{p_j>0}\frac{(p_j-a_0)_+^2}{p_j}
=\sum_{p_j>0}p_j\left(1-\frac{a_0}{p_j}\right)_+^2
\le(1-a_0)_+^2.
$$

再用正概率数不超过 $n$，便得到（257.5）。证明只把名义点 SLD 的特征基固定成一个实际测量，不对参数变化中的特征向量求导，也没有使用跨秩的 Bures 连续性。证毕。

有限邻域项不能无条件删除。二元仿射密度

$$
\rho(v)=\operatorname{diag}\left(
\frac{1+av/r}{2},\frac{1-av/r}{2}\right),
\qquad 0<a<1,
\tag{257.9}
$$

在 $[-r,r]$ 及稍大邻域内为正，满足 $\rho''=0$，但中心信息为 $a^2/r^2$。令 $a\uparrow1$，说明当 $L=0$ 时 $r^{-2}$ 的系数一不可降低。二阶项的系数在偶数维中也不能统一降低。令 $n=2k$、$L>0$，置 $M=kL$，定义非负偶函数

$$
v_M(t)=(\sqrt M-M|t|)_+.
\tag{257.9a}
$$

它的积分为一，Lipschitz 常数为 $M$。固定非负、偶、积分为一的光滑紧支撑函数 $\chi$，取 $\chi_\epsilon(t)=\epsilon^{-1}\chi(t/\epsilon)$ 作卷积，得到 $v_\epsilon=v_M*\chi_\epsilon$。于是 $v_\epsilon$ 光滑、偶、非负、积分为一，且 $\|v_\epsilon'\|_\infty\le M$、$v_\epsilon(0)\to\sqrt M$。令

$$
p_\epsilon(t)=\int_{-\infty}^t v_\epsilon(x)\,dx,
\qquad
\rho_\epsilon(t)=\operatorname{diag}(p_\epsilon(t),1-p_\epsilon(t))
\otimes\frac{I_k}{k}.
\tag{257.9b}
$$

这些是全实轴上的光滑密度曲线，满足 $p_\epsilon(0)=1/2$，以及

$$
\sup_t\|\rho_\epsilon''(t)\|_{\rm op}\le\frac Mk=L,
\qquad
I_Q(\rho_\epsilon(0))=4v_\epsilon(0)^2\longrightarrow4M=2nL.
$$

若将（257.5）中 $2n$ 统一换成较小系数，先取足够大 $r$、再取足够小 $\epsilon$，上述曲线便违反该界。因此在偶数维的一般密度曲线类中，两个加性项的系数分别不可降低；特别地，一般四维类的二阶项系数八不可降低。这不声称已经求出每个固定有限 $r$ 的联合最优包络，也不声称这些饱和曲线满足原项目处理器的额外矩、预算与节点约束。

**推论 257.3（已知三阶变化界下的有限数据认证）。** 设 $T$ 为目标紧区间，$I$ 为较大的紧区间，并已知每个 $u\in T$ 都满足 $[u-r,u+r]\subset I$。假设 $\rho\in C^3(I)$，且已知一个对允许类有效的数值界

$$
\sup_{v\in I}\|\rho'''(v)\|_{\rm op}\le M.
\tag{257.10}
$$

非空有限采样集 $\{v_j\}\subset I$ 的填充半径为
$h=\sup_{v\in I}\min_j|v-v_j|$。若在各点得到二阶导数估计 $H_j$，并有认证误差 $\|H_j-\rho''(v_j)\|_{\rm op}\le\varepsilon$，则

$$
L_{\rm cert}=\max_j\|H_j\|_{\rm op}+\varepsilon+Mh
\tag{257.11}
$$

是 $\sup_I\|\rho''\|_{\rm op}$ 的上界，且

$$
\sup_{u\in T}I_Q(\rho_u)\le2nL_{\rm cert}+r^{-2},
\qquad
\int_T I_Q\,du\le |T|(2nL_{\rm cert}+r^{-2}).
\tag{257.12}
$$

证明。 对任意 $v\in I$，取最近的采样点 $v_j$。微积分基本定理和（257.10）给出
$\|\rho''(v)-\rho''(v_j)\|_{\rm op}\le M|v-v_j|\le Mh$，从而得到（257.11）。逐点应用定理257.2并积分即得结论，也可直接使用（257.5）的较紧余项。这里积分按 Lebesgue 意义理解：记 $X=\rho'$、$\mathscr L_\rho(Z)=\rho Z+Z\rho$，则

$$
I_Q(\rho_u)
=\lim_{\epsilon\downarrow0}
2\operatorname{Re}\operatorname{Tr}
\left[X_u(\mathscr L_{\rho_u}+\epsilon\operatorname{Id})^{-1}(X_u)\right].
$$

核—核块为零保证这个点态极限就是 SLD 谱式；每个正则化项连续，故信息可测。上界再保证可积，无需假定跨秩连续。证毕。

这不是从解析性或有限数据自动推导一个未知的 $M$。已知的（257.10）是新增约束，排除了第256节中任意快的隐藏往返。也可用一个已知的二阶导数连续模替换 $Mh$；所需信息是窗口之间的定量变化控制。

**推论 257.4（原尾窗上的认证与强迫二阶变化）。** 回到第255节的四维任务，设 $T_s=T_s(\delta_s)$，$r_s>0$，且其扩展区间

$$
I_s=[\inf T_s-r_s,\sup T_s+r_s]\subset J_{a_s}.
\tag{257.13}
$$

令 $L_s=\sup_{v\in I_s}\|\rho_s''(v)\|_{\rm op}$。沿用 $\kappa_s=\Delta_s/(dse_s)\to1$，则每个任务满足

$$
P_s\le e_s^2(8L_s+r_s^{-2}),\qquad
Q_s\le\kappa_s e_s^2(8L_s+r_s^{-2}).
\tag{257.14}
$$

若允许族满足原低内部代价条件、固定有限 $\gamma>0$，且 $e_s/r_s\to0$，则

$$
\liminf_{s\downarrow0}e_s^2 L_s\ge\frac{m_2(\gamma)}8>0.
\tag{257.15}
$$

证明。 在定理257.2中取 $n=4$，再使用原尾窗长度 $2\Delta_s$ 及代价定义，即得（257.14）。第249、250节给出 $\liminf P_s\ge m_2(\gamma)$。由 $8e_s^2L_s\ge P_s-e_s^2/r_s^2$ 及额外假设，得到（257.15）。证毕。

上述半径条件在更窄的任务尺度中可以由实际几何验证。记第三节点的输入为 $u_{3,s}=2h_3(s)-1$，取

$$
r_s=\frac{1-u_{3,s}}2=1-h_3(s)\sim d^2s^2.
\tag{257.16}
$$

第243节的 $F_s=2\sqrt{h_3(s)(1-h_3(s))}$ 与 $F_s/s\to2d$ 给出最后的等价式。由于尾窗两端都趋于一，而输入域左端趋于 $2a_*-1<1$，充分小任务中（257.13）成立。因此 $e_s=o(s^2)$ 足以保证（257.15）。原来的 $e_s=o(s)$ 本身不保证这一更强条件，不能在整个过渡尺度上省略边界项。

对任意固定任务和固定扩展区间，若整个相容准备类具有同一个有限 $L_s$，则（257.14）提供共同有限上界。故第256.3节的无界代价族不可能同时具有这种统一二阶导数控制。这里的 $\rho''$ 是关于输入参数的密度矩阵二阶导数，与规范节点处的 Fisher 信息普通曲率及物理时间中的加速度是不同对象。

**注记 257.5（有限记录与定量续接）。** 有限状态和导数读数需要一个限制读数之间如何变化的规则，才能认证连续窗口中的代价。正性把这个规则接到了 Fisher 信息：概率不能在尚未触及零之前，以任意大的斜率下降而又保持二阶变化受限。因而恢复上界不一定要先假设所有状态满秩；足够强的局部变化控制可以直接处理零概率和秩变化点。

标量正性估计的既有来源是 Glaeser，*Racine carrée d'une fonction différentiable*，Annales de l'Institut Fourier **13**(2), 203–210（1963），DOI:10.5802/aif.146，§II 的引理I及第204页证明；作者将这个引理归于 Malgrange。该处对实轴上严格正的 $C^2$ 函数和二阶导数上界给出 $(f')^2\le2Lf$。本节保留有限邻域的边界项，并通过固定的名义 SLD 测量转为密度曲线的点态界。SLD 测量与谱式均为既有工具，有限采样认证和实际尾窗尺度由上述条件与推导承担；所证的一般偶数维系数性质不等于固定处理器约束类中的最优性，也不构成物理能耗界、Lean 认证或穷尽文献后的优先权。

<a id="entry-864"></a>

## 追加锚（本行以下为增补区）

<a id="section-258"></a>

## 258. 分开转弯的概率与二阶变化界的最优维度系数

第257节的算子范数界含有维度因子。本节改用密度二阶导数的迹范数，检验能否通过限制所有方向合计的变化量去掉这个因子。答案是否定的：在整个实轴上，最优上界仍随维度线性增长，而且对角、处处满秩、实解析的曲线已经足以逼近它。构造也补足第257节未处理的奇数维算子范数系数；本节不改判此前只在偶数维证明的结论。

**命题 258.1（迹范数控制与实轴上界）。** 设 $r>0$，且 $\rho(t)$ 是定义在包含 $[u-r,u+r]$ 的区间上的 $n$ 维 $C^2$ 密度曲线。若

$$
\sup_{|t-u|\le r}\|\rho''(t)\|_1\le L,
\qquad L\ge0,
\tag{258.1}
$$

则

$$
I_Q(\rho_u)\le nL+
\frac{(1-Lr^2/4)_+^2}{r^2}
\le nL+r^{-2}.
\tag{258.2}
$$

若曲线定义在整个实轴且（258.1）的界在实轴上一致成立，则

$$
\boxed{I_Q(\rho_u)\le nL.}
\tag{258.3}
$$

整个实轴上的算子范数界 $\sup_t\|\rho''(t)\|_{\rm op}\le\Lambda$ 同样给出 $I_Q(\rho_u)\le2n\Lambda$。

证明。 对任意迹为零的 Hermitian 矩阵 $H$，正、负谱的总量相等，各为 $\|H\|_1/2$。每个特征值的绝对值至多为这个总量，所以

$$
\|H\|_{\rm op}\le\frac{\|H\|_1}{2}.
\tag{258.4}
$$

由 $\operatorname{Tr}\rho\equiv1$，矩阵 $\rho''$ 迹为零。在定理257.2中取算子范数界 $L/2$ 即得（258.2）。实轴上的统一界允许任意 $r>0$，令 $r\to\infty$ 得到（258.3）；算子范数结论直接同理。零特征值由第257节的点态论证处理。证毕。

**引理 258.2（互不重叠的转弯区间）。** 固定 $n\ge2$、$L>0$、$B>1$，置

$$
N=n-1,\qquad
\lambda=2B,\qquad
A=\frac{B+1}{2},\qquad
c=\frac{L(B-1)}2.
\tag{258.5}
$$

定义非负偶函数

$$
\phi_B(x)=
\begin{cases}
1,& |x|\le1,\\
(B-|x|)/(B-1),&1<|x|<B,\\
0,&|x|\ge B.
\end{cases}
\tag{258.6}
$$

它满足 $\int_0^\infty\phi_B=A$，且 Lipschitz 常数为 $1/(B-1)$。任取 $R>0$，令

$$
t_i=R\lambda^{-i}\quad(0\le i<N),\qquad
S_j=\sum_{i=0}^{N-1}\lambda^{-ji}\quad(j=1,2),
\tag{258.7}
$$

并设

$$
q_i(t)=c t_i^2\left(A-\int_0^{t/t_i}\phi_B(x)\,dx\right),
\qquad
q_*(t)=1-\sum_{i=0}^{N-1}q_i(t).
\tag{258.8}
$$

若 $2cAR^2S_2\le1$，则 $\rho^{(0)}(t)=\operatorname{diag}(q_*(t),q_0(t),\ldots,q_{N-1}(t))$ 是实轴上的 $C^{1,1}$ 密度曲线，且其弱二阶导数几乎处处满足

$$
\|(\rho^{(0)})''(t)\|_1\le L,
\qquad
\|(\rho^{(0)})''(t)\|_{\rm op}\le L/2.
\tag{258.9}
$$

证明。 由（258.6）及其偶性，

$$
\begin{aligned}
0&\le q_i(t)\le2cAt_i^2,\\
q_i(0)&=cAt_i^2,\\
q_i'(t)&=-ct_i\phi_B(t/t_i),\\
q_i''(t)&=-c\phi_B'(t/t_i)\quad\text{几乎处处}.
\end{aligned}
\tag{258.10}
$$

因此 $q_*\ge0$，所有分量之和为一。导数 $q_i'$ 是 Lipschitz 函数，弱二阶导数没有额外的点质量。它的非零部分只可能位于

$$
t_i<|t|<Bt_i.
\tag{258.11}
$$

因 $t_{i+1}=t_i/(2B)$，这些区间两两不相交。几乎每个 $t$ 至多有一个 $q_i''(t)$ 非零；$q_*''$ 恰为它的相反数。故整个对角二阶导数的迹范数至多为 $2c/(B-1)=L$，算子范数至多为 $c/(B-1)=L/2$。这同时证明了两个界。证毕。

**定理 258.3（每个维度的最优系数与解析逼近）。** 对任意 $n\ge2$、$L>0$ 和 $0<\delta<1$，存在实轴上的对角密度曲线 $\rho$，其每个矩阵元都能延拓为复平面上的整函数，而且在每个有限实数参数处满秩，满足

$$
\sup_t\|\rho''(t)\|_1\le L,
\qquad
\sup_t\|\rho''(t)\|_{\rm op}\le L/2,
\qquad
\rho''(0)=0,
\tag{258.12}
$$

而

$$
I_Q(\rho_0)\ge(1-\delta)nL.
\tag{258.13}
$$

因此，在整个实轴的允许类中，迹范数上界（258.3）的系数 $n$ 是最优的。对于算子范数约束，系数 $2n$ 也在每个 $n\ge2$ 中最优，包括奇数维。这里的最优性是上确界可任意逼近，不主张某一条解析曲线恰好取到等号。

证明。 在引理258.2中选择

$$
R^2=\frac1{2cAS_2}.
\tag{258.14}
$$

于是 $\sum_iq_i(0)=1/2$，$q_*(0)=1/2$，中心处的每个概率都严格为正。这个尚未平滑的曲线在中心的 Fisher 信息为

$$
\begin{aligned}
I^{(0)}(0)
&=\sum_i\frac{c^2t_i^2}{cAt_i^2}
  +\frac{(c\sum_i t_i)^2}{1/2}\\
&=\frac cA\left(N+\frac{S_1^2}{S_2}\right)\\
&\ge\frac cA(N+1)
=nL\frac{B-1}{B+1}.
\end{aligned}
\tag{258.15}
$$

最后一步使用 $S_1^2\ge S_2$。全曲线此前只有 $C^{1,1}$ 正则性，下面把它变成所需的解析曲线，同时保留统一界。

取方差为 $\epsilon^2$ 的高斯核

$$
g_\epsilon(t)=\frac1{\sqrt{2\pi}\epsilon}
\exp\left(-\frac{t^2}{2\epsilon^2}\right),
\qquad
\rho^{(\epsilon)}(t)
=\int_{\mathbb R}g_\epsilon(t-x)\rho^{(0)}(x)\,dx.
\tag{258.16}
$$

这是对同一条完整密度曲线取凸平均，故正性、迹一及对角性都保留。每个 $q_i$ 在一条左侧半轴上严格为正，$q_*$ 在一条右侧半轴上等于一；高斯核处处正，所以卷积后的每个分量在每个有限实数 $t$ 都严格为正。对有界函数的高斯卷积能逐矩阵元延拓到整个复平面：若 $z=a+ib$，核的绝对值为实轴高斯核乘以 $\exp(b^2/(2\epsilon^2))$，在每个复紧集上有可积支配，允许对复参数微分。这给出所称的整函数延拓；正性只对实数参数主张。

有界的弱二阶导数与高斯卷积可交换。使用（258.9）、范数凸性和 $\int g_\epsilon=1$，得到（258.12）的两个统一范数界。卷积后的二阶导数连续，所以这些界在每一点成立。

由 $\phi_B$ 偶性，还有精确恒等式

$$
q_i(t)+q_i(-t)=2cAt_i^2.
\tag{258.17}
$$

偶高斯卷积保留此式。因此 $q_i^{(\epsilon)}(0)=cAt_i^2$，$q_*^{(\epsilon)}(0)=1/2$，所有二阶导数在中心为零。令 $Z$ 为标准正态变量，定义

$$
\theta_i(\epsilon)
=\mathbb E\,\phi_B(\epsilon Z/t_i).
\tag{258.18}
$$

则 $0<\theta_i\le1$，且对固定有限组 $t_i>0$，当 $\epsilon\downarrow0$ 时所有 $\theta_i\to1$。中心导数恰为

$$
(q_i^{(\epsilon)})'(0)=-ct_i\theta_i,
\qquad
(q_*^{(\epsilon)})'(0)=c\sum_i t_i\theta_i.
\tag{258.19}
$$

对任意 $0<\eta<1$，可以选一个共同的 $\epsilon>0$，使每个 $\theta_i\ge\sqrt{1-\eta}$。曲线对角且满秩，SLD 信息就是对应的经典 Fisher 信息，故

$$
\begin{aligned}
I_Q(\rho^{(\epsilon)}_0)
&=\frac cA\sum_i\theta_i^2
  +2c^2\left(\sum_i t_i\theta_i\right)^2\\
&\ge(1-\eta)\frac cA
  \left(N+\frac{S_1^2}{S_2}\right)\\
&\ge(1-\eta)nL\frac{B-1}{B+1}.
\end{aligned}
\tag{258.20}
$$

先取足够大 $B$，再取足够小 $\eta$ 和对应 $\epsilon$，就能使最后一项不小于（258.13）。命题258.1给出匹配的上界 $nL$，所以系数最优。给定算子范数预算 $\Lambda>0$ 时，令 $L=2\Lambda$，同一构造满足其预算并使信息任意逼近 $2n\Lambda$。一维密度恒等于一，其信息为零，不在这个最优性陈述中。证毕。

**命题 258.4（任意小迹范数邻域仍保留线性维度增长）。** 固定 $n\ge2$、$L>0$、$0<\tau<1$、$0<\delta<1$，以及秩一投影 $P$。存在与定理258.3同样整函数延拓、实轴上处处满秩的相互可交换密度曲线，满足（258.12），并且

$$
\sup_{t\in\mathbb R}\|\rho(t)-P\|_1<\tau,
\qquad
I_Q(\rho_0)\ge(1-\delta)(n-1)L.
\tag{258.21}
$$

证明。 取基使 $P$ 对应 $q_*$ 的方向，保留引理258.2中的 $B,c,\lambda$，改取

$$
R^2=\frac{\tau}{8cAS_2}.
\tag{258.22}
$$

由（258.10），对所有实数 $t$，

$$
\|\rho^{(0)}(t)-P\|_1
=2\sum_iq_i(t)
\le4cAR^2S_2=\tau/2<\tau.
\tag{258.23}
$$

$q_*\ge1-\tau/4$，所以它保持严格为正。高斯凸平均保留（258.23）的统一界；所有小概率分量经卷积也严格为正，整函数延拓及中心二阶导数为零的论证不变。

中心小概率仍精确等于 $cAt_i^2$。忽略 $q_*$ 对信息的非负贡献，并像（258.18）一样选择卷积尺度，得到

$$
I_Q(\rho^{(\epsilon)}_0)
\ge(1-\eta)\frac cA N
=(1-\eta)(n-1)L\frac{B-1}{B+1}.
\tag{258.24}
$$

再选择 $B,\eta$ 便得到（258.21）。任意给定 $P$ 可由固定酉变换从这个基的构造取得，所有范数与信息不变。证毕。

（258.21）给出邻域约束内的一个下界，不宣称它就是该受限类的最优值。

**注记 258.5（共享瞬时预算不能合并不同尺度的转弯）。** 固定 $L>0$ 和任意小的 $\tau>0$，（258.21）随维度增长而无界。因此，仅凭这两个数，不存在对所有有限维都有效的有限信息上界；但在每个固定维度内，（258.3）仍是共同有限上界，二者不能混淆。

这个机制不依赖非交换性。每个小概率都在中心带有斜率，但它们为保持正性而改变斜率的区间互不重叠。于是每一个参数位置都只支付有限的二阶变化，而中心信息把所有小概率的相对斜率同时计入。高斯卷积后转弯区间会重叠，不过范数预算已由凸性保留，不再依赖平滑后的严格支撑分离。中心 $\rho''(0)=0$ 也不妨碍高信息，因为正性约束需要整个邻域中的变化资料。

本节使用的自由是任意分离的参数尺度，以及随之缩小的高斯宽度。整函数延拓没有附带统一复域大小界，也没有统一三阶导数界；因此它不否定第257节在已知定量变化条件下的有限采样认证。任意小的迹范数邻域只约束状态位置，并不限制这种多尺度组织。

上界沿用第257节的标量正性估计与固定 SLD 测量；其文献背景仍是该节所列 Glaeser（1963）§II 引理I中归于 Malgrange 的估计。分尺度概率、高斯卷积和系数逼近由本节显式构造承担。这是一般密度曲线的最优性，未证明构造满足原四维处理器的矩、预算、规范节点或最优普通曲率条件；也未求出每个有限邻域半径下的联合最优包络。这里没有关于量子独有优势、物理能耗、Lean 认证或穷尽文献后的优先权主张。

<a id="entry-866"></a>

## 追加锚（本行以下为增补区）

<a id="section-259"></a>

## 259. 用校准端点替代外扩窗口的信息界

第257节在目标窗口两侧保留半径 $r$，由正性得到含 $r^{-2}$ 的信息上界。实际任务还提供了另一种边界资料：两个指定节点的 Fisher 信息已经由精确校准固定。本节证明这些端点值可以替代几何外扩项。应用时控制的区域是两个校准节点之间的完整区间；它不同于第257节围绕窄尾窗取得的较小扩展区间。

**引理 259.1（带端点斜率的正性最大界）。** 设 $a<b$，$f$ 在 $[a,b]$ 的一个开邻域上为非负 $C^2$ 函数，且 $f''\le L$ 在 $[a,b]$ 上成立，其中 $L\ge0$。定义

$$
R_f(t)=
\begin{cases}
f'(t)^2/f(t),&f(t)>0,\\
0,&f(t)=0,
\end{cases}
\tag{259.1}
$$

以及定向端点值

$$
E_a=
\begin{cases}
(f'(a)_+)^2/f(a),&f(a)>0,\\
0,&f(a)=0,
\end{cases}
\qquad
E_b=
\begin{cases}
((-f'(b))_+)^2/f(b),&f(b)>0,\\
0,&f(b)=0.
\end{cases}
\tag{259.2}
$$

则对全部 $t\in[a,b]$，

$$
\boxed{R_f(t)\le\max\{2L,E_a,E_b\}.}
\tag{259.3}
$$

证明。 非负开邻域保证任何零点的一阶导数为零，包含 $a,b$。在 $f'=0$ 的点，（259.3）直接成立。设 $f'(t)>0$，沿包含 $t$ 的正导数连通分支向左，记其左端为 $c\in[a,t)$。置

$$
H=(f')^2-2Lf,
\qquad
H'=2f'(f''-L).
\tag{259.4}
$$

在该分支中 $H'\le0$。若 $c>a$，连续性给出 $f'(c)=0$，故 $H(t)\le H(c)\le0$。若 $c=a$ 且 $f'(a)=0$，结论相同。其余情形 $f'(a)>0$，于是 $f(a)>0$ 且 $f(t)\ge f(a)$。当 $H(a)\le0$ 时仍有 $R_f(t)\le2L$；当 $H(a)>0$ 时，

$$
R_f(t)=2L+\frac{H(t)}{f(t)}
\le2L+\frac{H(a)}{f(t)}
\le2L+\frac{H(a)}{f(a)}=E_a.
\tag{259.5}
$$

对 $f'(t)<0$，沿负导数分支向右到其右端。在这个分支上 $H'\ge0$，而向右 $f$ 递减，同样得到 $R_f(t)\le\max\{2L,E_b\}$。端点自身的同向情形已经包含在端点值中，反向情形使用上述向区间内部追踪的论证。整个证明不需要 $R_f$ 在零点连续。证毕。

开邻域的正性在端点处有实际作用。若只要求 $f\ge0$ 于 $[0,1]$，取 $f(t)=t$，则按（259.2）的零值约定，$L=E_a=E_b=0$，但 $R_f(t)=1/t>0$；因此不能直接删除端点零值必须驻定的条件。另一方面，取 $L>0$、$[a,b]=[-1,1]$ 和 $f(t)=Lt^2/2$，则 $E_a=E_b=0$，且非零点满足 $R_f=2L$，说明标量二阶项的系数二不能降低。

**定理 259.2（由两端信息封住整个区间）。** 设 $\rho$ 是 $[a,b]$ 的一个开邻域上的 $n$ 维 $C^2$ 密度曲线，且

$$
L_{\rm op}=\sup_{t\in[a,b]}\|\rho''(t)\|_{\rm op}.
\tag{259.6}
$$

则

$$
\boxed{
\sup_{t\in[a,b]}I_Q(\rho_t)
\le2nL_{\rm op}+I_Q(\rho_a)+I_Q(\rho_b).
}
\tag{259.7}
$$

以 $L_1=\sup_{[a,b]}\|\rho''\|_1$ 计量时，还有

$$
\sup_{t\in[a,b]}I_Q(\rho_t)
\le nL_1+I_Q(\rho_a)+I_Q(\rho_b).
\tag{259.8}
$$

这些是点态 SLD 信息的界，允许内部和端点处改变秩，不要求最小正特征值具有统一下界。

证明。 固定任意名义点 $u\in[a,b]$。由第257节的内点正性论证，名义 SLD 存在；端点也在给定的非负开邻域内部，故同一论证适用。取这个 SLD 的固定正交特征基，形成在整个 $[a,b]$ 上不变的测量。其概率 $p_j(t)$ 满足 $p_j''\le L_{\rm op}$，且在名义点的经典信息之和恰为 $I_Q(\rho_u)$。引理259.1给出

$$
I_Q(\rho_u)
\le\sum_{j=1}^n\max\{2L_{\rm op},E_{j,a},E_{j,b}\}
\le2nL_{\rm op}+\sum_jE_{j,a}+\sum_jE_{j,b}.
\tag{259.9}
$$

每个定向端点项不超过该测量的完整端点信息项，而固定测量的经典信息不超过端点 SLD 信息。这一事实可在端点直接验证：对端点 SLD $S$ 和测量基向量 $e$，有

$$
p'=\operatorname{Re}\langle e,\rho S e\rangle,
\qquad
(p')^2\le p\,\langle e,S\rho S e\rangle.
\tag{259.10}
$$

对 $p>0$ 除以 $p$ 并求和，不超过 $\operatorname{Tr}(\rho S^2)$；$p=0$ 时 $p'=0$，其项为零。因此（259.9）给出（259.7），且端点基与名义点基不必相同。由第258节的迹零 Hermitian 范数不等式 $L_{\rm op}\le L_1/2$，得到（259.8）。证毕。

**推论 259.3（无需外扩的有限采样认证）。** 在定理259.2的区间上，设 $\rho\in C^3$，已知 $\sup_{[a,b]}\|\rho'''\|_{\rm op}\le M$。对非空有限采样集 $\{v_j\}\subset[a,b]$，设填充半径为 $h$，二阶导数估计为 $H_j$，误差满足 $\|H_j-\rho''(v_j)\|_{\rm op}\le\varepsilon$。若另有有效端点上界 $I_Q(\rho_a)\le C_a$、$I_Q(\rho_b)\le C_b$，则

$$
\sup_{[a,b]}I_Q
\le2n\left(\max_j\|H_j\|_{\rm op}+\varepsilon+Mh\right)+C_a+C_b.
\tag{259.11}
$$

任意可测 $T\subset[a,b]$ 的信息积分不超过右侧乘以 $|T|$。证明是第257节的导数连续模认证与定理259.2的直接组合；SLD 可测性也沿用该节的正则化表达式。这里的 $M$、采样误差和端点信息上界都是假设中的定量资料，不从有限个密度样本自动产生。相较第257节，这个认证使用端点信息，不需要把采样区间扩展到 $[a,b]$ 之外。

**推论 259.4（原完整节点区间的全过渡尺度二阶代价）。** 沿用第249—255节实际任务、有限正过渡参数 $\gamma$、原两个分别成立的预算及 $0<e_s=o(s)$。定义

$$
\begin{aligned}
I_s^{\rm node}&=[u_1(s),u_3(s)],\\
L_{{\rm op},s}^{\rm node}
&=\sup_{u\in I_s^{\rm node}}\|\rho_s''(u)\|_{\rm op},\\
L_{1,s}^{\rm node}
&=\sup_{u\in I_s^{\rm node}}\|\rho_s''(u)\|_1,\\
C_s&=\frac1{1-u_1(s)^2}+\frac1{1-u_3(s)^2}.
\end{aligned}
\tag{259.12}
$$

则对充分小的实际任务，

$$
\begin{aligned}
P_s&\le e_s^2\left(8L_{{\rm op},s}^{\rm node}+C_s\right),\\
Q_s&\le\kappa_s e_s^2\left(8L_{{\rm op},s}^{\rm node}+C_s\right),
\end{aligned}
\tag{259.13}
$$

且把 $8L_{{\rm op},s}^{\rm node}$ 换成 $4L_{1,s}^{\rm node}$ 后两式仍成立。若准备族满足第244.9式任一低内部代价条件，则

$$
\boxed{
\liminf_{s\downarrow0}e_s^2L_{{\rm op},s}^{\rm node}
\ge\frac{m_2(\gamma)}8,
\qquad
\liminf_{s\downarrow0}e_s^2L_{1,s}^{\rm node}
\ge\frac{m_2(\gamma)}4.
}
\tag{259.14}
$$

本结论只用原有的 $e_s=o(s)$，不另要求 $e_s=o(s^2)$。

证明。 两个指定节点都是实际输入域 $J_{a_s}$ 的内点，精确尖锐校准给出

$$
I_Q(\rho_{u_i(s)})=I_r(u_i(s))
=\frac1{1-u_i(s)^2}\quad(i=1,3).
\tag{259.15}
$$

第239、243、245节的实际节点渐近为 $h_1(s)\to c_*\in(0,1)$、$1-h_3(s)\sim d^2s^2$，其中 $u_i=2h_i-1$。因此

$$
C_s=\frac1{4h_1(s)(1-h_1(s))}+\frac1{F_s^2}
\sim\frac1{4d^2s^2},
\qquad e_s^2C_s\longrightarrow0.
\tag{259.16}
$$

原尾窗 $T_s=[2p_{\delta_s}-1,u_3(s)]$ 的左端趋于一，而 $u_1(s)\to2c_*-1<1$，故 $T_s\subset I_s^{\rm node}$ 最终成立。在定理259.2中取 $n=4$，使用（259.15）便控制整个节点区间，也控制尾窗。再乘以 $e_s^2$，或先在长度 $2\Delta_s$ 的尾窗上积分，得到（259.13）；积分归一化给出原来的 $\kappa_s=\Delta_s/(dse_s)\to1$。

第249、250节在原低内部代价条件下给出 $\liminf P_s\ge m_2(\gamma)$。从

$$
8e_s^2L_{{\rm op},s}^{\rm node}
\ge P_s-e_s^2C_s
\tag{259.17}
$$

及其迹范数版本，结合（259.16）得到（259.14）。证明不改变两个预算、尖锐集合、全输入精确性或秩的允许范围。证毕。

**注记 259.5（两种不同的边界资料）。** 外扩半径和端点信息提供两种不同的控制方式。第257节适合只有局部邻域正性与变化界的情形；本节在已知校准端点信息时，控制它们之间的整段曲线。对实际任务，恢复全部 $e_s=o(s)$ 尺度的代价，是把二阶导数的取上确界区域明确改为完整节点区间。不能据此宣布相同下界已经在原来的较小尾窗扩展区间内成立。

标量步骤使用（259.4）的单调性，量子步骤使用固定测量的经典信息不超过 SLD 信息；文献背景与第257节的 Glaeser—Malgrange 正性估计及标准 SLD 测量关系一致。这里的端点最大界、实际节点尺度和积分因子由正文推导承担，不把它们归于未核对的外部定理。本节未判定量子端点界的联合最优常数，也未给出原处理器下这些二阶下界的达到或最优性证明；本节仍是纯理论文本，不主张 Lean 认证或物理能量解释。

<a id="entry-868"></a>

## 追加锚（本行以下为增补区）

<a id="section-260"></a>

## 260. 共同矩阵上界、测量对偶与方向敏感的信息认证

第258节区分了同一参数位置的二阶变化总量与分布在不同尺度上的变化。本节保留更多关系资料：不把每个二阶导数压成一个范数，而是寻找一个固定正矩阵，同时在 Loewner 次序下控制整段曲线。这个共同上界的最小迹具有标准的测量优化对偶；它可以直接用于信息认证，也能区别范数相同而方向不同的数据。

**定义 260.1（共同二阶矩阵上界）。** 对定义在区间 $I$ 上的 $C^2$ 密度曲线，称与参数无关的 Hermitian 矩阵 $C$ 为共同上界，如果

$$
C\succeq0,
\qquad C\succeq\rho''(t)\quad(t\in I).
\tag{260.1}
$$

在紧区间上，定义

$$
\nu_I(\rho)=
\min\left\{\operatorname{Tr}C:
C\succeq0,\ C\succeq\rho''(t)\ \text{对所有 }t\in I\right\}.
\tag{260.2}
$$

这个最小值存在：有界的 $\rho''$ 使足够大的标量矩阵可行，且半正定矩阵的迹有界子水平集紧；全部约束的交集闭。这里要求同一个 $C$ 对所有参数有效，不以一族随参数改变的上界代替它。

**定理 260.2（共同矩阵上界的信息控制）。** 若（260.1）在 $[u-r,u+r]$ 上成立，其中 $r>0$，则

$$
I_Q(\rho_u)\le2\operatorname{Tr}C+r^{-2}.
\tag{260.3}
$$

若同一个 $C$ 在整个实轴上控制一条 $C^2$ 密度曲线，则

$$
I_Q(\rho_u)\le2\operatorname{Tr}C.
\tag{260.4}
$$

若密度曲线在 $[a,b]$ 的非负开邻域上为 $C^2$，且 $C$ 在 $[a,b]$ 上有效，则

$$
\sup_{[a,b]}I_Q
\le2\operatorname{Tr}C+I_Q(\rho_a)+I_Q(\rho_b).
\tag{260.5}
$$

证明。 在每个名义点固定其 SLD 的一个正交特征基 $e_j$，令 $p_j(t)=\langle e_j,\rho(t)e_j\rangle$，并置

$$
c_j=\langle e_j,Ce_j\rangle\ge0.
\tag{260.6}
$$

由（260.1），在所需的整个区间上 $p_j''\le c_j$。第257节的标量局部正性界逐项给出

$$
\frac{p_j'(u)^2}{p_j(u)}
\le2c_j+\frac{p_j(u)}{r^2}
\quad\text{当 }p_j(u)>0.
\tag{260.7}
$$

零概率项的导数为零。名义 SLD 测量精确给出点态信息，故求和并使用 $\sum_jc_j=\operatorname{Tr}C$、$\sum_jp_j=1$，得到（260.3）。全实轴上令 $r\to\infty$ 即得（260.4）。对于端点形式，改为对每个 $p_j$ 使用第259节的标量最大界，并将两个端点的固定测量信息分别控制为端点 SLD 信息，得到（260.5）。以上论证允许秩变化，且不对测量基随参数求导。证毕。

在（260.5）中取最小共同上界，便得到 $2\nu_{[a,b]}(\rho)$。这是一条上界，不声称对每一个预先指定的矩阵 $C$ 都达到最优 Fisher 信息。选取 $C=L_{\rm op}I$ 立即恢复第259节的标量范数界；直接保留矩阵方向则可能给出更小的迹。

为建立下述有限采样认证，先定义其有限矩阵优化问题，并调用既有的测量对偶。给定非空有限组 $n$ 阶 Hermitian 矩阵 $H_1,\ldots,H_m$，另置 $H_0=0$，定义

$$
\nu(H)=\min\left\{\operatorname{Tr}C:
C=C^*,\ C\succeq H_j\ (0\le j\le m)\right\}.
\tag{260.8}
$$

则

$$
\boxed{
\nu(H)=
\max\left\{
\sum_{j=0}^m\operatorname{Tr}(E_jH_j):
E_j\succeq0,\ \sum_{j=0}^mE_j=I
\right\}.
}
\tag{260.9}
$$

两端最优值都取得。加入 $H_0=0$ 正好要求共同上界半正定；等价地，可以删去目标中的零项，把其余测量效应的约束写成 $\sum_{j=1}^mE_j\preceq I$。

证明。 对任意两侧可行解，

$$
\sum_j\operatorname{Tr}(E_jH_j)
\le\sum_j\operatorname{Tr}(E_jC)
=\operatorname{Tr}C.
\tag{260.10}
$$

反向最优值相等正是标准的 Hermitian 测量收益半定规划对偶：测量侧取 $E_j=I/(m+1)$ 可严格可行，上界侧取足够大的 $C=\beta I$ 也严格可行。Slater 强对偶给出相等与达到；测量集合紧，以及 $H_0=0$ 下共同上界的迹子水平集紧，也直接保证两边的达到。这是 Watrous《The Theory of Quantum Information》§3.1.2 的最优测量规划在 $\phi(j)=H_j$ 上的应用，不把半定规划对偶本身当作新增定理。

在这个对应中，$E_j$ 是一个实际 POVM 的效应，$H_j$ 是 Hermitian 收益矩阵。$H_j$ 可以有负特征值，因此（260.9）一般不是未经转换的状态判别成功概率；其意义是标准的测量收益优化。它给共同上界的迹提供一个可核验的下界证据，与可行 $C$ 提供的上界证据配对。

**定理 260.4（有限采样的有效共同上界及收敛误差）。** 设 $I=[a,b]$，$\rho\in C^3$，并已知

$$
\sup_{t\in I}\|\rho'''(t)\|_{\rm op}\le M.
\tag{260.11}
$$

非空有限采样集 $\{v_j\}_{j=1}^m\subset I$ 的填充半径为 $h$。假设 Hermitian 估计矩阵满足

$$
\|H_j-\rho''(v_j)\|_{\rm op}\le\varepsilon.
\tag{260.12}
$$

记 $d=\varepsilon+Mh$，并令

$$
\nu_d(H)=
\min\left\{\operatorname{Tr}C:
C\succeq0,\ C\succeq H_j+dI\ (1\le j\le m)\right\}.
\tag{260.13}
$$

则每个最优 $C$ 都是实际曲线在 $I$ 上的共同上界，并有

$$
\boxed{
\nu_I(\rho)\le\nu_d(H)
\le\nu_I(\rho)+n(2\varepsilon+Mh).
}
\tag{260.14}
$$

另外，直接使用未加偏移的有限矩阵问题也给出

$$
\nu_d(H)\le\nu(H)+n(\varepsilon+Mh).
\tag{260.15}
$$

证明。 对任意 $t\in I$，取最近采样点 $v_j$。由（260.11）、（260.12）及 Hermitian 算子范数误差，

$$
\rho''(t)
\preceq\rho''(v_j)+MhI
\preceq H_j+(\varepsilon+Mh)I
\preceq C.
\tag{260.16}
$$

因此（260.13）中的可行解也对实际连续区间可行，给出（260.14）的左侧。反之，取（260.2）的最优解 $C_*$。由 $H_j\preceq\rho''(v_j)+\varepsilon I\preceq C_*+\varepsilon I$，可知

$$
C_*+(2\varepsilon+Mh)I
\tag{260.17}
$$

对（260.13）可行，得到右侧。若 $C_H$ 是（260.8）的最优解，则 $C_H+dI$ 对偏移后的问题可行，得到（260.15）。证毕。

（260.14）中的两个估计误差项不能在一般 Hermitian 读数下合并成一个。例如实际 $\rho$ 为常值、$M=0$，而每个读数都是 $H_j=\varepsilon I$，则 $\nu_I(\rho)=0$，但偏移后的认证值为 $2n\varepsilon$。这说明了本认证程序中该误差系数的必要性；若另加无偏或迹约束，须重新分析对应的估计类。

若另满足定理260.2的端点条件，即 $\rho$ 在 $[a,b]$ 的一个开邻域上为 $C^2$ 密度曲线，并有有效端点上界 $B_a\ge I_Q(\rho_a)$、$B_b\ge I_Q(\rho_b)$，则得到

$$
\sup_I I_Q\le2\nu_d(H)+B_a+B_b.
\tag{260.18}
$$

任意可测子集 $T\subset I$ 上的积分再乘以 $|T|$ 即被控制。局部形式适用于满足 $[u-r,u+r]\subset I$ 的名义点：此时 $I_Q(\rho_u)\le2\nu_d(H)+r^{-2}$。若目标集合 $T$ 中每一点都满足这一包含关系，则该界控制 $\sup_T I_Q$，并相应控制其积分。在固定曲线和已知 $M$ 下，当认证误差与网格半径同时趋零时，（260.14）使这个有限矩阵认证值收敛到真正的连续共同上界值。没有已知的变化模或误差界时，不能把这一结论用于第256节的无限制准备类。

**命题 260.5（非交换二阶方向的精确共同上界）。** 在二维空间中取

$$
H_1=\Lambda\sigma_x,\qquad H_2=\Lambda\sigma_z,
\qquad \Lambda>0,
\tag{260.19}
$$

其中 $\sigma_x,\sigma_z$ 为 Pauli 矩阵。则

$$
\nu(H_1,H_2)=\sqrt2\,\Lambda.
\tag{260.20}
$$

一个达到最小值的共同上界为

$$
C_0=\frac{\Lambda}{\sqrt2}I
+\frac{\Lambda}{2}(\sigma_x+\sigma_z).
\tag{260.21}
$$

证明。 对 $aI+v\cdot\sigma$，两个特征值为 $a\pm\|v\|$。在 $C_0$、$C_0-H_1$ 和 $C_0-H_2$ 中，向量部分长度均为 $\Lambda/\sqrt2$，故三者均半正定，且 $\operatorname{Tr}C_0=\sqrt2\Lambda$。另一方面，取

$$
E_1=\frac12\left(I+\frac{\sigma_x-\sigma_z}{\sqrt2}\right),
\qquad E_2=I-E_1,\qquad E_0=0.
\tag{260.22}
$$

这是一个可行测量，收益为

$$
\operatorname{Tr}(E_1H_1)+\operatorname{Tr}(E_2H_2)
=\sqrt2\Lambda.
\tag{260.23}
$$

由（260.10），两个可行证据相等，证明（260.20）。若两份矩阵都加 $dI$，其中 $d\ge0$，则 $C_0+dI$ 与同一个测量分别给出相等的两侧值，故

$$
\nu(H_1+dI,H_2+dI)=\sqrt2\Lambda+2d.
\tag{260.24}
$$

这些二阶数据也能由实际正密度曲线在一个有限区间上共同实现。取 $\ell>0$ 满足 $\Lambda\ell^2\le1/2$，令 $x=t/\ell$，并在 $0\le t\le\ell$ 上定义

$$
\rho(t)=\frac I2+\Lambda\ell^2
\left[
\left(\frac{x^2}{2}-\frac{x^3}{6}\right)\sigma_x
+\frac{x^3}{6}\sigma_z
\right].
\tag{260.25}
$$

方括号中向量系数的长度至多为 $\sqrt5/6$，因此 $\rho(t)$ 的两个特征值都严格为正；连续性还给出整个闭区间的正开邻域。它的迹恒为一，矩阵元是多项式，并且

$$
\rho''(t)=\Lambda\bigl((1-x)\sigma_x+x\sigma_z\bigr).
\tag{260.26}
$$

这是两个端点二阶矩阵的凸组合，故 $C_0$ 控制整段曲线；端点又迫使任何共同上界满足（260.19），所以 $\nu_{[0,\ell]}(\rho)=\sqrt2\Lambda$。该曲线的最大二阶算子范数恰为 $\Lambda$。对同一条曲线、同样的两个端点信息，标量范数证书的二阶项是 $4\Lambda$，共同矩阵证书的对应项则是 $2\sqrt2\Lambda$，得到严格改进。这个比较不主张实际 Fisher 峰值达到任一上界，也不把多项式密度延拓后的全实轴正性当作已知。证毕。

**推论 260.6（实际节点区间的方向敏感二阶代价）。** 在第259节的完整节点区间 $I_s^{\rm node}$ 上，记

$$
\nu_s=\nu_{I_s^{\rm node}}(\rho_s).
\tag{260.27}
$$

沿用其精确端点和 $C_s$，原尾窗代价满足

$$
P_s\le e_s^2(2\nu_s+C_s),
\qquad
Q_s\le\kappa_s e_s^2(2\nu_s+C_s).
\tag{260.28}
$$

在原任一低内部代价条件、有限正过渡参数 $\gamma$ 及全部原尺度 $0<e_s=o(s)$ 下，

$$
\liminf_{s\downarrow0}e_s^2\nu_s
\ge\frac{m_2(\gamma)}2.
\tag{260.29}
$$

证明。 对（260.5）取共同上界的最小迹，使用第259节的节点校准和尾窗归一化，得到（260.28）。再由 $e_s^2C_s\to0$ 及原峰值下界即得（260.29）。同时，两个简单可行上界给出

$$
\nu_s\le4L_{{\rm op},s}^{\rm node},
\qquad
\nu_s\le2L_{1,s}^{\rm node},
\tag{260.30}
$$

所以本结论与第259节的两个范数版本相容，并保留了它们舍去的共同方向资料。这里仍不证明原处理器约束下的达到或最优常数。证毕。

**命题 260.7（共同性与定义域的两种限制）。** 在紧区间上，共同上界满足

$$
\nu_I(\rho)\ge
\sup_{t\in I}\operatorname{Tr}\bigl(\rho''(t)_+\bigr),
\tag{260.31}
$$

但一般不能取等号。另一方面，若一个秩至多一的固定半正定 $C$ 在整个实轴上满足（260.1），则密度曲线必为常值。

证明。 令 $P_t$ 为 $\rho''(t)$ 正谱的投影。对每个可行 $C$，有

$$
\operatorname{Tr}C\ge\operatorname{Tr}(P_tC)
\ge\operatorname{Tr}\bigl(\rho''(t)_+\bigr).
\tag{260.32}
$$

取参数上确界和共同上界下确界得到（260.31）。在命题260.5中，右侧为 $\Lambda$，而左侧为 $\sqrt2\Lambda$，因此两者确实不同。第258节的分尺度例子还表明，这种差别并不需要非交换矩阵。

现在设 $C$ 秩至多一，且在整个实轴上有效。对任意 $w\in\ker C$，函数 $f_w(t)=\langle w,\rho(t)w\rangle$ 有界且满足 $f_w''\le0$，故为实轴上的有界凹函数，必须为常值。于是 $\langle w,\rho''(t)w\rangle=0$。由 $C-\rho''(t)\succeq0$，零二次型蕴含 $(C-\rho''(t))w=0$，从而 $\rho''(t)w=0$。Hermitian 矩阵 $\rho''(t)$ 因而支撑在 $C$ 的至多一维像空间中；它又迹为零，所以只能为零。最后，密度曲线在实轴上仿射且有界，故为常值。证毕。

命题260.5中的 $C_0$ 恰为秩一，却允许有限区间中的非平凡正密度曲线。这不与本命题冲突：要求同一个上界与正性在整个实轴共同延续，是额外且更强的条件。因此 $2\operatorname{Tr}C$ 是一般有效上界，但不能对每个指定的 $C$ 都宣称达到。

测量收益及其半定规划对偶的来源为 John Watrous，*The Theory of Quantum Information*（Cambridge University Press，2018），[作者公开的书稿版本](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§1.2.3 的定理1.18及 §3.1.2 第133—136页的 Hermitian 收益规划、式（3.33）—（3.42）。该书已经允许一般 Hermitian 收益，故本节不把有符号收益或强对偶作为新发现。共同二阶上界的信息控制、带误差的连续区间认证、明确的正密度实现及原尾窗代价的连接由上述推导承担。没有统一矩阵上界、变化模或认证误差的有限观测，仍不能获得这些保证。

<a id="entry-870"></a>

## 追加锚（本行以下为增补区）

<a id="section-261"></a>

## 261. 固定矩阵二阶上界的精确全实轴极值

第260节给出 $I_Q\le2\operatorname{Tr}C$，但同节的秩一结论说明：对一个指定矩阵 $C$，这个数未必是最优值。本节在全实轴上完成该问题的分类。决定能否逼近迹上界的条件是 $C$ 是否至少具有两个正特征方向；构造可以始终与 $C$ 对角化在同一个基中。

**定义 261.1（固定共同上界的允许类）。** 固定 $n$ 阶半正定矩阵 $C$，令

$$
\mathcal R(C)=
\left\{\rho\in C^2(\mathbb R;M_n):
\rho(t)\succeq0,\ \operatorname{Tr}\rho(t)=1,
\ \rho''(t)\preceq C\ \text{对所有 }t\in\mathbb R\right\},
\tag{261.1}
$$

并定义

$$
\mathfrak F(C)=\sup_{\rho\in\mathcal R(C)}I_Q(\rho_0).
\tag{261.2}
$$

这个类总含常值密度，故非空。矩阵 $C$ 在整个问题中固定，不随参数或准备曲线改变。

**定理 261.2（秩分界与精确上确界）。** 有

$$
\boxed{
\mathfrak F(C)=
\begin{cases}
0,&\operatorname{rank}C\le1,\\
2\operatorname{Tr}C,&\operatorname{rank}C\ge2.
\end{cases}
}
\tag{261.3}
$$

两种情况下，即使把允许类进一步限制为每个矩阵元可延拓成整函数、每个有限实数参数处满秩、且全部状态与 $C$ 在同一个固定基中对角化，上确界仍相同。第二种情形只断言任意逼近，不要求一条曲线恰好取得等号。

证明。 第260节已给出上界 $I_Q\le2\operatorname{Tr}C$。当 $C$ 秩至多一时，该节的核空间凹性论证使所有允许曲线恒定，所以信息为零；常值密度 $I/n$ 也属于所述更小类。

以下设 $m=\operatorname{rank}C\ge2$。先在固定基中写

$$
C=\operatorname{diag}(c_0,c_1,\ldots,c_N,0,\ldots,0),
\qquad N=m-1,\quad c_j>0.
\tag{261.4}
$$

第零方向作为补偿概率，其余 $N$ 个正方向作为分别改变的概率。令 $c_{\min}=\min_{0\le j\le N}c_j$，任取 $\kappa>0$，并选

$$
\lambda>1+\frac1{\kappa c_{\min}}.
\tag{261.5}
$$

对 $1\le i\le N$，置

$$
v_i=R\lambda^{-(i-1)},\qquad \tau_i=\kappa v_i,
\tag{261.6}
$$

其中 $R>0$ 稍后由归一化确定。定义非负连续分段线性的速度

$$
w_i(t)=
\begin{cases}
0,&t\le-\tau_i-v_i/c_0,\\
c_0(t+\tau_i+v_i/c_0),
&-\tau_i-v_i/c_0<t<-\tau_i,\\
v_i,&-\tau_i\le t\le\tau_i,\\
c_i(\tau_i+v_i/c_i-t),
&\tau_i<t<\tau_i+v_i/c_i,\\
0,&t\ge\tau_i+v_i/c_i.
\end{cases}
\tag{261.7}
$$

它在左侧以斜率 $c_0$ 上升，在右侧以斜率 $-c_i$ 下降；两侧一般不对称。令

$$
q_i(t)=\int_t^\infty w_i(x)\,dx,
\qquad
q_0(t)=\mu-\sum_{i=1}^Nq_i(t).
\tag{261.8}
$$

若 $m=n$，取 $\mu=1$；若 $m<n$，取任意固定 $0<\mu<1$，并在 $\ker C$ 的 $n-m$ 个方向各放常值概率 $(1-\mu)/(n-m)$。

各速度的总面积为

$$
\int_{\mathbb R}w_i(t)\,dt
=v_i^2\left(2\kappa+\frac1{2c_0}+\frac1{2c_i}\right).
\tag{261.9}
$$

因此选择

$$
R^2=
\frac{\mu}{
\displaystyle\sum_{i=1}^N\lambda^{-2(i-1)}
\left(2\kappa+\frac1{2c_0}+\frac1{2c_i}\right)}
\tag{261.10}
$$

便使 $\sum_iq_i(-\infty)=\mu$。所有 $q_i$ 非负且递减，故 $q_0\ge0$，总活动概率恒为 $\mu$。连同核空间中的常值部分，得到一条迹为一的对角密度曲线 $\rho^{(0)}$。

现在核对固定矩阵预算，而不将它改成标量范数。因为 $q_i'=-w_i$，其弱二阶导数在左侧转弯区间等于 $-c_0$，在右侧转弯区间等于 $c_i$，其余处为零。对任一正特征值 $c_j$，由（261.5）有

$$
v_{i+1}\left(\kappa+\frac1{c_j}\right)
\le\frac{v_i}{\lambda}
\left(\kappa+\frac1{c_{\min}}\right)
<\kappa v_i=\tau_i.
\tag{261.11}
$$

故不同概率的转弯区间在正、负两侧分别互不相交。几乎每个 $t$ 至多有一个非零的 $q_i''$。在左侧转弯时，非零二阶分量为

$$
q_i''=-c_0,\qquad q_0''=c_0;
\tag{261.12}
$$

在右侧转弯时则为

$$
q_i''=c_i,\qquad q_0''=-c_i.
\tag{261.13}
$$

逐个对角分量比较可见，两种情况下都满足 $(\rho^{(0)})''\preceq C$。各 $w_i$ 连续且 Lipschitz，故这条曲线为 $C^{1,1}$，上述有界弱二阶导数没有额外点质量。

在中心，速度处于平台，直接计算两侧面积得到

$$
\begin{aligned}
q_i(0)&=v_i^2\left(\kappa+\frac1{2c_i}\right),
&q_i'(0)&=-v_i,\\
q_0(0)&=\left(\kappa+\frac1{2c_0}\right)\sum_i v_i^2,
&q_0'(0)&=\sum_i v_i.
\end{aligned}
\tag{261.14}
$$

所有活动中心概率严格为正，核空间部分在需要时也严格为正。因此中心 Fisher 信息为

$$
\begin{aligned}
I^{(0)}(0)
&=\sum_{i=1}^N\frac1{\kappa+1/(2c_i)}
+\frac{(\sum_i v_i)^2}
{(\kappa+1/(2c_0))\sum_i v_i^2}\\
&\ge\sum_{j=0}^N\frac1{\kappa+1/(2c_j)}.
\end{aligned}
\tag{261.15}
$$

最后一步只使用正数 $v_i$ 的关系 $(\sum_i v_i)^2\ge\sum_i v_i^2$。当 $\kappa\downarrow0$，右侧趋于 $2\sum_jc_j=2\operatorname{Tr}C$。归一化尺度 $R$ 与活动总质量 $\mu$ 都在这些比值中消去。

为得到所要求的解析曲线，对整条有界密度曲线作高斯卷积

$$
\rho^{(\epsilon)}(t)
=\int_{\mathbb R}g_\epsilon(t-x)\rho^{(0)}(x)\,dx,
\qquad
g_\epsilon(t)=\frac{e^{-t^2/(2\epsilon^2)}}{\sqrt{2\pi}\epsilon}.
\tag{261.16}
$$

正性、迹一及共同对角基由凸平均保留。每个 $q_i$ 在左侧半轴严格为正，$q_0$ 在右侧半轴严格为正；高斯核处处正，故每个活动分量在每个有限实数参数处严格为正。核空间中的常值概率不变。由此整条曲线在实轴上满秩。与第258节相同，有界函数的高斯卷积逐矩阵元延拓为整函数。

固定矩阵上界也被精确保留：弱导数与卷积可交换，且

$$
C-(\rho^{(\epsilon)})''(t)
=\int_{\mathbb R}g_\epsilon(t-x)
\bigl(C-(\rho^{(0)})''(x)\bigr)\,dx
\succeq0.
\tag{261.17}
$$

对已经固定的 $\kappa,\lambda,R$，高斯逼近恒等使中心概率及其一阶导数收敛到（261.14）。这些中心概率严格为正，所以对角 Fisher 信息的有限有理和连续，得到

$$
I_Q(\rho^{(\epsilon)}_0)\longrightarrow I^{(0)}(0)
\quad(\epsilon\downarrow0).
\tag{261.18}
$$

因此，对任意 $0<\delta<1$，先选足够小 $\kappa$，再依次确定 $\lambda,R$，最后选足够小 $\epsilon$，即可在固定 $C$ 下达到

$$
I_Q(\rho^{(\epsilon)}_0)
\ge(1-\delta)2\operatorname{Tr}C.
\tag{261.19}
$$

结合既有上界即得（261.3）。固定酉共轭把构造送回任意给定矩阵 $C$ 的原坐标，同时保持 Loewner 条件与信息。证毕。

这里两侧速度通常不对称，所以本节只使用平滑后中心一阶数据的收敛，不宣称像第258节的偶对称构造那样精确保留中心概率或 $\rho''(0)=0$。所需的固定矩阵预算由（261.17）直接保证，无需这些额外等式。

**推论 261.3（上界矩阵失秩处的极值不连续）。** 在二维空间取

$$
C_\varepsilon=\operatorname{diag}(1,\varepsilon),
\qquad \varepsilon\ge0.
\tag{261.20}
$$

则 $C_\varepsilon\to C_0$ 的算子范数差为 $\varepsilon$，但

$$
\mathfrak F(C_\varepsilon)=2(1+\varepsilon)
\quad(\varepsilon>0),
\qquad
\mathfrak F(C_0)=0.
\tag{261.21}
$$

证明。 正 $\varepsilon$ 时矩阵秩为二，零时秩为一，直接应用定理261.2。证毕。

这个不连续性属于对整类允许曲线取最优值之后的结论，不是某一条固定曲线的信息突然变化。精确的零特征方向使相应概率在全实轴上凹且有界，从而固定；任意正余量则允许非对称的转弯。逼近最优值时，曲线及其参数尺度随上界变化；虽然各曲线均延拓到整个复平面，本节没有给出态的统一正谱隙、统一三阶导数界、复域上的统一函数大小界或尺度复杂度控制。

一个固定正矩阵的迹给出总上界，但能否使用这些方向，还取决于它们是否允许概率守恒下的共同续接。只有一个可变正方向时，迹为一把变化全部消掉；至少两个方向时，负二阶变化可以由另一个方向承担，再在不同参数区间分别恢复。上述构造把这种共同实现写成了具体的概率曲线。

每条逼近曲线中的状态两两对易，并与给定的 $C$ 对易，因此这里没有量子独有优势主张。问题定义要求正性和同一个矩阵上界在整个实轴上成立，不能把（261.3）无条件搬到有限区间、任意随参数变化的上界，或原处理器的矩、分项预算、尖锐节点约束类中。高斯解析化及标量正性背景沿用第258—260节；固定矩阵的各向异性达到由本节构造承担，不要求原处理器约束下的达到。

<a id="entry-872"></a>

## 追加锚（本行以下为增补区）

<a id="section-262"></a>

## 262. 固定正谱隙下的失秩连续性与非交换尺度优势

第261节的极值跳变允许准备曲线随上界矩阵变化，且没有统一的态谱下界。本节固定这个缺失的条件。在二维上界 $C_\eta=\operatorname{diag}(1,\eta)$ 趋于秩一时，所有保持固定正谱隙的允许曲线，其信息都趋于零；但一般量子曲线和两两对易曲线的最优衰减阶不同。

**定理 262.1（接近秩一时的定量刚性）。** 设 $C\succeq0$，记

$$
\Lambda=\|C\|_{\rm op},\qquad
\delta=\operatorname{Tr}C-\Lambda,
\qquad 0<\delta\le\Lambda.
\tag{262.1}
$$

若 $\rho$ 是全实轴上的 $C^2$ 密度曲线，处处满足 $\rho''\preceq C$，则

$$
\|\rho'(0)\|_{\rm HS}^2
\le5\Lambda^{2/3}\delta^{1/3}.
\tag{262.2}
$$

若名义点还满足 $\rho(0)\succeq\alpha I$，其中 $\alpha>0$，则

$$
I_Q(\rho_0)\le
\frac5\alpha\Lambda^{2/3}\delta^{1/3}.
\tag{262.3}
$$

证明。 取 $C$ 的一个最大特征方向投影 $P$，令 $Q=I-P$，写成

$$
C=\Lambda P+C_Q,\qquad
W=\Lambda Q-C_Q\succeq0,
\qquad f(t)=\operatorname{Tr}(W\rho(t)).
\tag{262.4}
$$

置 $\tau=\operatorname{Tr}C$ 以及

$$
\beta=\operatorname{Tr}(WC)
=\Lambda\delta-\operatorname{Tr}(C_Q^2),
\qquad K=\tau^2-\operatorname{Tr}(C^2).
\tag{262.5}
$$

有 $0\le f\le\Lambda$、$0\le\beta\le\Lambda\delta$，并且 $f''\le\beta$。对非负标量函数使用全实轴正性界，得到

$$
|f'|\le\sqrt{2\beta\Lambda}.
\tag{262.6}
$$

此处允许 $\beta=0$，那时 $f$ 为常值。令 $H=\rho''$、$D=C-H$。由 $D\succeq0$、$\operatorname{Tr}H=0$，有 $\operatorname{Tr}D=\tau$，从而 $\operatorname{Tr}(D^2)\le\tau^2$。展开并使用 $C+W=\Lambda I$，得到

$$
\|H(t)\|_{\rm HS}^2
\le K+2\operatorname{Tr}(CH(t))
=K-2f''(t).
\tag{262.7}
$$

因此，对任意 $h>0$，

$$
\int_{-h}^h\|\rho''(t)\|_{\rm HS}^2\,dt
\le2hK+4\sqrt{2\beta\Lambda}.
\tag{262.8}
$$

以下直接给出所需的一维插值步骤。两个密度矩阵的 Hilbert–Schmidt 距离至多为 $\sqrt2$，故对称差商满足

$$
\left\|\frac{\rho(h)-\rho(-h)}{2h}\right\|_{\rm HS}
\le\frac1{\sqrt2h}.
\tag{262.9}
$$

一阶导数与此差商的差可以写成 $\rho''$ 对一个带符号三角核的积分；该核的平方积分为 $h/6$。Cauchy–Schwarz 和（262.8）于是给出

$$
\|\rho'(0)\|_{\rm HS}
\le\frac1{\sqrt2h}
+\sqrt{\frac{Kh^2}{3}
+\frac{2h}{3}\sqrt{2\beta\Lambda}}.
\tag{262.10}
$$

具体地，这个核在 $[-h,0]$ 上为 $(h+t)/(2h)$，在 $[0,h]$ 上为 $-(h-t)/(2h)$。又因为

$$
K=2\Lambda\delta+\delta^2-\operatorname{Tr}(C_Q^2)
\le3\Lambda\delta,
\tag{262.11}
$$

取 $h=(\Lambda^2\delta)^{-1/6}$，使用 $\delta\le\Lambda$，可得

$$
\|\rho'(0)\|_{\rm HS}^2
\le
\left(\frac1{\sqrt2}+\sqrt{1+\frac{2\sqrt2}{3}}\right)^2
\Lambda^{2/3}\delta^{1/3}
<5\Lambda^{2/3}\delta^{1/3}.
\tag{262.12}
$$

最后，在 $\rho(0)$ 的特征基中，所有特征值至少为 $\alpha$。标准 SLD 公式给出

$$
I_Q(\rho_0)
=\sum_{i,j}\frac{2|\rho'_{ij}(0)|^2}{\lambda_i+\lambda_j}
\le\frac1\alpha\|\rho'(0)\|_{\rm HS}^2.
\tag{262.13}
$$

结合（262.12）即得结论。证毕。

该信息上界只需要名义点的谱下界；全实轴上的统一谱下界是一个更强的充分条件。若 $\delta=0$，第260节的秩一刚性直接给出零信息。对于有界的 $\Lambda$ 和固定正 $\alpha$，因此恢复了靠近秩一上界的信息连续性。这里没有声称数字 $5$ 最优。

**定义 262.2（保持正谱隙的二维比较类）。** 对 $0<\eta\le1$，令

$$
C_\eta=\operatorname{diag}(1,\eta).
\tag{262.14}
$$

记 $\mathcal A_\eta$ 为全实轴上满足

$$
\rho\in C^2,\qquad
\operatorname{Tr}\rho=1,\qquad
\rho(t)\succeq I/4,\qquad
\rho''(t)\preceq C_\eta
\tag{262.15}
$$

的密度曲线集合；$\mathcal A_\eta^{\rm com}$ 再要求 $[\rho(t),\rho(s)]=0$ 对所有实数 $s,t$ 成立。后者不要求状态与 $C_\eta$ 对易。分别定义两类的名义信息上确界为 $F_\eta$ 和 $F_\eta^{\rm com}$。

**定理 262.3（非交换曲线的三分之一次幂阶）。** 存在与 $\eta$ 无关的 $k>0$ 和 $\eta_0>0$，使得

$$
k\eta^{1/3}\le F_\eta\le20\eta^{1/3}
\qquad(0<\eta<\eta_0).
\tag{262.16}
$$

即使只允许逐矩阵元可延拓成整函数的曲线，下界仍成立。

证明。 上界是定理262.1在 $\Lambda=1$、$\delta=\eta$、$\alpha=1/4$ 上的直接应用。为构造下界，固定实值 $F\in C_c^\infty((-1,1))$，满足 $F(0)=0$、$F'(0)=1$、$\|F\|_\infty\le1$，并置

$$
J=\int_{\mathbb R}F''(u)^2\,du>0,\quad
A=\frac1{16},\quad
v=\frac{\sqrt\eta}{8},\quad
T=\left(\frac{2A^2J}{v}\right)^{1/3},\quad
x(t)=AF(t/T).
\tag{262.17}
$$

定义有界分段连续函数

$$
g(t)=
\begin{cases}
2x''(t)^2,&-T\le t\le T,\\
-\eta/2,&T<t<T+2v/\eta,\\
0,&\text{其余情形},
\end{cases}
\tag{262.18}
$$

并以 $y''=g$、$y(-\infty)=1/2$、$y'(-\infty)=0$ 定义 $y$。第一段加速度的积分为

$$
\int_{-T}^T2x''(t)^2\,dt
=\frac{2A^2J}{T^3}=v,
\tag{262.19}
$$

第二段的积分为 $-v$。故 $y'$ 从零增加到 $v$，再下降到零，全程非负。总增量满足

$$
0\le y(t)-\frac12
\le2Tv+\frac{v^2}{\eta}
=O(\eta^{1/3})+\frac1{64}.
\tag{262.20}
$$

对所有充分小的 $\eta$，有 $1/2\le y\le5/8$。定义中间密度曲线

$$
\rho^{(0)}(t)=
\begin{pmatrix}y(t)&x(t)\\x(t)&1-y(t)\end{pmatrix}.
\tag{262.21}
$$

它的最小特征值至少为

$$
\frac12-\sqrt{(1/8)^2+(1/16)^2}>\frac14.
\tag{262.22}
$$

现核对同一个指定上界。第一段中 $g=2x''{}^2$，并因 $T\to\infty$ 而有 $g\le1/2$。于是

$$
C_\eta-(\rho^{(0)})''
=\begin{pmatrix}1-g&-x''\\-x''&\eta+g\end{pmatrix}
\succeq0,
\tag{262.23}
$$

因为其对角元非负，行列式至少为 $(1/2)g-x''{}^2=0$。第二段中 $x''=0$、$g=-\eta/2$，两个对角元也为正。其余位置二阶导数为零。这条曲线为 $C^{1,1}$，弱二阶导数有界，故这些比较几乎处处有效，没有额外点质量。

在名义点，$x(0)=0$、$x'(0)=A/T$。测量 $\sigma_x$ 的两个概率为 $1/2\pm x$，因此其经典信息恰为

$$
4A^2/T^2
=\frac{4A^2}{(16A^2J)^{2/3}}\eta^{1/3}.
\tag{262.24}
$$

对整条曲线作宽度 $\epsilon$ 的高斯卷积。凸平均同时保留 $\rho\succeq I/4$、迹一和精确的上界 $C_\eta$；有界矩阵元的卷积延拓成整函数。对每个已经固定的 $\eta$，中心的一阶数据在 $\epsilon\downarrow0$ 时收敛。因此可选择 $\epsilon$，使同一个 $\sigma_x$ 测量的信息至少保留（262.24）的一半。SLD 信息不小于这份测量信息，故可取

$$
k=\frac{2A^2}{(16A^2J)^{2/3}}>0.
\tag{262.25}
$$

这证明下界及解析性版本。平滑宽度允许依赖 $\eta$，谱下界和矩阵上界则不因此放宽。证毕。

**定理 262.4（所有两两对易二维曲线的平方根阶）。** 对定义262.2中的整个对易类，有

$$
\sqrt\eta\le F_\eta^{\rm com}
\le\frac83\sqrt\eta.
\tag{262.26}
$$

下界也由整函数曲线实现。

证明。 非常值的两两对易二维密度族有一个共同特征基，因此可以写成

$$
\rho(t)=I/2+z(t)N,\qquad
N=\boldsymbol n\cdot\boldsymbol\sigma,\quad
\|\boldsymbol n\|=1,\quad |z(t)|\le b=1/4.
\tag{262.27}
$$

这里允许这个基相对于 $C_\eta$ 任意旋转。上界条件的行列式给出

$$
\eta+(1-\eta)n_z z''-(z'')^2\ge0.
\tag{262.28}
$$

因此存在 $a,d>0$，使 $-a\le z''\le d$、$ad=\eta$。分别对非负函数 $z+b$ 和 $b-z$ 使用全实轴标量正性界，得到

$$
z'^2\le\min\{2d(z+b),\,2a(b-z)\}
\le\frac{4adb}{a+d}
\le2b\sqrt\eta.
\tag{262.29}
$$

中间的不等式取两条仿射函数交点处的最大值。由于特征值为 $1/2\pm z$，

$$
I_Q=\frac{z'^2}{1/4-z^2}
\le\frac{2b\sqrt\eta}{1/4-b^2}
=\frac83\sqrt\eta.
\tag{262.30}
$$

常值族的信息为零，也满足该界。反向取

$$
\rho(t)=I/2+A_0\sin(\omega t)\sigma_x,
\qquad A_0=1/4,\quad
\omega^2=\sqrt\eta/A_0.
\tag{262.31}
$$

其状态两两对易，处处至少为 $I/4$，矩阵元为整函数，二阶非对角元的绝对值至多为 $\sqrt\eta$。因此 $C_\eta-\rho''$ 的对角元为 $1,\eta$，行列式非负，满足相同矩阵上界。中心信息为 $4A_0\sqrt\eta=\sqrt\eta$，证明下界。证毕。

合并两条定理可知，在完全相同的上界和谱下界条件下，

$$
F_\eta=\Theta(\eta^{1/3}),\qquad
F_\eta^{\rm com}=\Theta(\eta^{1/2}),\qquad
\frac{F_\eta}{F_\eta^{\rm com}}=\Theta(\eta^{-1/6}).
\tag{262.32}
$$

因而充分小的 $\eta$ 时，定理262.3中的逼近曲线必不两两对易。这个区别已与“仅要求状态和上界在同一基中对角化”的更小比较类分开：定理262.4允许全部固定特征基方向。

定理262.1所用标量正性估计沿用第257—261节的 Glaeser–Malgrange 背景，SLD 公式沿用同处的标准来源；插值结构的经典背景为 L. Nirenberg，*On elliptic partial differential equations*，Annali della Scuola Normale Superiore di Pisa，第三辑第13卷（1959），115—162页，[公开原文](https://www.numdam.org/item/ASNSP_1959_3_13_2_115_0.pdf)，Lecture II，第124—126页，式（2.2）—（2.3）。其中的一维参数 $j=1,m=2,p=q=\infty,r=2$ 给出经典指数 $2/3$；本节不把插值方法本身作为新增结果。这里使用的有限窗口估计及其常数由（262.9）—（262.12）直接证明，不额外假设全实轴二阶导数平方可积。正性与矩阵上界均要求在全实轴成立。定理262.1的信息上界仅需名义点的固定正谱下界；定义262.2及两类上确界的比较则共同要求全实轴上的统一下界 $\rho(t)\succeq I/4$。下界构造保持这一全域条件。它们不加入原处理器的矩、分项预算、校准节点或规定有限阶数据，所以（262.32）是本节所定义曲线类中的非交换优势，不能自动提升为原受限任务的最优优势。

<a id="entry-874"></a>

## 追加锚（本行以下为增补区）

<a id="section-263"></a>

## 263. 正谱隙下对易极值的精确公式与方向转换

第262节比较了固定正谱隙下的一般曲线与对易曲线。本节将对易侧的阶估计推进为精确上确界，并允许谱下界变化。对易状态的共同特征基可以相对于给定的矩阵上界旋转；这个方向自由度必须保留。

**定义 263.1（二维对易极值及其参数）。** 固定 $0<\alpha<1/2$、$0<\eta\le1$。记 $F_{\rm com}(\alpha,\eta)$ 为全实轴上所有 $C^2$ 密度曲线的名义 SLD 信息上确界，其中

$$
\rho(t)\succeq\alpha I,\qquad
\rho''(t)\preceq\operatorname{diag}(1,\eta),\qquad
[\rho(s),\rho(t)]=0
\quad(s,t\in\mathbb R).
\tag{263.1}
$$

置

$$
b=\frac12-\alpha,
\qquad q=\frac{1-\eta}{1+\eta},
\qquad
z_*=
\min\left\{\sqrt{(2b^2-1/4)_+},\ bq\right\}.
\tag{263.2}
$$

**定理 263.2（全部共同特征基方向上的精确极值）。** 有

$$
\boxed{
F_{\rm com}(\alpha,\eta)
=\frac{2\sqrt\eta\sqrt{b^2-z_*^2}}{1/4-z_*^2}.
}
\tag{263.3}
$$

即使只允许逐矩阵元可延拓成整函数的曲线，上确界仍相同。

证明。 非常值的对易二维族可以写成

$$
\rho(t)=I/2+z(t)N,
\qquad N=\boldsymbol n\cdot\boldsymbol\sigma,
\qquad\|\boldsymbol n\|=1,
\qquad |z(t)|\le b.
\tag{263.4}
$$

固定 $N$ 后，由矩阵上界的行列式可知

$$
-a\le z''\le d,\qquad
a,d>0,\qquad ad=\eta,\qquad
d-a=(1-\eta)n_z.
\tag{263.5}
$$

反之，满足这些关系的加速度给出同一个矩阵上界：差矩阵的迹为 $1+\eta>0$，行列式非负，故为半正定。允许方向的全部范围等价于

$$
\eta\le a\le1,\qquad d=\eta/a.
\tag{263.6}
$$

名义点记 $z=z(0)$、$v=z'(0)$。由非负函数 $z(t)+b$ 和 $b-z(t)$ 的标量正性估计，

$$
v^2\le\min\{2d(z+b),\,2a(b-z)\}.
\tag{263.7}
$$

同时反转 $N$ 与 $z(t)$ 不改变状态，所以求上确界时可设 $z\ge0$。对固定 $0\le z<b$，第一项随 $a$ 递减，第二项随 $a$ 递增。无约束的平衡值为

$$
a_z=\sqrt\eta\sqrt{\frac{b+z}{b-z}},\qquad
d_z=\sqrt\eta\sqrt{\frac{b-z}{b+z}}.
\tag{263.8}
$$

其中 $a_z\ge\sqrt\eta\ge\eta$，而 $a_z\le1$ 当且仅当 $z\le bq$。因此，在所有方向上优化（263.7）得到

$$
v^2\le
\begin{cases}
2\sqrt\eta\sqrt{b^2-z^2},&0\le z\le bq,\\
2(b-z),&bq<z\le b.
\end{cases}
\tag{263.9}
$$

在 $z=b$ 时导数为零，也包含于第二式。信息为 $I_Q=v^2/(1/4-z^2)$。第二段对应的比值严格递减，因为

$$
\frac{d}{dz}\frac{b-z}{1/4-z^2}
=-\frac{(z-b)^2+1/4-b^2}{(1/4-z^2)^2}<0.
\tag{263.10}
$$

故只需在 $0\le z\le bq$ 上最大化

$$
R(z)=\frac{2\sqrt\eta\sqrt{b^2-z^2}}{1/4-z^2}.
\tag{263.11}
$$

对 $w=z^2$ 求对数导数，其符号由

$$
-\frac1{2(b^2-w)}+\frac1{1/4-w}
=\frac{2b^2-1/4-w}{2(b^2-w)(1/4-w)}
\tag{263.12}
$$

决定。最大值正好位于（263.2）的 $z_*$，证明上界。

为证明可任意逼近，选取（263.8）在 $z_*$ 上的 $a,d$。若 $\eta<1$，取一个 Pauli 方向满足

$$
n_z=\frac{d-a}{1-\eta};
\tag{263.13}
$$

由 $z_*\le bq$，其绝对值至多为一。若 $\eta=1$，则 $z_*=0$、$a=d=1$，直接取 $N=\sigma_x$。令

$$
v_*^2=2d(z_*+b)=2a(b-z_*).
\tag{263.14}
$$

构造一个在 $[-b,b]$ 之间周期运动的标量函数。上升段从 $z=-b$、$z'=0$ 开始，以加速度 $d$ 到达 $z_*$，此时速度为 $v_*$；继而以加速度 $-a$ 到达 $z=b$ 并停止。下降段从 $b$ 以加速度 $-a$ 到达 $z_*$，再以加速度 $d$ 回到 $-b$ 并停止。各段一阶数据相接，周期为

$$
\mathcal T=2v_*\left(\frac1a+\frac1d\right).
\tag{263.15}
$$

所得 $z^{(0)}$ 为全实轴上的 $C^{1,1}$ 周期函数，值域包含于 $[-b,b]$，弱二阶导数只取 $d$ 和 $-a$。因此

$$
\rho^{(0)}=I/2+z^{(0)}N
\tag{263.16}
$$

保持谱下界 $\alpha I$，并几乎处处满足指定矩阵上界。令名义点位于上升段的加速度切换处，则其中心信息等于

$$
\frac{v_*^2}{1/4-z_*^2}=R(z_*).
\tag{263.17}
$$

用高斯核卷积整条周期曲线。凸平均保留谱下界、迹一和矩阵上界；所有状态仍在同一 Pauli 方向上，所以保持两两对易。有界函数的高斯卷积给出整函数矩阵元。对固定 $\alpha,\eta$，中心状态与一阶导数收敛，而特征值始终至少为 $\alpha$，故信息趋于（263.17）。这证明精确上确界及整函数版本。证毕。

这里是上确界的达到序列；没有要求一条光滑曲线精确取得（263.3）。方向（263.13）可以不同于 $C_\eta$ 的特征方向，把对易比较类限制为与上界矩阵共同对角化会丢失这一自由度。

**推论 263.3（谱下界阈值和两个极限）。** 令

$$
\alpha_c=\frac{1-1/\sqrt2}{2}.
\tag{263.18}
$$

若 $\alpha_c\le\alpha<1/2$，则对所有 $0<\eta\le1$，

$$
F_{\rm com}(\alpha,\eta)
=8(1/2-\alpha)\sqrt\eta.
\tag{263.19}
$$

尤其在第262节的谱下界 $\alpha=1/4$ 下，

$$
F_{\rm com}(1/4,\eta)=2\sqrt\eta.
\tag{263.20}
$$

若 $0<\alpha<\alpha_c$，则对所有充分小的正 $\eta$，

$$
F_{\rm com}(\alpha,\eta)
=\frac{\sqrt\eta}{\sqrt{\alpha(1-\alpha)}}.
\tag{263.21}
$$

对于每个固定 $0<\eta\le1$，另外有

$$
\lim_{\alpha\downarrow0}F_{\rm com}(\alpha,\eta)
=2(1+\eta).
\tag{263.22}
$$

证明。 第一种情形中 $2b^2\le1/4$，故 $z_*=0$，代入（263.3）得到（263.19）。第二种情形中 $\sqrt{2b^2-1/4}<b$，而 $bq\to b$，所以充分小的 $\eta$ 时 $z_*^2=2b^2-1/4$。使用 $1/4-b^2=\alpha(1-\alpha)$ 即得（263.21）。对于固定 $0<\eta<1$，当 $\alpha\downarrow0$，有 $b\to1/2$ 且 $z_*=bq$ 最终成立。代入（263.3）并使用 $1-q^2=4\eta/(1+\eta)^2$，得到（263.22）；当 $\eta=1$ 时，$q=z_*=0$，由（263.3）直接得到对所有 $0<\alpha<1/2$ 均成立的 $F_{\rm com}(\alpha,1)=8b$，故 $\alpha\downarrow0$ 时极限为 $4$。证毕。

式（263.22）恢复了第261节同一满秩上界的无限制对易上确界，但任意固定正 $\alpha$ 下的信息在 $\eta\downarrow0$ 时仍趋于零。因此两个依次取极限的次序不同：

$$
\lim_{\eta\downarrow0}\lim_{\alpha\downarrow0}F_{\rm com}(\alpha,\eta)=2,
\qquad
\lim_{\alpha\downarrow0}\lim_{\eta\downarrow0}F_{\rm com}(\alpha,\eta)=0.
\tag{263.23}
$$

这两个读数把第261节的跳变具体定位到未固定的谱下界。它们不改变第262节在固定谱下界上的非交换阶优势，也没有给出一般非交换类的精确最优系数。全部构造仍属于本节定义的全实轴密度曲线类；原处理器的附加约束没有在此实现。
