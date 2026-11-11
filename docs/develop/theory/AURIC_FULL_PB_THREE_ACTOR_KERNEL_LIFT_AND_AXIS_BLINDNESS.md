# AURIC 三演员核提升与原轴核盲区

本卷的父来源为[《AURIC 全部探针与环境耦合的固定输出延续》](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)，固定读取该文件在提交 `315786a180a8b00f80b76bb4949281b7394137cf` 中的原文。

未另注明卷名的 §§1–31（含 §30A）及其定义、引理、定理和编号公式均指上述钉版父卷；§§32–33 及其定义、引理、定理和编号公式均指本卷。显式点名的外部卷及其递归钉版来源范围保持原文解释。

下列入口承接正文中保留的父卷锚链接，均读取上述钉版父来源。

<a id="6-完整原问题与七项物理合同的精确身份"></a>
父卷 [§6：完整原问题与七项物理合同的精确身份](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#6-完整原问题与七项物理合同的精确身份)。

<a id="30a5-准确的前件删除来源与完整目标"></a>
父卷 [§30A.5：准确的前件删除、来源与完整目标](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30a5-准确的前件删除来源与完整目标)。

## 32. 三演员的实际离面核提升与三格支撑下的 PB 单独刚性

本节证明两项新的纸面结果：两坐标齐次核向原第三坐标提升的准确可解条件，以及原零模像在三格均有支撑时的全部对角残量分离。后一结果包含每条生成元三坐标均非零的原秩一像线；这样的像线与三个坐标二平面都只有零交，故这里不能以平面压缩或平面内零模像替代。原问题要求任意非零零模像，本节没有完成这一整个量词：包含于某个坐标二平面的像仍有未付分支，见 §32.6。这里的“三格支撑”是所证子类的明确边界，不是完整问题的新成功标准。

### 32.1 三维原类型与结论的准确范围

**定义 32.1（同一原环境中的三演员输入）。** 令 $m\ge0$ 任意有限，取

$$
\begin{gathered}
A=M_{m+3}(\mathbb C),\qquad \mathcal H=\mathbb C^3\oplus\mathbb C^m,
\qquad P=I_3\oplus0_m,\\
C=\operatorname{diag}(c_1,c_2,c_3)=\operatorname{diag}(1,2,3),
\qquad c=C\oplus0_m,\\
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix}=t^*,
\qquad S=\operatorname{diag}(s_1,s_2,s_3),\quad s_j\in\mathbb R,
\qquad s=S\oplus0_m .
\end{gathered}
\tag{32.1}
$$

$B,D_{\rm env}$ 任意 Hermitian，$V$ 任意。每次分别固定 $\sigma\in\{1,-1\}$，置 $\iota=\sigma i$、$K_\sigma(a,b)=\iota[a,b]/2$、$g=K_\sigma(c,t)+s$。对每个原 $x=x^*=PxP$，在完整原代数中定义

$$
\begin{gathered}
a\circ b=(ab+ba)/2,\qquad h=K_\sigma(c,x),\quad r=c\circ x,
\quad k_t=c\circ t,\\
R_\delta=x+\delta(h-k_t),\qquad S_\delta=t+\delta(r+g),
\quad \delta\in\{1,-1\},\\
L=-2x\circ(h-k_t)-2t\circ(r+g),\\
B_\phi(U,Z)=\phi(U^2)\phi(Z^2)-\phi(U\circ Z)^2 .
\end{gathered}
\tag{32.2}
$$

原 PB 仍是同一个探针、同一个完整原代数正复线性泛函上的

$$
|\phi(L)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{32.3}
$$

令 $N=\ker D_{\rm env}$、$W=V|_N$、$\mathcal W=\operatorname{ran}W$、$N_1=N\ominus\ker W$，并取原逆 $J=(W|_{N_1})^{-1}:\mathcal W\to N_1$。这是定义 17.1 的同一有限维逆构造，演员维数在这里改为三；不调用该定理的两演员维数界或把其六维截面当作三演员定理。特别 $VJw=w$、$D_{\rm env}Jw=0$，所有环境条目保持原值。

称 $\mathcal W$ **在三格均有支撑**，若

$$
\exists\omega\in\mathcal W:\qquad \omega_1\omega_2\omega_3\ne0.
\tag{32.4}
$$

等价地，$\mathcal W$ 不包含于任何一个坐标二平面。一个方向直接成立；反方向可取 $\mathcal W$ 的任意复基，把三个坐标限制写成三个非零复线性多项式。它们的乘积是非零多项式，在无限域 $\mathbb C$ 上不恒为零，故存在三个坐标均非零的原线性组合。这只在原像内选向量，不增加新的环境像。

**定理 32.3（三格支撑子类的三残量刚性）。** 对满足 (32.4) 的每份 (32.1)，每个分别固定的 $\sigma$，全部原 Hermitian 角探针和全部原正复线性泛函满足 (32.3)，当且仅当 $S=0$。对任一指定 $0<\mu<\infty$，只量化 $\phi(I_{m+3})=\mu$ 也得到同一结论。任意非零 $S$、任意这样的 $\mu$，都存在原同一环境中的一个有限实际角探针和一个质量恰为 $\mu$ 的原向量泛函，使两笔预算同时严格正且 (32.3) 严格失败。不假设 P2、平衡残量、环境可逆、$W$ 的秩条件或未知总响应映射。

证明分为下面的实际离面提升、四条分离读取及原空间有限运输。定理编号 32.3 的证明在 §32.5 结束；引理 32.2 是其中所用离面结构的独立准确表述。

### 32.2 两个比例关系的准确离面可解条件

固定单位 $u\in\mathbb C^3$，其支撑恰为两格 $a,b$，$u_a u_b\ne0$，记 $A_0=c_a$、$B_0=c_b$，$A_0\ne B_0$。本小节的 $a,b$ 是坐标指标，$A_0,B_0$ 是谱值。给定一个该平面上的 Hermitian 块 $X^{ab}$ 和原向量 $w\in\mathcal W$。假设平面上的两份作用列已经满足

$$
\begin{aligned}
\mathsf R_\delta&=Xu+\frac\delta2\bigl(\iota(CXu-XCu)-Cw\bigr),\\
\mathsf S_\delta&=w+\frac\delta2\bigl(CXu+XCu+\iota Cw\bigr),\\
\mathsf S_\delta&=\zeta_\delta\mathsf R_\delta,\qquad
\zeta_\delta=\beta_\delta-\delta\iota\alpha_\delta,
\quad \alpha_\delta>0,\quad\beta_\delta\in\mathbb R.
\end{aligned}
\tag{32.5}
$$

假设的意思只是把前三式限制到 $a,b$ 两坐标，并以 $X^{ab}$ 计算这两行；尚未假定第三行存在。所有斜率均有限。令 $j$ 为剩余坐标、$d=c_j$。若记待定的第三行作用值为 $p_j=(Xu)_j$、$q_j=(XCu)_j$，则它们须且只须满足

$$
\begin{pmatrix}a_+&b_+\\a_-&b_-\end{pmatrix}
\begin{pmatrix}p_j\\q_j\end{pmatrix}
=-w_j\begin{pmatrix}d_+\\d_-\end{pmatrix},\qquad
\begin{cases}
a_\delta=d(1-\iota\zeta_\delta)-2\delta\zeta_\delta,\\
b_\delta=1+\iota\zeta_\delta,\\
d_\delta=2\delta+d(\iota+\zeta_\delta).
\end{cases}
\tag{32.6}
$$

**引理 32.2（原离面行的准确提升）。** 置

$$
\Delta_d=a_+b_--a_-b_+
=-2\bigl[\zeta_++\zeta_-+
 \iota d(\zeta_+-\zeta_-)+2\iota\zeta_+\zeta_-\bigr].
\tag{32.7}
$$

保持已定 $X^{ab}$、原 $u$、原 $w$ 和两份斜率不变，存在 Hermitian $X\in M_3(\mathbb C)$ 满足完整 (32.5)，准确当且仅当

$$
\Delta_d\ne0\qquad\text{或}\qquad w_j=0.
\tag{32.8}
$$

$\Delta_d\ne0$ 时，两个离面作用值唯一，离面行由它们唯一确定，第三个对角元可任取实数。$\Delta_d=0$ 且 $w_j=0$ 时，可以取两个作用值均为零。$\Delta_d=0$ 且 $w_j\ne0$ 时，不存在这样的提升。

证明。将 $\mathsf S_\delta-\zeta_\delta\mathsf R_\delta=0$ 的第 $j$ 行乘以 $2\delta$ 就得到 (32.6)。其行列式展开为 (32.7)，没有更换演员基。

先检查奇异处是否可能还容纳非零 $w_j$。对任意单坐标解，置 $r_j=w_j-\iota p_j$，直接从原两列得

$$
\mathsf S_{\delta,j}-\iota\mathsf R_{\delta,j}
=(1+\delta\iota d)r_j.
\tag{32.9}
$$

$\zeta_+\ne\iota$，因为其相对于 $\iota$ 的虚部为 $-\alpha_+<0$。若 $\zeta_-=\iota$，则 $b_-=0$、$a_-=2(d+\iota)$；又 $b_+=1+\alpha_++\iota\beta_+\ne0$，故 $\Delta_d=-2(d+\iota)b_+\ne0$。这个允许的特殊斜率不产生奇异例外。

其余情形定义

$$
\gamma_\delta=(\zeta_\delta-\iota)^{-1},\qquad
\gamma=(\gamma_++\gamma_-)/2,\qquad
\eta=(\gamma_+-\gamma_-)/2.
$$

由 (32.9)，全部单坐标解准确为

$$
\begin{aligned}
p_j&=(\gamma+\iota\eta d)r_j,\\
q_j&=\bigl(2\iota\eta+(\iota-2\gamma)d\bigr)r_j,\\
w_j&=(1+\iota\gamma-\eta d)r_j.
\end{aligned}
\tag{32.10}
$$

确实，两份 $\mathsf R_{\delta,j}$ 等于
$(\gamma+\delta\eta)(1+\delta\iota d)r_j$；相加给 $p_j$，相减及 $w_j=r_j+\iota p_j$ 给另两式。反过来代回就给两份核等式，故这不是只有必要性的参数式。

若 $f=1+\iota\gamma-\eta d\ne0$，每个指定 $w_j$ 都有唯一 $r_j=w_j/f$ 及唯一 $p_j,q_j$，故系数矩阵可逆。若 $f=0$，每个解都满足 $w_j=0$，而任取非零 $r_j$ 时 $p_j=\iota r_j\ne0$，给出非零齐次解，故系数矩阵奇异。这证明 $\Delta_d=0$ 恰对应 $f=0$，并证明 (32.8) 的全部奇异分支。这里没有把奇异值域条件删掉。

最后补出 Hermitian 矩阵。对于任一已取得的 $p_j,q_j$，取

$$
X_{ja}=\frac{B_0p_j-q_j}{(B_0-A_0)u_a},\qquad
X_{jb}=\frac{q_j-A_0p_j}{(B_0-A_0)u_b},\qquad
X_{aj}=\overline{X_{ja}},\quad X_{bj}=\overline{X_{jb}},\quad X_{jj}\in\mathbb R.
\tag{32.11}
$$

两项分母均非零。这两行线性方程直接给 $(Xu)_j=p_j$、$(XCu)_j=q_j$。因为 $u_j=(Cu)_j=0$，补上的共轭条目不会改变 $a,b$ 两行的 $Xu,XCu$；已定平面块的 Hermitian 性与新增的共轭配对共同保证整个 $X=X^*$。所以这是同一完整三维探针的插值，不是重新指定两份彼此无关的作用列。∎

这个引理不适用于仅有一个非零坐标的 $u$：此时 (32.11) 的两项插值数据不独立。它也不把 $w$ 的投影认作原 $\mathcal W$ 中的向量；输入始终是原 $w$，其第三分量出现在 (32.6) 的右端。

### 32.3 同一原像上的显式秩一核族

以下构造直接在三维中完成 Hermitian 插值，也明确避开引理 32.2 的奇异行列式。取同一个满足 (32.4) 的原 $\omega$。选两个坐标 $a,b$，其谱值记为 $A_0<B_0$，并选实数 $T>1$、$T\ne2$。令

$$
\begin{gathered}
\kappa=-\iota T,\qquad
p_j=\frac{2+\kappa c_j}{\iota(\kappa c_j-\kappa^2-2)}\,\omega_j
\quad(j=1,2,3),\qquad X=pp^*,\\
v_a=\frac{B_0-\kappa}{B_0-A_0},\qquad
v_b=\frac{\kappa-A_0}{B_0-A_0},\\
(u_0)_a=\frac{v_a}{\overline{p_a}},\qquad
(u_0)_b=\frac{v_b}{\overline{p_b}},\qquad
(u_0)_j=0\quad(j\notin\{a,b\}),\\
\nu=\|u_0\|>0,\qquad u=u_0/\nu,\qquad w=\omega/\nu,\\
\zeta_\delta=-\iota+\delta\kappa,\qquad
\alpha_+=1+T,\quad\alpha_-=T-1,\quad\beta_+=\beta_-=0.
\end{gathered}
\tag{32.12}
$$

这里没有数值选根：$\kappa c_j-\kappa^2-2=T^2-2-\iota T c_j$，其虚部非零；$2+\kappa c_j=2-\iota T c_j$ 也非零。$p_a,p_b$ 因原 $\omega_a,\omega_b\ne0$ 而非零，$v_a,v_b$ 均非零，故 $u_a u_b\ne0$、$\nu>0$，所有量有限。$X=pp^*$ 明确 Hermitian。由

$$
v_a+v_b=1,\qquad A_0v_a+B_0v_b=\kappa
$$

直接得同一探针的两份作用

$$
p^*u_0=1,\qquad p^*Cu_0=\kappa,\qquad
Xu_0=p,\qquad XCu_0=\kappa p .
\tag{32.13}
$$

未选的坐标也保留 $p_j$ 的实际值，故离面行一般非零。

验证两个比例。将 (32.5) 的两列同乘 $\nu$，用 (32.13) 得

$$
\begin{aligned}
\nu\mathsf R_\delta
 &=p+\frac\delta2\bigl(\iota(C-\kappa I)p-C\omega\bigr),\\
\nu\mathsf S_\delta
 &=\omega+\frac\delta2\bigl((C+\kappa I)p+\iota C\omega\bigr).
\end{aligned}
$$

在 $\nu(\mathsf S_\delta-\zeta_\delta\mathsf R_\delta)$ 中，$\delta$ 的系数为

$$
\tfrac12((C+\kappa I)p+\iota C\omega)-\kappa p
+\tfrac\iota2\bigl(\iota(C-\kappa I)p-C\omega\bigr)=0;
$$

常数项为

$$
\tfrac12\bigl((2I+\kappa C)\omega+
 \iota((\kappa^2+2)I-\kappa C)p\bigr)=0,
\tag{32.14}
$$

最后一式逐坐标正是 (32.12) 对 $p_j$ 的定义。因此完整三行同时满足 (32.5)，不是只在所选二平面上成立。两份 $\alpha$ 严格正，斜率的虚部方向完全符合 (32.5)。引理 32.2 中这族斜率的离面行列式为

$$
\Delta_d=-4\iota(d\kappa-\kappa^2-2)
=-4\iota(T^2-2-\iota Td)\ne0
\quad(d\in\{1,2,3\}).
\tag{32.15}
$$

这给出了精确的非奇异性，也解释了为何原 $\omega$ 的离面分量可以被实际探针接住。

### 32.4 两种权重在两个谱边上的三残量分离

对 (32.12) 的核对，计算整个残量的实际配对

$$
F_{ab,T}(S)=\operatorname{Re}\bigl((w-\iota Xu)^*Su\bigr).
$$

$u$ 的未选坐标分量为零，只使本次读取不含该格残量，没有删掉该格的作用像。由 (32.13)，

$$
F_{ab,T}(S)=\nu^{-2}\sum_{j\in\{a,b\}}
 s_j\operatorname{Re}\left(\frac{\iota(\overline\kappa^2+4)}
                                  {2+\overline\kappa c_j}\,v_j\right).
\tag{32.16}
$$

所用比值恒等式是
$\overline{\omega_j/p_j}+\iota
=\iota(\overline\kappa^2+4)/(2+\overline\kappa c_j)$。
它消去原像的复相位，没有共轭或更换 $V,D_{\rm env}$。

代入 $\overline\kappa=\iota T$，有

$$
\boxed{\quad
F_{ab,T}(S)=\frac{T(4-T^2)(A_0B_0-2)}
                  {(B_0-A_0)\nu^2}
 \left(\frac{s_a}{4+T^2A_0^2}-\frac{s_b}{4+T^2B_0^2}\right).
\quad}
\tag{32.17}
$$

逐项的实部为

$$
\operatorname{Re}\frac{\iota(B_0+\iota T)}{2+\iota TA_0}
=\frac{T(A_0B_0-2)}{4+T^2A_0^2},\qquad
\operatorname{Re}\frac{\iota(-A_0-\iota T)}{2+\iota TB_0}
=-\frac{T(A_0B_0-2)}{4+T^2B_0^2};
$$

再乘 $(4-T^2)/(B_0-A_0)$ 与 $\nu^{-2}$ 即得 (32.17)。

只选谱边 $(1,3)$ 与 $(2,3)$，每边取 $T=3,4$。这两边均满足 $A_0B_0\ne2$，所以 (32.17) 的前因子非零。若同一边的两条读取均为零，则

$$
\frac{s_a}{4+9A_0^2}=\frac{s_b}{4+9B_0^2},\qquad
\frac{s_a}{4+16A_0^2}=\frac{s_b}{4+16B_0^2}.
\tag{32.18}
$$

交叉乘积的差为

$$
(4+9A_0^2)(4+16B_0^2)
 -(4+16A_0^2)(4+9B_0^2)=28(B_0^2-A_0^2)>0,
\tag{32.19}
$$

故 $s_a=s_b=0$。边 $(1,3)$ 读出 $s_1=s_3=0$，边 $(2,3)$ 读出 $s_2=s_3=0$。因此这四条原核读取分离整个 $\mathbb R^3$ 残量：任意非零 $S$ 至少有一条 $F_{ab,T}(S)\ne0$。四次均使用同一个原 $\omega$，各次有自己的 $u,X,\nu$；全称 PB 允许这些不同探针和泛函，不要求把不同次读取拼成同一次预算。

这不是将旧 $(1,2)$ 证明的谱值改名：本族在 $A_0B_0=2$ 时 (32.17) 恰为零，不能支付旧两演员定理。定理 30A.2 的两条已付读取不在这里重证，也没有被视作任意谱比的定理。新的分离实际使用了另两条谱边和三维原像的全部分量。

### 32.5 回到同一完整环境的有限严格违反

下面直接沿原作用列运输，不需要假定两演员系数矩阵在三维自动成立。取 §32.4 的一个 $F=F_{ab,T}(S)\ne0$ 的核对，令 $y=Jw$。对实数 $q$ 定义同一环境中的

$$
x_q=qX\oplus0_m,\qquad \xi_q=(u,qy),\qquad
\ell_S(q)=\phi_{\xi_q}(L(x_q)),\qquad
\phi_\xi(a)=\xi^*a\xi.
\tag{32.20}
$$

在本小节，原 $S_\delta$ 的下标再加 $0$ 表示仅把残量置零，其余原输入保持不变。由 $Vy=w$、$D_{\rm env}y=0$，完整原矩阵乘法给

$$
\begin{aligned}
R_\delta(x_q)\xi_q
 &=q(\mathsf R_\delta,0)
   +\bigl(-\delta(C\circ B)u,-\delta V^*Cu/2\bigr),\\
S_{\delta,0}(x_q)\xi_q
 &=q(\mathsf S_\delta,0)
   +\bigl((B+\delta\iota[C,B]/2)u,
           V^*(I-\delta\iota C/2)u\bigr),\\
S_{\delta,S}(x_q)\xi_q
 &=S_{\delta,0}(x_q)\xi_q+\delta(Su,0),\\
t\xi_q&=(Bu+qw,V^*u),\\
\ell_S(q)&=\ell_0(q)-2\operatorname{Re}\bigl((t\xi_q)^*(Su,0)\bigr).
\end{aligned}
\tag{32.21}
$$

这里保留了 $B,V^*u,V^*Cu$ 和全部原环境输出。$D_{\rm env}y=0$ 仅是这次选定向量的性质，不是环境可逆性、环境替换或压缩平方假设。

取本核对的有限 $\alpha_\delta,\beta_\delta$，定义有限实二次式

$$
\begin{aligned}
Q_S(q)=\sum_{\delta=\pm1}\bigl[
 &\alpha_\delta\|R_\delta(x_q)\xi_q\|^2\\
 &+\alpha_\delta^{-1}
   \|S_{\delta,S}(x_q)\xi_q-\beta_\delta R_\delta(x_q)\xi_q\|^2\bigr]
 -2\ell_S(q).
\end{aligned}
\tag{32.22}
$$

§1 的标准零残量换位恒等式对任意自伴 $c,x,t$ 都成立，不要求演员为两维。它与 §§27–28 的同一复 Gram 配方给出

$$
Q_0(q)=\sum_{\delta=\pm1}\alpha_\delta^{-1}
 \|S_{\delta,0}(x_q)\xi_q-\zeta_\delta R_\delta(x_q)\xi_q\|^2.
\tag{32.23}
$$

更具体地，零残量时
$\ell_0(q)=-\sigma\sum_\delta\delta\operatorname{Im}
 ((R_\delta\xi_q)^*S_{\delta,0}\xi_q)$；展开右侧平方的交叉项正好是 $-2\ell_0(q)$。由完整 (32.5)，每个平方内的 $q$ 项为零，所以 $Q_0(q)=Q_0(0)$。这一步使用完整三行比例，不使用两演员判据的外推。

记 $v_S=(Su,0)$，$M_\delta(q)=S_{\delta,0}(x_q)\xi_q-\beta_\delta R_\delta(x_q)\xi_q$。由 (32.21)–(32.22)，

$$
\begin{aligned}
Q_S(q)-Q_0(q)
={}&2\sum_\delta\delta\alpha_\delta^{-1}
       \operatorname{Re}(M_\delta(q)^*v_S)
 +(\alpha_+^{-1}+\alpha_-^{-1})\|v_S\|^2\\
 &+4\operatorname{Re}((t\xi_q)^*v_S).
\end{aligned}
$$

核等式使 $M_\delta(q)$ 的 $q$ 系数为
$-\delta\iota\alpha_\delta(\mathsf R_\delta,0)$，而
$\mathsf R_++\mathsf R_-=2Xu$。故全部线性项准确相加为

$$
Q_S(q)=4q\operatorname{Re}((w-\iota Xu)^*Su)+\Gamma_S
       =4qF+\Gamma_S,\qquad \Gamma_S=Q_S(0)\in\mathbb R.
\tag{32.24}
$$

$\Gamma_S$ 有限，按原向量 $(u,0)$ 和原算子计算；没有漏掉任何环境常数项。它不含 $J$ 的范数，该范数仍保留在下面的实际质量中。这也给出 (30A.5) 在本三维实际类型下的原配对及边框线性式，而非把两维实坐标硬当作三维坐标。

取一个实际有限实数

$$
\Lambda=-\frac{\Gamma_S+1}{4F},\qquad x=x_\Lambda,\qquad
\xi=\xi_\Lambda=(u,\Lambda Jw),\qquad Q_S(\Lambda)=-1 .
\tag{32.25}
$$

§27.2 的成熟实 Gram／算术几何平均下界逐笔用于同一个 $x,\xi$，即得

$$
\phi_\xi(L)
=\tfrac12+\tfrac12\sum_\delta
 \bigl[\alpha_\delta\|R_\delta\xi\|^2
 +\alpha_\delta^{-1}\|S_\delta\xi-\beta_\delta R_\delta\xi\|^2\bigr]
\ge\tfrac12+\sum_\delta\sqrt{B_{\phi_\xi}(R_\delta,S_\delta)}.
\tag{32.26}
$$

这里不要求某个零 Gram 变分下确界取到。两个预算与左端确实使用同一个原向量泛函，所有范数都是原全空间作用像，因而所有平方仍是原 $M_{m+3}(\mathbb C)$ 中的平方。

给定 $0<\mu<\infty$，有 $\|\xi\|^2=1+\Lambda^2\|Jw\|^2\ge1$，故

$$
\xi_\mu=\sqrt\mu\,\xi/\|\xi\|,\qquad
\phi_{\xi_\mu}(I_{m+3})=\mu.
\tag{32.27}
$$

(32.26) 的严格差额至少为 $\mu/(2\|\xi\|^2)>0$。

还须在三演员原类型中支付两笔同时正预算，而不能直接套用定理 27.3 的固定两维常数。令 $J_{ab}=e_{ab}+e_{ba}\in M_3(\mathbb C)$，保持 $\phi=\phi_{\xi_\mu}$ 不变，只作 $x'=x+\lambda(J_{ab}\oplus0_m)$。每份 $B_\phi(R_\delta(x'),S_\delta(x'))$ 都是非负实多项式，次数至多四。演员读取分量为 $z=\sqrt\mu\,u/\|\xi\|$，仍支撑在 $a,b$。最高次作用列分别为

$$
((J_{ab}+\delta H_\sigma(J_{ab}))z,0),\qquad
(\delta(A_0+B_0)J_{ab}z/2,0).
$$

在这个平面上，$\|J_{ab}z\|^2=\|z\|^2$、
$\|H_\sigma(J_{ab})z\|^2=(B_0-A_0)^2\|z\|^2/4$，且这两列的实内积为零。于是每份多项式的四次系数准确为

$$
\frac{(B_0^2-A_0^2)^2}{16}\|z\|^4
=\frac{(B_0^2-A_0^2)^2\mu^2}{16\|\xi\|^4}>0.
\tag{32.28}
$$

故每笔预算的实零点集有限。原 PB 严格差额关于 $\lambda$ 连续，在零严格为正；在这个正开邻域内避开两个有限零点集和零，取一个有限实 $\lambda$，就使两笔预算同时严格正而违反仍在。没有另选泛函、质量或环境。

这证明任意非零 $S$ 的全部所述违反。若 $S=0$，直接复用 §1 在任意自伴 $c,x,t$ 上的标准 $K_\sigma$ 恒等式及全部正泛函的复 Gram／Cauchy–Schwarz，得到全部原 (32.3)，包括混合正泛函。必要性已有原向量泛函见证，所以不需要借两演员读取截面作三维全正泛函提升。质量零的正泛函只有零泛函，仍给零等式。所有等式只使用 $\iota^2=-1$、$\overline\iota=-\iota$ 与原复线性数据，因而两个 $\sigma$ 分别成立；$J,B,V,D_{\rm env}$ 始终是原来一份，不作共轭替换。定理 32.3 得证。∎

### 32.6 已消去的前件与仍未支付的整类问题

本节的实质新增内容是 (32.6)–(32.11) 的准确离面可解条件、(32.12)–(32.19) 在同一个真实三格零模像上的四条分离读取，以及它们经 (32.20)–(32.28) 取得原环境中的有限共同泛函正预算违反。一般 Hermitian 插值、二阶线性方程、复 Gram 配方及连续多项式扰动是成熟工具；所证新应用不是通用边框公式或单独的核值域必要条件。非零残量在 (32.4) 的整个子类中已被实际 PB 违反排除；零残量的全 PB 充分性另由 §1 支付，未把“核配对为零”当作 PB 充分性。

在这个明确子类中，P2 不再是固定输出刚性的独立前件：PB 先给 $S=0$，标准 $K_\sigma$ 再给全正 P2。若另已辨识 $g=D(c,t)$，则只对这一原输入对得到 $c\circ t-iD(c,t)$ 等于 $\sigma=1$ 时的 $ct$、$\sigma=-1$ 时的 $tc$。这不从完整 $\mathsf H_A(D)$ 中删除 A1/P2，也不删除承载卷定义 41.1 从两份实际外层 P2 导出显式预算的桥；不把完整 H／总 D 分类当作本节前件。

**准确未决域。** 原问题仍要求每个 $\mathcal W\ne0$，而 (32.4) 失败准确是 $\mathcal W$ 包含于某个坐标二平面。例如 $\mathbb C(1,1,0)^\mathsf T$、$\mathbb C e_1$、$\mathbb C e_3$ 都不在定理 32.3 的域中。对这些像，(32.12) 在缺失坐标上不能定义所需的 $u_0$；引理 32.2 只在已有双非零坐标 $u$ 的前提下提升，不把一个轴读取自动变成横向读取。它还准确指出 $\Delta_d=0,w_j\ne0$ 时这条提升确实不可能。需另构造分离缺失坐标的合法共同核读取，或直接判定剩余原 Schur 不等式；只证明所有核配对为零仍不够。这里未给任何非零 $S$ 的全 PB 模型，也未证明这些例子是反模型。原三演员全非零像问题和完整 Omega 成功标准均保持未解。两演员定理 30A.2、原 $W=0$ 三矩结果 §30 及全部既有域均保持各自类型，不能因二演员结论而省去这份缺失坐标义务。

成熟归属沿 §§1、5、17、27–30A：复 Gram／Cauchy–Schwarz 与正泛函背景见已引 Blackadar 的 [*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；Hermitian 矩阵、行列式和有限维插值使用 Horn–Johnson，*Matrix Analysis* 的标准线性代数。核与像的广义 Schur 背景沿 Higham 的 [Generalized Schur Complement，Theorem 1](https://nhigham.com/2023/06/01/what-is-the-schur-complement-of-a-matrix/) 和 Penrose 的 [*A generalized inverse for matrices*](https://doi.org/10.1017/S0305004100030401)。本节实际承重等式均已列出；这些成熟来源不被归为本节特定三维核族的作者。这里标为仓内综合推导，不主张历史原创、文献穷尽、物理来源已构造或 Lean／kernel 核验。

完整来源逐字沿 [§6](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标) 的同一递归钉版全文与七项消费者；这些链接是完整合同的保留，不以本段摘要替代。原全部准备、事件、过程、参考／副本、真正相关联合、零／不等／次归一质量、物理钟、单位、控制、parent／ready／flags、完整记录、失败、拒绝、停止、销毁、泄漏、真遗忘、两侧与逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口及每份完整输出的所有合法未来都保留。数学 $u,\xi,x$ 不生产准备、菜单、复制或相干控制；不借旧 Born／CP／QC、密度或历史身份倒推来源。

[C139 固定源卷 §§50–73](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 已得的合法前接、唯一正回溯、下降、固定返回刚性、条件过程比较和整台递归参考及累计支持继续按原域使用；[C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 的同一旧 $D$ 恢复及其消费者继续保留。[有限返回续卷 §162](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的完整原根候选和七项合同，以及 [§164](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 对候选查询返回与原活动接头的区别，各守已付域；没有把它们倒称缺失，也没有把另增服务的候选当作原 $B_{r_\star}$ 的活动返回。

原分析器仍须为字面旧程序 $\tau;T_P$ 的指定接受族，在全部原准备、中间切口、参考／副本、合法分析词和树、原坐标、固定支持全质量和完整菜单上，供应到同一原实际完整菜单及接受端的准备无关准确关联，保持原支持与未归一标尺；C139 §23.3 式 (23.7) 的实际证书不由本节矩阵产生。CountRead 仍须同一接受叶完整活动输出、实际读后活动 ready、第一合法消费者，以及读后同一完整活动输入对全部合法未来的真实 Return；有限返回卷 §164.1 的原活动接头、全参考／控制／钟与旧未来对应仍须由来源构造。复 Hilbert／相干、Born／全菜单、实际张量联合、typed CP／Kraus、完整仪器／TP／更新／Lüders、全部历史／Return、Hamiltonian／物理钟／共同正作用量七项均仅在原完整合同成立时消费。本节没有支付这些来源，完整量子起源仍未完成。

### 32.7 中文直观：同一连线上的两把尺与三维插值

二元关系在这里是固定输入对 $(c,t)$ 与它的输出 $g$：对角误差 $S$ 表示输出偏离标准换位关系多少。反过来问误差不为零会怎样，就要找同一个探针和同一个读取，使两笔预算同时不够。不能把两间房间各自最省的预算拼在一起，也不能把第三根连线剪掉后重算平方。

先在两格放一个两边都非零的读取方向。探针必须同时决定“作用在这个方向上”和“作用在按 $c$ 加权后的方向上”。这两个方向独立，所以第三行的两个条目可以准确接住第三格的两份作用值；两行比例方程的行列式决定它们是否存在。行列式为零而原第三格连线非零时，这条路确实堵住。引理把这道门写成了准确条件，没有用维数直觉冒充相容性。

对一条真实连到三格的零模像，本节选出的秩一探针直接把三根连线全部保留。在谱边 $1$–$3$ 上换两种有限权重，两个误差无法在两把尺上同时抵消；再在谱边 $2$–$3$ 上做同样两次，三格误差便全部消失。图形上是三点用两条相接的边连起来，每条边各有两把不成比例的尺；它们背后始终是同一条原环境连线，第三格的实际作用由完整探针负责。

一旦某把尺读出非零误差，就沿这条合法方向取一个有限尺度。标准部分的二次代价在两份比例关系上相消，误差却留下带符号的一次项，于是同一个原环境向量给严格违反；最后只轻微改探针，便让两笔面积都为正。环境再复杂也只改变所需有限尺度和质量归一化，不需要把环境换小。这里省去的是三格都有原支撑这批输入中额外的固定 P2 前件。原连线缺一格时仍需新的横向读取；原装置能否执行指定菜单、读后是否真的 ready、完整活动输入能否对所有合法未来返回，更仍是原世界必须供应的关系。

## 新增锚（本行以下为后续增补区）

## 33. 原轴零模像上的全称核盲区与完整 PB 分类的必要路线

### 33.1 原类型、有限合法核对与结论

保持定义 32.1 的同一完整原输入、(32.2) 的全部乘积和原 PB (32.3)，特别
$C=\operatorname{diag}(1,2,3)$，$B,D_{\rm env}$ 任意 Hermitian，$V$ 任意，$\mathcal W=V(\ker D_{\rm env})$。以下分别固定一个 $\sigma\in\{1,-1\}$，置 $\iota=\sigma i$。不假设 P2，也不改环境或把原平方换成演员压缩平方。

**定义 33.1（完整有限合法同时核对）。** 取单位 $u\in\mathbb C^3$、$X=X^*\in M_3(\mathbb C)$、实际 $w\in\mathcal W$，记

$$
\begin{gathered}
p=Xu,\qquad q=XCu,\qquad v=w-\iota p,\\
\mathsf R_\delta=p+\frac\delta2\bigl(\iota(Cp-q)-Cw\bigr),\qquad
\mathsf S_\delta=w+\frac\delta2\bigl(Cp+q+\iota Cw\bigr),\\
\zeta_\delta=\beta_\delta-\delta\iota\alpha_\delta,
\qquad 0<\alpha_\delta<\infty,\quad\beta_\delta\in\mathbb R,\\
\mathsf S_\delta=\zeta_\delta\mathsf R_\delta\quad(\delta=+1,-1),
\qquad F(S)=\operatorname{Re}(v^*Su).
\end{gathered}
\tag{33.1}
$$

两份比例均须在全部三坐标成立。这是 (32.5) 的完整核关系，不是分别投影后的关系；$X$ 必须同时实现 $Xu$ 与 $XCu$。

**定理 33.2（两条原轴像对第三格的全称核盲区）。** 若 $\mathcal W=\mathbb C e_1$ 或 $\mathcal W=\mathbb C e_2$，则对每一个 (33.1) 的完整有限合法同时核对，均有

$$
\boxed{\quad
F(E_{33})=\operatorname{Re}(\overline{v_3}u_3)
=\operatorname{Re}\bigl(\overline{(w-\iota Xu)_3}u_3\bigr)=0.
\quad}
\tag{33.2}
$$

$u$ 可以有任意额外坐标支撑，$w=0$、$v=0$、特殊斜率 $\zeta_-=\iota$ 和所有退化对角插值系数均在量词内。结论对两个 $\sigma$ 分别成立。它反驳的是“每个非零实际像都能用这些完整合法核读取分离全部对角残量”的全称主张；没有断言 $S=E_{33}$ 或任一非零倍数满足全部原 PB。

### 33.2 逆斜率参数、全部坐标分支与零向量

从 (33.1) 直接相减，得到与 (32.9) 相同的完整向量恒等式

$$
\mathsf S_\delta-\iota\mathsf R_\delta
=(I+\delta\iota C)v.
\tag{33.3}
$$

合法性保证 $\zeta_+\ne\iota$。若 $\zeta_-=\iota$，则 $(I-\iota C)v=0$。其三个对角元 $1-\iota c_j$ 全部非零，故 $v=0$，已得 (33.2)。这一分支的全部作用列还满足

$$
p=-\iota w,\qquad \mathsf R_+=0,\qquad q=-2w.
\tag{33.4}
$$

其中 $\mathsf R_+=0$ 来自 $\zeta_+\ne\iota$ 及 (33.3)，再代回 $\mathsf R_+$ 就给最后一式；没有对 $\zeta_--\iota$ 作除法。

其余情形置

$$
\gamma_\delta=(\zeta_\delta-\iota)^{-1},\qquad
\gamma=(\gamma_++\gamma_-)/2,\qquad
\eta=(\gamma_+-\gamma_-)/2,
\qquad D(d)=1+\iota\gamma-\eta d.
\tag{33.5}
$$

每个 $\gamma_\delta$ 有限且非零，故
$\gamma^2-\eta^2=\gamma_+\gamma_-\ne0$。由
$\mathsf R_\delta=(\gamma+\delta\eta)(I+\delta\iota C)v$
的和、差，准确得到

$$
\boxed{
\begin{aligned}
p&=(\gamma I+\iota\eta C)v,\\
q&=\bigl(2\iota\eta I+(\iota-2\gamma)C\bigr)v,\\
w&=\bigl((1+\iota\gamma)I-\eta C\bigr)v.
\end{aligned}}
\tag{33.6}
$$

反代亦给两份完整核等式，所以它们是准确参数式。具体地，对任一谱值 $d$，(32.6) 的行列式在这些参数下为

$$
\Delta_d=-\frac{4\iota D(d)}{\gamma^2-\eta^2}.
\tag{33.7}
$$

因此 $D(d)\ne0$ 时 $v_j=w_j/D(d)$ 唯一；$D(d)=0,w_j\ne0$ 时无解；$D(d)=w_j=0$ 时 $v_j$ 可任取，随后由 (33.6) 决定 $p_j,q_j$。后两种分支不使用 $D(d)^{-1}$。这也是 (32.8)–(32.10) 的同一退化分类。

先处理 $w=0$。若 $D$ 在两个不同谱值上同时为零，则 $\eta=0$、$\gamma=\iota$，从而 $\gamma_+=\gamma_-=\iota$、$\zeta_+=\zeta_-=0$，违反严格正的 $\alpha_\pm$。故 $v$ 至多支撑在一格；$v=0$ 时已完成证明。否则 $p=\iota v$，而 $X=X^*$ 给 $u^*p\in\mathbb R$。若唯一非零格为 $j$，则

$$
0=\operatorname{Im}_\iota(u^*p)
=\operatorname{Re}(\overline{u_j}v_j).
\tag{33.8}
$$

这里 $\operatorname{Im}_\iota(A+\iota B)=B$，$A,B\in\mathbb R$。若 $j=3$，(33.8) 即为所求；若 $j\ne3$，则 $v_3=0$。这包括常数 $D$ 无零点时的 $v=0$ 分支。

### 33.3 假设第三格读数非零时的准确 Hermitian 相容性

以下设 $w\ne0$，并反设
$n=\operatorname{Re}(\overline{v_3}u_3)\ne0$。记 $w=w_a e_a$，$a\in\{1,2\}$，$w_a\ne0$；此处指标 $a$ 同时等于谱值 $c_a$。由 $v_3\ne0$、$w_3=0$ 和 (33.6)，必有

$$
\eta=\frac{1+\iota\gamma}{3},\qquad
D(d)=(1+\iota\gamma)(1-d/3).
\tag{33.9}
$$

$w_a=D(a)v_a\ne0$ 强制 $\gamma\ne\iota$ 且 $v_a\ne0$。设 $b$ 是 $1,2$ 中不同于 $a$ 的另一格，则 $D(b)\ne0$，所以
$v_b=p_b=q_b=0$；并未令 $u_b$ 为零。由 (33.6)，对 $d=a,3$ 写

$$
\begin{gathered}
p_d=P_dv_d,\qquad q_d=Q_dv_d,\\
P_d=(1-d/3)\gamma+\iota d/3,
\qquad Q_d=-2(d+1/3)\gamma+\iota(d+2/3),\\
P_3=\iota,\qquad Q_3=(-20\gamma+11\iota)/3.
\end{gathered}
\tag{33.10}
$$

若 $u_a=0$，则 $u^*p=\iota\overline{u_3}v_3\in\mathbb R$ 立即给 $n=0$。故反设下 $u_au_3\ne0$。置

$$
z_a=\overline{u_a}v_a,\qquad z_3=\overline{u_3}v_3,
\qquad \operatorname{Re}z_3=n,
\qquad A_d=3P_d-Q_d,\quad B_d=Q_d-aP_d.
\tag{33.11}
$$

同一个 Hermitian $X$ 给出全部四个实相容条件

$$
u^*p\in\mathbb R,\qquad (Cu)^*q\in\mathbb R,
\qquad u^*q=p^*Cu.
\tag{33.12}
$$

这些条件仅含 $a,3$ 两格的输出，因为 $p_b=q_b=0$，即使 $u_b\ne0$ 亦然。其准确等价形式是

$$
\boxed{\quad
A_a z_a\in\mathbb R,\qquad B_3z_3\in\mathbb R,
\qquad B_a z_a=\overline{A_3z_3}.
\quad}
\tag{33.13}
$$

为核对等价性，令

$$
U_0=\begin{pmatrix}u_a&a u_a\\u_3&3u_3\end{pmatrix},\qquad
Y_0=\begin{pmatrix}p_a&q_a\\p_3&q_3\end{pmatrix}.
$$

$\det U_0=(3-a)u_au_3\ne0$。式 (33.12) 正是 $U_0^*Y_0$ Hermitian，亦即下面的有效插值矩阵 Hermitian：

$$
Y_0U_0^{-1}
=\frac1{3-a}
\begin{pmatrix}
 A_av_a/u_a&B_av_a/u_3\\
 A_3v_3/u_a&B_3v_3/u_3
\end{pmatrix}.
\tag{33.14}
$$

取两个对角元的实性及两个非对角元的共轭关系，即得 (33.13)。式 (33.14) 不声称等于原 $X$ 的主子块，也没有压缩任何 PB 平方。

这些也是指定 $Xu=p,XCu=q$ 的充分相容条件，而不只是必要读数。事实上令 $U=[u,Cu]$、$Y=[p,q]$，则

$$
G=U^*U,\qquad
\det G=\sum_{j<k}(c_j-c_k)^2|u_j|^2|u_k|^2>0.
$$

若 (33.12) 成立，$U^*Y=Y^*U$，则显式矩阵

$$
\widetilde X
=YG^{-1}U^*+UG^{-1}Y^*
 -UG^{-1}(U^*Y)G^{-1}U^*
\tag{33.15}
$$

满足 $\widetilde X=\widetilde X^*$ 及 $\widetilde XU=Y$：后式的第二、三项因 $Y^*U=U^*Y$ 恰好抵消。这交代了任意额外 $u_b$ 的完整插值，而非以平面内读取代替完整原问题。以下只消费其必要方向。

### 33.4 $\operatorname{Re}\gamma\ne0$：完整乘积与负平方

写 $\gamma=x+\iota y$，$x,y\in\mathbb R$。由 (33.10)–(33.11) 直接得到全部插值系数

$$
\begin{aligned}
A_a&=((3a+11)\gamma-2\iota)/3,&
A_3&=(20\gamma-2\iota)/3,\\
B_a&=((a^2-9a-2)\gamma+(-a^2+3a+2)\iota)/3,&
B_3&=(-20\gamma+(11-3a)\iota)/3.
\end{aligned}
\tag{33.16}
$$

先设 $x\ne0$。$a=1$ 时四个 $\gamma$ 系数依次为 $14,20,-10,-20$，$a=2$ 时为 $17,20,-16,-20$，均非零。因此 $A_a,A_3,B_a,B_3$ 均非零。又 $z_a,z_3$ 非零，所以
$\tau_a=A_az_a$、$\tau_3=B_3z_3$ 是非零实数。式 (33.13) 的最后一式给出准确等式

$$
\frac{A_a\overline{B_a}}{A_3\overline{B_3}}
=\frac{\tau_a}{\tau_3}\frac{|B_a|^2}{|A_3|^2}
\in\mathbb R.
\tag{33.17}
$$

全部分母在本分支已证非零。令 $r_\gamma=x^2+y^2$，$N_a=A_a\overline{B_a}$、$M_a=A_3\overline{B_3}$；$M_a$ 的 $B_3$ 仍使用同一个 $a$。逐项乘法给

$$
\begin{aligned}
N_1&=\frac{-140r_\gamma+76y-8}{9}-4\iota x,&
M_1&=\frac{-400r_\gamma+200y-16}{9}-\frac{40}{3}\iota x,\\
N_2&=\frac{-272r_\gamma+100y-8}{9}-4\iota x,&
M_2&=\frac{-400r_\gamma+140y-10}{9}-\frac{20}{3}\iota x.
\end{aligned}
\tag{33.18}
$$

例如 $N_1=(14\gamma-2\iota)(-10\overline\gamma-4\iota)/9$，实部为
$(-140(x^2+y^2)+76y-8)/9$，相对于 $\iota$ 的虚部为 $-4x$；其余三式由 (33.16) 同样直接相乘得到。

由 (33.17)，$N_a=\rho_aM_a$，$\rho_a\in\mathbb R$。比较 (33.18) 的虚部并用 $x\ne0$，强制
$\rho_1=3/10$、$\rho_2=3/5$。但完整差值是

$$
\begin{aligned}
N_1-\frac3{10}M_1
 &=\frac{-20(x^2+y^2)+16y-16/5}{9}
 =-\frac{20}{9}\left(x^2+\left(y-\frac25\right)^2\right),\\
N_2-\frac35M_2
 &=\frac{-32(x^2+y^2)+16y-2}{9}
 =-\frac{32}{9}\left(x^2+\left(y-\frac14\right)^2\right).
\end{aligned}
\tag{33.19}
$$

两者在 $x\ne0$ 时均严格负，不可能等于零。故反设 $n\ne0$ 不能发生在本分支。

### 33.5 纯虚 $\gamma$ 与全部退化对角系数

剩下 $\gamma=\iota y$，$y\in\mathbb R$。不能在此沿用 (33.17)，因为某些对角系数会为零。写

$$
\begin{gathered}
P_a=\iota P,\qquad Q_a=\iota Q,\qquad Q_3=\iota R,\\
P=\frac{(3-a)y+a}{3},\qquad
Q=\frac{3a+2-2(3a+1)y}{3},\qquad
R=\frac{11-20y}{3},\\
z_a=\ell+\iota h,\qquad z_3=n+\iota k,
\qquad \ell,h,n,k\in\mathbb R.
\end{gathered}
\tag{33.20}
$$

式 (33.12) 的完整四个实条件准确变为

$$
\begin{aligned}
P\ell+n&=0,\\
aQ\ell+3Rn&=0,\\
(Q+aP)\ell+(R+3)n&=0,\\
(Q-aP)h+(R-3)k&=0.
\end{aligned}
\tag{33.21}
$$

第三、四式分别来自复等式 $u^*q=p^*Cu$ 的两个实分量；不能只保留某个表中比值。若 $P=0$ 或 $\ell=0$，第一式已给 $n=0$。反设 $n\ne0$ 下，$P\ell\ne0$，前面三式给

$$
n=-P\ell,\qquad aQ=3RP,\qquad Q=(R+3-a)P,
\qquad (3-a)(a-R)P=0.
\tag{33.22}
$$

因 $3-a>0$，必有 $R=a$、$Q=3P$，从而 $y=(11-3a)/20$。这两种候选的全部关键值为

$$
\begin{aligned}
a=1:\quad &y=\frac25,\quad \eta=\frac15,\quad
P=\frac35,\quad Q=\frac35,\quad R=1,\\
&A_a=\frac65\iota,\quad A_3=2\iota,\quad B_a=B_3=0;\\[2mm]
a=2:\quad &y=\frac14,\quad \eta=\frac14,\quad
P=\frac34,\quad Q=\frac32,\quad R=2,\\
&A_a=\frac34\iota,\quad A_3=\iota,\quad B_a=B_3=0.
\end{aligned}
\tag{33.23}
$$

两种候选都违反 (33.22) 的 $Q=3P$：差值 $Q-3P$ 分别为 $-6/5$、$-3/4$。亦可直接使用无除法的 (33.13)：$B_a=0$、$A_3\ne0$ 强制 $z_3=0$，再次与 $n\ne0$ 矛盾。这明确处理了零对角插值系数，而非从非零分支取未经证明的极限。

斜率合法性还给同一候选的独立排除。两份逆斜率及恢复值准确为

$$
\begin{aligned}
a=1:\quad &\gamma+\eta=(1+2\iota)/5,
&&\gamma-\eta=(-1+2\iota)/5,\\
&\zeta_+=\iota+(\gamma+\eta)^{-1}=1-\iota,
&&\zeta_-=\iota+(\gamma-\eta)^{-1}=-1-\iota;\\[1mm]
a=2:\quad &\gamma+\eta=(1+\iota)/4,
&&\gamma-\eta=(-1+\iota)/4,\\
&\zeta_+=\iota+(\gamma+\eta)^{-1}=2-\iota,
&&\zeta_-=\iota+(\gamma-\eta)^{-1}=-2-\iota.
\end{aligned}
\tag{33.24}
$$

这里四个被求逆的数均非零，但两种 $\zeta_-$ 都要求 $\alpha_-=-1$，与合法性矛盾。主证明在 (33.23) 已完成，并不依赖将这些候选误当作实际 Hermitian 核对。结合特殊斜率、$w=0$、$v=0$、任意额外支撑与 $x\ne0$ 分支，定理 33.2 得证。全部计算只用 $\iota^2=-1$ 和 $\overline\iota=-\iota$，故无需共轭替换原输入就分别覆盖两个取向。∎

### 33.6 原非零零模像的具体恒常核方向与未决 Schur 余量

定理 33.2 给出新的路线排除：对这两条原轴像，$S=sE_{33}$、$s\ne0$ 不可能由任何 (33.1) 的有限合法同时核对取得非零 $F(S)$。因此，原三演员整类分类必须处理这些输入的非核方向及完整残余 Schur 正性；“再寻找对所有非零像都成立的完整核分离”在这些轴像上已被定理否定。这不妨碍别的真实 PB 违反机制，也没有反驳定理 32.3 的三格支撑子类结果。§32.6 对一般缺失坐标情形保留的两条路线，在这里已排除完整核分离这一条。

一个保持 $\mathcal W\ne0$ 的实际原族是

$$
m=1,\qquad B=0,\qquad D_{\rm env}=0,\qquad
V=e_1,\qquad S=sE_{33},\quad s\in\mathbb R.
\tag{33.25}
$$

它的完整代数是原 $M_4(\mathbb C)$，$\mathcal W=\mathbb C e_1$，并非旧 $W=0$ 分支。对其任一 (33.1) 核对，取原 $y=Jw$，沿 $x_\lambda=\lambda X\oplus0$、$\xi_\lambda=(u,\lambda y)$ 定义同一完整原 $Q_S(\lambda)$，准确按 (32.22) 保留两笔代价及 $-2\phi_{\xi_\lambda}(L)$。式 (32.21)–(32.24) 的推导只用完整核关系，对这些核对仍成立，故

$$
Q_{sE_{33}}(\lambda)=4\lambda F(sE_{33})+\Gamma_s=\Gamma_s.
\tag{33.26}
$$

常数可直接求出。在 $\lambda=0$、$\xi_0=(u,0)$，原完整作用列为

$$
R_\delta(0)\xi_0=(0,-\delta u_1/2),\qquad
S_{\delta,S}(0)\xi_0
=\bigl(\delta s u_3e_3,(1-\delta\iota/2)u_1\bigr).
\tag{33.27}
$$

零残量配方 (32.23) 在此给出环境平方；新增演员列与它正交，且
$\operatorname{Re}((t\xi_0)^*(Su,0))=0$。因此完整常数准确为

$$
\boxed{\quad
\Gamma_s=(\alpha_+^{-1}+\alpha_-^{-1})s^2|u_3|^2
+|u_1|^2\sum_{\delta=\pm1}\alpha_\delta^{-1}
 \left|1+\frac\delta2(\zeta_\delta-\iota)\right|^2
\ge0.
\quad}
\tag{33.28}
$$

式 (33.26)–(33.28) 只判定这些核方向上的同一带符号代价，不是 (33.25) 的全部 PB 证明。非核探针、任意原环境向量、全部正泛函以及 PB 绝对值的两侧仍须同时满足。

确切地，任何完整实系数消元所得的二次式
$z^{\mathsf T}Az+2b^{\mathsf T}z+\Gamma$ 对所有 $z$ 非负，要求

$$
A\succeq0,\qquad b\in\operatorname{ran}A,\qquad
\Gamma-b^{\mathsf T}A^\dagger b\ge0.
\tag{33.29}
$$

核方向先强制 $b\perp\ker A$；即使这一像条件另已完全证明，仍须第三式，因为配方为
$(z+A^\dagger b)^{\mathsf T}A(z+A^\dagger b)+\Gamma-b^{\mathsf T}A^\dagger b$。
定理 33.2 不支付其余系数，也没有把某一部分核方向的零读取说成全部像条件。这里未证明任何非零 $s$ 在 (33.25) 上满足全部原 PB，也未给出排除其每个非零 $s$ 的非核严格见证；原“所有非零 $\mathcal W$ 的 PB 单独刚性”保持未决。

### 33.7 中文意义、原来源与成果边界

核关系要求同一探针对两个输入方向产生两对复比例，两笔正预算又要求比例的虚部方向相反。原连线只落在第一格或第二格时，若还想在第三格读出非零残量，完整三行方程会先把所有可能输出压到这条轴与第三格。读取方向可以另有支撑，但同一个 Hermitian 探针的四个实相容条件不会因此减少。复参数有非零实部时，相容性留下严格负平方；纯虚时，零对角系数必须直接处理，剩下的候选也互相矛盾。第三格残量因此被这一整类合法核读取共同漏掉。这是对方法能力的准确否定，不是说残量已经通过全部物理预算。

与三格支撑情形相比，研究路线在这里发生实质区别：三格实际像可以由 §32 的四条核读取排除非零残量；这两条原轴像不能照搬，必须检验非核代价和完整 Schur 余量，才能决定非零残量究竟被 PB 排除还是确实存在全 PB 模型。$B=D_{\rm env}=0,V=e_1$ 的例子只把这种差别具体化，没有把原全称目标改成一个已完成的小目标。

Hermitian 插值、复 Gram 配方与广义 Schur 的成熟背景沿 §32.6 的已有来源；本节具体轴像等式与障碍是仓内手推综合结果，不主张文献穷尽、历史新颖性、Lean／kernel 核验、完整量子公理、全局最小性或完整量子起源完成。

完整原 Omega、同一递归钉版来源和七项消费者仍逐字沿 [§6](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标)、§32.6 保留；链接不以本段摘要替代原合同。全部原准备、事件、过程、参考／副本、真正相关联合、零／不等／次归一质量、钟与单位、控制、parent／ready／flags、完整记录、失败、拒绝、停止、销毁、泄漏、真遗忘、两侧及逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口与所有合法未来均不缩小。C139 固定来源 §§50–73 的下降、参考、递归支持等既得结果，C128 §§385–392 的同一原 $D$ 恢复，以及有限返回卷 §§162、164 的完整根候选、七项合同和原活动接头边界，继续按已付域使用，不重列为缺失。

原分析器仍须为字面旧程序 $\tau;T_P$ 的指定接受族，在原全部准备、切口、参考／副本、合法分析词和树、原坐标、固定支持全质量及完整菜单上供应准备无关的实际接受关联，保持原支持与未归一标尺；C139 §23.3 的 (23.7) 实际证书未由本节取得。CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及读后同一完整活动输入对所有合法未来的真实 Return；有限返回卷 §164.1 的原活动接头与全参考／控制／钟／旧未来对应未由数学插值生成。复 Hilbert／相干、Born／全菜单、实际张量联合、typed CP／Kraus、完整仪器／TP／更新／Lüders、全部历史／Return、Hamiltonian／物理钟／共同正作用量七项消费者仍只在各自完整原来源合同成立时使用。没有准备生成、矩阵综合到实际菜单的推断、旧 Born／CP／QC 循环、密度／历史身份替代或免费相干控制／复制。

## 新增锚（本行以下为后续增补区）

## 34. 非零原轴像的边界 Gram 见证与隔离轴子类的三残量刚性

本节的 §§34.1–34.7、定义／引理／定理 34.x 及公式 (34.x) 均为本卷局部编号；§§32–33 仍指本卷，§§1–31（含 §30A）仍按卷首约定读取提交 `315786a180a8b00f80b76bb4949281b7394137cf` 的父卷。以下保持 (32.1)–(32.3) 的完整原代数、全部原 Hermitian 角探针和全部正复线性泛函。新增承重结论是一个直接计算面积的非核见证：它准确解决 (33.25) 的每个非零实残量，并与已付定理 30A.2 合成隔离轴输入的三残量分类。它不分类任意 $B,V,D_{\rm env}$ 的所有轴像。

### 34.1 固定的原四维输入

**定义 34.1（同一非零零模像的四维族）。** 在原 $A=M_4(\mathbb C)$、原标准基 $e_1,e_2,e_3,e_4$ 中取

$$
\begin{gathered}
c=\operatorname{diag}(1,2,3,0),\qquad
P=\operatorname{diag}(1,1,1,0),\qquad t=E_{14}+E_{41},\\
S=\operatorname{diag}(0,0,s)\in M_3(\mathbb C),\qquad S\oplus0=sE_{33},\\
g=\frac\iota2(E_{14}-E_{41})+sE_{33},\qquad
s\in\mathbb R,\quad\iota=\sigma i,\quad\sigma\in\{1,-1\}.
\end{gathered}
\tag{34.1}
$$

这里是 (33.25) 的同一 $m=1,B=D_{\rm env}=0,V=e_1$，所以 $\mathcal W=\mathbb C e_1\ne0$。$R_\delta,S_\delta,L,B_\phi$ 均严格取 (32.2)，不改变 $g$ 或任何环境条目。探针域仍为所有 $x=x^*=PxP$；构造一个特定探针只用于否定这个全称 PB。

### 34.2 两个正谱值上的实际边界见证

**引理 34.2（被原 $t$ 湮灭的正谱平面）。** 在同一有限维完整原矩阵代数中，设二维子空间 $Q\mathcal H\subseteq P\mathcal H$ 对原 $c$ 和自伴残量 $\Sigma$ 均约化，且在一组固定正交基下

$$
 c|_Q=\operatorname{diag}(a,b),\quad 0<a<b,\qquad
 \Sigma|_Q=\operatorname{diag}(0,s),\qquad tQ=0.
\tag{34.2}
$$

仍令 $g=K_\sigma(c,t)+\Sigma$ 并使用 (32.2) 的完整乘积。原算子在 $Q^\perp$ 上可以有其原来的任意作用。若 $s\ne0$，则任给有限 $\mu>0$，同一完整原空间中都有质量恰为 $\mu$ 的向量泛函和一个有限原角探针，严格违反 PB。还可保持该泛函、环境和质量不变，只对探针作任意小的非零实扰动，使两笔预算同时严格为正且违反仍在。

证明。置

$$
\begin{gathered}
k=\frac{a+b}{2}>0,\qquad d=\frac{b-a}{2}>0,\qquad
A_0=1+k^2,\qquad \rho=\frac{s}{2dA_0},\\
X=\rho\begin{pmatrix}-k^2&k\\k&-k^2-2\end{pmatrix},\qquad
x=X\oplus0_{Q^\perp},\qquad
u=\frac{(1,\iota)^{\mathsf T}}{\sqrt2},\qquad
f=\frac{(1,-\iota)^{\mathsf T}}{\sqrt2},\\
\phi_\mu(T)=\mu\,u^*Tu,\qquad \phi_\mu(I)=\mu.
\end{gathered}
\tag{34.3}
$$

$u,f$ 在 $Q$ 中取值，并以零延伸到完整原空间；它们单位且正交。$x=x^*=PxP$。为避免把压缩平方当作原平方，先核对实际作用：$cQ=Qc$ 和 $tQ=0$ 给 $ctQ=tcQ=0$，故 $k_tQ=K_\sigma(c,t)Q=0$；$x,h,r,\Sigma$ 都保持 $Q$，所以 $R_\delta,S_\delta$ 在 $u$ 上的完整作用像确实仍在 $Q$。又 $tu=0$，故 $\phi_\mu(t\circ(r+g))=0$。以下范数和内积都是完整原空间中的作用像，因而 $\phi_\mu(T^2)=\mu\|Tu\|^2$ 对所用自伴 $T$ 成立，没有替换原乘法。

令 $Z=\operatorname{diag}(1,-1)$、$J=\begin{pmatrix}0&1\\1&0\end{pmatrix}$、$H=\begin{pmatrix}0&-\iota\\\iota&0\end{pmatrix}$。在该平面上

$$
\begin{gathered}
c=kI-dZ,\qquad X=\rho(-A_0I+Z+kJ),\qquad
Zu=f,\quad Ju=\iota f,\quad Hu=u,\\
h=K_\sigma(c,x)|_Q=dk\rho H,\qquad
Xu=\rho[-A_0u+(1+\iota k)f],\\
r|_Q=\rho[(-kA_0-d)I+(k+dA_0)Z+k^2J],\qquad
\Sigma|_Q=dA_0\rho(I-Z).
\end{gathered}
\tag{34.4}
$$

例如 $[Z,J]=\begin{pmatrix}0&2\\-2&0\end{pmatrix}$，故 $\iota[-dZ,k\rho J]/2=dk\rho H$；Jordan 乘积中 $ZJ+JZ=0$，给出所列 $r$ 的三个系数。这样 $(r+\Sigma)u$ 的 $u,f$ 系数分别为 $\rho(-kA_0+dk^2)$ 和 $\rho(k+\iota k^2)$，完整作用列准确为

$$
\begin{aligned}
R_+u&=\rho[(-A_0+dk)u+(1+\iota k)f],\\
R_-u&=\rho[(-A_0-dk)u+(1+\iota k)f],\\
S_+u&=kR_+u,\qquad S_-u=-kR_+u,\\
\phi_\mu(L)&=-2\mu\operatorname{Re}((Xu)^*hu)
             =2\mu dkA_0\rho^2>0.
\end{aligned}
\tag{34.5}
$$

特别 $B_{\phi_\mu}(R_+,S_+)=0$，而 $R_+u\ne0$，因为 $\rho\ne0$ 且 $1+\iota k\ne0$。为计算另一笔预算，记 $p=-A_0+dk$、$n=-A_0-dk$、$q=1+\iota k$，于是 $|q|^2=A_0$，并有

$$
\begin{gathered}
\|R_-u\|^2=\rho^2(n^2+A_0),\qquad
\|S_-u\|^2=k^2\rho^2(p^2+A_0),\\
(R_-u)^*S_-u=-k\rho^2(np+A_0)\in\mathbb R,\\
(n^2+A_0)(p^2+A_0)-(np+A_0)^2
=A_0(n-p)^2=4d^2k^2A_0.
\end{gathered}
\tag{34.6}
$$

这里用的是 PB 的实 Gram 行列式；内积实性也已实际核对，未漏掉虚部。由此

$$
\begin{aligned}
\sqrt{B_{\phi_\mu}(R_-,S_-)}&=2\mu dk^2\sqrt{A_0}\,\rho^2,\\
|\phi_\mu(L)|-\sum_{\delta=\pm1}\sqrt{B_{\phi_\mu}(R_\delta,S_\delta)}
&=2\mu dkA_0\rho^2\left(1-\frac{k}{\sqrt{1+k^2}}\right)>0.
\end{aligned}
\tag{34.7}
$$

严格性只用 $1+k^2>k^2$；没有数值近似或有限枚举。

最后在同一个 $\phi_\mu$ 上令 $x_\varepsilon=x+\varepsilon(J\oplus0_{Q^\perp})$。每份 $B_\delta(\varepsilon)=B_{\phi_\mu}(R_\delta(x_\varepsilon),S_\delta(x_\varepsilon))$ 都是非负实多项式，次数至多四，因为两份作用列关于实 $\varepsilon$ 仿射。直接在完整作用像上，其一次项为

$$
\dot R_\delta u=\delta d\,u+\iota f,\qquad
\dot S_\delta u=\delta k\iota f,\qquad
\operatorname{Re}((\dot R_\delta u)^*\dot S_\delta u)=\delta k.
$$

所以两份四次系数都准确等于

$$
\mu^2[(1+d^2)k^2-k^2]
=\mu^2d^2k^2=\frac{(b^2-a^2)^2}{16}\mu^2>0.
\tag{34.8}
$$

这也正是 (32.28) 在单位演员向量 $u$、无环境向量分量及谱值 $a,b$ 上的参数对应。每个预算多项式都不恒为零，其实零点集有限。(34.7) 的 PB 差额关于 $\varepsilon$ 连续，因为两个非负预算的平方根、绝对值和作用列均连续，且在零严格为正。因此存在 $\eta>0$，使 $|\varepsilon|<\eta$ 时仍严格违反；在任意更小的零邻域内，避开两个有限零点集以及零，便同时取得 $B_+(\varepsilon)>0$、$B_-(\varepsilon)>0$。始终没有改变 $\phi_\mu$、$t$、$g$ 或原环境。全部式子只用 $\iota^2=-1$、$\overline\iota=-\iota$，故两个 $\sigma$ 分别成立。∎

### 34.3 原 $M_4$ 的精确分类与显式 Gram 数据

**定理 34.3（原非零轴像四维族的全部实残量）。** 对 (34.1) 的每个分别固定的 $\sigma$，全部原 Hermitian 三演员角探针 $x=x^*=PxP$ 和全部原 $M_4(\mathbb C)$ 正复线性泛函满足 (32.3)，当且仅当 $s=0$。任给 $0<\mu<\infty$，将泛函仅限于质量恰为 $\mu$ 仍有同一分类。每个 $s\ne0$ 在原同一环境中都有该指定质量的有限严格见证，并可使两笔预算同时严格正。质量零保留原零等式。

证明。取原平面 $Q=\operatorname{span}(e_2,e_3)$。原 $t,k_t,K_\sigma(c,t)$ 都湮灭它，$c$ 和 $sE_{33}$ 保持它，故引理 34.2 的条件逐项成立：$a=2,b=3,k=5/2,d=1/2,A_0=29/4,\rho=4s/29$。特别这是原完整 $M_4$ 内的实际约化平面，未把原 $\mathcal W=\mathbb C e_1$ 改成零像或另换环境。以下列出这次代入的紧凑完整数据，以明确其原乘积意义。探针仅在 $23$ 平面非零，且

$$
\begin{gathered}
X_s=\frac{s}{29}\begin{pmatrix}-25&10\\10&-33\end{pmatrix},\qquad x_s=X_s\oplus0_{Q^\perp},\\
u_\sigma=\frac{e_2+\iota e_3}{\sqrt2},\qquad
f_\sigma=\frac{e_2-\iota e_3}{\sqrt2},\\
h|_Q=\frac{5s}{29}\begin{pmatrix}0&-\iota\\\iota&0\end{pmatrix},\qquad
hu_\sigma=\frac{5s}{29}u_\sigma,\\
(r+sE_{33})|_Q=\frac{s}{29}\begin{pmatrix}-50&25\\25&-70\end{pmatrix}.
\end{gathered}
\tag{34.9}
$$

对角项直接为 $2(-25)=-50$、$3(-33)+29=-70$，非对角项为 $(2+3)10/2=25$。$X_su_\sigma=(s/29)[-29u_\sigma+(4+10\iota)f_\sigma]$，所以原完整作用列为

$$
\begin{aligned}
R_+u_\sigma&=\frac{s}{29}[-24u_\sigma+(4+10\iota)f_\sigma],\\
R_-u_\sigma&=\frac{s}{29}[-34u_\sigma+(4+10\iota)f_\sigma],\\
S_+u_\sigma&=\frac{s}{29}[-60u_\sigma+(10+25\iota)f_\sigma]
            =\frac52R_+u_\sigma,\\
S_-u_\sigma&=-\frac{s}{29}[-60u_\sigma+(10+25\iota)f_\sigma],\\
\phi_{u_\sigma}(L)&=-2\operatorname{Re}((X_su_\sigma)^*hu_\sigma)
                 =\frac{10s^2}{29}.
\end{aligned}
\tag{34.10}
$$

因为 $tu_\sigma=0$，$t\circ(r+g)$ 的评价确实为零；没有宣称该项在整个 $M_4$ 中为零。由完整作用像而非压缩平方得到

$$
\begin{gathered}
B_{\phi_{u_\sigma}}(R_+,S_+)=0,\qquad
\|R_-u_\sigma\|^2=\frac{1272s^2}{841},\qquad
\|S_-u_\sigma\|^2=\frac{4325s^2}{841},\\
(R_-u_\sigma)^*S_-u_\sigma=-\frac{2330s^2}{841}\in\mathbb R,\\
1272=34^2+4^2+10^2,\qquad 4325=60^2+10^2+25^2,\\
-2330=(-34)60+(4-10\iota)(-10-25\iota),\\
B_{\phi_{u_\sigma}}(R_-,S_-)
=\frac{(1272\cdot4325-2330^2)s^4}{841^2}
=\frac{72500s^4}{707281}
=\left(\frac{50s^2}{29\sqrt{29}}\right)^2.
\end{gathered}
\tag{34.11}
$$

因此对 $s\ne0$，单位质量下的严格差额为

$$
\frac{10s^2}{29}-\frac{50s^2}{29\sqrt{29}}
=\frac{10s^2}{29}\left(1-\frac5{\sqrt{29}}\right)>0,
\qquad 29>25.
\tag{34.12}
$$

取 $\phi_\mu(T)=\mu u_\sigma^*Tu_\sigma$，则质量准确为 $\mu$，左端和每份预算平方根均乘以 $\mu$，故差额为 (34.12) 的 $\mu$ 倍。对于 $J_{23}=E_{23}+E_{32}$，引理的同泛函扰动 $x_s+\varepsilon J_{23}$ 给每笔预算准确四次系数 $25\mu^2/16>0$；连续严格差额与两个有限零点集共同给任意小的两正预算见证。这不是假设零预算不在 PB 域内；未经扰动的零预算已经合法且严格违反。

若 $s=0$，直接复用父卷 §1 的标准 $K_\sigma$ 恒等式

$$
L=K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-)
\tag{34.13}
$$

及其全正泛函复 Gram／Cauchy–Schwarz 证明，即对所有原探针和所有正复线性泛函（包括混合泛函）得到 (32.3)。这里的充分性没有从单个向量读取外推。质量零时，正泛函的 $\phi(I)=0$ 由 Cauchy–Schwarz 强制 $\phi=0$，所以两边均为零。非零 $s$ 的见证与零 $s$ 的全称充分性共同完成分类，两个 $\sigma$ 分别成立。∎

### 34.4 面积边界与合法同时核盲区的准确区别

(34.10) 的加号作用对在 $s\ne0$ 时非零且成实比例 $S_+u_\sigma=(5/2)R_+u_\sigma$。若对这一对完整作用像作实 Gram 变分，取 $\beta_+=5/2$ 后，其代价为

$$
\alpha_+\|R_+u_\sigma\|^2+
\alpha_+^{-1}\|S_+u_\sigma-\beta_+R_+u_\sigma\|^2
=\alpha_+\|R_+u_\sigma\|^2.
\tag{34.14}
$$

其零下确界只在 $\alpha_+\downarrow0$ 取得极限；没有严格正有限 $\alpha_+$ 的零代价最优点。这正是边界预算，不属于定义 33.1 所要求的 $\alpha_+>0$ 有限合法同时齐次核类别。这里含残量的 $S_\delta u_\sigma$ 也不被偷换成 (33.1) 的零残量齐次列 $\mathsf S_\delta$。本证明直接比较完整 PB 的左端与两笔面积，没有构造合法核或取得 $F(sE_{33})\ne0$；定理 33.2 的全称核盲区仍原样成立。

扰动后两笔面积为正也不要求两份作用对同时满足齐次核关系。连续性只运输一个已经严格的完整 PB 差额。因此“合法核读取看不见第三格”和“第三格非零残量违反 PB”在这个同一原输入上同时成立。新机制是非核有限见证，并非再寻找一条被 33.2 排除的核分离路线。

### 34.5 任意有限环境的隔离轴输入

**定理 34.4（隔离第一轴输入的全部三残量）。** 保持定义 32.1 的原全部对象，令 $m\ge1$ 任意有限，并限定实际输入为

$$
 B=\beta E_{11},\qquad V=e_1v,\qquad
 \beta\in\mathbb R,\quad v\in M_{1,m}(\mathbb C),\qquad
 D_{\rm env}=D_{\rm env}^*,\qquad v(\ker D_{\rm env})\ne\{0\}.
\tag{34.15}
$$

这里 $S=\operatorname{diag}(s_1,s_2,s_3)$ 仍有三个独立任意实条目，$g=K_\sigma(c,t)+(S\oplus0_m)$。则对每个分别固定的 $\sigma$，全部原三演员角探针和全部原完整代数正泛函满足 (32.3)，当且仅当 $s_1=s_2=s_3=0$。任意指定有限 $\mu>0$ 上全称检验也有同一结论；每个非零 $S$ 都有同一原环境、质量恰为 $\mu$、两笔预算同时正的有限严格见证。质量零仍为零等式。

证明。由 (34.15)，原 $\mathcal W=\mathbb C e_1$，并且 $t$ 湮灭整个原 $23$ 平面。先在原空间中取

$$
\mathcal H_0=\operatorname{span}(e_1,e_2)\oplus\mathbb C^m_{\rm env},
\qquad \jmath:\mathcal H_0\hookrightarrow\mathcal H.
\tag{34.16}
$$

这是实际子空间，不是另造环境。它对原 $c,t,S\oplus0_m$ 均约化：$t$ 只在第一轴及原环境之间连线，$c,S$ 均对角；剩下的 $e_3$ 没有连到 $\mathcal H_0$。在 $\mathcal H_0$ 上，参数准确为父卷定义 30A.1 的

$$
C_0=\operatorname{diag}(1,2),\quad
B_0=\begin{pmatrix}\beta&0\\0&0\end{pmatrix},\quad
V_0=\begin{pmatrix}v\\0\end{pmatrix},\quad
D_0=D_{\rm env},\quad S_0=\operatorname{diag}(s_1,s_2).
$$

其零模像非零。任一父卷探针 $x_0$ 以 $x=\jmath x_0\jmath^*$ 嵌入，仍是原三演员角探针，第三行列为零。对其 $R_{\delta,0},S_{\delta,0},L_0$，完整原作用满足

$$
R_\delta\jmath=\jmath R_{\delta,0},\qquad
S_\delta\jmath=\jmath S_{\delta,0},\qquad
L\jmath=\jmath L_0.
\tag{34.17}
$$

原因是每个因子都保持这个同一实际子空间，且 $s_3E_{33}\jmath=0$；所以每个完整乘积的作用逐项交织，平方与 Jordan 乘积亦然。这一步给出了原全乘积的实际嵌入，没有仅凭主子块就假设压缩平方相等。

若 $(s_1,s_2)\ne(0,0)$，直接消费定理 30A.2：它在这份原 $D_0,V_0,B_0$ 上供应有限探针和质量恰为 $\mu$ 的向量 $\eta\in\mathcal H_0$，使两笔原预算同时正且 PB 严格失败。将同一个向量送入 $\jmath\eta$，其范数和质量不变；由 (34.17)，左右端及两份预算逐项不变，故成为完整原 $M_{m+3}$ 中的见证，任意 $s_3$ 均不影响它。这里复用既有两演员结论，不重新取得该结论的证明贡献。

因此全称 PB 先迫使 $s_1=s_2=0$。若此时 $s_3\ne0$，原 $23$ 平面满足引理 34.2 的全部条件，参数正是定理 34.3 的 $a=2,b=3,s=s_3$。原 $\beta,v,D_{\rm env}$ 无论为何值，仍全部湮灭该平面，(34.9)–(34.12) 的完整作用、指定质量和同泛函两正预算扰动原样给严格见证。这便迫使 $s_3=0$。最后 $S=0$ 时，(34.13) 和父卷 §1 对完整原代数上全部正泛函给出充分性，含混合、零及次归一泛函。两个分支都只固定一个 $\sigma$，不共轭或改变原环境。∎

(34.15) 是比“$\mathcal W=\mathbb C e_1$”更强、且在证明中实际使用的隔离条件。一般轴像只限制 $V$ 在 $\ker D_{\rm env}$ 上的像：$V$ 在非零环境谱方向可以有第二、第三行，$B$ 也可以有 $13,23$ 或其他混合条目。这些作用会破坏 (34.2) 或 (34.16) 的共同不变性，故定理 34.4 不能扩大为任意轴像分类。任意非零 $\mathcal W$ 的全三残量 PB 单独刚性、任意 $B,V,D_{\rm env}$ 以及一般算子块仍未由本节解决。定理 32.3 的全三格支撑结果和定理 33.2 的轴核盲区各保留准确原域；旧 $W=0$ 分支不被重新用作本节的研究靶。

### 34.6 局部 P2 删除、成熟工具与原来源边界

定理 34.3、34.4 所证的是原固定输出 $g=K_\sigma(c,t)+S\oplus0_m$ 的确切子类。只在这些已证输入上，全部原 PB（甚至某个指定正有限质量上的全称 PB）先给 $S=0$，父卷 §1 再给全部正泛函的固定输出 P2：$\phi(g)^2\le B_\phi(c,t)$。因此此处的固定输出 P2 可作为后果，毋须另加前件。若另已辨识 $g=D(c,t)$，便只对这一输入对得到 $c\circ t-iD(c,t)=ct$（$\sigma=1$）或 $tc$（$\sigma=-1$）。没有从完整 $\mathsf H_A(D)$ 删除 A1/P2，没有删除承载卷定义 41.1 由两份实际外层 P2 导出显式预算的桥，也没有从仅有少数探针的测试推得全称结论；完整 H／总 D 分类不作为这里的前件或新增成果。

成熟工具的归属沿 §32.6、父卷 §§1、5、27–30A：正泛函的复 Gram／Cauchy–Schwarz、实 Gram 面积、Hermitian 矩阵运算、非零实多项式只有有限实根、平方根连续性均为标准工具。本节的仓内综合内容是 (34.3)–(34.12) 的特定非核构造、严格差额和原全空间见证，以及它与定理 30A.2 在 (34.15) 的同一原空间中的组合。不是把成熟 Gram 定理另命名为新结果，不主张历史优先权、文献穷尽、全局最小性或 Lean／kernel 核验。

[Watrous 文献注的有限实际自参考判据](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations) 已在其共同有限矩阵坐标、同一实际自复合、严格正参考权重及保留输入扇区标签的前件下，由同一参考输出的正性准确判别各块 CP，连同原边缘约束给有限 Kraus／仪器对应；其“Complete finite candidate”在全部原有限条件下的成就保留。该结果是已有 Choi／Kraus 工具在其指定有限域中的应用，不是本节新证明，也不从静态比较生成所有实际装置、原高阶复合、物理钟或完整 Omega 来源。

完整普通候选仍准确采用父卷 [§6 式 (6.1)](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标) 的同一逐层钉版全文及全部原条件，并保留[有限返回续卷定义 162.1、复用命题 162.2](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的完整原根与七项消费者；这些引用不以本段概述替换。七项分别仍需：共同全词及实际相干准备才消费复 Hilbert；实际事件、完整菜单及正质量绑定才消费 Born；原真正相关共同联合和交换生成才消费张量；整台 typed 箭头的原合法接续、参考、真支持及所需表示才消费 CP／Kraus；实际完整仪器、单位分区、正输出质量、像内射线保持与校准才消费 TP／更新／Lüders；全部原记录和合法未来及真实返回才消费历史／Return；同一实际连续可逆流、强连续实现、生成元域、物理钟／单位与共同正作用量才消费 Hamiltonian。

所有原准备、事件、过程、参考／副本、真正相关联合、零／不等／次归一质量、原钟／单位／控制、parent／ready／flags、完整记录、失败、拒绝、停止、销毁、泄漏、真遗忘、两侧及逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口与每份完整输出的所有合法未来都保留。数学向量和探针不生产准备、菜单、复制或相干控制；没有旧 Born／CP／QC、密度或历史身份的循环。

[C139 固定源卷 §§50–73](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的原合法前接、唯一正回溯、下降、固定返回刚性、条件过程比较及递归参考／累计支持，[§§74–85](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的准确近似参考及容量边界，以及 [C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 的同一旧 $D$ 恢复，继续在各自已付域消费，不倒称缺失。[C139 §23.3 的 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 仍要求原字面程序 $\tau;T_P$ 的指定接受族，在原全部准备、切口、参考／副本、合法分析词及树、原坐标、固定支持全质量及完整菜单上，到同一原实际菜单与接受端的准备无关准确证书，保持原支持和未归一标尺；矩阵相等、纯校准、合法逆或矩阵综合不提供它。[有限返回续卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 区分另增服务的查询候选与原 $B_{r_\star}$ 的活动接头：CountRead 仍须同一接受叶完整活动输出、实际读后 active-ready、第一合法消费者，以及同一完整活动输入对全部合法未来的真实 Return，连同原参考／控制／钟和全部旧未来对应。这两份原来源构造没有由本节取得。完整原量子起源、完整量子公理候选的无缺口来源及整体严格更简的目标仍未完成。

### 34.7 中文几何：一笔面积贴边，另一笔仍不够

原环境的连线仍落在第一格，原世界也仍是完整四维。让探针只作用在第二、第三格，恰好可以利用原 $t$ 在这两个方向上真的没有作用，而不是先剪掉环境再重算乘法。探针和同一个读取方向产生四列实际向量；选定的系数使加号两列沿同一条实直线，于是它们张成的面积为零。减号两列仍张开，面积严格为正，但直接算出的左端比这份面积更大。只要第三格残量不为零，不论正负，这个缺额都是正的平方倍数；任何指定正质量只会把缺额同比缩放。

这里没有找到一条新的合法核。旧核路线要求两份复比例同时带着严格正的变分权重，而这次实直线的最优权重落在零边界，正是旧路线不覆盖的位置。再轻微转一下同一个探针，两笔面积都可以变正；因为原来已有严格缺额，小转动不会把缺额立刻抹去。这说明零预算是发现见证的合法起点，也能通向两笔预算都正的实际见证。

对隔离第一轴的整类输入，先在第一、第二格和同一个完整环境中直接使用旧两演员定理，排除前两格误差；第三格误差随后由这张第二、第三格的面积图排除。两步各自使用一个合法共同探针和泛函，不把不同次读取的预算拼起来。图形省下的只有这批固定输出额外索取 P2 的前件；一般连线混到第二、第三格时，这张图的共同不变平面会消失，仍需新的数学。原装置究竟能执行哪张全菜单、读后是否真正 ready、完整活动输入能否对所有旧未来返回，更仍须原来源给出，不能由这张面积图代造。

## 新增锚（本行以下为后续增补区）


## 35. 两笔正预算的显式非核见证与全输出耦合必要界

本节的 §§35.1–35.5、定理／命题 35.x 和公式 (35.x) 均为本卷局部编号；§§32–34 仍指本卷，§§1–31（含 §30A）仍严格按卷首的原提交与递归钉版合同解释。所有 $R_\delta,S_\delta,L,B_\phi$ 均取 (32.2) 的完整原乘积，PB 仍是 (32.3)，探针仍遍取全部原 Hermitian 三演员角，泛函仍遍取完整原代数上的全部正复线性泛函。定理 34.3 已完成原 (34.1) 的全部实 $s$ 分类；定理 34.4 已完成 (34.15) 的三个独立残量分类，引理 34.2 的一般正谱约化平面结论亦保留。本节增加一份无需扰动即有两笔正预算、差额更大的指定质量见证，以及不要求该平面被 $t$ 湮灭的全输出必要界；不重复这些分类的证明，也不把一般 $B,V,D_{\rm env}$ 限成隔离轴输入。

### 35.1 原非零轴像中的两笔显式正预算

**定理 35.1（指定质量的严格内部面积见证）。** 固定 (34.1) 的原完整 $M_4(\mathbb C)$、$t=E_{14}+E_{41}$、$\mathcal W=\mathbb C e_1\ne0$ 和任一个 $\iota=\sigma i$。对每个实 $s\ne0$、每个指定 $0<\mu<\infty$，取

$$
\begin{gathered}
E=\operatorname{span}_{\mathbb C}(e_2,e_3),\qquad
u=e_2+e_3,\qquad d=e_2-e_3,\qquad v=u/\sqrt2,\\
x|_E=\frac{s}{2}\begin{pmatrix}-5&4+\iota\\4-\iota&-4\end{pmatrix},
\qquad x|_{E^\perp}=0,\\
\phi_\mu(a)=\frac\mu2u^*au=\mu v^*av,
\qquad \phi_\mu(I_4)=\mu .
\end{gathered}
\tag{35.1}
$$

则同一个原探针、同一个泛函上的完整 PB 数据准确为

$$
\begin{gathered}
\phi_\mu(L)=\frac{9\mu s^2}{8},\qquad
\sqrt{B_{\phi_\mu}(R_+,S_+)}=\frac{5\mu s^2}{16},\qquad
\sqrt{B_{\phi_\mu}(R_-,S_-)}=\frac{5\sqrt5\,\mu s^2}{16},\\
\Delta_\mu:=|\phi_\mu(L)|-
 \sum_{\delta=\pm1}\sqrt{B_{\phi_\mu}(R_\delta,S_\delta)}
=d_0\mu s^2>0,\qquad d_0=\frac{13-5\sqrt5}{16}>0 .
\end{gathered}
\tag{35.2}
$$

特别，$s\ne0$ 时两笔原预算已经同时严格正。两种取向分别得到这些同一实数；$s=0$ 或 $\mu=0$ 时这份构造只给零等式，不再是严格见证。

证明。$x=x^*=PxP$，$u,d$ 为实向量，$\|u\|^2=\|d\|^2=2$。原 $t$ 确实湮灭 $E$，且 $cE\subseteq E$，所以 $k_tu=K_\sigma(c,t)u=tu=0$。完整作用像而非压缩平方给

$$
\begin{aligned}
xu&=-\frac{s}{2}e_2+\frac{s}{2}\iota d,\\
hu&=\frac{s}{4}u-s\iota d,\\
(r+sE_{33})u&=\frac{5s}{4}\iota d,\\
R_\delta u&=a_\delta+s(1/2-\delta)\iota d,
\qquad a_\delta=-\frac{s}{2}e_2+\frac{\delta s}{4}u,\\
S_\delta u&=\frac{5\delta s}{4}\iota d .
\end{aligned}
\tag{35.3}
$$

逐条核对中，$h_{23}=s(1/4-\iota)$、$h_{32}=s(1/4+\iota)$；$r+sE_{33}$ 的两个对角元均为 $-5s$，非对角元为 $5s\pm5\iota s/4$。这些条目直接给前三行，后两行就是原定义。$t\circ(r+g)$ 在该泛函上的读数为零，因为 $tu=0$；没有将此 Jordan 项宣称为整个原代数中的零算子。

复空间实化后的内积为 $\langle a,b\rangle_{\mathbb R}=\operatorname{Re}(a^*b)$。$a_\delta$ 为实向量，因而与 $\iota d$ 实正交；$R_\delta u$ 的另一分量与 $S_\delta u$ 实平行。故原平方恒等式
$\phi_\mu(A^2)=(\mu/2)\|Au\|^2$、
$\phi_\mu(A\circ B)=(\mu/2)\operatorname{Re}((Au)^*Bu)$ 给

$$
\sqrt{B_{\phi_\mu}(R_\delta,S_\delta)}
=\frac\mu2\|a_\delta\|\,\|S_\delta u\|,
\qquad
\begin{cases}
a_+=-sd/4,\\
a_-=-s(3e_2+e_3)/4,
\end{cases}
\qquad
\|S_\delta u\|=5\sqrt2\,|s|/4 .
\tag{35.4}
$$

这给 (35.2) 的两份平方根，预算本身分别为 $25\mu^2s^4/256$ 和 $125\mu^2s^4/256$。又由 (35.3)，
$\operatorname{Re}((xu)^*hu)=-s^2/8-s^2=-9s^2/8$，所以
$\phi_\mu(L)=-\mu\operatorname{Re}((xu)^*hu)=9\mu s^2/8$。相减得所述差额；$13^2>25\cdot5$ 保证严格正。与 (34.12) 的同质量差额相比，其系数严格增大：

$$
\frac{10}{29}\left(1-\frac5{\sqrt{29}}\right)
<\frac{40}{841}<\frac7{64}<d_0 .
\tag{35.5}
$$

第一步用 $\sqrt{29}<29/5$，最后一步用 $\sqrt5<9/4$，中间只是正整数交叉相乘。没有声称新探针在全部原探针中最优。取向改变只共轭这份探针；原 $t,c$ 与实向量 $u$ 不变，(35.3)–(35.4) 只用 $\overline\iota=-\iota$、$\iota^2=-1$，故两个 $\sigma$ 各自成立。∎

### 35.2 零残量同时核的排除与三演员、环境的共同参与

在 (35.1) 的同一作用列中

$$
R_+u=s(-1/4-\iota/2)d\in\mathbb C d,\qquad
S_{+,0}u=\frac{5s}{4}\iota d-se_3\notin\mathbb C d
\quad(s\ne0),
\tag{35.6}
$$

其中下标 $0$ 只表示从原 $S_+$ 中减去残量 $sE_{33}$，不改变其他原输入。因为 $e_3\notin\mathbb C d$，不存在任何复数 $\zeta_+$ 使 $S_{+,0}u=\zeta_+R_+u$；归一化为 $v$ 亦然。因此这份读取甚至不满足定义 33.1 的第一份零残量核比例，当然不产生合法同时核分离。定理 33.2 的盲区与 §34.4 对边界机制的解释均保持原义；此处从完整 PB 面积内部直接取得有限违反。

**命题 35.2（三个演员非对角对及原环境均参与的见证）。** 固定定理 35.1 的任意 $s\ne0$、$\mu>0$ 和取向，保持原 $c,t,g$ 不变。对实 $\varepsilon$ 取

$$
\begin{gathered}
x_\varepsilon=x+\varepsilon(E_{12}+E_{21}+E_{13}+E_{31}),\\
u_\varepsilon=u+\varepsilon(e_1+e_4),\qquad
\|u_\varepsilon\|^2=2+2\varepsilon^2,\\
\phi_{\mu,\varepsilon}(a)=
 \frac{\mu\,u_\varepsilon^*a u_\varepsilon}{2+2\varepsilon^2},
\qquad \phi_{\mu,\varepsilon}(I_4)=\mu .
\end{gathered}
\tag{35.7}
$$

存在 $\eta>0$，使每个 $0<|\varepsilon|<\eta$ 都在同一个泛函上严格违反原 PB 且两笔预算同时严格正。此时 $x_\varepsilon$ 的 $12,13,23$ 三个非对角对均非零，$u_\varepsilon$ 的三个演员分量与原环境分量均非零，并且

$$
t u_\varepsilon=\varepsilon(e_1+e_4)\ne0 .
\tag{35.8}
$$

证明。$x_\varepsilon$ 始终是原 Hermitian 角探针；$12,13$ 条目为 $\varepsilon$，$23$ 条目保持 $s(4+\iota)/2\ne0$。所有原作用列关于 $\varepsilon$ 连续，泛函分母恒正，故两笔完整预算和 PB 的绝对值差额连续；预算非负性来自正泛函的实 Gram。零处预算分别为 (35.4) 后列出的两个正数，差额为 $d_0\mu s^2>0$。对这三个连续函数各取一个零邻域，使其值大于各自零处值的一半，再取三个邻域的交，即得所需 $\eta$。这对该邻域内每个非零实 $\varepsilon$ 成立，不是只避开一个未知零点集。直接以原 $t$ 作用给 (35.8)，环境既没有更换也没有删去。若要两种取向共用同一 $\eta$，取各自正半径的较小者即可；探针仍按各自 $\iota$ 解释。这里的参与是原矩阵及向量的数学参与，不生成实际准备或装置。∎

### 35.3 任意原有限环境的全输出必要界

**定理 35.3（原平面向整个空间的耦合控制）。** 保持定义 32.1 的任意有限 $m$、任意原 $B,V,D_{\rm env}$，只限定残量为 $S=\operatorname{diag}(0,0,s)$。原 $t$ 不必保持 $E=\operatorname{span}(e_2,e_3)$，$\mathcal W$ 不作隔离或秩假设。定义

$$
T=\|t|_E:E\longrightarrow\mathcal H\|
 =\sup_{z\in E,\ \|z\|=1}\|tz\|,
\qquad \mathcal H=\mathbb C^3\oplus\mathbb C^m .
\tag{35.9}
$$

范数包含 $tz$ 在整个原 $\mathcal H$ 中的所有演员及环境输出，不能换成 $\|P_Et|_E\|$。对任一分别固定的 $\sigma$，若全部原探针、全部原正泛函满足 PB，或仅在任一指定有限质量 $\mu>0$ 上全称满足 PB，则必有

$$
\boxed{\qquad d_0s^2\le32|s|T+30T^2,
\qquad d_0=(13-5\sqrt5)/16 .\qquad}
\tag{35.10}
$$

若反向严格不等式 $d_0s^2>32|s|T+30T^2$ 成立，(35.1) 零延伸到同一原空间的 $x,v$ 和 $\phi_\mu(a)=\mu v^*av$ 就是指定质量的完整 PB 严格见证。$T=0$ 时，任意其余原环境和耦合都保留 (35.2) 的精确值，全部 PB 准确当且仅当 $s=0$。$T>0$ 时 (35.10) 只是必要条件，允许足够小的非零 $s$；它不证明任何这样的输入满足全部 PB，也不是一般非零 $\mathcal W$ 的分类或非零残量反模型。

证明。全程沿原 $\mathcal H$ 计算，以单位 $v=(e_2+e_3)/\sqrt2$ 及同一 $x$ 作比较。仅在这份估计中，用上标 $(0)$ 表示把 $t$ 取为零后的代数比较列，保持 $c,x,sE_{33}$ 原值；实际待判输入始终是给定的原 $t$。记 $K=K_\sigma(c,t)$、$k=c\circ t$，则

$$
\begin{gathered}
\|tv\|\le T,\qquad \|tcv\|\le3T,\qquad \|ctv\|\le3T,
\qquad \|kv\|,\|Kv\|\le3T,\\
(R_\delta-R_\delta^{(0)})v=-\delta kv,
\qquad (S_\delta-S_\delta^{(0)})v=tv+\delta Kv,\\
\|(R_\delta-R_\delta^{(0)})v\|\le3T,
\qquad \|(S_\delta-S_\delta^{(0)})v\|\le4T .
\end{gathered}
\tag{35.11}
$$

这里 $cv\in E$、$\|c\|=3$，所以 $tcv$ 的估计也只使用同一个全输出 $T$，没有以环境块范数替代。由 (35.3) 的实际基准列，

$$
\begin{gathered}
\|R_+^{(0)}v\|^2=5s^2/16,\qquad
\|R_-^{(0)}v\|^2=41s^2/16,\\
\|R_\delta^{(0)}v\|\le2|s|,\qquad
\|S_\delta^{(0)}v\|=5|s|/4,
\qquad \|xv\|^2=3s^2/8\le s^2 .
\end{gathered}
\tag{35.12}
$$

为控制平方根在零预算处也有效的误差，在原复空间的实化中选一组实标准正交基。对实坐标向量 $a,b$，把 $a\wedge_{\mathbb R}b$ 定义为所有 $i<j$ 的坐标 $a_i b_j-a_j b_i$。直接展开得

$$
\|a\wedge_{\mathbb R}b\|^2
=\|a\|^2\|b\|^2-\langle a,b\rangle_{\mathbb R}^2,
\qquad \|a\wedge_{\mathbb R}b\|\le\|a\|\|b\| .
$$

这是 PB 所用未中心化实 Gram 面积的坐标恒等式。双线性展开
$(a+e)\wedge(b+f)-a\wedge b=a\wedge f+e\wedge b+e\wedge f$，再用欧氏范数的反三角与三角不等式，完整给出

$$
\left|\|(a+e)\wedge(b+f)\|-\|a\wedge b\|\right|
\le\|a\|\|f\|+\|e\|\|b\|+\|e\|\|f\| .
\tag{35.13}
$$

不需要除以面积或假设 Gram 非退化。将 (35.11)–(35.12) 代入，写
$A_\delta=\sqrt{B_{\phi_v}(R_\delta,S_\delta)}$、
$A_\delta^{(0)}=\sqrt{B_{\phi_v}(R_\delta^{(0)},S_\delta^{(0)})}$，得到每笔原面积的误差

$$
|A_\delta-A_\delta^{(0)}|
\le\left(8+\frac{15}{4}\right)|s|T+12T^2
=\frac{47}{4}|s|T+12T^2 .
\tag{35.14}
$$

原左端的比较也在完整作用列上进行。令 $\ell_t=v^*Lv$，$\ell_0=9s^2/8$，展开原 Jordan 读数恰为

$$
\begin{aligned}
\ell_t-\ell_0
 &=2\operatorname{Re}((xv)^*kv)
   -2\operatorname{Re}((tv)^*((r+sE_{33})v+Kv)),\\
|\ell_t-\ell_0|
 &\le6|s|T+\frac52|s|T+6T^2
 =\frac{17}{2}|s|T+6T^2 .
\end{aligned}
\tag{35.15}
$$

其中 $\|(r+sE_{33})v\|=5|s|/4$ 来自 (35.3)。尤其没有丢掉 $t\circ g$ 或把 $t^2$ 换成演员压缩平方。由 $||\ell_t|-|\ell_0||\le|\ell_t-\ell_0|$，两种绝对值侧均受控制。以同一个 $\phi_\mu=\mu\phi_v$ 同时评价左端和两笔预算；左端与每笔平方根准确同乘 $\mu$，所以

$$
|\phi_\mu(L)|-\sum_\delta\sqrt{B_{\phi_\mu}(R_\delta,S_\delta)}
\ge\mu\bigl[d_0s^2-32|s|T-30T^2\bigr].
\tag{35.16}
$$

系数为 $17/2+2(47/4)=32$、$6+2(12)=30$。全称 PB 在这份同一泛函上应用即得 (35.10)，反向严格不等式则给见证；没有混用不同质量、不同泛函或不同环境的最优值。

若 $T=0$，原 $t$ 湮灭整个 $E$；因 $cE\subseteq E$，$kv=Kv=tv=0$。所以所有原作用列及左端都与 (35.3) 的比较列逐项相等，(35.2) 的准确数值不受其余环境影响。非零 $s$ 因而被排除。零 $s$ 的充分性直接使用 (34.13) 的原算子恒等式；为明确其全正泛函范围，固定任意原正复线性泛函 $\phi$ 和自伴 $U,Z$，置 $a=\phi(U^2)$、$b=\phi(Z^2)$、$z=\phi(UZ)$。正性给 $a,b\ge0$，且对每个复 $\lambda$，
$\phi((\lambda U+Z)^*(\lambda U+Z))=a|\lambda|^2+2\operatorname{Re}(\bar\lambda z)+b\ge0$。若 $a>0$，取 $\lambda=-z/a$ 得 $|z|^2\le ab$；若 $a=0$，变动 $\lambda$ 强制 $z=0$，结论亦然。正泛函保持伴随，故 $\phi(U\circ Z)=\operatorname{Re}z$、$\phi(K_\sigma(U,Z))=-\sigma\operatorname{Im}z$。于是

$$
|\operatorname{Im}z|^2\le ab-(\operatorname{Re}z)^2=B_\phi(U,Z),
\qquad
|\phi(L)|
=\left| -\sigma\sum_{\delta=\pm1}\delta\operatorname{Im}\phi(R_\delta S_{\delta,0})\right|
\le\sum_{\delta=\pm1}\sqrt{B_\phi(R_\delta,S_{\delta,0})} .
\tag{35.17}
$$

这对任意原 $t$ 的零残量均成立，涵盖混合、奇异密度、零预算、两个绝对值侧及两个分别固定的 $\sigma$；没有只从向量态外推，也不需要混合行列式定理。$\phi(I)=0$ 时，以上二次式取 $U=I$、任意自伴 $Z$ 就给 $\phi(Z)=0$，再由复线性得 $\phi=0$，保留零质量等式；零质量本身不强制 (35.10)。∎

### 35.4 已付分类、成熟工具与完整来源的边界

(35.1)–(35.8) 的指定系数与严格差额、(35.9)–(35.16) 的全输出必要估计属于本仓的 $\texttt{repo-derived}$ 推导。成熟的正泛函 Gram／Cauchy–Schwarz 沿父卷 §§1、5 及 §32.6 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；实二向量 Gram 面积、实化、有限维范数与连续性只作为被消费的标准工具，所需面积恒等式和误差推导已在证明内给出。此处预算未中心化，不以协方差或归一方差替换原平方；不为指定系数、常数最优性或文献优先权作外部归属。

定理 34.3 的原非零轴像分类、定理 34.4 的隔离轴三残量分类，以及定理 32.3 的三格支撑分类各按其全部原量词保留。一般原 $\mathcal W\ne0$、任意 $B,V,D_{\rm env}$ 的三残量分类、一般算子块、完整 $\mathsf H$／未知总 $D$、$\mathcal E_+^D=\mathcal E_-^D$ 与 $N_\omega(\varepsilon)^2\to0$ 均未由 (35.10) 解决。特别，(35.10) 没有从“$T>0$ 可容纳小非零 $s$”推出全 PB 模型；也没有把证明内的 $t=0$ 比较列替换 (34.1) 的实际非零 $t$。这里只在 $T=0$ 的已证固定输出域复用零残量的全正 P2 后果，不从完整 $\mathsf H_A(D)$ 删除 A1/P2 或原外层预算桥。

完整 Omega 对象、全部原量词和七项消费者的前件逐项沿父卷 [§6 式 (6.1)](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标)，并沿[有限返回续卷定义 162.1、复用命题 162.2](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的同一全文及全部递归上游保留；§34.6 的精确解释继续适用，本段不是缩短合同。所有原准备、事件、过程、参考／副本、相关联合、零／不等质量、钟／单位／控制、ready／flags、完整记录与失败／停止／销毁、固定支持全质量、完整菜单、已量化切口及所有合法未来均按这些全文解释，数学矩阵不生成准备、菜单、复制、相干控制或实际返回。外部物理文本的来源身份与独立核验仍受原摄入边界约束，不由这份代数计算认证。

[Watrous 文献注的有限带标签实际参考判据](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations) 已在共同有限直和矩阵坐标、同一实际自复合、严格正参考权重和保留输入扇区标签的条件下，以一份完整联合输出的正性判别各块 CP；相应参考边缘等式／不等式刻画有限通道、分支和仪器，对每个必然接受态逐点保持的既有中性条件再给 Lüders。其完整有限候选保留该条件几何的成果；一份参考不是单次二元测量，也不生成实际装置、原高阶复合或物理钟。[C139 固定源卷 §§50–85](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的下降、返回刚性、递归参考／支持与近似容量结果及 [C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 的同一旧 $D$ 恢复继续在各自原域消费。

实际来源缺口仍是 [C139 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 对字面 $\tau;T_P$ 指定接受族，在全部原准备、切口、参考／副本、合法分析词／树、固定支持全质量和完整菜单上的准备无关准确原接受关联，以及[有限返回续卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 区分出的原 $B_{r_\star}$ 活动接头。CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者及同一完整活动输入对全部旧合法未来的真实 Return，保留原参考、控制和钟。矩阵相等、纯校准、操作逆、矩阵综合及另增查询服务均不供应这些接线。完整原量子起源、无缺口来源的完整量子公理候选及整体严格更简目标仍未完成；这里没有 Lean／kernel 认证主张。

### 35.5 中文几何：两张面积都有正余量，原连线的影响另计

对同一份读取，预算量的是两列实际作用向量张开的实面积。新探针让每份第一列分成两部分：一部分与第二列平行，另一部分与它实正交。平行部分不贡献面积，正交部分直接给面积的准确乘积。两张面积这次都严格大于零，但它们的和仍小于同一次读取的左端；缺额准确随残量平方和原质量缩放。再轻微接入第一演员，并让读取在原环境中也有非零分量，三个演员之间的非对角连线和环境作用便都参与。原来有严格余量，所以足够小的这种变化仍保留违反。

若原环境本来就会把第二、第三格送往别处，就必须把送到整个原空间的长度计入 $T$。两列作用像各改变多少，便给它们张成面积改变多少；同一原左端也有一份可直接估计的改变。三份误差合起来得到 (35.10)：残量带来的原缺额若超过这些影响，原 PB 就不可能对全部探针成立。$T=0$ 时其他方向再复杂也不会影响这份见证；$T>0$ 时估计只划出一块不能成立的区域，区域之外还须真正证明，不能把“尚未被这把尺排除”说成“已经成立”。实际分析器能接受什么、读后是否活动就绪、完整输入能否对全部旧未来返回，仍由原来源承担。

## 新增锚（本行以下为后续增补区）
## 36. 非零第二、第三演员混合下的三残量刚性与固定探针面积见证

本节的 §§36.1–36.6、定义／命题／定理 36.x 与公式 (36.x) 均为本卷局部编号；§§32–35 指本卷，父卷 §§1–31（含 §30A）及其全部递归来源仍按卷首钉版解释。原 PB 始终是 (32.2)–(32.3) 的完整原乘积与全部原探针、全部原正复线性泛函。本节处理实际 $23$ 连线非零的轴像类：先把父卷两份轴读取作为完整三维齐次列消费，再以一个固定探针分离剩余第三格；不把 $12$ 压缩平方当作原平方。$23$ 平面仍是原 $c,t$ 的约化平面，但原 $t$ 在其中非零，故不再使用 $t$ 湮灭该平面的前件。

### 36.1 实际混合输入与全称检验的准确域

**定义 36.1（带非零 $23$ 混合的原轴像输入）。** 在定义 32.1 的同一原空间 $\mathcal H=\mathbb C^3\oplus\mathbb C^m$、$m\ge1$ 任意有限、$c=\operatorname{diag}(1,2,3)\oplus0_m$ 中，限定

$$
\begin{gathered}
B=\beta E_{11}+b(E_{23}+E_{32}),\qquad
\beta,b\in\mathbb R,\quad b\ne0,\qquad V=e_1v,\\
v\in M_{1,m}(\mathbb C),\qquad D_{\rm env}=D_{\rm env}^*,
\qquad v(\ker D_{\rm env})\ne\{0\},\\
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix},\qquad
S=\operatorname{diag}(s_1,s_2,s_3),\quad s_j\in\mathbb R,\qquad
g=K_\sigma(c,t)+(S\oplus0_m).
\end{gathered}
\tag{36.1}
$$

这里 $\mathcal W=V(\ker D_{\rm env})=\mathbb C e_1$，每次分别固定 $\sigma=\pm1$、$\iota=\sigma i$。原环境、$v$ 的复条目和非零环境谱均不改变。$E=\operatorname{span}_{\mathbb C}(e_2,e_3)$ 对原 $c,t$ 约化，且

$$
c|_E=\begin{pmatrix}2&0\\0&3\end{pmatrix},\qquad
t|_E=b\begin{pmatrix}0&1\\1&0\end{pmatrix}\ne0 .
\tag{36.2}
$$

相反，$\operatorname{span}(e_1,e_2)\oplus\mathbb C^m$ 不被原 $t$ 保持，因为 $te_2=be_3$。定理 34.4 的 (34.16) 约化论证不适用于 (36.1)。下文的前两格读取直接在完整原空间中运输。

### 36.2 原轴的前两格读取与完整三维有限运输

**命题 36.2（被三残量分类消费的前两格刚性）。** 保持定义 32.1，允许 $B$ 为任意原 Hermitian 三维块，仅要求 $V=e_1v$、$v(\ker D_{\rm env})\ne\{0\}$，$D_{\rm env}$ 任意原有限 Hermitian 块。若全部原 PB 成立，或在任一指定有限正质量上全称成立，则必有 $s_1=s_2=0$。若 $(s_1,s_2)\ne(0,0)$，任意 $s_3$、任意指定 $\mu>0$ 都有同一原环境中的有限严格违反，并可使两笔预算同时严格正。此命题的活消费者是定理 36.4；它不分类任意 $B$ 下的第三格残量。

证明。只消费父卷 (29.19)–(29.22)、(30A.11)–(30A.18) 中属于轴 $1$ 的两条读取，不使用轴 $2$ 的像向量。将其 $u,w$ 补第三坐标零，将 $X$ 补第三行、列零。第一条的完整参数为

$$
\begin{gathered}
u^{(a)}=e_1,\qquad X^{(a)}=\operatorname{diag}(1,1,0),
\qquad w^{(a)}=-e_1,\\
(\alpha_+,\alpha_-)=(1/3,1),\qquad
(\beta_+,\beta_-)=(0,-4),\qquad
(\zeta_+,\zeta_-)=(-\iota/3,-4+\iota).
\end{gathered}
\tag{36.3}
$$

依 (32.5) 的齐次定义，它的三维作用列准确为

$$
\mathsf R_+=\tfrac32e_1,\quad
\mathsf R_-=\tfrac12e_1,\quad
\mathsf S_+=-\tfrac\iota2e_1,\quad
\mathsf S_-=(-2+\tfrac\iota2)e_1,
\qquad F_a(S)=-s_1 .
\tag{36.4}
$$

两份比例 $\mathsf S_\delta=\zeta_\delta\mathsf R_\delta$ 逐项成立。第二条为父卷的混合轴 $1$ 读取：

$$
\begin{gathered}
 u^{(m)}=\frac{(-8+10\iota,\ 5-4\iota,\ 0)^{\mathsf T}}{\sqrt{205}},\qquad
 w^{(m)}=\frac{(1-\iota,0,0)^{\mathsf T}}{\sqrt{205}},\\
 X^{(m)}=\begin{pmatrix}
 1&(55+3\iota)/41&0\\
 (55-3\iota)/41&2&0\\0&0&0
 \end{pmatrix},\\
 (\alpha_+,\alpha_-)=(4/5,2/17),\qquad
 (\beta_+,\beta_-)=(-3/5,-9/17),\\
 (\zeta_+,\zeta_-)=\bigl((-3-4\iota)/5,\ (-9+2\iota)/17\bigr).
\end{gathered}
\tag{36.5}
$$

两份 $u$ 都是单位向量；第一份是轴向量，第二份的前两坐标均非零。运输不要求第一份也双非零。为逐列核对第二份，直接乘同一个 Hermitian $X^{(m)}$ 得

$$
\begin{aligned}
\sqrt{205}\,X^{(m)}u^{(m)}&=(-1+5\iota,\ 6\iota,\ 0)^{\mathsf T},\\
\sqrt{205}\,X^{(m)}Cu^{(m)}&=(6,\ 10-2\iota,\ 0)^{\mathsf T},\\
\sqrt{205}\,(w^{(m)}-\iota X^{(m)}u^{(m)})&=(6,6,0)^{\mathsf T},\\
\sqrt{205}\,\mathsf R_+&=(-4+2\iota,\ -7+\iota,\ 0)^{\mathsf T},\\
\sqrt{205}\,\mathsf R_-&=(2+8\iota,\ 7+11\iota,\ 0)^{\mathsf T},\\
\sqrt{205}\,\mathsf S_+&=(4+2\iota,\ 5+5\iota,\ 0)^{\mathsf T},\\
\sqrt{205}\,\mathsf S_-&=(-2-4\iota,\ -5-5\iota,\ 0)^{\mathsf T}.
\end{aligned}
\tag{36.6}
$$

将 (36.5) 的两份 $\zeta$ 分别乘 (36.6) 的两份 $\mathsf R$ 就得到对应 $\mathsf S$。所有第三坐标都准确为零，因为这里的齐次列只使用 $C,X,u,w$，而不是删除了实际 $B$ 的输出。两份 $\alpha$ 都严格正且有限，虚部方向为 $-\delta\iota\alpha_\delta$。配对为

$$
F_m(S)=\operatorname{Re}((w^{(m)}-\iota X^{(m)}u^{(m)})^*Su^{(m)})
=\frac{-48s_1+30s_2}{205} .
\tag{36.7}
$$

因此 $(s_1,s_2)\ne(0,0)$ 时，(36.4)、(36.7) 至少一条非零；$s_3u_3=0$ 仅使这次配对不读取第三格。

下面明确消费本卷 (32.21)–(32.28) 的三维原环境运输。取所选核对的 $F\ne0$，以定义 32.1 的同一原逆取 $y=Jw$，所以 $Vy=w$、$D_{\rm env}y=0$。对实 $q$ 令 $x_q=qX\oplus0_m$、$\xi_q=(u,qy)$。完整作用列为

$$
\begin{aligned}
R_\delta(x_q)\xi_q
 &=q(\mathsf R_\delta,0)
   +\bigl(-\delta(C\circ B)u,-\delta V^*Cu/2\bigr),\\
S_{\delta,0}(x_q)\xi_q
 &=q(\mathsf S_\delta,0)
   +\bigl((B+\delta\iota[C,B]/2)u,
              V^*(I-\delta\iota C/2)u\bigr),\\
S_{\delta,S}(x_q)\xi_q
 &=S_{\delta,0}(x_q)\xi_q+\delta(Su,0),\qquad
 t\xi_q=(Bu+qw,V^*u).
\end{aligned}
\tag{36.8}
$$

下标 $0$ 仅去掉残量，不改变实际 $t$。特别在 (36.1) 中，常数列包含

$$
(C\circ B)u=\beta u_1e_1+\tfrac{5b}{2}u_2e_3,\qquad
(B+\delta K_\sigma(C,B))u
=\beta u_1e_1+b(1+\delta\iota/2)u_2e_3 .
\tag{36.9}
$$

混合读取的 $u_2\ne0$，这些实际第三格输出确实存在；它们与 $V^*u,V^*Cu$ 一同保留于下式常数项。

写 $\ell_S(q)=\xi_q^*L(x_q)\xi_q$，用所选的正有限 $\alpha_\delta$、实 $\beta_\delta$ 定义

$$
Q_S(q)=\sum_{\delta=\pm1}\left[
 \alpha_\delta\|R_\delta\xi_q\|^2+
 \alpha_\delta^{-1}\|S_{\delta,S}\xi_q-\beta_\delta R_\delta\xi_q\|^2
 \right]-2\ell_S(q).
\tag{36.10}
$$

零残量的原换位恒等式及复平方配方正是 (32.23)：

$$
Q_0(q)=\sum_\delta\alpha_\delta^{-1}
 \|S_{\delta,0}\xi_q-\zeta_\delta R_\delta\xi_q\|^2=Q_0(0).
\tag{36.11}
$$

最后一个等号使用的是 (36.4)、(36.6) 的完整三维比例：各平方内的 $q$ 系数为零。再写 $M_\delta=S_{\delta,0}\xi_q-\beta_\delta R_\delta\xi_q$、$v_S=(Su,0)$，则

$$
\begin{aligned}
Q_S-Q_0={}&2\sum_\delta\delta\alpha_\delta^{-1}
 \operatorname{Re}(M_\delta^*v_S)
 +(\alpha_+^{-1}+\alpha_-^{-1})\|v_S\|^2
 +4\operatorname{Re}((t\xi_q)^*v_S),\\
Q_S(q)={}&4q\operatorname{Re}((w-\iota Xu)^*Su)+\Gamma_S
          =4qF+\Gamma_S,\qquad \Gamma_S=Q_S(0)\in\mathbb R .
\end{aligned}
\tag{36.12}
$$

线性系数来自 $M_\delta$ 的 $q$ 系数 $-\delta\iota\alpha_\delta(\mathsf R_\delta,0)$、$\mathsf R_++\mathsf R_-=2Xu$ 和 $t\xi_q$ 的 $q$ 系数 $(w,0)$。这同时验证符号；$\Gamma_S$ 按 (36.8) 的全输出计算，不丢弃 (36.9)。令

$$
\Lambda=-\frac{\Gamma_S+1}{4F},\qquad
x=x_\Lambda,\quad \xi=\xi_\Lambda,\qquad
Q_S(\Lambda)=-1 .
\tag{36.13}
$$

所有数有限。对实化内积 $\langle a,z\rangle_{\mathbb R}=\operatorname{Re}(a^*z)$，面积不随 $z\mapsto z-\beta a$ 改变，且不超过 $\|a\|\|z-\beta a\|$。逐笔用算术几何平均，(36.10) 因而给

$$
\xi^*L\xi\ge\frac12+
 \sum_\delta\sqrt{B_{\phi_\xi}(R_\delta,S_{\delta,S})},\qquad
\phi_\xi(a)=\xi^*a\xi .
\tag{36.14}
$$

这在正的左侧给严格违反，故也违反原绝对值形式。取 $\xi_\mu=\sqrt\mu\,\xi/\|\xi\|$，其中 $\|\xi\|^2=1+\Lambda^2\|Jw\|^2$，得到质量恰为 $\mu$、差额至少 $\mu/(2\|\xi\|^2)>0$ 的同一原向量泛函。

最后保持该泛函，只将 $x$ 改成 $x+\lambda((E_{12}+E_{21})\oplus0_m)$。两笔预算均是非负实四次以下多项式，各自四次系数按 (32.28) 为

$$
\frac{9\mu^2}{16\|\xi\|^4}>0 .
\tag{36.15}
$$

这一系数只要求单位 $u$ 支撑在前两格，不要求 $u_1u_2\ne0$，故也适用于 (36.3)。两份实零点集有限；原严格差额在零的某个开邻域内仍正，在其中避开这些零点与零选一个有限实 $\lambda$，两笔预算便同时严格正。两种 $\sigma$ 的核等式均只使用 $\iota^2=-1$ 与 $\bar\iota=-\iota$；原 $B,V,D_{\rm env},J$ 不共轭。于是任一非零前两格残量都不可能满足全称 PB，命题得证。∎

### 36.3 非零混合平面上的固定探针与线性差额

**定理 36.3（第三格残量的固定探针严格见证）。** 在 (36.1) 中先取 $s_1=s_2=0$、$s_3=s$。对任意 $s\ne0$、任意指定有限 $\mu>0$ 和任一个分别固定的 $\sigma$，取下列原角探针与原完整代数泛函：

$$
\begin{gathered}
 X|_E=b\begin{pmatrix}0&2+\iota\\2-\iota&0\end{pmatrix},
 \qquad X|_{E^\perp}=0,\\
 u=e_2+\frac{2-\iota}{8}e_3,\qquad \|u\|^2=\frac{69}{64},\qquad
 \phi_\mu(a)=\frac{64\mu}{69}u^*au,\quad \phi_\mu(I)=\mu .
\end{gathered}
\tag{36.16}
$$

则同一个 $X,\phi_\mu$ 的完整数据准确为

$$
\begin{gathered}
 \phi_\mu(L)=-\frac{32\mu sb}{69},\qquad
 \sqrt{B_{\phi_\mu}(R_+,S_+)}=0,\qquad
 \sqrt{B_{\phi_\mu}(R_-,S_-)}=\frac{10\sqrt5\,\mu|sb|}{69},\\
 |\phi_\mu(L)|-\sum_\delta\sqrt{B_{\phi_\mu}(R_\delta,S_\delta)}
 =\frac{32-10\sqrt5}{69}\,\mu|sb|>0 .
\end{gathered}
\tag{36.17}
$$

保持同一泛函，只作 $X_\varepsilon=X+\varepsilon P_E$，便存在 $\eta>0$，使每个 $0<|\varepsilon|<\eta$ 都严格违反原 PB，且两笔预算同时严格正。$X$ 本身不依赖 $s$；严格差额对 $|sb|$ 一次齐次。

证明。所有计算都是原完整空间的作用列；(36.2) 的实际约化性保证这些列留在 $E$，没有用压缩平方代替原平方。记 $B_E=t|_E$、$C_E=c|_E$。原定义逐条给

$$
\begin{gathered}
 h|_E=b\begin{pmatrix}0&1/2-\iota\\1/2+\iota&0\end{pmatrix},\qquad
 k_t|_E=\tfrac52B_E,\qquad (X+h)|_E=k_t|_E,\\
 r|_E=\tfrac52X|_E,\qquad
 K_\sigma(c,t)|_E=b\begin{pmatrix}0&-\iota/2\\\iota/2&0\end{pmatrix},\\
 (r+K_\sigma(c,t))|_E=B_E+2X|_E,\\
 R_+|_E=0,\quad R_-|_E=2X|_E,\qquad
 S_+|_E=2(B_E+X|_E)+sE_{33}|_E,\quad
 S_-|_E=-2X|_E-sE_{33}|_E .
\end{gathered}
\tag{36.18}
$$

其中 $(1-\iota/2)(2+\iota)=5/2$ 核对了第一份消去。又

$$
 X^2|_E=5b^2I_E,\qquad B_E^2=b^2I_E,\qquad
 B_E\circ X|_E=2b^2I_E,
$$

所以原左端算子在 $E$ 上为

$$
 L|_E=2X^2|_E-2B_E^2-4B_E\circ X|_E-2B_E\circ(sE_{33}|_E)
 =-sb\begin{pmatrix}0&1\\1&0\end{pmatrix} .
\tag{36.19}
$$

没有将 $t\circ(r+g)$ 丢掉；正是它的非零混合项留下 (36.19)。$u^*(E_{23}+E_{32})u=1/2$，故 $u^*Lu=-sb/2$，质量因子给 (36.17) 第一项。

为核对预算，置

$$
 a=R_-u=\frac{5b}{4}e_2+2b(2-\iota)e_3,\qquad
 z=E_{33}u=\frac{2-\iota}{8}e_3 .
\tag{36.20}
$$

则 $S_-u=-a-sz$，且逐项内积为

$$
 \|a\|^2=\frac{345b^2}{16},\qquad
 \|z\|^2=\frac5{64},\qquad
 a^*z=\frac{5b}{4}\in\mathbb R,\qquad
 \|a\|^2\|z\|^2-\bigl(\operatorname{Re}(a^*z)\bigr)^2
 =\frac{125b^2}{1024} .
\tag{36.21}
$$

PB 使用的是实化 Gram，不是以 $|a^*z|^2$ 替换实部平方的一般复 Gram；在 (36.21) 这一个内积恰为实数，两者数值相等。对任意自伴原 $U,Z$，原平方准确给

$$
 \phi_\mu(U^2)=\frac{64\mu}{69}\|Uu\|^2,\qquad
 \phi_\mu(U\circ Z)=\frac{64\mu}{69}
                    \operatorname{Re}((Uu)^*Zu) .
\tag{36.22}
$$

加实倍数 $-a$ 不改变实面积，故第二笔面积为
$(64\mu/69)|s|\sqrt{125b^2/1024}=10\sqrt5\mu|sb|/69$；预算本身为 $500\mu^2s^2b^2/4761>0$。第一笔由 $R_+u=0$ 准确为零。$32^2>100\cdot5$ 证明差额正；$s$ 与 $b$ 的两种符号均由绝对值保留，没有把负左侧误作违反。

对实 $\varepsilon$，(36.18) 直接给

$$
\begin{aligned}
 R_+(X_\varepsilon)u&=\varepsilon u,\\
 S_+(X_\varepsilon)u&=2(B_E+X|_E)u+sE_{33}u+\varepsilon C_Eu,\\
 \bigl(S_+(X_\varepsilon)u\bigr)_2&=b(7-\iota)/4+2\varepsilon .
\end{aligned}
\tag{36.23}
$$

$u_2=1$，而最后一项的通常虚部是 $-\sigma b/4\ne0$。所以 $S_+(X_\varepsilon)u$ 对每个实 $\varepsilon$ 都不是 $u$ 的实倍数；$\varepsilon\ne0$ 时第一笔实 Gram 严格正。第二笔预算在零为上述正数，原绝对值差额在零为 (36.17) 的正数；它们均连续。各取一个零邻域保持为零处值的一半以上，再取两邻域交，便有有限 $\eta>0$。因此每个 $0<|\varepsilon|<\eta$ 同时保留第二笔正性与严格违反，并由 (36.23) 支付第一笔正性。质量、环境与泛函均未改变。

取向改变只改变上述演员构造中的 $\iota$，所有恒等式仍由 $\iota^2=-1$、$\bar\iota=-\iota$ 成立。$\beta,v,D_{\rm env}$ 在 $E^\perp$ 保持原值，无须共轭它们。两种取向各自得到同一实预算与绝对值差额。∎

### 36.4 全部三个独立残量的精确分类

**定理 36.4（非零 $23$ 混合原轴像类的全部 PB）。** 对定义 36.1 的每份实际输入、每个分别固定的 $\sigma$，全部原 Hermitian 三演员角探针和全部原完整代数正复线性泛函满足 PB，当且仅当

$$
 \boxed{\quad S=0 .\quad}
\tag{36.24}
$$

对任意指定 $0<\mu<\infty$，只在质量恰为 $\mu$ 的全部原正泛函上全称检验也有同一结论。每个非零 $S$ 均有同一原环境、指定质量、两笔预算同时严格正的有限实际见证。该结论对任意实 $\beta$、任意实非零 $b$、任意有限原 $v,D_{\rm env}$ 满足 (36.1) 成立，不要求 P2、平衡残量或环境可逆。

证明。若 $(s_1,s_2)\ne(0,0)$，直接消费命题 36.2，任意 $s_3$ 已有原三维严格正预算违反。若 $s_1=s_2=0$ 而 $s_3\ne0$，消费定理 36.3 的有限非零 $\varepsilon$ 见证。两种情形穷尽每个非零 $S$，每份违反内部始终使用同一探针、同一原泛函与同一质量；没有把不同读取的面积拼在一起。

若 $S=0$，直接复用 (34.13)、(35.17) 的一般原算子恒等式与全部正泛函复 Cauchy–Schwarz：

$$
 L=\sum_{\delta=\pm1}\delta K_\sigma(R_\delta,S_{\delta,0}),\qquad
 |\phi(K_\sigma(U,Z))|^2
 \le\phi(U^2)\phi(Z^2)-\phi(U\circ Z)^2 .
\tag{36.25}
$$

因此 $|\phi(L)|\le\sum_\delta\sqrt{B_\phi(R_\delta,S_{\delta,0})}$ 对每个原正复线性泛函成立，包括混合与奇异密度、零预算及任意有限质量；充分性没有仅从向量态外推。质量零的正泛函为零泛函，仍是零等式，不能单独强制 $S=0$。这证明全部断言。$b=0$ 的输入直接复用定理 34.4，不另造同义分类。∎

### 36.5 与既有两根工具、同时核盲区及完整来源的关系

父卷 §30A 的轴读取在命题 36.2 中直接消费，本卷 (32.21)–(32.28) 的原空间有限运输亦被直接消费；它们不计为新的数学机制。特别，(36.8)–(36.12) 对任意 $B$ 的应用只支付前两格，(36.9) 说明非零 $23$ 作用并未被压缩掉。定理 36.3 的固定 $X$、具体列 (36.18)–(36.23) 与有限线性 $|bs|$ 差额是这批输入上的 $\texttt{repo-derived}$ 构造，不作最优性、全局最小性或历史优先权主张。

[父卷所引承载卷定理 41.2](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md#412-两个明确斜率的有限充分定理) 已用两个实根处理 $c=p+2q$、$t=ptq+qtp+b_\perp$、无支撑与补块连线的域，并携带原固定 P2 前件。该结论按原域保留；本节不把仅更名谱值的两根消去称为新机制。这里实际读取的谱值是 $2,3$，完整原输入还有第一轴及其实际环境连线，定理 36.4 的前件只有 PB；上述钉版定理并不是以这些同一假设直接给出 (36.24) 的现成结论。所需特定应用的完整系数与证明已列在定理 36.3，未把成熟两根思想归为本节原创。

实化 Gram 面积、正泛函复 Cauchy–Schwarz、算术几何平均与有限维连续性是成熟工具，归属沿 §35.4、§32.6 及父卷 §§1、5、27–30A；正泛函背景仍见 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)。原环境逆与核回收保持 §32.6 所引 Penrose／广义 Schur 背景；本节没有以这些文献认证特定系数、文献优先权、实际装置或 Lean／kernel 证明。

定理 33.2 的全称合法同时齐次核盲区保持成立。定理 36.3 起点只有实际有限列的 $R_+u=0$；这不产生 (33.1) 的合法同时齐次核。实际零残量列还满足 $R_-u=a\ne0$、$S_{-,0}u=-a$，实比例 $-1$ 要求 $\alpha_-=0$，不合 (33.1) 的严格正斜率条件；实际 $S_{+,0}u$ 的第二格为 $b(7-\iota)/4\ne0$，也不能与零 $R_+u$ 成比例。这里没有把实际列冒称齐次列，也没有宣称 $F(E_{33})\ne0$ 的合法同时核分离。小扰动运输的是严格 PB 缺额，不是补出被 33.2 排除的核。

**准确剩余域与完整目标。** §35.4、§32.6、父卷 [§6（尤其式 (6.1)）](#6-完整原问题与七项物理合同的精确身份) 与 [§30A.5](#30a5-准确的前件删除来源与完整目标)，以及[有限返回续卷定义 162.1、复用命题 162.2 与定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的同一全文及全部递归钉版来源在本节严格合取保留；这些是完整原合同的准确引用，不以以下说明替代任何对象、公式、量词或七项消费者前件。§§32–35 已得结论均保持其原域。一般任意 $B,V,D_{\rm env}$、每个非零 $\mathcal W$ 的三残量全 PB 分类仍未证明；本节也未去掉实际 $23$ 平面的约化性。一般算子块、完整 $\mathsf H$／任意总 $D$、$\mathcal E_+^D=\mathcal E_-^D$ 与 $N_\omega(\varepsilon)^2\to0$ 仍不由此解决。只在 (36.1) 的固定输出域中，PB 排除全部残量后可消费标准 $K_\sigma$ 的全正 P2；不从完整 $\mathsf H_A(D)$ 删除 A1/P2，也不删除父卷所引定义 41.1 的实际外层预算桥。

完整 Omega 中全部原准备、事件、过程、参考／副本、真正相关联合、零／不等／次归一质量、钟／单位／控制、parent／ready／flags、完整记录与失败／拒绝／停止／销毁／泄漏／遗忘、两侧与逆向返回、固定支持全质量、完整菜单、全部已量化切口及所有旧合法未来均按上述全文保留。复 Hilbert／相干、Born／全菜单、实际张量联合、typed CP／Kraus、完整仪器／TP／更新／Lüders、全部历史／Return、Hamiltonian／物理钟／共同正作用量七项仍仅在各自原完整合同成立时消费。数学 $u,x,\xi,J$ 不生成准备、菜单、复制、相干控制或物理源，不能由旧 Born／CP／QC、密度／历史身份、操作逆或矩阵综合回填这些关系。

§35.4 所列 C139 固定源 §§50–85、C128 原词 §§385–392 及有限返回 §162 的已付成果均按原域保留。实际来源仍须供应 [C139 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 对字面 $\tau;T_P$ 指定接受族的准备无关准确实际接受关联，覆盖全部原准备、切口、参考／副本、合法分析词／树、固定支持全质量与完整菜单。CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及有限返回定义 164.1 所区分的原 $B_{r_\star}$ 活动接头：读后同一完整活动输入保留原参考、控制、钟并对全部旧合法未来真实 Return。另增查询服务和这份面积见证都不构造该接头。完整原 Omega 量子起源、无缺口来源的完整量子公理候选与整体严格更简目标仍为进行中的未完成目标；局部分类不改其完成判据。

### 36.6 中文几何：让真实混合留下可读的面积缺额

前两格的误差用父卷已有的两把尺读取。一把正对第一轴，另一把同时穿过第一、第二格；它们对两个误差给不成比例的实读数，所以不能同时抵消。现在第二格确实连着第三格，这两把尺的实际作用也会落到第三格。完整三维运输把这些输出全部计入有限常数，齐次方向仍使二次代价相消；非零误差留下的一次项便能在一个有限尺度上超过它。这里没有剪断连线，也没有把压缩后的平方冒充原平方。

前两格清零后，第三格仍不能靠合法同时核读取看见，但完整 PB 比核读取更强。在第二、第三格上选同一个固定探针，它与真实混合准确相配，使第一张面积暂时为零。真实混合与第三格误差共同给左端一个 $|bs|$ 量级的非零读数；第二张面积也同量级增长，却只有 $10\sqrt5$ 对 $32$ 的系数。两张面积的和因而严格不够。混合再小，只要实际 $b\ne0$，每个实际 $s\ne0$ 都留下正缺额；这不是只排除足够大的误差，也不是把未排除区域当作成立区域。

再给探针对角加一个足够小的实数，第一列由零变成读取方向本身，而第二列仍带有无法与它实平行的虚部，第一张面积立即变正。第二张面积和已有严格缺额因连续性继续为正。这一步说明边界上的发现可以成为两笔预算都正的有限见证，却不制造合法同时核，更不取消 33.2 的盲区。所得结论只排除了这批真实混合输入的全部对角误差；真实分析器、活动就绪与原完整返回仍须由原世界的来源关系供应。

## 新增锚（本行以下为后续增补区）

## 37. 原环境零模的精确向量列运输与任意离面连线下的三残量刚性

本节的 §§37.1–37.7、定义／定理 37.x 与公式 (37.x) 均为本卷局部编号；§§32–36 及卷首对父卷 §§1–31（含 §30A）的钉版约定不变。原算子、全部原 Hermitian 角探针和全部原正复线性泛函严格取 (32.1)–(32.3)。本节以同一原环境的零模补偿第一轴作用，再解探针的两个离面条目，使完整 PB 所需的作用列准确运输；这一步允许任意 Hermitian 的 $23$ 块。其活消费者在该块对角为零、复交叉项任意的整类中消去全部三个残量，实际 $23$ 平面无需对原 $t$ 约化。

### 37.1 任意 Hermitian 平面块与同一原零模

**定义 37.1（原输入与二维比较资料）。** 在定义 32.1 的同一原空间中，取任意有限 $m\ge1$，按 $\mathbb Ce_1\oplus E\oplus\mathbb C^m$、$E=\operatorname{span}_{\mathbb C}(e_2,e_3)$ 写

$$
\begin{gathered}
 C_E=\operatorname{diag}(2,3),\qquad
 c=\operatorname{diag}(1,C_E,0_m),\qquad P=I_3\oplus0_m,\\
 t=\begin{pmatrix}
 \beta&a&v\\ a^*&T&0\\ v^*&0&D_{\rm env}
 \end{pmatrix},\qquad
 \beta\in\mathbb R,\quad a=(a_2,a_3)\in M_{1,2}(\mathbb C),\quad T=T^*\in M_2(\mathbb C),\\
 D_{\rm env}=D_{\rm env}^*,\qquad
 v\in M_{1,m}(\mathbb C),\qquad v(\ker D_{\rm env})\ne\{0\},\\
 S=\operatorname{diag}(s_1,s_2,s_3),\quad s_j\in\mathbb R,\qquad
 g=K_\sigma(c,t)+(S\oplus0_m),\qquad \iota=\sigma i,\quad \sigma=\pm1 .
\end{gathered}
\tag{37.1}
$$

这里 $V=e_1v$，原 $\mathcal W=\mathbb Ce_1\ne0$。$\beta,a,T,v,D_{\rm env}$ 均为固定原数据；$a$ 的大小和相位不受限制。只要 $a\ne0$，原 $t$ 就不保持 $E$。选同一原环境中的 $z_0$ 满足 $D_{\rm env}z_0=0$、$vz_0=1$：取任一 $y\in\ker D_{\rm env}$ 且 $vy\ne0$，令 $z_0=y/(vy)$ 即可，未改变环境矩阵。

为说明运输，给定任意 $X=X^*\in M_2(\mathbb C)$，只在二维比较资料中定义

$$
\begin{gathered}
 S_E=\operatorname{diag}(s_2,s_3),\qquad
 h_E=\frac\iota2[C_E,X],\quad k_E=\frac{C_ET+TC_E}{2},\\
 r_E=\frac{C_EX+XC_E}{2},\qquad
 g_E=\frac\iota2[C_E,T]+S_E,\\
 R_{\delta,E}=X+\delta(h_E-k_E),\qquad
 S_{\delta,E}=T+\delta(r_E+g_E),\qquad \delta=\pm1,\\
 L_E=-2X\circ(h_E-k_E)-2T\circ(r_E+g_E),\qquad
 \psi_u(A)=u^*Au .
\end{gathered}
\tag{37.2}
$$

这些是比较用的矩阵表达式，不是把原 $t$ 换成另一输入。以 $\jmath_E:E\hookrightarrow\mathcal H$ 表示标准等距包含；所有原平方仍在完整 $M_{m+3}(\mathbb C)$ 中计算。

### 37.2 两个离面条目与四列的实际抵消

**定理 37.2（任意 $T$ 的精确原向量列运输）。** 对每份 (37.1)、每个分别固定的 $\sigma$、每个 $u=(u_2,u_3)^{\mathsf T}\in E$ 满足 $u_2u_3\ne0$，以及每个 Hermitian $X$，置

$$
\begin{gathered}
 p=au,\qquad q=aC_Eu,\qquad w=-p z_0,\qquad
 \xi=(0,u,w),\\
 \ell=\left(-\frac{\iota q}{u_2},\frac{\iota q}{u_3}\right),\qquad
 x=\begin{pmatrix}0&\ell&0\\\ell^*&X&0\\0&0&0_m\end{pmatrix}.
\end{gathered}
\tag{37.3}
$$

则 $x=x^*=PxP$，所有条目有限，且同一份原向量、原探针上的完整作用列满足

$$
\begin{gathered}
 x\xi=\jmath_E Xu,\qquad t\xi=\jmath_E Tu,\\
 (h-k_t)\xi=\jmath_E(h_E-k_E)u,\qquad
 (r+g)\xi=\jmath_E(r_E+g_E)u,\\
 R_\delta\xi=\jmath_E R_{\delta,E}u,\qquad
 S_\delta\xi=\jmath_E S_{\delta,E}u,\\
 \xi^*L\xi=u^*L_Eu,\qquad
 B_{\phi_\xi}(R_\delta,S_\delta)
 =B_{\psi_u}(R_{\delta,E},S_{\delta,E}),\qquad
 \phi_\xi(A)=\xi^*A\xi .
\end{gathered}
\tag{37.4}
$$

对任意指定有限 $\mu>0$，令

$$
 N_u=\|\xi\|^2=\|u\|^2+|au|^2\|z_0\|^2>0,\qquad
 \phi_\mu(A)=\frac\mu{N_u}\xi^*A\xi .
\tag{37.5}
$$

则 $\phi_\mu$ 是完整原代数上的正复线性泛函，质量恰为 $\mu$；原 PB 的左端及每笔面积分别准确等于二维比较资料相应值的 $\mu/N_u$ 倍。因此任何这样的 $X,u$ 上的严格向量 PB 违反，连同其每笔预算的正性，都运输到同一原输入、同一原环境和指定质量。对固定 $u$，同一 $\xi,\ell,N_u$ 同时适用于全部 Hermitian $X$。

证明。首先逐项核对复数与共轭：$x$ 的下三角是所写上三角的伴随，不要求 $a,u,q$ 为实。$\iota^2=-1$、$\overline\iota=-\iota$，而

$$
 \ell u=-\iota q+\iota q=0,\qquad
 \ell C_Eu=-2\iota q+3\iota q=\iota q,\qquad
 vw=-p,\quad D_{\rm env}w=0 .
\tag{37.6}
$$

现在直接作用于完整原向量，按 $e_1,E,\mathrm{env}$ 三块列出

$$
\begin{array}{c|ccc}
 &e_1&E&\mathrm{env}\\ \hline
 x\xi&0&Xu&0\\
 xc\xi&\iota q&XC_Eu&0\\
 cx\xi&0&C_EXu&0\\
 t\xi&au+vw=0&Tu&0\\
 tc\xi&q&TC_Eu&0\\
 ct\xi&0&C_ETu&0
\end{array}
\tag{37.7}
$$

这里没有隐去环境输出。$x$ 的环境行恒零；$t\xi$ 的环境行是 $v^*0+D_{\rm env}w=0$，$tc\xi$ 的环境行是 $v^*0=0$，$ct\xi$ 的环境行由原 $c$ 的环境零块给零。$\beta$ 因 $\xi_1=(c\xi)_1=0$ 不参与这些列，但仍是原 $t$ 的条目。

由 (37.7) 取原换位和 Jordan 乘积，得到各自完整的四列

$$
\begin{array}{c|ccc}
 &e_1&E&\mathrm{env}\\ \hline
 h\xi&q/2&h_Eu&0\\
 k_t\xi&q/2&k_Eu&0\\
 r\xi&\iota q/2&r_Eu&0\\
 g\xi&-\iota q/2&g_Eu&0
\end{array}
\tag{37.8}
$$

例如 $h\xi$ 的第一格是 $\iota(-\iota q)/2=q/2$；$g\xi$ 的第一格是 $\iota(-q)/2$，残量在该格的作用为 $s_1\xi_1=0$。所以 $q\ne0$ 时，四个第一轴输出都非零，分别在 $h-k_t$ 和 $r+g$ 中准确抵消；$q=0$ 时这些第一格按同一等式为零。不能先删去四列的第一格再计算。由此才得到 (37.4) 的前六个作用列等式。

为核对全部原乘积，使用自伴算子的标准列恒等式：对于任意原 $U=U^*,Z=Z^*$，

$$
 \xi^*U^2\xi=\|U\xi\|^2,\qquad
 \xi^*(U\circ Z)\xi=\operatorname{Re}((U\xi)^*Z\xi).
\tag{37.9}
$$

这是 $\xi^*UZ\xi=(U\xi)^*Z\xi$ 与其共轭的半和，不是压缩平方推断。对前六列代入，原左端准确为

$$
\begin{aligned}
 \xi^*L\xi
 &=-2\operatorname{Re}((x\xi)^*(h-k_t)\xi)
   -2\operatorname{Re}((t\xi)^*(r+g)\xi)\\
 &=-2\operatorname{Re}((Xu)^*(h_E-k_E)u)
   -2\operatorname{Re}((Tu)^*(r_E+g_E)u)
 =u^*L_Eu .
\end{aligned}
\tag{37.10}
$$

两笔原平方和 Jordan 乘积也分别是同一两列的范数及实内积。因此

$$
\begin{aligned}
 B_{\phi_\xi}(R_\delta,S_\delta)
 &=\|R_{\delta,E}u\|^2\|S_{\delta,E}u\|^2
   -\bigl(\operatorname{Re}((R_{\delta,E}u)^*S_{\delta,E}u)\bigr)^2\\
 &=B_{\psi_u}(R_{\delta,E},S_{\delta,E}) .
\end{aligned}
\tag{37.11}
$$

此处仍为 PB 的实 Gram 行列式，没有将实部平方改成复内积绝对值平方，也没有断言 $L\xi=\jmath_E L_Eu$ 或全部原算子的乘积交织。最后 $\xi$ 的三个正交块给 (37.5) 的范数；$A\ge0$ 时 $\xi^*A\xi\ge0$，故 $\phi_\mu$ 为正且 $\phi_\mu(I)=\mu$。正缩放 $\mu/N_u$ 使 $L$ 的评价及每笔面积各乘一次该因子，预算本身乘其平方。$\ell,w,N_u$ 不含 $X$，所以整个固定 $u$ 的探针族及其扰动共用它们。所有计算对两种分别固定的 $\sigma$ 成立，原 $\beta,a,T,v,D_{\rm env}$ 无需共轭或改变。∎

定理 37.2 是针对给定 $u$ 的完整向量泛函运输。更换 $u$ 一般会改变补偿行 $\ell$，因此不声称对一份固定原探针建立任意混合正泛函的二维等价。它也没有给出对原 $t,x,h,k_t,r,g$ 共同不变的固定子空间。$a\ne0$ 时 $E$ 对原 $t$ 不约化，(37.8) 显示四个原算子各自的作用列也可离开 $E$；留下的是指定组合在指定原向量上的准确抵消。

### 37.3 零对角平面块的整类结论与非零实混合见证

**定理 37.3（任意复 $23$ 连线、任意离面列的三残量分类）。** 保持 (37.1) 的全部原数据和量词，仅将平面块限定为

$$
 T=T_z=\begin{pmatrix}0&z\\\overline z&0\end{pmatrix},\qquad z\in\mathbb C .
\tag{37.12}
$$

则对每个分别固定的 $\sigma$，全部原 Hermitian 三演员角探针与完整原代数上的全部正复线性泛函满足 (32.3)，当且仅当 $S=0$。任意指定有限 $\mu>0$ 上的全称检验也给同一允许集。每个非零 $S$ 在同一原输入上都有质量恰为 $\mu$、两笔原预算同时严格正的有限实际角探针见证。$\beta,a_2,a_3,z$ 的大小及相位不受小量限制；$z=0$ 也包含在内。不假设 P2、平衡残量、环境可逆或未知总响应映射。

证明先处理必要性。若 $(s_1,s_2)\ne(0,0)$，直接消费命题 36.2：它已经允许任意原 Hermitian $B$，包含 (37.1)、(37.12) 的全部 $\beta,a,z$，且允许任意 $s_3$。同一原环境、指定质量及两正预算的有限严格违反均由该命题供应，无须重新证明前两格的运输。所以全称 PB 必先给 $s_1=s_2=0$。以下只需对 $s=s_3\ne0$ 取得第三格违反。

先取实 $z=b\ne0$。直接使用定理 36.3 在二维比较资料中的既有探针与向量，参数准确为

$$
 X_b=b\begin{pmatrix}0&2+\iota\\2-\iota&0\end{pmatrix},\qquad
 u_b=\begin{pmatrix}1\\(2-\iota)/8\end{pmatrix},\qquad
 \|u_b\|^2=69/64,\qquad S_E=\operatorname{diag}(0,s).
\tag{37.13}
$$

两个坐标均非零，可直接代入定理 37.2。原定理 (36.17) 用 $\phi=64\mu\psi_{u_b}/69$；去掉这一归一因子，其已经证明的原列数据正是

$$
\begin{gathered}
 \psi_{u_b}(L_E)=-sb/2,\qquad
 \sqrt{B_{\psi_{u_b}}(R_{+,E},S_{+,E})}=0,\\
 \sqrt{B_{\psi_{u_b}}(R_{-,E},S_{-,E})}
 =\frac{5\sqrt5}{32}|sb|,\qquad
 \Delta_E:=|\psi_{u_b}(L_E)|-
   \sum_\delta\sqrt{B_{\psi_{u_b}}(R_{\delta,E},S_{\delta,E})}
 =\frac{16-5\sqrt5}{32}|sb|>0 .
\end{gathered}
\tag{37.14}
$$

这只复用 (36.18)–(36.22) 已付的二维列运算，没有将原非约化 $E$ 上的压缩乘积当作完整乘积。实际原探针取 (37.3) 的补偿行，$q=0$ 时该行按式为零；实际原向量具有同一环境分量 $w=-au_bz_0$，它也允许为零。由定理 37.2，指定质量上的完整原差额准确是

$$
 \Delta_\mu=\frac\mu{N_{u_b}}\,
               \frac{16-5\sqrt5}{32}|sb|>0,\qquad
 N_{u_b}=\frac{69}{64}+|au_b|^2\|z_0\|^2 .
\tag{37.15}
$$

$16^2>25\cdot5$ 给严格正性，包含 $s,b$ 的所有符号。$a$ 任意大只改变有限正分母和补偿条目，不需要把离面连线限制在连续性邻域内。

为了使两笔预算同时正，仍消费定理 36.3 的同向量扰动 $X_{b,\varepsilon}=X_b+\varepsilon I_E$。在完整原空间中，这准确对应 $x_\varepsilon=x+\varepsilon P_E$，补偿行、$\xi$ 与质量均不变。(36.23) 给出的两列是

$$
\begin{gathered}
 R_{+,E}(X_{b,\varepsilon})u_b=\varepsilon u_b,\\
 S_{+,E}(X_{b,\varepsilon})u_b
 =2(bJ+X_b)u_b+sE_{33}|_E u_b+\varepsilon C_Eu_b,\qquad
 J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
 \bigl(S_{+,E}(X_{b,\varepsilon})u_b\bigr)_2
 =b(7-\iota)/4+2\varepsilon .
\end{gathered}
\tag{37.16}
$$

最后一行下标 $2$ 是原第二演员的坐标，即 $E$ 的第一格。对每个实 $\varepsilon$，该坐标的通常虚部为 $-\sigma b/4\ne0$，而 $(u_b)_2=1$，所以第二列不可能是 $u_b$ 的实倍数。故 $\varepsilon\ne0$ 时第一笔实 Gram 预算严格正。第二笔预算在零处为 $125s^2b^2/1024>0$；差额在零处为 (37.14) 的正数。两者关于实 $\varepsilon$ 连续：作用列仿射，预算为非负多项式，平方根在包括零的非负半轴连续。分别取零邻域使各值超过零处的一半，再取交，便有有限 $\eta>0$，每个 $0<|\varepsilon|<\eta$ 都保留两笔正预算与严格违反。定理 37.2 对整个扰动族使用同一 $u_b,\xi,\ell$，故原完整数据也逐项如此。这一小扰动只把第一笔预算从边界移到内部；它没有缩小 $\beta,a,v,D_{\rm env}$ 的原允许域。

### 37.4 零混合直接消费既有两正预算探针

当 $z=b=0$ 时，不把 (37.13) 的零探针当作见证，也无需新造连续性论证。直接消费定理 35.1 已经有两笔严格正预算的探针，二维对应为

$$
 u_0=\begin{pmatrix}1\\1\end{pmatrix},\qquad
 X_{s,0}=\frac{s}{2}\begin{pmatrix}-5&4+\iota\\4-\iota&-4\end{pmatrix},\qquad T=0 .
\tag{37.17}
$$

定理 35.1 的质量因子为 $\mu/2$；其 (35.2)–(35.4) 给出的未归一列数据因此为

$$
\begin{gathered}
 \psi_{u_0}(L_E)=\frac{9s^2}{4},\qquad
 \sqrt{B_{\psi_{u_0}}(R_{+,E},S_{+,E})}=\frac{5s^2}{8}>0,\\
 \sqrt{B_{\psi_{u_0}}(R_{-,E},S_{-,E})}=\frac{5\sqrt5\,s^2}{8}>0,\qquad
 \Delta_E=\frac{13-5\sqrt5}{8}s^2>0 .
\end{gathered}
\tag{37.18}
$$

$13^2>25\cdot5$ 给严格性。两个坐标非零，所以仍由定理 37.2 取原补偿行、原 $w=-(a_2+a_3)z_0$，原左端与两笔面积准确各乘 $\mu/N_{u_0}$，其中 $N_{u_0}=2+|a_2+a_3|^2\|z_0\|^2$。两笔预算本来就正，无须扰动。这是对既有严格探针的消费；定理 34.4 的原隔离轴分类保持原域，新付的是 $a$ 任意时的原完整作用运输。

### 37.5 任意复交叉项的坐标对应与充分性

对任意 $z\ne0$，记 $\rho=|z|>0$、$d=z/\rho$，取二维对角酉矩阵

$$
 U=\operatorname{diag}(d,1),\qquad
 U^*T_zU=\rho J,\qquad U^*C_EU=C_E,\qquad U^*S_EU=S_E .
\tag{37.19}
$$

第一式的非对角条目为 $\overline d z=\rho$ 与 $\overline z d=\rho$，两对角元仍为零。这实际核对了复相位的方向，不要求原 $a,v$ 为实。取 (37.13) 在 $b=\rho$ 时的 $X'_\rho,u'_\rho$，在原 $E$ 坐标中令

$$
 X=UX'_\rho U^*,\qquad u=Uu'_\rho,\qquad
 X_\varepsilon=U(X'_\rho+\varepsilon I_E)U^*=X+\varepsilon I_E .
\tag{37.20}
$$

$u$ 两坐标仍非零。因为 $U$ 与 $C_E,S_E$ 通勤，(37.2) 的每个换位、Jordan 乘积、加和都满足相同共轭关系，例如

$$
 h_E(X)u=U h_E(X'_\rho)u'_\rho,\qquad
 k_E(T_z)u=U k_E(\rho J)u'_\rho,
\tag{37.21}
$$

其余 $r_E,g_E,R_{\delta,E},S_{\delta,E},L_E$ 同理；这些关系分别由 $U^*U=I_E$ 插入每个实际二维乘积得到。因此所有范数、复内积及其实部不变，(37.14)–(37.16) 以 $b=\rho$ 原样成立。再在原固定坐标中用实际 $a$ 计算 $p=au,q=aC_Eu$，应用定理 37.2，使原左端及两笔面积准确各乘 $\mu/N_u$，并取得两正预算严格违反。没有改变或共轭原 $t$：$U$ 只是选取二维探针和向量的数学坐标工具，不是可免费执行的控制，也不对原输入作物理变换。两种 $\sigma$ 均分别成立；原 $a,v,D_{\rm env}$ 始终是原来的一份。

实非零、零和复非零分支覆盖全部 (37.12)。结合命题 36.2，任何非零 $S$ 都已被一个原有限见证排除，且每份见证内部使用同一原泛函、同一探针和同一质量。没有把来自不同向量的两个面积相加。

若 $S=0$，直接复用 (36.25)、(34.13) 及父卷 §1 的一般原算子恒等式与全正泛函复 Cauchy–Schwarz，PB 对完整原代数上的全部正复线性泛函成立，包括混合、奇异、零预算与任意有限质量；此充分性不依赖定理 37.2，也不从纯向量结论外推。质量零的正泛函只有零泛函，给零等式，不能单独迫使 $S=0$。这完成定理 37.3 的全部断言。∎

### 37.6 成熟归属、已删除前件与完整未决边界

定理 37.2 的 (37.3)、(37.6)–(37.11) 及其指定质量对应是 $\texttt{repo-derived}$ 的精确补偿构造。自伴列恒等式、实 Gram／Cauchy–Schwarz、从非零线性泛函选零模原像、对角酉坐标变换和有限维连续性均为成熟工具：正泛函背景沿 §32.6、§35.4、§36.5 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；Hermitian 矩阵和酉坐标运算沿 Horn–Johnson，[*Matrix Analysis*](https://doi.org/10.1017/CBO9781139020411)。原逆和广义 Schur 的既有归属仍按 §32.6 的 Penrose／Higham 引文解释，(37.6) 自身只用原零模及 $vz_0=1$。这些来源不被归为本节特定补偿行或系数的作者。

定理 37.3 直接消费命题 36.2、定理 36.3 和定理 35.1，不将其读取、固定探针或严格面积重新计为新增机制。与定理 36.4 相比，实际删除的是 (36.1) 中 $a=0$ 所保证的原 $23$ 约化前件，并纳入任意复 $23$ 相位及零混合。整个 $a\in\mathbb C^2$ 都在结论域内，特别 $a_2a_3z\ne0$ 时原三个演员的三对连线全非零，大小可任意，不是隔离轴附近的小邻域。父卷定理 17.2 的固定探针环境截面保持两演员原类型，不能作为这里随 $u$ 改变补偿行的现成等价；本卷 §36.5 所引钉版承载卷定理 41.2 保持 $c=p+2q$、无支撑与补块连线及原固定 P2 前件，也不直接给出 (37.1) 的任意离面 PB 单独分类。本节不主张历史优先权、文献穷尽、常数最优、全局最简或 Lean／kernel 认证。

定理 33.2 对全部有限合法同时齐次核的盲区仍成立。定理 37.2 运输的是实际有限作用列，包含实际 $T$ 与残量；(37.14) 是既有边界面积违反，(37.18) 是既有内部面积违反。它们不供应 (33.1) 中两份严格正有限斜率的合法齐次核，也不把任一未排除残量称为合法。本节因而没有从“核配对为零”推出 PB 充分性。

**准确剩余数学域。** 定理 37.2 允许任意 Hermitian $T$，但定理 37.3 的分类仍明确要求 (37.12)。$T$ 的任意非零对角项尚未在这里得到全部第三格残量分类；不能把运输恒等式本身当作这项分类。一般任意 $B,V,D_{\rm env}$、每个非零 $\mathcal W$ 的全部三残量分类仍未证明，尤其一般 $V$ 不必具有 $e_1v$ 的全环境行结构。一般算子值块、完整 $\mathsf H$／任意总 $D$、$\mathcal E_+^D=\mathcal E_-^D$ 与 $N_\omega(\varepsilon)^2\to0$ 仍未由本节解决；没有给出剩余域的非零残量全 PB 模型。只在 (37.12) 的已证固定输出域中，PB 得到 $S=0$ 后可直接消费标准 $K_\sigma$ 的全正 P2；若另已辨识 $g=D(c,t)$，只对这一原输入对得到 $c\circ t-iD(c,t)=ct$（$\sigma=1$）或 $tc$（$\sigma=-1$）。不从完整 $\mathsf H_A(D)$ 删除 A1/P2，也不删除原实际外层预算桥。

**完整原来源与七项消费者。** §32.6、§35.4、§36.5、父卷 [§6 式 (6.1)](#6-完整原问题与七项物理合同的精确身份) 与 [§30A.5](#30a5-准确的前件删除来源与完整目标)，以及[有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的同一全文及全部递归钉版来源在这里严格合取保留。以下说明不替换任何原对象、公式或量词：同一原 $\Omega$/native、$E,C,u,N,\mathcal P,S,D,q,K/J$、全词和跨评价配对、原模式网络及全部绑定不变，旧 $D$ 不被替换。全部原准备、事件、过程、参考／副本、真正相关联合、中央／经典／不等维／静默／无轴块、零／不等／次归一质量、同一真实乘积、同一 $\sigma,t_0$、物理钟／单位／控制、parent／ready／flags、环境、完整输出和细记录、失败／拒绝／停止／销毁／泄漏、真分组遗忘、两侧及逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口与每份完整输出的每个旧合法未来均保留。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不合并，未定义请求不补零。

七项后果仍只在上述原完整条件内消费：共同全词与实际相干准备才给复 Hilbert／相干；原实际事件、完整菜单、固定支持全质量和正质量绑定才给 Born 及其归一；同一真实相关联合、忠实交换腿与共同生成才给张量；整台 typed 箭头的合法接续、真实递归参考、环境／记录／失败／port／post-port、真支持和累计支持运输才给 CP／Kraus；完整 typed 仪器、全部输出失败细记录、实际单位分区、AC、$N_u,X,X_s$、平方根词、接受端、严格正输出质量与射线／校准前件才给 TP／更新／Lüders；全部原历史、记录、真遗忘及每个合法未来的真实返回才给历史／Return；同一实际连续可逆流、实际逆、强连续实现、生成元域、原固定域／resolvent、钟／单位／能量及共同正 $\hbar$ 才给 Hamiltonian。有限返回 §162 的原根关系、全部十一端点、同一 ready 的零活动支及其完整递归合同，以及原 $3s+r\le1$ 预算均保持原义；有限矩阵列不代付其中任何来源。

[C139 固定源卷 §§50–85](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的合法前接、唯一正回溯、下降、固定返回刚性、条件过程比较、整台递归参考、累计支持和近似容量结果，以及 [C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 的同一旧 $D$ 恢复继续按已付原域保留，不倒称缺失。实际分析器仍须为字面旧程序 $\tau;T_P$ 的指定接受族，在全部原准备、切口、参考／副本、合法分析词／树、原坐标、固定支持全质量与完整菜单上，供应 [C139 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的准备无关准确接受证书，保持原支持和未归一标尺；只要求指定当前接受关联，不将其加强为历史双射。矩阵相等、某菜单存在、纯校准、操作逆或矩阵综合均不提供它。

CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及读后同一完整活动输入保留原参考、控制、钟并对全部旧合法未来真实 Return。有限返回定义 164.1 的另增查询候选不等于原 $B_{r_\star}$ 活动接头；本节没有构造该接头。数学 $z_0,u,\xi,x,U$ 不生产准备、原菜单、复制、相干控制或实际装置，不由旧 Born／CP／QC、密度或历史身份回填来源。完整原 Omega 量子起源、无缺口来源的完整量子公理候选及整体严格更简目标仍为进行中的未完成目标，所有原成功条件保持不变。

### 37.7 中文几何：补回真实输出，再让两笔面积共同说话

第二、第三演员所在的平面若连着第一轴，直接在平面里算就会漏掉一段真实输出。这里没有剪断那两根线。先沿原环境中不被环境自身移动的一条零模，放入恰好的复幅度，使原 $t$ 送到第一轴的两笔贡献相消。这个环境向量来自同一个原环境，不是另添一个世界或替换原输入。

探针还要同时应付两把尺：不加谱权重时，它在第一轴的输出为零；加上原来的二、三权重后，它须留下准确的 $\iota q$。两个非零读取坐标允许唯一解出这里选定的两个离面条目。换位尺和 Jordan 尺随后各留下半份第一轴输出：四列一般都不为零，却正好在预算实际使用的两对组合中一减一加地抵消。得到的是这一次读取上的完整列相等，不是整批算子突然共有一个不变平面。

因此两笔预算量到的真实面积，以及同一次读取的左端，恰好都是原二维见证的数值。真实离面连线再大，也只需相应改变这份有限补偿和原向量的归一分母。$23$ 连线非零时，旧固定探针留下与 $|bs|$ 成比例的严格缺额，小改探针对角便让两笔面积同时为正；连线为零时，旧的严格内部探针已经给出两笔正面积。复相位只是数学坐标里的转动，实际原输入保持不动。

所以这批原输入不再需要“第二、第三演员与外面隔离”的前件。但“可以把一份向量见证准确接回原矩阵”仍不同于“原世界已经有那台准备、分析器或返回装置”。任意平面自作用、任意环境像、完整总响应及实际来源仍须各自补齐；局部三残量清零没有把完整量子起源变成已完成目标。

## 新增锚（本行以下为后续增补区）

## 38. 任意 Hermitian 二演员块的零模回接与第三残量刚性

本节只在 §37 的原轴环境中推进剩余的第三格问题。二维比较块现在是任意
Hermitian
$$
T=\begin{pmatrix}d&z\\\overline z&e\end{pmatrix},\qquad d,e\in\mathbb R,\quad z\in\mathbb C,
$$
而残量只写成 $sP_3$，其中 $P_3=\operatorname{diag}(0,1)$、$s\in\mathbb R$。
本节的新结论由逐项矩阵恒等式给出：不把二维矩阵当成实际压缩，不改变原 $B$、原环境或实际探针域。§36.2 继续负责前两格，§37.2 负责把同一份二维见证接回完整原矩阵；本节只支付 §37.6 中「任意 $T$ 的非零对角项尚未分类」这一条在本轴环境内的缺口。

### 38.1 二维资料、面积和质量

固定一个取向 $\sigma\in\{1,-1\}$，写 $\iota=\sigma i$，并在二维空间固定
$C_E=\operatorname{diag}(2,3)$。对 Hermitian $X$ 定义

$$
\begin{gathered}
K(A,B)=\frac{\iota}{2}[A,B],\qquad A\circ B=\frac{AB+BA}{2},\\
h=K(C_E,X),\quad k=C_E\circ T,\quad r=C_E\circ X,\quad
 g=K(C_E,T)+sP_3,\\
R_\delta=X+\delta(h-k),\qquad
S_\delta=T+\delta(r+g),\qquad \delta\in\{1,-1\},\\
L=-2X\circ(h-k)-2T\circ(r+g).
\end{gathered}
\tag{38.1}
$$

对非零 $u\in\mathbb C^2$ 记 $\psi_u(A)=u^*Au$。因为 $R_\delta$、$S_\delta$
自伴，完整 PB 面积的未归一形式是

$$
\mathcal A_\delta(X,u)^2
 =\|R_\delta u\|^2\|S_\delta u\|^2
  -\bigl(\operatorname{Re}((R_\delta u)^*S_\delta u)\bigr)^2
 =B_{\psi_u}(R_\delta,S_\delta)\ge0 .
\tag{38.2}
$$

这里的平方是实化后的 Gram 行列式。任给 $0<\mu<\infty$，

$$
\phi_{\mu,u}(A)=\frac{\mu}{\|u\|^2}u^*Au
\tag{38.3}
$$

是全矩阵代数上的正复线性泛函，且 $\phi_{\mu,u}(I)=\mu$；其左端和每个
面积分别乘以 $\mu/\|u\|^2$，预算本身乘以该因子的平方。

### 38.2 接触恒等式和实际的单侧核

**引理 38.1（残量接触恒等式）。** 令 $P=P_3$。在 (38.1) 的同一固定取向下恒有

$$
L=K(R_+,S_+)-K(R_-,S_-)-2K(X,sP)-2T\circ(sP).
\tag{38.4}
$$

若某个非零 $u$ 满足

$$
R_+u=0,\qquad S_-u=\lambda Xu,\qquad \lambda\in\mathbb R,
\tag{38.5}
$$
则两份面积都为零，并且令

$$
 v=\operatorname{Im}_{\iota}\bigl((Xu)^*Pu\bigr),\qquad
 w=\operatorname{Re}\bigl((Tu)^*Pu\bigr),\qquad
\operatorname{Im}_{\iota}(q)=\frac{q-\overline q}{2\iota},
$$
就有

$$
\psi_u(L)=-2s(w-v).
\tag{38.6}
$$

证明。先把 $g$ 的残量去掉，写 $g_0=K(C_E,T)$、
$A=h-k$、$B_0=r+g_0$。直接展开双线性换位得

$$
K(R_+,S_+)-K(R_-,S_-)=2K(X,B_0+sP)+2K(A,T).
\tag{38.7}
$$

把 $h=K(C_E,X)$、$r=C_E\circ X$、$k=C_E\circ T$、
$g_0=K(C_E,T)$ 代入右端，按乘积的次序展开；含 $C_EX T$、
$TC_EX$、$XTC_E$、$C_ETX$ 的项分别成对抵消，剩余项正好是

$$
2K(X,B_0)+2K(A,T)
 =-2X\circ A-2T\circ B_0.
\tag{38.8}
$$

因此 (38.4) 成立。这是有限矩阵乘法恒等式，没有使用 PB 或压缩平方。
若 (38.5) 成立，则 $R_-u=2Xu$；第一份 Gram 面积含有零列，第二份的两列是
$2Xu$ 与实倍数 $\lambda Xu$，所以两者均为零。对任意自伴 $Y,Z$，
$u^*K(Y,Z)u=-\operatorname{Im}_{\iota}((Yu)^*Zu)$；将 (38.5) 代回
(38.4)，并用 $u^*(T\circ P)u=w$，即得 (38.6)。证毕。

这里使用的是实际含残量的非齐次 $R_+$ 的一个向量核。通常
$R_-u=2Xu\ne0$，也没有为两种符号同时构造残量去掉后的齐次列。因而这
一步不取得 §33.2 所说的两份严格正斜率的同时齐次核，也不产生
$F(E_{33})\ne0$ 的合法同时核分离；§33.2 的核盲区保持原义。

### 38.3 相位回拉与同一取向的符号运输

先处理复相位。若 $z\ne0$，令 $b=|z|>0$、
$d_z=z/b$，并取

$$
U=\operatorname{diag}(d_z,1).
\tag{38.9}
$$

正确的坐标关系是

$$
U^*TU=\begin{pmatrix}d&b\\b&e\end{pmatrix},\qquad
U^*C_EU=C_E,\qquad U^*P_3U=P_3.
\tag{38.10}
$$

第一式的两个非对角项分别是 $\overline{d_z}z=b$ 和
$\overline z d_z=b$；若 $z=0$ 则取 $b=0$、$U=I_E$。对实矩阵 $T'=U^*TU$ 取得 $X'$、$u'$ 后，回到原坐标必须取

$$
X_{\mathrm{orig}}=UX'U^*,\qquad u_{\mathrm{orig}}=Uu'.
\tag{38.11}
$$

因为 $U$ 与 $C_E,P_3$ 对易，每个换位、Jordan 乘积、$R_\delta$、$S_\delta$
和 $L$ 都按 $U(\cdot)U^*$ 共轭；所有范数和实部内积保持不变。这是二维数学坐标的拉回，不是对实际输入施加一个相干控制，也没有改变实际 $B$ 或环境。

在 $T=\begin{pmatrix}d&b\\b&e\end{pmatrix}$ 实对称时，固定同一个
$\iota=\sigma i$，对任意已构造的 $(s,X,u)$ 置

$$
\widetilde s=-s,\qquad \widetilde X=-\overline X,\qquad
\widetilde u=\overline u .
\tag{38.12}
$$

这里的横线是逐项复共轭，取向 $\sigma$ 不变。由于 $C_E,T,P_3$ 为实矩阵，
逐项有

$$
\widetilde R_\delta=-\overline{R_{-\delta}},\qquad
\widetilde S_\delta=\overline{S_{-\delta}},\qquad
\widetilde L=-\overline L .
\tag{38.13}
$$

证明在于 $\widetilde h=\overline h$、$\widetilde k=k$、
$\widetilde r=-\overline r$、$\widetilde g=-\overline g$；其中
$\overline{K(C_E,T)}=-K(C_E,T)$，而残量同时变成 $-sP_3$。于是
$\widetilde R_\delta\widetilde u=-\overline{R_{-\delta}u}$、
$\widetilde S_\delta\widetilde u=\overline{S_{-\delta}u}$。实 Gram 面积不变而两种符号交换，且
$\widetilde u^*\widetilde L\widetilde u=-\overline{u^*Lu}$；
自伴性使这个期望为实数，故绝对值严格差额不变。这是在同一个固定取向下
的符号运输，未把 $\sigma$ 换成 $-\sigma$。

### 38.4 任意 Hermitian 二维块的有限严格向量分类

**定理 38.2（任意 $T$ 的非零残量严格见证）。** 对任意实 $d,e$、任意
$z\in\mathbb C$、任意 $s\ne0$ 和任意固定取向 $\sigma$，存在一个 Hermitian
$X$ 与一个两个坐标均非零的有限向量 $u$，使

$$
|\psi_u(L)|>\mathcal A_+(X,u)+\mathcal A_-(X,u).
\tag{38.14}
$$

下面先给出实 $z=b\ge0$ 的全部分支，再用 (38.9)–(38.13) 回到任意复 $z$ 和
实际给定的符号 $s$。

**情形 A：$e\ne0$ 且 $b>0$。** 先由 (38.12) 取 $se>0$。置

$$
M=-\frac{7e}{2}-s,\qquad
X=\begin{pmatrix}
2d+\dfrac{5b^2}{M}&\iota b\\
-\iota b&-\dfrac e2-s
\end{pmatrix},\qquad
u=\begin{pmatrix}1\\\dfrac{(2+\iota)b}{M}\end{pmatrix}.
\tag{38.15}
$$

因为 $se>0$，$M$ 不为零；$b>0$ 还保证 $u_2u_3\ne0$。直接计算

$$
R_+=\begin{pmatrix}
\dfrac{5b^2}{M}&(-2+\iota)b\\
(-2-\iota)b&M
\end{pmatrix},\qquad
R_+u=0,
\tag{38.16}
$$

确切地，第一行乘以 $u$ 是
$5b^2/M+(-2+\iota)(2+\iota)b^2/M=0$，第二行乘以 $u$ 是
$(-2-\iota)b+(2+\iota)b=0$。

其中 $( -2+\iota)(2+\iota)=-5$，而第二行满足
$(-2-\iota)+(2+\iota)=0$。逐项形成的另一列是

$$
S_-=\begin{pmatrix}
-3d-\dfrac{10b^2}{M}&(1-2\iota)b\\
(1+2\iota)b&\dfrac{5e}{2}+2s
\end{pmatrix}
=-\frac32X-\frac12R_+ .
\tag{38.17}
$$

第一行、第二行的等式分别由
$-3d-10b^2/M=-3X_{11}/2-5b^2/(2M)$、
$5e/2+2s=-3X_{22}/2-M/2$ 以及对应的非对角条目直接给出，故
$S_-u=-3Xu/2$。

系数 $-3/2$、$-1/2$ 都是真实数，所以 (38.5) 可用。令

$$
 n=|u_3|^2=\frac{5b^2}{M^2},\qquad
w=\operatorname{Re}(u^*TP_3u)=\frac{2b^2}{M}+en,\qquad
v=\operatorname{Im}_{\iota}(u^*XP_3u)=\frac{2b^2}{M}.
\tag{38.18}
$$

第一项来自 $b u_3$ 的实部，第二项来自
$\iota b u_3=(-1+2\iota)b^2/M$；$X_{22}$ 项为实数。故
$w-v=en$，由 (38.6)

$$
\psi_u(L)=-2sen=-\frac{10seb^2}{M^2}\ne0,\qquad
\mathcal A_+=\mathcal A_-=0 .
\tag{38.19}
$$

所有分母均已在 $M\ne0$ 处核对，$d$ 没有任何限制。

**情形 B：$e\ne0$ 且 $b=0$。** 取 $X=0$、$u=(\rho,1)^{\mathsf T}$。此时

$$
R_\delta u=(-2\delta d\rho,-3\delta e)^{\mathsf T},\qquad
S_\delta u=(d\rho,e+\delta s)^{\mathsf T},\qquad
\psi_u(L)=-2se .
\tag{38.20}
$$

两列为实列，故二维实面积就是行列式的绝对值：

$$
\mathcal A_\delta=|d\rho|\,|\delta e-2s|,\qquad
H_0=|e-2s|+|e+2s|>0 .
\tag{38.21}
$$

若 $d\ne0$，取
$\rho=|se|/(|d|H_0)>0$；则两笔面积之和是 $|se|$，而
$|\psi_u(L)|=2|se|$。若 $d=0$，取 $\rho=1$，两笔面积都为零而左端为
$2|se|$。所以两种情况下都有有限严格差额，且两个坐标均非零。

**情形 C：$e=0$、$d\ne0$ 且 $b\ge0$。** 先由 (38.12) 取 $ds>0$。置

$$
H=\sqrt{b^2+\frac{8ds}{5}},\qquad q=b+H,\qquad
\theta=\frac{b}{2H},
\tag{38.22}
$$

以及

$$
X=\begin{pmatrix}
-\dfrac{5q^2}{4s}&(2+\iota)b+\dfrac{(6+8\iota)H}{5}\\
(2-\iota)b+\dfrac{(6-8\iota)H}{5}&-\dfrac{2Hs}{q}
\end{pmatrix},\qquad
u=\begin{pmatrix}1\\\dfrac{q(1-\iota/2)}{s}\end{pmatrix}.
\tag{38.23}
$$

由于 $ds>0$，$H>b\ge0$、$q>0$、$H,s,q$ 均非零；故根式为实数，矩阵和向量
的每个条目有限，且两个坐标均非零。利用
$H^2-b^2=8ds/5$，逐项得到

$$
R_+=\begin{pmatrix}
-\dfrac{5Hq}{2s}&(2+\iota)H\\
(2-\iota)H&-\dfrac{2Hs}{q}
\end{pmatrix},\qquad R_+u=0,
\tag{38.24}
$$

并得到另一个完整的算子恒等式。其逐项矩阵为

$$
S_-=\begin{pmatrix}
 d+\dfrac{5q^2}{2s}&(-4-2\iota)b-(3+4\iota)H\\
 (-4+2\iota)b-(3-4\iota)H&\dfrac{6Hs}{q}-s
\end{pmatrix}
=-\frac52X+\theta R_+ .
\tag{38.25}
$$

第一行乘以 $u$ 时，
$-5Hq/(2s)+(2+\iota)Hq(1-\iota/2)/s=0$；第二行乘以 $u$ 时，
$(2-\iota)H-2H(1-\iota/2)=0$。因此 $R_+u=0$，且
$S_-u=-5Xu/2$；$-5/2$ 与 $\theta=b/(2H)$ 都是真实数。

计算接触项时，

$$
 w=\operatorname{Re}(u^*TP_3u)=\frac{bq}{s},\qquad
 v=\operatorname{Im}_{\iota}(u^*XP_3u)=\frac{Hq}{s},
\tag{38.26}
$$

因为
$ (1-\iota/2)X_{12}=5b/2+(2+\iota)H$，而 $X_{22}|u_3|^2$
是实数。因此 $w-v=(b-H)q/s=(b^2-H^2)/s=-8d/5$，由 (38.6)

$$
\psi_u(L)=\frac{16ds}{5}>0,\qquad
\mathcal A_+=\mathcal A_-=0 .
\tag{38.27}
$$

这也覆盖 $b=0$、$d\ne0$，没有小耦合或小对角项的假设。

**情形 D：两条已付分支。** 当 $d=e=0$、$b>0$ 时，直接消费 §36.3 的纯混合见证

$$
X=b\begin{pmatrix}0&2+\iota\\2-\iota&0\end{pmatrix},\qquad
u=\begin{pmatrix}1\\(2-\iota)/8\end{pmatrix},\qquad
\psi_u(L)=-\frac{sb}{2},\quad
\mathcal A_+=0,\quad
\mathcal A_- =\frac{5\sqrt5}{32}|sb|,
\tag{38.28}
$$

其严格差额是 $(16-5\sqrt5)|sb|/32>0$；这里不重写已付的列乘法。当
$d=e=b=0$ 时直接消费 §35.1 的零矩阵见证

$$
X=\frac{s}{2}\begin{pmatrix}-5&4+\iota\\4-\iota&-4\end{pmatrix},\qquad
u=\begin{pmatrix}1\\1\end{pmatrix},\qquad
\psi_u(L)=\frac{9s^2}{4},\quad
\mathcal A_+=\frac{5s^2}{8},\quad
\mathcal A_- =\frac{5\sqrt5\,s^2}{8},
\tag{38.29}
$$

其严格差额是 $(13-5\sqrt5)s^2/8>0$，且两笔面积已经严格正。

这四种情形穷尽所有 $d,e\in\mathbb R$ 与 $b\ge0$：先按 $e$ 是否为零、再按 $b$ 是否为零，
当 $e=0$ 时按 $d$ 是否为零分开。A、C 的根式和分母已逐项核对，B 的
$H_0$ 非零；D 的两个向量均有两个非零坐标。对一般复 $z$ 用 (38.9)–(38.11)
拉回，对实际符号用 (38.12)–(38.13) 拉回；同一固定取向下，严格差额和有限性均保持。
因此 (38.14) 对所有 $T$、所有 $s\ne0$ 成立。

### 38.5 从边界见证到两笔严格正预算

**引理 38.3（有限内部扰动）。** 保持定理 38.2 所得的同一个 $T,s,u$，对实数
$\varepsilon$ 置 $X_\varepsilon=X+\varepsilon I_E$。则

$$
R_{\delta,\varepsilon}u=R_\delta u+\varepsilon u,\qquad
S_{\delta,\varepsilon}u=S_\delta u+\delta\varepsilon C_Eu .
\tag{38.30}
$$

每个未归一平方面积

$$
G_\delta(\varepsilon)=\|R_{\delta,\varepsilon}u\|^2
 \|S_{\delta,\varepsilon}u\|^2
 -\bigl(\operatorname{Re}((R_{\delta,\varepsilon}u)^*
 S_{\delta,\varepsilon}u)\bigr)^2
\tag{38.31}
$$

都是取值于 $[0,\infty)$ 的实系数多项式，且最高次项为

$$
\bigl(\|u\|^2\|C_Eu\|^2-(u^*C_Eu)^2\bigr)\varepsilon^4
=|u_2|^2|u_3|^2\varepsilon^4 .
\tag{38.32}
$$

证明。(38.30) 只用 $K(C_E,I_E)=0$、
$C_E\circ(X+\varepsilon I_E)=r+\varepsilon C_E$。因此 (38.31) 是实多项式，
非负性是两个实化列的 Gram 行列式。其四次系数由最高次列 $u$ 和
$\delta C_Eu$ 给出；写 $a=|u_2|^2$、$b_0=|u_3|^2$，则

$$
(a+b_0)(4a+9b_0)-(2a+3b_0)^2=a b_0=|u_2|^2|u_3|^2>0.
$$

所以每个 $G_\delta$ 都不是零多项式，两个实根集合均为有限集。记
$\Delta(\varepsilon)$ 为左端绝对值减去两笔平方根；作用列和 $L$ 关于
$\varepsilon$ 连续，平方根在 $[0,\infty)$ 上连续，而定理 38.2 给出
$\Delta(0)>0$。取一个只由连续性得到的非零邻域，使
$\Delta(\varepsilon)>0$，再从其中避开两个有限根集和 $0$，即可选取有限的
$\varepsilon\ne0$，使 $G_+(\varepsilon)>0$、$G_-(\varepsilon)>0$ 且仍严格违反 PB。
这里没有给出统一的 $\varepsilon$ 或量化半径；每个见证只需一个这样的有限选择。
对任意指定 $\mu>0$，用 (38.3) 乘以正因子即可使质量恰为 $\mu$，并保持
两笔预算严格正和严格差额。∎

### 38.6 同一原环境中的精确回接

现在回到 §37.1 的同一完整有限环境，固定

$$
 t=\begin{pmatrix}
 \beta&a&v\\
 a^*&T&0\\
 v^*&0&D
 \end{pmatrix},\qquad
 c=\operatorname{diag}(1,C_E,0_m),\qquad
 S=\bigl(\operatorname{diag}(s_1,s_2,s_3)\bigr)\oplus 0_m,
\tag{38.33}
$$

其中 $\beta\in\mathbb R$、$a\in M_{1,2}(\mathbb C)$、$D=D^*$，并且
$v(\ker D)\ne0$。$B$ 或 $T$、$a$、$v$、$D$ 都是实际原输入的同一份条目，
不作替换。取同一原环境中的 $z_0\in\ker D$ 满足 $vz_0=1$。为使这里的二维式 (38.1) 与
完整三格残量逐项一致，以下专门比较取 $s_2=0$ 并写 $s=s_3$；$s_1$ 可任意，因为
$\xi_1=0$。推论 38.5 的消费者先由 §36.2 取 $s_1=s_2=0$。在这一取值下，
$S=(\operatorname{diag}(s_1,0,s))\oplus0_m$，其 $E$-块残量正好是 $sP_3$；若保留
$s_2\ne0$，$g\xi$ 的 $E$-列会多出 $s_2u_2$，故不在本专门运输断言中。

**定理 38.4（二维严格见证的完整原运输）。** 在上述 $s_2=0$、$s=s_3$ 的专门比较下，
对定理 38.2 或引理 38.3 的任意 $u=(u_2,u_3)^{\mathsf T}$（两个坐标非零）和任意
Hermitian $X$，置

$$
 p=au,\qquad q=aC_Eu,\qquad w_0=-p z_0,\qquad
 \xi=(0,u,w_0),\qquad
 \ell=\left(-\frac{\iota q}{u_2},\frac{\iota q}{u_3}\right),
\tag{38.34}
$$

并在原探针域中取

$$
 x=\begin{pmatrix}0&\ell&0\\\ell^*&X&0\\0&0&0_m\end{pmatrix}.
\tag{38.35}
$$

则 $x=x^*=PxP$。设二维量仍由 (38.1) 计算，完整原量由 (32.1)–(32.2)
计算。逐项有

$$
\ell u=0,\qquad \ell C_Eu=\iota q,\qquad vw_0=-p,\qquad Dw_0=0,
\tag{38.36}
$$

从而完整作用列为

$$
\begin{array}{c|ccc}
 &e_1&E&\mathrm{env}\\ \hline
 x\xi&0&Xu&0\\
 xc\xi&\iota q&XC_Eu&0\\
 cx\xi&0&C_EXu&0\\
 t\xi&0&Tu&0\\
 tc\xi&q&TC_Eu&0\\
 ct\xi&0&C_ETu&0
\end{array}
\tag{38.37}
$$

并且由原换位和 Jordan 乘积得到

$$
\begin{array}{c|ccc}
 &e_1&E&\mathrm{env}\\ \hline
 h\xi&q/2&h_Eu&0\\
 k_t\xi&q/2&k_Eu&0\\
 r\xi&\iota q/2&r_Eu&0\\
 g\xi&-\iota q/2&g_Eu&0
\end{array}
\tag{38.38}
$$

所以

$$
\begin{gathered}
(h-k_t)\xi=(0,(h_E-k_E)u,0),\qquad
(r+g)\xi=(0,(r_E+g_E)u,0),\\
R_\delta\xi=(0,R_{\delta,E}u,0),\qquad
S_\delta\xi=(0,S_{\delta,E}u,0),
\end{gathered}
\tag{38.39}
$$

这里的 $s_1$ 第一格因 $\xi_1=0$ 不产生额外项，而 $s_2=0$ 使 $E$-列没有额外的
$s_2u_2$；所以 (38.37)–(38.39) 的每一列都与 (38.1) 的二维列逐项相同，环境列仍为零，
从而 (38.40) 的完整乘积与两份实 Gram 等式也逐项恢复。对任意原自伴 $U,Z$，
$\xi^*U^2\xi=\|U\xi\|^2$、
$\xi^*(U\circ Z)\xi=\operatorname{Re}((U\xi)^*Z\xi)$；因此完整乘积而非
压缩平方满足

$$
\xi^*L\xi=u^*L_Eu,\qquad
B_{\phi_\xi}(R_\delta,S_\delta)
 =B_{\psi_u}(R_{\delta,E},S_{\delta,E}),\qquad
\phi_\xi(A)=\xi^*A\xi .
\tag{38.40}
$$

证明就是 (38.36) 的四个有限列等式代入 (38.37)–(38.38)，再逐项应用上述
自伴列恒等式；没有丢掉第一轴或环境列。特别，(38.40) 不断言
$L\xi$ 等于嵌入的 $L_Eu$，也不声称全部原算子的乘积在 $E$ 上交织。

原向量的实际归一因子是

$$
N_u=\|\xi\|^2=\|u\|^2+|au|^2\|z_0\|^2>0,\qquad
\phi_{\mu}^{\mathrm{orig}}(A)=\frac{\mu}{N_u}\xi^*A\xi .
\tag{38.41}
$$

它在完整原代数上正且质量恰为 $\mu$；左端和每笔面积准确乘
$\mu/N_u$。只有交叉行 $\ell$（即离面条目）依赖所选 $u$ 而与 $X$ 无关；完整探针 $x$ 仍含 $X$，
故 $X+\varepsilon I_E$ 的扰动仍使用同一个 $\xi,\ell,N_u$。这正是定理 37.2 的
精确运输；它不建立一个固定原探针对所有 $u$ 的混合泛函等价，不要求 $E$ 为 $t$ 的
reducing plane，也不把不同 $u$ 的二维资料拼成一份固定混合泛函。

### 38.7 原轴环境中的三残量全称分类

**推论 38.5（删除零对角 $T$ 限制）。** 在 (38.33) 的同一原轴环境中，令
$T$ 为任意 Hermitian $2\times2$ 块，$a$、$\beta$、$v$、$D$ 任意满足上述条件。
对每个分别固定的取向 $\sigma$ 和任意指定 $0<\mu<\infty$，全部原 Hermitian
探针与质量为 $\mu$ 的全部原正复线性泛函满足完整 PB，当且仅当

$$
 s_1=s_2=s_3=0.
\tag{38.42}
$$

证明。若 $(s_1,s_2)\ne(0,0)$，直接消费 §36.2 的同一原环境见证；它已经允许
任意 Hermitian $B$、任意 $a$、任意 $v(\ker D)\ne0$ 和任意 $s_3$，并且可以把
两笔预算同时做成严格正。因此全称 PB 先迫使 $s_1=s_2=0$。若此时 $s_3=s\ne0$，
定理 38.2 和引理 38.3 给出任意 Hermitian $T$ 上两个坐标均非零、两笔预算
同时严格正的有限二维见证；定理 38.4 用同一个实际 $t$、同一个环境和
$N_u=\|u\|^2+|au|^2\|z_0\|^2$ 将其完整回接，故原 PB 严格失败。于是
$s_3=0$。反向 $S=0$ 的充分性直接消费已付的 §34.13、§36.25 及父卷 §1 的
一般原算子恒等式与全正泛函复 Cauchy–Schwarz；它涵盖混合、奇异、零预算和
任意有限正质量。正质量结论对两种分别固定的 $\sigma$ 各自成立，未用一个取向
去替代另一个取向。证毕。

这个推论只在 (38.33) 的轴向环境、可用的同一零模和对角残量范围内删除
§37.6 的「任意 Hermitian $T$ 尚未分类」边界；它没有改变实际 $B$ 或环境，也
没有把二维矩阵见证变成实际制备、实际菜单或相干控制。任意规定的有限正质量
均由 (38.41) 给出；零质量的正泛函为零，仍不会单独辨别残量。

### 38.8 归属、原来源合同和确切剩余边界

接触恒等式、A/C 两族的系数、B 的行列式预算、符号与相位运输，以及 (38.34)–
(38.41) 的组合，都是本卷在已有定义上的手工矩阵推导。复 Gram／Cauchy–Schwarz、
Hermitian 矩阵、Jordan 乘积、有限维连续性和对角酉坐标的成熟背景继续沿
§35.4、§36.5、§37.6 已有归属；不主张历史新颖性、常数最优性、全局最小性或
Lean／kernel 认证。

§35.4、§36.5、§37.6 及其递归来源合同继续完整有效。C139 §23.3 式 (23.7) 仍要求
字面旧程序 $\tau;T_P$ 在全部原准备、事件、中间切口、参考／副本、合法分析词和树、
原坐标、固定支持全质量及完整菜单上供应同一实际接受端的准备无关准确关联，并
保持原支持与未归一标尺；矩阵相等、纯校准、合法逆或矩阵综合不提供该证书。
有限返回卷定义 162.1、命题 162.2 和定义 164.1 仍要求同一接受叶的整份活动
输出、实际读后 active-ready、首个合法消费者，以及读后同一整份活动输入对全部
旧合法未来的真实 Return，连同原参考、控制和物理钟的对应。C139 固定源 §§50–85、
C128 原词 §§385–392 的下降、参考、递归支持、容量和同一原 $D$ 恢复继续按已付
域计入；本节不重复计为新成果。

全部原对象与量词保持不变：原 Omega/native、准备、事件、过程、参考／副本、真正
相关联合、零／不等／次归一质量、钟、单位、控制、parent、ready、flags、完整记录、
失败、拒绝、停止、销毁、泄漏、真遗忘、两侧及逆向 Return、固定支持全质量、完整
菜单、所有中间切口及每份完整输出的每个旧合法未来都保留。数学 $X,u,\xi,x,U$
不生成准备，不生成实际菜单，不复制，不提供自由相干控制，也不替代原类型、记录、
历史或返回合同。复 Hilbert／相干、Born、张量、typed CP／Kraus、完整仪器／TP／
更新／Lüders、全部历史／Return、Hamiltonian／物理钟及共同正作用量，仍只在各自
原来源合同成立时消费。

未由本节解决的边界是明确的：一般 $V$ 与一般非零 $\mathcal W$ 的完整分类尚未取得；是否有本构造所需的原可读零模，应按各自实际输入核对。即使满足 (38.33) 的轴向环境和 $v(\ker D)\ne0$，本节的结论也仅针对对角残量。非对角三格残量、非轴向完整算子块、未知总响应、$\mathcal E_+^D=\mathcal E_-^D$、$N_\omega(\varepsilon)^2\to0$，以及实际全响应、准备无关来源和完整菜单，均未由本节解决。
七项消费者结果仍按其各自完整前件有条件地计入；本节不新增来源结论，也不否定
既有结果。这里的分类也没有把局部 PB 排除提升为完整量子起源或无缺口的全局量子公理；
它只在 (38.33) 的准确轴环境中把第三格任意 Hermitian 块纳入已有两格结论。

### 38.9 中文几何说明

把每组复输出先实化到 $\mathbb R^4$；一组 $R_\delta u,S_\delta u$ 的两个向量至多张成
一个二维实平面，两种 $\delta$ 给出的四个输出向量不要求共用一个固定 $\mathbb R^2$ 平面。这里的平方根始终来自
(38.2) 的实 Gram 行列式（取实部内积），不是复内积的模平方。A、C 先手工把正号列压到零，
再让负号列与 $Xu$ 沿同一条实直线；接触恒等式
把残量留下的读数直接化成 $-2s(w-v)$。A 中这个读数是
$-10seb^2/M^2$，C 中是 $16ds/5$；B 则用两列的行列式把两笔面积的总预算
精确压到 $|se|$。

纯混合分支消费已经付出的线性缺额，零矩阵分支消费已经付出的两笔内部面积；所有
分支都先在有限边界上找到同一份严格违反。把 $X$ 沿单位矩阵轻微移动时，每笔面积
的平方仍是非负实多项式，两个坐标都非零使其四次项严格为正，所以可以避开有限个
根而让两块面积同时打开。严格缺额的连续性保证这次移动仍然不满足 PB，但没有把
这个存在性半径宣称成统一常数，也不提供统一资源界、物理控制或实际准备。

回接原环境时，零模中的 $w_0$ 抵消第一轴的实际输出，探针的两条离面条目使换位尺和
Jordan 尺各自留下的第一轴分量在所需组合中抵消。原环境向量仍留在 $\xi$ 中，代价是
(38.41) 的真实范数分母；因此这是同一实际矩阵上的一次完整列运输，不是删去环境的
压缩，也不是声称整个原算子共享一个不变平面。局部第三残量刚性已经扩展到任意
Hermitian $T$，而来源、装置和完整 Omega 目标仍按上面的未决边界继续开放。

## 新增锚（本行以下为后续增补区）

## 39. 共振两腿原零模像的三格读取与 PB 单独刚性

本节处理 §32.6 中原像含有 $(q_1,q_2,0)^{\mathsf T}$、$q_1q_2\ne0$ 的分支。谱值 $1,2$ 的乘积恰为 $2$，所以 (32.17) 的旧 $F_{12,T}$ 恒等于零；这只使那族秩一读取失效，不是非零残量满足全部 PB 的证据。下面用同一实际零模像、一个不必秩一的 Hermitian 探针和带非零实部的两份复斜率，给出三条分离全部对角残量的完整核读取。原环境的有限运输复用 §32.5；全正泛函的零残量充分性独立复用父卷 §1。定理 32.3 的三格支撑结果及 §38 的原轴分类各按原域保留，不计为本节新增内容。

### 39.1 同一原输入、单个零模与分类定理

**定义 39.1（共振两腿输入）。** 完整沿用定义 32.1、(32.2)–(32.3)。为避免与 $S_\delta$ 混淆，本节把定义 32.1 的对角残量矩阵 $S$ 记为 $E$，即

$$
\begin{gathered}
\mathcal H=\mathbb C^3\oplus\mathbb C^m,\quad A=M_{m+3}(\mathbb C),
\quad P=I_3\oplus0_m,\quad C=\operatorname{diag}(1,2,3),\quad c=C\oplus0_m,\\
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix}=t^*,\qquad
E=\operatorname{diag}(s_1,s_2,s_3),\quad s_\ell\in\mathbb R,\quad s=E\oplus0_m,\\
\sigma\in\{1,-1\}\text{ 分别固定},\quad \iota=\sigma i,\quad
K_\sigma(a,b)=\iota[a,b]/2,\quad g=K_\sigma(c,t)+s .
\end{gathered}
\tag{39.1}
$$

只增加以下原输入条件：存在同一原环境中的一个向量 $\eta$，满足

$$
D_{\rm env}\eta=0,\qquad V\eta=q=(q_1,q_2,0)^{\mathsf T},\qquad q_1q_2\ne0.
\tag{39.2}
$$

$B,D_{\rm env}$ 任意 Hermitian，$V$ 的其余列任意。不要求 $\mathcal W=V(\ker D_{\rm env})$ 包含于 $12$ 平面，不要求整个 $V$ 秩一，也不要求原 $t$ 有任何演员约化平面。$\eta\ne0$ 随 (39.2) 自动成立。所有伴随、平方、预算及正泛函都在完整原 $A$ 中计算。

**定理 39.2（一个共振两腿零模足以排除三格残量）。** 对每份满足 (39.1)–(39.2) 的原输入和每个分别固定的 $\sigma$，下列条件等价：全部原 Hermitian 角探针 $x=x^*=PxP$ 和全部原正复线性泛函满足原 PB (32.3)；$E=0$。对任意指定 $0<\mu<\infty$，只在质量恰为 $\phi(I_{m+3})=\mu$ 的全部原正泛函上全称检验，也有同一允许集。对每个 $E\ne0$ 和每个这样的 $\mu$，存在同一原 $B,V,D_{\rm env}$ 中的有限实际 $x$ 和一个共同原向量泛函，使两笔原预算同时严格正而 (32.3) 严格失败。此结论不携带 P2、残量平衡或未知总响应的前件。

证明先构造三组完整 Hermitian 核插值，再在同一原环境中给出有限违反；零残量的全正泛函充分性在 §39.6 单独给出。

### 39.2 两份作用必须来自同一个 Hermitian 探针

以下内积对第一变量共轭线性。先允许 $u$ 不归一，所有齐次等式均按原向量写出。取实 $0<\lambda<2/5$，定义

$$
\begin{gathered}
v=(2q_1/\lambda,\,4q_2/\lambda,\,1)^{\mathsf T},\qquad
q=\frac\lambda4(3I-C)v,\\
y=-v-\iota q,\qquad
z=Cv+\frac{\iota\lambda}{2}(I+3C)v,\qquad q-\iota y=\iota v .
\end{gathered}
\tag{39.3}
$$

这里 $v_3=1$ 是辅助方向；$(3I-C)v$ 的第三坐标严格为零。特别，原 $q$ 没有第三条腿，也未向 $\mathcal W$ 添入任何向量。探针输出可以有第三分量，事实上 $y_3=-1$；这与 $q_3=0$ 完全相容。定义 33.1 中的差向量 $w-\iota Xu$ 在此将是 $\iota v$，不是本节辅助向量 $v$ 本身。

对实参数 $a_0,b_0$ 定义两个实三列

$$
\begin{aligned}
T&=(2a_0-4b_0,\,-a_0+7b_0,\,-3b_0)^{\mathsf T},\\
H&=a_0(2\lambda,-5\lambda/4,0)^{\mathsf T}
+b_0\left(\frac{20-16\lambda^2}{9\lambda},
           \frac{115\lambda^2-128}{36\lambda},
           \frac{4-5\lambda^2}{3\lambda}\right)^{\mathsf T},\\
u_\ell&=\frac{T_\ell+\iota H_\ell}{\overline{v_\ell}}
\quad(\ell=1,2,3).
\end{aligned}
\tag{39.4}
$$

$v_1v_2v_3\ne0$，所以任意原 $q_1,q_2$ 的复相位均可直接代入，不旋转原演员基。只需要下面准确的三组参数：

$$
(\lambda,a_0,b_0)=(1/5,1,0),\qquad(1/5,0,1),\qquad(1/3,0,1).
\tag{39.5}
$$

第一组 $T_1=2,T_2=-1$，后两组 $T_1=-4,T_2=7$，故每组都有 $u_1u_2\ne0$。由于 $C$ 的第一、第二谱值不同，$u,Cu$ 线性独立：若 $Cu=\gamma u$，第一坐标迫使 $\gamma=1$，第二坐标迫使 $\gamma=2$，矛盾。

给出全部 Hermitian 相容性。写

$$
t_k=\sum_{\ell=1}^3 c_\ell^kT_\ell,\qquad
h_k=\sum_{\ell=1}^3 c_\ell^kH_\ell\quad(k=0,1,2).
$$

按 $a_0,b_0$ 分列，(39.4) 的六个矩准确为

$$
\begin{array}{c|rr}
 &a_0\text{ 系数}&b_0\text{ 系数}\\ \hline
t_0&1&0\\
t_1&0&1\\
t_2&-2&-3\\
h_0&3\lambda/4&-\lambda/4\\
h_1&-\lambda/2&-7\lambda/18-8/(9\lambda)\\
h_2&-3\lambda&-4\lambda
\end{array}
\tag{39.6}
$$

例如 $T$ 三列加权的 $b_0$ 系数依次是 $-4+7-3=0$、$-4+14-9=1$、$-4+28-27=-3$。$H$ 的 $b_0$ 系数统一到分母 $36\lambda$ 后，三个分子依次为

$$
\begin{aligned}
&(80-64\lambda^2)+(115\lambda^2-128)+(48-60\lambda^2)=-9\lambda^2,\\
&(80-64\lambda^2)+2(115\lambda^2-128)+3(48-60\lambda^2)
=-32-14\lambda^2,\\
&(80-64\lambda^2)+4(115\lambda^2-128)+9(48-60\lambda^2)
=-144\lambda^2 .
\end{aligned}
$$

$a_0$ 部分直接是 $2\lambda-5\lambda/4$、$2\lambda-10\lambda/4$、$2\lambda-20\lambda/4$。所以 (39.6) 给出

$$
\begin{gathered}
t_2+3t_1+2t_0=0,\qquad
h_0=\lambda(3t_0-t_1)/4,\qquad
h_2=\lambda(t_1+3t_2)/2,\\
2t_1+\lambda(2h_0+9h_1-h_2)/4=0 .
\end{gathered}
\tag{39.7}
$$

最后一式中 $2h_0+9h_1-h_2$ 的 $a_0$ 系数是 $0$，$b_0$ 系数是 $-8/\lambda$，故其左端确为 $2b_0-2b_0$。

由 $v_\ell^*u_\ell=T_\ell+\iota H_\ell$，有 $u^*C^kv=t_k-\iota h_k$。把 (39.3) 代入，得到

$$
\begin{aligned}
u^*y
&=-t_0-\frac\lambda4(3h_0-h_1)
  +\iota\left[h_0-\frac\lambda4(3t_0-t_1)\right],\\
(Cu)^*z
&=t_2+\frac\lambda2(h_1+3h_2)
  +\iota\left[-h_2+\frac\lambda2(t_1+3t_2)\right],\\
u^*z-\overline{(Cu)^*y}
&=2t_1+\frac\lambda4(2h_0+9h_1-h_2)
  +\frac{\iota\lambda}{4}(2t_0+3t_1+t_2).
\end{aligned}
\tag{39.8}
$$

(39.7) 因而逐项给出 $u^*y\in\mathbb R$、$(Cu)^*z\in\mathbb R$、$u^*z=\overline{(Cu)^*y}$。这正是同一 Hermitian 算子同时满足 $Xu=y$、$XCu=z$ 的相容性，而不是各自可写两列就算可实现。

还可直接写出全矩阵，无需援用插值存在性定理。令

$$
\begin{gathered}
U=[u,Cu],\quad Y=[y,z],\quad G=U^*U,\quad J_0=U^*Y=J_0^*,\\
X=YG^{-1}U^*+UG^{-1}Y^*-UG^{-1}J_0G^{-1}U^* .
\end{gathered}
\tag{39.9}
$$

$G$ 正定，因为 $\theta^*G\theta=\|U\theta\|^2>0$ 对每个 $\theta\ne0$ 成立。$G^{-1}$ 与 $J_0$ 都 Hermitian，(39.9) 的前两项互为伴随，第三项自伴，故 $X=X^*$。又 $Y^*U=J_0^*=J_0$，直接相乘得到

$$
XU=Y+UG^{-1}J_0-UG^{-1}J_0=Y .
\tag{39.10}
$$

因此这三组都给出有限实际 Hermitian $X$，准确实现两份作用，不要求 $X\ge0$ 或 $X$ 秩一。

### 39.3 Cayley 比值、非零实部与两种合法虚部

对每组 (39.5)，用同一 $q,u,X$ 定义完整三坐标齐次列

$$
\begin{aligned}
\mathcal R_\delta&=y+\frac\delta2\bigl(\iota(Cy-z)-Cq\bigr),\\
\mathcal S_\delta&=q+\frac\delta2\bigl(Cy+z+\iota Cq\bigr)
\qquad(\delta=+1,-1).
\end{aligned}
\tag{39.11}
$$

它们就是 (32.5) 的列，取 $w=q$。逐项相加减得

$$
\begin{aligned}
\mathcal S_\delta-\iota\mathcal R_\delta
 &=(I+\delta\iota C)(q-\iota y)=(I+\delta\iota C)\iota v,\\
\mathcal S_\delta+\iota\mathcal R_\delta
 &=q+\iota y+\delta z=2q-\iota v+\delta z .
\end{aligned}
\tag{39.12}
$$

置

$$
\tau_\delta=-1+\frac{\delta\lambda}{2}-\frac{3\iota\lambda}{2}.
$$

(39.3) 使 (39.12) 的第二行等于

$$
\left[\frac\lambda2(3I-C)-\iota I+\delta C
       +\frac{\delta\iota\lambda}{2}(I+3C)\right]v
=\tau_\delta(I+\delta\iota C)\iota v.
\tag{39.13}
$$

故同一完整两列满足

$$
\begin{gathered}
\mathcal S_\delta=\zeta_\delta\mathcal R_\delta,\qquad
\zeta_\delta=\iota\frac{\tau_\delta+1}{\tau_\delta-1}
             =\beta_\delta-\delta\iota\alpha_\delta,\\
d_\delta=|\tau_\delta-1|^2
       =4-2\delta\lambda+5\lambda^2/2>0,\\
\beta_\delta=-3\lambda/d_\delta\ne0,\qquad
\alpha_\delta=\frac{\lambda(1-5\delta\lambda/2)}{d_\delta}>0,\\
a_\delta:=\mathcal R_\delta
       =\frac{\tau_\delta-1}{2}(I+\delta\iota C)v\ne0 .
\end{gathered}
\tag{39.14}
$$

为核对比值，$\iota(\tau_\delta+1)=3\lambda/2+\delta\iota\lambda/2$；乘以 $\overline{\tau_\delta-1}=-2+\delta\lambda/2+3\iota\lambda/2$ 后，实部为 $-3\lambda$，$\iota$ 系数为 $-\delta\lambda+5\lambda^2/2$，正是 (39.14)。$\tau_\delta-1\ne0$，因为其 $\iota$ 系数非零；$I+\delta\iota C$ 三个对角元均非零，且 $v_3=1$，所以 $a_\delta\ne0$。$0<\lambda<2/5$ 分别保证 $1-5\lambda/2>0$ 与 $1+5\lambda/2>0$。因此两份斜率的虚部方向准确合法，两份实部也都非零。

若采用定义 33.1 的单位向量约定，置 $\nu=\|u\|>0$，把 $u,q,y,z$ 同除以 $\nu$，保留同一 $X$ 与斜率。此时 $\widehat w=q/\nu=V(\eta/\nu)\in\mathcal W$，完整两核仍成立，残量读取同除以 $\nu^2$。以下运输直接使用未归一的原 $u,q,\eta$，使 (39.2) 的固定 $q$ 保持原值；不需要修改原 $t$。

### 39.4 三条准确读取与行列式 $192$

对未归一的核，原残量读取是

$$
F(E)=\operatorname{Re}\bigl((q-\iota Xu)^*Eu\bigr)
=\operatorname{Re}\bigl((\iota v)^*Eu\bigr)
=\sum_{\ell=1}^3s_\ell H_\ell .
\tag{39.15}
$$

最后一步用 $\overline{v_\ell}u_\ell=T_\ell+\iota H_\ell$ 及 $\operatorname{Re}(-\iota T_\ell+H_\ell)=H_\ell$，故对任意原复相位成立。三组 (39.5) 的读取完整为

$$
\begin{aligned}
F_1&=\frac{8s_1-5s_2}{20},\\
F_2&=\frac{484}{45}s_1-\frac{617}{36}s_2+\frac{19}{3}s_3,\\
F_3&=\frac{164}{27}s_1-\frac{1037}{108}s_2+\frac{31}{9}s_3 .
\end{aligned}
\tag{39.16}
$$

例如第二组的三个 $H$ 系数依次是 $(484/25)/(9/5)$、$(-617/5)/(36/5)$、$(19/5)/(3/5)$；第三组依次是 $(164/9)/3$、$(-1037/9)/12$、$31/9$。这些化简给出 (39.16) 的全部分数。

若 $F_1=0$，则 $s_2=8s_1/5$。在这一关系上另两行准确变为

$$
3F_2=-50s_1+19s_3,\qquad
45F_3=-418s_1+155s_3 .
\tag{39.17}
$$

前两项系数的消去分别为 $484/15-1234/15=-50$、$820/3-2074/3=-418$。剩余二阶系数矩阵的行列式为

$$
\det\begin{pmatrix}-50&19\\-418&155\end{pmatrix}
=19\cdot418-50\cdot155=7942-7750=192\ne0 .
\tag{39.18}
$$

所以 $F_1=F_2=F_3=0$ 强制 $s_1=s_2=s_3=0$；每个非零 $E$ 至少被其中一组读出。三次读取允许各用自己的探针和泛函，但每份违反内部始终同一个探针、同一个泛函，不把不同次的两笔预算拼接。

旧 (32.17) 在谱边 $12$ 的因子 $A_0B_0-2=1\cdot2-2$ 恒为零，故旧 $F_{12,T}$ 的全部权重都不能分离此处的残量。本构造没有改写这个事实。新 $X$ 同时实现 $y,z$，新斜率具有 $\beta_\delta\ne0$，后两组 $u_3\ne0$，其 $H_3$ 系数分别为 $19/3$ 与 $31/9$；第三格由探针和读取参与，而不是由原 $q$ 添腿。定理 33.2 的 $\mathcal W=\mathbb C e_1$ 或 $\mathbb C e_2$ 前件在 (39.2) 下不成立，因此两条原轴的全称核盲区也未被否定。

### 39.5 复用原环境运输，并给出直接正预算的有限尺度

固定 $E\ne0$，取 (39.16) 中一个 $F\ne0$ 的核，保留它的全部 $\lambda,u,X,\zeta_\delta,\alpha_\delta,a_\delta$。这是 §32.5 的同一零模运输机制，下面把其常数列和一个显式有限尺度全部展开。对实 $\rho$ 令

$$
x_\rho=(\rho X)\oplus0_m,\qquad \xi_\rho=(u,\rho\eta),\qquad
\psi(A)=\xi_\rho^*A\xi_\rho .
\tag{39.19}
$$

完整的两个算子是

$$
\begin{aligned}
R_\delta(x_\rho)
&=\begin{pmatrix}
\rho(X+\delta\iota[C,X]/2)-\delta(CB+BC)/2&-\delta CV/2\\
-\delta V^*C/2&0_m
\end{pmatrix},\\
S_\delta(x_\rho)
&=\begin{pmatrix}
B+\delta\bigl(\rho(CX+XC)/2+\iota[C,B]/2+E\bigr)&V+\delta\iota CV/2\\
V^*-\delta\iota V^*C/2&D_{\rm env}
\end{pmatrix} .
\end{aligned}
\tag{39.20}
$$

尤其下左块都是 $V^*$ 型，不能把 $V^*Cu$ 或 $V^*u$ 换成维数不合的 $VCu$ 或 $Vu$。由同一原 $V\eta=q,D_{\rm env}\eta=0$，完整列乘法给

$$
\begin{aligned}
R_\delta(x_\rho)\xi_\rho
&=\rho(a_\delta,0)+P_\delta,\qquad
P_\delta=\left(-\frac\delta2(CB+BC)u,-\frac\delta2V^*Cu\right),\\
S_\delta(x_\rho)\xi_\rho
&=\rho\zeta_\delta(a_\delta,0)+Q_\delta,\\
Q_\delta
&=\left(\bigl(B+\delta[\iota(CB-BC)/2+E]\bigr)u,
         V^*(I-\delta\iota C/2)u\right),\\
t\xi_\rho&=(Bu+\rho q,V^*u),\qquad
s\xi_\rho=(Eu,0),\qquad x_\rho\xi_\rho=(\rho Xu,0).
\end{aligned}
\tag{39.21}
$$

所有范数仍取 $\mathbb C^3\oplus\mathbb C^m$ 的完整列。未删去 $B$、任一其余环境连线或它们的预算贡献；$D_{\rm env}\eta=0$ 只取消本次输入向量的对应项。

定义有限常数

$$
\begin{gathered}
e_\delta=Q_\delta-\zeta_\delta P_\delta,\qquad
b=\operatorname{Re}\bigl((Bu)^*Eu\bigr),\qquad
C_0=\sum_{\delta=\pm1}\frac{\|e_\delta\|^2}{\alpha_\delta},\\
M=1+\max\left\{
\frac{C_0+2|b|}{2|F|},\quad
\max_{\delta=\pm1}
\frac{\|P_\delta\|+1+2\|e_\delta\|/\alpha_\delta}{\|a_\delta\|}
\right\},\qquad
\rho=-\operatorname{sign}(F)M .
\end{gathered}
\tag{39.22}
$$

$F$ 为非零实数；(39.14) 保证所有 $\alpha_\delta,\|a_\delta\|$ 严格正，因此 $M$ 有限。置

$$
r_\delta=R_\delta(x_\rho)\xi_\rho,\qquad
S_\delta(x_\rho)\xi_\rho=\zeta_\delta r_\delta+e_\delta,\qquad
k_\delta=\psi(K_\sigma(R_\delta,S_\delta)).
$$

写 $\operatorname{Im}_\iota(a+\iota d)=d$（$a,d\in\mathbb R$）。自伴列恒等式给

$$
k_\delta=-\operatorname{Im}_\iota
 \bigl(r_\delta^*(\zeta_\delta r_\delta+e_\delta)\bigr).
\tag{39.23}
$$

现在逐笔估计，始终使用完整输出列。由 (39.22) 的严格余量及三角不等式，

$$
\begin{aligned}
\|r_\delta\|
&\ge |\rho|\|a_\delta\|-\|P_\delta\|\\
&>1+2\|e_\delta\|/\alpha_\delta,\\
\delta k_\delta
&\ge\alpha_\delta\|r_\delta\|^2
       -|r_\delta^*e_\delta|\\
&\ge\alpha_\delta\|r_\delta\|^2
       -\|r_\delta\|\|e_\delta\|\\
&\ge\frac{\alpha_\delta}{2}\|r_\delta\|^2>0 .
\end{aligned}
\tag{39.24}
$$

第三行到末行只用 $\|r_\delta\|>2\|e_\delta\|/\alpha_\delta$。故 $k_+>0,k_-<0$，且 $|k_\delta|=\delta k_\delta$。

仍令 $A_\delta(\psi)=\sqrt{B_\psi(R_\delta,S_\delta)}$ 为原未中心化实 Gram 预算。不能用复 Gram 行列式代替它。准确分解是

$$
\begin{aligned}
A_\delta(\psi)^2
&=\|r_\delta\|^2\|\zeta_\delta r_\delta+e_\delta\|^2
 -\left[\operatorname{Re}
       \bigl(r_\delta^*(\zeta_\delta r_\delta+e_\delta)\bigr)\right]^2\\
&=k_\delta^2+\Delta_\delta,\\
\Delta_\delta
&=\|r_\delta\|^2\|e_\delta\|^2-|r_\delta^*e_\delta|^2\ge0 .
\end{aligned}
\tag{39.25}
$$

第二步先用 $|z|^2=(\operatorname{Re}z)^2+(\operatorname{Im}_\iota z)^2$ 分出 $k_\delta^2$，再展开 $\zeta_\delta r_\delta+e_\delta$；其 $|\zeta_\delta|^2$ 项和交叉项在复 Gram 差中相消，留下所示 $\Delta_\delta$。非负性是完整列的复 Cauchy–Schwarz。由 (39.24)，每笔原预算本身严格正，并且

$$
\begin{aligned}
0\le A_\delta(\psi)-|k_\delta|
&=\frac{\Delta_\delta}{A_\delta(\psi)+|k_\delta|}\\
&\le\frac{\|r_\delta\|^2\|e_\delta\|^2}{2|k_\delta|}\\
&\le\frac{\|e_\delta\|^2}{\alpha_\delta} .
\end{aligned}
\tag{39.26}
$$

这里的分母非零，且 $2|k_\delta|\ge\alpha_\delta\|r_\delta\|^2$。因此

$$
A_+(\psi)+A_-(\psi)\le k_+-k_-+C_0 .
\tag{39.27}
$$

左端仍须由原 $L$ 计算。父卷 §1 的标准零残量恒等式，在加回同一 $s$ 后准确成为

$$
L=K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-)
       -2\bigl(t\circ s+K_\sigma(x_\rho,s)\bigr).
\tag{39.28}
$$

这是同一结合代数中的等式：$L$ 的残量增量是 $-2t\circ s$，两份 $K$ 之差的残量增量是 $2K_\sigma(x_\rho,s)$，所以从零残量等式立刻得到 (39.28)。用 (39.21) 的完整列，

$$
\begin{aligned}
\psi(t\circ s)&=\operatorname{Re}\bigl((Bu+\rho q)^*Eu\bigr),\\
\psi(K_\sigma(x_\rho,s))
 &=-\rho\operatorname{Im}_\iota\bigl((Xu)^*Eu\bigr),\\
\psi(t\circ s+K_\sigma(x_\rho,s))
 &=b+\rho\operatorname{Re}\bigl((q-\iota Xu)^*Eu\bigr)
 =b+\rho F .
\end{aligned}
\tag{39.29}
$$

由于 $M>(C_0+2|b|)/(2|F|)$、$\rho F=-M|F|$，

$$
\begin{aligned}
2M|F|-2b
&>C_0+2|b|-2b\ge C_0,\\
\psi(L)
&=k_+-k_-+2M|F|-2b\\
&>k_+-k_-+C_0\ge A_+(\psi)+A_-(\psi)>0 .
\end{aligned}
\tag{39.30}
$$

因此 $|\psi(L)|$ 严格超过两笔预算之和，且两笔预算已经同时正，无需另作趋零扰动。这是 §32.5 的原空间有限运输在新核上的显式尺度版本，不把环境常数视为零或把运输机制计为新的来源结论。

最后给任意指定 $0<\mu<\infty$，令

$$
\phi_\mu(A)=\frac{\mu}{\|\xi_\rho\|^2}\xi_\rho^*A\xi_\rho,
\qquad \|\xi_\rho\|^2=\|u\|^2+M^2\|\eta\|^2>0 .
\tag{39.31}
$$

这是完整原代数上的正复线性泛函，$\phi_\mu(I)=\mu$。正倍数 $a\psi$ 使 $\psi(L)$ 和每个 $A_\delta(\psi)$ 都同乘 $a$，因为 $B_{a\psi}=a^2B_\psi$。所以 (39.30) 的严格违反及两笔正预算一起保持。两份符号始终使用同一个 $x_\rho,\xi_\rho,t$ 和原环境。

### 39.6 零残量在全部正泛函上的充分性

$E=0$ 时，直接消费父卷 §1 的标准 $K_\sigma$ 恒等式，(39.28) 的最后一项为零。对完整原 $A$ 上任一正复线性泛函 $\phi$、任意自伴 $U,Z$，正性给复 Cauchy–Schwarz

$$
|\phi(UZ)|^2\le\phi(U^2)\phi(Z^2),\qquad
\phi(UZ)=\phi(U\circ Z)-\iota\phi(K_\sigma(U,Z)).
$$

两个自伴读数均为实，故

$$
\phi(K_\sigma(U,Z))^2
\le\phi(U^2)\phi(Z^2)-\phi(U\circ Z)^2=B_\phi(U,Z).
\tag{39.32}
$$

对 $U=R_\delta,Z=S_\delta$ 各用一次，再用三角不等式，得到

$$
|\phi(L)|\le
|\phi(K_\sigma(R_+,S_+))|+|\phi(K_\sigma(R_-,S_-))|
\le A_+(\phi)+A_-(\phi).
\tag{39.33}
$$

此充分性覆盖混合、非忠实、奇异和零预算泛函，完全独立于必要性所选的向量及零模。质量零时，正泛函的 Cauchy–Schwarz 给 $|\phi(A)|^2\le\phi(I)\phi(A^*A)=0$，所以只有零泛函，PB 是零等式，不能单凭零质量辨别残量。每个指定正质量的必要性则由 (39.31) 支付。

所有构造和估计只用 $\iota^2=-1$、$\overline\iota=-\iota$ 与同一原复线性数据。因而对 $\sigma=1$ 和 $\sigma=-1$ 分别执行，即各得整个结论；不需共轭替换 $B,V,D_{\rm env},q$，也不声称两取向必须共用同一见证。定理 39.2 得证。∎

### 39.7 最小星、固定输出消费者与准确剩余数学域

**推论 39.3（同一个固定共振两腿最小星）。** 对任意固定 $q=(q_1,q_2,0)^{\mathsf T}$、$q_1q_2\ne0$，取

$$
t=\begin{pmatrix}0_3&q\\q^*&0\end{pmatrix}\in M_4(\mathbb C),\qquad
c=\operatorname{diag}(1,2,3,0),\qquad s=\operatorname{diag}(s_1,s_2,s_3,0).
\tag{39.34}
$$

每个分别固定的取向下，全部原角探针和全部完整正泛函的 PB 准确当且仅当 $s_1=s_2=s_3=0$；每个非零残量在每个指定正有限质量上都有同一星中的有限严格违反，且两笔预算同时正。

证明。取 $m=1,B=0,V=q,D_{\rm env}=0,\eta=1$，直接应用定理 39.2。整个 $q$ 始终固定，环境与连线不随尺度更换。∎

在定理 39.2 的精确域内，原 PB 单独推出 $s=0$，故 $g=K_\sigma(c,t)$；(39.32) 另取 $U=c,Z=t$，得到全部正泛函的固定输出 P2。这里省去的只是这批固定输出另加 P2 的前件。只有另已独立辨识实际响应 $g=D(c,t)$，才可消费

$$
c\circ t-iD(c,t)=
\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1\end{cases}
$$

这一原输入对的乘积识别。不从完整 $\mathsf H_A(D)$ 删除 A1/P2，不删除承载卷定义 41.1 由两份实际外层 P2 推出显式预算的桥，也不把固定输出值当作未知总 $D$ 的构造或全域分类。

(39.2) 只要求一个实际零模原像，故任意其余环境耦合都在结论中；$\mathcal W$ 是否还含别的两腿或三腿向量无需另查。原三格支撑分类仍直接复用定理 32.3，原轴和任意 Hermitian 二维块的已得分类仍按 §§34–38 的各自条件保留。§39 没有判定所有不含 (39.2) 向量的其余原 $\mathcal W$，也没有给出那些剩余输入的非零残量全 PB 模型。一般非对角或算子值残量、未知总响应、完整 $\mathsf H$ 的一般输入、$\mathcal E_+^D=\mathcal E_-^D$ 与 $N_\omega(\varepsilon)^2\to0$ 不由本定理推出。

每个固定 $q_1q_2\ne0$、固定原输入和固定非零残量的全部插值与尺度均有限；分母只使用已证非零的 $v_\ell$、$\lambda$、$G$、$d_\delta$、$\alpha_\delta$、$a_\delta$、$F$ 及 $\|\xi_\rho\|^2$。没有给出 $q$ 接近任一原轴时统一有界的 $X,M$、归一化差额或取得／验证成本；轴上不能用含 $q_1q_2$ 分母的公式取值，仍须按原轴定理处理。有限数学尺度也不是物理资源界或原装置的执行授权。

### 39.8 成熟归属与完整原来源边界

本节的仓内综合推导是 (39.3)–(39.18) 的共振两腿 Hermitian 相容族、带非零实部的合法双斜率及三格分离。正泛函与复 Cauchy–Schwarz 的成熟背景沿 §32.6 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；Hermitian 矩阵、Gram 矩阵及有限维线性代数沿 Horn–Johnson，[*Matrix Analysis*](https://doi.org/10.1017/CBO9781139020411)。(39.9)–(39.10) 已直接证明所需自伴插值，不把一般矩阵插值文献视为本节 PB 分类的供应者。§32.5 支付原空间有限运输机制；(39.20)–(39.31) 是该机制在本核上的完整列代入和显式有限界，不另计来源构造。

复比例参量作为不确定性等号条件的成熟背景可参见 Hyunchul Nha，[*Unitary equivalence between ordinary intelligent states and generalized intelligent states*](https://arxiv.org/html/0709.3307v2)，§II 式 (4)–(5)。该处使用中心化输出向量的复线性依赖；本节始终使用未中心化原 PB 和 (39.25) 的实 Gram 预算。该文后续酉等价结论还要求能实施相应旋转的酉算子，本节没有这一前件，也不借该结论旋转原演员或生成控制。以上归属不主张本节特定核族的历史优先权、文献穷尽、常数最优、整体最简或 Lean／kernel 认证。

完整原目标仍严格合取父卷 [§6，尤其 (6.1)–(6.2)](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标)，以及本卷 §32.6、§35.4、§36.5、§37.6、§38.8 所保留的同一全文与全部逐层钉版上游；[有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的完整根候选、七项消费者和原活动接头边界同时保留。这些是完整原合同的引用，以下展开不替换其中任何对象、公式、前件或量词。

同一原 $\Omega$/native、$E,C,u,N,\mathcal P,S,D,q,K/J$、全词及跨评价配对、原模式网络与全部具名绑定保持原身份；本节局部矩阵 $E$ 不替代这些合同中的原域或原 Jordan 响应 $S$。全部原准备、事件、过程、参考／副本、真正相关共同联合、中央／经典／不等维／静默／无轴块、零／不等／次归一质量、同一真实乘积、同一 $\sigma,t_0$、物理钟、单位、控制、parent／ready／flags、环境、完整活动输出、全部成功失败细记录、port／post-port、拒绝、停止、销毁、泄漏、真分组遗忘、两侧及逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口及每份完整输出的每个旧合法未来均保留。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不合并，未定义请求不补零；全部根端点、同一 ready 的零活动支、原固定域／resolvent 及 $3s+r\le1$ 预算不变。

实际来源缺口仍有具体内容。[C139 固定源卷 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 要求字面旧程序 $\tau;T_P$ 的指定接受族，在全部原准备、事件、切口、参考／副本、合法分析词与树、原坐标、固定支持全质量及完整菜单上，供应到同一实际菜单事件 $k_b^\dagger P_{J_0}k_b$ 与原接受端的准备无关准确关联，保持原支持与未归一标尺、类型、ready、控制、钟、互补结果、记录和合法未来。这里只要求指定当前接受关联，不额外加强成历史双射。[Fourier 卷 §10.3–10.4](AURIC_C139_FOURIER_OVERLAPS_AND_GLOBAL_FRAMED_BORN_RIGIDITY.md) 的原子归属及特定正校准源仍须独立供应；其双块反例已表明全菜单校准或局部有理配方相等不自动下降到全部原准备。矩阵相等、某菜单存在、纯校准、操作逆与矩阵综合都不供应这些实际接线，本节没有构造它们。

CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及读后同一整份活动输入保留原参考、控制、钟并对全部旧合法未来真实 Return。有限返回定义 164.1 的查询候选与原 $B_{r_\star}$ 活动接头保持区别；保存整表、地址或档案不生成活动发生标识与未来权限。本节的 $u,X,\eta,\xi_\rho$ 不生产实际准备、原菜单、复制、自由相干控制、历史身份或真实 Return，也不以旧 Born／CP／QC 或密度表示循环倒推来源。

既得成果照其原域计入：[C139 固定源卷 §§50–73](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的合法前接、唯一正回溯、下降、固定返回刚性、条件过程比较、整台递归参考及累计真支持，[§§74–85](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的近似参考与容量界，以及 [C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 对同一个旧 $D$ 的恢复与消费者均保留，不重列为缺失。局部三标签或三演员结果不替代全 $K/J$、全词、源、菜单和过程义务。

七项量子消费者仍只在各自完整原条件下使用：共同全词、共同核及实际相干准备才给复 Hilbert／相干；实际事件、完整菜单、固定支持全质量及正质量绑定才给 Born 归一；同一真正相关共同联合、忠实同向交换腿及共同生成才给张量；整台 typed 箭头的合法接续、真实递归参考、全部环境／记录／失败／后口、相关正输入、真支持与累计支持运输才给 CP／Kraus；完整 typed 仪器、实际单位分区、AC、$N_u,X,X_s$、平方根词与接受端、严格正输出质量及射线／校准前件才给 TP／更新／Lüders；全部原历史、真遗忘及每个旧合法未来的实际两侧／逆向返回才给历史／Return；同一实际连续可逆流、实际逆、强连续实现、生成元域、物理钟／单位／能量和共同正 $\hbar$ 才给 Hamiltonian。

静态 EJA 条件候选保留其声明的原前提：实际 canonical-trace 代数、完整锥／态／效果、既有比较到 Jordan 的桥、全局正性、其中指定映射 $p_{13}$ 的迹保持、未归一单位及完整实线性张成上的边缘恒等式均不能由本节删去；这些不是定理 39.2 的额外前提，也未由该定理取得。其复扇区、块张量和静态 Born 结论仍在原条件内，经典扇区保留；本节不新增实际源、过程、动力、物理钟或高阶相容桥。因此这里取得的是原固定输出问题中一个实质分支的 PB 单独刚性，完整原 Omega 量子起源、无缺口来源的完整量子公理候选与整体严格更简目标仍未完成。

### 39.9 中文几何：原连线缺一腿，读取仍能看见三格

先固定原二元关系 $(c,t)$，把它的给定输出写成标准换位部分加三格误差。反过来检验误差能否留下，就必须给出同一个探针和同一个读取，使两笔原预算都不够。旧秩一方案在第一、第二谱方向恰遇 $1\times2=2$ 的抵消，无论怎样换它的权重都读成零。这只说明那把尺失明，不能据此把非零误差宣布为合法。

新方案把“环境连到哪里”和“探针作用到哪里”分开。原环境依旧只给出 $q=(q_1,q_2,0)$；辅助方向 $v$ 的第三格却可以放一，因为乘上 $3I-C$ 时第三格恰好消失，原连线仍没有第三腿。探针在第三格的输出不必消失。它必须同时接住 $u$ 和按 $C$ 加权的 $Cu$，所以不能任意指定两个不相干的输出；六个实矩与四条相容关系恰好保证同一 Hermitian 探针存在，显式矩阵把这一点落实。

再让两份复比例都有实部，同时守住相反方向的合法虚部。这样得到三把不同的尺：第一把锁定前两格误差的比例，后两把分别牵涉第三格。按第一把的比例消去后，剩下两把尺的行列式是 $192$，所以三格非零误差不可能在三次读取里全部躲掉。这是关系间的相容性提供了可分辨性，不是添加新的原输入坐标，也不是对演员作一次可免费执行的旋转。

接回环境时，只放大同一个角探针和同一个零模原像，原 $t$ 完全不变。主列满足两份精确复比例；复杂环境与残量留下的额外列都保留，其额外面积有常数上界。非零误差的带符号读数却随尺度线性增长。选取 (39.22) 的有限尺度，就让两笔预算都打开为严格正，同时仍被左端超过；最后统一乘一个正因子，质量便恰好是任意指定的正数。每次违反都在一份共同实现中成立，没有把分别最省的两次预算拼成一个不存在的实验。

所得刚性回答的是这批原矩阵关系能否容纳对角误差；它已经排除全部非零误差。它并不回答原 Omega 中哪台旧装置实际供应这些菜单、读后是否真 ready、同一活动输入能否对所有旧未来返回。那些完整来源合同及既得成果继续原样承担各自作用，局部可证明的约束不改变完整目标的成功标准。

## 新增锚（本行以下为后续增补区）

## 40. 秩二谱环境中非零第三对角的有限双正预算排除

### 40.1 原固定输入与条件结论

**定义 40.1（两条原环境连线的固定输出）。** 完整沿用定义 32.1、(32.2)–(32.3)，专门取原有序基 $(e_1,e_2,e_3,f_1,f_2)$ 中的

$$
\begin{gathered}
\mathcal H=\mathbb C^3\oplus\mathbb C^2,\qquad A=M_5(\mathbb C),
\qquad P=I_3\oplus0_2,\qquad c=\operatorname{diag}(1,2,3,0,0),\\
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix},\qquad
B=B^*\in M_3(\mathbb C),\qquad
V=[\kappa e_1,\gamma e_2],\qquad D_{\rm env}=\operatorname{diag}(0,d),\\
\kappa,\gamma>0,\qquad d\in\mathbb R\setminus\{0\},\qquad
\mathsf E_s=sE_{33}=\operatorname{diag}(0,0,s,0,0),\qquad s\in\mathbb R,\\
\sigma\in\{1,-1\}\text{ 分别固定},\qquad \iota=\sigma i,\qquad
K(a,b)=\frac{\iota}{2}[a,b],\qquad g=K(c,t)+\mathsf E_s .
\end{gathered}
\tag{40.1}
$$

所有 $R_\delta,S_\delta,L,B_\phi$ 仍由完整原乘积 (32.2) 定义，PB 仍为 (32.3)。这里 $s$ 是第三格的实残量系数，$E_{33}$ 是完整 $M_5$ 的原矩阵单位；不改动原来源合同中的域或响应符号。记

$$
a=(B_{12},B_{13}),\qquad C_E=\operatorname{diag}(2,3),\qquad
T=\begin{pmatrix}b_0&z\\\overline z&e\end{pmatrix}
 =(B_{jk})_{j,k\in\{2,3\}},\qquad
b_0,e\in\mathbb R,\quad z\in\mathbb C .
\tag{40.2}
$$

这里 $T$ 是原主子块，不要求 $\operatorname{span}(e_2,e_3)$ 对 $B$ 不变。二维 $R_{\delta,E},S_{\delta,E},L_E$ 只表示 (38.1) 中参数恰为 $C_E,T,X,sP_3$ 的比较式，$P_3=\operatorname{diag}(0,1)$。其与原空间的关系须由下述完整作用列支付。

**定理 40.2（$B_{33}\ne0$ 的原秩二输入排除第三残量）。** 对每份满足 (40.1) 且 $e=B_{33}\ne0$ 的固定原输入，每个分别固定的 $\sigma$、每个实 $s\ne0$ 和每个指定 $0<\mu<\infty$，存在一个有限原 Hermitian 角探针 $x=x^*=PxP$ 和一个完整原 $M_5$ 上的正向量泛函 $\phi$，使

$$
\phi(I_5)=\mu,\qquad
B_\phi(R_+,S_+)>0,\qquad B_\phi(R_-,S_-)>0,\qquad
|\phi(L)|>\sum_{\delta=\pm1}\sqrt{B_\phi(R_\delta,S_\delta)}.
\tag{40.3}
$$

所有原 $B,\kappa,\gamma,d$、两条环境列及演员基在同一见证中保持原值。因此在这个 $B_{33}\ne0$ 的固定输入类，全部原探针与质量恰为任一指定 $\mu>0$ 的全部完整正泛函上的 PB 迫使 $s=0$；对全部正泛函量化亦然。$s=0$ 的全正泛函充分性直接复用父卷 §1 与本卷 §39.6，不作为新增结论。

### 40.2 保留第二环境列的准确向量回接

**引理 40.3（存活环境的实 Gram 代价）。** 在 (40.1) 中暂不要求 $e\ne0$。对任意 $u=(u_2,u_3)^{\mathsf T}$、$u_2u_3\ne0$ 和任意 Hermitian $X\in M_2(\mathbb C)$，取

$$
\begin{gathered}
q=aC_Eu,\qquad w=-\frac{au}{\kappa},\qquad
\ell=\left(-\frac{\iota q}{u_2},\frac{\iota q}{u_3}\right),\qquad
\xi=(0,u_2,u_3,w,0)^{\mathsf T},\\
x=\begin{pmatrix}0&\ell&0_{1,2}\\
\ell^*&X&0_{2,2}\\0_{2,1}&0_{2,2}&0_{2,2}\end{pmatrix},\qquad
\chi_\xi(A)=\xi^*A\xi .
\end{gathered}
\tag{40.4}
$$

则 $x=x^*=PxP$，$\xi\ne0$，且原完整作用列准确满足

$$
\begin{aligned}
R_\delta\xi&=(0,R_{\delta,E}u,0,-\delta\gamma u_2),\\
S_\delta\xi&=(0,S_{\delta,E}u,0,\gamma(1-\delta\iota)u_2),\\
\chi_\xi(L)&=u^*L_Eu .
\end{aligned}
\tag{40.5}
$$

上式的块顺序是 $e_1,(e_2,e_3),f_1,f_2$。令

$$
\begin{gathered}
A_\delta=\|R_{\delta,E}u\|^2,\qquad
D_\delta=\|S_{\delta,E}u\|^2,\qquad
C_\delta=\operatorname{Re}((R_{\delta,E}u)^*S_{\delta,E}u),\\
G_{\delta,E}=A_\delta D_\delta-C_\delta^2,\qquad
n=\gamma^2|u_2|^2>0 .
\end{gathered}
$$

则完整原预算为

$$
\begin{aligned}
B_{\chi_\xi}(R_\delta,S_\delta)
 &=G_{\delta,E}+n(2A_\delta+D_\delta+2\delta C_\delta)+n^2,\\
2A_\delta+D_\delta+2\delta C_\delta
 &=\|S_{\delta,E}u+\delta R_{\delta,E}u\|^2
   +\|R_{\delta,E}u\|^2\ge0,\\
\sqrt{B_{\chi_\xi}(R_\delta,S_\delta)}&\ge n>0 .
\end{aligned}
\tag{40.6}
$$

证明。首先 $\ell u=0$、$\ell C_Eu=\iota q$、$\kappa w=-au$。在原完整空间中直接相乘给

$$
\begin{array}{c|cccc}
 &e_1&E&f_1&f_2\\ \hline
x\xi&0&Xu&0&0\\
xc\xi&\iota q&XC_Eu&0&0\\
cx\xi&0&C_EXu&0&0\\
t\xi&0&Tu&0&\gamma u_2\\
tc\xi&q&TC_Eu&0&2\gamma u_2\\
ct\xi&0&C_ETu&0&0
\end{array}
\tag{40.7}
$$

于是 $h\xi$ 与 $k_t\xi$ 的第一格均为 $q/2$，$r\xi$ 与 $g\xi$ 的第一格分别为 $\iota q/2$、$-\iota q/2$；其 $E$ 块准确是二维定义的对应列。它们的 $f_1$ 格均为零，$f_2$ 格依次是 $0,\gamma u_2,0,-\iota\gamma u_2$，故得到 (40.5) 的前两式。由原自伴列恒等式

$$
\chi_\xi(U^2)=\|U\xi\|^2,\qquad
\chi_\xi(U\circ Z)=\operatorname{Re}((U\xi)^*Z\xi)
\tag{40.8}
$$

计算 $L$，新增的环境贡献只有
$-2\operatorname{Re}(\overline{\gamma u_2}(-\iota\gamma u_2))=0$，给出第三式。两笔预算各自使用同一个完整向量和探针，其两范数平方为 $A_\delta+n,D_\delta+2n$，实内积为 $C_\delta-\delta n$。展开
$(A_\delta+n)(D_\delta+2n)-(C_\delta-\delta n)^2$ 即为 (40.6)。$G_{\delta,E}\ge0$ 是二维列的实 Gram 非负性。

因此第二环境列增加了必须保留的代价，不能由二维严格违反直接推出完整 PB 严格违反。(40.5) 只断言所选向量上的两列与一个期望值；没有断言 $L\xi$ 为 $L_Eu$ 的嵌入，也没有算子交织或全正泛函之间的等价。原归一因子为

$$
N_u=\|u\|^2+\frac{|au|^2}{\kappa^2}>0,\qquad
\phi_{\mu,u}(A)=\frac{\mu}{N_u}\xi^*A\xi .
\tag{40.9}
$$

它在完整原 $M_5$ 上正且质量恰为 $\mu$；PB 左端与每笔预算平方根均乘同一个正因子 $\mu/N_u$。证毕。

### 40.3 任意复 $B_{23}$ 的实比例边界族

现在证明定理 40.2。固定 $s\ne0,e\ne0$。二次方程

$$
F(p):=3p^2+4sp+s^2-7e^2=0
\tag{40.10}
$$

有两个不同实根
$p=(-2s\pm\sqrt{s^2+21e^2})/3$。至少一个满足 $p^2\ne9e^2$：否则两个不同根只能是 $3e,-3e$，其和为零，与根和 $-4s/3\ne0$ 矛盾。固定任一这样的根，置

$$
\begin{gathered}
D_p=p^2-9e^2\ne0,\qquad
\beta_\delta=\frac{e+\delta(3p+s)}{p-3\delta e}\in\mathbb R,\\
\alpha=\frac{\beta_++\beta_-}{2}
 =\frac{e(10p+3s)}{D_p},\qquad
\lambda=\frac{\beta_+-\beta_-}{2}
 =\frac{3e^2+3p^2+sp}{D_p} .
\end{gathered}
\tag{40.11}
$$

这些实数满足

$$
\alpha^2-\lambda(\lambda-2)=-\frac{F(p)}{D_p}=0,
\qquad \alpha\ne0 .
\tag{40.12}
$$

第一式可由 $\alpha^2-\lambda^2=\beta_+\beta_-$ 直接计算。若 $\alpha=0$，则 $10p+3s=0$，将 $s=-10p/3$ 代入 $F(p)=0$ 得 $7p^2/9-7e^2=0$，与 $D_p\ne0$ 矛盾。因此下列除法全部合法。

令 $b=|z|$，当 $b>0$ 时取 $\theta=z/b$，当 $b=0$ 时取 $\theta=1$；始终有 $|\theta|=1,z=b\theta$。定义

$$
\begin{gathered}
r_0=\frac{5b}{\alpha},\qquad
Q_0=b\left(\frac{2\lambda-4}{\alpha}+\iota\right),\qquad
P_0=r_0+Q_0=b\left(\frac{1+2\lambda}{\alpha}+\iota\right),\\
H_0=-2b+\frac{\iota(2-\lambda)b}{\alpha},\qquad
F_0=\frac{5\lambda b}{\alpha}+2\iota b,\\
u_\rho=(\rho\theta,1)^{\mathsf T},\qquad
X_\rho=\begin{pmatrix}r_0/\rho&\theta Q_0\\
\overline{\theta Q_0}&p\end{pmatrix},\qquad \rho>0 .
\end{gathered}
\tag{40.13}
$$

每个有限 $\rho>0$ 都给有限 Hermitian $X_\rho$ 和两个坐标非零的 $u_\rho$。没有旋转原基或改变 $T$；$\theta$ 只是同一原探针与向量的系数。直接计算有

$$
\begin{aligned}
X_\rho u_\rho&=(\theta P_0,p+\rho\overline{Q_0})^{\mathsf T},\\
Tu_\rho&=(\theta(b+b_0\rho),e+b\rho)^{\mathsf T},\\
K(C_E,X_\rho)u_\rho
 &=(-\iota\theta Q_0/2,\iota\rho\overline{Q_0}/2)^{\mathsf T},\\
(C_E\circ T)u_\rho
 &=\left(\theta(5b/2+2b_0\rho),3e+5b\rho/2\right)^{\mathsf T},\\
(C_E\circ X_\rho)u_\rho
 &=\left(\theta(2r_0+5Q_0/2),3p+5\rho\overline{Q_0}/2\right)^{\mathsf T},\\
(K(C_E,T)+sP_3)u_\rho
 &=(-\iota b\theta/2,s+\iota b\rho/2)^{\mathsf T} .
\end{aligned}
\tag{40.14}
$$

(40.12) 恰好支付两条实比例相容式

$$
\alpha P_0+\lambda H_0=b,\qquad
\lambda P_0+\alpha H_0=F_0,
\qquad
b+\delta F_0=\beta_\delta(P_0+\delta H_0).
\tag{40.15}
$$

例如第一式的虚系数是
$b(\alpha+\lambda(2-\lambda)/\alpha)=0$，第二式的实系数是
$b(\lambda+2\lambda^2-2\alpha^2)/\alpha=5\lambda b/\alpha$，虚系数是 $2b$。最后一式使用 $\beta_\delta=\alpha+\delta\lambda$。第三坐标的比例另由 (40.11) 给出

$$
e+\delta(3p+s)=\beta_\delta(p-3\delta e).
\tag{40.16}
$$

### 40.4 完整作用列、准确残量与显式有限尺度

对 (40.13) 应用引理 40.3。这里

$$
\begin{gathered}
q_\rho=2B_{12}\rho\theta+3B_{13},\qquad
\ell_\rho=(-\iota q_\rho/(\rho\theta),\iota q_\rho),\\
\xi_\rho=(0,\rho\theta,1,-(B_{12}\rho\theta+B_{13})/\kappa,0)^{\mathsf T},
\end{gathered}
\tag{40.17}
$$

$x_\rho$ 则由 (40.4) 的同一块公式给出。为展示所有存活列，在完整原五维基中写

$$
\begin{aligned}
\mathbf v_\delta&=(0,\theta(P_0+\delta H_0),p-3\delta e,0,0)^{\mathsf T},\\
\mathbf a_\delta&=\left(0,-2\delta b_0\theta,
 \overline{Q_0}+\delta(\iota\overline{Q_0}/2-5b/2),0,-\delta\gamma\theta\right)^{\mathsf T},\\
\mathbf b_\delta&=\left(0,b_0\theta,
 b+\delta(5\overline{Q_0}/2+\iota b/2),0,
 \gamma(1-\delta\iota)\theta\right)^{\mathsf T} .
\end{aligned}
\tag{40.18}
$$

将 (40.14) 代回 (40.5)，再用 (40.15)–(40.16)，得到每个 $\rho>0$ 上的准确完整列

$$
\mathbf R_\delta(\rho):=R_\delta\xi_\rho
 =\mathbf v_\delta+\rho\mathbf a_\delta,\qquad
\mathbf S_\delta(\rho):=S_\delta\xi_\rho
 =\beta_\delta\mathbf v_\delta+\rho\mathbf b_\delta .
\tag{40.19}
$$

因此 $\rho\downarrow0$ 时两个作用对分别趋于实平行，且保留的环境分量趋于零。这里尚未以极限探针为见证；下一步直接选择严格正的有限尺度。

引理 38.1 的 (38.4) 是仅用结合乘法与 $\iota^2=-1$ 的恒等式，同样适用于完整原 $c,x_\rho,t$。故

$$
L=K(R_+,S_+)-K(R_-,S_-)
 -2K(x_\rho,\mathsf E_s)-2t\circ\mathsf E_s .
\tag{40.20}
$$

由 (40.14)、(40.7) 和 $\operatorname{Im}_\iota Q_0=b$，每个 $\rho>0$ 上准确有

$$
\begin{aligned}
\chi_{\xi_\rho}(K(x_\rho,\mathsf E_s))
 &=-s\operatorname{Im}_\iota(p+\rho Q_0)=-s\rho b,\\
\chi_{\xi_\rho}(t\circ\mathsf E_s)&=s(e+b\rho),\\
\chi_{\xi_\rho}(K(x_\rho,\mathsf E_s)+t\circ\mathsf E_s)&=se\ne0 .
\end{aligned}
\tag{40.21}
$$

此处 $\operatorname{Im}_\iota w=(w-\overline w)/(2\iota)$，并使用自伴列恒等式
$\chi_\xi(K(U,Z))=-\operatorname{Im}_\iota((U\xi)^*Z\xi)$。所以残量读数并非只在极限才非零。

记完整原实 Gram 面积为

$$
\mathcal A_\delta(\rho)=
\left(\|\mathbf R_\delta(\rho)\|^2\|\mathbf S_\delta(\rho)\|^2
 -\operatorname{Re}(\mathbf R_\delta(\rho)^*\mathbf S_\delta(\rho))^2\right)^{1/2} .
$$

因为 $\beta_\delta$ 实，从第二列减去 $\beta_\delta$ 倍第一列不改变这个实 Gram 行列式。由 (40.19)，对 $0<\rho\le1$ 得

$$
\begin{aligned}
\mathcal A_\delta(\rho)
 &\le\|\mathbf v_\delta+\rho\mathbf a_\delta\|
       \|\rho(\mathbf b_\delta-\beta_\delta\mathbf a_\delta)\|\\
 &\le\rho(\|\mathbf v_\delta\|+\|\mathbf a_\delta\|)
             \|\mathbf b_\delta-\beta_\delta\mathbf a_\delta\| .
\end{aligned}
\tag{40.22}
$$

所有系数已由固定输入与 $s,\sigma$ 明确给出，故以下数有限：

$$
\mathscr C=\sum_{\delta=\pm1}
 (\|\mathbf v_\delta\|+\|\mathbf a_\delta\|)
 \|\mathbf b_\delta-\beta_\delta\mathbf a_\delta\|\ge0,
\qquad
\rho_* =\min\left\{1,\frac{|se|}{2(1+\mathscr C)}\right\}>0 .
\tag{40.23}
$$

这个尺度实际为有限正数，且

$$
\sum_\delta\mathcal A_\delta(\rho_*)\le\rho_*\mathscr C<\frac{|se|}{2}.
\tag{40.24}
$$

为从面积控制左端，对任意两条完整复列 $v,w$，复 Cauchy–Schwarz 给
$|\operatorname{Im}_\iota(v^*w)|^2\le\|v\|^2\|w\|^2-\operatorname{Re}(v^*w)^2$。将其用于 (40.20) 的两项，并用 (40.21)，得到同一探针和同一向量上的

$$
\begin{aligned}
|\chi_{\xi_{\rho_*}}(L)|
 -\sum_\delta\mathcal A_\delta(\rho_*)
 &\ge2|se|-2\sum_\delta\mathcal A_\delta(\rho_*)\\
 &>|se|>0 .
\end{aligned}
\tag{40.25}
$$

另一方面，引理 40.3 没有删除第二条环境列，故对每个符号准确保证

$$
\mathcal A_\delta(\rho_*)\ge\gamma^2\rho_*^2>0 .
\tag{40.26}
$$

最后取完整原向量的范数与指定质量

$$
N_{\rho_*}=1+\rho_*^2+
 \frac{|B_{12}\rho_*\theta+B_{13}|^2}{\kappa^2}>0,\qquad
\phi(A)=\frac{\mu}{N_{\rho_*}}\xi_{\rho_*}^*A\xi_{\rho_*} .
\tag{40.27}
$$

$\phi$ 是完整 $M_5$ 上的一个正复线性泛函，$\phi(I_5)=\mu$。将 (40.25)–(40.26) 乘 $\mu/N_{\rho_*}>0$，得到 (40.3)，其中每笔预算平方根至少为
$\mu\gamma^2\rho_*^2/N_{\rho_*}$，严格差额大于 $\mu|se|/N_{\rho_*}$。这完成必要性及有限双正预算见证。零残量的全正泛函充分性按 §39.6 复用，未由单个向量外推。证毕。

### 40.5 退化边界、既有结果与完整原来源

$z=B_{23}=0$ 时，(40.13) 中 $b=r_0=P_0=Q_0=H_0=F_0=0$、$\theta=1$，所有公式仍成立；无需非零混合假设。$B_{11},B_{12},B_{13},B_{22}$ 以及 $z$ 的其余取值任意。$B_{12},B_{13}$ 只通过同一原第一环境零模的准确补偿进入 (40.17)、(40.27)，没有把它们设零。原 $d\ne0$ 保持不变，因所选向量的 $f_2$ 输入格为零而不出现在作用列中；原 $\gamma>0$ 则在两条完整输出列中产生 (40.26)。$\kappa>0$ 保证补偿格有定义。所有公式只用 $\overline\iota=-\iota,\iota^2=-1$，所以两个分别固定的取向各自成立，任意复 $B$ 无须共轭或替换。

$s=0$ 的充分性、零质量正泛函只能为零及其零等式均复用 §39.6。$e=B_{33}=0$ 不在定理 40.2 的域内：(40.21) 的分离读数此时为零，(40.23) 也不给正尺度。这不证明任何非零残量满足全称 PB，也不证明它必定失败；相同秩二输入中 $B_{33}=0$ 的原第三残量问题仍未回答。$\rho\downarrow0$ 时某些探针条目可无界，但见证只使用明确有限的 $\rho_*>0$；没有统一有界探针或资源上界。

本节数学归属为 `repo-derived`：新增承重关系是 (40.5)–(40.6) 的存活环境准确代价与 (40.10)–(40.27) 的任意复混合边界族、恒定非零残量读取及有限双正预算排除。前者由定理 40.2 实际消费，不单独充当全称分类。原 $\mathcal W=V(\ker D_{\rm env})=\mathbb C e_1$，所以定理 32.3 的三格支撑前件不满足，§39 的 $q_1q_2\ne0$ 零模前件也不满足；总 $V$ 的秩为二，(38.33) 的完整轴行条件不满足。§38 的二维恒等式与回接方法仍是直接前置，但其零环境列预算不能代替 (40.6)。[续卷 II §§32、41–43](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION_II.md) 保持其固定两演员输入与接触前提，不提供本定理的三演员结论；父卷 §13 的固定 P2 子类也不作为这里 PB 单独必要性的供应者。

正泛函及复 Cauchy–Schwarz 的成熟背景沿 §32.6、§39.8 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；Hermitian 矩阵和实 Gram 的标准线性代数沿 Horn–Johnson，[*Matrix Analysis*](https://doi.org/10.1017/CBO9781139020411)。本节所用准确列、相容式、实面积界和质量因子均已在证明中给出，不将这些书籍归为特定 PB 排除族的作者，不主张历史新颖性、文献穷尽、最优尺度或 Lean／kernel 认证。

完整原目标严格保留父卷 [§6 的 (6.1)–(6.2)](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标)、本卷 §39.8 以及[有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的同一全文和全部递归钉版上游。这些完整合同共同保留每个原对象与量词，以上矩阵条件不替换或缩短它们：原 $\Omega$/native、旧 $D$、固定 $K/J$、原准备与发生、ownership／parent／ready、真正相关参考与副本、固定支持全质量、完整菜单、全部中间切口、环境及完整输出／失败／零标签、控制／钟／单位和每份完整输出的每个旧合法未来均守原身份。§39.8 中实际旧程序接受关联、原活动接头与全未来 Return 的来源义务及已付消费者仍按各自原域保留。

定理 40.2 是指定固定输出矩阵模型中的条件关系推导；$x_\rho,\xi_\rho,\phi$ 不生成实际准备、可访问控制或新服务，不实现完整来源的共根或可达性。共同正规根态 $\omega$、全部有限与无限历史、递归参考、量子与经典选择、实际时间／作用量和物理空间维数三均未由本定理取得；GNS 向量不因此成为纯态或物理全局酉演化，$\zeta,J,\omega$ 不被合并，三个演员不等于物理三维。完整原量子起源与全部原成功条件仍保持未完成。

## 新增锚（本行以下为后续增补区）

## 41. 完整四维输出的分级自由、全环境面积关系与有限排除

本节固定同一共振两腿纯星输入，允许输出为任意完整 Hermitian 四阶矩阵，不增加 P2。这里分别给出全输出的对角归约、整条分级直线的全称 PB 充分性、一个固定探针家族的准确分类，以及保留第四列的同时核二次排除。对角归约消费[多项式 PB 卷 §28](AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md) 的实际证明接口；环境残量为零的截面直接消费定理 39.2。这两项及其替代读取组织均属复用，不计为新增分类。完整输出允许集是否恰为分级直线仍未解决；下面的家族分类不替换这一目标。

### 41.1 固定输入、完整输出与原量词

**定义 41.1（不预置支撑的原固定输出）。** 在同一原基内取

$$
\begin{gathered}
\mathcal H=\mathbb C^3\oplus\mathbb C,\quad A=M_4(\mathbb C),\quad
C=\operatorname{diag}(1,2,3),\quad c=C\oplus0,\\
P=I_3\oplus0,\quad Q=I_4-P,\quad J=P-Q,\\
q=(q_1,q_2,0)^{\mathsf T},\quad q_1q_2\ne0,\qquad
 t=\begin{pmatrix}0&q\\q^*&0\end{pmatrix},\\
\sigma\in\{1,-1\}\text{ 分别固定},\quad\iota=\sigma i,\quad
K(a,b)=\iota[a,b]/2,\quad a\circ b=(ab+ba)/2.
\end{gathered}
\tag{41.1}
$$

原 $c,t,q$ 全程固定，$q^*$ 是 $1\times3$ 行，未对原复相位作可实施旋转。初始输出 $g=g^*\in A$ 任意；此时不假设 $PgP=g$，也不预置任何环境对角元。对每个原演员探针 $x=x^*=PxP$，定义

$$
\begin{gathered}
h=K(c,x),\quad r=c\circ x,\quad k_t=c\circ t,\\
R_\delta=x+\delta(h-k_t),\quad S_\delta=t+\delta(r+g),\quad\delta=\pm1,\\
L=-2x\circ(h-k_t)-2t\circ(r+g),\\
B_\phi(U,Z)=\phi(U^2)\phi(Z^2)-\phi(U\circ Z)^2,\quad
\mathcal A_\delta(\phi)=\sqrt{B_\phi(R_\delta,S_\delta)}.
\end{gathered}
\tag{41.2}
$$

“全称原 PB”准确指对全部这样的 $x$ 和完整 $A$ 上的全部正复线性泛函成立

$$
|\phi(L)|\le\mathcal A_+(\phi)+\mathcal A_-(\phi).
\tag{41.3}
$$

这包括混合、非忠实泛函及零预算；不只检验纯态或忠实态。预算是未中心化的实 Gram 面积，不是复 Gram 行列式。每份不等式的两笔预算使用同一个 $x,t,g,\phi$。以下构造的全部严格违反都可归一到任意预先指定的有限正质量 $\phi(I_4)=\mu>0$。若只检验质量零，正泛函 Schwarz 给 $|\phi(a)|^2\le\phi(I_4)\phi(a^*a)=0$，只有零泛函，不能识别输出。

### 41.2 原始预算如何锁定完整非对角行

**复用引理 41.2（只消费标量预算之后的谱格论证）。** 全称原 PB 必迫使

$$
E:=g-K(c,t)=\operatorname{diag}(s_1,s_2,s_3,s_0),\qquad s_j\in\mathbb R.
\tag{41.4}
$$

这里 $s_0$ 没有被置零。多项式 PB 定理 28.2 的原陈述含有比定义 41.1 更强的完整未知响应前件，不能把那个陈述直接改读为本引理。准确可复用的是该证明在 (28.13) 之后的纯标量推导 (28.14)–(28.25)：本处 (41.3) 已直接供应其 (28.13)，不必再由未知外层响应及另一份 P2 推出它。

证明。取演员内不同的原谱格 $l=e_ie_i^*,m=e_je_j^*$，$i,j\in\{1,2,3\}$、$i\ne j$，谱值分别为 $a,b$。令

$$
\begin{gathered}
e=e_ie_j^*+e_je_i^*,\quad j_0=\iota(l-m)e,\quad n_l=2l,\quad
\lambda=(a-b)/2\ne0,\quad\mu_0=(a+b)/2,\\
V_l=a\,n_l\circ t-n_l\circ k_t,\qquad Z_l=t+ak_t.
\end{gathered}
$$

取原探针 $x=Te+\alpha n_l$，$T,\alpha$ 为任意有限实数。已知的 $K(c,x)$ 和 $c\circ x$ 给出

$$
\begin{aligned}
R_+&=T(e+\lambda j_0)-k_t+\alpha n_l,&
S_+&=t+g+\mu_0Te+a\alpha n_l,\\
R_-&=T(e-\lambda j_0)+k_t+\alpha n_l,&
S_-&=t-g-\mu_0Te-a\alpha n_l,\\
L&=2Te\circ k_t-2\mu_0Tt\circ e-2t\circ g
       -2\alpha(\lambda Tj_0+V_l).
\end{aligned}
\tag{41.5}
$$

因此原 PB 正是多项式卷 (28.13)。下面说明所消费接口的全部数学操作，尤其没有独立 P2：在实半内积 $\langle U,Z\rangle_\phi=\phi(U\circ Z)$ 中，Gram 列消元给

$$
B_\phi(A_0+\alpha n_l,B_0+\theta\alpha n_l)
=B_\phi(A_0+\alpha n_l,B_0-\theta A_0).
$$

右端是 $\alpha$ 的非负二次多项式，首项为 $B_\phi(n_l,B_0-\theta A_0)$。对 (41.5) 两笔分别取 $\theta=a,-a$，再将 PB 除以 $|\alpha|$ 并取标量多项式极限，得到

$$
\begin{gathered}
2|\phi(\lambda Tj_0+V_l)|\le
\sqrt{B_\phi(n_l,C_+)}+\sqrt{B_\phi(n_l,C_-)},\\
C_+=Z_l+g-\lambda Te-a\lambda Tj_0,\qquad
C_-=Z_l-g+\lambda Te-a\lambda Tj_0.
\end{gathered}
\tag{41.6}
$$

首项预算为零也允许此连续极限。由 $cl=al$ 直接有 $lV_ll=(1-l)V_l(1-l)=0$ 及

$$
lV_l(1-l)=\tfrac12l[c,t](1-l).
\tag{41.7}
$$

取单位 $\xi\in(1-l)\mathcal H$，先设 $d=\|m\xi\|>0$，令 $\eta=j_0\xi/d$、$\nu=e\xi/d=-\iota\eta$。在向量 $\xi_\varepsilon=(\xi+\varepsilon\eta)/\sqrt{1+\varepsilon^2}$ 上读 (41.6)。若 $\Pi_\eta z=z-\operatorname{Re}\langle\eta,z\rangle\eta$，完整实 Gram 的准确值为

$$
B_{\phi_\varepsilon}(n_l,W)
=\frac{4\varepsilon^2}{(1+\varepsilon^2)^2}
 \|\Pi_\eta(W\xi+\varepsilon W\eta)\|^2.
$$

约去共同正因子后令 $\varepsilon\downarrow0$；$\Pi_\eta(j_0\xi)=0$ 消掉两份中共同的 $-a\lambda Tj_0$，所得为

$$
2|\lambda Td+A_\xi|
\le\|z_+-\lambda Td\nu\|+\|z_-+\lambda Td\nu\|,
\quad
A_\xi=\operatorname{Re}\langle\eta,V_l\xi\rangle,\quad
z_\pm=\Pi_\eta((Z_l\pm g)\xi).
\tag{41.8}
$$

在 $T\to+\infty$ 和 $T\to-\infty$ 两向减去共同的 $2|\lambda T|d$，用平方差有理化，准确得到 $\operatorname{Re}\langle\nu,g\xi\rangle=-A_\xi$。再对同一谱格取第二伴轴 $e'=j_0,j'_0=-e$，得到第二个实读数；两读数合为

$$
\langle j_0m\xi,(g-\iota V_l)\xi\rangle=0.
\tag{41.9}
$$

$d=0$ 时左边本来为零，不定义 $\eta$。对固定算子作齐次扩展，在 $\xi=u+z$、$u\in m\mathcal H,z\in(1-l-m)\mathcal H$ 上相减，先得 $l(g-\iota V_l)(1-l-m)=0$；对 $z=0$ 的复二次型极化，再得 $l(g-\iota V_l)m=0$。由 (41.7) 即

$$
l(g-K(c,t))(1-l)=0.
\tag{41.10}
$$

所有极限只施于固定矩阵的标量范数或 Gram 多项式，没有对未知映射取极限。对三个演员谱格分别选一个不同的演员谱格作配对，(41.10) 锁住每条行到整个余空间，尤其包含第四列。$E=E^*$ 再锁住相应列；剩下的恰是四个实对角元，得到 (41.4)。环境本身没有被作为已识别的演员谱格，故这一论证不读出 $s_0=0$。∎

若另已给 $s_0=0$，取定义 39.1 的 $m=1,B=0,V=q,D_{\rm env}=0,\eta=1$，定理 39.2 就直接给 $s_1=s_2=s_3=0$。这是原支持截面的复用结论；不需要另一套九次读取，也不将这条结论重复计为新内容。

### 41.3 分级直线的全称充分性与零谱 P2 障碍

**定理 41.3（完整符号恒等式及分级自由）。** 对定义 41.1 的任意完整 Hermitian 残量 $E=g-K(c,t)$，有

$$
K(R_+,S_+)-K(R_-,S_-)=L+W,
\qquad W=\iota[x,E]+tE+Et.
\tag{41.11}
$$

特别，对任意实数 $a$，输出

$$
g=K(c,t)+a(P-Q)
\tag{41.12}
$$

满足全部原 PB，包括全部混合／非忠实正泛函和零预算。若 $a\ne0$，它却不满足环境零谱格的 P2 零读取。因此完整固定输出 PB 本身不能推出该 P2。

证明。置 $V=x+\iota t$、$U_\delta=R_\delta+\iota S_\delta$。直接乘法给

$$
\begin{aligned}
U_\delta&=(I_4+\delta\iota c)V+\delta\iota E,\\
U_+^*U_+-U_-^*U_-&=2\iota(V^*E-EV)=2W,\\
U_\delta^*U_\delta&=R_\delta^2+S_\delta^2+2K(R_\delta,S_\delta),\\
(R_+^2+S_+^2)-(R_-^2+S_-^2)&=-2L.
\end{aligned}
\tag{41.13}
$$

第二行的 $V^*=x-\iota t$ 给 $\iota(V^*E-EV)=\iota[x,E]+tE+Et$，符号由此确定。合并后两行得到 (41.11)。若 $E=aJ$，演员支撑给 $[x,J]=0$，纯星给 $tJ+Jt=0$，故 $W=0$。对任意正复线性 $\phi$ 和任意自伴 $U,Z$，复 Schwarz 及自伴读数为实给

$$
|\phi(UZ)|^2\le\phi(U^2)\phi(Z^2),\quad
\phi(UZ)=\phi(U\circ Z)-\iota\phi(K(U,Z)),\quad
|\phi(K(U,Z))|\le\sqrt{B_\phi(U,Z)}.
\tag{41.14}
$$

这不要求 $\phi$ 忠实或归一。对 (41.11) 的两份 $K$ 用三角不等式，即得 (41.3)。另一方面，令 $\phi_4(a)=e_4^*ae_4$，则 $ce_4=0$、$\phi_4(c^2)=0$、$\phi_4(K(c,t))=0$，但 $\phi_4(g)=-a$。原谱零 P2 的 $|\phi_4(g)|\le\sqrt{B_{\phi_4}(c,t)}=0$ 在 $a\ne0$ 时失败。∎

对 (41.4)，$W$ 的演员块是 $\iota[X,D]$，上右列是 $(D+s_0I_3)q$，其中 $D=\operatorname{diag}(s_1,s_2,s_3)$、$x=X\oplus0$。分级平移 $E\mapsto E+aJ$ 虽保持 $W,L$，却把 $S_\delta$ 改为 $S_\delta+\delta aJ$，完整 Gram 预算随之改变，不能先令 $s_0$ 消失再套用定理 39.2。下面的准确预算也直接显示这个变化。定理 41.3 只给固定 $(c,t,g)$ 的充分族和 P2 障碍，不供应满足全部嵌套调用的总响应 $D(\cdot,\cdot)$，更不是完整原 $\Omega$ 反模型。

### 41.4 一个固定探针家族的准确全环境分类

**定理 41.4（零探针、任意实环境幅度的充要关系）。** 保持 (41.1)、(41.4)，令

$$
\begin{gathered}
u=(2/\overline{q_1},-1/\overline{q_2},0)^{\mathsf T},\quad
\xi_w=(u,w),\quad \phi_w(A)=\xi_w^*A\xi_w,\quad x=0,\quad w\in\mathbb R,\\
m=|q_1|^2>0,\quad n=|q_2|^2>0,\quad b=m+4n,\quad a=m+2n,\\
d=2s_1-s_2+s_0,\quad k=2(s_1-s_2),\\
F=b(1+4s_1^2/m+s_2^2/n)-k^2,\\
G=b(m+n+b/4+s_0^2)-a^2,\qquad H=bd-ak.
\end{gathered}
\tag{41.15}
$$

这里的 $a$ 只是标量简写，不是 (41.12) 的分级参数。对这个固定 $x,u$、全部实 $w$ 的家族，原 PB 成立当且仅当

$$
\boxed{\quad 4(2s_1-s_2+s_0)^2\le
m+4n+\left(4\sqrt{n/m}\,s_1+\sqrt{m/n}\,s_2\right)^2=F.\quad}
\tag{41.16}
$$

因而 (41.16) 对全称原 PB 必要，但本定理只在上述家族内断言充分性，不涉及 $s_3$ 的完整分类。

证明。原相位没有消失在未经允许的旋转中，而是通过 $q^*u=1,q^*Cu=0$ 的准确收缩参与。完整四维列为

$$
\begin{aligned}
R_\delta\xi_w&=(-\delta wCq/2,0),\\
S_\delta\xi_w&=(\delta Du+wq+\delta\iota wCq/2,\ 1+\delta s_0w).
\end{aligned}
\tag{41.17}
$$

第四分量 $1+\delta s_0w$ 不能删去。另有 $(Cq)^*Du=k$、$q^*Cq=a$、$\|Cq\|^2=b$，这些标量均为实。由此逐项给

$$
\begin{aligned}
\phi_w(L)&=-2wd,\\
\|R_\delta\xi_w\|^2&=bw^2/4,\\
\|S_\delta\xi_w\|^2
 &=1+4s_1^2/m+s_2^2/n+2\delta dw
       +(m+n+b/4+s_0^2)w^2,\\
\operatorname{Re}\langle R_\delta\xi_w,S_\delta\xi_w\rangle
 &=-w(k+\delta aw)/2,\\
B_{\phi_w}(R_\delta,S_\delta)
 &=\frac{w^2}{4}\bigl(F+2\delta Hw+Gw^2\bigr).
\end{aligned}
\tag{41.18}
$$

例如前两笔复交叉项中涉及 $\iota(Cq)^*Du$ 或 $\iota q^*Cq$ 的部分纯虚，故无实贡献；不是把完整内积改为复 Gram。左端由 $L=-2t\circ g$ 得到，标准换位部分在该向量上的读数为零。展开常数还得

$$
F=b+\left(4\sqrt{n/m}\,s_1+\sqrt{m/n}\,s_2\right)^2\ge b>0,
\qquad
G=m^2/4+3mn+4n^2+bs_0^2>0.
\tag{41.19}
$$

两份二次式 $F\pm2Hw+Gw^2$ 对所有实 $w$ 非负：在 $w\ne0$ 处它们是 (41.18) 的实际非负 Gram 预算除以正数，零处为 $F>0$。在各自顶点读值，得 $H^2\le FG$。因此

$$
f(w):=\sqrt{F+2Hw+Gw^2}+\sqrt{F-2Hw+Gw^2}
=\left\|\left(\sqrt G w+\frac H{\sqrt G},\sqrt{F-H^2/G}\right)\right\|
 +\left\|\left(\sqrt G w-\frac H{\sqrt G},\sqrt{F-H^2/G}\right)\right\|
\tag{41.20}
$$

是实直线上的偶凸函数。凸性来自仿射列的欧氏范数，偶性来自两项互换，故 $f(w)\ge f(0)=2\sqrt F$，包括 $H^2=FG$ 的退化情形。$w\ne0$ 时原 PB 准确等于 $4|d|\le f(w)$。若 (41.16) 成立，则 $4|d|\le2\sqrt F\le f(w)$；反向若对全部非零 $w$ 成立，令 $w\to0$ 即 $4|d|\le2\sqrt F$。$w=0$ 处原 PB 两端本来都是零，不用除以 $w$。这证明准确充要性。∎

若 $4d^2>F$，置 $T=2|H|+G>0$，则每个满足

$$
0<|w|<\min\left\{1,\frac F{2T},\frac{4d^2-F}{2T}\right\}
\tag{41.21}
$$

的有限实数都给严格违反，且两笔预算同时严格正。确实，$|w|<1$ 时每份二次式与 $F$ 的距离小于 $T|w|$；所列阈值使它们都大于 $F/2>0$ 且小于 $4d^2$，故两根之和小于 $4|d|$。这把极限必要性接成有限正预算见证。取 $\mu\phi_w/(\|u\|^2+w^2)$ 即得任意指定正质量，严格性及两笔正预算均由齐次性保持。

即使沿分级直线 $s_1=s_2=s_3=a_0,s_0=-a_0$，此家族也有 $d=k=H=0$，但 $F=b+(16n/m+8+m/n)a_0^2$、$G=m^2/4+3mn+4n^2+ba_0^2$。因此分级残量虽给零缺陷 $W$，预算仍随它改变。这是不能用分级平移消去环境残量的一个完整列例证。

### 41.5 同时演员核必须保留环境二次代价

**定理 41.5（完整缺陷二次式及有限严格排除）。** 保持 (41.1)、(41.4)。任取有限 $X=X^*\in M_3(\mathbb C)$、$u\in\mathbb C^3$、实 $\beta_\delta$ 和正 $\alpha_\delta$，要求在同一原 $q$ 上准确满足

$$
\begin{aligned}
A_\delta&=Xu+\frac\delta2\bigl(\iota(CXu-XCu)-Cq\bigr),\\
Z_\delta&=q+\frac\delta2(CXu+XCu+\iota Cq),\\
Z_\delta&=(\beta_\delta-\delta\iota\alpha_\delta)A_\delta.
\end{aligned}
\tag{41.22}
$$

这是演员主列的两个相容核条件，未宣称第四列也成核。定义标量及系数

$$
\begin{gathered}
z=q^*u,\quad p=q^*Cu,\quad
b_\delta=z+\frac\delta2(\beta_\delta-\iota)p
                      -\frac\iota2\alpha_\delta p,\qquad
\eta=\sum_{\delta=\pm1}\frac1{2\alpha_\delta}>0,\\
w_E=\operatorname{Re}\bigl((q-\iota Xu)^*Du\bigr)+s_0\operatorname{Re}z,\\
A_2=s_0^2\eta,\qquad
A_1=2w_E+s_0\sum_{\delta=\pm1}\frac{\delta\operatorname{Re}b_\delta}{\alpha_\delta},\\
A_0=\eta\|Du\|^2+\sum_{\delta=\pm1}\frac{|b_\delta|^2}{2\alpha_\delta}\ge0.
\end{gathered}
\tag{41.23}
$$

此处 $p$ 是复标量，与静态候选的映射 $p$ 无关，$b_\delta$ 也不是 (41.15) 的 $b$。全称原 PB 必须对每份实际核数据满足

$$
A_2\rho^2+A_1\rho+A_0\ge0\quad(\rho\in\mathbb R).
\tag{41.24}
$$

等价地，$s_0\ne0$ 时必须 $A_1^2\le4A_2A_0$；$s_0=0$ 时必须 $A_1=0$。若相应条件失败，就存在有限原探针和同一完整正泛函使 PB 严格失败，且可使两笔预算都正并具有任意指定有限正质量。

证明。令 $x_\rho=(\rho X)\oplus0$、$\xi_\rho=(u,\rho)$、$\psi_\rho(a)=\xi_\rho^*a\xi_\rho$。完整矩阵在同一环境中为

$$
\begin{aligned}
R_\delta&=\begin{pmatrix}
\rho(X+\delta\iota[C,X]/2)&-\delta Cq/2\\
-\delta q^*C/2&0
\end{pmatrix},\\
S_\delta&=\begin{pmatrix}
\delta\bigl(\rho(CX+XC)/2+D\bigr)&q+\delta\iota Cq/2\\
q^*-\delta\iota q^*C/2&\delta s_0
\end{pmatrix}.
\end{aligned}
\tag{41.25}
$$

于是完整列而非压缩列满足

$$
\begin{aligned}
R_\delta\xi_\rho&=(\rho A_\delta,-\delta p/2),\\
S_\delta\xi_\rho&=(\rho Z_\delta+\delta Du,
                       z-\delta\iota p/2+\delta s_0\rho),\\
\mathfrak d_\delta(\rho)
 &:=(S_\delta-\beta_\delta R_\delta
                    +\delta\iota\alpha_\delta R_\delta)\xi_\rho
   =(\delta Du,b_\delta+\delta s_0\rho),\\
\psi_\rho(W)&=2\rho w_E.
\end{aligned}
\tag{41.26}
$$

最后一行的演员交换子贡献为 $-2\rho\operatorname{Im}_\iota((Xu)^*Du)$，星形贡献为 $2\rho\operatorname{Re}(q^*Du)+2\rho s_0\operatorname{Re}(q^*u)$，正是所列 $w_E$。这里 $\operatorname{Im}_\iota(a+\iota b)=b$。因此完整缺陷平方给准确二次式

$$
\begin{aligned}
\mathcal Q(\rho)
&:=\sum_{\delta=\pm1}\frac{\|\mathfrak d_\delta(\rho)\|^2}{2\alpha_\delta}
           +\psi_\rho(W)\\
&=\sum_{\delta=\pm1}
 \frac{\|Du\|^2+|b_\delta+\delta s_0\rho|^2}{2\alpha_\delta}
       +2\rho w_E
 =A_2\rho^2+A_1\rho+A_0.
\end{aligned}
\tag{41.27}
$$

尤其 $s_0\ne0$ 时的 $A_2\rho^2$ 是实际环境平方，不能从 §39 的支持残量线性增长证明中删除。

还须说明负二次式为什么是原 PB 的违反。对任意正 $\phi$、$\alpha>0,\beta\in\mathbb R$，设

$$
\mathcal T_\phi(R,S;\alpha,\beta)
=\frac{\phi((S-\beta R)^2)+\alpha^2\phi(R^2)}{2\alpha}.
\tag{41.28}
$$

写 $a=\phi(R^2),b=\phi(R\circ S),c=\phi(S^2)$。若 $a>0$，分子配方为 $a(\beta-b/a)^2+c-b^2/a+\alpha^2a$，算术几何平均给 $\mathcal T_\phi\ge\sqrt{ac-b^2}=\sqrt{B_\phi(R,S)}$。若 $a=0$，实 Schwarz 给 $b=0$，结论仍成立。对当前向量泛函，交叉项的准确符号为

$$
\frac{\|\mathfrak d_\delta(\rho)\|^2}{2\alpha_\delta}
=\mathcal T_{\psi_\rho}(R_\delta,S_\delta;\alpha_\delta,\beta_\delta)
 -\delta\psi_\rho(K(R_\delta,S_\delta)).
\tag{41.29}
$$

确实 $\psi_\rho(K(R,S))=-\operatorname{Im}_\iota\langle R\xi_\rho,S\xi_\rho\rangle$，展开 $+\delta\iota\alpha R\xi_\rho$ 的平方就给上述负号。由 (41.11)，有

$$
\mathcal Q(\rho)=\sum_{\delta=\pm1}
 \mathcal T_{\psi_\rho}(R_\delta,S_\delta;\alpha_\delta,\beta_\delta)
 -\psi_\rho(L).
\tag{41.30}
$$

故 $\mathcal Q(\rho)<0$ 直接推出 $\psi_\rho(L)>\mathcal A_+(\psi_\rho)+\mathcal A_-(\psi_\rho)$，是在同一探针、同一泛函上的实际严格违反，而不只是一个核条件失效。$s_0\ne0$ 且判别式正时，有限选择 $\rho=-A_1/(2A_2)$ 给 $\mathcal Q=A_0-A_1^2/(4A_2)<0$；$s_0=0,A_1\ne0$ 时，可取 $\rho=-\operatorname{sign}(A_1)(A_0+1)/|A_1|$，准确给 $\mathcal Q=-1$。配方也证明了 (41.24) 的两个等价条件。

若该向量违反的某笔预算为零，固定此有限 $\rho$ 后置 $\widetilde\psi=\psi_\rho+\varepsilon\operatorname{Tr}_4$。原严格差对 $\varepsilon$ 连续，故对充分小的有限 $\varepsilon>0$ 仍严格。此泛函忠实，且 $R_\delta,S_\delta$ 是实线性独立矩阵：它们的固定上右列分别为 $-\delta Cq/2$ 与 $(I_3+\delta\iota C/2)q$。在任一活动坐标，若后者等于实数 $k$ 乘前者，就需 $1+\delta\iota c_\ell/2=-k\delta c_\ell/2$，其非零虚部矛盾。$R_\delta\ne0$，因此也排除其他实线性依赖。忠实泛函在自伴实空间给正定内积，严格实 Schwarz 保证两笔预算都正。最后取

$$
\phi=\frac{\mu}{\|u\|^2+\rho^2+4\varepsilon}
       (\psi_\rho+\varepsilon\operatorname{Tr}_4),\qquad 0<\mu<\infty.
\tag{41.31}
$$

齐次性保持严格违反、两笔正预算及质量 $\mu$。这一步证明的是一个混合泛函见证，未声称扰动后仍是向量泛函。∎

### 41.6 代入实际核后对第三残量的新增有限排除

**推论 41.6（指定零探针全幅家族之外的第三格排除）。** 在 (41.1)、(41.4) 下，(41.24) 有下述实际、显式的 $s_3$ 约束。取

$$
\begin{gathered}
v=(10q_1,20q_2,1)^{\mathsf T},\quad
T=(-4,7,-3)^{\mathsf T},\quad H=(484/45,-617/36,19/3)^{\mathsf T},\\
u_\ell=(T_\ell+\iota H_\ell)/\overline{v_\ell},\quad
 y=-v-\iota q,\quad z_0=Cv+\frac\iota{10}(I_3+3C)v,\\
U=[u,Cu],\quad Y=[y,z_0],\quad G_U=U^*U,\quad J_U=U^*Y,\\
X=YG_U^{-1}U^*+UG_U^{-1}Y^*-UG_U^{-1}J_UG_U^{-1}U^*.
\end{gathered}
\tag{41.32}
$$

这是 (39.4)–(39.9) 的同一组 $(\lambda,a_0,b_0)=(1/5,0,1)$，其 Hermitian 构造与核本身属复用。保留其实际主列，斜率准确为

$$
\beta_+=-6/37,\quad\alpha_+=1/37,\qquad
\beta_-=-2/15,\quad\alpha_-=1/15,\qquad\eta=26.
\tag{41.33}
$$

本节新增的是在该核上保留 $s_0$ 后的全环境约束。为将它完全写成有限标量，置

$$
\begin{gathered}
z=-1/20+\iota\,787/3600,\qquad p=3/10-\iota\,383/600,\\
b_+=z-(3+19\iota)p/37,\qquad b_-=z+(1+7\iota)p/15,\\
B_*=37|b_+|^2/2+15|b_-|^2/2,\\
C_*=26(s_1^2|u_1|^2+s_2^2|u_2|^2)+B_*,\qquad
\ell=2(484s_1/45-617s_2/36)-5699s_0/300.
\end{gathered}
\tag{41.34}
$$

全称 PB 必须满足

$$
\left(\frac{38}{3}s_3+\ell\right)^2
\le104s_0^2\left(\frac{11492}{9}s_3^2+C_*\right)
\quad(s_0\ne0).
\tag{41.35}
$$

$s_0=0$ 时对应必要式为 $38s_3/3+\ell=0$。特别，若

$$
0<|s_0|<\frac{19}{26\sqrt{442}},\qquad
\gamma=\frac49\bigl(361-26^2\cdot442\,s_0^2\bigr)>0,
\tag{41.36}
$$

则每个满足以下显式有限阈值的 $s_3$ 都被严格排除：

$$
|s_3|>1+\frac{(76/3)|\ell|+|\ell^2-104s_0^2C_*|}{\gamma}.
\tag{41.37}
$$

这些排除具有定理 41.5 的同一有限原探针、两笔正预算及任意指定正质量保证。

证明。先核对实际核并非凭空假设。(41.32) 的矩为

$$
(t_0,t_1,t_2)=(0,1,-3),\qquad
(h_0,h_1,h_2)=(-1/20,-407/90,-4/5),
\quad t_k=\sum c_\ell^kT_\ell,\quad h_k=\sum c_\ell^kH_\ell.
$$

它们满足 (39.7)：$t_2+3t_1+2t_0=0$，$h_0=(3t_0-t_1)/20$，$h_2=(t_1+3t_2)/10$，且 $2h_0+9h_1-h_2=-40$。由 (39.8) 的直接内积展开，$J_U=J_U^*$。$u_1u_2\ne0$ 使 $u,Cu$ 独立，故 $G_U$ 正定；(41.32) 的前两项互为伴随，最后一项自伴，且 $XU=Y$，准确实现 $Xu=y,XCu=z_0$。这也给 (39.12)–(39.14) 的同一 Cayley 核：$\tau_\delta=-1+\delta/10-3\iota/10$、$|\tau_\delta-1|^2=(41-4\delta)/10$，$Z_\delta=\iota(\tau_\delta+1)(\tau_\delta-1)^{-1}A_\delta$，其比值正是 (41.33)。所以 (41.22) 在同一实际 Hermitian $X$ 上成立。

完整环境收缩保留 $q^*$ 的行维数。由 $\overline v_\ell u_\ell=T_\ell+\iota H_\ell$，准确有

$$
\begin{aligned}
q^*u&=(-4+\iota\,484/45)/10+(7-\iota\,617/36)/20
       =-1/20+\iota\,787/3600,\\
q^*Cu&=(-4+\iota\,484/45)/10+2(7-\iota\,617/36)/20
       =3/10-\iota\,383/600,\\
q-\iota Xu&=\iota v,\qquad
w_E=\sum_{\ell=1}^3s_\ell H_\ell-s_0/20,\\
|u_3|^2&=9+361/9=442/9.
\end{aligned}
\tag{41.38}
$$

任意原 $q_1,q_2$ 的相位均由这些原列准确消去，不改动 $t$。把 (41.33) 代入 (41.23) 就给 (41.34) 的 $b_\pm$；此外

$$
\begin{aligned}
37\operatorname{Re}b_+-15\operatorname{Re}b_-
&=22\operatorname{Re}z-4\operatorname{Re}p
                  +26\operatorname{Im}_\iota p\\
&=-11/10-6/5-26\cdot383/600=-5669/300.
\end{aligned}
$$

所以 $A_2=26s_0^2$，$A_1=38s_3/3+\ell$，$A_0=11492s_3^2/9+C_*$。定理 41.5 的判别式就成为 (41.35)。将其移到左侧，恰为

$$
\Delta=\gamma s_3^2+(76/3)\ell s_3+\ell^2-104s_0^2C_*.
\tag{41.39}
$$

在 (41.36) 下 $\gamma>0$；若 (41.37) 成立，则 $|s_3|>1$ 且 $\gamma|s_3|>(76/3)|\ell|+|\ell^2-104s_0^2C_*|$，从而 $\Delta>0$，这是严格 PB 违反的有限判据，证明所述排除。

为明确其超出定理 41.4 的内容，取 $s_1=s_2=0$ 及

$$
0<|s_0|<\min\left\{\frac{\sqrt{m+4n}}2,\frac{19}{26\sqrt{442}}\right\}.
\tag{41.40}
$$

此时 $d=s_0,F=m+4n$，无论 $s_3$ 为何，全部 (41.15) 的零探针家族都通过原 PB。然而 $C_*=B_*$、$\ell=-5699s_0/300$ 是有限常数，每个满足 (41.37) 的有限 $s_3$ 都由同一原输入中的另一份探针严格排除。这给出环境残量非零时的实际第三格排除，既未从必要测试制造非分级全称 PB 模型，也未声称这些测试已穷尽全部输出。∎

以上完整列、实部收缩、平方配方及阈值对每个分别固定的 $\sigma$ 均成立：只使用 $\iota^2=-1$、$\overline\iota=-\iota$ 及相对于该 $\iota$ 的实虚分解。没有在同一份 PB 内混合两种取向，也没有把复共轭解释为免费物理控制。

### 41.7 准确允许集、复用界面与仍开的分类

令 $\mathscr P_q$ 是定义 41.1 下全称原 PB 的完整输出集合。现有结论准确给

$$
\{K(c,t)+aJ:a\in\mathbb R\}\subseteq\mathscr P_q
\subseteq\{K(c,t)+\operatorname{diag}(s_1,s_2,s_3,s_0):s_j\in\mathbb R\},
\tag{41.41}
$$

右侧还必须同时满足 (41.16) 和对每份实际 (41.22) 的 (41.24)。环境零截面由定理 39.2 复用为 $\mathscr P_q\cap\{s_0=0\}=\{K(c,t)\}$。完整 $\mathscr P_q$ 是否仅为左侧分级直线仍是 open；没有证明满足这些必要条件即满足全部 PB，也没有证明一个非分级残量全称充分。定理 41.6 证明的只是其中一类有限排除，不把它改名为完整量子新公理。

这里阻止旧结论直接完成新分类的是一个准确项：原支持证明的线性残量读取在完整输出中与 $s_0^2\eta\rho^2$ 竞争。优化 $\rho$ 得到判别式，不能仅凭线性系数非零就声称任意大尺度产生违反。分级直线本身满足全称 PB，已经证明 PB 不能单独供应完整零谱 P2；这项固定输出障碍独立于未解决的“是否还有别的允许输出”。

### 41.8 数学归属与完整原目标的保留

未中心化复 Schwarz 的成熟形式及其对称／交换部分解，见 Schrödinger，*About Heisenberg Uncertainty Relation*，原文英译 [arXiv:quant-ph/9903100v3，式 (7)–(8)](https://arxiv.org/html/quant-ph/9903100v3#S0.E7)；该文随后中心化所得式 (9) 不是本节预算的定义。任意正复线性泛函的版本由 (41.14) 直接证明，正泛函背景也沿 §39.8 所引 Blackadar。实 Gram 面积、复列内积、Hermitian 插值、实二次式配方与仿射范数凸性是成熟线性代数；(41.20)、(41.27)–(41.30) 已在本节给出所需推导，不以文献名替代证明。Jordan 数据与复取向的区别可参见 Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)；该工作不被作为本节特定全输出允许集的分类定理。

仓内复用是多项式 PB 的 (28.13)–(28.25) 实际证明接口、定理 39.2 的 $s_0=0$ 截面和 (39.3)–(39.14) 的实际核。本节全环境关系 (41.16)、二次排除 (41.24) 及其实际第三格推论 (41.35)–(41.40) 是这些固定输入上的纸面综合；分级充分性与 P2 障碍的证明是 (41.11)–(41.14)。这些归属不主张历史优先权、文献穷尽、常数最优、整体最简或 Lean／kernel 认证。

本节完整保留并合取 [§39.8](#398-成熟归属与完整原来源边界) 的全文、其指向父卷 §6、§30A.5 和各逐层钉版原来源的完整合同，而非用以下说明替换它们。同一原 $\Omega$/native、原域 $E,C,u,N,\mathcal P,S,D,q,K/J$、全词、跨评价配对、原模式网络及具名接线保持身份；本节的矩阵 $E,D,u,q$ 只在定义 41.1 的局部域使用，不重定义这些上游对象。全部原准备、事件、过程、参考／副本、真正相关联合、中央／经典／不等维／静默／无轴块、零／不等／次归一质量、物理钟、单位、控制、parent／ready／flags、环境、全部成功失败细记录、完整活动输出、port／post-port、拒绝、停止、销毁、泄漏、真分组遗忘、两侧及逆向 Return、固定支持全质量、完整菜单、全部已量化中间切口与每份输出的每个旧合法未来继续保留。精确 $B$ 与闭 $B_{\rm cl}$、同一 $\sigma,t_0$、原域／resolvent 及 $3s+r\le1$ 均保持各自原边界，未定义请求不补零。

实际来源中，[C139 固定源卷 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md#233全原域归属仍保留的量词) 仍需字面旧程序 $\tau;T_P$ 的指定接受族与同一实际全菜单事件 $k_b^\dagger P_{J_0}k_b$ 的准备无关接受接口证书，覆盖全部原准备、参考、切口、合法分析词与树，并保留支持、未归一标尺、类型、ready、控制、钟、互补结果、记录与合法未来。它不要求历史双射，但没有被矩阵相等、菜单存在、纯校准、操作逆或矩阵综合供应。[Fourier 卷 §10.3–10.4](AURIC_C139_FOURIER_OVERLAPS_AND_GLOBAL_FRAMED_BORN_RIGIDITY.md) 的实际原子归属与特定正校准准备仍须构造；其已给局部双块反例不被误报为完整原 $\Omega$ 反模型。

CountRead 仍需同一接受叶的完整活动输出、真实读后 active-ready、第一合法消费者，以及保留整份活动输入、原参考／控制／钟和全部旧合法未来的实际 Return。[有限返回续卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的独立查询候选与原活动接头继续区分；表、地址和档案不供应活动发生标识或未来权限。本节没有生成准备、复制、自由相干控制或密度／历史身份，也不从旧 Born／CP／QC 循环推回实际来源。固定源 §§50–85、原词 §§385–392 及 §39.8 已列的下降、递归参考、累计真支持和同一旧 $D$ 恢复，仍按既成原域复用，不重新列作缺失。

[静态 Atlas 续卷 III §63](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md#63-两个单位切片与完整读回律) 的两映射／两单位切片结果保持完整条件：三个实际有限全态全效果载体及其整个锥、有限混合比较 S 和保归一化 Jordan 桥、各扇区本原迹一的 canonical trace、全锥正的 $L$、同一个全局正保迹的 $p$、两条完整实张成、全部实方向的 $W_J,W_H,\mathrm{III}$，以及良定义后的整锥交叉插入 $I_{13}$ 正性均保留。其 $p_{13}=I_{13}^*$ 的全锥正保迹性及完整读回律已在这些条件下取得，不能改报为本节新增缺口；本节也没有删去这些条件。含经典扇区的复矩阵块、块张量及静态 Born 仍在该准确域内，不因此取得 CP、仪器、动力学、独立右载体或无界份数相容。

七项量子消费者继续按 §39.8 和有限返回 162.1–162.2 的完整合同使用：共同全词、共同核及实际相干准备才接 Hilbert／相干；实际事件、完整菜单、固定支持全质量及正质量绑定才接 Born；真正相关共同联合、忠实同向交换腿及共同生成才接张量；完整 typed 接续、递归参考、全部环境／记录／失败／后口、相关正输入、真支持与累计运输才接 CP／Kraus；完整仪器、单位分区、AC、$N_u,X,X_s$、平方根词与接受端、正输出质量及射线／校准条件才接 TP／更新／Lüders；全历史、真遗忘及全部旧未来的实际两侧／逆向返回才接历史／Return；真实连续可逆流、实际逆、强连续实现、生成元域、物理钟／单位／能量和共同正 $\hbar$ 才接 Hamiltonian。局部 PB 障碍不撤回这些已成条件定理，也不支付它们未给的实际前件。完整全输出分类、完整原 Omega 量子起源、无缺口来源的完整量子公理候选及整体严格更简目标均仍未完成。

### 41.9 完整中文几何

原问题先固定演员与它连向环境的那两条腿，再问同一个输出在所有演员探针和所有完整读出下能否守住预算。预算是完整四维中两条列向量张开的实面积，第四格即使不是演员，也仍参与面积。谱格之间的两种伴轴可以先锁住所有非对角误差，但环境留下一个实数，不能因它的演员谱值是零就直接删掉。若演员三格一起加上同一个数、环境反向减去这个数，带符号的交换子恒等式恰好仍闭合，所以这整条分级直线都通过 PB；它在环境零谱测试上却留下非零输出，说明 PB 单独并不保证该 P2。对其他误差，零探针已给一把准确的尺：完整第四列产生的常数、一次项和二次项决定两笔面积的最小和，超过 (41.16) 就在有限非零幅度上失败，而且两笔预算都开着。但这一把尺看不见第三格，不能把它当成全部分类。把同一实际 Hermitian 探针的两个演员核接回环境时，第四列还留下随尺度增长的项；平方后是正的二次代价，旧的线性放大不能压过它。保留这项再配方，得到新的判别式；代入原有的第三格核，还能明确排除一些通过全部零探针测试的完整输出。这些都是同一原输入、同一份实现内的约束，不把分别最优的预算拼接，也不把必要测试通过当作全称充分。目前仍缺的是对全部非分级输出的穷尽判定；这些矩阵尺还没有造出原世界的准备、菜单、接受接头或真实活动返回，完整量子起源的目标因此保持原样。

## 新增锚（本行以下为后续增补区）
## 42. 秩二原环境零第三对角的全 PB 分类与有限奇异探针

### 42.1 同一固定输出与分类的准确量词

**定义 42.1（零第三对角的原秩二输入）。** 完整沿用定义 40.1 的原有序基 $(e_1,e_2,e_3,f_1,f_2)$、原 $A=M_5(\mathbb C)$、$P=I_3\oplus0_2$、$c=\operatorname{diag}(1,2,3,0,0)$，仅将其任意 Hermitian 块 $B$ 限定为 $B_{33}=0$。具体写成

$$
\begin{gathered}
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix},\qquad
V=[\kappa e_1,\gamma e_2],\qquad D_{\rm env}=\operatorname{diag}(0,d),\\
\kappa,\gamma>0,\qquad d\in\mathbb R\setminus\{0\},\qquad
B=B^*,\qquad B_{33}=0,\\
a=(B_{12},B_{13}),\qquad C_E=\operatorname{diag}(2,3),\qquad
T=\begin{pmatrix}b&z\\\overline z&0\end{pmatrix},\qquad
b=B_{22}\in\mathbb R,\quad z=B_{23}\in\mathbb C,\\
\mathsf E_s=sE_{33},\qquad s\in\mathbb R,\qquad
\sigma\in\{1,-1\}\text{ 分别固定},\qquad \iota=\sigma i,\qquad
g=K(c,t)+\mathsf E_s,\quad K(U,Z)=\frac{\iota}{2}[U,Z].
\end{gathered}
\tag{42.1}
$$

这里 $T$ 只是原 $B$ 的指定主子块，不要求 $E=\operatorname{span}(e_2,e_3)$ 对 $t$ 或 $B$ 不变。所有标签仍为 (32.2) 的完整原乘法：对任意原 $x=x^*=PxP$，

$$
\begin{gathered}
h=K(c,x),\quad r=c\circ x,\quad k_t=c\circ t,\quad U\circ Z=(UZ+ZU)/2,\\
R_\delta=x+\delta(h-k_t),\qquad
S_\delta=t+\delta(r+g),\qquad \delta\in\{1,-1\},\\
L=-2x\circ(h-k_t)-2t\circ(r+g),\qquad
B_\phi(U,Z)=\phi(U^2)\phi(Z^2)-\phi(U\circ Z)^2.
\end{gathered}
\tag{42.2}
$$

PB 始终指同一 $x$、同一完整原正复线性泛函 $\phi$ 上的 (32.3)，两份预算不分别优化。

**定理 42.2（$B_{33}=0$ 的全部原探针分类）。** 固定任意一份 (42.1)，固定任一取向 $\sigma$，再任意指定 $0<\mu<\infty$。以下三项等价：

1. $s=0$；
2. 全部原 Hermitian 角探针和全部原 $M_5(\mathbb C)$ 正复线性泛函满足 PB；
3. 全部原 Hermitian 角探针和全部质量恰为 $\mu$ 的原 $M_5(\mathbb C)$ 正复线性泛函满足 PB。

更准确地，每个 $s\ne0$ 都有下文明确给出的一个有限原 $x$、一个原向量 $\xi\ne0$ 和一个正泛函 $\phi$，使

$$
\begin{gathered}
N=\|\xi\|^2>0,\qquad \phi(I_5)=\mu,\\
\sqrt{B_\phi(R_\delta,S_\delta)}
 \ge\frac{\mu\gamma^2\rho_*^2}{N}>0\quad(\delta=1,-1),\\
\phi(L)-\sum_{\delta=\pm1}\sqrt{B_\phi(R_\delta,S_\delta)}
 >\frac{\mu s^2}{20N}>0.
\end{gathered}
\tag{42.3}
$$

$\rho_*>0$ 是 (42.22) 的显式有限尺度。原 $B,V,D_{\rm env},d,t,g$ 和演员基均保持原值；不加 P2、未知总响应的旋转／自然性／连续性或任何新的环境前件。下述各小节共同构成证明；$s=0$ 和零质量情形在 §42.6 按原域复用。

### 42.2 同一个 Hermitian 探针与完整五维输出

固定 $s\ne0$，置

$$
A_0=-\frac{5s}{2},\qquad Q_0=\frac{s}{2}(4+\iota),\qquad p=-2s.
\tag{42.4}
$$

对每个有限 $\rho>0$，在原坐标中取

$$
\begin{gathered}
u_\rho=(\rho,1)^{\mathsf T},\qquad
X_\rho=\begin{pmatrix}A_0/\rho^2&Q_0/\rho\\
\overline{Q_0}/\rho&p\end{pmatrix},\\
\eta_\rho=2B_{12}\rho+3B_{13},\qquad
\ell_\rho=(-\iota\eta_\rho/\rho,\ \iota\eta_\rho),\\
\xi_\rho=(0,\rho,1,-(B_{12}\rho+B_{13})/\kappa,0)^{\mathsf T},\\
x_\rho=\begin{pmatrix}
0&\ell_\rho&0_{1,2}\\
\ell_\rho^*&X_\rho&0_{2,2}\\
0_{2,1}&0_{2,2}&0_{2,2}
\end{pmatrix}.
\end{gathered}
\tag{42.5}
$$

此处块顺序为 $e_1,(e_2,e_3),(f_1,f_2)$。$A_0,p$ 为实数，故 $X_\rho=X_\rho^*$，进而 $x_\rho=x_\rho^*=Px_\rho P$。$u_2=\rho\ne0,u_3=1\ne0$，所以引理 40.3 的两个除法合法；$\xi_\rho$ 的第三格为一，保证其非零。$\kappa>0$ 和 $\rho>0$ 保证所有条目有限，不要求 $a,z$ 或 $\eta_\rho$ 非零。

这是 (40.4) 在同一原空间的直接取值。为显式核对回接，记 $w_\rho=-au_\rho/\kappa$，则

$$
\ell_\rho u_\rho=-\iota\eta_\rho+\iota\eta_\rho=0,\qquad
\ell_\rho C_Eu_\rho=-2\iota\eta_\rho+3\iota\eta_\rho=\iota\eta_\rho,
\qquad au_\rho+\kappa w_\rho=0.
$$

完整原乘法给出下表，块顺序为 $e_1,E,f_1,f_2$：

$$
\begin{array}{c|cccc}
 &e_1&E&f_1&f_2\\ \hline
x_\rho\xi_\rho&0&X_\rho u_\rho&0&0\\
x_\rho c\xi_\rho&\iota\eta_\rho&X_\rho C_Eu_\rho&0&0\\
cx_\rho\xi_\rho&0&C_EX_\rho u_\rho&0&0\\
t\xi_\rho&0&Tu_\rho&0&\gamma\rho\\
tc\xi_\rho&\eta_\rho&TC_Eu_\rho&0&2\gamma\rho\\
ct\xi_\rho&0&C_ETu_\rho&0&0
\end{array}
\tag{42.6}
$$

特别 $h\xi_\rho,k_t\xi_\rho$ 的第一格同为 $\eta_\rho/2$，$r\xi_\rho,g\xi_\rho$ 的第一格分别为 $\iota\eta_\rho/2,-\iota\eta_\rho/2$，故两条 $R_\delta,S_\delta$ 的第一格均准确抵消。所有这些列的 $f_1$ 格为零。$h,r,k_t,g$ 的 $f_2$ 格依次为 $0,0,\gamma\rho,-\iota\gamma\rho$，所以 $R_\delta,S_\delta$ 的 $f_2$ 输出分别为 $-\delta\gamma\rho,\gamma(1-\delta\iota)\rho$。原 $d$ 因输入 $f_2$ 格为零而不出现；原第二环境输出保留。

$E$ 两格所需的每条列也可直接写出：

$$
\begin{aligned}
X_\rho u_\rho&=((A_0+Q_0)/\rho,\ \overline{Q_0}+p)^{\mathsf T},\\
K(C_E,X_\rho)u_\rho&=(-\iota Q_0/(2\rho),\ \iota\overline{Q_0}/2)^{\mathsf T},\\
(C_E\circ X_\rho)u_\rho&=((2A_0+5Q_0/2)/\rho,\ 5\overline{Q_0}/2+3p)^{\mathsf T},\\
Tu_\rho&=(b\rho+z,\ \overline z\rho)^{\mathsf T},\\
(C_E\circ T)u_\rho&=(2b\rho+5z/2,\ 5\overline z\rho/2)^{\mathsf T},\\
(K(C_E,T)+sP_3)u_\rho&=(-\iota z/2,\ s+\iota\overline z\rho/2)^{\mathsf T},
\quad P_3=\operatorname{diag}(0,1).
\end{aligned}
\tag{42.7}
$$

其中常数的关键相消为

$$
\begin{gathered}
A_0+Q_0=s(-1/2+\iota/2),\qquad
\overline{Q_0}+p=-\iota s/2,\\
-\iota Q_0/2=s(1/4-\iota),\qquad
\iota\overline{Q_0}/2=s(1/4+\iota),\\
2A_0+5Q_0/2=5\iota s/4,\qquad
5\overline{Q_0}/2+3p+s=-5\iota s/4.
\end{gathered}
\tag{42.8}
$$

定义下列全部有限系数；它们不是另选的作用列：

$$
\begin{array}{c|ccc}
\delta&r_\delta&r'_\delta&v_\delta\\ \hline
+1&s(-1/4-\iota/2)&s(1/4+\iota/2)&5\iota s/4\\
-1&s(-3/4+3\iota/2)&s(-1/4-3\iota/2)&-5\iota s/4
\end{array}
$$

$$
\begin{gathered}
q_\delta=-5\delta z/2,\qquad m_\delta=(1-\delta\iota/2)z,\\
a_\delta=-2\delta b,\qquad b_\delta=-5\delta\overline z/2,\qquad c_\delta=-\delta\gamma,\\
d_\delta=b,\qquad e_\delta=(1+\delta\iota/2)\overline z,\qquad
f_\delta=\gamma(1-\delta\iota).
\end{gathered}
\tag{42.9}
$$

小写 $c_\delta,d_\delta$ 是这里的列系数，与原算子 $c$、原环境参数 $d$ 不同。由 (42.6)–(42.8)，完整原列准确为

$$
\begin{aligned}
\mathbf R_\delta(\rho):=R_\delta\xi_\rho
 &=\left(\frac{r_\delta}{\rho}+q_\delta+\rho a_\delta\right)e_2
   +(r'_\delta+\rho b_\delta)e_3+\rho c_\delta f_2,\\
\mathbf S_\delta(\rho):=S_\delta\xi_\rho
 &=\left(\frac{v_\delta}{\rho}+m_\delta+\rho d_\delta\right)e_2
   +(-v_\delta+\rho e_\delta)e_3+\rho f_\delta f_2.
\end{aligned}
\tag{42.10}
$$

$B_{11}$ 未被设零，而是由于输入第一格为零及 (42.6) 的原补偿而不贡献这些列。$B_{12},B_{13}$ 仍在同一个 $x_\rho,\xi_\rho$ 中；$b,z$ 任意，未作相位归一、旋转原基或更换原 $t$。三条存活输出方向 $e_2,e_3,f_2$ 只描述这些指定向量的输出，不给算子约化或全泛函压缩等价。

### 42.3 实 Gram 的完整复外积分解与全部多项式系数

记 $\chi_\rho(Y)=\xi_\rho^*Y\xi_\rho$，并在原 $\mathbb C^5$ 上定义

$$
\begin{gathered}
I_\delta(\rho)=\operatorname{Im}_{\iota}
 (\mathbf R_\delta(\rho)^*\mathbf S_\delta(\rho)),\qquad
\operatorname{Im}_{\iota}w=(w-\overline w)/(2\iota),\\
\Omega_\delta(\rho)=\mathbf R_\delta(\rho)\wedge\mathbf S_\delta(\rho),\qquad
\mathcal A_\delta(\rho)=\sqrt{B_{\chi_\rho}(R_\delta,S_\delta)},\\
j_\delta(\rho)=\rho^2I_\delta(\rho),\qquad
\mathcal W_\delta(\rho)=\rho\Omega_\delta(\rho).
\end{gathered}
\tag{42.11}
$$

外积范数使用原 Hermitian 内积诱导的范数，原有序正交基的 $e_j\wedge e_k$（$j<k$，包括环境基向量）为正交单位基。此处应用标准 Gram／Lagrange 恒等式，直接展开为

$$
\begin{aligned}
\|R\wedge S\|^2
 &=\sum_{j<k}|R_jS_k-R_kS_j|^2\\
 &=\sum_{j\ne k}|R_j|^2|S_k|^2
   -2\operatorname{Re}\sum_{j<k}R_j\overline{R_k}S_k\overline{S_j}\\
 &=\|R\|^2\|S\|^2-|R^*S|^2.
\end{aligned}
$$

由于原 $R_\delta,S_\delta$ 自伴，$\chi_\rho(U^2)=\|U\xi_\rho\|^2$、$\chi_\rho(U\circ Z)=\operatorname{Re}((U\xi_\rho)^*Z\xi_\rho)$。又 $|w|^2=(\operatorname{Re}w)^2+(\operatorname{Im}_{\iota}w)^2$，故原实 Gram 面积准确是

$$
\mathcal A_\delta(\rho)^2
 =I_\delta(\rho)^2+\|\Omega_\delta(\rho)\|^2.
\tag{42.12}
$$

这是完整复外积加虚内积，不是把原实 Gram 换成复 Gram。因 (42.10) 的其余两格准确为零，外积的非零坐标只可能沿
$E_{23}=e_2\wedge e_3$、$E_{2f}=e_2\wedge f_2$、$E_{3f}=e_3\wedge f_2$。这些记号是外积基，不是原矩阵单位。

以下给出 (42.11) 的所有多项式系数。对每个 $\delta$，暂在右端省略同一 $\delta$ 下标，令

$$
\begin{aligned}
\alpha_{\delta,1}&=\operatorname{Im}_{\iota}(\overline r m+\overline q v),\\
\alpha_{\delta,2}&=\operatorname{Im}_{\iota}
 (\overline r d+\overline q m+\overline a v-\overline{r'}v),\\
\alpha_{\delta,3}&=\operatorname{Im}_{\iota}
 (\overline q d+\overline a m+\overline{r'}e-\overline b v),\\
\alpha_{\delta,4}&=\operatorname{Im}_{\iota}
 (\overline a d+\overline b e+\overline c f).
\end{aligned}
\tag{42.13}
$$

这里只在右端省略下标的 $b,c,d,e,f$ 均指 (42.9) 的 $b_\delta,c_\delta,d_\delta,e_\delta,f_\delta$，不是原 $b,c,d$。定义 $\mathbf W_{\delta,k}$ 为下表三坐标的外积向量：

$$
\begin{array}{c|ccc}
 &E_{23}&E_{2f}&E_{3f}\\ \hline
\mathbf W_{\delta,1}&re-qv-r'm-bv&rf-cv&0\\
\mathbf W_{\delta,2}&qe-av-r'd-bm&qf-cm&r'f+cv\\
\mathbf W_{\delta,3}&ae-bd&af-cd&bf-ce
\end{array}
\tag{42.14}
$$

于是逐项相乘给出有限的准确多项式

$$
\begin{aligned}
j_\delta(\rho)&=J_\delta+\sum_{k=1}^4\alpha_{\delta,k}\rho^k,
 &J_\delta&=\operatorname{Im}_{\iota}(\overline{r_\delta}v_\delta),\\
\mathcal W_\delta(\rho)&=\mathbf D_\delta+
 \sum_{k=1}^3\rho^k\mathbf W_{\delta,k},
 &\mathbf D_\delta&=-(r_\delta+r'_\delta)v_\delta E_{23}.
\end{aligned}
\tag{42.15}
$$

为核对阶数及关键抵消，$\rho^{-2}$ 的外积项是两个 $e_2$ 方向的外积，准确为零；$\rho^{-1}$ 的 $E_{23}$ 系数是 $-r_\delta v_\delta-r'_\delta v_\delta$。例如未乘 $\rho$ 的完整 $E_{2f}$ 系数是
$r_\delta f_\delta-c_\delta v_\delta+\rho(q_\delta f_\delta-c_\delta m_\delta)+\rho^2(a_\delta f_\delta-c_\delta d_\delta)$，而 $E_{3f}$ 系数是
$\rho(r'_\delta f_\delta+c_\delta v_\delta)+\rho^2(b_\delta f_\delta-c_\delta e_\delta)$，正好给 (42.14)。没有遗漏环境外积。两种符号的首项直接计算为

$$
\begin{gathered}
\overline{r_+}v_+=s^2(-5/8-5\iota/16),\qquad
\overline{r_-}v_-=s^2(-15/8+15\iota/16),\\
J_+=-5s^2/16<0,\qquad J_-=15s^2/16>0,\\
r_++r'_+=0,\qquad r_-+r'_-=-s,\\
\mathbf D_+=0,\qquad \mathbf D_-=-5\iota s^2E_{23}/4,
\qquad \|\mathbf D_-\|=5s^2/4.
\end{gathered}
\tag{42.16}
$$

因此首项不依赖任意的 $b,z,\gamma$，但这些原输入仍完整存在于 (42.13)–(42.14)。令

$$
K_\delta=\sum_{k=1}^4|\alpha_{\delta,k}|,\qquad
H_\delta=\sum_{k=1}^3\|\mathbf W_{\delta,k}\|.
$$

所有系数有限，故 $K_\delta,H_\delta$ 有限非负。由三角不等式，对 $0<\rho\le1$ 有明确界

$$
|j_\delta(\rho)-J_\delta|\le\rho K_\delta,\qquad
\|\mathcal W_\delta(\rho)-\mathbf D_\delta\|\le\rho H_\delta.
\tag{42.17}
$$

### 42.4 原接触恒等式、常残量与显式有限差额

引理 38.1 的 (38.4) 只用结合乘法，故在原 $M_5$ 中同样成立。为展示所需抵消，记 $g_0=K(c,t)$、$A=h-k_t$、$B_0=r+g_0$。双线性给

$$
K(R_+,S_+)-K(R_-,S_-)=2K(x_\rho,B_0+\mathsf E_s)+2K(A,t).
$$

去掉 $\mathsf E_s$ 后，展开中两个混合项分别为

$$
\begin{aligned}
2K(x_\rho,g_0)&=-\tfrac12(x_\rho ct-x_\rho tc-ctx_\rho+tcx_\rho),\\
2K(h,t)&=-\tfrac12(cx_\rho t-x_\rho ct-tcx_\rho+tx_\rho c).
\end{aligned}
$$

其中 $x_\rho ct,tcx_\rho$ 成对抵消；另有
$2K(x_\rho,r)=-K(c,x_\rho^2)$、$-2K(k_t,t)=-K(c,t^2)$。因此

$$
\begin{aligned}
2K(x_\rho,B_0)+2K(A,t)
 &=-K(c,x_\rho^2+t^2)\\
 &\quad+\tfrac12(x_\rho tc+ctx_\rho-cx_\rho t-tx_\rho c)\\
 &=-2x_\rho\circ A-2t\circ B_0.
\end{aligned}
$$

最后一式也可将右端分为 $-2x_\rho\circ h-2t\circ g_0=-K(c,x_\rho^2+t^2)$ 与
$2x_\rho\circ k_t-2t\circ r=\tfrac12(x_\rho tc+ctx_\rho-cx_\rho t-tx_\rho c)$ 直接核对。加回残量即得

$$
L=K(R_+,S_+)-K(R_-,S_-)-2K(x_\rho,\mathsf E_s)-2t\circ\mathsf E_s.
\tag{42.18}
$$

对原自伴 $U,Z$，准确有

$$
\chi_\rho(K(U,Z))=-\operatorname{Im}_{\iota}((U\xi_\rho)^*Z\xi_\rho).
$$

由 (42.6)–(42.8)，$(x_\rho\xi_\rho)_3=-\iota s/2$、$(t\xi_\rho)_3=\overline z\rho$、$\mathsf E_s\xi_\rho=se_3$。故

$$
\begin{aligned}
(x_\rho\xi_\rho)^*\mathsf E_s\xi_\rho&=\iota s^2/2,
 &\chi_\rho(K(x_\rho,\mathsf E_s))&=-s^2/2,\\
(t\xi_\rho)^*\mathsf E_s\xi_\rho&=s\rho z,
 &\chi_\rho(t\circ\mathsf E_s)&=s\rho\operatorname{Re}z,\\
\chi_\rho(L)&=-I_+(\rho)+I_-(\rho)+s^2-2s\rho\operatorname{Re}z.
\end{aligned}
\tag{42.19}
$$

常非零项 $s^2$ 来自同一个 $X_\rho,u_\rho$ 的非零虚部，不再要求 §40.4 的 $sB_{33}$ 读取非零。

对任一使 $j_\delta(\rho)\ne0$ 的尺度，由 (42.11)–(42.12) 有准确有理化等式

$$
\begin{aligned}
E_\delta(\rho)&:=\mathcal A_\delta(\rho)-|I_\delta(\rho)|\\
 &=\frac{\|\mathcal W_\delta(\rho)\|^2}
 {\sqrt{j_\delta(\rho)^2+\rho^2\|\mathcal W_\delta(\rho)\|^2}
   +|j_\delta(\rho)|}\\
 &\le\frac{\|\mathcal W_\delta(\rho)\|^2}{2|j_\delta(\rho)|}.
\end{aligned}
\tag{42.20}
$$

这是完整原预算超出虚内积绝对值的非负代价。定义同一固定输入的有限数

$$
M=1+K_++K_-+H_++H_-+|\operatorname{Re}z|>0.
\tag{42.21}
$$

明确选取

$$
\rho_* =\min\left\{1,\frac{s^2}{128M},\frac{|s|}{32M}\right\}>0.
\tag{42.22}
$$

每个 $K_\delta,H_\delta,|\operatorname{Re}z|$ 都严格小于 $M$。所以 (42.17) 给
$\rho_*K_\delta<s^2/128$、$\rho_*H_\delta<s^2/128$，而最后一个尺度项给
$2|s|\rho_*|\operatorname{Re}z|<s^2/16$。结合 (42.16)，逐项得到

$$
\begin{gathered}
j_+(\rho_*)<0,\qquad |j_+(\rho_*)|\ge |J_+|/2=5s^2/32,\\
j_-(\rho_*)>0,\qquad j_-(\rho_*)\ge(63/64)J_-,\\
\|\mathcal W_+(\rho_*)\|\le s^2/16,\qquad
\|\mathcal W_-(\rho_*)\|\le(65/64)\|\mathbf D_-\|,\\
2|s|\rho_*|\operatorname{Re}z|<s^2/16.
\end{gathered}
\tag{42.23}
$$

所用常数比较分别是
$1/128<5/32$、$1/128<15/1024$、$1/128<1/16$、$1/128<5/256$；其中 $15s^2/1024=J_-/64$，$5s^2/256=\|\mathbf D_-\|/64$。因此不靠未指定的邻域选择，已在有限尺度上保证所需符号及分母非零。

将 (42.23) 代入 (42.20)，写 $E_\delta=E_\delta(\rho_*)$，得到

$$
\begin{aligned}
E_+&\le\frac{s^4/256}{5s^2/16}=\frac{s^2}{80},\\
E_-&\le\frac{(65/64)^2}{63/64}
 \frac{(5s^2/4)^2}{2(15s^2/16)}
 =\frac{4225}{4032}\frac{5s^2}{6}
 =\frac{21125}{24192}s^2<\frac78s^2.
\end{aligned}
\tag{42.24}
$$

最后的严格比较由 $7/8-21125/24192=43/24192>0$ 给出。由于 $I_+(\rho_*)<0<I_-(\rho_*)$，(42.19) 中两个大项准确等于 $|I_+|+|I_-|$，不是近似相消。故同一个原见证上的严格差额为

$$
\begin{aligned}
\chi_{\rho_*}(L)-\mathcal A_+(\rho_*)-\mathcal A_-(\rho_*)
 &=s^2-2s\rho_*\operatorname{Re}z-E_+-E_-\\
 &>s^2\left(1-\frac1{16}-\frac1{80}-\frac78\right)
 =\frac{s^2}{20}>0.
\end{aligned}
\tag{42.25}
$$

特别 $\chi_{\rho_*}(L)>0$，所以将 PB 左端写成 $|\chi_{\rho_*}(L)|$ 不改变这个差额。所有尺度和系数只依赖同一固定原输入、$s,\sigma$；没有替换原响应值或把两次读取的分别最优值拼在一起。

### 42.5 存活环境、两笔正预算和准确全质量

还须逐笔支付环境对原实 Gram 的贡献。令 $R_{\delta,E}u_\rho,S_{\delta,E}u_\rho$ 为引理 40.3 的二维比较列；它们只是 (42.10) 的 $E$ 两格。记其范数平方为 $A_{\delta,E},D_{\delta,E}$，实内积为 $C_{\delta,E}$，实 Gram 行列式为 $G_{\delta,E}\ge0$。由保留的完整 $f_2$ 输出，置 $n=\gamma^2\rho^2>0$，完整两范数平方和实内积分别准确为

$$
A_{\delta,E}+n,\qquad D_{\delta,E}+2n,\qquad C_{\delta,E}-\delta n.
$$

最后一式使用 $\operatorname{Re}((-\delta\gamma\rho)^*\gamma(1-\delta\iota)\rho)=-\delta n$。因此

$$
\begin{aligned}
B_{\chi_\rho}(R_\delta,S_\delta)
 &=(A_{\delta,E}+n)(D_{\delta,E}+2n)-(C_{\delta,E}-\delta n)^2\\
 &=G_{\delta,E}+n(2A_{\delta,E}+D_{\delta,E}+2\delta C_{\delta,E})+n^2,\\
2A_{\delta,E}+D_{\delta,E}+2\delta C_{\delta,E}
 &=\|S_{\delta,E}u_\rho+\delta R_{\delta,E}u_\rho\|^2
   +\|R_{\delta,E}u_\rho\|^2\ge0.
\end{aligned}
\tag{42.26}
$$

这是 (40.6) 在原类型内的代入，故 $\mathcal A_\delta(\rho_*)\ge\gamma^2\rho_*^2>0$。这些环境项也已全部包括在 (42.12)–(42.24) 的完整外积与虚内积中；(42.26) 不另扣除或忽略其代价。

任给指定 $0<\mu<\infty$，取

$$
N=\|\xi_{\rho_*}\|^2
 =1+\rho_*^2+\frac{|B_{12}\rho_*+B_{13}|^2}{\kappa^2}>0,\qquad
\phi(Y)=\frac{\mu}{N}\xi_{\rho_*}^*Y\xi_{\rho_*}.
\tag{42.27}
$$

这是完整原 $M_5(\mathbb C)$ 上的正复线性泛函，$\phi(I_5)=\mu$ 准确成立。每笔预算乘 $(\mu/N)^2$，每笔预算平方根和左端均乘同一个 $\mu/N>0$。将 (42.25)–(42.26) 乘此因子即得 (42.3)。这排除了每个非零实 $s$，且在每个指定正质量上同时给出两笔严格正预算。

### 42.6 零残量、两个取向及本固定分支的边界

$s=0$ 时，(42.18) 的残量项为零。直接复用 §39.6 的全正泛函复 Cauchy–Schwarz：对完整原代数上的任一正复线性泛函，
$\phi(K(U,Z))^2\le B_\phi(U,Z)$；将其用于两符号，再用三角不等式即得 PB。此充分性覆盖混合、非忠实、奇异、零预算及任意有限质量的正泛函，不从所选向量泛函外推。质量零的正泛函只能为零，PB 是零等式，亦按 §39.6 复用；它不能独自辨认 $s$。这与 §42.5 的每个指定正质量的必要性合起来，完成定理 42.2 的三项等价。

所有列、实数系数和符号计算只用 $\iota^2=-1,\overline\iota=-\iota$，所以分别固定 $\sigma=1$ 或 $\sigma=-1$ 均成立，不共轭或改变任意原 $B$，也不要求两取向共用同一探针。$z=0,b=0,a=0$ 的任意组合均可直接代入，未要求额外非零坐标；真正需要的 $u_2u_3\ne0$、$\kappa>0$、$\gamma>0$、$N>0$ 和有理化分母非零已逐项给出。原 $d\ne0$ 始终保持，不以它在指定列中不出现为由删除原输入条件。∎

定理 42.2 支付 §40.5 所指的 $B_{33}=0$ 第三残量分支；与定理 40.2 合用，得到定义 40.1 中任意 Hermitian $B$ 的固定输出 $sE_{33}$ 全 PB 当且仅当 $s=0$，并在每个指定正质量上有非零残量的有限双正预算见证。这里没有把一般对角、非对角或算子值残量纳入新结论，也没有把总 $V$ 秩二等同于零模像具有两腿；本原环境仍是 $V(\ker D_{\rm env})=\mathbb C e_1$。§§32–40 的全部定理继续保留其原假设和原域。

有限见证只使用 (42.22) 的正 $\rho_*$。当 $\rho\downarrow0$ 时某些探针条目无界，不给统一有界探针、最优尺度、物理控制或取得成本。一般任意 $B,V,D_{\rm env}$ 的全部残量、未知总响应及完整 $\mathsf H$，仍须其各自关系；$\mathcal E_+^D=\mathcal E_-^D$ 和 $N_\omega(\varepsilon)^2\to0$ 也不由此推出。

### 42.7 几何简化、量子乘法行与完整原来源

几何上无需令两笔实 Gram 面积同时趋零。由完整有限多项式 (42.15) 和准确等式 (42.20) 直接有

$$
\lim_{\rho\downarrow0}E_+(\rho)=0,\qquad
\lim_{\rho\downarrow0}E_-(\rho)
 =\frac{\|\mathbf D_-\|^2}{2J_-}=\frac{5s^2}{6}.
\tag{42.28}
$$

原因是 $j_\delta\to J_\delta\ne0$、$\mathcal W_\delta\to\mathbf D_\delta$，故 (42.20) 分母趋于 $2|J_\delta|$；$\mathbf D_+=0$ 给第一式。两笔原面积各有 $\rho^{-2}$ 大项，但其虚内积部分由 (42.19) 精确支付。最终未归一差额趋于 $s^2-5s^2/6=s^2/6>0$。实际严格见证仍是有限的 (42.22)，(42.28) 只解释构造。所需几何资料化为同一对原列的两个二元运算 $R^*S$ 与 $R\wedge S$；三条存活输出方向中的环境分量全部保留。没有更换原世界的乘法，也没有增加免费旋转。

常数种子 (42.4) 直接取自既有 (38.29)，原完整回接与 $n^2$ 代价取自引理 40.3，接触恒等式取自引理 38.1。本节在其准确原类型内给出 (42.5)–(42.27) 的奇异有限探针族、完整列多项式、相反首项符号、剩余面积代价与有限正尺度，进而完成零第三对角的全称分类。标准正泛函、复 Cauchy–Schwarz 的背景沿 §39.8 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)；Hermitian／实 Gram 和复外积的有限维线性代数步骤沿 Horn–Johnson，[*Matrix Analysis*](https://doi.org/10.1017/CBO9781139020411)。所需恒等式和界均在本定理证明内展开，这些成熟工具不单列为新的 PB 定理。

本节没有新增公理。复矩阵代数、Hermitian 量、结合乘法和完整正泛函已经是原模型前件，结论只是在原 PB 下排除指定固定槽位的残量。只有另已辨识同一个原响应值 $g=D(c,t)$，才可将 $s=0$ 写成 $D(c,t)=\sigma i[c,t]/2$，从而准确得到

$$
c\circ t-iD(c,t)
 =\frac{ct+tc}{2}+\frac{\sigma}{2}(ct-tc)
 =\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
\tag{42.29}
$$

这对应常规复乘法在这个原输入对上的 Jordan 部分与定向 Lie 部分。对 $U=c,Z=t$ 再用 §39.6 的同一复 Cauchy–Schwarz，得到该固定输出的全正泛函 P2；P2 没有进入定理 42.2 的必要性前件。一个固定槽位的 (42.29) 不给未知总 $D$ 的全域律或全局取向一致性，不从完整 $\mathsf H_A(D)$ 删除 A1/P2，也不删除承载卷定义 41.1 的实际外层预算桥。对通常的复 Hilbert、Born、张量、CP／Kraus、仪器更新、历史和 Hamiltonian 公理的对应，仍只按以下原完整来源合同逐项消费，不能将已有前件改名计作公理减少。

完整原来源严格合取卷首钉版父卷 [§6 式 (6.1)–(6.2)](#6-完整原问题与七项物理合同的精确身份)、[§30A.5](#30a5-准确的前件删除来源与完整目标)、本卷 §39.8，以及[有限返回续卷定义 162.1、复用命题 162.2、定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 的同一全文和全部递归钉版上游。以下解释不替换任何原对象、公式、前件或量词。同一原 $\Omega$/native、$E,C,u,N,\mathcal P,S,D,q,K/J$、全词与跨评价配对、原模式网络及所有具名绑定保持原身份；本节的局部 $\mathsf E_s$ 和矩阵 $B$ 不替代这些合同中的原响应或生成锥。

全部原准备、发生、事件、过程、ownership／parent／ready／flags、真正相关参考及副本、中央／经典／不等维／静默／无轴块、零／不等／次归一质量、同一真实乘积、同一 $\sigma,t_0$、固定支持全质量、完整菜单、全部中间切口、环境、完整活动输出与全部成功／失败／零标签细记录、port／post-port、拒绝／停止／销毁／泄漏、真分组遗忘、两侧及逆向 Return、控制／钟／单位和每份完整输出的每个旧合法未来均守原域。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不合并，未定义请求不补零；原根端点、同一 ready 的零活动支、固定域／resolvent 与 $3s+r\le1$ 预算保持原合同含义。

具体的第一未付桥梁是实际固定值 $g=D(c,t)$ 的辨识，若它尚未由原来源供应。即便此桥梁已付，(42.29) 也没有供应 §39.8 所保留的实际旧程序接受关联：[C139 固定源卷 §23.3 式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 中字面旧程序 $\tau;T_P$ 的指定接受族，仍须在全部原准备、事件、切口、参考／副本、合法分析词与树、原坐标、固定支持全质量及完整菜单上，给出到同一实际菜单事件 $k_b^\dagger P_{J_0}k_b$ 与原接受端的准备无关准确关联，保持未归一标尺、支持、类型、ready、控制、钟、互补结果、记录及合法未来；不额外将指定接受关联加强成历史双射。[Fourier 卷 §§10.3–10.4](AURIC_C139_FOURIER_OVERLAPS_AND_GLOBAL_FRAMED_BORN_RIGIDITY.md) 的原子归属和指定正校准源也按原条件独立供应，局部配方或全菜单校准相等不能代替全部原准备上的下降。

CountRead 仍须同一接受叶的完整活动输出、实际读后 active-ready、第一合法消费者，以及读后同一整份活动输入保留原参考、控制、钟并对全部旧合法未来真实 Return。有限返回定义 164.1 的查询候选与原 $B_{r_\star}$ 活动接头保持区别，整表、地址、档案或矩阵状态不生成活动发生标识与未来权限。既得 [C139 固定源卷 §§50–73、§§74–85](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md) 的合法前接、正回溯、下降、固定返回刚性、条件过程比较、递归参考、累计真支持和近似参考／容量界，以及 [C128 原词卷 §§385–392](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md) 对同一旧 $D$ 的恢复与消费者，均继续在原域计入。

七项量子消费者的准确条件继续采用 §39.8：共同全词、共同核及实际相干准备才给复 Hilbert／相干；实际事件、完整菜单、固定支持全质量及正质量绑定才给 Born 归一；同一真正相关共同联合、忠实同向交换腿及共同生成才给张量；整台 typed 箭头的合法接续、真实递归参考、全部环境／记录／失败／后口、相关正输入、真支持与累计支持运输才给 CP／Kraus；完整 typed 仪器、实际单位分区、AC、$N_u,X,X_s$、平方根词与接受端、严格正输出质量及射线／校准前件才给 TP／更新／Lüders；全部原历史、真遗忘及每个旧合法未来的实际两侧／逆向返回才给历史／Return；同一实际连续可逆流、实际逆、强连续实现、生成元域、物理钟／单位／能量及共同正 $\hbar$ 才给 Hamiltonian。

静态 EJA 候选同样保留 §39.8 的实际 canonical-trace 代数、完整锥／态／效果、比较到 Jordan 的桥、全局正性、指定 $p_{13}$ 的迹保持、未归一单位及完整实线性张成上的边缘恒等式。共同正规根态 $\omega$、全部有限及无限历史、递归参考、量子与经典选择、完整 instruments/futures、物理钟和正作用量均未由定理 42.2 生成；$\zeta,J,\omega$ 不合并。正矩阵泛函并不自动构成实际准备或物理 Born 读取，向量泛函不自动给物理纯态、全局酉演化或源的共根／可达性。三个演员及三条存活列方向均不是物理空间三维。完整原量子起源及无缺口来源的完整量子公理重建仍未由本节完成，全部原成功条件保持不变。

直观地说，原来的两张面积图在第三对角不为零时可以一起压小，再用那一格留下的读数找出残量；第三对角为零，这把尺就失灵了。这里仍用原来的五维桌面、两条环境连线和同一份输入，只将同一探针的一格按 $1/\rho^2$、一条斜边按 $1/\rho$ 放大。两张面积图都变大，但原乘法恒等式准确支付了它们共同的大项；真正额外的面积由同一对复列的内积和外积分开计算，一笔趋零，另一笔只花去 $5s^2/6$，而残量留下 $s^2$，所以仍有正差额。原第二环境列并未消失，它的每个交叉面积都留在有限系数里；明确选取一个有限正的 $\rho_*$ 就能同时压住这些低阶代价，得到两笔预算都正、质量恰为任意指定正数的原 PB 违反。这说明这个固定矩阵分支不能容纳非零残量，却不会把矩阵见证变成实际物理准备、完整菜单、真实返回或整个量子宇宙。

## 新增锚（本行以下为后续增补区）


## 43. 同一零探针的全复环境幅度与不平方下界

**定理 43.1（固定家族的相位完备充要条件）。** 准确保持定义 41.1、(41.4) 的完整四维模型、同一原 $q$、分别固定的 $\sigma$、$\iota=\sigma i$、同一实际对角残量 $E$，以及定理 41.4 的 $x=0$ 和

$$
u=(2/\overline{q_1},-1/\overline{q_2},0)^{\mathsf T},\qquad
\xi_w=(u,w),\qquad \phi_w(A)=\xi_w^*A\xi_w.
\tag{43.1}
$$

将 $w$ 的范围扩大为整个 $\mathbb C$。这个家族对全部复 $w$ 满足原 PB，当且仅当原条件 (41.16) 成立；没有比实幅度家族更强的新必要条件。结论不涉及全部演员探针的完整允许集分类。

证明。采用与 (41.15) 相同的 $m,n,b,a,d,F,G,H$，另写 $r=s_1-s_2$ 和 $V=1+4s_1^2/m+s_2^2/n$，即

$$
\begin{gathered}
b=m+4n,\quad a=m+2n,\quad d=2s_1-s_2+s_0,\\
F=bV-4r^2=b+(4\sqrt{n/m}\,s_1+\sqrt{m/n}\,s_2)^2>0,\\
G=b(m+n+b/4+s_0^2)-a^2,\qquad H=bd-2ar.
\end{gathered}
\tag{43.2}
$$

对 $w\ne0$，唯一地取 $\rho=|w|>0$ 和实数 $X,Y$ 使

$$
w=\rho(X+\iota Y),\qquad X^2+Y^2=1.
\tag{43.3}
$$

这里 $Y=\sigma\operatorname{Im}(w)/\rho$；不能把 (43.3) 改为 $\rho(X+iY)$ 而继续使用下面不含 $\sigma$ 的 $Y$ 系数。原 $q$ 的任意相位只通过 $q^*u=1$、$q^*Cu=0$、$(Cq)^*Du=2r$ 收缩，$D=\operatorname{diag}(s_1,s_2,s_3)$。没有旋转原环境或改变 $t$。

(41.17) 的完整列对复 $w$ 仍准确成立：

$$
R_\delta\xi_w=(-\delta wCq/2,0),\qquad
S_\delta\xi_w=(\delta Du+wq+\delta\iota wCq/2,\ 1+\delta s_0w).
\tag{43.4}
$$

取同一列的范数和实内积，得到

$$
\begin{aligned}
\phi_w(L)&=-2d\rho X,\\
\|R_\delta\xi_w\|^2&=b\rho^2/4,\\
\|S_\delta\xi_w\|^2
 &=V+2\delta d\rho X-2r\rho Y
       +(m+n+b/4+s_0^2)\rho^2,\\
\operatorname{Re}\langle R_\delta\xi_w,S_\delta\xi_w\rangle
 &=-r\rho X-\delta a\rho^2/2,\\
\frac{4B_{\phi_w}(R_\delta,S_\delta)}{\rho^2}
 &=F+4r^2Y^2+\rho(-2brY+2\delta HX)+G\rho^2.
\end{aligned}
\tag{43.5}
$$

例如 $\operatorname{Re}(\iota w)=-\rho Y$ 给第三行的 $-2r\rho Y$；第四行使用 $\operatorname{Re}\overline w=\rho X$。第四输出的平方 $s_0^2\rho^2$ 和交叉项 $2\delta s_0\rho X$ 都在第三行内，未压缩掉环境。最后一行由前两范数的乘积减去第四行的平方得到，仍是实 Gram 预算。

必要性直接限制到实 $w$，应用定理 41.4；若 $4d^2>F$，(41.21) 已给有限实幅度的严格双正预算见证。以下证明充分性而不对两个根式的和反复平方。直接展开 (43.2) 给

$$
\begin{aligned}
T&:=G-b^2/4=mn+bs_0^2>0,\\
FT-H^2
 &=\frac{b}{mn}(-mn+ms_2s_0+4ns_1s_0)^2\ge0.
\end{aligned}
\tag{43.6}
$$

置

$$
A=F+4r^2Y^2-2brY\rho+G\rho^2,\qquad K_0=2HX\rho.
$$

因 $X^2\le1$ 和 $H^2/F\le T$，有准确配方

$$
\begin{aligned}
A-F-\frac{K_0^2}{4F}
 &=(2rY-b\rho/2)^2
       +\rho^2\left(T-\frac{H^2X^2}{F}\right)\ge0,\\
A\pm K_0&\ge\left(\sqrt F\pm\frac{K_0}{2\sqrt F}\right)^2,\\
\sqrt{A+K_0}+\sqrt{A-K_0}
 &\ge\left|\sqrt F+\frac{K_0}{2\sqrt F}\right|
       +\left|\sqrt F-\frac{K_0}{2\sqrt F}\right|
 \ge2\sqrt F.
\end{aligned}
\tag{43.7}
$$

这些不等式包括根式为零的情况，没有假定严格正预算。原 PB 在 $\rho>0$ 时准确为

$$
4|dX|\le\sqrt{A+K_0}+\sqrt{A-K_0}.
$$

若 $4d^2\le F$，则 $4|dX|\le4|d|\le2\sqrt F$，由 (43.7) 即成立。$w=0$ 时两端均为零，不作除法。两笔预算始终使用同一 $\xi_w,x,t,g,\phi_w$，充分性没有拼接分别最小的列。这证明全复幅度的充要条件。∎

本条的 repo-derived 内容是 (43.4)–(43.7) 对定理 41.4 的相位完备扩展和同一完整列的不平方下界。正泛函 Schwarz、实 Gram 与平方配方作为成熟中间工具，沿 §41.8 的数学归属使用。该扩展不改变 (41.41) 的夹逼，不给非分级残量的全称充分模型，也不消去定理 41.5 的 $s_0^2\eta\rho^2$ 代价。原来源和七项消费者严格合取 §41.8、§39.8 的完整合同，未由这份固定零探针家族供应。相同 M4 原始探针的正映射运输问题见[原始标定与共同源运输续卷 §44](AURIC_FULL_PB_RAW_CALIBRATION_AND_COMMON_SOURCE_TRANSPORT_CONTINUATION.md)。§42 是另一份 M5 秩二原环境模型，不用于本条或该 M4 标定。

## 新增锚（本行以下为后续增补区）
