# AURIC：复合比较的同尺度乘积序稳定性续篇（V96）

本卷承接 [AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md)。外部定义、假设与编号（特别是定义 8.1–8.4）按 V96 原卷解释；本续篇使用 `Q97.*` 作为内部定义、命题与公式编号。


## Q97. 有限原始报告在同一内积和内生标尺上的定量修复

**定义 Q97.1（原比较乘法的完整平方锥）。** 在定义 8.1 的实空间上记 $e=1$、$\|x\|=g(x,x)^{1/2}$，对任意双线性映射 $F$ 记

$$
\|F\|_{\rm bil}=\sup_{\|x\|=\|y\|=1}\|F(x,y)\|.
$$

三线性映射的范数同样在三个单位输入上取上确界。对交换含幺正 Frobenius 乘法 $S$，定义

$$
\begin{aligned}
\mathcal C_S&=\overline{\operatorname{cone}\{S(x,x):x\in J\}},\\
E_S&=\mathcal C_S\cap(e-\mathcal C_S),\\
\Omega_S&=\{u\in J:g(u,e)=1,\ g(u,x)\ge0\text{ 对全部 }x\in\mathcal C_S\}.
\end{aligned}\tag{Q97.1}
$$

闭包、对偶及 Hausdorff 距离 $d_H$ 均取原来的 $g$；$d_H$ 初始允许值为 $+\infty$。这些集合使用全部平方，不限制到定义 8.3 的探针，也不预设为矩阵正锥。

**定理 Q97.2（原始有限报告的同单位、同内积、同标尺修复）。** 对每个整数 $N\ge4$、实数 $K\ge1$ 和 $0<\kappa\le1$，存在只依赖 $(N,K,\kappa)$ 的 $C_{\rm event}>0$、$\eta_0>0$，满足以下结论。设两个定义 8.1 的场 $J_A,J_B$ 满足

$$
4\le\dim J_A,\dim J_B\le N,\qquad
\|e_J\|=1,\qquad
\|S_J\|_{\rm bil},\|B_J\|_{\rm bil}\le K.
$$

在任意完整正交单位基中取定义 8.3 的全部带标签探针。每方的原参照对 $(b_J,d_J)$ 满足

$$
\|b_J\|,\|d_J\|\le1,\qquad
\|B_J(b_J,d_J)\|\ge\kappa.
$$

令 $\lambda_*,\Gamma$ 恰为定义 8.4 的内生读数，并假设

$$
\lambda:=\lambda_*\in[\kappa,K],\qquad
\eta:=\Gamma^{1/4}\le\eta_0.
$$

则每方在同一个实空间、同一个内积 $g_J$ 和同一个单位 $e_J$ 上存在乘法 $\widetilde S_J,\widetilde B_J$，满足定义 8.1，且

$$
\|\widetilde B_J(b_J,d_J)\|\ge\kappa/2.
\tag{Q97.2}
$$

以这两个修复场形成定义 8.2 的同一模板，有

$$
\widetilde R_{\lambda_*}(H,X,Y)=0
\quad\text{对全部 }H,X,Y\in J_A\otimes_{\mathbb R}J_B,
\tag{Q97.3}
$$

以及

$$
\boxed{\max_{J\in\{J_A,J_B\}}\left(
\|S_J-\widetilde S_J\|_{\rm bil}
+\sqrt{\lambda_*}\|B_J-\widetilde B_J\|_{\rm bil}
+d_H(E_{S_J},E_{\widetilde S_J})
+d_H(\Omega_{S_J},\Omega_{\widetilde S_J})
\right)\le C_{\rm event}\Gamma^{1/4}.}
\tag{Q97.4}
$$

式 (Q97.4) 中每方涉及的四个集合均非空紧致。修复不改变观测到的 $\lambda_*$，不改变参照输入，也不要求原场满足 Jordan、交替或 Jacobi 恒等式。

常数可如下选择。取普适常数 $a\ge1$、$0<\varepsilon_*\le1$，使 Alexei Kitaev 的 [*Almost-idempotent quantum channels and approximate C*-algebras*, arXiv:2405.02434v2，§2 定义 2.1–2.2、定理 2.3](https://arxiv.org/html/2405.02434v2#S2) 及定义 2.2 后的逆映射结论，对每个 $\varepsilon\le\varepsilon_*$ 给出从某个有限维真正 $C^*$ 代数到任意有限维 $\varepsilon$-$C^*$ 代数的双射 $a\varepsilon$-同构。该同构严格保持对合，单位、乘法和范数的误差按该定义理解。这里只使用这两个普适常数的存在性，不指定其数值。令

$$
\begin{aligned}
U&=\frac{8N}{\kappa},&
G&=\frac{33N^{5/2}K^3}{\kappa^2},\\
V&=3(4G+6K^{3/2}U),&
M&=2\bigl(K+\sqrt K(K+1)\bigr),\\
A&=10000aM^6,&
\delta_0&=\min\{\varepsilon_*/M,1/A\},\\
L&=K+1,&
\eta_0&=\min\left\{1,\frac{\kappa}{8N},\frac{\delta_0}{V},
\frac{\kappa}{2(U+AV/\sqrt\kappa)}\right\},\\
C_{\rm event}&=(5L^2+3L+3)AV+\sqrt K\,U.
\end{aligned}\tag{Q97.5}
$$

证明。以下全部范数都保持原来的内积；复化时使用它的标准复 Hilbert 范数。先由实际有限报告构造满足外部稳定性定理前件的乘法，再恢复原单位和原内积，最后比较 (Q97.1) 的完整集合。

### Q97.1 原导子的斜伴随性和有限自守报告

定义 8.1 所用的有限正 Frobenius 导子论证可具体写成如下形式。若 $d\in\operatorname{Der}(S)$，则 $de=0$、$[d,L_a]=L_{da}$。由于 $L_a$ 自伴，取伴随给 $[d^\dagger,L_a]=-L_{da}$，所以 $H=d+d^\dagger$ 与全部 $L_a$ 对易。$H$ 的每个本征空间 $J_j$ 因而是 $S$-理想。不同本征空间的乘积同时落在两个空间中，故为零。将 $e$ 正交分解为 $\sum_j e_j$，则 $e_j$ 是 $J_j$ 的单位，且 $L_{e_j}$ 是到 $J_j$ 的正交投影 $P_j$。导子作用于 $S(e_j,e_j)=e_j$ 给

$$
de_j=2P_jde_j.
$$

投影的本征值只有 $0,1$，故 $de_j=0$。若 $H|_{J_j}=h_j I$，则

$$
h_j\|e_j\|^2=g(He_j,e_j)=2g(de_j,e_j)=0.
$$

每个非零 $J_j$ 的单位 $e_j$ 非零，所以 $H=0$。这正是定义 8.1 引用的 V95 定理 2.1 的导子结论；此处对原来的每个 $D_a$ 使用它，不另添度量不变性假设。

置 $\rho=\Gamma^{1/2}=\eta^2$。定义 8.4 的 $\Gamma$ 是带标签报告的未平均平方和，所以每条报告的范数都不超过 $\rho$。固定一方及另一方的原参照，记 $v=B_{\rm opp}(b,d)$。式 (9.4) 在每个定义 8.3 的自身探针上给

$$
R_\lambda(p\otimes d,p\otimes b,p\otimes e)
=\lambda D_p^2p\otimes v.
$$

由 $\lambda\ge\kappa$、$\|v\|\ge\kappa$ 以及 $D_p^\dagger=-D_p$ 得

$$
\|D_p^2p\|\le\frac{\eta^2}{\kappa^2},\qquad
\|B(p,p)\|^2=-g(p,D_p^2p)\le\frac{\eta^2}{\kappa^2}.
\tag{Q97.6}
$$

这里 $p$ 是单位向量。此平方根机制是定理 10.1 的应用；下面保留完整基和两两和的系数损失。记 $\alpha=\eta/\kappa$、$H_B(x,y)=B(x,y)+B(y,x)$。基向量给 $\|H_B(e_i,e_i)\|\le2\alpha$，而

$$
H_B(e_i,e_j)=2B\left(\frac{e_i+e_j}{\sqrt2},\frac{e_i+e_j}{\sqrt2}\right)
-B(e_i,e_i)-B(e_j,e_j)
$$

给 $i\ne j$ 时 $\|H_B(e_i,e_j)\|\le4\alpha$。对任意单位 $x,y$ 展开基系数，得到

$$
\|H_B(x,y)\|\le4\alpha\|x\|_1\|y\|_1
\le\frac{4N\eta}{\kappa}=:\sigma.
\tag{Q97.7}
$$

特别地，原单位律只先给 $B(x,e)=0$，再由 (Q97.7) 才得到 $\|B(e,x)\|\le\sigma\|x\|$。以上论证对两方分别完成，因此也控制反序参照。

### Q97.2 单位消去的交替三形式及其误差

令 $t(x,y,z)=g(B(x,y),z)$。斜伴随性使它在末两槽反对称。定义

$$
\phi(x,y,z)=\frac{t(x,y,z)+t(y,z,x)+t(z,x,y)}3,\qquad
P_e x=x-g(e,x)e,
$$

并用 Riesz 对应定义 $C$：

$$
g(C(x,y),z)=\phi(P_ex,P_ey,P_ez).
\tag{Q97.8}
$$

逐槽交换表明 $\phi$ 为交替三形式。又有

$$
\begin{aligned}
t(x,y,z)-t(y,z,x)&=g(H_B(x,y),z),\\
t(x,y,z)-t(z,x,y)&=-g(H_B(x,z),y).
\end{aligned}
$$

因此单位三元组上 $|t-\phi|\le2\sigma/3$。由 $B(x,e)=0$ 及斜伴随性，$\phi(e,x,y)=t(e,x,y)/3$，其范数不超过 $\sigma/3$。展开三个 $P_e$ 时，含两个 $e$ 的项都因交替性为零，至多剩三个各不超过 $\sigma/3$ 的项。所以

$$
h:=\|C-B\|_{\rm bil}\le\frac{5\sigma}3\le2\sigma=U\eta.
\tag{Q97.9}
$$

$C$ 严格交替，$C(e,x)=C(x,e)=0$，且 $C_x:y\mapsto C(x,y)$ 斜伴随。由 $\eta\le\kappa/(8N)$，$h\le1$，故 $\|C\|_{\rm bil}\le K+1$。$S$ 此时保持原样。必须另算投影后的导子误差：令

$$
F_C(x;y,z)=C(x,S(y,z))-S(C(x,y),z)-S(y,C(x,z)).
$$

减去原来 $B$ 的严格导子恒等式，三个差项各不超过 $Kh$，从而

$$
\|F_C\|_{\rm tri}\le3Kh\le3KU\eta.
\tag{Q97.10}
$$

### Q97.3 混合报告、反序参照和全输入曲率

仍固定一方，另一方原参照记为 $(r,s)$，令

$$
v=B_{\rm opp}(r,s),\qquad w=B_{\rm opp}(s,r).
$$

由 (Q97.7)，$\|v\|\ge\kappa$、$\|w+v\|\le\sigma$。取原混合探针的实际顺序

$$
(H,X,Y)=(a\otimes r,c\otimes s,b\otimes e),\qquad
(a,b,c)=(e_i,e_j,e_k),\quad i<j.
$$

设 $z=B(a,b)$。式 (9.3) 是尚未交替时的恒等式，给

$$
R=[L_a,L_b]c\otimes v+\lambda B(c,z)\otimes w.
$$

令 $E_B(a,b)c=[L_a,L_b]c+\lambda B(B(a,b),c)$，则严格地

$$
E_B(a,b)c\otimes v
=R+\lambda H_B(c,z)\otimes v
-\lambda B(c,z)\otimes(w+v).
\tag{Q97.11}
$$

这同时保留本方对称缺陷和另一方反序参照缺陷。除以 $\|v\|$，利用 $\|z\|\le K$ 得

$$
\|E_B(e_i,e_j)e_k\|\le\frac{\eta^2}{\kappa}
+K^2\sigma+\frac{K^3\sigma}{\kappa}.
$$

现在才改用

$$
E(a,b)c=[L_a,L_b]c+\lambda C(C(a,b),c).
$$

嵌套括号的替换误差至多 $\lambda h(2K+1)\le K(2K+1)h$，故

$$
\begin{aligned}
\|E(e_i,e_j)e_k\|&\le q_0,\\
q_0&:=\frac{\eta^2}{\kappa}
+\left(5K^2+2K+\frac{K^3}{\kappa}\right)\sigma
\le\frac{33NK^3}{\kappa^2}\eta.
\end{aligned}\tag{Q97.12}
$$

末步使用 $\eta\le1$、$K\ge1$、$\kappa\le1$。投影后的 $E$ 在前两槽严格交替。对单位 $a,b,c$，展开完整基给

$$
\|E(a,b)c\|\le q_0\left(\sum_{i<j}|a_ib_j-a_jb_i|\right)
\left(\sum_k|c_k|\right).
$$

外积恒等式 $\sum_{i<j}(a_ib_j-a_jb_i)^2\le1$ 及 Cauchy–Schwarz 不等式分别将括号控制为 $\sqrt{n(n-1)/2}$、$\sqrt n$。所以

$$
\|E\|_{\rm tri}\le N^{3/2}q_0\le G\eta.
\tag{Q97.13}
$$

无须基包含单位，也无须增加探针。

### Q97.4 Jacobi 误差和复乘法的全部前件

交换性直接消去循环和中的六项，得到

$$
[L_a,L_b]c+[L_b,L_c]a+[L_c,L_a]b=0.
$$

定义 $J_C(a,b,c)=C(C(a,b),c)+C(C(b,c),a)+C(C(c,a),b)$。循环求和 (Q97.13) 给

$$
\lambda\|J_C\|_{\rm tri}\le3G\eta.
$$

对交替 $C$，逐项展开又有

$$
[C_a,C_b]c-C_{C(a,b)}c=-J_C(a,b,c),\qquad
\|[L_a,L_b]+\lambda[C_a,C_b]\|_{\rm op}\le4G\eta
\tag{Q97.14}
$$

对单位 $a,b$ 成立。因此没有在取得 Jacobi 界以前用 $[C_a,C_b]=C_{C(a,b)}$。

在原复化 $H=J\otimes_{\mathbb R}\mathbb C$ 上取共轭 $x\mapsto x^*$、原 Hilbert 内积（第一槽共轭线性），并定义复双线性乘法

$$
\mu(a,b)=S(a,b)-i\sqrt\lambda C(a,b).
\tag{Q97.15}
$$

它的单位严格为 $e$，且 $\mu(x,y)^*=\mu(y^*,x^*)$。实 $a$ 的 $S_a$ 自伴、$C_a$ 斜伴随，所以 $L_a^\mu=S_a-i\sqrt\lambda C_a$ 自伴；复线性扩展即给

$$
(L_x^\mu)^\dagger=L_{x^*}^\mu.
\tag{Q97.16}
$$

两次展开 (Q97.15)，以 $S$-结合缺陷 $-[L_a,L_c]b$ 合并实部，以 (Q97.10) 合并虚部，得到对实输入的严格恒等式

$$
\begin{aligned}
\mathcal A_\mu(a,b,c)
&:=\mu(\mu(a,b),c)-\mu(a,\mu(b,c))\\
&=-E(a,c)b-\lambda J_C(a,b,c)
+i\sqrt\lambda\bigl(F_C(a;b,c)+F_C(c;a,b)\bigr).
\end{aligned}\tag{Q97.17}
$$

实单位三元组上的范数至多 $(4G+6K^{3/2}U)\eta$。若 $x=a+ib$，则 $\|a\|+\|b\|\le\sqrt2\|x\|$；三个输入的复展开至多损失 $2\sqrt2<3$，两个输入至多损失 $2$。由此

$$
\|\mathcal A_\mu\|_{{\rm tri},H}\le V\eta,\qquad
\|\mu\|_{{\rm bil},H}\le2\bigl(K+\sqrt K(K+1)\bigr)=M.
\tag{Q97.18}
$$

### Q97.5 在正确范数中应用有限维稳定性

在本证明内部，先对任意满足 (Q97.15)–(Q97.16) 的有限维乘法说明修复步骤。设 $\|\mu\|_{{\rm bil},H}\le M$、$\|\mathcal A_\mu\|_{{\rm tri},H}\le\delta\le\delta_0$，且单位 $e$ 的范数为一。定义

$$
p(x)=\|L_x^\mu\|_{\rm op}.
$$

由于 $L_x^\mu e=x$，有

$$
\|x\|\le p(x)\le M\|x\|,\qquad p(e)=1,\qquad p(x^*)=p(x).
\tag{Q97.19}
$$

所以 $p$ 是完备范数。结合缺陷给

$$
\|L_{\mu(x,y)}^\mu-L_x^\mu L_y^\mu\|_{\rm op}
\le\delta\|x\|\|y\|.
$$

由此及 (Q97.16) 得到全部复输入上的三个估计

$$
\begin{aligned}
p(\mu(x,y))&\le(1+\delta)p(x)p(y),\\
p(\mathcal A_\mu(x,y,z))&\le M\delta\,p(x)p(y)p(z),\\
p(\mu(x^*,x))&\ge\|(L_x^\mu)^\dagger L_x^\mu\|_{\rm op}
-\delta\|x\|^2\ge(1-\delta)p(x)^2.
\end{aligned}\tag{Q97.20}
$$

取 $\varepsilon=M\delta$。式 (Q97.20) 分别验证 Kitaev 定义 2.1 的 (2.1)、(2.2)、(2.5)；(Q97.19)、对合反乘法和原来的严格单位分别验证其 (2.4)、(2.7)。因此 $(H,p,\mu,*)$ 是该文意义下的有限维 $\varepsilon$-$C^*$ 代数。这里需要的是 $p$ 范数中的前件，不能直接把原 Hilbert 范数当作 $C^*$ 范数。

当 $\delta>0$ 时，由 $\varepsilon\le\varepsilon_*$ 和所引用的定理 2.3，取真正的有限维 $C^*$ 代数 $F$ 及双射复线性映射 $v:F\to H$，严格交织对合，且令 $d=aM\delta$ 后有

$$
\begin{aligned}
p(v(1)-e)&\le d,\\
p(v(ab)-\mu(v(a),v(b)))&\le d\|a\|_F\|b\|_F,\\
(1-d)\|a\|_F&\le p(v(a))\le(1+d)\|a\|_F.
\end{aligned}\tag{Q97.21}
$$

这些正是定义 2.2 的 (2.8)–(2.10) 和严格 $*$ 条件；从定理陈述的同构方向转到这里的方向只使用其后的逆映射结论，并已吸收到普适 $a,\varepsilon_*$ 中。外部依赖到此为止：它提供范数近似同构，不直接提供原单位和原 Hilbert 内积中的修复。

### Q97.6 严格单位、忠实正泛函和邻近迹

在 $F$ 上取任意状态 $f$，置

$$
r=e-v(1),\qquad w(a)=v(a)+f(a)r.
$$

$r$ 自伴，故 $w$ 严格 $*$ 线性且 $w(1)=e$。由 $\|f\|=1$ 得

$$
p(w(a)-v(a))\le d\|a\|_F,\qquad
(1-2d)\|a\|_F\le p(w(a))\le(1+2d)\|a\|_F.
\tag{Q97.22}
$$

$d\le1/8$ 时 $w$ 单射；源和目标维数相同，所以它为双射。将 $w=v+fr$ 的两个乘法因子展开，再用 (Q97.21) 和 $p(\mu(x,y))\le(1+\varepsilon)p(x)p(y)$，给

$$
\begin{aligned}
p(\mu(w(a),w(b))-w(ab))
&\le\bigl[2d+2(1+\varepsilon)(1+d)d+(1+\varepsilon)d^2\bigr]
\|a\|_F\|b\|_F\\
&\le8d\|a\|_F\|b\|_F
\end{aligned}\tag{Q97.23}
$$

当 $\varepsilon\le1$、$d\le1/8$。其中 $2d$ 分别来自 $v$ 的乘法误差和 $f(ab)r$；两个交叉项及二次项给其余三项。

拉回真正的乘法，记

$$
\nu(x,y)=w\bigl(w^{-1}(x)w^{-1}(y)\bigr),\qquad
n(x)=\|w^{-1}(x)\|_F.
$$

$\nu$ 严格结合，单位为 $e$，对合仍为原共轭，而 $n$ 是其 $C^*$ 范数。注意 (Q97.22) 是

$$
(1-2d)n(x)\le p(x)\le(1+2d)n(x).
$$

将 (Q97.23) 的输入改成 $w^{-1}(x),w^{-1}(y)$，再用 (Q97.19)，得到原 Hilbert 双线性范数中的估计

$$
\|\nu-\mu\|_{{\rm bil},H}
\le\frac{8dM^2}{(1-2d)^2}\le16M^2d=:q
=16aM^3\delta.
\tag{Q97.24}
$$

特别地 $\|\nu\|_{{\rm bil},H}\le M+q$。每个 $\nu$-酉元 $u$ 满足 $n(u)=1$，故 $\|u\|\le p(u)\le1+2d$。

令 $\tau(x)=\langle e,x\rangle$。由 (Q97.16) 及原单位，

$$
\tau(\mu(x^*,y))=\langle x,y\rangle,\qquad
\tau(\mu(x,y))=\tau(\mu(y,x)).
$$

第二式也可由 $\tau(\mu(x,y))=\langle x^*,y\rangle$ 的对称复双线性直接得到。因而

$$
\begin{aligned}
|\tau(\nu(x,y)-\nu(y,x))|&\le2q\|x\|\|y\|,\\
\tau(\nu(x^*,x))&\ge(1-q)\|x\|^2.
\end{aligned}\tag{Q97.25}
$$

$q<1$ 时，$\tau$ 是真正 $C^*$ 代数 $(H,\nu,*)$ 上忠实正的含幺泛函。此后才使用该真正代数的紧酉群 $\mathcal U$ 及其归一 Haar 测度，定义

$$
t(x)=\int_{\mathcal U}\tau\bigl(\nu(u^*,\nu(x,u))\bigr)\,du.
\tag{Q97.26}
$$

每个被积泛函忠实正且含幺，所以 $t$ 也如此。Haar 不变性使 $t$ 对酉共轭不变；对自伴 $a$ 的 $\exp(isa)$ 在 $s=0$ 求导给 $t(ax-xa)=0$，再复线性扩展 $a$，得到 $t$ 为迹。这里的指数和乘积全部在已经结合的 $\nu$ 中。

为量化 $t-\tau$，在 (Q97.25) 中取 $u^*$ 和 $\nu(x,u)$；结合性及 $\nu(u,u^*)=e$ 给

$$
\nu(\nu(x,u),u^*)=x.
$$

于是

$$
\|t-\tau\|_{H^*}
\le2q(M+q)(1+2d)^2\le8Mq
\tag{Q97.27}
$$

当 $q\le1$、$d\le1/8$。这一步只在真正代数上平均，不对原来的非结合乘法假设酉群结构。

### Q97.7 恢复同一个原 Hilbert 内积

迹给正定 Hermitian 形式

$$
h(x,y)=t(\nu(x^*,y)),\qquad h(e,e)=1.
$$

由 (Q97.24)、(Q97.27)，它与原内积之差在单位二元组上至多

$$
q+8Mq(M+q)\le17M^2q=:r_0.
\tag{Q97.28}
$$

令 $h(x,y)=\langle x,H_0y\rangle$，则 $H_0>0$、$\|H_0-I\|\le r_0$。迹性给 $h(x^*,y^*)=h(y,x)$，故 $H_0$ 与原共轭对易。$z=H_0^{1/2}e$ 是实单位向量，因为 $\|z\|^2=h(e,e)=1$。在 $e,z$ 的实平面内取正交旋转 $Qe=z$，在正交补取恒等；$z=e$ 时直接取 $Q=I$。由于二者接近，

$$
\|Q-I\|=\|z-e\|\le r_0.
$$

置

$$
T=H_0^{-1/2}Q.
\tag{Q97.29}
$$

则 $Te=e$，$T$ 与共轭对易，且 $h(Tx,Ty)=\langle x,y\rangle$。当 $r_0\le1/16$ 时，在谱区间 $[1-r_0,1+r_0]$ 上使用平方根和逆平方根的标量估计，有

$$
\begin{gathered}
\|H_0^{1/2}-I\|,\|H_0^{-1/2}-I\|\le r_0,\\
\|T-I\|\le3r_0,\qquad \|T^{-1}-I\|\le2r_0,
\qquad \|T\|,\|T^{-1}\|\le2.
\end{gathered}\tag{Q97.30}
$$

定义

$$
\widehat\nu(x,y)=T^{-1}\nu(Tx,Ty).
\tag{Q97.31}
$$

它仍严格结合，单位仍为 $e$，对合仍为原共轭。迹形式满足

$$
h(\nu(a,x),y)=h(x,\nu(a^*,y)),
$$

故经 (Q97.29) 的等距运输后，在原来的内积中严格成立

$$
(L_x^{\widehat\nu})^\dagger=L_{x^*}^{\widehat\nu}.
\tag{Q97.32}
$$

为保留运输常数，将 (Q97.31) 与 $\nu(x,y)$ 相减，分为 $T^{-1}-I$ 的项和两个输入变化项。(Q97.30) 给

$$
\begin{aligned}
\|\widehat\nu-\nu\|_{{\rm bil},H}
&\le(M+q)\bigl(2r_0\cdot4+3r_0\cdot2+3r_0\bigr)\\
&=17(M+q)r_0\le34Mr_0.
\end{aligned}
$$

合并 (Q97.24)、(Q97.28)，得到

$$
\|\widehat\nu-\mu\|_{{\rm bil},H}
\le q+34Mr_0\le579M^3q
\le9264aM^6\delta\le A\delta.
\tag{Q97.33}
$$

所有使用的小量条件均由 (Q97.5) 保证。具体地，$\delta\le1/A$ 给

$$
d\le\frac1{10000M^5},\qquad
q\le\frac{16}{10000M^3},\qquad
r_0\le\frac{272}{10000M}<\frac1{16},
$$

从而 $d\le1/8$、$q<1$；而 $\delta\le\varepsilon_*/M$ 给 $\varepsilon\le\varepsilon_*\le1$。当 $\delta=0$ 时，原 $\mu$ 已严格结合，直接取 $\widehat\nu=\mu$ 即可。由 (Q97.32)，$\widehat\nu$ 的原 Hilbert 左正则表示为严格 $*$ 表示，且单位保证其忠实性。

### Q97.8 原参照的活动性和同一标尺的全输入结论

在两方分别以 $\delta=V\eta\le\delta_0$ 应用上述构造，记 $R=AV\eta$。对实 $a,b$ 定义

$$
\widetilde S(a,b)=\frac{\widehat\nu(a,b)+\widehat\nu(b,a)}2,\qquad
\widetilde B(a,b)=\frac{i}{2\sqrt\lambda}
\bigl(\widehat\nu(a,b)-\widehat\nu(b,a)\bigr).
\tag{Q97.34}
$$

对合反乘法使这两个值仍在原实空间 $J$ 中。结合性使 $\widetilde B$ 交替、满足 Jacobi，且每个 $\widetilde B_a$ 是 $\widetilde S$ 的导子；单位为原来的 $e$。由 (Q97.32) 对实向量取内积的实部，$\widetilde S_a$ 自伴；取虚部，$\widetilde B_a$ 斜伴随。因此是原 $g$ 上的正 Frobenius 比较场。

由 (Q97.15)、(Q97.33) 的对称部分和反对称部分分别得到

$$
\|S-\widetilde S\|_{\rm bil}\le R,\qquad
\sqrt\lambda\|C-\widetilde B\|_{\rm bil}\le R.
$$

连同 (Q97.9)，有

$$
\begin{aligned}
\|S-\widetilde S\|_{\rm bil}
+\sqrt\lambda\|B-\widetilde B\|_{\rm bil}
&\le2R+\sqrt K\,U\eta,\\
\|B-\widetilde B\|_{\rm bil}
&\le(U+AV/\sqrt\kappa)\eta\le\kappa/2.
\end{aligned}\tag{Q97.35}
$$

把第二式用于原来的 $(b_J,d_J)$ 即给 (Q97.2)，所以修复后的 $D$ 非零，定义 8.1 的非零条件也满足。此外 $R\le A\delta_0\le1$，故 $\|\widetilde S\|_{\rm bil}\le K+1=L$。

在原复张量空间上，$\widehat\nu_A\otimes\widehat\nu_B$ 严格结合，且其乘法展开恰为

$$
\widehat\nu_A\otimes\widehat\nu_B
=\widetilde M_\lambda-i\sqrt\lambda\,\widetilde T,
$$

其中 $\widetilde M_\lambda,\widetilde T$ 正是定义 8.2 用 (Q97.34) 形成的模板。前者是对称部分，后者是 $i/(2\sqrt\lambda)$ 乘以交换子。结合代数中 $[H,XY]=[H,X]Y+X[H,Y]$；对 $XY+YX$ 求和并除以二，便给交换子作用于对称乘法的导子恒等式。这是全部张量输入的恒等式，因此推出 (Q97.3)，包括非简单张量。此处始终是原始定义 8.4 的同一个 $\lambda=\lambda_*$。

### Q97.9 完整平方锥的状态和效果估计

为完成 (Q97.4)，在本证明中比较同一 $(J,g,e)$ 上任意两个交换含幺正 Frobenius 乘法 $S,S'$，其中 $\|e\|=1$、$\|S\|_{\rm bil},\|S'\|_{\rm bil}\le L$，记 $\Delta=\|S-S'\|_{\rm bil}$。以下证明不要求 Jordan 恒等式。

仍记 $\tau(x)=g(e,x)$。Frobenius 恒等式和单位给

$$
\tau(S(a,a))=\|a\|^2.
$$

所以每个有限平方锥组合 $x$ 满足 $\|x\|\le L\tau(x)$，而归一截面恰为

$$
\mathcal C_S\cap\{\tau=1\}
=\operatorname{conv}\{S(a,a):\|a\|=1\}.
\tag{Q97.36}
$$

右边是有限维紧集的凸包，故紧致，且全部元素的范数不超过 $L$。为验证闭包不改变此描述，若有限锥组合 $x_m$ 收敛，则其平方组合的总归一系数为 $\tau(x_m)$，有界。若极限的 $\tau$ 为零，范数不等式使极限为零；否则除以 $\tau(x_m)$ 后用右边的紧致性，再乘回极限系数即可。故全锥都满足

$$
\|x\|\le L\tau(x)\quad(x\in\mathcal C_S).
\tag{Q97.37}
$$

并且 $e=S(e,e)\in\mathcal C_S$，$g(e,S(a,a))=\|a\|^2\ge0$，所以 $e\in\mathcal C_S^*$。

对任意 $u$，Frobenius 性给 $g(u,S(a,a))=g(L_ua,a)$，故

$$
u\in\mathcal C_S^*\quad\Longleftrightarrow\quad L_u\ge0.
\tag{Q97.38}
$$

若 $u\in\mathcal C_S^*$ 且 $\tau(u)=0$，则 $g(e,L_ue)=0$。正半定性使 $L_ue=0$，而 $L_ue=u$，故 $u=0$。所以每个非零对偶元素都能按 $\tau$ 归一成 $\Omega_S$ 中的元素。

若 $u\in\Omega_S$、$\|w\|=1$，则全部实 $s$ 上有

$$
0\le g(u,S(e+sw,e+sw))
=1+2s\,g(u,w)+s^2g(u,S(w,w)).
$$

二次式的非负性给 $g(u,w)^2\le g(u,S(w,w))\le L\|u\|$。取 $w=u/\|u\|$ 得 $\|u\|\le L$。$\Omega_S$ 闭且包含 $e$，所以非空紧致。由闭凸锥的双极定理，每个 $\|v\|\le1/L$ 满足

$$
g(u,e+v)\ge1-L\|v\|\ge0\quad(u\in\Omega_S),
$$

因而

$$
\overline B(e,1/L)\subset\mathcal C_S.
\tag{Q97.39}
$$

同样的论证适用于 $S'$。

现在取 $u\in\Omega_S$。由 (Q97.38)，$L_u\ge0$，而 $\|L'_u-L_u\|\le\Delta\|u\|\le L\Delta$，所以 $L'_u+L\Delta I\ge0$。由于 $S'$ 的单位同样为 $e$，

$$
u'=\frac{u+L\Delta e}{1+L\Delta}\in\Omega_{S'},\qquad
\|u'-u\|\le L(L+1)\Delta.
$$

交换 $S,S'$ 即控制另一方向，因此

$$
d_H(\Omega_S,\Omega_{S'})\le L(L+1)\Delta.
\tag{Q97.40}
$$

效果需要同时保持 $x$ 和 $e-x$ 的正性。取 $x\in E_S$，则 $\alpha=\tau(x)\in[0,1]$，且由 (Q97.37) 有 $\|x\|\le L$。用 (Q97.36) 将 $x$ 和 $e-x$ 各写成单位向量平方的有限凸组合，分别带总系数 $\alpha$、$1-\alpha$。保持同一向量和系数，只将 $S$ 换为 $S'$，得到 $x_0,y_0\in\mathcal C_{S'}$，满足

$$
\begin{gathered}
\tau(x_0)=\alpha,\quad\tau(y_0)=1-\alpha,\\
\|x_0-x\|\le\alpha\Delta\le\Delta,\qquad
\|y_0-(e-x)\|\le(1-\alpha)\Delta\le\Delta.
\end{gathered}
$$

当总系数为零时取相应元素为零。置

$$
r=e-x_0-y_0,\qquad \|r\|\le2\Delta,\qquad t=2L\Delta.
$$

$\Delta>0$ 时，(Q97.39) 给 $r+te\in\mathcal C_{S'}$。于是

$$
x'=\frac{x_0+te}{1+2t},\qquad
e-x'=\frac{y_0+r+te}{1+2t}
$$

都在 $\mathcal C_{S'}$ 中，故 $x'\in E_{S'}$，且

$$
\|x'-x\|\le\frac{\Delta+t(1+2L)}{1+2t}
\le[1+2L(1+2L)]\Delta.
$$

$\Delta=0$ 时直接取 $x'=x$。交换两乘法给另一方向。因此

$$
d_H(E_S,E_{S'})\le[1+2L(1+2L)]\Delta.
\tag{Q97.41}
$$

效果集闭，(Q97.37) 将其范数控制为 $L$，且它包含 $0,e$，所以也非空紧致。这证明了两个完整集合的估计；既未把平方锥换成矩阵正锥，也未只比较有限探针的极性条件。

### Q97.10 合并常数及适用对象

对每方取 $S'=\widetilde S$、$\Delta\le R=AV\eta$，并用 $L=K+1$。将 (Q97.40)–(Q97.41) 加到 (Q97.35)，四项总和至多

$$
\begin{aligned}
&\bigl[2+L(L+1)+1+2L(1+2L)\bigr]AV\eta+\sqrt K\,U\eta\\
&\hspace{1cm}=\bigl[(5L^2+3L+3)AV+\sqrt K\,U\bigr]\eta
=C_{\rm event}\Gamma^{1/4}.
\end{aligned}
$$

再取两方的最大值即得 (Q97.4)。全部常数只使用 $(N,K,\kappa)$ 和所引稳定性定理的普适常数，因而对基、参照和条件范围内的原场一致。

本定理的实际输入是定义 8.1–8.4 的原场、带标签报告及其明确的张量模板；其输出是同一载体上这些模板的精确修复。定义 20.1、27.1、33.1 所涉及的另给实际延伸，若要取得相应定量结论，还须证明该实际延伸与这里模板之间的误差关系。式 (Q97.4) 本身不给出这项关系。这里的四次根是所证统一上界，不包含最优指数的断言。∎

## 追加锚（本行以下为增补区）
