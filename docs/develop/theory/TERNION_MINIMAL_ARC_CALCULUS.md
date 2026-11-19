# 三维球面上的最小弧演算：平移、离散作用与三角形和乐

> **本卷的机器契约。** 消化器 `generic-v1`；地址只由本文件字节算出。本卷只增不减：卷首与既有各章合入后不再改写，修订、勘误与增补写在文末追加锚之后的新章里。

## 1. 定位与状态

**参考输入。** 本卷是 trureturing 的参考输入，Lean 形式化才是唯一真源；不得把形式化工件反向绑定到本卷的章节号或定理号上。

**证明状态。** 本卷给出 ZFC 内的普通数学证明，未经 Lean kernel 验证；哪条已被形式化，以冻结账本为准。

**范围。** 本卷只处理单位四元数球面 $S^3$ 上固定的标准三元运算与比较核。由三元运算与比较核的公理推出 $S^3$ 的分类不在本卷范围内，相关工作见 [issue #31739](https://github.com/the-omega-institute/trureturing/issues/31739)。

## 2. 记号与约定

**约定 2.1（四元数与球面）。** $\mathbb H$ 取欧氏内积 $\langle x,y\rangle=\operatorname{Re}(\bar x y)$；$\operatorname{Im}\mathbb H\cong\mathbb R^3$ 带叉积 $\times$，于是对 $\xi,\eta\in\operatorname{Im}\mathbb H$ 有 $\xi\eta=-\langle\xi,\eta\rangle+\xi\times\eta$。令 $M=S^3=\{x\in\mathbb H:|x|=1\}$，三元运算 $[x,y,z]=x\bar y z$，相关 $c(x,y)=\langle x,y\rangle$，球面距离 $d(x,y)=\arccos c(x,y)\in[0,\pi]$，比较核 $\kappa(x,y)=\tfrac12(1+c(x,y))=\cos^2(d(x,y)/2)=\bigl|\tfrac12(x+y)\bigr|^2$。对 $\xi\in\operatorname{Im}\mathbb H$，$\exp\xi=\cos|\xi|+\sin|\xi|\,\xi/|\xi|$。

**约定 2.2（反射、矢高与右平凡化）。** $x$ 处的反射为 $s_x(w)=[x,w,x]=x\bar w x$。由 $x\bar w+w\bar x=2\langle x,w\rangle$ 右乘 $x$ 得 $s_x(w)=2\langle x,w\rangle x-w$。步 $(x,y)$ 的矢高为 $v(x,y)=1-c(x,y)=2(1-\kappa(x,y))=\tfrac12|y-x|^2$。切空间写成右平凡化 $T_uM=\{\xi u:\xi\in\operatorname{Im}\mathbb H\}$；$M$ 带由 $\mathbb H$ 诱导的圆度量 $g$。

**约定 2.3（最小弧与半位移）。** 对 $y\ne-x$，从 $x$ 到 $y$ 的最小弧是连接二者的最短大圆弧，长 $d(x,y)<\pi$。半位移为

$$
h_{yx}:=\frac{(x+y)\bar x}{|x+y|}=\frac{1+y\bar x}{2\sqrt{\kappa(x,y)}} .
$$

对 $a\in M$ 记 $\Theta(a):=2d(1,a)=2\arccos\operatorname{Re}a\in[0,2\pi]$；$\operatorname{Ad}(a)\colon\xi\mapsto a\xi\bar a$ 是绕 $\operatorname{Im}a$ 转角 $\Theta(a)$ 的旋转。由 $d$ 的双不变性，

$$
\Theta(ab)\le\Theta(a)+\Theta(b),\qquad \Theta(bab^{-1})=\Theta(a)=\Theta(a^{-1}).
$$

## 3. 最小弧上的 Levi-Civita 平移

**定理 3.1（最小弧平移是半位移的共轭）。** 设 $u,w\in M$，$w\ne-u$，$g:=w\bar u$，$h:=h_{wu}$，$m:=hu$。则 $h\in M$，$\operatorname{Re}h>0$，$h^2=g$，$m=(u+w)/|u+w|$ 是从 $u$ 到 $w$ 的最小弧的中点，并且：

- 圆度量的 Levi-Civita 联络沿从 $u$ 到 $w$ 的最小弧的平行移动为 $P\colon T_uM\to T_wM$，$P(\xi u)=(h\xi\bar h)\,w$；
- $P=-\,d(s_m)|_{T_uM}$。

**证明。** 由 $(u+w)\bar u=1+g$ 与 $|u+w|=|1+g|$ 得 $h=(1+g)/|1+g|$。写 $g=\cos\theta+n\sin\theta$，$\theta=d(u,w)\in[0,\pi)$，$n\in\operatorname{Im}\mathbb H$ 为单位向量（$\theta=0$ 时任取）。则 $1+g=2\cos\tfrac\theta2\bigl(\cos\tfrac\theta2+n\sin\tfrac\theta2\bigr)$，且 $\cos\tfrac\theta2>0$，故 $h=\cos\tfrac\theta2+n\sin\tfrac\theta2\in M$，$\operatorname{Re}h>0$，$h^2=\cos\theta+n\sin\theta=g$。$m=hu=(u+w)/|u+w|$ 是 $u,w$ 所在大圆上与二者等距的点，即最小弧中点。

令 $a:=\tfrac\theta2 n$，$h_t:=e^{ta}$，$\gamma(t):=e^{2ta}u$（$t\in[0,1]$）。$\gamma$ 是 $u$ 经左平移的单参数子群轨道，为大圆弧，$\gamma(0)=u$，$\gamma(1)=gu=w$，长度 $|2a|=\theta=d(u,w)$，故 $\gamma$ 就是最小弧。对 $\xi\in\operatorname{Im}\mathbb H$ 令

$$
V(t):=(h_t\xi\bar h_t)\,\gamma(t)=e^{ta}\xi e^{ta}u .
$$

$h_t\xi\bar h_t\in\operatorname{Im}\mathbb H$，故 $V(t)\in T_{\gamma(t)}M$。由于 $a$ 与 $e^{ta}$ 可交换，

$$
\dot V(t)=e^{ta}(a\xi+\xi a)e^{ta}u=-2\langle a,\xi\rangle\,e^{2ta}u=-2\langle a,\xi\rangle\,\gamma(t),
$$

这里用了 $a\xi+\xi a=-2\langle a,\xi\rangle$。于是 $\dot V$ 处处与 $T_{\gamma(t)}M$ 正交，即 $V$ 的协变导数为零，$V$ 沿 $\gamma$ 平行。$V(0)=\xi u$，$V(1)=(h\xi\bar h)w$，第一条得证。

$s_m(z)=m\bar z m$ 的微分为 $v\mapsto m\bar v m$。对 $v=\xi u$ 有 $\bar v=\bar u\bar\xi=-\bar u\xi$，故

$$
-\,d(s_m)(\xi u)=m\bar u\xi m=(hu)\bar u\,\xi\,(hu)=h\xi h u=(h\xi\bar h)\,h^2u=(h\xi\bar h)\,w ,
$$

第二条得证。$\square$

**命题 3.2（多边形的 Levi-Civita 和乐）。** 设 $x_0,x_1,\dots,x_n=x_0\in M$，相邻两点不对径，并令 $H:=h_{x_nx_{n-1}}\cdots h_{x_1x_0}$。则沿最小弧多边形 $x_0\to x_1\to\cdots\to x_n$ 的 Levi-Civita 平行移动在右平凡化下为 $\xi x_0\mapsto(H\xi\bar H)\,x_0$，其转角至多 $\Theta(H)$。

**证明。** 由定理 3.1，逐段平移在右平凡化下为 $\operatorname{Ad}(h_{x_kx_{k-1}})$，复合为 $\operatorname{Ad}(H)$。$\operatorname{Ad}(H)$ 是转角 $\Theta(H)$ 的旋转，作为 $\mathrm{SO}(3)$ 元的转角为 $\min(\Theta(H),2\pi-\Theta(H))\le\Theta(H)$。$\square$

称 $H$ 为该多边形在 $x_0$ 处的自旋和乐。

## 4. 离散最小作用与递推的相容阶

**定理 4.1（离散最小作用）。** 设 $p,q\in M$，$\Theta:=d(p,q)<\pi$，$N\ge1$。对 $x_0=p$，$x_N=q$ 与任意 $x_1,\dots,x_{N-1}\in M$，

$$
S(x):=\sum_{k=0}^{N-1}v(x_k,x_{k+1})\ \ge\ N\bigl(1-\cos(\Theta/N)\bigr),
$$

等号当且仅当 $x_k=\gamma(k\Theta/N)$ 对一切 $k$ 成立，其中 $\gamma$ 为从 $p$ 到 $q$ 的单位速度最小测地线。该极小点满足 $x_{k+1}=[x_k,x_{k-1},x_k]$（$1\le k\le N-1$）。另外，端点固定且各步满足 $d(x_k,x_{k+1})<\pi/2$ 的序列是 $S$ 在 $M^{N-1}$ 上的临界点，当且仅当它对 $1\le k\le N-1$ 满足 $x_{k+1}=[x_k,x_{k-1},x_k]$。

**证明。** 令 $f(t)=1-\cos t$，$d_k=d(x_k,x_{k+1})\in[0,\pi]$；$f$ 在 $[0,\pi]$ 上严格递增。若 $\Theta=0$，右端为 $0$，等号当且仅当全部 $d_k=0$，即 $x_k=p$。以下设 $\Theta>0$。由三角不等式 $D:=\sum_kd_k\ge\Theta>0$。令 $d_k':=d_k\Theta/D\le d_k$，则 $S=\sum f(d_k)\ge\sum f(d_k')$，且 $(d_k')$ 位于紧单纯形 $\Delta=\{t_k\ge0,\ \sum t_k=\Theta\}$ 中。对 $s,t\ge0$，$s+t\le\Theta<\pi$，

$$
f(s)+f(t)=2-2\cos\tfrac{s+t}2\cos\tfrac{s-t}2\ \ge\ 2-2\cos\tfrac{s+t}2=2f\bigl(\tfrac{s+t}2\bigr),
$$

因 $\cos\frac{s+t}2>0$，等号当且仅当 $s=t$。$\sum f(t_k)$ 在 $\Delta$ 上取到最小值；若最小点有两项不等，以其平均替换会严格减小和，矛盾。故最小值只在 $t_k\equiv\Theta/N$ 处取到，等于 $Nf(\Theta/N)$，不等式得证。

等号成立时 $\sum f(d_k)=\sum f(d_k')$ 且 $d_k'\le d_k$，由严格递增得 $d_k=d_k'$；又 $d_k'=\Theta/N$，故 $D=\Theta$，$d_k=\Theta/N$。于是 $d(p,x_k)\le k\Theta/N$，$d(x_k,q)\le(N-k)\Theta/N$，两者之和不小于 $\Theta$，故二者均取等。满足 $d(p,x)+d(x,q)=d(p,q)<\pi$ 的点落在唯一最小测地线上，因此 $x_k=\gamma(k\Theta/N)$。反之，此序列的各步长为 $\Theta/N$，取到下界。写 $\gamma(t)=\cos t\,p+\sin t\,\tau$，$\tau\perp p$ 为单位向量，由余弦和角公式 $\gamma(t+\delta)=2\cos\delta\,\gamma(t)-\gamma(t-\delta)$；令 $\delta=\Theta/N$，$c(\gamma(t),\gamma(t-\delta))=\cos\delta$，由约定 2.2 即得 $x_{k+1}=s_{x_k}(x_{k-1})=[x_k,x_{k-1},x_k]$。

临界点：$S$ 关于 $x_k$（$0<k<N$）的外围梯度为 $-(x_{k-1}+x_{k+1})$，故 $x$ 为球面上的临界点当且仅当存在 $\mu_k\in\mathbb R$ 使 $x_{k-1}+x_{k+1}=\mu_kx_k$。由 $|x_{k+1}|^2=|\mu_kx_k-x_{k-1}|^2$ 得 $\mu_k\bigl(\mu_k-2c(x_k,x_{k-1})\bigr)=0$。若 $\mu_k=0$，则 $x_{k+1}=-x_{k-1}$，$c(x_k,x_{k+1})=-c(x_k,x_{k-1})$，即 $d(x_k,x_{k+1})=\pi-d(x_k,x_{k-1})$，与两步均小于 $\pi/2$ 矛盾。故 $\mu_k=2c(x_k,x_{k-1})$，即 $x_{k+1}=s_{x_k}(x_{k-1})$；反之此式给出 $\mu_k=2c(x_k,x_{k-1})$，为临界点。临界点方程是离散变分原理的一个实例，先例见 Moser–Veselov（Comm. Math. Phys. 139 (1991) 217–243）；本定理的全局不等式与等号刻画不依赖该先例。$\square$

**定理 4.2（递推的相容阶）。** 设 $x\colon(a,b)\to M$ 为 $C^4$ 曲线，$\nabla_t\dot x=\ddot x+|\dot x|^2x$ 为其协变加速度，$c_\pm(t,h):=c(x(t),x(t\pm h))$。在 $(a,b)$ 的紧子区间上一致地，当 $h\to0$，

$$
\begin{aligned}
x(t+h)-[x(t),x(t-h),x(t)]&=h^2\,\nabla_t\dot x(t)-\tfrac{h^3}{2}\,\tfrac{d}{dt}|\dot x|^2(t)\;x(t)+O(h^4),\\
x(t+h)+x(t-h)-(c_++c_-)\,x(t)&=h^2\,\nabla_t\dot x(t)+O(h^4),
\end{aligned}
$$

且第二式左端对每个 $h$ 都与 $M$ 在 $x(t)$ 处相切。第一式左端对一切 $t$ 及一切充分小的 $h>0$ 为零，当且仅当 $x$ 是常速测地线。

**证明。** 记 $x=x(t)$。由 $|x|^2=1$ 逐次求导得 $\langle x,\dot x\rangle=0$，$\langle x,\ddot x\rangle=-|\dot x|^2$，$\langle x,x'''\rangle=-3\langle\dot x,\ddot x\rangle=-\tfrac32(|\dot x|^2)'$。带余项的 Taylor 公式给出 $x(t+h)+x(t-h)=2x+h^2\ddot x+O(h^4)$ 与

$$
c_\pm=1-\tfrac{h^2}{2}|\dot x|^2\mp\tfrac{h^3}{4}(|\dot x|^2)'+O(h^4),
$$

余项在紧子区间上一致。由约定 2.2，$[x,x(t-h),x]=2c_-x-x(t-h)$，故第一式左端为 $x(t+h)+x(t-h)-2c_-x$，代入即得第一式。又 $c_++c_-=2-h^2|\dot x|^2+O(h^4)$，得第二式；$\langle x,\ x(t+h)+x(t-h)-(c_++c_-)x\rangle=c_++c_--(c_++c_-)=0$ 给出相切。若第一式左端恒为零，除以 $h^2$ 并令 $h\to0$ 得 $\nabla_t\dot x\equiv0$，$x$ 为测地线，从而常速。反之，常速测地线 $x(t)=\cos(\omega t)p+\sin(\omega t)\tau$ 满足 $x(t+h)=2\cos(\omega h)x(t)-x(t-h)$ 且 $c_-=\cos(\omega h)$，左端为零。$\square$

## 5. 三角形的自旋和乐乘积公式

**定理 5.1（最小弧三角形的自旋和乐）。** 设 $x,y,z\in M$ 两两不对径，$c_{xy}=c(x,y)$，$\kappa_{xy}=\kappa(x,y)$，其余类推，$a:=h_{xz}h_{zy}h_{yx}$ 为三角形 $x\to y\to z\to x$ 在 $x$ 处的自旋和乐。则

$$
a=\frac{(1+c_{xy}+c_{yz}+c_{zx})+\operatorname{Im}(y\bar x)\times\operatorname{Im}(z\bar x)}{4\sqrt{\kappa_{xy}\kappa_{yz}\kappa_{zx}}},
\qquad
\operatorname{Re}a=\frac{\kappa_{xy}+\kappa_{yz}+\kappa_{zx}-1}{2\sqrt{\kappa_{xy}\kappa_{yz}\kappa_{zx}}} .
$$

$a$ 在 $(x,y,z)\mapsto(xb,yb,zb)$（$b\in M$）下不变。若 $x,y,z$ 线性无关，令 $E\in(0,2\pi)$ 为大球面 $M\cap\operatorname{span}(x,y,z)$ 中测地三角形 $xyz$ 的球面超出量（面积），则 $\Theta(a)=E$，

$$
\tan\tfrac E2=\frac{\lVert x\wedge y\wedge z\rVert}{1+c_{xy}+c_{yz}+c_{zx}},\qquad
\cos E=\frac{(\kappa_{xy}+\kappa_{yz}+\kappa_{zx}-1)^2}{2\kappa_{xy}\kappa_{yz}\kappa_{zx}}-1,
$$

其中 $\tan\tfrac E2$ 的式子在分母为零时理解为 $E=\pi$，并且 $\operatorname{Im}a$ 与 $\operatorname{Im}(y\bar x)\times\operatorname{Im}(z\bar x)$ 同向。若 $y=\exp(Y)x$，$z=\exp(Z)x$，$Y,Z\in\operatorname{Im}\mathbb H$，$|Y|,|Z|\le r$，则当 $r\to0$，$a=\exp\bigl(\tfrac14Y\times Z+O(r^4)\bigr)$。

**证明。** 对 $b\in M$，$(yb)\overline{(xb)}=y\bar x$，故每个半位移因而 $a$ 在右平移下不变；$c$ 与 $\kappa$ 亦然，且 $\operatorname{Im}(y\bar x)$ 只依赖于 $y\bar x$。用 $b=\bar x$ 可设 $x=1$。此时 $h_{yx}=(1+y)/|1+y|$，$h_{zy}=(1+z\bar y)/|y+z|$，$h_{xz}=(1+\bar z)/|1+z|$，且

$$
(1+\bar z)(1+z\bar y)(1+y)=2+(y+\bar y)+(z+\bar z)+(z\bar y+\bar z y).
$$

写 $y=y_0+Y'$，$z=z_0+Z'$，$Y',Z'\in\operatorname{Im}\mathbb H$。则 $y+\bar y=2c_{xy}$，$z+\bar z=2c_{zx}$，$z\bar y+\bar zy=2z_0y_0-2Z'Y'=2c_{yz}+2\,Y'\times Z'$。由 $|u+w|=2\sqrt{\kappa(u,w)}$，分母为 $8\sqrt{\kappa_{xy}\kappa_{yz}\kappa_{zx}}$，即得 $a$ 的公式；再由 $1+c=2\kappa$ 得 $\operatorname{Re}a$ 的公式。

Gram 行列式为 $\lVert x\wedge y\wedge z\rVert^2=1+2c_{xy}c_{yz}c_{zx}-c_{xy}^2-c_{yz}^2-c_{zx}^2$，直接展开给出

$$
(1+c_{xy}+c_{yz}+c_{zx})^2+\lVert x\wedge y\wedge z\rVert^2=2(1+c_{xy})(1+c_{yz})(1+c_{zx})=16\,\kappa_{xy}\kappa_{yz}\kappa_{zx}.
$$

由 $|a|=1$ 得 $|\operatorname{Im}a|=\lVert x\wedge y\wedge z\rVert/(4\sqrt{\kappa_{xy}\kappa_{yz}\kappa_{zx}})$，故 $\tfrac12\Theta(a)\in[0,\pi]$ 的余弦为 $\operatorname{Re}a$、正弦为 $|\operatorname{Im}a|\ge0$，其正切等于 $\lVert x\wedge y\wedge z\rVert/(1+c_{xy}+c_{yz}+c_{zx})$，所在象限由分母符号决定。在三维空间 $\operatorname{span}(x,y,z)$ 中 $\lVert x\wedge y\wedge z\rVert=|\det(x,y,z)|$，van Oosterom–Strackee 的立体角公式（IEEE Trans. Biomed. Eng. BME-30 (1983) 125–126；另见 Eriksson, Math. Mag. 63 (1990) 184–187）把这一角等同于三角形所张锥的立体角之半，再由 Girard 定理该立体角等于 $E$；这两步是已知中间结论。$\cos E=2\cos^2\tfrac E2-1=2(\operatorname{Re}a)^2-1$ 给出余弦式。$x=1$ 时大球面在 $1$ 处的切平面由 $Y',Z'$ 张成，$\operatorname{Im}a$ 是 $Y'\times Z'$ 的正倍数。

最后，$x=1$ 时 $Y'=\sin|Y|\,Y/|Y|=Y+O(r^3)$，$Z'$ 同理，$Y'\times Z'=Y\times Z+O(r^4)$，而 $4\sqrt{\kappa_{xy}\kappa_{yz}\kappa_{zx}}=4+O(r^2)$，故 $\operatorname{Im}a=\tfrac14Y\times Z+O(r^4)$；由于 $|\operatorname{Im}a|=O(r^2)$，$\log a=\operatorname{Im}a\,(1+O(|\operatorname{Im}a|^2))=\tfrac14Y\times Z+O(r^4)$。$\square$

用三边长 $\alpha,\beta,\gamma$ 表示时，$\operatorname{Re}a=\cos\tfrac E2$ 即球面三角中已知的 $\cos\tfrac E2=(1+\cos\alpha+\cos\beta+\cos\gamma)/(4\cos\tfrac\alpha2\cos\tfrac\beta2\cos\tfrac\gamma2)$（Todhunter, *Spherical Trigonometry*, 5th ed., 1886, Art. 103）；定理 5.1 的承重部分是整个和乐元 $a$ 的乘积公式，它对顶点与三个 $\sqrt\kappa$ 是有理式。

## 6. 可剖分圆盘的超出量界

**定义 6.1（可剖分三角化圆盘与顶点映射）。** 平面三角化圆盘 $K$ 称为可剖分的，若其三角形可排成 $T_1,\dots,T_m$，使每个 $K_j=T_1\cup\cdots\cup T_j$ 是闭圆盘，且对 $j\ge2$，$T_j\cap K_{j-1}$ 是 $T_j$ 的一条或两条边组成的路径。顶点映射 $x\colon K^0\to M$ 称为容许的，若每条边的两端点不对径。$K$ 的边界与每个三角形取逆时针定向。对 $T$ 的逆时针顶点序 $(p,q,r)$，记 $a_T:=h_{x_px_r}h_{x_rx_q}h_{x_qx_p}$，并记 $E_T:=\Theta(a_T)$。

**定理 6.2（非交换超出量界）。** 设 $K$ 为可剖分三角化圆盘，$x$ 为容许顶点映射，$H_\partial$ 为边界最小弧多边形在某个边界顶点处的自旋和乐（逐边乘以半位移，见命题 3.2）。则

$$
\Theta(H_\partial)\le\sum_{T}E_T .
$$

若某个三角形 $T$ 的三个顶点像线性无关，$E_T$ 等于其像的测地三角形的球面超出量（定理 5.1）。特别地，闭最小弧多边形的 Levi-Civita 和乐转角，不超过任一此类填充中各三角形的 $\Theta(a_T)$ 之和。

**证明。** 对边路径 $\gamma=(p_0\to\cdots\to p_n)$ 记 $\operatorname{hol}(\gamma):=h_{x_{p_n}x_{p_{n-1}}}\cdots h_{x_{p_1}x_{p_0}}$，则拼接满足 $\operatorname{hol}(\gamma\ast\gamma')=\operatorname{hol}(\gamma')\operatorname{hol}(\gamma)$，反向路径的和乐是逆元，同一闭路换基点后和乐共轭。由约定 2.3，$\Theta$ 是类函数，于是闭路的 $\Theta(\operatorname{hol})$ 不依赖基点与起点；每个三角形边界在任一顶点处的和乐与 $a_T$ 共轭，其 $\Theta$ 等于 $E_T$。

对 $j$ 归纳证明 $\Theta(\operatorname{hol}(\partial K_j))\le\sum_{i\le j}E_{T_i}$。$j=1$ 时为等式。设 $j\ge2$，$\delta:=T_j\cap K_{j-1}$ 是从 $q$ 到 $p$ 的边路径，取定向使 $\partial K_{j-1}$ 在 $p$ 处写成 $\alpha\ast\delta$，$\alpha$ 从 $p$ 到 $q$。相邻面在公共边上定向相反，故 $\partial T_j$ 在 $p$ 处为 $\bar\delta\ast\beta$，$\beta$ 是 $\partial T_j$ 中从 $q$ 到 $p$ 的其余边，而 $\partial K_j=\alpha\ast\beta$。于是

$$
\operatorname{hol}(\alpha\ast\beta)=\operatorname{hol}(\beta)\operatorname{hol}(\delta)^{-1}\operatorname{hol}(\delta)\operatorname{hol}(\alpha)=\operatorname{hol}(\bar\delta\ast\beta)\,\operatorname{hol}(\alpha\ast\delta),
$$

由次可加性 $\Theta(\operatorname{hol}\partial K_j)\le E_{T_j}+\Theta(\operatorname{hol}\partial K_{j-1})$，归纳完成。$K_m=K$ 给出不等式。这一切割恒等式是格点非阿贝尔 Stokes 公式的有限形式，先例见 Aref'eva（Theor. Math. Phys. 43 (1980) 353–356）与 Karp–Mansouri–Rno（J. Math. Phys. 40 (1999) 6033–6043），此处只作中间步骤。最后一句由命题 3.2 与上述不等式得到。$\square$

当全部顶点像落在同一大 $2$-球面上时，各因子可交换，$\operatorname{Re}H_\partial$ 由带符号超出量之和给出，这是已知的离散 Gauss–Bonnet 情形，本卷不单列。

## 7. 有理顶点上的精确弧演算

**定理 7.1（有理弧演算）。** 记 $M(\mathbb Q)=M\cap\mathbb Q^4$。设所涉全部顶点属于 $M(\mathbb Q)$。则：

- 三元运算、$c$、$\kappa$、矢高 $v$ 及递推 $x_{n+1}=[x_n,x_{n-1},x_n]$ 的各项均为有理的；
- 对不对径的 $x_p,x_q$，沿从 $x_p$ 到 $x_q$ 的最小弧的 Levi-Civita 平移在右平凡化下为 $\operatorname{Ad}(1+x_q\bar x_p)\in\mathrm{SO}(3,\mathbb Q)$，任一闭最小弧多边形的 Levi-Civita 和乐亦属 $\mathrm{SO}(3,\mathbb Q)$，其自旋和乐为 $N/|N|$，$N\in\mathbb Q^4$；
- 每个两两不对径的三角形有 $\cos E\in\mathbb Q$，其值由定理 5.1 给出。

半位移与超出量本身一般不是有理的：$x=1$，$y=i$，$z=j$ 时 $h_{yx}=(1+i)/\sqrt2$，$E=\pi/2$。

**证明。** 第一条由 $[x,y,z]=x\bar yz$、$c=\langle\cdot,\cdot\rangle$、$\kappa=\tfrac12(1+c)$、$v=1-c$ 与 $x_{n+1}=2c(x_n,x_{n-1})x_n-x_{n-1}$ 均为有理运算得到。第二条：$h_{x_qx_p}=N_{qp}/|N_{qp}|$，$N_{qp}=1+x_q\bar x_p\in\mathbb Q^4$，故 $\operatorname{Ad}(h_{x_qx_p})\xi=N_{qp}\xi\bar N_{qp}/|N_{qp}|^2$ 有理；由定理 3.1 它就是最小弧平移，有理旋转之积仍有理，自旋和乐等于 $\prod N_{qp}/\prod|N_{qp}|$，而 $|\prod N_{qp}|=\prod|N_{qp}|$。第三条是定理 5.1 的余弦式，右端为 $\kappa$ 的有理式。例子：$(1+i)/\sqrt2$ 非有理；$1,i,j$ 张成的测地三角形是八分之一球面，面积 $4\pi/8=\pi/2$。$\square$

## 8. 来源、文献状态与边界

**文献表态。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Moser, Veselov, Comm. Math. Phys. 139 (1991) 217–243 | `literature-attested`：定理 4.1 临界点方程作为离散变分原理的实例；不用于全局不等式与等号刻画 |
| van Oosterom, Strackee, IEEE Trans. Biomed. Eng. BME-30 (1983) 125–126；Eriksson, Math. Mag. 63 (1990) 184–187；Girard 定理；Todhunter (1886) Art. 103 | `literature-attested`：定理 5.1 中把角 $\tfrac12\Theta(a)$ 等同于 $E/2$ 的一步与 $\cos\tfrac E2$ 的边长形式；不用于和乐元 $a$ 的乘积公式 |
| Aref'eva, Theor. Math. Phys. 43 (1980) 353–356；Karp, Mansouri, Rno, J. Math. Phys. 40 (1999) 6033–6043 | `literature-attested`：定理 6.2 证明中的切割恒等式（格点非阿贝尔 Stokes）；不用于超出量界本身 |
| — | `repo-derived`：定理 3.1、命题 3.2、定理 4.1 的不等式与等号刻画、定理 4.2、定理 5.1 的乘积公式与小三角形展开、定理 6.2、定理 7.1。作者的文献比对在所检索范围内未见这些陈述的同一形式；本卷不作超出此范围的新颖性主张 |

**本卷不收的已知结果。** 三元运算与左右平坦联络 $\nabla^L,\nabla^R$ 的对应及其平均为 Levi-Civita 联络（Cartan–Schouten 1926）、反射 $s_x$ 构成 Loos 意义的对称空间（Loos 1969）、递推 $x_{n+1}=[x_n,x_{n-1},x_n]$ 生成等距测地采样及其 Chebyshev 形式、只有 $S^1,S^3$ 承载此类三元运算的障碍定理、Cayley 坐标的有理参数化，以及矢高和与二次变差的关系（Föllmer 1981 的改写）。这些按第 3.8 条只能以 `Library/` 文献注引用。

## 追加锚（本行以下为增补区）
