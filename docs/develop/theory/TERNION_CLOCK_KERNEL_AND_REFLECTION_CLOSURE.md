# 三维球面上的钟不变核与乘积向量的反射闭包

> **本卷的机器契约。** 消化器 `generic-v1`；地址只由本文件字节算出。本卷只增不减：卷首与既有各章合入后不再改写，修订、勘误与增补写在文末追加锚之后的新章里。

## 1. 定位与状态

**参考输入。** 本卷是 trureturing 的参考输入，Lean 形式化才是唯一真源；不得把形式化工件反向绑定到本卷的章节号或定理号上。

**证明状态。** 本卷给出 ZFC 内的普通数学证明，未经 Lean kernel 验证；哪条已被形式化，以冻结账本为准。

**范围。** 本卷在单位四元数球面 $S^3$ 的标准模型上工作，所用记号与 [最小弧演算卷](TERNION_MINIMAL_ARC_CALCULUS.md) 的约定 2.1、2.2 相同。由公理推出 $S^3$ 的分类不在本卷范围内，相关工作见 [issue #31739](https://github.com/the-omega-institute/trureturing/issues/31739)。

## 2. 记号与约定

**约定 2.1（模型、钟与复结构）。** $M=S^3\subset\mathbb H$，$c(x,y)=\operatorname{Re}(\bar xy)$，$\kappa=\tfrac12(1+c)$，$s_x(w)=x\bar wx=2c(x,w)x-w$。钟是右乘单参数群 $\rho_\chi(z)=z\,e^{i\chi}$（$\chi\in\mathbb R/2\pi\mathbb Z$），记其轨道集合 $P:=M/\{\rho_\chi\}$，$x$ 的轨道记 $[x]$。令 $J(z):=z\,i$，则 $J$ 是 $V=\mathbb H$ 上的正交复结构；用 $z_0+jz_1\mapsto(z_0,z_1)$（$z_0,z_1\in\mathbb C$）把 $(V,J)$ 等同于 $\mathbb C^2$。定义

$$
\langle x,y\rangle_T:=c(x,y)+i\,c(Jx,y).
$$

**约定 2.2（左右乘）。** 对 $a,b\in M$ 记 $L_a(z)=az$，$R_b(z)=zb$，以及 $f_{a,b}:=L_aR_b\colon z\mapsto azb$。

## 3. 钟不变量

**引理 3.1（钟下的振幅）。** 在约定 2.1 下，$\langle x,y\rangle_T=\bar z_0w_0+\bar z_1w_1$ 对 $x=z_0+jz_1$，$y=w_0+jw_1$ 成立；它对 $x$ 共轭线性、对 $y$ 线性，$\langle\rho_\chi x,y\rangle_T=e^{-i\chi}\langle x,y\rangle_T$，且对 $x,y\in M$，$c(\rho_\chi x,y)=\operatorname{Re}\bigl(e^{-i\chi}\langle x,y\rangle_T\bigr)$。

**证明。** $j(a+bi)=aj-bk$，故 $jz_1$ 在 $\mathbb R^4$ 中的坐标为 $(0,0,\operatorname{Re}z_1,-\operatorname{Im}z_1)$，由此 $c(x,y)=\operatorname{Re}(\bar z_0w_0)+\operatorname{Re}(\bar z_1w_1)$。又 $x\,i=z_0i+jz_1i$，故 $c(Jx,y)=\operatorname{Re}(\overline{z_0i}\,w_0)+\operatorname{Re}(\overline{z_1i}\,w_1)=\operatorname{Im}(\bar z_0w_0)+\operatorname{Im}(\bar z_1w_1)$。两式合成 $\langle x,y\rangle_T=\bar z_0w_0+\bar z_1w_1$。$\rho_\chi x=z_0e^{i\chi}+jz_1e^{i\chi}$ 给出相位关系，取实部得最后一式。$\square$

**定理 3.2（Born 核的四种钟不变表示）。** 对 $x,y\in M$ 令 $\beta(x,y):=|\langle x,y\rangle_T|^2$。则 $\beta$ 只依赖 $[x],[y]$，并且

$$
\beta(x,y)=\max_{\chi}c(\rho_\chi x,y)^2=\frac1\pi\int_0^{2\pi}c(\rho_\chi x,y)^2\,d\chi=\max_{\chi}\kappa\bigl(y,s_{\rho_\chi x}(y)\bigr)=8\operatorname{Var}_\chi\kappa(\rho_\chi x,y),
$$

其中 $\operatorname{Var}_\chi$ 是 $\chi$ 在 $[0,2\pi)$ 上均匀分布时的方差；此外 $\frac1{2\pi}\int_0^{2\pi}\kappa(\rho_\chi x,y)\,d\chi=\tfrac12$。

**证明。** 记 $z=\langle x,y\rangle_T$。由引理 3.1，$c(\rho_\chi x,y)=|z|\cos(\chi-\arg z)$，其平方的最大值为 $|z|^2$、在 $[0,2\pi)$ 上的平均为 $|z|^2/2$，而它本身的平均为 $0$。这给出前两种表示与 $\kappa$ 的平均 $\tfrac12$。对 $w\in M$，$\kappa(y,s_w(y))=\tfrac12\bigl(1+c(y,2c(w,y)w-y)\bigr)=c(w,y)^2$；取 $w=\rho_\chi x$ 并对 $\chi$ 取最大，得第三种表示。$\kappa(\rho_\chi x,y)=\tfrac12+\tfrac12c(\rho_\chi x,y)$，其方差为 $\tfrac14\cdot\tfrac12|z|^2=|z|^2/8$。由于 $|\langle\rho_\chi x,\rho_{\chi'}y\rangle_T|=|z|$，$\beta$ 只依赖轨道。$\square$

通过 $x\mapsto r_x$（Bloch 向量）与 Hopf 映射 $M\to P\cong S^2$，$\beta=\tfrac12(1+\langle r_x,r_y\rangle)$ 是已知的 Bloch 公式；上面的定理不依赖这一步。

**命题 3.3（$\beta$ 的不变群）。** 设 $a,b\in M$。$f_{a,b}$ 保持 $\beta$（即 $\beta(f_{a,b}x,f_{a,b}y)=\beta(x,y)$ 对一切 $x,y\in M$）当且仅当 $b\in\{e^{i\theta}\}\cup\{j e^{i\theta}\}$。

**证明。** 充分性：$L_a$ 与 $R_{e^{i\theta}}$ 都是等距且与 $J$（右乘 $i$）交换，故保持 $\langle\cdot,\cdot\rangle_T$。$R_j$ 是等距且 $J(zj)=zji=-zij=-(Jz)j$，于是 $\langle xj,yj\rangle_T=c(x,y)-i\,c(Jx,y)=\overline{\langle x,y\rangle_T}$，模不变。

必要性：对单位向量，Cauchy–Schwarz 的等号情形给出 $\beta(x,y)=1$ 当且仅当 $y=x\lambda$，$\lambda\in\mathbb C$，$|\lambda|=1$，即 $[y]=[x]$。故保持 $\beta$ 的 $f_{a,b}$ 把每条轨道映入一条轨道：对一切 $x,\theta$，$a\,x e^{i\theta}b\in(axb)\{e^{i\varphi}\}$，即 $\bar b e^{i\theta}b\in\{e^{i\varphi}\}$。取 $\theta=\pi/2$ 得 $\bar b\,i\,b$ 为属于 $\mathbb C$ 的单位纯虚四元数，即 $\bar b ib=\pm i$。$\bar bib=i$ 当且仅当 $b$ 与 $i$ 交换，即 $b\in\mathbb C$；$\bar bib=-i$ 当且仅当 $b$ 与 $i$ 反交换，即 $b\in j\mathbb C$。$\square$

## 4. 乘积向量的反射闭包

**定义 4.1（乘积单位向量与实反射）。** 设 $N\ge1$，$V_N=(\mathbb C^2)^{\otimes N}$ 为复 Hilbert 空间，带实内积 $c_N(\psi,\phi)=\operatorname{Re}\langle\psi,\phi\rangle$，实维数 $2^{N+1}$。令 $\Sigma_N=\{u_1\otimes\cdots\otimes u_N:u_k\in\mathbb C^2,\ |u_k|=1\}$。对单位向量 $x\in V_N$ 定义 $s_x(w)=2c_N(x,w)x-w$，并令 $\Gamma_N$ 为 $\{s_x:x\in\Sigma_N\}$ 生成的群。

**定理 4.2（反射闭包是整个单位球面）。** 在定义 4.1 下：

- $\Gamma_N=\mathrm O(V_N,c_N)$；
- 若 $S\subseteq S(V_N)$ 满足 $\Sigma_N\subseteq S$，且对一切 $x\in\Sigma_N$、$w\in S$ 有 $s_x(w)\in S$，则 $S=S(V_N)$；
- 每个酉算子 $U\in\mathrm U(V_N)$ 都是有限个 $s_x$（$x\in\Sigma_N$）之积；
- 对单位向量 $x,w\in V_N$，$\tfrac12\bigl(1+c_N(w,s_xw)\bigr)=c_N(w,x)^2$。

**证明。** 以 $R_x(v)=v-2c_N(x,v)x$ 记超平面反射，则 $s_x=-R_x$。实维数为偶数，故 $\det s_x=\det(-1)\det R_x=-1$。对单位向量 $a,b$，$s_as_b=R_aR_b$ 是平面 $\operatorname{span}(a,b)$ 内转角为 $a,b$ 夹角两倍的旋转，并固定该平面的正交补。

对 $x=x_1\otimes\cdots\otimes x_N\in\Sigma_N$ 与下标 $k$，令 $E_k(x)=\{x_1\otimes\cdots\otimes x_{k-1}\otimes u\otimes x_{k+1}\otimes\cdots\otimes x_N:u\in\mathbb C^2\}$，这是实四维子空间，且其中 $u\otimes$ 型向量的范数为 $|u|$，故 $S(E_k(x))\subseteq\Sigma_N$。由上段，$\Gamma_N$ 含 $E_k(x)$ 内任意平面上的任意角旋转，从而含 $\mathrm{SO}(E_k(x))$ 在 $V_N$ 上（固定正交补）的作用。特别地，对 $E_k(x)$ 中的正交单位向量 $a,b$，单参数群 $t\mapsto\exp(t\,a\wedge b)$ 含于 $\Gamma_N$，其中 $a\wedge b$ 是算子 $v\mapsto c_N(a,v)b-c_N(b,v)a$。

取 $\{e_0,e_1\}$ 为 $\mathbb C^2$ 的标准基，$\mathcal B=\{\lambda e_{I_1}\otimes\cdots\otimes e_{I_N}:\lambda\in\{1,i\},\ I\in\{0,1\}^N\}$ 是 $(V_N,c_N)$ 的实规范正交基。若 $\mathcal B$ 中两元的指标 $I,I'$ 至多在一个位置 $k$ 不同，它们都属于 $E_k(x)$，$x_l=e_{I_l}$（$l\ne k$），因为相位 $\lambda$ 可并入第 $k$ 个因子。以此邻接关系，$\mathcal B$ 构成连通图。对 $\mathcal B$ 中两两不同的 $a,b,d$，$[a\wedge b,\ b\wedge d]=\pm\,a\wedge d$，沿连通路径归纳可得一切 $a\wedge d$（$a,d\in\mathcal B$）属于由邻接对 $a\wedge b$ 生成的 Lie 代数，故该 Lie 代数为 $\mathfrak{so}(V_N)$。由 Lie 代数的一组生成元的单参数子群生成的群是对应的连通 Lie 子群（标准事实），因此 $\Gamma_N\supseteq\mathrm{SO}(V_N)$。再由 $\det s_x=-1$ 得 $\Gamma_N=\mathrm O(V_N)$。

第二条：$\Sigma_N\subseteq S$ 且 $S$ 对 $s_x$（$x\in\Sigma_N$）封闭，故 $\Gamma_N\Sigma_N\subseteq S$；$\mathrm{SO}(V_N)$ 在单位球面上传递（$\dim V_N\ge4$），故 $\Gamma_N\Sigma_N=S(V_N)$。第三条：$\mathrm U(V_N)\subseteq\mathrm O(V_N)=\Gamma_N$。第四条：$c_N(w,2c_N(x,w)x-w)=2c_N(x,w)^2-1$。$\square$

**命题 4.3（乘积态的镜像是极大纠缠的）。** 取 $N=2$，$x=e_0\otimes e_0$，$h=(e_0+e_1)/\sqrt2$，$w=h\otimes h$，$h^-=(e_0-e_1)/\sqrt2$。则 $c_2(x,w)=\tfrac12$，

$$
s_x(w)=\tfrac12\bigl(e_0\otimes e_0-e_0\otimes e_1-e_1\otimes e_0-e_1\otimes e_1\bigr),
$$

其系数矩阵行列式的绝对值为 $\tfrac12$（等于该维数下可取的最大值），故 $s_x(w)\notin\Sigma_2$。逐因子反射给出 $s_{e_0}(h)\otimes s_{e_0}(h)=h^-\otimes h^-\in\Sigma_2$，且 $\tfrac12\bigl(1+c_2(w,h^-\otimes h^-)\bigr)=\tfrac12\ne\tfrac14=c_2(w,x)^2$。

**证明。** $\langle e_0\otimes e_0,h\otimes h\rangle=\tfrac12$，$s_x(w)=x-w$，展开即得所示向量；系数矩阵为 $\tfrac12\begin{pmatrix}1&-1\\-1&-1\end{pmatrix}$，行列式为 $-\tfrac12$。单位向量 $\psi=\sum\psi_{ij}e_i\otimes e_j$ 属于 $\Sigma_2$ 当且仅当 $\det(\psi_{ij})=0$；对单位 $\psi$，$|\det|\le\tfrac12$（两个奇异值平方和为 $1$，其积至多 $\tfrac12$）。$s_{e_0}(h)=2\cdot\tfrac1{\sqrt2}e_0-h=h^-$；$\langle h,h^-\rangle=0$ 给出 $c_2(w,h^-\otimes h^-)=0$。$\square$

命题 4.3 说明定理 4.2 第四条的恒等式对逐因子反射不成立，而对 $V_N$ 上的反射 $s_x$ 成立；后者把乘积向量映出 $\Sigma_N$。

## 5. 无协变的结果选择

**命题 5.1（无协变选择函数）。** 令 $\mathcal A=\{\{p,-p\}:p\in S^2\}$。不存在映射 $F\colon S^2\times\mathcal A\to S^2$，使 $F(q,\{p,-p\})\in\{p,-p\}$，且对一切 $g\in\mathrm{SO}(3)$，$F(gq,\{gp,-gp\})=g\,F(q,\{p,-p\})$。

**证明。** 取 $q\perp p$，令 $g$ 为绕 $q$ 转角 $\pi$ 的旋转。则 $gq=q$，$gp=-p$，故 $\{gp,-gp\}=\{p,-p\}$，协变性给出 $F(q,\{p,-p\})=gF(q,\{p,-p\})$。但 $g$ 在 $\{p,-p\}$ 上互换两点、无不动点，矛盾。$\square$

经 Hopf 映射 $M\to P\cong S^2$，左乘 $L_a$ 在 $P$ 上诱导满射到 $\mathrm{SO}(3)$ 的作用（已知事实）；故命题 5.1 表明：对任一轨道 $[q]$ 与一对正交轨道 $\{[p],[p]^\perp\}$，不存在在左乘下协变、并从这对轨道中选出一条的规则。

## 6. 来源、文献状态与边界

**文献表态。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Hopf, Math. Ann. 104 (1931) 637–665；Bloch 公式 | `literature-attested`：$M\to P\cong S^2$ 与 $\beta=\tfrac12(1+\langle r_x,r_y\rangle)$，只在定理 3.2 之后与第 5 章作注；不用于定理 3.2、命题 3.3、命题 5.1 的证明 |
| 单参数子群生成连通 Lie 子群（标准 Lie 理论；另见 Yamabe, Osaka Math. J. 2 (1950) 13–14） | `literature-attested`：定理 4.2 证明中的一步 |
| — | `repo-derived`：引理 3.1、定理 3.2、命题 3.3、定理 4.2、命题 4.3、命题 5.1。本卷不主张这些陈述在文献中首次出现；其中复数恒等式与有限群作用论证是初等的 |

**本卷不收的已知结果。** 与左乘交换的正交复结构恰为钟的四分之一转（右乘单位纯虚四元数；Stueckelberg 的实 Hilbert 空间表述）、反转钟的对称平方为 $-1$（Wigner、Kramers）、单比特纯态的 Schrödinger 不确定性等式、Bloch 球内部作为 Klein 模型的双曲空间与 $\gamma^{-1}$ 等于并发度（Chen–Ungar；Jakob–Bergou）、$S^3$ 的球冠构成 de Sitter 空间且包含关系对应因果序（Möbius 几何）、Bargmann 三射线不变量、$\mathrm{SU}(2)$ 的 Schur–Weyl 对偶给出的无方向生成元，以及只在 $\mathrm U(1)$ 不变下二次型带两个参数的初等不变量论。这些按第 3.8 条只能以 `Library/` 文献注引用，或作为新条目证明中的中间步骤。

## 追加锚（本行以下为增补区）
