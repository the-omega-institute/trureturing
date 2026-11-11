# R5 续卷：显式根式塔的共同最小行与整数查询下界

本卷只讨论一个固定的实际特征零域塔、其中实际定义的图叶，以及原标签上的交维数。所有嵌入、乘法、迹和标量等价都在同一个原域中进行；分裂坐标只用来证明实际图叶满足所需的开条件，不能被另行指定为控制参数。记

$$
d_W(r)=\dim_{\mathbb Q}(W\cap rW),\qquad
J_W(r,s)=\dim_{\mathbb Q}(W\cap rW\cap sW),
$$

并约定 $W'=xW$（$x$ 为原域非零元）才算同一原标量类。迹配对的非退化性与传递性使用 Stacks Project，[§9.20，Tag 0BIE](https://stacks.math.columbia.edu/tag/0BIE) 的可分扩张结果。

本卷的主读出行是

$$
R_h=\left(\alpha+\sum_{k=1}^h\theta_k^{-3}\right)^{-1},\qquad
S_0=\alpha^{-3},\qquad S_j=\theta_j^2,
$$

并且它在每个位串上给出 $J(R_h,S_j)=1-\varepsilon_j$。

## 48. 实际根式塔、图叶与共同二元纤维

**定义 48.1（塔和实际窗口）。** 对 $j\ge0$ 令

$$
\gamma_j=2^{1/(6\cdot5^j)}>0,\qquad D_j=\mathbb Q(\gamma_j),\qquad
\alpha=3+\gamma_0,\qquad \theta_j=3+\gamma_j\ (j\ge1).
$$

于是 $\gamma_{j-1}=\gamma_j^5$，且 $\theta_j$ 满足

$$
(\theta_j-3)^5=\gamma_{j-1}.
$$

根窗口和根迹对偶为

$$
C_0=\langle1,\alpha,\alpha^3\rangle_{\mathbb Q},\qquad
W_{0,0}=C_0,\qquad W_{0,1}=C_0^{\perp_0},
$$

其中 $\perp_0$ 取 $\operatorname{Tr}_{D_0/\mathbb Q}(xy)$。

对 $j\ge1$ 写 $E=D_{j-1}$、$D=D_j$，置

$$
N_j=\langle1,\theta_j\rangle_E,\qquad e_j=\theta_j^3,\qquad
M_j=N_j\oplus Ee_j,\qquad
\ell_j(a+b\theta_j+ce_j)=c.
$$

在实际 $E$-代数 $E\oplus D$ 中定义图叶

$$
V_j=\{(\ell_j(x),x):x\in M_j\},\qquad
V_j^1=V_j^\perp,\qquad V_j^0=V_j,
$$

其中配对是

$$
\beta_j((a,x),(b,y))=ab+\operatorname{Tr}_{D/E}(xy).
$$

若 $A\le_{\mathbb Q}E$，记

$$
W(A,V_j^b)=\{x\in D:\exists a\in A,\ (a,x)\in V_j^b\},\qquad
W_{j,(\eta,b)}=W(W_{j-1,\eta},V_j^b).
$$

迹对偶在每一步同时翻转全部旧位：

$$
W_{j,(\eta,b)}^{\perp_j}=W_{j,(\mathbf1-\eta,\,1-b)}.
$$

图叶的对偶仍是实际图叶。若 $M_j'=N_j^\perp$（相对迹配对），则

$$
V_j^1=\{(\ell_j'(z),z):z\in M_j'\},\qquad
\ell_j'(z)=-\operatorname{Tr}_{D/E}(e_jz),\qquad N_j'=M_j^\perp.
$$

负号来自 $ab+\operatorname{Tr}_{D/E}(xy)=0$，并且在下文的对偶计算中不能删去。

事实上，对 $x=a+b\theta_j+ce_j\in M_j$ 和 $z\in N_j^\perp$，

$$
\ell_j(x)\ell_j'(z)+\operatorname{Tr}_{D/E}(xz)
=-c\operatorname{Tr}_{D/E}(e_jz)+\operatorname{Tr}_{D/E}\bigl((a+b\theta_j+ce_j)z\bigr)=0.
$$

这里使用 $z\perp N_j$；又因 $e_j\notin N_j$ 及迹非退化性，$\ell_j'$ 非零，故它在三维 $M_j'$ 上满射。

**命题 48.2（次数、乘积和足够的好条件）。** 对每个 $j\ge0$，有

$$
[D_j:\mathbb Q]=6\cdot5^j,\qquad [D_j:D_{j-1}]=5\quad(j\ge1).
$$

根乘积满足

$$
\operatorname{span}_{\mathbb Q}(C_0C_0)=D_0,
$$

而每层满足

$$
\operatorname{span}_E(N_jM_j)=D_j.
$$

这些条件连同图定义足以给出所有窗口的半维数、完整原标签的二元交维相同，以及迹对偶的逐位翻转。

证明。$X^{6\cdot5^j}-2$ 在素数 $2$ 处 Eisenstein，故给出 $D_j$ 的次数。正根的相容性给出实际包含 $D_{j-1}\subset D_j$，域塔公式遂给出相对次数五。

$C_0C_0$ 的六个乘积的幂次为 $0,1,2,3,4,6$。若它们有非平凡 $\mathbb Q$-关系，就有一个次数至多六、$T^5$ 系数为零的非零多项式在 $\alpha$ 处消失。但 $\alpha$ 的最小多项式为 $(T-3)^6-2$，其 $T^5$ 系数为 $-18$；次数至多六的消失多项式只能是其常数倍，因而系数必须为零。这证明根乘积张成 $D_0$。

在相对幂基 $1,\theta_j,\theta_j^2,\theta_j^3,\theta_j^4$ 中，$N_jM_j$ 含有

$$
1,\ \theta_j,\ \theta_j^2,\ \theta_j^3=e_j,\ \theta_j^4=\theta_je_j,
$$

故张成 $D_j$。特别地，六个图叶乘积

$$
(0,1),(0,\theta_j),(0,\theta_j^2),(0,\theta_j^3),(0,\theta_j^4),(1,\theta_j^6)
$$

张成 $E\oplus D$。因此对称乘积映射 $\operatorname{Sym}^2_E(V_j)\to E\oplus D$ 是同构；其转置就是足够的 $\mu$-非退化条件。对偶叶的可用性不要求另选一个独立的分裂控制：$M_j'$ 为三维，$\ell_j'$ 满射，且 $V_j^1$ 仍是同一个实际配对下的图。

迹传递和交换乘法的自伴性给出

$$
(xH)^{\perp_0}=x^{-1}H^{\perp_0},\qquad d_{H^{\perp_0}}(x)=d_H(x).
$$

因此前卷 §46 的秩分层公式和对偶封闭递归可直接应用，得到每一高度的所有 $W_{h,\varepsilon}$ 具有相同完整原标签函数 $d$，并且

$$
W_{h,\varepsilon}^{\perp_h}=W_{h,\mathbf1-\varepsilon},\qquad
\perp_h=\perp_{\operatorname{Tr}_{D_h/\mathbb Q}}.
$$

这一步使用的是实际迹配对，不是把各分裂坐标分别选成独立叶。$\square$

**引理 48.3（实际好叶的手工开条件）。** 上述根图和每层图在每个固定的实际塔中都可取为前卷 §46 所需的好参数；它们的分裂叶仍来自同一个实际 $\alpha$ 或 $\theta_j$ 的共轭。

证明。根的外部行可以写成 $(1,z,z^3)$，其中 $z=3+\gamma_0\zeta$、$\zeta^6=1$；每层相应为 $z=3+\gamma_j\zeta$、$\zeta^5=1$。三行的行列式是一个非零 Vandermonde 因子乘以 $z_a+z_b+z_c$，而含接合行 $(0,0,1)$ 的行列式是两个不同外部 $z$ 的差。由于

$$
|\,\gamma_j(\zeta_a+\zeta_b+\zeta_c)\,|\le3\gamma_j<6<9,
$$

这些和不为零；不同 $\zeta$ 给出不同的差。乘积张成已由命题 48.2 证明，互补 Plücker 子式给出对偶叶的均匀性。每个 $\zeta$ 只是同一实际根的一个嵌入坐标，不能被替换为另一个未下降的独立参数。$\square$

**定理 48.4（显式共同最小行和逐位读出）。** 对 $h\ge0$ 定义

$$
R_h=\left(\alpha+\sum_{k=1}^h\theta_k^{-3}\right)^{-1},\qquad
S_0=\alpha^{-3},\qquad S_j=\theta_j^2\ (1\le j\le h),
$$

空和为零。所有这些标签在固定的正实嵌入中都是实际 $D_h^\times$ 元，并在未知位串出现前固定。则对每个 $\varepsilon\in\{0,1\}^{h+1}$，

$$
d_{W_{h,\varepsilon}}(R_h)=1,\qquad
J_{W_{h,\varepsilon}}(R_h,S_j)=1-\varepsilon_j\quad(0\le j\le h).
$$

因此列出的 $2^{h+1}$ 个窗口属于同一个完整 $d$-纤维中的 $2^{h+1}$ 个不同原标量类；这里不说整个纤维只有这些类。

证明。先看根。由幂基独立性，

$$
C_0\cap\alpha^{-1}C_0=\mathbb Q\cdot1,\qquad
C_0\cap\alpha^{-1}C_0\cap\alpha^{-3}C_0=\mathbb Q\cdot1.
$$

而

$$
C_0^\perp\cap\alpha^{-1}C_0^\perp\cap\alpha^{-3}C_0^\perp
=(C_0+\alpha C_0+\alpha^3C_0)^\perp=(C_0C_0)^\perp=0.
$$

所以 $R_0=\alpha^{-1}$ 的交维为一，且根查询 $(R_0,S_0)$ 的答案是 $1-\varepsilon_0$。

设 $E=D_{j-1}$、$D=D_j$、$e=e_j$，并令 $t=R_{j-1}^{-1}$、$p=t+e^{-1}$。一维共同见证的实际局部计算如下。由

$$
(\theta_j-3)^5=\gamma_{j-1},\qquad
\theta_j^6=135\theta_j^4-1080\theta_j^3+3645\theta_j^2+(\gamma_{j-1}-5832)\theta_j+3645+15\gamma_{j-1},
$$

得到

$$
B=(e^2,e,\theta_je,1,\theta_j)
$$

是 $D$ 的 $E$-基；$e^2=\theta_j^6$ 的 $\theta_j^2$ 系数为 $3645\ne0$，其余四个向量给出其余幂次方向。若 $x=ce+a+b\theta_j\in M_j$，则 $px=tx+c+(a+b\theta_j)/e$；所以 $px\in M_j$ 等价于 $a+b\theta_j\in eM_j$，基 $B$ 的独立性迫使 $a=b=0$。故

$$
M_j\cap p^{-1}M_j=Ee,\qquad N_j\cap p^{-1}N_j=0.
$$

同一计算也给出透明提升的实际恒等式。对 $a,b\in E^\times$ 置

$$
T_e(a)=\frac{ae}{e+a}=\left(a^{-1}+e^{-1}\right)^{-1}.
$$

因为 $e\notin E$，分母不为零。把 $p=a^{-1}+e^{-1}$、$q=b^{-1}+e^{-1}$ 代入同一个基 $B$ 的计算，原支的三重见证空间为 $Ee$，接合像为 $E(1,a^{-1},b^{-1})$ 且核为零。下面的直接对偶计算对任意 $t\in E^\times$ 成立，取 $t=a^{-1}$ 即得对偶二重见证线上的 $\ell_j'(pz)=a^{-1}\ell_j'(z)$；再由 $q=p+(b^{-1}-a^{-1})$，得 $qz\in M_1$ 和 $\ell_j'(qz)=b^{-1}\ell_j'(z)$。因此对偶支也有同一三元接合像和零核，对任意父子空间 $A$ 都得到

$$
J_{W(A,V_j^c)}(T_e(a),T_e(b))=J_A(a,b)\qquad(c=0,1).
$$

这是同一实际叶参数的同时透明提升；显式共同行随后利用归一化平面把已经属于 $E$ 的旧第二标签原样留下，不另造一套变量行菜单。

对偶图仍取 $M_1=N_j^\perp$、$\ell_j'=-\operatorname{Tr}_{D/E}(e\,\cdot)$。记 $T_0=M_j\cap p^{-1}M_j$、$K_0=N_j\cap p^{-1}N_j$；由 $T_0=Ee$、$K_0=0$ 得

$$
T_1=(N_j+pN_j)^\perp,\quad \dim_E T_1=1,\qquad
K_1=(M_j+pM_j)^\perp=0.
$$

对 $z\in T_1$，有 $e,pe\in M_j$ 及 $z,pz\in M_1$。分别配对这两组原图、对偶图元素，得到

$$
-t\ell_j'(z)=\operatorname{Tr}_{D/E}(pez)
=\operatorname{Tr}_{D/E}(epz)=-\ell_j'(pz).
$$

若非零 $z$ 的 $\ell_j'(z)=0$，此式使 $z\in K_1$，矛盾。因此对偶接合线也恰为 $E(1,t)$。两片叶都由秩公式给出 $d_{W(A,V_j^b)}(p^{-1})=d_A(t^{-1})=1$。定理 49.1 证明中的实际归一化计算遂适用：父窗口中已有的标签 $s\in E^\times$ 被逐字保留，并且

$$
J_{W(A,V_j^b)}(p^{-1},s)=J_A(t^{-1},s)\qquad(b=0,1).
$$

同时，归一化后的原支核平面是 $L_0=E/e+E\theta_j/e$，而 $L_0\cap(L_1+E)=E/e$，其中交式由定理 49.1 的全乘积条件证明。因此 $\theta_j/e=\theta_j^{-2}$ 属于每个原支归一化窗口，却不属于任何对偶支归一化窗口；实际标签 $s=e/\theta_j=\theta_j^2$ 给出

$$
J_{W(A,V_j^b)}(p^{-1},\theta_j^2)=1-b.
$$

注意 $p^{-1}=R_j$，且递推 $R_j^{-1}=R_{j-1}^{-1}+\theta_j^{-3}$ 正好给出所写的闭式。对旧的 $S_i$（$i<j$）逐层使用“在 $E$ 中的标签不移动”，对新标签使用上一式，归纳得

$$
d_{W_{j,\varepsilon}}(R_j)=1,\qquad
J_{W_{j,\varepsilon}}(R_j,S_i)=1-\varepsilon_i.
$$

这里每层的 $b=0,1$ 都由原图和带负号的实际对偶图分别计算，父位串也始终任意，所以归纳覆盖所有对偶历史。半维迹对偶同时翻转所有位，只保证二元函数 $d$ 不变；在本菜单上，三元答案随之从 $1-\varepsilon_i$ 变为 $\varepsilon_i$。分母均为正实数，特别是 $e_j+\text{正数}>0$，不存在零分母。原标量乘法保持同一标签上的全部 $J$，而不同位串至少有一个上述答案不同，故这些窗口的原标量类两两不同。$\square$

## 49. 任意给定共同最小行的归一化平面

**定理 49.1（每个预先给定的最小行都有固定同一行读出）。** 固定 $h$，并给定实际 $r_0\in D_h^\times$，假设对全部 $\varepsilon\in\{0,1\}^{h+1}$ 都有

$$
d_{W_{h,\varepsilon}}(r_0)=1.
$$

则存在 $s_0,\ldots,s_h\in D_h^\times$，它们在未知 $\varepsilon$ 和任何查询回答出现前已经确定，并满足

$$
J_{W_{h,\varepsilon}}(r_0,s_j)=1-\varepsilon_j\qquad(0\le j\le h).
$$

第一标签始终是给定的 $r_0$；定理不替换它。

证明。先说明一维行的归一化。若 $H\cap r_0H=\mathbb Qz$，置 $A=z^{-1}H$。则对任意 $s\ne0$，

$$
J_H(r_0,s)=1\Longleftrightarrow s^{-1}\in A,\qquad
J_H(r_0,s)=0\Longleftrightarrow s^{-1}\notin A.
$$

更换 $z$ 的有理倍数，或把整个窗口乘以原标量，都不改变 $A$ 中的成员关系。

在非根层写 $E=D_{j-1}$、$D=D_j$、$n=[E:\mathbb Q]$、$p=r_0^{-1}$。对两片叶分别记

$$
M_0=M_j,\ \ell_0=\ell_j,\ N_0=N_j;\qquad
M_1=N_j^\perp,\ \ell_1(z)=-\operatorname{Tr}_{D/E}(e_jz),\ N_1=M_j^\perp.
$$

令

$$
T_b=M_b\cap p^{-1}M_b,\quad K_b=N_b\cap p^{-1}N_b,\quad
R_b=\{(\ell_b(x),\ell_b(px)):x\in T_b\}\subseteq E^2.
$$

定理 46.2 的实际 $E^2$ 像公式为

$$
d_{W(A,V_j^b)}(r_0)=n\dim_EK_b+\dim_{\mathbb Q}\bigl(R_b\cap A^2\bigr).
$$

左端为一，而 $n\ge6$；非零核贡献至少 $n$，全像或轴像分别贡献 $n$ 或 $n/2$。所以 $K_b=0$，$R_b$ 是非轴的一维 $E$-空间。特别地 $p\notin E$，否则 $K_b=N_b$。对 $b=0$ 取唯一的 $x_0\in T_0$、$\ell_0(x_0)=1$，写

$$
\ell_0(px_0)=t\in E^\times.
$$

则 $R_0=E(1,t)$，全部父窗口在 $t^{-1}$ 行的交维均为一，并且 $p-t\in x_0^{-1}N_0$。自伴乘法给

$$
T_1=(N_0+pN_0)^\perp,\qquad K_1=(M_0+pM_0)^\perp,\qquad
\dim_E T_1=1,\quad K_1=0.
$$

若 $z\in T_1$，则 $x_0,px_0\in M_0$、$z,pz\in M_1$。原图和对偶图的正交关系是 $\ell_0(x)\ell_1(y)=-\operatorname{Tr}_{D/E}(xy)$（$x\in M_0,y\in M_1$），因此

$$
-t\ell_1(z)=\operatorname{Tr}_{D/E}(px_0z)
=\operatorname{Tr}_{D/E}(x_0pz)=-\ell_1(pz).
$$

故 $\ell_1(pz)=t\ell_1(z)$。若非零 $z\in T_1$ 满足 $\ell_1(z)=0$，便有 $z\in K_1$，矛盾。所以 $R_1=E(1,t)$；这里没有倒数、负号或依赖父窗口的重新缩放。对每个 $b$ 取唯一的 $\ell_b(x_b)=1$ 的 $x_b\in T_b$，置

$$
L_b=x_b^{-1}N_b,\qquad H_b=x_b^{-1}M_b=E\oplus L_b.
$$

由 $p-t\in L_0\cap L_1$ 且 $p-t\ne0$，并且 $H_0\ne H_1$：若 $H_0=H_1$，则 $M_1=(x_1/x_0)M_0$，从而某个非零 $z$ 满足 $\operatorname{Tr}_{D/E}(zNM)=0$；但 $\operatorname{span}_E(NM)=D$ 和迹非退化性迫使 $z=0$，矛盾。于是

$$
L_0\cap L_1=E(p-t),\qquad
E\cap(L_0+L_1)=0.
$$

更具体地，$H_0,H_1$ 都含 $E\oplus E(p-t)$，各为三维且不同，故交恰为这二维空间、和为四维。由于 $E\cap L_b=0$ 且 $p-t\in L_0\cap L_1$，有 $L_0\cap L_1=E(p-t)$，所以 $L_0+L_1$ 为三维。再用 $E+(L_0+L_1)=H_0+H_1$ 的四维数，得到 $E\cap(L_0+L_1)=0$。

设父窗口为 $A_\eta$，并取 $y_\eta\ne0$ 使 $A_\eta\cap t^{-1}A_\eta=\mathbb Qy_\eta$。因为 $\ell_b(x_b)=1$，实际子窗口及其交线恰为 $W(A_\eta,V_j^b)=N_b+x_bA_\eta$ 和 $\mathbb Qx_by_\eta$。又因 $y_\eta\in E^\times$ 而 $L_b$ 为 $E$-空间，有 $y_\eta^{-1}L_b=L_b$，故归一化后的子窗口精确写成

$$
A_{(\eta,b)}=(x_by_\eta)^{-1}W(A_\eta,V_j^b)=L_b+y_\eta^{-1}A_\eta,\qquad
A_{(\eta,b)}\cap E=y_\eta^{-1}A_\eta.
$$

因此所有旧标签 $s\in E^\times$ 的答案逐字保留。另一方面可取

$$
v\in L_0\setminus(L_1+E),\qquad s_{\mathrm{new}}=v^{-1}.
$$

因为 $v\in A_{(\eta,0)}$ 而 $v\notin A_{(\eta,1)}\subseteq L_1+E$，新标签给出答案 $1$、$0$。从根开始，根的两个归一化三平面不同；否则 $C_0^\perp=xC_0$，则 $\operatorname{Tr}(xC_0C_0)=0$ 与 $\operatorname{span}(C_0C_0)=D_0$ 矛盾。故根也有一个固定的分离标签。按高度归纳，把旧标签逐字保留并在每层加入一个 $s_{\mathrm{new}}$，即得 $s_0,\ldots,s_h$。它们只依赖实际 $r_0$、实际图叶和已知的承诺族，不依赖未知位串。$\square$

**命题 49.2（归一化的几何解释）。** 在定理 49.1 的每一步，$A_{(\eta,b)}=L_b+A_{\mathrm{parent},\eta}$ 是一个“旧中心平面加新层核平面”的实际直和图景；$L_0\cap L_1=E(p-t)$ 是两片叶共享的唯一新方向，而 $E\cap(L_0+L_1)=0$ 说明该共享方向之外没有把旧中心混入新层的隐藏重合。

证明。$A_{\mathrm{parent},\eta}=y_\eta^{-1}A_\eta$ 是父行归一化后留在 $E$ 的平面，$L_b=x_b^{-1}N_b$ 是图叶的二维核平面。前面的实际配对计算给出两者的精确和式与交式。因为 $L_0\cap(L_1+E)=E(p-t)$，在 $L_0$ 中选出的 $v$ 只出现在 $b=0$ 的窗口；在 $b=1$ 的窗口，任何归一化向量都由对偶核和旧中心组成，落在 $L_1+E$。白话说，把一个已经只剩一条线的共同行拉直以后，两片叶都保留原来中心的影子，同时各自添一张二维“叶片”；两张叶片相交只留同一条新脊线，其他方向彼此错开。于是旧问题的标签可以原样沿塔向上携带，每一层再用一条穿过第一张叶片、避开第二张叶片的实际标签读出新位。此解释只描述已证明的实际子空间恒等式，不把分裂坐标当成额外旋钮。$\square$

## 50. 正性与完整整数读出的尖锐复杂度

**定理 50.1（正性查询恰为 $h+1$）。** 在已知的上述 $2^{h+1}$ 个实际原标量类承诺族中，查询可选任意实际非零标签对 $(r,s)$，回答只给

$$
\operatorname{Pos}_W(r,s)=\mathbf1[J_W(r,s)>0].
$$

精确识别未知原标量类的最坏查询数，无论自适应或非自适应，均为 $h+1$。同一结论对定理 49.1 中任意预先给定的共同最小行 $r_0$ 成立。

证明。定理 48.4 给出 $h+1$ 个固定的同一行查询 $(R_h,S_j)$，其回答为 $1-\varepsilon_j$，故上界成立；定理 49.1 给出任意给定 $r_0$ 的同一上界。

下界允许任意标签对，因而也允许自适应选择。所有 $2^{h+1}$ 个位串是不同原标量类；深度至多 $q$ 的二叉决策树至多有 $2^q$ 个叶。精确识别要求 $2^q\ge2^{h+1}$，故 $q\ge h+1$。这只是正性答案的二叉树计数，未被拿来证明完整整数模型的下界。$\square$

**引理 50.2（任意整数查询的局部三分）。** 固定上述一层 $E\subset D$、$[D:E]=5$、$M=N\oplus Ee$、$\dim_E N=2$、$\ell(e)=1$、$\ker\ell=N$，并有 $\operatorname{span}_E(NM)=D$。父中心 $A\le_{\mathbb Q}E$ 属于半维、共同完整二元函数的父承诺族。对非零标签 $r,s$ 写 $p=r^{-1}$、$q=s^{-1}$，置

$$
U=\operatorname{span}_E(1,p,q),\quad \delta=\dim_EU,\quad
T=\{x\in M:Ux\subseteq M\},\quad K=\{x\in M:Ux\subseteq N\},
$$

并令 $\rho(x)=(\ell(x),\ell(px),\ell(qx))$、$R=\rho(T)$。则

$$
J_{W(A,V)}(r,s)=n\dim_EK+\dim_{\mathbb Q}(R\cap A^3),\qquad n=[E:\mathbb Q],
$$

对 $V^\perp$ 有同样的公式配以迹正交补。其全部分支如下。

1. 若 $\delta=1$，则 $p,q\in E^\times$，两叶答案均为

$$
2n+J_A(r,s).
$$

2. 若 $\delta=2$，经交换可取 $p\notin E$、$q=a+bp$。令 $R_2=\{(\ell(x),\ell(px)):x\in M\cap p^{-1}M\}$、$\iota(A_0,B_0)=(A_0,B_0,aA_0+bB_0)$，并令 $w_A(L)=\dim_{\mathbb Q}(A^3\cap L)$。四种可能的 $(\dim_EK,\dim_ER_2)$ 与两片叶答案为

$$
\begin{array}{c|c|c}
(\kappa,\rho)_V&(\kappa,\rho)_{V^\perp}&(J_V,J_{V^\perp})\\ \hline
(1,0)&(0,2)&(n,\ w_A(\iota(E^2)))\\
(0,1)&(0,1)&(w_A(\iota(R_2)),\ w_A(\iota(R_2)))\\
(1,1)&(1,1)&(n+w_A(\iota(R_2)),\ n+w_A(\iota(R_2)))\\
(0,2)&(1,0)&(w_A(\iota(E^2)),\ n)
\end{array}
$$

这里 $R_2\le E^2$ 是二元接合像，$\iota(R_2)\le E^3$ 是相应的三元像；$a,b$ 不同时为零。写 $m=n/2$。对任意非零附着线 $L=E(c_0,c_1,c_2)$，其权重按非零坐标个数精确为

$$
w_A(L)=
\begin{cases}
m,&\text{只有一个非零坐标},\\
d_A(c_i/c_j),&\text{只有 }c_i,c_j\ne0,\\
J_A(c_0/c_1,c_0/c_2),&c_0c_1c_2\ne0.
\end{cases}
$$

前两种在父承诺族上都是整数常数，第三种才是一次父层完整 $J$ 查询。该式保留全部零坐标，包括 $a c_0+b c_1=0$ 的消去情形，绝不除以零坐标。对平面项则有

$$
\begin{aligned}
H_A:=w_A(\iota(E^2))
&=3m-\dim_{\mathbb Q}(A+aA+bA)\\
&=\begin{cases}
m+J_{A^\perp}(a^{-1},b^{-1}),&ab\ne0,\\
m+d_A(b),&a=0,\ b\ne0,\\
m+d_A(a),&b=0,\ a\ne0.
\end{cases}
\end{aligned}
$$

此处 $A^\perp$ 使用 $\operatorname{Tr}_{E/\mathbb Q}$。当 $A=W_{j-1,\eta}$ 且 $ab\ne0$ 时，非恒定项恰是 $J_{W_{j-1,\mathbf1-\eta}}(a^{-1},b^{-1})$，即逆系数标签上的一次父层查询并将全部父位取补；零系数的平面项则因共同 $d$ 而为整数常数。重复标签 $r=s$、$r=1$ 或 $s=1$ 也包含在分类中，其原定义分别给出共同的 $d_W(r)$、$d_W(s)$、$d_W(r)$。

3. 若 $\delta=3$，则 $p,q$ 生成 $D/E$。此时 $K=0$，且 $T$ 与其对偶对应至多一维；两片叶的秩对只能是 $(0,0),(1,0),(0,1)$。相应答案为

$$
(0,0),\qquad (w_A(L),0),\qquad(0,w_A(L))
$$

的某一种，其中 $L$ 是实际附着线，且即使 $L$ 与 $A^3$ 的交为零也照此取值。

证明。三重交的共同元素必须是同一个 $x$，故由 $\rho$ 的正合列得到第一式。$\delta=1$ 时 $T=M$、$K=N$，直接分解 $W(A,V)=N+eA$ 即得；对偶支同理。

$\delta=2$ 时，交换后可取 $p\notin E$、$q=a+bp$。令 $T_2=M\cap p^{-1}M$、$K_2=N\cap p^{-1}N$、$R_2=\{(\ell(x),\ell(px)):x\in T_2\}$，并写 $t=\dim_E T_2$、$\kappa=\dim_E K_2$、$\rho=\dim_E R_2=t-\kappa$。因 $D/E$ 的次数为素数五，$E(p)=D$；若 $p$ 保持一个非零真 $E$-子空间，该空间就会是 $D$-空间，矛盾。因此 $1\le t\le2$、$0\le\kappa\le1$。对偶图为 $M'=N^\perp$、$\ell'(y)=-\operatorname{Tr}_{D/E}(ey)$、$N'=M^\perp$，其二元空间满足

$$
T_2'=(N+pN)^\perp,\qquad K_2'=(M+pM)^\perp,
$$

故 $t'=1+\kappa$、$\kappa'=t-1$、$\rho'=2-\rho$。对 $x\in T_2$、$y\in T_2'$，有 $x,px\in M$ 和 $y,py\in M'$；两次原图与对偶图配对给出

$$
\ell(x)\ell'(py)=-\operatorname{Tr}_{D/E}(xpy)
=-\operatorname{Tr}_{D/E}(pxy)=\ell(px)\ell'(y).
$$

因此在 $\omega((A_0,B_0),(A_1,B_1))=A_0B_1-B_0A_1$ 下，$R_2'\subseteq R_2^{\perp_\omega}$；维数 $\rho'=2-\rho$ 给出等号。二维像于是互补，零像对应全像，一维像则为同一条线。这就逐项得到表中四行。

线权公式只需将参数 $\lambda$ 乘以一个非零的 $c_i$，把条件 $\lambda c_j\in A$ 化为同一个父元素落在相应的二重或三重交中。平面权公式则来自 $A^3\to E$ 的映射 $(A_0,B_0,C_0)\mapsto aA_0+bB_0-C_0$：核为 $A^3\cap\iota(E^2)$，像为 $A+aA+bA$。若 $ab\ne0$，像的迹正交补为 $A^\perp\cap a^{-1}A^\perp\cap b^{-1}A^\perp$，故秩—零度给出 $H_A=m+J_{A^\perp}(a^{-1},b^{-1})$。若 $a=0$，第一坐标任取于 $A$，其余条件为 $B_0\in A\cap b^{-1}A$，所以 $H_A=m+d_A(b^{-1})=m+d_A(b)$；$b=0$ 同理。这样全部零系数、轴线及重复坐标均已取其实际整数权重。

若 $\delta=3$，非零 $K$ 会把三维 $U$ 嵌入二维 $N$，不可能。若 $T$ 含两个独立向量，则 $M=xU=yU$，从而非底域标量稳定 $M$，矛盾。若两片叶都含非零 $T$，则其归一化会给 $N^\perp=zM$，即 $\operatorname{Tr}_{D/E}(zNM)=0$；但 $\operatorname{span}_E(NM)=D$ 和迹非退化性迫使 $z=0$。因此只剩列出的三种秩对。若标签取零，定义 $J(0,s)=J(r,0)=0$，不作任何逆元操作。$\square$

**定理 50.3（每个坐标子立方体的完整整数查询数恰为自由位数）。** 固定一个坐标子立方体 $Q\subseteq\{0,1\}^{h+1}$，令其自由坐标数为 $k$。允许任意实际非零标签对、任意自适应策略，并返回完整整数 $J_W(r,s)$。在上述固定承诺族及其实际好叶上，精确识别 $Q$ 中的原标量类恰需 $k$ 次查询；非自适应也达到 $k$。

证明。先由引理 50.2 作局部递归分类。任一当前查询在最新位上或者完全忽略该位，或者有一条整支取常数；剩余的一支若不常数，只是父层一次实际整数查询加一个与隐藏位无关的常数，并可能把父位串整体取补。具体地，$\delta=1$ 给出 $2n+J_{W_{j-1,\eta}}(r,s)$，忽略最新位。$\delta=2$ 的平面行在一支恒为 $n$，另一支在 $ab\ne0$ 时为 $m+J_{W_{j-1,\mathbf1-\eta}}(a^{-1},b^{-1})$，有零系数时为共同二元权重加 $m$。线行的两支完全相同：三个附着坐标均非零时为 $J_{W_{j-1,\eta}}(c_0/c_1,c_0/c_2)$ 加表中的 $0$ 或 $n$，有零坐标时为共同二元权重或 $m$ 加同一常数。$\delta=3$ 的一支恒为零，另一支按同一线权公式化为父查询或整数常数。所有父标签都是原域中的非零实际比值。全父补 $\eta\mapsto\mathbf1-\eta$ 把坐标子立方体双射到同维坐标子立方体，所以不会破坏这个描述。

由此得到单色子立方体引理：对任意已经固定的坐标条件、任意有 $k\ge1$ 个自由位的子立方体，都存在一个维数至少 $k-1$ 的坐标子立方体，使当前整数答案完全相同。按层数归纳：根只有一位，取一个端点即可；已经恒定的限制直接保留全体。最新位自由且有常数支时取该半边；最新位已固定到常数支时保留整个子立方体，固定到递归支时在父查询上归纳；最新位被忽略且自由时，父限制有自由位则归纳并保留最新位，父限制无自由位则整个限制已恒定。递归支若带全补，先取补后的父子立方体再映回原坐标；整数输出加常数不改变单色性。

现在从 $k$ 维 $Q_0$ 开始。算法每提出一个依赖此前完整整数答案的实际查询，就在当前子立方体中选择上述单色子立方体，并返回其共同的实际整数值。第 $i$ 次后仍有维数至少 $k-i$ 的子立方体，因而少于 $k$ 次时仍有两个不同位串给出完全相同的整数回答历史，不能精确识别。这个对手保留的是相同整数答案，不是把整数答案粗化成二元答案，因此不使用二叉计数。

上界由定理 48.4 的固定同一行菜单给出：对 $Q$ 中每个自由坐标只问相应的 $(R_h,S_j)$，答案 $1-\varepsilon_j$ 直接恢复该位；固定坐标无需查询。故自适应和非自适应复杂度都为 $k$。$\square$

**命题 50.4（高度一的三个整数答案）。** 取 $h=1$。选根基 $c_0=1,c_1=\alpha,c_2=\alpha^3$，并在第一层取 $N_1$ 的实际基 $u,v$。令

$$
a=c_1/c_0=\alpha,\qquad b=c_2/c_0=\alpha^3,\qquad
p=v/u,\qquad q=a+bp,
$$

并查询实际标签对 $(p^{-1},q^{-1})$。这里 $p,q\in D_1^\times$；$p\notin D_0$，且 $a,b\ne0$。四个位串的完整整数答案为

$$
J_{W_{1,\varepsilon}}(p^{-1},q^{-1})=
\begin{cases}
6,&\varepsilon_1=0,\\
3,&(\varepsilon_0,\varepsilon_1)=(0,1),\\
4,&(\varepsilon_0,\varepsilon_1)=(1,1).
\end{cases}
$$

证明。记 $E=D_0$、$D=D_1$、$e=e_1$。由 $u,v$ 是 $N_1=\langle1,\theta_1\rangle_E$ 的基，五个乘积 $u^2,uv,v^2,ue,ve$ 与幂基 $1,\theta_1,\theta_1^2,\theta_1^3,\theta_1^4$ 只差可逆基变换，因而独立。若 $x,y=px\in M_1$，则 $vx=uy$；将 $x=A u+B v+C e$、$y=A'u+B'v+C'e$ 代入，并比较这五个乘积的系数，得 $B=A'=C=C'=0$、$A=B'$。故

$$
T_2=K_2=Eu,\qquad R_2=0.
$$

这是引理 50.2 表的第一行，故原叶一支的答案恒为 $n=6$；对偶叶一支的答案为

$$
H_A=3+J_{A^\perp}(\alpha^{-1},\alpha^{-3}),
\qquad A=W_{0,\varepsilon_0}.
$$

根的手算是 $C_0\cap\alpha^{-1}C_0\cap\alpha^{-3}C_0=\mathbb Q1$，而

$$
C_0^\perp\cap\alpha^{-1}C_0^\perp\cap\alpha^{-3}C_0^\perp
=(C_0+\alpha C_0+\alpha^3C_0)^\perp=0,
$$

后一个零来自命题 48.2 的乘积张成。因此对偶叶答案为 $3+\varepsilon_0$，得到所列 $6,3,4$。这里 $p\notin E$，且 $a,b\ne0$ 使 $q=a+bp\ne0$，所以原标签及逆元均合法。答案 $3$ 或 $4$ 各自确定两位，最坏答案 $6$ 却留下根位自由，正是相同整数答案子立方体；完整整数下界不能由二元答案计数替代。$\square$

## 追加锚（本行以下为增补区）
