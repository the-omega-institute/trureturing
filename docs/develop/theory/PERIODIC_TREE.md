# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);素性位:141/141 本原(城册按类去重后天然本原);$\Psi{=}0$ 节点 12;城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## 8. 黄金连分数支：复位格点、镜面收缩与层际交换缺陷

### 8.1 黄金支、Fibonacci 矩阵与返回映射

**定义。** 令

$$
\alpha=\frac{\sqrt5-1}{2},\qquad \varphi=1+\alpha,
\qquad \psi=-\alpha,
$$

并令 $(F_n)_{n\ge0}$ 为满足 $F_0=0$、$F_1=1$、
$F_{n+2}=F_{n+1}+F_n$ 的 Fibonacci 数列。对 $L\in\mathbb N$，定义

$$
A_L=F_{L+3},\quad B_L=F_{L+2},\quad C_L=F_{L+1},\quad
M_L=\begin{pmatrix}A_L&B_L\\B_L&C_L\end{pmatrix},
$$

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
d_L=\psi^{L+2},\qquad \delta_L=|d_L|.
$$

**定理。** 上述数满足

$$
\alpha^2+\alpha=1,\qquad 0<\alpha<1,\qquad
M_L=Q^{L+2},\qquad \delta_L=\alpha^{L+2},
$$

以及 Cassini 行列式恒等式

$$
\boxed{\det M_L=A_LC_L-B_L^2=(-1)^L.}
$$

因此 $M_L\in GL_2(\mathbb Z)$；$L$ 为偶数时 $M_L\in SL_2(\mathbb Z)$，
$L$ 为奇数时 $M_L$ 反转定向。

**证明。** $\alpha$ 的等式由定义平方后化简得到，且正根的取值给出
$0<\alpha<1$。矩阵幂公式由 Fibonacci 递推归纳得到。对该公式取行列式，
并用 $\det Q=-1$，即得 $\det M_L=(-1)^{L+2}=(-1)^L$。
最后 $|\psi|=\alpha$ 给出 $\delta_L=\alpha^{L+2}$。

**定义。** 对 $m\in\mathbb Z$，定义黄金返回映射

$$
T_L(m)=A_Lm+B_L\lfloor m\alpha\rfloor.
$$

**定理。** 对每个 $L\in\mathbb N$ 与 $m\in\mathbb Z$，

$$
\boxed{T_L(m)=B_L\lfloor m\varphi\rfloor+C_Lm.}
$$

**证明。** 因为 $\varphi=1+\alpha$ 且 $m$ 为整数，
$\lfloor m\varphi\rfloor=m+\lfloor m\alpha\rfloor$。
再用 $A_L=B_L+C_L$ 展开右端即可。

### 8.2 全整数格点与定向相位窗口

**定理。** 若 $m,k\in\mathbb Z$ 且

$$
\binom e h=M_L\binom m k,
$$

则

$$
\boxed{e\alpha-h=d_L(m\alpha-k).}\tag{GC1}
$$

并且整数逆映射为

$$
\boxed{
m=(-1)^L(C_Le-B_Lh),\qquad
k=(-1)^L(A_Lh-B_Le).
}\tag{GC2}
$$

**证明。** Fibonacci 与黄金共轭恒等式给出

$$
B_L\alpha-C_L=-d_L,\qquad
A_L\alpha-B_L=\alpha d_L.
$$

将 $e=A_Lm+B_Lk$、$h=B_Lm+C_Lk$ 代入并合并系数，得到 GC1。
对 $M_L$ 使用上一节的伴随矩阵公式和
$A_LC_L-B_L^2=(-1)^L$，得到 GC2。

**定义。** 对 $e\in\mathbb Z$，定义定向相位窗口事件

$$
\operatorname{Hits}_L(e)
\iff \exists h\in\mathbb Z:\quad
0<\frac{e\alpha-h}{d_L}<1.
$$

**定理。** 对全部 $L\in\mathbb N$ 与 $e\in\mathbb Z$，相位窗口恰好等价于
非零 Beatty 返回：

$$
\boxed{
\operatorname{Hits}_L(e)
\iff \exists m\in\mathbb Z\setminus\{0\}:\ e=T_L(m).
}\tag{GC3}
$$

**证明。** 若 $e=T_L(m)$ 且 $m\ne0$，取
$k=\lfloor m\alpha\rfloor$ 及
$h=B_Lm+C_Lk$。数 $m\alpha$ 不是整数，故
$0<m\alpha-k<1$；GC1 随即给出窗口不等式。
反之，由窗口中的 $e,h$ 按 GC2 恢复 $m,k\in\mathbb Z$。
GC1 把窗口不等式化为 $0<m\alpha-k<1$，所以
$k=\lfloor m\alpha\rfloor$。若 $m=0$，则该不等式要求整数 $k$
严格位于 $(-1,0)$，矛盾；故 $m\ne0$，并且 $e=T_L(m)$。

### 8.3 任意分辨率的收缩与非周期性

**定理。** 对每个 $L\in\mathbb N$，

$$
\boxed{d_{L+1}=-\alpha d_L,\qquad d_{L+2}=\alpha^2d_L.}\tag{GC4}
$$

若 $r\in\mathbb N$ 且 $r>0$，定义
$D_{L,r}=d_L-d_{L+r}$，则

$$
\boxed{D_{L,r}\ne0,\qquad D_{L+1,r}=-\alpha D_{L,r}.}\tag{GC5}
$$

**证明。** 由 $d_L=(-\alpha)^{L+2}$ 直接得到 GC4 及第二个等式。
又有
$|d_{L+r}|=|d_L|\alpha^r<|d_L|$，所以 $d_L\ne d_{L+r}$，
即 $D_{L,r}\ne0$。

**定理。** 对每个 $p\in\mathbb Z$，

$$
\boxed{p\ne0\Longrightarrow p\alpha\notin\mathbb Z.}\tag{GC6}
$$

因此旋转 $x\mapsto x+\alpha\pmod1$ 不存在非零整数回归周期。

**证明。** 若 $p\ne0$ 且 $p\alpha=q\in\mathbb Z$，则
$\alpha=q/p\in\mathbb Q$，这与 $\sqrt5$ 的无理性矛盾。

### 8.4 接缝端点与跨层覆盖

**定义。** 给定 $e,h\in\mathbb Z$，令

$$
u=\frac{e\alpha-h}{d_L}.
$$

**定理。** 上述 $u$ 满足跨层恒等式

$$
\boxed{
\frac{e\alpha-h}{d_{L+2}}=\frac{u}{\alpha^2},\qquad
\frac{(e+B_L)\alpha-(h+C_L)}{d_{L+1}}
=\frac{1-u}{\alpha}.
}\tag{GC7}
$$

**证明。** 第一式来自 $d_{L+2}=\alpha^2d_L$。第二式使用
$B_L\alpha-C_L=-d_L$ 与 $d_{L+1}=-\alpha d_L$，直接化简即可。

**定理。** 若 $u=\alpha^2$，则接缝唯一落在负返回时刻：

$$
\boxed{e=-F_{L+4}=T_L(-1).}\tag{GC8}
$$

同时 $h=-F_{L+3}$。

**证明。** 将 $u=\alpha^2$ 代入定义，并用 Fibonacci 黄金误差恒等式化简，得到

$$
(e+F_{L+4})\alpha=h+F_{L+3}.
$$

$\alpha$ 无理，故等式两侧的整数系数分别为零，从而得到 $e,h$ 的值。
又因 $\lfloor-\alpha\rfloor=-1$，

$$
T_L(-1)=-A_L-B_L=-F_{L+4}.
$$

**定理。** 对每个 $e\in\mathbb Z$ 且 $e\ne-F_{L+4}$，有接缝外的分辨率覆盖

$$
\boxed{
\operatorname{Hits}_L(e)
\iff\operatorname{Hits}_{L+2}(e)
\ \lor\ \operatorname{Hits}_{L+1}(e+B_L).
}\tag{GC9}
$$

特别地，该等价式对每个 $e\ge0$ 成立。

**证明。** 取 $\operatorname{Hits}_L(e)$ 的见证 $h$ 及其参数 $u\in(0,1)$。
若 $u<\alpha^2$，GC7 第一式给出 $\operatorname{Hits}_{L+2}(e)$；
若 $u>\alpha^2$，GC7 第二式给出
$\operatorname{Hits}_{L+1}(e+B_L)$。等号情形由 GC8 恰为被排除的
$e=-F_{L+4}$。反向地，第一种窗口经 $u=\alpha^2v$ 回到
$u\in(0,\alpha^2)$；第二种窗口经 $u=1-\alpha v$ 回到
$u\in(\alpha^2,1)$。因此两者都推出 $\operatorname{Hits}_L(e)$。
最后 $F_{L+4}>0$，所以 $e\ge0$ 自动避开接缝。

### 8.5 嵌套返回的组合与定向进位

**定义。** 令

$$
c_L=\begin{cases}0,&d_L>0,\\1,&d_L<0.\end{cases}
$$

**命题。** $c_0=0$、$c_{L+1}=1-c_L$；等价地，$L$ 为偶数时
$c_L=0$，$L$ 为奇数时 $c_L=1$。

**证明。** $d_L=(-\alpha)^{L+2}\ne0$，且相邻两层符号相反。

**定理。** 对每个 $m\in\mathbb Z\setminus\{0\}$，

$$
\boxed{
\lfloor T_L(m)\alpha\rfloor
=B_Lm+C_L\lfloor m\alpha\rfloor-c_L.
}\tag{GC10}
$$

**证明。** 令 $k=\lfloor m\alpha\rfloor$。GC1 给出

$$
T_L(m)\alpha-(B_Lm+C_Lk)=d_L(m\alpha-k).
$$

无理性保证 $0<m\alpha-k<1$。若 $d_L>0$，右端严格位于 $(0,1)$；
若 $d_L<0$，右端严格位于 $(-1,0)$。分别取整即得所述修正项。

**定理。** 完整格点变换满足

$$
\boxed{M_KM_L=M_{K+L+2}.}
$$

**证明。** 由 $M_J=Q^{J+2}$，有
$M_KM_L=Q^{K+2}Q^{L+2}=Q^{K+L+4}=M_{K+L+2}$。

**定理。** 对 $m\in\mathbb Z\setminus\{0\}$，嵌套返回满足

$$
\boxed{
T_K(T_L(m))=T_{K+L+2}(m)-B_Kc_L.
}\tag{GC11}
$$

因而

$$
\boxed{
T_K(T_L(m))-T_L(T_K(m))=B_Lc_K-B_Kc_L.
}\tag{GC12}
$$

**证明。** 将 GC10 给出的
$\lfloor T_L(m)\alpha\rfloor$ 代入 $T_K(T_L(m))$，再使用
$M_KM_L=M_{K+L+2}$，得到 GC11。交换 $K,L$ 后两式相减，得到 GC12。

**命题。** GC12 的右端与非零输入 $m$ 无关。两层均为偶数时返回映射交换；
一奇一偶时缺陷非零；两层均为奇数时缺陷为 $B_L-B_K$。
此外 $T_L(0)=0$，但 GC11 的公式不把 $m=0$ 包含在内。

**证明。** 将 $c_J=0$ 或 $1$ 代入 GC12 即得前三项。
$B_J=F_{J+2}>0$ 给出一奇一偶时的非零性。最后由定义直接得到 $T_L(0)=0$。

### 8.6 区间 Fourier 积分的反射与平移

**定义。** 固定实数 $\omega\ne0$。对 $a,b\in\mathbb R$，采用负指数和定向积分约定，定义

$$
\mathcal F_\omega(a,b)=\int_a^b e^{-i\omega x}\,dx.
$$

**定理。** 对所有 $a,b,t\in\mathbb R$，

$$
\boxed{
\mathcal F_\omega(-b,-a)=\overline{\mathcal F_\omega(a,b)},\qquad
|\mathcal F_\omega(-b,-a)|^2=|\mathcal F_\omega(a,b)|^2,
}\tag{GC13}
$$

并且

$$
\boxed{
\mathcal F_\omega(a+t,b+t)
=e^{-i\omega t}\mathcal F_\omega(a,b).
}
$$

**证明。** 当 $\omega\ne0$ 时，端点公式为

$$
\mathcal F_\omega(a,b)=\frac{e^{-i\omega b}-e^{-i\omega a}}{-i\omega}.
$$

把 $(a,b)$ 换成 $(-b,-a)$，并用
$\overline{e^{-i\theta}}=e^{i\theta}$，得到反射取共轭；取模平方得到功率相等。
把端点同时平移 $t$，公因子 $e^{-i\omega t}$ 提出后得到平移公式。

**定义。** 对 $z,w\in\mathbb C$ 定义交叉系数
$\mathcal C(z,w)=z\overline w$。令

$$
z_t=e^{-i\omega t}z,\qquad w_t=e^{-i\omega t}w,\qquad
z^{\mathrm{mir}}=\overline z,\qquad w^{\mathrm{mir}}=\overline w.
$$

**定理。** 共同平移不改变交叉系数，共同反射则使它取共轭；特别地，

$$
\boxed{
\mathcal C(z_t,w_t)=\mathcal C(z,w),\qquad
\operatorname{Im}\mathcal C(z^{\mathrm{mir}},w^{\mathrm{mir}})
=-\operatorname{Im}\mathcal C(z,w).
}\tag{GC14}
$$

**证明。** 直接计算得
$z_t\overline{w_t}=e^{-i\omega t}z\,e^{i\omega t}\overline w=z\overline w$，
而
$\mathcal C(\overline z,\overline w)=\overline z\,w
=\overline{z\overline w}$。取虚部即得第二式。

**命题。** 若 $\mathcal C(z,w)$ 为零或实数，则共同反射前后的交叉系数虚部都为零。

**证明。** 实数等于自身的共轭，且实数的虚部为零；零是其实例。

### 8.7 有限载体与 Fibonacci 窗口

**定义。** 令

$$
R=\{0,1,2,3,4\}\times\{0,1,2\}\times\{0,1\}\times\{0,1\},
$$

$$
W_n=\{0,1\}^n,
\qquad
X_n=\{w\in W_n: w_jw_{j+1}=0\text{ 对所有 }1\le j<n\}.
$$

**命题。** 有

$$
|R|=60,\qquad |W_6|=64,\qquad |X_6|=21,\qquad
|W_6\setminus X_6|=43.
$$

此外 $|X_7|=34$、$|X_8|=55$，所以
$|X_8|-|X_6|=34\ne43$。

**证明。** 前两个基数由有限集合乘法原则得到。
令 $x_n=|X_n|$。按末位为 $0$ 或 $1$ 分拆合法字，得到
$x_n=x_{n-1}+x_{n-2}$，且 $x_1=2$、$x_2=3$。
递推给出 $x_6=21$、$x_7=34$、$x_8=55$，其余等式随即成立。

**定理。** 映射

$$
\rho(x,y,z,w)=12x+4y+2z+w
$$

是 $R$ 到 $\{0,1,\ldots,59\}$ 的双射。把值写成六位二进制时，
$W_6$ 中恰有 $60,61,62,63$ 四个码不在像中。

**证明。** 对 $r\in\{0,\ldots,59\}$，依次令

$$
w=r\bmod2,\qquad
z=\lfloor r/2\rfloor\bmod2,\qquad
y=\lfloor r/4\rfloor\bmod3,\qquad
x=\lfloor r/12\rfloor.
$$

这些值属于 $R$ 的相应因子，连续使用带余除法可恢复
$r=12x+4y+2z+w$，且恢复唯一。六位二进制编码覆盖 $0$ 至 $63$，
故像的补集恰为所列四个码。

### 8.8 不同分辨率中心的共同反射阻碍

**定义。** 第 $L$ 层有符号区间的中心记为

$$
\mu_L=\frac{d_L}{2}.
$$

**定理。** 若 $r\in\mathbb N$ 且 $r>0$，则不存在 $t\in\mathbb R$ 同时满足

$$
\mu_L+t=-\mu_L,\qquad
\mu_{L+r}+t=-\mu_{L+r}.
$$

**证明。** 两式分别给出 $t=-d_L$ 与 $t=-d_{L+r}$，从而要求
$D_{L,r}=d_L-d_{L+r}=0$，这与 GC5 矛盾。

**定理。** 若 $\omega\ne0$，且 $r\in\mathbb N$、$r>0$，则未取模的几何相位差

$$
\Theta_{L,r}=-\frac{\omega}{2}(d_L-d_{L+r})
$$

满足

$$
\boxed{\Theta_{L,r}\ne0,\qquad
\Theta_{L+1,r}=-\alpha\Theta_{L,r}.}
$$

**证明。** 非零性由 $\omega\ne0$ 与 GC5 得到；递推式由
$D_{L+1,r}=-\alpha D_{L,r}$ 得到。

**命题。** 对实数 $\theta$，条件 $\theta\ne0$ 本身不推出
$e^{i\theta}\ne1$。

**证明。** 取 $\theta=2\pi$，则 $\theta\ne0$，但
$e^{i\theta}=e^{2\pi i}=1$。

### 8.9 有限基数与黄金回归的分离

**命题。** 整数 $60$ 与 $64$ 都不是黄金旋转
$x\mapsto x+\alpha\pmod1$ 的回归周期。

**证明。** 两数均非零，故 GC6 分别给出
$60\alpha\notin\mathbb Z$ 与 $64\alpha\notin\mathbb Z$。

**命题。** 六位二进制字中不满足无相邻 $1$ 条件的字数为 $43$，
而 $|X_7|=|X_8|-|X_6|=34$；这两个计数不相等。

**证明。** 由 8.7 的递推计数，二者之差为 $43-34=9\ne0$。

---

## 9. 整数纤维、截面依赖与规范双面的乘法作用

### 9.1 黄金整数及其两个实嵌入

**定义。** 令

$$
\mathcal O=\mathbb Z[\varphi]
=\{a+b\varphi:a,b\in\mathbb Z\},
\qquad \varphi^2=\varphi+1.
$$

对 $z=a+b\varphi\in\mathcal O$，定义两个实嵌入及整数坐标读出

$$
z_+=a+b\varphi,
\qquad z_*=a+b\psi,
\qquad \pi(z)=b,
$$

其中 $\psi=-\alpha$ 且 $\psi^2=\psi+1$。

**定理。** 两个嵌入都保持加法与乘法，并且

$$
\boxed{z_+-z_*=\sqrt5\,\pi(z).}
$$

**证明。** 加法保持性直接来自坐标相加。因为 $\varphi$ 与 $\psi$
都满足 $x^2=x+1$，按该关系展开两个乘积即可得到乘法保持性。
又有 $\varphi-\psi=1+2\alpha=\sqrt5$，故
$z_+-z_*=b(\varphi-\psi)=\sqrt5\,b$。

### 9.2 完整整数纤维与乘法不下降

**定理。** 对每个 $n\in\mathbb Z$，完整纤维为

$$
\boxed{\pi^{-1}(n)=\{k+n\varphi:k\in\mathbb Z\}.}\tag{GS1}
$$

此外，$\pi(x)=\pi(y)$ 当且仅当存在 $k\in\mathbb Z$ 使 $y=x+k$。

**证明。** 写 $z=a+b\varphi$，则 $\pi(z)=n$ 等价于 $b=n$，
此时且仅此时 $z=a+n\varphi$。对 $x,y$ 应用同一坐标比较即得后一结论。

**定理。** 令 $u=c+d\varphi\in\mathcal O$。对任意 $k,n\in\mathbb Z$，

$$
\pi\bigl(u(k+n\varphi)\bigr)=(c+d)n+dk.
$$

并且乘法在整数纤维上下降为单值映射的充要条件是 $u$ 为普通整数：

$$
\boxed{
\exists f:\mathbb Z\to\mathbb Z\ \forall z\in\mathcal O,
\quad \pi(uz)=f(\pi z)
\quad\Longleftrightarrow\quad d=0.
}\tag{GS2}
$$

**证明。** 展开
$u(k+n\varphi)$ 并使用 $\varphi^2=\varphi+1$，其 $\varphi$ 坐标即为
$(c+d)n+dk$。若 $d=0$，取 $f(n)=cn$ 即可。反之，$0$ 与 $1$
同属零纤维，而其乘积读出分别为 $0$ 与 $d$；单值性强制 $d=0$。

**定理。** 若 $d\ne0$，则对每个固定的 $n$，映射

$$
k\longmapsto\pi\bigl(u(k+n\varphi)\bigr)
$$

是单射，因此每个纤维产生无限多个不同的一步输出。此时联合读出

$$
\boxed{z\longmapsto(\pi z,\pi(uz))\text{ 是单射}.}\tag{GS3}
$$

**证明。** 固定 $n$ 后，输出是斜率为非零整数 $d$ 的仿射函数，故对
$k$ 单射。若联合读出相等，第一坐标先确定相同的 $n$，第二坐标再由该单射
确定相同的 $k$；GS1 遂给出相同的 $z$。

### 9.3 任意截面的进位与复合缺陷

**定义。** 对 $\rho\in\mathbb R$ 与 $n\in\mathbb Z$，定义

$$
q_\rho(n)=\lfloor n\alpha+\rho\rfloor,
\qquad s_\rho(n)=q_\rho(n)+n\varphi,
\qquad r_\rho(n)=n\alpha-q_\rho(n).
$$

若 $u=a_u+b_u\varphi$，再定义

$$
P_u^\rho(n)=\pi(u s_\rho(n)),
$$

并在写成 $u s_\rho(n)=A+P_u^\rho(n)\varphi$ 后定义

$$
c_u^\rho(n)=q_\rho(P_u^\rho(n))-A.
$$

**命题。** $s_\rho$ 是 $\pi$ 的一个截面，并且

$$
\pi(s_\rho(n))=n,
\qquad -\rho\le r_\rho(n)<1-\rho,
\qquad (s_\rho(n))_*=-r_\rho(n).
$$

**证明。** 第一式由 $s_\rho(n)$ 的 $\varphi$ 坐标得到。
取整的基本界给出第二式，而
$q_\rho(n)+n\psi=q_\rho(n)-n\alpha=-r_\rho(n)$ 给出第三式。

**定理。** 对任意 $u\in\mathcal O$、$\rho\in\mathbb R$ 与
$n\in\mathbb Z$，截面进位满足

$$
\boxed{
c_u^\rho(n)=\lfloor u_*r_\rho(n)+\rho\rfloor,
\qquad
s_\rho(P_u^\rho(n))=u s_\rho(n)+c_u^\rho(n).
}\tag{GS4}
$$

**证明。** 写 $u s_\rho(n)=A+P\varphi$，其中 $P=P_u^\rho(n)$。
取内部嵌入并用 $(s_\rho(n))_*=-r_\rho(n)$，得到
$A-P\alpha=-u_*r_\rho(n)$，即 $P\alpha=A+u_*r_\rho(n)$。
因此

$$
c_u^\rho(n)=\lfloor P\alpha+\rho\rfloor-A
=\lfloor u_*r_\rho(n)+\rho\rfloor.
$$

第二式比较整数坐标与 $\varphi$ 坐标即可。

**定理。** 对所有 $u,v\in\mathcal O$、$\rho\in\mathbb R$ 与
$n\in\mathbb Z$，

$$
\boxed{
P_u^\rho(P_v^\rho(n))
=P_{uv}^\rho(n)+b_u c_v^\rho(n),
}\tag{GS5}
$$

$$
\boxed{
P_u^\rho(P_v^\rho(n))-P_v^\rho(P_u^\rho(n))
=b_u c_v^\rho(n)-b_v c_u^\rho(n).
}\tag{GS6}
$$

**证明。** 由 GS4，
$s_\rho(P_v^\rho(n))=v s_\rho(n)+c_v^\rho(n)$。
两边乘以 $u$ 后取 $\varphi$ 坐标，注意普通整数
$c_v^\rho(n)$ 乘以 $u$ 所贡献的 $\varphi$ 坐标为
$b_uc_v^\rho(n)$，便得到 GS5。交换 $u,v$，再用 $uv=vu$ 相减，得到 GS6。

### 9.4 中心截面的乘法不变性

**定理。** 对每个 $n\in\mathbb Z$，

$$
|r_{1/2}(n)|<\frac12.
$$

若 $u\in\mathcal O$ 且 $|u_*|\le1$，则

$$
\boxed{
c_u^{1/2}(n)=0,
\qquad
s_{1/2}(P_u^{1/2}(n))=u s_{1/2}(n).
}\tag{GS7}
$$

**证明。** 取整界先给出 $|r_{1/2}(n)|\le1/2$。
若出现端点，则 $n\alpha$ 为半整数；当 $n\ne0$ 时这与 $\alpha$ 无理矛盾，
而 $n=0$ 时 $r_{1/2}(0)=0$。故不等式严格。
于是 $|u_*r_{1/2}(n)|<1/2$，从而
$u_*r_{1/2}(n)+1/2\in(0,1)$。GS4 的取整公式给出进位为零，
再由 GS4 的第二式得到截面不变性。

**定理。** 集合

$$
\mathcal C=\{u\in\mathcal O:|u_*|\le1\}
$$

对乘法闭合。若 $u_1,\ldots,u_t\in\mathcal C$，则

$$
\boxed{
P_{u_1}^{1/2}\cdots P_{u_t}^{1/2}(n)
=P_{u_1\cdots u_t}^{1/2}(n).
}\tag{GS8}
$$

特别地，这些投影映射两两交换。

**证明。** 乘法嵌入给出
$(uv)_*=u_*v_*$，所以 $|u_*|,|v_*|\le1$ 推出 $|(uv)_*|\le1$。
对字长归纳，并在每一步使用 GS7，即得 GS8。环乘法交换律再给出投影映射的交换性。

### 9.5 全部分辨率共同不变窗口的锐利范围

**定义。** 对 $0\le\rho\le1$，令

$$
W_\rho=[-\rho,1-\rho]\subset\mathbb R.
$$

**定理。** 对 $d_L=\psi^{L+2}$，全部分辨率共同保持 $W_\rho$ 的充要条件是

$$
\boxed{
\forall L\in\mathbb N,\ d_LW_\rho\subseteq W_\rho
\quad\Longleftrightarrow\quad
\frac{1-\alpha}{2}\le\rho\le\frac{1+\alpha}{2}.
}\tag{GS9}
$$

若 $\rho$ 超出该闭区间，则 $L=1$ 的负收缩已经不保持 $W_\rho$。

**证明。** 每个正向 $d_L$ 都是不超过 $\alpha^2$ 的正收缩，因而保持
包含零的 $W_\rho$。对 $q>0$，负收缩 $-q$ 的像为

$$
[-q(1-\rho),q\rho],
$$

故它包含于 $W_\rho$ 当且仅当

$$
q(1-\rho)\le\rho,
\qquad q\rho\le1-\rho.
$$

最大的负向绝对值出现在 $L=1$，此时 $q=\alpha^3$；其余负向层再乘
$\alpha^2$，所以只需检验这一层。代入 $q=\alpha^3=2\alpha-1$，
两条不等式分别化为
$\rho\ge(1-\alpha)/2$ 与 $\rho\le(1+\alpha)/2$。
超出范围时，相应端点在 $L=1$ 即越出窗口。

### 9.6 规范黄金截面与返回锚定

**定义。** 对 $n\in\mathbb N$，令

$$
S(n)=\lfloor(n+1)\varphi\rfloor-1,
\qquad
\beta_{\mathbb R}(n)=S(n)-n\psi,
$$

并定义规范黄金整数

$$
\beta_{\mathrm G}(n)=(S(n)-n)+n\varphi\in\mathcal O.
$$

**定理。** 规范黄金整数恰好是偏移为 $\alpha$ 的截面：

$$
\boxed{
\beta_{\mathrm G}(n)=s_\alpha(n)
=\lfloor(n+1)\alpha\rfloor+n\varphi.
}\tag{GS10}
$$

其正实嵌入为 $\beta_{\mathbb R}(n)$，内部实嵌入为
$(\beta_{\mathrm G}(n))_*$。

**证明。** 因为 $\varphi=1+\alpha$，

$$
S(n)=n+\lfloor(n+1)\alpha\rfloor.
$$

代回定义便得到 GS10。正实嵌入满足

$$
(S(n)-n)+n\varphi=S(n)+n\alpha=S(n)-n\psi
=\beta_{\mathbb R}(n),
$$

内部嵌入则由定义直接得到。

**定义。** 对 $L\in\mathbb N$，令

$$
u_L=\varphi^{L+2},
\qquad U_L(n)=P_{u_L}^{\alpha}(n)\quad(n\in\mathbb Z).
$$

**定理。** 对每个 $L$ 与 $n\in\mathbb Z$，规范截面的进位为零，且

$$
s_\alpha(U_L(n))=u_Ls_\alpha(n).
$$

因此

$$
\boxed{U_K(U_L(n))=U_{K+L+2}(n).}\tag{GS11}
$$

若 $n\in\mathbb N$，则 $U_L(n)\ge0$，并且把该输出视为自然数时，

$$
\boxed{
\beta_{\mathrm G}(U_L(n))
=\varphi^{L+2}\beta_{\mathrm G}(n).
}\tag{GS12}
$$

**证明。** 由取整界，
$r_\alpha(n)\in[-\alpha,1-\alpha)$。将该半开区间乘以
$d_L=(u_L)_*$；利用 $|d_L|<1$、符号交替及无理性排除可能的整数端点，得到

$$
0\le d_Lr_\alpha(n)+\alpha<1.
$$

GS4 因而给出零进位与截面不变性。又因
$u_Ku_L=u_{K+L+2}$，连续应用截面不变性并取 $\pi$，得到 GS11。
对自然数 $n$，$s_\alpha(n)$ 的两个整数坐标非负，而
$u_L=F_{L+1}+F_{L+2}\varphi$ 的两个坐标也非负，故乘积的
$\varphi$ 坐标 $U_L(n)$ 非负。最后结合 GS10 与截面不变性得到 GS12。

**定理。** 第 8 节的返回映射与规范尺度映射满足锚定关系

$$
\boxed{T_L(m)=A_L+U_L(m-1),\qquad m\in\mathbb Z.}\tag{GS13}
$$

**证明。** 由
$u_L=F_{L+1}+F_{L+2}\varphi=C_L+B_L\varphi$，且

$$
q_\alpha(m-1)=\lfloor m\alpha\rfloor,
$$

展开 $u_Ls_\alpha(m-1)$ 的 $\varphi$ 坐标，得到

$$
U_L(m-1)=A_L(m-1)+B_L\lfloor m\alpha\rfloor
=T_L(m)-A_L.
$$

移项即得 GS13。

### 9.7 加法截面的乘法不变性阻碍

**定理。** 设 $s:\mathbb Z\to\mathcal O$ 是加法同态，且

$$
\pi(s(n))=n\qquad(n\in\mathbb Z).
$$

若 $u=c+d\varphi$ 且 $d\ne0$，则

$$
\boxed{
\neg\,\forall n\in\mathbb Z,
\quad u s(n)=s(\pi(u s(n))).
}\tag{GS14}
$$

**证明。** 由截面条件可写 $s(1)=a+\varphi$，其中 $a\in\mathbb Z$。
加法性给出 $s(n)=n(a+\varphi)$。若所述不变性成立，将 $n=1$ 代入，
并比较 $u(a+\varphi)$ 与 $s(\pi(u(a+\varphi)))$ 的两个整数坐标，得到

$$
d(a^2+a-1)=0.
$$

因 $d\ne0$，必有 $a(a+1)=1$；但两个相邻整数之积为偶数，不可能等于
$1$，矛盾。

### 9.8 返回映射与规范尺度不存在共同单射共轭

**定理。** 若 $B_Lc_K-B_Kc_L\ne0$，则不存在单射
$f:\mathbb Z\to\mathbb Z$ 同时满足

$$
f\circ T_K=U_K\circ f,
\qquad
f\circ T_L=U_L\circ f.
$$

**证明。** GS11 给出 $U_KU_L=U_LU_K$。若这样的 $f$ 存在，
则对任意非零 $m$，连续使用两条交织关系得到

$$
f(T_K(T_L(m)))=U_K(U_L(f(m)))
=U_L(U_K(f(m)))=f(T_L(T_K(m))).
$$

$f$ 的单射性迫使 $T_K(T_L(m))=T_L(T_K(m))$，
这与 GC12 及 $B_Lc_K-B_Kc_L\ne0$ 矛盾。

### 9.9 三种截面性质的分离

**定理。** 设 $u=c+d\varphi\in\mathcal O$ 满足 $d\ne0$ 且
$|u_*|\le1$。则下列三项同时成立：乘法 $z\mapsto uz$ 不下降为完整
$\pi$-纤维上的单值映射；中心截面 $s_{1/2}(\mathbb Z)$ 在该乘法下不变；
不存在既为加法同态又在该乘法下不变的 $\pi$-截面。

**证明。** 第一项由 GS2 与 $d\ne0$ 得到，第二项由 GS7 与
$|u_*|\le1$ 得到，第三项由 GS14 得到。
## 附录 T：WSS 的素数下标迹障碍与幂复合多项式

### T.1 黄金整数环、迹与范数

**定义。** 令

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad \psi=1-\varphi=\frac{1-\sqrt5}{2},
\qquad \mathcal O=\mathbb Z[\varphi].
$$

对 $z=a+b\varphi\in\mathcal O$，定义

$$
\overline z=a+b\psi,
\qquad \operatorname{Tr}(z)=z+\overline z,
\qquad \operatorname N(z)=z\overline z.
$$

**定义。** Lucas 数与 Fibonacci 数分别由

$$
L_n=\varphi^n+\psi^n,
\qquad
F_n=\frac{\varphi^n-\psi^n}{\sqrt5}
$$

定义。

**定理。** 对每个 $n\in\mathbb N$，

$$
\varphi^2=\varphi+1,
\qquad \varphi\psi=-1,
\qquad \operatorname N(\varphi^n)=(-1)^n.
$$

**证明。** 前两式由 $\varphi=(1+\sqrt5)/2$ 与
$\psi=(1-\sqrt5)/2$ 直接计算得到。由范数的乘法性，

$$
\operatorname N(\varphi^n)
=(\varphi\psi)^n=(-1)^n.
$$

### T.2 幂复合多项式与整数环指数

**定义。** 对 $n\in\mathbb N$，定义

$$
\mathcal P_n(X)=X^{2n}-X^n-1,
\qquad E_n=\mathcal P_n(\varphi)\in\mathcal O.
$$

**定义。** 设 $p$ 为奇素数，$\theta_p$ 是 $\mathcal P_p$ 的一个根，
$K_p=\mathbb Q(\theta_p)$，而 $\mathcal O_{K_p}$ 是 $K_p$ 的整数环。
当 $\mathcal P_p$ 是 $\theta_p$ 的最小多项式时，定义指定幂基的指数为

$$
I_p=[\mathcal O_{K_p}:\mathbb Z[\theta_p]].
$$

指定幂基是整数环的整基，依定义即为 $I_p=1$。

**定理。** 对每个奇素数 $p$，

$$
\operatorname{disc}(\mathcal P_p)=p^{2p}5^p.
$$

若 $\mathcal P_p$ 是 $\theta_p$ 的最小多项式，则

$$
\operatorname{disc}(\mathcal P_p)
=I_p^2\operatorname{disc}(K_p).
$$

**证明。** 导数为

$$
\mathcal P_p'(X)=pX^{p-1}(2X^p-1).
$$

以 $Y=X^p$ 计算两个结果式，得到

$$
\operatorname{Res}(\mathcal P_p,X^{p-1})=1,
\qquad
\operatorname{Res}(\mathcal P_p,2X^p-1)=-5^p.
$$

由于 $\deg\mathcal P_p=2p$ 且 $p$ 为奇数，判别式与结果式的符号相消，
从而得到第一式。第二式是基变换的判别式公式：
$\mathbb Z[\theta_p]$ 到 $\mathcal O_{K_p}$ 的基变换行列式绝对值为 $I_p$，
而判别式在基变换下乘以该行列式的平方。

### T.3 奇数下标的迹恒等式

**定理。** 对每个奇数 $n$，

$$
\boxed{E_n=(L_n-1)\varphi^n.}\tag{T1}
$$

**证明。** 每个二次元素 $x\in\mathcal O$ 满足

$$
x^2-\operatorname{Tr}(x)x+\operatorname N(x)=0,
$$

因为左端展开为
$x^2-(x+\overline x)x+x\overline x=0$。取 $x=\varphi^n$。
此时 $\operatorname{Tr}(x)=L_n$；又因 $n$ 为奇数，
$\operatorname N(x)=-1$。因此

$$
E_n=x^2-x-1=(\operatorname{Tr}(x)-1)x
=(L_n-1)\varphi^n.
$$

### T.4 标量整除、模同余与范数

**定理。** 对每个奇数 $n$ 与每个整数 $q$，

$$
\boxed{q\mid E_n\text{ 于 }\mathcal O
\iff q\mid L_n-1\text{ 于 }\mathbb Z.}\tag{T2}
$$

这包括复合整数 $q$ 及 $q=0$。

**证明。** 令 $x=\varphi^n$。由
$x\overline x=-1$ 可知 $x^{-1}=-\overline x\in\mathcal O$。
若 $E_n=qy$，则 T1 给出

$$
L_n-1=qyx^{-1}.
$$

写 $yx^{-1}=a+b\varphi$。比较 $\{1,\varphi\}$ 中的整数坐标可得
$b=0$ 及 $L_n-1=qa$。反之，若 $L_n-1=qa$，则
$E_n=q(a\varphi^n)$。上述论证也适用于 $q=0$。

**定理。** 对每个奇数 $n$ 与每个自然数 $q$，

$$
\boxed{E_n\equiv0\pmod q\text{ 于 }\mathcal O
\iff L_n\equiv1\pmod q\text{ 于 }\mathbb Z.}\tag{T3}
$$

**证明。** 两个同余分别等价于 $q\mid E_n$ 于 $\mathcal O$ 与
$q\mid L_n-1$ 于 $\mathbb Z$，故结论由 T2 得到。

**定理。** 对每个奇数 $n$，

$$
\boxed{\operatorname N(E_n)=-(L_n-1)^2.}\tag{T4}
$$

**证明。** 由 T1、范数的乘法性及
$\operatorname N(\varphi^n)=-1$，有

$$
\operatorname N(E_n)
=\operatorname N(L_n-1)\operatorname N(\varphi^n)
=(L_n-1)^2(-1).
$$

### T.5 素数平方特化与规范化周期商

**定义。** 对奇素数 $p\ne5$，令

$$
\epsilon=\left(\frac5p\right),
\qquad m=p-\epsilon.
$$

在下述整除性成立时，定义规范化商

$$
\ell_p=\frac{L_p-1}{p}\pmod p,
\qquad q_p=\frac{F_m}{p}\pmod p.
$$

**定理。** 对每个奇素数 $p\ne5$，有

$$
p\mid L_p-1,
\qquad p\mid F_{p-\epsilon},
\qquad 2\ell_p=5q_p\pmod p.
$$

**证明。** 在 $\mathbb F_p[\sqrt5]$ 中，Euler 判据与 Frobenius 映射给出

$$
(\sqrt5)^p=\epsilon\sqrt5,
\qquad L_p\equiv1\pmod p,
\qquad F_p\equiv\epsilon\pmod p.
$$

由
$L_p=F_p+2F_{p-1}=2F_{p+1}-F_p$，得到
$p\mid F_{p-\epsilon}$。写

$$
F_p=\epsilon+pA,
\qquad F_{p-\epsilon}=pB.
$$

若 $\epsilon=1$，Cassini 恒等式化为

$$
F_p^2-F_pF_{p-1}-F_{p-1}^2=1.
$$

模 $p^2$ 化简得 $2A\equiv B\pmod p$，而
$\ell_p\equiv A+2B$、$q_p\equiv B$，所以
$2\ell_p\equiv5q_p\pmod p$。若 $\epsilon=-1$，Cassini 恒等式化为

$$
F_{p+1}(F_{p+1}-F_p)-F_p^2=-1.
$$

模 $p^2$ 化简得 $2A\equiv-B\pmod p$，而
$\ell_p\equiv2B-A$、$q_p\equiv B$，仍有
$2\ell_p\equiv5q_p\pmod p$。

**定义。** 奇素数 $p$ 称为 WSS 素数，当且仅当

$$
p^2\mid L_p-1.
$$

**定理。** 对每个奇素数 $p$，

$$
\boxed{
p^2\mid\mathcal P_p(\varphi)\text{ 于 }\mathcal O
\iff p^2\mid L_p-1\text{ 于 }\mathbb Z.
}
$$

并且

$$
\operatorname N(\mathcal P_p(\varphi))=-(L_p-1)^2.
$$

若 $p\ne5$，上述条件还等价于
$\ell_p=0$，也等价于 $q_p=0$。

**证明。** 取 $n=p$、$q=p^2$ 代入 T2，得到第一组等价；取
$n=p$ 代入 T4，得到范数公式。最后，
$p^2\mid L_p-1$ 当且仅当 $\ell_p=0$；由于 $2$ 与 $5$ 在
$\mathbb F_p$ 中均可逆，等式 $2\ell_p=5q_p$ 又给出
$\ell_p=0\iff q_p=0$。

### T.6 两个实嵌入下的取值

**定义。** 定义 $\mathcal O$ 的两个实嵌入

$$
\sigma_+(a+b\varphi)=a+b\varphi,
\qquad
\sigma_*(a+b\varphi)=a+b\psi.
$$

**定理。** 对每个奇数 $n$，

$$
\sigma_+(E_n)=(L_n-1)\varphi^n,
\qquad
\sigma_*(E_n)=(L_n-1)\psi^n,
$$

并且两个实嵌入值的乘积为

$$
\sigma_+(E_n)\sigma_*(E_n)=-(L_n-1)^2.
$$

**证明。** 对 T1 分别应用 $\sigma_+$ 与 $\sigma_*$，得到前两式。
再使用 $\varphi\psi=-1$ 及 $n$ 为奇数，得到

$$
\sigma_+(E_n)\sigma_*(E_n)
=(L_n-1)^2(\varphi\psi)^n
=-(L_n-1)^2.
$$

## 附录 R：Fibonacci 回归谱与素数幂提升

### R.1 Fibonacci 矩阵与黄金二次环

**定义。** 令 $F_0=0$、$F_1=1$、$F_{t+2}=F_{t+1}+F_t$，并令

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad \det Q=-1,
\qquad \mathcal O=\mathbb Z[\varphi],\quad \varphi^2=\varphi+1.
$$

**命题。** Fibonacci 矩阵满足

$$
Q^2=
\begin{pmatrix}1&1\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

**证明。** 两端直接相乘都等于 $\begin{pmatrix}2&1\\1&1\end{pmatrix}$。

**定理。** 对全部 $t\ge0$，

$$
\boxed{
Q^t=
\begin{pmatrix}
F_{t+1}&F_t\\F_t&F_{t+1}-F_t
\end{pmatrix}.}
\tag{R1}
$$

**证明。** 当 $t=0$ 时右端是单位矩阵。若公式对 $t$ 成立，将右端乘以
$Q$，再用 $F_{t+2}=F_{t+1}+F_t$，便得到 $t+1$ 时的公式。

### R.2 序列周期、伴随矩阵阶与黄金单位阶

**定义。** 对正整数 $q$，令 $\pi(q)$ 为 $Q$ 在
$GL_2(\mathbb Z/q\mathbb Z)$ 中的阶；等价地，它是 Fibonacci 递推的可逆伴随矩阵
$\begin{pmatrix}1&1\\1&0\end{pmatrix}$ 的阶。特别地，$\pi(1)=1$。

**定理。** 对正整数 $q$ 与 $t\ge0$，

$$
\boxed{
\pi(q)\mid t
\iff(F_t,F_{t+1})\equiv(0,1)\pmod q
\iff\forall n\ge0,\ F_{n+t}\equiv F_n\pmod q.
}
\tag{R2}
$$

**证明。** 由 R1，$Q^t=I$ 当且仅当矩阵的左下项为 $0$、左上项为
$1$，即 $(F_t,F_{t+1})\equiv(0,1)$。若 $Q^t=I$，则
$Q^{n+t}=Q^n$，比较左下项便得序列同余。反之，在序列同余中依次取
$n=0,1$，即得所需的两项回归条件。

**定义。** 对 $z=a+b\varphi\in\mathcal O/q\mathcal O$，以反序坐标
$(b,a)$ 定义正则表示

$$
\mathcal R_q(z)=\begin{pmatrix}a+b&b\\b&a\end{pmatrix}.
\tag{R3}
$$

**定理。** $\mathcal R_q$ 是单射环同态，$\mathcal R_q(\varphi)=Q$，因而

$$
\boxed{\pi(q)=\operatorname{ord}(\overline\varphi\in(\mathcal O/q\mathcal O)^\times).}
\tag{R4}
$$

**证明。** 若 $w=c+d\varphi$，则
$zw=(ac+bd)+(ad+bc+bd)\varphi$；在坐标 $(d,c)$ 上，这正是 R3 的矩阵作用。
由此乘法与加法均被保持。矩阵第二列为 $(b,a)$，故表示为零只可能
$a=b=0$，所以它单射。取 $z=\varphi$ 得 $Q$；单射同态保持并反映
幂等于单位元，故两侧的阶相等。

### R.3 回归内容量与整除对偶

**定义。** 对 $t\ge0$，定义

$$
C_t=\gcd(F_t,F_{t+1}-1).
$$

**定理。** 对正整数 $q$ 与 $t\ge0$，

$$
\boxed{\pi(q)\mid t\iff q\mid C_t.}
\tag{R5}
$$

**证明。** 由 R2，左侧等价于 $q\mid F_t$ 且
$q\mid(F_{t+1}-1)$；这又等价于 $q$ 整除两数的最大公约数。

**命题。** $C_0=0$；若 $t>0$，则 $C_t>0$，并且满足
$\pi(q)\mid t$ 的正整数 $q$ 恰有 $\tau(C_t)$ 个。

**证明。** 初值得 $C_0=\gcd(0,0)=0$。当 $t>0$ 时，$F_t>0$，故
$C_t>0$。R5 表明所求正整数恰为 $C_t$ 的全部正约数，数量即
$\tau(C_t)$。

**定理。** 对正整数 $a,b$ 与非负整数 $s,t$，

$$
\boxed{
\pi(\operatorname{lcm}(a,b))=\operatorname{lcm}(\pi(a),\pi(b)),\qquad
C_{\gcd(s,t)}=\gcd(C_s,C_t).
}
\tag{R6}
$$

**证明。** 任意 $T$ 同时被 $\pi(a),\pi(b)$ 整除，当且仅当
$a,b$ 同时整除 $C_T$，也即 $\operatorname{lcm}(a,b)\mid C_T$；以
$T$ 取两边相应的最小周期，双向整除即得第一式。对任意正整数 $q$，
$q\mid C_{\gcd(s,t)}$ 当且仅当 $\pi(q)$ 同时整除 $s,t$，也即
$q$ 同时整除 $C_s,C_t$。若 $s=t=0$，第二式由 $C_0=0$ 直接成立；
否则两边均为正整数，分别取 $q$ 为等式两边便得第二式。

### R.4 第六十步回归与三个有限模数

**命题。** 有

$$
C_{60}=832040=2^3\cdot5\cdot11\cdot31\cdot61,
\qquad \tau(C_{60})=64.
$$

**证明。** 用 Fibonacci 递推算出 $F_{60}$ 与 $F_{61}$，再施行欧几里得算法，
得到 $\gcd(F_{60},F_{61}-1)=832040$；所示素因子分解给出
$\tau(C_{60})=(3+1)2^4=64$。

**命题。** 在 $C_{60}$ 的 $64$ 个正约数中，除 $q=1$ 外有 $63$ 个
非平凡模数，并且有 $49$ 个模数满足 $\pi(q)=60$。

**证明。** $64$ 个正约数中只有 $q=1$ 等于 $1$，其余 $63$ 个均大于 $1$。
由 R2 直接计算

$$
\pi(1)=1, \pi(2)=3, \pi(4)=6, \pi(8)=12,
\ \pi(5)=20, \pi(11)=10, \pi(31)=30, \pi(61)=60.
$$

**证明。** 含因子 $61$ 的 $32$ 个约数均有周期 $60$。不含 $61$ 时，周期的最小公倍数
等于 $60$ 的情形按 $2$ 的指数 $3,2,1,0$ 分别有 $7,4,4,2$ 个，合计
$17$ 个。因此总数为 $32+17=49$。

**命题。** 下列数值成立：

| 模数 $N$ | $\tau(N)$ | $\pi(N)$ |
|---|---:|---:|
| $5040=2^4 3^2 5\cdot7$ | 60 | 240 |
| $7560=2^3 3^3 5\cdot7$ | 64 | 720 |
| $55440=2^4 3^2 5\cdot7\cdot11$ | 120 | 240 |

**证明。** 约数个数由三行的素因子指数相乘得到。用 R2 逐次乘矩阵可得

$$
\pi(16)=24,\quad\pi(9)=24,\quad\pi(8)=12,\quad\pi(27)=72,\quad
\pi(5)=20,\quad\pi(7)=16,\quad\pi(11)=10.
$$

**证明。** 再由 R6 对各互素素数幂取周期的最小公倍数，依次得到 $240,720,240$。

### R.5 模平方的平方零回归缺陷与 Wall 二分律

**定义。** 设 $p>0$，$r=\pi(p)$，并定义整数

$$
a=F_r/p,\qquad b=(F_{r+1}-1)/p,\qquad
B=\begin{pmatrix}b&a\\a&b-a\end{pmatrix}.
$$

**证明。** 这些商为整数，因为 R2 给出 $p\mid F_r$ 与 $p\mid(F_{r+1}-1)$。

**定理。** 在 $\mathbb Z/p^2\mathbb Z$ 上，

$$
\boxed{Q^r=I+pB.}
\tag{R7}
$$

**证明。** 将 $F_r=pa$ 与 $F_{r+1}=1+pb$ 代入 R1 的四个矩阵项即可。

**定理。** 若环中 $D^2=0$，则对全部 $m\ge0$，

$$
(1+D)^m=1+mD.
$$

**证明。** 对 $m$ 归纳。归纳步中
$(1+mD)(1+D)=1+(m+1)D+mD^2=1+(m+1)D$。

**定理。** 对任意正整数 $p$，

$$
\pi(p)\mid\pi(p^2)\mid p\pi(p).
$$

**证明。** 降模同态给出左侧整除。令 $D=pB$；在模 $p^2$ 下有
$D^2=0$ 与 $pD=0$。由 R7 和前一定理，
$(Q^r)^p=(I+D)^p=I+pD=I$，故 $\pi(p^2)\mid pr$。

**定理。** 若 $p$ 为素数，则下列二者必有且仅有一个成立；该结论包括
$p=2$ 与 $p=5$：

$$
\boxed{\pi(p^2)=\pi(p)\quad\text{或}\quad
\pi(p^2)=p\pi(p).}
\tag{R8}
$$

**证明。** 由前一定理，$\pi(p^2)/\pi(p)$ 是 $p$ 的正约数；素性迫使它
等于 $1$ 或 $p$。

**定理。** 对素数 $p$，

$$
\boxed{
\pi(p^2)=\pi(p)
\iff p^2\mid C_{\pi(p)}
\iff p\mid a\ \text{且}\ p\mid b.
}
\tag{R9}
$$

**证明。** 第一处等价由 R5 对旧周期与模 $p^2$ 应用，并结合
$\pi(p)\mid\pi(p^2)$。又因 $F_r=pa$、$F_{r+1}-1=pb$，
$p^2$ 同时整除这两数当且仅当 $p$ 同时整除 $a,b$。

### R.6 奇素数的迹约束与判别式方向

**定理。** 若 $p$ 为奇素数，则 $r=\pi(p)$ 为偶数，并且 R.5 中的整数商满足

$$
\boxed{2b-a=-p(b^2-ab-a^2).}
\tag{R10}
$$

**证明。** 因 $Q^r\equiv I\pmod p$，取行列式得
$(-1)^r\equiv1\pmod p$。奇素数下 $1\not\equiv-1$，故 $r$ 为偶数。
**证明。** 再由 R1 与 R.5 中 $a,b$ 的定义，在整数矩阵中计算

$$
1=\det Q^r
=1+p(2b-a)+p^2(b^2-ab-a^2).
$$

**证明。** 在整数环中约去非零的 $p$，即得 R10。

**定理。** 对奇素数 $p$，

$$
\boxed{\pi(p^2)=\pi(p)\iff p\mid F_{\pi(p)}/p.}
\tag{R11}
$$

**证明。** R10 模 $p$ 给出 $2b=a$。由于 $2$ 在模 $p$ 下可逆，
$p\mid a$ 当且仅当 $p\mid b$；再用 R9。

**定义。** 在模 $p$ 下令

$$
H=\begin{pmatrix}1&2\\2&-1\end{pmatrix},\qquad
\overline B=\begin{pmatrix}b&a\\a&b-a\end{pmatrix}.
$$

**定理。** 对奇素数 $p$，

$$
\boxed{2\overline B=aH,\qquad (2\overline B)^2=5a^2I.}
\tag{R12}
$$

**证明。** 由 $2b=a$ 逐项比较得到第一式；直接相乘得 $H^2=5I$，
从而得到第二式。

**命题。** 若 $p$ 为素数、$p\ne2,5$ 且 $a\not\equiv0\pmod p$，则
$\ker\overline B=0$。此外，对模 $p^2$ 的状态向量 $v$，旧周期后的差为
$pBv$；若 $v\not\equiv0\pmod p$，则该差不为零。

**证明。** 若 $\overline Bv=0$，R12 给出 $5a^2v=0$；$5a^2$ 可逆，故
$v=0$。R7 给出 $Q^rv-v=pBv$。若后者在模 $p^2$ 下为零，则
$\overline B(v\bmod p)=0$，由核为零得到 $v\equiv0\pmod p$，与假设矛盾。

### R.7 模平方上的双根障碍

**定理。** 对每个整数 $n>1$，在 $(\mathbb Z/n^2\mathbb Z)[X]$ 中有
下式；等价地，$X^2-2X+1$ 不整除 $X^n-1$：

$$
\boxed{(X-1)^2\nmid X^n-1.}
\tag{R13}
$$

**证明。** 若 $X^n-1=(X-1)^2g(X)$，形式求导并代入 $X=1$，右端为
$0$，左端为 $n$。于是 $n=0$ 于 $\mathbb Z/n^2\mathbb Z$，即
$n^2\mid n$，这与 $n>1$ 矛盾。最后的等价表述来自
$X^2-2X+1=(X-1)^2$。

### R.8 平方零系数的一阶幂律

**定义。** 对交换环 $R$，令 $R[\varphi]=R[T]/(T^2-T-1)$，并把元素写成
$z=z_a+z_b\varphi$。

**定理。** 若 $z_b^2=0$，则对每个 $k\ge0$ 有下式，其中 $k=0$ 时
第二式右端按 $0\cdot z_a^0z_b=0$ 解释：

$$
\boxed{
(z^k)_a=z_a^k,\qquad
(z^k)_b=kz_a^{k-1}z_b,
}
$$

**证明。** 对 $k$ 归纳。乘法公式为
$(xy)_a=x_ay_a+x_by_b$ 与
$(xy)_b=x_ay_b+x_by_a+x_by_b$。归纳步代入归纳假设；所有含
$z_b^2$ 的项消失，余项分别合并为 $z_a^{k+1}$ 与
$(k+1)z_a^kz_b$。

### R.9 等幂的归一化系数输运

**定理。** 设 $p>0$，$x,y\in\mathcal O$，$k,l\ge0$，且
$x_b=pA$、$y_b=pB$、$x^k=y^l$。则在 $\mathbb Z/p\mathbb Z$ 中有

$$
\boxed{
kx_a^{k-1}A=ly_a^{l-1}B.
}
\tag{R15}
$$

**证明。** 将 $x,y$ 降到 $\mathcal O/p^2\mathcal O$。因
$x_b^2=y_b^2=0$，R.8 给出等幂两侧的 $\varphi$ 系数分别为
$pkx_a^{k-1}A$ 与 $ply_a^{l-1}B$。它们模 $p^2$ 相等，所以对应整数之差
被 $p^2$ 整除；在整数整除等式中约去 $p$，再降模 $p$，即得 R15。

### R.10 带符号的 Frobenius 指标

**定义。** 对素数 $p\ne2,5$，定义

$$
\epsilon_p=\left(\frac5p\right),\qquad
n_p=p-\epsilon_p,\qquad r_p=\pi(p),
$$

$$
\eta_p=\frac{F_{r_p}}p\pmod p,\qquad
q_p=\frac{F_{n_p}}p\pmod p.
$$

**定理。** 有 $\epsilon_p\in\{1,-1\}$、$n_p>0$，并且

$$
p\mid F_{n_p},\qquad
\varphi^{n_p}=\epsilon_p\pmod p,\qquad
r_p\mid2n_p,\qquad p\nmid r_p.
$$

**证明。** 令 $\delta=2\varphi-1$，则 $\delta^2=5$。在特征 $p$ 的
二次代数中，由 Frobenius 同态与 Euler 判据，
$\delta^p=\epsilon_p\delta$。若 $\epsilon_p=1$，便有
$\varphi^{p-1}=1$；若 $\epsilon_p=-1$，则
$\varphi^p=1-\varphi=-\varphi^{-1}$，故 $\varphi^{p+1}=-1$。
两种情形统一为 $\varphi^{n_p}=\epsilon_p$。比较 $\varphi$ 系数得
$p\mid F_{n_p}$，平方后得 $\varphi^{2n_p}=1$，故 $r_p\mid2n_p$。
又 $n_p\equiv-\epsilon_p\not\equiv0\pmod p$ 且 $p$ 为奇数，所以
$p\nmid r_p$。

**命题。** 当 $p=3$ 时，$\epsilon_p=-1$、$n_p=4$、$F_{n_p}=3$，而
$\pi(3)=8$；当 $p=7$ 时，$n_p=8$、$r_p=16$。

**证明。** Legendre 符号直接给出两个 $\epsilon_p$ 的值；Fibonacci 递推给出
$F_4=3$。对 $Q$ 分别在模 $3$ 与模 $7$ 下逐次乘方，并用 R2 检查所有真因子，
得到所列最小周期。

### R.11 首次回归深度

**定义。** 对素数 $p$，令 $\nu_p$ 表示正整数的 $p$-进赋值，并定义

$$
s_p=\nu_p(C_{r_p}),\qquad r_p=\pi(p),
$$

**命题。** $C_{r_p}>0$、$p\mid C_{r_p}$，因而 $s_p$ 是有限正整数。

**证明。** $r_p>0$，故 $F_{r_p}>0$，于是 $C_{r_p}>0$。R5 对
$t=r_p$ 给出 $p\mid C_{r_p}$，所以 $s_p\ge1$ 且有限。

### R.12 周期商与 Frobenius 商的准确比例

**定理。** 对每个素数 $p\ne2,5$，

$$
\boxed{
\eta_p=-r_pq_p\quad\text{于 }\mathbb F_p,\qquad
-r_p\in\mathbb F_p^\times.
}
\tag{R14}
$$

**证明。** 在 R15 中取
$x=\varphi^{r_p}$、$y=\varphi^{n_p}$、$k=n_p$、$l=r_p$；等幂前提来自
$(\varphi^{r_p})^{n_p}=(\varphi^{n_p})^{r_p}$。由 R2 与 R.10，
$x_a=1$、$y_a=\epsilon_p$ 于模 $p$，所以

$$
n_p\eta_p=r_p\epsilon_p^{r_p-1}q_p\pmod p.
$$

**证明。** R.6 表明 $r_p$ 为偶数，故
$\epsilon_p^{r_p-1}=\epsilon_p$；又
$n_p\equiv-\epsilon_p\pmod p$。约去单位 $\epsilon_p$ 即得
$\eta_p=-r_pq_p$。R.10 已证明 $p\nmid r_p$，所以 $-r_p$ 是单位。

**命题。** 对 $p=7$，有 $n_p=8$、$r_p=16$、$q_p=3$、$\eta_p=1$，且
$-r_p\equiv5\pmod7$，从而 $\eta_p=(-r_p)q_p$。

**证明。** 递推得 $F_8=21$、$F_{16}=987$；分别先除以 $7$ 再模 $7$，
得到 $q_p=3$ 与 $\eta_p=1$，而 $-16\equiv5$ 且 $5\cdot3\equiv1$。

**定理。** 对素数 $p\ne2,5$，

$$
\boxed{\pi(p^2)=\pi(p)\iff q_p=0.}
\tag{R16}
$$

**证明。** R11 将左侧等价为 $\eta_p=0$；R14 中的系数 $-r_p$ 是单位，
故 $\eta_p=0$ 当且仅当 $q_p=0$。

### R.13 素数幂的准确缺陷深度

**定理。** 设 $p$ 为素数，$s>0$，$s+2\le ps$，$B\in\mathcal O$ 且
$p\nmid B$。则对每个 $j\ge0$，存在 $D_j\in\mathcal O$ 使下式成立，
且左侧与 $1$ 的差恰被 $p^{s+j}$ 整除而不被 $p^{s+j+1}$ 整除：

$$
\boxed{
(1+p^sB)^{p^j}=1+p^{s+j}(B+pD_j).
}
\tag{R17}
$$

**证明。** 对 $j$ 归纳。$j=0$ 时取 $D_0=0$。设第 $j$ 步括号内为
$U=B+pD_j$，则 $U\equiv B\pmod p$。对
$(1+p^{s+j}U)^p$ 作二项展开：一次项为 $p^{s+j+1}U$；中间项因
$p\mid\binom{p}{i}$ 且 $i\ge2$，都被 $p^{s+j+2}$ 整除；最高次项由
$s+2\le ps$ 也被 $p^{s+j+2}$ 整除。因此余项可吸收到新的
$D_{j+1}$ 中，且括号仍模 $p$ 等于 $B$。因为 $p\nmid B$，这个括号不被
$p$ 整除，故所述深度准确。

**定理。** 在 R17 的假设下，$1+p^sB$ 在
$(\mathcal O/p^{s+j}\mathcal O)^\times$ 中的阶恰为 $p^j$。

**证明。** R17 给出其 $p^j$ 次幂为 $1$。若 $j>0$，R17 对 $j-1$
给出的差恰只有深度 $s+j-1$，所以 $p^{j-1}$ 次幂尚不为 $1$。
该阶是 $p^j$ 的约数，却不整除 $p^{j-1}$，故只能是 $p^j$。

**命题。** 对奇素数，$s\ge1$ 即满足 $s+2\le ps$；对 $p=2$，该条件在
$s\ge2$ 时满足。

**证明。** 第一种情形有 $p\ge3$，故 $ps-(s+2)=(p-1)s-2\ge0$；
第二种情形化为 $s\ge2$。

### R.14 奇素数的完整周期塔

**定理。** 对任意奇素数 $p$ 与任意 $e\ge1$，

$$
\boxed{
\pi(p^e)=r_p\,p^{\max(e-s_p,0)},
\qquad s_p=\nu_p(C_{r_p}).
}
\tag{R18}
$$

**证明。** 由 Fibonacci 递推，
$C_{r_p}=\gcd(F_{r_p},F_{r_p-1}-1)$。结合 $s_p$ 的定义与 R2，
$\varphi^{r_p}-1$ 的两个整数坐标都被
$p^{s_p}$ 整除，但不都被 $p^{s_p+1}$ 整除。因此存在
$B\in\mathcal O$ 使

$$
\varphi^{r_p}=1+p^{s_p}B,\qquad p\nmid B.
$$

**证明。** 若 $e\le s_p$，则 $r_p$ 已在模 $p^e$ 下回归，而降模到 $p$ 又给
$r_p\mid\pi(p^e)$，故 $\pi(p^e)=r_p$。若 $e=s_p+j$，R.13 表明
$\varphi^{r_p}$ 在模 $p^e$ 下的阶为 $p^j$。令
$T=\pi(p^e)$；因 $r_p\mid T$，元素幂的阶公式给出

$$
\operatorname{ord}(\varphi^{r_p})
=\frac{T}{\gcd(T,r_p)}=\frac{T}{r_p}=p^j.
$$

**证明。** 于是 $T=r_pp^j$，与第一种情形合并即得 R18。

**定理。** 对素数 $p\ne2,5$，

$$
\boxed{q_p=0\iff s_p\ge2.}
\tag{R19}
$$

**证明。** 由 R5，$s_p\ge2$ 当且仅当
$p^2\mid C_{r_p}$，也即 $\pi(p^2)=\pi(p)$；再用 R16，即得 R19。

**命题。** 对素数 $p\ne2,5$，若 $q_p\ne0$，则

$$
\forall e\ge1,\quad \pi(p^e)=\pi(p)p^{e-1}.
$$

**证明。** 若 $q_p\ne0$，则 R19 给出 $s_p\not\ge2$，而 R.11 给出
$s_p\ge1$，故 $s_p=1$；代入 R18 即得最后一式。

### R.15 二进与分歧素数的完整周期塔

**定理。** 对每个 $e\ge1$，

$$
\boxed{
\pi(2^e)=3\cdot2^{e-1},\qquad
\pi(5^e)=20\cdot5^{e-1}.
}
\tag{R20}
$$

**证明。** 由 R2 的有限检查，
$\pi(2)=3$、$\pi(4)=6$、$\pi(5)=20$。在 $\mathcal O$ 中直接递推得到

$$
\varphi^6=1+4(1+2\varphi),
\qquad
\varphi^{20}=1+5(836+1353\varphi).
$$

**证明。** 第一式括号不被 $2$ 整除，是深度 $2$ 的原始缺陷；第二式括号不被 $5$
整除，是深度 $1$ 的原始缺陷。分别从模 $4$ 与模 $5$ 应用 R.13 的准确阶
结论，得到 $e\ge2$ 时
$\pi(2^e)=6\cdot2^{e-2}$，以及全部 $e\ge1$ 时
$\pi(5^e)=20\cdot5^{e-1}$。前者再与 $e=1$ 合并，便是 R20。

**命题。** $\pi(2^0)=\pi(5^0)=\pi(1)=1$，所以 R20 的范围不能扩为
$e=0$。

**证明。** 模 $1$ 的可逆矩阵群只有单位元，故其元素阶为 $1$；而 R20
右侧在 $e=0$ 不按自然数指数给出所需值。

### R.16 周期平台与逐层提升

**命题。** 对奇素数 $p$，若 $1\le e\le s_p$，则
$\pi(p^e)=r_p$；若 $e\ge s_p$，则

$$
\pi(p^{e+1})=p\,\pi(p^e).
$$

**证明。** 第一式由 R18 中 $\max(e-s_p,0)=0$ 得到。第二式中指数
分别为 $e-s_p+1$ 与 $e-s_p$，相差 $1$，故两周期相差因子 $p$。

### R.17 任意周期倍数的精确回归深度

**定理。** 令 $p$ 为奇素数、$r_p=\pi(p)$、
$s_p=\nu_p(C_{r_p})$。对全部 $k\ge0$ 与 $e\ge1$，

$$
\boxed{
p^e\mid C_{r_pk}\iff p^{\max(e-s_p,0)}\mid k.
}
\tag{R21}
$$

**证明。** 由 R5，左侧等价于 $\pi(p^e)\mid r_pk$。代入 R18，并在
自然数整除见证中约去正整数 $r_p$，即得右侧。$k=0$ 时两边都成立。

**定理。** 在前一定理的假设下，若 $k>0$，则

$$
\boxed{
\nu_p(C_{r_pk})=s_p+\nu_p(k).
}
\tag{R22}
$$

**证明。** 令 $d=s_p+\nu_p(k)$。由 R21，$p^d\mid C_{r_pk}$，而
$p^{d+1}\nmid C_{r_pk}$。又因 $r_pk>0$，有 $F_{r_pk}>0$，从而
$C_{r_pk}>0$；按 $p$-进赋值的定义即得 R22。
## TR. 环面返回模、有限观察与耗散结构

### TR.1 返回模与列向量约定

**定义。** 对整数二阶矩阵 $A$ 与自然数 $n$，采用列向量约定，定义返回模

$$
R(A,n)=\mathbb Z^2/(A^n-I)\mathbb Z^2,
$$

其中分母是同态 $A^n-I:\mathbb Z^2\to\mathbb Z^2$ 的像。

**定义。** 对自然数 $q$，记 $\mathbb Z/(q)=\mathbb Z/q\mathbb Z$；特别约定 $\mathbb Z/(0)=\mathbb Z$。

### TR.2 行列式为二的校准族

**定义。** 对任意自然数 $k$，定义 companion 族、balanced 族及其整数交织子

$$
C_k=\begin{pmatrix}4k+1&1\\4k&1\end{pmatrix},\qquad
D_k=\begin{pmatrix}2k+1&2\\2k(k+1)&2k+1\end{pmatrix},\qquad
P_k=\begin{pmatrix}1&0\\-2k&2\end{pmatrix}.
$$

**定理。** 对每个 $k\geq0$，有

$$
\det C_k=\det D_k=1,\qquad
\operatorname{tr}C_k=\operatorname{tr}D_k=4k+2,
$$

以及

$$
C_kP_k=P_kD_k,\qquad \det P_k=2.
$$

对每个 $n\geq0$，还有

$$
(C_k^n-I)P_k=P_k(D_k^n-I),
\qquad
\det(C_k^n-I)=\det(D_k^n-I).
$$

**证明。** 前两组等式由二阶行列式、迹和矩阵乘法直接计算。由 $C_kP_k=P_kD_k$ 对 $n$ 归纳，得 $C_k^nP_k=P_kD_k^n$，减去 $P_k$ 即得交织恒等式。两边取行列式后得到

$$
2\det(C_k^n-I)=2\det(D_k^n-I),
$$

在整数中约去 $2$ 即得最后一式。

**定理。** $P_k$ 在 $\mathbb Z^2$ 上单射，其像的指数为 $2$，因而诱导一个度数为 $2$ 的格同源；它不是整数基变换。

**证明。** 若 $P_k(p,q)=0$，则第一坐标给出 $p=0$，第二坐标再给出 $q=0$，故 $P_k$ 单射。其像恰为第二坐标为偶数的整数向量集合：正向由 $P_k(p,q)=(p,-2kp+2q)$，反向对 $(x,2y)$ 取 $(p,q)=(x,y+kx)$。因此像的指数为 $2$。整数基变换的行列式只能是 $\pm1$。

**定理。** $C_k$ 与 $D_k$ 的共同特征多项式的判别式为

$$
(4k+2)^2-4=16k(k+1).
$$

当 $k=1$ 时，其特征值生成的二次域是 $\mathbb Q(\sqrt2)$。

**证明。** 两个矩阵的行列式均为 $1$、迹均为 $4k+2$，故特征多项式为 $X^2-(4k+2)X+1$，判别式即所示。$k=1$ 时，判别式为 $32=(4\sqrt2)^2$，其平方根生成 $\mathbb Q(\sqrt2)$。

### TR.3 返回模的有限基数

**定理。** 若 $k>0$ 且 $n>0$，则

$$
\det(C_k^n-I)=2-\operatorname{tr}(C_k^n)<0,
$$

从而 $C_k^n-I$ 与 $D_k^n-I$ 都非奇异。

**证明。** $C_k$ 的所有矩阵元非负。对 $m$ 归纳可得 $C_k^m$ 的所有矩阵元非负，且两个对角元至少为 $1$。写 $n=m+1$，则

$$
\operatorname{tr}(C_k^{m+1})
=(4k+1)(C_k^m)_{00}+4k(C_k^m)_{01}
+(C_k^m)_{10}+(C_k^m)_{11}>2.
$$

又因 $\det(C_k^n)=1$，二阶恒等式 $\det(M-I)=\det M-\operatorname{tr}M+1$ 给出所述负号。TR.2 的行列式恒等式随即给出 $D_k^n-I$ 的非奇异性。

**定理。** 对任意非奇异整数二阶矩阵 $M$，商群 $\mathbb Z^2/M\mathbb Z^2$ 有限，且

$$
\#(\mathbb Z^2/M\mathbb Z^2)=|\det M|.
$$

**证明。** 对 $M$ 作整数初等行、列变换，得到 Smith 标准形 $\operatorname{diag}(d_1,d_2)$。这些变换在定义域和陪域上都是整系数可逆变换，因而不改变商群的基数。标准形的商群为 $\mathbb Z/(d_1)\times\mathbb Z/(d_2)$，其基数是 $|d_1d_2|=|\det M|$。

**定理。** 对所有 $k>0$、$n>0$，$R(C_k,n)$ 与 $R(D_k,n)$ 都是有限群，并且

$$
\#R(C_k,n)=\#R(D_k,n)=|\det(C_k^n-I)|.
$$

**证明。** 应用前一定理及 TR.2、TR.3。若 $n=0$，则 $R(A,0)=\mathbb Z^2$，故该有限性结论不适用。

### TR.4 整数交织子的偶性障碍

**定理。** 设 $k\geq0$，并设

$$
U=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in M_2(\mathbb Z).
$$

若 $C_kU=UD_k$，则

$$
c=2k((k+1)b-a),\qquad d=2(a-kb),
$$

且

$$
\det U=2\bigl(a^2-k(k+1)b^2\bigr).
$$

特别地，$\det U$ 为偶数，不存在 $\det U=\pm1$ 的整数交织子，所以 $C_k$ 与 $D_k$ 不在 $GL_2(\mathbb Z)$ 中共轭。

**证明。** 比较 $C_kU=UD_k$ 的第一行两个矩阵元，依次解得 $c$ 与 $d$。将它们代入 $ad-bc$ 并展开，得到行列式公式。可逆整数矩阵的行列式只能是 $\pm1$，与偶性矛盾。

**定理。** 在整数二阶矩阵中，全部正时间返回模的基数序列不能确定整数共轭类。

**证明。** 任取 $k>0$。TR.3 给出 $C_k$ 与 $D_k$ 在每个正时间的相同返回模基数，TR.4 则证明二者不整数共轭。

### TR.5 companion 与 balanced 族的像核恒等式

**定义。** 对 $k\geq0$ 定义群同态

$$
\pi_C:\mathbb Z^2\to\mathbb Z/(4k),qquad
\pi_C(x,y)=y\pmod{4k},
$$

以及

$$
\pi_D:\mathbb Z^2\to\mathbb Z/(2)\times\mathbb Z/(2k),qquad
\pi_D(x,y)=\bigl(x\pmod2,\ y-kx\pmod{2k}\bigr).
$$

**定理。** $\pi_C$ 满射，并且

$$
\ker\pi_C=(C_k-I)\mathbb Z^2.
$$

**证明。** 任意剩余类由 $(0,y)$ 映到，故 $\pi_C$ 满射。又

$$
(C_k-I)\binom pq=\binom{4kp+q}{4kp},
$$

所以其像包含于 $\ker\pi_C$。反之，若 $\pi_C(x,y)=0$，则 $y=4ka$；于是

$$
\binom xy=(C_k-I)\binom{a}{x-4ka}.
$$

**定理。** $\pi_D$ 满射，并且

$$
\ker\pi_D=(D_k-I)\mathbb Z^2.
$$

**证明。** 给定两个剩余类，取整数代表 $a,b$，则 $(a,b+ka)$ 映到它们。又

$$
(D_k-I)\binom pq
=\binom{2kp+2q}{2k(k+1)p+2kq},
$$

其第一坐标为偶数，且第二坐标减去第一坐标的 $k$ 倍等于 $2kp$，故像包含于核。反之，若 $(x,y)$ 位于核，写 $x=2a$、$y-kx=2kb$，则

$$
\binom xy=(D_k-I)\binom{b}{a-kb}.
$$

### TR.6 一步返回模的结构分离

**定理。** 对每个 $k\geq0$，有加法群同构

$$
R(C_k,1)\cong\mathbb Z/(4k),qquad
R(D_k,1)\cong\mathbb Z/(2)\times\mathbb Z/(2k).
$$

当 $k=0$ 时，这两式分别为 $R(C_0,1)\cong\mathbb Z$ 与 $R(D_0,1)\cong\mathbb Z/(2)\times\mathbb Z$。

**证明。** 分别对 TR.5 的满射应用第一同构定理，并以其中的像核恒等式识别分母。

**定理。** 若 $k>0$，则 $R(D_k,1)$ 的每个元素都被 $2k$ 湮灭，而 $R(C_k,1)$ 中存在不被 $2k$ 湮灭的元素。因此

$$
R(C_k,1)\not\cong R(D_k,1).
$$

**证明。** 在 $\mathbb Z/(2)\times\mathbb Z/(2k)$ 中，乘以 $2k$ 后两个分量都为零。在 $\mathbb Z/(4k)$ 中，剩余类 $1$ 不被 $2k$ 湮灭，否则 $4k$ 整除 $2k$，与 $k>0$ 矛盾。TR.6 的同构将这两个性质传回实际返回模。

**定理。** 对每个 $k>0$，$C_k$ 与 $D_k$ 的全部正时间返回模基数相同，但一步返回模的加法群不同构。

**证明。** 第一部分由 TR.3，第二部分由前一定理。

### TR.7 返回模结构与标量观察

**命题。** 在校准族 $C_k,D_k$ 中，标量序列

$$
n\longmapsto\#R(A,n),\qquad n>0,
$$

不决定一步返回模的群结构，而一步返回模的湮灭阶能够区分 $C_k$ 与 $D_k$。

**证明。** TR.6 同时给出相同标量序列和不同的 $2k$-湮灭性质。

### TR.8 交织子范数与模共轭判据

**定理。** 设 $S$ 为交换环，$k\geq0$。矩阵 $U\in M_2(S)$ 满足 $C_kU=UD_k$ 当且仅当存在 $a,b\in S$ 使

$$
U=U(a,b)=
\begin{pmatrix}
a&b\\
2k((k+1)b-a)&2(a-kb)
\end{pmatrix}.
$$

此时

$$
\det U(a,b)=2\bigl(a^2-k(k+1)b^2\bigr).
$$

**证明。** 正向由交织等式第一行的两个分量依次求出第二行；整个推导没有除法。反向把所示矩阵代入四个矩阵元，四式均成立。行列式公式由展开得到。

**定义。** 对自然数 $m$，称 $C_k$ 与 $D_k$ 在 $\mathbb Z/(m)$ 上共轭，如果存在 $P,Q\in M_2(\mathbb Z/(m))$ 满足

$$
PQ=QP=I,qquad C_kP=PD_k.
$$

**定理。** 对所有自然数 $k,m$，

$$
C_k\text{ 与 }D_k\text{ 在 }\mathbb Z/(m)\text{ 上共轭}
\quad\Longleftrightarrow\quad m\text{ 为奇数}.
$$

**证明。** 若 $m=2r+1$，在 $\mathbb Z/(m)$ 中令 $u=-r$，则 $2u=1$。取

$$
P=\begin{pmatrix}1&0\\-2k&2\end{pmatrix},qquad
Q=\begin{pmatrix}1&0\\k&u\end{pmatrix}.
$$

直接乘法给出 $PQ=QP=I$ 与 $C_kP=PD_k$。反之，若 $m$ 为正偶数，则存在环同态 $\mathbb Z/(m)\to\mathbb Z/(2)$。任何可逆交织子都满足 $\det(P)\det(Q)=1$；TR.8 的行列式公式在 $\mathbb Z/(2)$ 中却使左边为 $0$，矛盾。若 $m=0$，系数环为 $\mathbb Z$，TR.4 排除可逆交织子。$m=1$ 为零环，且属于奇数情形。

### TR.9 环面作用与周期群

**定义。** 令 $V=\mathbb R^2$，令 $j:\mathbb Z^2\to V$ 为逐坐标嵌入，$L=j(\mathbb Z^2)$，并令

$$
\mathbb T^2=V/L.
$$

对整数矩阵 $A$，其实线性延拓保持 $L$，故诱导连续群同态

$$
f_A:\mathbb T^2\to\mathbb T^2,qquad [x]\longmapsto[Ax].
$$

**定义。** 对自然数 $n$，定义周期整除 $n$ 的固定点群

$$
K(A,n)=\ker f_{A^n-I}.
$$

**定理。** 对整数矩阵 $A,B$ 与自然数 $n$，

$$
f_A\circ f_B=f_{AB},qquad f_A^n=f_{A^n},qquad
z\in K(A,n)\Longleftrightarrow f_A^n(z)=z.
$$

**证明。** 每个等式在代表元上分别化为 $A(Bx)=(AB)x$、矩阵幂的归纳以及 $(A^n-I)x=A^nx-x$。由于整数矩阵保持格 $L$，这些代表元计算均良定义。

### TR.10 环面固定点与返回商

**定理。** 设 $M=A^n-I$ 且 $\det M\ne0$。则存在加法群同构

$$
R(A,n)\cong K(A,n).
$$

其逆可写为

$$
[x]\longmapsto[Mx]
\quad\text{从}\quad
M_{\mathbb R}^{-1}\mathbb Z^2/\mathbb Z^2
\quad\text{到}\quad
\mathbb Z^2/M\mathbb Z^2.
$$

**证明。** 由 $\det M\ne0$，实线性映射 $M_{\mathbb R}$ 可逆。定义

$$
b_M:\mathbb Z^2\to\ker f_M,qquad
z\longmapsto[M_{\mathbb R}^{-1}j(z)].
$$

若 $[x]\in\ker f_M$，则 $M_{\mathbb R}x\in L$，故存在 $z\in\mathbb Z^2$ 使 $M_{\mathbb R}x=j(z)$，从而 $b_M(z)=[x]$；所以 $b_M$ 满射。另一方面，$b_M(z)=0$ 当且仅当存在 $w\in\mathbb Z^2$ 使 $M_{\mathbb R}^{-1}j(z)=j(w)$，也即 $z=Mw$。因此 $\ker b_M=M\mathbb Z^2$，第一同构定理给出结论。所写逆映射由同一计算得出。

**定理。** 对 $k>0$、$n>0$，$f_{C_k}$ 与 $f_{D_k}$ 的周期整除 $n$ 的固定点群具有相同有限基数；在 $n=1$ 时，这两个固定点群不同构。

**证明。** TR.3 保证相关行列式非零，TR.10 把固定点群分别同构到返回模，再应用 TR.3 与 TR.6。

### TR.11 粒子流与环面自同构的同痕障碍

**假设。** 设 $T\geq0$，$\Phi:[0,T]\times\mathbb T^2\to\mathbb T^2$ 连续，且 $\Phi_0=\operatorname{id}_{\mathbb T^2}$；对每个 $t$，记 $\Phi_t(x)=\Phi(t,x)$。

**定理。** $\Phi_T$ 与恒等映射同痕，因而 $\Phi_T$ 在一阶同调群上的诱导映射是恒等。若整数环面自同构 $f_A$ 在一阶同调上的作用为非恒等矩阵 $A$，则 $\Phi_T\ne f_A$。

**证明。** 映射 $(s,x)\mapsto\Phi_{sT}(x)$ 是从恒等映射到 $\Phi_T$ 的同痕。同调的同痕不变性给出第一项。若 $\Phi_T=f_A$，则二者在一阶同调上的作用相同，迫使 $A=I$，矛盾。

**定义。** 对常系数对称逆度量

$$
H=\begin{pmatrix}h_{00}&h_{01}\\h_{01}&h_{11}\end{pmatrix}
$$

和黏性 $\nu$，定义平坦二维零压力、零外力的 Navier--Stokes 残差

$$
\mathcal R_H(v)=\partial_tv+(v\cdot\nabla)v
-\nu\bigl(h_{00}\partial_{xx}+2h_{01}\partial_{xy}+h_{11}\partial_{yy}\bigr)v.
$$

### TR.12 格同源下的剪切解与度量输运

**定义。** 在两个空间坐标均以 $2\pi$ 为周期的平坦环面上，令

$$
u(t,X,Y)=(e^{-\nu t}\cos Y,0),qquad
Q_k=P_k^{-1}=\begin{pmatrix}1&0\\k&1/2\end{pmatrix},
$$

并定义

$$
v(t,x,y)=Q_ku(t,P_k(x,y))
=(1,k)e^{-\nu t}\cos(-2kx+2y).
$$

**定理。** $u$ 光滑、无散度，且满足欧氏度量下的无外力、零压力 Navier--Stokes 方程

$$
\partial_tu+(u\cdot\nabla)u-\nu\Delta u=0.
$$

**证明。** 直接求导得 $\operatorname{div}u=0$、$(u\cdot\nabla)u=0$、$\partial_tu=\nu\Delta u$。

**定理。** 令

$$
G_k=P_k^{\mathsf T}P_k,qquad
H_k=Q_kQ_k^{\mathsf T}
=\begin{pmatrix}1&k\\k&k^2+1/4\end{pmatrix}.
$$

则 $G_kH_k=H_kG_k=I$，且 $H_k$ 正定。具体地，对 $(r,s)\ne(0,0)$，

$$
(r,s)H_k(r,s)^{\mathsf T}=(r+ks)^2+s^2/4>0.
$$

**证明。** 由 $P_kQ_k=Q_kP_k=I$ 直接得到两侧逆关系。二次型恒等式由展开得到；若 $s\ne0$，第二项为正，若 $s=0$，则 $r\ne0$ 且第一项为正。

**定义。** 对实数 $\lambda$，令

$$
v_\lambda(t,x,y)=(1,k)e^{-\nu\lambda t}\cos(-2kx+2y).
$$

**定理。** $v_\lambda$ 关于时空变量光滑，并在两个空间方向上均为 $2\pi$ 周期；它无散度，且

$$
\mathcal R_H(v_\lambda)
=\nu\bigl(4h_{00}k^2-8h_{01}k+4h_{11}-\lambda\bigr)v_\lambda.
$$

**证明。** 光滑性与周期性由指数函数、余弦函数及整数频率直接得到。令 $\ell=(-2k,2)$、$a=(1,k)$，则 $\ell\cdot a=0$，所以散度及完整对流项消失。再用

$$
\partial_tv_\lambda=-\nu\lambda v_\lambda,\qquad
\partial_{xx}v_\lambda=-4k^2v_\lambda,\qquad
\partial_{xy}v_\lambda=4kv_\lambda,\qquad
\partial_{yy}v_\lambda=-4v_\lambda
$$

代入 TR.11 的残差定义，即得公式。

**定理。** $v_1=v$ 满足逆度量 $H_k$ 下的方程；在欧氏逆度量下则有

$$
\mathcal R_I(v)=\nu(4k^2+3)v.
$$

若 $\nu>0$，该残差在 $(t,x,y)=(0,0,0)$ 的第一分量严格为正。另一方面，

$$
w(t,x,y)=(1,k)e^{-4\nu(k^2+1)t}\cos(-2kx+2y)
$$

满足欧氏度量下的无外力方程，并且 $w(0,x,y)=v(0,x,y)$。

**证明。** 在残差公式中依次代入 $(h_{00},h_{01},h_{11},\lambda)=(1,k,k^2+1/4,1)$、$(1,0,1,1)$ 与 $(1,0,1,4(k^2+1))$。第一组和第三组的系数为零，第二组的系数为 $4k^2+3$。初值等式由令 $t=0$ 得到。

**定理。** $H_k$ 的最小特征值没有与 $k$ 无关的正下界，并且

$$
\lambda_{\min}(H_k)\leq\frac{1}{4(k^2+1)}\longrightarrow0.
$$

**证明。** 在 Rayleigh 商中取非零向量 $(-k,1)$。TR.12 的二次型等于 $1/4$，而该向量的欧氏长度平方为 $k^2+1$。

### TR.13 Hilbert 空间的耗散管与二次李雅普诺夫证书

**假设。** 设 $H$ 为实内积空间，$u:[0,T]\to H$ 连续，并在 $[0,T)$ 具有右导数 $\dot u$。设 $\gamma>0$、$\rho\geq0$，且

$$
\langle u(t),\dot u(t)\rangle
\leq-\gamma\|u(t)\|^2+\rho\|u(t)\|.
$$

**定理。** 对每个 $t\in[0,T]$，

$$
\|u(t)\|\leq e^{-\gamma t}\|u(0)\|
+\frac{\rho}{\gamma}\bigl(1-e^{-\gamma t}\bigr).
$$

特别地，当 $\rho=0$ 时，$\|u(t)\|\leq e^{-\gamma t}\|u(0)\|$。

**证明。** 对 $\delta>0$ 定义

$$
z_\delta(t)=\sqrt{\|u(t)\|^2+\delta^2}.
$$

被开方数严格为正，故在 $u(t)=0$ 时链式法则仍适用。记 $n=\|u(t)\|$、$z=z_\delta(t)$，则 $z\geq n$、$z\geq\delta$，并且

$$
z_\delta'(t)=\frac{\langle u(t),\dot u(t)\rangle}{z_\delta(t)}
\leq-\gamma z_\delta(t)+\rho+\gamma\delta.
$$

最后一个不等式可在乘以正数 $z$ 后由恒等式

$$
(-\gamma z+\rho+\gamma\delta)z-(-\gamma n^2+\rho n)
=\rho(z-n)+\gamma\delta(z-\delta)
$$

得到。标量 Gronwall 比较给出

$$
z_\delta(t)\leq e^{-\gamma t}z_\delta(0)
+\frac{\rho+\gamma\delta}{\gamma}\bigl(1-e^{-\gamma t}\bigr).
$$

由 $\|u(t)\|\leq z_\delta(t)$，再令 $\delta\downarrow0$，利用平方根与指数函数的连续性即得结论。

**定理。** 设 $\gamma>0$、$\rho\geq0$，$u:[0,T]\to H$ 连续且在 $[0,T)$ 具有右导数。设 $A(t):H\to H$ 为有界线性算子，$f:[0,T]\to H$ 连续，并且

$$
u'(t)=A(t)u(t)+f(t),\qquad
\langle x,A(t)x\rangle\leq-\gamma\|x\|^2,qquad
\|f(t)\|\leq\rho.
$$

则 $u$ 满足前一定理的同一指数管估计。

**证明。** 由 Cauchy--Schwarz 不等式，

$$
\langle u,u'\rangle
=\langle u,A(t)u\rangle+\langle u,f\rangle
\leq-\gamma\|u\|^2+\rho\|u\|.
$$

应用前一定理。

**定义。** 设 $L:H\to H$ 线性，$B:H\times H\to H$ 双线性，$f\in H$，定义

$$
F(x)=Lx-B(x,x)+f.
$$

**假设。** 对所有 $a,b,w\in H$，设

$$
\langle b,B(a,b)\rangle=0,qquad
\langle w,Lw\rangle\leq-\mu\|w\|^2,qquad
-\langle w,B(w,v)\rangle\leq G\|w\|^2,
$$

并设 $G<\mu$、$F(v)=0$。

**定理。** 对所有 $w,x\in H$，

$$
\langle w,F(v+w)-F(v)\rangle
=\langle w,Lw\rangle-\langle w,B(w,v)\rangle,
$$

以及

$$
\langle x-v,F(x)-F(v)\rangle
\leq-(\mu-G)\|x-v\|^2.
$$

**证明。** 展开 $B(v+w,v+w)$。由假设，$\langle w,B(v,w)\rangle=0$ 与 $\langle w,B(w,w)\rangle=0$，只留下 $B(w,v)$。再代入关于 $L$ 与 $B(w,v)$ 的两个二次型上界。

**定理。** 在上述假设下，对每个 $x\in H$，

$$
\|x-v\|\leq\frac{\|F(x)\|}{\mu-G}.
$$

并且 $v$ 是 $F$ 的唯一零点。

**证明。** 若 $x=v$，结论显然。否则将前一定理与 $F(v)=0$ 合并，取相反数后用 Cauchy--Schwarz 不等式，得到

$$
(\mu-G)\|x-v\|^2
\leq\|x-v\|\,\|F(x)\|.
$$

约去正数 $\|x-v\|$ 即得距离界。若再有 $F(x)=0$，右边为零，故 $x=v$。

**定理。** 设 $\rho\geq0$，且 $u:[0,T]\to H$ 连续并在 $[0,T)$ 具有右导数。若轨迹满足

$$
u'(t)=F(u(t))+r(t),\qquad \|r(t)\|\leq\rho,
$$

则对 $t\in[0,T]$，

$$
\|u(t)-v\|\leq e^{-(\mu-G)t}\|u(0)-v\|
+\frac{\rho}{\mu-G}\bigl(1-e^{-(\mu-G)t}\bigr).
$$

**证明。** 令 $e=u-v$。前述负裕量和 Cauchy--Schwarz 不等式给出

$$
\langle e,e'\rangle
\leq-(\mu-G)\|e\|^2+\rho\|e\|.
$$

应用 TR.13 的耗散管定理。

### TR.14 受迫剪切不动点与耗散记忆

**定义。** 对 $k\geq0$、$\nu>0$，令

$$
\Phi_k(x,y)=(1,k)\cos(-2kx+2y),qquad
\Gamma_k=4\nu(k^2+1),qquad
u_a(t,x,y)=a(t)\Phi_k(x,y).
$$

**定理。** 若 $a$ 可微，则 $u_a$ 无散度，且欧氏零压力残差满足

$$
\partial_tu_a+(u_a\cdot\nabla)u_a-\nu\Delta u_a
=(a'+\Gamma_ka)\Phi_k.
$$

此外，$a(t)=u_a(t,0,0)_1$，其中下标 $1$ 表示第一坐标分量。

**证明。** 波矢 $(-2k,2)$ 与幅向量 $(1,k)$ 正交，故散度和对流项消失。坐标二阶导数之和为 $-4(k^2+1)u_a$，从而得到残差公式。在 $(x,y)=(0,0)$ 处，第一坐标分量的幅值为 $1$，故得到读数恒等式。

**定理。** 对常数 $c$，时间不变场

$$
u_*(x,y)=c\Phi_k(x,y)
$$

是外力 $f_*=\Gamma_kc\Phi_k$ 下的稳态解。若 $\rho\geq0$ 且

$$
a'=-\Gamma_k(a-c)+r,qquad |r(t)|\leq\rho,
$$

则对所有 $t\in[0,T]$、$(x,y)$ 及两个坐标分量 $i$，

$$
|u_{a,i}(t,x,y)-u_{*,i}(x,y)|
\leq(1+k)\left[
e^{-\Gamma_kt}|a(0)-c|
+\frac{\rho}{\Gamma_k}(1-e^{-\Gamma_kt})
\right].
$$

**证明。** 取 $a\equiv c$ 代入前一定理即得稳态方程。对 $a-c$ 应用 TR.13 的标量情形，再用

$$
|\Phi_{k,i}(x,y)|\leq1+k
$$

即可得到一致空间界。

**定义。** 对实常数 $a,b,d$，考虑二状态系统

$$
x'=-ax+by,qquad y'=-bx-dy,
$$

并定义能量 $E=x^2+y^2$。

**定理。** 该系统满足精确能量恒等式

$$
E'=-2ax^2-2dy^2.
$$

若 $a,d\geq\gamma>0$，则对 $t\in[0,T]$，

$$
E(t)\leq E(0)e^{-2\gamma t},
$$

且该估计与耦合常数 $b$ 无关。

**证明。** 对 $x^2+y^2$ 求导，两个交叉项 $2bxy$ 与 $-2bxy$ 相消。于是 $E'\leq-2\gamma E$，标量 Gronwall 比较给出结论。

**定理。** 若 $b\ne0$，则隐藏状态由可见状态及其导数精确恢复：

$$
y=\frac{x'+ax}{b}.
$$

若观测值满足 $|\widehat x-x|\leq\varepsilon_x$ 与 $|\widehat v-x'|\leq\varepsilon_v$，则

$$
\left|\frac{\widehat v+a\widehat x}{b}-y\right|
\leq\frac{\varepsilon_v+|a|\varepsilon_x}{|b|}.
$$

**证明。** 第一式由 $x'=-ax+by$ 解出 $y$。第二式将重建误差写成

$$
\frac{(\widehat v-x')+a(\widehat x-x)}{b}
$$

并应用三角不等式。

**定理。** 若 $t\geq0$，$x$ 在 $[0,t]$ 上连续且 $y$ 在该区间满足隐藏方程，则

$$
y(t)=e^{-dt}\left(y(0)-b\int_0^t e^{ds}x(s)\,ds\right).
$$

因此可见变量满足精确 Volterra 方程

$$
x'(t)=-ax(t)+be^{-dt}y(0)
+\int_0^tK(t-s)x(s)\,ds,
\qquad
K(\tau)=-b^2e^{-d\tau}.
$$

**证明。** 对 $e^{dt}y(t)$ 求导，得

$$
\frac{d}{dt}\bigl(e^{dt}y(t)\bigr)=-be^{dt}x(t).
$$

在 $[0,t]$ 上积分并乘以 $e^{-dt}$ 得隐藏历史公式。将其代入 $x'=-ax+by$，再用

$$
e^{-dt}e^{ds}=e^{-d(t-s)}
$$

即得卷积形式及核 $K$。

**定理。** 对相同可见输入 $x$，若 $y,z$ 是两个隐藏解且 $d>0$，则

$$
|b(y(t)-z(t))|
\leq |b|e^{-dt}|y(0)-z(0)|.
$$

**证明。** 差 $q=y-z$ 满足 $q'=-dq$，故 $q(t)=e^{-dt}q(0)$；取绝对值并乘以 $|b|$。

**定理。** 若 $d\ne0$ 且隐藏方程处于稳态，即 $-bx-dy=0$，则

$$
y=-\frac{b}{d}x,qquad
-ax+by=-\left(a+\frac{b^2}{d}\right)x.
$$

**证明。** 第一式由稳态方程除以 $d$ 得到；代入可见方程右端并整理即得第二式。
### TR.15 (a,−1)-Fibonacci 不动点与 Benfield–Lippard 猜想 6.5(v) 的反例

#### 定义 15.1 序列、Pisano 周期与不动点

对整数 $a$，定义 $(a,-1)$-Fibonacci 序列

$$
U_0=0,\qquad U_1=1,\qquad U_{n+2}=aU_{n+1}-U_n\quad(n\geq0).
$$

对整数 $m>1$，其 Pisano 周期 $\pi_{(a,-1)}(m)$ 是满足
$(U_T,U_{T+1})\equiv(0,1)\pmod m$ 的最小正整数 $T$；若
$\pi_{(a,-1)}(m)=m$，则称 $m$ 为不动点。
递推在相邻两项上的变换可逆，因此模 $m$ 的序列从初始项起即为周期序列。
令

$$
A_a=\begin{pmatrix}a&-1\\1&0\end{pmatrix}.
$$

由于 $\det A_a=1$，它模 $m$ 属于有限群 $\mathrm{SL}_2(\mathbb Z/m\mathbb Z)$。
递推归纳给出，对 $n\geq1$，

$$
A_a^n=\begin{pmatrix}U_{n+1}&-U_n\\U_n&-U_{n-1}\end{pmatrix}.
$$

当 $(U_n,U_{n+1})\equiv(0,1)$ 时，递推还给出 $U_{n-1}\equiv-1$，
故该返回条件等价于 $A_a^n\equiv I\pmod m$。
因此 $\pi_{(a,-1)}(m)$ 也就是 $A_a$ 模 $m$ 的乘法阶。

#### 引文 15.2 猜想的正参数第五分支与临界素数

Benfield–Lippard，*Fixed points of K-Fibonacci sequences*，
arXiv:2404.08194v2，§6「Final Thoughts」的猜想 6.5
（文献条目 [benfieldlippard2024fixedpoints](../../../Library/ArithUnits/benfieldlippard2024fixedpoints.md)）
先令 $p_1^{e_1}\cdots p_t^{e_t}$ 为 $a^2+4b$ 的素因数分解，取 $b=-1$、$a>2$。
对每个 $m>1$ 及非负整数 $j_1,\ldots,j_t$，猜想以五个分支刻画
$\pi_{(a,-1)}(m)=m$ 的充要条件。其中第 (v) 项原文为：

> (v) $a \equiv -1 \pmod{6}$ and $m = p_i^{j_i}$ or $m = 6 \cdot p_1^{j_1+1} \cdots p_t^{j_t}$.

这里 $p_i$ 均取自 $a^2-4$ 的素因数；第二种形式中的 $j_1+1$ 保留原文。
因此这一分支的必要方向声称：当 $a>2$ 且 $a\equiv-1\pmod6$ 时，
任何不动点 $m>1$ 都是一个素数幂，或是 $6$ 的倍数。

紧接猜想的文字为：

> It appears that in the previous conjecture, only one prime has powers that are fixed points for any given $a$; let this be the *critical prime* for the $(a,-1)$-Fibonacci sequence.

作者继而指出这个素数不总是 $a^2-4$ 的最小或最大素因数，并说 $a=3$ 是没有临界素数的特殊情形。
这一段是猜想之后的观察，不是已经证明的唯一性定理。

#### 命题 15.3 混合模数十五的反例及其参数族

对 $a=47$，有

$$
\pi_{(47,-1)}(15)=15,\qquad
47\equiv-1\pmod6,\qquad 47^2-4=2205=3^2\cdot5\cdot7^2.
$$

不动点 $15$ 不属于引文 15.2 第 (v) 项列出的任何一种形式，
所以该项的「仅当」方向为假。
更一般地，每个满足 $a>2$ 且 $a\equiv47\pmod{30}$ 的整数 $a$
都有 $\pi_{(a,-1)}(15)=15$，并给出同一分支的反例。

证明。若 $a\equiv2\pmod r$，递推与初值归纳给出 $U_n\equiv n\pmod r$。
对 $a=47$，模 $3$ 与模 $5$ 的剩余序列分别为

$$
\begin{aligned}
(U_n\bmod3)_{n\geq0}&=0,1,2,0,1,2,\ldots,\\
(U_n\bmod5)_{n\geq0}&=0,1,2,3,4,0,1,2,3,4,\ldots.
\end{aligned}
$$

返回初始相邻对 $(0,1)$ 的正时刻分别恰为 $3$ 和 $5$ 的正倍数。
由中国剩余定理，模 $15$ 返回等价于同时模 $3$、模 $5$ 返回，故

$$
\pi_{(47,-1)}(15)
=\operatorname{lcm}\bigl(\pi_{(47,-1)}(3),\pi_{(47,-1)}(5)\bigr)
=\operatorname{lcm}(3,5)=15.
$$

$15=3\cdot5$ 有两个不同素因数，不是任何单一素数的幂，且 $6\nmid15$；
这同时排除了第 (v) 项的两种形式。
若 $a\equiv47\pmod{30}$，则仍有 $a\equiv2\pmod{15}$ 及
$a\equiv-1\pmod6$，相同的剩余序列与排除论证逐字适用。证毕。

#### 命题 15.4 两个完整的素数幂不动点塔

对每个整数 $e\geq1$，

$$
\pi_{(47,-1)}(3^e)=3^e,\qquad
\pi_{(47,-1)}(5^e)=5^e.
$$

因此，同一参数 $a=47$ 下，两个不同素数 $3,5$ 的全部正整数次幂都是不动点；
引文 15.2 的临界素数唯一性观察即使按完整幂塔理解也不成立。

证明。写 $A=A_{47}$。直接整数矩阵乘法给出

$$
\begin{aligned}
A^3&=I+3B_3,&
B_3&=\begin{pmatrix}34576&-736\\736&-16\end{pmatrix},\\
A^5&=I+5B_5,&
B_5&=\begin{pmatrix}45785971&-974611\\974611&-20746\end{pmatrix}.
\end{aligned}
$$

两个种子的左上角分别满足 $34576\equiv1\pmod3$ 与
$45785971\equiv1\pmod5$，所以 $B_p$ 至少有一个元素不被 $p$ 整除。
命题 15.3 的剩余序列还给出 $A$ 模 $p$ 的阶恰为 $p$，其中 $p=3,5$。

以下提升论证适用于任意奇素数 $p$ 以及满足
$A^p=I+pB$、$B\not\equiv0\pmod p$ 的整数矩阵 $A,B$。
对每个整数 $r\geq1$，归纳构造整数矩阵 $D_r$，使得

$$
A^{p^r}=I+p^rD_r,\qquad D_r\equiv B\pmod p.
$$

$r=1$ 时取 $D_1=B$。若结论对 $r$ 成立，因 $I$ 与 $D_r$ 交换，
普通二项式展开在它们生成的交换子环中给出

$$
A^{p^{r+1}}
=(I+p^rD_r)^p
=I+p^{r+1}D_r+\sum_{k=2}^{p}\binom pk p^{rk}D_r^k.
$$

当 $2\leq k\leq p-1$ 时，$p\mid\binom pk$ 且
$rk+1\geq r+2$；当 $k=p$ 时，$rp\geq r+2$，这里使用 $p\geq3$。
所以末项之和逐元素被 $p^{r+2}$ 整除，能够写成
$p^{r+2}E_r$。取 $D_{r+1}=D_r+pE_r$ 即得归纳步。
等价地，对每个 $j\geq0$ 存在整数矩阵 $C_j$ 使

$$
A^{p^{j+1}}=I+p^{j+1}(B+pC_j).
$$

于是 $A^{p^e}\equiv I\pmod{p^e}$，其阶整除 $p^e$。
当 $e\geq2$ 时，$D_{e-1}\equiv B\not\equiv0\pmod p$，故
$A^{p^{e-1}}-I=p^{e-1}D_{e-1}$ 不被 $p^e$ 逐元素整除。
阶既整除 $p^e$ 又不整除 $p^{e-1}$，只能等于 $p^e$。
$e=1$ 的阶已由剩余序列确定；分别代入两个种子即得全部结论。证毕。

#### 注记 15.5 黄金坐标与 Wall–Sun–Sun 边界

若 $\varphi^2=\varphi+1$，则 $\varphi^8=13+21\varphi$，其迹为
$L_8=2\cdot13+21=47$；相应基矩阵
$\left(\begin{smallmatrix}21&0\\13&-1\end{smallmatrix}\right)$ 的行列式为
$-21=-F_8$，故只有在 $21$ 模 $m$ 可逆时它才是可逆基变换。

经典 Wall–Sun–Sun 问题针对普通 Fibonacci 递推
$F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$，询问是否存在素数 $p\ne2,5$ 使
$p^2\mid F_{p-(5/p)}$，其中 $(5/p)$ 为 Legendre 符号。
命题 15.3 与 15.4 针对 $(47,-1)$ 递推，并未判定这一经典存在性问题。

## 追加锚（本行以下为增补区）
