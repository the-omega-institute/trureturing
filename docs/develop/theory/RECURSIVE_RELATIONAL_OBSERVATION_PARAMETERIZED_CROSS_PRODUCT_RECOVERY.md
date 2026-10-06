# 递归关系观察：参数化叉积原树的预测、符号损失与制备恢复

本卷在同一套非空有序二标签树上，分别研究完整数值未来、对所有制备成立的符号行为，以及原始叶对的恢复。树的原生替换始终保持所供制备；参数变化只用于解释运输。三种目标所需的记录、观察权限和恢复条件不同。

这里给出普通数学证明与有限精确核验，不提供新的 Lean 形式化，也不将散文证明或有限计算称为内核验证。经典叉积恒等式、单位方向标签、组成计数、数量反演及一般纤维判据均为复用工具。正文中的恢复是声明来源、读口和更新合同下的数学恢复，不包含物理制备、有限位传感或新的原生控制权限。

## 1. 原树、额外制备与一条实际历史

**定义 1.1（非空有序来源与原生替换）。** 来源集合 $\mathcal T$ 由有限语法

$$
t::=\alpha\mid\beta\mid\langle s,t\rangle
$$

生成。左右次序、每层括号和两种叶标签都属于来源身份；不施加交换律、结合律，也没有空树。固定

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

记实际叶数组成为 $\nu(t)=(m,n)\in\mathbb N^2$，满足 $m+n\ge1$，两个叶的组成为 $(1,0),(0,1)$，节点组成相加。复用 [Atomic §3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的

$$
\nu(\rho t)=M\nu(t),\qquad M(m,n)=(n,m+n),\qquad M^2=M+I.
$$

**定义 1.2（参数化结构解释）。** 主载体为定向欧氏空间 $V=\mathbb R^3$，二元运算为原定向叉积。制备 $p=(a,b)\in\mathcal P=V^2$ 是额外供应的实向量数据。同一棵树中每个 $\alpha$ 都取同一个 $a$，每个 $\beta$ 都取同一个 $b$；不允许给每次叶出现独立赋值。结构解释唯一地满足

$$
E_p(\alpha)=a,\quad E_p(\beta)=b,\quad
E_p(\langle s,t\rangle)=E_p(s)\times E_p(t).
$$

实际增广来源为 $\mathcal J=\mathcal T\times\mathcal P$，实际源更新为

$$
S(t,p)=(\rho t,p),\qquad x_j(t,p)=E_p(\rho^jt)\quad(j\ge0).
$$

这直接使用 [Atomic §2](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的唯一结构延拓，没有改变原构造。

**约定 1.3（付费数值观察）。** 基本取得合同只供应一棵未知当前树及其固定未知制备。Read 返回当前精确向量、不改源；一次 $\rho$ 覆盖唯一当前源。读调用、实际更新、回复宽度、保留记录、程序、运算、精度及时间／动作／Stop 身份分别计费。初始化不供应树码、组成、叶对或校准。数量读、树码读、额外制备记录及同制备配对权限仅在明确增加它们的章节使用。确定协议只依公共合同和已取得记录选择下一事件，须在其声明域内有限停止；数值下界不使用时间或源大小侧信道。

数学解码、静态上下文和解释运输均不授予源的逆更新、复制、复位、归一化、旋转、重制备、叶重命名或任意外部向量输入。两个 live 句柄的 graft 另须有实际共同制备及权限；单个句柄的 $\rho$ 数值协议无需 graft。

## 2. 经典代数与二生成切面

**约定 2.1（Gram 数据与五个向量）。** 对任意制备置

$$
\begin{gathered}
A=|a|^2,\quad B=|b|^2,\quad C=a\cdot b,\quad
\Delta=AB-C^2,\\
K=b\times a,\qquad L=K\times a=Ca-Ab,\qquad
N=K\times b=Ba-Cb,\qquad F(a,b)=(b,K).
\end{gathered}
$$

$F$ 是解释参数的数学映射，不是实际源菜单中的动作。$\Delta>0$ 恰表示 $a,b$ 线性独立。

**引理 2.2（重复向量恒等式与切面）。** 所用叉积满足

$$
\langle u\times v,w\rangle=\langle u,v\times w\rangle,\qquad
|u\times v|^2=|u|^2|v|^2-\langle u,v\rangle^2,
$$

并有

$$
u\times(v\times u)=|u|^2v-\langle u,v\rangle u.
$$

因此 $K\perp a,b$、$|K|^2=\Delta$，约定2.1的 $L,N$ 公式成立。若 $\Delta>0$，$U_p=\operatorname{span}\{a,b,K\}$ 是闭合三维叉积切面；若 $\Delta=0$，叶生成空间至多一维，内部叉积全为零。

证明。极化范数式得

$$
\langle u\times v,u\times w\rangle
=|u|^2\langle v,w\rangle-\langle u,v\rangle\langle u,w\rangle.
$$

对任意 $z$，循环配对及此式给

$$
\langle u\times(v\times u),z\rangle
=\langle z\times u,v\times u\rangle
=|u|^2\langle z,v\rangle-\langle u,z\rangle\langle u,v\rangle.
$$

内积非退化给恒等式。垂直性来自交替性与循环配对；范数式给 $|K|^2$。于是 $a\times b=-K$，$K\times a,L$ 和 $K\times b,N$ 均在叶平面内，双线性证明 $U_p$ 闭合。独立时三生成元线性独立；依赖时每个内部节点的叉积为零。

**约定 2.3（七维扩展的准确范围）。** 同样允许 $V=\operatorname{Im}\mathbb O$，其中 $\mathbb O$ 是正定范数的实除八元数代数，$u\times v=(uv-vu)/2$。Baez 的两生成结合性和 Darpö 的向量积配对／范数恒等式给引理2.2的同一证明；每个实际树及所有 $F^j(p)$ 都在同一二生成切面内。因此下文的全树结论也适用于这项解释。循环标架映射只在该三维切面上定义；不声称任意七维元组的递推、全 $SO(7)$ 等变或相应控制。七维版本使用标量三重积，不能写成七维行列式。

对固定 $p$，$E_p(\mathcal T)$ 可数且只是 $U_p$ 的子集；树码有限且可数。它不等于该切面、球面或线性张成。跨所有所供 $p$ 的像是 $V$，因为叶 $\alpha$ 可取任意 $a$；这个连续来源完全由额外制备端口供应。

## 3. 解释运输、实际参数像与不可逆性

**定理 3.1（原替换的全树运输）。** 对所有 $t\in\mathcal T,p\in\mathcal P,j\ge0$，

$$
E_p(\rho^jt)=E_{F^j(p)}(t).
$$

$F$ 的 Gram 更新为 $(A,B,C)\mapsto(B,\Delta,0)$。

证明。一阶两侧在 $\alpha$ 处同为 $b$、在 $\beta$ 处同为 $b\times a$，并保持同一个有序叉积节点；结构归纳使两侧对所有树相等。重复应用此等式给所有 $j$。$K\perp b$ 且 $|K|^2=\Delta$ 给 Gram 更新。实际执行仍是 $(\rho^jt,p)$，这个等式没有执行 $F$ 制备。

**定理 3.2（解释参数的实际像及完整纤维）。** 有

$$
F(\mathcal P)=\{(v,w):v\ne0,\ v\cdot w=0\}\cup\{(0,0)\}.
$$

对 $v\ne0$，任意这样的 $(v,w)$ 的全部原像恰为

$$
F^{-1}(v,w)=
\left\{\left(\frac{w\times v+\tau v}{|v|^2},v\right):\tau\in\mathbb R\right\};
$$

零像的纤维为 $\{(a,0):a\in V\}$。在

$$
\mathcal O=\{(u,v):u,v\ne0,\ u\perp v\}
$$

上 $F$ 是双射，数学逆为

$$
F^{-1}(v,w)=\left(-\frac{v\times w}{|v|^2},v\right).
$$

在独立制备域上，每个 $F^j,j\ge1$ 与 $F$ 有相同纤维。在全域上，每个 $j\ge2$ 的像为 $\mathcal O\cup\{(0,0)\}$，其零纤维恰为全部依赖制备。

证明。任何像都满足 $b\perp K$，而 $b=0$ 强迫 $K=0$。若 $v\ne0,w\perp v$，引理2.2给 $v\times(w\times v)=|v|^2w$，故 $a_0=(w\times v)/|v|^2$ 是一原像的第一坐标。范数式说明 $v\times(a-a_0)=0$ 当且仅当差平行于 $v$；以 $\tau=a\cdot v$ 参数化即得全部纤维。$v=0$ 强迫 $b=0$，$a$ 任意。

在 $\mathcal O$ 上纤维唯一的正交原像取 $\tau=0$，且非零，故所给逆确实在 $\mathcal O$ 内。独立制备一次进入 $\mathcal O$，后续在那里双射，不能再改变纤维。依赖制备先到 $(b,0)$，再到 $(0,0)$；独立制备永不为零。反复使用 $\mathcal O$ 中的逆使每个非零正交对在任意指定 $j$ 都实际可达，给全部像结论。

**命题 3.3（来源单射与解释损失分开）。** 原树替换 $\rho$ 单射；这不赋予 $F$、数值记录或实际源逆动作。

证明。复用 [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) 的原树接口与替换单射结论。其解码依据是：没有 $\rho$ 像为叶 $\alpha$；叶 $\beta$ 只来自 $\alpha$；$\langle\beta,\alpha\rangle$ 只来自 $\beta$，不能来自内部树，因为内部像的右孩子不可能为 $\alpha$。其它内部像分别对有序孩子递归解码，有限树归纳给单射。该解码是实际像上的数学恢复，与定理3.2的参数纤维不同。

## 4. 五符号归约与全树带符号尾递推

**定义 4.1（单位标签）。** 固定正交单位叶 $e_1,e_2$，令 $f_1=e_1,f_2=e_2,f_3=e_2\times e_1$。这是左手叉积标架；索引按模三循环。记

$$
\chi(t)=E_{(e_1,e_2)}(t)\in\{0,\pm f_1,\pm f_2,\pm f_3\}.
$$

复用 [Boundary Geometry 定理7.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) 的全树单位标签与循环运输：$R_0f_i=f_{i+1}$ 保持叉积，$\chi(\rho t)=R_0\chi(t)$。七值都由实际叶或有序节点实现。这个复用只针对该固定单位解释。

**引理 4.2（全制备五符号表与初值符号）。** 对任意 $p$，以下为完整上三角叉积表；同符号乘积为零，反序取负。

| 4符号 $\times$ | $b$ | $K$ | $L$ | $N$ |
| --- | --- | --- | --- | --- |
| 4表 $a$ | $-K$ | $-L$ | $AK$ | $CK$ |
| 4表 $b$ | — | $-N$ | $CK$ | $BK$ |
| 4表 $K$ | — | — | $-\Delta a$ | $-\Delta b$ |
| 4表 $L$ | — | — | — | $-\Delta K$ |

每棵树可递归选择一个恒等于 $E_p(t)$、对所有 $p$ 同时有效的描述子：零，或

$$
\varepsilon A^iB^jC^h\Delta^\ell Z,
\quad \varepsilon\in\{\pm1\},\ i,j,h,\ell\in\mathbb N,
\quad Z\in\{a,b,K,L,N\}.
$$

描述子不要求唯一。所选描述子非零且 $h=0$ 恰等价于 $\chi(t)\ne0$。在 $\Delta>0$ 时：若 $\chi(t)=\sigma f_1$，初值为 $\sigma$ 乘一个严格正数再乘 $a$ 或 $N$；若标签为 $\sigma f_2$，初值相应为 $\sigma$ 乘正数再乘 $b$ 或 $-L$；若标签为 $\sigma f_3$，初值为 $\sigma$ 乘正数再乘 $K$。

证明。前几项由定义和反序符号得到。代入 $L=Ca-Ab,N=Ba-Cb$，得到 $a\times L=AK,a\times N=CK,b\times L=CK,b\times N=BK$。$K\perp a,b$ 给 $K\times(K\times a)=-\Delta a$ 及对应的 $b$ 式。最后双线性展开

$$
(Ca-Ab)\times(Ba-Cb)=-(AB-C^2)K.
$$

这证明十个非对角项。叶描述子为 $a,b$；在节点处相乘子描述子的单项式，再查此完整表，零孩子或同符号即为零，其余仍有要求的形状。结构归纳不作任何除法，覆盖 $C=0$ 或 $\Delta=0$。

在单位参考处 $A=B=\Delta=1,C=0,L=-f_2,N=f_1$，五个符号都非零，故描述子恰在零或正 $C$ 次数时消失。$\Delta>0$ 且 $h=0$ 时 $A,B,\Delta$ 均正，单位处的方向和符号给所列三类。零标签的树在非正交制备处仍可有非零初值，不能把它在所有制备处判成零。

**定理 4.3（全树尾的实际标架与递推）。** 设 $\Delta>0$，置 $r=\sqrt B,s=\sqrt\Delta$ 以及

$$
g_1=b/r,\qquad g_2=K/s,\qquad g_3=N/(rs).
$$

它们是 $U_p$ 中的左手正交单位标架。令 $R$ 循环 $g_i$，则 $R$ 保持切面内叉积。若 $\nu(t)=(m,n)$、$\chi(t)=\sigma f_i\ne0$，则

$$
\begin{aligned}
x_1&=\sigma r^m s^n g_i,\\
x_2&=\sigma s^m(rs)^n g_{i+1},\\
q_{j+2}&=q_jq_{j+1},\qquad q_j=|x_j|\quad(j\ge1),\\
x_{j+2}&=\sigma(x_{j+1}\times x_j)=|x_j|R x_{j+1}\quad(j\ge1).
\end{aligned}
$$

若 $\chi(t)=0$，全部 $x_j,j\ge1$ 为零。若 $\Delta=0$，全部 $x_j,j\ge2$ 为零。

证明。$K\perp b,N=K\times b$ 且 $|N|^2=B\Delta$ 给正交单位性。叉积表为 $g_{i+1}\times g_i=g_{i+2}$，所以循环保持乘法。按叶数的结构归纳给齐次性

$$
E_{(r g_1,s g_2)}(t)=r^m s^n\chi_g(t),
$$

其中 $\chi_g$ 将 $f_i$ 换成 $g_i$，并保持零及符号。定理3.1把 $x_1$ 写为此式，$x_2$ 则使用叶对 $(s g_2,rs g_3)$。此后每次标签循环，组成按 $M$ 更新。由 $M^2=M+I$，相隔两步的每个指数是前两步指数之和，故正幅度满足乘法递推；标架表和 $\sigma^2=1$ 给带符号叉积式。零标签在正交的 $F(p)$ 处齐次求值为零，之后仍零。依赖分支的 $F^2(p)=0$ 给第二项后的全零结论。

## 5. 无校准三次向量读取的尖锐全树闭合

**定理 5.1（初始三读的全称恢复式）。** 规定 $\operatorname{sgn}(0)=0$。对每个实际 $t,p$ 都有

$$
x_3=\operatorname{sgn}\bigl(x_0\cdot(x_2\times x_1)\bigr)(x_2\times x_1).
$$

在三维中符号也可写为 $-\operatorname{sgn}\det(x_0,x_1,x_2)$。令 $W_3(t,p)=(x_0,x_1,x_2)$、$\mathcal B_3=W_3(\mathcal J)$，则其实际像上的后继为

$$
G(x,y,z)=\bigl(y,z,\operatorname{sgn}(x\cdot(z\times y))(z\times y)\bigr).
$$

任意两个实际来源，即使树和制备都未知，$W_3$ 相同当且仅当包含时刻零的完整向量 $\rho$ 未来相同。任意长度至少三的连续初始记录也决定完整未来。

证明。先取 $\Delta>0$、非零标签 $\sigma f_i$。令 $w=x_2\times x_1$；定理4.3给 $w$ 是 $g_{i+2}$ 的严格正倍数，$x_3=\sigma w$。须由初值确定 $\sigma$。若 $i=1$，$w$ 是 $N$ 的正倍数，而引理4.2的两种初值方向满足 $a\cdot N=\Delta>0,N\cdot N=B\Delta>0$。若 $i=2$，$w$ 是 $b$ 的正倍数，$b\cdot b=B>0,(-L)\cdot b=\Delta>0$。若 $i=3$，两者所用方向为 $K$，$|K|^2=\Delta>0$。每种情况都给 $\operatorname{sgn}(x_0\cdot w)=\sigma$。

零标签时 $x_1=x_2=x_3=0$，尽管 $x_0$ 可能非零；依赖制备时 $x_2=x_3=0$。这两分支的 $w$ 均为零，所以公式仍成立。在三维 $x_0\cdot(x_2\times x_1)=-\det(x_0,x_1,x_2)$，给等价符号。

将同一全称公式依次应用于实际树 $\rho t,\rho^2t,\ldots$，得 $G(W_3(t,p))=W_3(\rho t,p)$，后继仍实际可达。归纳恢复所有后项；反向完整未来相同包含前三项。较长记录的末三项恢复继续的后项，而原有前缀保留时刻零。此证明只断言 $\mathcal B_3$ 的闭合，没有断言任意环境三元组可达。

**命题 5.2（同一制备的两读反例与窗口下界）。** 在全树连续窗口约定下，三是统一最短长度；甚至一个固定制备即可反驳长度二的闭合。取

$$
a=(5/4,0,0),\quad b=(3/4,1,0),\quad
\lambda=25/16,
$$

则 $A=B=\Delta=\lambda,C=15/16$。令 $k=\langle\beta,\alpha\rangle$、

$$
t_A=\langle\alpha,\langle k,\alpha\rangle\rangle,
\qquad t_B=\langle\beta,\langle k,\beta\rangle\rangle.
$$

二者前三项为

$$
\begin{array}{c|ccc}
&x_0&x_1&x_2\\\hline
t_A&AK&BN&\Delta^2b\\
t_B&BK&\Delta N&B\Delta^2b
\end{array}
$$

前两项相同，第三项不同。

证明。引理4.2给初值 $AK,BK$。在 $F(p)$ 处 $A'=B,B'=\Delta,K'=N$，得到第二项。在 $F^2(p)$ 处 $A''=\Delta,B''=B\Delta,K''=N\times K=\Delta b$，得到第三项；$b\ne0,\lambda\ne1$ 排除相等。因而两窗口的实际后继不能为函数。将二树各先替换一次，当前值相同、下一值不同，排除一窗口闭合；零观察由 $\alpha$ 与 $\langle\alpha,\alpha\rangle$ 的初值不同排除。三窗口充分性由定理5.1给出。这是全树的统一连续窗口界，不是每个制备分别的最短界、任意编码的存储界或规范轨道的界。

**命题 5.3（数值后继无逆及规范轨道例外）。** 在 $C\ne0,\Delta>0$ 时，树

$$
t=\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle
$$

有初值 $CK$、零标签，故 $W_3(t,p)=(CK,0,0)$。零 cherry $\langle\alpha,\alpha\rangle$ 的记录为 $(0,0,0)$；两者经 $G$ 均到零。因此 $G$ 没有实际像上的逆。

另在规范来源 $T_j=\rho^j\alpha$ 上，原结构关系为 $T_{j+2}=\langle T_{j+1},T_j\rangle$，所以对所有 $p$ 有 $E_p(T_{j+2})=E_p(T_{j+1})\times E_p(T_j)$。这个已知规范轨道的二值递推不延伸到全部树；命题5.2给了实际反例。它也没有赋予 Clifford 叶积的逆或六周期。

## 6. 实际联合像、纤维和同制备上下文

**定理 6.1（三向量像与组成标记的两向量像）。** 固定 $p$，$\mathcal B_{3,p}=W_3(\mathcal T\times\{p\})$ 恰为 $V^3$ 中由

$$
(a,b,K),\qquad(b,K,N)
$$

生成的最小逐坐标有序叉积子 magma。未知制备像为 $\bigcup_p\mathcal B_{3,p}$。

另一实际记录为 $\eta_p(t)=(\nu(t),E_p(t),E_p(\rho t))$。定义

$$
D_p(0,0)=\varnothing,\quad D_p(1,0)=\{(a,b)\},\quad
D_p(0,1)=\{(b,K)\}.
$$

对 $m+n\ge2$，$D_p(m,n)$ 为所有有序非空分拆 $(m,n)=d+e$ 的以下集合之并：

$$
\{(u\times u',v\times v'):(u,v)\in D_p(d),\ (u',v')\in D_p(e)\}.
$$

则 $\eta_p(\mathcal T)$ 恰为 $\bigcup_{m+n\ge1}\{(m,n)\}\times D_p(m,n)$，每个 $D_p(m,n)$ 有限并带实际树见证。

证明。解释和 $\rho$ 都保持有序节点，故 $W_3(\langle s,t\rangle,p)$ 是两子记录的逐坐标叉积。结构归纳给生成集合的一侧包含，反向将任意有限生成表达式解释成对应原树。两向量递归的一侧包含用实际根分拆；反向对叶数归纳，为所选两个孩子记录取得实际树，再在同一 $p$ 下有序 graft。每个分拆的孩子叶数严格减少，有限分拆及有限子集合保证有限性。这里未将两个边缘像改成自由乘积或线性张成。

组成为 $(m,n)$ 的原树数直接复用 GenealogicalFiberTransport 的

$$
\operatorname{Catalan}_{m+n-1}\binom{m+n}{m}\quad(m+n\ge1).
$$

其来源对应为：$L=m+n$ 个有序叶的满二叉形状有 $\operatorname{Catalan}_{L-1}$ 种，每形状选择 $m$ 个叶位标 $\alpha$。求值可合并这些树，不能把此数当作 $|D_p(m,n)|$。零组成的实际来源纤维为空，不套用自然数减法总化的数值表达式。

**定理 6.2（固定制备的严格单孔上下文）。** 固定 $p$，允许有限上下文

$$
\mathsf C::=\square\mid\rho\mathsf C\mid
\langle u,\mathsf C\rangle\mid\langle\mathsf C,u\rangle,
\qquad u\in\mathcal T,
$$

旁树 $u$ 使用同一制备。两树的 $W_3$ 相同，当且仅当每个这种上下文的当前向量读数相同。

证明。相等记录经 $G$ 保持相等；graft 时旁树的同一实际记录逐坐标相乘也保持相等。按上下文结构归纳得到其当前输出相同。反向取 $\square,\rho\square,\rho^2\square$ 恢复三坐标。这是对每个静态反事实上下文的全称比较，不是在一个破坏性源上实际执行所有上下文。

**命题 6.3（未知制备与配对合法性的边界）。** 跨制备的 $W_3$ 相等足以保持 $\rho$ 未来，却不足以保持使用各自原叶的全部上下文。取同一树 $\beta$，

$$
p=(e_1,e_2),\qquad p'=(e_1+\lambda e_2,e_2),\quad\lambda\ne0.
$$

二者记录都是 $(e_2,-e_3,e_1)$。上下文 $\langle\alpha,\langle\alpha,\square\rangle\rangle$ 却分别给 $-e_2$ 和 $\lambda e_1-e_2$。

证明。两制备有相同 $b,K,N$。后一个上下文为 $a\times(a\times b)=Ca-Ab$；代入各自的 $A,C$ 得所列不等输出。使用的是各自原标签的旁树，未加入任意外部向量。

两个待配对句柄必须实际同制备；单凭数值 $W_3$ 或 $\eta$ 不能判断该守卫，因为零 cherry 在每个制备处都给零向量记录及同一组成。须另保留权威共同制备身份，或确实所供的 $p$；身份本身不供应数值校准。不合法配对应记录独立失败符号，区别于成功零输出。新增部分操作要下降时，其定义域与后继行为必须在实际联合记录纤维上恒定；这是 [Continuation 定理13.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的合法域饱和条件，而非创建句柄或复制来源的权限。

**定理 6.4（固定制备完整数值响应的精确纤维）。** 对 $\Delta>0$，记 $r=\sqrt B,s=\sqrt\Delta$。

1. 若 $\chi(t)=0$，同一完整响应纤维恰由满足 $\chi(u)=0,E_p(u)=E_p(t)$ 的树组成。
2. 若 $\chi(t)\ne0$ 且 $(r,s)\ne(1,1)$，纤维恰由 $\nu(u)=\nu(t),\chi(u)=\chi(t),E_p(u)=E_p(t)$ 的树组成。
3. 若 $\chi(t)\ne0$ 且 $r=s=1$，纤维恰由 $\chi(u)=\chi(t),E_p(u)=E_p(t)$ 的树组成，组成可不同。

证明。零标签尾全零，非零标签尾非零，所以两分支不混合。非零分支的 $x_1$ 方向确定同一标签索引及符号。若两组成之差为 $(d_m,d_n)$，$x_1,x_2$ 幅度相同给

$$
\begin{aligned}
d_m\log r+d_n\log s&=0,\\
d_n\log r+(d_m+d_n)\log s&=0.
\end{aligned}
$$

非零整数差时行列式 $d_m^2+d_md_n-d_n^2\ne0$：$d_n=0$ 直接成立，$d_n\ne0$ 时若为零，会使有理数 $d_m/d_n$ 等于无理根 $(-1\pm\sqrt5)/2$。因此非零差迫使两对数为零。非单位 $(r,s)$ 只能有零组成差；单位分支的全部尾幅度为一，只由标签决定。反向用定理4.3恢复各尾，再用初值条件补时刻零；零标签分支只有初值条件。

**命题 6.5（全部退化纤维与语法遗失）。** 当 $\Delta=0,b\ne0$，恰有三种不同完整记录：叶 $\alpha$ 的 $(a,b,0)$，叶 $\beta$ 的 $(b,0,0)$，全部内部树的 $(0,0,0)$。当 $b=0,a\ne0$，只有 $\alpha$ 为 $(a,0,0)$，其它树全零；$a=b=0$ 时全树合并。

证明。依赖叶的每个内部叉积为零；$F(p)=(b,0),F^2(p)=0$ 给三个坐标，所列非零条件区分各类。对未知制备，一给定实际记录 $(x,y,z)$ 的纤维准确写为

$$
\bigcup_{t\in\mathcal T}
\{(t,p):E_p(t)=x, E_{F(p)}(t)=y, E_{F^2(p)}(t)=z\}.
$$

每个指定树贡献有限组关于 $p$ 的多项式坐标方程；这个并只取实际树与允许制备，不断言一般唯一性。

任何上述行为记录都不能恢复完整语法。$\langle\alpha,\alpha\rangle$ 与 $\langle\beta,\beta\rangle$ 在每个 $p$ 都为零但组成不同；三个 $\alpha$ 的两种括号均为零但形状不同；$\langle\langle\alpha,\alpha\rangle,\langle\beta,\beta\rangle\rangle$ 与反序接合组成同为 $(2,2)$、全响应零但原树不同。这些也是后文全参数符号记录的实际反例。

## 7. 实际尾像及条件二值补充

**定义 7.1（已替换来源的尾记录）。** 取 $\mathcal X_1=\rho(\mathcal T)\times\mathcal P$，当前源的向量及下一向量记为 $y,z$。非零尾的单位标签符号记为 $\epsilon\in\{\pm1\}$；若 $z\times y=0$ 则统一记 $\epsilon=+1$。目标为当前及全部后续向量，记录为 $\theta=(y,z,\epsilon)$。

**定理 7.2（尾记录的精确实际像与尖锐二值区别）。** 有

$$
\theta(\mathcal X_1)=
\{(y,z,\epsilon):y,z\ne0,\ y\perp z,\ \epsilon\in\{\pm1\}\}
\cup\{(y,0,+1):y\in V\}.
$$

不存在实际 $(0,z),z\ne0$。非零分支后继为 $(z,\epsilon(z\times y),\epsilon)$，零下一值分支后继为 $(0,0,+1)$。固定任一非零正交数值对 $(y,z)$，恰有两个完整未来类；在 $(y,0)$ 上恰有一个。相对于已保留精确 $y,z$ 的配对记录，二值补充必要且充分。

证明。定理4.3给非零尾的正交连续向量和带符号递推；零标签尾全零；依赖制备的已替换当前值可非零，但下一项和以后全零。这给像的一侧包含及不存在 $(0,z\ne0)$。

反向对任意非零正交 $y,z$，取当前树 $\beta=\rho\alpha$，供应 $b=y,a=-y\times z/|y|^2$，得到当前和下一值 $y,z$，标签符号为正。为实现负号，令 $t_* =\langle\beta,\langle\beta,\alpha\rangle\rangle$，其单位标签为 $-f_1$。置

$$
Y=|y|^2,\quad Z=|z|^2,\quad
D_0=Y^2/Z,\quad B_0=Z^2/Y^3,
$$

并供应

$$
b=-y/D_0,\qquad K=-z/(B_0D_0),\qquad a=(K\times b)/B_0.
$$

直接算得 $b\perp K,|b|^2=B_0,|K|^2=D_0$。引理2.2给 $b\times a=K$，故是实际制备。树 $t_*$ 的通式为 $-N$，因此当前树 $\rho t_*$ 的值为 $-D_0b=y$，下一值为 $-B_0D_0K=z$，其标签符号为负。两个见证共享同一数值对，未要求它们制备相同。任意 $y$ 的 $(y,0,+1)$ 由当前 $\beta$ 和制备 $(0,y)$ 实现。七维时每个构造仍在其二生成切面内。

非零对的两种第三值 $\pm(z\times y)$ 不同；指定符号后递推确定全尾，所以恰两类。零下一值时全序列为 $y,0,0,\ldots$，只有一类。必须以至少两个记录值区分两类，记录 $\epsilon$ 达到此界；这仅是条件一位区别，不是两个精确实向量的有限位成本、任意编码的存储下界或读原语最小性。

**命题 7.3（尾的付费取得与同制备接合）。** 三次尾向量读、两次 $\rho$ 得 $y,z,w$，可取得

$$
\epsilon=\frac{w\cdot(z\times y)}{|z\times y|^2}
$$

在非零分支上的准确 $\pm1$；零分支取 $+1$。两次连续尾读不能统一确定下一向量，定理7.2的两实际见证即为反例。若另供原树码，可从码算单位符号，树码权限仍单独计费。对任意初始来源，定理5.1用 $W_3$ 算其未来尾符号，无须第四次初始向量读。

两个实际同制备尾记录可接合：令

$$
\begin{aligned}
Y&=y_s\times y_t,&Z&=z_s\times z_t,\\
W&=[\epsilon_s(z_s\times y_s)]\times[\epsilon_t(z_t\times y_t)].
\end{aligned}
$$

若 $Z\times Y=0$，新符号取 $+1$；否则取 $W\cdot(Z\times Y)/|Z\times Y|^2$。

证明。三读商公式由定理7.2的实际第三值给出。$\rho(\mathcal T)$ 对同制备接合闭合，因为 $\langle\rho s,\rho t\rangle=\rho\langle s,t\rangle$。三个所列接合值正是该实际树的连续输出，故定理4.3保证非零商为 $\pm1$，并给正确第三值及像内闭合。零分支的下一项以后全零。此结论保留实际同制备守卫，不声称任意环境 $\theta$ 元组可以合法接合。

## 8. 已校准的数量与向量联合两读

**定义 8.1（新增数量口与校准合同）。** 本节固定公共校准 $p$；每次 Read 返回 $q(t)=2m+3n$ 及 $E_p(t)$。数量是同一树的加法组成观察，向量节点仍为叉积。两次联合读的数量为 $r_0=2m+3n,r_1=3m+5n$，复用 Atomic5.4／13.3 的整数逆

$$
m=5r_0-3r_1,\qquad n=2r_1-3r_0.
$$

故取得 $\eta_p(t)=(\nu(t),u,v)$，$u=x_0,v=x_1$；其实际域是定理6.1的组成标记像。

**定理 8.2（校准联合边界的后继与上下文）。** $\Delta>0$ 时使用定理4.3的校准 $R,r,s$，置 $\lambda=s/r,\mu=r$，则

$$
(\nu,u,v)\longmapsto(M\nu,v,\lambda^m\mu^nRv).
$$

$\Delta=0$ 时后继为 $(M\nu,v,0)$。同制备有序构造为

$$
(\nu,u,v),(\zeta,z,w)\longmapsto(\nu+\zeta,u\times z,v\times w).
$$

在该固定校准实际域，$\eta$ 相等当且仅当完整数量／向量联合 $\rho$ 未来相同，也当且仅当全部定理6.2型上下文的联合输出相同。

证明。$F(p)$ 的叶对为 $(b,K)$，下一叶对为 $(K,N)=(\lambda Rb,\mu RK)$。结构归纳的齐次性与 $R$ 的叉积相容给

$$
E_{F^2(p)}(t)=\lambda^m\mu^nR E_{F(p)}(t).
$$

依赖分支 $F^2(p)=0$，不需除法或标架。组成按 $M$ 更新，$\rho$ 与接合相容，得所列构造。相同记录逐操作保持相同，归纳给联合未来及上下文输出相同。反向首两联合输出用整数逆取得 $\nu,u,v$；上下文取洞及一次替换即可。每个后继和接合都有原树见证，未扩张实际域。

**推论 8.3（原始正交制备的较小校准记录）。** 若原 $a,b$ 非零且正交，取初始标架 $(a/\sqrt A,b/\sqrt B,K/\sqrt{AB})$ 的循环 $R_p$、$\lambda=\sqrt{B/A},\mu=\sqrt A$，则

$$
(\nu,u)\longmapsto(M\nu,\lambda^m\mu^nR_pu).
$$

证明。叶对满足 $F(p)=(\lambda R_pa,\mu R_pb)$，同一结构齐次归纳即得。单位正交情形就是复用的单位标签／组成闭合。这项特例仍收费校准，不能改成全制备结论。

**命题 8.4（校准非正交实例的尖锐取得与初值档案）。** 令 $h=a\times b=-K$，取原六叶树

$$
\begin{aligned}
X&=\langle\alpha,\langle\beta,\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle\rangle\rangle,\\
Y&=\langle\alpha,\langle\langle\alpha,\beta\rangle,
\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle\rangle.
\end{aligned}
$$

二者组成均为 $(3,3)$，且 $E_p(X)=C^2h,E_p(Y)=\Delta h$。在公共校准 $p=(e_1,e_1+e_2)$ 处，首联合读均为 $(15,e_3)$，下一向量分别为零和 $(-2,2,0)$。因此恢复全初始联合行为在这个实例至少一次更新；两读一次更新达到。

证明。置 $z=b\times h=Ba-Cb$。$a\times z=-Ch,h\times z=\Delta b$，故 $X$ 为 $a\times[b\times(a\times z)]=C^2h$，$Y$ 为 $a\times(h\times z)=\Delta h$。在指定制备 $A=1,B=2,C=\Delta=1$；$F(p)$ 有 $C'=0,\Delta'=2,h'=b\times K=(-1,1,0)$，得到下一项。零更新重复读无法分开二者。

读调用下界也为二，即使允许唯一读在非初始时刻。树

$$
U=\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle,
\qquad V_0=\langle\langle\alpha,\beta\rangle,\langle\alpha,\beta\rangle\rangle
$$

组成同为 $(2,2)$，初值分别为 $CK$ 和零，一阶后全部向量均零，全部数量以后也相同。在这固定校准处，一次读以前的确定 $\rho$ 日程源无关：若读在零时刻，$X,Y$ 反驳正确性；若读在任何后时刻，$U,V_0$ 反驳正确性。无读更不能恢复非恒定目标。两读一次更新由定理8.2达到。这不声称每个校准、任意编码口或更宽菜单都有该下界。$U,V_0$ 同时说明仅保留组成及下一向量一般会遗失初值，$u$ 必须另保留。

**命题 8.5（同树同组成仍不能免校准）。** 取 $t=\langle\alpha,\langle\alpha,\beta\rangle\rangle$，其组成 $(2,1)$、两数量 $(7,11)$。供应

$$
p_0=(e_1,e_2),\qquad
p_1=\left(2e_1,\frac{\sqrt{31}e_1+e_2}{4}\right).
$$

两制备的 $(x_0,x_1)$ 都为 $(-e_2,e_3)$，而 $x_2$ 分别为 $-e_1$ 和 $(-e_1+\sqrt{31}e_2)/32$，故未知制备两联合读不能统一预测下一项。

证明。树通式为 $L=Ca-Ab$，其一阶式为 $-BK$，二阶式为 $-\Delta N$。$p_1$ 的 $A=4,B=2,C=\sqrt{31}/2,\Delta=1/4,K=-e_3/2,N=(e_1-\sqrt{31}e_2)/8$，直接代入得所列三项。树码和组成均相同，遗漏的条件确实是校准。无校准定理5.1通过新增一次向量读解决预测任务，未免费取得校准。

## 9. 全参数多项式语义与实际符号像

**定义 9.1（Gram 多项式记录）。** 本节将基向量记为 $h=a\times b$，避免与组成 $\nu$ 混用。令 $\mathscr R=\mathbb Z[A,B,C]$。每棵树递归生成三多项式 $z(t)=(P_t,Q_t,T_t)$，叶记录为 $(1,0,0),(0,1,0)$。对 $u,v\in\mathscr R^3$ 置 $d_{ij}=u_iv_j-u_jv_i$，定义

$$
J(u,v)=(Bd_{23}-Cd_{31},\ -Cd_{23}+Ad_{31},\ d_{12}),
\qquad z(\langle s,t\rangle)=J(z(s),z(t)).
$$

**定理 9.2（全制备唯一表示）。** 对所有树及所有制备，包括依赖制备，

$$
E_p(t)=P_t(A,B,C)a+Q_t(A,B,C)b+T_t(A,B,C)h.
$$

三多项式作为全制备表示唯一。实际符号像 $\mathcal Z_{\rm src}$ 恰为两个叶三元组生成的最小 $J$ 子 magma，不是整个 $\mathscr R^3$。

证明。$h\times a=Ab-Ca,b\times h=Ba-Cb$，将两线性组合的叉积按这三条基对展开，正是 $J$。结构归纳证明存在性且不除任何可能为零的量。

若两三元组对所有制备给相同向量，对每个 $A>0,B>0,C^2<AB$ 取

$$
a=(\sqrt A,0,0),\qquad
b=(C/\sqrt A,\sqrt{B-C^2/A},0).
$$

$a,b,h$ 线性独立，故每个系数差在这个非空开 Gram 域为零。开域中取一个开长方体，固定除一变量外的变量，一元多项式在区间上为零就全系数为零；再依次对其它变量重复，得到原多项式为零。这证明全称唯一性，不断言单个退化制备能识别系数。七维可在嵌入的三维二生成切面作同一测试。像的一侧包含用结构递归，反向每个有限 $J$ 表达式就是对应原树。

**命题 9.3（原替换的半线性符号后继）。** 定义 $\mathfrak h(f)=f(B,\Delta,0)$，则

$$
\Sigma(P,Q,T)=(-B\mathfrak h(T),\ \mathfrak h(P)+C\mathfrak h(T),\ -\mathfrak h(Q)),
\qquad z(\rho t)=\Sigma z(t).
$$

$\Sigma$ 可加且为 $\mathfrak h$ 半线性，不是 $\mathscr R$ 线性。记录 $z$ 由 $J,\Sigma$ 决定所有全制备未来及同制备有编码上下文。

证明。$F(p)$ 的叶对是 $(b,-h)$，Gram 为 $(B,\Delta,0)$，其第三基向量为 $b\times(-h)=-Ba+Cb$。代入定理9.2并收集 $a,b,h$ 系数得所列公式；全称唯一性给与实际 $\rho$ 的交换式。两种递归保持实际符号像。这个记录取得自有限树码，不是有限数值读的结果。

## 10. 全称第一损失、剩余记录与精确恢复

**定义 10.1（零相关截面与正交后继）。** 令 $\mathscr R_0=\mathbb Z[A,B]$，$H$ 将每个系数限制到 $C=0$，$i:\mathscr R_0^3\to\mathscr R^3$ 为系数包含。定义

$$
\mathfrak h_0(f)=f(B,AB),\qquad
\Theta(P,Q,T)=(-B\mathfrak h_0(T),\ \mathfrak h_0(P),\ -\mathfrak h_0(Q)).
$$

准确的关系为

$$
H\Sigma=\Theta H.
$$

完整环上的 $\mathfrak h$ 分解为 $\widetilde{\mathfrak h}H$，其中 $\widetilde{\mathfrak h}:\mathscr R_0\to\mathscr R$ 取 $f(A,B)\mapsto f(B,AB-C^2)$；$H\widetilde{\mathfrak h}=\mathfrak h_0$。它不等于直接将 $\mathfrak h_0H$ 包含回完整环，例如 $\mathfrak h(B)=AB-C^2$。

**引理 10.2（正交符号后继单射）。** $\mathfrak h_0$ 及 $\Theta$ 都单射。

证明。单项式 $A^iB^j$ 被 $\mathfrak h_0$ 送到 $A^jB^{i+j}$；两个非负指数对的像相同必有相同 $j$ 再有相同 $i$，所以不同单项式不碰撞，系数不能抵消。$\Theta$ 的零值强迫三个 $\mathfrak h_0$ 值为零，因为 $\mathscr R_0$ 为整环，乘 $B$ 无核；再用 $\mathfrak h_0$ 单射。

**定理 10.3（全符号模块的核及实际树无新增后期损失）。** 在 $\mathscr R^3$ 上，

$$
\ker\Sigma=C\mathscr R^3.
$$

对任意实际树 $s,t$ 以及每个整数 $n\ge1$，以下三条件等价：

$$
\begin{gathered}
\forall p\in\mathcal P,\quad E_p(\rho^ns)=E_p(\rho^nt),\\
H z(s)=H z(t),\\
z(s)-z(t)\text{ 的每个系数坐标都被 }C\text{ 整除}.
\end{gathered}
$$

证明。若 $Hz=0$，每个坐标都被 $C$ 整除，在 $\mathfrak h$ 的 $C\mapsto0$ 代入下为零，故 $\Sigma z=0$。反向 $\Sigma z=0$ 给 $\Theta Hz=H\Sigma z=0$，引理10.2给 $Hz=0$。多项式在 $C=0$ 处为零恰等价于每个项含正 $C$ 次数，即被 $C$ 整除，得核公式。

对树差，若 $H(z(s)-z(t))=0$，第一次 $\Sigma$ 已消去差，以后仍零。反向全制备的第 $n$ 项相同，由定理9.2唯一性给 $\Sigma^n(z(s)-z(t))=0$；限制到 $C=0$ 得 $\Theta^nH(z(s)-z(t))=0$，逐次单射迫使原截面差为零。这证明每个 $n$ 的全称等价。它是实际子 magma 上的碰撞判据，不声称模块中每个元素或每个 $C$ 倍数都有原树见证；固定数值制备可有更多碰撞，属不同关系。

实际第一损失非空：命题5.3所列树（亦即命题8.4的 $U$）有 $z(U)=(0,0,-C)$，而零 cherry 的记录为零；两树一次替换后对每个制备都为零。在 $p=(e_1,e_1+e_2)$ 处原初值分别为 $-e_3$ 和零。这个原树见证区别于只在环境多项式模块中计算核。

**定理 10.4（可访问剩余记录的全称恢复）。** 若另供原始树码，可定义有限多项式剩余记录

$$
\mathcal L(t)=\frac{z(t)-iH z(t)}C.
$$

从已访问的 $\Sigma z(t)$ 及 $\mathcal L(t)$，可唯一恢复 $z(t)$，从而恢复其全制备语义及全部编码上下文行为。

证明。分子限制到 $C=0$ 为零，逐坐标准确整除。先由 $H\Sigma z(t)=\Theta Hz(t)$ 在实际 $\Theta$ 像上反演。对 $\Theta(P,Q,T)$，首坐标准确除以 $-B$ 得 $\mathfrak h_0(T)$，第二坐标为 $\mathfrak h_0(P)$，第三取负为 $\mathfrak h_0(Q)$。其单项式逆为

$$
A^uB^v\longmapsto A^{v-u}B^u\quad(v\ge u)
$$

且每个实际坐标都满足此像条件。引理10.2保证逆唯一。最后 $z(t)=iHz(t)+C\mathcal L(t)$。恢复的是全称语义记录，不是原树语法或物理制备。

**命题 10.5（有限码与无统一符号预算）。** 每树给有限多项式且递归终止；树码长度、次数、展开系数长度与存储无全树统一上界。一个实际族为 $k=\langle\beta,\alpha\rangle$、$t_0=\alpha$、$t_{j+1}=\langle k,\langle k,t_j\rangle\rangle$，满足

$$
z(t_j)=((-\Delta)^j,0,0),\qquad\text{叶数}=1+4j.
$$

证明。$K\perp a$，引理2.2给 $K\times(K\times a)=-\Delta a$，归纳得到向量式及唯一多项式式，每步增加四叶。展开 $(AB-C^2)^j$ 的次数增长，$j+1$ 个二项系数绝对值总和为 $2^j$，所以至少一个不小于 $2^j/(j+1)$，其长度无界。其它表示可压缩此族，不据此声称所有表示的同一复杂度下界；这里只给展开多项式及树码的界限。准确整除、代入及递归都按声明有限表示付费，没有从一次数值 Read 或未授予的参数扫描取得全称记录，也没有统一有限位预算或维数最小性声明。

## 11. 原始制备的目标纤维与额外档案

**定理 11.1（静态全树尾与规范尾的制备纤维）。** 目标固定为原始 $p=(a,b)$。静态全当前族 $(E_p(t))_{t\in\mathcal T}$ 的制备纤维为单点。静态全后替换族

$$
\Phi(p)=(E_p(\rho^jt))_{t\in\mathcal T,j\ge1}
$$

的纤维恰为定理3.2的 $F$ 纤维。已知规范尾从 $T_1=\beta$ 开始的完整数值序列也有同一纤维。

证明。全当前族的两个叶坐标就是 $a,b$。相同 $F(p)$ 经定理3.1给全部后替换值相同；反向全族的 $(\alpha,j=1),(\beta,j=1)$ 坐标就是 $b,K$，强迫相同 $F(p)$。规范尾的首两值也是 $b,K$，以后由规范叉积递推决定，故纤维相同。这里比较静态信息，不供应同时读取全部树的实验。

**定理 11.2（原始剪切的准确补充记录）。** 在 $b\ne0$ 域，另供应或在制备时确实保留 $\tau=a\cdot b$，则尾记录 $(b,K,\tau)$ 恢复

$$
a=\frac{K\times b+\tau b}B.
$$

这包括 $K=0$ 的依赖分支。一般额外可访问记录 $Z$ 充分，当且仅当其在每个允许的实际 $F$ 纤维上单射。在无限制 $b\ne0$ 域，一个实标量足够；没有附加数据不够，有限或可数附加字母表也不够。

证明。定理3.2给完整仿射直线纤维，$K\times b=Ba-Cb$，代入 $\tau=C$ 得逆式。任意 $a+\lambda b$ 保持 $b,K$ 及全尾，原制备却不同，排除无附加记录。一般判据复用准确纤维原则：同一非空联合记录纤维若含两个不同制备，解码不能同时正确；若每个纤维恰一个制备，则取该唯一值解码。每条无限制仿射实线不可数，不能单射到有限或可数字母表。这不设定任意不连续实编码的维数下界。

**命题 11.3（零叶及取得合同的退化边界）。** 若 $b=0$，$F(p)=0,\tau=0$ 与 $a$ 无关，必须另保留在 $a$ 上单射的记录；保留 $a$ 足够。在线性实记录 $V\to\mathbb R^d$ 约定下，秩—零度强迫 $d\ge\dim V$，主版本为三，七维版本为七。受限制备域可缩小纤维并改变该要求。

已知从 $T_1$ 开始的具体取得是 Read$(b)$、$\rho$、Read$(K)$；$\tau$ 须另供或由获准的早期测量保留，尾计算不能生成它。$b\ne0,K=0$ 时须保留首读 $b$，再更新的 $F^2(p)=0$ 会丢失它。若已知初始是 $\alpha$，两读在 $\alpha,\beta$ 直接得 $(a,b)$，是不同起始合同。若原树任意未知，零 cherry 对所有制备有全零未来，无限多个 $\rho$ 数值读也不保证提供任何制备信息。这些结论分别由定理3.2及实际树求值给出。

## 12. 已知节点上的破坏性制备取得

**定理 12.1（已知原节点的实际像与完整制备纤维）。** 从已知字面节点 $T_2=\langle\beta,\alpha\rangle$ 开始，未知 $p$。在节点及一次 $\rho$ 后两读记为

$$
u=K,\qquad v=N=K\times b.
$$

独立制备的准确像是全部非零正交 $(u,v)$；依赖制备全部给 $(0,0)$，无其它退化对。非零对的完整制备纤维为

$$
b=-\frac{u\times v}{|u|^2},\qquad
B=\frac{|v|^2}{|u|^2},\qquad
a=\frac vB+\lambda b\quad(\lambda\in\mathbb R).
$$

同一已知节点的整个数值历史与该对有相同制备纤维。若另可访问 $\tau=a\cdot b$，两读一次更新恢复 $a=v/B+(\tau/B)b$。

证明。$u\perp b,v=u\times b$ 给 $u\times v=-|u|^2b,|v|^2=|u|^2B$；$v=Ba-Cb$ 给仿射表达式。反向任意非零正交 $u,v$，定义所列 $b,B$，则 $|b|^2=B>0$ 且

$$
b\times v=\frac{(-u\times v)\times v}{|u|^2}=Bu.
$$

取任意 $a=v/B+\lambda b$，得到 $b\times a=u$、$u\times b=v$，所以每个纤维点都实际实现且独立。原始点必有 $\lambda=C/B$，故无遗漏。规范节点尾由首两值的规范递推决定，整个历史相等的反向又包含这两值。依赖制备给 $K=N=0$，全节点历史零。最后 $v\perp b$，所以 $a\cdot b=\lambda B$；供应 $\tau$ 得唯一原制备。

**定理 12.2（精确节点协议的两读下界）。** 在已知 $T_2$、独立未知制备、另可访问 $\tau$、无校准或其它制备档案的合同中，任意确定有限停止的 $\rho$ 单历史协议若至多一次向量 Read，不能恢复全部原制备。两次读一次更新的定理12.1协议达到该读数下界。

证明。限制到 $a=\lambda e_1,b=\mu e_2$、$\lambda,\mu>0$，全族 $\tau=0$。唯一读之前日程没有依赖未知数值的输入，故若有读，其规范时刻 $j\ge2$ 固定。设 Fibonacci 整数 $F_0=0,F_1=1$。由规范叉积递推归纳，$T_j$ 的轴及符号只依 $j$，幅度为

$$
\lambda^{F_{j-1}}\mu^{F_j}.
$$

$j=2$ 的幅度为 $\lambda\mu$，后续两正交轴相乘使幅度相乘，指数按同一 Fibonacci 递推相加。两指数均正。让 $\lambda>0$ 任意变化，取 $\mu=\lambda^{-F_{j-1}/F_j}$，全族同一读数、同一读时刻及 $\tau=0$，原叶对不同。此后的无读更新、后处理与停止都依同一已取得记录，不能分开它们。无读时更不能分开。这个下界量化指定协议中的任意唯一读时刻，不是任意测量函数或较宽校准菜单的原语最小性。

**命题 12.3（依赖节点的档案修复及树身份界限）。** 在依赖分支，$(0,0,\tau)$ 不足：$p=(e_1,e_1)$ 与 $p'=(e_2,e_2)$ 有同一 $\tau=1$ 和全零节点历史。若 $b\ne0$，另存 $b$ 后由 $a=\tau b/B$ 修复；若 $b=0$，须存原 $a$ 或纤维上的其它单射记录。恢复 $p$ 可求值每棵另有代码的树，却不能由数值恢复未知原树；命题6.5的零树身份反例仍成立。

## 13. 同一实现的资源坐标与精确运算边界

**约定 13.1（各目标的同时取得费用）。** 令 $d=\dim V$，主版本 $d=3$，返回完整环境八元数坐标时 $d=7$。下表各行是一条实际历史的共同资源配置。精确实数、整数、多项式和二值记录分别计，源生成、端口供应、合法配对、动作／时间／失败／Stop 身份及输出费用也分别保留。

| 13目标与合同 | 同时读／源更新 | 保留记录与附加权限 | 解码工作与 scratch |
| --- | --- | --- | --- |
| 13初始数值未来：未知树及制备 | 3向量Read、2次 $\rho$ | 初始3向量，即 $3d$ 精确实坐标；源及时间身份；无数量或校准口 | 每次 $G$ 一叉积、一点积、一次准确符号；一临时向量及有限标量 |
| 13当前尾未来：$\mathcal X_1$ | 3尾向量Read、2次 $\rho$ | 取得时3向量；完成后2向量及条件符号 | 一叉积、点积和守卫除法；归档更早初值另计 |
| 13初始联合行为：固定校准 $p$ | 2联合Read、1次 $\rho$；共2向量和2整数回复 | $\nu,u,v$；另有校准及同制备身份 | 整数逆；有限正数幂及校准框架映射；退化分支返回零 |
| 13全参数语义及第一损失恢复 | 另可访问原有限树码；符号递归 | 有限 $z$，或 $\Sigma z$ 加 $\mathcal L$；无数值读取得声明 | 多项式运算／准确整除；次数、系数和代码成本随实际输入，无统一预算 |
| 13原制备：已知 $T_1$ | 2向量Read、1次 $\rho$；另供或早期保留 $\tau$ | $b,K,\tau$ 或恢复的 $a,b$；分支身份 | 有限叉积、范数及 $B\ne0$ 除法；$b=0$ 另存 $a$ |
| 13原制备：已知独立 $T_2$ | 2向量Read、1次 $\rho$；另供 $\tau$ | $u,v,\tau$ 或恢复的 $a,b$ | $|u|^2,B\ne0$ 的有限运算；依赖分支按命题12.3另存档案 |

第一行逐次归档 $x_0$、更新读 $x_1$、更新读 $x_2$，然后停止，当前源为 $\rho^2t$；预测不是把源逆转。若目标保留时刻零，归档的 $x_0$ 不能随滑动窗口删除。尾行只有在第三个读数已提供符号后才可删除它。联合行用两数量回复解码组成，保留初始 $u$；校准可具体存为 $g_1,g_2,g_3,r,s$ 或原 $p$，获取／保存它另计。一个朴素有限幂算法作 $m+n$ 次标量乘法，再作固定维度标架映射；不将其解释为任意实数的有界位复杂度。

**命题 13.2（另授代码时的显式源与算术界）。** 在额外树码权限及逐显式节点求值约定下，$L$ 叶树需 $L-1$ 次叉积，节点数为 $2L-1$；一次 $\rho$ 后至多 $2L$ 叶，$j$ 次后至多 $2^jL$ 叶。求三初始树的向量共至多 $7L-3$ 次叉积。

证明。叶没有叉积、一个节点把两个孩子的叉积数相加再加一，归纳得 $L-1$；节点数同理。每个旧叶一次替换成至多两叶，新生成叶不在同一遍继续替换，所以逐次倍增界成立。三棵树的求值费用至多 $(L-1)+(2L-1)+(4L-1)$。逐节点遍历也能构造其字面替换，输出大小按同一节点数收费。这是明确代码表示的成本，不是黑箱物理 Read 或 $\rho$ 的价格；无代码权限的数值协议仍只使用声明端口。

**约定 13.3（下界、精度与比较范围）。** 定理5.1／命题5.2的最短值针对连续窗口；定理7.2针对固定精确向量对的补充区别；定理11.2针对实际纤维上的附加字母表；命题11.3针对线性记录；定理12.2针对已知节点的确定单读协议；命题8.4针对校准实例的实际联合读／更新。各下界不能换成任意编码、每个制备或物理成本的普遍下界。

所有数值公式使用精确符号、相等判断及非零守卫除法。若表示不供应准确符号／相等，没有从公式自动得到有效分支算法。有限多项式递归因孩子更小而终止；固定数值解码由有限运算构成，但任意实常数的有效表示、位运算误差及输出精度需另给。这里没有噪声律、稳定有限位重建、统计充分性、物理时钟或最优物理预算。

比较须同时固定目标、初始及生成源大小、制备、代码访问、校准、实际联合身份、读种类与宽度、实际更新／graft、实数／整数／多项式／二值档案、解码工作／scratch／输出、精度和控制／失败／Stop 元数据。校准两联合读与无校准三向量读没有所证的全坐标支配关系，不给共同标量价格。组成、原始剪切与条件尾符号分别服务不同目标。

## 14. 来源复用、文献范围与已发表接口的区别

**约定 14.1（原始接口与复用边界）。** 本卷使用以下原始来源，而不把名称相似或线性张成当作恢复权限。

| 14来源 | 承担的原前提与复用范围 |
| --- | --- |
| 14原语法：[Atomic](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§2–5、13；[Continuation](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) §1 | 非空有序树、原 $\rho$、结构解释、$M$ 与数量逆；复用基础，向量节点不换成加法 |
| 14切面：[Boundary Geometry](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) §§5、7、8 | 完整旋转合同与原生可达性分开；固定单位全树标签；八元数二生成切面及外部上下文边界 |
| 14形式源：[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) 及 [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.md) | `FreeMagma Bool`，true对应 $\alpha$、false对应 $\beta$；非空组成纤维、形状与叶位、替换单射；零组成为空 |
| 14上下文：[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)、Continuation13.2 | 全部有限严格上下文、失败与正常零分开、实际联合合法域饱和；本卷固定制备子合同另有直接证明 |
| 14线性观察：Boundary16–17；[ObservableKrylovGrowthBound](../../../D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound.lean)、[MaximalUnobservableSubspace](../../../D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace.lean)、[ObservableKrylovPermanentStability](../../../D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability.lean) | 线性初态、线性更新及线性观察；其维数、加法递推和稳定结论不实例化本卷非线性原树过程 |
| 14Clifford：Atomic355–356 | 结合 Clifford 叶积，356的窗口来自同一原树的连续替换；其六周期和代数逆不移植到叉积或连续变量叶出现 |
| 14已发表原生控制：[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) §44 | 固定单位制备的实际组成／方向像、原生控制及付费单历史取得；本卷直接复用单位机制，额外可变叶制备不由这些控制供应 |
| 14外部仪器：Boundary37–43、Process44.15–44.18 | 所供 $W=E\oplus\mathbb H$ 初态、锚、仪器读／破坏性更新、公共校准，以及仿射或球帽／两半径层来源；不是本卷 $E_p(\rho^jt)$ 的原生变叶过程 |
| 14算术来源估计：Atomic407–413 | Mellin／Abel 来源估计；不授原树制备、复制、逆或校准菜单 |

Process44 已给固定单位制备的方向控制和取得结果，不能将本卷的单位标签、数量逆或相同单位特例另称未发表增量。Boundary43 的两半径初始来源及制备／读取误差合同与本卷额外叶对不同，其误差下界不回答下节的问题。Atomic19、375 的更宽操作或物理接口亦须逐项另外供应。读取既有 D5 原文只是复用接口，本卷不新增或声称运行其 Lean 核验。

**约定 14.2（主要文献与所用数学）。** 经典基础为 `literature-attested`：Erik Darpö, *Vector product algebras*, [arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，Lemma2及证明，*Bull. London Math. Soc.* 41(5), 898–902，[DOI](https://doi.org/10.1112/blms/bdp066)，其交替积、非退化对称型、循环配对与范数条件在本卷取正定实情形。John C. Baez, *The Octonions*, *Bull. Amer. Math. Soc.* 39, 145–205，[DOI](https://doi.org/10.1090/S0273-0979-01-00934-X)，作者原文 [预备定义与交替性](https://math.ucr.edu/home/baez/octonions/node2.html) 和 [叉积／$G_2$](https://math.ucr.edu/home/baez/octonions/node14.html) 支持实八元数及二生成切面；不支持完整 $SO(7)$ 控制。所需重复向量公式已在引理2.2直接证明。

Soledad Villar 等，*Scalars are universal: Equivariant machine learning, structured like classical physics*, [arXiv:2106.06610v2](https://arxiv.org/pdf/2106.06610v2)，Proposition5及AppendixB，为经典多项式等变 Gram 系数表示的背景；本卷只需两输入三维情形，并直接证明其特定树递归和唯一性，不据一般等变形式推定实际像。Mihály Petreczky、Laurent Bako、Jan H. van Schuppen，*Realization theory of discrete-time linear switched systems*, [arXiv:1103.1343v2](https://arxiv.org/pdf/1103.1343v2)，Remark6说明响应表可能需要不同切换实验；其线性实现定理未用作本卷前提，也不供应单历史中的反事实重播。

本卷全树符号恢复、实际尾像、校准联合边界和已知节点取得是上述准确源合同下的仓内综合推导（`repo-derived`）。普通证明与实际反例承担结论，不作全球原创性或穷尽检索声明。J. C. Turner, *On Vector Sequence Recurrence Equations in Fibonacci Vector Geometry*, [DOI](https://doi.org/10.1007/978-94-011-4271-7_32) 的完整原文假设尚未取得；它只是未核查线索，不充当前提或新颖性证据。

## 15. 有限核验的证据界与未解稳定性

**约定 15.1（精确核验的作用）。** 有限核验可检查树枚举、原括号求值、运输、归约、窗口公式及指定反例；全称结论由前文结构归纳、唯一性与单射证明承担。有限样本不证明无限全树或任意制备的命题，也不取代真实联合像的反向构造、读协议下界或所供实数的有效表示。没有据样本建立物理读／控制、有限位精度或稳定性结论。

整数及有理数核验枚举了1–7叶的全部20,134棵有序树，在10个正交、非正交、依赖或零叶制备上核对时刻0–5的三读公式及尾关系；字面替换运输另核对1–4叶的102棵树及0–3次替换。符号核验枚举1–6叶的3,238棵树，核对 $H\Sigma=\Theta H$、剩余反演及第1–3次替换的相同碰撞类。命题5.2、8.4的有理反例和命题8.5在 $\mathbb Q(\sqrt{31})$ 中的同树反例逐坐标准确成立；网格 $\{-1,0,1\}^3$ 中192个非零有序正交对核对了定理7.2的两个实际见证及制备／节点逆式。这些范围之外的全称结论仍由各条普通证明承担。

**开放问题 15.2（无界树大小下的实际三读稳定性）。** 固定 $L,H>0$ 与 $0<\delta_0<L^4$。仅取实际树／制备满足

$$
|a|,|b|\le L,\qquad \Delta\ge\delta_0,\qquad
|x_0|,|x_1|,|x_2|\le H.
$$

对两实际来源都满足这些限制且 $\max_{0\le j\le2}|x_j-x'_j|\le\varepsilon$，定义

$$
\omega(\varepsilon)=\sup|x_3-x'_3|,
$$

空上确界约定为零。树大小无界时，是否 $\omega(\varepsilon)\to0$？若成立，尖锐阶是什么；若不成立，哪组实际成对树／制备见证障碍？这项稳定性问题保持实际 $W_3$ 像及共同来源条件，不能以环境符号函数的跳变替代反例。它尚未由本卷的精确恢复、有限核验或其它仪器的误差合同解决。

## 追加锚（本行以下为增补区）

## 16. 实际来源的投影约束与无界树稳定域

本节至第23节回答开放问题15.2的指定下一向量任务；其原文保留。来源、括号、定向叉积和唯一实际更新仍为定义1.1–1.2，制备在执行过程中固定。定理3.1、引理4.2、定理4.3及5.1分别供应运输、五符号描述子、实际尾幅度与精确预测；这些已建立的接口不重复计作稳定性结果。以下主结论只取三维版本。

**定义 16.1（主域、记录距离与目标模量）。** 固定实数 $L,H>0$、$0<d_0<L^4$；$d_0$ 对应开放问题15.2的 $\delta_0$。记

$$
\mathcal D_{L,H,d_0}=\{(t,p)\in\mathcal T\times(\mathbb R^3)^2:
|a|,|b|\le L,\ \Delta\ge d_0,\ |x_j|\le H\ (0\le j\le2)\}.
$$

树可为任意非空有限有序树，大小无统一上限。置 $q_j=|x_j|$、$w=x_2\times x_1$，两记录间使用

$$
d(W_3,W'_3)=\max_{0\le j\le2}|x_j-x'_j|,\qquad
\omega(\varepsilon)=\sup_{\substack{(t,p),(t',p')\in\mathcal D_{L,H,d_0}\\
d(W_3,W'_3)\le\varepsilon}}|x_3-x'_3|.
$$

空上确界取零。两成员分别满足全部联合限制，树和制备都可不同。该域非空：取垂直叶长 $d_0^{1/4}<L$，零 cherry 的整个响应为零；包含零子树的更大树也供应任意大来源。本任务只预测 $x_3$，不把目标换成原语法、原制备或全时间误差。

为避免标量界 $L$ 与约定2.1的向量 $L$ 混淆，以下记

$$
U=K\times a=Ca-Ab,\qquad V=K\times b=Ba-Cb.
$$

它们分别就是前文的向量 $L,N$；$A,B,C,\Delta,K,F$ 含义不变。计数、正交化、缩放与旋转仅为证明中构造实际竞争源的方法，不供应数量、语法、校准、逆、复制、复位、归一化、旋转或重制备的观察／动作端口。

**引理 16.2（投影同时控制角度与幅度）。** 设 $\Delta>0$ 且 $\chi(t)=\sigma f_i\ne0$。令 $u=w/|w|$，则

$$
P:=\sigma x_0\cdot u>0,\qquad
P\ge\frac{q_2}{q_1},\qquad
P\ge\sqrt{\frac{\Delta}{AB}}\,q_0.
$$

证明。定理4.3的尾标架给

$$
x_1=\sigma r^ms^ng_i,\qquad
x_2=\sigma r^ns^{m+n}g_{i+1},\qquad
w=q_1q_2g_{i+2},\quad r=\sqrt B,\ s=\sqrt\Delta.
$$

由引理4.2，非零标签的所选描述子没有 $C$ 因子，可将 $\sigma$ 提出，并选初值符号 $Z\in\{a,b,K,-U,V\}$，使 $x_0=\sigma A^iB^j\Delta^kZ$。这里 $i,j,k$ 为描述子指数，而非标签索引。赋予 $A,B,C,\Delta$ 双次数 $(2,0),(0,2),(1,1),(2,2)$，赋予 $a,b,K,U,V$ 双次数 $(1,0),(0,1),(1,1),(2,1),(1,2)$。完整表的每一项都保持孩子双次数的和；故对 $Z$ 的次数 $(m_Z,n_Z)$ 有

$$
m=2i+2k+m_Z,\qquad n=2j+2k+n_Z.
$$

对应正向投影如下；各行的 $u$ 是该符号实际所属尾分支的 $g_{i+2}$。

| 16初值符号 $Z$ | $Z\cdot u$ | $(Z\cdot u)/|Z|$ |
| --- | --- | --- |
| 16投影 $a$ | $s/r$ | $\sqrt{\Delta/(AB)}$ |
| 16投影 $b$ | $r$ | $1$ |
| 16投影 $K$ | $s$ | $1$ |
| 16投影 $-U$ | $s^2/r$ | $\sqrt{\Delta/(AB)}$ |
| 16投影 $V$ | $rs$ | $1$ |

例如 $a\cdot V=\Delta$、$(-U)\cdot b=\Delta$，而 $|U|^2=A\Delta,|V|^2=B\Delta$，给两个非平凡比值。各投影又恰等于 $(s/r)^{m_Z}r^{n_Z}$。利用 $A=(\Delta/B)(AB/\Delta)$ 得完整恒等式

$$
P=\left(\frac{AB}{\Delta}\right)^i(s/r)^mr^n
=\left(\frac{AB}{\Delta}\right)^i\frac{q_2}{q_1}.
$$

$AB/\Delta\ge1$ 给幅度不等式；投影／范数比值中正单项式相消，给角度不等式。所有所除量在本分支严格为正。

**推论 16.3（实际三读的统一定量关系）。** 对任意制备与树，

$$
|x_0\cdot w|\ge q_2^2,\qquad q_2\le q_0q_1.
$$

在主域上置 $c=\sqrt{d_0}/L^2\in(0,1)$，还同时有

$$
|x_0\cdot w|\ge c q_0|w|,\qquad |w|\le H^2q_0,
\qquad |x_3|=|w|\le H^2.
$$

证明。规则分支中 $|w|=q_1q_2$，将引理16.2第一界乘以此量得到第一式；$P\le q_0$ 给第二式。主域的 $AB\le L^4,\Delta\ge d_0$ 给角度下界 $c$，并由 $q_1\le H$ 得 $|w|=q_1q_2\le q_0q_1^2\le H^2q_0$。定理5.1给最后等式。零标签的 $x_1,x_2,x_3$ 全零；依赖制备的 $x_2,x_3$ 全零，故这些分支也满足不含除法的全部结论。这里没有假设某一读数或三重积有统一严格正下界。

环境三元组 $x_0=\pm\varepsilon e_3,x_1=e_1,x_2=e_2$ 在 $\varepsilon<1$ 时违反 $q_2\le q_0q_1$。因此，环境符号公式在这些点的跳变不能当作实际来源的不稳定见证。

## 17. 全树下一输出的线性模量与实际尖锐对

**定理 17.1（变化制备的统一线性界）。** 对定义16.1的每组参数及每个 $\varepsilon\ge0$，

$$
0\le\omega(\varepsilon)\le
\min\{2H^2,K_*\varepsilon\},\qquad
K_*=2H+\frac{2H^2+4H}{c}.
$$

因此开放问题15.2所问的 $\omega(\varepsilon)\to0$ 对全部允许参数成立；此处的系数是充分界，不是最优系数。

证明。取任意实际对，令 $e=d(W_3,W'_3)$、$\delta_w=|w-w'|$。两成员的读数范数界及双线性给

$$
\delta_w\le|x_2-x'_2|\,|x_1|+|x'_2|\,|x_1-x'_1|\le2He.
$$

若任一 $w$ 为零，或两非零分支的实际符号相同，定理5.1给目标差至多 $\delta_w$。余下两符号相反且 $q_0,q'_0>0$；交换成员名使 $q_0\ge q'_0$。三重积异号及推论16.3给

$$
cq_0|w|\le|x_0\cdot w-x'_0\cdot w'|
\le e|w|+q'_0\delta_w.
$$

除以 $q_0$，用 $|w|/q_0\le H^2,q'_0/q_0\le1$，得

$$
|w|\le\frac{H^2e+\delta_w}{c},\qquad
|x_3-x'_3|=|w+w'|\le2|w|+\delta_w\le K_*e.
$$

此论证覆盖 $e=0$ 及全部符号、零分支。两目标范数又各不超过 $H^2$；取实际对的上确界得到所列两界，不需要紧性、有限树截断或固定制备。

**定理 17.2（非零目标的实际线性下界）。** 若主域含一个 $x_3\ne0$ 的来源，则 $\omega(\varepsilon)=\Theta(\varepsilon)$ 当 $\varepsilon\downarrow0$；若不含，则 $\omega\equiv0$。

证明。固定该来源，令 $v=|x_3|>0$、$M_0=\max(q_0,q_1,q_2)>0$。取垂直于 $x_3$ 的旋转轴，以正向旋转 $Q_\theta$ 同时旋转两个原叶，保留同一字面树。定向体积给 $Q(u\times v)=(Qu)\times(Qv)$，结构归纳得 $x'_j=Q_\theta x_j$。两制备的 Gram 数据、叶范数及三个读数范数完全相同，故包括等号在内的全部限制同时保留。旋转差满足

$$
|Q_\theta z-z|\le2|z|\sin(\theta/2),
$$

当 $z$ 垂直于轴时等号成立。对 $0<\varepsilon\le2M_0$ 选 $2\sin(\theta/2)=\varepsilon/M_0$，则三读差都至多 $\varepsilon$，目标差恰为 $(v/M_0)\varepsilon$。结合定理17.1得尖锐阶。若全域目标为零，定义直接给零模量。旋转构造的是两个合法所供制备，未授予内部观察者旋转动作。固定 $p$ 的子域继承上界，却不能直接继承本变化制备下界。

## 18. 非零预测的实际可行性与达到／未达到的阈值

**定义 18.1（统一参数与组成支撑）。** 置

$$
\varphi=\frac{1+\sqrt5}{2},\quad s_0=\sqrt{d_0},\quad
z=\log s_0,\quad \ell=\log L,\quad h=\log H,\quad
\gamma=z-\ell/\varphi^2,\quad T=s_0^{\varphi^2}/L=e^{\varphi^2\gamma}.
$$

站立条件为 $z<2\ell$。非零单位标签的组成支撑恰为

$$
\mathcal S=\{(1,0),(0,1)\}\cup
\{(m,n):m,n\ge1,\ (m,n)\notin(2\mathbb N)^2\}.
$$

此支撑直接复用 [Process Geometry 定理44.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)：三轴的 $\mathbb F_2^2$ 分次排除双偶混合组成，纯标签多叶树的同标签 cherry 排除其非零值。可用的实际见证是从 $\langle\beta,\alpha\rangle$ 出发，两次左接同一标签来增加对应叶数2；正奇／奇组成由此全得到。正偶／奇再左接一次 $\alpha$，正奇／偶再左接一次 $\beta$，所接轴与原轴垂直，仍非零。另两纯组成就是原叶。这些是构造来源的有限配方，不是观察者取得组成或接合权限。

**定理 18.2（全实际像上的三线可行性判据）。** 主域含非零 $x_3$，当且仅当存在 $(m,n)\in\mathcal S$ 及 $v\in[z-\ell,\ell]$，使

$$
\begin{aligned}
f_0(v)&=mz+(n-m)v\le h,\\
f_1(v)&=nz+mv\le h,\\
f_2(v)&=(m+n)z+nv=f_0(v)+f_1(v)\le h.
\end{aligned}
$$

证明。任一非零目标来源有 $\Delta>0$ 和非零标签。将 $a$ 换为 $a_\perp=a-(C/B)b=V/B$：它与 $b$ 垂直，范数不增加，$B,\Delta,F(p)$ 不变，故全部尾值不变。正交齐次性给新初值范数

$$
|E_{(a_\perp,b)}(t)|=(s/r)^mr^n=q_2/q_1\le q_0
$$

（引理16.2）。再同时缩放两垂直叶，比例 $(d_0/\Delta)^{1/4}\le1$。每个 $\rho^jt$ 有正的有限叶数，其求值按这个比例的叶数次幂缩放，故叶界与三读界都保留，行列式成为 $d_0$，且非零仍非零。这证明全部原来源的存在性可归约到正交、恰取最小行列式的实际制备，而非环境三元组。

这样的叶长必可写为 $|b|=e^v,|a|=s_0e^{-v}$；两叶界恰给 $z-\ell\le v\le\ell$。正交齐次性及组成更新给

$$
q_0=s_0^me^{(n-m)v},\quad
q_1=s_0^ne^{mv},\quad
q_2=s_0^{m+n}e^{nv}=q_0q_1.
$$

取对数即得必要性。反向，为所选支撑组成取定义18.1的字面树，再供应 $(s_0e^{-v}e_1,e^ve_2)$。所列幅度是同一实际来源的三个读数，叶界、行列式和三个不等式同时成立，尾非零。故判据充分且覆盖全部树大小。

**定理 18.3（完整零／非零制度）。** 在站立条件下，下表准确决定定理17.2的非零线性分支；不满足右栏条件时目标全零且 $\omega\equiv0$。

| 18参数制度 | 主域存在非零预测的充要条件 |
| --- | --- |
| 18收缩 $\gamma<0$，即 $d_0<L^{2/\varphi^2}$ | 每个 $H>0$ |
| 18临界 $\gamma=0$，即 $d_0=L^{2/\varphi^2}$ | 恰为 $H>1$，不包含等号 |
| 18非收缩 $\gamma>0$，即 $d_0>L^{2/\varphi^2}$ | 恰为 $H\ge H_*>1$，$H_*$ 由定理18.4给出并达到 |

临界和非收缩制度均强迫 $L>1,s_0>1$。

证明。先取实际端点制备 $a=Le_1,b=(s_0/L)e_2$，及规范实际树 $T_j=\rho^j\alpha$。命题5.3的原结构递推给垂直循环方向及正幅度

$$
Q_0=L,\quad Q_1=s_0/L,\quad Q_{j+2}=Q_{j+1}Q_j.
$$

以 $F_0=0,F_1=1,F_{j+1}=F_j+F_{j-1}$ 记 Fibonacci 数，则对 $j\ge1$，

$$
\log Q_j=F_{j-1}\ell+F_j(z-\ell)
=\frac{\varphi^j}{\sqrt5}\gamma+O(\varphi^{-j}).
$$

这里复用的闭式 $F_j=(\varphi^j-(-\varphi^{-1})^j)/\sqrt5$ 由两个初值与同一递推验证。$\gamma<0$ 时三个连续幅度都趋于零，任意 $H>0$ 都由某个有限 $T_j$ 实现；包括 $L\le1$ 或 $s_0\le1$ 的情况。$\gamma=0$ 时 $z=\ell/\varphi^2<2\ell$ 强迫 $\ell,z>0$，准确有 $\log Q_j=\ell(-\varphi^{-1})^j\to0$，故所有 $H>1$ 可行。

为排除临界 $H\le1$，对定理18.2的任意组成及允许 $v$，计算

$$
f_0+\varphi f_1=(m+\varphi n)(z+v/\varphi)
\ge\varphi\gamma(m+\varphi n).
$$

临界时右侧零。若 $h<0$，前两线均至多 $h$ 与此矛盾。若 $h=0$，两线必须同时为零；将其视为关于两叶对数的线性方程，其行列式为 $m^2+mn-n^2\ne0$。非空整数组成不可能给零：零坐标情形直接成立，其余会使有理比值成为 $X^2+X-1=0$ 的无理根。因此两叶对数都零，与两者和 $z>0$ 矛盾。这证明临界下确界1未达到。非收缩部分由下一定理给出。

最后，若 $\ell\le0$，$z<2\ell\le\ell/\varphi^2$，必有 $\gamma<0$；若 $\ell>0,z\le0$ 也必收缩。故余下制度的 $\ell,z$ 均正。

**定理 18.4（非收缩制度的有限达到阈值）。** 若 $\gamma>0$，定义

$$
\begin{gathered}
g_{mn}=\min_{v\in[z-\ell,\ell]}\max\{f_0(v),f_1(v),f_2(v)\},\\
\mathcal F=\{(m,n)\in\mathcal S:m+\varphi n\le\varphi z/\gamma\},\\
h_*=\min_{(m,n)\in\mathcal F}g_{mn},\qquad H_*=e^{h_*}.
\end{gathered}
$$

这是非空有限优化，$0<h_*\le z$。每项 $g_{mn}$ 只须在区间两端及落在区间中的下列已定义交点取最大值再比较：

$$
\frac{(n-m)z}{n-2m},\qquad -\frac{nz}{m},\qquad
-\frac{mz}{n-m}.
$$

零分母项略去。某个实际有限树及允许制备在 $H=H_*$ 同时满足全部界，并有非零预测。

证明。定理18.3证明中的加权式及 $f_0,f_1\le\max f_j$ 给

$$
g_{mn}\ge\gamma(m+\varphi n)/\varphi>0.
$$

$\alpha$ 来源在两叶同长 $\sqrt{s_0}<L$ 时三幅度为 $\sqrt{s_0},\sqrt{s_0},s_0$，其最大对数恰为 $z>0$。任一能与该值持平或改善的组成必在 $\mathcal F$；被略去的组成的最大对数严格大于 $z$，不能改变全局下确界。$\mathcal F$ 有限且含 $\alpha$，每个闭区间上的连续函数都达到最小值，故全局最小正且达到。三条仿射线的凸分段线性最大值，在端点、线交点或常值线段处达到最小；常值线段的端点也给同值。上式恰为三种两两交点，平行或重合不增加候选。这证明有限求值公式。用定理18.2的实际组成见证和优化制备实现最小值，得到 $H\ge H_*$ 的充分性；同一判据给必要性，包括等号。

有限集只服务存在性／阈值计算，不给主模量定理添加树大小上限；任意大零树和任意实际规则树都仍在相应全称域内。

## 19. 有限判据的覆盖证明与端点简化

**命题 19.1（测试给定读数界的两种有限截止）。** 在 $\gamma>0$ 时，若 $h\le0$ 则无非零预测；若 $h>0$，定理18.2的完整三线判据可仅测试

$$
(m,n)\in\mathcal S,\qquad m+\varphi n\le h/\gamma.
$$

较宽截止 $m+\varphi n\le\varphi h/\gamma$ 也给准确决定。它们是不同的有限列表，但连同相同三线判据，均成功当且仅当 $h\ge h_*$。

证明。即使不作正交化，定理4.3给规则尾

$$
q_1q_2^{\varphi}=(rs^{\varphi})^{m+\varphi n},\qquad
rs^{\varphi}\ge s^{\varphi^2}/L\ge T.
$$

因 $\Delta\le AB\le L^2B$，有 $r\ge s/L$；$s\ge s_0$ 给第二个界。由 $q_1,q_2\le H$ 及 $\log T=\varphi^2\gamma$，得到 $(m+\varphi n)\gamma\le h$。这是较小列表的必要截止。较宽列表来自 $f_0+\varphi f_1\ge\varphi\gamma(m+\varphi n)$ 及 $f_0,f_1\le h$。两列表都覆盖每个可行组成，测试内的三线不等式又各自充分，故完整决定等价。若以 Gram 平方量写参数 $\log d_0,2\log L,2\log H,\log B$，分别是 $2z,2\ell,2h,2v$，不得把这项倍数变化与截止的 $\varphi$ 因子混为一谈。

**定理 19.2（端点制度的准确有限公式）。** 若 $s_0\le1$，站立条件强迫 $\gamma<0$，任意 $H>0$ 可行。若 $s_0>1$，令

$$
\eta=\ell/z-1>-1/2.
$$

非零预测的充要条件还可写为

| 19端点参数 | 准确条件 |
| --- | --- |
| 19叶阈值 $\eta\le1$，即 $L\le s_0^2$ | $H\ge s_0$ |
| 19有限中间区 $1<\eta<\varphi$ | $H\ge s_0^{\psi(\eta)}$ |
| 19临界端点 $\eta=\varphi$，即 $L=s_0^{\varphi^2}$ | $H>1$ |
| 19收缩端点 $\eta>\varphi$ | 每个 $H>0$ |

中间区置

$$
\begin{gathered}
G_\eta(m,n)=\max\{(1+\eta)m-\eta n,\ n-\eta m,\ m+(1-\eta)n\},\\
B_\eta=\frac{\eta+1}{\eta+1-\eta^2},\\
\mathcal E_\eta=\{(m,n):1\le m\le\lfloor B_\eta\rfloor,
\ m<n\le\lfloor\eta m+1\rfloor,\ (m,n)\notin(2\mathbb N)^2\},\\
\psi(\eta)=\min\bigl(\{1\}\cup
\{G_\eta(m,n):(m,n)\in\mathcal E_\eta\}\bigr)>0.
\end{gathered}
$$

证明。$s_0\le1$ 时，若 $\ell>0$ 直接有 $\gamma<0$；若 $\ell\le0$，则 $z<2\ell\le\ell/\varphi^2$，仍收缩。以下取 $z>0$。纯组成中 $\alpha$ 的 $f_2=z$、$\beta$ 的 $f_1=z$，不能低于叶阈值；$\alpha$ 在等叶长处达到它。对混合 $n\le m$，若 $v<0$，则 $f_0\ge mz\ge z$；若 $v\ge0$，则 $f_2\ge(m+n)z\ge2z$。故任何改善必须有 $n>m\ge1$。此时三线关于 $v$ 的斜率均正，其最优点为 $v=z-\ell=-\eta z$，由实际端点制备 $a=Le_1,b=(s_0/L)e_2$ 实现；该点最大对数除以 $z$ 恰为 $G_\eta$。

当 $\eta\le1$，第三项 $m+(1-\eta)n\ge m\ge1$，不能改善叶阈值，得第一行。当 $1<\eta<\varphi$，任何可与叶持平或改善的组成须有 $G_\eta\le1$，由前两项得到

$$
\frac{(1+\eta)m-1}{\eta}\le n\le\eta m+1,\qquad
(\eta+1-\eta^2)m\le\eta+1.
$$

这证明有限集 $\mathcal E_\eta$ 覆盖全部可能优化者；略去的组成的指数严格大于1。前两项不能同时非正，否则会有 $1+1/\eta\le n/m\le\eta$，与 $\eta^2<\eta+1$ 矛盾。因此有限最小值正，且每个所留组成有实际树及端点制备，阈值达到。

当 $\eta=\varphi$，令 $e=n-\varphi m$，端点三项为 $-\varphi e,e,-e/\varphi$；整数组成及无理性给 $e\ne0$，最大值严格正。连续 Fibonacci 组成 $(F_j,F_{j+1})$ 的 $e=(-1)^j\varphi^{-j}\to0$，相邻数互素、不会双偶，故均在支撑内。其最大指数趋于零但不达到，正是定理18.3的临界制度。若 $\eta>\varphi$，选择有理比值 $1+1/\eta<n/m<\eta$，约成互素正整数后取任意大奇数倍。支撑仍非双偶，前两项负；第三项是前两项的和，也负。其倍数趋向负无穷，证明任意 $H>0$ 可行。

**命题 19.3（其它有限列表与同一阈值）。** 在 $1<\eta<\varphi$，也可用全部支持的 $n>m\ge1$ 且

$$
m+n\le\frac{\varphi^3}{\varphi-\eta}
$$

计算 $\min(\{1\}\cup\{G_\eta\})$；或使用较小加权列表 $m+\varphi n\le\varphi^3/(\varphi-\eta)$。两者均给 $\psi(\eta)$，与定理18.4的区间优化相同。

证明。令 $a_0=(1+\eta)m-\eta n,b_0=n-\eta m$，则

$$
a_0+\varphi b_0=(\varphi-\eta)(n+m/\varphi),\qquad
G_\eta\ge\frac{(\varphi-\eta)(m+\varphi n)}{\varphi^3}
\ge\frac{(\varphi-\eta)(m+n)}{\varphi^3}.
$$

超出任何所列截止的组成的最大值大于1，不能改善或持平。另一方面 $\gamma=z(\varphi-\eta)/\varphi^2$，故加权截止恰是定理18.4的 $\mathcal F$ 截止。纯组成及 $n\le m$ 已由定理19.2排除改善，$n>m$ 的区间最小值确在端点，故两个优化相同。较宽列表不意味着其每个组成都可行；必须仍计算完整最大值。

**例 19.4（非平滑阈值与零目标的非零初值）。** 精确公式给

$$
\psi(5/4)=3/4,\quad\psi(3/2)=1/2,\quad
\psi(8/5)=1/5,\quad\psi(21/13)=1/13.
$$

前两值可直接检查各自 $\mathcal E_\eta$：$m$ 分别至多3及10；$\eta=5/4$ 的列表是 $(1,2),(2,3),(3,4)$，最大指数分别为 $3/4,5/4,2$；若 $\eta=3/2$，正的 $G_\eta$ 是半整数，$(1,2)$ 达到 $1/2$。后两值无需更大枚举：正的 $G_{8/5},G_{21/13}$ 分别为 $1/5,1/13$ 的整数倍，组成 $(3,5),(8,13)$ 分别给三项 $(-1/5,1/5,0),(-1/13,1/13,0)$。它们都在实际支撑中，因此达到对应下界。例如 $\eta=8/5$ 的同源三范数为 $(s_0^{-1/5},s_0^{1/5},1)$。$L=2,d_0=4$ 给 $\eta=0,H_*=2$。

零目标制度不意味着初值也零。对任意站立参数，取

$$
a=Le_1,\qquad b=\xi e_1+(\sqrt{d_0}/L)e_2,
$$

其中 $0<\xi<\sqrt{L^2-d_0/L^2}$ 且 $L\xi\sqrt{d_0}\le H$；这样的小 $\xi$ 总存在。命题5.3的实际树 $\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle$ 有初值 $CK\ne0$，范数 $L\xi\sqrt{d_0}$，零标签及全零尾，且两叶界与 $\Delta=d_0$ 同时成立。

这些判据是数学实参数的精确存在性决定；未知实数的相等或整数截止的有限位有效决定仍需表示合同。证明中的组成搜索不成为内部观察者的数量端口。

## 20. 同一破坏性历史的有限精度取得、恢复风险与位成本

**定义 20.1（联合有界误差取得合同）。** 对一个未知 $(t,p)\in\mathcal D_{L,H,d_0}$ 执行

$$
\operatorname{Read},\rho,\operatorname{Read},\rho,
\operatorname{Read},\operatorname{Stop}.
$$

这是三次付费完整向量回复、两次破坏性原更新的一条实际历史，停止时当前源为 $\rho^2t$。另供应同时误差承诺

$$
|y_j-x_j|\le\delta\qquad(0\le j\le2),\quad\delta\ge0.
$$

制备和动作仍准确。三个误差可联合对抗、相关及依赖历史，不假设独立抽样、复读、平均、噪声分布或重播。回复不必是任何精确实际 $W_3$。公共界只是制备／仪器供应者承担的域与精度承诺，不是读出原 $a,b$ 的校准。

**定理 20.2（无需额外端口的显式恢复器）。** 计算

$$
\widetilde w=y_2\times y_1,\qquad
\widehat x_3=\operatorname{sgn}(y_0\cdot\widetilde w)\widetilde w,
\quad\operatorname{sgn}(0)=0.
$$

对每个允许实际来源和误差三元组，

$$
|\widehat x_3-x_3|\le\frac4c(H^2+2H+\delta)\delta.
$$

特别在 $\delta\le1$ 时，$C_{\rm err}=4(H^2+2H+1)/c$ 是充分线性系数。恢复器本身不读取公共参数、组成、树码、校准或附加符号，也不作归一化、除法或源更新。

证明。展开带误差叉积给

$$
|\widetilde w-w|\le b_\delta:=(2H+\delta)\delta.
$$

若 $w=0$，或计算符号与实际非零符号相同，目标误差至多 $b_\delta$。若符号错误或计算符号为零，目标误差至多 $2|w|+b_\delta$。令 $u_0=|x_0|$。若 $u_0<2\delta$，推论16.3给此误差至多 $4H^2\delta+b_\delta$，不超过所述界。若 $u_0\ge2\delta>0$，两标量异号或计算值为零，故

$$
\begin{aligned}
cu_0|w|&\le|x_0\cdot w-y_0\cdot\widetilde w|\\
&\le\delta|w|+(u_0+\delta)b_\delta
\le H^2u_0\delta+\tfrac32u_0b_\delta.
\end{aligned}
$$

因此误差至多 $2H^2\delta/c+(3/c+1)b_\delta\le(4/c)(H^2\delta+b_\delta)$，恰为所述界。$c<1$ 保证上述常数比较。$\delta=0$ 时定理5.1给准确结果，含全部零分支。错误符号的幅度由实际来源约束控制，而非由仪器免费供应符号裕量。

**推论 20.3（固定三读的准确风险阶与抽象选择边界）。** 假设除这三个回复及相同日程／Stop 元数据外，没有精确来源、语法、制备或时间费用侧信道；误差允许定义20.1的完整三个乘积球。令

$$
R_\delta=\inf_{R:((\mathbb R^3)^3)\to\mathbb R^3}
\sup_{\substack{(t,p)\in\mathcal D_{L,H,d_0}\\|y_j-x_j|\le\delta}}
|R(y)-x_3|.
$$

这里允许全部集合函数，不附有效性、可测性或连续性约束。复用 [Recovery Geometry 定义3.1及定理3.2](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 的候选纤维原则，得到

$$
\frac12\omega(2\delta)\le R_\delta\le\omega(2\delta).
$$

非零制度的固定记录对抗风险为 $\Theta(\delta)$；全零目标制度的类感知常零恢复器风险零，并可免去专为 $x_3$ 的取得。通用带噪公式本身在后一制度不必输出零。

证明与接口对应。取 $X=\mathcal D_{L,H,d_0}$、数据空间 $Y=(\mathbb R^3)^3$、合法中心空间 $S=\mathbb R^3$、目标 $F(t,p)=x_3$，噪声关系就是定义20.1。任意距离至多 $2\delta$ 的两实际记录都可产生同一逐分量中点回复，任一共同输出至少在一端误差为目标差的一半。取上确界给下界，即使上确界未达到也成立。上界可为每个非空兼容来源纤维选一个实际来源并输出其目标；同一数据的其它兼容记录距它至多 $2\delta$，故误差至多 $\omega(2\delta)$，空纤维可输出零。该选择是集合函数存在，不是有限来源搜索。定理20.2另给无需选择的有限运算上界。定理17.2的实际旋转对给非零制度的反向阶。

这仅是该固定记录及完整误差关系的下界；更丰富付费协议或某个确定量化器，未必允许中点回复，不能自动继承它。

**命题 20.4（离开实际像的 Lipschitz 延拓存在）。** 令 $\mathcal A=W_3(\mathcal D_{L,H,d_0})$，则 $x_3=f(W_3)$ 在 $\mathcal A$ 上良定义且 $K_*$-Lipschitz。它有到全部 $(\mathbb R^3)^3$ 的向量延拓，常数至多 $\sqrt3K_*$；此存在性不供应有限求值器或像外数据的实际来源身份。

证明。定理5.1给良定义，定理17.1给 Lipschitz。对每个输出坐标 $i$ 使用 McShane 标量延拓（文献见约定23.1）：

$$
\overline f_i(y)=\sup_{z'\in\mathcal A}
\{f_i(z')-K_*d(y,z')\}.
$$

固定一个 $z_0\in\mathcal A$，三角不等式和像内 Lipschitz 给被取上确界的每项至多 $f_i(z_0)+K_*d(y,z_0)$；$z'=z_0$ 又给有限下界，故值有限。若 $y\in\mathcal A$，像内不等式使每项至多 $f_i(y)$，$z'=y$ 达到等号。各项关于 $y$ 的 Lipschitz 常数为 $K_*$，取上确界仍保持，三个坐标的 Euclidean 组合给 $\sqrt3K_*$。本证明不需要像闭合、紧性或有限树集。无限上确界和抽象纤维选择各有自己的实现义务；取得与位成本由下一命题的直接公式承担。

**命题 20.5（dyadic 回复的有限整数解码）。** 若仪器实际供应

$$
y_{jk}=n_{jk}2^{-b},\quad n_{jk}\in\mathbb Z,\quad b\in\mathbb N,
$$

并保证定义20.1的同时误差，则定理20.2可由固定次数整数乘加与整数符号比较实现，准确包含计算结果为零的分支。最近坐标舍入本身的 Euclidean 向量误差至多 $\sqrt3\,2^{-b-1}$；若另有传感误差，其与量化误差用三角不等式明确合成总 $\delta$。

证明与共同资源。$\delta\le1$ 时 $|y_{jk}|\le H+1$，九个分子各需 $O(1+b+\log(1+H))$ 位，记此宽度为 $B_{\rm num}$。叉积公共分母为 $2^{2b}$，点积公共分母为 $2^{3b}$，正分母不影响符号。用整数准确计算两者，返回带该符号的 dyadic 叉积，不需要未表示实数的符号 oracle。最终再舍入输出时，其向量误差 $\xi_{\rm out}$ 加到定理20.2右侧。

同一实现保留九个 $O(B_{\rm num})$ 位数值字，另保留付费的动作／读数／时间／Stop／源版本身份与 live 源句柄。固定数量的 $O(B_{\rm num})$ 位临时字和三个输出字足够；中间乘积宽度只是输入宽度的固定倍数。学校乘法及加法给 $O(B_{\rm num}^2)$ 位工作、$O(B_{\rm num})$ 临时位。三个先后回复必须按实际历史取得与保留，树／组成／语法寄存器不在合同中。

有效选择输出容差，还需可用的保守公共界 $\overline H\ge H$、$0<\overline c\le c$；选择 $b$ 使总 $\delta\le1$ 且

$$
\frac{4(\overline H^2+2\overline H+1)}{\overline c}\delta
+\xi_{\rm out}
$$

不超过所求容差。单有数学实常数不供应这一计算表示。这些是取得后的保留／解码／输出成本，不给制备或界的认证、物理有限位 Read、准确 $\rho$ 执行、隐藏树存储及无界树求值定价；显式树码另供时才适用命题13.2的逐节点成本。近似动作或制备误差需另建合同，不能挤进纯读数误差。

若一个另外声明的随机模型保证同时事件 $|y_j-x_j|\le\delta$ 的概率至少 $1-\alpha$，则上述逐路径结论在该事件上成立，因而具有该概率保证。独立性、集中估计、分布风险和复读平均收益均不从此推出。当前有限整数解码已给同域线性误差阶与位阶；引入公共参数、守卫和有理除法的截断／裁剪公式不构成这里已证明的取得或资源改进，常数最优性及另求恢复器连续性的任务仍分别保留。

## 21. 仅有三读幅度界的较宽来源：尖锐平方根边界

**定义 21.1（全制备的较宽实际域）。** 令

$$
\mathcal D_H=\{(t,p)\in\mathcal T\times(\mathbb R^3)^2:
q_0,q_1,q_2\le H\}.
$$

原树、叉积和 $\rho$ 都不变，制备允许任意大小及依赖叶对，没有 $L,d_0$ 条件。以相同三读距离及目标定义模量 $\Omega_H$。它是另一个实际来源问题，不替代定义16.1。

**定理 21.2（全制备的平方根上界）。** 对所有 $H>0,\varepsilon\ge0$，

$$
\Omega_H(\varepsilon)\le
\min\{2H^2,\max(2H\varepsilon,\sqrt6H^2\sqrt\varepsilon)\}.
$$

证明。推论16.3的 $|x_0\cdot w|\ge q_2^2$ 不需要叶界或非退化下界；定理5.1也覆盖依赖及零标签来源。任一实际对的 $|w-w'|\le2H\varepsilon$。零或同符号分支的目标差至多此量；异号分支满足

$$
q_2^2+(q'_2)^2\le|x_0\cdot w-x'_0\cdot w'|
\le H^2\varepsilon+H(2H\varepsilon)=3H^2\varepsilon.
$$

故目标差至多 $H(q_2+q'_2)\le\sqrt6H^2\sqrt\varepsilon$。最后每目标范数仍至多 $H^2$，给独立幅度截断。每个分支使用的两成员都在同一较宽实际域中。

**定理 21.3（保留原括号与联合限制的实际平方根尖锐对）。** 对每个 $H>0$ 有 $\Omega_H(\varepsilon)=\Theta(\sqrt\varepsilon)$ 当 $\varepsilon\downarrow0$。

证明。固定 $h_0,h_1\in(0,H)$。在正向正交标架中取足够小 $s>0$，置

$$
\begin{gathered}
r=\sqrt{h_1/s},\quad B=r^2,\quad \Delta=s^2,\quad
C=\sqrt{h_0^2h_1/s^3-s^2}>0,\\
b=re_1,\qquad a=(C/r)e_1+(s/r)e_2.
\end{gathered}
$$

直接计算得到

$$
A=h_0^2/s^2,\quad K=se_3,\quad V=rse_2,\quad
U=(s/r)(-se_1+Ce_2).
$$

取字面树 $t=\langle\alpha,\langle\alpha,\beta\rangle\rangle$，初值为 $U$、单位标签 $-f_2$。运输及五符号表给其一、二阶表达式 $-BK,-\Delta V$，故

$$
x_0=(s/r)(-se_1+Ce_2),\quad |x_0|=h_0,\quad
x_1=-h_1e_3,\quad x_2=-qe_2,\quad q=rs^3=\sqrt{h_1}s^{5/2}.
$$

令 $\theta=2\arctan(s/C)$，构造第二制备

$$
\begin{gathered}
b'=r(\cos\theta e_1+\sin\theta e_2),\quad K'=-se_3,\\
V'=rs(\sin\theta e_1-\cos\theta e_2),\qquad
a'=(C/B)b'+V'/B.
\end{gathered}
$$

$K'\times b'=V'$，并由 $b'\perp V'$ 得 $b'\times a'=K'$；后一个恒等式也可用 $b'\times(K'\times b')=BK'$ 核对。两制备的 $A,B,C,\Delta$ 完全相同。选第二字面树 $t'=\langle\langle\alpha,\beta\rangle,\alpha\rangle$，即在构造另一来源时反转根次序；它的初值为 $-U'$，标签 $+f_2$，两尾为 $BK',\Delta V'$。半角恒等式给

$$
\cos\theta=\frac{C^2-s^2}{C^2+s^2},\qquad
\sin\theta=\frac{2Cs}{C^2+s^2},\qquad
U'=\frac{CV'-\Delta b'}B=(s/r)(se_1-Ce_2)=-U.
$$

因此

$$
x'_0=x_0,\quad x'_1=x_1,\quad
x'_2=q(\sin\theta e_1-\cos\theta e_2).
$$

两来源的三范数同为 $(h_0,h_1,q)$，$s$ 足够小时同时在 $\mathcal D_H$。精确记录差与目标差分别为

$$
\begin{aligned}
\varepsilon_s&=2q\sin(\theta/2)
=\frac{2rs^4}{\sqrt{C^2+s^2}}=\frac{2s^5}{h_0},\\
|x_3-x'_3|&=2h_1q\cos(\theta/2)
=\sqrt2\,h_1^{3/2}\sqrt{h_0}\sqrt{\varepsilon_s}\cos(\theta/2).
\end{aligned}
$$

这里实际符号相反，$x_3=-(x_2\times x_1)$、$x'_3=x'_2\times x'_1$，所以不是环境符号分支假设。$s\downarrow0$ 时 $\cos(\theta/2)\to1$；$\varepsilon_s=2s^5/h_0$ 参数化每个足够小正误差，而非只给稀疏序列。由此得到全小误差的平方根下界，结合定理21.2完成尖锐阶。

该对的叶范数为 $|a|=h_0/s,|b|=\sqrt{h_1/s}$，都发散，且 $\Delta=s^2\to0$。因此它不属于任何固定 $L,d_0$ 的主域，不能反驳定理17.1，也不授予观察者根反转或制备旋转动作。

**推论 21.4（较宽域的条件有限读后果）。** 若定义20.1的同一准确制备／准确动作／联合读误差合同改用 $\mathcal D_H$，同一直接恢复器满足

$$
|\widehat x_3-x_3|\le b_\delta+2H\sqrt{p_\delta},\qquad
b_\delta=(2H+\delta)\delta,\quad
p_\delta=H^2\delta+(H+\delta)b_\delta.
$$

固定三读完整误差球下的最小最坏风险为 $\Theta(\sqrt\delta)$。

证明。若计算符号错误或为零而实际规则符号非零，则

$$
q_2^2\le|x_0\cdot w|
\le|x_0\cdot w-y_0\cdot\widetilde w|
\le\delta|w|+(H+\delta)b_\delta\le p_\delta.
$$

故 $|w|\le Hq_2\le H\sqrt{p_\delta}$，误差至多所列界；零或同符号分支有更小的 $b_\delta$ 界。对实际尖锐对在记录距 $2\delta$ 时使用共同中点回复，推论20.3的同一纤维论证给匹配下界。Dyadic 解码的读数／更新／位阶保持命题20.5所列，但有效输出容差需要平方量级的读误差预算。此处没有可用的统一 $c$，不能套用主域的线性系数。

## 22. 下一输出、准确全未来与全时间误差的区别

**命题 22.1（原实际域内的全未来不一致连续实例）。** 在 $L=2,H=4,d_0=1$ 的主域，若把目标距离改为扩展距离

$$
d_\infty=\sup_{j\ge3}|x_j-x'_j|\in[0,+\infty],
$$

则每个正的初始三读容差都允许 $d_\infty=+\infty$ 的实际对。

证明。取原叶树 $\alpha$，制备 $a=(3/2)e_1,b=(3/2)e_2$。叶范数小于2，$\Delta=81/16\ge1$，初始三范数 $3/2,3/2,9/4\le4$。规范结构递推使 $|x_j|=(3/2)^{F_{j+1}}$，方向循环在三条垂直轴上。绕 $e_3$ 以任意小非零正向角 $\theta$ 同时旋转两叶，保留树；所有初始限制准确保持，$x_0,x_1$ 差随角趋于零，$x_2$ 固定。未来反复出现的 $e_1,e_2$ 方向上的差为

$$
2\sin(\theta/2)(3/2)^{F_{j+1}}\longrightarrow+\infty.
$$

故任意正三读容差可容纳此对。轨道本身也不属于通常有界序列空间 $\ell^\infty$，所以这里使用扩展上确界距离而不虚称其中的有限范数。

本例只证明一组原参数下的全时间限制，不给全参数的时间一致分类。定理5.1的准确全未来相等、定理17.1的稳定下一输出、原制备恢复、同制备上下文与全时间误差是不同目标。零树的完整历史仍不给制备信息；定理6.3及11.1–11.3的上下文／制备纤维边界也保留。关系模型中的这些恢复结果不自动提供物理空间、时钟或记忆装置的识别。

## 23. 稳定性结果的来源、精确核验与保留边界

**约定 23.1（所复用接口及主要文献的准确范围）。** 来源与精确解释使用本卷第1–5节；组成支撑使用 [Process Geometry44.1–44.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)，一般恢复纤维使用 [Recovery Geometry3.1–3.4](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)。[Continuation13.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的实际像下降、共同来源及合法域饱和条件保留：准确因子化本身不保证稳定性、制备反演或未知制备间的上下文拼接。原单位方向的控制、Boundary43的另一初态／仪器及 Process44 的数量／方向读口，都不供应本卷的变化叶制备、读误差或额外动作。这里两成员的联合限制由每个实际树／制备见证承担，未用两个边缘的分别可行代替共同实现。

经典叉积基础为 `literature-attested`：Darpö，*Vector product algebras*，[arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，定义及 Lemma2。其特征不为2、交替双线性积、非退化对称型、循环配对与范数条件在定向正定实三维中成立；这里只复用其垂直性及重复向量恒等式，不重复主张向量积分类。

McShane，*Extension of range of functions*，*Bulletin AMS* 40，837–842，[原文](https://www.ams.org/journals/bull/1934-40-12/S0002-9904-1934-05978-0/S0002-9904-1934-05978-0.pdf)，Theorem1 的前提是任意度量空间子集上的实值 Lipschitz 函数，不要求子集闭合或紧致。命题20.4严格使用这一范围，并直接给出上确界的有限性、像内一致与 Lipschitz 证明；它不把数学延拓称为有限取得算法。

Foucart、Liao，*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, but what of the Parameter?*，[arXiv:2111.02601v1](https://arxiv.org/pdf/2111.02601v1)，Introduction1.1–1.2 的模型／数据一致纤维及确定最坏误差提供背景。将本卷实际四向量图嵌入 $\mathbb R^{12}$，观察及目标可写成线性坐标投影，但实际模型集仍是原树／制备的图，不能改成环境线性空间。该文专门正则化结果需要 Hilbert 近似模型 $\operatorname{dist}(f,V)\le\epsilon$、Euclidean 数据噪声、$V\cap\ker\Lambda=\{0\}$，部分还需正交归一表示子；本卷实际图及分块最大误差合同没有建立这些前提，不调用其专门算法或最优参数结论。一般候选纤维／选择、协变性、Fibonacci 闭式、范数不等式与分段线性优化都是复用基础。

实际投影幅度约束、无界树及变化制备的模量、准确阈值与有限算术取得后果，以及另域的实际平方根尖锐对，是声明源合同下的仓内综合推导（`repo-derived`）。这里只提供普通数学证明和有限精确佐证，不新增 Lean 核验、不作全球原创性或文献穷尽声明。

**约定 23.2（针对有限算术与阈值的精确核验结果）。** 有理数核验取1–4叶全部102棵字面有序树，及三个制备

$$
\begin{aligned}
p_1&=((1,0,0),(0,1,0)),\\
p_2&=((3/2,1/2,0),(1/2,3/2,1/2)),\\
p_3&=((1/2,1,1/2),(1,-1/2,1)).
\end{aligned}
$$

在 $L=3,H=16,d_0=1$ 下有274个允许树／制备对。对 $b=0,1,2,3,4$ 将各坐标舍入至最近 $2^{-b}$ 格点，再分别使用未附加扰动、或在九个坐标之一附加 $\pm2^{-b},\pm2\cdot2^{-b}$ 共37种回复；同时误差界取 $\delta=3\cdot2^{-b}$。有理平方范数准确核对了50,690个回复实例的误差合同和定理20.2，包含41,070个真实零叉积、9,347个相同符号、188个计算零符号与85个相反符号实例。实际四向量以原括号求值及定理3.1运输取得；没有把带噪回复当作精确实际记录。

两项另外的有理端点核对取 $\eta=7/5,17/11$，较小端点列表的 $m$ 上限分别为5、16，含8、63个混合组成；准确 $\mathbb Q(\sqrt5)$ 加权截止列表含81、768个支持组成。三线交点优化与端点公式分别给共同指数 $3/5,4/11$，实际组成见证为 $(1,2),(3,5)$。这些有限核验可检出有限算术或有限列表的错误；所有列表覆盖、临界未达到、任意制备、任意树大小及全小误差尖锐阶仍由第16–22节的普通证明承担，不以样本给无限结论或给原来源加大小配额。

**约定 23.3（已回答的任务与尚需单独合同的问题）。** 开放问题15.2的下一向量稳定性及准确零／线性制度由定理17.1–19.3给出；有限误差取得由定义20.1的额外仪器承诺支持，较宽来源与全未来分别按第21、22节的量词承担。最优常数、更丰富付费协议的下界、制备／动作不确定性、物理认证与价格、另供随机规律、任意上下文及全参数全时间分类均需另外研究，未作为这里的前提。抽象上确界、选择或参数存在与有限算法分开；原源、操作、记录、精度及共同实现的限制不因某个恢复公式而消失。

## 追加锚（本行以下为增补区）
## 24. 固定三向量记录的全时间模量

本节至第32节保持定义16.1的全部实际来源及定义20.1的一条取得历史，将目标从下一向量改为所有 $j\ge3$ 的共同误差上确界。原树大小和预测时刻都无统一上限，原制备在每个来源的执行中固定。第1–5节的精确恢复、第16–19节的实际投影与存在性阈值直接复用；下一向量连续不自动给出本节的全时间结论。

**定义 24.1（全时间扩展距离与模量）。** 固定 $L,H>0$、$0<d_0<L^4$，取 $\mathcal D=\mathcal D_{L,H,d_0}$。对 $s=(t,p),s'=(t',p')\in\mathcal D$ 置

$$
\begin{aligned}
d_3(s,s')&=\max_{0\le i\le2}|x_i(s)-x_i(s')|,\\
d_\infty(s,s')&=\sup_{j\ge3}|x_j(s)-x_j(s')|\in[0,+\infty],\\
\Omega(\varepsilon)&=\sup_{\substack{s,s'\in\mathcal D\\d_3(s,s')\le\varepsilon}}d_\infty(s,s')\qquad(\varepsilon\ge0).
\end{aligned}
$$

空上确界取零。每对的两个成员分别满足两叶界、$\Delta\ge d_0$ 和三个读数界；不以环境三元组代替实际像。记

$$
\begin{gathered}
\varphi=(1+\sqrt5)/2,\quad \psi=-1/\varphi,\quad
s_0=\sqrt{d_0},\quad z=\log s_0,\quad\ell=\log L,\\
G=\varphi^2z-\ell=\varphi^2\gamma,\qquad
D_{\rm crit}=L^{2/\varphi^2},\qquad c=s_0/L^2\in(0,1),\\
F_0=0,\quad F_1=1,\quad F_{n+2}=F_{n+1}+F_n.
\end{gathered}
$$

这里 $\gamma$ 恰为定义18.1的参数，$H_*$ 恰为定理18.4的实际达到阈值，不另定义不同的阈值。$U,V$ 继续使用定义16.1的记法。

**定理 24.2（原全来源的完整全时间制度）。** 对每组站立参数，$\Omega(0)=0$。正误差下的制度如下；$\Theta$ 均指 $\varepsilon\downarrow0$、系数可依固定 $L,H,d_0$。

| 24实际参数制度 | 全时间结论 |
| --- | --- |
| 24收缩叶界 $L<1$，任意 $H>0$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24单位叶界 $L=1,H<1$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24单位叶界 $L=1,H\ge1$ | $\Omega(\varepsilon)=1$，$0<\varepsilon\le(2+6/c)^{-1}$ |
| 24可达收缩 $L>1,d_0<D_{\rm crit},H<1$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24可达临界近似 $L>1,d_0<D_{\rm crit},H=1$ | $\Omega(\varepsilon)=1$，$0<\varepsilon\le(2+6/c)^{-1}$ |
| 24超单位读界 $L>1,d_0<D_{\rm crit},H>1$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$ |
| 24临界排除 $L>1,d_0=D_{\rm crit},H\le1$ | $\Omega\equiv0$ |
| 24临界超单位读界 $L>1,d_0=D_{\rm crit},H>1$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$ |
| 24正增长但未达阈值 $L>1,d_0>D_{\rm crit},H<H_*$ | $\Omega\equiv0$ |
| 24正增长且达到阈值 $L>1,d_0>D_{\rm crit},H\ge H_*$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$，包括 $H=H_*$ |

在线性行，令 $M=\min(L,H)<1$，则每个误差下 $\Omega\le2M^2$，且有定理26.2的全时间线性上界。在两个单位平台行，所有误差下 $\Omega\le2$，并且 $\varepsilon\ge2$ 时恰等于2。除此之外的有限误差完整曲线及最优线性系数未在此确定。

证明。定理5.1在实际三读像上恢复完整未来，故 $d_3=0$ 迫使全部未来相同。零 cherry 在任意允许正交制备处供应全零历史，$\mathcal D$ 非空。引理25.1–25.2给增长制度，定理26.2–26.3给全部线性行，定理27.1–27.4给两平台行及两个误差端点，定理28.1–28.2给零与无穷行。若 $L\le1$，站立条件 $z<2\ell$ 强迫 $G<0$；若 $L>1$，$G$ 的符号恰为 $d_0-D_{\rm crit}$ 的符号。因此各行互斥且穷尽全部参数。

## 25. 正幅度增长与既有实际阈值的对应

**引理 25.1（实际尾的增长判据）。** 非零尾的 $r=|b|,s=\sqrt\Delta$、$\nu(t)=(m,n)$ 沿用定理4.3。置

$$
\Gamma(p)=\log r+\varphi\log s.
$$

则 $\Gamma<0,=0,>0$ 分别使 $q_j\to0,1,+\infty$。方向保留定理4.3的三循环；零标签来源的全部 $j\ge1$ 向量仍为零。

证明。定理4.3给 $q_{j+2}=q_jq_{j+1}$，两个初值严格为正。归纳得到经典正输入乘法递推的公式

$$
q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\qquad(j\ge2).
$$

取对数，特征根为 $\varphi,\psi$，主项系数的符号是 $\log q_1+\varphi\log q_2$ 的符号。实际齐次性给

$$
\log q_1+\varphi\log q_2=(m+\varphi n)\Gamma(p).
$$

非空树使 $m+\varphi n>0$。主项为零时只剩 $O(\varphi^{-j})$，所以幅度趋于1；其余主项趋于正或负无穷，得到另两结论。先分出实际零尾再取对数，不删除零分支。

**引理 25.2（原叶界允许的增长参数）。** 两叶界及行列式下界所容许的 $(r,s)$ 恰为

$$
s\ge s_0,\qquad s\le Lr,\qquad r\le L.
$$

因此 $\min\Gamma=G$，在 $(a,b)=(Le_1,(s_0/L)e_2)$ 达到；$\max\Gamma=(1+2\varphi)\ell$，在两正交叶长均为 $L$ 时达到。

证明。$s^2=\Delta\le|a|^2|b|^2$ 给必要性。每个所列 $(r,s)$ 都由同一正交制备 $((s/r)e_1,re_2)$ 实现。给定 $s$，最小 $r$ 是 $s/L$，于是 $\Gamma\ge\varphi^2\log s-\ell\ge G$；两者等号同时由所列端点达到。另一方面 $r\le L,s\le L^2$，得最大值及其正交达到。

**约定 25.3（同一个有限阈值及两处未达到端点）。** 定理18.2的 $f_0,f_1,f_2$、区间 $I=[z-\ell,\ell]$ 和实际组成支撑 $\mathcal S$ 原样复用。其三线不等式有实际树／正交制备的反向见证；组成列表只为证明或离线存在性计算服务，没有给观察者组成口或来源大小上限。

在 $G>0$ 时，可把同一个 $H_*$ 写为较小截止

$$
\begin{gathered}
Q=\frac{\varphi^2z}{G},\qquad
\mathcal F_0=\{(m,n)\in\mathcal S:m+\varphi n\le Q\},\\
\log H_*=
\min_{(m,n)\in\mathcal F_0}\min_{v\in I}\max(f_0(v),f_1(v),f_2(v)).
\end{gathered}
$$

对应证明就是命题19.1的较小截止：若三读上界不超过 $s_0$，则

$$
(m+\varphi n)G\le\log q_1+\varphi\log q_2\le\varphi^2z.
$$

原叶 $\alpha$ 在等叶长 $\sqrt{s_0}<L$ 处已有上界 $s_0$；故每个可能持平或改善者都在 $\mathcal F_0$。定理18.4所用较宽列表的截止为 $\varphi z/\gamma=\varphi Q$；两列表保留相同完整三线检验，覆盖所有优化者，因此最小值及实际达到身份相同。以 $m+n\le\lfloor Q\rfloor$ 或更宽总数截止代替加权列表也可以，条件是仍只用 $\mathcal S$ 并检验全部三线；覆盖不意味着每个所留组成都可行。若采用 $G/\varphi$ 而非 $\gamma=G/\varphi^2$ 作为增长记法，也必须把截止乘数同时换算，不能仅比较参数名称。

所以 $G<0$ 的非零三读上界下确界为0而不达到，$G=0$ 的下确界为1而不达到，$G>0$ 的 $1<H_*\le s_0$ 有实际达到者；这是定理18.3–18.4的同一端点结论。定理19.2–19.3的端点变量 $\eta=\ell/z-1$ 及有限公式也不变：$d_0\ge L$ 时 $H_*=s_0$，$D_{\rm crit}<d_0<L$ 时 $1<H_*<s_0$；$\eta=\varphi$ 是未达到的临界1，$\eta>\varphi$ 是未达到的0。这些既有阈值与例19.4覆盖的 $L=e,d_0=e^{4/5},H_*=e^{1/5}$ 都不是另一个全时间结果。

## 26. 非负单项式的全时间界与尖锐线性阶

**引理 26.1（三个对应锚与第一锚误差）。** 假设两实际来源的 $q_0,q_1,q_2$ 均不超过 $M>0$，且 $d_3\le\varepsilon$。置

$$
K(M)=2M+\frac{2M(2M+1)}c.
$$

则 $|x_3-x'_3|\le K(M)\varepsilon$。对单个来源及 $j\ge3$，记

$$
a_j=F_{j-2},\quad b_j=F_{j-1},\quad
k_j=1+((j-1)\bmod3).
$$

有不含负指数或除法的实际公式

$$
x_j=
\begin{cases}
q_1^{a_j-1}q_2^{b_j}x_1,&k_j=1,\\
q_1^{a_j}q_2^{b_j-1}x_2,&k_j=2,\\
q_1^{a_j-1}q_2^{b_j-1}x_3,&k_j=3.
\end{cases}
$$

约定 $0^0=1$，零尾也满足公式；$j=3$ 的最后一个系数恰为1。

证明。非零尾用定理4.3的三循环和引理25.1的正幅度式，同一相位的向量与相应锚同向，直接得到三个系数。此范围 $a_j,b_j\ge1$，故指数非负；零尾的三个锚均零，不作除法仍得准确值。

为给第一锚的充分系数，写 $w=x_2\times x_1$，双线性给 $|w-w'|\le2M\varepsilon$。同号或任一零尾由定理5.1直接使用此界。若两非零实际符号相反，三个归一化读数的有符号三重积各自绝对值至少为 $c$，差至少 $2c$。不等式

$$
\left|\frac{x}{|x|}-\frac{y}{|y|}\right|\le\frac{2|x-y|}{|x|}
$$

及三重积逐因子相减给

$$
2c\le2\varepsilon(q_0^{-1}+q_1^{-1}+q_2^{-1})
\le\frac{2\varepsilon(2M+1)}{q_2}.
$$

末步用推论16.3的 $q_2\le q_0q_1$ 及 $q_0,q_1\le M$，得 $q_0,q_1\ge q_2/M$。所以 $q_2\le(2M+1)\varepsilon/c$；实际异号目标差至多

$$
|w-w'|+2|w|\le2M\varepsilon+2Mq_2\le K(M)\varepsilon.
$$

归一化只用于证明且各所除量已非零。这个第一锚系数是既有下一步线性控制的一个充分推论，不主张新的下一步最优常数。

**定理 26.2（原全树的全时间线性上界）。** 在定理24.2的线性行，令 $M=\min(L,H)<1$、$K_0=\max(1,K(M))$，则对每个 $\varepsilon\ge0$，

$$
\Omega(\varepsilon)\le
\min\left\{2M^2,\left(K_0+\frac{M}{(1-M)^2}\right)\varepsilon\right\}.
$$

证明。若 $L\le1$，由 $|u\times v|\le|u||v|$ 的结构归纳，任意非空原树 $u$ 满足 $|E_p(u)|\le L^{\#\text{叶}(u)}\le L$；每个替换树仍是这样的树。三读界又给 $q_0,q_1,q_2\le H$，故三锚的前两个范数至多 $M$，第三为 $q_1q_2\le M^2\le M$。若 $L>1,H<1$，直接由三读界得到相同结论。

对 $[0,M]^2$ 上总次数为 $n$ 的非负单项式，逐个相减其 $n$ 个因子给大小至多 $M^n$、两值之差至多 $nM^{n-1}\varepsilon$；次数0的差为零。$q_1,q_2$ 的范数差均至多 $\varepsilon$。引理26.1的每个未来向量是一个这样的系数乘相应锚，锚差至多 $K_0\varepsilon$、锚范数至多 $M$，所以向量差至多

$$
(K_0M^n+nM^n)\varepsilon
\le\left(K_0+\sum_{n\ge1}nM^n\right)\varepsilon
=\left(K_0+\frac M{(1-M)^2}\right)\varepsilon.
$$

这个界同时覆盖所有 $j$、所有树和全部零／符号分支，未固定预测时刻或来源大小。正幅度递推还给每个 $j\ge3$ 的范数至多 $M^2$，于是另有 $2M^2$ 界。

**定理 26.3（线性行的实际尖锐对）。** 每个线性行都有正数 $b,\varepsilon_0$ 使 $\Omega(\varepsilon)\ge b\varepsilon$，$0<\varepsilon\le\varepsilon_0$。

证明。引理25.2及站立条件给这些行的 $G<0$；定理18.3供应一个有限实际树及允许制备，其 $x_3\ne0$。固定该来源，令 $M_0=\max(q_0,q_1,q_2)>0$。复用定理17.2的正向旋转对：旋转轴垂直于 $x_3$，并取 $2\sin(\theta/2)=\varepsilon/M_0$，$0<\varepsilon\le2M_0$。同时旋转所供的两个叶并保留同一字面树，叉积等变使全部输出同旋转；两来源的 Gram、叶界与三读范数界逐项保持。记录差至多 $\varepsilon$，$j=3$ 差恰为 $(q_3/M_0)\varepsilon$。故全时间上确界至少为此值。此处构造静态竞争来源，没有给观察者旋转动作。

## 27. 精确单位平台与两套实际收缩族

**定理 27.1（对应锚给局部精确平台上界）。** 在两个单位平台行，$\Omega\le2$，且 $0<\varepsilon\le(2+6/c)^{-1}$ 时 $\Omega(\varepsilon)\le1$。

证明。$L=1$ 或 $H=1$ 都给 $q_0,q_1,q_2\le1$，全部未来范数至多 $q_1q_2\le1$。引理26.1把每个未来写为同相位锚的 $[0,1]$ 系数倍；三个对应锚的距离分别至多 $\varepsilon,\varepsilon,K(1)\varepsilon$，范数至多1。对任意 $u,v$ 及 $\alpha,\beta\in[0,1]$，凸性给

$$
|\alpha u-\beta v|\le\max\{0,|u|,|v|,|u-v|\}.
$$

具体把 $\alpha u-\beta v$ 写成四角值 $0,u,-v,u-v$ 的双线性权重之和即可。$K(1)=2+6/c$，所以规定范围内每个同相位差都至多1。零及异号锚也受同一凸性界控制。

**定理 27.2（原规范树的实际单位平台下界）。** 两个平台行的每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)\ge1$。在 $L>1,d_0<D_{\rm crit},H=1$ 行，下界可完全由每个成员都严格收缩的实际来源对给出，包含 $1<d_0<D_{\rm crit}$。

证明。若 $L=1,H\ge1$，用同一树 $\alpha$，分别供应 $(e_1,e_2)$ 与 $(\lambda e_1,\lambda e_2)$，$\lambda<1$ 趋于1且 $\lambda^4\ge d_0$。两者全部联合限制成立，记录距离 $1-\lambda^2\to0$。前者每个幅度为1，后者的规范幅度为 $\lambda^{F_{j+1}}\to0$，方向相同，故全时间差上确界为1。

以下取第二个平台行。选择

$$
\max(1,s_0)<s_*<L^{1/\varphi^2},\quad
A_*=s_*^{\varphi^2},\quad r_*=s_*^{-\varphi},\quad
p_*=(A_*e_1,r_*e_2),\quad C_*=\log A_*>0.
$$

$A_*,r_*<L$，$\Delta_*=s_*^2>d_0$，且 $\Gamma(p_*)=0$。原规范树 $T_l=\rho^l\alpha$ 的方向循环为 $e_1,e_2,e_2\times e_1$，幅度的准确对数为 $C_*\psi^l$。其原始组成与叶数是

$$
\nu(T_l)=(F_{l-1},F_l)\ (l\ge1),\qquad
N_l=\#\text{叶}(T_l)=F_{l+1}\ (l\ge0).
$$

两个初始树都恰一叶，结构递推给 $N_{l+2}=N_{l+1}+N_l$；组成则按原 $M$ 递推，证明上述索引。因而同乘原叶以 $e^{-\tau}$ 的准确缩放因子是 $e^{-\tau F_{l+1}}$。

令 $k\to\infty$ 只取正的12倍数，定义

$$
\tau_s=\frac{2(1+C_*)\varphi^{-k}}{F_{k+1}},\qquad
\tau_f=\varphi^{k/2}\tau_s.
$$

比较同一实际树 $T_k$ 在两个固定制备 $e^{-\tau_s}p_*$ 和 $e^{-\tau_f}p_*$ 下的历史。两种叶缩放均不增加叶范数；$\tau_f\to0$ 使两行列式 $\Delta_*e^{-4\tau}$ 最终都至少 $d_0$。对取得偏移 $h=0,1,2$，其六个准确对数为

$$
C_*\psi^{k+h}-\tau F_{k+h+1},\qquad \tau\in\{\tau_s,\tau_f\}.
$$

正项至多 $C_*\varphi^{-k}$；即使较小的减项也至少 $2(1+C_*)\varphi^{-k}$。所以六个读数范数都不超过1。固定 $h$ 时这些对数趋于0，且 $k\equiv0\pmod3$ 固定共同三轴相位，因此 $d_3\to0$。

取相对预测时刻 $j_k=3k/4\equiv0\pmod3$。Binet 公式给 $F_{k+j_k+1}/F_{k+1}\asymp\varphi^{j_k}$，从而

$$
\tau_sF_{k+j_k+1}\to0,\qquad
\tau_fF_{k+j_k+1}\to+\infty,\qquad
C_*\psi^{k+j_k}\to0.
$$

两幅度在同一轴上分别趋于1和0。给定任意固定正 $\varepsilon$，最终记录距离不超过它，未来距离可任意接近1，故 $\Omega(\varepsilon)\ge1$。每个成员却有 $\Gamma=-(1+2\varphi)\tau<0$，确实逐个收缩。若 $d_0>1$，任意允许非零历史都必须收缩：三读界给 $\log q_1,\log q_2\le0$，故 $\Gamma\le0$；等号会迫使 $q_1=q_2=1$。组成矩阵的行列式 $m^2+mn-n^2\ne0$（定理6.4的整数／无理根论证）继而迫使 $r=s=1$，与 $\Delta\ge d_0>1$ 矛盾。因此此子制度没有中性来源，下界仍成立。

**命题 27.3（正奇／奇实际树的同一平台见证）。** 第二个平台行也有完全由正奇／奇组成实际树给出的严格收缩对。

证明。选 $\max(1,d_0)<D<D_{\rm crit}$，供应临界制备

$$
p_*=(D^{\varphi^2/2}e_1,D^{-\varphi/2}e_2).
$$

它有严格叶界、$\Delta=D>d_0$。取 $m_h=F_{3h+1},n_h=F_{3h+2}$，$h\ge0$。Fibonacci 递推模2的周期3表明二者都是奇数。使用 Process44.2 从 $\langle\beta,\alpha\rangle$ 双左接标签的实际配方，取得组成 $(m_h,n_h)$ 的非零树；必要时在构造另一来源时反转其根，使单位标签恒为 $+f_3$。每个成员使用这一确定符号的实际树及同一所供制备，不能把组成与方向的两个边缘分别实现。

置 $\delta_h=n_h-\varphi m_h=\psi^{3h+1}$，临界制备的三个初始对数为

$$
w_0=-\tfrac12\varphi\log D\,\delta_h,\qquad
w_1=\tfrac12\log D\,\delta_h,\qquad w_2=w_0+w_1.
$$

令 $e_h=\max(|w_0|,|w_1|)>0$、$\beta_h=2e_h/(m_h+n_h)$，实际供应 $e^{-\beta_h}p_*$。同叶缩放分别从前两对数减去 $(m_h+n_h)\beta_h$、$(m_h+2n_h)\beta_h$，第三对数为前两项之和。因此三个对数都负，且趋于0；$\beta_h\to0$ 保留最终两叶界及行列式下界，$\Gamma<0$。所有记录趋于同一个单位三轴记录 $(f_3,f_1,f_2)$。

给定 $\varepsilon>0$、$\xi\in(0,1/2)$，先选一个最终允许的 $h$，使其记录距该单位记录小于 $\varepsilon/2$。它严格收缩，故有某个 $J\ge3$ 使 $q_J<\xi$。固定这个 $J$ 后，再选更大的 $h'$：其记录仍距单位记录小于 $\varepsilon/2$，而引理26.1在这个固定有限时刻的单项式式使 $q'_J>1-\xi$。两个实际来源相位、符号一致，记录距小于 $\varepsilon$，未来距大于 $1-2\xi$。令 $\xi\downarrow0$ 得同一下界。这一构造与定理27.2共同证明无一致收缩裕量的原来源障碍，不是以标量环境模型代替实际树。

**定理 27.4（单位平台的大误差端点）。** 两个平台行在 $\varepsilon\ge2$ 时均有 $\Omega(\varepsilon)=2$。

证明。上界见定理27.1。若 $L=1$，取单位制备处的 $\langle\beta,\alpha\rangle$ 与根反序树；两个三读及所有未来均为相反单位向量，$d_3=2,d_\infty=2$。若 $L>1,H=1$，取定理27.2中足够晚的任一收缩 $T_k$，及在同一制备处反转它根的实际树。$k\ge2$ 时它确是内部树，原 $\rho$ 保持根的反转且叉积取负，故每个时刻两输出相反。两者全部限制成立，$d_3\le2$；固定相对时刻3的 $q_3\to1$，其距离 $2q_3\to2$。因此上确界2成立，不要求允许的中性树或最大值达到。

## 28. 全零未来与每个正误差的实际无穷对

**定理 28.1（准确零制度）。** 若 $G=0,H\le1$，或 $G>0,H<H_*$，则所有实际未来 $x_j,j\ge3$ 均零，$\Omega\equiv0$。

证明。定理18.3–18.4排除全部非零标签尾；定理4.3给剩余来源的全零尾。这不宣称原初值零或来源域为空。例19.4在每组站立参数都给实际零标签、非零初值见证：取 $a=Le_1,b=\xi e_1+(s_0/L)e_2$，$\xi>0$ 足够小，使 $|b|\le L$ 且 $L\xi s_0\le H$。字面树 $\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle$ 的初值为 $CK\ne0$、范数 $L\xi s_0$，$\Delta=d_0$，三个取得值及全零尾同时合法。

**定理 28.2（准确无穷制度及阈值等号）。** 若 $L>1,G\le0,H>1$，或 $L>1,G>0,H\ge H_*$，则对每个 $\varepsilon>0$ 都有一对同时允许的实际来源满足 $d_3\le\varepsilon$、$d_\infty=+\infty$。

证明。先构造一个允许的非零增长来源。在 $G<0$ 时选择 $\max(1,s_0)<s<L^{1/\varphi^2}$，在 $G=0$ 时取 $s=s_0=L^{1/\varphi^2}$。临界正交制备 $a=s^{\varphi^2}e_1,b=s^{-\varphi}e_2$ 的规范幅度趋于1，所以某个固定有限 $T_k$ 的三个读数都严格小于 $H$。保留 $s$，把 $r=s^{-\varphi}$ 改成 $re^v$，同时把第一叶长改成 $s/(re^v)$。取足够小 $v>0$，第一叶不增加、第二叶仍不超过 $L$，$\Delta=s^2\ge d_0$ 不变。这个固定有限树的三个多项式求值连续，故三个严格读界也保持，而 $\Gamma$ 变为 $v>0$。这里有限连续性只构造一个共同实现的增长来源，未据此断言全时间连续。

在 $G>0,H\ge H_*$ 时，直接使用定理18.4的实际达到者；引理25.2给其 $\Gamma\ge G>0$，包括准确等号 $H=H_*$。

固定上述任一实际增长来源。绕其 $x_1$ 轴作任意小非零正向旋转 $Q_\theta$，第二来源保留原树、供应 $(Q_\theta a,Q_\theta b)$。所有 Gram、叶界及三个读数范数完全保持；角度足够小使 $d_3\le\varepsilon$。$x_2$ 相位垂直于旋转轴；在 $j\equiv2\pmod3$ 的无穷时刻，实际差为 $2\sin(\theta/2)q_j\to+\infty$。这是一个实际成对来源的无限距离，不是分别可达的两个边缘极值；旋转不成为观察者端口。

## 29. 只用含误差旧记录的全时间数值求值器

**定义 29.1（裁剪、第三锚及非负幂求值）。** 在线性行使用公共域界 $M=\min(L,H)<1$。对任意有限实向量报告 $y_0,y_1,y_2$，令 $P_M$ 为到闭 Euclidean $M$ 球的径向投影，计算

$$
Y_i=P_M(y_i),\quad W=Y_2\times Y_1,\quad
Z=P_M\!\left(\operatorname{sgn}(Y_0\cdot W)W\right),\quad
\widehat u=|Y_1|,\quad\widehat v=|Y_2|.
$$

$\operatorname{sgn}(0)=0$。对每个请求的 $j\ge3$，用引理26.1的 $a_j,b_j,k_j$ 返回

$$
\widehat x_j=
\begin{cases}
\widehat u^{a_j-1}\widehat v^{b_j}Y_1,&k_j=1,\\
\widehat u^{a_j}\widehat v^{b_j-1}Y_2,&k_j=2,\\
\widehat u^{a_j-1}\widehat v^{b_j-1}Z,&k_j=3.
\end{cases}
$$

次数0的幂为1。公式对零、非正交、错号及不在实际记录像上的报告都定义；它是保留报告的数值后处理，裁剪不执行源的归一化，也不生成新的制备、读数或动作。

**定理 29.2（全部报告分支的统一第一锚控制）。** 若实际来源在该线性行且同时满足 $|y_i-x_i|\le\delta$、$i=0,1,2$、$\delta\ge0$，则

$$
|Z-x_3|\le K_{\rm err}\delta,\qquad
K_{\rm err}=2M+\frac{4M(2M+1)}c.
$$

证明。径向公式给对球内每个 $z$，$(v-P_Mv)\cdot(z-P_Mv)\le0$。代入 $z=P_Mw$，再加交换 $v,w$ 后的不等式，得

$$
|P_Mv-P_Mw|^2\le(v-w)\cdot(P_Mv-P_Mw)
\le|v-w|\,|P_Mv-P_Mw|.
$$

所以 $P_M$ 为1-Lipschitz，球内点不动，$|Y_i-x_i|\le\delta$。真实 $x_3$ 在球内，最后投影不增加它的误差。设 $w=x_2\times x_1$，双线性给 $|W-w|\le2M\delta$。

真实零尾时 $x_1=x_2=0$，于是 $|W|\le M\delta$，不论报告初值或计算符号为何。真实非零尾而计算符号正确时，投影前误差至多 $2M\delta$。若 $Y_0=0$，$q_0\le\delta$，推论16.3给 $q_2\le M\delta$，计算输出为零且 $|x_3|\le M^2\delta$。若 $Y_1=0$ 或 $Y_2=0$，相应真实范数至多 $\delta$，$W=0$ 且 $|x_3|\le M\delta$。这些情况都满足所述系数。

余下真实三个向量及三个 $Y_i$ 均非零。它们的归一化三重积之差至多

$$
2\delta(q_0^{-1}+q_1^{-1}+q_2^{-1})
\le\frac{2\delta(2M+1)}{q_2}.
$$

若计算符号错误或为零，真实归一化三重积的绝对值至少 $c$，报告的该值异号或零，所以 $q_2\le2(2M+1)\delta/c$。此时投影前误差至多

$$
|W-w|+2|w|\le2M\delta+2Mq_2\le K_{\rm err}\delta.
$$

$W=0$ 而各 $Y_i\ne0$ 的平行报告也在此三重积为零的分支中；证明未假设报告正交或可实现。所用归一化只为估计，定义29.1的求值器不除任何取得幅度。$\delta=0$ 时定理5.1及实际单项式式直接给准确结果。

**定理 29.3（显式记录求值器的全时间精度）。** 在定理29.2的全部条件下，

$$
\sup_{j\ge3}|\widehat x_j-x_j|
\le\left(\max(1,K_{\rm err})+\frac M{(1-M)^2}\right)\delta.
$$

证明。$\widehat u,\widehat v,q_1,q_2\in[0,M]$ 且相应范数差至多 $\delta$；三个真实和计算锚的范数都至多 $M$，锚误差分别至多 $\delta,\delta,K_{\rm err}\delta$。按定理26.2的逐因子单项式估计，对每个对应相位给同一个总次数界，再用 $\sum_{n\ge1}nM^n=M/(1-M)^2$。全证明只把报告当作数值输入，从未当成新的实际来源。故结论同时覆盖全部树大小、全部预测时刻和所有像外分支。

定理20.2的既有直接符号／叉积恢复器也可作为第三锚：在 $\delta\le1$ 时，以其已证充分系数代入同一个全时间单项式估计，得到另一有效线性上界。定义29.1的公共界裁剪与上述系数只是全时间实现的一种选择，不主张第一步位成本或最优常数优于命题20.5。

**推论 29.4（所声明理想运算的成本）。** 对单个请求时刻 $j$，定义29.1可用 $O(j)$ 次理想单位成本整数／实标量运算、$O(j)$ 位宽的指数和固定维数实数工作寄存器求值。

证明。逐次整数递推用 $O(j)$ 次加法取得 Fibonacci 指数，Binet 式给其位宽 $\Theta(j)$；固定数量的幂各用反复平方，乘法数 $O(\log F_j)=O(j)$。裁剪、范数、叉积、点积、准确符号及向量缩放各只有固定次数。九个原报告坐标可原样保留，三个派生锚及两个范数可在固定维数 scratch 中每次重算，或以另计缓存存储保留。请求索引／计数器和每个输出仍分别收费。

这里整数增长字的运算不是单位位工作，实数范数、径向投影的除法、准确符号及公共常数均需另给表示合同。推论仅为理想运算计数，不提供任意实数的有效符号 oracle、全时间舍入精度日程或物理执行成本；无限输出序列也不在有限时间内整体发射。

## 30. 固定取得记录的风险与同时资源

**定义 30.1（确定同时误差的完整序列风险）。** 保持定义20.1的准确制备／准确原动作，三次 Read、两次 $\rho$ 后 Stop；只有旧报告和同一日程／来源版本／时间／动作／Stop 身份可用，不供应来源大小或计时侧信道。允许所有确定集合函数 $R:(\mathbb R^3)^3\to(\mathbb R^3)^{\{j\ge3\}}$，置

$$
\mathcal R_\delta=
\inf_R\sup_{\substack{s\in\mathcal D\\ |y_i-x_i(s)|\le\delta\ (0\le i\le2)}}
\sup_{j\ge3}|R(y)_j-x_j(s)|.
$$

未加效率、可测性或连续性条件。报告误差可完全相关、联合对抗且依赖历史。

**推论 30.2（实际全时间风险制度）。** 对每个 $\delta\ge0$，

$$
\tfrac12\Omega(2\delta)\le\mathcal R_\delta\le\Omega(2\delta).
$$

准确数据有 $\mathcal R_0=0$。线性行的风险为 $\Theta(\delta)$，定理29.3给显式仅用记录的理想运算上界；零行的类感知常零预测准确。平台行每个 $\delta>0$ 都有 $1/2\le\mathcal R_\delta\le1$，且 $\delta\ge1$ 时恰为1。无穷行每个 $\delta>0$ 都有 $\mathcal R_\delta=+\infty$。

证明与复用对应。沿用推论20.3的候选纤维比较，将目标从 $x_3$ 换成完整 $j\ge3$ 序列及扩展上确界距离；该距离的三角不等式逐时刻成立，取上确界仍成立。任意 $d_3\le2\delta$ 的实际对共享逐分量中点报告，任一共同预测在某一端的全时间误差至少为两序列距离的一半，得到下界，包括无穷。每个非空兼容纤维选一个实际来源并报告其准确未来，其它兼容记录与它距离至多 $2\delta$，得到抽象上界；空纤维任取输出。此选择不供应有限成员检验或来源搜索。线性阶由定理26.3及29.3，平台下界由任意正容差的单位平台，平台上界由常零预测，无穷由定理28.2。$\delta\ge1$ 时定理27.4的 $\Omega(2\delta)=2$ 给平台风险的等号。

**推论 30.3（同一实现的取得、位表示与源代码费用）。** 本任务的原取得为

$$
\operatorname{Read}(x_0),\rho,\operatorname{Read}(x_1),\rho,
\operatorname{Read}(x_2),\operatorname{Stop}.
$$

恰有3次完整向量 Read、2次原破坏性更新、每回复宽3及九个保留数值坐标，停止时源是 $\rho^2t$。这些调用与定义29.1的预测算术分开；域／精度承诺 $L,H,d_0,\delta$ 由供应者承担，记录元数据不夹带语法、组成或校准。

若另外声明一个有界坐标格点表示，逐坐标步长至多 $2\xi/\sqrt3$ 可使单向量量化误差至多 $\xi$。在原报告 $|y_i|\le H+\delta$ 的范围中，九个坐标各需 $O(1+\log(1+(H+\delta)/\xi))$ 位，再加表示、精度及身份元数据；固定有界 $\delta$ 时可写为每坐标 $O(1+\log(1+H/\xi))$，常数依该固定界。原始传感、量化、数值运算及最终输出误差有各自预算。命题20.5的 dyadic 第一向量整数解码仍可复用，却未为定义29.1的全时间范数／裁剪／幂给出舍入证明。

若额外实际供应一棵 $N=m+n$ 叶的显式代码，三取得状态的叶数分别为

$$
N=m+n,\quad m+2n\le2N,\quad2m+3n\le3N.
$$

它们各有 $2\#\text{叶}-1$ 个节点；字面逐节点求三个向量的叉积数准确为

$$
(N-1)+(m+2n-1)+(2m+3n-1)=4m+6n-3\le6N-3.
$$

证明。位宽由上述格点误差及坐标范围直接得到；这只是条件表示，不把一个准确实坐标称为有限位资源。叶数使用原 $M,M^2$ 的组成，节点与叉积数使用命题13.2及 Process44.9的满二叉结构归纳。这个推论细化命题13.2的较松 $7N-3$ 显式代码上界，不给无代码观察者新端口，也不给外部 Read／$\rho$ 仪器定价。来源 $N$ 无界，两个调用不能证明源侧维护、存储或感测有 $N$ 无关的物理成本。

付费新读协议改变兼容来源纤维，还要计新读宽度、更新、身份与存储；它不是本固定旧记录任务。确定有界误差下复读可以重复同一误差，平均收益需另供随机律。换度量、固定预测终点、限制树大小、增加共同收缩裕量或其它控制菜单都是另一个问题，未用于定理24.2。

## 31. 达到的精确实例 $H_*(6,4)=32/27$

**定理 31.1（全支撑覆盖的有限精确证书）。** 对 $L=6,d_0=4$，有

$$
H_*=32/27,
$$

且在三读最大值恰为此数时已有实际增长来源。

证明。此时 $z=\log2,\ell=\log6$。两个纯叶的最小读数上界均为2。先证较小组成截止 $Q=\varphi^2z/G<80$，使用纯整数不等式

$$
559^2<5\cdot250^2,\qquad2^{103411}>6^{40000}.
$$

它们分别给 $\varphi^2>1309/500$ 及

$$
\log_2 6<\frac{103411}{40000}
=\frac{79}{80}\frac{1309}{500}<\frac{79}{80}\varphi^2.
$$

所以 $G>\varphi^2z/80>0$。约定25.3证明每个可能改善或持平纯叶上界2的实际组成都满足 $m+n\le m+\varphi n\le Q<80$；枚举更宽的 $m+n\le80$ 安全且覆盖全部原树，不给问题加树大小配额。

若混合 $m>n>0$，$f_0=f_2$ 的交点 $v=-nz/m$ 位于 $[-\log3,\log6]$。两条相反斜率的最大值在那里最小，其值为 $(m+n-n^2/m)z>mz\ge2z$；$f_1$ 在交点更小。因此这些组成不能改善2。若 $n\ge m>0$，三个斜率都非负，区间左端 $v=-\log3$ 给最小值。在该端点，同一实际制备的幅度为

$$
q_0=6^m/3^n,\qquad q_1=2^n/3^m,\qquad q_2=q_0q_1.
$$

以下程序只使用准确整数／有理数，完整测试剩余支撑（包括等组成；双偶数被原支撑排除）：

```python
from fractions import Fraction as Q
assert 559**2 < 5*250**2
assert 2**103411 > 6**40000
best=Q(2); minimizers=[]; supported=0
for m in range(1,81):
    for n in range(1,81-m):
        if m%2==0 and n%2==0: continue
        supported += 1
        if m>n:
            assert Q(m+n)-Q(n*n,m)>m
            continue
        q0=Q(6)**m/Q(3)**n
        q1=Q(2)**n/Q(3)**m
        value=max(q0,q1,q0*q1)
        if value<best: best=value; minimizers=[(m,n)]
        elif value==best: minimizers.append((m,n))
assert supported==2380
assert best==Q(32,27) and minimizers==[(3,5)]
print(supported, str(best), minimizers)
```

输出为 `2380 32/27 [(3, 5)]`。有限程序的覆盖由前述截止及实际三线优化证明承担；程序不给有限样本之外的新无限量词。

为给字面实际达到者，令 $k=\langle\beta,\alpha\rangle$，先双左接 $\alpha$，再两轮双左接 $\beta$，得到八叶树

$$
t=\left\langle\beta,\left\langle\beta,\left\langle\beta,
\left\langle\beta,\left\langle\alpha,\left\langle\alpha,
\langle\beta,\alpha\rangle\right\rangle\right\rangle
\right\rangle\right\rangle\right\rangle\right\rangle.
$$

其组成为 $(3,5)$，单位标签为 $-f_3$。在 $p=(6e_1,e_2/3)$ 处，$|a|=6,|b|=1/3,\Delta=4$，字面有序求值及原运输给

$$
\begin{aligned}
x_0&=(0,0,8/9),&x_1&=(-32/27,0,0),\\
x_2&=(0,-256/243,0),&x_3&=(0,0,8192/6561).
\end{aligned}
$$

前三范数准确为 $8/9,32/27,256/243$，最大值 $32/27$。$\Gamma\ge G>0$，故阈值达到者本身增长；定理28.2的小正向旋转对保留全部等号，证明在准确 $H=32/27$ 时每个正记录误差都有无穷全时间距离。仅用叶来源会误将所需读界提高到2。

## 32. 原始来源对应、精确证据及未决边界

**约定 32.1（复用与数学证据的范围）。** 本节的实际对象仍是 Atomic2–3 的非空有序树、原 $\rho$ 及固定叶对的结构解释：本卷定义1.1–1.2直接给该对应；GenealogicalFiberTransport 的 `Source=FreeMagma Bool` 中 true／false 分别对应 $\alpha,\beta$。本卷定理3.1的运输只作解释换参，不执行换制备。Boundary7.2的固定单位标签通过同一有序节点归纳接入本卷定理4.3；Process44.2的组成／单位方向共同像提供真正的双接及根反序来源见证，不由线性张成或边缘计数推定联合实现。

实际恢复前提恰为本卷定理5.1及引理16.2／推论16.3：$x_3=\operatorname{sgn}(x_0\cdot(x_2\times x_1))(x_2\times x_1)$，非零尾有 $q_2\le q_0q_1$ 和归一化三重积绝对值至少 $c$；零标签尾按原描述子及正交运输归零。第25节的 $G=\varphi^2\gamma$、三线判据、紧截止覆盖和阈值达到／未达到与第18–19节逐项相同。正向旋转保持叉积及全部供应约束的证明复用定理17.2；旋转、根反序、正交化与缩放都只准备竞争来源，不成为未知源菜单。第30节只把推论20.3的候选纤维比较接到完整序列，通用最坏恢复方法不计作新的数学发现。

经典叉积基础仍引用 Darpö，*Vector product algebras*，[arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，Lemma2及证明；特征不为2、交替双线性积、非退化对称型、循环配对与范数恒等式在原定向正定实三维成立。正输入幂公式可对应 Peter J. Larcombe、Ovidiu D. Bagdasar，*On a Result of Bunder Involving Horadam Sequences: A Proof and Generalization*，*Fibonacci Quarterly* 51(2), 174–176，[原文](https://www.fq.math.ca/Papers1/51-2/LarcombeBagdasarHoradam.pdf)，式(2.2)–(2.3)：取其幂参数 $p=q=1$、$z_n=q_{n+1}$，只在两个初值正的分支使用；该文不承担本卷的实际组成、零／符号分支、平台或端口结论。

[Computational Behavior15](COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md)及 [RankOneInfiniteHorizonRisk](../../../D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.lean) 的严格稳定标量族说明没有共同谱隙时的已知外推机制；其来源为 $a^n$，不能代替第27节的共同实际树／制备桥。[FiniteHorizonPredictionPseudometric](../../../D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.lean) 的有限距离接口可取状态 $\mathcal T\times\mathcal P$、更新 $(t,p)\mapsto(\rho t,p)$、观察 $E_p(t)$、$T=2$，再限制比较的初态到 $\mathcal D$，其域无需更新不变；单独的有界无限距离结论要求整个输出载体的全局距离界，原 $\mathbb R^3$ 及增长行不满足。[NoUniformInfiniteFutureRadius](../../../D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius.lean) 使用无理圆周旋转与 floor 字母读数，来源和观察均不同。读取这些原文不构成本卷新增 Lean 编译证据。

RH_OFFLINE 的增订一·10中复 Fibonacci rapidity，及 Atomic416 的固定算术观察阈值／绝对商块渐近，都没有这里的叶制备和三向量取得假设，不用同名递推或对数尺度充当几何前提。Boundary43 的半径制备／读误差及 Process44 的外部 affine 仪器也保持其独立来源和权限合同。本卷第24–31节是上述准确接口下的普通数学综合推导（`repo-derived`），未主张全球原创性、文献穷尽或新的内核核验。

**约定 32.2（有限精确证据）。** 定理31.1的完整整数／有理数程序给2380个混合支撑组成、唯一最优组成 $(3,5)$ 及准确值 $32/27$；其八叶字面树在原制备下的四向量、根反序取负及前三读上界逐坐标准确成立。规范树 $T_0$ 至 $T_{15}$ 的字面组成和叶数核对 $N_l=F_{l+1}$；在 $\mathbb Q(\sqrt5)$ 中核对 $F_{n+1}-\varphi F_n=\psi^n$，$0\le n\le37$，其中13个 $n\equiv1\pmod3$ 的连续数组成为奇／奇；对应前五个双接字面树保持规定组成及非零第三轴。

另取1–4叶全部102棵有序标签树，在五个正交、非正交、依赖或零叶制备上，准确核对3060个三读恢复式及2040个字面运输实例；正交半单位制备还核对612个非负单项式实例。对 $L=1,H=1/2,d_0=1/16$，准确有理报告核对12834个实例及 $j=3,\ldots,12$ 的128340个未来比较，实际零尾、正确符号、错误符号和计算零符号分别为9250、1008、784、1792个；7322个报告需输入裁剪，28个报告非正交。使用的误差预算是各报告向量真实差的 $\ell^1$ 范数最大值，它是准确的 Euclidean 同时误差上界，不改变主问题的 $d_3$。系数准确为 $K_{\rm err}=17$、全时间充分系数19。非零初值 $x_0=(0,0,-1/5)$ 的实际零尾在 $L=2,H=1/2,d_0=1$ 下另核对125份报告和1250个相同有限时刻比较。

一个额外有理共同实现取 $T_6$、$L=2,H=1,d_0=5/4$，两正交叶长分别为 $(7/4,7/10)$ 与 $(7/4,699/1000)$。其行列式准确为 $2401/1600$、$23941449/16000000$，六个取得范数都不超过1，两个正 $q_1,q_2$ 都严格小于1，记录距离小于 $1/32$；原括号及运输给相同结果。它只核对一个 $d_0>1,H=1$ 的实际收缩对，第27节的无限族与上确界仍由其完整证明承担。

这些有限计算检验准确指标、有限证书覆盖后的枚举和具体报告分支；不是无限全树、任意制备或全时间结论的抽样证明。全称内容由结构归纳、源的联合约束、增长判据、非负单项式估计及第27–28节的实际成对构造承担。

**约定 32.3（仍需单独处理的边界）。** 定理24.2确定完整参数制度、准确零误差、尖锐线性阶、一个明确正区间上的精确单位平台、平台大误差端点及任意正误差的无穷障碍；尚未确定有界制度的完整有限误差曲线、最优线性系数或平台正误差的全部精确风险常数。精确参数阈值是数学存在性决定，其任意实数比较／整数截止的有限位有效决定仍需表示合同。

定义29.1是旧记录的理想运算求值器，不认证任意实数的符号／范数表示、全时间舍入精度、公共域承诺取得、准确制备／动作或物理传感价格。确定同时误差不供应统计复读收益。新的付费读、树码、校准、计数、复制、reset、逆、根交换或旋转菜单，以及不同目标度量或共同收缩裕量均须单独供应，不能作为本原任务已解决的替代物。准确完整未来、语法恢复、原制备反演、同制备上下文拼接与物理空间／时钟／记忆装置的恢复依然是不同关系。

## 追加锚（本行以下为增补区）
## 33. 原参数化树源的精确参考取得

本节及第 34–47 节研究同一实际树历史在不同被动坐标图下的参考取得。共同坐标记录与独立坐标扩展分别陈述；每种取得合同明确给出新增状态、同制备绑定、共观测或保留条件、回复宽度与资源义务。结论覆盖全部非空有序树及全部制备，包括零、平行、反平行、符号与计数分支。精确可识别性、有限取得、条件误差、全时间误差及物理和位资源是不同问题，普通数学证明不宣称 Lean 核验或物理认证。

## 34. 完整来源、记录与目标合同

**定义 34.1（实际来源与历史）。** 令 $\mathcal T$ 为以 $\alpha,\beta$ 为叶的自由有限非空有序二叉树集，构造子记作 $\langle s,t\rangle$。树大小不设上界，不加结合律、交换律、叶识别或空树。原替换为

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
$$

在固定定向欧氏空间 $\mathbb R^3$ 中，一次共同制备 $p=(a,b)$ 给出

$$
E_p(\alpha)=a,\qquad E_p(\beta)=b,\qquad
E_p(\langle s,t\rangle)=E_p(s)\times E_p(t),\qquad
x_j=E_p(\rho^jt).
$$

同一历史中的 $p$ 始终不变。比较世界允许 $p$ 遍历所有向量对，包括零、平行和反平行对；构造比较世界不授予观察者重新制备或主动旋转权限。

**定义 34.2（原取得接口）。** 原调用顺序为

$$
\operatorname{Read},\rho,\operatorname{Read},\rho,
\operatorname{Read},\operatorname{Stop},
$$

对应版本 $t,\rho t,\rho^2t$，原合同使用一个共同坐标图。读取不改变对象；$\rho$ 破坏性覆写唯一来源句柄。取得记录包含精确数值回复、声明的调用顺序，以及不编码来源内容的来源、制备、事件、版本和 Stop 身份。接口不含树代码、计数、叶或地址读出、复制、复位、逆操作、主动旋转、共读探针、运输轴、参考状态，也不含通过费用或耗时编码来源的旁路。描述结构成本的计数不是已观测计数；数值档案不是物理向量档案。

**定义 34.3（独立被动坐标扩展与目标）。** 单独声明世界

$$
w=(t,p,Q_0,Q_1,Q_2),\qquad Q_j\in G,
\qquad G=SO(3)\ \text{或}\ O(3),\qquad y_j=Q_jx_j,
$$

其中三个未知 $Q_j$ 独立且不受额外约束。被动 $Q_j$ 仅将物理向量写成坐标，不改变 $p$、物理叉积或实际树历史。严格未来、当前起未来及包含前缀的目标分别为

$$
F_+(w)=(Q_2x_j)_{j\ge3},\qquad
F_2(w)=(Q_2x_j)_{j\ge2},\qquad
F_0(w)=(Q_2x_j)_{j\ge0}.
$$

目标坐标图是实际最后取得的 $Q_2$，并非一个未指定的未来坐标图。$F_2$ 比 $F_+$ 仅多已取得的 $y_2$；$F_0$ 是另一个任务，不能把它的要求默加到严格未来任务中。

各条件扩展必须给出新增来源或仪器状态、制备和身份绑定、精确共观测或持续保留保证、时序及回复宽度。数学充分性以这些保证为前提；原 Read/$\rho$ 菜单不提供它们，给定校准也不等于已建立物理桥梁。

## 35. 原始全来源闭包、零分支与投影约束

**引理 35.1（解释映射与五符号闭包）。** 记

$$
\begin{aligned}
A&=\|a\|^2,& B&=\|b\|^2,& C&=a\cdot b,& \Delta&=AB-C^2,\\
K&=b\times a,& U&=K\times a=Ca-Ab,& N&=K\times b=Ba-Cb.
\end{aligned}
$$

解释映射 $F(a,b)=(b,K)$ 满足

$$
E_p(\rho^jt)=E_{F^j(p)}(t),\qquad
(A,B,C)\longmapsto(B,\Delta,0).
$$

每棵树有一个普适描述子，形如零或

$$
\varepsilon A^hB^kC^\ell\Delta^dZ,\qquad
h,k,\ell,d\in\mathbb N,\quad \varepsilon\in\{1,-1\},
\quad Z\in\{a,b,K,U,N\}.
$$

**证明。** 两个叶上的解释等式就是两条原替换；有序叉积节点保等式，故结构归纳证明一步，再迭代证明任意 $j$。欧氏叉积恒等式给出 $b\perp K$ 及 $\|K\|^2=\Delta$。完整乘法表为

$$
\begin{aligned}
a\times b&=-K,&a\times K&=-U,&a\times U&=AK,&a\times N&=CK,\\
b\times K&=-N,&b\times U&=CK,&b\times N&=BK,\\
K\times U&=-\Delta a,&K\times N&=-\Delta b,&U\times N&=-\Delta K.
\end{aligned}
$$

对角项为零，逆序项取负。各式由双线性及 $u\times(v\times u)=\|u\|^2v-(u\cdot v)u$ 得到；例如 $K\times(K\times a)=-\Delta a$，展开 $(Ca-Ab)\times(Ba-Cb)$ 得 $-\Delta K$。节点处乘子单项式相乘，再用此表归约，即得描述子的结构归纳。证明不作除法，因而包括 $C=0$ 和 $\Delta=0$；描述子不要求唯一。若 $\Delta=0$，则 $F(p)=(b,0)$、$F^2(p)=(0,0)$，所以即使早期向量非零，也有 $x_j=0$ 对所有 $j\ge2$。$F$ 是解释恒等式，不是可执行的制备操作。证毕。

**定理 35.2（完整尾序列与零边界）。** 取左手单位标架

$$
f_1=e_1,\quad f_2=e_2,\quad f_3=e_2\times e_1,
\qquad \chi(t)=E_{(e_1,e_2)}(t).
$$

$\chi(t)$ 为零或 $\sigma f_i$，其中 $\sigma\in\{1,-1\}$。若 $\Delta>0$，令

$$
r=\sqrt B,\qquad s=\sqrt\Delta,\qquad
 g_1=\frac b r,\quad g_2=\frac K s,\quad g_3=\frac N{rs}.
$$

它们是左手正交单位轴，循环指标满足 $g_{i+1}\times g_i=g_{i+2}$。设实际叶计数为 $\nu(t)=(m,n)$。在 $\chi(t)=\sigma f_i$ 分支中，

$$
\begin{aligned}
x_1&=\sigma r^ms^ng_i,\\
x_2&=\sigma r^ns^{m+n}g_{i+1},\\
q_{j+2}&=q_jq_{j+1},\qquad
x_{j+2}=\sigma(x_{j+1}\times x_j)\quad(j\ge1),
\qquad q_j=\|x_j\|>0.
\end{aligned}
$$

若 $\chi(t)=0$，所有 $x_j$（$j\ge1$）为零。结合 $\Delta=0$ 分支可得

$$
x_2=0\quad\Longleftrightarrow\quad F_2\text{ 全零}
\quad\Longleftrightarrow\quad F_+\text{ 全零}.
$$

**证明。** 五符号表在 $A=B=\Delta=1,C=0$ 时的符号为 $f_1,f_2,f_3,-f_2,f_1$，有限单位标签集对叉积闭合。因此归纳选定的描述子给出非零标签恰在非零描述子且 $\ell=0$ 时。标签为零不要求非正交制备下的 $x_0$ 为零，只要求正交尾部为零。

计数替换为 $M(m,n)=(n,m+n)$，且 $M^2=M+I$。在正交对 $F(p)=(rg_1,sg_2)$ 及后继 $(sg_2,rsg_3)$ 上，双叶齐次性由结构归纳得到前两式。单位标签的循环替换在叶上成立，并由节点叉积保持。$M^2=M+I$ 使后继幅值的每个指数等于前两个指数之和；左手标架乘法和 $\sigma^2=1$ 给出向量递推。轴每三步重复。零标签在任意正交制备上评价为零，故整个尾部为零；$\Delta=0$ 已由引理 35.1 处理。这些分支穷尽全部制备和树。证毕。

**引理 35.3（实际联合来源的投影约束）。** 在非零尾部令 $w=x_2\times x_1=q_1q_2g_{i+2}$，则

$$
\begin{aligned}
P&=\sigma x_0\cdot\frac w{\|w\|}
 =\left(\frac{AB}{\Delta}\right)^h
   \left(\frac sr\right)^m r^n
 =\left(\frac{AB}{\Delta}\right)^h\frac{q_2}{q_1}
 \ge\frac{q_2}{q_1},\\
P&\ge\sqrt{\frac\Delta{AB}}\,q_0,\\
|x_0\cdot(x_2\times x_1)|&\ge q_2^2,\qquad q_2\le q_0q_1.
\end{aligned}
$$

最后两条不等式在零分支也成立。

**证明。** 提取 $\sigma$ 后，初始非零描述子是正单项式乘 $a,b,K,-U,N$ 之一。它们对相应 $g_{i+2}$ 的正投影依次为 $s/r,r,s,s^2/r,rs$；双叶次数依次为 $(1,0),(0,1),(1,1),(2,1),(1,2)$。$A,B,\Delta$ 的次数为 $(2,0),(0,2),(2,2)$。乘法表在每个节点保持次数，描述子的总次数就是实际 $(m,n)$。将正投影按次数合并即得 $P$ 的等式，且 $AB\ge\Delta$。$a,-U$ 的投影与范数之比为 $\sqrt{\Delta/(AB)}$，$b,K,N$ 的该比为一；正标量相消给出第二条。第一条乘 $\|w\|=q_1q_2$ 得标量三重积下界，再由 $P\le q_0$ 得范数约束。零分支有 $w=q_2=0$，无需除法。这里约束的是实际联合来源，并非任意 $\mathbb R^9$ 三元组。证毕。

**定理 35.4（共同坐标解码及正交协变）。** 定义

$$
H(u,v,z)=\operatorname{sgn}\bigl(u\cdot(z\times v)\bigr)(z\times v),
\qquad \operatorname{sgn}(0)=0.
$$

全部实际来源满足 $x_3=H(x_0,x_1,x_2)$；对实际树 $\rho^kt$ 使用原来的 $p$，可用滚动三元组恢复全部未来。任意 $Q\in O(3)$ 满足

$$
H(Qu,Qv,Qz)=QH(u,v,z).
$$

**证明。** 非零分支由引理 35.3 的正投影确定符号；零分支的 $w,x_3$ 均为零。将同一定理用于实际树 $\rho^kt$ 给出逐步迭代。正交变换满足 $(Qu)\times(Qv)=\det(Q)Q(u\times v)$，标量三重积符号也乘 $\det(Q)$，两因子相消，零情形仍成立。故一个未知共同 $O(3)$ 坐标图足够；三个独立坐标报告不满足此应用条件。证毕。

引理 35.1–定理 35.4 复用本卷已发表的第 1.1–1.3、2.1–2.2、3.1、4.1–4.3、5.1 及 16.2–16.3 项。此处完整陈述普通证明，以明确后续取得结论的来源前提。

## 36. 被动与主动反射及全部计数分支

**命题 36.1（主动比较的计数符号）。** 对比较制备 $Rp=(Ra,Rb)$，保留原物理叉积，记 $\delta=\det R$、$L(t)=m+n$，则

$$
E_{Rp}(t)=\delta^{L(t)-1}RE_p(t).
$$

这不同于被动报告 $QE_p(t)$。在不正坐标图中，物理构造子的坐标表达为 $\det(Q)$ 乘坐标标准叉积，因而被动解释对每棵树正是 $QE_p(t)$。

**证明。** 叶上指数为零；节点上两子树指数及新增叉积因子之和为 $L(s)+L(t)-1$，归纳即得。原 $\rho$ 给出 $L_{j+2}=L_j+L_{j+1}$，且 $M^3=I$ 模二。$L_0,L_1,L_2$ 的奇偶性为 $m+n,m,n$，每三步重复。不正主动比较在四种计数奇偶支上的额外符号为

| $(m,n)\bmod2$ | 时间 $0,1,2$ 的符号 |
| --- | --- |
| $(0,0)$ | $(-,-,-)$ |
| $(1,0)$ | $(+,+,-)$ |
| $(0,1)$ | $(+,-,+)$ |
| $(1,1)$ | $(-,+,+)$ |

主动比较下连续三向量行列式的总指数为

$$
(L_j-1)+(L_{j+1}-1)+(L_{j+2}-1)+1=2L_{j+2}-2,
$$

故行列式不变；一个共同被动不正 $Q$ 则使其乘 $\det Q$。这些比较不授予主动操作。证毕。

**命题 36.2（非零标签的精确计数支持）。** 非零单位标签可达的计数恰为两个叶计数 $(1,0),(0,1)$，以及满足 $m,n\ge1$ 且不同时为偶数的计数。反转任一非零内部树的根，得到不同树、相同计数及全部 $x_j$ 的相反值。计数不确定 $\sigma$；叶的 $\sigma=1$。

**证明。** 在 $\mathbb F_2^2$ 中给 $f_1,f_2,f_3$ 分别赋非零次数 $(1,0),(0,1),(1,1)$。非零乘积加次数；同轴乘积为零，故零次数不能对应非零标签。多于一叶的纯标签树含同标签樱桃节点，评价为零。

反之，从 $k=\langle\beta,\alpha\rangle$ 开始，连续两次从左接上 $\alpha$ 或 $\beta$，用垂直单位轴的 $u\times(u\times v)=-v$，保持非零奇/奇标签并使相应计数增加二。因此全部正奇/奇计数可达；再接一枚 $\alpha$ 或 $\beta$，分别得到全部正偶/奇或奇/偶计数，所乘轴不同。这个构造覆盖无界大小。根反转在每次 $\rho$ 下仍是同一有序根分解的反转，叉积反交换给出每个时间的负值。混合支持计数也可能有零树，故支持不保证未知形状的尾部非零。证毕。

## 37. 精确径向像、独立坐标报告像与普适同制备符号对

**定理 37.1（精确报告像）。** 对 $G=SO(3)$ 或 $O(3)$，实际径向像与字面报告像分别恰为

$$
\{(q_0,q_1,q_2)\in[0,\infty)^3:q_2\le q_0q_1\},
\qquad
\mathcal R=\{(y_0,y_1,y_2):\|y_2\|\le\|y_0\|\|y_1\|\}.
$$

**证明。** 必要性是引理 35.3。若 $q_2=0$，取 $t=\alpha$、$a=q_0e_1,b=q_1e_1$，实际三元组为 $(a,b,0)$。这包括不等式允许的每种零／非零组合，特别是 $q_0=0$ 或 $q_1=0$。若 $q_2>0$，记 $h=q_0,k=q_1,l=q_2$，仍取叶 $\alpha$，令

$$
b=ke_1,\qquad a=\frac Ck e_1+\frac lk e_2,
\qquad C=\sqrt{h^2k^2-l^2}.
$$

于是 $(\|a\|,\|b\|,\|b\times a\|)=(h,k,l)$，也包括等号 $C=0$。每个非零物理向量可由一个正旋转送到任意同范数报告，零向量无需选择；三个独立正旋转属于 $SO(3)$，也属于 $O(3)$。上述各组三向量始终来自一个实际历史和同一个 $p$。证毕。

**定理 37.2（每个正可行三元组的同制备反根见证）。** 对所有 $h,k,l>0$ 且 $l\le hk$，存在同一个 $p$ 及计数同为 $(2,1)$ 的两棵实际树，前三个范数为 $(h,k,l)$，全部时间向量互为相反值，单位标签符号也相反。

**证明。** 置

$$
\begin{aligned}
r&=(k^3/l)^{1/5},&s&=(l^2/k)^{1/5},
&C&=\sqrt{h^2r^2/s^2-s^2},\\
b&=re_1,&a&=\frac Cr e_1+\frac sr e_2.
\end{aligned}
$$

因 $s^2/r=l/k\le h$，$C$ 为实数；$r,s>0$，且

$$
B=r^2,\quad\Delta=s^2,\quad A=h^2/s^2,
\quad K=se_3,\quad N=rse_2.
$$

取

$$
t_-=\langle\alpha,\langle\alpha,\beta\rangle\rangle,
\qquad t_+=\langle\langle\alpha,\beta\rangle,\alpha\rangle.
$$

它们有 $\chi(t_-)=-f_2,\chi(t_+)=f_2$。字面评价及五符号表给出

$$
\begin{aligned}
(x_0,x_1,x_2)(t_-,p)&=(U,-BK,-\Delta N),\\
(x_0,x_1,x_2)(t_+,p)&=-(U,-BK,-\Delta N),\\
\|U\|&=\sqrt{A\Delta}=h,
\qquad \|BK\|=r^2s=k,
\qquad \|\Delta N\|=rs^3=l.
\end{aligned}
$$

根反转在全部后来时间仍使值取负，故两符号在同一制备和相同计数上达到，包括 $h=l/k,C=0$ 边界。

三个叶是实现该全称同制备反根要求的最小叶数：叶没有内部根可反转；混合二叶树计数为 $(1,1)$，其 $q_1=rs,q_2=rs^2$ 强迫 $s=l/k,r=k^2/l$，初始 $\|K\|=s$，只能实现 $h=l/k$，纯二叶树尾部为零。五叶 $(3,2)$ 反根对同样可作冗余见证；它不替代这里对全部正三元组的三叶构造。定理 37.1 的叶实现及本定理的三叶负符号树均保留其实际来源意义。证毕。

## 38. 完整达到的未来纤维与取得的充要边界

**定理 38.1（完整未来纤维）。** 固定任意 $y\in\mathcal R$。若 $y_2=0$，$F_+$ 与 $F_2$ 的纤维均是唯一全零序列。若 $q_2=\|y_2\|>0$，记 $z=y_2,q_1=\|y_1\|$，全部实际相容未来恰由下列签名生成：

$$
\begin{gathered}
X_1=v,\qquad X_2=z,
\qquad X_{j+2}=\kappa(X_{j+1}\times X_j)\quad(j\ge1),\\
v\cdot z=0,\qquad\|v\|=q_1,\qquad\kappa\in\{1,-1\}.
\end{gathered}
$$

参数空间是完整达到的 $S^1\times\{1,-1\}$；在实际世界中 $v=Q_2x_1,\kappa=\det(Q_2)\sigma$。

**证明。** 定理 35.2 和正交叉积公式给出包含性。为达到任意 $(v,\kappa)$，在定理 37.2 的共同制备上选择 $\sigma=\kappa$ 的根。把 $(x_1,x_2)$ 送到 $(v,z)$ 的正旋转存在：将两组归一化有序垂直向量各补其标准定向法向，映射所得两个定向正交标架。另独立选正旋转 $Q_0,Q_1$ 把 $x_0,x_1$ 送到给定 $y_0,y_1$。这是一条实际历史，先在 $SO(3)$ 中实现，因而也在 $O(3)$ 中实现；没有将不同边缘世界相乘，也没有新增主动操作。零分支由定理 35.2 处理。证毕。

**定理 38.2（签名取得的充要条件）。** 任意在同一世界上诚实取得的附加记录 $Z$，能由 $(y,Z)$ 恢复全部严格未来，当且仅当非零数据纤维上的 $v$ 和 $\kappa$ 都恒定。零纤维无需这两个量。

**证明。** 递推给出

$$
X_3=\kappa(z\times v),\qquad X_4=q_2^2v,
\qquad
\kappa=\frac{X_3\cdot(z\times v)}{q_1^2q_2^2}.
$$

第二式用 $(z\times v)\times z=\|z\|^2v$。由严格未来可恢复 $v$ 及 $\kappa$，故它们在可解码的数据纤维上必须恒定；反之，取得二者后显示的递推充分。不同签名给出不同未来。只校准 $X_3$ 时，$(v,\kappa)$ 与 $(-v,-\kappa)$ 有相同下一向量及相反 $X_4$；只取符号仍余整个圆，只取方向仍余两个下一向量。证毕。

**命题 38.3（原独立报告的精确不可识别性及条件纤维）。** 三次字面报告能恢复 $F_+$ 当且仅当 $y_2=0$。每个非零实际 $(t,p)$ 即使公开完整 $t,p$，也仍存在同历史圆形障碍；后来任意多次独立未知坐标报告不绑定历史 $Q_2$。

**证明。** 非零完整纤维由定理 38.1 达到。更强地，只将 $Q_2$ 改为 $Q_2P$，其中 $P$ 是固定 $x_2$ 的非恒等正旋转；保留 $Q_0,Q_1,t,p$ 和完整日程。$y_2$ 不变，非零且垂直于 $x_2$ 的 $x_3$ 被移动。后来坐标图可在两世界中全部保持相同，甚至有无穷多次后来报告，所取得报告仍相同而旧 $Q_2$ 下目标不同。若后来通道复用或运输 $Q_2$，那是额外参考合同。

固定非零 $t,p$ 时，$SO(3)$ 中 $\sigma$ 固定，条件纤维恰为一个圆；$O(3)$ 中两个 $\kappa$ 仍均可达，因为有序二轴注册有正和不正补全，关于 $\operatorname{span}(x_1,x_2)$ 的反射固定该二轴而翻转 $x_3$。固定 $p$、树未知时，在固定范数三元组的 $SO(3)$ 纤维中，只要有相容非零内部树，其根反转就实现两符号；若相容树全为叶，则仅有正符号。$O(3)$ 中两种情况都含两 $\kappa$。除叶例外，不能从计数推断树符号。证毕。

## 39. 最大可恢复商、前缀及公开制备的细化

**定理 39.1（尾轨道与最大可识别不变量商）。** 非零未来的范数完全由 $q_1,q_2$ 决定：

$$
q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\quad(j\ge2),
\qquad F_0=0,\ F_1=1,\ F_{n+2}=F_n+F_{n+1}.
$$

$F_2$ 或 $F_+$ 的共同 $O(3)$ 轨道分类为零类或 $(q_1,q_2)$；完整共同 $SO(3)$ 轨道分类还需 $\kappa$。从字面独立报告可识别的最大不变量商，即使允许 $SO(3)$ 不变函数，也只保留该 $O(3)$ 分类。

**证明。** 幅值公式由乘法递推归纳。两两 Gram 项在 $j\equiv k\pmod3$ 时为 $q_jq_k$，否则为零；按时间排序的连续三轴行列式为

$$
\det[X_j,X_{j+1},X_{j+2}]=-\kappa q_jq_{j+1}q_{j+2}.
$$

将一个张成空间的有序三轴标架正交映到另一个，便映射全部尾坐标，故 Gram 决定共同 $O(3)$ 轨道；该映射为正旋转恰在连续行列式相同时。每个非零字面纤维都有两 $\kappa$，可识别函数必须合并这两符号。这不宣称恢复了完整 $SO(3)$ 轨道。证毕。

**定理 39.2（严格未来的最大任意可识别商）。** 最大任意可识别目标商是

$$
J_+=\begin{cases}
\text{零类},&z=0,\\
(z,q_1),&z\ne0.
\end{cases}
$$

严格未来和当前起未来使用同一分类。

**证明。** $y_2$ 与 $\|y_1\|$ 直接给出该商。对任意目标的固定 $q_1,q_2$ 和任意 $h\ge q_2/q_1$，定理 37.2 与定理 38.1 在初始范数 $h$ 上实现该目标。因此所有同 $z,q_1$ 的目标能共处一个字面记录，任何由报告可恢复的未来函数在此类上恒定，必经 $J_+$ 分解。$q_0$ 不能保留，因为它不是 $F_+$ 的函数。反之，非零严格目标自身可区分不同 $J_+$：

$$
q_2=q_4/q_3,\qquad q_1=q_3^2/q_4,
\qquad z=q_2X_5/\|X_5\|.
$$

零目标统一合并。证毕。

**定理 39.3（包含前缀的可识别性与最大商）。** 字面报告恢复 $F_0$ 当且仅当 $q_0=q_1=q_2=0$。最大可识别不变量前缀商为 $(q_0,q_1,q_2)$，最大任意可识别前缀商为 $(q_0,q_1,q_2,X_2)$。

**证明。** 非零尾部已不可识别；若 $q_2=0$，其零报告对 $Q_2$ 无约束，$Q_2$ 可移动非零 $x_0$ 或 $x_1$，不改变 $y_0,y_1,y_2$。若三者均零，定理 35.2 给出整个零历史。

显示的商同时是 $F_0$ 与字面记录的函数。任何两个商相同的实际 $F_0$ 目标可共享 $y_2=X_2$，并独立把 $x_0,x_1$ 旋转到同范数的共同 $y_0,y_1$。所以可恢复函数在该目标类上恒定。对不变量函数，共同改变 $X_2$ 的方向不能有影响，故它经三个范数分解。这是可识别商，不是完整前缀 $O(3)$ 轨道分类：初始 Gram 夹角和定向前缀数据可在同一记录下不同。前缀与未来的零类合并规则不同。证毕。

**命题 39.4（另供精确公共制备时的计数唯一性与例外）。** 若另供精确 $p$ 且 $\Delta>0$，在 $(r,s)\ne(1,1)$ 时，非零 $q_1,q_2$ 唯一确定实际整数计数。叶计数给 $\sigma=1$，内部非零树仍有同制备反根双符号。在 $r=s=1$ 时，叶范数纤维也含双符号。

**证明。** 两计数的差 $d_m,d_n$ 若给同 $q_1,q_2$，则

$$
d_m\log r+d_n\log s=0,\qquad
d_n\log r+(d_m+d_n)\log s=0.
$$

非零整数对的行列式 $d_m^2+d_md_n-d_n^2$ 非零：若 $d_n\ne0$ 而行列式为零，有理数 $d_m/d_n$ 必为无理根 $(-1\pm\sqrt5)/2$；$d_n=0$ 时立即成立。因此非零计数差强迫 $\log r=\log s=0$。非单位 $(r,s)$ 上计数唯一。叶符号为正；其余实际相容非零内部树及反根在同一公共 $p$ 上给双符号，并保持 $q_0$。

在 $r=s=1$ 时，$\alpha$ 的范数三元组 $(\sqrt A,1,1)$ 也由定理 37.2 的 $t_-,t_+$ 在同一 $p$ 给出，因为 $\|U\|=\sqrt{A\Delta}=\sqrt A$。$\beta$ 的 $(1,1,1)$ 也由 $k=\langle\beta,\alpha\rangle$ 及其反根给出，因为 $\|K\|=\|b\|=1$。其它相容内部树自有反根。因此每个非零单位 $(r,s)$ 范数纤维，包括叶纤维，都含双符号。退化 $p$ 的未来则全零。计数唯一性核心复用本卷定理 6.4；它是精确集合层面的结果，不供应有界搜索、有限精度整数识别或计数／校准端口。证毕。

## 40. 扩展全时间距离下的精确固定记录极小极大半径

**定理 40.1（下一向量的两种输出半径）。** 固定非零字面记录，$X_3$ 遍历 $z^\perp$ 中半径 $q_3=q_1q_2$ 的整圆。允许估计器输出任意 $\mathbb R^3$ 向量时，精确最坏极小极大半径为 $q_3$；要求输出相容下一向量时，半径为 $2q_3$。

**证明。** 零中心达到 $q_3$；任意中心面对两个已达到的相反向量，由三角不等式至少有一个误差为 $q_3$。圆上任意相容输出的对径点相容且距离为 $2q_3$，而圆直径也为此值。证毕。

**定理 40.2（完整序列的精确扩展半径）。** 对严格序列使用可取无穷的距离

$$
d_\infty(U,X)=\sup_{j\ge3}\|U_j-X_j\|.
$$

已知锚定余类为 $j\equiv2\pmod3$，此时 $X_j=(q_j/q_2)z$；另外两个余类是半径 $q_j$ 的圆。置

$$
R_\infty=\sup\{q_j:j\ge3,\ j\not\equiv2\pmod3\}\in[0,\infty].
$$

任意序列输出的精确极小极大半径为 $R_\infty$；要求输出一条实际相容完整未来时为 $2R_\infty$。零未来分支的两个半径均为零，包含当前 $X_2$ 不改变它们。

**证明。** 在锚定余类输出精确值，其余输出零，风险为 $R_\infty$。每个未知坐标都有已达到的对径点，任意输出在该坐标的风险至少为 $q_j$，取上确界得到下界，包含无穷及上确界未达到的情形。

相容输出任选一个签名，任意其它目标在未知坐标的距离不超过 $2q_j$，在锚定坐标相同。保持 $\kappa$、改 $v$ 为 $-v$ 是已达到的另一签名，它恰使两个未知余类方向取反而保留锚，距离为 $2R_\infty$。故上、下界相同。证毕。

这些是没有额外校准的固定精确独立坐标记录风险，不是含噪极小极大定理或随机噪声律。对径见证来自定理 37.2 的实际历史，也可用固定历史的 $Q_2$ 半转达到。公式只用既有 Fibonacci 递推，不借用共同坐标下的全时间制度分类；有限视界以相应有限坐标最大值代替上确界。

## 41. 强最终时刻规范库：无需对齐旧坐标的未来取得

**定义 41.1（最终时刻的实际 $b,K,N$ 库）。** 新增持久同制备原生库，其有标签句柄为

$$
c_1=\beta\ (b),\qquad
c_2=\langle\beta,\alpha\rangle\ (K),\qquad
c_3=\langle\langle\beta,\alpha\rangle,\beta\rangle\ (N).
$$

供应者须从实际目标制备另行构造或供应这些句柄，认证共同制备及句柄／版本身份，使它们免受目标 $\rho$ 的覆写，并将物理值保持到最终观测。这是新增辅助状态与供应，不是目标复制、叶访问或原 Read 返回的矩阵。标签与共观测属于付费合同。目标仍有三次时间顺序报告、两次更新；仅在时刻二，以原子或明确规定的最终回复，在同一实际 $Q_2$ 中共观测当前目标及所需参考句柄。无需早期参考或 $Q_0,Q_1$ 对齐。

在 $SO(3)$ 中，额外取得 $u=Q_2b,w=Q_2K$ 两个向量；含原九坐标共十五实坐标。在 $O(3)$ 中，再取得 $n=Q_2N$，共三个额外向量、十八实坐标；也可用两向量加另行取得且认证的最终定向位 $\det(Q_2)$，为十五实坐标加一位。该位的认证、绝对定向参考、状态、初始化、时刻绑定和物理价格都是额外义务，不能由两个向量猜出。

**定理 41.2（全来源的最终库充分性）。** 定义 41.1 的 $SO(3)$ 两探针或 $O(3)$ 三探针／定向位合同恢复全部严格未来，无须对齐旧坐标或取得过去向量。

**证明。** 若 $z=y_2=0$，直接输出零未来，不作归一化、求逆、轴或符号决定。此时库可退化，统一回复合同仍良定义。若 $z\ne0$，定理 35.2 给 $\Delta>0,r,s>0$。探针范数给 $r=\|u\|,s=\|w\|$。在 $SO(3)$ 中计算

$$
h_1=u/r,\qquad h_2=w/s,\qquad h_3=(w\times u)/(rs).
$$

这恰是 $Q_2g_1,Q_2g_2,Q_2g_3$。在 $O(3)$ 三探针合同中使用 $h_3=n/(rs)$；因

$$
\det[b,K,N]=-B\Delta<0,\qquad
\delta=\det Q_2=-\operatorname{sgn}\det[u,w,n],
$$

可取得真实被动图定向。定向位替代中令 $h_3=\delta(w\times u)/(rs)$。六个实际带符号轴中恰有一个 $\ell\in\{1,2,3\}$ 和 $\sigma\in\{1,-1\}$ 满足 $z=\sigma q_2h_\ell$；正交单位标架及 $q_2>0$ 保证唯一。定理 35.2 的 $x_2$ 位于带符号轴 $i+1$，故取循环指标

$$
v=\sigma q_1h_{\ell-1},\qquad
\kappa=\delta\sigma\quad(\delta=1\text{ 在 }SO(3)\text{ 中}).
$$

所得正是 $Q_2x_1$ 和正确图内递推符号。定理 38.1–38.2 于是恢复严格未来，包括其第一项。只需已取得的旧范数 $q_1$；没有共观测过去向量、揭示树或计数、执行制备映射 $F$ 或对齐 $Q_0,Q_1$。全部零、符号及大小分支均已处理。该库对未来目标充分，不自动恢复 $a,b$ 或前缀。证毕。

**定理 41.3（特定有标签库子集的尖锐必要性）。** 仅在定义 41.1 的特定库子集、且没有其它端口的菜单中，全来源完整未来在 $SO(3)$ 中至少需两个参考回复，在 $O(3)$ 中无定向数据时至少需三个。

**证明。** 在 $SO(3)$ 中任意一个参考都失败，即使有 $z$。取单位 $p=(e_1,e_2)$、$k=\langle\beta,\alpha\rangle$，使 $x_1$ 平行所选库轴的实际内部树可取

| 所选参考 | 实际树 | 单位标签 |
| --- | --- | --- |
| $b$ | $\langle k,\langle k,\alpha\rangle\rangle$（五叶） | $-f_1$ |
| $K$ | $\langle k,\alpha\rangle$（三叶） | $-f_2$ |
| $N$ | $k$（二叶） | $f_3$ |

第一尾方向由这些标签直接给出，全部幅值为一。第一世界的 $Q_2$ 取恒等；第二世界反根，并将 $Q_2$ 取绕所选物理库轴的正半转。参考不变，负 $x_2,x_3$ 被转回而匹配，但平行于固定轴的 $x_4$ 仍相反。独立正 $Q_0,Q_1$ 匹配前两报告。因此一个参考甚至能匹配下一向量，仍不足以恢复完整未来。定理 41.2 给两参考充分性。

在 $O(3)$ 中，任选两个库向量，关于其物理张成平面作反射。保持单位 $p$ 和同一棵树，并使 $x_2$ 位于已含轴：$\alpha$ 有 $x_2=K$，$\beta$ 有 $x_2=N$，$k$ 有 $x_2=b$，每个二探针对至少能选一个。被动末图反射固定两参考和 $z$，而未来循环访问遗漏正交轴，彼处向量不同。$t,p,Q_0,Q_1$ 均不变。三探针充分性见定理 41.2。这些实际来源反例证明限定菜单的二／三回复界；它们不是维数启发，也不是任意编码、标量或物理测量端口的下界。证毕。

## 42. 保留实际末图：恰需两次后续读取与更新

**定义 42.1（实际 $Q_2$ 的前瞻保留）。** 新增仪器状态须在第三报告的坐标图丢失前、且在 Stop 前，前瞻或原子绑定该报告实际使用的 $Q_2$。它保证指定的随后目标 Read 使用这个保留图，$\rho$ 仅改变目标。确认、坐标图／来源／事件身份、参考保留及成本均需记录。该状态不返回免费轴或矩阵；未保留的历史图消失后不能追溯安装。

**定理 42.2（两次额外 Read 与两次额外 $\rho$ 的充分性）。** 在定义 42.1 菜单中，原第三报告若有 $z=0$，可在 $\rho^2t$ Stop 并输出零未来。非零时，保留 $Q_2$，执行一次 $\rho,\operatorname{Read}$ 取得时间三，再执行一次取得时间四，最后在 $\rho^4t$ Stop，即可恢复严格未来。

**证明。** $X_2,X_3,X_4$ 位于同一图。可在实际移位树上使用定理 35.4 的 $H$ 并迭代；也可计算

$$
v=X_4/q_2^2,\qquad
\kappa=\operatorname{sgn}\bigl(X_3\cdot(z\times v)\bigr).
$$

该标量的绝对值为 $q_1^2q_2^2>0$，故给出精确符号，定理 38.2 解码从时间三起的未来，包括已读取的 $X_3,X_4$。没有来源逆操作。非零日程共五次对象向量 Read、十五实坐标、四次 $\rho$，另计新增参考状态；未对齐前缀不随之恢复。证毕。

**定理 42.3（每个非零纤维的限定菜单下界）。** 定义 42.1 菜单中，每个非零字面纤维至少需两次额外向量 Read，且至少需两次额外 $\rho$ 更新，才能恢复完整严格未来。允许唯一额外 Read 在策略选择的任意晚但有限时刻，仍不能突破读取下界。

**证明。** 令 $u=z/q_2,d=X_3/q_3$。纤维可写为

$$
X_j=\begin{cases}
q_ju,&j\equiv2\pmod3,\\
q_jd,&j\equiv0\pmod3,\\
q_j\kappa(d\times u),&j\equiv1\pmod3.
\end{cases}
$$

所有垂直于 $u$ 的单位 $d$ 及两 $\kappa$ 均由定理 37.2 的同制备构造和正注册达到。唯一额外读取前，确定历史策略只见同一字面记录，故在比较世界中选择相同时间 $J$。若 $J\equiv2$，取同 $\kappa$、不同 $d$；若 $J\equiv0$，取同 $d$、相反 $\kappa$；若 $J\equiv1$，取 $(d,\kappa)$ 和 $(-d,-\kappa)$。唯一回复各自相同，完整目标却在另一余类不同。无读策略也失败，所有动作、状态及 Stop 可共用不编码来源的身份元数据；同版本重复读不增信息。

若最多一次额外更新，无论多少读取，只能取得 $X_2,X_3$，上述 $J\equiv0$ 对匹配二者而 $X_4$ 相反。定理 42.2 恰用两更新及两新值达到。下界仅属该菜单，不是来源执行、运行时或任意端口的最优性结论。证毕。

**推论 42.4（限定输入独立随机化仍不能单读全解）。** 输入独立随机策略若至多一次额外向量读且有限停止，并且策略／随机种子事件及成功事件可测，则不可能对每个世界几乎必然精确成功。

**证明。** 在固定字面记录上，按唯一读取的三种余类或无读取分割种子空间，四类之一有正概率。独立于实际种子，固定定理 42.3 给该类的已达到比较对。类中每个种子的两条完整记录相同而目标不同，算法不能同时正确；两个固定世界的错误概率之和至少为该类概率。因此不能逐世界几乎必然成功。结论不涉及输入相关种子、不可测策略、无限停止、期望读取预算或近似风险。证毕。

有限取得期间保留 $Q_2$，足以产生数学坐标及对全部后来指标的精确有限求值器。若要与后来物理设备比较，须另给后来时刻的物理参考保留合同，求值器本身不提供它。

## 43. 三时刻与过去校准：不同规范库及精确退化

**定义 43.1（三时刻参考合同）。** 参考库在第一次目标报告前安装，在各实际 $Q_j$ 中与目标共观测。共同制备真实性、标签、免受目标 $\rho$ 影响、持续保持及同时刻绑定均为付费前提。目标仍在 $\rho^2t$ Stop，但返回比最终时刻未来库更多的数据。以下严格区分所供物理向量：规范库供 $b,K$（$SO(3)$）或 $b,K,N$（$O(3)$）；制备库供 $a,b$（$SO(3)$）或 $a,b,K$（$O(3)$）。不能在两菜单间默换探针。

**定理 43.2（三时刻 $b,K,N$ 规范库的精确过去范围）。** $SO(3)$ 的 $b,K$ 库增加六向量回复，共二十七实坐标；$O(3)$ 的 $b,K,N$ 库增加九回复，共三十六实坐标。它们对全部来源恢复未来；恢复 $F_0$ 的范围为 $\Delta>0$，或 $\Delta=0,b\ne0$，或已经全零的前缀。在 $b=0,a\ne0$ 分支，除 $t=\alpha$ 外全部树的完整历史为零，故成功；$t=\alpha$ 则失败。

**证明。** 当 $\Delta>0$，$O(3)$ 库的真列矩阵

$$
A_j=[Q_jb,Q_jK,Q_jN]
$$

可逆，并有 $A_2A_j^{-1}=Q_2Q_j^{-1}$。$SO(3)$ 两探针构造的正交三轴也有同一相对运输性质。对齐 $y_0,y_1$ 并加 $y_2$ 后，用定理 35.4 恢复未来，已对齐档案给出 $F_0$。即使 $\chi(t)=0$ 或 $x_2=0$，此结论仍成立，因为参考秩属于 $p$，不属于特定目标尾部。两探针加另付费的相对奇偶标志也能恢复 $O(3)$ 运输：过去校准需到时刻二的两条链路各一标志，或各时刻独立认证 $\det(Q_j)$ 的三位；这不同于仅最终时刻的一位变体。

当 $\Delta=0,b\ne0$，$a$ 为 $b$ 的倍数，所有内部叉积消失，全部来源值在 $\operatorname{span}b$ 上。$b_j=Q_jb$ 非零，对每个过去报告的精确对齐值为

$$
\frac{y_j\cdot b_j}{\|b_j\|^2}\,b_2.
$$

它包括 $a=0$、平行及反平行叶，恢复所需向量而不宣称恢复全环境矩阵。若 $a=b=0$，所有值为零。

最后给出完整边界反例：取 $b=0,a\ne0,t=\alpha$。字面替换给

$$
x_0=a\ne0,\qquad x_1=x_2=0,\qquad
b=K=N=0.
$$

全部三个时刻的规范参考都为零。固定 $Q_0,Q_1$，取两个移动 $a$ 的不同正 $Q_2$；每个扩展回复、标签、制备／版本记录及日程均相同，$F_0$ 却已在 $Q_2a$ 处不同。因而该菜单不能对所有制备恢复过去。本卷命题 6.5 和命题 11.3 给同一实际零叶边界：$b=0,a\ne0$ 时，其它树均全零，只有 $\alpha$ 留非零初值。全部来源的未来充分性仍由定理 41.2 保持，不能由零未来推断取得了非零过去的定向；也未增加 $a$ 探针。证毕。

**定理 43.3（三时刻 $a,b,K$ 制备库的全制备前缀恢复）。** 定义 43.1 的另一个菜单，供 $a,b$（$SO(3)$）或 $a,b,K$（$O(3)$），对全部制备及全部树恢复 $F_0$，含零、平行、反平行及 $b=0,a\ne0$。回复数量仍为六／九额外向量和二十七／三十六实坐标，但供应状态不同。

**证明。** 若 $\Delta>0$，$a,b$ 独立。将 $a$ 归一化，去掉 $b$ 沿 $a$ 的分量并归一化，再用定向叉积补全，所得 $SO(3)$ 三轴矩阵满足 $D_j=Q_jD_{\rm native}$，故

$$
D_2D_j^{\mathsf T}=Q_2Q_j^{-1}.
$$

在 $O(3)$ 中取 $P_j=[Q_ja,Q_jb,Q_jK]$，由 $\det[a,b,K]=-\Delta\ne0$ 得 $P_2P_j^{-1}$ 为精确运输。只用两叶探针加独立定向位时，用 $\det(Q_j)$ 乘由前两轴导出的叉积，取得物理法向；三位变体为二十七实坐标加三位，相对奇偶标志则提供对应两链路变体。

若 $\Delta=0$，从 $a,b$ 中按精确探针范数选择一个有标签的非零物理参考 $r$。它在每个时刻的 $r_j=Q_jr$ 非零，全部来源值在 $\operatorname{span}r$ 上。以

$$
\frac{y_j\cdot r_j}{\|r_j\|^2}\,r_2
$$

对齐；两叶全零时直接用零。这包括 $b=0,a\ne0$ 时选 $a$，因而证明全制备 $F_0$，无逆来源操作或零处分母。恢复的是实际直线上的值，不是唯一三维图运输。

两个 $a,b$ 探针独自仍非完整 $O(3)$ 解：单位 $p$、$t=\beta$ 有 $x_2=N=e_1$ 位于叶平面，关于该平面的最终被动反射固定两叶和 $z$，却翻转后来 $K$ 轴向量。这是同来源实际反例，同时适用于未来和前缀。因此本菜单需要第三物理法向或付费定向数据。证毕。

叶制备库的物化宽度可不同于规范库：两枚一叶状态与一、二、三叶状态不是同一供应。二者均非免费公共 $p$ 或物理可供应性宣告。最终时刻规范库、三时刻规范库、全制备叶库及完整过去对齐保留各自目标与资源条件；未来任务不要求更宽的过去消费者。

## 44. 前瞻物理输出记忆与共读替代合同

**定义 44.1（两枚实际物理输出槽）。** 在前两次原读取时，把实际物理 $x_0,x_1$ 捕获到两个新增且有身份的物理向量槽。认证其目标／来源／制备／版本关联，在目标经历 $\rho$ 时保留物理值。这是新物理输出记忆状态，旧数值记录 $y_0,y_1$ 不提供它们。最终时刻在实际 $Q_2$ 中同时共观测两槽与当前目标，返回 $Q_2x_0,Q_2x_1,z$；必须在该图丢失前绑定同一个瞬时 $Q_2$，即使旧数值 Read 使用不同图。两次捕获、两物理槽、保存、标签、身份认证及最终共读都收费；目标仍两次更新后在 $\rho^2t$ Stop。

**定理 44.2（完整共读及收缩回复）。** 完整合同对 $SO(3)$ 或 $O(3)$ 的全部制备恢复未来和数值前缀。额外两向量回复，即最终多六实坐标，总发出十五实坐标。只为未来可改供 $v=Q_2x_1$ 加符号位

$$
\kappa=\operatorname{sgn}\bigl((Q_2x_0)\cdot(z\times v)\bigr)
\quad(z\ne0),
$$

在 $z=0$ 时供任意固定二值位。

**证明。** 完整回复是共同图中的实际来源三元组，定理 35.4 的 $H$ 与迭代恢复 $F_+$，共观测槽直接给数值前缀。理想槽状态有六个实坐标自由度，这个描述不推出设备或位成本。

非零尾部的显示符号恰为 $\det(Q_2)\sigma$，定理 38.2 解码未来；零尾部不需符号或归一化。收缩回复额外宽度为三实坐标加一位，但传感器仍须拥有两个实际捕获输出、同时 $Q_2$ 绑定及身份保证，因此不证明更便宜的捕获／存储硬件。它不返回 $Q_2x_0$，自身不能解决前缀恢复。另供直接目标方向加符号位传感口，须再明确声明该测量合同，原 Read/$\rho$ 不推出它。

未保留的 $x_0,x_1$ 不能由数值记录在本合同下追溯捕获；物理槽替代既不是目标复制／复位，也不是未计价的档案运输矩阵。证毕。

## 45. 条件误差、有限视界与全时间障碍

**命题 45.1（有秩裕量的条件运输误差）。** 设真共同参考列矩阵 $P_j$ 的最小奇异值至少为 $\mu>0$，真运输

$$
T=P_2P_j^{-1}=Q_2Q_j^{-1}
$$

为正交矩阵。令 $\widehat P_j=P_j+E_j$，两时刻算子误差均不超过 $e<\mu$，且 $\widehat T=\widehat P_2\widehat P_j^{-1}$，则

$$
\widehat T-T=(E_2-TE_j)(P_j+E_j)^{-1},
\qquad D:=\|\widehat T-T\|_{\rm op}\le\frac{2e}{\mu-e}.
$$

若真目标范数不超过 $H$、报告误差不超过 $\delta$，则对齐误差不超过 $DH+(1+D)\delta$。三列各自直接测量误差不超过 $\eta$ 时，可取 $e\le\sqrt3\eta$。

**证明。** 将差式右乘 $P_j+E_j$ 得分子恒等式；$\|(P_j+E_j)u\|\ge(\mu-e)\|u\|$ 给逆范数界，且 $\|T\|_{\rm op}=1$。将对齐差拆成 $(\widehat T-T)x$ 与 $\widehat T$ 乘报告误差，得到后一个界。列误差用 Frobenius 范数控制算子范数。结论仅是有秩条件的有限记录结果，并不对全部制备统一成立。证毕。

**命题 45.2（导出叉积列的误差与局部轴识别）。** 在 $SO(3)$ 中，若真叶范数不超过 $L$、个别测量误差不超过 $\eta$，由测得叶形成原始列 $[a,b,a\times b]$ 时，第三列误差不超过 $2L\eta+\eta^2$，可取

$$
e\le\sqrt{2\eta^2+(2L\eta+\eta^2)^2}.
$$

对原始规范列 $[b,K,K\times b]$，用 $\|b\|,\|K\|$ 的各自上界之和替代 $2L$。最终库带符号轴分类在每个固定非零真世界局部稳定，但全来源上不提供统一裕量。

**证明。** 展开 $(a+e_a)\times(b+e_b)-a\times b$，三个误差项的界分别为 $L\eta,L\eta,\eta^2$，再合成三列的 Frobenius 界。规范列同理。在 $O(3)$ 中，这种导出第三列不被默认为共观测物理法向；须有 $SO(3)$ 前提或另付费定向信息。归一化矩阵须另算其诱导误差，不能把原始列误差直接当成归一化误差。定向位错误不属显示的矩阵误差合同，除非另给界。

固定非零世界的六代表 $\pm q_2h_\ell$ 两两距离至少 $\sqrt2q_2$，同轴异号距离为 $2q_2$。若目标扰动不超过 $\epsilon$，以相同精确幅值 $q_2$ 构造的扰动轴代表误差不超过 $q_2\eta_{\rm axis}$，且

$$
\epsilon+q_2\eta_{\rm axis}<q_2/\sqrt2,
$$

则最近轴分类不变：真代表距离至多左侧，错误代表距离至少 $\sqrt2q_2$ 减左侧。幅值也带误差时，在此差异界另加 $|\widehat q_2-q_2|(1+\eta_{\rm axis})$，因为扰动轴范数不超过 $1+\eta_{\rm axis}$；若扰动轴另归一化为单位，幅值项仅为 $|\widehat q_2-q_2|$。$r,s>0$ 处归一化连续，$O(3)$ 库真行列式绝对值 $B\Delta>0$，故足够小的局部探针误差也保持定向。

这些裕量为正但依世界而定；全来源的 $r,s,q_2$ 可趋零，无统一秩或符号裕量。精确 $z=0$ 测试不因此成为含噪零／符号 oracle。噪声、标签、参考／制备身份、定向及共观测前提均需计价。证毕。

**命题 45.3（复用两种不同来源域的含噪下一向量界）。** 保持原制备与 $\rho$ 准确，先在共同坐标下取得实际三元组，三个同时向量读误差均不超过 $\zeta$。在本卷定义 16.1 的主域 $\mathcal D_{L,H,d_0}$，即

$$
\|a\|,\|b\|\le L,\quad \Delta\ge d_0,
\quad 0<d_0<L^4,\quad q_0,q_1,q_2\le H,
\qquad c=\sqrt{d_0}/L^2,
$$

本卷定理 20.2 给

$$
\|H(\text{含噪三元组})-x_3\|
\le\frac4c(H^2+2H+\zeta)\zeta.
$$

在不同的、更宽的定义 21.1 域 $\mathcal D_H$，允许全部制备且只要求 $q_0,q_1,q_2\le H$，本卷推论 21.4 给

$$
\begin{aligned}
\text{误差}&\le b_\zeta+2H\sqrt{p_\zeta},\\
b_\zeta&=(2H+\zeta)\zeta,\qquad
p_\zeta=H^2\zeta+(H+\zeta)b_\zeta.
\end{aligned}
$$

**证明。** 叉积误差至多 $b_\zeta$。主域上引理 35.3 的真投影至少 $c\|x_0\|$：若 $\|x_0\|<2\zeta$，实际 $q_2\le q_0q_1$ 控制目标幅度；否则将标量误差界除以 $\|x_0\|$，并用 $\|x_0\|+\zeta\le3\|x_0\|/2$。错误或计算为零的符号分支给

$$
c\|x_0\|\|x_2\times x_1\|
\le H^2\|x_0\|\zeta+\tfrac32\|x_0\|b_\zeta,
$$

合成即得主域系数；正确符号、真零及计算零分支包含在内，无须精确含噪符号 oracle。

较宽域没有统一 $c$。符号错误或为零时，普适三重积下界给 $q_2^2\le p_\zeta$，故 $\|x_2\times x_1\|\le H\sqrt{p_\zeta}$；同符号或零目标仅需叉积误差界。若三元组经含噪校准对齐，先将命题 45.1 的对齐界合成为同时 $\zeta$，再应用满足实际域前提的那一定理。这些复用结论不成为新校准噪声最优性。证毕。

**命题 45.4（实际平方根尖锐对的完整见证）。** 较宽 $\mathcal D_H$ 上，下一向量模量与固定三读完整误差球风险具有平方根最坏阶；见证保留原括号和同一联合来源限制，不反驳固定 $L,d_0$ 的主域线性界。

**证明。** 复用本卷定理 21.3，完整构造如下。固定 $h_0,h_1\in(0,H)$，取足够小 $s>0$，在正定向标准标架置

$$
\begin{gathered}
r=\sqrt{h_1/s},\quad B=r^2,\quad\Delta=s^2,\quad
C=\sqrt{h_0^2h_1/s^3-s^2},\\
b=re_1,\qquad a=(C/r)e_1+(s/r)e_2.
\end{gathered}
$$

选定理 37.2 的字面 $t_-$，得

$$
x_0=(s/r)(-se_1+Ce_2),\quad x_1=-h_1e_3,
\quad x_2=-qe_2,\qquad q=rs^3=\sqrt{h_1}s^{5/2}.
$$

令 $\theta=2\arctan(s/C)$，另构造实际制备和反根树

$$
\begin{gathered}
b'=r(\cos\theta e_1+\sin\theta e_2),\qquad K'=-se_3,\\
N'=rs(\sin\theta e_1-\cos\theta e_2),
\qquad a'=(C/B)b'+N'/B,\qquad t'=t_+.
\end{gathered}
$$

$K'\times b'=N'$、$b'\perp N'$ 及 $b'\times(K'\times b')=BK'$ 给 $b'\times a'=K'$；两制备有相同 $A,B,C,\Delta$。半角恒等式

$$
\cos\theta=\frac{C^2-s^2}{C^2+s^2},\qquad
\sin\theta=\frac{2Cs}{C^2+s^2}
$$

给

$$
U'=\frac{CN'-\Delta b'}B=(s/r)(se_1-Ce_2)=-U,
\quad x'_0=x_0,\quad x'_1=x_1,
\quad x'_2=q(\sin\theta e_1-\cos\theta e_2).
$$

两范数三元组均为 $(h_0,h_1,q)$，所以同时在 $\mathcal D_H$。记录距离与下一目标差精确为

$$
\begin{aligned}
\varepsilon_s&=2q\sin(\theta/2)=2s^5/h_0,\\
\|x_3-x'_3\|&=2h_1q\cos(\theta/2)
=\sqrt2\,h_1^{3/2}\sqrt{h_0}\sqrt{\varepsilon_s}\cos(\theta/2).
\end{aligned}
$$

这由平面单位向量弦长公式及实际相反符号得到：$x_3=-(x_2\times x_1)$、$x'_3=x'_2\times x'_1$，并非任意环境符号假设。$s\downarrow0$ 时 $\cos(\theta/2)\to1$，且 $\varepsilon_s$ 参数化每个足够小正距离，给完整小误差平方根下界；本卷定理 21.2 给匹配上界。记录距离 $2\zeta$ 的实际对共用中点含噪回复，本卷推论 20.3 的纤维论证给匹配风险下界。

该对的叶范数 $\|a\|=h_0/s,\|b\|=\sqrt{h_1/s}$ 发散，$\Delta=s^2\to0$，因此不属于任意固定 $L,d_0$ 主域。两成员各是实际树／制备，不是任意环境数据，也不授予根反转或主动制备操作。证毕。

**命题 45.5（原制备移位窗口与有限视界误差）。** 若原精确 $q_0,q_1,q_2\le H$，保留三元组 $X_2,X_3,X_4$ 的幅值界可取 $H'=\max(H,H^2,H^3)$。移位窗口定理的来源是实际树 $\rho^kt$ 配同一个原 $p$，因此叶界和 $\Delta$ 仍是原值，无须将它们强加到仅作解释的 $F^2(p)$。

**证明。** $q_3=q_1q_2\le H^2$、$q_4=q_2q_3\le H^3$。若 $\kappa$ 已认证，带符号叉积迭代的误差 $e_j=\|\widehat X_j-X_j\|$ 由双线性展开满足

$$
e_{j+2}\le q_{j+1}e_j+q_je_{j+1}+e_je_{j+1}.
$$

符号未认证时则需在每个移位实际三元组上使用适用的 $H$ 域界。两方法均需真范数与累计误差账目，均只给有限视界结论，常数可随视界增长。证毕。

**命题 45.6（有限精确取得不推出统一全时间含噪保证）。** 原实际来源含一对初始有限记录可任意接近、未来扩展上确界差为无穷的合法制备；添加固定有限原生参考库或实际输出捕获记录仍不消除此障碍。

**证明。** 复用本卷命题 22.1：取 $t=\alpha,p=((3/2)e_1,(3/2)e_2)$，属于 $L=2,H=4,d_0=1$ 主域，且

$$
q_j=(3/2)^{F_{j+1}}.
$$

另一个固定制备由绕 $e_3$ 的小非零正旋转得到。初始三报告随角趋零而接近，$x_2$ 固定；循环 $e_1,e_2$ 方向的未来差为

$$
2\sin(\theta/2)(3/2)^{F_{j+1}},
$$

上确界无穷。每个固定原生参考及捕获／读取向量在正旋转下协变，范数有限；固定有限整组记录的扰动随角趋零，全部定向位可保持相同。因此有限精确恢复不提供统一全时间上确界误差保证，即使已声明有限校准库。这里比较的是全来源的合法制备对，不是准许观察者执行主动旋转。本命题不增加全参数全时间分类、校准噪声最优性或固定位数承诺。证毕。

## 46. 联合资源与精确实数限制

**约定 46.1（同一实现的资源向量）。** 成本保留为多坐标量：实际目标制备／供应与活树存储，目标 $\rho$ 执行，每个取得回复及宽度，事件／时间／Stop／来源／制备身份，辅助库或物理槽供应及维护，坐标图／定向参考状态和认证，原始数值档案，紧凑预测器及临时空间，每个有限请求输出，以及精度／算术／运行时。没有一个共同标量价格证明各合同中的物理赢家。

各合同的同时回复与更新资源为：

| 合同 | 额外取得及状态 | 含原报告的坐标总数 | 目标更新 |
| --- | --- | --- | --- |
| 原共同图或独立图三读 | 三个原对象向量回复；独立图恢复边界见第 38.1–38.3 项 | 九实坐标 | 二次 |
| 最终时刻 $b,K$／$b,K,N$ 库 | 二／三参考回复；持久同制备原生状态与最终共观测 | 十五／十八实坐标 | 二次 |
| 最终时刻 $O(3)$ 两探针加定向位 | 两回复及认证绝对定向、初始化与时刻绑定 | 十五实坐标加一位 | 二次 |
| 保留实际 $Q_2$ 的非零日程 | 两次后续对象回复；有限仪器参考保留 | 十五实坐标 | 四次 |
| 三时刻 $b,K$／$b,K,N$ 库 | 六／九参考回复；每时刻同制备共观测及相对参考义务 | 二十七／三十六实坐标 | 二次 |
| 三时刻 $a,b$／$a,b,K$ 制备库 | 同回复数量，供给不同物理状态；退化直线回退 | 二十七／三十六实坐标 | 二次 |
| 前瞻物理输出槽完整共读 | 两新增向量槽、两捕获、保持、最终共读；额外六坐标 | 十五实坐标 | 二次 |
| 物理槽的收缩未来回复 | 同捕获与传感义务；额外三坐标及一符号位 | 十二实坐标加一位 | 二次 |

三时刻 $O(3)$ 两探针定向替代须另计两个相对链路标志或三个逐时刻认证位。零未来可在原三读／二更新后停止，但所声明的参考供应状态不能因此免费。回复宽度不代替制备、保持、认证或硬件费用；这些是可分别选择的数学合同，物理实施未由本卷建立。

**命题 46.2（精确预测器与不同档案义务）。** 精确校准后签名 $(v,z,\kappa)$ 有六个实坐标及一个符号，$q_1=\|v\|$。每个有限输出可用固定维数滚动临时空间、每步一次带符号叉积计算；请求输出存储与原档案分别计价。

**证明。** 定理 38.1 的二向量递推给滚动求值；零分支使用零。签名是预测器，不替代必须保留的原始档案和身份。一个有限精确求值器表示无限序列，不能有限时间打印无限坐标。

若在另一个合同中明确供应来源代码，原叶计数 $(m,n)$ 给 $L_2=2m+3n,L_4=5m+8n$，完整二叉树有 $2L_j-1$ 节点；这些由计数替换直接得到，不从原 Read 揭示计数，也不在缺少表示模型时定价物理 $\rho$。证毕。

**命题 46.3（精确实数与位承诺的边界）。** 任意实坐标、受保护符号判定、归一化和除法都是数学操作，不自动给有限位实现。固定非零字面记录上的不可数圆不能由有限或可数附加字母表精确区分。

**证明。** 若每个圆上目标都精确可识别，附加记录在不同目标间必须不同；否则定理 38.2 失败。不可数集不能单射到可数集，所以该字母表不能使所有目标纤维成为单点。这只是信息障碍，不是近似位下界。

本卷命题 20.5 的条件 dyadic $H$ 解码，在仪器供应 dyadic 坐标与同时精度承诺、总误差不超过一的合同中，需固定次数整数运算，分子宽度

$$
B_{\rm num}=O(1+b+\log(1+H)),
$$

学校算法位工作 $O(B_{\rm num}^2)$、临时位 $O(B_{\rm num})$，$b$ 为二进制小数精度。该既有有限下一向量结果不定价新库中的平方根／除法／参考生产或无界未来增长。有效界、量化、来源／制备／动作误差、坐标漂移、传感误差律、认证及有限视界数值预算须各自供应。资源陈述不隐藏逆、复制、复位或来源码端口。证毕。

## 47. 来源映射、成熟结果的假设及保留边界

**约定 47.1（本卷内的准确复用位置）。** 来源、解释、尾部及共同图闭合来自本卷第 1–5 节；实际联合像、根反转、退化及计数纤维来自第 6.1–6.5 项；实际尾像和二值区别来自第 7 节；制备及零档案边界来自第 11.1–11.3 项；资源、操作及文献限制来自第 13–15 节；投影来自第 16.2–16.3 项；计数支持来自定义 18.1；含噪下一向量与 dyadic 解码来自定理 20.2、命题 20.5、定理 21.3 和推论 21.4；实际增长尾障碍来自命题 22.1。第 24–32 节的共同图全时间结论保留其来源域、制度及数值／资源条件，不提供免费的跨图校准。

第 35–36 节给出后续所用的原来源普通证明；第 37 节给精确报告像及同制备反根见证；第 38 节给全部达到的未来纤维与取得充要条件；第 39–40 节给不同目标商和精确记录风险；第 41–44 节分别给最终库、保留末图、三时刻不同库及物理槽合同；第 45–46 节给条件误差与共同资源。全称结论依赖这些证明，不依赖有限样本枚举。

**约定 47.2（仓内运输与读取结果的实际前提）。** 下列路径的结果只在其原假设下适用；它们不从原向量 Read/$\rho$ 菜单产生参考状态。

| 仓内真源路径 | 复用位置及条件 |
| --- | --- |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md` | 第 19.10–19.12 项区分不变量记录、协变输出、种子条件及实际联合记录纤维分解，前提是目标在实际联合纤维上恒定；第 20.7 项的同来源 XOR 校准位是另行取得变量；第 20.9 项区分被动坐标运输与物理移动／事件记录。纤维分解不取得缺失数据。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md` | 第 11 节假设有类型的运输映射、路径／相干及分辨率数据。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md` | 第 40 节假设 transition cocycle 及实际像／拼接条件。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md` | 第 347、397 节运输联合事件／规范数据，开放路径有端点标架及 holonomy 义务；无已观测关系时不能推断标架。 |
| `docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md` | 第 377 节另给群、表示、运输、二胞及测度，不由原 FIB 语法供应原生参考句柄。 |
| `docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md` | 第 19 节给 $SO(3)$ 边运输与权重；第 44 节使用不同的 $W=E$ 加 $H$ 仪器、严格球冠和明确操作／制备菜单，不能当成本卷原接口权限。 |
| `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean` | `FreeMagma Bool` 来源中 `true` 对应 $\alpha$，有替换／计数、单射和谱系组成纤维；不供应向量评价校准或物理逆操作。 |
| `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean` | 使用带地址的 $\alpha$／$\beta$／分支／缺席四符号读取及有限 frontier 回退，是不同于原向量 Read 的端口。 |
| `D5/S3/Observer/AgencyHolonomy/MemoryTransport.lean` | 组合已经给定的记忆映射。 |
| `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.lean` | 假设已经给定可见环路数据。 |
| `D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion.lean` | 假设已经给定群系数及全局标架拼接数据。 |
| `Library/Geometry/darpo2009vectorproduct.md` | 区分相容向量积恒等式／分类与完整 $SO(7)$ 协变，区分反事实控制字识别与一条实际历史取得；这里不借用七维或解析可逆控制定理。 |
| `Library/Geometry/singerwu2011vectordiffusion.md` | 假设加权正交边块、反向转置对称；流形近似另需局部 PCA／切标架采样条件。这里不借用流形极限或图估计定理。 |

此表前五个理论路径与五个 D5／两个 Library 路径对应修订 `29b8128bae35565e814eba59541bd28934aa64ac` 的相关完整节或模块；几何卷第 19、44 节及本卷第 1–23 节对应修订 `55c7d475f0367a2c7cc3989dedefad8e4552a04e` 的已发表正文。来源定位不等于重新编译这些 Lean 模块；本卷没有从它们冒领已形式化的参考取得定理。

**约定 47.3（主要文献的窄适用映射）。** Horn，*Closed-form solution of absolute orientation using unit quaternions*，JOSA A 4 (1987)，629–642，[作者原 PDF](https://people.csail.mit.edu/bkph/papers/Absolute_Orientation.pdf)，第 1.B、2.A 节的精确三轴构造要求已知对应非共线点和正旋转。本卷原点共同、尺度一，有标签 $(0,a,b)$ 或 $(0,b,K)$ 恰在 $\Delta>0$ 时非共线。第 38.1、41.2、43.2–43.3 项的正三轴证明明确满足这些条件；$O(3)$ 须有实际第三法向或认证定向。这里不借用其最小二乘估计器或统计性能。

Villar 等，*Scalars are universal: Equivariant machine learning, structured like classical physics*，[arXiv:2106.06610v2](https://arxiv.org/pdf/2106.06610v2)，第 5–6 页引理 1–2 描述同时有限向量组的 $O(d)$ Gram 不变量与 $SO(d)$ 的 Gram 加 $d$ 维子行列式。本卷 $d=3$，一个张成空间的尾三元组由递推决定全部余项，秩零分支另行处理；第 39.1 项的直接有限标架论证核对其前提，并不把三个独立变换报告当作一个共同群作用，也不借用无限输入或学习／近似定理。一般多项式协变、流形／连接一致性、向量积分类和 Kabsch 统计最优性均非这里的依据。

欧氏叉积、轨道／稳定子、注册及纤维分解是复用的成熟关系。本卷新增的实际独立报告纤维、固定记录目标商与半径，以及来源绑定的有限取得合同，是这些关系在原树源上的具体推导，不以重命名协变主张新意，也不主张全局数学原创。有限算术只能检查指定实例、发现反例；定理 37.2、41.3、43.2 和命题 45.4 已给所需完整实际见证及其普通证明。物理可供应性、误差／硬件实验、有限位与形式核验不是这些证明的结论。

**约定 47.4（未决的不同义务）。** 原接口的非零独立图不可识别性保持不变；各扩展的数学充分性以其新增端口、实际来源／制备绑定及同图取得为条件。物理库／槽／参考供应，前瞻 $Q_2$ 保留与共观测认证，校准噪声律、精度及成本认证，任意端口的最优资源价格和新的 Lean 形式化仍是分别未建立的义务。普通证明不等于连续物理空间、时钟或记忆装置的识别，也不将关系表达的长期目标判为完成。

## 追加锚（本行以下为增补区）
