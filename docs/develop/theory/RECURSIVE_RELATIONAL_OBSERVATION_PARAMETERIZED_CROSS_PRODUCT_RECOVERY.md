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
