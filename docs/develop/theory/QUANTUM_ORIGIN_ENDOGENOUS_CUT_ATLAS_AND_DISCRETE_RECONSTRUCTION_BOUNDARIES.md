# Quantum origin endogenous cut atlas and discrete reconstruction boundaries

本卷在纯实有限维内积载体上研究多个局部锐三轴二元切分窗口的全局正交复结构黏合判据、共享二维分支图上的无参考系 $\mathbb{Z}_2$ 手征和乐障碍、实载体算子三轴纯度球面方程，以及初等锐 $k$ 轴实二元切分在相位内生生成与双切分复合层析下的分类边界。

## 1. 定位、实内积载体与局部窗口合同

**约定 1.1（纯实内积载体与对称算子记号）。** 固定有限维非零实内积空间 $(V,g)$，其中 $g:V\times V\to\mathbb{R}$ 为正定对称双线性形式，范数记为 $\|v\|=\sqrt{g(v,v)}$。本卷不在 $V$ 上预先假定复标量乘法。对任意实线性算子 $T\in\operatorname{End}_{\mathbb{R}}(V)$，以 $T^{\mathsf T}\in\operatorname{End}_{\mathbb{R}}(V)$ 表示关于 $g$ 的实伴随（在任意 $g$-标准正交基下即矩阵转置），满足

$$
g(Tu,v)=g(u,T^{\mathsf T}v)\qquad(u,v\in V).
$$

记实对称算子空间为 $\operatorname{Sym}(V,g)=\{S\in\operatorname{End}_{\mathbb{R}}(V):S^{\mathsf T}=S\}$，半正定锥为 $\operatorname{Sym}_+(V,g)=\{S\in\operatorname{Sym}(V,g):g(v,Sv)\ge0\ (\forall v\in V)\}$，严格正定关系记为 $S\succ0$，实迹记为 $\operatorname{Tr}_{\mathbb{R}}(\cdot)$。空间 $(V,g)$ 上的正交复结构是指满足

$$
J^{\mathsf T}=-J,\qquad J^2=-I_V
$$

的实线性算子 $J\in\operatorname{End}_{\mathbb{R}}(V)$；满足该二式的 $J$ 自动为 $g$-正交等距（$J^{\mathsf T}J=-J^2=I_V$）且对一切 $v\in V$ 满足 $g(v,Jv)=0$。

**约定 1.2（窗口支撑与实张量复合）。** 空间 $(V,g)$ 上的正交投影是指满足 $\Pi^2=\Pi=\Pi^{\mathsf T}$ 的算子 $\Pi\in\operatorname{Sym}(V,g)$。称算子 $T\in\operatorname{End}_{\mathbb{R}}(V)$ 支撑于 $\Pi$，若 $\Pi T=T\Pi=T$（等价地，$\operatorname{Ran}T\subseteq\operatorname{Ran}\Pi$ 且 $(\operatorname{Ran}\Pi)^{\perp}\subseteq\ker T$）。对两个实内积空间 $(V_A,g_A)$ 与 $(V_B,g_B)$，其实张量积 $V_A\otimes_{\mathbb{R}}V_B$ 赋予唯一使 $(g_A\otimes g_B)(u_1\otimes v_1,u_2\otimes v_2)=g_A(u_1,u_2)g_B(v_1,v_2)$ 成立的正定实内积 $g_A\otimes g_B$；在此内积下 $(T_A\otimes T_B)^{\mathsf T}=T_A^{\mathsf T}\otimes T_B^{\mathsf T}$。

**来源与适用边界 1.3。** 既有卷 [`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 的定理 4.2、定理 7.2、定理 8.2 与定理 A.1 分别在单一全空间锐三轴切分（$\Pi=I_V$）上建立了内生中心复结构 $J=A_1A_2A_3$、在给定双因子各自复结构时给出了对齐复合扇区、在预先指定子空间间正交输运同构时给出了闭环相容条件，并给出了实不可约代数换位子的 $\mathbb{R}/\mathbb{C}/\mathbb{H}$ 三分；[`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 的定理 2.2 与定理 5.2 在复内积载体上建立了普遍内部二分与复算子三轴纯度球面；[`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 第 205–213 节在特定黄金脉冲守卫轨迹与远距门对易模型上建立了测度同构及局部相位装配，同时明确保留一般跨接口复单位黏合、可除环选型、有限精度守卫读出与一般系统复合的未决边界。第 2–5 节在不预设全局复结构亦不预设外部边输运同构的前提下，给出任意重叠或斜交实投影窗口图册的全局正交复结构黏合等价判据与标架逆公式，刻画共享二维分支图上对逐窗口坐标轴翻转规范不变的 $\mathbb{Z}_2$ 手征圈和乐障碍，导出纯实载体上的非交换算子三轴纯度球面与秩二 $J$-平面极值态，并确定初等锐 $k$ 轴实二元切分选出 $k=3$ 与 $\mathbb{C}$ 的精确边界。

## 2. 重叠实三轴切分图册的度量黏合定理与斜交失效边界

**定义 2.1（局部锐三轴实切分窗口与覆盖图册）。** 设 $\Pi\in\operatorname{Sym}(V,g)$ 为非零正交投影。支撑于 $\Pi$ 的局部锐三轴实切分窗口是指二元组 $(\Pi,A)$，其中实线性映射 $A:\mathbb{R}^3\to\operatorname{Sym}(V,g)$ 满足：对一切 $u\in\mathbb{R}^3$，

$$
A(u)^2=\|u\|^2\Pi.
$$

由 $A(u)^{\mathsf T}=A(u)$，对任意 $v\in\ker\Pi$ 有 $\|A(u)v\|^2=g(v,A(u)^2v)=\|u\|^2g(v,\Pi v)=0$，故 $\ker\Pi\subseteq\ker A(u)$，取转置自动给出窗口支撑等式 $\Pi A(u)=A(u)\Pi=A(u)$。取 $\mathbb{R}^3$ 的标准正交基 $\{e_1,e_2,e_3\}$，记 $A_i=A(e_i)$（$i=1,2,3$），并定义该窗口的局部手征积算子为

$$
J_{(\Pi,A)}=A_1A_2A_3\in\operatorname{End}_{\mathbb{R}}(V).
$$

空间 $(V,g)$ 上的覆盖锐三轴图册是指有限族 $\mathfrak{A}=\{(\Pi_\alpha,A_\alpha)\}_{\alpha\in\mathcal{I}}$，其中每个 $(\Pi_\alpha,A_\alpha)$ 为局部锐三轴实切分窗口，且其标架算子

$$
M_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}\Pi_\alpha\in\operatorname{Sym}_+(V,g)
$$

在 $V$ 上严格正定（$M_{\mathfrak{A}}\succ0$，等价地 $\sum_{\alpha\in\mathcal{I}}\operatorname{Ran}\Pi_\alpha=V$）。记各窗口局部手征积为 $J_\alpha=A_{\alpha,1}A_{\alpha,2}A_{\alpha,3}$，图册手征和算子为

$$
K_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}J_\alpha\in\operatorname{End}_{\mathbb{R}}(V).
$$

**引理 2.2（局部手征积的内生部分复结构性质）。** 对定义 2.1 中的任意局部锐三轴实切分窗口 $(\Pi,A)$，其轴生成元满足反对易关系 $\{A_i,A_j\}=A_iA_j+A_jA_i=2\delta_{ij}\Pi$（$1\le i,j\le3$），且局部手征积 $J_{(\Pi,A)}=A_1A_2A_3$ 满足

$$
\Pi J_{(\Pi,A)}=J_{(\Pi,A)}\Pi=J_{(\Pi,A)},\qquad J_{(\Pi,A)}^{\mathsf T}=-J_{(\Pi,A)},\qquad J_{(\Pi,A)}^2=-\Pi,
$$

并对一切 $u\in\mathbb{R}^3$ 满足 $[J_{(\Pi,A)},A(u)]=0$ 及 $\operatorname{dim}_{\mathbb{R}}\operatorname{Ran}\Pi\in 4\mathbb{Z}_{>0}$。此外，将 $A$ 复合任意正交基变换 $R\in O(3)$（$A^{(R)}(u)=A(Ru)$）时，有 $J_{(\Pi,A^{(R)})}=(\det R)\,J_{(\Pi,A)}$。

**证明。** 对任意 $u,w\in\mathbb{R}^3$，展开 $A(u+w)^2=\|u+w\|^2\Pi$ 并减去 $A(u)^2+A(w)^2=(\|u\|^2+\|w\|^2)\Pi$，得 $A(u)A(w)+A(w)A(u)=2\langle u,w\rangle\Pi$；取 $u=e_i,w=e_j$ 即得 $\{A_i,A_j\}=2\delta_{ij}\Pi$。由 $\Pi A_i=A_i\Pi=A_i$ 直接推出 $\Pi J_{(\Pi,A)}=J_{(\Pi,A)}\Pi=J_{(\Pi,A)}$。

对转置，利用 $A_i^{\mathsf T}=A_i$ 与三次相邻交换反对易，有

$$
J_{(\Pi,A)}^{\mathsf T}=(A_1A_2A_3)^{\mathsf T}=A_3A_2A_1=-A_3A_1A_2=A_1A_3A_2=-A_1A_2A_3=-J_{(\Pi,A)}.
$$

进而

$$
J_{(\Pi,A)}^2=-J_{(\Pi,A)}J_{(\Pi,A)}^{\mathsf T}=-A_1A_2A_3A_3A_2A_1=-A_1A_2\Pi A_2A_1=-A_1\Pi A_1=-\Pi.
$$

对每个 $i\in\{1,2,3\}$，$A_i$ 与其余两个轴算子反对易、与自身对易，故经过两次反号得 $A_iJ_{(\Pi,A)}=J_{(\Pi,A)}A_i$；由线性性知对一切 $u\in\mathbb{R}^3$ 有 $[J_{(\Pi,A)},A(u)]=0$。在非零子空间 $W=\operatorname{Ran}\Pi$ 上，$J_W=J_{(\Pi,A)}|_W$ 赋予 $W$ 复向量空间结构，而 $A_1|_W,A_3|_W$ 为满足 $(A_3|_W)^2=I_W$、$A_1|_W A_3|_W=-A_3|_W A_1|_W$ 的 $\mathbb{C}$-线性对合：$A_1|_W$ 将 $\ker(A_3|_W-I_W)$ 复线性同构地映为 $\ker(A_3|_W+I_W)$，故 $\dim_{\mathbb{C}}W=2\dim_{\mathbb{C}}\ker(A_3|_W-I_W)\in2\mathbb{Z}_{>0}$，从而 $\dim_{\mathbb{R}}W=2\dim_{\mathbb{C}}W\in4\mathbb{Z}_{>0}$。最后，在 $W$ 上三元线性形式 $(u_1,u_2,u_3)\mapsto\text{交错化 }\frac{1}{6}\sum_{\pi\in S_3}\operatorname{sgn}(\pi)A(u_{\pi(1)})A(u_{\pi(2)})A(u_{\pi(3)})$ 在 $(Re_1,Re_2,Re_3)$ 处取值 $(\det R)J_{(\Pi,A)}$，而由 $\{A(Re_i),A(Re_j)\}=2\delta_{ij}\Pi$ 知 $A(Re_1)A(Re_2)A(Re_3)$ 已完全反对称，故 $J_{(\Pi,A^{(R)})}=(\det R)J_{(\Pi,A)}$。∎

**定理 2.3（覆盖图册全局正交复结构黏合等价定理与标架显式公式）。** 设 $\mathfrak{A}=\{(\Pi_\alpha,A_\alpha)\}_{\alpha\in\mathcal{I}}$ 是 $(V,g)$ 上的覆盖锐三轴图册。下列三项条件彼此等价：

1. **全局正交复结构存在性**：存在 $(V,g)$ 上的正交复结构 $J\in\operatorname{End}_{\mathbb{R}}(V)$（$J^{\mathsf T}=-J$，$J^2=-I_V$），使得对一切 $\alpha\in\mathcal{I}$ 有 $\Pi_\alpha J=J\Pi_\alpha=J_\alpha$；
2. **成对跨投影手征相容性**：对一切 $\alpha,\beta\in\mathcal{I}$，有

$$
\Pi_\alpha J_\beta=J_\alpha\Pi_\beta;
$$

3. **标架交织恒等式**：对一切 $\alpha\in\mathcal{I}$，有

$$
\Pi_\alpha K_{\mathfrak{A}}=J_\alpha M_{\mathfrak{A}}.
$$

当上述等价条件成立时，满足条件 1 的正交复结构 $J$ 唯一，由显式标架逆公式给出：

$$
J=M_{\mathfrak{A}}^{-1}K_{\mathfrak{A}}=K_{\mathfrak{A}}M_{\mathfrak{A}}^{-1},
$$

并且 $J$ 自动与一切窗口的一切方向读出对易：对一切 $\alpha\in\mathcal{I}$ 与一切 $u\in\mathbb{R}^3$，有 $[J,A_\alpha(u)]=0$。

**证明。** 先证 $1\Rightarrow2$：若存在 $J$ 使 $\Pi_\gamma J=J\Pi_\gamma=J_\gamma$（$\forall\gamma\in\mathcal{I}$），则对任意 $\alpha,\beta\in\mathcal{I}$，

$$
\Pi_\alpha J_\beta=\Pi_\alpha(J\Pi_\beta)=(\Pi_\alpha J)\Pi_\beta=J_\alpha\Pi_\beta.
$$

次证 $2\Rightarrow3$：将 $\Pi_\alpha J_\beta=J_\alpha\Pi_\beta$ 对全部 $\beta\in\mathcal{I}$ 求和，即得 $\Pi_\alpha K_{\mathfrak{A}}=\sum_{\beta}\Pi_\alpha J_\beta=\sum_{\beta}J_\alpha\Pi_\beta=J_\alpha M_{\mathfrak{A}}$。

再证 $3\Rightarrow1$ 及唯一性与对易性。设对一切 $\alpha\in\mathcal{I}$ 有 $\Pi_\alpha K_{\mathfrak{A}}=J_\alpha M_{\mathfrak{A}}$。对该式关于 $\alpha\in\mathcal{I}$ 求和，得

$$
M_{\mathfrak{A}}K_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}\Pi_\alpha K_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}J_\alpha M_{\mathfrak{A}}=K_{\mathfrak{A}}M_{\mathfrak{A}},
$$

故 $M_{\mathfrak{A}}$ 与 $K_{\mathfrak{A}}$ 对易。因 $M_{\mathfrak{A}}\succ0$ 可逆，$M_{\mathfrak{A}}^{-1}$ 亦与 $K_{\mathfrak{A}}$ 对易。定义 $J=K_{\mathfrak{A}}M_{\mathfrak{A}}^{-1}=M_{\mathfrak{A}}^{-1}K_{\mathfrak{A}}$。由引理 2.2 知每个 $J_\alpha^{\mathsf T}=-J_\alpha$，故 $K_{\mathfrak{A}}^{\mathsf T}=-K_{\mathfrak{A}}$，配合 $(M_{\mathfrak{A}}^{-1})^{\mathsf T}=M_{\mathfrak{A}}^{-1}$ 得

$$
J^{\mathsf T}=(K_{\mathfrak{A}}M_{\mathfrak{A}}^{-1})^{\mathsf T}=M_{\mathfrak{A}}^{-1}K_{\mathfrak{A}}^{\mathsf T}=-M_{\mathfrak{A}}^{-1}K_{\mathfrak{A}}=-J.
$$

在 $\Pi_\alpha K_{\mathfrak{A}}=J_\alpha M_{\mathfrak{A}}$ 右乘 $M_{\mathfrak{A}}^{-1}$，得 $\Pi_\alpha J=J_\alpha$。对该式取转置并代入 $\Pi_\alpha^{\mathsf T}=\Pi_\alpha$、$J^{\mathsf T}=-J$、$J_\alpha^{\mathsf T}=-J_\alpha$，得 $-J\Pi_\alpha=-J_\alpha$，即 $J\Pi_\alpha=J_\alpha$。再利用引理 2.2 的 $J_\alpha\Pi_\alpha=J_\alpha$ 与 $J_\alpha^2=-\Pi_\alpha$，对每个 $\alpha\in\mathcal{I}$ 有

$$
\Pi_\alpha J^2=(\Pi_\alpha J)J=J_\alpha J=(J_\alpha\Pi_\alpha)J=J_\alpha(\Pi_\alpha J)=J_\alpha^2=-\Pi_\alpha.
$$

对全部 $\alpha\in\mathcal{I}$ 求和得 $M_{\mathfrak{A}}J^2=-M_{\mathfrak{A}}$，左乘 $M_{\mathfrak{A}}^{-1}$ 即得 $J^2=-I_V$，故 $J$ 是满足条件 1 的正交复结构。

对唯一性，设 $\widetilde{J}$ 也满足对一切 $\alpha\in\mathcal{I}$ 有 $\Pi_\alpha\widetilde{J}=J_\alpha$，求和得 $M_{\mathfrak{A}}\widetilde{J}=K_{\mathfrak{A}}$，左乘 $M_{\mathfrak{A}}^{-1}$ 即得 $\widetilde{J}=M_{\mathfrak{A}}^{-1}K_{\mathfrak{A}}=J$。最后，对任意 $\alpha\in\mathcal{I}$ 与 $u\in\mathbb{R}^3$，由 $A_\alpha(u)=\Pi_\alpha A_\alpha(u)\Pi_\alpha$ 与引理 2.2 的 $[J_\alpha,A_\alpha(u)]=0$，有

$$
JA_\alpha(u)=(J\Pi_\alpha)A_\alpha(u)=J_\alpha A_\alpha(u)=A_\alpha(u)J_\alpha=A_\alpha(u)(\Pi_\alpha J)=A_\alpha(u)J.
$$

故 $[J,A_\alpha(u)]=0$。∎

**命题 2.4（两两交集相容与跨投影度量相容的严格分离：三窗口代数障碍与两窗口斜交度量反例）。** 在赋予标准欧氏内积 $g$ 的 $V=\mathbb{R}^8=\mathbb{R}^4\oplus\mathbb{R}^4$ 上：

1. **三窗口两两零交但代数黏合失效**：存在由三个四维局部锐三轴窗口组成的覆盖图册 $\mathfrak{A}_{\mathrm{alg}}=\{(\Pi'_1,A'_1),(\Pi'_2,A'_2),(\Pi'_3,A'_3)\}$，使得任意两不同窗口子空间的交集均为零（$\operatorname{Ran}\Pi'_\alpha\cap\operatorname{Ran}\Pi'_\beta=\{0\}$，$\alpha\ne\beta$，故两两集合交集上的一致性条件真空成立），但在 $\mathbb{R}^8$ 上甚至不存在任何不要求保度量的纯实线性算子 $J_{\mathrm{lin}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^8)$ 在每个 $\operatorname{Ran}\Pi'_\alpha$ 上限制为 $J'_\alpha|_{\operatorname{Ran}\Pi'_\alpha}$（$\alpha=1,2,3$）；
2. **两窗口代数黏合唯一成立但度量正交黏合失效**：存在双窗口覆盖锐三轴图册 $\mathfrak{A}=\{(\Pi_1,A_1),(\Pi_2,A_2)\}$，使得 $\operatorname{Ran}\Pi_1\cap\operatorname{Ran}\Pi_2=\{0\}$ 且 $\operatorname{Ran}\Pi_1\oplus\operatorname{Ran}\Pi_2=\mathbb{R}^8$，因而在直和分解下存在唯一的纯代数复结构 $J_{\mathrm{alg}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^8)$（$J_{\mathrm{alg}}^2=-I_8$）在 $\operatorname{Ran}\Pi_1$ 与 $\operatorname{Ran}\Pi_2$ 上分别限制为 $J_1|_{\operatorname{Ran}\Pi_1}$ 与 $J_2|_{\operatorname{Ran}\Pi_2}$，但跨投影手征差满足 $(\Pi_1J_2-J_1\Pi_2)_{1,2}=-\frac{3}{25}\ne0$，故 $(\mathbb{R}^8,g)$ 上不存在任何与内积 $g$ 相容的正交复结构 $J$（甚至在允许独立窗口定向翻转 $J_\alpha\mapsto s_\alpha J_\alpha$，$s_1,s_2\in\{\pm1\}$ 后仍不存在）满足 $\Pi_\alpha J=s_\alpha J_\alpha$（$\alpha=1,2$）；
3. **成对主角恢复度量相容**：若将第 2 项构造中的斜交倾角对角阵替换为成对倾角 $C_{\mathrm{pair}}=\operatorname{diag}(\frac{3}{4},\frac{3}{4},\frac{4}{3},\frac{4}{3})$，则 $\operatorname{Ran}\Pi_1\cap\operatorname{Ran}\Pi_2=\{0\}$ 仍然成立，且 $\Pi_1J_2=J_1\Pi_2$ 精确恢复，定理 2.3 给出全局正交复结构。

**证明。** 在 $\mathbb{R}^4=\mathbb{R}^2\otimes\mathbb{R}^2$ 上固定标准锐三轴实对称对合组：令

$$
I_2=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
\omega_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
$$

定义 $4\times4$ 实矩阵

$$
E_1=\sigma_x\otimes I_2,\qquad E_2=\omega_2\otimes\omega_2,\qquad E_3=\sigma_z\otimes I_2.
$$

因 $\omega_2^{\mathsf T}=-\omega_2$，有 $E_2^{\mathsf T}=\omega_2^{\mathsf T}\otimes\omega_2^{\mathsf T}=E_2$，故 $E_1,E_2,E_3$ 均为对称正交对合且两两反对易，其乘积为块对角反对称复单位

$$
J_0=E_1E_2E_3=(\sigma_x\omega_2\sigma_z)\otimes\omega_2=I_2\otimes\omega_2=\operatorname{diag}(\omega_2,\omega_2).
$$

先证第 1 项。在 $\mathbb{R}^8=\mathbb{R}^4\oplus\mathbb{R}^4$ 中取三个 $8\times4$ 列标准正交矩阵

$$
W'_1=\begin{pmatrix}I_4\\0\end{pmatrix},\qquad
W'_2=\begin{pmatrix}0\\I_4\end{pmatrix},\qquad
W'_3=\frac{1}{\sqrt{2}}\begin{pmatrix}I_4\\I_4\end{pmatrix}.
$$

令 $\Pi'_\alpha=W'_\alpha(W'_\alpha)^{\mathsf T}$（$\alpha=1,2,3$），对 $\alpha=1,2$ 取 $A'_{\alpha,i}=W'_\alpha E_i(W'_\alpha)^{\mathsf T}$，对 $\alpha=3$ 翻转第三轴符号取 $A'_{3,1}=W'_3E_1(W'_3)^{\mathsf T}$、$A'_{3,2}=W'_3E_2(W'_3)^{\mathsf T}$、$A'_{3,3}=-W'_3E_3(W'_3)^{\mathsf T}$。三窗口各自满足定义 2.1，$\Pi'_1+\Pi'_2+\Pi'_3\succeq I_8\succ0$，且子空间 $\operatorname{Ran}\Pi'_1=\mathbb{R}^4\oplus\{0\}$、$\operatorname{Ran}\Pi'_2=\{0\}\oplus\mathbb{R}^4$ 与对角子空间 $\operatorname{Ran}\Pi'_3=\{(x,x):x\in\mathbb{R}^4\}$ 两两交集均为 $\{0\}$。然而局部手征积在各自子空间上的作用分别为 $J'_1(x,0)=(J_0x,0)$、$J'_2(0,x)=(0,J_0x)$ 与 $J'_3(x,x)=(-J_0x,-J_0x)$。若存在 $J_{\mathrm{lin}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^8)$ 同时限制为三者，则对非零 $x\in\mathbb{R}^4$，线性关系 $(x,0)+(0,x)-(x,x)=0$ 迫使 $(J_0x,0)+(0,J_0x)-(-J_0x,-J_0x)=(2J_0x,2J_0x)=0$，与 $J_0$ 可逆矛盾，证毕结论 1。

再证第 2 项。在 $\mathbb{R}^8=\mathbb{R}^4\oplus\mathbb{R}^4$ 中定义两个 $8\times4$ 列标准正交等距嵌入矩阵 $W_1,W_2$：取勾股有理对角阵

$$
C=\operatorname{diag}\!\left(\frac{3}{4},\frac{4}{3},\frac{3}{4},\frac{3}{4}\right),\quad
D_1=\operatorname{diag}\!\left(\frac{4}{5},\frac{3}{5},\frac{4}{5},\frac{4}{5}\right),\quad
CD_1=\operatorname{diag}\!\left(\frac{3}{5},\frac{4}{5},\frac{3}{5},\frac{3}{5}\right),
$$

令

$$
W_1=\begin{pmatrix}I_4\\0\end{pmatrix},\qquad
W_2=\begin{pmatrix}D_1\\CD_1\end{pmatrix}.
$$

因 $D_1^2+(CD_1)^2=I_4$，有 $W_1^{\mathsf T}W_1=W_2^{\mathsf T}W_2=I_4$。定义 $\Pi_\alpha=W_\alpha W_\alpha^{\mathsf T}$ 与 $A_{\alpha,i}=W_\alpha E_i W_\alpha^{\mathsf T}$（$\alpha\in\{1,2\}$，$i\in\{1,2,3\}$）。由 $W_\alpha^{\mathsf T}W_\alpha=I_4$ 直接验证 $(\Pi_\alpha,A_\alpha)$ 为局部锐三轴实切分窗口，且局部手征积为 $J_\alpha=W_\alpha J_0 W_\alpha^{\mathsf T}$。分块矩阵 $\begin{pmatrix}W_1&W_2\end{pmatrix}=\begin{pmatrix}I_4&D_1\\0&CD_1\end{pmatrix}$ 上三角且对角块 $I_4$ 与 $CD_1$ 均非奇异，故 $\operatorname{Ran}\Pi_1\cap\operatorname{Ran}\Pi_2=\{0\}$、$\operatorname{Ran}\Pi_1\oplus\operatorname{Ran}\Pi_2=\mathbb{R}^8$ 且 $M_{\mathfrak{A}}=\Pi_1+\Pi_2\succ0$。因两子空间直和分解成立，由 $J_{\mathrm{alg}}(W_\alpha x)=W_\alpha(J_0x)$（$x\in\mathbb{R}^4$，$\alpha=1,2$）唯一定义的线性算子满足 $J_{\mathrm{alg}}^2=-I_8$。

计算左上 $4\times4$ 块 $W_1^{\mathsf T}(\Pi_1J_2)W_1$ 与 $W_1^{\mathsf T}(J_1\Pi_2)W_1$：因 $W_1^{\mathsf T}\Pi_1=W_1^{\mathsf T}$、$W_1^{\mathsf T}J_1=J_0W_1^{\mathsf T}$ 且 $W_1^{\mathsf T}W_2=D_1$，有

$$
W_1^{\mathsf T}(\Pi_1J_2)W_1=D_1J_0D_1,\qquad
W_1^{\mathsf T}(J_1\Pi_2)W_1=J_0D_1^2.
$$

在首两个坐标组成的 $2\times2$ 子块上，$D_1$ 的对角元为 $(\frac{4}{5},\frac{3}{5})$，$J_0$ 的子块为 $\omega_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$，于是

$$
(\Pi_1J_2)_{1,2}=(D_1J_0D_1)_{1,2}=-\frac{4}{5}\cdot\frac{3}{5}=-\frac{12}{25},\qquad
(J_1\Pi_2)_{1,2}=(J_0D_1^2)_{1,2}=-\left(\frac{3}{5}\right)^2=-\frac{9}{25},
$$

差值为 $-\frac{3}{25}\ne0$。更一般地，对任意符号选择 $s_1,s_2\in\{\pm1\}$，若存在满足 $J^{\mathsf T}=-J$ 与 $\Pi_\alpha J=s_\alpha J_\alpha$（$\alpha=1,2$）的算子 $J$，则取转置必有 $J\Pi_\alpha=s_\alpha J_\alpha$，从而 $\Pi_1(s_2J_2)=\Pi_1J\Pi_2=(s_1J_1)\Pi_2$，要求在 $(1,2)$ 元上有 $-\frac{12}{25}s_2=-\frac{9}{25}s_1$，这在 $s_1,s_2\in\{\pm1\}$ 下不可能成立（$|\frac{12}{25}|\ne|\frac{9}{25}|$），证毕结论 2。

最后证第 3 项：若改取成对倾角 $C_{\mathrm{pair}}=\operatorname{diag}(\frac{3}{4},\frac{3}{4},\frac{4}{3},\frac{4}{3})$ 与 $D_{1,\mathrm{pair}}=\operatorname{diag}(\frac{4}{5},\frac{4}{5},\frac{3}{5},\frac{3}{5})$，则 $D_{1,\mathrm{pair}}=\frac{4}{5}I_2\oplus\frac{3}{5}I_2$ 与 $J_0=\omega_2\oplus\omega_2$ 严格对易，同时 $C_{\mathrm{pair}}D_{1,\mathrm{pair}}=\frac{3}{5}I_2\oplus\frac{4}{5}I_2$ 亦与 $J_0$ 对易且可逆。此时

$$
\Pi_1J_2=\begin{pmatrix}D_{1,\mathrm{pair}}J_0D_{1,\mathrm{pair}}&D_{1,\mathrm{pair}}J_0C_{\mathrm{pair}}D_{1,\mathrm{pair}}\\0&0\end{pmatrix}
=\begin{pmatrix}J_0D_{1,\mathrm{pair}}^2&J_0D_{1,\mathrm{pair}}C_{\mathrm{pair}}D_{1,\mathrm{pair}}\\0&0\end{pmatrix}=J_1\Pi_2,
$$

同理 $\Pi_2J_1=(\Pi_1J_2)^{\mathsf T}\cdot(-1)=(-J_1\Pi_2)^{\mathsf T}=J_2\Pi_1$，全部成对跨投影相容条件满足，由定理 2.3 得唯一全局正交复结构（此处即为 $J_0\oplus J_0$）。∎

## 3. 共享二维锐分支图上的无参考系手征和乐与定向障碍

**定义 3.1（共享二维实分支图与定向无关三轴边窗口）。** 设有限连通无向简单图 $\mathcal{G}=(Q,E)$（$|Q|\ge2$）的每个顶点 $q\in Q$ 对应一个二维实子空间 $B_q\subseteq V$（$\dim_{\mathbb{R}}B_q=2$），且全空间正交直和分解为

$$
V=\bigoplus_{q\in Q}B_q,
$$

记到 $B_q$ 的正交投影为 $P_q\in\operatorname{Sym}(V,g)$（$P_qP_r=\delta_{qr}P_q$，$\sum_{q\in Q}P_q=I_V$）。图 $\mathcal{G}$ 上的共享分支锐三轴网络是指为每条边 $e=\{q,r\}\in E$ 配备一个四维局部锐三轴实切分窗口 $(\Pi_e,A_e)$，使得：

$$
\Pi_e=P_q+P_r,\qquad A_{e,3}=\eta_{e,q}P_q+\eta_{e,r}P_r,
$$

其中分支符号满足 $\{\eta_{e,q},\eta_{e,r}\}=\{+1,-1\}$（即第三轴锐二元读出恰分离两个共享二维分支 $B_q$ 与 $B_r$）。因单窗口对坐标轴正交标记允许三轴定向反转 $R\in O(3)\setminus SO(3)$（引理 2.2 中 $J_e\mapsto -J_e$），称全局正交复结构 $J$ 与网络在无预设轴定向意义下相容，若存在边定向符号族 $\{s_e\}_{e\in E}\in\{\pm1\}^E$ 使得对一切 $e\in E$ 有 $\Pi_e J=J\Pi_e=s_eJ_e$。

**引理 3.2（边窗口自动分块约化与等距分支输运）。** 在定义 3.1 的网络中，对每条边 $e=\{q,r\}\in E$：

1. 局部手征积 $J_e=A_{e,1}A_{e,2}A_{e,3}$ 关于 $B_q\oplus B_r$ 自动分块对角化：存在唯一的二维正交复结构 $J_{e,q}\in\operatorname{End}_{\mathbb{R}}(B_q)$ 与 $J_{e,r}\in\operatorname{End}_{\mathbb{R}}(B_r)$（$J_{e,x}^{\mathsf T}=-J_{e,x}$，$J_{e,x}^2=-I_{B_x}$，$x\in\{q,r\}$），使得

$$
J_e=J_{e,q}P_q+J_{e,r}P_r;
$$

2. 定义分支间实线性算子 $U_{e,qr}=P_qA_{e,1}P_r|_{B_r}:B_r\to B_q$，则 $U_{e,qr}$ 是 $B_r$ 到 $B_q$ 的满射实线性等距（$U_{e,qr}U_{e,qr}^{\mathsf T}=I_{B_q}$，$U_{e,qr}^{\mathsf T}U_{e,qr}=I_{B_r}$），并且第一、第二轴算子完全由 $(J_{e,q},U_{e,qr})$ 决定：

$$
U_{e,qr}J_{e,r}=J_{e,q}U_{e,qr},\qquad P_qA_{e,2}P_r|_{B_r}=-\eta_{e,q}J_{e,q}U_{e,qr},\qquad P_xA_{e,1}P_x=P_xA_{e,2}P_x=0\quad(x\in\{q,r\});
$$

3. 在任一公共顶点 $q\in Q$ 处，对任意两条与 $q$ 关联的边 $e,f\in E$，标量

$$
\chi_q(e,f)=-\frac{1}{2}\operatorname{Tr}_{B_q}(J_{e,q}J_{f,q})
$$

取值于 $\{+1,-1\}$，且满足 $J_{e,q}=\chi_q(e,f)J_{f,q}$。

**证明。** 固定 $e=\{q,r\}\in E$。由引理 2.2 有 $[J_e,A_{e,3}]=0$；而 $P_q=\frac{1}{2}(\Pi_e+\eta_{e,q}A_{e,3})$、$P_r=\frac{1}{2}(\Pi_e-\eta_{e,q}A_{e,3})$，故 $[J_e,P_q]=[J_e,P_r]=0$。结合 $\Pi_eJ_e=J_e\Pi_e=J_e$ 得 $J_e=P_qJ_eP_q+P_rJ_eP_r$；令 $J_{e,x}=P_xJ_eP_x|_{B_x}$（$x\in\{q,r\}$），由 $J_e^{\mathsf T}=-J_e$ 与 $J_e^2=-(P_q+P_r)$ 即得 $J_{e,x}^{\mathsf T}=-J_{e,x}$ 与 $J_{e,x}^2=-I_{B_x}$，证毕第 1 项。

对第 2 项，对 $i\in\{1,2\}$，由 $\{A_{e,i},A_{e,3}\}=0$ 与 $A_{e,3}=\eta_{e,q}(P_q-P_r)$（$\eta_{e,q}\in\{\pm1\}$）得 $A_{e,i}(P_q-P_r)=-(P_q-P_r)A_{e,i}$。两边同乘 $P_x$（$x\in\{q,r\}$）得 $P_xA_{e,i}P_x=-P_xA_{e,i}P_x$，故 $P_xA_{e,i}P_x=0$。于是 $A_{e,1}=P_qA_{e,1}P_r+P_rA_{e,1}P_q$；由 $A_{e,1}^{\mathsf T}=A_{e,1}$ 知 $(U_{e,qr})^{\mathsf T}=P_rA_{e,1}P_q|_{B_q}$。代入 $A_{e,1}^2=P_q+P_r$ 并取对角块，即得 $U_{e,qr}U_{e,qr}^{\mathsf T}=I_{B_q}$ 与 $U_{e,qr}^{\mathsf T}U_{e,qr}=I_{B_r}$。在 $A_{e,1}J_e=J_eA_{e,1}$ 两边左乘 $P_q$、右乘 $P_r$，得 $U_{e,qr}J_{e,r}=J_{e,q}U_{e,qr}$。再在 $J_e=A_{e,1}A_{e,2}A_{e,3}$ 左乘 $A_{e,1}$、右乘 $A_{e,3}$，利用 $A_{e,1}^2=A_{e,3}^2=\Pi_e$ 与 $[A_{e,1},J_e]=0$ 得 $A_{e,2}=J_eA_{e,1}A_{e,3}$；左乘 $P_q$、右乘 $P_r$ 并代入 $A_{e,3}P_r=\eta_{e,r}P_r=-\eta_{e,q}P_r$，即得 $P_qA_{e,2}P_r|_{B_r}=-\eta_{e,q}J_{e,q}U_{e,qr}$，证毕第 2 项。

对第 3 项，二维欧氏平面 $(B_q,g|_{B_q})$ 上满足 $K^{\mathsf T}=-K$ 的反对称算子空间是一维实空间（在任一标准正交基下由 $\omega_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ 张成），其中满足 $K^2=-I_{B_q}$ 者恰为 $\pm\omega_2$ 两个元素。故 $J_{e,q}=\pm J_{f,q}$；由 $J_{f,q}^2=-I_{B_q}$ 与 $\operatorname{Tr}_{B_q}(I_{B_q})=2$ 得 $-\frac{1}{2}\operatorname{Tr}_{B_q}((\pm J_{f,q})J_{f,q})=\pm1$，证毕第 3 项。∎

**定理 3.3（共享分支网络的无基 $\mathbb{Z}_2$ 手征圈和乐判据）。** 设 $\mathcal{G}=(Q,E)$ 为定义 3.1 中的有限连通图（因此 $\sum_{e\in E}\Pi_e=\sum_{q\in Q}\deg_{\mathcal{G}}(q)P_q\succ0$ 构成覆盖图册）。对 $\mathcal{G}$ 中任意闭路 $C=(q_1,e_1,q_2,e_2,\ldots,q_L,e_L,q_1)$（其中 $e_k=\{q_k,q_{k+1}\}$，$q_{L+1}=q_1$，$e_0=e_L$），定义其无参考系手征和乐号为

$$
\mathcal{H}(C)=\prod_{k=1}^{L}\chi_{q_k}(e_{k-1},e_k)=\prod_{k=1}^{L}\left(-\frac{1}{2}\operatorname{Tr}_{B_{q_k}}(J_{e_{k-1},q_k}J_{e_k,q_k})\right)\in\{+1,-1\}.
$$

则：

1. **定向规范不变性**：在任意独立的逐窗口三轴定向翻转 $J_e\mapsto s_eJ_e$（$\{s_e\}_{e\in E}\in\{\pm1\}^E$）下，$\mathcal{H}(C)$ 严格不变；
2. **全局正交复结构存在充要判据**：存在边定向符号 $\{s_e\}_{e\in E}\in\{\pm1\}^E$ 与 $(V,g)$ 上的正交复结构 $J$ 使得对一切 $e\in E$ 有 $\Pi_eJ=J\Pi_e=s_eJ_e$，当且仅当对 $\mathcal{G}$ 的每一个简单圈 $C$（等价地，关于 $\mathcal{G}$ 的一棵生成树 $T$ 的全部基本圈）均有 $\mathcal{H}(C)=+1$；
3. **全局共轭唯一性**：当上述条件成立时，由连通性知二元组 $(J,\{s_e\}_{e\in E})$ 在单一全局复共轭变换 $(J,\{s_e\}_{e\in E})\mapsto(-J,\{-s_e\}_{e\in E})$ 之下唯一，且 $J=\bigoplus_{q\in Q}J_q$，其中每个 $J_q=s_eJ_{e,q}$（任取与 $q$ 关联的 $e\in E$）。

**证明。** 对第 1 项，当 $J_e$ 替换为 $s_eJ_e$ 时，有 $J_{e,q}\mapsto s_eJ_{e,q}$，故每个顶点转移号变换为 $\chi_{q_k}(e_{k-1},e_k)\mapsto s_{e_{k-1}}s_{e_k}\chi_{q_k}(e_{k-1},e_k)$。沿闭路 $C$ 连乘时，每条相继边 $e_k$（$1\le k\le L$）在 $k$ 处与 $k+1$ 处（$L+1\equiv1$）各出现一次，因 $s_{e_k}^2=+1$，总乘积 $\prod_{k=1}^L(s_{e_{k-1}}s_{e_k})=\prod_{k=1}^L s_{e_k}^2=+1$，故 $\mathcal{H}(C)$ 不变。

对第 2 项的必要性，设存在 $(J,\{s_e\}_{e\in E})$ 使 $\Pi_eJ=J\Pi_e=s_eJ_e$（$\forall e\in E$）。对任意顶点 $q\in Q$ 与关联边 $e=\{q,r\}$，有 $P_q\Pi_e=\Pi_eP_q=P_q$，故 $P_qJ=P_q\Pi_eJ=s_eP_qJ_e=s_eJ_{e,q}P_q$ 且 $JP_q=s_eJ_{e,q}P_q$。因此 $J$ 在 $B_q$ 上限制为与关联边选取无关的二维正交复结构 $J_q=s_eJ_{e,q}$。于是对任意同一顶点 $q$ 的两条关联边 $e,f$，有 $J_{e,q}=s_es_fJ_{f,q}$，即 $\chi_q(e,f)=s_es_f$。沿任意闭路 $C$ 连乘即得 $\mathcal{H}(C)=\prod_{k=1}^L(s_{e_{k-1}}s_{e_k})=+1$。

对第 2 项的充分性与第 3 项，设对 $\mathcal{G}$ 的一棵生成树 $T=(Q,E_T)$ 的所有基本圈均有 $\mathcal{H}(C)=+1$。先注意到对同一顶点 $q$ 的任意三条关联边 $e,f,h$，由 $J_{e,q}=\chi_q(e,f)J_{f,q}$ 与 $J_{f,q}=\chi_q(f,h)J_{h,q}$ 得转移号满足余链乘法恒等式 $\chi_q(e,h)=\chi_q(e,f)\chi_q(f,h)$ 以及 $\chi_q(e,e)=+1$、$\chi_q(f,e)=\chi_q(e,f)$。固定根顶点 $q_*\in Q$ 及 $B_{q_*}$ 上的一个二维正交复结构 $J_{q_*}\in\{\pm J_{e_*,q_*}\}$（其中 $e_*$ 为与 $q_*$ 关联的一条树边；两个选取恰相差全局负号）。对每个 $q\in Q$，沿生成树 $T$ 中从 $q_*$ 到 $q$ 的唯一简单路径 $P_T(q_*,q)=(q_*=v_0,t_1,v_1,\ldots,t_m,v_m=q)$（$t_j\in E_T$），沿树边归纳唯一确定树边符号 $s_{t_j}\in\{\pm1\}$ 与顶点复结构 $J_{v_j}\in\operatorname{End}_{\mathbb{R}}(B_{v_j})$：在 $v_{j-1}$ 处由 $s_{t_j}J_{t_j,v_{j-1}}=J_{v_{j-1}}$ 唯一确定 $s_{t_j}\in\{\pm1\}$（因 $J_{v_{j-1}}\in\{\pm J_{t_j,v_{j-1}}\}$），再置 $J_{v_j}=s_{t_j}J_{t_j,v_j}$。如此对一切树边 $t=\{u,v\}\in E_T$ 均有 $J_u=s_tJ_{t,u}$ 且 $J_v=s_tJ_{t,v}$。

现取任意非树弦边 $e=\{u,v\}\in E\setminus E_T$。令 $w\in Q$ 为 $P_T(q_*,u)$ 与 $P_T(q_*,v)$ 在 $T$ 中的最近公共祖先，则由 $T$ 中从 $u$ 经 $w$ 到 $v$ 的唯一简单树路径与弦边 $e$ 闭合而成唯一基本圈 $C_e=(u=x_1,t'_1,x_2,\ldots,t'_p,x_{p+1}=v,e,u)$（$t'_i\in E_T$）。在树路径内部各顶点 $x_2,\ldots,x_p$ 处，由树边构造知 $s_{t'_{i-1}}J_{t'_{i-1},x_i}=J_{x_i}=s_{t'_i}J_{t'_i,x_i}$，故 $\chi_{x_i}(t'_{i-1},t'_i)=s_{t'_{i-1}}s_{t'_i}$。代入基本圈和乐假设 $+1=\mathcal{H}(C_e)$，消去成对出现的内部树边符号后得

$$
+1=\chi_u(e,t'_1)\left(\prod_{i=2}^{p}s_{t'_{i-1}}s_{t'_i}\right)\chi_v(t'_p,e)=\chi_u(e,t'_1)\,s_{t'_1}s_{t'_p}\,\chi_v(t'_p,e),
$$

其中 $p=1$ 时中间空积为 $+1$。令 $s_e=s_{t'_1}\chi_u(e,t'_1)\in\{\pm1\}$：一方面由 $J_u=s_{t'_1}J_{t'_1,u}$ 与 $J_{t'_1,u}=\chi_u(e,t'_1)J_{e,u}$ 得 $s_eJ_{e,u}=J_u$；另一方面由上式知 $s_e=s_{t'_p}\chi_v(t'_p,e)$，故由 $J_v=s_{t'_p}J_{t'_p,v}$ 与 $J_{t'_p,v}=\chi_v(t'_p,e)J_{e,v}$ 同时得 $s_eJ_{e,v}=J_v$。于是对一切边 $e=\{q,r\}\in E$（无论树边或弦边）均有 $s_eJ_e=J_qP_q+J_rP_r$。定义全局算子 $J=\bigoplus_{q\in Q}J_q$，则 $J^{\mathsf T}=-J$、$J^2=-I_V$，且对每条边 $e=\{q,r\}\in E$ 有 $\Pi_eJ=(P_q+P_r)J=J_qP_q+J_rP_r=s_eJ_e=J\Pi_e$（这同时满足定理 2.3 关于重标号图册 $\{(\Pi_e,s_eA_e)\}_{e\in E}$ 的跨投影相容条件 $\Pi_e(s_fJ_f)=(s_eJ_e)\Pi_f$）。因根顶点 $J_{q_*}$ 仅有两值且连通树归纳每步唯一，$(J,\{s_e\}_{e\in E})$ 在整体变号下唯一。∎

**命题 3.4（六维三分支 Möbius 手征阻挫三角形反例）。** 在 $V=\mathbb{R}^6=B_1\oplus B_2\oplus B_3$（每个 $B_q=\mathbb{R}^2$ 赋予标准欧氏内积）上，存在三角形图 $C_3=(\{1,2,3\},\{e_{12},e_{23},e_{31}\})$ 上的共享分支锐三轴网络，使得每条边上的四维窗口 $(\Pi_e,A_e)$ 均严格满足定义 2.1 与定义 3.1，但三边圈的手征和乐为 $\mathcal{H}(C_3)=-1$；因此，无论对三个局部窗口如何独立调整坐标轴正交定向 $\{s_e\}\in\{\pm1\}^3$，$(\mathbb{R}^6,g)$ 上均不存在与三窗口同时相容的正交复结构。

**证明。** 在每个二维分支 $\mathbb{R}^2$ 上记 $\omega_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$、$\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$（满足 $\sigma_z^{\mathsf T}=\sigma_z$，$\sigma_z^2=I_2$，且 $\sigma_z\omega_2\sigma_z=-\omega_2$）。对一条边 $e=\{q,r\}$、选定二维复结构对 $(K_q,K_r)\in\{\pm\omega_2\}^2$ 及满足 $UK_r=K_qU$ 的 $2\times2$ 正交阵 $U\in O(2)$，在子空间 $B_q\oplus B_r=\mathbb{R}^4$ 上按分块矩阵定义

$$
A_{e,1}\big|_{B_q\oplus B_r}=\begin{pmatrix}0&U\\U^{\mathsf T}&0\end{pmatrix},\quad
A_{e,2}\big|_{B_q\oplus B_r}=\begin{pmatrix}0&-K_qU\\U^{\mathsf T}K_q&0\end{pmatrix},\quad
A_{e,3}\big|_{B_q\oplus B_r}=\begin{pmatrix}I_2&0\\0&-I_2\end{pmatrix},
$$

并在余下第三分支上置零。直接计算：$(-K_qU)^{\mathsf T}=-U^{\mathsf T}K_q^{\mathsf T}=U^{\mathsf T}K_q$，故三矩阵均实对称；由 $UU^{\mathsf T}=U^{\mathsf T}U=I_2$ 与 $K_q^2=-I_2$ 知三矩阵平方均为 $I_4$；对反对易性，

$$
\begin{pmatrix}0&U\\U^{\mathsf T}&0\end{pmatrix}\begin{pmatrix}0&-K_qU\\U^{\mathsf T}K_q&0\end{pmatrix}
+\begin{pmatrix}0&-K_qU\\U^{\mathsf T}K_q&0\end{pmatrix}\begin{pmatrix}0&U\\U^{\mathsf T}&0\end{pmatrix}
=\begin{pmatrix}K_q-K_q&0\\0&-U^{\mathsf T}K_qU+U^{\mathsf T}K_qU\end{pmatrix}=0,
$$

且前两矩阵均为反对角块故与块对角的 $A_{e,3}$ 反对易。因此对任意 $u\in\mathbb{R}^3$ 有 $A_e(u)^2=\|u\|^2\Pi_e$。计算局部手征积在 $B_q\oplus B_r$ 上的块：

$$
J_e\big|_{B_q\oplus B_r}
=\begin{pmatrix}0&U\\U^{\mathsf T}&0\end{pmatrix}\begin{pmatrix}0&-K_qU\\U^{\mathsf T}K_q&0\end{pmatrix}\begin{pmatrix}I_2&0\\0&-I_2\end{pmatrix}
=\begin{pmatrix}K_q&0\\0&-U^{\mathsf T}K_qU\end{pmatrix}\begin{pmatrix}I_2&0\\0&-I_2\end{pmatrix}
=\begin{pmatrix}K_q&0\\0&K_r\end{pmatrix},
$$

其中末步用到 $UK_r=K_qU\iff U^{\mathsf T}K_qU=K_r$。

现对三边分别赋值：在 $e_{12}=\{1,2\}$ 上取 $(K_1,K_2)=(\omega_2,\omega_2)$，$U=I_2$；在 $e_{23}=\{2,3\}$ 上取 $(K_2,K_3)=(\omega_2,\omega_2)$，$U=I_2$；在扭转边 $e_{31}=\{3,1\}$ 上取 $(K_3,K_1)=(\omega_2,-\omega_2)$，$U=\sigma_z$（满足 $\sigma_z(-\omega_2)=\omega_2\sigma_z$）。于是三个顶点处的诱导局部复结构对依次为：

- 顶点 $1$：$J_{e_{31},1}=-\omega_2$，$J_{e_{12},1}=+\omega_2$，故 $\chi_1(e_{31},e_{12})=-1$；
- 顶点 $2$：$J_{e_{12},2}=+\omega_2$，$J_{e_{23},2}=+\omega_2$，故 $\chi_2(e_{12},e_{23})=+1$；
- 顶点 $3$：$J_{e_{23},3}=+\omega_2$，$J_{e_{31},3}=+\omega_2$，故 $\chi_3(e_{23},e_{31})=+1$。

连乘得 $\mathcal{H}(C_3)=(-1)(+1)(+1)=-1\ne+1$。由定理 3.3 第 2 项知全局正交复结构不存在。∎

## 4. 纯实载体上的算子三轴纯度球面与秩二平面极值态

**定义 4.1（实二分支内生块分解与实纯度亏格算子）。** 设 $(V_0,g_0)$ 为配备正交复结构 $J_0$ 的非零实内积空间（$\dim_{\mathbb{R}}V_0=2d$，$d\ge1$），记 $J_0$-相容实对称空间为 $\operatorname{Sym}_{J_0}(V_0)=\{M\in\operatorname{Sym}(V_0,g_0):[M,J_0]=0\}$。在二分支实载体 $V=\mathbb{R}^2\otimes_{\mathbb{R}}V_0$（赋予乘积内积 $g=g_{\mathbb{R}^2}\otimes g_0$）上，配备标准锐三轴实读出生成元

$$
A_1=\sigma_x\otimes I_{V_0},\qquad A_2=-\varepsilon\otimes J_0,\qquad A_3=\sigma_z\otimes I_{V_0},\qquad
\varepsilon=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

由 $\varepsilon^{\mathsf T}=-\varepsilon$ 与 $J_0^{\mathsf T}=-J_0$ 知 $A_1,A_2,A_3\in\operatorname{Sym}(V,g)$ 两两反对易且平方为 $I_V$，其内生正交复结构为

$$
J=A_1A_2A_3=(-\sigma_x\varepsilon\sigma_z)\otimes J_0=I_2\otimes J_0.
$$

对任意满足 $[R_{\mathbb{R}},J]=0$ 的实对称算子 $R_{\mathbb{R}}\in\operatorname{Sym}_J(V)$，定义其在二维分支因子 $\mathbb{R}^2$ 上的四个内生轴偏迹块算子 $S_{\mathbb{R}},X_{\mathbb{R}},Y_{\mathbb{R}},Z_{\mathbb{R}}\in\operatorname{End}_{\mathbb{R}}(V_0)$：

$$
S_{\mathbb{R}}=\operatorname{Tr}_{\mathbb{R}^2}(R_{\mathbb{R}}),\quad
X_{\mathbb{R}}=\operatorname{Tr}_{\mathbb{R}^2}(A_1R_{\mathbb{R}}),\quad
Y_{\mathbb{R}}=\operatorname{Tr}_{\mathbb{R}^2}(A_2R_{\mathbb{R}}),\quad
Z_{\mathbb{R}}=\operatorname{Tr}_{\mathbb{R}^2}(A_3R_{\mathbb{R}}),
$$

其中偏迹 $\operatorname{Tr}_{\mathbb{R}^2}:\operatorname{End}_{\mathbb{R}}(\mathbb{R}^2\otimes_{\mathbb{R}}V_0)\to\operatorname{End}_{\mathbb{R}}(V_0)$ 由 $\operatorname{Tr}_{\mathbb{R}^2}(B\otimes M)=\operatorname{Tr}_{\mathbb{R}}(B)M$ 线性扩张。对任意实标量 $m>0$，定义实算子三轴纯度亏格算子为

$$
D_{m,\mathbb{R}}(R_{\mathbb{R}})=mS_{\mathbb{R}}-S_{\mathbb{R}}^2-X_{\mathbb{R}}^2-Y_{\mathbb{R}}^2-Z_{\mathbb{R}}^2.
$$

**定理 4.2（实载体算子三轴纯度球面定理与秩二 $J$-平面极值刻画）。** 在定义 4.1 的设定下，设 $R_{\mathbb{R}}\in\operatorname{Sym}_+(V,g)$ 满足 $[R_{\mathbb{R}},J]=0$ 且实迹归一化为 $\operatorname{Tr}_{\mathbb{R}}(R_{\mathbb{R}})=m>0$。则：

1. **内生块重构与实谱双倍上界**：四个偏迹块均属于 $\operatorname{Sym}_{J_0}(V_0)$，$\operatorname{Tr}_{\mathbb{R}}(S_{\mathbb{R}})=m$，$R_{\mathbb{R}}$ 由四块唯一重构为

$$
R_{\mathbb{R}}=\frac{1}{2}\bigl(I_2\otimes S_{\mathbb{R}}+\sigma_x\otimes X_{\mathbb{R}}-\varepsilon\otimes J_0Y_{\mathbb{R}}+\sigma_z\otimes Z_{\mathbb{R}}\bigr)
=\frac{1}{2}\begin{pmatrix}S_{\mathbb{R}}+Z_{\mathbb{R}}&X_{\mathbb{R}}-J_0Y_{\mathbb{R}}\\X_{\mathbb{R}}+J_0Y_{\mathbb{R}}&S_{\mathbb{R}}-Z_{\mathbb{R}}\end{pmatrix},
$$

且 $R_{\mathbb{R}}$ 的每个实特征值具有偶数重数，从而满足紧实算子不等式

$$
0\preceq R_{\mathbb{R}}\preceq\frac{m}{2}I_V;
$$

2. **实算子三轴纯度恒等式与半正定不等式**：恒有

$$
D_{m,\mathbb{R}}(R_{\mathbb{R}})=2\,\operatorname{Tr}_{\mathbb{R}^2}\!\left(\frac{m}{2}R_{\mathbb{R}}-R_{\mathbb{R}}^2\right)\in\operatorname{Sym}_+(V_0,g_0),
$$

即算子序球面界 $S_{\mathbb{R}}^2+X_{\mathbb{R}}^2+Y_{\mathbb{R}}^2+Z_{\mathbb{R}}^2\preceq mS_{\mathbb{R}}$ 在 $(V_0,g_0)$ 上恒成立；

3. **秩二 $J$-不变平面饱和充要条件**：下列四项条件彼此等价：
   - (a) 算子纯度亏格消失：$D_{m,\mathbb{R}}(R_{\mathbb{R}})=0$；
   - (b) 标量迹亏格消失：$\operatorname{Tr}_{\mathbb{R}}\bigl(D_{m,\mathbb{R}}(R_{\mathbb{R}})\bigr)=0$；
   - (c) 二次投影关系成立：$R_{\mathbb{R}}^2=\frac{m}{2}R_{\mathbb{R}}$；
   - (d) 存在单位向量 $x\in V$（$\|x\|=1$，自动满足 $g(x,Jx)=0$）使得

$$
R_{\mathbb{R}}=\frac{m}{2}\bigl(xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T}\bigr),
$$

其中 $xx^{\mathsf T}\in\operatorname{Sym}_+(V,g)$ 表示 $v\mapsto g(x,v)x$；此时 $\operatorname{rank}_{\mathbb{R}}(R_{\mathbb{R}})=2$（复纯态在 $J$-不变实密度空间中的秩二迹归一化形式见 McKague–Mosca–Gisin 2009 附录 A.1），且单位向量 $x$ 在二维 $J$-不变极值平面 $\operatorname{Ran}R_{\mathbb{R}}=\operatorname{span}_{\mathbb{R}}\{x,Jx\}$ 内的正交旋转 $x\mapsto(\cos\theta)x+(\sin\theta)Jx$ 下唯一确定。

**证明。** 先证第 1 项。将 $R_{\mathbb{R}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^2\otimes_{\mathbb{R}}V_0)$ 按 $M_2(\mathbb{R})$ 的正交基 $\{I_2,\sigma_x,\sigma_z,-\varepsilon\}$ 唯一展开为

$$
R_{\mathbb{R}}=\frac{1}{2}\bigl(I_2\otimes M_0+\sigma_x\otimes M_1+\sigma_z\otimes M_3-\varepsilon\otimes N_2\bigr)\qquad(M_0,M_1,M_3,N_2\in\operatorname{End}_{\mathbb{R}}(V_0)).
$$

条件 $R_{\mathbb{R}}^{\mathsf T}=R_{\mathbb{R}}$ 等价于 $M_0,M_1,M_3\in\operatorname{Sym}(V_0,g_0)$ 且 $N_2^{\mathsf T}=-N_2$（因 $\varepsilon^{\mathsf T}=-\varepsilon$）；条件 $[R_{\mathbb{R}},I_2\otimes J_0]=0$ 等价于 $M_0,M_1,M_3,N_2$ 均与 $J_0$ 对易。令 $Y'=-J_0N_2$，因 $N_2^{\mathsf T}=-N_2$、$J_0^{\mathsf T}=-J_0$ 且 $[N_2,J_0]=0$，有 $(Y')^{\mathsf T}=-N_2^{\mathsf T}J_0^{\mathsf T}=-N_2J_0=Y'$、$[Y',J_0]=0$，且 $J_0Y'=-J_0^2N_2=N_2$。直接按定义计算偏迹（利用 $\operatorname{Tr}_{\mathbb{R}}(I_2)=2$，其余三基矩阵迹为 $0$，且 $(-\varepsilon)^2=-I_2$、$J_0^2=-I_{V_0}$）：

$$
\operatorname{Tr}_{\mathbb{R}^2}(R_{\mathbb{R}})=M_0,\quad
\operatorname{Tr}_{\mathbb{R}^2}(A_1R_{\mathbb{R}})=M_1,\quad
\operatorname{Tr}_{\mathbb{R}^2}(A_2R_{\mathbb{R}})=\frac{1}{2}\operatorname{Tr}_{\mathbb{R}}((-\varepsilon)^2)(-J_0N_2)=Y',\quad
\operatorname{Tr}_{\mathbb{R}^2}(A_3R_{\mathbb{R}})=M_3,
$$

故 $M_0=S_{\mathbb{R}},M_1=X_{\mathbb{R}},Y'=Y_{\mathbb{R}},M_3=Z_{\mathbb{R}}\in\operatorname{Sym}_{J_0}(V_0)$，且 $\operatorname{Tr}_{\mathbb{R}}(S_{\mathbb{R}})=\operatorname{Tr}_{\mathbb{R}}(R_{\mathbb{R}})=m$。对谱上界，因 $R_{\mathbb{R}}\in\operatorname{Sym}_+(V,g)$ 实对称，其特征空间 $E_\lambda=\ker(R_{\mathbb{R}}-\lambda I_V)$ 两两正交直和成 $V$ 且每个 $\lambda\ge0$。由 $[R_{\mathbb{R}},J]=0$ 知 $J(E_\lambda)\subseteq E_\lambda$；若 $E_\lambda\ne\{0\}$，则 $(J|_{E_\lambda})^2=-I_{E_\lambda}$ 给出 $(\det J|_{E_\lambda})^2=(-1)^{\dim_{\mathbb{R}}E_\lambda}\ge0$，故每个实特征空间维数 $\dim_{\mathbb{R}}E_\lambda\in2\mathbb{Z}_{>0}$ 至少为 $2$。因此最大特征值 $\lambda_{\max}$ 满足 $2\lambda_{\max}\le\sum_{\lambda}(\dim_{\mathbb{R}}E_\lambda)\lambda=\operatorname{Tr}_{\mathbb{R}}(R_{\mathbb{R}})=m$，即 $0\preceq R_{\mathbb{R}}\preceq\frac{m}{2}I_V$。

次证第 2 项。将重构公式平方并取 $\mathbb{R}^2$ 偏迹：交叉项中 $I_2\sigma_x,I_2\sigma_z,I_2\varepsilon,\sigma_x\sigma_z,\sigma_x\varepsilon,\sigma_z\varepsilon$ 的实迹全为零，仅四个平方对角项保留实迹：

$$
\operatorname{Tr}_{\mathbb{R}}(I_2^2)=\operatorname{Tr}_{\mathbb{R}}(\sigma_x^2)=\operatorname{Tr}_{\mathbb{R}}(\sigma_z^2)=2,\qquad
\operatorname{Tr}_{\mathbb{R}}((-\varepsilon)^2)=\operatorname{Tr}_{\mathbb{R}}(-I_2)=-2.
$$

而在第四项的 $V_0$ 因子上有 $(J_0Y_{\mathbb{R}})^2=J_0^2Y_{\mathbb{R}}^2=-Y_{\mathbb{R}}^2$（用到 $[J_0,Y_{\mathbb{R}}]=0$），与二维因子负迹 $(-2)$ 相乘恰得正号 $+2Y_{\mathbb{R}}^2$。因此

$$
\operatorname{Tr}_{\mathbb{R}^2}(R_{\mathbb{R}}^2)=\frac{1}{4}\bigl(2S_{\mathbb{R}}^2+2X_{\mathbb{R}}^2+(-2)(-Y_{\mathbb{R}}^2)+2Z_{\mathbb{R}}^2\bigr)
=\frac{1}{2}\bigl(S_{\mathbb{R}}^2+X_{\mathbb{R}}^2+Y_{\mathbb{R}}^2+Z_{\mathbb{R}}^2\bigr).
$$

用 $\frac{m}{2}\operatorname{Tr}_{\mathbb{R}^2}(R_{\mathbb{R}})=\frac{m}{2}S_{\mathbb{R}}$ 减去上式再乘 $2$，即得精确恒等式 $D_{m,\mathbb{R}}(R_{\mathbb{R}})=2\operatorname{Tr}_{\mathbb{R}^2}(\frac{m}{2}R_{\mathbb{R}}-R_{\mathbb{R}}^2)$。由第 1 项 $0\preceq R_{\mathbb{R}}\preceq\frac{m}{2}I_V$ 知在谱分解下每个特征值满足 $\frac{m}{2}\lambda-\lambda^2=\lambda(\frac{m}{2}-\lambda)\ge0$，故 $Q=\frac{m}{2}R_{\mathbb{R}}-R_{\mathbb{R}}^2\in\operatorname{Sym}_+(V,g)$。对任意 $w\in V_0$，记 $\mathbb{R}^2$ 的标准基为 $\{b_1,b_2\}$，则 $g_0(w,\operatorname{Tr}_{\mathbb{R}^2}(Q)w)=g(b_1\otimes w,Q(b_1\otimes w))+g(b_2\otimes w,Q(b_2\otimes w))\ge0$，故 $D_{m,\mathbb{R}}(R_{\mathbb{R}})\in\operatorname{Sym}_+(V_0,g_0)$。

最后证第 3 项。(a)$\Rightarrow$(b) 平凡。若 (b) 成立，则 $0=\frac{1}{2}\operatorname{Tr}_{\mathbb{R}}(D_{m,\mathbb{R}}(R_{\mathbb{R}}))=\operatorname{Tr}_{\mathbb{R}}(Q)$，而 $Q\in\operatorname{Sym}_+(V,g)$，半正定算子迹为零当且仅当该算子为零，故 $Q=\frac{m}{2}R_{\mathbb{R}}-R_{\mathbb{R}}^2=0$，得 (c)。若 (c) 成立，则 $Q=0$，代入第 2 项恒等式立得 (a)；同时 $\frac{2}{m}R_{\mathbb{R}}$ 为非零实正交投影算子，其实迹（即实秩）为 $\operatorname{Tr}_{\mathbb{R}}(\frac{2}{m}R_{\mathbb{R}})=\frac{2}{m}\cdot m=2$，且与 $J$ 对易。任取 $\operatorname{Ran}R_{\mathbb{R}}$ 中的单位向量 $x\in V$（$\|x\|=1$），则 $Jx\in\operatorname{Ran}R_{\mathbb{R}}$ 亦为单位向量且 $g(x,Jx)=0$，故 $\{x,Jx\}$ 构成二维值域 $\operatorname{Ran}R_{\mathbb{R}}$ 的 $g$-标准正交基，到 $\operatorname{Ran}R_{\mathbb{R}}$ 的正交投影即为 $xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T}$，乘以 $\frac{m}{2}$ 得 (d)。反之，若 (d) 成立，因 $\{x,Jx\}$ 标准正交，直接验证 $P_x=xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T}$ 满足 $P_x^2=P_x=P_x^{\mathsf T}$、$JP_x=(Jx)x^{\mathsf T}-x(Jx)^{\mathsf T}=P_xJ$、$\operatorname{Tr}_{\mathbb{R}}(P_x)=2$，故 $R_{\mathbb{R}}=\frac{m}{2}P_x$ 满足 $R_{\mathbb{R}}^2=\frac{m}{2}R_{\mathbb{R}}$，得 (c)；同一二维子空间内的任意单位向量皆形如 $(\cos\theta)x+(\sin\theta)Jx$。∎

**命题 4.3（实载体纯度球面的两条紧失效边界：秩一实投影越界与二轴读出盲核）。** 在定义 4.1 的实载体 $V=\mathbb{R}^2\otimes_{\mathbb{R}}V_0$ 上：

1. **秩一实正算子的手征不相容性**：对任意单位向量 $x\in V$（$\|x\|=1$）与 $m>0$，秩一实半正定算子 $R_1=m\,xx^{\mathsf T}$ 满足 $\operatorname{Tr}_{\mathbb{R}}(R_1)=m$，但其与内生复结构 $J$ 的换位子恒非零：

$$
[R_1,J]=-m\bigl(x(Jx)^{\mathsf T}+(Jx)x^{\mathsf T}\bigr)\ne0,\qquad \operatorname{Tr}_{\mathbb{R}}\bigl([R_1,J]^{\mathsf T}[R_1,J]\bigr)=2m^2>0,
$$

且超出定理 4.2 的特征值上界（$\lambda_{\max}(R_1)=m>\frac{m}{2}$）；对其实施 $J$-不变投影 $\frac{1}{2}(R_1-JR_1J)$ 则恰坍缩回定理 4.2 第 3(d) 项的秩二平面态；

2. **删去手征第二轴后的纯态—最大混合态不可分性**：在最小维数 $V_0=\mathbb{R}^2$（$V=\mathbb{R}^4$，$J_0=\omega_2$）上，若仅保留实二轴读出 $(A_1,A_3)$ 而删去含 $J_0$ 的第二轴 $A_2=-\varepsilon\otimes\omega_2$，则秩二极值纯态 $R_*=\frac{m}{4}(I_4+A_2)$ 与秩四最大混合态 $R_{\mathrm{mix}}=\frac{m}{4}I_4$ 给出完全相同的二轴偏迹块 $(S_{\mathbb{R}},X_{\mathbb{R}},Z_{\mathbb{R}})=(\frac{m}{2}I_2,0,0)$ 及严格正的二轴残差 $mS_{\mathbb{R}}-S_{\mathbb{R}}^2-X_{\mathbb{R}}^2-Z_{\mathbb{R}}^2=\frac{m^2}{4}I_2\succ0$，而三轴亏格精确区分二者：$D_{m,\mathbb{R}}(R_*)=0\ne\frac{m^2}{4}I_2=D_{m,\mathbb{R}}(R_{\mathrm{mix}})$。

**证明。** 对第 1 项，任取 $v\in V$，利用 $J^{\mathsf T}=-J$ 计算

$$
[xx^{\mathsf T},J]v=x\,g(x,Jv)-(Jx)\,g(x,v)=-x\,g(Jx,v)-(Jx)\,g(x,v)=-\bigl(x(Jx)^{\mathsf T}+(Jx)x^{\mathsf T}\bigr)v.
$$

因 $\|x\|=\|Jx\|=1$ 且 $g(x,Jx)=0$，算子 $x(Jx)^{\mathsf T}+(Jx)x^{\mathsf T}$ 在正交对 $\{x,Jx\}$ 上互换二基向量、在正交补上为零，故其平方在 $\operatorname{span}_{\mathbb{R}}\{x,Jx\}$ 上为恒等算子，实 Frobenius 范数平方为 $2m^2>0$。同时 $(Jxx^{\mathsf T}J)v=Jx\,g(x,Jv)=-Jx\,g(Jx,v)=-(Jx)(Jx)^{\mathsf T}v$，故 $\frac{1}{2}(R_1-JR_1J)=\frac{m}{2}(xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T})$。

对第 2 项，因 $A_2^{\mathsf T}=A_2$、$A_2^2=I_4$、$[A_2,J]=0$ 且 $\operatorname{Tr}_{\mathbb{R}}(A_2)=0$，算子 $\frac{1}{2}(I_4+A_2)$ 为实秩 $2$ 的 $J$-不变正交投影，故 $R_*=\frac{m}{4}(I_4+A_2)\in\operatorname{Sym}_+(\mathbb{R}^4)$ 满足 $\operatorname{Tr}_{\mathbb{R}}(R_*)=m$ 且 $R_*^2=\frac{m}{2}R_*$，由定理 4.2 知 $D_{m,\mathbb{R}}(R_*)=0$。计算偏迹：对 $R_*$ 与 $R_{\mathrm{mix}}$ 均有 $S_{\mathbb{R}}=\frac{m}{2}I_2$、$X_{\mathbb{R}}=Z_{\mathbb{R}}=0$（因 $\operatorname{Tr}_{\mathbb{R}^2}(A_1A_2)=\operatorname{Tr}_{\mathbb{R}^2}(A_3A_2)=0$），二者的二轴残差同为 $m(\frac{m}{2}I_2)-(\frac{m}{2}I_2)^2=\frac{m^2}{4}I_2\succ0$；唯独在第二轴上有 $Y_{\mathbb{R}}(R_*)=\operatorname{Tr}_{\mathbb{R}^2}(\frac{m}{4}A_2^2)=\frac{m}{2}I_2$ 而 $Y_{\mathbb{R}}(R_{\mathrm{mix}})=0$，从而三轴亏格 $D_{m,\mathbb{R}}$ 精确分离纯态与混合态。∎

## 5. 初等锐 $k$ 轴实二元切分的相位内生性与双切分复合选型定理

**定义 5.1（初等锐 $k$ 轴实二元切分）。** 设 $k\ge1$ 为正整数。非零有限维实内积空间 $(V,g)$ 上的锐 $k$ 轴实二元切分是指三元组 $(V,g,A)$，其中实线性映射 $A:\mathbb{R}^k\to\operatorname{Sym}(V,g)$ 满足：

1. **球面锐二元律**：对一切 $u\in\mathbb{R}^k$ 有 $A(u)^2=\|u\|^2I_V$，且对非零 $u\ne0$ 两个锐特征分支 $V_{\pm}(u)=\ker(A(u)\mp\|u\|I_V)$ 均非零；
2. **可观测量不可约性**：由全部轴读出生成的实结合子代数 $\mathcal{A}=\operatorname{Alg}_{\mathbb{R}}(A(\mathbb{R}^k))\subseteq\operatorname{End}_{\mathbb{R}}(V)$ 在 $V$ 上不可约作用，记其换位子代数为 $\mathcal{D}=\mathcal{A}'=\{q\in\operatorname{End}_{\mathbb{R}}(V):[q,M]=0\ (\forall M\in\mathcal{A})\}$。

称 $(V,g,A)$ 为**初等**锐 $k$ 轴实二元切分，若此外满足：

3. **分支极小无简并性**：对每个单位方向 $u\in S^{k-1}$，正负分支 $V_+(u)$ 与 $V_-(u)$ 作为左 $\mathcal{D}$-模均为极小非零模（即不含真非零 $\mathcal{D}$-不变子空间，等价地 $\dim_{\mathcal{D}}V_+(u)=\dim_{\mathcal{D}}V_-(u)=1$）。

对任意实子空间 $W$ 上的换位子子代数 $\mathcal{C}\subseteq\operatorname{End}_{\mathbb{R}}(W)$，记 $\mathcal{C}$-相容实对称态空间为 $\operatorname{Sym}_{\mathcal{C}}(W)=\{S\in\operatorname{Sym}(W):[S,q]=0\ (\forall q\in\mathcal{C})\}$。

**引理 5.2（体积元奇偶律与初等轴数四值分类）。** 设 $(V,g,A)$ 为定义 5.1 中满足条件 1–2 的锐 $k$ 轴实二元切分，取 $\mathbb{R}^k$ 标准正交基下 $A_i=A(e_i)$（$1\le i\le k$），定义体积元算子 $\Omega_k=A_1A_2\cdots A_k\in\mathcal{A}$。则：

1. **体积元奇偶与中心判据**：$\{A_i,A_j\}=2\delta_{ij}I_V$，且

$$
\Omega_k^{\mathsf T}=(-1)^{k(k-1)/2}\Omega_k,\qquad
\Omega_k^2=(-1)^{k(k-1)/2}I_V,\qquad
A_i\Omega_k=(-1)^{k-1}\Omega_kA_i\quad(1\le i\le k).
$$

特别地，$\Omega_k$ 属于中心 $Z(\mathcal{A})$ 且构成 $(V,g)$ 上的正交复结构（$\Omega_k^{\mathsf T}=-\Omega_k$，$\Omega_k^2=-I_V$）当且仅当 $k\equiv3\pmod4$；当 $k$ 为偶数或 $k\equiv1\pmod4$ 时，中心恒坍缩为标量 $Z(\mathcal{A})=\mathbb{R}I_V$；

2. **初等切分的轴数紧分类**：锐 $k$ 轴实二元切分 $(V,g,A)$ 满足定义 5.1 条件 3（初等性）当且仅当 $k\in\{2,3,4,5\}$。四类初等切分的三元组 $(k,\mathcal{D},\dim_{\mathbb{R}}V)$ 及单切分对称态维数 $\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)$ 精确穷尽如下：
   - $k=2$：$\mathcal{D}\cong\mathbb{R}$，$\dim_{\mathbb{R}}V=2$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)=3$；
   - $k=3$：$\mathcal{D}=Z(\mathcal{A})\cong\mathbb{C}$，$\dim_{\mathbb{R}}V=4$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)=4$；
   - $k=4,5$：$\mathcal{D}\cong\mathbb{H}$，$\dim_{\mathbb{R}}V=8$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)=6$；其中任意初等 $k=4$ 切分的体积元 $A_5=\Omega_4=A_1A_2A_3A_4\in\mathcal{A}$ 自动构成与 $A_1,\ldots,A_4$ 两两反对易的第五个实对称对合轴，从而在同一个可观测量代数 $\mathcal{A}$ 内扩张为初等 $k=5$ 切分。

**证明。** 对第 1 项，极化 $A(u+w)^2=\|u+w\|^2I_V$ 得 $\{A_i,A_j\}=2\delta_{ij}I_V$。倒序重排 $A_k\cdots A_1$ 为 $A_1\cdots A_k$ 需要 $\frac{k(k-1)}{2}$ 次不同轴邻位交换，故 $\Omega_k^{\mathsf T}=A_k\cdots A_1=(-1)^{k(k-1)/2}\Omega_k$；又 $\Omega_k\Omega_k^{\mathsf T}=A_1\cdots A_kA_k\cdots A_1=I_V$，故 $\Omega_k^2=(-1)^{k(k-1)/2}\Omega_k\Omega_k^{\mathsf T}=(-1)^{k(k-1)/2}I_V$。将 $A_i$ 穿过 $A_1\cdots A_k$ 时与其余 $k-1$ 个因子反对易、与自身对易，得 $A_i\Omega_k=(-1)^{k-1}\Omega_kA_i$。按模 $2$ 基 $\{A_{i_1}\cdots A_{i_r}:1\le i_1<\cdots<i_r\le k\}$ 检视与全部 $A_i$ 的对易性：当 $k$ 为偶数时，任意非空乘积 $A_{i_1}\cdots A_{i_r}$ 若 $r$ 为奇数则与不在指标集外（或当 $r<k$ 时选不在其中的 $A_j$，当 $r=k$ 时与一切 $A_j$）反对易，若 $r$ 为偶数（$r\ge2$）则与属于指标集的任一 $A_{i_1}$ 反对易，故 $Z(\mathcal{A})=\mathbb{R}I_V$；当 $k$ 为奇数时，仅 $r=0$（$I_V$）与 $r=k$（$\Omega_k$）与全部 $A_i$ 对易，故 $Z(\mathcal{A})=\operatorname{span}_{\mathbb{R}}\{I_V,\Omega_k\}$。若 $k\equiv1\pmod4$，则 $\frac{k(k-1)}{2}$ 为偶数，$\Omega_k^{\mathsf T}=\Omega_k$ 且 $\Omega_k^2=I_V$；若 $\Omega_k\ne\pm I_V$，则非零中心正交投影 $\frac{1}{2}(I_V\pm\Omega_k)$ 将 $V$ 分解为两个非零 $\mathcal{A}$-不变子空间，与不可约性矛盾，故 $\Omega_k\in\{\pm I_V\}$ 且 $Z(\mathcal{A})=\mathbb{R}I_V$。唯当 $k\equiv3\pmod4$ 时，$\frac{k(k-1)}{2}$ 为奇数，$\Omega_k\in Z(\mathcal{A})$ 满足 $\Omega_k^{\mathsf T}=-\Omega_k$ 与 $\Omega_k^2=-I_V$。

对第 2 项，先排除 $k=1$：若 $k=1$，条件 1 给出非零正负特征空间 $V_+(e_1)$ 与 $V_-(e_1)$，而 $\mathcal{A}=\operatorname{span}_{\mathbb{R}}\{I_V,A_1\}$ 保持二者不变，与条件 2 的不可约性矛盾，故 $k\ge2$。对 $k\ge2$，任取 $j\ne i$ 有 $A_i=-A_jA_iA_j$，取实迹得 $\operatorname{Tr}_{\mathbb{R}}(A_i)=0$；又 $\operatorname{Tr}_{\mathbb{R}}(A_iA_j)=\frac{1}{2}\operatorname{Tr}_{\mathbb{R}}(\{A_i,A_j\})=\delta_{ij}\dim_{\mathbb{R}}V$，故 $A_1,\ldots,A_k$ 是无迹实对称子空间 $\mathcal{A}_{\mathrm{sym},0}=\{M\in\mathcal{A}:M^{\mathsf T}=M,\ \operatorname{Tr}_{\mathbb{R}}(M)=0\}$ 中两两正交的非零元，从而 $k\le\dim_{\mathbb{R}}\mathcal{A}_{\mathrm{sym},0}$。

由 Schur 引理、Frobenius 实可除代数定理（Frobenius 1878）及实转置封闭不可约代数的双换位子定理（[`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 定理 A.1），$\mathcal{D}=\mathcal{A}'$ 是转置不变有限维实可除代数，作为实代数同构于 $\mathbb{R},\mathbb{C},\mathbb{H}$ 之一（记 $\delta=\dim_{\mathbb{R}}\mathcal{D}\in\{1,2,4\}$），且 $\mathcal{A}=\operatorname{End}_{\mathcal{D}}(V)$。对任意 $q\in\mathcal{D}$，其实对称部分 $q_+=\frac{1}{2}(q+q^{\mathsf T})\in\mathcal{D}$ 在 $V$ 上有实特征值 $\lambda\in\mathbb{R}$，因可除代数中非零元在 $V$ 上可逆，必有 $q_+=\lambda I_V$；同理反对称部分 $q_-=\frac{1}{2}(q-q^{\mathsf T})\in\mathcal{D}$ 满足 $q_-^2=-q_-^{\mathsf T}q_-\preceq0$，故 $q_-^2=-\mu^2I_V$（$\mu\ge0$），这表明实转置 $q\mapsto q^{\mathsf T}$ 在 $\mathcal{D}$ 上恰为标准范数共轭 $\bar{q}=\lambda I_V-q_-$，且对一切 $x\in V$ 与反对称元 $q_-$ 有 $g(x,q_-x)=0$。

设条件 3 成立：$\dim_{\mathcal{D}}V_+(e_1)=\dim_{\mathcal{D}}V_-(e_1)=1$，从而 $\dim_{\mathcal{D}}V=2$，$\dim_{\mathbb{R}}V=2\delta$。分别在相互正交的特征空间 $V_+(e_1)$ 与 $V_-(e_1)$ 中任取 $g$-单位向量 $v_1,v_2$，则 $V=\mathcal{D}v_1\oplus\mathcal{D}v_2$，且对一切 $q_1,q_2\in\mathcal{D}$ 与 $r,s\in\{1,2\}$ 有 $g(q_1v_r,q_2v_s)=\delta_{rs}\operatorname{Re}(\bar{q}_1q_2)$。任意左 $\mathcal{D}$-线性算子 $T\in\mathcal{A}=\operatorname{End}_{\mathcal{D}}(V)$ 由 $T(v_s)=\sum_{r=1}^2 m_{rs}v_r$（$m_{rs}\in\mathcal{D}$）唯一表示；利用 $\mathbb{R},\mathbb{C},\mathbb{H}$ 上恒成立的实部循环律 $\operatorname{Re}(ab)=\operatorname{Re}(ba)$，有

$$
g\bigl(q_1v_r,T(q_2v_s)\bigr)=\operatorname{Re}(\bar{q}_1q_2m_{rs})=\operatorname{Re}(\bar{m}_{rs}\bar{q}_1q_2)=\operatorname{Re}\bigl(\overline{(q_1\bar{m}_{rs})}q_2\bigr),
$$

故 $T^{\mathsf T}=T$ 当且仅当 $m_{11},m_{22}\in\mathbb{R}$ 且 $m_{21}=\bar{m}_{12}\in\mathcal{D}$。因 $\operatorname{Sym}_{\mathcal{D}}(V)$ 与 $\mathcal{A}\cap\operatorname{Sym}(V,g)$ 在此处（$\mathcal{A}=\mathcal{D}'$）完全重合，得

$$
\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)=2+\delta,\qquad \dim_{\mathbb{R}}\mathcal{A}_{\mathrm{sym},0}=1+\delta,\qquad \dim_{\mathbb{R}}\mathcal{A}=4\delta.
$$

逐类核对：
- 若 $\mathcal{D}\cong\mathbb{R}$（$\delta=1$）：$2\le k\le1+1=2$，故 $k=2$，$\dim_{\mathbb{R}}V=2$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{R}}(V)=3$（由 $(\sigma_x,\sigma_z)$ 在 $\mathbb{R}^2$ 上实现）；
- 若 $\mathcal{D}\cong\mathbb{C}$（$\delta=2$）：$k\le1+2=3$，而 $k=2$ 生成的代数维数至多为 $2^2=4<8=4\delta$，故必有 $k=3$，$\dim_{\mathbb{R}}V=4$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(V)=4$，且由第 1 项知 $Z(\mathcal{A})=\operatorname{span}_{\mathbb{R}}\{I_4,\Omega_3\}\cong\mathbb{C}$ 恰等于二维换位子 $\mathcal{D}$（由命题 2.4 中的 $(E_1,E_2,E_3)$ 在 $\mathbb{R}^4$ 上实现）；
- 若 $\mathcal{D}\cong\mathbb{H}$（$\delta=4$）：$k\le1+4=5$，而 $\dim_{\mathbb{R}}\mathcal{A}=16>2^3=8$ 排除 $k\le3$，故 $k\in\{4,5\}$，$\dim_{\mathbb{R}}V=8$，$\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{H}}(V)=6$。当 $k=4$ 时，由第 1 项知 $A_5=\Omega_4\in\mathcal{A}$ 满足 $A_5^{\mathsf T}=(-1)^6A_5=A_5$、$A_5^2=I_V$ 且 $A_iA_5=-A_5A_i$（$1\le i\le4$），自动给出第五个反对易实对称轴（显式八维实现见命题 5.4）。反之，若 $k\ge6$，因一切情形均有 $\delta\le4$，故 $k>1+\delta$ 迫使 $\dim_{\mathcal{D}}V>2$，分支不可能是极小的一维 $\mathcal{D}$-模。∎

**定理 5.3（初等锐二元切分的相位内生生成与双切分复合选型定理）。** 设 $(V,g,A)$ 是定义 5.1 中的初等锐 $k$ 轴实二元切分（故 $k\in\{2,3,4,5\}$），并取其两个同构副本 $(V_A,g_A,A_A)$ 与 $(V_B,g_B,A_B)$ 构成实欧氏张量复合空间 $(V_A\otimes_{\mathbb{R}}V_B,g_A\otimes g_B)$ 及联合局部可观测量代数 $\mathcal{A}_{AB}=\mathcal{A}_A\otimes_{\mathbb{R}}\mathcal{A}_B\subseteq\operatorname{End}_{\mathbb{R}}(V_A\otimes_{\mathbb{R}}V_B)$。下列三项条件彼此等价，且每一项均唯一选出轴数 $k=3$、复可除换位子类型 $\mathcal{D}\cong\mathbb{C}$ 与四维实载体 $\dim_{\mathbb{R}}V=4$：

1. **相位生成元的可观测量内生性**：可观测量代数 $\mathcal{A}$ 自身包含一个与 $\mathcal{A}$ 对易的正交复结构 $J\in Z(\mathcal{A})$（$J^{\mathsf T}=-J$，$J^2=-I_V$；等价地，$Z(\mathcal{A})\supsetneq\mathbb{R}I_V$）；
2. **双切分中心内生扇区分解**：复合可观测量代数的中心 $Z(\mathcal{A}_A\otimes_{\mathbb{R}}\mathcal{A}_B)$ 含有非平凡正交投影 $P$（$0\ne P\ne I_{V_A\otimes V_B}$，$P^2=P=P^{\mathsf T}$）；
3. **双切分换位子保型与局部对称乘积层析闭合**：存在非零 $\mathcal{A}_{AB}$-不变子空间 $W\subseteq V_A\otimes_{\mathbb{R}}V_B$，使得限制代数 $\mathcal{A}_W=\mathcal{A}_{AB}|_W$ 在 $W$ 上的换位子 $\mathcal{D}_W=\mathcal{A}_W'\subseteq\operatorname{End}_{\mathbb{R}}(W)$ 作为实代数同构于单切分换位子 $\mathcal{D}$，并且 $\mathcal{D}_W$-相容对称态空间满足局部乘积维数恒等式（Hardy 2001 局部层析判据在实切分子空间上的算子形式）：

$$
\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}_W}(W)=\bigl(\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)\bigr)^2.
$$

**证明。** 由引理 5.2 第 2 项，只需在穷尽初等切分的四个值 $k\in\{2,3,4,5\}$ 上逐一检验三项条件。

先检验条件 1：由引理 5.2 第 1 项，在 $\{2,3,4,5\}$ 中仅 $k=3\equiv3\pmod4$ 满足 $Z(\mathcal{A})=\operatorname{span}_{\mathbb{R}}\{I_4,\Omega_3\}\supsetneq\mathbb{R}I_V$（其中 $J=\Omega_3$ 为中心正交复结构）；对 $k=2,4,5$ 均有 $Z(\mathcal{A})=\mathbb{R}I_V$。故条件 1 成立当且仅当 $k=3$。

次检验条件 2：对域 $\mathbb{R}$ 上的有限维结合代数，有标准线性代数恒等式 $Z(\mathcal{A}_A\otimes_{\mathbb{R}}\mathcal{A}_B)=Z(\mathcal{A}_A)\otimes_{\mathbb{R}}Z(\mathcal{A}_B)$（在 $\mathcal{A}_B$ 的一组实基 $\{b_j\}$ 下，$\sum_j x_j\otimes b_j$ 与一切 $a\otimes I_{V_B}$ 对易当且仅当每个 $x_j\in Z(\mathcal{A}_A)$，再对第一因子对称施用同一论证即得）。当 $k\in\{2,4,5\}$ 时，$Z(\mathcal{A}_A)=\mathbb{R}I_{V_A}$、$Z(\mathcal{A}_B)=\mathbb{R}I_{V_B}$，故 $Z(\mathcal{A}_{AB})=\mathbb{R}I_{V_A\otimes V_B}$ 为一维实标量，不含任何非平凡投影。当 $k=3$ 时，$J_A=\Omega_{3,A}\in Z(\mathcal{A}_A)$ 与 $J_B=\Omega_{3,B}\in Z(\mathcal{A}_B)$ 满足 $(J_A\otimes J_B)^{\mathsf T}=(-J_A)\otimes(-J_B)=J_A\otimes J_B$ 且 $(J_A\otimes J_B)^2=(-I_4)\otimes(-I_4)=I_{16}$，于是中心元素（对应 $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{C}\cong\mathbb{C}\oplus\mathbb{C}$，Dyson 1962；亦见 [`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 定理 7.2）

$$
P_{\mp}=\frac{1}{2}\bigl(I_{16}\mp J_A\otimes J_B\bigr)\in Z(\mathcal{A}_A\otimes_{\mathbb{R}}\mathcal{A}_B)
$$

恰为满足 $P_-+P_+=I_{16}$、$P_-P_+=0$、$\operatorname{rank}_{\mathbb{R}}P_{\mp}=8$ 的非平凡正交中心投影。故条件 2 成立当且仅当 $k=3$。

最后检验条件 3：
- 当 $k=2$（$\mathcal{D}=\mathbb{R}$，$V=\mathbb{R}^2$）时，$\mathcal{A}_{AB}\cong M_2(\mathbb{R})\otimes_{\mathbb{R}}M_2(\mathbb{R})\cong M_4(\mathbb{R})$ 在 $V_A\otimes_{\mathbb{R}}V_B\cong\mathbb{R}^4$ 上不可约，唯一非零不变子空间为 $W=\mathbb{R}^4$。其上 $\mathcal{D}_W=\mathbb{R}I_4\cong\mathbb{R}$，但对称空间维数为

$$
\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{R}}(\mathbb{R}^4)=\frac{4\times5}{2}=10\ne9=3^2=\bigl(\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{R}}(\mathbb{R}^2)\bigr)^2,
$$

条件 3 不成立。
- 当 $k\in\{4,5\}$（$\mathcal{D}\cong\mathbb{H}$，$V\cong\mathbb{R}^8$）时，单切分可观测量代数为中心单实代数 $\mathcal{A}\cong M_2(\mathbb{H})$（实维数 $16$）。由经典四元数实张量同构 $\mathbb{H}\otimes_{\mathbb{R}}\mathbb{H}\cong M_4(\mathbb{R})$（Dyson 1962；Baez 2012），有

$$
\mathcal{A}_{AB}\cong M_2(\mathbb{H})\otimes_{\mathbb{R}}M_2(\mathbb{H})\cong M_4(\mathbb{H}\otimes_{\mathbb{R}}\mathbb{H})\cong M_{16}(\mathbb{R}),
$$

它在 $\mathbb{R}^8\otimes_{\mathbb{R}}\mathbb{R}^8\cong\mathbb{R}^{64}$ 上同构于不可约模 $\mathbb{R}^{16}$ 的四重直和 $(\mathbb{R}^{16})^{\oplus4}$。因此，$\mathbb{R}^{64}$ 的任意非零 $\mathcal{A}_{AB}$-不变子空间 $W$ 均同构于 $(\mathbb{R}^{16})^{\oplus r}$（其中重数 $r\in\{1,2,3,4\}$），限制代数 $\mathcal{A}_W\cong M_{16}(\mathbb{R})$ 在 $W$ 上的换位子为 $\mathcal{D}_W\cong M_r(\mathbb{R})$：当 $r=1$ 时 $\mathcal{D}_W\cong\mathbb{R}\not\cong\mathbb{H}$（且 $\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{R}}(\mathbb{R}^{16})=\frac{16\times17}{2}=136\ne36=6^2$）；当 $r\in\{2,3,4\}$ 时 $M_r(\mathbb{R})$ 含非零零因子，根本不是可除代数，同样有 $\mathcal{D}_W\not\cong\mathbb{H}$。故对一切非零不变子空间 $W$，条件 3 均不成立。
- 当 $k=3$（$\mathcal{D}\cong\mathbb{C}$，$V\cong\mathbb{R}^4$）时，取对齐中心投影的值域 $W=\operatorname{Ran}P_-=\ker(J_A\otimes I_4-I_4\otimes J_B)$（$\dim_{\mathbb{R}}W=8$）。在 $W$ 上 $J_W=(J_A\otimes I_4)|_W=(I_4\otimes J_B)|_W$ 构成正交复结构，赋予 $W$ 四维复内积空间结构 $W\cong\mathbb{C}^4$；由 $\mathcal{A}_A=\operatorname{End}_{\mathbb{C}}(V_A)\cong M_2(\mathbb{C})$ 与 $\mathcal{A}_B=\operatorname{End}_{\mathbb{C}}(V_B)\cong M_2(\mathbb{C})$ 知 $\mathcal{A}_W=\operatorname{End}_{\mathbb{C}}(W)\cong M_4(\mathbb{C})$ 在 $W$ 上不可约，其换位子为 $\mathcal{D}_W=\operatorname{span}_{\mathbb{R}}\{I_W,J_W\}\cong\mathbb{C}\cong\mathcal{D}$。如同引理 5.2 第 2 项对复厄米矩阵的实维数计算，$n=4$ 维复空间上 $\mathcal{D}_W$-相容实对称空间维数为

$$
\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(W)=4+\frac{4\times3}{2}\cdot2=16=4^2=\bigl(\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(V)\bigr)^2,
$$

条件 3 精确成立。三项条件遂彼此等价且唯一选出 $k=3$。∎

**命题 5.4（五轴四元数切分的相位外生性显式实现与七轴非初等复中心反例）。**

1. **五轴四元数切分的可观测量—相位不交性**：在 $V=\mathbb{R}^8=\mathbb{R}^2\otimes\mathbb{R}^2\otimes\mathbb{R}^2$ 上，令

$$
\begin{aligned}
B_1&=\sigma_x\otimes I_2\otimes I_2,&
B_2&=\sigma_z\otimes\sigma_x\otimes I_2,&
B_3&=\sigma_z\otimes\omega_2\otimes\omega_2,\\
B_4&=\sigma_z\otimes\sigma_z\otimes I_2,&
B_5&=B_1B_2B_3B_4=\omega_2\otimes I_2\otimes\omega_2,
\end{aligned}
$$

则 $(B_1,\ldots,B_5)$ 生成定义 5.1 中的初等锐五轴实二元切分，其换位子 $\mathcal{D}_5=\operatorname{span}_{\mathbb{R}}\{I_8,Q_1,Q_2,Q_3\}\cong\mathbb{H}$ 由三个反对称四元数虚单位

$$
Q_1=I_2\otimes I_2\otimes\omega_2,\qquad
Q_2=\sigma_x\otimes\omega_2\otimes\sigma_z,\qquad
Q_3=\sigma_x\otimes\omega_2\otimes\sigma_x
$$

（满足 $Q_1^2=Q_2^2=Q_3^2=-I_8$，$Q_1Q_2=Q_3=-Q_2Q_1$）给出，包含二维球面族的正交复结构 $\{c_1Q_1+c_2Q_2+c_3Q_3:\sum_{i=1}^3c_i^2=1\}$；但体积元 $\Omega_5=B_1B_2B_3B_4B_5=+I_8$，且 $\mathcal{A}_5\cap\mathcal{D}_5=\mathbb{R}I_8$，即 $\mathcal{D}_5$ 中没有任何正交复结构属于可观测量代数 $\mathcal{A}_5$；

2. **删去分支极小初等性假设后的高维反例**：在 $V=\mathbb{R}^{16}=(\mathbb{R}^2)^{\otimes4}$ 上，存在满足定义 5.1 条件 1–2（但不满足条件 3 初等性）的不可约锐七轴实二元切分 $(V,g,A^{(7)})$，使得定理 5.3 的三项条件（内生复中心 $Z(\mathcal{A}^{(7)})=\operatorname{span}_{\mathbb{R}}\{I_{16},\Omega_7\}\cong\mathbb{C}$、双切分中心正交扇区投影 $P_{\mp}=\frac{1}{2}(I_{256}\mp\Omega_{7,A}\otimes\Omega_{7,B})$，以及对齐扇区 $W\cong\mathbb{C}^{64}$ 上的复换位子保型与乘积层析维数 $64^2=(8^2)^2=4096$）全部成立，但每个方向 $u\in S^6$ 的锐特征分支 $V_{\pm}(u)$ 作为 $\mathcal{D}^{(7)}\cong\mathbb{C}$-模均携带四重内部简并（$\dim_{\mathbb{C}}V_{\pm}(u)=4>1$）。

**证明。** 对第 1 项，因每个 $B_r$（$1\le r\le5$）恰含偶数个反对称因子 $\omega_2$（$0$ 个或 $2$ 个），故 $B_r^{\mathsf T}=B_r$ 且 $B_r^2=I_8$；直接按张量因子检验反对易（如 $B_1B_2=(\sigma_x\sigma_z)\otimes\sigma_x\otimes I_2=-B_2B_1$，且 $\sigma_x\sigma_z^3=(-\omega_2)$、$\sigma_x\omega_2\sigma_z=I_2$ 给出 $B_1B_2B_3B_4=(-\omega_2)\otimes I_2\otimes(-\omega_2)=\omega_2\otimes I_2\otimes\omega_2=B_5$），从而 $\Omega_5=B_5^2=I_8$。每个 $Q_j$（$j=1,2,3$）恰含奇数个（$1$ 个）因子 $\omega_2$，故 $Q_j^{\mathsf T}=-Q_j$ 且 $Q_j^2=-I_8$；又 $Q_1Q_2=\sigma_x\otimes\omega_2\otimes(\omega_2\sigma_z)=\sigma_x\otimes\omega_2\otimes\sigma_x=Q_3=-Q_2Q_1$。逐因子核对对易性：$Q_1$ 在前两因子为 $I_2$、第三因子为 $\omega_2$，与 $B_1,\ldots,B_4$ 的第三因子（$I_2$ 或 $\omega_2$）均对易；$Q_2,Q_3$ 在第一因子为 $\sigma_x$（与 $B_1$ 的 $\sigma_x$ 对易，与 $B_2,B_3,B_4$ 的 $\sigma_z$ 反对易），在后两因子为 $\omega_2\otimes\sigma_z$ 或 $\omega_2\otimes\sigma_x$（与 $B_1$ 的 $I_2\otimes I_2$ 对易，与 $B_2,B_4$ 在第二因子 $\omega_2\sigma_x=-\sigma_x\omega_2$、$\omega_2\sigma_z=-\sigma_z\omega_2$ 反对易而在第三因子对易，与 $B_3$ 在第二因子对易而在第三因子反对易），两次反号相消，故 $[Q_j,B_r]=0$（$1\le j\le3$，$1\le r\le5$）。于是 $\operatorname{span}_{\mathbb{R}}\{I_8,Q_1,Q_2,Q_3\}\cong\mathbb{H}$ 含于 $\mathcal{D}_5$。因 $B_1,\ldots,B_4$ 的 $16$ 个子集乘积在 Hilbert–Schmidt 内积下两两正交，故 $\dim_{\mathbb{R}}\mathcal{A}_5\ge16$；而 $\mathbb{R}^8\cong\mathbb{H}^2$ 上与 $\mathbb{H}$ 对易的全线性代数 $\operatorname{End}_{\mathbb{H}}(\mathbb{R}^8)\cong M_2(\mathbb{H})$ 实维数恰为 $16$，故 $\mathcal{A}_5=\operatorname{End}_{\mathbb{H}}(\mathbb{R}^8)$ 不可约、$\mathcal{D}_5=\operatorname{span}_{\mathbb{R}}\{I_8,Q_1,Q_2,Q_3\}$、$\dim_{\mathbb{H}}V_{\pm}(u)=1$，且 $\mathcal{A}_5\cap\mathcal{D}_5=Z(M_2(\mathbb{H}))=\mathbb{R}I_8$。

对第 2 项，在 $(\mathbb{R}^2)^{\otimes4}=\mathbb{R}^{16}$ 上定义七个实对称正交对合（每个恰含 $0$ 个或 $2$ 个 $\omega_2$ 因子）：

$$
\begin{aligned}
G_1&=I_2\otimes I_2\otimes I_2\otimes\sigma_x,&
G_2&=I_2\otimes I_2\otimes I_2\otimes\sigma_z,&
G_3&=I_2\otimes I_2\otimes\omega_2\otimes\omega_2,\\
G_4&=I_2\otimes\omega_2\otimes\sigma_x\otimes\omega_2,&
G_5&=\sigma_x\otimes\omega_2\otimes\sigma_z\otimes\omega_2,&
G_6&=\sigma_z\otimes\omega_2\otimes\sigma_z\otimes\omega_2,\\
G_7&=\omega_2\otimes I_2\otimes\sigma_z\otimes\omega_2.
\end{aligned}
$$

逐对核对四个张量槽上的反对易个数均为奇数（$G_1,G_2,G_3$ 在第四槽为两两反对易的三元组 $(\sigma_x,\sigma_z,\omega_2)$ 而前三槽对易；$G_4,G_5,G_6,G_7$ 在第四槽同为 $\omega_2$ 故与 $G_1,G_2$ 反对易，在第三槽同为 $\sigma_x$ 或 $\sigma_z$ 故与 $G_3$ 的第三槽 $\omega_2$ 反对易、第四槽同为 $\omega_2$ 对易；$G_4$ 与 $G_5,G_6,G_7$ 在第三槽 $\sigma_x$ 对 $\sigma_z$ 反对易而其余槽对易；$G_5,G_6,G_7$ 在前两槽构成 $(\sigma_x\otimes\omega_2,\sigma_z\otimes\omega_2,\omega_2\otimes I_2)$ 两两反对易而后两槽相同对易），故 $\{G_i,G_j\}=2\delta_{ij}I_{16}$（$1\le i,j\le7$）。由引理 5.2 第 1 项（$7\equiv3\pmod4$），体积元 $\Omega_7=G_1\cdots G_7\in Z(\mathcal{A}^{(7)})$ 满足 $\Omega_7^{\mathsf T}=-\Omega_7$ 与 $\Omega_7^2=-I_{16}$，赋予 $\mathbb{R}^{16}$ 八维复内积空间结构 $\mathbb{C}^8$。因实 Clifford 代数 $C\ell_{7,0}$ 实维数为 $2^7=128$ 且中心 $\operatorname{span}_{\mathbb{R}}\{I,\Omega_7\}\cong\mathbb{C}$ 为域，其任意商代数只要保持 $\Omega_7^2=-I$ 即为单代数（Atiyah–Bott–Shapiro 1964），故同态像 $\mathcal{A}^{(7)}\subseteq\operatorname{End}_{\mathbb{C}}(\mathbb{C}^8)$ 实维数为 $128=\dim_{\mathbb{R}}M_8(\mathbb{C})$，从而 $\mathcal{A}^{(7)}=\operatorname{End}_{\mathbb{C}}(\mathbb{C}^8)\cong M_8(\mathbb{C})$ 在 $\mathbb{R}^{16}$ 上不可约，换位子为 $\mathcal{D}^{(7)}=Z(\mathcal{A}^{(7)})\cong\mathbb{C}$。此时定理 5.3 的条件 1 与条件 2 直接成立，对齐扇区 $W=\ker(\Omega_{7,A}\otimes I_{16}-I_{16}\otimes\Omega_{7,B})\cong\mathbb{C}^{64}$ 满足 $\mathcal{D}_W\cong\mathbb{C}$ 且 $\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(\mathbb{C}^{64})=64^2=4096=(8^2)^2=\bigl(\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(\mathbb{C}^8)\bigr)^2$，条件 3 亦成立；但每个无迹复线性对合 $A^{(7)}(u)$（$u\in S^6$）在 $\mathbb{C}^8$ 上的 $\pm1$ 特征空间维数均为 $\dim_{\mathbb{C}}V_{\pm}(u)=4>1$，证明了定义 5.1 条件 3（分支极小初等性）对于定理 5.3 唯一锁定 $k=3$ 不可或缺。∎

**来源与适用边界 5.5。** 第 2–3 节在未预设全局复结构亦未预设外部边同构的有限维实内积空间上给出跨投影手征黏合判据（定理 2.3）与共享二维分支图上的无基 $\mathbb{Z}_2$ 圈和乐判据（定理 3.3），严格区分于预先给定全局正交复结构 $J$ 后的实—复 Hilbert 等价（Baez 2012 定理 7）以及预先指定子空间间正交输运映射后的闭环判据（[`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 定理 8.2）。第 4 节直接以实转置与内生偏迹导出非交换算子块球面恒等式（定理 4.2），其中单态秩二实化密度归一化沿用 McKague–Mosca–Gisin 2009 附录 A.1，算子纯度亏格将 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 定理 5.2 从复载体下沉到纯实载体。第 5 节的初等切分分类与选型（引理 5.2、定理 5.3）以 Frobenius 1878 实可除代数分类、Dyson 1962 与 Baez 2012 定理 12 的实张量代数同构、Caves–Fuchs–Schack 2002 第 V 节与 Hardy 2001 的局部对称乘积层析计数，以及 Atiyah–Bott–Shapiro 1964 的实 Clifford 单性为中间代数工具；定理 5.3 的排除结论仅针对单切分不可约可观测量代数与完整局部对称正锥的标准实张量复合，不排除通过附加共享外部相位辅助比特并限制可访问子代数在更大实或四元数载体上构造的受限模拟（McKague–Mosca–Gisin 2009）。第 1–5 节尚未涉及跨窗口概率赋值的 Born 迹密度闭合、单本体参考切分下的完全正性仪器与有限精度守卫读出、以及离散晶格隐藏库消去下的红外共同光锥条件。

## 追加锚（本行以下为增补区）
