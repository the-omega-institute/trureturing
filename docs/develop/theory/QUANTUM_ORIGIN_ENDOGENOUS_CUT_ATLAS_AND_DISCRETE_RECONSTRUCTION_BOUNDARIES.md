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

1. **三窗口两两零交但代数黏合失效**：存在由三个四维局部锐三轴窗口组成的覆盖图册 $\mathfrak{A}_{\mathrm{alg}}=\{(\Pi'_1,A'_1),(\Pi'_2,A'_2),(\Pi'_3,A'_3)\}$，使得任意两不同窗口子空间的交集均为零（$\operatorname{Ran}\Pi'_\alpha\cap\operatorname{Ran}\Pi'_\beta=\{0\}$，$\alpha\ne\beta$，故两两集合交集上的一致性条件真空成立），但在 $\mathbb{R}^8$ 上对**全部八种**独立窗口轴定向符号选择 $(s_1,s_2,s_3)\in\{\pm1\}^3$，甚至不存在任何不要求保度量的纯实线性算子 $J_{\mathrm{lin}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^8)$ 在每个 $\operatorname{Ran}\Pi'_\alpha$ 上限制为 $s_\alpha J'_\alpha|_{\operatorname{Ran}\Pi'_\alpha}$（$\alpha=1,2,3$）；
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

先证第 1 项。在 $\mathbb{R}^8=\mathbb{R}^4\oplus\mathbb{R}^4$ 中取三个有理 $8\times4$ 列标准正交矩阵

$$
W'_1=\begin{pmatrix}I_4\\0\end{pmatrix},\qquad
W'_2=\begin{pmatrix}0\\I_4\end{pmatrix},\qquad
W'_3=\frac{1}{5}\begin{pmatrix}3I_4\\4I_4\end{pmatrix},
$$

并令反射对角阵 $F=\operatorname{diag}(1,1,1,-1)\in O(4)$（$F^{\mathsf T}=F$，$F^2=I_4$），定义 $\widetilde{E}_i=FE_iF$（$i=1,2,3$），其手征积为 $\widetilde{J}_0=\widetilde{E}_1\widetilde{E}_2\widetilde{E}_3=FJ_0F=\operatorname{diag}(\omega_2,-\omega_2)\ne\pm J_0$。令 $\Pi'_\alpha=W'_\alpha(W'_\alpha)^{\mathsf T}$（$\alpha=1,2,3$），对 $\alpha=1,2$ 取 $A'_{\alpha,i}=W'_\alpha E_i(W'_\alpha)^{\mathsf T}$，对 $\alpha=3$ 取 $A'_{3,i}=W'_3\widetilde{E}_i(W'_3)^{\mathsf T}$。三窗口各自满足定义 2.1，$\Pi'_1+\Pi'_2+\Pi'_3=I_8+\Pi'_3\succeq I_8\succ0$，且子空间 $\operatorname{Ran}\Pi'_1=\mathbb{R}^4\oplus\{0\}$、$\operatorname{Ran}\Pi'_2=\{0\}\oplus\mathbb{R}^4$ 与斜对角子空间 $\operatorname{Ran}\Pi'_3=\{(3x,4x):x\in\mathbb{R}^4\}$ 两两交集均为 $\{0\}$。局部手征积在各自子空间上的作用分别为 $J'_1(x,0)=(J_0x,0)$、$J'_2(0,y)=(0,J_0y)$ 与 $J'_3(3x,4x)=(3\widetilde{J}_0x,4\widetilde{J}_0x)$。若对某组符号 $(s_1,s_2,s_3)\in\{\pm1\}^3$ 存在 $J_{\mathrm{lin}}\in\operatorname{End}_{\mathbb{R}}(\mathbb{R}^8)$ 在每个 $\operatorname{Ran}\Pi'_\alpha$ 上限制为 $s_\alpha J'_\alpha|_{\operatorname{Ran}\Pi'_\alpha}$，则由 $(3x,4x)=(3x,0)+(0,4x)$ 及线性性得

$$
(3s_3\widetilde{J}_0x,\,4s_3\widetilde{J}_0x)=J_{\mathrm{lin}}(3x,4x)=J_{\mathrm{lin}}(3x,0)+J_{\mathrm{lin}}(0,4x)=(3s_1J_0x,\,4s_2J_0x)\qquad(\forall x\in\mathbb{R}^4),
$$

比较前四坐标即要求 $s_1\operatorname{diag}(\omega_2,\omega_2)=s_3\operatorname{diag}(\omega_2,-\omega_2)$，首块迫使 $s_1=+s_3$ 而次块迫使 $s_1=-s_3$，对一切 $(s_1,s_2,s_3)\in\{\pm1\}^3$ 矛盾，证毕结论 1。

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
\operatorname{Tr}_{\mathbb{R}^2}(A_2R_{\mathbb{R}})=\frac{1}{2}\operatorname{Tr}_{\mathbb{R}}((-\varepsilon)^2)(J_0N_2)=-J_0N_2=Y',\quad
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

**证明。** 对第 1 项，极化 $A(u+w)^2=\|u+w\|^2I_V$ 得 $\{A_i,A_j\}=2\delta_{ij}I_V$。倒序重排 $A_k\cdots A_1$ 为 $A_1\cdots A_k$ 需要 $\frac{k(k-1)}{2}$ 次不同轴邻位交换，故 $\Omega_k^{\mathsf T}=A_k\cdots A_1=(-1)^{k(k-1)/2}\Omega_k$；又 $\Omega_k\Omega_k^{\mathsf T}=A_1\cdots A_kA_k\cdots A_1=I_V$，故 $\Omega_k^2=(-1)^{k(k-1)/2}\Omega_k\Omega_k^{\mathsf T}=(-1)^{k(k-1)/2}I_V$。将 $A_i$ 穿过 $A_1\cdots A_k$ 时与其余 $k-1$ 个因子反对易、与自身对易，得 $A_i\Omega_k=(-1)^{k-1}\Omega_kA_i$。由 $\{A_i,A_j\}=2\delta_{ij}I_V$ 知，$\mathcal{A}$ 由 $2^k$ 个有序子集乘积 $\{A_S:S\subseteq\{1,\ldots,k\}\}$（其中空集积 $A_\varnothing=I_V$，对 $S=\{i_1<\cdots<i_r\}$ 取 $A_S=A_{i_1}\cdots A_{i_r}$）线性张成。定义 $k$ 个两两对易的平均算子 $\Pi_j(X)=\frac{1}{2}(X+A_jXA_j)$（$1\le j\le k$）及其复合 $P_Z=\Pi_1\cdots\Pi_k:\mathcal{A}\to\mathcal{A}$：任意中心元素 $X\in Z(\mathcal{A})$ 满足 $P_Z(X)=X$，而若某个单项式 $A_S$ 与某个 $A_j$ 反对易则 $\Pi_j(A_S)=0$，从而 $P_Z(A_S)=0$。对任意非空子集 $S$（$r=|S|\ge1$）：若 $r$ 为偶数（$r\ge2$），任取属于 $S$ 的指标 $j\in S$，则 $A_j$ 与自身对易、与 $S\setminus\{j\}$ 中其余 $r-1$ 个（奇数个）因子反对易，故 $A_jA_S=-A_SA_j$，$P_Z(A_S)=0$；若 $r$ 为奇数且 $r<k$，任取不属于 $S$ 的指标 $j\in\{1,\ldots,k\}\setminus S$，则 $A_j$ 与 $S$ 中全部 $r$ 个（奇数个）因子反对易，同样有 $A_jA_S=-A_SA_j$，$P_Z(A_S)=0$。因此，当 $k$ 为偶数时一切非空子集 $S$（偶 $r\ge2$ 或奇 $r\le k-1<k$）均满足 $P_Z(A_S)=0$，故 $Z(\mathcal{A})=P_Z(Z(\mathcal{A}))=\mathbb{R}I_V$；当 $k$ 为奇数时仅 $S=\varnothing$（$I_V$）与 $S=\{1,\ldots,k\}$（$\Omega_k$）在 $P_Z$ 下存活，故 $Z(\mathcal{A})=\operatorname{span}_{\mathbb{R}}\{I_V,\Omega_k\}$。若 $k\equiv1\pmod4$，则 $\frac{k(k-1)}{2}$ 为偶数，$\Omega_k^{\mathsf T}=\Omega_k$ 且 $\Omega_k^2=I_V$；若 $\Omega_k\ne\pm I_V$，则非零中心正交投影 $\frac{1}{2}(I_V\pm\Omega_k)$ 将 $V$ 分解为两个非零 $\mathcal{A}$-不变子空间，与不可约性矛盾，故 $\Omega_k\in\{\pm I_V\}$ 且 $Z(\mathcal{A})=\mathbb{R}I_V$。唯当 $k\equiv3\pmod4$ 时，$\frac{k(k-1)}{2}$ 为奇数，$\Omega_k\in Z(\mathcal{A})$ 满足 $\Omega_k^{\mathsf T}=-\Omega_k$ 与 $\Omega_k^2=-I_V$。

对第 2 项，设 $(V,g,A)$ 满足定义 5.1 条件 1–2。先排除 $k=1$：若 $k=1$，条件 1 给出非零正负特征空间 $V_+(e_1)$ 与 $V_-(e_1)$，而 $\mathcal{A}=\operatorname{span}_{\mathbb{R}}\{I_V,A_1\}$ 保持二者不变，与条件 2 的不可约性矛盾，故 $k\ge2$。对 $k\ge2$，任取 $j\ne i$ 有 $A_i=-A_jA_iA_j$，取实迹得 $\operatorname{Tr}_{\mathbb{R}}(A_i)=0$；又 $\operatorname{Tr}_{\mathbb{R}}(A_iA_j)=\frac{1}{2}\operatorname{Tr}_{\mathbb{R}}(\{A_i,A_j\})=\delta_{ij}\dim_{\mathbb{R}}V$，故 $A_1,\ldots,A_k$ 是无迹实对称子空间 $\mathcal{A}_{\mathrm{sym},0}=\{M\in\mathcal{A}:M^{\mathsf T}=M,\ \operatorname{Tr}_{\mathbb{R}}(M)=0\}$ 中两两正交的非零元，从而 $k\le\dim_{\mathbb{R}}\mathcal{A}_{\mathrm{sym},0}$。

由 Schur 引理与 Frobenius 实可除代数定理（Frobenius 1878；亦见 [`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 定理 A.1），换位子 $\mathcal{D}=\mathcal{A}'$ 是转置不变有限维实可除代数，作为实代数同构于 $\mathbb{R},\mathbb{C},\mathbb{H}$ 之一（记 $\delta=\dim_{\mathbb{R}}\mathcal{D}\in\{1,2,4\}$）；再由有限维不可约模的 Jacobson 稠密性定理（Artin–Wedderburn 双中心化子定理），有 $\mathcal{A}=\operatorname{End}_{\mathcal{D}}(V)\cong M_m(\mathcal{D})$，其中 $m=\dim_{\mathcal{D}}V$，$\dim_{\mathbb{R}}V=m\delta$，$\dim_{\mathbb{R}}\mathcal{A}=m^2\delta$。对任意单位方向 $u\in S^{k-1}$，取正交单位向量 $w\in S^{k-1}$（$w\perp u$，因 $k\ge2$ 存在），则 $A(w)\in\mathcal{A}$ 与 $\mathcal{D}$ 对易、满足 $A(w)^2=I_V$ 且 $A(u)A(w)=-A(w)A(u)$，故 $A(w)$ 给出左 $\mathcal{D}$-模同构 $V_+(u)\xrightarrow{\sim}V_-(u)$；结合 $V=V_+(u)\oplus V_-(u)$ 与 $V_{\pm}(u)\ne\{0\}$，恒有 $\dim_{\mathcal{D}}V_+(u)=\dim_{\mathcal{D}}V_-(u)=\frac{m}{2}\ge1$（$m\in2\mathbb{Z}_{>0}$）。因此定义 5.1 条件 3（对一切 $u\in S^{k-1}$ 有 $\dim_{\mathcal{D}}V_{\pm}(u)=1$）精确等价于 $m=2$。对任意 $q\in\mathcal{D}$，其实对称部分 $q_+=\frac{1}{2}(q+q^{\mathsf T})\in\mathcal{D}$ 在 $V$ 上有实特征值 $\lambda\in\mathbb{R}$，因可除代数中非零元在 $V$ 上可逆，必有 $q_+=\lambda I_V$；同理反对称部分 $q_-=\frac{1}{2}(q-q^{\mathsf T})\in\mathcal{D}$ 满足 $q_-^2=-q_-^{\mathsf T}q_-\preceq0$，故 $q_-^2=-\mu^2I_V$（$\mu\ge0$），这表明实转置 $q\mapsto q^{\mathsf T}$ 在 $\mathcal{D}$ 上恰为标准范数共轭 $\bar{q}=\lambda I_V-q_-$，且对一切 $x\in V$ 与反对称元 $q_-$ 有 $g(x,q_-x)=0$。

先证反向（$\Leftarrow$）：设 $k\in\{2,3,4,5\}$，证明任意满足条件 1–2 的 $(V,g,A)$ 必有 $m=2$。
- 当 $k=2$ 时，$m^2\delta=\dim_{\mathbb{R}}\mathcal{A}\le2^2=4$，结合 $m\ge2$ 与 $\delta\ge1$ 唯一迫使 $m=2$、$\delta=1$（$\mathcal{D}\cong\mathbb{R}$，$\dim_{\mathbb{R}}V=2$）；
- 当 $k=3$ 时，由第 1 项知 $Z(\mathcal{A})\cong\mathbb{C}$；因 $Z(\operatorname{End}_{\mathcal{D}}(V))\cong Z(\mathcal{D})$，在 $\mathbb{R},\mathbb{C},\mathbb{H}$ 中中心同构于 $\mathbb{C}$ 者唯独 $\mathcal{D}\cong\mathbb{C}$（$\delta=2$），再由 $2m^2=\dim_{\mathbb{R}}\mathcal{A}\le2^3=8$ 与 $m\ge2$ 迫使 $m=2$（$\dim_{\mathbb{R}}V=4$，$Z(\mathcal{A})=\mathcal{D}$）；
- 当 $k\in\{4,5\}$ 时，若 $k=5$ 则由第 1 项知 $\Omega_5\in\{\pm I_V\}$，故 $A_5=\pm A_1A_2A_3A_4\in\operatorname{Alg}_{\mathbb{R}}(A_1,\ldots,A_4)$，因此在 $k=4,5$ 两种情形下均有 $m^2\delta=\dim_{\mathbb{R}}\mathcal{A}\le2^4=16$。另一方面，算子 $K_1=A_1A_2,K_2=A_2A_3,K_3=A_1A_3$ 满足 $K_1^2=K_2^2=K_3^2=K_1K_2K_3=-I_V$（生成四元数代数 $\mathbb{H}$），而第四轴 $A_4$ 与 $K_1,K_2,K_3$ 逐一经过两次反对易后严格对易（$[A_4,K_j]=0$，$j=1,2,3$），故两个非零特征空间 $V_+(e_4)$ 与 $V_-(e_4)$ 均为非零左 $\mathbb{H}$-模，实维数均属于 $4\mathbb{Z}_{>0}$，从而 $m\delta=\dim_{\mathbb{R}}V=\dim_{\mathbb{R}}V_+(e_4)+\dim_{\mathbb{R}}V_-(e_4)\ge4+4=8$。将 $8m\le m(m\delta)=m^2\delta\le16$ 与 $m\ge2$ 联立，唯一迫使 $m=2$ 与 $\delta=4$（$\mathcal{D}\cong\mathbb{H}$，$\dim_{\mathbb{R}}V=8$）。

再证正向（$\Rightarrow$）及对称态维数公式与各类的非空实现：设条件 3 成立，即 $m=2$，$\dim_{\mathbb{R}}V=2\delta$。分别在相互正交的特征空间 $V_+(e_1)$ 与 $V_-(e_1)$ 中任取 $g$-单位向量 $v_1,v_2$，则 $V=\mathcal{D}v_1\oplus\mathcal{D}v_2$，且对一切 $q_1,q_2\in\mathcal{D}$ 与 $r,s\in\{1,2\}$ 有 $g(q_1v_r,q_2v_s)=\delta_{rs}\operatorname{Re}(\bar{q}_1q_2)$。任意左 $\mathcal{D}$-线性算子 $T\in\mathcal{A}=\operatorname{End}_{\mathcal{D}}(V)$ 由 $T(v_s)=\sum_{r=1}^2 m_{rs}v_r$（$m_{rs}\in\mathcal{D}$）唯一表示；利用 $\mathbb{R},\mathbb{C},\mathbb{H}$ 上恒成立的实部循环律 $\operatorname{Re}(ab)=\operatorname{Re}(ba)$ 与共轭反自同构律 $\overline{q_1\bar{m}_{rs}}=m_{rs}\bar{q}_1$，有

$$
g\bigl(q_1v_r,T(q_2v_s)\bigr)=\operatorname{Re}(\bar{q}_1q_2m_{rs})=\operatorname{Re}(m_{rs}\bar{q}_1q_2)=\operatorname{Re}\bigl(\overline{(q_1\bar{m}_{rs})}q_2\bigr),
$$

故 $T^{\mathsf T}=T$ 当且仅当 $m_{11},m_{22}\in\mathbb{R}$ 且 $m_{21}=\bar{m}_{12}\in\mathcal{D}$。因 $\operatorname{Sym}_{\mathcal{D}}(V)$ 与 $\mathcal{A}\cap\operatorname{Sym}(V,g)$ 在此处（$\mathcal{A}=\mathcal{D}'$）完全重合，得

$$
\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)=2+\delta,\qquad \dim_{\mathbb{R}}\mathcal{A}_{\mathrm{sym},0}=1+\delta,\qquad \dim_{\mathbb{R}}\mathcal{A}=4\delta.
$$

由 $2\le k\le\dim_{\mathbb{R}}\mathcal{A}_{\mathrm{sym},0}=1+\delta\le1+4=5$ 直接推出 $k\in\{2,3,4,5\}$（对一切 $k\ge6$ 不存在满足条件 3 的切分），并将 $\delta\in\{1,2,4\}$ 代入 $2+\delta$ 即得三类的 $\dim_{\mathbb{R}}\operatorname{Sym}_{\mathcal{D}}(V)$ 分别为 $3,4,6$：$k=2$ 由 $(\sigma_x,\sigma_z)$ 在 $\mathbb{R}^2$ 上实现；$k=3$ 由命题 2.4 中的 $(E_1,E_2,E_3)$ 在 $\mathbb{R}^4$ 上实现；$k=4,5$ 由命题 5.4 第 1 项在 $\mathbb{R}^8$ 上实现，且对任意初等 $k=4$ 切分，第 1 项给出 $A_5=\Omega_4\in\mathcal{A}$ 满足 $A_5^{\mathsf T}=(-1)^6A_5=A_5$、$A_5^2=I_V$ 及 $A_iA_5=-A_5A_i$（$1\le i\le4$），在同代数 $\mathcal{A}$ 内扩张为初等 $k=5$ 切分。∎

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

**证明。** 对第 1 项，因每个 $B_r$（$1\le r\le5$）恰含偶数个反对称因子 $\omega_2$（$0$ 个或 $2$ 个），故 $B_r^{\mathsf T}=B_r$ 且 $B_r^2=I_8$；直接按张量因子检验反对易（如 $B_1B_2=(\sigma_x\sigma_z)\otimes\sigma_x\otimes I_2=-B_2B_1$，且 $\sigma_x\sigma_z^3=\sigma_x\sigma_z=\omega_2$、$\sigma_x\omega_2\sigma_z=I_2$ 给出 $B_1B_2B_3B_4=\omega_2\otimes I_2\otimes\omega_2=B_5$），从而 $\Omega_5=B_5^2=I_8$。每个 $Q_j$（$j=1,2,3$）恰含奇数个（$1$ 个）因子 $\omega_2$，故 $Q_j^{\mathsf T}=-Q_j$ 且 $Q_j^2=-I_8$；又 $Q_1Q_2=\sigma_x\otimes\omega_2\otimes(\omega_2\sigma_z)=\sigma_x\otimes\omega_2\otimes\sigma_x=Q_3=-Q_2Q_1$。逐因子核对对易性：$Q_1$ 在前两因子为 $I_2$、第三因子为 $\omega_2$，与 $B_1,\ldots,B_4$ 的第三因子（$I_2$ 或 $\omega_2$）均对易；$Q_2,Q_3$ 在第一因子为 $\sigma_x$（与 $B_1$ 的 $\sigma_x$ 对易，与 $B_2,B_3,B_4$ 的 $\sigma_z$ 反对易），在后两因子为 $\omega_2\otimes\sigma_z$ 或 $\omega_2\otimes\sigma_x$（与 $B_1$ 的 $I_2\otimes I_2$ 对易，与 $B_2,B_4$ 在第二因子 $\omega_2\sigma_x=-\sigma_x\omega_2$、$\omega_2\sigma_z=-\sigma_z\omega_2$ 反对易而在第三因子对易，与 $B_3$ 在第二因子对易而在第三因子反对易），两次反号相消，故 $[Q_j,B_r]=0$（$1\le j\le3$，$1\le r\le5$）。于是 $\operatorname{span}_{\mathbb{R}}\{I_8,Q_1,Q_2,Q_3\}\cong\mathbb{H}$ 含于 $\mathcal{D}_5$。因 $B_1,\ldots,B_4$ 的 $16$ 个子集乘积在 Hilbert–Schmidt 内积下两两正交，故 $\dim_{\mathbb{R}}\mathcal{A}_5\ge16$；而 $\mathbb{R}^8\cong\mathbb{H}^2$ 上与 $\mathbb{H}$ 对易的全线性代数 $\operatorname{End}_{\mathbb{H}}(\mathbb{R}^8)\cong M_2(\mathbb{H})$ 实维数恰为 $16$，故 $\mathcal{A}_5=\operatorname{End}_{\mathbb{H}}(\mathbb{R}^8)$ 不可约、$\mathcal{D}_5=\operatorname{span}_{\mathbb{R}}\{I_8,Q_1,Q_2,Q_3\}$、$\dim_{\mathbb{H}}V_{\pm}(u)=1$，且 $\mathcal{A}_5\cap\mathcal{D}_5=Z(M_2(\mathbb{H}))=\mathbb{R}I_8$。

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

逐对核对四个张量槽上的反对易个数均为奇数（$G_1,G_2,G_3$ 在第四槽为两两反对易的三元组 $(\sigma_x,\sigma_z,\omega_2)$ 而前三槽对易；$G_4,G_5,G_6,G_7$ 在第四槽同为 $\omega_2$ 故与 $G_1,G_2$ 反对易，在第三槽同为 $\sigma_x$ 或 $\sigma_z$ 故与 $G_3$ 的第三槽 $\omega_2$ 反对易、第四槽同为 $\omega_2$ 对易；$G_4$ 与 $G_5,G_6,G_7$ 在第三槽 $\sigma_x$ 对 $\sigma_z$ 反对易而其余槽对易；$G_5,G_6,G_7$ 在前两槽构成 $(\sigma_x\otimes\omega_2,\sigma_z\otimes\omega_2,\omega_2\otimes I_2)$ 两两反对易而后两槽相同对易），故 $\{G_i,G_j\}=2\delta_{ij}I_{16}$（$1\le i,j\le7$）。由引理 5.2 第 1 项（$7\equiv3\pmod4$），体积元 $\Omega_7=G_1\cdots G_7\in Z(\mathcal{A}^{(7)})$ 满足 $\Omega_7^{\mathsf T}=-\Omega_7$ 与 $\Omega_7^2=-I_{16}$，赋予 $\mathbb{R}^{16}$ 八维复内积空间结构 $\mathbb{C}^8$。对全体 $2^7=128$ 个有序子集乘积 $G_S$（$S\subseteq\{1,\ldots,7\}$），当 $1\le|K|\le6$ 时存在某 $G_j$ 与 $G_K$ 反对易（偶数 $|K|$ 取 $j\in K$，奇数 $|K|$ 取 $j\notin K$）使 $\operatorname{Tr}_{\mathbb{R}}(G_K)=0$，当 $|K|=7$ 时由 $\Omega_7^{\mathsf T}=-\Omega_7$ 得 $\operatorname{Tr}_{\mathbb{R}}(\Omega_7)=0$，故 $128$ 个非零算子 $G_S$ 在实 Hilbert–Schmidt 内积 $(X,Y)\mapsto\operatorname{Tr}_{\mathbb{R}}(X^{\mathsf T}Y)$ 下两两正交、线性无关（等价地，实 Clifford 代数 $C\ell_{7,0}\cong M_8(\mathbb{C})$ 自身即是实维数 $2^7=128$ 的单代数，Atiyah–Bott–Shapiro 1964，故非零代数同态 $C\ell_{7,0}\to\operatorname{End}_{\mathbb{C}}(\mathbb{C}^8)$ 必为单射）。因此 $\dim_{\mathbb{R}}\mathcal{A}^{(7)}=128=\dim_{\mathbb{R}}M_8(\mathbb{C})$，从而 $\mathcal{A}^{(7)}=\operatorname{End}_{\mathbb{C}}(\mathbb{C}^8)\cong M_8(\mathbb{C})$ 在 $\mathbb{R}^{16}$ 上不可约，换位子为 $\mathcal{D}^{(7)}=Z(\mathcal{A}^{(7)})\cong\mathbb{C}$。此时定理 5.3 的条件 1 与条件 2 直接成立，对齐扇区 $W=\ker(\Omega_{7,A}\otimes I_{16}-I_{16}\otimes\Omega_{7,B})\cong\mathbb{C}^{64}$ 满足 $\mathcal{D}_W\cong\mathbb{C}$ 且 $\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(\mathbb{C}^{64})=64^2=4096=(8^2)^2=\bigl(\dim_{\mathbb{R}}\operatorname{Sym}_{\mathbb{C}}(\mathbb{C}^8)\bigr)^2$，条件 3 亦成立；但每个无迹复线性对合 $A^{(7)}(u)$（$u\in S^6$）在 $\mathbb{C}^8$ 上的 $\pm1$ 特征空间维数均为 $\dim_{\mathbb{C}}V_{\pm}(u)=4>1$，证明了定义 5.1 条件 3（分支极小初等性）对于定理 5.3 唯一锁定 $k=3$ 不可或缺。∎

**来源与适用边界 5.5。** 第 2–3 节在未预设全局复结构亦未预设外部边同构的有限维实内积空间上给出跨投影手征黏合判据（定理 2.3）与共享二维分支图上的无基 $\mathbb{Z}_2$ 圈和乐判据（定理 3.3），严格区分于预先给定全局正交复结构 $J$ 后的实—复 Hilbert 等价（Baez 2012 定理 7）以及预先指定子空间间正交输运映射后的闭环判据（[`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 定理 8.2）。第 4 节直接以实转置与内生偏迹导出非交换算子块球面恒等式（定理 4.2），其中单态秩二实化密度归一化沿用 McKague–Mosca–Gisin 2009 附录 A.1，算子纯度亏格将 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 定理 5.2 从复载体下沉到纯实载体。第 5 节的初等切分分类与选型（引理 5.2、定理 5.3）以 Frobenius 1878 实可除代数分类、有限维不可约模的 Jacobson—Artin—Wedderburn 双中心化子定理、Dyson 1962 与 Baez 2012（定理 6、定理 12 证明及第 7 节）的实张量结构、Caves–Fuchs–Schack 2002 第 V 节与 Hardy 2001 的局部对称乘积层析计数，以及 Atiyah–Bott–Shapiro 1964 的实 Clifford 单性为中间代数工具；定理 5.3 的排除结论仅针对单切分不可约可观测量代数与完整局部对称正锥的标准实张量复合，不排除通过附加共享外部相位辅助比特并限制可访问子代数在更大实或四元数载体上构造的受限模拟（McKague–Mosca–Gisin 2009）。第 1–5 节尚未涉及跨窗口概率赋值的 Born 迹密度闭合、单本体参考切分下的完全正性仪器与有限精度守卫读出、以及离散晶格隐藏库消去下的红外共同光锥条件。

## 追加锚（本行以下为增补区）

## 6. 重叠二元切分菜单的关系一致性秩判据与非正锥边界

**定义 6.1（复载体上的二元切分效果菜单、声明框架关系与关系一致性）。** 设 $\mathcal{H}$ 为有限维复内积空间（$\dim_{\mathbb{C}}\mathcal{H}=d\ge2$），记厄米算子实向量空间为 $\operatorname{Herm}(\mathcal{H})$（$\dim_{\mathbb{R}}\operatorname{Herm}(\mathcal{H})=d^2$），效果集为 $\mathcal{E}(\mathcal{H})=\{E\in\operatorname{Herm}(\mathcal{H}):0\preceq E\preceq I_{\mathcal{H}}\}$。有限切分菜单是指三元组 $\mathfrak{M}=(\{E_j\}_{j=0}^N,\mathcal{R})$，其中 $N\in\mathbb{Z}_{\ge1}$，$E_0=I_{\mathcal{H}}$，$E_1,\ldots,E_N\in\mathcal{E}(\mathcal{H})\setminus\{0,I_{\mathcal{H}}\}$，定义算子求值实线性映射

$$
\mathsf{E}_{\mathfrak{M}}:\mathbb{R}^{N+1}\longrightarrow\operatorname{Herm}(\mathcal{H}),\qquad
\mathsf{E}_{\mathfrak{M}}(c)=\sum_{j=0}^{N}c_jE_j,
$$

而 $\mathcal{R}\subseteq\ker\mathsf{E}_{\mathfrak{M}}\subseteq\mathbb{R}^{N+1}$ 为一组由允许的内部正交或效果分解（例如二元互补关系 $e_0-e_a-e_b\in\mathcal{R}$ 对应 $E_a+E_b=I_{\mathcal{H}}$，以及细分树关系 $e_a-e_b-e_c\in\mathcal{R}$ 对应 $E_a=E_b+E_c$，其中 $\{e_0,\ldots,e_N\}$ 为 $\mathbb{R}^{N+1}$ 标准基）给出的已声明框架关系集，记其张成实子空间为 $L_{\mathfrak{M}}=\operatorname{span}_{\mathbb{R}}(\mathcal{R})\subseteq\ker\mathsf{E}_{\mathfrak{M}}$。

菜单 $\mathfrak{M}$ 上的**框架概率赋值**是指向量 $k=(k_0,k_1,\ldots,k_N)^{\mathsf T}\in\mathbb{R}^{N+1}$，满足

$$
k_0=1,\qquad 0\le k_j\le1\quad(1\le j\le N),\qquad \langle r,k\rangle=0\quad(\forall r\in L_{\mathfrak{M}}).
$$

对非空有限切分菜单族 $\mathscr{M}=\{\mathfrak{M}_\gamma\}_{\gamma\in\Upsilon}$（其中 $\mathfrak{M}_\gamma=(\{E_{\gamma,j}\}_{j=0}^{N_\gamma},\mathcal{R}_\gamma)$，效果并集记为 $\mathcal{E}(\mathscr{M})=\bigcup_{\gamma\in\Upsilon}\{E_{\gamma,j}:0\le j\le N_\gamma\}$），$\mathscr{M}$ 上的**相容菜单族概率赋值**是指单值映射 $v:\mathcal{E}(\mathscr{M})\to[0,1]$，使得对每个 $\gamma\in\Upsilon$，其限制向量 $k_{v,\gamma}=(v(E_{\gamma,0}),\ldots,v(E_{\gamma,N_\gamma}))^{\mathsf T}\in\mathbb{R}^{N_\gamma+1}$ 均为 $\mathfrak{M}_\gamma$ 上的框架概率赋值（故在任意两子菜单交集上取值自动一致）。

称菜单 $\mathfrak{M}$ 上的框架概率赋值 $k$ 满足 [`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md) 第 11 节意义下的**线性关系一致性（RC）**，若对一切算子线性依赖 $c\in\ker\mathsf{E}_{\mathfrak{M}}$ 均有 $\langle c,k\rangle=0$（等价地，存在实线性泛函 $\ell:\operatorname{Ran}\mathsf{E}_{\mathfrak{M}}\to\mathbb{R}$，使得 $k_j=\ell(E_j)$ 对一切 $0\le j\le N$ 成立，从而存在厄米代表元 $H\in\operatorname{Herm}(\mathcal{H})$ 使 $k_j=\operatorname{Tr}(HE_j)$）。

**定理 6.2（有限切分菜单强制线性关系一致性的充要核空间秩判据）。** 对定义 6.1 中的任意有限切分菜单 $\mathfrak{M}=(\{E_j\}_{j=0}^N,\mathcal{R})$，下列三项条件彼此等价：

1. $\mathfrak{M}$ 上的**每一个**框架概率赋值 $k$ 均满足线性关系一致性（RC）；
2. 已声明框架关系张成全部算子线性依赖：

$$
L_{\mathfrak{M}}=\ker\mathsf{E}_{\mathfrak{M}};
$$

3. 关系维数恒等式成立：

$$
\dim_{\mathbb{R}}L_{\mathfrak{M}}=N+1-\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}}.
$$

此外，当上述等价条件成立且 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}}=d^2$（菜单完备层析）时，每个框架概率赋值 $k$ 唯一确定一个迹为一的厄米算子 $H_k\in\operatorname{Herm}(\mathcal{H})$（$\operatorname{Tr}H_k=1$）使得 $k_j=\operatorname{Tr}(H_kE_j)$（$0\le j\le N$）。若进一步在一族各自满足 $L_{\mathfrak{M}_\gamma}=\ker\mathsf{E}_{\mathfrak{M}_\gamma}$ 且各自包含同一完备层析基菜单 $\mathfrak{M}_{\gamma_0}$（$\gamma_0\in\Upsilon$，$\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_{\gamma_0}}=d^2$，$\{E_{\gamma_0,j}\}_{j=0}^{N_{\gamma_0}}\subseteq\{E_{\gamma,j}\}_{j=0}^{N_\gamma}$）的切分菜单族 $\mathscr{M}=\{\mathfrak{M}_\gamma\}_{\gamma\in\Upsilon}$ 上给出相容菜单族概率赋值 $v:\mathcal{E}(\mathscr{M})\to[0,1]$，使得全体秩一正交投影位于 $\mathcal{E}(\mathscr{M})$ 的闭包中，则对一切 $d\ge2$ 存在唯一半正定迹一密度算子 $H_v\in\operatorname{Herm}(\mathcal{H})$（$H_v\succeq0,\operatorname{Tr}H_v=1$）使 $v(E)=\operatorname{Tr}(H_vE)$ 对一切 $E\in\mathcal{E}(\mathscr{M})$ 成立（将 [`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md) 定理 11.2 的可数归一划分全局 RC 判据推进至局部核完备子菜单族）；而在不预先假设跨标架线性关系一致性的设定下，若赋值定义在 $\dim_{\mathbb{C}}\mathcal{H}\ge3$ 的全部正交投影分解上满足框架可加性（Gleason 1957（定理 2.8 与第 3 节）），或定义在全体效果集 $\mathcal{E}(\mathcal{H})$（$d\ge2$）上对一切满足 $\sum_m E_m\preceq I_{\mathcal{H}}$ 的有限效果分解满足可加性（Busch 2003），则可同时导出线性关系一致性与半正定密度表示。

**证明。** 由秩–零化度定理 $\dim_{\mathbb{R}}\ker\mathsf{E}_{\mathfrak{M}}=N+1-\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}}$ 及包含关系 $L_{\mathfrak{M}}\subseteq\ker\mathsf{E}_{\mathfrak{M}}$，条件 2 与条件 3 直接等价。若条件 2 成立，则任意框架概率赋值 $k\perp L_{\mathfrak{M}}=\ker\mathsf{E}_{\mathfrak{M}}$ 直接满足 RC，故 $2\Rightarrow1$。

现证 $1\Rightarrow2$（逆否命题）。假设 $L_{\mathfrak{M}}\subsetneq\ker\mathsf{E}_{\mathfrak{M}}$，取 $r\in\ker\mathsf{E}_{\mathfrak{M}}\setminus L_{\mathfrak{M}}$。断言 $r\notin L_{\mathfrak{M}}+\mathbb{R}e_0$：若不然，设 $r=\ell+te_0$（$\ell\in L_{\mathfrak{M}}\subseteq\ker\mathsf{E}_{\mathfrak{M}}$，$t\in\mathbb{R}$），作用 $\mathsf{E}_{\mathfrak{M}}$ 得 $0=\mathsf{E}_{\mathfrak{M}}(r)=\mathsf{E}_{\mathfrak{M}}(\ell)+tE_0=tI_{\mathcal{H}}$，故 $t=0$、$r=\ell\in L_{\mathfrak{M}}$，矛盾。因此在欧氏内积下，$r$ 到子空间 $L_{\mathfrak{M}}+\mathbb{R}e_0$ 的正交补投影 $v=r-\operatorname{Proj}_{L_{\mathfrak{M}}+\mathbb{R}e_0}(r)\in\mathbb{R}^{N+1}$ 非零，满足 $v\perp L_{\mathfrak{M}}$、$v_0=\langle e_0,v\rangle=0$ 且 $\langle r,v\rangle=\|v\|^2>0$。考虑中心最大混合迹赋值 $k^*\in\mathbb{R}^{N+1}$，定义为

$$
k^*_j=\frac{1}{d}\operatorname{Tr}(E_j)\qquad(0\le j\le N).
$$

显然 $k^*_0=1$；对每个 $1\le j\le N$，因 $0\preceq E_j\preceq I_{\mathcal{H}}$ 且 $E_j\notin\{0,I_{\mathcal{H}}\}$，半正定算子迹的忠实性给出严格内部不等式 $0<k^*_j<1$；又因迹线性，$k^*\perp\ker\mathsf{E}_{\mathfrak{M}}\supseteq L_{\mathfrak{M}}$。取充分小的正数

$$
0<\epsilon\le\min_{1\le j\le N}\frac{\min(k^*_j,1-k^*_j)}{\|v\|_\infty},
$$

令 $k=k^*+\epsilon v$。则 $k_0=k^*_0+\epsilon\cdot0=1$，对一切 $1\le j\le N$ 有 $0\le k_j\le1$，且对一切 $\ell\in L_{\mathfrak{M}}$ 有 $\langle\ell,k\rangle=\langle\ell,k^*\rangle+\epsilon\langle\ell,v\rangle=0$，故 $k$ 是 $\mathfrak{M}$ 上的合法框架概率赋值；然而 $\langle r,k\rangle=\langle r,k^*\rangle+\epsilon\langle r,v\rangle=\epsilon\|v\|^2>0$，违反了 $r\in\ker\mathsf{E}_{\mathfrak{M}}$ 对应的 RC，矛盾。故 $L_{\mathfrak{M}}=\ker\mathsf{E}_{\mathfrak{M}}$。

当 $L_{\mathfrak{M}}=\ker\mathsf{E}_{\mathfrak{M}}$ 且 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}}=d^2$ 时，$\mathsf{E}_{\mathfrak{M}}$ 满射到 $\operatorname{Herm}(\mathcal{H})$，$k\perp\ker\mathsf{E}_{\mathfrak{M}}$ 唯一诱导实线性泛函 $\ell_k:\operatorname{Herm}(\mathcal{H})\to\mathbb{R}$ 使 $\ell_k(E_j)=k_j$；关于非退化实内积 $(X,Y)\mapsto\operatorname{Tr}(XY)$ 的 Riesz 表示给出唯一 $H_k\in\operatorname{Herm}(\mathcal{H})$ 使 $\ell_k(X)=\operatorname{Tr}(H_kX)$，且 $\operatorname{Tr}H_k=\ell_k(E_0)=k_0=1$。对包含完备层析基菜单 $\mathfrak{M}_{\gamma_0}$ 且各自满足 $L_{\mathfrak{M}_\gamma}=\ker\mathsf{E}_{\mathfrak{M}_\gamma}$ 的菜单族 $\mathscr{M}=\{\mathfrak{M}_\gamma\}_{\gamma\in\Upsilon}$，因 $\{E_{\gamma_0,j}\}_{j=0}^{N_{\gamma_0}}\subseteq\{E_{\gamma,j}\}_{j=0}^{N_\gamma}$ 已张成全部 $\operatorname{Herm}(\mathcal{H})$，每个子菜单自动满足 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_\gamma}=d^2$，其上限制 $k_{v,\gamma}$ 唯一确定的迹一厄米算子 $H_{v,\gamma}$ 在张成集 $\{E_{\gamma_0,j}\}_{j=0}^{N_{\gamma_0}}$ 上均满足 $\operatorname{Tr}(H_{v,\gamma}E_{\gamma_0,j})=v(E_{\gamma_0,j})=\operatorname{Tr}(H_{v,\gamma_0}E_{\gamma_0,j})$，故对一切 $\gamma\in\Upsilon$ 有 $H_{v,\gamma}=H_{v,\gamma_0}=:H_v$，从而对一切 $E\in\mathcal{E}(\mathscr{M})$ 有 $\operatorname{Tr}(H_vE)=v(E)\ge0$。对任意单位向量 $|\psi\rangle\in\mathcal{H}$，取序列 $\{E^{(m)}\}_{m\ge1}\subseteq\mathcal{E}(\mathscr{M})$ 收敛于秩一投影 $|\psi\rangle\langle\psi|$，由有限维线性泛函 $X\mapsto\operatorname{Tr}(H_vX)$ 的连续性立得 $\langle\psi,H_v\psi\rangle=\operatorname{Tr}(H_v|\psi\rangle\langle\psi|)=\lim_{m\to\infty}\operatorname{Tr}(H_vE^{(m)})=\lim_{m\to\infty}v(E^{(m)})\ge0$，故 $H_v\succeq0$（对比 [`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md) 定理 11.2）。∎

**命题 6.3（跨切口缺乏三维桥时的光滑非迹球面赋值与完备稀疏菜单的非半正定反例）。**

1. **缺乏跨参考槽交织时的光滑凸非 Born 球面赋值**：在 $\mathbb{C}^2$（或嵌入 $\mathbb{C}^2\otimes\mathbb{C}^m$，$m\ge2$，但仅允许单槽二元切分 $\{P_n\otimes I_m,P_{-n}\otimes I_m\}_{n\in S^2}$，其中 $P_n=\frac{1}{2}(I_2+n\cdot\sigma)$）上，光滑单参数函数族

$$
k_\eta(P_n\otimes I_m)=\frac{1}{2}(1+\eta n_z^3)\qquad(\eta\in[-1,1],\ n=(n_x,n_y,n_z)\in S^2)
$$

对一切 $n\in S^2$ 取值于 $[0,1]$ 且严格满足每个二元切分的框架归一化 $k_\eta(P_n\otimes I_m)+k_\eta(P_{-n}\otimes I_m)=1$（并关于 $\eta\in[-1,1]$ 构成凸集）；但对一切 $\eta\ne0$，它在四个共面勾股方向 $n_1=(0,0,1),n_2=(0,0,-1),n_3=(\frac{3}{5},0,\frac{4}{5}),n_4=(-\frac{3}{5},0,\frac{4}{5})$ 的算子恒等式 $P_{n_3}+P_{n_4}=\frac{9}{5}P_{n_1}+\frac{1}{5}P_{n_2}$ 上给出残差

$$
k_\eta(P_{n_3}\otimes I_m)+k_\eta(P_{n_4}\otimes I_m)-\frac{9}{5}k_\eta(P_{n_1}\otimes I_m)-\frac{1}{5}k_\eta(P_{n_2}\otimes I_m)=-\frac{36}{125}\eta\ne0,
$$

故违反 RC 且不存在任何密度算子迹表示；

2. **强制 RC 且完备层析的稀疏菜单仍不蕴涵全锥半正定性**：在 $\mathcal{H}=\mathbb{C}^3$ 上，记 $\omega=e^{2\pi i/3}$，由标准正交基 $\{e_0,e_1,e_2\}$ 与三组二次相位基

$$
v_{s,k}=\frac{1}{\sqrt{3}}\sum_{j=0}^{2}\omega^{sj^2+kj}e_j\qquad(s,k\in\{0,1,2\})
$$

组成的四组相互无偏正交基（共 $12$ 个秩一投影 $P_{b,k}$，连同 $E_0=I_3$ 及每个三结果基编码为二元切分树的四个归一求和关系）构成有限菜单 $\mathfrak{M}_{12}$，满足 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_{12}}=9=\dim_{\mathbb{R}}\operatorname{Herm}(\mathbb{C}^3)$ 与 $\dim_{\mathbb{R}}L_{\mathfrak{M}_{12}}=4=13-9$，故按定理 6.2 **强制一切框架概率赋值满足 RC 并唯一重构迹一厄米算子** $H=\sum_{b=0}^3\sum_{k=0}^2 k(P_{b,k})P_{b,k}-I_3$；然而取单位向量 $u=\frac{1}{\sqrt{21}}(1,2,4)^{\mathsf T}\in\mathbb{C}^3$ 与迹一厄米算子

$$
H_*=\frac{8}{15}I_3-\frac{3}{5}uu^\dagger,
$$

其诱导赋值 $k_*(P_{b,k})=\operatorname{Tr}(H_*P_{b,k})$ 满足全部二元切分树可加性、全体 RC 关系，且在全部 $12$ 个菜单秩一投影上严格正（$\min_{b,k}k_*(P_{b,k})=\frac{1}{15}>0$，$\max_{b,k}k_*(P_{b,k})=\frac{53}{105}<1$），但 $H_*$ 的谱为 $\{-\frac{1}{15},\frac{8}{15},\frac{8}{15}\}$，不半正定（$H_*\not\succeq0$）。

**证明。** 对第 1 项，由 $(-n)_z^3=-n_z^3$ 与 $|n_z|\le1$ 知 $k_\eta(P_n\otimes I_m)\in[0,1]$ 且 $k_\eta(P_n\otimes I_m)+k_\eta(P_{-n}\otimes I_m)=1$。直接展开算子：

$$
P_{n_3}+P_{n_4}=\frac{1}{2}\!\left(I_2+\frac{3}{5}\sigma_x+\frac{4}{5}\sigma_z\right)+\frac{1}{2}\!\left(I_2-\frac{3}{5}\sigma_x+\frac{4}{5}\sigma_z\right)=I_2+\frac{4}{5}\sigma_z=\frac{9}{5}P_{n_1}+\frac{1}{5}P_{n_2}.
$$

代入 $n_{3,z}^3=n_{4,z}^3=\frac{64}{125}$、$n_{1,z}^3=1$、$n_{2,z}^3=-1$，左端值为 $1+\frac{64}{125}\eta$，右端值为 $\frac{9}{10}(1+\eta)+\frac{1}{10}(1-\eta)=1+\frac{4}{5}\eta=1+\frac{100}{125}\eta$，相减即得 $-\frac{36}{125}\eta\ne0$。

对第 2 项，同基内由 $\langle v_{s,k},v_{s,k'}\rangle=\frac{1}{3}\sum_{j=0}^2\omega^{(k'-k)j}=\delta_{kk'}$ 知每组 $\{P_{b,k}\}_{k=0}^2$ 满足 $\sum_{k=0}^2P_{b,k}=I_3$；跨基上当 $a\not\equiv0\pmod3$ 时，高斯和模方 $|\sum_{j=0}^2\omega^{aj^2+bj}|^2=\sum_{r=0}^2\omega^{ar^2+br}\sum_{\ell=0}^2\omega^{2ar\ell}=3$（仅 $r=0$ 项存活），故标准基与三组 $\{v_{s,k}\}_{k=0}^2$（$s=0,1,2$）两两跨基内积模方均为 $\frac{1}{3}$。对不同基 $b\ne b'$，$\operatorname{Tr}((P_{b,k}-\frac{1}{3}I_3)(P_{b',k'}-\frac{1}{3}I_3))=\frac{1}{3}-\frac{1}{3}=0$，四个基各自的无迹二维子空间两两正交，维数之和为 $4\times2=8$，连同 $I_3$ 张成全部 $9$ 维 $\operatorname{Herm}(\mathbb{C}^3)$，且正交展开对一般 $H\in\operatorname{Herm}(\mathbb{C}^3)$ 给出 $H=\sum_{b=0}^3\sum_{k=0}^2\operatorname{Tr}(HP_{b,k})P_{b,k}-(\operatorname{Tr}H)I_3$，故对一切迹一厄米算子（$\operatorname{Tr}H=1$）直接化为重构公式 $H=\sum_{b=0}^3\sum_{k=0}^2\operatorname{Tr}(HP_{b,k})P_{b,k}-I_3$。四个基的归一关系 $e_0-\sum_{k=0}^2e_{b,k}$（$b=0,1,2,3$；若将每基写为两步二元切分树 $I_3=P_{b,0}+Q_b$、$Q_b=P_{b,1}+P_{b,2}$，则多 $4$ 个辅助算子与 $4$ 条独立定义关系，余维不变）线性无关（第 $b$ 条含独有变量 $e_{b,1},e_{b,2}$），故 $\dim_{\mathbb{R}}L_{\mathfrak{M}_{12}}=4=13-9$，满足定理 6.2。对 $u=\frac{1}{\sqrt{21}}(1,2,4)^{\mathsf T}$，$\|u\|^2=\frac{1+4+16}{21}=1$，故 $H_*=\frac{8}{15}I_3-\frac{3}{5}uu^\dagger$ 在 $u$ 上的特征值为 $\frac{8}{15}-\frac{3}{5}=-\frac{1}{15}<0$，在 $u^\perp$ 上为二重 $\frac{8}{15}$，迹为 $-\frac{1}{15}+\frac{16}{15}=1$。在标准基上 $|\langle u,e_k\rangle|^2\in\{\frac{1}{21},\frac{4}{21},\frac{16}{21}\}$，对应 $k_*$ 值为 $\{\frac{53}{105},\frac{44}{105},\frac{8}{105}\}$；在三组二次相位基上利用 $2^2\equiv1\pmod3$ 直接计算 $63|\langle u,v_{s,k}\rangle|^2=|1+2\omega^{s+k}+4\omega^{s+2k}|^2=21+4\operatorname{Re}(\omega^{s+k})+8\operatorname{Re}(\omega^{s+2k})+16\operatorname{Re}(\omega^k)$，在 $s=0$ 时取 $\{49,7,7\}$（在 $v_{0,0}=\frac{1}{\sqrt{3}}(1,1,1)^{\mathsf T}$ 处取最大值 $49$，即 $|\langle u,v_{0,0}\rangle|^2=\frac{7}{9}$）、在 $s\in\{1,2\}$ 时取 $\{31,19,13\}$，故 $k_*(P_{s+1,k})=\frac{56-63|\langle u,v_{s,k}\rangle|^2}{105}\in\{\frac{7}{105},\frac{25}{105},\frac{37}{105},\frac{43}{105},\frac{49}{105}\}$；合并四组基立得 $\min_{b,k}k_*(P_{b,k})=\frac{7}{105}=\frac{1}{15}>0$ 且 $\max_{b,k}k_*(P_{b,k})=\frac{53}{105}<1$（若显式并入二元树辅助秩二投影 $Q_b=I_3-P_{b,0}$，亦有 $k_*(Q_b)=1-k_*(P_{b,0})\in[\frac{52}{105},\frac{14}{15}]\subset(0,1)$）。这证明有限线性菜单不等式无法替代非多面体半正定锥的全方向（或算子纯度／对偶正锥）正性条件。∎

## 7. 单本体参考切分下的完全正性、算子纯度亏格正交分类与 Lüders 更新判据

**定义 7.1（单本体内部参考切分、算子三轴纯度亏格与二元仪器）。** 设单本体复载体分解为内部参考切分与待作用子系统的复张量扇区 $\mathcal{H}_{\mathrm{ref}}\otimes\mathcal{H}_S$，其中 $\mathcal{H}_{\mathrm{ref}}=\mathbb{C}^d$，$\mathcal{H}_S=\mathbb{C}^d$（$d\ge2$），固定标准正交基 $\{|j\rangle\}_{j=0}^{d-1}$ 下的最大纠缠纯参考态

$$
|\Phi_d^+\rangle=\frac{1}{\sqrt{d}}\sum_{j=0}^{d-1}|j\rangle\otimes|j\rangle,\qquad P_{\Phi_d^+}=|\Phi_d^+\rangle\langle\Phi_d^+|.
$$

对任意保持厄米性的复线性映射 $\Lambda:M_d(\mathbb{C})\to M_{d'}(\mathbb{C})$（等价地，实线性映射 $\Lambda:\operatorname{Herm}(\mathbb{C}^d)\to\operatorname{Herm}(\mathbb{C}^{d'})$ 的唯一复线性扩张），定义其在单本体参考切分上的联合输出算子为

$$
R_\Lambda=(I_d\otimes\Lambda)(P_{\Phi_d^+})\in\operatorname{Herm}(\mathbb{C}^d\otimes\mathbb{C}^{d'}).
$$

当 $d=d'=2$ 时，沿用 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 定义 5.1 与定理 5.2 在 $m=1$ 时的复算子三轴分块：将任意迹一厄米算子 $R=\frac{1}{2}(I_2\otimes S+\sigma_x\otimes X+\sigma_y\otimes Y+\sigma_z\otimes Z)\in\operatorname{Herm}(\mathbb{C}^2\otimes\mathbb{C}^2)$（其中 $\operatorname{Tr}_{\mathrm{ref}}$ 始终表示对第一张量因子 $\mathbb{C}^2$ 求偏迹，$S=\operatorname{Tr}_{\mathrm{ref}}(R)$）的算子三轴纯度亏格记为

$$
D_1(R)=2S-S^2-X^2-Y^2-Z^2=2\,\operatorname{Tr}_{\mathrm{ref}}(R-R^2)\in\operatorname{Herm}(\mathbb{C}^2).
$$

二元量子仪器是指一对保持厄米性的复线性映射 $\{\Lambda_0,\Lambda_1\}$（$\Lambda_b:M_d(\mathbb{C})\to M_d(\mathbb{C})$），其和 $\Lambda_0+\Lambda_1$ 保迹。

**定理 7.2（参考切分联合正性、算子纯度亏格的 Bloch 正交分类与 Lüders 投影更新充要定理）。**

1. **单本体参考切分联合正性与 Kraus 记录等距实现（文献先例桥接步骤：Choi 1975 定理 1–2；Kraus 1971）**：在定义 7.1 下，二元仪器 $\{\Lambda_0,\Lambda_1\}$ 的两个分支在单本体参考切分上保持联合半正定

$$
R_{\Lambda_b}=(I_d\otimes\Lambda_b)(P_{\Phi_d^+})\succeq0\qquad(b\in\{0,1\})
$$

当且仅当每个 $\Lambda_b$ 完全正（Choi 1975 定理 2），亦当且仅当存在有限 Kraus 算子族 $\{K_{b\alpha}\}_{\alpha=1}^{r_b}\subseteq M_d(\mathbb{C})$（Choi 1975 定理 1；Kraus 1971；$r_b=\operatorname{rank}R_{\Lambda_b}\le d^2$，$\sum_{b=0}^1\sum_{\alpha=1}^{r_b}K_{b\alpha}^\dagger K_{b\alpha}=I_d$），使得 $\Lambda_b(\rho)=\sum_{\alpha=1}^{r_b}K_{b\alpha}\rho K_{b\alpha}^\dagger$，即记 $r=\max\{1,r_0,r_1\}$（对 $r_b<\alpha\le r$ 置 $K_{b\alpha}=0$）后由单本体内部记录等距 $V:\mathbb{C}^d\to\mathbb{C}^2\otimes\mathbb{C}^r\otimes\mathbb{C}^d$，$V|\psi\rangle=\sum_{b=0}^1\sum_{\alpha=1}^r|b\rangle\otimes|\alpha\rangle\otimes K_{b\alpha}|\psi\rangle$（[`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 命题 4.3）按记录标签投影并对内部上下文偏迹实现；

2. **二能级保迹映射的算子三轴纯度亏格显式公式与 $O(3)$ 正交二分**：设 $d=d'=2$，$\Lambda:M_2(\mathbb{C})\to M_2(\mathbb{C})$ 为任意保持厄米性且保迹的映射，其 Bloch 仿射作用由 $\Lambda(\frac{1}{2}(I_2+r\cdot\sigma))=\frac{1}{2}(I_2+(t+Mr)\cdot\sigma)$（$t\in\mathbb{R}^3$，$M\in M_3(\mathbb{R})$）唯一确定。则其参考切分联合算子 $R_\Lambda=(I_2\otimes\Lambda)(P_{\Phi_2^+})$ 与对称侧算子 $\widetilde{R}_\Lambda=(\Lambda\otimes I_2)(P_{\Phi_2^+})$ 的算子三轴纯度亏格精确为

$$
\begin{aligned}
D_1(R_\Lambda)&=\frac{1}{4}\bigl(3-\|t\|^2-\|M\|_F^2\bigr)I_2+\frac{1}{2}(t\cdot\sigma),\\
D_1(\widetilde{R}_\Lambda)&=\frac{1}{4}\bigl(3-\|t\|^2-\|M\|_F^2\bigr)I_2-\frac{1}{2}\bigl((CM^{\mathsf T}t)\cdot\sigma\bigr),\qquad C=\operatorname{diag}(1,-1,1),
\end{aligned}
$$

其中 $\|M\|_F^2=\operatorname{Tr}(M^{\mathsf T}M)$。特别地，若 $\Lambda$ 是单系统正映射（即把 Bloch 球映入自身），则

$$
D_1(R_\Lambda)=0\iff D_1(\widetilde{R}_\Lambda)=0\iff t=0\text{ 且 }M\in O(3),
$$

此时恰分裂为两个连通分支：
   - 当 $\det M=+1$（$M\in SO(3)$）时，$\Lambda(\rho)=U\rho U^\dagger$（$U\in SU(2)$）为酉完全正通道，$R_\Lambda\succeq0$ 为秩一纯态；
   - 当 $\det M=-1$（$M\in O(3)\setminus SO(3)$）时，$\Lambda(\rho)=U\rho^{\mathsf T}U^\dagger$（$U\in SU(2)$），此时 $R_\Lambda=(I_2\otimes U)(\frac{1}{2}F)(I_2\otimes U^\dagger)$（其中 $F$ 为交换算子），满足 $D_1(R_\Lambda)=0$ 与一切乘积向量期望非负，但最小特征值恒为 $-\frac{1}{2}<0$（当 $U=I_2$ 时恰退化为 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 命题 7.1 的算子 $F/2$）；

3. **锐二元 Lüders 投影更新的充要特征空间不扰动判据（文献先例桥接步骤：Lüders 1951；Busch–Lahti–Mittelstaedt 1991；Busch 2008 定理 5）**：设 $\{\Lambda_0,\Lambda_1\}$ 为满足第 1 项联合正性的二元 CP 仪器，其效果算子为一对互补正交投影 $E_b=\Lambda_b^\dagger(I_d)=P_b$（$P_0+P_1=I_d$，$P_b^2=P_b=P_b^\dagger$）。则该仪器对一切输入 $\rho\in M_d(\mathbb{C})$ 均具有 Lüders 形式（Lüders 1951）

$$
\Lambda_b(\rho)=P_b\rho P_b\qquad(b\in\{0,1\})
$$

当且仅当满足理想测量意义下的**本征纯态不扰动性**（Busch–Lahti–Mittelstaedt 1991；Busch 2008 定理 5）：对每个 $b\in\{0,1\}$ 及一切单位向量 $|\psi\rangle\in\operatorname{Ran}P_b$（$\|\psi\|=1$），有 $\Lambda_b(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|$。

**证明。** 第 1 项中 $R_{\Lambda_b}\succeq0\iff\Lambda_b$ 完全正 $\iff$ Kraus 表示 $\Lambda_b(\rho)=\sum_{\alpha=1}^{r_b}K_{b\alpha}\rho K_{b\alpha}^\dagger$ 为 Choi 1975 定理 1 与定理 2 的标准结论；保迹条件 $(\Lambda_0+\Lambda_1)^\dagger(I_d)=I_d$ 即为 $\sum_{b,\alpha}K_{b\alpha}^\dagger K_{b\alpha}=I_d$，这使 $V|\psi\rangle=\sum_{b,\alpha}|b\rangle\otimes|\alpha\rangle\otimes K_{b\alpha}|\psi\rangle$ 精确满足 $V^\dagger V=I_d$ 且 $\operatorname{Tr}_{\mathbb{C}^r}\bigl((\langle b|\otimes I_r\otimes I_d)V\rho V^\dagger(|b\rangle\otimes I_r\otimes I_d)\bigr)=\Lambda_b(\rho)$。

现证第 2 项。利用 $P_{\Phi_2^+}=\frac{1}{4}(I_2\otimes I_2+\sigma_x\otimes\sigma_x-\sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z)$、$\Lambda(I_2)=I_2+t\cdot\sigma$ 与 $\Lambda(\sigma_j)=\sum_{a=1}^3 M_{aj}\sigma_a$（$j=1,2,3$），直接写出 $R_\Lambda=(I_2\otimes\Lambda)(P_{\Phi_2^+})$ 的四块系数：

$$
S=\frac{1}{2}(I_2+t\cdot\sigma),\quad
X=\frac{1}{2}\sum_{a=1}^{3}M_{a1}\sigma_a,\quad
Y=-\frac{1}{2}\sum_{a=1}^{3}M_{a2}\sigma_a,\quad
Z=\frac{1}{2}\sum_{a=1}^{3}M_{a3}\sigma_a.
$$

由 $(v\cdot\sigma)^2=\|v\|^2I_2$（$v\in\mathbb{R}^3$）得 $X^2+Y^2+Z^2=\frac{1}{4}(\sum_{j=1}^3\sum_{a=1}^3 M_{aj}^2)I_2=\frac{1}{4}\|M\|_F^2I_2$，同时 $2S-S^2=(I_2+t\cdot\sigma)-\frac{1}{4}((1+\|t\|^2)I_2+2t\cdot\sigma)=\frac{1}{4}(3-\|t\|^2)I_2+\frac{1}{2}(t\cdot\sigma)$，相减即得 $D_1(R_\Lambda)$ 公式。同理对 $\widetilde{R}_\Lambda=(\Lambda\otimes I_2)(P_{\Phi_2^+})$，将第一因子按 $\{I_2,\sigma_x,\sigma_y,\sigma_z\}$ 重排，有

$$
\widetilde{S}=\frac{1}{2}I_2,\qquad
\widetilde{B}_a=\frac{1}{2}\!\left(t_aI_2+\sum_{j=1}^{3}M_{aj}c_j\sigma_j\right)\quad(a=1,2,3;\ (c_1,c_2,c_3)=(1,-1,1)).
$$

平方求和：$\sum_{a=1}^3\widetilde{B}_a^2=\frac{1}{4}\sum_{a=1}^3\bigl[(t_a^2+\sum_{j=1}^3 M_{aj}^2)I_2+2t_a\sum_{j=1}^3 M_{aj}c_j\sigma_j\bigr]=\frac{1}{4}(\|t\|^2+\|M\|_F^2)I_2+\frac{1}{2}((CM^{\mathsf T}t)\cdot\sigma)$，从 $2\widetilde{S}-\widetilde{S}^2=\frac{3}{4}I_2$ 中减去即得 $D_1(\widetilde{R}_\Lambda)$ 公式。

现设 $\Lambda$ 为正映射，故对一切单位向量 $n\in S^2$ 有 $\|t+Mn\|\le1$。首先，由 $\{I_2,\sigma_1,\sigma_2,\sigma_3\}$ 线性无关，$D_1(R_\Lambda)=0$ 直接当且仅当 $t=0$ 且 $\|M\|_F^2=3$。其次，对 $D_1(\widetilde{R}_\Lambda)=0$，在三个标准轴上对 $\|t+Me_j\|^2+\|t-Me_j\|^2=2\|t\|^2+2\|Me_j\|^2\le2$ 关于 $j=1,2,3$ 求和，得 $3\|t\|^2+\|M\|_F^2\le3$；若 $D_1(\widetilde{R}_\Lambda)=0$，其标量迹部分迫使 $\|t\|^2+\|M\|_F^2=3$，与前式相减得 $2\|t\|^2\le0$，同样迫使 $t=0$ 与 $\|M\|_F^2=3$。当 $t=0$ 时，$\Lambda$ 正等价于算子范数 $\|M\|_{\mathrm{op}}\le1$，即 $M$ 的三个奇异值满足 $0\le s_1,s_2,s_3\le1$；结合 $\sum_{j=1}^3 s_j^2=\|M\|_F^2=3$，当且仅当 $s_1=s_2=s_3=1$，即 $M\in O(3)$。由双覆盖同态 $SU(2)\to SO(3)$：当 $\det M=+1$ 时 $M$ 由某个 $U\in SU(2)$ 共轭实现，$\Lambda(\rho)=U\rho U^\dagger$；当 $\det M=-1$ 时 $MC\in SO(3)$（因 $\det C=-1$），而转置映射 $\rho\mapsto\rho^{\mathsf T}$ 的 Bloch 矩阵恰为 $C=\operatorname{diag}(1,-1,1)$，故 $\Lambda(\rho)=U\rho^{\mathsf T}U^\dagger$，且 $(I_2\otimes T)(P_{\Phi_2^+})=\frac{1}{4}(I_2\otimes I_2+\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z)=\frac{1}{2}F$，酉共轭保持谱 $\{\frac{1}{2},\frac{1}{2},\frac{1}{2},-\frac{1}{2}\}$ 与乘积态非负性。

最后证第 3 项。必要性显然（对 $|\psi\rangle\in\operatorname{Ran}P_b$ 有 $P_b|\psi\rangle=|\psi\rangle$）。反之，设 $\Lambda_b(\rho)=\sum_{\alpha=1}^{r_b}K_{b\alpha}\rho K_{b\alpha}^\dagger$ 满足 $\sum_{\alpha=1}^{r_b}K_{b\alpha}^\dagger K_{b\alpha}=P_b$ 且对一切单位 $|\psi\rangle\in\operatorname{Ran}P_b$ 有 $\Lambda_b(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|$。先对任意 $|\phi\rangle\in\ker P_b=\operatorname{Ran}(I_d-P_b)$，有 $\sum_{\alpha}\|K_{b\alpha}|\phi\rangle\|^2=\langle\phi,P_b\phi\rangle=0$，故 $K_{b\alpha}(I_d-P_b)=0$，即 $K_{b\alpha}=K_{b\alpha}P_b$ 对一切 $\alpha$ 成立。再对任意单位 $|\psi\rangle\in\operatorname{Ran}P_b$，取 $|\psi\rangle\langle\psi|=\sum_{\alpha=1}^{r_b}|K_{b\alpha}\psi\rangle\langle K_{b\alpha}\psi|$：对任意正交于 $|\psi\rangle$ 的 $|w\rangle\perp|\psi\rangle$，两边取 $\langle w,\cdot\,w\rangle$ 得 $\sum_\alpha|\langle w,K_{b\alpha}\psi\rangle|^2=0$，故对每个 $\alpha$ 存在复标量 $c_{b\alpha}(\psi)\in\mathbb{C}$ 使 $K_{b\alpha}|\psi\rangle=c_{b\alpha}(\psi)|\psi\rangle$。若 $\operatorname{Ran}P_b$ 中存在线性无关向量 $|\psi_1\rangle,|\psi_2\rangle$，由 $K_{b\alpha}(|\psi_1\rangle+|\psi_2\rangle)=c_{b\alpha}(\psi_1)|\psi_1\rangle+c_{b\alpha}(\psi_2)|\psi_2\rangle$ 同时必须平行于 $|\psi_1\rangle+|\psi_2\rangle$，迫使 $c_{b\alpha}(\psi_1)=c_{b\alpha}(\psi_2)=c_{b\alpha}$ 为与 $|\psi\rangle\in\operatorname{Ran}P_b$ 无关的常数（$\operatorname{rank}P_b\le1$ 时平凡成立）。于是 $K_{b\alpha}=K_{b\alpha}P_b=c_{b\alpha}P_b$；代入 $\sum_\alpha K_{b\alpha}^\dagger K_{b\alpha}=P_b$（当 $P_b\ne0$ 时）得 $\sum_\alpha|c_{b\alpha}|^2=1$（$P_b=0$ 时 $K_{b\alpha}=0$），从而对一切 $\rho\in M_d(\mathbb{C})$ 有 $\Lambda_b(\rho)=\sum_\alpha|c_{b\alpha}|^2 P_b\rho P_b=P_b\rho P_b$。∎

**命题 7.3（非 CP 正映射不满足纯度亏格消失与可重复锐 CP 仪器偏离 Lüders 更新的双反例）。**

1. **混噪转置正映射的纯度亏格非零性**：在 $d=d'=2$ 上，对参数 $t\in(\frac{1}{3},1)$ 定义保迹单系统正映射 $\Lambda_t(X)=tX^{\mathsf T}+(1-t)\frac{\operatorname{Tr}X}{2}I_2$（将 Bloch 球均匀收缩并反射为半径 $t<1$ 的球）。则其参考切分输出 $R_{\Lambda_t}=\frac{t}{2}F+\frac{1-t}{4}I_4$ 具有负特征值 $\frac{1-3t}{4}<0$（例如 $t=\frac{1}{2}$ 时为 $-\frac{1}{8}<0$），因而不是完全正映射；但其算子三轴纯度亏格为严格正标量倍数

$$
D_1(R_{\Lambda_t})=\frac{3(1-t^2)}{4}I_2\succ0\qquad\left(t=\frac{1}{2}\text{ 时 }D_1(R_{1/2})=\frac{9}{16}I_2\ne0\right),
$$

证明单系统正且非 CP 的映射一般不满足 $D_1(R_\Lambda)=0$（仅定理 7.2 第 2 项中的满球正交自同构分支满足 $D_1=0$）；

2. **退化锐投影下可重复正交记录但非 Lüders 的 CP 仪器**：在 $\mathbb{C}^4$ 上令秩二互补正交投影为 $P_0=|0\rangle\langle0|+|1\rangle\langle1|$、$P_1=|2\rangle\langle2|+|3\rangle\langle3|$，令 $U_0=|0\rangle\langle1|+|1\rangle\langle0|+|2\rangle\langle2|+|3\rangle\langle3|$，定义单 Kraus 二元仪器 $\Lambda_0(\rho)=K_0\rho K_0^\dagger$、$\Lambda_1(\rho)=K_1\rho K_1^\dagger$，其中 $K_0=U_0P_0$、$K_1=P_1$。则 $\{\Lambda_0,\Lambda_1\}$ 完全正、由精确二元记录等距 $V|\psi\rangle=|0\rangle\otimes K_0|\psi\rangle+|1\rangle\otimes K_1|\psi\rangle$ 实现、效果算子恰为锐正交投影 $(P_0,P_1)$，且满足测量结果可重复性（$\operatorname{Tr}(P_{b'}\Lambda_b(\rho))=\delta_{bb'}\operatorname{Tr}(P_b\rho)$，即 $\Lambda_{b'}\circ\Lambda_b=0$ 对 $b'\ne b$），但 $\Lambda_0(|0\rangle\langle0|)=|1\rangle\langle1|\ne|0\rangle\langle0|=P_0|0\rangle\langle0|P_0$，证明删去定理 7.2 第 3 项的特征子空间内纯态不扰动前件后 Lüders 更新不唯一。

**证明。** 对第 1 项，$\Lambda_t$ 的 Bloch 参数为平移向量 $0$ 与矩阵 $M_t=t\operatorname{diag}(1,-1,1)$，对 $\|r\|\le1$ 有 $\|M_tr\|=t\|r\|\le t<1$，故 $\Lambda_t$ 正且保迹。由 $F$ 在三重对称子空间上特征值为 $+1$、在一维反对称 Bell 态 $\frac{1}{\sqrt{2}}(|01\rangle-|10\rangle)$ 上特征值为 $-1$，知 $R_{\Lambda_t}=\frac{t}{2}F+\frac{1-t}{4}I_4$ 的特征值为三重 $\frac{1+t}{4}$ 与一重 $\frac{1-3t}{4}$；当 $t\in(\frac{1}{3},1)$ 时 $\frac{1-3t}{4}<0$。代入定理 7.2 第 2 项公式（$\|0\|^2=0$，$\|M_t\|_F^2=3t^2$），立得 $D_1(R_{\Lambda_t})=\frac{1}{4}(3-3t^2)I_2=\frac{3(1-t^2)}{4}I_2\succ0$。

对第 2 项，$U_0^\dagger=U_0$、$U_0^2=I_4$ 且 $[U_0,P_0]=0$，故 $K_0^\dagger K_0=P_0U_0^2P_0=P_0$、$K_1^\dagger K_1=P_1$、$K_0^\dagger K_0+K_1^\dagger K_1=I_4$。对 $b'\ne b$，$P_1K_0=P_1U_0P_0=U_0P_1P_0=0$ 且 $P_0K_1=P_0P_1=0$，故 $\operatorname{Tr}(P_{b'}\Lambda_b(\rho))=0$ 且 $\operatorname{Tr}(P_b\Lambda_b(\rho))=\operatorname{Tr}(K_b^\dagger P_bK_b\rho)=\operatorname{Tr}(P_b\rho)$；然而 $K_0|0\rangle=U_0|0\rangle=|1\rangle$，故 $\Lambda_0(|0\rangle\langle0|)=|1\rangle\langle1|\ne|0\rangle\langle0|$。∎

## 8. 有限比特量化正守卫读器的全历史测度同构稳定性与双侧失效边界

**定义 8.1（静态闭下水平集有限精度量化器与量化正守卫配置律）。** 沿用 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定义 205.1、206.1–206.2 与假设 206.3 的全部固定读器对象：局部十五门轨迹 $\theta_i^\lambda(\tau)$（$i\in\{0,1\}$，$\tau\in[0,15]$），最小正块质量 $m_*\in(0,1]$，原正守卫阈值 $\vartheta=\frac{m_*}{16}\in(0,\frac{1}{16}]$，参数邻域 $|\lambda-\alpha|<\eta=\min\{\frac{\alpha}{2},\frac{2\pi-\alpha}{2},\frac{\sqrt{m_*}}{96}\}$，以及在 $D_q(\Psi)>0$ 纤维上的精确归一权重 $p_\Psi(q,z)=\frac{|\Psi(q,z)|^2}{D_q(\Psi)}\in[0,1]$。

误差包络为 $\delta\ge0$ 的**静态有限精度量化器**是指值域有限的函数 $Q:[0,1]\to[0,1]$，满足一致误差界

$$
\sup_{x\in[0,1]}|Q(x)-x|\le\delta.
$$

称 $Q$ 对阈值 $\vartheta$ 具有**闭触发下水平集**，若集合 $S_{Q,\vartheta}=\{x\in[0,1]:Q(x)\le\vartheta\}$ 为 $[0,1]$ 的闭子集（例如任意单调不减左连续量化器，特别是分辨位数 $b\in\mathbb{Z}_{>0}$、步长 $2^{-b}$ 的向上网格比较量化器 $Q_{\uparrow,b}(0)=0$、$Q_{\uparrow,b}(x)=2^{-b}\lceil 2^bx\rceil$ 对 $x\in(0,1]$，其触发集精确为闭区间 $S_{Q_{\uparrow,b},\vartheta}=[0,2^{-b}\lfloor 2^b\vartheta\rfloor]$）。

**量化正守卫配置律** $G_j^Q$ 是指将假设 206.3 式 (206.3) 中的两次精确权重比较统一替换为有限精度读数 $Q$ 的比较，其余接缝顺序、等待规则、源驱动与因果档案拉回类一字不改：在二点块 $\{z,z^{\leftrightarrow j}\}$ 上，

$$
G_j^Q(\Psi,q,z)=1\iff D_q(\Psi)>0,\quad Q\bigl(p_\Psi(q,z)\bigr)\le\vartheta,\quad Q\bigl(p_\Psi(q,z^{\leftrightarrow j})\bigr)\ge2\vartheta,
$$

单点块或 $D_q(\Psi)=0$ 时 $G_j^Q=0$；从上次检查后 $G_j^Q=0$ 的时刻 $s_0\in[0,1)$ 起，下一事件时刻仍取 $\{s \in (s_0, 1] : G_j^Q(\widehat{\Psi}_s, q, z) = 1\}$ 的首点。

**定理 8.2（$\delta<\frac{3}{4}\vartheta$ 下的有限比特量化正守卫适定性、精确报告与全历史测度同构定理）。** 在定义 8.1 下，设静态有限精度量化器 $Q:[0,1]\to[0,1]$ 对 $\vartheta$ 具有闭触发下水平集 $S_{Q,\vartheta}$，且其一致量化误差满足严格上界

$$
0\le\delta<\frac{3}{4}\vartheta=\frac{3m_*}{64}
$$

（特别地，对向上 $b$ 比特网格量化器 $Q_{\uparrow,b}$，只要比特数满足 $b>\log_2\!\left(\frac{64}{3m_*}\right)$ 即有 $\delta=2^{-b}<\frac{3}{4}\vartheta$）。则在同一参数邻域 $|\lambda-\alpha|<\eta$ 内，对两个分支 $i\in\{0,1\}$、一切十一地址有限前缀 $a$ 后的正支撑入口 $(q,z_*)$（$q\in E_i$）及一切七地址外生未来 $f$，量化正守卫系统同时满足：

1. **首点闭集取得、零入口误跳与有界跳数**：十五个单位调用生成唯一确定的右连续局部配置路径 $r_i^{\lambda,Q}:[0,15]\to S_i$，每次等待后的触发时刻集在 $(s_0,1]$ 内为闭集故首点必然取得；全部十五门的入口检查恒为 $G_{d_k}^Q=0$（零入口跳动）；每次跳动前精确权重满足 $p_i^\lambda(\tau^-,z)\in[\max(0,\vartheta-\delta),\vartheta+\delta]$，跳后精确权重满足

$$
p_i^\lambda(\tau^+,z^{\leftrightarrow j})>11\vartheta-\delta>\frac{41}{4}\vartheta,
$$

跳后量化读数满足 $Q(p_i^\lambda(\tau^+,z^{\leftrightarrow j}))>11\vartheta-2\delta>\frac{19}{2}\vartheta>\vartheta$（零同刻往返跳动）；同一单位门内相邻两次跳动的时间间隔严格大于

$$
\Delta s_{\min}(\delta)=\frac{10\vartheta-2\delta}{8\pi}>\frac{17\vartheta}{16\pi}>0,
$$

故每门跳动次数至多为 $N_Q(\delta)=1+\left\lfloor\frac{8\pi}{10\vartheta-2\delta}\right\rfloor<\infty$（十五门总跳数至多 $15N_Q(\delta)$）；

2. **统一右值裕量与零差错精确报告 $J^{Q}=L$**：全区间右值满足 $Q(p_i^\lambda(\tau,r_i^{\lambda,Q}(\tau)))>\vartheta$ 及精确权重下界

$$
p_i^\lambda\bigl(\tau,r_i^{\lambda,Q}(\tau)\bigr)>\vartheta-\delta>\frac{\vartheta}{4}\qquad(0\le\tau\le15),
$$

从而终端配置 $z_i^{\lambda,Q}=r_i^{\lambda,Q}(15)$ 必满足 $(z_i^{\lambda,Q})_{13}=i$，在全部正质量源列上零差错输出精确逻辑切口位 $J^Q=L$；

3. **十一地址前缀与七地址未来的全历史测度同构保持**：将 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 208.2 中的精确读器微历史映射替换为 $r_i^{\lambda,Q}$ 后，扩展程序在全部可数原程序对 $(a,f)$、全部 $1024$ 旧标签、原跳时、精确报告 $J^Q=L$ 与因果档案拉回类上与原理想比较过程保持完全相同的概率律与双射历史测度同构。

**证明。** 直接消费 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 207.1 中仅依赖酉门脉冲、不依赖配置跳动规则且由酉传播范数扰动界 (207.3) 给出的三项波函数不等式 (207.5)、(207.7) 与 (207.8)：在 $|\lambda-\alpha|<\eta$ 上，各门守恒块质量满足 $m_{i,k,B}^0=0\Rightarrow m_B^\lambda<\frac{\vartheta}{4}$ 与 $m_{i,k,B}^0>0\Rightarrow m_B^\lambda>12\vartheta$；单脉冲内任一固定坐标权重导数满足 $|p'(s)|<8\pi$；且十五门终端相反报告子空间总质量满足 $\sum_{z:z_{13}\ne i}|\theta_i^\lambda(15,z)|^2<\frac{\vartheta}{4}$。

先在单门 $k\in\{1,\ldots,15\}$ 上作归纳。在 $k=1$ 入口有 $p_i^\lambda(0,z_*)=1$，故 $Q(1)\ge1-\delta>1-\frac{3}{4}\vartheta>\vartheta$（因 $\vartheta\le\frac{1}{16}$），入口守卫 $G_{d_1}^Q=0$。一般地，设第 $k$ 门入口处当前配置 $z$ 满足 $Q(p_i^\lambda(k-1,z))>\vartheta$。则入口守卫立即为 $0$（零入口跳动），且入口精确权重满足 $p_i^\lambda(k-1,z)\ge Q(p_i^\lambda(k-1,z))-\delta>\vartheta-\delta>\frac{\vartheta}{4}$。因该块总质量 $m_B^\lambda\ge p_i^\lambda(k-1,z)>\frac{\vartheta}{4}$，由块质量二分式 (207.5) 知该块不可能是扰动零块，必属于正质量块：$m_B^\lambda>12\vartheta$ 在整段闭脉冲 $[k-1,k]$ 上恒定。

若该块为单点块，则 $G_{d_k}^Q\equiv0$ 且 $p_i^\lambda(k-1+s,z)=m_B^\lambda>12\vartheta>\vartheta+\delta$，故整段满足 $Q(p_i^\lambda)\ge p_i^\lambda-\delta>11\vartheta>\vartheta$。若该块为二点块 $\{z,z^{\leftrightarrow j}\}$，记 $p(s)=p_i^\lambda(k-1+s,z)$，$p_{\leftrightarrow}(s)=m_B^\lambda-p(s)$。注意对任意满足 $p(s)\le\vartheta+\delta$ 的时刻 $s\in[0,1]$，伙伴坐标精确权重恒满足

$$
p_{\leftrightarrow}(s)=m_B^\lambda-p(s)>12\vartheta-(\vartheta+\delta)=11\vartheta-\delta,
$$

故其量化读数恒满足

$$
Q\bigl(p_{\leftrightarrow}(s)\bigr)\ge p_{\leftrightarrow}(s)-\delta>11\vartheta-2\delta>\left(11-\frac{3}{2}\right)\vartheta=\frac{19}{2}\vartheta>2\vartheta.
$$

由于 $Q(p(s))\le\vartheta\Rightarrow p(s)\le Q(p(s))+\delta\le\vartheta+\delta$，上述不等式表明：在正质量二点块上，只要第一条件 $p(s)\in S_{Q,\vartheta}$ 成立，第二目的地可用条件 $Q(p_{\leftrightarrow}(s))\ge2\vartheta$ 自动严格成立。因此从任意满足 $G_{d_k}^Q=0$（即 $p(s_0)\notin S_{Q,\vartheta}$）的时刻 $s_0\in[0,1)$ 出发，触发时刻集合精确化简为

$$
\bigl\{s\in(s_0,1]:G_{d_k}^Q(\widehat{\Psi}_s,q,z)=1\bigr\}=\bigl\{s\in[s_0,1]:p(s)\in S_{Q,\vartheta}\bigr\}.
$$

因 $s\mapsto p(s)$ 连续且 $S_{Q,\vartheta}$ 是 $[0,1]$ 的闭子集，右端原像是紧区间 $[s_0,1]$ 的闭子集（且不含 $s_0$）。若该集合非空，必有严格大于 $s_0$ 的最小元 $s_1\in(s_0,1]$（首点精确取得，无需横截性）。在 $s_1$ 处跳前权重满足 $p(s_1)\in S_{Q,\vartheta}\subseteq[0,\vartheta+\delta]$，且首点最小性进一步迫使 $p(s_1)\in[\vartheta-\delta,\vartheta+\delta]=[\max(0,\vartheta-\delta),\vartheta+\delta]$（因 $\delta<\frac{3}{4}\vartheta$ 故 $\vartheta-\delta>\frac{\vartheta}{4}>0$；由 $|Q(x)-x|\le\delta$ 知对一切 $x>\vartheta+\delta$ 恒有 $Q(x)>\vartheta$ 且 $[0,\vartheta-\delta]\subseteq S_{Q,\vartheta}$，又由 $p(s_0)\notin S_{Q,\vartheta}$ 知 $p(s_0)>\vartheta-\delta$，若 $p(s_1)<\vartheta-\delta$ 则连续函数 $p$ 在 $(s_0,s_1)$ 内由介值定理必先取到 $\vartheta-\delta\in S_{Q,\vartheta}$，与 $s_1$ 的最小性矛盾）；跳至 $z^{\leftrightarrow j}$ 后，新当前权重满足 $p_{\leftrightarrow}(s_1)>11\vartheta-\delta$ 且 $Q(p_{\leftrightarrow}(s_1))>\frac{19}{2}\vartheta>\vartheta$，故跳后同刻守卫为 $0$。若此后在同一门内于 $s_2\in(s_1,1]$ 再次触发跳动，则新坐标权重须从 $>11\vartheta-\delta$ 连续下降至 $\le\vartheta+\delta$，变化量至少为 $(11\vartheta-\delta)-(\vartheta+\delta)=10\vartheta-2\delta>\frac{17}{2}\vartheta>0$；除以导数上界 $|p'|<8\pi$ 即得 $s_2-s_1>\frac{10\vartheta-2\delta}{8\pi}=\Delta s_{\min}(\delta)$，故单门内跳数至多为 $1+\lfloor\frac{1}{\Delta s_{\min}(\delta)}\rfloor=N_Q(\delta)$。出门时刻（含 $s=1$ 恰触发并先完成出门跳动的情形）右值恒满足 $Q(p_i^\lambda(k,r_i^{\lambda,Q}(k)))>\vartheta$。因 $Q$ 是仅依赖归一化纤维坐标权重的静态函数，第 $k$ 门的出门量化读数与第 $k+1$ 门的入口量化读数完全相等，故第 $k+1$ 门入口自动满足 $Q(p_i^\lambda(k,r_i^{\lambda,Q}(k)))>\vartheta$，归纳覆盖全部十五门，证毕第 1 项。

在 $\tau=15$ 处，由 $Q(p_i^\lambda(15,z_i^{\lambda,Q}))>\vartheta$ 得 $|\theta_i^\lambda(15,z_i^{\lambda,Q})|^2>\vartheta-\delta>\frac{\vartheta}{4}$；结合相反报告总质量上界 $\sum_{z:z_{13}\ne i}|\theta_i^\lambda(15,z)|^2<\frac{\vartheta}{4}$，若 $(z_i^{\lambda,Q})_{13}\ne i$ 则产生矛盾 $\frac{\vartheta}{4}<|\theta_i^\lambda(15,z_i^{\lambda,Q})|^2<\frac{\vartheta}{4}$，故必有 $(z_i^{\lambda,Q})_{13}=i$，即 $J^Q=L$，证毕第 2 项。

最后，在 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 208.2 的证明中，全局波函数演化 $\widehat{\Psi}^{\lambda}$、未来源跳动率中的严格正终端标量因子 $|\theta_i^\lambda(15,z_i^{\lambda,Q})|^2>\frac{\vartheta}{4}>0$ 消去（式 (208.6)）及因果档案核 $\kappa$ 仅依赖三个读器输出性质：①读器期间不改变逻辑源坐标 $q$；②对每个 $(i,\lambda)$ 局部微历史路径 $r_i^{\lambda,Q}$ 是仅由 $(i,\lambda)$ 唯一确定的有限跳右连续确定性函数（与前缀波幅大小、相位及隐藏过去无关）；③输出报告精确等于 $J^Q=L$。第 1–2 项已全部提供这三条性质，原定理 208.2 的双射编码与测度相等逐字保持，证毕第 3 项。∎

**命题 8.3（闭下水平集条件与量化步长界的双侧紧失效反例）。**

1. **右连续向下取整量化器在十五门读器上破坏连续时间首点取得**：取任意满足 $2^{-b}<\frac{3}{4}\vartheta$ 的右连续向下 $b$ 比特网格量化器 $Q_{\downarrow,b}(x)=2^{-b}\lfloor 2^bx\rfloor$（$\|Q_{\downarrow,b}-\mathrm{id}\|_\infty\le 2^{-b}<\frac{3}{4}\vartheta$）。其触发下水平集为右半开区间

$$
S_{Q_{\downarrow,b},\vartheta}=\bigl\{x\in[0,1]:2^{-b}\lfloor 2^bx\rfloor\le\vartheta\bigr\}=\bigl[0,\ (\lfloor 2^b\vartheta\rfloor+1)2^{-b}\bigr).
$$

在定理 8.2 的整个参数邻域 $|\lambda-\alpha|<\eta$ 内，对分支 $i=1$（及任意产生正质量 $E_1$ 支撑的十一地址前缀，如 $a=(9)$），定义 8.1 的十五门读器在首次使精确权重低于 $\vartheta_{\mathrm{open}}=(\lfloor 2^b\vartheta\rfloor+1)2^{-b}$ 的单位门 $k\in\{1,\ldots,15\}$ 上，从 $s_0=0$ 出发的触发时刻集合 $U=\{s\in(0,1]:G_{d_k}^{Q_{\downarrow,b}}=1\}$ 非空，但其下确界 $s_*=\inf U\in[0,1)$ 处必有 $Q_{\downarrow,b}(p(s_*))=\vartheta_{\mathrm{open}}>\vartheta$（$s_*\notin U$），故**首事件时刻不存在（下确界不可取得）**，证明定理 8.2 中“闭触发下水平集”前件不可删除；

2. **粗糙步长 $2^{-b}>\vartheta$ 使向上网格量化器精确退化为零幅失稳读器**：若向上 $b$ 比特网格量化器 $Q_{\uparrow,b}$（满足闭下水平集条件，$Q_{\uparrow,b}(0)=0$，对 $x>0$ 为 $2^{-b}\lceil 2^bx\rceil$）的量化步长超出阈值 $\delta=2^{-b}>\vartheta$，则对一切 $x\in(0,1]$ 均有 $Q_{\uparrow,b}(x)\ge 2^{-b}>\vartheta$，其闭触发下水平集坍缩为单点零集

$$
S_{Q_{\uparrow,b},\vartheta}=\{0\}.
$$

于是量化正守卫 $G_j^{Q_{\uparrow,b}}(\Psi,q,z)=1$ 逐点退化为 $p_\Psi(q,z)=0$（且 $Q_{\uparrow,b}(p_\Psi(q,z^{\leftrightarrow j}))\ge2\vartheta$），在定理 8.2 与 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 205.3 的交邻域 $0<|\lambda-\alpha|<\min(\eta,\eta_0)$ 内，全部十五门沿局部轨迹永不命中零点，配置恒停留在 $z_*$，实际报告恒坍缩为 $J_\lambda^{Q_{\uparrow,b}}\equiv0$；特别地，在定理 205.3 第 2 项的见证程序 $(a,f)=((9),\varepsilon)$ 上（此时 $\Pr(L=1)=x=\varphi^{-1}=\frac{\sqrt{5}-1}{2}>0$ 且条件错误率 $\Pr(J_\lambda^{Q_{\uparrow,b}}\ne L\mid L=1)=1$），产生不随 $|\lambda-\alpha|\to0$ 消失的固定总变差失配 $d_{\mathrm{TV}}(\mathcal{L}(J_\lambda^{Q_{\uparrow,b}}),\mathcal{L}(J_\alpha))=x=\varphi^{-1}>0$。

**证明。** 对第 1 项，整数底函数不等式 $\lfloor 2^bx\rfloor\le\lfloor 2^b\vartheta\rfloor$ 等价于 $2^bx<\lfloor 2^b\vartheta\rfloor+1$，即 $x<\vartheta_{\mathrm{open}}=(\lfloor 2^b\vartheta\rfloor+1)2^{-b}$。因 $\vartheta\le\frac{1}{16}$ 且 $2^{-b}<\frac{3}{4}\vartheta$，有 $\frac{\vartheta}{4}<\vartheta<\vartheta_{\mathrm{open}}\le\vartheta+2^{-b}<\frac{7}{4}\vartheta\le\frac{7}{64}<1$。在 $|\lambda-\alpha|<\eta$ 与分支 $i=1$ 上，初始权重满足 $p_1^\lambda(0,z_*)=1>\vartheta_{\mathrm{open}}$，而因 $(z_*)_{13}=0\ne1$，定理 207.1 式 (207.8) 给出终端权重 $p_1^\lambda(15,z_*)<\frac{\vartheta}{4}<\vartheta_{\mathrm{open}}$。由 $\tau\mapsto p_1^\lambda(\tau,z_*)$ 在 $[0,15]$ 上连续，集合 $\{m\in\{1,\ldots,15\}:\min_{s\in[0,1]}p_1^\lambda(m-1+s,z_*)<\vartheta_{\mathrm{open}}\}$ 非空，取其最小门号 $k$。对一切 $1\le m<k$ 及 $s\in[0,1]$，均有 $p_1^\lambda(m-1+s,z_*)\ge\vartheta_{\mathrm{open}}$，即 $Q_{\downarrow,b}(p_1^\lambda(m-1+s,z_*))\ge\vartheta_{\mathrm{open}}>\vartheta$，故前 $k-1$ 门守卫恒为 $0$，配置在进入第 $k$ 门时仍停留在 $z_*$ 且入口满足 $p(0)=p_1^\lambda(k-1,z_*)\ge\vartheta_{\mathrm{open}}>\frac{\vartheta}{4}$（$s_0=0$ 处 $G_{d_k}^{Q_{\downarrow,b}}=0$）。由块质量二分式 (207.5) 知含 $z_*$ 的第 $k$ 门守恒块必满足 $m_B^\lambda>12\vartheta$，且因 $\min_{s\in[0,1]}p(s)<\vartheta_{\mathrm{open}}\le p(0)$（单点块上 $p$ 恒为常数 $m_B^\lambda$），该块必为二点块 $\{z_*,z_*^{\leftrightarrow d_k}\}$；在该块上只要 $p(s)<\vartheta_{\mathrm{open}}$，就有 $Q_{\downarrow,b}(p_{\leftrightarrow}(s))\ge m_B^\lambda-p(s)-2^{-b}>12\vartheta-\frac{7}{4}\vartheta-\frac{3}{4}\vartheta=\frac{19}{2}\vartheta>2\vartheta$，故从 $s_0=0$ 出发的触发集精确等于 $U=\{s\in(0,1]:p(s)<\vartheta_{\mathrm{open}}\}\ne\varnothing$。记 $s_*=\inf U\in[0,1)$：若 $s_*=0$ 则 $s_*\notin(0,1]\supseteq U$；若 $s_*>0$ 且 $s_*\in U$，则 $p(s_*)<\vartheta_{\mathrm{open}}$，连续性给出存在 $s'\in(0,s_*)$ 使 $p(s')<\vartheta_{\mathrm{open}}$（即 $s'\in U$），与 $s_*=\inf U$ 矛盾；又由 $U$ 的下确界极限知 $p(s_*)\le\vartheta_{\mathrm{open}}$ 且 $p(0)\ge\vartheta_{\mathrm{open}}$，故必有 $p(s_*)=\vartheta_{\mathrm{open}}$、$Q_{\downarrow,b}(p(s_*))=\vartheta_{\mathrm{open}}>\vartheta$ 且 $s_*\notin U$，即 $U$ 无最小元。

对第 2 项，当 $2^{-b}>\vartheta$ 时，$\lfloor 2^b\vartheta\rfloor=0$；对任意 $x\in(0,1]$，$\lceil 2^bx\rceil\ge1$ 给出 $Q_{\uparrow,b}(x)\ge2^{-b}>\vartheta$，而 $Q_{\uparrow,b}(0)=0\le\vartheta$，故 $S_{Q_{\uparrow,b},\vartheta}=\{0\}$。在交邻域 $0<|\lambda-\alpha|<\min(\eta,\eta_0)$ 内，由 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 205.3，从 $z_*$ 出发的局部概率 $|\theta_i^\lambda(\tau,z_*)|^2$ 在全部十五段脉冲上严格大于 $0$，故 $p_\Psi(q,z_*)\notin\{0\}$ 恒成立，$G_j^{Q_{\uparrow,b}}\equiv0$，配置路径逐字等于假设 205.2 在该去心邻域内的恒定无跳路径 $r_i(\tau)\equiv z_*$（其中 $(z_*)_{13}=0$），对见证程序 $(a,f)=((9),\varepsilon)$ 直接触发定理 205.3 第 2 项式 (205.5) 的恒零报告与固定正总变差偏差 $x=\varphi^{-1}$。∎

## 9. 第 6–8 节的来源、文献归属与适用边界

**来源与适用边界 9.1。** 第 6–8 节在第 1–5 节已由重叠实三轴切分图册黏合出全局正交复结构 $J$ 与复 Hilbert 载体 $\mathcal{H}=(V,g,J)$ 的基础上，建立概率闭合、单本体仪器更新与有限精度守卫读出三组结构边界，且不修改第 1–5 节的任何既有条目。第 6 节将 [`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md) 定理 11.2 与命题 11.3 的前置条件推进到任意有限二元切分菜单：定理 6.2 给出框架概率赋值自动满足 RC 的充要核空间相等条件 $L_{\mathfrak{M}}=\ker\mathsf{E}_{\mathfrak{M}}$，并在包含同一完备层析基菜单且局部核完备的菜单族上由秩一投影闭包直接导出 $H_v\succeq0$（$d\ge2$）；不预先假设跨标架 RC 时的同时线性化与正锥闭合在 $\dim_{\mathbb{C}}\mathcal{H}\ge3$ 完整正交标架可加情形归属 Gleason 1957（定理 2.8 与第 3 节）、在全效果集 $\mathcal{E}(\mathcal{H})$ 子恒等可加分解情形归属 Busch 2003；命题 6.3 第 2 项以 $\mathbb{C}^3$ 四组相互无偏基菜单证明即使同时具备有限框架可加性、完整 RC、完备厄米层析与菜单投影严格正概率，仍不蕴涵重构算子半正定。第 7 节中定理 7.2 第 1 项与第 3 项作为承重推导两侧的文献先例桥接步骤：完全正性与 Choi 矩阵 $R_{\Lambda_b}\succeq0$ 及 Kraus 算子求和分解的等价严格归属 Choi 1975 定理 1–2（算子求和表示亦见 Kraus 1971，而单系统正性与二分算子在乘积向量上的块正性对偶归属 Jamiołkowski 1972），锐正交投影完全正仪器由本征纯态不扰动性（理想测量条件）唯一锁定为 Lüders 投影更新（Lüders 1951）的充要刻画归属 Busch–Lahti–Mittelstaedt 1991 与 Busch 2008 定理 5；定理 7.2 第 2 项针对 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 定理 5.2 的算子三轴纯度亏格给出一般保迹二能级映射下的显式公式与 $O(3)=SO(3)\sqcup(O(3)\setminus SO(3))$ 精确二分，将命题 7.1 的 $F/2$ 反例定位于 $\det M=-1$ 连通分支，并在命题 7.3 中证明混噪非 CP 正映射满足 $D_1\succ0$、退化锐投影可重复 CP 仪器删去本征纯态不扰动性后偏离 Lüders 更新（同时区分用于检验二能级 CP 的二维参考切分与实现秩四通道所需的四维或两位内部记录上下文）。第 8 节消费 [`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 定理 205.3、207.1 与 208.2 的波函数扰动不等式和因果档案结构，证明闭下水平集与一致误差界 $\delta<\frac{3}{4}\vartheta=\frac{3m_*}{64}$ 保持连续时间首点取得、有限跳数界、精确报告与全历史测度同构；有限跳数仍本质依赖原十五门系统的有界相位导数 $|p'|<8\pi$ 与正质量二点块跳跃增益 $>10\vartheta-2\delta$，而非仅由抽象有限地址集推出。第 6–8 节尚未涉及离散晶格隐藏库消去下的多探针共同传播速度与有限体积涨落界。

## 追加锚（本行以下为增补区）

## 10. 离散周期晶格无隙多探针的隐藏库消去、门户对称判据与速度分裂反例

**定义 10.1（离散周期晶格上的无隙可见—有隙隐藏耦合二次量子系统与零模切折合对）。** 固定空间维数 $d\ge1$、晶格常数 $a>0$、周期边长整数 $L\ge3$、可见探针分量数 $M\ge1$ 与隐藏库分量数 $M_h\ge1$。在离散周期环面晶格 $\Lambda_L=(\mathbb{Z}/L\mathbb{Z})^d$ 上，记对偶离散波矢集为 $\Lambda_L^*=\{\frac{2\pi}{La}n:n=(n_1,\ldots,n_d)\in\{0,1,\ldots,L-1\}^d\}$，最近邻离散负拉普拉斯符号为

$$
\mu_k=\frac{4}{a^2}\sum_{r=1}^{d}\sin^2\!\left(\frac{\pi n_r}{L}\right)\ge0\qquad\left(\mu_k=0\iff k=0;\ \min_{k\ne0}\mu_k=\mu_{\min}(L)=\frac{4}{a^2}\sin^2\!\left(\frac{\pi}{L}\right)>0\right).
$$

考虑实空间格点厄米正则场 $\hat{X}(x)=(\hat{q}(x),\hat{h}(x))^{\mathsf T}$ 与 $\hat{P}(x)$（$x\in\Lambda_L$，可见坐标 $\hat{q}(x)$ 占前 $M$ 分量，隐藏坐标 $\hat{h}(x)$ 占后 $M_h$ 分量，满足 $[\hat{X}_\alpha(x),\hat{P}_\beta(y)]=i\hbar\delta_{xy}\delta_{\alpha\beta}$ 及 $[\hat{X}_\alpha(x),\hat{X}_\beta(y)]=[\hat{P}_\alpha(x),\hat{P}_\beta(y)]=0$），作酉离散 Fourier 变换 $\hat{X}_k=\frac{1}{L^{d/2}}\sum_{x\in\Lambda_L}e^{-ik\cdot ax}\hat{X}(x)$、$\hat{P}_k=\frac{1}{L^{d/2}}\sum_{x\in\Lambda_L}e^{-ik\cdot ax}\hat{P}(x)$（其中 $-k\in\Lambda_L^*$ 指倒格模代表 $\frac{2\pi}{La}((-n)\bmod L)$，满足 $\mu_{-k}=\mu_k$，故实场共轭配对 $\hat{X}_{-k,\alpha}=\hat{X}_{k,\alpha}^\dagger$、$\hat{P}_{-k,\alpha}=\hat{P}_{k,\alpha}^\dagger$ 与正则对易 $[\hat{X}_{k,\alpha},\hat{P}_{k',\beta}^\dagger]=i\hbar\delta_{kk'}\delta_{\alpha\beta}$ 同时成立）。时间反演偶、晶格平移与各向同性离散梯度耦合的实二次正则量子晶格总哈密顿量为 $\hat{H}=\sum_{k\in\Lambda_L^*}\hat{H}_k$，其中单波矢模哈密顿量为

$$
\hat{H}_k=\frac{1}{2}\hat{P}_k^\dagger T^{-1}\hat{P}_k+\frac{1}{2}\hat{X}_k^\dagger V(\mu_k)\hat{X}_k,\qquad V(\mu_k)=V_0+\mu_kV_1,
$$

其中惯性矩阵 $T\in M_{M+M_h}(\mathbb{R})$、零波矢局域势矩阵 $V_0\in M_{M+M_h}(\mathbb{R})$ 与离散梯度刚度矩阵 $V_1\in M_{M+M_h}(\mathbb{R})$ 均为实对称矩阵，按可见—隐藏分块写作

$$
T=\begin{pmatrix}T_{VV}&T_{VH}\\ T_{VH}^{\mathsf T}&T_{HH}\end{pmatrix}\succ0,\qquad
V_0=\begin{pmatrix}A_0&C_0\\ C_0^{\mathsf T}&H_0\end{pmatrix}\succeq0,\qquad
V_1=\begin{pmatrix}V_{1,VV}&V_{1,VH}\\ V_{1,VH}^{\mathsf T}&V_{1,HH}\end{pmatrix}\succeq0,
$$

并满足**隐藏库局域有隙** $H_0\succ0$ 与**可见扇区红外无隙（零模平衡）**

$$
A_0-C_0H_0^{-1}C_0^{\mathsf T}=0.
$$

定义零模切嵌入矩阵 $N_0\in M_{(M+M_h)\times M}(\mathbb{R})$、单模下三角消去矩阵 $S\in\operatorname{SL}_{M+M_h}(\mathbb{R})$ 及可见折合惯性—刚度矩阵对 $(Z_{\mathrm{eff}},K_{\mathrm{eff}})$ 为

$$
N_0=\begin{pmatrix}I_M\\ -H_0^{-1}C_0^{\mathsf T}\end{pmatrix},\qquad
S=\begin{pmatrix}I_M&0\\ -H_0^{-1}C_0^{\mathsf T}&I_{M_h}\end{pmatrix},\qquad
Z_{\mathrm{eff}}=N_0^{\mathsf T}TN_0,\qquad
K_{\mathrm{eff}}=N_0^{\mathsf T}V_1N_0.
$$

**定理 10.2（无隙切空间正定判据、红外共同声速矩阵充要条件与跨速度门户正交交织充分定理）。** 在定义 10.1 下：

1. **零模切空间分解与非零波矢全局正定充要判据**：恒有 $S^{\mathsf T}V_0S=\operatorname{diag}(0_M,H_0)$ 与 $\ker V_0=\operatorname{Ran}N_0$（$\dim_{\mathbb{R}}\ker V_0=M$），折合惯性矩阵恒严格正定 $Z_{\mathrm{eff}}\succ0$；且下列三项彼此等价（即使未约化梯度刚度 $V_1$ 退化奇异，例如隐藏库局域不传播 $V_{1,HH}=0,V_{1,VH}=0$）：
   - 对一切非零晶格波矢 $k\ne0$（或任一 $\mu>0$），完整模势矩阵严格正定 $V(\mu_k)=V_0+\mu_kV_1\succ0$；
   - $\ker V_0\cap\ker V_1=\{0\}$；
   - 折合可见刚度矩阵严格正定 $K_{\mathrm{eff}}=N_0^{\mathsf T}V_1N_0\succ0$；

2. **多探针共同红外声速的广义本征值充要条件**：当 $K_{\mathrm{eff}}\succ0$ 时，将矩阵束 $(K_{\mathrm{eff}},Z_{\mathrm{eff}})$ 的 $M$ 个广义特征值（即对称正定矩阵 $\widehat{K}_{\mathrm{eff}}=Z_{\mathrm{eff}}^{-1/2}K_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1/2}$ 的特征值）按递增次序记为 $0<c_1^2\le c_2^2\le\cdots\le c_M^2$。则完整晶格动力学束 $(V(\mu_k),T)$ 的前 $M$ 条声学本征频率平方 $\omega_1(k)^2\le\cdots\le\omega_M(k)^2$ 在红外标度 $\mu_k\to0^+$（例如固定整波数模号并令 $La\to\infty$）下满足 $\lim_{\mu_k\to0^+}\frac{\omega_j(k)^2}{\mu_k}=c_j^2$（$1\le j\le M$），且全部 $M$ 个可见探针共享单一正红外声速 $c_1=\cdots=c_M=c_{\mathrm{eff}}>0$ 当且仅当

$$
K_{\mathrm{eff}}=c_{\mathrm{eff}}^2Z_{\mathrm{eff}};
$$

3. **无需未约化全系统等速的可见不可约门户交织充分机制**：设群 $G$ 在可见探针空间 $\mathbb{R}^M$ 上有实正交**不可约**表示 $g\mapsto R_g\in O(M)$，在隐藏库空间 $\mathbb{R}^{M_h}$ 上有任意实正交表示 $g\mapsto\widetilde{R}_g\in O(M_h)$（不要求 $\widetilde{R}_g$ 不可约，亦不要求未约化系统满足 $V_1=c^2T$）。若分块矩阵对对角作用 $D_g=\operatorname{diag}(R_g,\widetilde{R}_g)\in O(M+M_h)$ 不变：

$$
D_g^{\mathsf T}TD_g=T,\qquad D_g^{\mathsf T}V_0D_g=V_0,\qquad D_g^{\mathsf T}V_1D_g=V_1\qquad(\forall g\in G),
$$

且 $K_{\mathrm{eff}}\ne0$，则存在纯量 $z_{\mathrm{eff}}>0$、$k_{\mathrm{eff}}>0$ 使 $Z_{\mathrm{eff}}=z_{\mathrm{eff}}I_M$、$K_{\mathrm{eff}}=k_{\mathrm{eff}}I_M$，从而全部 $M$ 个可见探针严格共享共同红外声速 $c_{\mathrm{eff}}=\sqrt{k_{\mathrm{eff}}/z_{\mathrm{eff}}}>0$。特别地，当可见探针具有裸惯性 $I_M$ 与裸速度 $c_0>0$，通过 $O(M)$ 等变矢量门户 $\frac{\Omega^2}{2}\|h-\alpha q\|^2$（$M_h=M,\Omega>0,\alpha\in\mathbb{R}$）耦合具有**不同**裸速度 $v_h\ge0$（$v_h\ne c_0$，惯性 $I_M$）的隐藏矢量多重态时，未约化系统违背 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 定理 21.1 的全系统共同锥判据，但约化红外可见扇区严格具有共同声速

$$
c_{\mathrm{eff}}^2=\frac{c_0^2+\alpha^2v_h^2}{1+\alpha^2}.
$$

**证明。** 直接展开分块乘法：因 $A_0=C_0H_0^{-1}C_0^{\mathsf T}$，有

$$
S^{\mathsf T}V_0S=\begin{pmatrix}I_M&-C_0H_0^{-1}\\ 0&I_{M_h}\end{pmatrix}\begin{pmatrix}C_0H_0^{-1}C_0^{\mathsf T}&C_0\\ C_0^{\mathsf T}&H_0\end{pmatrix}\begin{pmatrix}I_M&0\\ -H_0^{-1}C_0^{\mathsf T}&I_{M_h}\end{pmatrix}=\begin{pmatrix}0_M&0\\ 0&H_0\end{pmatrix}.
$$

因 $S$ 可逆且 $H_0\succ0$，$V_0x=0\iff S^{\mathsf T}V_0S(S^{-1}x)=0\iff S^{-1}x=\binom{u}{0}\iff x=S\binom{u}{0}=N_0u$（$u\in\mathbb{R}^M$），且 $\operatorname{rank}N_0=M$，故 $\ker V_0=\operatorname{Ran}N_0$，由 $T\succ0$ 知 $Z_{\mathrm{eff}}=N_0^{\mathsf T}TN_0\succ0$。对任意 $\mu>0$，因 $V_0\succeq0$ 与 $\mu V_1\succeq0$，二次型 $x^{\mathsf T}(V_0+\mu V_1)x=x^{\mathsf T}V_0x+\mu x^{\mathsf T}V_1x\ge0$ 取零当且仅当 $x\in\ker V_0\cap\ker V_1$；将 $x\in\ker V_0$ 写为 $x=N_0u$，则 $x\in\ker V_1\iff u^{\mathsf T}N_0^{\mathsf T}V_1N_0u=u^{\mathsf T}K_{\mathrm{eff}}u=0$（因 $V_1\succeq0$）。故 $V_0+\mu V_1\succ0\iff\ker V_0\cap\ker V_1=\{0\}\iff K_{\mathrm{eff}}\succ0$，证毕第 1 项。

第 2 项中，$\lim_{\mu_k\to0^+}\frac{\omega_j(k)^2}{\mu_k}=c_j^2$ 由下节定理 11.1 的非微扰双侧界 $0\le c_j^2-\frac{\omega_j(k)^2}{\mu_k}\le\frac{\mu_k\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{\Omega_{\mathrm{opt},0}^2-\mu_kc_M^2}$ 直接推出；而对称矩阵 $\widehat{K}_{\mathrm{eff}}=Z_{\mathrm{eff}}^{-1/2}K_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1/2}$ 的全部 $M$ 个特征值均等于 $c_{\mathrm{eff}}^2$ 当且仅当 $\widehat{K}_{\mathrm{eff}}=c_{\mathrm{eff}}^2I_M$，两边同乘 $Z_{\mathrm{eff}}^{1/2}$ 即 $K_{\mathrm{eff}}=c_{\mathrm{eff}}^2Z_{\mathrm{eff}}$。

现证第 3 项。由 $D_g^{\mathsf T}V_0D_g=V_0$ 取分块得 $R_g^{\mathsf T}C_0\widetilde{R}_g=C_0$ 与 $\widetilde{R}_g^{\mathsf T}H_0\widetilde{R}_g=H_0$，故 $C_0\widetilde{R}_g=R_gC_0$、$H_0^{-1}\widetilde{R}_g=\widetilde{R}_gH_0^{-1}$。于是

$$
D_gN_0=\begin{pmatrix}R_g&0\\ 0&\widetilde{R}_g\end{pmatrix}\begin{pmatrix}I_M\\ -H_0^{-1}C_0^{\mathsf T}\end{pmatrix}=\begin{pmatrix}R_g\\ -\widetilde{R}_gH_0^{-1}C_0^{\mathsf T}\end{pmatrix}=\begin{pmatrix}R_g\\ -H_0^{-1}(C_0\widetilde{R}_g^{\mathsf T})^{\mathsf T}\end{pmatrix}=\begin{pmatrix}I_M\\ -H_0^{-1}C_0^{\mathsf T}\end{pmatrix}R_g=N_0R_g.
$$

由这一门户交织恒等式 $D_gN_0=N_0R_g$，对一切 $g\in G$ 有

$$
R_g^{\mathsf T}Z_{\mathrm{eff}}R_g=(N_0R_g)^{\mathsf T}T(N_0R_g)=N_0^{\mathsf T}(D_g^{\mathsf T}TD_g)N_0=Z_{\mathrm{eff}},\qquad
R_g^{\mathsf T}K_{\mathrm{eff}}R_g=N_0^{\mathsf T}(D_g^{\mathsf T}V_1D_g)N_0=K_{\mathrm{eff}}.
$$

因 $Z_{\mathrm{eff}}$ 与 $K_{\mathrm{eff}}$ 是实对称矩阵，其特征子空间均在实不可约正交表示 $\{R_g\}_{g\in G}$ 下不变；不可约性排除非平凡真不变子空间，故 $Z_{\mathrm{eff}}=z_{\mathrm{eff}}I_M$（$z_{\mathrm{eff}}>0$）且 $K_{\mathrm{eff}}=k_{\mathrm{eff}}I_M$（由 $K_{\mathrm{eff}}\succeq0$ 且 $K_{\mathrm{eff}}\ne0$ 知 $k_{\mathrm{eff}}>0$），从而 $K_{\mathrm{eff}}=(k_{\mathrm{eff}}/z_{\mathrm{eff}})Z_{\mathrm{eff}}$。在矢量门户特例中，$T=I_{2M}$，$V_1=\operatorname{diag}(c_0^2I_M,v_h^2I_M)$，$H_0=\Omega^2I_M$，$C_0=-\alpha\Omega^2I_M$，故 $N_0=\binom{I_M}{\alpha I_M}$，$Z_{\mathrm{eff}}=(1+\alpha^2)I_M$，$K_{\mathrm{eff}}=(c_0^2+\alpha^2v_h^2)I_M$，相除即得 $c_{\mathrm{eff}}^2=\frac{c_0^2+\alpha^2v_h^2}{1+\alpha^2}$。∎

**命题 10.3（单共享隐藏标量门户的速度分裂阻塞定理与多探针全异声速实现）。**

1. **单共享隐藏标量无法保持多探针共同光锥**：设可见探针数 $M\ge2$，具有全同裸惯性 $T_{VV}=I_M$ 与全同裸梯度刚度 $V_{1,VV}=c_0^2I_M$（$c_0>0$），耦合至**单一共享隐藏标量库**（$M_h=1$，$T_{HH}=1$，$T_{VH}=0$，$V_{1,HH}=v_h^2$，$v_h\ge0$，$V_{1,VH}=0$），局域无隙平衡门户势为 $\frac{\Omega^2}{2}(h-b^{\mathsf T}q)^2$（$\Omega>0$，耦合向量 $b\in\mathbb{R}^M\setminus\{0\}$）。只要隐藏库裸速度与可见裸速度不同（$v_h\ne c_0$，即 $v_h^2\ne c_0^2$，含局域不传播库 $v_h=0$），约化可见扇区必然违背定理 10.2 第 2 项的共同声速判据，精确分裂为 $M-1$ 个未偏移横向模与 $1$ 个门户纵向模：

$$
c_\perp^2=c_0^2\quad(\text{重数 }M-1,\ u\perp b),\qquad
c_\parallel^2=\frac{c_0^2+\|b\|^2v_h^2}{1+\|b\|^2}\ne c_0^2\quad(\text{重数 }1,\ u\parallel b).
$$

特别地，取 $M=2,M_h=1,c_0=1,v_h=2,\Omega=3$ 及探针置换对称耦合 $b=(1,1)^{\mathsf T}$，有 $Z_{\mathrm{eff}}=\begin{pmatrix}2&1\\ 1&2\end{pmatrix}$，$K_{\mathrm{eff}}=\begin{pmatrix}5&4\\ 4&5\end{pmatrix}$，反对称模 $u_\perp=(1,-1)^{\mathsf T}$ 与对称模 $u_\parallel=(1,1)^{\mathsf T}$ 的红外声速平方分别为 $c_\perp^2=1\ne3=c_\parallel^2$；

2. **$M$ 个探针产生 $M$ 个两两不同稳定声速的对角实现**：取 $M\ge2,M_h=M$，$T=I_{2M}$，$V_1=\operatorname{diag}(c_0^2I_M,v_h^2I_M)$（$c_0>0,\ v_h\ge0,\ v_h\ne c_0$），局域势为 $\sum_{j=1}^M\frac{\Omega^2}{2}(h_j-jq_j)^2$（$\Omega>0$），则系统满足定义 10.1 的全部稳定性与无隙可见条件（且 $K_{\mathrm{eff}}\succ0$），但其 $M$ 条可见声学分支具有 $M$ 个严格两两不同的红外声速平方

$$
c_j^2=\frac{c_0^2+j^2v_h^2}{1+j^2}\qquad(1\le j\le M).
$$

**证明。** 对第 1 项，门户势矩阵为 $V_0=\Omega^2\begin{pmatrix}bb^{\mathsf T}&-b\\ -b^{\mathsf T}&1\end{pmatrix}$，满足 $H_0=\Omega^2>0$、$C_0=-\Omega^2b$ 与 $A_0-C_0H_0^{-1}C_0^{\mathsf T}=\Omega^2bb^{\mathsf T}-\Omega^2bb^{\mathsf T}=0$。零模切嵌入为 $N_0=\binom{I_M}{b^{\mathsf T}}$，故

$$
Z_{\mathrm{eff}}=I_M+bb^{\mathsf T},\qquad K_{\mathrm{eff}}=c_0^2I_M+v_h^2bb^{\mathsf T}.
$$

对任意 $u\in b^\perp\setminus\{0\}$（维数 $M-1\ge1$），$K_{\mathrm{eff}}u=c_0^2u=c_0^2Z_{\mathrm{eff}}u$，故 $c_\perp^2=c_0^2$；在 $b$ 上，$K_{\mathrm{eff}}b=(c_0^2+\|b\|^2v_h^2)b$ 而 $Z_{\mathrm{eff}}b=(1+\|b\|^2)b$，故 $c_\parallel^2=\frac{c_0^2+\|b\|^2v_h^2}{1+\|b\|^2}$。两者之差为 $c_\parallel^2-c_\perp^2=\frac{\|b\|^2(v_h^2-c_0^2)}{1+\|b\|^2}\ne0$（因 $b\ne0$ 且 $c_0>0,v_h\ge0,v_h\ne c_0\Rightarrow v_h^2\ne c_0^2$）。将 $M=2,c_0^2=1,v_h^2=4,b=(1,1)^{\mathsf T}$（$\|b\|^2=2$）代入立得 $c_\perp^2=1$ 与 $c_\parallel^2=\frac{1+8}{1+2}=3$（注意此时探针置换群 $\mathbb{Z}_2$ 在 $\mathbb{R}^2$ 上可约分解为 $\mathbb{R}u_\perp\oplus\mathbb{R}u_\parallel$，印证定理 10.2 第 3 项中可见表示不可约性不可删去）。第 2 项对每个指标 $j\in\{1,\ldots,M\}$ 独立退化为 $1+1$ 维块 $Z_{\mathrm{eff}}=\operatorname{diag}(1+j^2)_{j=1}^M$、$K_{\mathrm{eff}}=\operatorname{diag}(c_0^2+j^2v_h^2)_{j=1}^M\succ0$（因 $c_0>0,v_h\ge0$），而函数 $t\mapsto\frac{c_0^2+tv_h^2}{1+t}$ 在 $c_0>0,v_h\ge0,v_h\ne c_0$（$v_h^2\ne c_0^2$）时于 $[0,\infty)$ 上导数 $\frac{v_h^2-c_0^2}{(1+t)^2}\ne0$ 恒定非零故严格单调，$c_1^2,\ldots,c_M^2$ 两两互异。∎

## 11. 离散晶格非微扰声学色散界、超锥 Bessel 尾项分离与有限体积无隙涨落夹逼

**定理 11.1（动能正交化零模变换与全部声学分支的非微扰紧致双侧色散界）。** 在定义 10.1 下，设 $K_{\mathrm{eff}}\succ0$，记 $S^{\mathsf T}TS=\begin{pmatrix}Z_{\mathrm{eff}}&T_{12}\\ T_{12}^{\mathsf T}&T_{22}\end{pmatrix}\succ0$ 与 $S^{\mathsf T}V_1S=\begin{pmatrix}K_{\mathrm{eff}}&W_{12}\\ W_{12}^{\mathsf T}&W_{22}\end{pmatrix}\succeq0$。令隐藏惯性 Schur 补为 $\widetilde{T}_H=T_{22}-T_{12}^{\mathsf T}Z_{\mathrm{eff}}^{-1}T_{12}\succ0$，定义分块上三角矩阵

$$
U_T=\begin{pmatrix}Z_{\mathrm{eff}}^{-1/2}&-Z_{\mathrm{eff}}^{-1}T_{12}\widetilde{T}_H^{-1/2}\\ 0&\widetilde{T}_H^{-1/2}\end{pmatrix}.
$$

则变换矩阵 $SU_T$ 同时将惯性矩阵化为单位阵 $U_T^{\mathsf T}S^{\mathsf T}TSU_T=I_{M+M_h}$、将零波矢势矩阵保持为分块对角阵 $U_T^{\mathsf T}S^{\mathsf T}V_0SU_T=\operatorname{diag}(0_M,\widetilde{H}_0)$（其中 $\widetilde{H}_0=\widetilde{T}_H^{-1/2}H_0\widetilde{T}_H^{-1/2}\succ0$，其最小特征值 $\Omega_{\mathrm{opt},0}^2=\lambda_{\min}(\widetilde{H}_0)>0$ 恰为 $k=0$ 处束 $(V_0,T)$ 的精确光学频率间隙平方），并将完整动力学束 $(V(\mu_k),T)$ 正交等价化为标准实对称矩阵

$$
\mathcal{M}(\mu_k)=U_T^{\mathsf T}S^{\mathsf T}(V_0+\mu_kV_1)SU_T=\begin{pmatrix}\mu_k\widehat{K}_{\mathrm{eff}}&\mu_k\widehat{W}_{12}\\ \mu_k\widehat{W}_{12}^{\mathsf T}&\widetilde{H}_0+\mu_k\widehat{W}_{22}\end{pmatrix},
$$

其中 $\widehat{K}_{\mathrm{eff}}=Z_{\mathrm{eff}}^{-1/2}K_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1/2}$（特征值为 $0<c_1^2\le\cdots\le c_M^2$），$\widehat{W}_{12}=Z_{\mathrm{eff}}^{-1/2}(W_{12}\widetilde{T}_H^{-1/2}-K_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1}T_{12}\widetilde{T}_H^{-1/2})$，$\widehat{W}_{22}\succeq0$。由此得到：

1. **全布里渊区无条件变分上界**：对**一切**波矢 $k\in\Lambda_L^*$ 及每条声学分支 $1\le j\le M$，有

$$
\omega_j(k)^2\le\mu_kc_j^2;
$$

2. **声学窗口内的非微扰紧致双侧界**：对一切满足 $\mu_kc_M^2<\Omega_{\mathrm{opt},0}^2$ 的波矢 $k$ 及全部 $1\le j\le M$，有

$$
0\le\mu_kc_j^2-\omega_j(k)^2\le\frac{\mu_k^2\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{\Omega_{\mathrm{opt},0}^2-\mu_kc_M^2},
$$

且右端上界前因子常数 $1$ 在满足定义 10.1 的二模系统 $T=I_2,V_0=\operatorname{diag}(0,\Omega^2),V_1=\begin{pmatrix}c^2&w\\ w&w^2/c^2\end{pmatrix}\succeq0$（$c>0,w\ne0,\Omega>0$，即 $\mathcal{M}(\mu)=\begin{pmatrix}\mu c^2&\mu w\\ \mu w&\Omega^2+\mu w^2/c^2\end{pmatrix}$）的 $\mu\to0^+$ 渐近比 $\lim_{\mu\to0^+}\frac{\mu c^2-\omega_1(\mu)^2}{\mu^2w^2/(\Omega^2-\mu c^2)}=1$（展开式为 $\mu c^2-\omega_1(\mu)^2=\frac{\mu^2w^2}{\Omega^2-\mu c^2}+O(\mu^3)$）下精确达到。

**证明。** 直接按分块矩阵乘法检验 $U_T^{\mathsf T}\begin{pmatrix}Z_{\mathrm{eff}}&T_{12}\\ T_{12}^{\mathsf T}&T_{22}\end{pmatrix}U_T$：左上块为 $Z_{\mathrm{eff}}^{-1/2}Z_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1/2}=I_M$；右上块为 $Z_{\mathrm{eff}}^{-1/2}(-T_{12}\widetilde{T}_H^{-1/2}+T_{12}\widetilde{T}_H^{-1/2})=0$；右下块为 $\widetilde{T}_H^{-1/2}(T_{22}-T_{12}^{\mathsf T}Z_{\mathrm{eff}}^{-1}T_{12})\widetilde{T}_H^{-1/2}=I_{M_h}$。又因 $U_T$ 为分块上三角阵，其作用在 $S^{\mathsf T}V_0S=\operatorname{diag}(0_M,H_0)$ 上给出 $\operatorname{diag}(0_M,\widetilde{T}_H^{-1/2}H_0\widetilde{T}_H^{-1/2})=\operatorname{diag}(0_M,\widetilde{H}_0)$，作用在 $S^{\mathsf T}V_1S\succeq0$ 上保持左上块 $Z_{\mathrm{eff}}^{-1/2}K_{\mathrm{eff}}Z_{\mathrm{eff}}^{-1/2}=\widehat{K}_{\mathrm{eff}}$ 与右下块 $\widehat{W}_{22}\succeq0$。故 $(V(\mu_k),T)$ 的全体广义特征值逐一等于 $\mathcal{M}(\mu_k)$ 的标准特征值 $\omega_1(k)^2\le\cdots\le\omega_{M+M_h}(k)^2$。

因 $\mu_k\widehat{K}_{\mathrm{eff}}$ 是 $\mathcal{M}(\mu_k)$ 的左上 $M\times M$ 主子矩阵，Cauchy 主子矩阵特征值交错定理对一切 $\mu_k\ge0$ 与 $1\le j\le M$ 直接给出 $\omega_j(k)^2\le\lambda_j(\mu_k\widehat{K}_{\mathrm{eff}})=\mu_kc_j^2$，证毕第 1 项。

当 $\mu_kc_M^2<\Omega_{\mathrm{opt},0}^2$ 时，置正标量 $\sigma=\Omega_{\mathrm{opt},0}^2-\mu_kc_M^2>0$。由完平方半正定恒等式

$$
\begin{pmatrix}\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}&\mu_k\widehat{W}_{12}\\ \mu_k\widehat{W}_{12}^{\mathsf T}&\sigma I_{M_h}\end{pmatrix}=\begin{pmatrix}\frac{\mu_k}{\sqrt{\sigma}}\widehat{W}_{12}\\ \sqrt{\sigma}I_{M_h}\end{pmatrix}\begin{pmatrix}\frac{\mu_k}{\sqrt{\sigma}}\widehat{W}_{12}^{\mathsf T}&\sqrt{\sigma}I_{M_h}\end{pmatrix}\succeq0
$$

及 $\widetilde{H}_0+\mu_k\widehat{W}_{22}\succeq\widetilde{H}_0\succeq\Omega_{\mathrm{opt},0}^2I_{M_h}=(\sigma+\mu_kc_M^2)I_{M_h}$，从 $\mathcal{M}(\mu_k)$ 中减去该半正定非对角耦合块立得 Loewner 下界

$$
\mathcal{M}(\mu_k)\succeq\begin{pmatrix}\mu_k\widehat{K}_{\mathrm{eff}}-\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}&0\\ 0&\mu_kc_M^2I_{M_h}\end{pmatrix}.
$$

右端分块对角矩阵的右下块全部 $M_h$ 个特征值均为 $\mu_kc_M^2$，而左上块的第 $j$ 小特征值满足 $\lambda_j(\mu_k\widehat{K}_{\mathrm{eff}}-\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T})\le\mu_kc_j^2\le\mu_kc_M^2$（$1\le j\le M$），故右端矩阵的前 $M$ 小特征值精确等于左上块的 $M$ 个特征值。应用 Weyl 算子单调性与微扰界 $\lambda_j(A-B)\ge\lambda_j(A)-\|B\|_{\mathrm{op}}$（$B\succeq0$），即得

$$
\omega_j(k)^2\ge\lambda_j\!\left(\mu_k\widehat{K}_{\mathrm{eff}}-\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}\right)\ge\mu_kc_j^2-\frac{\mu_k^2\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{\Omega_{\mathrm{opt},0}^2-\mu_kc_M^2}.
$$

对满足定义 10.1 的 $2\times2$ 证人 $T=I_2,V_0=\operatorname{diag}(0,\Omega^2),V_1=\begin{pmatrix}c\\ w/c\end{pmatrix}\begin{pmatrix}c&w/c\end{pmatrix}\succeq0$（$c>0,w\ne0,\Omega>0$），记 $\Delta(\mu)=\Omega^2+\mu(w^2/c^2-c^2)>0$（充分小 $\mu>0$），对 $\mathcal{M}(\mu)-\mu c^2I_2=\begin{pmatrix}0&\mu w\\ \mu w&\Delta(\mu)\end{pmatrix}$ 用求根公式给出 $\mu c^2-\omega_1(\mu)^2=\frac{\sqrt{\Delta(\mu)^2+4\mu^2w^2}-\Delta(\mu)}{2}=\frac{2\mu^2w^2}{\sqrt{\Delta(\mu)^2+4\mu^2w^2}+\Delta(\mu)}=\frac{\mu^2w^2}{\Omega^2}+O(\mu^3)=\frac{\mu^2w^2}{\Omega^2-\mu c^2}+O(\mu^3)$，故 $\lim_{\mu\to0^+}\frac{\mu c^2-\omega_1(\mu)^2}{\mu^2w^2/(\Omega^2-\mu c^2)}=1$，证毕渐近紧致性。∎

**命题 11.2（离散最近邻晶格上超锥 Bessel 对易尾项与布里渊区四阶旋转各向异性的双分离命题）。**

1. **红外声速不蕴涵离散晶格上的严格零支撑微因果光锥（利用一维谐振链 Bessel 传播核：Schrödinger 1914）**：在一维无限最近邻谐振晶格 $\mathbb{Z}$（晶格间距 $a>0$，单位惯性 $T=1$，纯可见无隙刚度 $(Kq)(x)=\frac{c_0^2}{a^2}(2q(x)-q(x+1)-q(x-1))$，$c_0>0$；或周期晶格 $\mathbb{Z}/L\mathbb{Z}$，$L\ge 2r+1$）上，红外声速精确为 $c_{\mathrm{eff}}=c_0$，但在任意非零格点距离 $r\in\mathbb{Z}_{\ge1}$（空间距离 $|x|=ra$）上，无穷晶格 Heisenberg 正则对易子精确等于 $2r$ 阶第一类 Bessel 函数（Schrödinger 1914）

$$
\frac{1}{i\hbar}\bigl[\hat{q}(r,t),\hat{p}(0,0)\bigr]=J_{2r}\!\left(\frac{2c_0t}{a}\right)=\sum_{n=0}^{\infty}\frac{(-1)^n}{n!(n+2r)!}\left(\frac{c_0t}{a}\right)^{2r+2n},
$$

从而在整个超锥区间 $0<c_0t<\min(ra,\,a\sqrt{2r+1})$ 内严格大于零，满足双侧交错级数界

$$
0<\frac{(c_0t/a)^{2r}}{(2r)!}\left(1-\frac{(c_0t/a)^2}{2r+1}\right)<\frac{1}{i\hbar}\bigl[\hat{q}(r,t),\hat{p}(0,0)\bigr]<\frac{(c_0t/a)^{2r}}{(2r)!};
$$

2. **等速隐藏库耦合下离散晶格仍有 $O(a^2|k|^4)$ 旋转各向异性**：在 $d\ge2$ 维超立方晶格上，即使全部可见与隐藏模满足 $c_a=c_0=c_{\mathrm{eff}}>0$（从而连续场四阶失配系数 $A_2=0$，见 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 定理 25.1），连续布里渊区色散符号 $\mu(k)=\frac{4}{a^2}\sum_{r=1}^d\sin^2(\frac{ak_r}{2})$（$k\in[-\frac{\pi}{a},\frac{\pi}{a}]^d$，在 $L\to\infty$ 下由离散波矢集 $\Lambda_L^*$ 稠密采样，且在 $\sqrt{d}\in\mathbb{Q}$ 时于有限周期 $L$ 同模格点上精确取到）在固定欧氏模长 $|k|=\kappa>0$（$a\kappa\ll1$）下沿晶轴方向 $k_{\mathrm{axis}}=(\kappa,0,\ldots,0)$ 与空间对角方向 $k_{\mathrm{diag}}=\frac{\kappa}{\sqrt{d}}(1,\ldots,1)$ 的领先差值仍满足

$$
\mu(k_{\mathrm{diag}})-\mu(k_{\mathrm{axis}})=\frac{a^2(d-1)}{12d}\kappa^4+O(a^4\kappa^6)>0.
$$

**证明。** 对第 1 项，因 $0\preceq K\preceq\frac{4c_0^2}{a^2}I$ 有界，定义整函数有界自伴算子 $C(t)=\sum_{m=0}^\infty\frac{(-1)^mt^{2m}}{(2m)!}K^m$ 与 $S_{\mathrm{sinc}}(t)=\sum_{m=0}^\infty\frac{(-1)^mt^{2m+1}}{(2m+1)!}K^m$（无需在 $0\in\operatorname{spec}(K)$ 处对 $\sqrt{K}$ 求逆），则线性 Heisenberg 方程 $\ddot{\hat{q}}(t)=-K\hat{q}(t)$ 的唯一解为 $\hat{q}(t)=C(t)\hat{q}(0)+S_{\mathrm{sinc}}(t)\hat{p}(0)$，故 $\frac{1}{i\hbar}[\hat{q}(r,t),\hat{p}(0,0)]=[C(t)]_{r,0}=\sum_{m=0}^\infty\frac{(-1)^mt^{2m}}{(2m)!}(K^m)_{r,0}$。在 $\ell^2(\mathbb{Z})$ 上记右移酉算子 $(Sq)(x)=q(x-1)$（故 $Se_0=e_1$，$(S^\ell)_{r,0}=\delta_{r,\ell}$），则 $K=\frac{c_0^2}{a^2}(2I-S-S^{-1})=-\frac{c_0^2}{a^2}S^{-1}(S-I)^2$，从而 $K^m=(-1)^m(\frac{c_0^2}{a^2})^mS^{-m}(S-I)^{2m}$。在二项展开 $S^{-m}(S-I)^{2m}=\sum_{j=0}^{2m}(-1)^{2m-j}\binom{2m}{j}S^{j-m}$ 中取 $S^r$ 项（即 $j=m+r$，$m\ge r$；当 $m<r$ 时为 $0$），其系数为 $(-1)^{m-r}\binom{2m}{m+r}$，与前因子 $(-1)^m$ 相乘得 $(K^m)_{r,0}=(-1)^r(\frac{c_0^2}{a^2})^m\binom{2m}{m+r}$。代入余弦级数并令 $n=m-r\ge0$，有 $(-1)^m(-1)^r=(-1)^{2r+n}=(-1)^n$ 且 $\frac{1}{(2m)!}\binom{2m}{m+r}=\frac{1}{(m-r)!(m+r)!}=\frac{1}{n!(n+2r)!}$，逐项合成为 $J_{2r}(\frac{2c_0t}{a})$。当 $0<\frac{c_0t}{a}<\sqrt{2r+1}$ 时，正项序列 $u_n=\frac{(c_0t/a)^{2r+2n}}{n!(n+2r)!}$ 满足 $\frac{u_{n+1}}{u_n}=\frac{(c_0t/a)^2}{(n+1)(n+2r+1)}\le\frac{(c_0t/a)^2}{2r+1}<1$，严格单调递减趋于 $0$，莱布尼茨交错级数截断不等式 $u_0-u_1<\sum_{n=0}^\infty(-1)^nu_n<u_0$ 直接给出所示正双侧界（在有限环 $\mathbb{Z}/L\mathbb{Z}$，$L\ge2r+1$ 上，循环右移满足 $S_L^L=I$，故 $(S_L^{j-m})_{r,0}=\mathbf{1}_{j-m\equiv r\pmod L}$，给出镜像求和 $\sum_{\ell\in\mathbb{Z}}J_{2|r+\ell L|}(\frac{2c_0t}{a})$，在 $0<\frac{c_0t}{a}\le1$ 内每项皆严格为正，总和同样严格大于零）。

对第 2 项，由 $\sin^2(\frac{ak_r}{2})=\frac{a^2k_r^2}{4}-\frac{a^4k_r^4}{48}+O(a^6k_r^6)$，对 $r=1,\ldots,d$ 求和并乘 $\frac{4}{a^2}$ 得 $\mu_k=|k|^2-\frac{a^2}{12}\sum_{r=1}^dk_r^4+O(a^4|k|^6)$。在 $k_{\mathrm{axis}}$ 上 $\sum_{r=1}^dk_r^4=\kappa^4$，在 $k_{\mathrm{diag}}$ 上 $\sum_{r=1}^dk_r^4=d(\frac{\kappa^2}{d})^2=\frac{\kappa^4}{d}$，两者相减即得 $\frac{a^2}{12}(1-\frac{1}{d})\kappa^4+O(a^4\kappa^6)>0$。∎

**定理 11.3（有限体积无隙晶格零均值扇区的精确可见刚度、算子单调量子协方差夹逼与红外维数判据——[`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 注 19.1 闭合）。** 在定义 10.1 下，设 $K_{\mathrm{eff}}\succ0$。

1. **零波矢零模发散与非零波矢精确可见刚度恒等式**：在 $k=0$ 零模上，对软质量正则化 $V_0(\sigma)=V_0+\sigma^2\operatorname{diag}(I_M,0_{M_h})$（$\sigma>0$），其可见静态逆矩阵满足 $[(V_0(\sigma))^{-1}]_{VV}=\sigma^{-2}I_M\to\infty$（$\sigma\downarrow0$）；而在零均值投影扇区的每一个非零波矢 $k\in\Lambda_L^*\setminus\{0\}$（$\mu_k\ge\mu_{\min}(L)>0$）上，可见边际逆刚度 $K_{\mathrm{vis}}(\mu_k)=([(V_0+\mu_kV_1)^{-1}]_{VV})^{-1}\succ0$ 恒满足精确恒等式

$$
K_{\mathrm{vis}}(\mu_k)=\mu_kK_{\mathrm{eff}}-\mu_k^2W_{12}(H_0+\mu_kW_{22})^{-1}W_{12}^{\mathsf T},
$$

并在一切 $k\ne0$ 上满足无条件上界 $K_{\mathrm{vis}}(\mu_k)\preceq\mu_kK_{\mathrm{eff}}$，在满足 $\mu_k\|K_{\mathrm{eff}}^{-1/2}W_{12}H_0^{-1}W_{12}^{\mathsf T}K_{\mathrm{eff}}^{-1/2}\|_{\mathrm{op}}\le\eta<1$ 的波矢窗口内满足双侧 Loewner 夹逼

$$
(1-\eta)\mu_kK_{\mathrm{eff}}\preceq\mu_kK_{\mathrm{eff}}-\mu_k^2W_{12}H_0^{-1}W_{12}^{\mathsf T}\preceq K_{\mathrm{vis}}(\mu_k)\preceq\mu_kK_{\mathrm{eff}};
$$

2. **非零波矢解耦扇区量子 KMS 热态与零温基态可见协方差的算子单调 Loewner 双侧界**：在解耦非零波矢哈密顿量 $\hat{H}_{\ne0}=\sum_{k\in\Lambda_L^*\setminus\{0\}}\hat{H}_k$（满足 $[\hat{H}_0,\hat{H}_{\ne0}]=0$ 且在每个 $k\ne0$ 上有严格正频阵 $\mathcal{M}(\mu_k)\succ0$，故在非零波矢 Fock 空间 $\mathcal{F}_{\ne0}$ 上对任意逆温度 $\beta\in(0,\infty)$ 具有唯一迹类 Gibbs／KMS 平衡态 $\rho_{\beta,\ne0}=(\operatorname{Tr}_{\mathcal{F}_{\ne0}}e^{-\beta\hat{H}_{\ne0}})^{-1}e^{-\beta\hat{H}_{\ne0}}$ 与唯一可归一 Fock 基态 $|0\rangle_{\ne0}$；对仅正则化 $k=0$ 模的全系统哈密顿量 $\hat{H}_0(\sigma)+\hat{H}_{\ne0}$，$\sigma>0$ 时其全系统 Gibbs 态／基态对 $\mathcal{F}_0$ 求偏迹恒等于 $\rho_{\beta,\ne0}$ 与 $|0\rangle_{\ne0}\langle0|$，对全格点一致软质量正则化 $V_0(\sigma)$ 则在 $\sigma\downarrow0$ 下于 $\mathcal{F}_{\ne0}$ 上按迹范数收敛且对一切有界可观测量与正则多项式可观测量期望收敛）下，每个非零波矢 $k\in\Lambda_L^*\setminus\{0\}$ 的位置对称协方差 $\operatorname{Cov}_\beta(\hat{X}_k)=\langle\hat{X}_k\hat{X}_k^\dagger\rangle_{\beta,\ne0}=\bigl(\langle\frac{1}{2}\{\hat{X}_{k,\alpha},\hat{X}_{k,\gamma}^\dagger\}\rangle_{\beta,\ne0}\bigr)_{\alpha,\gamma}$ 与零温量子基态协方差 $\operatorname{Cov}_\infty(\hat{X}_k)=\langle\hat{X}_k\hat{X}_k^\dagger\rangle_{\mathrm{vac},\ne0}=\frac{\hbar}{2}SU_T\mathcal{M}(\mu_k)^{-1/2}U_T^{\mathsf T}S^{\mathsf T}$ 的可见 $M\times M$ 主块满足通用热—零点分解夹逼

$$
\max_{\preceq}\!\left\{\frac{1}{\beta}K_{\mathrm{vis}}(\mu_k)^{-1},\ \operatorname{Cov}_\infty(\hat{q}_k)\right\}\preceq\operatorname{Cov}_\beta(\hat{q}_k)\preceq\frac{1}{\beta}K_{\mathrm{vis}}(\mu_k)^{-1}+\operatorname{Cov}_\infty(\hat{q}_k)
$$

（其中左端意为 $\operatorname{Cov}_\beta(\hat{q}_k)$ 同时在 Loewner 序下大于等于两项，特含全局下界 $\operatorname{Cov}_\beta(\hat{q}_k)\succeq\frac{1}{\beta\mu_k}K_{\mathrm{eff}}^{-1}$）；记红外主项为 $\Sigma_{\mathrm{IR}}(\mu_k)=\frac{\hbar}{2\sqrt{\mu_k}}Z_{\mathrm{eff}}^{-1/2}\widehat{K}_{\mathrm{eff}}^{-1/2}Z_{\mathrm{eff}}^{-1/2}$、动能混合矩阵为 $B_V=-Z_{\mathrm{eff}}^{-1}T_{12}\widetilde{T}_H^{-1/2}$、无量纲耦合比为 $\theta_k=\frac{2\mu_k\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{c_1^2\Omega_{\mathrm{opt},0}^2}$，则在一切满足 $\theta_k<1$ 的非零波矢 $k\ne0$ 上，零温基态可见协方差满足显式非渐近双侧 Loewner 夹逼

$$
\frac{1}{\sqrt{1+\theta_k}}\Sigma_{\mathrm{IR}}(\mu_k)+\frac{\hbar}{2}B_V\bigl(\widetilde{H}_0+\mu_k\widehat{W}_{22}+\tfrac{1}{2}\Omega_{\mathrm{opt},0}^2I_{M_h}\bigr)^{-1/2}B_V^{\mathsf T}\preceq\operatorname{Cov}_\infty(\hat{q}_k)\preceq\frac{1}{\sqrt{1-\theta_k}}\Sigma_{\mathrm{IR}}(\mu_k)+\frac{\hbar}{\sqrt{2}\,\Omega_{\mathrm{opt},0}}B_VB_V^{\mathsf T}
$$

（特别地，当 $\mu_k\to0^+$ 时有 $\operatorname{Cov}_\infty(\hat{q}_k)=\Sigma_{\mathrm{IR}}(\mu_k)+O(1)$，当无折合动能混合 $T_{12}=0$ 时余项更紧为 $O(\sqrt{\mu_k})$）；

3. **实空间局域零均值涨落随 $L\to\infty$ 的维数收敛与发散二分（谐振门户系统的红外维数标度，对比 Mermin–Wagner 1966；Hohenberg 1967）**：令实空间格点零均值投影场为 $\widetilde{q}(x)=\hat{q}(x)-\frac{1}{L^d}\sum_{y\in\Lambda_L}\hat{q}(y)=\frac{1}{L^{d/2}}\sum_{k\ne0}e^{ik\cdot ax}\hat{q}_k$。当固定晶格常数 $a>0$ 并令周期边长 $L\to\infty$ 时：
   - 在零温量子基态（$\beta=\infty$）下，$\operatorname{Tr}\operatorname{Cov}_\infty(\widetilde{q}(x))=\frac{1}{L^d}\sum_{k\ne0}\operatorname{Tr}\operatorname{Cov}_\infty(\hat{q}_k)$ 当且仅当空间维数 $d\ge2$ 时关于 $L$ 一致有界，而在 $d=1$ 时按 $\Theta(\ln L)$ 发散；
   - 在有限正温 KMS 热态（$0<\beta<\infty$）下，$\operatorname{Tr}\operatorname{Cov}_\beta(\widetilde{q}(x))$ 当且仅当空间维数 $d\ge3$ 时关于 $L$ 一致有界，而在 $d=2$ 时按 $\Theta(\ln L)$ 发散、在 $d=1$ 时按 $\Theta(L)$ 发散。

**证明。** 对第 1 项，因变换 $\binom{q}{h}=S\binom{q}{\xi}$ 的左上块为 $I_M$、右上块为 $0$，有 $\Pi_VS=\begin{pmatrix}I_M&0\end{pmatrix}$（其中 $\Pi_V=\begin{pmatrix}I_M&0\end{pmatrix}$）。因此对任意可逆对称矩阵 $B$，$[B^{-1}]_{VV}=\Pi_VB^{-1}\Pi_V^{\mathsf T}=(\Pi_VS)(S^{\mathsf T}BS)^{-1}(\Pi_VS)^{\mathsf T}=[(S^{\mathsf T}BS)^{-1}]_{11}$。将此式分别应用于 $S^{\mathsf T}V_0(\sigma)S=\operatorname{diag}(\sigma^2I_M,H_0)$ 与 $S^{\mathsf T}(V_0+\mu_kV_1)S=\begin{pmatrix}\mu_kK_{\mathrm{eff}}&\mu_kW_{12}\\ \mu_kW_{12}^{\mathsf T}&H_0+\mu_kW_{22}\end{pmatrix}$，分块逆矩阵 Schur 补公式立即给出 $[V_0(\sigma)^{-1}]_{VV}=\sigma^{-2}I_M$ 与精确恒等式 $K_{\mathrm{vis}}(\mu_k)=\mu_kK_{\mathrm{eff}}-\mu_k^2W_{12}(H_0+\mu_kW_{22})^{-1}W_{12}^{\mathsf T}$。因 $W_{22}\succeq0$ 且 $H_0\succ0$，算子求逆的反单调性给出 $0\preceq(H_0+\mu_kW_{22})^{-1}\preceq H_0^{-1}$，两边夹乘 $\mu_k^2W_{12}(\cdot)W_{12}^{\mathsf T}$ 即得第 1 项的全部 Loewner 不等式。

对第 2 项，在动能正交化坐标 $\hat{X}_k=SU_T\hat{Y}_k$、$\hat{P}_k=(SU_T)^{-\mathsf T}\hat{\Pi}_k$ 下，$\hat{H}_k=\frac{1}{2}\hat{\Pi}_k^\dagger\hat{\Pi}_k+\frac{1}{2}\hat{Y}_k^\dagger\mathcal{M}(\mu_k)\hat{Y}_k$（对一切 $k\ne0$ 有 $\mathcal{M}(\mu_k)\succ0$，且 $[\hat{Y}_{k,\alpha},\hat{Y}_{k',\gamma}^\dagger]=0$、$[\hat{Y}_{k,\alpha},\hat{\Pi}_{k',\gamma}^\dagger]=i\hbar\delta_{kk'}\delta_{\alpha\gamma}$）；在非零波矢总哈密顿量 $\hat{H}_{\ne0}=\sum_{k\in\Lambda_L^*\setminus\{0\}}\hat{H}_k$ 中利用实对称性 $\mathcal{M}(\mu_{-k})=\mathcal{M}(\mu_k)$ 将自共轭实模（$\Lambda_L^*$ 中 $k=-k$）与共轭模对 $\{k,-k\}$（$\Lambda_L^*$ 中 $k\ne-k$）展开为独立正频厄米玻色简正模，谱分解即给出 $\operatorname{Cov}_\beta(\hat{Y}_k)=\frac{\hbar}{2}\mathcal{M}(\mu_k)^{-1/2}\coth(\frac{\beta\hbar}{2}\mathcal{M}(\mu_k)^{1/2})$ 与 $\operatorname{Cov}_\infty(\hat{Y}_k)=\frac{\hbar}{2}\mathcal{M}(\mu_k)^{-1/2}$（由张量分解 $\mathcal{F}_0\otimes\mathcal{F}_{\ne0}$ 知，$\hat{H}_0(\sigma)+\hat{H}_{\ne0}$ 在 $\sigma>0$ 下对 $\mathcal{F}_0$ 求偏迹消去零模配分因子 $Z_{0,\beta}(\sigma)$ 后恒等于 $\rho_{\beta,\ne0}$ 与 $|0\rangle_{\ne0}\langle0|$；对全格点一致正则化 $V_0(\sigma)$，每个 $k\ne0$ 的正定频率阵 $\mathcal{M}_\sigma(\mu_k)=\mathcal{M}(\mu_k)+\sigma^2U_T^{\mathsf T}S^{\mathsf T}\operatorname{diag}(I_M,0_{M_h})SU_T\to\mathcal{M}(\mu_k)\succ0$，高斯简正模密度阵与真空态按迹范数收敛且全体有限阶高斯矩按 Wick 公式收敛）。对一切标量 $u>0$，由 $e^{-u}=\cosh u-\sinh u>0$、$\frac{d}{du}(u\cosh u-\sinh u)=u\sinh u>0$ 及 $e^{-u}<1<\frac{\sinh u}{u}$ 立得初等双曲不等式

$$
\max\!\left(\frac{1}{u},\,1\right)<\coth u<\frac{1}{u}+1\qquad(\forall u>0).
$$

在谱上取 $u=\frac{\beta\hbar}{2}\lambda^{1/2}$（$\lambda\in\operatorname{spec}\mathcal{M}(\mu_k)$），即得 $\max_{\preceq}\{\frac{1}{\beta}\mathcal{M}(\mu_k)^{-1},\frac{\hbar}{2}\mathcal{M}(\mu_k)^{-1/2}\}\preceq\operatorname{Cov}_\beta(\hat{Y}_k)\preceq\frac{1}{\beta}\mathcal{M}(\mu_k)^{-1}+\frac{\hbar}{2}\mathcal{M}(\mu_k)^{-1/2}$；两边夹乘 $\Pi_VSU_T(\cdot)U_T^{\mathsf T}S^{\mathsf T}\Pi_V^{\mathsf T}$ 并注意 $(SU_T)\mathcal{M}(\mu_k)^{-1}(SU_T)^{\mathsf T}=V(\mu_k)^{-1}$ 的左上块恰为 $K_{\mathrm{vis}}(\mu_k)^{-1}\succeq(\mu_kK_{\mathrm{eff}})^{-1}$，立得热—零点分解夹逼。再取 $\sigma=\frac{1}{2}\Omega_{\mathrm{opt},0}^2$，由定理 11.1 的完平方不等式及其变号对偶同时给出分块对角双侧界

$$
\mathcal{M}_-(\mu_k)=\begin{pmatrix}\mu_k\widehat{K}_{\mathrm{eff}}-\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}&0\\ 0&\frac{1}{2}\Omega_{\mathrm{opt},0}^2I_{M_h}\end{pmatrix}\preceq\mathcal{M}(\mu_k)\preceq\begin{pmatrix}\mu_k\widehat{K}_{\mathrm{eff}}+\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}&0\\ 0&\widetilde{H}_0+\mu_k\widehat{W}_{22}+\frac{1}{2}\Omega_{\mathrm{opt},0}^2I_{M_h}\end{pmatrix}=\mathcal{M}_+(\mu_k).
$$

因 $\widehat{K}_{\mathrm{eff}}\succeq c_1^2I_M\succ0$，在 $\sigma=\frac{1}{2}\Omega_{\mathrm{opt},0}^2$ 下有标量化界 $0\preceq\frac{\mu_k^2}{\sigma}\widehat{W}_{12}\widehat{W}_{12}^{\mathsf T}\preceq\frac{2\mu_k^2\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{\Omega_{\mathrm{opt},0}^2}I_M\preceq\theta_k\mu_k\widehat{K}_{\mathrm{eff}}$，故当 $\theta_k<1$ 时 $\mathcal{M}_\pm(\mu_k)$ 的左上块分别被纯标量倍数 $(1-\theta_k)\mu_k\widehat{K}_{\mathrm{eff}}\succ0$（从下）与 $(1+\theta_k)\mu_k\widehat{K}_{\mathrm{eff}}$（从上）正定控制。因函数 $t\mapsto t^{-1/2}=\frac{1}{\pi}\int_0^\infty(t+s)^{-1}s^{-1/2}\,ds$ 在 $(0,\infty)$ 上算子单调递减（Löwner 1934），有 $\mathcal{M}_+(\mu_k)^{-1/2}\preceq\mathcal{M}(\mu_k)^{-1/2}\preceq\mathcal{M}_-(\mu_k)^{-1/2}$；两端分块对角阵求负二分之一次幂后仍为严格分块对角阵，左乘 $\Pi_VSU_T=\begin{pmatrix}Z_{\mathrm{eff}}^{-1/2}&B_V\end{pmatrix}$、右乘其转置时交叉项恒等于零，直接给出所示非渐近双侧 Loewner 夹逼，且由 $(\frac{1}{\sqrt{1\mp\theta_k}}-1)\Sigma_{\mathrm{IR}}(\mu_k)=O(\sqrt{\mu_k})$ 立得渐近式 $\operatorname{Cov}_\infty(\hat{q}_k)=\Sigma_{\mathrm{IR}}(\mu_k)+O(1)$。

对第 3 项，平移不变性使不同波矢 $k\ne k'$ 正交无关联，故 $\operatorname{Cov}_\beta(\widetilde{q}(x))=\frac{1}{L^d}\sum_{k\ne0}\operatorname{Cov}_\beta(\hat{q}_k)$。在整个离散布里渊区 $n\in[-L/2,L/2)^d\cap\mathbb{Z}^d\setminus\{0\}$ 上，由 $\frac{2}{\pi}\theta\le\sin\theta\le\theta$（$\theta\in[0,\pi/2]$）知 $\frac{16}{L^2a^2}\|n\|_2^2\le\mu_k\le\frac{4\pi^2}{L^2a^2}\|n\|_2^2$；结合 $(V_0+\mu_kV_1)$ 在全非零布里渊区上正定连续，在 $\mu_k\ge\delta_0>0$ 的紫外区域内每项 $\operatorname{Tr}\operatorname{Cov}_\infty(\hat{q}_k)$ 与 $\operatorname{Tr}\operatorname{Cov}_\beta(\hat{q}_k)$ 一致有正上下界，贡献 $O(1)$；在红外球 $0<\mu_k<\delta_0$ 内，由第 1–2 项的双侧界知 $\operatorname{Tr}\operatorname{Cov}_\infty(\hat{q}_k)=\Theta(\mu_k^{-1/2})=\Theta(L/\|n\|_2)$，而有限正温下 $\operatorname{Tr}\operatorname{Cov}_\beta(\hat{q}_k)=\Theta(\mu_k^{-1})=\Theta(L^2/\|n\|_2^2)$。将有限和 $\frac{1}{L^d}\sum_{1\le\|n\|_2\le cL}(L/\|n\|_2)^{\alpha}=L^{\alpha-d}\sum_{1\le\|n\|_2\le cL}\|n\|_2^{-\alpha}$ 分别在 $\alpha=1$（零温量子基态）与 $\alpha=2$（有限正温 KMS 态）下与 $d$ 维球壳积分比较：$d>\alpha$ 时 $L^{\alpha-d}\cdot\Theta(L^{d-\alpha})=\Theta(1)$ 一致有界，$d=\alpha$ 时为 $\Theta(\ln L)$，$d<\alpha$（即 $d=1,\alpha=2$）时为 $\Theta(L)$。∎

## 12. 第 10–11 节的来源、文献归属与适用边界

**来源与适用边界 12.1。** 第 10–11 节在不修改第 1–9 节任何既有条目的前提下，在离散周期晶格 $(\mathbb{Z}/L\mathbb{Z})^d$ 上补齐了 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 第 19 节（命题 19.1 与注 19.1）与第 21–29 节保留的三项离散—无隙桥梁：模拟引力与涌现时空中多组分场出现多重声速／双度量以及利用内部对称群恢复共同二阶传播锥的物理研究方向归属 Barceló–Liberati–Visser 2005、Liberati–Visser–Weinfurtner 2006 第 4.4 节与第 7 节及 Sindoni 2011；定理 10.2 第 3 项在不假定未约化全系统满足 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 定理 21.1、定理 22.3 与假设 23.1 的全系统等速或未约化不可约条件、亦不要求隐藏表示不可约的前提下，由零模切交织恒等式 $D_gN_0=N_0R_g$ 给出可见不可约门户导出共同红外声速的精确代数证明，并在命题 10.3 中证明单共享隐藏标量门户（$M_h=1,c_0>0,v_h\ge0,v_h\ne c_0$）必然将 $M\ge2$ 个探针分裂为 $c_\perp^2=c_0^2$ 与 $c_\parallel^2=\frac{c_0^2+\|b\|^2v_h^2}{1+\|b\|^2}$。Schur 补特征值约化误差界的一般数值分析先例归属 Dusson–Sigal–Stamm 2021；定理 11.1 针对无隙声学零模矩阵束构造了同时正交化动能并保持零模核的上三角变换 $SU_T$，由分块完平方与 Weyl 单调性给出无隐藏常数（前因子为渐近紧致的 $1$）的非微扰双侧色散界。一维最近邻谐振链位移—动量响应的精确 Bessel 函数解归属 Schrödinger 1914，离散量子晶格有限群速度指数尾界的一般理论归属 Lieb–Robinson 1972（一般度量图量子自旋系统见 Nachtergaele–Sims 2006，无界谐振晶格推广归属 Cramer–Serafini–Eisert 2008 与 Nachtergaele–Raz–Schlein–Sims 2009），幂函数 $t\mapsto t^{-1/2}$ 的算子单调性归属 Löwner 1934，低维连续对称无隙涨落的红外维数发散现象归属 Mermin–Wagner 1966 与 Hohenberg 1967；命题 11.2 以精确 $J_{2r}(\frac{2c_0t}{a})$ 超锥非零对易子与 $O(a^2|k|^4)$ 晶格方向差严格划清“红外领先共同声速”与“连续严格零支撑光锥／全频洛伦兹不变性”的界限，而定理 11.3 通过显式分离 $k=0$ 零模发散与 $k\ne0$ 零均值投影扇区的算子单调夹逼闭合了 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 注 19.1。第 10–11 节结论严格限定于二次谐振晶格模型，不声称已导出动态弯曲时空张量引力方程（Einstein 场方程）或非线性相互作用重整化不变性。

## 追加锚（本行以下为增补区）

## 13. 斜交零交集图册的定向锁定、超选择扇区分裂与连续实动力学的 Schrödinger–von Neumann 生成元

**定义 13.1（无预设轴定向图册的非正交图、容许全局复结构集与图册不变实可观测量空间）。** 设 $\mathfrak{A}=\{(\Pi_\alpha,A_\alpha)\}_{\alpha\in\mathcal{I}}$ 是有限维非零实内积空间 $(V,g)$ 上的覆盖锐三轴实切分图册（定义 2.1，$M_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}\Pi_\alpha\succ0$，$J_\alpha=A_{\alpha,1}A_{\alpha,2}A_{\alpha,3}$）。

1. **窗口非正交图**：定义无向简单图 $\Gamma_{\mathfrak{A}}=(\mathcal{I},E_{\mathrm{no}})$，其中不同指标对 $\{\alpha,\beta\}\in E_{\mathrm{no}}$（$\alpha\ne\beta$）当且仅当 $\Pi_\alpha\Pi_\beta\ne0$（注意 $\operatorname{Ran}\Pi_\alpha\cap\operatorname{Ran}\Pi_\beta\ne\{0\}\Rightarrow\Pi_\alpha\Pi_\beta\ne0$，但命题 2.4 第 3 项给出 $\operatorname{Ran}\Pi_1\cap\operatorname{Ran}\Pi_2=\{0\}$ 而 $\Pi_1\Pi_2\ne0$ 的斜交情形）；
2. **无预设轴定向容许全局复结构集**：因局部三轴正交重标号 $R_\alpha\in O(3)$ 允许局部手征变号 $J_\alpha\mapsto(\det R_\alpha)J_\alpha$（引理 2.2），定义图册容许全局正交复结构集为

$$
\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\Bigl\{J\in\operatorname{End}_{\mathbb{R}}(V):J^{\mathsf T}=-J,\ J^2=-I_V,\ \exists\{s_\alpha\}_{\alpha\in\mathcal{I}}\in\{\pm1\}^{\mathcal{I}},\ \forall\alpha\in\mathcal{I},\ \Pi_\alpha J=J\Pi_\alpha=s_\alpha J_\alpha\Bigr\};
$$

3. **图册不变实可观测量空间**：定义与全部容许全局复结构对易的实对称算子空间为

$$
\mathcal{O}_{\mathfrak{A}}(V)=\bigl\{X\in\operatorname{Sym}(V,g):\forall J\in\mathcal{J}_{\mathrm{glob}}(\mathfrak{A}),\ [X,J]=0\bigr\}.
$$

**引理 13.2（斜交零交集窗口的跨投影手征非退化性、定向比公式与连通分量超选择分裂定理）。** 设 $\mathfrak{A}=\{(\Pi_\alpha,A_\alpha)\}_{\alpha\in\mathcal{I}}$ 为 $(V,g)$ 上的覆盖锐三轴图册。

1. **斜交跨投影手征范数恒等式**：对任意 $\alpha,\beta\in\mathcal{I}$，记实 Frobenius 范数平方为 $\|T\|_F^2=\operatorname{Tr}_{\mathbb{R}}(T^{\mathsf T}T)$，恒有

$$
(\Pi_\alpha J_\beta)J_\beta=-\Pi_\alpha\Pi_\beta,\qquad
\|\Pi_\alpha J_\beta\|_F^2=\|J_\alpha\Pi_\beta\|_F^2=\|\Pi_\alpha\Pi_\beta\|_F^2=\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta).
$$

特别地，$\Pi_\alpha\Pi_\beta\ne0\iff\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)>0\iff\Pi_\alpha J_\beta\ne0\iff J_\alpha\Pi_\beta\ne0$（无需 $\operatorname{Ran}\Pi_\alpha\cap\operatorname{Ran}\Pi_\beta\ne\{0\}$）；

2. **边定向比显式公式与 $2^c$ 计数定理**：设 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})\ne\varnothing$，记 $\Gamma_{\mathfrak{A}}$ 的连通分支分解为 $\mathcal{I}=\bigsqcup_{r=1}^c\mathcal{I}_r$（$c\ge1$），并令 $V_r=\sum_{\alpha\in\mathcal{I}_r}\operatorname{Ran}\Pi_\alpha$。则对每个 $J\in\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})$，符号族 $\{s_\alpha(J)\}_{\alpha\in\mathcal{I}}\in\{\pm1\}^{\mathcal{I}}$ 唯一确定，且在每条非正交边 $\{\alpha,\beta\}\in E_{\mathrm{no}}$ 上相对定向乘积由无基迹比唯一锁定：

$$
s_\alpha(J)s_\beta(J)=-\frac{\operatorname{Tr}_{\mathbb{R}}(J_\beta\Pi_\alpha J_\alpha\Pi_\beta)}{\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)}\in\{+1,-1\}.
$$

全空间正交直和分解为 $V=\bigoplus_{r=1}^cV_r$（每个 $\dim_{\mathbb{R}}V_r=2d_r\ge4$ 为偶数，$\sum_{r=1}^cd_r=d=\frac{1}{2}\dim_{\mathbb{R}}V$），容许全局复结构集基数精确为 $|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=2^c$：任取一个 $J_0=\bigoplus_{r=1}^cJ_{0,r}\in\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})$，有

$$
\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\left\{\bigoplus_{r=1}^{c}\epsilon_rJ_{0,r}:(\epsilon_1,\ldots,\epsilon_c)\in\{+1,-1\}^c\right\};
$$

3. **连通性与超选择扇区分裂的充要判据**：在 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})\ne\varnothing$ 下，图册不变实可观测量空间精确分解为各连通分支上的分块对角直和

$$
\mathcal{O}_{\mathfrak{A}}(V)=\bigoplus_{r=1}^{c}\operatorname{Sym}_{J_{0,r}}(V_r),\qquad
\dim_{\mathbb{R}}\mathcal{O}_{\mathfrak{A}}(V)=\sum_{r=1}^{c}d_r^2.
$$

因此，容许复结构在整体复共轭下唯一（$|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=2$）当且仅当 $\Gamma_{\mathfrak{A}}$ 连通（$c=1$），亦当且仅当 $\mathcal{O}_{\mathfrak{A}}(V)$ 不发生跨扇区超选择坍缩而具有满复厄米维数 $\dim_{\mathbb{R}}\mathcal{O}_{\mathfrak{A}}(V)=d^2$。

**证明。** 对第 1 项，由引理 2.2 的 $J_\beta^2=-\Pi_\beta$、$J_\beta^{\mathsf T}=-J_\beta$ 与 $\Pi_\alpha^2=\Pi_\alpha=\Pi_\alpha^{\mathsf T}$，直接计算得 $(\Pi_\alpha J_\beta)J_\beta=\Pi_\alpha J_\beta^2=-\Pi_\alpha\Pi_\beta$，以及

$$
\|\Pi_\alpha J_\beta\|_F^2=\operatorname{Tr}_{\mathbb{R}}\bigl((\Pi_\alpha J_\beta)^{\mathsf T}(\Pi_\alpha J_\beta)\bigr)=\operatorname{Tr}_{\mathbb{R}}(-J_\beta\Pi_\alpha^2J_\beta)=-\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha J_\beta^2)=\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)=\|\Pi_\alpha\Pi_\beta\|_F^2.
$$

由 $(J_\alpha\Pi_\beta)^{\mathsf T}=-\Pi_\beta J_\alpha$ 同理得 $\|J_\alpha\Pi_\beta\|_F^2=\operatorname{Tr}_{\mathbb{R}}(\Pi_\beta\Pi_\alpha)=\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)$。因非零矩阵的 Frobenius 范数严格为正，四个非零条件等价。

对第 2 项，因每个窗口 $\Pi_\alpha\ne0$ 满足 $\|J_\alpha\|_F^2=\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha)\ge4>0$（引理 2.2），由 $\Pi_\alpha J=s_\alpha(J)J_\alpha$ 唯一确定 $s_\alpha(J)\in\{\pm1\}$。对任意边 $\{\alpha,\beta\}\in E_{\mathrm{no}}$，定理 2.3 应用于重标号图册 $\{(\Pi_\gamma,s_\gamma(J)A_\gamma)\}$ 给出 $s_\beta(J)\Pi_\alpha J_\beta=s_\alpha(J)J_\alpha\Pi_\beta$，即 $\Pi_\alpha J_\beta=s_\alpha(J)s_\beta(J)J_\alpha\Pi_\beta$。两边与 $\Pi_\alpha J_\beta$ 作实 Frobenius 内积：左端为 $\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)>0$，右端为 $s_\alpha(J)s_\beta(J)\operatorname{Tr}_{\mathbb{R}}(-J_\beta\Pi_\alpha J_\alpha\Pi_\beta)$，相除并乘 $(s_\alpha(J)s_\beta(J))^2=1$ 即得迹比公式。

若 $r\ne r'$，则对一切 $\alpha\in\mathcal{I}_r$ 与 $\beta\in\mathcal{I}_{r'}$ 有 $\{\alpha,\beta\}\notin E_{\mathrm{no}}$，故 $\Pi_\alpha\Pi_\beta=0$，即 $\operatorname{Ran}\Pi_\alpha\perp\operatorname{Ran}\Pi_\beta$，从而 $V_r\perp V_{r'}$；结合覆盖性 $\sum_{\alpha\in\mathcal{I}}\operatorname{Ran}\Pi_\alpha=V$ 与 $V_r\ne\{0\}$，得正交直和 $V=\bigoplus_{r=1}^cV_r$。任取 $J_0\in\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})$，对 $\alpha\in\mathcal{I}_r$ 有 $J_0(\operatorname{Ran}\Pi_\alpha)=\operatorname{Ran}(J_0\Pi_\alpha)=\operatorname{Ran}(s_\alpha(J_0)J_\alpha)\subseteq\operatorname{Ran}\Pi_\alpha\subseteq V_r$，故 $J_0(V_r)\subseteq V_r$，$J_0=\bigoplus_{r=1}^cJ_{0,r}$；由 $J_{0,r}^2=-I_{V_r}$ 与 $\dim_{\mathbb{R}}V_r\ge\dim_{\mathbb{R}}\operatorname{Ran}\Pi_{\alpha_r}\ge4$ 知 $\dim_{\mathbb{R}}V_r=2d_r$（$d_r\ge2$）。在每个连通分支 $\mathcal{I}_r$ 内任取根 $\alpha_r\in\mathcal{I}_r$，沿 $\mathcal{I}_r$ 的生成树由固定的边比 $s_\alpha(J)s_\beta(J)=s_\alpha(J_0)s_\beta(J_0)$ 归纳可知，存在唯一 $\epsilon_r\in\{\pm1\}$ 使对一切 $\alpha\in\mathcal{I}_r$ 有 $s_\alpha(J)=\epsilon_rs_\alpha(J_0)$，从而在 $V_r$ 上 $(\sum_{\alpha\in\mathcal{I}_r}\Pi_\alpha|_{V_r})J|_{V_r}=\epsilon_r(\sum_{\alpha\in\mathcal{I}_r}\Pi_\alpha|_{V_r})J_{0,r}$；因 $\sum_{\alpha\in\mathcal{I}_r}\Pi_\alpha|_{V_r}\succ0$，必有 $J|_{V_r}=\epsilon_rJ_{0,r}$。反之，对任意 $(\epsilon_1,\ldots,\epsilon_c)\in\{\pm1\}^c$，算子 $J_{(\epsilon)}=\bigoplus_{r=1}^c\epsilon_rJ_{0,r}$ 满足 $J_{(\epsilon)}^{\mathsf T}=-J_{(\epsilon)}$、$J_{(\epsilon)}^2=-I_V$，且对 $\alpha\in\mathcal{I}_r$ 有 $\Pi_\alpha J_{(\epsilon)}=(\epsilon_rs_\alpha(J_0))J_\alpha=J_{(\epsilon)}\Pi_\alpha$。因每个 $V_r\ne\{0\}$ 上 $J_{0,r}\ne-J_{0,r}$，这 $2^c$ 个算子两两不同，故 $|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=2^c$。

对第 3 项，将 $X\in\operatorname{Sym}(V,g)$ 按 $V=\bigoplus_{r=1}^cV_r$ 写成分块矩阵 $(X_{rr'})_{1\le r,r'\le c}$（$X_{rr'}:V_{r'}\to V_r$）。条件 $[X,J_{(\epsilon)}]=0$ 等价于对一切 $1\le r,r'\le c$ 有 $\epsilon_{r'}X_{rr'}J_{0,r'}=\epsilon_rJ_{0,r}X_{rr'}$。当 $r=r'$ 时该式化为 $[X_{rr},J_{0,r}]=0$，即 $X_{rr}\in\operatorname{Sym}_{J_{0,r}}(V_r)$（实维数 $d_r^2$）；当 $r\ne r'$ 时，分别取 $\epsilon_r=\epsilon_{r'}=+1$ 与 $\epsilon_r=+1,\epsilon_{r'}=-1$ 得 $X_{rr'}J_{0,r'}=J_{0,r}X_{rr'}$ 与 $-X_{rr'}J_{0,r'}=J_{0,r}X_{rr'}$，两式相加得 $2J_{0,r}X_{rr'}=0$，左乘 $-J_{0,r}$ 即 $X_{rr'}=0$。故 $\mathcal{O}_{\mathfrak{A}}(V)=\bigoplus_{r=1}^c\operatorname{Sym}_{J_{0,r}}(V_r)$，维数为 $\sum_{r=1}^cd_r^2$；因 $d_r\ge2$，$\sum_{r=1}^cd_r^2=(\sum_{r=1}^cd_r)^2=d^2$ 当且仅当 $c=1$。∎

**定理 13.3（连续可逆实载体动力学的 Schrödinger–von Neumann 生成元涌现与任意维反酉转置分支拓扑消去定理）。** 设 $(V,g)$ 为 $\dim_{\mathbb{R}}V=2d$（$d\ge2$）的实内积空间，配备一对互为相反数的正交复结构 $\mathcal{J}_{\mathrm{glob}}=\{+J,-J\}$（$J^{\mathsf T}=-J$，$J^2=-I_V$，例如由满足 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})\ne\varnothing$ 且非正交图连通的覆盖锐三轴图册唯一生成）。选定定向 $+J$，赋予 $V$ 复标量乘法 $(a+ib)v=av+bJv$（$a,b\in\mathbb{R}$）与第二变元复线性厄米内积

$$
\langle u,v\rangle_J=g(u,v)+i\,g(Ju,v)\qquad(u,v\in V),
$$

构成 $d$ 维复 Hilbert 空间 $\mathcal{H}_J=(V,J,\langle\cdot,\cdot\rangle_J)$。对任意保持厄米性且保迹的映射 $\Lambda:M_d(\mathbb{C})\to M_d(\mathbb{C})$，定义其在定义 7.1 单本体最大纠缠参考切分 $P_{\Phi_d^+}$ 上的 $d$ 维算子纯度亏格为 $D^{(d)}(R_\Lambda)=d\,\operatorname{Tr}_{\mathrm{ref}}(R_\Lambda-R_\Lambda^2)\in\operatorname{Herm}(\mathcal{H}_J)$（$d=2$ 时即 $D_1(R_\Lambda)$）。则：

1. **反酉共轭分支的连通性拓扑消去**：设 $I\subseteq\mathbb{R}$ 为含 $0$ 的连通区间，$t\mapsto O(t)\in O(V,g)$（$t\in I$）为满足 $O(0)=I_V$ 的连续正交演化路径，且保持 $\{+J,-J\}$ 不变：$O(t)\{+J,-J\}O(t)^{\mathsf T}=\{+J,-J\}$（$\forall t\in I$）。则对一切 $t\in I$ 必有

$$
O(t)JO(t)^{\mathsf T}=+J\quad\text{（即 }[O(t),J]=0\text{）},
$$

反酉反对易分支 $OJO^{\mathsf T}=-J$ 被连通性恒等排除，且每个 $O(t)$ 精确为 $\mathcal{H}_J$ 上的复酉算子（$\langle O(t)u,O(t)v\rangle_J=\langle u,v\rangle_J$）；

2. **厄米哈密顿生成元唯一分解与 Schrödinger–von Neumann 方程（文献先例桥接步骤：Stone 1932；Stueckelberg 1960）**：若 $\{O(t)\}_{t\in\mathbb{R}}\subseteq O(V,g)$ 为保持 $\{+J,-J\}$ 不变的可微单参数正交群（$O(t+s)=O(t)O(s)$，$O(0)=I_V$），记实生成元为 $A=\left.\frac{d}{dt}\right|_{t=0}O(t)\in\operatorname{End}_{\mathbb{R}}(V)$，则 $A^{\mathsf T}=-A$ 且 $[A,J]=0$。定义实对称算子 $H_{\mathbb{R}}=JA\in\operatorname{End}_{\mathbb{R}}(V)$，则 $H_{\mathbb{R}}\in\operatorname{Sym}_J(V)$ 唯一确定、在 $\mathcal{H}_J$ 上为复线性厄米自伴算子（$\langle H_{\mathbb{R}}u,v\rangle_J=\langle u,H_{\mathbb{R}}v\rangle_J$），且 $A=-JH_{\mathbb{R}}$（在全局复共轭规范 $+J\mapsto-J$ 下 $H_{\mathbb{R}}\mapsto-H_{\mathbb{R}}$ 而物理生成元 $A=-JH_{\mathbb{R}}$ 严格不变）。对任意纯态轨迹 $\psi(t)=O(t)\psi_0\in V$ 与实 $J$-不变密度轨迹 $R_{\mathbb{R}}(t)=O(t)R_{\mathbb{R}}(0)O(t)^{\mathsf T}\in\operatorname{Sym}_J(V)$，演化方程精确化为无量纲 Schrödinger 方程与 von Neumann 换位子方程（引入正作用量尺度常数 $\hbar>0$ 并置 $\widehat{H}=\hbar H_{\mathbb{R}}$ 即还原带 $\hbar$ 形式）：

$$
J\frac{d}{dt}\psi(t)=H_{\mathbb{R}}\psi(t)\quad\left(\text{即 }i\frac{d}{dt}\psi(t)=H_{\mathbb{R}}\psi(t)\right),\qquad
\frac{d}{dt}R_{\mathbb{R}}(t)=[A,R_{\mathbb{R}}(t)]=-J\bigl[H_{\mathbb{R}},R_{\mathbb{R}}(t)\bigr];
$$

3. **任意维数 $d\ge2$ 保参考纯度正映射的酉／反酉二分与非 CP 转置分支的拓扑消去**：对任意 $d\ge2$ 及保持厄米性、保迹且**单系统正**（$\rho\succeq0\Rightarrow\Lambda(\rho)\succeq0$，不预设完全正性或保单位性）的映射 $\Lambda:M_d(\mathbb{C})\to M_d(\mathbb{C})$，有 $D^{(d)}(R_\Lambda)=0\iff\operatorname{Tr}(R_\Lambda^2)=1\iff\Lambda$ 属于两个拓扑不连通紧流形分支之一：

$$
\mathcal{U}_+(d)=\bigl\{\rho\mapsto U\rho U^\dagger:U\in U(d)\bigr\}\quad\text{或}\quad\mathcal{U}_-(d)=\bigl\{\rho\mapsto U\rho^{\mathsf T}U^\dagger:U\in U(d)\bigr\},
$$

其中酉完全正分支 $\mathcal{U}_+(d)$ 满足 $R_\Lambda\succeq0$ 与 $\lambda_{\min}(R_\Lambda)=0$，而非 CP 反酉转置分支 $\mathcal{U}_-(d)$ 恒满足 $R_\Lambda=(I_d\otimes U)(\frac{1}{d}F_d)(I_d\otimes U^\dagger)$、$D^{(d)}(R_\Lambda)=0$ 及负最小特征值 $\lambda_{\min}(R_\Lambda)=-\frac{1}{d}<0$（重数 $\frac{d(d-1)}{2}$；$d=2,U=I_2$ 时即 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 命题 7.1 的 $F/2$；注意当 $d\equiv0,1\pmod4$ 如 $d=4$ 时转置映射在无迹厄米空间上的行列式为 $(-1)^{d(d-1)/2}=+1$，而 $\lambda_{\min}(R_\Lambda)\in\{0,-\frac{1}{d}\}$ 对一切 $d\ge2$ 普适分离两分支）。因此，任何满足 $\Lambda_0=\mathrm{id}_{M_d(\mathbb{C})}$ 且处处保持 $D^{(d)}(R_{\Lambda_t})=0$ 的连续单参数保迹单系统正映射族 $\{\Lambda_t\}_{t\in I}$（$0\in I$ 为连通区间）必恒有 $\lambda_{\min}(R_{\Lambda_t})\equiv0$，从而拓扑排除整个非 CP 转置分支 $\mathcal{U}_-(d)$，迫使每个 $\Lambda_t(\rho)=U(t)\rho U(t)^\dagger$ 为酉完全正演化。

**证明。** 先验核对 $\langle\cdot,\cdot\rangle_J$：由 $J^{\mathsf T}=-J$ 与 $J^2=-I_V$，对任意 $u,v\in V$ 有 $\langle u,Jv\rangle_J=g(u,Jv)+ig(Ju,Jv)=-g(Ju,v)+ig(u,v)=i\langle u,v\rangle_J$，$\overline{\langle v,u\rangle_J}=g(v,u)-ig(Jv,u)=g(u,v)+ig(Ju,v)=\langle u,v\rangle_J$，且 $\langle u,u\rangle_J=\|u\|^2+ig(Ju,u)=\|u\|^2\ge0$，确为复内积。

对第 1 项，映射 $t\mapsto O(t)JO(t)^{\mathsf T}$ 从连通集 $I$ 连续映入二点离散子集 $\{+J,-J\}$（$\|(+J)-(-J)\|_F=2\sqrt{2d}>0$），故必为常值映射；在 $t=0$ 处取值为 $+J$，故对一切 $t\in I$ 有 $O(t)JO(t)^{\mathsf T}=+J$。右乘 $O(t)$ 得 $O(t)J=JO(t)$，即 $O(t)$ 在 $\mathcal{H}_J$ 上复线性，且 $\langle O(t)u,O(t)v\rangle_J=g(O(t)u,O(t)v)+ig(O(t)Ju,O(t)v)=\langle u,v\rangle_J$。

对第 2 项，在 $t=0$ 处对 $O(t)^{\mathsf T}O(t)=I_V$ 与 $O(t)J=JO(t)$ 求导，立得 $A^{\mathsf T}+A=0$ 与 $AJ=JA$。令 $H_{\mathbb{R}}=JA$，则

$$
H_{\mathbb{R}}^{\mathsf T}=(JA)^{\mathsf T}=A^{\mathsf T}J^{\mathsf T}=(-A)(-J)=AJ=JA=H_{\mathbb{R}},\qquad [H_{\mathbb{R}},J]=J[A,J]=0,
$$

故 $H_{\mathbb{R}}\in\operatorname{Sym}_J(V)$；左乘 $J$ 得 $JH_{\mathbb{R}}=J^2A=-A$，即 $A=-JH_{\mathbb{R}}$（反之任意 $H_{\mathbb{R}}\in\operatorname{Sym}_J(V)$ 定义的 $A=-JH_{\mathbb{R}}$ 满足 $A^{\mathsf T}=-A$ 与 $[A,J]=0$）。对任意 $u,v\in V$，$\langle H_{\mathbb{R}}u,v\rangle_J=g(H_{\mathbb{R}}u,v)+ig(JH_{\mathbb{R}}u,v)=g(u,H_{\mathbb{R}}v)+ig(Ju,H_{\mathbb{R}}v)=\langle u,H_{\mathbb{R}}v\rangle_J$。由 $\frac{d}{dt}O(t)=AO(t)=-JH_{\mathbb{R}}O(t)$ 左乘 $J$ 得 $J\frac{d}{dt}\psi(t)=-J^2H_{\mathbb{R}}\psi(t)=H_{\mathbb{R}}\psi(t)$；对 $R_{\mathbb{R}}(t)=O(t)R_{\mathbb{R}}(0)O(t)^{\mathsf T}$ 求导，利用 $A^{\mathsf T}=-A$ 与 $[R_{\mathbb{R}}(t),J]=0$ 得 $\frac{d}{dt}R_{\mathbb{R}}(t)=AR_{\mathbb{R}}(t)+R_{\mathbb{R}}(t)A^{\mathsf T}=[A,R_{\mathbb{R}}(t)]=-J[H_{\mathbb{R}},R_{\mathbb{R}}(t)]$。

对第 3 项，固定无迹厄米空间 $\operatorname{Herm}_0(\mathcal{H}_J)$ 的满足 $\operatorname{Tr}(G_aG_b)=d\,\delta_{ab}$ 的实基 $\{G_a\}_{a=1}^{d^2-1}$。由正交展开 $P_{\Phi_d^+}=\frac{1}{d^2}(I_d\otimes I_d+\sum_{a=1}^{d^2-1}G_a^{\mathsf T}\otimes G_a)$ 与交换算子 $F_d=\sum_{j,k=0}^{d-1}|j\rangle\langle k|\otimes|k\rangle\langle j|=\frac{1}{d}(I_d\otimes I_d+\sum_{a=1}^{d^2-1}G_a\otimes G_a)$，保厄米保迹映射 $\Lambda$ 唯一表为 $\Lambda(I_d)=I_d+\sum_{a=1}^{d^2-1}t_aG_a$、$\Lambda(G_b)=\sum_{a=1}^{d^2-1}M_{ab}G_a$（$t\in\mathbb{R}^{d^2-1}$，$M\in M_{d^2-1}(\mathbb{R})$），且直接计算得 $\operatorname{Tr}(R_\Lambda^2)=\frac{1}{d^2}(1+\|t\|^2+\|M\|_F^2)$ 与 $\operatorname{Tr}(F_d(\Lambda\otimes\Lambda)(F_d))=1+\|t\|^2+\|M\|_F^2=d^2\operatorname{Tr}(R_\Lambda^2)$。若 $D^{(d)}(R_\Lambda)=0$，取迹得 $0=\operatorname{Tr}D^{(d)}(R_\Lambda)=d(1-\operatorname{Tr}(R_\Lambda^2))$，故 $\operatorname{Tr}(R_\Lambda^2)=1$。此时对单位球面 $S^{2d-1}\subset\mathcal{H}_J$ 上的任一纯态 $P_\psi=|\psi\rangle\langle\psi|$，单系统正性与保迹性给出 $\Lambda(P_\psi)\succeq0$、$\operatorname{Tr}\Lambda(P_\psi)=1$，故 $\operatorname{Tr}(\Lambda(P_\psi)^2)\le1$（取等当且仅当 $\Lambda(P_\psi)$ 为秩一投影）。对 $S^{2d-1}$ 上归一 Haar 测度 $d\psi$ 利用对称二阶矩恒等式 $\int_{S^{2d-1}}(P_\psi\otimes P_\psi)\,d\psi=\frac{1}{d(d+1)}(I_d\otimes I_d+F_d)$ 与 $\operatorname{Tr}(X^2)=\operatorname{Tr}(F_d(X\otimes X))$，得

$$
1\ge\int_{S^{2d-1}}\operatorname{Tr}\bigl(\Lambda(P_\psi)^2\bigr)\,d\psi=\frac{\operatorname{Tr}(\Lambda(I_d)^2)+\operatorname{Tr}(F_d(\Lambda\otimes\Lambda)(F_d))}{d(d+1)}=\frac{d(1+\|t\|^2)+d^2\operatorname{Tr}(R_\Lambda^2)}{d(d+1)}=1+\frac{\|t\|^2}{d+1}\ge1,
$$

同时迫使 $t=0$（即 $\Lambda(I_d)=I_d$ 自动保单位）及连续非负函数 $1-\operatorname{Tr}(\Lambda(P_\psi)^2)\equiv0$（即 $\Lambda$ 将一切纯态映为纯态）。任取标准正交基 $\{|\psi_j\rangle\}_{j=1}^d$，$\sum_{j=1}^d\Lambda(P_{\psi_j})=I_d$ 迫使各秩一投影 $\Lambda(P_{\psi_j})$ 两两正交，从而对一切谱分解 $X=\sum_{j=1}^d\lambda_jP_{\psi_j}$ 有 $\operatorname{Tr}(\Lambda(X)^2)=\sum_{j=1}^d\lambda_j^2=\operatorname{Tr}(X^2)$；极化得 $\Lambda$ 是 $\operatorname{Herm}(\mathcal{H}_J)$ 上的实正交线性双射且保持全部纯态间跃迁概率 $\operatorname{Tr}(\Lambda(P_\psi)\Lambda(P_\phi))=\operatorname{Tr}(P_\psi P_\phi)=|\langle\psi,\phi\rangle|^2$，其伴随逆 $\Lambda^{-1}=\Lambda^\dagger$ 对任意秩一投影 $P_\chi$ 满足 $\langle\psi,\Lambda^\dagger(P_\chi)\psi\rangle=\operatorname{Tr}(P_\chi\Lambda(P_\psi))\ge0$、$\operatorname{Tr}\Lambda^\dagger(P_\chi)=1$ 与 $\operatorname{Tr}(\Lambda^\dagger(P_\chi)^2)=1$，故 $\Lambda$ 给出秩一纯态投影集到自身的满双射及态空间仿射自同构。由 Wigner 射影跃迁概率定理（Wigner 1931；Bargmann 1964；等价地由态空间仿射自同构与因子 Jordan $*$-同构分类定理，Kadison 1951 定理 7、定理 10 与推论 11 及 Kadison 1965 定理 2.6、定理 4.5 与推论 4.7），存在 $U\in U(d)$ 使 $\Lambda\in\mathcal{U}_+(d)$ 或 $\Lambda\in\mathcal{U}_-(d)$。反之，$\Lambda\in\mathcal{U}_+(d)$ 给出秩一投影 $R_\Lambda=P_{(I_d\otimes U)|\Phi_d^+\rangle}$（$D^{(d)}(R_\Lambda)=0,\lambda_{\min}(R_\Lambda)=0$）；$\Lambda\in\mathcal{U}_-(d)$ 给出 $R_\Lambda=(I_d\otimes U)(\frac{1}{d}F_d)(I_d\otimes U^\dagger)$，其平方为 $\frac{1}{d^2}I_{d^2}$，偏迹满足 $\operatorname{Tr}_{\mathrm{ref}}(R_\Lambda)=\frac{1}{d}I_d=\operatorname{Tr}_{\mathrm{ref}}(R_\Lambda^2)$（$D^{(d)}(R_\Lambda)=0$），而在酉旋转反对称子空间 $(I_d\otimes U)\Lambda^2(\mathbb{C}^d)$（维数 $\frac{d(d-1)}{2}\ge1$）上特征值为 $-\frac{1}{d}<0$。最后由 Weyl 特征值微扰界 $|\lambda_{\min}(R_{\Lambda_t})-\lambda_{\min}(R_{\Lambda_s})|\le\|R_{\Lambda_t}-R_{\Lambda_s}\|_{\mathrm{op}}$，连续映射 $t\mapsto\lambda_{\min}(R_{\Lambda_t})\in\{0,-\frac{1}{d}\}$ 在连通集 $I$ 上取初值 $\lambda_{\min}(P_{\Phi_d^+})=0$，故恒等于 $0$，即 $\Lambda_t\in\mathcal{U}_+(d)$。∎

**命题 13.4（单系统正性对本征不扰动锐投影仪器的自动完全正化引理与离散时间反酉反射反例）。**

1. **锐投影效果下“单系统正 + 本征纯态不扰动”自动蕴涵 Lüders 完全正形式（省去定理 7.2 第 3 项 Busch–Lahti–Mittelstaedt 1991／Busch 2008 定理 5 中的预先完全正性假设）**：设 $\Lambda_b:M_d(\mathbb{C})\to M_d(\mathbb{C})$ 为保持厄米性的**单系统正映射**（对一切 $\rho\succeq0$ 有 $\Lambda_b(\rho)\succeq0$，尚未预先假定完全正性 $R_{\Lambda_b}\succeq0$），满足 $\Lambda_b^\dagger(I_d)=P_b$（$P_b^2=P_b=P_b^\dagger$）且对一切单位向量 $|\psi\rangle\in\operatorname{Ran}P_b$ 有 $\Lambda_b(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|$。则对一切 $X\in M_d(\mathbb{C})$ 必有 $\Lambda_b(X)=P_bXP_b$（从而自动完全正）；这表明定理 7.2 第 1 项与第 3 项的逻辑分离精确发生在允许仪器族中的非投影效果单系统正仪器（命题 7.3 第 1 项）与退化子空间内有酉旋转的完全正锐投影仪器（命题 7.3 第 2 项）之间；
2. **删去时间连续性后的离散反酉保图册反射反例**：在 $V=\mathbb{R}^{2d}$（$d\ge2$，例如 $V=\mathbb{R}^8=(\mathbb{R}^2)^{\otimes3}$，$J_\star=I_2\otimes I_2\otimes\omega_2$）及满足 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\{+J_\star,-J_\star\}$ 的连通覆盖锐三轴图册上，离散可逆正交反射群 $\{R_0^n\}_{n\in\mathbb{Z}}\subseteq O(2d)$（其中 $V=\mathbb{R}^8$ 时取 $R_0=I_2\otimes I_2\otimes\sigma_z\in O(8)$）严格保实内积、保图册容许复结构集 $R_0\{+J_\star,-J_\star\}R_0^{\mathsf T}=\{-J_\star,+J_\star\}$，在 $\mathcal{H}_{J_\star}\cong\mathbb{C}^d$ 上诱导复转置自同构 $\rho\mapsto\rho^{\mathsf T}$（单系统正、保迹且 $D^{(d)}(R_T)=0$），但 $R_0J_\star=-J_\star R_0$（$\lambda_{\min}(R_T)=-\frac{1}{d}<0$），不能嵌入任何保持 $\{+J_\star,-J_\star\}$ 的连续单参数正交群，也不存在任何复线性厄米生成元 $H_{\mathbb{R}}\in\operatorname{Sym}_{J_\star}(V)$ 使 $R_0=e^{-J_\star H_{\mathbb{R}}}$。

**证明。** 对第 1 项，因 $\operatorname{Herm}(\operatorname{Ran}P_b)$ 由 $\operatorname{Ran}P_b$ 内的秩一投影线性张成，本征纯态不扰动性通过线性扩张给出 $\Lambda_b(P_bXP_b)=P_bXP_b$（$\forall X\in M_d(\mathbb{C})$）。对任意单位向量 $|\phi\rangle\in\operatorname{Ran}(I_d-P_b)$，有 $\operatorname{Tr}(\Lambda_b(|\phi\rangle\langle\phi|))=\langle\phi,\Lambda_b^\dagger(I_d)\phi\rangle=\langle\phi,P_b\phi\rangle=0$；由单系统正性 $\Lambda_b(|\phi\rangle\langle\phi|)\succeq0$ 知 $\Lambda_b(|\phi\rangle\langle\phi|)=0$，线性扩张得 $\Lambda_b((I_d-P_b)X(I_d-P_b))=0$。现任取单位向量 $|u\rangle\in\operatorname{Ran}P_b$、$|v\rangle\in\operatorname{Ran}(I_d-P_b)$、相位 $\theta\in\mathbb{R}$ 及 $\epsilon>0$，将单系统半正定秩一算子 $|\chi_\epsilon\rangle\langle\chi_\epsilon|$（其中 $|\chi_\epsilon\rangle=\sqrt{\epsilon}|u\rangle+e^{i\theta}|v\rangle$）代入 $\Lambda_b$：

$$
0\preceq\Lambda_b(|\chi_\epsilon\rangle\langle\chi_\epsilon|)=\epsilon|u\rangle\langle u|+\sqrt{\epsilon}\,\Lambda_b\bigl(e^{-i\theta}|u\rangle\langle v|+e^{i\theta}|v\rangle\langle u|\bigr)+0.
$$

两边除以 $\sqrt{\epsilon}>0$ 并令 $\epsilon\downarrow0$，由半正定锥闭性得 $\Lambda_b(e^{-i\theta}|u\rangle\langle v|+e^{i\theta}|v\rangle\langle u|)\succeq0$；将 $\theta$ 换为 $\theta+\pi$ 同理得其负算子亦半正定，故 $\Lambda_b(e^{-i\theta}|u\rangle\langle v|+e^{i\theta}|v\rangle\langle u|)=0$ 对一切 $\theta$ 成立。分别取 $\theta=0$ 与 $\theta=\frac{\pi}{2}$ 作复线性组合，得 $\Lambda_b(|u\rangle\langle v|)=\Lambda_b(|v\rangle\langle u|)=0$，从而 $\Lambda_b(P_bX(I_d-P_b))=\Lambda_b((I_d-P_b)XP_b)=0$，合并四块即 $\Lambda_b(X)=P_bXP_b$。

对第 2 项，$R_0^{\mathsf T}=R_0$、$R_0^2=I_8$，且 $\sigma_z\omega_2\sigma_z=-\omega_2$ 给出 $R_0J_\star R_0^{\mathsf T}=-J_\star$。任何形如 $e^{-J_\star H_{\mathbb{R}}}$（$H_{\mathbb{R}}\in\operatorname{Sym}_{J_\star}(V)$）的算子均与 $J_\star$ 对易，而 $[R_0,J_\star]=2R_0J_\star\ne0$，故 $R_0$ 不具有该形式；由定理 13.3 第 1 项亦知 $R_0$ 不可能位于保持 $\{+J_\star,-J_\star\}$ 的连续路径连通分支中。∎

## 14. 量子起源与离散红外有效光锥的十一前件合成主定理及逻辑独立性反例矩阵

**定义 14.1（无类型悬空候选系统元组与十一项无冗余结构前件）。** 为使每一项前件在其余前件任意真假组合下均严格良定义（无前序结论缺失造成的类型悬空），定义候选系统元组为

$$
\mathfrak{S}=\bigl((V,g),\,J_\star,\,\mathfrak{A},\,\{O_t\}_{t\in\mathbb{T}},\,\mathscr{M},\,(P_0,P_1),\,\mathcal{I}_{\mathrm{adm}},\,\{\Lambda_0^{\mathrm{sharp}},\Lambda_1^{\mathrm{sharp}}\},\,Q,\,\mathcal{L}_{\mathrm{lat}}\bigr),
$$

其中各分量具有如下互不依赖前序定理结论的基础类型：

- **实内积载体与候选正交复结构槽位** $((V,g),J_\star)$：$\dim_{\mathbb{R}}V=2d$（$d\ge2$）的实内积空间 $(V,g)$ 及满足 $J_\star^{\mathsf T}=-J_\star,J_\star^2=-I_V$ 的实算子 $J_\star\in\operatorname{End}_{\mathbb{R}}(V)$，诱导复 Hilbert 空间记为 $\mathcal{H}_\star=(V,J_\star,\langle\cdot,\cdot\rangle_{J_\star})$（$\dim_{\mathbb{C}}\mathcal{H}_\star=d$）；
- **局部初等锐切分窗口族** $\mathfrak{A}=\{(\Pi_\alpha,A_\alpha,J_\alpha)\}_{\alpha\in\mathcal{I}}$：非空有限覆盖窗口族（$M_{\mathfrak{A}}=\sum_{\alpha\in\mathcal{I}}\Pi_\alpha\succ0$），每个 $\Pi_\alpha\in\operatorname{Sym}(V,g)$ 为非零正交投影（$W_\alpha=\operatorname{Ran}\Pi_\alpha$），$A_\alpha|_{W_\alpha}:\mathbb{R}^{k_\alpha}\to\operatorname{Sym}(W_\alpha,g|_{W_\alpha})$（$k_\alpha\ge2$，$\Pi_\alpha A_\alpha(u)=A_\alpha(u)\Pi_\alpha=A_\alpha(u)$）满足定义 5.1 条件 1–3（初等锐 $k_\alpha$ 轴实二元切分，生成不可约代数 $\mathcal{A}_\alpha\subseteq\operatorname{End}_{\mathbb{R}}(W_\alpha)$），$J_\alpha\in\operatorname{End}_{\mathbb{R}}(V)$ 满足 $\Pi_\alpha J_\alpha=J_\alpha\Pi_\alpha=J_\alpha$、$J_\alpha^{\mathsf T}=-J_\alpha$、$J_\alpha^2=-\Pi_\alpha$ 且 $[J_\alpha,A_\alpha(u)]=0$；
- **可逆实正交演化族** $\{O_t\}_{t\in\mathbb{T}}\subseteq O(V,g)$：群参数集 $\mathbb{T}=\mathbb{R}$ 或 $\mathbb{Z}$，$O_0=I_V$，$O_{t+s}=O_tO_s$，且保持候选共轭对 $O_t\{+J_\star,-J_\star\}O_t^{\mathsf T}=\{+J_\star,-J_\star\}$；
- **切分概率菜单族** $\mathscr{M}=\{\mathfrak{M}_\gamma\}_{\gamma\in\Upsilon}$：$\mathcal{H}_\star$ 上由有限切分菜单组成的非空菜单族（定义 6.1，指标集 $\Upsilon$ 非空，每个子菜单 $\mathfrak{M}_\gamma$ 含有限个效果，并集效果集记为 $\mathcal{E}(\mathscr{M})=\bigcup_{\gamma\in\Upsilon}\{E_{\gamma,j}:0\le j\le N_\gamma\}$）；相容菜单族概率赋值指满足 $v(I_{\mathcal{H}_\star})=1$ 且在每个 $\mathfrak{M}_\gamma$ 上满足已声明框架关系 $k_{v,\gamma}\perp L_{\mathfrak{M}_\gamma}$ 的单值映射 $v:\mathcal{E}(\mathscr{M})\to[0,1]$；
- **允许单系统正二元仪器族与指定锐投影读出** $((P_0,P_1),\mathcal{I}_{\mathrm{adm}},\{\Lambda_0^{\mathrm{sharp}},\Lambda_1^{\mathrm{sharp}}\})$：$(P_0,P_1)$ 为 $\mathcal{H}_\star$ 上一对非零互补正交投影（$P_0+P_1=I_{\mathcal{H}_\star}$），$\mathcal{I}_{\mathrm{adm}}$ 为 $M_d(\mathbb{C})$ 上由保持厄米性、单系统正且和映射保迹的二元仪器组成的非空允许族，其中指定锐投影读出 $\{\Lambda_0^{\mathrm{sharp}},\Lambda_1^{\mathrm{sharp}}\}\in\mathcal{I}_{\mathrm{adm}}$ 满足 $(\Lambda_b^{\mathrm{sharp}})^\dagger(I_d)=P_b$（$b\in\{0,1\}$）；
- **有限精度守卫读器量化函数** $Q:[0,1]\to[0,1]$：作用于定义 8.1 固定十五门守卫轨迹（正守卫阈值 $\vartheta=\frac{m_*}{16}\in(0,\frac{1}{16}]$，一致误差 $\delta_Q=\sup_{x\in[0,1]}|Q(x)-x|$）的值域有限静态量化函数；
- **离散空间周期晶格层** $\mathcal{L}_{\mathrm{lat}}=(d_{\mathrm{sp}},a,L,M,M_h,T,V_0,V_1)$（$d_{\mathrm{sp}}\ge1,a>0,L\ge3,M\ge2,M_h\ge1$）：满足定义 10.1 基础稳定性、隐藏库有隙 $H_0\succ0$、可见零模平衡 $A_0-C_0H_0^{-1}C_0^{\mathsf T}=0$ 与非零模有效刚度严格正定 $K_{\mathrm{eff}}=N_0^{\mathsf T}V_1N_0\succ0$ 的离散周期晶格二次正则量子系统。

在 $\mathfrak{S}$ 上定义十一项无耦合结构前件 $\mathsf{Q}_1,\ldots,\mathsf{Q}_{11}$：

- **$\mathsf{Q}_1$（局部可观测量中心内生相位生成）**：对一切 $\alpha\in\mathcal{I}$，$J_\alpha|_{W_\alpha}\in Z(\mathcal{A}_\alpha)$（等价地 $Z(\mathcal{A}_\alpha)\supsetneq\mathbb{R}I_{W_\alpha}$，由定理 5.3 唯一迫使 $k_\alpha=3$ 且 $J_\alpha\in\{\pm A_{\alpha,1}A_{\alpha,2}A_{\alpha,3}\}$）；
- **$\mathsf{Q}_2$（跨投影度量手征相容与载体对齐）**：存在局部定向符号族 $\{s_\alpha\}_{\alpha\in\mathcal{I}}\in\{\pm1\}^{\mathcal{I}}$ 使一切 $\alpha,\beta\in\mathcal{I}$ 满足 $\Pi_\alpha(s_\beta J_\beta)=(s_\alpha J_\alpha)\Pi_\beta$ 且 $\Pi_\alpha J_\star=s_\alpha J_\alpha$；
- **$\mathsf{Q}_3$（非正交切分重叠图连通）**：窗口非正交图 $\Gamma_{\mathfrak{A}}=(\mathcal{I},\{\{\alpha,\beta\}:\alpha\ne\beta,\ \Pi_\alpha\Pi_\beta\ne0\})$ 连通；
- **$\mathsf{Q}_4$（连续可微单参数时间演化）**：时间群为 $\mathbb{T}=\mathbb{R}$，且 $t\mapsto O_t\in O(V,g)$ 关于 $t\in\mathbb{R}$ 可微；
- **$\mathsf{Q}_5$（有限菜单框架关系核完备与公共基完备层析）**：对一切 $\gamma\in\Upsilon$ 有 $L_{\mathfrak{M}_\gamma}=\ker\mathsf{E}_{\mathfrak{M}_\gamma}$，且存在公共基菜单 $\gamma_0\in\Upsilon$ 使 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_{\gamma_0}}=d^2$ 且对一切 $\gamma\in\Upsilon$ 有 $\{E_{\gamma_0,j}\}_{j=0}^{N_{\gamma_0}}\subseteq\{E_{\gamma,j}\}_{j=0}^{N_\gamma}$；
- **$\mathsf{Q}_6$（全正锥秩一投影方向闭合）**：全体秩一正交投影含于菜单效果并集闭包 $\mathcal{P}_1(\mathcal{H}_\star)\subseteq\overline{\mathcal{E}(\mathscr{M})}$；
- **$\mathsf{Q}_7$（单本体纠缠参考切分联合正性）**：对一切 $\{\Lambda_0,\Lambda_1\}\in\mathcal{I}_{\mathrm{adm}}$ 及 $b\in\{0,1\}$，联合参考输出满足 $R_{\Lambda_b}=(I_d\otimes\Lambda_b)(P_{\Phi_d^+})\succeq0$；
- **$\mathsf{Q}_8$（指定锐投影切分的本征纯态不扰动性）**：对每个 $b\in\{0,1\}$ 及一切单位向量 $|\psi\rangle\in\operatorname{Ran}P_b$，有 $\Lambda_b^{\mathrm{sharp}}(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|$；
- **$\mathsf{Q}_9$（闭触发下水平集与 $\frac{3}{4}\vartheta$ 量化误差界）**：量化器触发集 $S_{Q,\vartheta}=Q^{-1}([0,\vartheta])$ 为 $[0,1]$ 的闭子集，且 $\delta_Q<\frac{3}{4}\vartheta=\frac{3m_*}{64}$；
- **$\mathsf{Q}_{10}$（可见不可约正交门户等变性）**：存在群 $G$ 在可见探针空间 $\mathbb{R}^M$ 上的实不可约正交表示 $R_g\in O(M)$ 与隐藏空间上的正交表示 $\widetilde{R}_g\in O(M_h)$，使 $D_g=\operatorname{diag}(R_g,\widetilde{R}_g)$ 对一切 $g\in G$ 保持 $(T,V_0,V_1)$ 共轭不变；
- **$\mathsf{Q}_{11}$（空间红外收敛维数门限）**：对零温量子基态涨落取空间维数 $d_{\mathrm{sp}}\ge2$（对有限正温 $0<\beta<\infty$ 的 KMS 热态涨落取 $d_{\mathrm{sp}}\ge3$）。

**定理 14.2（条件化量子起源与离散晶格红外有效光锥合成主定理）。** 若定义 14.1 中的系统 $\mathfrak{S}$ 同时满足前件 $\mathsf{Q}_1\wedge\mathsf{Q}_2\wedge\cdots\wedge\mathsf{Q}_{11}$，则以下五项结论全部内生闭合：

1. **三轴唯一选型、内生复 Hilbert 载体唯一重构与纯态秩二球面（由 $\mathsf{Q}_1,\mathsf{Q}_2,\mathsf{Q}_3$ 导出）**：局部轴数恒为 $k_\alpha=3$，图册容许全局正交复结构集精确为二元共轭对 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\{+J_\star,-J_\star\}$，其中 $J_\star=M_{\mathfrak{A}}^{-1}\sum_{\alpha\in\mathcal{I}}s_\alpha J_\alpha$ 完全由实二元切分轴积内生重构，图册不变可观测量空间不发生超选择坍缩（$\mathcal{O}_{\mathfrak{A}}(V)=\operatorname{Sym}_{J_\star}(V)\cong_{\mathbb{R}}\operatorname{Herm}(\mathcal{H}_\star)$，实维数 $d^2$），双局部窗口切分实张量复合局部层析完备；在每个四维局部窗口 $W_\alpha$（经引理 3.2 正交同构于定义 4.1 的 $\mathbb{R}^2\otimes_{\mathbb{R}}B_{\alpha,+}$，其中 $B_{\alpha,+}$ 为对齐重标号第三轴的正本征二维实子空间）及全局二分支扩展实载体 $\mathbb{R}^2\otimes_{\mathbb{R}}V$（在定义 4.1 中取 $(V_0,g_0,J_0)=(V,g,J_\star)$，对任意奇偶 $d\ge2$ 均良定义）上，内生算子三轴纯度球面极值态分别精确对应支撑于 $W_\alpha$ 内的秩二 $J_\star$-不变纯态平面与 $\mathbb{R}^2\otimes_{\mathbb{R}}V$ 中的秩二 $(I_2\otimes J_\star)$-不变纯态平面（其单分支扇区 $e_1e_1^{\mathsf T}\otimes\rho_{\mathbb{R}}$ 双射覆盖全空间 $V$ 的全体秩二 $J_\star$-不变纯态平面；定理 2.3、引理 3.2、定理 4.2、定理 5.3、引理 13.2）；
2. **反酉分支拓扑消去与厄米 Schrödinger–von Neumann 生成元（结合 $\mathsf{Q}_4$ 导出）**：演化群 $\{O_t\}_{t\in\mathbb{R}}$ 拓扑排除反酉分支，全由 $\mathcal{H}_\star$ 上的复酉算子组成，且存在唯一复厄米自伴生成元 $H_{\mathbb{R}}=J_\star\dot{O}_0\in\operatorname{Sym}_{J_\star}(V)$ 使 $J_\star\dot{\psi}(t)=H_{\mathbb{R}}\psi(t)$ 与 $\dot{R}_{\mathbb{R}}(t)=-J_\star[H_{\mathbb{R}},R_{\mathbb{R}}(t)]$ 成立（定理 13.3）；
3. **唯一半正定密度算子 Born 迹法则（结合 $\mathsf{Q}_5,\mathsf{Q}_6$ 导出）**：$\mathscr{M}$ 上的每一个相容菜单族概率赋值 $v$ 均自动满足全局 RC，并由唯一的半正定迹一密度算子 $\rho_v\in\operatorname{Herm}_+(\mathcal{H}_\star)$（$\rho_v\succeq0,\operatorname{Tr}\rho_v=1$）给出 $v(E)=\operatorname{Tr}(\rho_vE)$（$\forall E\in\mathcal{E}(\mathscr{M})$，定理 6.2 及 [`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md) 定理 11.2）；
4. **单本体 Kraus 等距记录实现与唯一 Lüders 投影更新（结合 $\mathsf{Q}_7,\mathsf{Q}_8$ 导出）**：$\mathcal{I}_{\mathrm{adm}}$ 中每个仪器均具有完全正 Kraus 分解与单本体内部记录等距实现 $\Lambda_b(\rho)=\sum_{\alpha}K_{b\alpha}\rho K_{b\alpha}^\dagger$，且指定锐互补正交投影读出唯一锁定为 Lüders 投影更新 $\Lambda_b^{\mathrm{sharp}}(\rho)=P_b\rho P_b$（定理 7.2）；
5. **有限比特读器全历史测度同构与离散晶格多探针共同红外声速及一致有界局域涨落（结合 $\mathsf{Q}_9,\mathsf{Q}_{10},\mathsf{Q}_{11}$ 导出）**：有限比特量化正守卫读器在 $|\lambda-\alpha|<\eta$ 内首点闭集可达、跳数一致有界、零差错输出 $J^Q=L$ 并保持十一地址前缀与七地址未来的全历史测度同构（定理 8.2）；同时离散晶格全部 $M$ 条无隙可见探针严格共享单一红外声速 $c_{\mathrm{eff}}>0$（$K_{\mathrm{eff}}=c_{\mathrm{eff}}^2Z_{\mathrm{eff}}$），在 $\mu_kc_{\mathrm{eff}}^2<\Omega_{\mathrm{opt},0}^2$ 内满足紧双侧非微扰色散界 $0\le\mu_kc_{\mathrm{eff}}^2-\omega_j(k)^2\le\frac{\mu_k^2\|\widehat{W}_{12}\|_{\mathrm{op}}^2}{\Omega_{\mathrm{opt},0}^2-\mu_kc_{\mathrm{eff}}^2}$，且实空间格点零均值局域涨落协方差在 $L\to\infty$ 下一致有界（定理 10.2、定理 11.1、定理 11.3）。

**证明。** 由 $\mathsf{Q}_1$ 与定理 5.3，每个窗口必有 $k_\alpha=3$、$\dim_{\mathbb{R}}W_\alpha=4$、双窗口切分实张量复合局部层析完备且 $J_\alpha=\epsilon_\alpha A_{\alpha,1}A_{\alpha,2}A_{\alpha,3}$（$\epsilon_\alpha\in\{\pm1\}$）；结合 $\mathsf{Q}_2$ 与定理 2.3（作用于重标号图册 $\{(\Pi_\alpha,s_\alpha\epsilon_\alpha A_\alpha)\}$）知 $J_\star\in\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})\ne\varnothing$ 且 $J_\star=M_{\mathfrak{A}}^{-1}\sum_{\alpha\in\mathcal{I}}s_\alpha J_\alpha$；再由 $\mathsf{Q}_3$（$c=1$）与引理 13.2 第 2–3 项得 $\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\{+J_\star,-J_\star\}$ 与 $\mathcal{O}_{\mathfrak{A}}(V)=\operatorname{Sym}_{J_\star}(V)$。对每个四维局部窗口 $W_\alpha$，将 $s_\alpha\epsilon_\alpha A_{\alpha,3}|_{W_\alpha}$ 的 $\pm1$ 二维本征子空间记为 $B_{\alpha,+}\oplus B_{\alpha,-}$，引理 3.2 给出等距 $U_\alpha:B_{\alpha,-}\xrightarrow{\sim}B_{\alpha,+}$ 将 $(W_\alpha,s_\alpha\epsilon_\alpha A_\alpha|_{W_\alpha},J_\star|_{W_\alpha})$ 正交同构为定义 4.1 的 $(\mathbb{R}^2\otimes_{\mathbb{R}}B_{\alpha,+},(\sigma_x\otimes I,-\varepsilon\otimes J_\star|_{B_{\alpha,+}},\sigma_z\otimes I),I_2\otimes J_\star|_{B_{\alpha,+}})$，同时对全空间 $(V_0,g_0,J_0)=(V,g,J_\star)$（任意 $d\ge2$）直接构造定义 4.1 的二分支扩展实载体 $\mathbb{R}^2\otimes_{\mathbb{R}}V$；在两者上分别应用定理 4.2 第 3 项（并注意到单分支扇区 $R_{\mathbb{R}}=e_1e_1^{\mathsf T}\otimes\rho_{\mathbb{R}}$ 满足 $D_{m,\mathbb{R}}(R_{\mathbb{R}})=0\iff\rho_{\mathbb{R}}^2=\frac{m}{2}\rho_{\mathbb{R}}$，使 $V$ 中秩二 $J_\star$-不变纯态平面 $\operatorname{span}_{\mathbb{R}}\{x,J_\star x\}$——即单位向量 $x\in V,\|x\|=1$ 模去平面内正交旋转 $x\mapsto(\cos\theta)x+(\sin\theta)J_\star x$——与单分支极值态 $e_1e_1^{\mathsf T}\otimes\frac{m}{2}(xx^{\mathsf T}+(J_\star x)(J_\star x)^{\mathsf T})$ 一一对应），即得结论 1。在 $\{+J_\star,-J_\star\}$ 上应用 $\mathsf{Q}_4$ 与定理 13.3 第 1–2 项得结论 2。在 $\operatorname{Herm}(\mathcal{H}_\star)$ 上，由 $\mathsf{Q}_5$ 与定理 6.2 知公共基菜单 $\mathfrak{M}_{\gamma_0}$ 唯一确定迹一厄米算子 $\rho_v\in\operatorname{Herm}(\mathcal{H}_\star)$ 使 $v(E_{\gamma_0,j})=\operatorname{Tr}(\rho_vE_{\gamma_0,j})$，而任意子菜单 $\mathfrak{M}_\gamma$ 包含 $\{E_{\gamma_0,j}\}$ 且满足 $L_{\mathfrak{M}_\gamma}=\ker\mathsf{E}_{\mathfrak{M}_\gamma}$，故其唯一厄米代表必与 $\rho_v$ 在满秩基 $\{E_{\gamma_0,j}\}$ 上取值相同从而恒等于 $\rho_v$；再由 $\mathsf{Q}_6$ 的秩一投影闭包与线性泛函连续性得对一切单位向量 $|\psi\rangle\in\mathcal{H}_\star$ 有 $\langle\psi,\rho_v\psi\rangle\ge0$，即 $\rho_v\succeq0$，得结论 3。在 $\mathcal{H}_\star$ 上分别将 $\mathsf{Q}_7$ 代入定理 7.2 第 1 项、将 $\mathsf{Q}_7\wedge\mathsf{Q}_8$ 代入定理 7.2 第 3 项，得结论 4。最后将 $\mathsf{Q}_9$ 代入定理 8.2、将 $\mathsf{Q}_{10}$ 代入定理 10.2 第 3 项与定理 11.1、将 $\mathsf{Q}_{11}$ 代入定理 11.3 第 3 项，证毕结论 5。∎

**定理 14.3（同一固定八维实载体上的十一前件逻辑独立性定理与 $11\times 11$ 单槽变异反例矩阵）。** 在**同一个固定八维实内积载体** $V=\mathbb{R}^8=(\mathbb{R}^2)^{\otimes3}$（$d=4$，固定 $J_\star=Q_1=I_2\otimes I_2\otimes\omega_2$，$\mathcal{H}_\star=(V,J_\star,\langle\cdot,\cdot\rangle_{J_\star})\cong\mathbb{C}^4$）上，存在单一基准系统 $\mathfrak{S}_*$ 同时满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$，且对每一个指标 $j\in\{1,\ldots,11\}$，仅替换 $\mathfrak{S}_*$ 的单个对应组件（其余组件完全保持 $\mathfrak{S}_*$ 不变）即得良类型反例系统 $\mathfrak{K}_j$，满足 $\bigwedge_{i\ne j}\mathsf{Q}_i\wedge\neg\mathsf{Q}_j$ 并使定理 14.2 中由 $\mathsf{Q}_j$ 支撑的目标性质精确失效（表中“✓”表示前件成立，“✗”表示仅该项前件不成立）：

| 单槽变异反例（固定 $V=\mathbb{R}^8,\mathcal{H}_\star\cong\mathbb{C}^4$） | $\mathsf{Q}_1$ | $\mathsf{Q}_2$ | $\mathsf{Q}_3$ | $\mathsf{Q}_4$ | $\mathsf{Q}_5$ | $\mathsf{Q}_6$ | $\mathsf{Q}_7$ | $\mathsf{Q}_8$ | $\mathsf{Q}_9$ | $\mathsf{Q}_{10}$ | $\mathsf{Q}_{11}$ | 精确失效的目标结论与定量读数 |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| $\mathfrak{K}_1$（单窗口五轴四元数切分） | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | $k_1=5$，$Z(\mathcal{A}_5)=\mathbb{R}I_8$（$J_\star\notin\mathcal{A}_5$），双切分复合层析维数 $136\ne36$（定理 5.3、命题 5.4(1)） |
| $\mathfrak{K}_2$（八维勾股斜交失配双窗口） | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | $(s_2\Pi_1J_2-s_1J_1\Pi_2)_{1,2}\in\{\pm\frac{3}{25},\pm\frac{21}{25}\}$ 非零，$\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\varnothing$（命题 2.4(2)） |
| $\mathfrak{K}_3$（八维双正交块不连通图册） | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | $|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=4>2$，$\mathcal{O}_{\mathfrak{A}}(\mathbb{R}^8)$ 超选择分裂，$\dim_{\mathbb{R}}\mathcal{O}_{\mathfrak{A}}=8<16$（引理 13.2） |
| $\mathfrak{K}_4$（离散反酉反射群 $\{R_0^n\}_{n\in\mathbb{Z}}$） | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | $R_0J_\star R_0^{\mathsf T}=-J_\star$ 反酉，$\lambda_{\min}(R_T)=-\frac{1}{4}<0$，无厄米生成元 $H_{\mathbb{R}}$（命题 13.4(2)） |
| $\mathfrak{K}_5$（$\mathbb{C}^4$ 仅声明二元互补核菜单族） | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 三次扰动赋值取值 $[\frac{1}{4},\frac{3}{4}]$ 满足二元归一但违反共面 RC，残差 $-\frac{18}{125}\ne0$（命题 6.3(1)） |
| $\mathfrak{K}_6$（$\mathbb{C}^4$ 完备稀疏有限菜单 $\mathfrak{M}_{38}$） | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | 完备 RC（秩 $16$）且全菜单严格正 $\in[\frac{1}{16},\frac{15}{16}]$，但 $\lambda_{\min}(\widehat{H}_*)=-\frac{1}{16}<0$（命题 6.3(2)） |
| $\mathfrak{K}_7$（并入混噪转置正非投影仪器） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | 单系统正且指定锐读出为 Lüders，但非投影分支 $\lambda_{\min}(R_{\Lambda_0^{\mathrm{tr}}})=-\frac{3}{64}<0$，无 Kraus 实现 |
| $\mathfrak{K}_8$（$\mathbb{C}^4$ 秩二投影内翻转 CP 仪器） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | 完全正、锐投影且结果可重复，但 $\Lambda_0(\lvert 0\rangle\langle 0\rvert)=\lvert 1\rangle\langle 1\rvert\ne P_0\lvert 0\rangle\langle 0\rvert P_0$（命题 7.3(2)） |
| $\mathfrak{K}_9$（右连续向下取整或粗步长 $2^{-b}>\vartheta$） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | $Q_{\downarrow,b}$ 首事件时刻不取得；$Q_{\uparrow,b}$（$2^{-b}>\vartheta$）坍缩为 $J_\lambda\equiv0$，总变差失配 $\varphi^{-1}>0$（命题 8.3） |
| $\mathfrak{K}_{10}$（三维晶格单共享隐藏标量门户） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | $d_{\mathrm{sp}}=3$ 涨落一致有界，但两探针红外声速分裂为 $c_\perp^2=1\ne3=c_\parallel^2$（命题 10.3(1)） |
| $\mathfrak{K}_{11}$（一维基态／二维热态 $O(2)$ 矢量门户） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **✗** | 两探针严格共享红外声速 $c_{\mathrm{eff}}^2=\frac{5}{2}$，但实空间零均值涨落按 $\Theta(\ln L)$ 发散（定理 11.3(3)） |

**证明。** 在固定实载体 $V=\mathbb{R}^8=(\mathbb{R}^2)^{\otimes3}$（标准内积 $g$）与 $J_\star=Q_1=I_2\otimes I_2\otimes\omega_2=\omega_2^{\oplus4}$（赋予 $\mathcal{H}_\star\cong\mathbb{C}^4$ 标准正交基 $|0\rangle,|1\rangle,|2\rangle,|3\rangle$）上，定义满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 的单一基准实例 $\mathfrak{S}_*$：
- $\mathfrak{A}_*$：命题 2.4 第 3 项（在同一标准正交基下 $J_0\oplus J_0=I_2\otimes I_2\otimes\omega_2=\omega_2^{\oplus4}=J_\star$）的双窗口成对倾角斜交覆盖初等锐三轴图册 $\{(\Pi_1,A_1,J_1),(\Pi_2,A_2,J_2)\}$（$k_\alpha=3$，$J_\alpha=A_{\alpha,1}A_{\alpha,2}A_{\alpha,3}\in Z(\mathcal{A}_\alpha)$，$\Pi_1J_2=J_1\Pi_2$，$\Pi_\alpha J_\star=J_\alpha$，$\operatorname{Tr}_{\mathbb{R}}(\Pi_1\Pi_2)=2>0$ 故 $\Gamma_{\mathfrak{A}_*}=K_2$ 连通）；
- $\{O_t^*\}_{t\in\mathbb{R}}$：$O_t^*=I_8$（$t\in\mathbb{R}$，平凡 $C^\infty$ 单参数群）；
- $\mathscr{M}_*$：以第 6 项构造的满秩有限菜单 $\mathfrak{M}_0=\mathfrak{M}_{38}$（满足 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_0}=16=4^2$ 且声明完整核基 $L_{\mathfrak{M}_0}=\ker\mathsf{E}_{\mathfrak{M}_0}$）为公共基菜单，对每个单位射线 $[\psi]\in\mathbb{CP}^3$ 取并入 $\{P_\psi,I_4-P_\psi\}\setminus\{E_{0,j}\}_{j=0}^{38}$ 并声明完整核基 $L_{\mathfrak{M}_\psi}=\ker\mathsf{E}_{\mathfrak{M}_\psi}$ 的有限扩展菜单 $\mathfrak{M}_\psi$，组成指标集 $\Upsilon=\{0\}\sqcup\mathbb{CP}^3$ 上的菜单族 $\mathscr{M}_*=\{\mathfrak{M}_0\}\cup\{\mathfrak{M}_\psi\}_{[\psi]\in\mathbb{CP}^3}$（满足 $\gamma_0=0\in\Upsilon$ 及 $\mathcal{P}_1(\mathbb{C}^4)\subseteq\mathcal{E}(\mathscr{M}_*)$）；
- 仪器层：$P_0=|0\rangle\langle0|+|1\rangle\langle1|$，$P_1=|2\rangle\langle2|+|3\rangle\langle3|$，$\mathcal{I}_{\mathrm{adm}}^*=\{\{\Lambda_0^{\mathrm{L\ddot{u}d}},\Lambda_1^{\mathrm{L\ddot{u}d}}\}\}$（$\Lambda_b^{\mathrm{L\ddot{u}d}}(\rho)=P_b\rho P_b$），指定锐读出即 $\{\Lambda_0^{\mathrm{L\ddot{u}d}},\Lambda_1^{\mathrm{L\ddot{u}d}}\}$；
- 读器量化器：$Q^*=Q_{\uparrow,b_*}$，$b_*=\lceil\log_2(\frac{128}{3m_*})\rceil$（$S_{Q^*,\vartheta}$ 闭且 $\delta_{Q^*}=2^{-b_*}\le\frac{3m_*}{128}<\frac{3}{4}\vartheta$）；
- 晶格层 $\mathcal{L}_{\mathrm{lat}}^*$：$d_{\mathrm{sp}}=3,a=1,L=4,M=M_h=2$，定理 10.2 第 3 项的 $O(2)$ 等变矢量门户（$T=I_4,c_0=1,v_h=2,\alpha=1,\Omega=3$，$c_{\mathrm{eff}}^2=\frac{5}{2}$）。

在 $\mathfrak{S}_*$ 上每次仅替换对应单一槽位（其余全部槽位保持 $\mathfrak{S}_*$ 不变）：

1. **$\mathfrak{K}_1$**：仅将 $\mathfrak{A}_*$ 替换为命题 5.4 第 1 项的单窗口初等五轴四元数切分 $\{(I_8,(B_1,\ldots,B_5),Q_1)\}$。因 $[Q_1,B_r]=0$、$M_{\mathfrak{A}}=I_8\succ0$、单顶点图连通且 $\Pi_1J_\star=Q_1=J_1$，$\mathsf{Q}_2,\mathsf{Q}_3$ 及 $\mathsf{Q}_4$–$\mathsf{Q}_{11}$ 全真；唯 $\mathsf{Q}_1$ 假（$k_1=5$，$Z(\mathcal{A}_5)=\mathbb{R}I_8$，$Q_1\notin\mathcal{A}_5$），换位子 $\mathcal{D}_5\cong\mathbb{H}$ 含整个二维球面族的正交复结构，且双切分实张量复合违背局部层析（$136\ne36$）；
2. **$\mathfrak{K}_2$**：仅将 $\mathfrak{A}_*$ 替换为命题 2.4 第 2 项在 $\mathbb{R}^8$ 上的双窗口勾股斜交初等锐三轴图册。此时 $k_\alpha=3$（$\mathsf{Q}_1$ 真），$M_{\mathfrak{A}}\succ0$ 且 $\Pi_1\Pi_2\ne0$ 故 $\Gamma_{\mathfrak{A}}=K_2$ 连通（$\mathsf{Q}_3$ 真），$\mathsf{Q}_4$–$\mathsf{Q}_{11}$ 全真；唯 $\mathsf{Q}_2$ 假，命题 2.4 第 2 项证明对一切 $(s_1,s_2)\in\{\pm1\}^2$ 均有 $s_2\Pi_1J_2\ne s_1J_1\Pi_2$，$\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})=\varnothing$（若改用四分支圈图 $C_4$ 上含一条扭转边的共享二维分支网络，同样在 $\mathbb{R}^8$ 上给出 $\mathcal{H}(C_4)=-1$ 与 $\mathcal{J}_{\mathrm{glob}}=\varnothing$）；
3. **$\mathfrak{K}_3$**：仅将 $\mathfrak{A}_*$ 替换为双正交块初等锐三轴图册 $\{(\Pi_1,A_1,J_\star\Pi_1),(\Pi_2,A_2,J_\star\Pi_2)\}$（$\Pi_1=I_4\oplus0_4,\Pi_2=0_4\oplus I_4$）。此时 $k_\alpha=3$（$\mathsf{Q}_1$ 真），$s_\alpha=+1$ 满足 $\Pi_\alpha J_\beta=0=J_\alpha\Pi_\beta$（$\alpha\ne\beta$）与 $\Pi_\alpha J_\star=J_\alpha$（$\mathsf{Q}_2$ 真），$\mathsf{Q}_4$–$\mathsf{Q}_{11}$ 全真；因 $\Pi_1\Pi_2=0$，$\Gamma_{\mathfrak{A}}$ 有 $c=2$ 个连通分支（唯 $\mathsf{Q}_3$ 假），引理 13.2 给出 $|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=4>2$ 与超选择坍缩 $\dim_{\mathbb{R}}\mathcal{O}_{\mathfrak{A}}(\mathbb{R}^8)=2^2+2^2=8<16$；
4. **$\mathfrak{K}_4$**：仅将 $\{O_t^*\}_{t\in\mathbb{R}}$ 替换为命题 13.4 第 2 项在 $\mathbb{R}^8$ 上的离散正交反射群 $\{R_0^n\}_{n\in\mathbb{Z}}$（$R_0=I_2\otimes I_2\otimes\sigma_z\in O(8)$，$R_0J_\star R_0^{\mathsf T}=-J_\star$）。唯 $\mathsf{Q}_4$ 为假，其余十项全真，$R_0$ 在 $\mathcal{H}_\star\cong\mathbb{C}^4$ 上诱导非 CP 反酉转置映射（$\lambda_{\min}(R_T)=-\frac{1}{4}<0$），无复线性厄米生成元；
5. **$\mathfrak{K}_5$**：仅将 $\mathscr{M}_*$ 替换为仅含单切口二元互补菜单的菜单族 $\mathscr{M}^{(5)}=\{\tilde{\mathfrak{M}}_\psi\}_{[\psi]\in\mathbb{CP}^3}$，其中 $\tilde{\mathfrak{M}}_\psi=(\{I_4,P_\psi,I_4-P_\psi\},\{e_0-e_1-e_2\})$。此时 $\mathcal{P}_1(\mathbb{C}^4)\subseteq\mathcal{E}(\mathscr{M}^{(5)})$（$\mathsf{Q}_6$ 真）且 $\mathsf{Q}_1$–$\mathsf{Q}_4,\mathsf{Q}_7$–$\mathsf{Q}_{11}$ 全真，每个单切口虽有 $L_{\tilde{\mathfrak{M}}_\psi}=\ker\mathsf{E}_{\tilde{\mathfrak{M}}_\psi}$，但 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\tilde{\mathfrak{M}}_\psi}=2<16$ 故不存在秩 $16$ 的公共基菜单（唯 $\mathsf{Q}_5$ 假）；因 $\mathbb{C}^4$ 上秩一投影 $P_\psi$ 与秩三投影 $I_4-P_\phi$ 集合不交，光滑单调三次赋值 $v(P_\psi)=\frac{1}{2}+\frac{1}{4}(2|\langle0,\psi\rangle|^2-1)^3\in[\frac{1}{4},\frac{3}{4}]$、$v(I_4-P_\psi)=1-v(P_\psi)\in[\frac{1}{4},\frac{3}{4}]$ 满足全部已声明二元归一关系，但在二维子空间 $\operatorname{span}_{\mathbb{C}}\{|0\rangle,|1\rangle\}$ 的四个共面勾股秩一方向 $|\psi_1\rangle=|0\rangle,|\psi_2\rangle=|1\rangle,|\psi_{3,4}\rangle=\frac{3|0\rangle\pm|1\rangle}{\sqrt{10}}$（满足 $P_{\psi_3}+P_{\psi_4}=\frac{9}{5}P_{\psi_1}+\frac{1}{5}P_{\psi_2}$）上违反跨切口 RC，残差精确为 $-\frac{18}{125}\ne0$（命题 6.3 第 1 项，$\eta=\frac{1}{2}$），不存在任何厄米迹表示；
6. **$\mathfrak{K}_6$**：仅将 $\mathscr{M}_*$ 替换为单元素有限稀疏完备菜单族 $\{\mathfrak{M}_{38}\}$：在 $\mathbb{C}^4=\mathbb{C}^3\oplus\mathbb{C}|3\rangle$ 上取命题 6.3 第 2 项的四组相互无偏基共 $12$ 个秩一投影 $P_{b,k}\oplus0$、$|3\rangle\langle3|$、$6$ 个跨块耦合秩一投影 $|\psi_{j,\phi}\rangle\langle\psi_{j,\phi}|$（$|\psi_{j,\phi}\rangle=\frac{1}{\sqrt{2}}(|j\rangle+e^{i\phi}|3\rangle)$，$j\in\{0,1,2\},\phi\in\{0,\frac{\pi}{2}\}$）共 $19$ 个秩一投影及其 $19$ 个秩三互补投影 $I_4-E$（共 $38$ 个非平凡效果，连同 $E_0=I_4$），并声明 $\ker\mathsf{E}_{\mathfrak{M}_{38}}$ 的一组完整基。此时 $L_{\mathfrak{M}_{38}}=\ker\mathsf{E}_{\mathfrak{M}_{38}}$ 且 $\operatorname{rank}_{\mathbb{R}}\mathsf{E}_{\mathfrak{M}_{38}}=9+1+6=16=4^2$（$\mathsf{Q}_5$ 真），唯 $\mathsf{Q}_6$ 假；迹一厄米算子 $\widehat{H}_*=\frac{15}{16}H_*\oplus\frac{1}{16}|3\rangle\langle3|$（$H_*=\frac{8}{15}I_3-\frac{3}{5}uu^\dagger$，$u=\frac{1}{\sqrt{21}}(1,2,4)^{\mathsf T}$）诱导的相容赋值 $v_*(E)=\operatorname{Tr}(\widehat{H}_*E)$ 满足全部 RC 且在全部 $38$ 个非平凡菜单效果上严格取值于 $[\frac{1}{16},\frac{15}{16}]\subset(0,1)$，但唯一重构算子具有负特征值 $\lambda_{\min}(\widehat{H}_*)=\frac{15}{16}\cdot(-\frac{1}{15})=-\frac{1}{16}<0$（$\widehat{H}_*\not\succeq0$）；
7. **$\mathfrak{K}_7$**：仅向允许仪器族 $\mathcal{I}_{\mathrm{adm}}^*$ 并入 $\mathbb{C}^4$ 上的非投影单系统正混噪转置二元仪器 $\{\Lambda_0^{\mathrm{tr}},\Lambda_1^{\mathrm{tr}}\}$（$\Lambda_0^{\mathrm{tr}}(X)=\Lambda_1^{\mathrm{tr}}(X)=\frac{1}{2}(\frac{1}{2}X^{\mathsf T}+\frac{1}{8}(\operatorname{Tr}X)I_4)$，效果为 $E_0=E_1=\frac{1}{2}I_4$，对一切单系统态 $X\succeq0$ 保持半正定且和保迹），同时保留指定锐读出 $\{\Lambda_0^{\mathrm{L\ddot{u}d}},\Lambda_1^{\mathrm{L\ddot{u}d}}\}$ 不变。此时 $\mathsf{Q}_8$ 及 $\mathsf{Q}_1$–$\mathsf{Q}_6,\mathsf{Q}_9$–$\mathsf{Q}_{11}$ 全真，唯 $\mathsf{Q}_7$ 假：$R_{\Lambda_0^{\mathrm{tr}}}=\frac{1}{16}F_4+\frac{1}{64}I_{16}$ 在 $\Lambda^2(\mathbb{C}^4)$ 上取负特征值 $-\frac{1}{16}+\frac{1}{64}=-\frac{3}{64}<0$，不存在 Kraus 等距记录实现；
8. **$\mathfrak{K}_8$**：仅将 $\mathcal{I}_{\mathrm{adm}}^*$ 与指定锐读出替换为命题 7.3 第 2 项在 $\mathbb{C}^4$ 上的单元素锐投影可重复 CP 仪器族 $\{\{\Lambda_0,\Lambda_1\}\}$（$\Lambda_0(\rho)=U_0P_0\rho P_0U_0^\dagger,\Lambda_1(\rho)=P_1\rho P_1$，$U_0=|0\rangle\langle1|+|1\rangle\langle0|+P_1$）。此时 $R_{\Lambda_b}\succeq0$（$\mathsf{Q}_7$ 真），唯 $\mathsf{Q}_8$ 假，且 $\Lambda_0(|0\rangle\langle0|)=|1\rangle\langle1|\ne P_0|0\rangle\langle0|P_0$；
9. **$\mathfrak{K}_9$**：仅将 $Q^*$ 替换为命题 8.3 第 1 项的右连续向下取整量化器 $Q_{\downarrow,b_*}$（违背闭下水平集，首事件时刻不取得）或命题 8.3 第 2 项的粗步长向上量化器 $Q_{\uparrow,1}$（$\delta=\frac{1}{2}>\vartheta$，触发集坍缩为 $\{0\}$，产生恒定正总变差偏差 $\varphi^{-1}=\frac{\sqrt{5}-1}{2}>0$），唯 $\mathsf{Q}_9$ 假；
10. **$\mathfrak{K}_{10}$**：仅将 $\mathcal{L}_{\mathrm{lat}}^*$ 替换为命题 10.3 第 1 项在 $d_{\mathrm{sp}}=3$ 上的单共享隐藏标量门户晶格（$M=2,M_h=1,c_0=1,v_h=2,\Omega=3,b=(1,1)^{\mathsf T}$）。此时 $K_{\mathrm{eff}}=\begin{pmatrix}5&4\\ 4&5\end{pmatrix}\succ0$ 且 $d_{\mathrm{sp}}=3$（$\mathsf{Q}_{11}$ 真），唯 $\mathsf{Q}_{10}$ 假（可见置换群 $\mathbb{Z}_2$ 在 $\mathbb{R}^2$ 上可约），两探针红外声速分裂为 $c_\perp^2=1\ne3=c_\parallel^2$；
11. **$\mathfrak{K}_{11}$**：仅将 $\mathcal{L}_{\mathrm{lat}}^*$ 的空间维数由 $d_{\mathrm{sp}}=3$ 改为零温基态下的 $d_{\mathrm{sp}}=1$（或有限正温 $0<\beta<\infty$ 下的 $d_{\mathrm{sp}}=2$），保留 $O(2)$ 不可约等变矢量门户（$\mathsf{Q}_{10}$ 真，两探针严格共享红外声速 $c_{\mathrm{eff}}^2=\frac{5}{2}$），唯 $\mathsf{Q}_{11}$ 假；由定理 11.3 第 3 项，实空间格点零均值局域涨落方差按 $\Theta(\ln L)$ 随 $L\to\infty$ 发散。∎

## 15. 不可由运动学切分原理导出的物理输入边界与第 13–15 节文献归属

**命题 15.1（十一前件公理类的内部不变变形族与四类不可单独导出的物理输入边界）。** 定义 14.1 的前件合取 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 在以下显式结构变形下保持封闭，因此单凭上述内生切分运动学与二次谐振晶格原理**不能**唯一确定或导出以下四类物理内容：

1. **具体动力学哈密顿量谱与有量纲物理常数的标度自由度**：在满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 的任意系统 $\mathfrak{S}$ 中，将连续演化生成元替换为**任意**复厄米算子 $H_{\mathbb{R}}\in\operatorname{Sym}_{J_\star}(V)$（$O_t=e^{-tJ_\star H_{\mathbb{R}}}$），并对晶格与作用量参数同时实施任意正标度变换

$$
(\hbar,\,a,\,T,\,V_0,\,V_1)\longmapsto(\lambda_\hbar\hbar,\,\lambda_aa,\,\lambda_TT,\,\lambda_0V_0,\,\lambda_1V_1)\qquad(\lambda_\hbar,\lambda_a,\lambda_T,\lambda_0,\lambda_1\in\mathbb{R}_{>0}),
$$

所得系统仍严格满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$，而有效声速与光学间隙分别任意缩放为 $c_{\mathrm{eff}}'=\sqrt{\frac{\lambda_1}{\lambda_T}}\,c_{\mathrm{eff}}$ 与 $\Omega_{\mathrm{opt},0}'=\sqrt{\frac{\lambda_0}{\lambda_T}}\,\Omega_{\mathrm{opt},0}$；故普朗克常数 $\hbar$、极限光速数值、晶格紫外尺度 $a$、耦合谱及具体物质规范群须由独立动力学或经验读数输入；

2. **有限晶格间距 $a>0$ 下的严格零支撑微因果光锥与精确全频洛伦兹对称性**：在满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 且 $a>0$ 固定的离散周期晶格实例（例如取解耦有隙隐藏库的等速超立方晶格 $d_{\mathrm{sp}}\ge2,T=I_{M+M_h},V_0=\operatorname{diag}(0_M,\Omega^2I_{M_h}),V_1=c_0^2I_{M+M_h}$，$\Omega>0,c_0>0$）上，红外领先共同声速 $c_{\mathrm{eff}}=c_0>0$ 与隐藏库有隙 $H_0=\Omega^2I_{M_h}\succ0$ 已完全成立，但其横向零模平板正则算子对 $\bar{q}_1(x_1)=L^{-(d_{\mathrm{sp}}-1)/2}\sum_{x_\perp}\hat{q}_1(x_1,x_\perp)$、$\bar{p}_1(x_1)=L^{-(d_{\mathrm{sp}}-1)/2}\sum_{x_\perp}\hat{p}_1(x_1,x_\perp)$ 严格约化为命题 11.2 第 1 项的一维链：在空间平板距离 $ra$（$L\ge2r+1$）的超锥窗口内，对易子在 $L\to\infty$ 下于 $0<c_0t<\min(ra,a\sqrt{2r+1})$ 内精确等于严格正的 $J_{2r}(\frac{2c_0t}{a})>0$（有限 $L$ 下于 $0<c_0t\le\min(ra,a)$ 内镜像和同样严格为正，迫使该超锥距离上存在严格非零的格点间对易子），且 $d_{\mathrm{sp}}\ge2$ 维超立方布里渊区色散符号存在非零四阶方向差 $\frac{a^2(d_{\mathrm{sp}}-1)}{12d_{\mathrm{sp}}}\kappa^4+O(a^4\kappa^6)>0$；严格零支撑光锥仅在连续标度极限 $a\to0$（配合固定物理波长 $|k|=\text{const}$）下渐近恢复；

3. **动态弯曲时空度规与 Einstein 张量引力场方程**：在 $\mathsf{Q}_{10}\wedge\mathsf{Q}_{11}$ 中，折合对 $(Z_{\mathrm{eff}},K_{\mathrm{eff}}=c_{\mathrm{eff}}^2Z_{\mathrm{eff}})$ 给出的是冻结平移不变背景上的平坦有效声学锥度规 $\eta_{\mathrm{eff}}=\operatorname{diag}(-c_{\mathrm{eff}}^2,1,\ldots,1)$，背景矩阵 $(T,V_0,V_1)$ 无自身动力学自由度亦无应力—能量反作用方程，因而满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 的平坦谐振晶格实例恒有零曲率，不蕴涵弯曲流形微分同胚不变作用量或 Einstein 场方程 $G_{\mu\nu}=8\pi G_{\mathrm{N}}T_{\mu\nu}$；

4. **非高斯强相互作用连续场紫外重整化不动点**：$\mathsf{Q}_{10}\wedge\mathsf{Q}_{11}$ 刻画二次正则自由／线性门户耦合谐振晶格的精确高斯扇区；非二次自相互作用项在 $a\to0$ 连续紫外极限下的重整化群流、反常抵消与非微扰渐近自由／非平凡不动点存在性不属于二次 Schur 消去定理的推论范围。

**证明。** 第 1 项直接由定理 13.3 第 2 项中 $H_{\mathbb{R}}\in\operatorname{Sym}_{J_\star}(V)$ 的任意性及定义 10.1、定理 10.2 中正标量缩放保持 $H_0\succ0$、$A_0-C_0H_0^{-1}C_0^{\mathsf T}=0$、$K_{\mathrm{eff}}\succ0$ 与 $D_g$ 等变性验证：在新参数下 $N_0'=\binom{I_M}{-(\lambda_0H_0)^{-1}(\lambda_0C_0^{\mathsf T})}=N_0$，$Z_{\mathrm{eff}}'=\lambda_TZ_{\mathrm{eff}}$，$K_{\mathrm{eff}}'=\lambda_1K_{\mathrm{eff}}$，$\widetilde{H}_0'=\frac{\lambda_0}{\lambda_T}\widetilde{H}_0$，故两标度比独立任意变化。第 2 项直接由命题 11.2 第 1–2 项在满足 $\mathsf{Q}_1\wedge\cdots\wedge\mathsf{Q}_{11}$ 的等速超立方晶格上给出显式正读数验证。第 3 项由基准实例 $\mathfrak{S}_*$ 的晶格哈密顿量系数 $(T,V_0,V_1)$ 为与量子态无关的常数矩阵、其有效声学度规恒为常系数闵氏对角阵故黎曼曲率恒为零且无引力反作用验证。第 4 项由定义 10.1 的哈密顿量严格为坐标与动量的二次齐次型（Wick 收缩闭合的高斯理论）这一模型定义域边界直接给出。∎

**来源与适用边界 15.2。** 第 13 节将连续酉／正交单参数群生成元理论（Stone 1932）、量子跃迁概率与态空间仿射自同构的酉／反酉二分定理（Wigner 1931；Bargmann 1964；Kadison 1951 定理 7、定理 10 与推论 11；Kadison 1965 定理 2.6、定理 4.5 与推论 4.7）以及实空间反对称复结构算子 $J$ 在实量子力学超选择规则中的作用（对比 Stueckelberg 1960）推进到本卷第 2–3 节的内生覆盖锐三轴图册：引理 13.2 在不假设子空间非零交集（涵盖命题 2.4 第 3 项的斜交零交集窗口）的前提下建立 $\|\Pi_\alpha J_\beta\|_F^2=\operatorname{Tr}_{\mathbb{R}}(\Pi_\alpha\Pi_\beta)$、无基定向比迹公式、$|\mathcal{J}_{\mathrm{glob}}(\mathfrak{A})|=2^c$ 以及非连通图册上 $\mathcal{O}_{\mathfrak{A}}(V)=\bigoplus_{r=1}^c\operatorname{Sym}_{J_{0,r}}(V_r)$ 的超选择坍缩判据；定理 13.3 同时给出厄米哈密顿生成元 $H_{\mathbb{R}}=JA$ 的唯一涌现、任意维数 $d\ge2$ 保参考纯度单系统正映射的 $\mathcal{U}_+(d)\sqcup\mathcal{U}_-(d)$ 二分，以及由连续谱不变量 $\lambda_{\min}(R_{\Lambda_t})\in\{0,-\frac{1}{d}\}$ 对整个非 CP 反酉转置分支（含 [`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md) 命题 7.1 的 $F/2$）的拓扑消去；命题 13.4 第 1 项补充证明了在锐投影效果下“单系统正 + 本征纯态不扰动”已自动蕴涵完全正 Lüders 形式。第 14 节将本卷第 2–13 节与既有卷 [`AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md`](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)、[`AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md`](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)、[`AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md`](AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md)、[`AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md`](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md) 及 [`QUANTUM-REALITY.md`](QUANTUM-REALITY.md) 的接口整合为同一八维实载体上无类型悬空的十一前件合成定理与 $11\times 11$ 单槽变异独立性反例矩阵。第 15 节命题 15.1 将本卷的条件化数学重构与自由参数标度、有限格距离散超锥尾项、动态弯曲时空引力场方程（对比模拟引力声学度规的非动力学背景边界 Barceló–Liberati–Visser 2005）及相互作用连续紫外量子场论严格划清边界。

## 追加锚（本行以下为增补区）

## 16. 单一有限 dyadic 效果表的局部关系证书

**定义 16.1（同一网格上的完整二、三结果菜单表）。** Let $d,m\in\mathbb Z$ with $d\ge2$, $m\ge1$, $N=2^m$, $h=N^{-1}$, and
$$
K=\{E\in\operatorname{Herm}_d(h\mathbb Z[i]):0\le E\le I\}.
$$
Assume a single function $p:K\to[0,1]$ satisfies
$$
\left|\sum_{j=1}^r p(E_j)-1\right|\le\epsilon
$$
for every labelled tuple with $r\in\{2,3\}$, $\sum_jE_j=I$, including zeros and repetitions, where $0\le\epsilon\le1/10$.

All hypotheses concern this one supplied table at this one $N$; no compatibility between different $m$ is assumed. The finite-menu setting of Definition 6.1 is used with all the stated labelled two- and three-result normalization relations.

Let $D_i=|i\rangle\langle i|$. For $i<j$, let $S_{ij}$ have entries $1$ in positions $(i,j),(j,i)$, and let $T_{ij}$ have entries $i,-i$ in these positions. Define the rank-one projections
$$
R_{ij}=(D_i+D_j+S_{ij})/2,\qquad
J_{ij}=(D_i+D_j+T_{ij})/2.
$$
All these projections belong to $K$, including when $m=1$. Together with the $D_i$, they form a real basis $\mathcal B$ of $\operatorname{Herm}_d$, of cardinality $n=d^2$. Define the unique Hermitian matrix $H$ by
$$
\operatorname{Tr}(HQ)=p(Q)\qquad(Q\in\mathcal B).
\tag{16.1}
$$
Put
$$
B_d=4d^2-3d,\quad c_d=B_d^{-1},\quad
K_d=6d^2+6,\quad T_d=2d+1,\quad M_d=2d.
$$

**定理 16.2（一致局部目标证书）。** Under Definition 16.1, for every $E\in K$ with $\|E\|_{\rm op}\le c_d$,
$$
|p(E)-\operatorname{Tr}(HE)|\le K_d\epsilon.
\tag{16.2}
$$
Moreover,
$$
|\operatorname{Tr}H-1|\le T_d\epsilon,
\qquad \|H\|_{\rm op}\le M_d.
\tag{16.3}
$$
These estimates hold for all $m\ge1$; their constants do not grow with $m$.

**证明。** The menu hypothesis gives $0\le p(0)\le2\epsilon$, $|p(I)-1|\le3\epsilon$, and
$$
|p(A)+p(B)-p(A+B)|\le2\epsilon
\tag{16.4}
$$
whenever $A,B,A+B\in K$.

Indeed, subtract the inequalities for $(I,0)$ and $(I,0,0)$ to bound $p(0)$; the pair inequality then bounds $p(I)$. For (16.4), compare $(A,B,I-A-B)$ with $(A+B,I-A-B)$. These are permitted labelled menus even when entries coincide or vanish.

For use in this proof, suppose $Q\in K$, $L\ge1$ is an integer, and $kQ/L\in K$ for $0\le k\le L$. Then
$$
\left|p(kQ/L)-\frac{k}{L}p(Q)\right|\le4\epsilon
\quad(0\le k\le L).
\tag{16.5}
$$

To obtain this estimate, write $f(k)=p(kQ/L)$ and $\delta=2\epsilon$. Equation (16.4) gives $|f(k)+f(l)-f(k+l)|\le\delta$ for $k+l\le L$. Set $g(k)=f(k)-(k/L)f(L)$ on $0\le k<L$, viewed as the cyclic group $\mathbb Z/L\mathbb Z$. When $k+l<L$, its additive defect is at most $\delta$. When $k+l\ge L$, set $u=k+l-L$ and use
$$
|f(k)-f(L-l)-f(u)|\le\delta,\qquad
|f(L)-f(L-l)-f(l)|\le\delta.
$$
Thus $|g(k)+g(l)-g(k+l\bmod L)|\le2\delta$ in both cases. Average this inequality over $l$; translation preserves the finite average, giving $|g(k)|\le2\delta$. The endpoint $k=L$ is exact. This also covers $L=1$.

Write $E_{ij}=x_{ij}+iy_{ij}$, $i<j$, and expand
$$
E=\sum_i a_iD_i+\sum_{i<j}(2x_{ij}R_{ij}+2y_{ij}J_{ij}),
\quad
a_i=E_{ii}-\sum_{j<i}(x_{ji}+y_{ji})-\sum_{j>i}(x_{ij}+y_{ij}).
\tag{16.6}
$$
If $t=\|E\|_{\rm op}$, then $|E_{ij}|\le t$, whence
$$
\sum_i|a_i|+\sum_{i<j}(2|x_{ij}|+2|y_{ij}|)
\le (4d^2-3d)t\le1.
\tag{16.7}
$$
Split (16.6) into its positive and negative coefficients, obtaining $E=P-Q$, with $P,Q\ge0$. Each summand is a coefficient in $[0,1]$ times a member of $\mathcal B$. By (16.7), all partial sums, $P$, and $Q$ are effects. They belong to the original grid: the coefficients of $D_i$ are multiples of $h$, while those of $R_{ij},J_{ij}$ are multiples of $2h$. Consequently (16.5) applies to each summand, with $L=N$ for $D_i$, and $L=N/2$ for $R_{ij},J_{ij}$.

For a positive sum with $k$ nonzero summands, telescoping (16.4) and using (16.5) gives error at most $(6k+2)\epsilon$ between its table value and the corresponding linear combination of the basis values. This bound also holds for $k=0$, since $p(0)\le2\epsilon$. The total number of summands in $P,Q$ is at most $d^2$. Apply (16.4) to $E+Q=P$, and subtract the two linear combinations. The error is at most $(6d^2+6)\epsilon$, proving (16.2).

Since $I=\sum_iD_i$, (16.4) and the menu bounds above yield
$$
|\operatorname{Tr}H-1|\le2(d-1)\epsilon+3\epsilon=T_d\epsilon.
$$
The diagonal entries of $H$ are $p(D_i)\in[0,1]$. Equation (16.1) implies that both real and imaginary parts of every off-diagonal entry lie in $[-1,1]$. Hence its maximum absolute row sum is at most $1+\sqrt2(d-1)\le2d$, which bounds its operator norm. $\square$

## 17. 同一表格的正性探针与局部密度近似

**定理 17.1（同表格秩一探针与一致负谱界）。** Under Definition 16.1, set
$$
A_d=16K_d/c_d,\qquad D_d=16M_dd/c_d,
\quad a_d=A_d\epsilon+D_dh.
$$

The matrix in (16.1) satisfies
$$
\lambda_{\min}(H)\ge-a_d.
\tag{17.1}
$$
**证明。** First suppose $N\ge8d/c_d$. Let $\psi$ be a unit eigenvector for $\lambda=\lambda_{\min}(H)$, and put $R=\sqrt{c_dN}/2$. Round each real and imaginary component of $R\psi$ to an integer, obtaining $v\in\mathbb Z[i]^d$ with
$$
\|v-R\psi\|\le b:=\sqrt{d/2},\qquad R\ge2b.
$$
In particular $v\ne0$. The actual grid effect
$$
F=vv^*/N=\gamma ww^*,\quad w=v/\|v\|,\quad\gamma=\|v\|^2/N
$$
satisfies $c_d/16\le\gamma\le c_d$; hence (16.2) applies. Since $p(F)\ge0$, it gives
$$
w^*Hw\ge-16K_d\epsilon/c_d.
$$
The squared component of $w$ perpendicular to $\psi$ is at most
$$
\eta\le b^2/\|v\|^2\le8d/(c_dN).
$$
The eigenvector property eliminates the cross terms, so
$$
w^*Hw\le\lambda+2M_d\eta
\le\lambda+(16M_dd/c_d)h.
$$
Combining the last two inequalities proves (17.1). If $N<8d/c_d$, then $D_dh>2M_d$, and the already proved $\lambda_{\min}(H)\ge-M_d$ proves (17.1) directly. Thus coarse grids are included. $\square$

**推论 17.2（一致局部密度近似）。** Under Definition 16.1, there is a finite constant depending only on $d$, for example
$$
C_d^{\rm loc}=2T_d+K_d+T_d+2dA_d+2dD_d,
$$
such that one matrix $\rho\succeq0$ with $\operatorname{Tr}\rho=1$ obeys
$$
\max_{E\in K:\,\|E\|_{\rm op}\le c_d}
|p(E)-\operatorname{Tr}(\rho E)|
\le C_d^{\rm loc}(\epsilon+h).
\tag{17.2}
$$

**证明。** If $\epsilon\ge1/(2T_d)$, any density matrix works, because both compared numbers lie in $[0,1]$, and $1\le2T_d\epsilon$. Otherwise $s=\operatorname{Tr}H\ge1/2$. Write $H=H_+-H_-$, $t=\operatorname{Tr}H_-\le da_d$, $Z=\operatorname{Tr}H_+=s+t>0$, and $\rho=H_+/Z$. Then
$$
\|H-\rho\|_1=t+|Z-1|\le2da_d+T_d\epsilon.
\tag{17.3}
$$
For every effect, its trace pairing with $H-\rho$ is bounded by this trace norm. Combine (16.2) and (17.3).

The eigenvector coverage and positive-part normalization steps are intermediate mechanisms from [V59](AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md), Theorem 5.2 and Proposition 5.3, and [V64](AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md), Definition 5.1 and Theorem 5.2. In the present derivation, the local relation certificate, the actual same-grid probes, their positive gain and quadratic directional coverage follow from Definition 16.1; the cited conditional mechanisms do not supply that local certificate. These are mathematical statements about the supplied table, with no physical acquisition or priority assertion.

$\square$

## 18. 任意目标关系的未决问题

**定义 18.1（任意目标关系问题及小效果分解条件）。** For the specific $H$ in (16.1), ask whether there is a finite dimension-only constant $L_d$ such that, for every $m\ge1$ and every table in Definition 16.1,
$$
\sup_{E\in K}|p(E)-\operatorname{Tr}(HE)|
\le L_d(\epsilon+h)
\tag{18.1}
$$
with $L_d$ independent of $m$. If (18.1) holds, (17.1)–(17.3) give a single density matrix approximating the table on all of $K$ at rate $C_d(\epsilon+h)$ with a dimension-only constant, treating the large-$\epsilon$ case as above. Theorem 16.2 establishes the corresponding relation only on $\|E\|\le c_d$. If $E=\sum_{j=1}^k E_j$, where $k\ge1$, $E_j\in K$ and $\|E_j\|_{\rm op}\le c_d$, then telescoping (16.4) and Theorem 16.2 gives the conditional bound
$$
|p(E)-\operatorname{Tr}(HE)|\le[kK_d+2(k-1)]\epsilon.
$$
No uniformly bounded such decomposition is asserted. In particular, dividing or rounding a boundary effect need not preserve its original grid or its positive face. The local estimate and this conditional bound neither prove the all-grid approximation assertion nor provide an admissible counterfamily. The arbitrary-target relation remains an open mathematical question.

## 19. 固定四维的互补投影分解障碍

**命题 19.1（任意 dyadic 精度下的小块分解障碍）。** In fixed dimension $d=4$, for every integer $m\ge1$ and $N=2^m$, there are complementary rank-two grid projections $P,Q\in K$ such that every nonzero grid effect below either projection has operator norm exactly one. In particular, neither projection is a sum of grid effects of norm at most $c_4<1$. This is an obstruction to the small-piece decomposition route; it is not a counterexample to all-grid stability.

**证明。** By Lagrange's classical four-square theorem (every nonnegative integer is a sum of four integer squares) choose Gaussian integers $a,b$ with $|a|^2+|b|^2=N-1=:q$. Put
$$
U=\begin{pmatrix}a&b\\-\overline b&\overline a\end{pmatrix},\qquad
V=\begin{pmatrix}I_2\\U\end{pmatrix},\qquad
P=VV^*/N,\qquad Q=I_4-P.
$$
Then $`U^*U=UU^*=qI_2`$, $`V^*V=NI_2`$, and
$$
P=N^{-1}\begin{pmatrix}I_2&U^*\\U&qI_2\end{pmatrix},\qquad
Q=N^{-1}\begin{pmatrix}qI_2&-U^*\\-U&I_2\end{pmatrix}.
$$
Thus these are complementary rank-two projections in the prescribed grid.

If $0\le F\le P$, its range lies in $\operatorname{ran}P=\operatorname{ran}V$. Consequently $`F=VXV^*`$, where $X$ is its upper-left block. Set $B=NX$. The grid condition makes $B$ an integral Gaussian Hermitian matrix, and the upper-left principal-block inequality gives $0\le B\le I_2$. Its diagonal entries are therefore zero or one. Positivity of $B$ forces every off-diagonal entry incident to a zero diagonal entry to vanish; positivity of $I_2-B$ does the same for every diagonal entry equal to one. Hence $B$ is a diagonal coordinate projection. It follows that $`F=VBV^*/N`$ is itself an orthogonal projection and, when nonzero, has norm one. The same proof for $Q$, using its lower-right block, applies because $`Q=WW^*/N`$ for $`W=\begin{pmatrix}-U^*\\I_2\end{pmatrix}`$, with $`W^*W=NI_2`$. Finally, every positive summand in a decomposition of $P$ is below $P$, so no decomposition into nonzero effects of norm less than one is possible; likewise for $Q$.

For instance, $N=8$ admits $a=2+i,b=1+i$. The four-square input establishes the construction for arbitrarily fine dyadic grids at fixed dimension. This construction supplies no admissible non-Born table. The question in Definition 18.1 still concerns all labelled menus, including relations involving proper subprojections and their complements. $\square$

## 追加锚（本行以下为增补区）

## 20. 偶幺模格给出的固定十六维互补原子对

**定义 20.1（格与模二二次空间）。** In Euclidean $\mathbb R^8$, put

$$
L=\{x\in\mathbb Z^8:\textstyle\sum_i x_i\in2\mathbb Z\}
\ \cup\
\{x\in(\mathbb Z+\tfrac12)^8:\textstyle\sum_i x_i\in2\mathbb Z\}.
$$

This is the classical $E_8$ root lattice. A root means a vector of squared norm two. Write $\overline L=L/2L$, and define

$$
b(\overline x,\overline y)=(x,y)\pmod2,
\qquad q(\overline x)=\|x\|^2/2\pmod2.
$$

For the classical lattice description and root count, see [E8 lattice](https://en.wikipedia.org/wiki/E8_lattice). The lattice and finite quadratic-space facts needed here are proved below. The four-square theorem used in the construction is Lagrange's classical theorem.

**定理 20.2（固定十六维的互补原子对）。** For every integer $m\ge2$, $N=2^m$, $h=N^{-1}$, there are real rank-eight orthogonal projections $P_N,Q_N\in K_{16,m}$ with $P_N+Q_N=I_{16}$ such that

$$
\{F\in K_{16,m}:F\le P_N\}=\{0,P_N\},\qquad
\{F\in K_{16,m}:F\le Q_N\}=\{0,Q_N\}.
\tag{20.1}
$$

The sets include all complex Gaussian Hermitian effects on the original grid.

**证明。** Let $D=\{x\in\mathbb Z^8:\sum_i x_i\in2\mathbb Z\}$ and $u=(1/2,\ldots,1/2)$. Then $L=D\cup(u+D)$, with $2u\in D$, $(u,D)\subset\mathbb Z$ and $\|u\|^2=2$. Every vector of $D$ has even squared norm, so $L$ is even and integral. The covolume of $D$ is two and $[L:D]=2$, giving covolume one for $L$. Thus any integral basis Gram matrix has determinant one. This also proves nondegeneracy of $b$; evenness makes $b$ alternating and $q$ well defined.

The four vectors

$$
\begin{aligned}
g_1&=(1,1,1,1,0,0,0,0),\\
g_2&=(1,1,0,0,1,1,0,0),\\
g_3&=(1,0,1,0,1,0,1,0),\\
g_4&=2e_1
\end{aligned}
$$

have $q=0$ and pairwise $b=0$. Their classes are independent: the coordinate parity of an element of $2L$ is either all zero or all one. The first three parity vectors are independent and their eighth coordinates vanish, so a combination can have either of these two patterns only when its three coefficients vanish. Also $2e_1\notin2L$, since $e_1\notin L$. Their classes span a four-dimensional totally $q$-singular subspace $A$. Nondegeneracy gives $A=A^{\perp_b}$. On each of the fifteen cosets other than $A$, the restriction of $q$ is a nonconstant affine function with linear part $a\mapsto b(x,a)$, and takes the value one eight times. On $A$ it is zero. Thus there are $120$ classes with $q=1$.

The roots in $D$ are the $112$ vectors $\pm e_i\pm e_j$, $i<j$. The half-integral roots are the $128$ vectors with coordinates $\pm1/2$ and an even number of minus signs. There are no other roots. Two distinct roots in the same class modulo $2L$ differ by $2x$ for nonzero $x\in L$, whose squared norm is at least eight. The squared distance of two roots is at most eight, with equality only for opposite roots. The $240$ roots therefore give $120$ distinct opposite pairs and exhaust the $120$ classes with $q=1$.

Let $V$ be any four-dimensional $b$-isotropic subspace of $\overline L$ with $q|_V\ne0$. Choose a basis $v_1,\ldots,v_4$ of $V$ with $q(v_1)=1$ and $q(v_j)=0$ for $j>1$. A symplectic basis extension gives an isotropic complement with basis $w_1,\ldots,w_4$ and $b(v_i,w_j)=\delta_{ij}$. If $q$ vanishes on this complement, replace $w_2$ by $w_2+v_2$. The span remains isotropic and complementary to $V$, and $q(w_2+v_2)=1$.

On the resulting $W$, $q$ is a nonzero linear functional. Its eight classes with value one span $W$: for any fixed such class $z$, every class $w$ with value zero is $z+(z+w)$. Choose root representatives of these eight classes. Their pairwise inner products are even. Distinct classes exclude equal or opposite roots, so the Cauchy inequality forces these even inner products to be zero. They form the asserted orthogonal frame.

The required integral-interval property is as follows. Let $B$ be a real matrix of a $\mathbb Z$-basis of $L$ and $C=B^{\mathsf T}B$. If $X\in\operatorname{Herm}_8(\mathbb Z[i])$ and $0\le X\le C$, then $X=0$ or $X=C$.

First let $Y$ be real integral symmetric with $0\le Y\le C$. Unimodularity makes $C^{-1}Y$ integral. It is self-adjoint for the inner product with Gram matrix $C$, with eigenvalues in $[0,1]$. Each eigenvalue is an algebraic integer and all its algebraic conjugates are eigenvalues of this integral matrix. A nontrivial eigenvalue would have all conjugates strictly between zero and one, whose product cannot be a nonzero integer. Hence all eigenvalues are zero or one, and $C^{-1}Y$ is an integral orthogonal projection splitting $L$ into orthogonal sublattices.

This splitting is trivial. Nonzero vectors of $L$ have squared norm at least two, so every root lies wholly in one summand. The integer roots $\pm e_i\pm e_j$ have a connected graph under nonzero inner product and span $\mathbb R^8$. They all lie in one summand, and the other vanishes. Thus $Y=0$ or $Y=C$.

For general Hermitian $X$, its entrywise real part $Y$ is integral symmetric and satisfies $0\le Y\le C$ on real vectors. If $Y=0$, positivity and zero diagonal force $X=0$. If $Y=C$, apply that argument to $C-X$. This covers all Gaussian Hermitian subeffects.

The quaternion endomorphisms used in the construction have the following form. For integers $a,b,c,e$ with odd $t=a^2+b^2+c^2+e^2$, put

$$
A=\begin{pmatrix}
a&-b&-c&-e\\
b&a&-e&c\\
c&e&a&-b\\
e&-c&b&a
\end{pmatrix},\qquad T=\operatorname{diag}(A,A).
$$

Then $T^{\mathsf T}T=TT^{\mathsf T}=tI_8$, both $T$ and $T^{\mathsf T}$ preserve $L$, and $\overline T$ is an isometry of $q$ on $L/2L$ with inverse $\overline{T^{\mathsf T}}$.

The displayed matrix is the standard integral matrix of left quaternion multiplication; multiplication gives $A^{\mathsf T}A=AA^{\mathsf T}=tI_4$. All row and column sums are odd, with common parity $a+b+c+e\equiv t\pmod2$. The sum of the row sums is $4a$. Thus $T$ preserves integral vectors of even coordinate sum. For half-integral $x=n+u\in L$, $\sum_i n_i$ is even. All coordinates of $Tx$ are half-integral and

$$
\sum_i(Tx)_i=\sum_j\Bigl(\sum_iT_{ij}\Bigr)n_j+4a\in2\mathbb Z.
$$

Hence $T$ preserves $L$. Transposition replaces $b,c,e$ by their negatives, so the same holds for $T^{\mathsf T}$. Since $t$ is odd, their compositions are the identity modulo $2L$. Also $q(\overline{Tx})=tq(\overline x)=q(\overline x)$.

Put $t=N/2-1$, which is positive and odd. Lagrange's four-square theorem supplies integers $a,b,c,e$ with squared sum $t$; take $T$ from the quaternion construction above. Let $R$ have columns $e_1+e_2,e_1-e_2,\ldots,e_7+e_8,e_7-e_8$. Then $RR^{\mathsf T}=2I_8$. Its column group contains $2L$, since

$$
2x=\sum_{j=1}^8(x,r_j)r_j\qquad(x\in L).
$$

This group has covolume $16$, so its image $U$ in $L/2L$ has dimension four. It is $b$-isotropic with $q|_U\ne0$. Apply the isotropic-complement argument above to $\overline T^{-1}U$, obtaining an isotropic complement $W$ and an orthogonal root frame $S$ whose classes span $W$.

Define real $8$-by-$16$ matrices

$$
V_+=[\,R\ \ TS\,],\qquad V_-=[\,-T^{\mathsf T}R\ \ S\,].
$$

Their columns generate $L$ as an integral group. The first column group contains $2L$ from $R$ and has image $U+\overline T W=L/2L$. The second contains $2L$ from $S$ and has image $\overline T^{-1}U+W=L/2L$. Here $2L\subset S\mathbb Z^8$ follows from the same orthogonal-frame identity as for $R$. Direct multiplication gives

$$
V_+V_+^{\mathsf T}=V_-V_-^{\mathsf T}=2(1+t)I_8=NI_8,
\qquad V_+V_-^{\mathsf T}=0.
$$

Consequently

$$
P_N=V_+^{\mathsf T}V_+/N,\qquad Q_N=V_-^{\mathsf T}V_-/N
$$

are complementary rank-eight orthogonal projections. Integrality of $L$ puts them on the original $h$ grid.

For either matrix $V$, suppose $F\in K_{16,m}$ lies below $V^{\mathsf T}V/N$. Set $Z=NF\in\operatorname{Herm}_{16}(\mathbb Z[i])$. The inequality $0\le Z\le V^{\mathsf T}V$ implies $\ker V\subset\ker Z$, so

$$
Z=V^{\mathsf T}A_0V,\qquad 0\le A_0\le I_8,
\qquad A_0=VZV^{\mathsf T}/N^2.
$$

Write $V=BM$ in an integral basis $B$ of $L$. The columns generate $L$, so the integral matrix $M$ has an integral right inverse $J$. Thus

$$
X=J^{\mathsf T}ZJ=B^{\mathsf T}A_0B
\in\operatorname{Herm}_8(\mathbb Z[i]),\qquad
0\le X\le B^{\mathsf T}B.
$$

the integral-interval argument above gives $X=0$ or $B^{\mathsf T}B$, hence $A_0=0$ or $I_8$ and $F=0$ or $V^{\mathsf T}V/N$. This proves both interval assertions for every complex grid subeffect. $\square$

## 21. 完整有限菜单表的统一取消估计反例族

**定理 21.1（固定维数的全表反例）。** Fix complex dimension $d=16$. For every integer $m\ge7$, put $N=2^m$, $h=N^{-1}$, and choose $P_N,Q_N$ from Theorem 20.2. On the whole original effect set $K=K_{16,m}$ define one table

$$
p_N(E)=\begin{cases}
3/4,&E=P_N,\\
1/4,&E=Q_N,\\
\operatorname{Tr}(E)/16,&E\notin\{P_N,Q_N\}.
\end{cases}
\tag{21.1}
$$

It takes values in $[0,1]$ and satisfies exactly

$$
\sum_{j=1}^r p_N(E_j)=1
\quad\left(r\in\{2,3\},\ E_j\in K,\ \sum_jE_j=I_{16}\right)
\tag{21.2}
$$

for all labelled tuples, including zeros and repetitions. With the registered nearest-coordinate rounding $R_h$, ties toward zero, set at $E=P_N$

$$
G=16hI_{16},\qquad F=R_h(P_N/2)+G,\qquad D=2F-P_N.
$$

These are original-grid effects and

$$
p_N(P_N)+p_N(D)-2p_N(F)=\frac14.
\tag{21.3}
$$

For $\epsilon=0$, the residual divided by $\epsilon+h$ equals $2^m/4$ and is unbounded. Thus no finite dimension-only constants $C_{16},C'_{16}$ satisfy the registered cancellation estimate. The matrix $H$ of (16.1) is $I_{16}/16$, and

$$
|p_N(P_N)-\operatorname{Tr}(HP_N)|=\frac14,
\tag{21.4}
$$

which also refutes the uniform assertion (18.1).

**证明。** The trace table and both exceptional values lie in $[0,1]$. If a tuple summing to $I_{16}$ contains $P_N$, its other entries lie below $Q_N$. By (20.1), they are zero or $Q_N$, and exactly one is $Q_N$. The same argument applies to a tuple containing $Q_N$. Its table values therefore sum to $3/4+1/4=1$, with any extra zero contributing zero. If neither exceptional projection occurs, the sum is the trace sum $\operatorname{Tr}(I_{16})/16=1$. This covers every labelled two- and three-entry menu and every allowed repetition.

For $\delta=R_h(P_N/2)-P_N/2$, coordinate rounding and the maximum absolute row sum give

$$
\|\delta\|_{\rm op}\le\alpha h,\qquad
\alpha=\tfrac12+15/\sqrt2<16.
$$

Each diagonal error is at most $h/2$ and each off-diagonal modulus is at most $h/\sqrt2$. Hence, for $N\ge128$,

$$
\begin{aligned}
F&=P_N/2+16hI_{16}+\delta\succeq(16-\alpha)hI_{16},
&\|F\|_{\rm op}&\le\tfrac12+(16+\alpha)h<\tfrac12+32h\le\tfrac34,\\
D&=32hI_{16}+2\delta\succeq2(16-\alpha)hI_{16},
&\|D\|_{\rm op}&\le(32+2\alpha)h<64h\le\tfrac12.
\end{aligned}
$$

Rounding makes $F$ a grid matrix and $D=2F-P_N$ is on the same grid. The bounds prove $F,D\in K$ and exclude equality with $P_N$ or $Q_N$, both of norm one. Thus $p_N(F)$ and $p_N(D)$ are their trace values. The arithmetic identity $P_N+D=2F$ gives

$$
p_N(P_N)+p_N(D)-2p_N(F)
=\frac34-\operatorname{Tr}(P_N)/16
=\frac34-\frac8{16}=\frac14.
$$

All table arguments lie in the original $K$. The matrices $P_N/2$ and $\delta$ occur only in arithmetic. Every grid in the family obeys $N\ge128\ge4d$, and $\epsilon=0\in[0,1/10]$. Given finite $C_{16},C'_{16}\ge0$, choose $m\ge7$ with $2^m>4C'_{16}$ to contradict the proposed bound.

Every member of the tomography basis $\mathcal B$ of Definition 16.1 has rank one; the exceptional projections have rank eight. Thus (21.1) agrees with the trace table on $\mathcal B$, which proves $H=I_{16}/16$ and (21.4). The family uses a single complete table on each finite grid and no cross-grid hypothesis. $\square$

## 追加锚（本行以下为增补区）

## 22. Gaussian 整数原子的复八维全 dyadic 投影实现

**定理 22.1（四维整数原子与八维互补投影）。** For every integer $m\ge2$, put $N=2^m$ and $h=N^{-1}$. There exist complementary rank-four orthogonal projections $P_m,Q_m\in K_{8,m}$ such that

$$
\{F\in K_{8,m}:0\le F\le P_m\}=\{0,P_m\},
\qquad
\{F\in K_{8,m}:0\le F\le Q_m\}=\{0,Q_m\}.
\tag{22.1}
$$

The construction uses the following Gaussian Hermitian matrix, denoted by $G$ to distinguish it from the tomography matrix $H$ in (16.1):

$$
Q=\begin{pmatrix}1+i&1\\-1&1-i\end{pmatrix},
\qquad
G=H_{\mathbb H}=
\begin{pmatrix}2I_2&Q\\Q^\dagger&2I_2\end{pmatrix}.
\tag{22.2}
$$

**证明。** Matrix multiplication gives

$$
\begin{gathered}
Q^\dagger Q=QQ^\dagger=3I_2,\qquad
G^2-4G+I_4=0,\qquad G^{-1}=4I_4-G,\\
(G-I_4)^2=2G,\qquad
\operatorname{spec}(G)=\{2-\sqrt3,2-\sqrt3,2+\sqrt3,2+\sqrt3\},
\qquad \det G=1.
\end{gathered}
\tag{22.3}
$$

For example, the off-diagonal block matrix $G-2I_4$ has square $3I_4$ and trace zero, giving the stated spectrum. Thus $G$ is positive definite. For every $z\in\mathbb Z[i]^4$, the value $z^\dagger Gz$ is an even integer: the diagonal terms are $2|z_j|^2$, and the off-diagonal terms occur as twice an integral real part. Positivity and the standard coordinate vectors therefore give

$$
\min_{0\ne z\in\mathbb Z[i]^4}z^\dagger Gz=2.
\tag{22.4}
$$

Here the integral-interval argument of §20 applies to the realification

$$
\mathcal R(G)=
\begin{pmatrix}\operatorname{Re}G&-\operatorname{Im}G\\
\operatorname{Im}G&\operatorname{Re}G\end{pmatrix}.
$$

For completeness, its required hypotheses and their consequence can be checked without a lattice classification. This is an integral positive definite Gram matrix with determinant $(\det G)^2=1$. Its eight standard real basis vectors have squared norm two. In the order $e_1,e_2,e_3,e_4,ie_1,ie_2,ie_3,ie_4$, the nonzero-pairing graph contains the edges

$$
(1,3),(1,4),(1,7),(2,3),(2,8),(3,5),(4,6),
$$

which connect all eight vertices. If $X\in\operatorname{Herm}_4(\mathbb Z[i])$ and $0\le X\le G$, the integer matrix

$$
A=\mathcal R(G)^{-1}\mathcal R(X)
$$

is self-adjoint for this Gram inner product and has all eigenvalues in $[0,1]$. An eigenvalue strictly between zero and one is an algebraic integer whose conjugates are also eigenvalues of $A$. Its irreducible polynomial cannot have zero or one as a root, so all these conjugates lie strictly between zero and one. Their product would be a nonzero integer of absolute value less than one, a contradiction. Thus $A^2=A$. Its integral image and integral kernel split the lattice orthogonally. By (22.4), a vector of squared norm two cannot have nonzero components in both summands. Every standard real basis vector lies in one summand; the connected pairing graph places all of them in the same summand. The other summand is zero. Consequently

$$
\{X\in\operatorname{Herm}_4(\mathbb Z[i]):0\le X\le G\}=\{0,G\}.
\tag{22.5}
$$

This is the §20 order-atomicity mechanism on the explicit Gaussian Gram matrix (22.2), rather than another assumption about a classified lattice.

To realize the atom at every dyadic scale, set

$$
\begin{gathered}
Q_0=Q-I_2=\begin{pmatrix}i&1\\-1&-i\end{pmatrix},
\qquad
S=\operatorname{diag}(iQ_0,iQ_0),\\
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
U=\begin{pmatrix}0&\sigma_x\\\sigma_x&0\end{pmatrix}.
\end{gathered}
$$

Direct multiplication yields

$$
\begin{gathered}
Q_0^\dagger=-Q_0,\quad Q_0^2=-2I_2,\quad
S^\dagger=S,\quad U^\dagger=U,\quad S^2=2I_4,\quad U^2=I_4,\\
SG=GS,\qquad UG=GU,\qquad SU+US=0.
\end{gathered}
\tag{22.6}
$$

Choose integers $c_1,c_2,c_3$ with

$$
c_1^2+2c_2^2+2c_3^2=N/2-2=:n_m.
\tag{22.7}
$$

For $m=2$ use $(0,0,0)$, and for $m=3$ use $(0,1,0)$. For $m\ge4$, $n_m\equiv2\pmod4$, so it is not of the form $4^a(8b+7)$ with nonnegative integers $a,b$. Legendre's classical three-square theorem, used here only as an intermediate arithmetic tool, supplies $n_m=x^2+y^2+z^2$. Reduction modulo four shows that exactly one of $x,y,z$ is even. Relabel it as $x$ and put $c_1=x$, $c_2=(y+z)/2$, $c_3=(y-z)/2$. The latter two numbers are integers and satisfy (22.7). The arithmetic criterion used here is the [Legendre three-square criterion](https://mathworld.wolfram.com/SumofSquaresFunction.html).

Define Gaussian integer matrices

$$
B=i c_1U+i c_2S+c_3US,\qquad C=I_4+(G-I_4)B.
$$

The three matrices $iU,iS,US$ are skew-Hermitian, commute with $G$, anticommute pairwise, and have squares $-I_4,-2I_4,-2I_4$. Equations (22.6)–(22.7) therefore imply

$$
\begin{gathered}
B^\dagger=-B,\qquad B^2=-n_m I_4,\qquad BG=GB,\qquad CG=GC,\\
C^\dagger C=CC^\dagger
=I_4+2n_mG
=(N-4)G+I_4
=NG-G^2.
\end{gathered}
\tag{22.8}
$$

Indeed $C^\dagger=I_4-(G-I_4)B$, and their product is $I_4-(G-I_4)^2B^2$. This also proves (22.8) for the two separately chosen coarse scales.

Now put

$$
V=\begin{pmatrix}G\\C\end{pmatrix},\qquad
W=\begin{pmatrix}-C^\dagger\\G\end{pmatrix}.
$$

The commutation and norm identities above give

$$
V^\dagger V=W^\dagger W=NG,\qquad V^\dagger W=0.
$$

Both matrices have column rank four. Thus

$$
P_m=\frac1N VG^{-1}V^\dagger,\qquad
Q_m=\frac1N WG^{-1}W^\dagger=I_8-P_m
\tag{22.9}
$$

are complementary rank-four orthogonal projections. All entries of $G^{-1},V,W$ are Gaussian integers, so both projections lie on the original $h$ grid.

It remains to prove their order-atomicity against all complex grid subeffects. If $0\le F\le P_m$ and $Z=NF\in\operatorname{Herm}_8(\mathbb Z[i])$, positivity implies $\operatorname{ran}Z\subseteq\operatorname{ran}V$. Let $X$ be the upper-left four-by-four block of $Z$. Since the upper block of $V$ is the invertible matrix $G$, restriction to this block reconstructs every operator supported on $\operatorname{ran}V$:

$$
Z=VG^{-1}XG^{-1}V^\dagger,\qquad 0\le X\le G.
\tag{22.10}
$$

For example, write $Z=VTV^\dagger$ and obtain $X=GTG$; the upper-left block of $NP_m$ is $G$. Now $X$ is Gaussian Hermitian integral, so (22.5) gives $X=0$ or $X=G$, and hence $F=0$ or $F=P_m$. For $Q_m$, use the lower-right block of $Z=NF$ and the lower block $G$ of $W$; the same calculation applies. This proves (22.1). $\square$

## 23. 所有复维数不小于八的单网格 Born 障碍

**定理 23.1（全尺度全表反例与任意厄米拟合下界）。** For every pair of integers $d\ge8$, $m\ge2$, there is a table $p:K_{d,m}\to[0,1]$ satisfying Definition 16.1 with $\epsilon=0$ whose pinned matrix (16.1) is the density matrix

$$
H_0=(I_8/8)\oplus0_{d-8}.
$$

It obeys $p(E)=\operatorname{Tr}(H_0E)$ for every $E\in K_{d,m}$ of operator norm strictly less than one. At the rank-four projection $E_*=P_m\oplus0_{d-8}$, however,

$$
p(E_*)-\operatorname{Tr}(H_0E_*)=\frac12.
\tag{23.1}
$$

Moreover, with $B_d=4d^2-3d$ as in §16,

$$
\inf_{H'\in\operatorname{Herm}_d}
\ \sup_{E\in K_{d,m}}
|p(E)-\operatorname{Tr}(H'E)|
\ \ge\frac{1}{2(B_d+1)}.
\tag{23.2}
$$

Consequently (18.1) fails for every fixed $d\ge8$.

**证明。** Take $P_m,Q_m$ from Theorem 22.1. For the complementary block, use the same effect-set formula $K_{r,m}=\{M\in\operatorname{Herm}_r(h\mathbb Z[i]):0\le M\le I_r\}$ for every $r\ge1$, including $r=1$, and interpret $K_{0,m}$ as the singleton consisting of the zero-dimensional matrix. Define disjoint fibers

$$
\mathcal F_+=\{P_m\oplus M:M\in K_{d-8,m}\},\qquad
\mathcal F_-=\{Q_m\oplus M:M\in K_{d-8,m}\},
$$

and define one function on the entire original grid by

$$
p(E)=\operatorname{Tr}(H_0E)+
\begin{cases}
1/2,&E\in\mathcal F_+,\\
-1/2,&E\in\mathcal F_-,\\
0,&E\notin\mathcal F_+\cup\mathcal F_-.
\end{cases}
\tag{23.3}
$$

On either fiber the trace value is $4/8=1/2$, so the modified values are one and zero. Elsewhere the trace value is in $[0,1]$. Thus $p$ takes values in $[0,1]$, and $p(0)=0$.

We verify every labelled two- and three-entry menu, including zeros and repetitions. First, an effect whose upper-left eight-by-eight block is a projection has zero off-diagonal blocks relative to $\mathbb C^8\oplus\mathbb C^{d-8}$. To see this, write that block as $A$. For $x\in\ker A$, the equality $\langle(x,0),E(x,0)\rangle=0$ and positivity force $E(x,0)=0$. For $x\in\operatorname{ran}A$, apply the same reasoning to $I-E$. These two subspaces exhaust $\mathbb C^8$ and force the cross blocks to vanish.

Suppose a menu contains $E_1=P_m\oplus M$. Each other entry has an eight-by-eight principal block $A_j$ in the same grid satisfying $0\le A_j\le Q_m$. By (22.1) each $A_j$ is zero or $Q_m$. Since their sum is $Q_m$, exactly one is $Q_m$, and all the others are zero. The preceding cross-block argument shows that this unique entry belongs to $\mathcal F_-$. Thus the perturbations in (23.3) cancel exactly. The argument with the two fibers exchanged is identical. If neither fiber occurs, the menu sum is just $\operatorname{Tr}(H_0I_d)=1$. This verifies the complete menu condition, without excluding any allowed coincidence of labels or entries.

Every member of $\mathcal B$ has rank one, whereas every member of either fiber has rank at least four. Hence (23.3) agrees with the $H_0$ trace table on $\mathcal B$, and (16.1) pins precisely $H=H_0$. All fiber members have norm one, proving the claimed agreement on the open norm ball. Equation (23.1) follows because $E_*\in\mathcal F_+$.

For an arbitrary Hermitian $H'$, set

$$
\eta=\sup_{E\in K_{d,m}}|p(E)-\operatorname{Tr}(H'E)|,\qquad D=H'-H_0.
$$

The basis values imply $|\operatorname{Tr}(DQ)|\le\eta$ for every $Q\in\mathcal B$. Expand $E_*$ using (16.6). The first inequality of (16.7), which holds with coefficient sum at most $B_d\|E_*\|_{\rm op}=B_d$ even outside the local ball, gives

$$
|\operatorname{Tr}(DE_*)|\le B_d\eta,\qquad
\frac12\le
|p(E_*)-\operatorname{Tr}(H'E_*)|+
|\operatorname{Tr}(DE_*)|
\le(B_d+1)\eta.
$$

This proves (23.2) for every $H'$, without any positivity or trace assumption on $H'$. Finally, at fixed $d$, (23.1) holds for arbitrarily large $m$, whereas any dimension-only multiple of $h=2^{-m}$ tends to zero. It contradicts (18.1) with $\epsilon=0$. $\square$

**适用边界 23.2。** Theorems 20.2–21.1 already give the real rank-eight construction in complex dimension sixteen and its full-table obstruction. Theorems 22.1–23.1 supply the additional complex-dimension-eight construction, all $m\ge2$, its extension to every $d\ge8$, and the arbitrary-Hermitian lower bound. The single-grid problem (18.1) for $2\le d\le7$ is not settled by these constructions. The threshold eight and the three-square arithmetic restriction describe this construction; they are not an impossibility theorem for counterexamples in smaller complex dimensions. These conclusions concern the explicitly defined effect grids and menu relations, with no empirical assertion about physical realizations.

## 24. 保留单侧谱余量的原网格内部稳定性

**定理 24.1（任意维的单侧内部定理）。** For each integer $d\ge2$, retain $c_d,K_d,T_d,M_d$ from Definition 16.1 and define

$$
\begin{gathered}
k_d=\left\lceil\log_2(2/c_d)\right\rceil,\qquad q_d=2^{k_d},\\
U_d=(2q_d-1)K_d+4(q_d-1),\\
L_d=U_d+T_d+1+\frac{8d(1+dM_d)}{c_d}.
\end{gathered}
\tag{24.1}
$$

For every $m\ge1$, every table satisfying Definition 16.1, and every $E\in K_{d,m}$ satisfying at least one of

$$
\lambda_{\max}(E)\le1-4dh,\qquad
\lambda_{\min}(E)\ge4dh,
\tag{24.2}
$$

the pinned matrix $H$ satisfies

$$
|p(E)-\operatorname{Tr}(HE)|\le L_d(\epsilon+h).
\tag{24.3}
$$

In the fine-grid regime $h\le c_d/(8d)$, the sharper bounds are $U_d\epsilon$ under the first condition in (24.2) and $(U_d+T_d+1)\epsilon$ under the second.

**证明。** Suppose first that $h\le c_d/(8d)$ and $E\le(1-4dh)I_d$. Round the diagonal entries and the real and imaginary parts above the diagonal of $E/2$ to nearest multiples of $h$, and fill the lower triangle by Hermitian symmetry. Denote the resulting Hermitian grid matrix by $S$. Each diagonal error is at most $h/2$, and each off-diagonal modulus error is at most $h/\sqrt2$. Therefore, by the maximum absolute row sum,

$$
\|S-E/2\|_{\rm op}
\le\bigl(1/2+(d-1)/\sqrt2\bigr)h\le dh.
$$

Put $F=S+dhI_d$ and $R=2F-E$. All three matrices $F,R,2F$ have entries on the original grid: $d$ is integral, and $E$ and $S$ are grid matrices. The error bound gives

$$
\begin{gathered}
0\le R\le4dhI_d,\qquad 0\le F,\qquad
2F=E+R\le I_d,\\
\|F\|_{\rm op}\le\|E\|_{\rm op}/2+2dh.
\end{gathered}
\tag{24.4}
$$

Thus $F,R,2F,E+R,I-2F$ are effects in the same $K_{d,m}$. In particular the labelled menus

$$
(F,F,I-2F),\quad(2F,I-2F),\quad
(E,R,I-E-R),\quad(E+R,I-E-R)
$$

are legitimate. Subtracting their normalization relations, or applying (16.4) twice, yields

$$
|p(E)-2p(F)+p(R)|\le4\epsilon.
\tag{24.5}
$$

This step is iterated only while retaining the upper margin. Set $E_0=E$ and let $E_{j+1}=F_j$ be the construction above applied to $E_j$. If $\|E_j\|_{\rm op}\le1-4dh$, then (24.4) gives $\|E_{j+1}\|_{\rm op}\le1/2$. Since $4dh\le c_d/2\le1/2$, this is again at most $1-4dh$. Consequently every step is legal. Induction in (24.4) gives

$$
\|E_j\|_{\rm op}
\le2^{-j}\|E\|_{\rm op}+4dh(1-2^{-j}).
$$

At $j=k_d$ this is at most $c_d/2+4dh\le c_d$. Each remainder $R_j$ also has norm at most $4dh\le c_d/2$. Thus Theorem 16.2 applies to $E_{k_d}$ and all $R_j$ on the original grid.

Write $e(A)=p(A)-\operatorname{Tr}(HA)$. Since $E_j=2E_{j+1}-R_j$ as matrices, (24.5) gives

$$
|e(E_j)|\le2|e(E_{j+1})|+(K_d+4)\epsilon,\qquad
|e(E_{k_d})|\le K_d\epsilon.
$$

Summing this finite geometric recurrence yields

$$
|e(E)|\le
\bigl[q_dK_d+(q_d-1)(K_d+4)\bigr]\epsilon
=U_d\epsilon.
$$

If instead $\lambda_{\min}(E)\ge4dh$, then $I-E$ satisfies the upper-margin condition. The pair menu and (16.3) imply

$$
|e(E)+e(I-E)|
=|p(E)+p(I-E)-\operatorname{Tr}H|
\le(T_d+1)\epsilon.
$$

This proves the stated fine-grid lower-margin estimate.

Finally, if $h>c_d/(8d)$, (16.3) and $0\le E\le I_d$ give, for every grid effect,

$$
|p(E)-\operatorname{Tr}(HE)|\le1+dM_d
<\frac{8d(1+dM_d)}{c_d}\,h.
$$

This proves (24.3) also on coarse grids. $\square$

**适用边界 24.2。** The region excluded by the disjunction (24.2) is exactly

$$
\{E\in K_{d,m}:
\lambda_{\min}(E)<4dh,\quad
\lambda_{\max}(E)>1-4dh\}.
$$

It consists of effects whose spectrum comes within the stated margin of both zero and one. In particular it contains every nontrivial projection, including the rank-four witness in Theorem 23.1. Thus (24.3) and the single-grid counterexamples have disjoint hypotheses at those witnesses.

## 25. 跨尺度相容性强制的全局 Born 线性与噪声边界

**定理 25.1（精确相容塔的唯一全局密度矩阵）。** Fix integers $d\ge2$ and $m_0\ge1$. For every $m\ge m_0$, let $p_m$ satisfy Definition 16.1 on $K_{d,m}$ with $\epsilon=0$, and assume

$$
p_{m+1}(E)=p_m(E)\qquad(E\in K_{d,m}).
\tag{25.1}
$$

Then there exists a unique density matrix $H$, independent of $m$, such that

$$
\exists H\succeq0,\ \operatorname{Tr}H=1,\
\forall m\ge m_0,\ \forall E\in K_{d,m},\qquad
p_m(E)=\operatorname{Tr}(HE).
\tag{25.2}
$$

Conversely every density matrix defines such an exact compatible tower by the trace formula.

**证明。** The grids are nested. Every $Q\in\mathcal B$ lies in every one of them, and (25.1) makes its table value independent of scale. Thus all the matrices pinned by (16.1) are the same Hermitian matrix $H$. Equation (16.3) gives $\operatorname{Tr}H=1$. At scale $n$, Theorem 17.1 gives $\lambda_{\min}(H)\ge-D_d2^{-n}$. Letting $n$ tend to infinity proves $H\succeq0$.

Fix $m\ge m_0$ and $E\in K_{d,m}$, and take $k_d,q_d$ from (24.1). At every auxiliary scale $n\ge m+k_d$, all matrices $E/2^j$, $0\le j\le k_d$, belong to $K_{d,n}$: their entries have denominator dividing $2^{m+j}$, and they remain effects. The doubling menus

$$
(F,F,I-2F),\qquad(2F,I-2F)
$$

give $p_n(2F)=2p_n(F)$ whenever $F,2F\in K_{d,n}$. Iteration gives

$$
p_n(E)=q_dp_n(E/q_d).
$$

Because $\|E/q_d\|_{\rm op}\le1/q_d\le c_d/2$, Theorem 16.2 with $\epsilon=0$ gives $p_n(E/q_d)=\operatorname{Tr}(HE/q_d)$. Compatibility then implies

$$
p_m(E)=p_n(E)=\operatorname{Tr}(HE).
$$

Only the positivity step uses a limit of auxiliary scales; the linear identity is exact at every $n\ge m+k_d$. Uniqueness follows from the basis $\mathcal B$. For the converse, positivity and trace one put every trace value in $[0,1]$ and make every menu sum one, while the same formula on nested grids is compatible. $\square$

**定理 25.2（固定层数细化的逐尺度含噪稳定性）。** For each $d\ge2$, choose $k_d,q_d$ as in (24.1), and let $C_d^{\rm loc}$ be the constant of Corollary 17.2. Put

$$
C_d^{\rm ref}=1+2(q_d-1)+q_dC_d^{\rm loc}.
\tag{25.3}
$$

For every $m\ge1$, $0\le\epsilon\le1/10$ and $\Delta\ge0$, suppose a table $p_m:K_{d,m}\to[0,1]$ admits a table $p_{m+k_d}$ satisfying Definition 16.1 with parameter $\epsilon$ on the finer grid and

$$
|p_{m+k_d}(E)-p_m(E)|\le\Delta
\qquad(E\in K_{d,m}).
\tag{25.4}
$$

Then there is a density matrix $\rho_{(m)}$, allowed to depend on $m$ and on these tables, such that

$$
\sup_{E\in K_{d,m}}
|p_m(E)-\operatorname{Tr}(\rho_{(m)}E)|
\le C_d^{\rm ref}(\epsilon+\Delta+h).
\tag{25.5}
$$

In particular, for a family with such refinements the conclusion has quantifiers $\forall m\ \exists\rho_{(m)}\ \forall E\in K_{d,m}$; it does not assert a common density matrix for all $m$.

**证明。** Denote the finer table by $p_f$ and its spacing by $h_f=h/q_d$. For every $E\in K_{d,m}$, all $E/2^j$ for $0\le j\le k_d$ are fine-grid effects. Equation (16.4) gives

$$
|p_f(2F)-2p_f(F)|\le2\epsilon.
$$

Iteration, with geometric accumulation of the errors, yields

$$
|p_f(E)-q_dp_f(E/q_d)|\le2(q_d-1)\epsilon.
\tag{25.6}
$$

Apply Corollary 17.2 once to the finer table. It supplies a single density matrix $\rho_{(m)}$ working simultaneously for every finer effect of norm at most $c_d$, with error at most $C_d^{\rm loc}(\epsilon+h_f)$. Every $E/q_d$ under consideration lies in this ball. Combining this estimate, (25.4), and (25.6) gives the uniform bound

$$
\begin{aligned}
|p_m(E)-\operatorname{Tr}(\rho_{(m)}E)|
&\le\Delta+2(q_d-1)\epsilon
+q_dC_d^{\rm loc}(\epsilon+h/q_d)\\
&=\Delta+\bigl[2(q_d-1)+q_dC_d^{\rm loc}\bigr]\epsilon
+C_d^{\rm loc}h\\
&\le C_d^{\rm ref}(\epsilon+\Delta+h).
\end{aligned}
$$

The local corollary includes both large noise and coarse grids, so no omitted scale regime remains. The same $\rho_{(m)}$ was chosen before $E$, proving (25.5). $\square$

**命题 25.3（一致相邻尺度误差不强制共同密度矩阵）。** For every $d\ge2$, every $m_0\ge1$, and every real $\delta>0$, there exists an infinite family of exact Born tables $p_m(E)=\operatorname{Tr}(\rho_mE)$ on $K_{d,m}$, $m\ge m_0$, such that

$$
\sup_{E\in K_{d,m}}|p_{m+1}(E)-p_m(E)|\le\delta
\qquad(m\ge m_0),
\tag{25.7}
$$

but on every tail $m\ge M\ge m_0$,

$$
\inf_{\rho\succeq0,\ \operatorname{Tr}\rho=1}
\ \sup_{m\ge M}\ \sup_{E\in K_{d,m}}
|p_m(E)-\operatorname{Tr}(\rho E)|=\frac14.
\tag{25.8}
$$

**证明。** Let $J=\lceil1/(2\delta)\rceil\ge1$, and let $r_m$ be the residue of $m-m_0$ in $\{0,\ldots,2J-1\}$. Define

$$
a_m=-\frac14+\frac{\min(r_m,\,2J-r_m)}{2J},
\qquad
\rho_m=\operatorname{diag}\left(\frac12+a_m,\frac12-a_m,0,\ldots,0\right).
$$

This is a triangular periodic ramp from $-1/4$ to $1/4$ and back, with

$$
|a_{m+1}-a_m|=\frac1{2J}\le\delta.
$$

All $\rho_m$ are positive semidefinite and trace one. Their trace tables satisfy every menu exactly. For any common effect $E$, its diagonal entries lie in $[0,1]$, so

$$
|p_{m+1}(E)-p_m(E)|
=|a_{m+1}-a_m|\,|E_{11}-E_{22}|
\le\delta,
$$

including the step across each period boundary. The fixed basis effect $D_1$ has table value $1/4$ when $r_m=0$ and $3/4$ when $r_m=J$, and both occur at arbitrarily large scales. For any fixed density matrix $\rho$, writing $t=\operatorname{Tr}(\rho D_1)$ gives

$$
\sup_{m\ge M}|p_m(D_1)-t|
\ge\max\{|1/4-t|,|3/4-t|\}\ge1/4.
$$

This proves the lower bound in (25.8). The fixed density matrix $\operatorname{diag}(1/2,1/2,0,\ldots,0)$ attains the upper bound, since the error on every effect is $|a_m|\,|E_{11}-E_{22}|\le1/4$. Thus (25.8) is exact. $\square$

**适用边界 25.4。** Exact refinement compatibility in Theorem 25.1 is a relation between different tables, additional to the complete menus within any one grid. If the table of Theorem 23.1 belonged to an exact compatible tower, Theorem 25.1 and its basis values would force the common density matrix to be $H_0$, contradicting (23.1). Thus none of those single-grid tables is a member of an exact compatible tower. Theorem 25.2 instead requires only one bounded-depth refinement for each base scale and permits different approximating densities. Proposition 25.3 shows that a positive uniform adjacent-scale defect alone cannot replace exact compatibility in the common-density conclusion, even when each individual table is already exactly Born.

The linear representation for states on the full continuous effect interval has the classical antecedent of Busch's generalized Gleason theorem, cited in §6 and available as [Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem](https://arxiv.org/abs/quant-ph/9909073). That continuous-domain result is not assumed in the proofs above. The results here are repo-derived statements about the specified discrete grids: their order-atomic obstruction, one-sided parity-halving estimate, bounded-depth refinement estimate, and exact-compatible-tower consequence. No priority beyond these derivations, no pre-Hilbert reconstruction, and no empirical realization of the refinement hypotheses is asserted.

## 追加锚（本行以下为增补区）

## 26. 无预设内积的最小锐效应与三种范数

**定义 26.1（操作载体、帧与两条原则）。** Let $A$ be a nonzero finite-dimensional real vector space, $A_+$ a closed, pointed, generating convex cone, and $u\in A^\vee$ strictly positive on $A_+\setminus\{0\}$. The dual cone is $A_+^\vee=\{f:f(A_+)\ge0\}$, and inequalities between functionals use this cone. States form $\Omega=\{x\in A_+:u(x)=1\}$; pure states are its extreme points. All effects in $[0,u]\subset A^\vee$ are admitted, each defining a binary cut $(f,u-f)$. A nonempty ordered frame $(\omega_1,\ldots,\omega_r)$ consists of pure states and effects $f_i$ with $\sum_i f_i\le u$ and $f_i(\omega_j)=\delta_{ij}$. Its unused effect $u-\sum_i f_i$ is allowed.

Principle S says that each pure $\omega$ has a least saturating effect $e_\omega$: $e_\omega(\omega)=1$, and $e_\omega\le f$ whenever $f\in[0,u]$ and $f(\omega)=1$. It also requires reciprocity $e_\omega(\sigma)=e_\sigma(\omega)$ for all pure $\omega,\sigma$. Principle Sp says that every $x\in A$ has a signed frame decomposition $x=\sum_i\lambda_i\omega_i$, $\lambda_i\in\mathbb R$. Neither principle mentions an inner product. Define

$$
\|x\|_B=\inf_{x=a-b,\ a,b\in A_+}\bigl(u(a)+u(b)\bigr),\qquad
\|f\|_u=\inf\{t\ge0:-tu\le f\le tu\}.
\tag{26.1}
$$

**定理 26.2（最小锐效应的线性化与可量化范数分离）。** Under Definition 26.1 and S and Sp, every frame satisfies

$$
e_{\omega_i}(\omega_j)=\delta_{ij},\qquad \sum_i e_{\omega_i}\le u.
\tag{26.2}
$$

The assignment $\omega\mapsto e_\omega$ extends uniquely to a linear isomorphism $\Phi:A\to A^\vee$. The form $\beta(x,y)=\Phi(x)(y)$ is symmetric positive definite and

$$
A_+=\{x:\beta(x,y)\ge0\text{ for all }y\in A_+\}.
\tag{26.3}
$$

For every signed frame decomposition, including frames not maximal,

$$
\|x\|_B=\sum_i|\lambda_i|,\qquad
\|\Phi(x)\|_u=\max_i|\lambda_i|,\qquad
\|x\|_\beta=\sqrt{\beta(x,x)}=\left(\sum_i\lambda_i^2\right)^{1/2}.
\tag{26.4}
$$

These quantities are independent of the decomposition. If a two-element frame exists, the parallelogram sides $\|x+y\|^2+\|x-y\|^2$ and $2\|x\|^2+2\|y\|^2$, at $x=\omega_1,y=\omega_2$, are respectively $8,4$ for the base norm, $2,4$ for the pulled-back order-unit norm, and $4,4$ for the $\beta$ norm. The $\beta$ norm satisfies the parallelogram law for every pair of vectors.

**证明。** Since $0\le e_{\omega_i}\le f_i$, all off-diagonal evaluations vanish and (26.2) follows, with diagonal value one. Sp makes pure states span $A$. If $\sum_j c_j\omega_j=0$, reciprocity gives, for every pure $\sigma$,

$$
\left(\sum_j c_j e_{\omega_j}\right)(\sigma)
=e_\sigma\left(\sum_j c_j\omega_j\right)=0.
$$

A functional vanishing on the spanning pure states vanishes everywhere. Thus $\Phi(\sum_jc_j\omega_j)=\sum_jc_je_{\omega_j}$ is well defined and linear. Reciprocity makes $\beta$ symmetric. On any frame decomposition (26.2) gives $\beta(x,x)=\sum_i\lambda_i^2$, which is strictly positive for $x\ne0$. Hence $\Phi$ is injective and, by equal finite dimensions, surjective; its extension is unique.

For $x\in A_+$, (26.2) gives $\lambda_i=e_{\omega_i}(x)\ge0$ in any frame decomposition. Conversely nonnegative frame coefficients give an element of $A_+$. Thus if $x,y\ge0$, writing $x=\sum_i\lambda_i\omega_i$ shows $\beta(x,y)=\sum_i\lambda_i e_{\omega_i}(y)\ge0$. If $\beta(x,y)\ge0$ for all $y\ge0$, its values on the members of a frame for $x$ force every $\lambda_i\ge0$, proving (26.3).

The positive and negative coefficient sums give $\|x\|_B\le\sum_i|\lambda_i|$. Put $h=\sum_i\operatorname{sgn}(\lambda_i)e_{\omega_i}$, with $\operatorname{sgn}(0)=0$. Equation (26.2) gives $-u\le h\le u$, so every $x=a-b$ with $a,b\ge0$ satisfies $h(x)\le u(a)+u(b)$. Since $h(x)=\sum_i|\lambda_i|$, the reverse bound follows. Set $M=\max_i|\lambda_i|$. The same effect inequality gives $-Mu\le\Phi(x)\le Mu$, while evaluation on $\omega_i$ forces any permissible bound $t$ to satisfy $t\ge|\lambda_i|$. This proves (26.4), including $x=0$. Finally bilinearity gives $\beta(x+y,x+y)+\beta(x-y,x-y)=2\beta(x,x)+2\beta(y,y)$. Substituting the two-frame coefficients $(1,1)$ and $(1,-1)$ in (26.4) gives the three stated pairs of sides. $\square$

**适用边界 26.3。** The parallelogram law is derived for $\|\cdot\|_\beta$ only. It is not an operational axiom for either norm in (26.1). Theorem 26.2 packages state-effect self-duality with the explicit three-norm comparison; self-dualizing geometry has antecedents in Müller–Ududec, [Structure of reversible computation determines the self-duality of quantum theory](https://arxiv.org/abs/1110.3516), using bit symmetry, whereas the hypotheses here are S and signed Sp. No implication between those different premise sets is assumed.

## 27. 光滑球锥的互易缺陷与多面体最小效应障碍

**定理 27.1（球锥替代模型的精确分界）。** For $n\ge2$, let $C_p=\{(t,y)\in\mathbb R\oplus\mathbb R^n:t\ge\|y\|_p\}$ and $u(t,y)=t$. For $1<p<\infty$ put $q=p/(p-1)$. Every pure state is $\omega_x=(1,x)$ with $\|x\|_p=1$. Its complete saturating-effect set and its least member are

$$
\begin{aligned}
f_s(t,y)&=(1-s)t+s\langle x^\sharp,y\rangle,\quad 0\le s\le\tfrac12,
&x^\sharp_i&=\operatorname{sgn}(x_i)|x_i|^{p-1},\\
e_x(t,y)&=\tfrac12\bigl(t+\langle x^\sharp,y\rangle\bigr).
\end{aligned}
\tag{27.1}
$$

At $x=e_1$ and $y=2^{-1/p}(e_1+e_2)$, the reciprocity defect is

$$
\left|e_x(\omega_y)-e_y(\omega_x)\right|
=\frac12\left|2^{-1/p}-2^{1/p-1}\right|,
\tag{27.2}
$$

which vanishes exactly at $p=2$. Both endpoint cones $C_1,C_\infty$ have no least saturating effect at any vertex pure state. By contrast, for every integer $N\ge1$, the classical cone $\mathbb R_+^N$ with $u(x)=\sum_i x_i$ satisfies S and Sp. Thus within these alternatives the smooth ball cones meet S exactly at $p=2$, while classical simplices remain admitted.

**证明。** Strict convexity of the $p$ ball identifies all its boundary points as its extreme points. Hölder duality says that $f(t,y)=\alpha t+\langle g,y\rangle$ is an effect exactly when

$$
\|g\|_q\le\alpha,\qquad \|g\|_q\le1-\alpha.
$$

Saturation gives $1-\alpha=\langle g,x\rangle\le\|g\|_q\le1-\alpha$. Equality in Hölder for $1<p<\infty$ forces $g=sx^\sharp$, where $s=1-\alpha=\|g\|_q$, and the other inequality gives $0\le s\le1/2$. This also covers $g=0$. Conversely every effect in (27.1) saturates. Moreover

$$
f_s-e_x=(\tfrac12-s)\bigl(t-\langle x^\sharp,y\rangle\bigr)\ge0
\quad\text{on }C_p,
$$

so $e_x$ is the least member. The two evaluations in (27.2) are $(1+2^{-1/p})/2$ and $(1+2^{1/p-1})/2$. Equality of their nonconstant terms is equivalent to $-1/p=1/p-1$, hence to $p=2$. At $p=2$, (27.1) is reciprocal for every pair. In fact every $C_p$ with $1<p<\infty$ satisfies Sp: if $z\ne0$, put $v=z/\|z\|_p$ and write

$$
(t,z)=\frac{t+\|z\|_p}{2}(1,v)+\frac{t-\|z\|_p}{2}(1,-v).
$$

The two states are distinguished by $e_v,e_{-v}$, whose sum is $u$; for $z=0$ choose any unit $v$. Thus failure of reciprocity is isolated even among these signed-spectral models.

For $p=\infty$, take vertices $a=(1,1,1,1,\ldots,1)$, $b=(1,1,-1,1,\ldots,1)$, $c=(1,-1,1,1,\ldots,1)$, $d=(1,-1,-1,1,\ldots,1)$. The effects $h_1=(t+y_1)/2$ and $h_2=(t+y_2)/2$ saturate $a$. A least saturating effect $h$ would obey $0\le h\le h_1,h_2$, so $h(b)=h(c)=0$ and $h(a)=1$. But $a+d=b+c$ forces $h(d)=-1$, contradicting positivity. Their convex combinations give the saturating family $h_\theta=(t+\theta y_1+(1-\theta)y_2)/2$, $0\le\theta\le1$. Signed coordinate permutations carry this contradiction to every vertex. The square cross-section at $n=2$ is the local gbit cone, also the marginal cone for PR-box models.

For $p=1$, use $a=(1,e_1)$, $b=(1,e_2)$, $c=(1,-e_2)$, $d=(1,-e_1)$ and saturating effects $h_\pm=(t+y_1\pm y_2)/2$. They are effects because their spatial dual $\ell^\infty$ norms are $1/2$. A least $h$ again vanishes at $b,c$, has $h(a)=1$, and violates positivity at $d$ by the same relation $a+d=b+c$. Signed permutations cover every cross-polytope vertex. Finally, in the classical cone the pure states are coordinate vectors $v_i$, an effect is a coordinate vector in $[0,1]^N$, and the least effect saturating $v_i$ is the $i$th coordinate functional. These are reciprocal and form the coordinate frame; $x=\sum_i x_iv_i$ proves Sp. $\square$

## 28. Jordan 桥、相干面过滤与多线性干涉边界

**定义 28.1（强对称与完整 compression 合同）。** In Definition 26.1 a reversible map is a linear cone automorphism preserving $u$, with group topology inherited from $\operatorname{GL}(A)$. Strong symmetry means that a group of such maps acts transitively on ordered frames of every fixed size for which frames exist. For a positive idempotent linear map $T:A\to A$, write $\operatorname{im}_+T=\operatorname{im}T\cap A_+$ and $\ker_+T=\ker T\cap A_+$. It is complemented if some positive idempotent $R$ satisfies $\operatorname{im}_+T=\ker_+R$ and $\ker_+T=\operatorname{im}_+R$.

A coherent face filter is a positive idempotent $T$ such that $u(Tx)\le u(x)$ for $x\ge0$, both $T$ and its dual $T^\vee$ are complemented, its positive range is the specified face, and it is neutral: $u(Tx)=u(x)$ with $x\ge0$ implies $Tx=x$. This is the state-side version of an Alfsen–Shultz compression; neutrality follows from their full definition and is displayed here to specify the operational disturbance condition. The distinction between state-side filters and effect-side compressions, including both complement conditions, is given in Barnum–Müller–Ududec, [Higher-order interference and single-system postulates characterizing quantum theory](https://arxiv.org/abs/1403.4147), Definitions 13–14, using Alfsen–Shultz, Geometry of State Spaces of Operator Algebras (2003), Definition 7.22.

Operationally choose disjoint blocks $B_i$ of a frame, set $a_i=\sum_{j\in B_i}e_{\omega_j}$, and define $F_i=\{x\ge0:a_i(x)=u(x)\}$. For a slit set $S$, let $F_S$ be the smallest face containing all $F_i$, $i\in S$, with $F_\varnothing=\{0\}$. A coherent slit family uses the coherent face filter onto $F_S$ for each $S$. This is a restriction on the operations used in the slit experiment, not a claim about every positive instrument.

**定理 28.2（操作最小效应至二次 slit 响应的条件桥与反例判据）。** Suppose S, Sp and strong symmetry hold in Definition 26.1, and slit operations satisfy Definition 28.1. Then $A$ is order-isomorphic, preserving $u$, to a Euclidean Jordan algebra $J$ with its cone of squares and Jordan trace $\tau$; it is either simple or a classical algebra $\mathbb R^N$. In this representation $\beta(x,y)=\tau(x\circ y)$. For any orthogonal idempotents $p_1,\ldots,p_k$ in $J$, any state $\omega$, and any effect $e$, the coherent response is

$$
f(S)=e(Q(p_S)\omega),\quad p_S=\sum_{i\in S}p_i,\quad
Q(a)=2L_a^2-L_{a\circ a},\quad L_a b=a\circ b.
\tag{28.1}
$$

With $Q(a,b)=L_aL_b+L_bL_a-L_{a\circ b}$ and indicators $s_i=\mathbf1_{i\in S}$, its unique multilinear polynomial is

$$
f(S)=\sum_i e(Q(p_i)\omega)s_i
+2\sum_{i<j}e(Q(p_i,p_j)\omega)s_is_j.
\tag{28.2}
$$

Consequently, for disjoint sets $B,T$ with $|T|\ge3$,

$$
I_T(B)=\sum_{R\subseteq T}(-1)^{|T|-|R|}f(B\cup R)=0.
\tag{28.3}
$$

These identities hold in every Euclidean Jordan algebra, including the Albert algebra. Every simple such algebra of rank at least two has a state, effect and two slits with $I_{\{1,2\}}(\varnothing)=1/2$; the complex qubit realizes this value with $\omega=E=|+\rangle\langle+|$ and coordinate slits. Classical associative algebras have $I_{\{i,j\}}(B)=0$ identically. A response having any nonzero multilinear coefficient of degree at least three cannot be a coherent-compression response of such a system.

**证明。** First match the hypotheses of the attributed intermediate classification [Barnum–Hilgert, Strongly symmetric spectral convex bodies are Jordan algebra state spaces, Theorem 1.1](https://arxiv.org/abs/1904.03753). The base $\Omega$ is compact: an unbounded sequence, divided by an auxiliary coordinate norm, would have a subsequential nonzero limit in $A_+$ annihilated by $u$, contrary to strict positivity. No choice of that auxiliary norm enters the conclusions. The base spans the hyperplane $u=1$ since the cone generates $A$. For $x\in\Omega$, Theorem 26.2 makes its Sp coefficients nonnegative, with sum one. Thus $\Omega$ is spectral in their Definition 3.4. Their measurement convention uses effects summing to $u$; adding the unused effect to the first frame effect changes none of its evaluations on frame members. Their frames therefore coincide with ours. The assumed reversible subgroup is contained in the affine automorphism group of $\Omega$, so its transitivity gives precisely their strong symmetry, Definition 3.5. The classification applies and gives a simplex or the normalized state space of a simple Euclidean Jordan algebra, not an arbitrary nonsimple Jordan state space. Homogenizing its affine isomorphism gives the stated linear cone isomorphism with $u=\tau$. There is no missing hypothesis for this application of their classification.

For the remaining intermediate tools use finite-dimensional Jordan spectral and Peirce calculus, as in Faraut–Korányi, Analysis on Symmetric Cones (1994), and the Alfsen–Shultz compression identification: primitive idempotents are pure states, faces correspond to idempotents $p$, and their unique compressions under the trace pairing are $Q(p)$, with positive range $J_+\cap J_1(p)$, where $J_1(p)=\{x:p\circ x=x\}$. The trace pairing self-dualizes the cone of squares. These maps are self-adjoint for that pairing, positive, neutral and idempotent; $Q(1-p)$ is their complement, also on the dual. These are tools about all finite-dimensional Euclidean Jordan algebras, so both branches just obtained meet their hypotheses.

To check that the derived pairing agrees with this trace representation, let $c$ be primitive and $a\in[0,1]$ satisfy $\tau(a\circ c)=1$. Decompose $a=\sum_j\alpha_jq_j$ in a Jordan frame, $0\le\alpha_j\le1$. The nonnegative weights $\tau(q_j\circ c)$ sum to one; hence they vanish wherever $\alpha_j<1$. For $r=\sum_{\alpha_j=1}q_j$ this gives $\tau(r\circ c)=1$. Since $\tau(Q(r)c)=\tau(r\circ c)=1$, neutrality gives $Q(r)c=c$. Its range implies $r\circ c=c$, so $(r-c)^2=r-c$ is a square and $c\le r$. Since $a\ge r$, $a\ge c$. Therefore the least saturating effect is $x\mapsto\tau(c\circ x)$, and spanning pure states identify $\Phi$ and $\beta$ with the trace pairing.

In particular the operational faces in Definition 28.1 become the faces of the corresponding block idempotents. Their joins correspond to sums of orthogonal idempotents, so their filters are exactly (28.1). Conversely any finite orthogonal idempotent family can be refined into disjoint blocks of a Jordan frame, so this covers all families in the statement. The compression contract, including its selection as the available slit operation, is essential here; the state-space classification alone is not a specification of arbitrary instruments.

Bilinearity of the Jordan product gives $Q(a+b)=Q(a)+Q(b)+2Q(a,b)$ and $Q(a,a)=Q(a)$. Hence $Q(p_S)=\sum_{i,j}s_is_jQ(p_i,p_j)$, and $s_i^2=s_i$ proves (28.2). For each monomial in that expression and $|T|\ge3$, at least one variable indexed by $T$ is absent. Pairing subsets $R$ that differ just in that variable cancels their contributions, proving (28.3) also with background $B$. Uniqueness of multilinear expansion on the Boolean cube follows inductively by evaluating at $s_k=0,1$ and subtracting; its coefficient at $\prod_{i\in T}s_i$ is $I_T(\varnothing)$. This proves the stated obstruction, with no associativity assumption on $J$.

For the nonzero second-order witness, it suffices to find orthogonal primitive $p,q$ and $z$ with $z\circ z=p+q$, $p\circ z=q\circ z=z/2$ and $\tau(z)=0$. The attributed Jordan–von Neumann–Wigner classification supplies all simple types. In each matrix type over $\mathbb R,\mathbb C,\mathbb H$, and in the Albert algebra, take $p=E_{11}$, $q=E_{22}$, $z=E_{12}+E_{21}$ using real entries. Their real two-by-two Jordan multiplication proves the required identities, including in the Albert algebra. In a simple spin factor $\mathbb R\oplus\mathbb R^k$, $k\ge2$, the product is $(t,x)\circ(s,y)=(ts+x\cdot y,ty+sx)$ and $\tau(t,x)=2t$. Choose perpendicular unit vectors $v,w$ and take $p=(1,v)/2$, $q=(1,-v)/2$, $z=(0,w)$. Direct substitution proves the same identities.

In all cases $c=(p+q+z)/2$ satisfies $c^2=c$, $\tau(c)=1$, so is a state and an effect under the trace pairing. With $\omega=c$ and $e(x)=\tau(c\circ x)$,

$$
Q(p+q)c=c,\qquad Q(p)c=p/2,\qquad Q(q)c=q/2,
\qquad f(\{1,2\})=1,\quad f(\{1\})=f(\{2\})=1/4.
$$

Thus $I_2=1/2$. In the complex qubit $c=|+\rangle\langle+|$ is exactly this witness. For a classical algebra the Jordan product is coordinatewise, $Q(p)x=px$ for every idempotent, and disjoint supports give $Q(p_S)=\sum_{i\in S}Q(p_i)$. Every response is linear in the indicators and all second-order terms vanish. $\square$

**适用边界 28.3。** Sorkin's [Quantum mechanics as quantum measure theory](https://arxiv.org/abs/gr-qc/9401003) supplies the inclusion-exclusion hierarchy; Jordan absence of higher-order interference is also literature-attested, including the Barnum–Müller–Ududec framework cited above. Theorem 28.2 is a repackaging of those tools with the S-to-trace bridge, the uniform value $I_2=1/2$, and the explicit multilinear-coefficient obstruction. A displayed cubic power alone is not an obstruction, since $s_i^3=s_i$ on indicators; coefficients must first be reduced to the unique multilinear expansion. For example $f(S)=\prod_{i=1}^3s_i$ has $I_{\{1,2,3\}}(\varnothing)=1$ and violates (28.3).

## 29. 自复合的秩维缺口与复数域选择

**假设 29.1（非平凡系统的自复合）。** Let $A$ satisfy Definition 26.1, S, Sp and strong symmetry, with maximum frame size $n\ge2$. Its connected identity component of reversible transformations is transitive on pure states. Assume a self-composite $C$ exists with the same operational, S, Sp and strong-symmetry properties, and with a connected reversible group transitive on its pure states. Alternatively impose simplicity of $C$ explicitly. Require rank multiplicativity $\operatorname{rank}C=n^2$ and local tomography: there are bilinear product maps $A\times A\to C$ and $A^\vee\times A^\vee\to C^\vee$ taking products of states to states and products of effects to effects, with $(u\otimes u)=u_C$ and $(f\otimes g)(x\otimes y)=f(x)g(y)$; product states span $C$, and product effects separate its vectors. These conditions identify its vector space with $A\otimes_{\mathbb R}A$, hence $\dim C=(\dim A)^2$; this dimension equality is the only composite property used in the type exclusion below.

**定理 29.2（带精确缺口和隐藏核见证的自复合选型）。** Under Hypothesis 29.1, $A$ is order-isomorphic with trace normalization to $\operatorname{Herm}_n(\mathbb C)$ and $C$ to $\operatorname{Herm}_{n^2}(\mathbb C)$. For

$$
N_d(r)=r+\frac d2r(r-1)
$$

for all real $a,b,d$ the polynomial identity is

$$
N_d(a)N_d(b)-N_d(ab)
=\frac{d(d-2)}4ab(a-1)(b-1).
\tag{29.1}
$$

A real rank-$n$ system has self-composite dimension below the smallest simple rank-$n^2$ dimension by $n^2(n-1)^2/4$; a quaternionic one has dimension above the largest by $2n^2(n-1)^2$. A spin factor of dimension $k+1$ can pass the constraints only for $k=3$. The Albert algebra fails by $729\notin\{45,81,153\}$. Classical nontrivial simplices fail the connected pure-state-transitivity hypothesis and have identically zero $I_2$.

**证明。** The bilinear product map induces a surjection $A\otimes_{\mathbb R}A\to C$ because product states span. Effects span $A^\vee$: boundedness on the compact base puts every functional in the linear span of $[0,u]$. The product pairing therefore makes that surjection injective, since factor-effect tensors span the tensor dual. This proves the dimension equality used below. Apply the classification inside Theorem 28.2 to $A$ and $C$. A connected group acting on the finite extreme-point set of a nontrivial simplex fixes each point, so cannot be transitive. More generally in a Jordan direct sum, cone automorphisms permute the finitely many simple summands; a connected group fixes each summand and cannot move pure states between them. Thus connected pure-state transitivity forces simplicity for either system; the alternative explicit simplicity assumption for $C$ suffices for that step. This also explains why full, possibly disconnected, strong symmetry alone cannot remove the classical branch.

Use the Jordan–von Neumann–Wigner classification only as an intermediate type list, with dimensions as tabulated in Barnum–Hilgert §4.2. The simple types are $\operatorname{Herm}_r(\mathbb R)$, $\operatorname{Herm}_r(\mathbb C)$, $\operatorname{Herm}_r(\mathbb H)$, with dimensions $N_1(r),N_2(r),N_4(r)$; rank-two spin factors $\mathbb R\oplus\mathbb R^k$, $k\ge2$, of dimension $k+1$; and the rank-three Albert algebra of dimension $27$. Rank-two matrix types also occur in the spin-factor list and cause no additional cases. Since $n^2\ge4$, the only possible simple types for $C$ are the three matrix types of rank $n^2$.

For (29.1), factor out $ab$ and put $h=d/2$. The remaining difference is

$$
[1+h(a-1)][1+h(b-1)]-[1+h(ab-1)]
=h(h-1)(a-1)(b-1).
$$

Since $N_1(r)<N_2(r)<N_4(r)$ for $r>1$, substituting $a=b=n$ gives

$$
N_1(n^2)-N_1(n)^2=\frac{n^2(n-1)^2}{4}>0,
\qquad
N_4(n)^2-N_4(n^2)=2n^2(n-1)^2>0.
\tag{29.2}
$$

Thus a real local system supplies fewer coordinates than any simple rank-$n^2$ candidate, and a quaternionic one supplies more than any candidate. This excludes even choosing a different composite matrix field. For a spin factor $n=2$, the rank-four dimensions are $\{N_1(4),N_2(4),N_4(4)\}=\{10,16,28\}$. Local tomography requires $(k+1)^2$ to be one of these; only $16$ is an integer square, so $k=3$ and the local algebra is $\operatorname{Herm}_2(\mathbb C)$. For the Albert algebra $n=3$ and $\dim C=27^2=729$, while rank nine permits only $\{N_1(9),N_2(9),N_4(9)\}=\{45,81,153\}$. Finally for a complex local system, $N_2(n)^2=n^4=N_2(n^2)$, and strict inequalities exclude the other two composite fields. Standard complex tensor products realize the required ranks, dimensions and product pairing, so this surviving case is inhabited.

The real alternative also has an explicit operational obstruction in its standard tensor composite. Put

$$
A_0=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
B=A_0\otimes A_0,\qquad
\rho_\pm=\frac{I_4\pm B}{4},\qquad P=\frac{I_4+B}{2}.
\tag{29.3}
$$

Here $B^{\mathsf T}=B$, $B^2=I_4$ and $\operatorname{tr}B=0$. Thus its eigenvalues $1,-1$ each have multiplicity two, $\rho_\pm$ are real density matrices, and $P$ is an effect. For every real symmetric pair $E,F$, skew symmetry gives $\operatorname{tr}(A_0E)=\operatorname{tr}(A_0F)=0$, so

$$
\operatorname{tr}(\rho_\pm(E\otimes F))
=\frac{\operatorname{tr}E\operatorname{tr}F}{4},\qquad
\operatorname{tr}(P\rho_+)=1,\quad\operatorname{tr}(P\rho_-)=0.
\tag{29.4}
$$

All local product-effect statistics agree although one global effect distinguishes perfectly. Embedding this two-by-two face and extending both states by zero gives the same witness for every real local rank $n\ge2$. It concretely identifies a hidden antisymmetric tensor coordinate. This standard real-composite phenomenon is consistent with the dimension exclusion, which also covers nonstandard simple composite candidates. For classical systems $Q(p)$ is coordinatewise masking, so Theorem 28.2 proves their asserted $I_2=0$. $\square$

**适用边界 29.3。** Local-tomographic selection of complex Jordan systems has antecedents in Barnum–Wilce, [Local tomography and the Jordan structure of quantum theory](https://arxiv.org/abs/1202.4513), and real-theory tomography defects in Hardy–Wootters, [Limited Holism and Real-Vector-Space Quantum Theory](https://arxiv.org/abs/1005.4870). These are attributed context for the intermediate framework, not additional unproved premises. The repo-derived quantitative content here is the cross-field rank-square comparison (29.2), together with the explicit spin, Albert and hidden-kernel accounting in the stated self-composite signature. Simplicity or its connected-transitivity justification, rank multiplicativity and local tomography are all explicit hypotheses; none is inferred from S and Sp. This theorem concerns state-effect geometry and an inhabited type choice, not a uniqueness classification of all possible product embeddings.

## 30. 产品统计确定的复合相干性与维数条件的边界

**命题 30.1（条件相干性与一个保正但不相干的比较族）。** Suppose iterated composites for a fixed labelled list of factors exist, each is locally tomographic, and each iterated product effect is labelled by the same list of factor effects. Assume the proposed linear isomorphisms between bracketings preserve every such labelled product statistic. Then each comparison is unique, and all paths of comparisons with the same endpoints agree, including the pentagon. Dimension equalities alone do not give this conclusion, even when every chosen comparison is a positive normalization-preserving reversible map.

**证明。** Iterated local tomography makes the labelled product effects span the dual at every bracketing: induction applies the separating product-effect condition at each binary node. If $U,V$ are two comparisons preserving those statistics, every labelled product effect annihilates $(U-V)x$ for every $x$, hence $U=V$. Any two paths have the same preservation property and endpoints; the same argument makes them equal. In particular both routes around the four-factor pentagon agree. Existence of the comparisons and consistent product-statistic labels are used here; pairwise dimension counts do not supply them.

For explicit comparison data showing this distinction, take ordinary complex qubits $A$ and all their usual tensor powers. Identify all bracketings canonically as vector spaces. Let $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. For the triple $(A,A,A)$ alone choose the comparison $\alpha_{A,A,A}=\operatorname{Ad}_{X\otimes I_2\otimes I_2}$ after canonical reassociation, where $\operatorname{Ad}_U(\rho)=U\rho U^\dagger$. For every other ordered triple of tensor powers choose canonical reassociation. Every chosen map is a positive trace-preserving order isomorphism, and all dimensions multiply correctly. In the pentagon from $((AA)A)A$ to $A(A(AA))$, the two-edge route uses $\alpha_{A\otimes A,A,A}$ and $\alpha_{A,A,A\otimes A}$ and is the identity. The three-edge route uses $\alpha_{A,A,A}\otimes\mathrm{id}_A$, then $\alpha_{A,A\otimes A,A}$, then $\mathrm{id}_A\otimes\alpha_{A,A,A}$. It acts by conjugation with $X\otimes X\otimes I_2\otimes I_2$. On the product state $|0000\rangle\langle0000|$ the two routes give respectively $|0000\rangle\langle0000|$ and $|1100\rangle\langle1100|$. A first-factor coordinate effect separates them, so the pentagon fails. These comparison data violate product-statistic preservation, exactly the extra condition used in the first part. $\square$

**适用边界 30.2。** Sections 1–15 start from an inner product. Sections 26–30 instead derive the quadratic form from the ordered operational principles S and Sp and select the complex matrix type after adding the explicit symmetry and self-composite hypotheses. Once that geometry is available, the window-atlas and gluing questions in §§2–5 apply with their own stated hypotheses; no atlas statement is restated or used to assume the quadratic form.

The repo-derived statements are the least-effect linearization with the simultaneous norm separations, the exact $\ell^p$ reciprocity defect and endpoint relation obstructions, the compression-response polynomial with its coefficient boundary and uniform second-order witness, the quantitative self-composite exclusions, and the distinction between statistical coherence and dimension equality. Self-duality, the Jordan classification, Jordan compression calculus, and absence of higher-order Jordan interference have the attributed antecedents specified inside those arguments. These statements are conditional mathematical derivations and quantitative repackagings, not claims of literature priority. All conclusions depend on the displayed principles and operation classes. No empirical claim is made, and no derivation of arbitrary state-update rules, general dynamics, or the physical validity of those principles is asserted.

## 追加锚（本行以下为增补区）

## 31. 原复 Gaussian dyadic 网格中低于八维的互补原子投影尾部排除

**定理 31.1（复维数二至七的互补端点区间在充分细网格上不存在）。** 沿用定义 16.1 的完整复效果网格，记

$$
K_{d,m}=\{E\in\operatorname{Herm}_d(2^{-m}\mathbb Z[i]):0\le E\le I_d\}.
$$

对每个固定的 $d\in\{2,3,4,5,6,7\}$ 以及每个整数 $m\ge22$，不存在非平凡厄米投影 $P\in K_{d,m}$（即 $P^2=P$ 且 $P\ne0,I_d$），使两个原网格区间同时只有端点：

$$
\{F\in K_{d,m}:0\le F\le P\}=\{0,P\},\qquad
\{F\in K_{d,m}:0\le F\le I_d-P\}=\{0,I_d-P\}.
\tag{31.1}
$$

这里的序关系始终是通常的复厄米半正定序，子效果遍历原 $2^{-m}\mathbb Z[i]$ 网格上的全部复厄米效果。因此，在这些固定维数中，“对任意整数 $L\ge1$，总能在某个 $m\ge L$ 找到满足 (31.1) 的投影”的事件为假，统一取 $L=22$ 即可排除。数字 $22$ 只是充分截断，不声称最优，也不分类较粗的网格。

**证明。** 置 $R=\mathbb Z[i]$、$\pi=1+i$、$N=2^m$。本证明中的局部记号 $H$ 和 $K$ 专指正定积分厄米 Gram 矩阵；$H$ 不是式 (16.1) 的层析矩阵，$K$ 也不是定义 16.1 的效果集。对秩 $r\ge1$ 的此类矩阵 $H$，在本证明内称它为原子，恰指

$$
\{Y\in\operatorname{Herm}_r(R):0\le Y\le H\}=\{0,H\}.
\tag{31.2}
$$

这只是所需的积分区间性质，不附加其他原子性约定。反设存在 (31.1) 中的投影。

（一）先把原网格区间转成积分正定区间。令 $A=NP$、$B=N(I_d-P)$，其秩分别为 $r$ 和 $s=d-r$，均非零。$A$ 在 $R^d$ 中的核是饱和子模：若 $a\ne0$ 且 $A(az)=0$，则 $Az=0$。Gaussian 整数环是主理想整环，故这个核是直和因子。取 Gaussian 幺模矩阵 $C$，使其最后 $s$ 列构成该核的一组基。于是

$$
C^*AC=\begin{pmatrix}H&0\\0&0\end{pmatrix},\qquad H\succ0,\quad H\in\operatorname{Herm}_r(R).
$$

令 $T$ 为 $C^{-1}$ 的前 $r$ 行，$J$ 为 $C$ 的前 $r$ 列，则

$$
TJ=I_r,\qquad A=T^*HT,\qquad H=J^*AJ.
\tag{31.3}
$$

若 $0\le X\le A$，则 $X$ 在 $\ker A$ 上为零：对该核中的 $z$，有 $0\le z^*Xz\le z^*Az=0$，正性遂给出 $Xz=0$。所以在 $C$ 坐标中，$X$ 也只有左上块可能非零。由此

$$
Y\longmapsto T^*YT,\qquad X\longmapsto J^*XJ
$$

互为积分厄米区间 $[0,H]$ 与 $[0,A]$ 的逆双射。另一方面，$F\mapsto NF$ 把原复网格中的 $[0,P]$ 双射到积分区间 $[0,A]$；反向所得 $F$ 自动满足 $F\le P\le I_d$，确属原效果网格。因此 $P$ 的端点性质恰等价于 $H$ 的原子性。对 $B$ 作同样构造，得到秩 $s$ 的正定积分厄米原子 $K$。

由 $A^2=NA$，代入 (31.3) 并在两侧分别乘 $J^*$ 和 $J$，得到 $H(TT^*)H=NH$，故

$$
TT^*=NH^{-1}.
\tag{31.4}
$$

右侧因左侧而积分。$\det H$ 是正整数，且 $N^r/\det H=\det(TT^*)$ 也是整数，所以 $\det H\mid N^r$，从而 $\det H$ 是二的幂。同理 $\det K$ 是二的幂。

（二）原子性给出只依赖秩的行列式上界。设 $r\ge2$，$\delta=\det H$。对 Hermitian 格 $(R^r,H)$ 使用实内积 $\operatorname{Re}(z^*Hw)$。原格的实 Gram 行列式为 $\delta^2$，欧氏余体积为 $\delta$；其 Hermitian 对偶格 $H^{-1}R^r$ 的实维数为 $2r$，欧氏余体积为 $1/\delta$。

若 $\delta>(2r)^r$，可选

$$
\delta^{-1/(2r)}<t<\frac1{\sqrt{2r}}.
$$

在该实欧氏空间的正交坐标中，取边长为 $t$ 的开立方体。其体积 $t^{2r}$ 大于对偶格的余体积。经典基本平行多面体鸽巢论证给出立方体内两个不同的点，其差是非零对偶格向量：把立方体的各格平移片移入一个基本平行多面体，对重数积分；若没有这样的两点，重数处处至多一，立方体体积就不能大于该基本域体积。所得差向量 $x$ 满足

$$
0<\|x\|_H^2<2rt^2<1.
$$

写 $x=H^{-1}q$，其中 $0\ne q\in R^r$，便有 $q^*H^{-1}q<1$。$H$ 内积的 Cauchy 不等式给出，对任意 $z\in\mathbb C^r$，

$$
z^*qq^*z=|q^*z|^2
\le(q^*H^{-1}q)(z^*Hz)\le z^*Hz.
$$

因此 $0<qq^*\le H$，而 $qq^*$ 是秩一积分厄米矩阵，在 $r\ge2$ 时不是 $H$，与原子性矛盾。故 $\det H\le(2r)^r$。秩一时，正积分标量的区间只有端点当且仅当该标量为 $1$；任何大于 $1$ 的标量都含真子标量 $1$。于是秩 $1\le r\le6$ 的原子统一满足

$$
1\le\det H\le12^6=2\,985\,984.
\tag{31.5}
$$

（三）互补性把两边的行列式关联起来。记

$$
L_P=\operatorname{ran}(P)\cap R^d,\qquad
L_Q=\operatorname{ran}(I_d-P)\cap R^d,
$$

其在环境标准 Hermitian 内积下的 Gram 行列式分别为 $\Delta_P,\Delta_Q$。$T^*$ 的列构成 $L_P$ 的一组基：它们张成 $\operatorname{ran}(P)$，而积分左逆 $J^*T^*=I_r$ 保证该复线性空间中的任意积分向量均有 Gaussian 整数坐标。因此 (31.4) 给出

$$
\Delta_P=\det(TT^*)=\frac{N^r}{\det H},\qquad
\Delta_Q=\frac{N^s}{\det K}.
\tag{31.6}
$$

为说明 $\Delta_P=\Delta_Q$，取 $L_P$ 的基矩阵 $U$，利用其本原性将它扩充成 $R^d$ 的 Gaussian 幺模基 $[U,V]$，并令 $Q=I_d-P$。$QV$ 的列构成 $QR^d$ 的基，且

$$
QR^d=L_Q^\#,
$$

其中右侧是在 $\operatorname{ran}(Q)$ 内、按标准 Hermitian 配对取的对偶格。包含关系 $QR^d\subseteq L_Q^\#$ 来自环境格的整数配对。反向地，$L_Q$ 也是饱和子模，因而是直和因子；其任一取值于 $R$ 的 Hermitian 配对泛函可延拓到 $R^d$。环境格的自对偶性将延拓泛函表示为某个 $R^d$ 中向量的配对，再作 $Q$ 投影即可表示原泛函。这证明反向包含。

幺模基 $[U,V]$ 的 Gram 行列式为 $1$。沿 $U$ 块作经典 Schur 补，余块恰为 $QV$ 的 Gram 矩阵，其行列式为对偶格行列式 $1/\Delta_Q$。因此 $1=\Delta_P/\Delta_Q$。结合 (31.6)，得

$$
\frac{\det H}{\det K}=N^{r-s}.
\tag{31.7}
$$

这里 $1\le r,s\le6$。若 $r\ne s$，两行列式中较大者至少为 $N$，因为较小者是至少为 $1$ 的正整数，而比值的绝对幂次至少为一。但 $m\ge22$ 给出 $N\ge2^{22}>12^6$，与 (31.5) 矛盾。所以只能 $r=s$，即 $d\in\{2,4,6\}$，且 $r=s\le3$。

（四）对二幂行列式建立积分幺模上格。设积分正定 Hermitian $R$-格 $L$ 的 Gram 矩阵为 $H$，其 Hermitian 配对记为 $h$，且 $\det H=2^k$，$k>0$。模 $\pi$ 约化后，$H$ 在 $R/(\pi)=\mathbb F_2$ 上奇异。选取 $y\in R^r$，使其非零剩余类 $\bar y$ 位于该约化矩阵的根基，即 $(H\bmod\pi)\bar y=0$，并在环境 Hermitian 空间置 $x=y/\pi$。

$Hy$ 的各坐标被 $\pi$ 整除，而 $\bar\pi=1-i$ 与 $\pi$ 相伴，所以 $x$ 与 $L$ 的配对均为 Gaussian 整数。再看范数的奇偶性。$h(y,y)$ 的每对非对角项之和是两倍整数；对任一 Gaussian 整数 $z$，$|z|^2\bmod2$ 等于其模 $\pi$ 剩余类。因此

$$
h(y,y)\bmod2
=\sum_j(H_{jj}\bmod2)\bar y_j
=\bar y^{\mathsf T}(H\bmod\pi)\bar y=0.
$$

第二个等号使用模 $\pi$ 后共轭为恒等、特征二中交叉项抵消及 $\bar y_j^2=\bar y_j$。于是 $h(x,x)=h(y,y)/2$ 是整数，$L'=L+Rx$ 是积分格。$\bar y\ne0$ 保证 $x\notin L$，而 $\pi x=y\in L$，所以 $L'/L$ 有恰好两个元素。实余体积因此减半；Hermitian Gram 行列式等于该实余体积，故

$$
\det L'=\frac{\det L}{2}.
$$

重复此过程，得到同秩的积分幺模 Gaussian 上格 $M\supseteq L$。若原行列式已经是 $1$，直接取 $M=L$。这一构造不使用非幺模形式的分类。

（五）秩至多三时，这个上格是标准 Gaussian 格。此处只复用经典普通实 Hermite 常数

$$
\gamma_2=\frac2{\sqrt3},\qquad
\gamma_4=\sqrt2,\qquad
\gamma_6=\frac2{3^{1/6}},
\qquad \gamma_2,\gamma_4,\gamma_6<2.
\tag{31.8}
$$

这些数值见 Stephanie Vance，[A Mordell Inequality for Lattices over Maximal Orders，arXiv:0810.2336v5，§4.2、表 3](https://arxiv.org/html/0810.2336v5)。表中列出 $A_2,D_4,E_6$ 的 Hermite 不变量，紧邻正文明确说明这些维数的所列格在普通实格中最优；所以这里用的是全部普通实格的界，不是仅限 Eisenstein 格或 Gaussian 格的界。按归一化，实维数 $n$、欧氏余体积 $v$ 的格具有非零向量，平方范数至多为 $\gamma_n v^{2/n}$。

Gaussian 积分幺模格 $M$ 的实化具有积分实 Gram 矩阵，其行列式为 $|\det H_M|^2=1$，欧氏余体积为 $1$。应用 (31.8) 于实维数 $2\operatorname{rank}_R M\in\{2,4,6\}$，得到平方范数小于 $2$ 的非零向量。整数正性迫使其平方范数为 $1$。若此向量为 $e$，则对每个 $z\in M$，$z-e\,h(e,z)$ 属于 $M$ 且与 $e$ 正交；因而正交分裂出标准 Gaussian 直和因子 $Re$。正交补仍是积分幺模格。逐秩重复，得到 $M$ 等距于标准格 $R^r$。

在这个标准基下，原格 $L$ 的基向量组成一个满秩方阵 $D\in M_r(R)$，其 Gram 矩阵为

$$
H=D^*D=\sum_{j=1}^r d_j^*d_j,
$$

其中 $d_j$ 是 $D$ 的第 $j$ 行。满秩性保证各行非零；当 $r\ge2$ 时，每个 $d_j^*d_j$ 都是非零秩一积分厄米子形式，满足 $0<d_j^*d_j\le H$ 且不等于秩为 $r$ 的 $H$。所以秩二或三、行列式为二幂的正定积分 Hermitian 格不可能是原子。这排除了（三）中的 $d=4,6$。

（六）剩余的平衡秩一情形给出奇偶矛盾。此时 $d=2$，且原子性迫使 $H=[1]$，故由 (31.3) 有

$$
A=vv^*,\qquad v=T^*=(a,b)^{\mathsf T}\in R^2,
\qquad |a|^2+|b|^2=N.
$$

最后一个等式由 $A^2=NA$ 及 $v\ne0$ 得到。$TJ=1$ 的共轭式 $J^*v=1$ 表明 $v$ 本原，即 $a,b$ 没有共同的 Gaussian 非单位因子。把 $a,b$ 写成四个实整数坐标，其平方和为 $N$。当 $4\mid N$ 时，模四计算表明奇数坐标的个数只能为零或四。在两种情形中，每个 Gaussian 坐标的实部和虚部都有相同奇偶性，故 $a,b$ 都被 $1+i$ 整除，与本原性矛盾。这里 $m\ge22$ 当然保证 $4\mid N$。

至此，每个 $d\in\{2,\ldots,7\}$ 的所有非平凡秩以及每个 $m\ge22$ 都已覆盖。全过程的积分子形式与序比较均允许复厄米矩阵，没有把子效果限制为实矩阵。定理得证。$\square$

**数学来源与适用边界。** Gaussian 主理想整环上的饱和子模分裂、基本域鸽巢论证、格对偶、Schur 补和 Cauchy 不等式都是上述新网格推论中的经典中间工具；普通实 Hermite 常数仅按 (31.8) 的明确来源和归一化复用，不将这些工具另作新增结果。这里的承重结论是原复 dyadic 网格上 $d=2,\ldots,7$ 的互补端点投影对在充分细尺度中的统一排除，不作全局优先权或穷尽文献检索主张。

结合定理 22.1 在 $d=8$、每个 $m\ge2$ 的构造，维数八恰是任意细原 dyadic 网格上存在这种非平凡互补端点投影对的最小复维数。这个阈值只针对该投影对机制。命题 19.1 要求的只是非零子效果范数为一，其区间仍可含多个非零元素；本节的排除不否定那个较弱的小块分解障碍。充分界限 $22$ 不给出最优截断或粗网格分类。原问题 (18.1) 在 $2\le d\le7$ 的全表格稳定性仍未解决；本节不推出低维 Born 稳定性，不排除其他全表格障碍，也不对物理实现作经验性断言。

## 追加锚（本行以下为增补区）

## 32. 非投影互补原子给出的四维全表反例与二维全表稳定性

沿用定义 16.1 的原复 Gaussian dyadic 网格、全部带标签二元和三元菜单及式 (16.1) 的唯一层析矩阵。以下两个维数分支都只涉及同一尺度上的一张完整表；不同尺度之间没有相容性假设。

**定理 32.1（四维非投影互补原子与主块拉回反例）。** 对每个整数 $d\ge4$ 和 $m\ge2$，存在一张完整表 $p_{d,m}:K_{d,m}\to[0,1]$，使定义 16.1 的全部菜单关系在 $\epsilon=0$ 时精确成立，其层析矩阵为

$$
H_d=(I_4/4)\oplus0_{d-4},
\qquad
\max_{X\in K_{d,m}}|p_{d,m}(X)-\operatorname{Tr}(H_dX)|=\frac14.
\tag{32.1}
$$

最大误差在一个形如 $E_m\oplus0_{d-4}$ 的效果处取得，其中 $E_m$ 与 $I_4-E_m$ 都是满秩非投影，且它们各自的原四维网格区间只有两个端点。因此，定义 18.1 的估计在每个固定的 $d\ge4$ 都不存在有限常数 $L_d$；特别地，同时要求 $d=2,\ldots,7$ 全部成立的断言为假。

**证明。** 记 $R=\mathbb Z[i]$、$N=2^m$、$M=N/2$。此时 $M$ 为偶整数且 $M\ge2$。Lagrange 四平方定理给出 $a,b\in R$，使

$$
|a|^2+|b|^2=M^2-1=:t.
$$

这里仅复用经典四平方存在性；例如 [Mathlib 的固定版本源码，`Nat.sum_four_squares`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/SumFourSquares.lean) 明确给出每个非负整数的四平方表示。把四个整数按实部、虚部分成两对即得所需 $a,b$。

置

$$
Q=\begin{pmatrix}a&b\\-\overline b&\overline a\end{pmatrix},
\qquad
A=\begin{pmatrix}MI_2&Q\\Q^*&MI_2\end{pmatrix},
\qquad
B=\begin{pmatrix}MI_2&-Q\\-Q^*&MI_2\end{pmatrix}.
\tag{32.2}
$$

直接相乘得到

$$
Q^*Q=QQ^*=tI_2,\qquad
A+B=NI_4,\qquad AB=BA=I_4.
\tag{32.3}
$$

矩阵 $A-MI_4$ 的平方为 $tI_4$、迹为零，故 $A$ 的两个特征值为 $M\pm\sqrt{M^2-1}$，各重数二；$B$ 有相同的谱。两特征值都严格介于 $0$ 与 $N$ 之间，且

$$
\det A=\det B=(M^2-t)^2=1.
\tag{32.4}
$$

此外，$A,B$ 的对角元均为偶整数。对任意 $z\in R^4$，对角项给出偶整数，非对角项成对给出两倍整数实部，所以 $z^*Az$ 与 $z^*Bz$ 均为偶整数。

现在验证全部复积分子形式的区间性质。所用机制是 §§20、22 的积分收缩与正交分裂机制；这里用 Gaussian 奇偶性排除分裂，不要求固定根基的连通图。设 $G\in\operatorname{Herm}_4(R)$ 正定、$\det G=1$，且每个 $z^*Gz$ 都为偶整数。若 $X\in\operatorname{Herm}_4(R)$ 满足 $0\le X\le G$，则 $C=G^{-1}X$ 为 Gaussian 整数矩阵，并满足

$$
C^*G=GC=X,\qquad
G^{1/2}CG^{-1/2}=G^{-1/2}XG^{-1/2}.
\tag{32.5}
$$

右侧为谱在 $[0,1]$ 内的厄米矩阵。因此 $C$ 可对角化且所有特征值都在 $[0,1]$。其特征多项式的系数属于 $R$，又因根全实而属于 $\mathbb R$，所以实际上属于 $\mathbb Z$。若某个特征值 $\alpha$ 严格介于零与一之间，它在 $\mathbb Q$ 上的首一不可约多项式属于 $\mathbb Z[x]$ 并整除该特征多项式。其全部共轭根都在 $[0,1]$，而不可约性排除端点零和一。因此这些共轭根的乘积是绝对值严格介于零与一之间的非零整数，矛盾。故 $C^2=C$。

于是 $R^4=\operatorname{im}C\oplus\ker C$，且两项关于 $G$ 正交。Gaussian 整数环为主理想整环，故两项都有自由基，其合并为 $R^4$ 的幺模基。在该基中，两个限制 Gram 矩阵均正定、积分且偶；两者的正整数行列式之积为一，所以各为一。若分裂非平凡，较小的一个非零直和因子的 Gaussian 秩为一或二。秩一的偶 Gram 矩阵不可能有行列式一。秩二时写成

$$
\begin{pmatrix}2u&x+iy\\x-iy&2v\end{pmatrix},
\qquad u,v,x,y\in\mathbb Z.
$$

行列式一要求 $x^2+y^2=4uv-1\equiv3\pmod4$，与整数平方模四只能为零或一矛盾。因此分裂只能平凡，$C=0$ 或 $I_4$，从而 $X=0$ 或 $G$。

将此结论分别应用于 $A,B$。令

$$
E_m=A/N,\qquad F_m=B/N.
$$

它们属于原 $K_{4,m}$，互补、满秩且互异，因为 $t>0$ 保证 $Q\ne0$。乘以 $N$ 给出原网格区间与积分区间的双射，因而

$$
\{X\in K_{4,m}:0\le X\le E_m\}=\{0,E_m\},
\qquad
\{X\in K_{4,m}:0\le X\le F_m\}=\{0,F_m\}.
\tag{32.6}
$$

又有 $E_mF_m=N^{-2}I_4\succ0$，所以它们不是投影。两者的迹均为二。

在整个 $K_{4,m}$ 上定义一张表

$$
p_{4,m}(X)=
\begin{cases}
3/4,&X=E_m,\\
1/4,&X=F_m,\\
\operatorname{Tr}(X)/4,&X\notin\{E_m,F_m\}.
\end{cases}
\tag{32.7}
$$

这些值都在 $[0,1]$。取任一原带标签二元或三元菜单 $X_1+\cdots+X_r=I_4$。若其中有 $E_m$，则每个其他项均在 $[0,F_m]$ 内，故由 (32.6) 只能为零或 $F_m$。它们的和是非零的 $F_m$，所以恰有一项为 $F_m$，其余均为零。菜单值之和为 $3/4+1/4=1$。含 $F_m$ 的情形完全相同。若两者都不出现，则所有项采用迹值，菜单和为 $\operatorname{Tr}(I_4)/4=1$。这一论证覆盖全部允许的零项、重复项和标签，没有删去任何菜单。

定义 16.1 的每个层析基元素 $D_i,R_{ij},J_{ij}$ 都为秩一，而两个特殊效果都为秩四。故该基上全部表值为 $1/4$，唯一的原层析矩阵恰为 $H_4=I_4/4$。表值在两个特殊效果处与迹值相差 $1/4$，其余处相等，证明四维的 (32.1)。

对任意 $d>4$，令 $C_d(X)$ 为 $X$ 的前四阶主块，并定义

$$
p_{d,m}(X)=p_{4,m}(C_d(X)),\qquad X\in K_{d,m}.
\tag{32.8}
$$

主块映射把原 $K_{d,m}$ 映入原 $K_{4,m}$，保加法、半正定序并把 $I_d$ 映为 $I_4$。故每个原二元或三元菜单都被映成已验证的四维菜单，(32.8) 精确满足全部归一化关系。在原层析基上，$C_d$ 的像分别是四维层析基元素、零，或者跨越主块内外的 $R_{ij},J_{ij}$ 所给出的 $D_i/2$。这些像均秩至多一，因而都采用迹值。这正好是 $H_d=(I_4/4)\oplus0_{d-4}$ 的基读数，故式 (16.1) 唯一钉住此 $H_d$。对所有 $X$，其迹预测为 $\operatorname{Tr}(C_d(X))/4$，所以误差至多 $1/4$；在 $E_m\oplus0_{d-4}$ 处取得等号。

最后，在任一固定 $d\ge4$ 中令 $m\to\infty$，本构造始终有 $\epsilon=0$，而

$$
\frac{\max_X|p_{d,m}(X)-\operatorname{Tr}(H_dX)|}{\epsilon+2^{-m}}
=\frac N4\longrightarrow\infty.
\tag{32.9}
$$

对任意有限 $L_d\ge0$，选择 $2^m>4L_d$ 即违反 (18.1)。没有改变其原尺度或误差量词。

为明确与既有谱余量结论的关系，四维特殊效果的特征值为 $\delta_N,1-\delta_N$，各重数二，其中

$$
\delta_N=\frac{1-\sqrt{1-4/N^2}}2
=\frac{2/N^2}{1+\sqrt{1-4/N^2}},
\qquad N^{-2}\le\delta_N\le2N^{-2}.
\tag{32.10}
$$

因此它们处于定理 24.1 排除的双侧边界带中，且在每个有限尺度都没有端点特征值。它们不属于定理 31.1 排除的投影对。$N=4$、$a=1+i,b=1$ 时，(32.2) 的 $A$ 正好是 (22.2) 的既有 Gram 矩阵；这里新增的关系是每个 dyadic $N$ 上直接在四维中同时实现 $A+B=NI_4$ 与 $AB=I_4$，并由此构成完整表，而非再次构造八维投影。$\square$

**定理 32.2（原网格二维完整表的一致稳定性）。** 在定义 16.1 中取 $d=2$。对每个 $m\ge1$、$0\le\epsilon\le1/10$ 及满足全部原菜单条件的同一完整表，其原层析矩阵 $H$ 满足

$$
\max_{E\in K_{2,m}}|p(E)-\operatorname{Tr}(HE)|
\le12190(\epsilon+2^{-m}).
\tag{32.11}
$$

当 $N=2^m\ge160$ 时，更强的上界为 $12190\epsilon$。本结论不增加仿射性、跨尺度相容性或任意有理细分假设。

**证明。** 写 $e(E)=p(E)-\operatorname{Tr}(HE)$。复用定理 16.2 和 24.1 的常数及其精细网格估计：

$$
c_2=1/10,\quad K_2=30,\quad M_2=4,\quad q_2=32,
\qquad U_2=63\cdot30+4\cdot31=2014.
\tag{32.12}
$$

先设 $N\ge160=8\cdot2/c_2$。于是范数至多 $c_2$ 的效果有 $|e|\le30\epsilon$，范数至多 $1-8/N$ 的效果有 $|e|\le2014\epsilon$。每次同网格合法加法的误差至多为式 (16.4) 的 $2\epsilon$。

先控制任意非零秩一效果 $E$。积分秩一矩阵 $NE$ 可写成

$$
NE=t vv^*,\qquad t\in\mathbb Z_{>0},\quad v\in R^2\text{ 本原}.
\tag{32.13}
$$

这里的本原是两个坐标生成单位理想。具体地，$NE$ 的复值域与 $R^2$ 的交是饱和秩一子模，Gaussian 主理想整环性质给出其本原生成元 $v$。每个积分列都是 $v$ 的 Gaussian 整数倍；厄米性及正性遂给出 $NE=t vv^*$，其中初始标量 $t$ 为正实数。取积分行 $\ell$ 满足 $\ell v=1$，则 $t=\ell(NE)\ell^*$ 为正整数，证明 (32.13)。记 $s=\|v\|^2$，有 $ts\le N$。

若 $t\ge2$，把 $t$ 拆成 $\lfloor t/2\rfloor+\lceil t/2\rceil$。所得两个原网格正子效果之和为 $E$，各范数至多 $2/3\le1-8/N$，故一次合法加法给出

$$
|e(E)|\le(2U_2+2)\epsilon\le4062\epsilon.
\tag{32.14}
$$

余下设 $t=1$。此时不可能有 $s=N$：因为 $4\mid N$，$v$ 的四个实整数坐标的平方和模四为零，奇数坐标数只能为零或四。在两种情形中，每个 Gaussian 坐标的实部、虚部奇偶性相同，两个坐标都被 $\pi=1+i$ 整除，与本原性矛盾。这正是定理 31.1 最后一步的既有二维奇偶观察。

所以 $k=N-s\ge1$。对每个坐标取 $w_j\in\{0,1\}$ 表示 $v_j$ 模 $\pi$ 的剩余类，并置 $r=\|w\|^2$。本原性保证 $r\in\{1,2\}$，而 Gaussian 整数的范数模二等于其模 $\pi$ 剩余类，故 $r\equiv s\pmod2$。若 $k=1$，则 $s$ 为奇数，迫使 $r=1$；若 $k\ge2$，则直接有 $r\le2\le k$。因此

$$
vv^*+ww^*\le(s+r)I_2\le NI_2.
\tag{32.15}
$$

这是二维原效果区间内的正性证书。又因为 $v\equiv w\pmod\pi$，两个向量

$$
u=(v+w)/\pi,\qquad z=(v-w)/\pi
$$

都属于 $R^2$。平行四边形恒等式给出

$$
vv^*+ww^*=uu^*+zz^*.
\tag{32.16}
$$

定义 $W=ww^*/N$、$F=uu^*/N$、$G=zz^*/N$。由 (32.15)–(32.16)，$E,W,F,G$ 及共同和 $E+W=F+G$ 均为原同一 $K_{2,m}$ 中的效果。其范数满足

$$
\|W\|\le2/N\le c_2,\qquad
\max(\|F\|,\|G\|)
\le\frac{(\sqrt N+\sqrt2)^2}{2N}
\le\frac{81}{128}<\frac34\le1-\frac8N.
\tag{32.17}
$$

中间的数值界来自 $N\ge160\ge128$，从而 $\sqrt{2/N}\le1/8$。分别对 $E+W$ 与 $F+G$ 应用 (16.4)，再相减；共同和的表值与 (32.16) 的线性迹配对都消去。因此

$$
|e(E)+e(W)-e(F)-e(G)|\le4\epsilon,
\qquad
|e(E)|\le(30+2\cdot2014+4)\epsilon=4062\epsilon.
\tag{32.18}
$$

即使辅助效果为零或彼此重复，相应菜单仍是原定义允许的菜单。合并 (32.14)、(32.18)，每个非零秩一原效果都有相同上界。

对于秩二的 $E$，只在此处复用一个精确的二元形式表示结果：Myung-Hwan Kim 与 Poo-Sung Park，[2-universal Hermitian lattices over imaginary quadratic fields，arXiv:0810.1342v1，定理 2](https://arxiv.org/html/0810.1342v1#ThmThm2) 证明 $\mathbb Q(i)$ 上的三元格 $\langle1,1,1\rangle$ 表示每个正定二元积分 Hermitian 格。其 §2 的表示约定是 $M_\ell=XM_LX^*$，§3 定义 3 中的二元格为正定格。因此对正定的 $NE\in\operatorname{Herm}_2(R)$，该结果恰给出

$$
NE=XX^*,\qquad X\in M_{2\times3}(R).
\tag{32.19}
$$

这里没有把二元供应推广到更高秩。将 $X$ 的三个列向量记为 $v_1,v_2,v_3$，便有

$$
E=\sum_{j=1}^3\frac{v_jv_j^*}{N}.
$$

每个非零项为已控制的秩一效果，全部部分和都为原网格效果：其条目积分除以同一个 $N$，且因所有项半正定而在序上不超过 $E\le I_2$。略去零列后，至多两次 (16.4) 给出

$$
|e(E)|\le\bigl(3\cdot4062+4\bigr)\epsilon=12190\epsilon.
\tag{32.20}
$$

秩一情形已有更强界，零效果则由 $p(0)\le2\epsilon$ 控制。因此精细网格上覆盖了整个效果表，关系数不随 $m$ 增长。

若 $N<160$，定理 16.2 的 $\|H\|\le4$ 和 $0\le E\le I_2$ 给出 $|e(E)|\le1+2\cdot4=9<1440/N\le12190/N$，证明 (32.11) 的全部粗尺度情形。$\square$

定理 32.1 在每个固定 $d\ge4$ 中否定 (18.1)，定理 32.2 则肯定其中的 $d=2$ 分支。二者均保持定义 16.1 的原网格、同一完整表、原层析基及原菜单量词；定理 16.2、17.1–17.2、24.1 与投影专属的定理 31.1 继续按各自假设适用。这里没有解决 $d=3$ 的 (18.1)，也没有断言四维是任意效果完整表反例的最小维数。二维的额外步骤是 (32.15)–(32.18) 的同网格奇偶补全及其与二元表示供应的组合；Gaussian 主理想整环、四平方定理、积分收缩的代数整数论证和 Kim–Park 表示定理均为有明确作用的经典中间工具。以上推导不作全球文献优先权或物理实现断言。

## 追加锚（本行以下为增补区）

## 33. 三维原完整表的同网格奇偶交换与全局稳定性

**定理 33.1（三维单网格完整表的统一原层析估计）。** 固定复维数 $d=3$。对每个整数 $m\ge1$，置 $N=2^m$，并保留定义 16.1 的原效果集合

$$
K_{3,m}=\{E\in\operatorname{Herm}_3(N^{-1}\mathbb Z[i]):0\le E\le I_3\}.
$$

设 $0\le\epsilon\le1/10$，且同一个函数 $p:K_{3,m}\to[0,1]$ 对每个 $r\in\{2,3\}$、每个满足 $\sum_{j=1}^rE_j=I_3$ 的带标签元组 $(E_1,\ldots,E_r)\in K_{3,m}^r$ 都满足

$$
\left|\sum_{j=1}^r p(E_j)-1\right|\le\epsilon,
$$

其中包括零项和重复项。令 $H$ 为式 (16.1) 的唯一原层析矩阵，即对原实基 $\mathcal B=\{D_a:1\le a\le3\}\cup\{R_{ab},J_{ab}:1\le a<b\le3\}$ 满足 $\operatorname{Tr}(HQ)=p(Q)$ 的 Hermitian 矩阵；这里 $R_{ab},J_{ab}$ 及 $T_{ab}$ 的符号完全按定义 16.1。则

$$
\max_{E\in K_{3,m}}|p(E)-\operatorname{Tr}(HE)|
\le400000(\epsilon+2^{-m}).
\tag{33.1}
$$

当 $N\ge648$ 时，更强的上界是 $332008\epsilon$。常数均与 $m,\epsilon,p$ 无关，不要求跨尺度相容性、额外仿射性或连续性。

**证明。** 全部矩阵与表值固定在上述同一个 $N$。记 $R=\mathbb Z[i]$、$\pi=1+i$，并写 $e(X)=p(X)-\operatorname{Tr}(HX)$。

（一）复用局部估计与单侧内部估计。定理 16.2 和 24.1 在 $d=3$ 时给出

$$
c_3=1/27,\qquad K_3=60,\qquad M_3=6,\qquad q_3=64,
\qquad U_3=127\cdot60+4\cdot63=7872.
\tag{33.2}
$$

先设 $N\ge648=8\cdot3/c_3$。于是 $\|X\|\le c_3$ 时有 $|e(X)|\le60\epsilon$，而 $\|X\|\le1-12/N$ 时有 $|e(X)|\le U_3\epsilon$。以下范数均为算子范数，向量范数为标准 Euclidean 范数。式 (16.4) 直接给出

$$
|e(A)+e(B)-e(A+B)|\le2\epsilon
\quad(A,B,A+B\in K_{3,m}).
\tag{33.3}
$$

特别地，若 $A+B=C+D\le I_3$ 且四个加项都是原网格半正定矩阵，则共同和也在原网格内，因而

$$
|e(A)+e(B)-e(C)-e(D)|\le4\epsilon.
\tag{33.4}
$$

每次 (33.3) 对应的原菜单恰为 $(A,B,I_3-A-B)$ 与 $(A+B,I_3-A-B)$。因此 (33.4) 允许任何零项或重复项，不需要共同和的误差已有上界。

（二）导出所需的有限积分秩一分解。先对 $G\in\operatorname{Herm}_r(R)$ 正定、$1\le r\le3$，证明存在 $0\ne q\in R^r$ 使 $qq^*\le G$。置 $D=\det G\in\mathbb Z_{>0}$。在 $R^r$ 上取实内积 $\operatorname{Re}(z^*G^{-1}w)$。其实维数为 $2r$，实 Gram 行列式为 $D^{-2}$，故 Euclidean 余体积为 $D^{-1}$。这里没有额外的因子二：标准 $R^r$ 在 $\operatorname{Re}(z^*w)$ 下的余体积为一。

只在这一步复用式 (31.8) 已引的普通实 Hermite 常数。Stephanie Vance，[A Mordell Inequality for Lattices over Maximal Orders，arXiv:0810.2336v5，§1、§4.2 与表 3](https://arxiv.org/html/0810.2336v5) 以实 Gram 行列式为基本域体积的平方，Hermite 不变量为最短平方范数除以该行列式的 $1/n$ 次方；§4.2 紧邻表 3 的正文说明维数不超过八的所列格在普通实格中最优。因此对任意上述实化格均可用

$$
\gamma_4=\sqrt2,\qquad \gamma_6=2/3^{1/6},
\qquad
0<q^*G^{-1}q\le\gamma_{2r}D^{-1/r}
\quad(r=2,3).
\tag{33.5}
$$

这不是只对 Gaussian 或 Eisenstein 子类使用的界。由于 $G$ 的伴随矩阵具有 Gaussian 整数条目且为正定 Hermitian 矩阵，

$$
a=q^*\operatorname{adj}(G)q=Dq^*G^{-1}q
\in\mathbb Z_{>0}.
$$

当 $r=3$ 时，

$$
4(D+1)^3-27D^2=(D-2)^2(4D+1)\ge0,
\qquad \gamma_6^3=8/\sqrt3<27/4.
$$

所以 $a\le\gamma_6D^{2/3}<D+1$。当 $r=2$ 时，同样有 $a\le\sqrt{2D}<D+1$，因为 $(D+1)^2-2D=D^2+1>0$。整数性在两种情形下都迫使 $a\le D$，即 $q^*G^{-1}q\le1$。当 $r=1$ 时直接取 $q=1$，因为 $G=[D]$ 且 $D\ge1$。对任意 $z\in\mathbb C^r$，$G$ 内积的 Cauchy 不等式于是给出

$$
|q^*z|^2\le(q^*G^{-1}q)(z^*Gz)\le z^*Gz,
\qquad 0<qq^*\le G.
\tag{33.6}
$$

现设 $0\ne A\in\operatorname{Herm}_3(R)$ 半正定，秩为 $r$。其积分核 $\ker(A)\cap R^3$ 饱和：若 $0\ne b\in R$ 且 $bx$ 在核中，则 $bAx=0$ 迫使 $Ax=0$。由于 $A$ 在 $\mathbb Q(i)$ 上有定义，此积分核的秩等于 $3-r$。复用第 31 节的 Gaussian 主理想整环分裂，取幺模矩阵 $V\in\operatorname{GL}_3(R)$，使最后 $3-r$ 个列向量构成该核的一组基。于是

$$
V^*AV=\begin{pmatrix}G&0\\0&0\end{pmatrix},
\qquad G\in\operatorname{Herm}_r(R)\text{ 正定}.
$$

令 $T$ 为 $V^{-1}$ 的前 $r$ 行，则 $A=T^*GT$；$T$ 有积分右逆，故 $T^*$ 单射。由 (33.6) 得到非零积分向量 $v=T^*q\in R^3$，满足

$$
0<vv^*\le A.
\tag{33.7}
$$

矩阵 $A-vv^*$ 仍为积分半正定矩阵，而其非负整数迹比 $\operatorname{Tr}A$ 严格减少 $\|v\|^2\ge1$。对迹归纳，连同零矩阵的空和，便得到每个积分半正定三阶矩阵的有限分解

$$
A=\sum_{j=1}^{\ell}v_jv_j^*,\qquad v_j\in R^3\setminus\{0\}.
\tag{33.8}
$$

此处没有关于 $\ell$ 的统一上界。分解是 (33.5)–(33.7) 导出的算术结论，不是对效果表增加的假设。若 $A=NE$ 且 $E\in K_{3,m}$，则 $Q_j=v_jv_j^*/N$ 及其任意部分和都在原 $K_{3,m}$ 内：条目的分母始终是同一个 $N$，且半正定性保证每个部分和在序上不超过 $E\le I_3$。

（三）控制范数严格小于一的秩一效果。对任意非零秩一原效果，复用 (32.13) 的饱和值域论证，在三维写成

$$
E=t vv^*/N,\qquad t\in\mathbb Z_{>0},\qquad
v\in R^3\text{ 本原},\qquad s=\|v\|^2,\quad ts\le N.
\tag{33.9}
$$

具体地，其积分饱和值域有本原生成元 $v$，厄米性与正性给出正实标量 $t$；取积分行 $b$ 满足 $bv=1$，便有 $t=b(NE)b^*\in\mathbb Z_{>0}$。

若 $t\ge2$，把 $t$ 拆成 $\lfloor t/2\rfloor+\lceil t/2\rceil$。两个正子效果都在原网格内，其范数至多 $2/3\le1-12/N$。一次 (33.3) 因而给出

$$
|e(E)|\le(2U_3+2)\epsilon=15746\epsilon.
\tag{33.10}
$$

这一步也适用于 $ts=N$ 的投影。

余下先设 $t=1$、$s<N$，并置 $k=N-s\ge1$。对 $v_j\equiv0\pmod\pi$ 的坐标取 $w_j=0$；对其余坐标取 Gaussian 单位 $w_j\in\{1,-1,i,-i\}$。单位的模 $\pi$ 剩余类均为一，所以

$$
w\equiv v\pmod\pi,\qquad
r=\|w\|^2\in\{1,2,3\},\qquad r\equiv s\equiv k\pmod2.
$$

本原性排除 $r=0$。若 $r\le k$，则 $vv^*+ww^*\le(s+r)I_3\le NI_3$。因为 $r\le3$ 且 $r,k$ 同奇偶，唯一尚未覆盖的情形为 $k=1,r=3$。

在这一情形，三个 $v_j$ 都非零。写 $\alpha_j=\overline{v_j}w_j$，先固定 $w_1=1$，再取单位 $w_2$ 使

$$
\operatorname{Re}(\alpha_1\overline{\alpha_2})\le-1.
$$

这是可行的，因为 $\overline{v_1}v_2$ 是非零 Gaussian 整数，其实部或虚部至少一个是非零整数，乘适当单位即可取到不大于负一的实部。再取单位 $w_3$ 使 $\operatorname{Re}((\alpha_1+\alpha_2)\overline{\alpha_3})\le0$；在两个相反的单位中至少一个满足此式。于是

$$
|v^*w|^2=|\alpha_1+\alpha_2+\alpha_3|^2
\le s-2=N-3.
\tag{33.11}
$$

令 $C$ 的两列为 $v,w$。矩阵 $NI_2-C^*C$ 的对角元为 $1,N-3$，行列式为 $N-3-|v^*w|^2\ge0$，故它半正定。矩形矩阵的非零奇异值在 $C^*C$ 与 $CC^*$ 中相同，所以 $CC^*\le NI_3$。连同 $r\le k$ 的情形，总有一个这样的 $w$ 满足

$$
w\equiv v\pmod\pi,\qquad \|w\|^2\le3,
\qquad vv^*+ww^*\le NI_3.
\tag{33.12}
$$

定义积分向量与原网格矩阵

$$
u=(v+w)/\pi,\qquad z=(v-w)/\pi,
\qquad W=ww^*/N,\quad F=uu^*/N,\quad G=zz^*/N.
$$

因为 $|\pi|^2=2$，平行四边形恒等式给出

$$
E+W=F+G\le I_3.
\tag{33.13}
$$

所有加项与共同和都属于原 $K_{3,m}$。此外，$N\ge648\ge192$ 保证 $\sqrt{3/N}\le1/8$，故

$$
\|W\|\le3/N\le1/27,
\qquad
\max(\|F\|,\|G\|)
\le\frac{(\sqrt N+\sqrt3)^2}{2N}
\le\frac{81}{128}<\frac34\le1-\frac{12}{N}.
\tag{33.14}
$$

对 (33.13) 使用 (33.4)，再用局部与内部估计，得到

$$
|e(E)|\le(60+2U_3+4)\epsilon=15808\epsilon.
\tag{33.15}
$$

因此每个非零秩一非投影效果都有 (33.15)，而 $t\ge2$ 的所有效果已有更强的 (33.10)。

（四）控制本原秩一投影。只余 $t=1$、$s=N$。因 $v$ 本原且 $N$ 为偶数，模 $\pi$ 非零的坐标数为正偶数；在三维只能恰为二。仅为记号方便排列坐标，写成 $v=(a,b,c)^{\mathsf T}$，其中 $a,b$ 模 $\pi$ 非零、$c$ 模 $\pi$ 为零。

Gaussian 整数模 $\pi$ 非零，当且仅当其实部、虚部奇偶性相反，故其范数模四为一。这里 $4\mid N$，所以

$$
|c|^2=N-|a|^2-|b|^2\equiv2\pmod4,
\qquad c\ne0.
$$

取

$$
w=(-\overline b,\overline a,0)^{\mathsf T},
\qquad r=\|w\|^2=N-|c|^2.
\tag{33.16}
$$

则 $0<r<N$、$v^*w=0$，且 $w\equiv v\pmod\pi$。正交性给出 $vv^*+ww^*\le NI_3$。仍定义 $u,z,W,F,G$ 如上，便有原网格共享和 (33.13)，并且

$$
\|W\|=r/N<1,
\qquad
\|F\|=\|G\|=\frac{N+r}{2N}<1.
$$

三个辅助效果都是非零秩一非投影，所以已经分别满足 (33.15)，无须假定它们具有统一的谱余量。再次使用 (33.4) 得

$$
|e(E)|\le(3\cdot15808+4)\epsilon=47428\epsilon.
\tag{33.17}
$$

(33.10)、(33.15)、(33.17) 遂证明每个非零秩一原效果都有统一上界 $47428\epsilon$，包括所有原网格秩一投影。

（五）以迹分组控制任意效果。对 $0\ne E\in K_{3,m}$ 使用 (33.8)，写 $E=\sum_{j=1}^{\ell}Q_j$。每个 $Q_j$ 为非零秩一原效果，且

$$
\sum_{j=1}^{\ell}\operatorname{Tr}(Q_j)
=\operatorname{Tr}(E)\le3.
\tag{33.18}
$$

把迹严格大于 $7/16$ 的每个项单独作为一组。将其余迹至多 $7/16$ 的项逐项累积，一旦组的迹达到 $7/16$ 就结束该组，再开始下一组。每个如此完成的组迹至多 $7/8$；至多最后一个未完成组的迹小于 $7/16$。因此得到分组和 $B_1,\ldots,B_g$，除至多一个组外，每组的迹至少为 $7/16$。由 (33.18)，

$$
(g-1)\frac7{16}\le3,
\qquad g\le7.
\tag{33.19}
$$

这里每个 $B_j$ 与各组的部分和仍是同一个原网格中的效果。单项大组为已由 (33.17) 控制的秩一效果；其余组由半正定性满足

$$
\|B_j\|\le\operatorname{Tr}(B_j)\le7/8\le1-12/N,
$$

故其误差至多 $U_3\epsilon\le47428\epsilon$。仅对这至多七个组逐次应用 (33.3)，而不对分解的全部 $\ell$ 个项逐次累积表误差，便有

$$
|e(E)|\le\bigl(47428g+2(g-1)\bigr)\epsilon
\le(7\cdot47428+12)\epsilon
=332008\epsilon.
\tag{33.20}
$$

零效果由 $|e(0)|=p(0)\le2\epsilon$ 覆盖。这证明精细尺度下对全部效果的估计，包括奇异效果、补效果奇异的效果，以及效果和补效果均正定的情形；分解长度不进入常数。

（六）补上粗尺度并说明来源范围。若 $N<648$，定理 16.2 的 $\|H\|\le6$、$0\le E\le I_3$ 及 $p(E)\in[0,1]$ 给出

$$
|e(E)|\le1+6\operatorname{Tr}(E)\le19
<\frac{19\cdot648}{N}<\frac{400000}{N}.
$$

与 (33.20) 合并即得 (33.1)。原矩阵 $H$ 在全部推导中固定不变；每个表关系都来自原分母 $N$ 上的合法菜单，积分分解与共享和的正性均已在上文导出。

本定理的全表估计由积分伴随矩阵的舍入、三坐标单位相位补全、正交奇偶共享和及有界迹分组共同推出。局部与单侧内部估计直接复用定理 16.2、24.1，饱和子模及本原秩一正规形复用第 31–32 节；普通实 Hermite 常数按 (33.5) 的明确版本与归一化引用。Gaussian 主理想整环、Cauchy 不等式和矩形 Gram 矩阵的谱关系均为经典中间工具，不另列为新增定理。结论只涉及所声明的数学效果表，不增加概率取得或物理实现前提，也不作穷尽文献或全球优先权断言。$\square$

## 追加锚（本行以下为增补区）

## 34. 原生双块源的分级与完整有限协议

**定义 34.1（同一原生源及其算术坐标）。** 取 [ImmediateWindowStateCapacity 的 `rawTransition` 与 `task`](../../../D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.lean) 的立即输出任务：允许高端零填充，无 End 标记，从缝位零和 $(0,0)$ 出发。窗口按从高到低的时间顺序作用，缝位守卫为 $s\land\operatorname{last}(b)$，成功后的缝位为 $\operatorname{first}(b)$。`zero`、`middle` 的首尾位均零，`high` 的首位零、尾位一；位的定义取自 [LiteralWindowEnd 的 `first`、`last`](../../../D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.lean)，但不借用其另一 End 任务。令

$$
B_0=\mathsf{zero}^{19}\mathsf{middle},\qquad
B_1=\mathsf{zero}^{19}\mathsf{high},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\quad P=S^{20}.
\tag{34.1}
$$

两块均从缝位零合法返回缝位零，所有有限拼接合法。每窗口的线性更新为 $S$，末窗口位移分别为 $e_2$ 与 $e_1+e_2$，故块更新为

$$
T_b(v)=Pv+e_2+be_1\quad(b=0,1),\qquad
v_\varnothing=0,\quad v_{wb}=T_b(v_w),\qquad
Q(w)=q(v_w),\quad q(x,y)=2x+3y.
\tag{34.2}
$$

这里 $v_w\in\mathbb N^2$ 是 [GraftAffineClosure 的多态 `step`、`quantity`](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean) 的非负整数坐标；立即读器的实际输出仍是声明模数的 $q\bmod m$。完整整数 $Q$ 的可计算性与它是否被实际读出是不同假设。记 $W=\{0,1\}^{<\omega}$，$|w|$ 为块数，每块含二十个原窗口。

**假设 34.2（复数载体、两个操作菜单与全局有限合同）。** 在同一个 $\{v_w:w\in W\}$ 上授予正交复 Hilbert 载体 $H=\ell^2(W)$ 和 Born 概率。$H_L$ 为恰长 $L$ 的子空间，$P_L,P_{<L},P_{>L}$ 为对应正交投影。最小菜单 $\mathcal M$ 的源操作仅为

$$
R_s|w\rangle=|ws\rangle\quad(s\in W),\qquad
J|w\rangle=|\operatorname{rev}(w)\rangle,
\qquad J^*=J,\quad J^2=I.
\tag{34.3}
$$

授予这些映射的相干有限控制、与未知输入独立的有限维 ready 控制器、任意有限维控制器操作和读口。对照菜单 $\mathcal G$ 再授予有界源对角算子 $D_f|w\rangle=f(w)|w\rangle$ 作为指定归一化仪器或相干控制的组成；其中包含有限结果的字投影仪器和任意对角相位。只知道一个效果，不等于授予该效果的更新仪器。两菜单均不含源删除、重置、逆追加、任意重制备或源与另一个寄存器的交换。

一次协议是一棵全局有限的自适应树：节点数、深度、每节点实际可读结果数、每结果的隐藏 Kraus 数、控制器维数及所用有限字集合均有限。每节点联合源—控制器 Kraus 矩阵的源条目是相应菜单生成元的有限乘积之有限复线性和；控制器系数为有限矩阵。所有实际分支的 Kraus 算子满足局部完备关系。终端保留的可读记录 $z$ 包含全部实际结果、成功、失败和早停标签；未读 Kraus 指标 $\mu$ 不成为记录，也不成为可用于后续控制的结果。有限维初始混合控制器可纯化，或把其准备指标收入隐藏指标。任意终端控制器读口包含在树内；其余控制器自由度迹出。保留有限维、不受操作的参考 $R$，允许源输入与 $R$ 纠缠。

将初始 ready 控制器代入并迹出终端控制器，得到有限族 $K_{z\mu}:H\to H$，满足

$$
\sum_{z,\mu}K_{z\mu}^*K_{z\mu}=I,\qquad
\mathcal I_z(\tau)=\sum_\mu
 (K_{z\mu}\otimes I_R)\tau(K_{z\mu}^*\otimes I_R),\qquad
p_z=\operatorname{Tr}\mathcal I_z(\tau).
\tag{34.4}
$$

可读输出整体为 $\sum_z|z\rangle\langle z|\otimes\mathcal I_z(\tau)$。这采用 Watrous [《The Theory of Quantum Information》第二章，定理 2.22、2.26 及 §2.3.2 的 (2.258)–(2.262)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) 的有限 Kraus、仪器及保留结果语义；它们是所授予概率合同的数学工具。Theurer 等 [《Quantifying Operations with an Application to Coherence》，(3)–(7)](https://arxiv.org/pdf/1806.07332v2) 同样将实际可选结果保留为经典旗标；隐藏 Kraus 分解不是额外可选结果。该合同不包含任意正常 CP 映射、无限次尝试、连续结果、无限 Kraus 和或仅逐条有限而整体无界的树。

**定理 34.3（原生坐标、有限可达支撑与零增长代数的对应）。** 在定义 34.1 和假设 34.2 下，$w\mapsto Q(w)$、从而 $w\mapsto v_w$ 均单射。基映射 $|w\rangle\mapsto|v_w\rangle$ 因而给出所声明载体之间的酉识别，使两个合法块恰对应右追加。对每个固定 $L$ 和每个上述协议，所有节点的实际可达源支撑都有限，协议精确限制为有限维、保留同一可读记录及参考的仪器树。其完整源 Kraus 历史满足

$$
P_{<L}K_{z\mu}P_L=0,\qquad
A_{z\mu}:=P_LK_{z\mu}P_L\in\mathcal A_L,
\tag{34.5}
$$

其中

$$
\begin{aligned}
\mathcal A_L^{\mathcal M}&=\operatorname{span}_{\mathbb C}\{I_L,J_L\},\qquad J_L=J|_{H_L},\\
\mathcal A_L^{\mathcal G}&=\bigoplus_{O}\mathcal B(H_O),\qquad
O=\{w,\operatorname{rev}(w)\},\quad
H_O=\operatorname{span}\{|u\rangle:u\in O\},\quad |w|=L.
\end{aligned}
\tag{34.6}
$$

回文的轨道只含一个字。(34.6) 是生成代数的相等，不声称该代数中每个归一化 Kraus 族都可由菜单合成。

证明。为给出坐标识别所需的完整算术桥，令 $a_j=q(P^je_1)$、$c_j=q(P^je_2)$。非负矩阵有 $S\succeq I$、$P\succeq S$ 且 $qS=(8,13)\succeq3q$，于是 $a_{j+1}\ge3a_j$、$c_{j+1}\ge3c_j$。在 $j\ge1$ 时，$P^je_2-P^je_1=S^{20j-1}(1,1)\succeq0$；在 $j=0$ 时 $a_0=2\le3=c_0$。因此 $0<a_j\le c_j$。若 $w=b_1\cdots b_L$ 按时间顺序排列，

$$
Q(w)=\sum_{j<L}c_j+\sum_{j<L}\varepsilon_ja_j,\qquad\varepsilon_j=b_{L-j}.
\tag{34.7}
$$

这里 $\varepsilon_j$ 是按逆时间位置排列的字母。固定 $L$ 时，在最高不同位置 $m$ 上的差至少为 $a_m-\sum_{j<m}a_j>a_m/2>0$。不同长度也分离：任一长 $L\ge1$ 的量至少为 $c_{L-1}$，任一更短字的量至多为

$$
\sum_{j<L-1}(a_j+c_j)\le2\sum_{j<L-1}c_j<c_{L-1}.
$$

空字的量为零。这证明两项单射及基识别。正交 Hilbert 结构仍来自假设 34.2，而非整数单射。标准全 Fock 空间左右创生与反转对应见 Arias–Popescu [《Factorization and Reflexivity on Fock spaces》，§1、引理 1.7 前的 flip $U$](https://arxiv.org/pdf/math/9404209)；此处采用右追加约定。仓内 [WordHistoryOperators 的 `WordHilbert`、`appendShift`](../../../D5/S3/Quantum/Dynamics/WordHistoryOperators.lean) 及其 [Blueprint 叙述](../../../Blueprint/D5/S3/Quantum/Dynamics/WordHistoryOperators.md) 使用相同约定。这个既有载体工具不提供实际受控 $J$。

每个节点的源条目有限展开，每个单项只会追加有限个字并反转或乘对角系数。取根至节点路径上各节点最大追加块数之和为 $g_v$；节点有限，故这些数均有限。输入长度不超过 $L$ 时，该节点的源支撑包含于

$$
F_v=\{w:|w|\le L+g_v\},\qquad |F_v|=2^{L+g_v+1}-1.
\tag{34.8}
$$

令 $E_v:\mathbb C^{F_v}\hookrightarrow H$ 为基嵌入。局部操作 $V_{y\nu}$（连同有限控制器）满足 $V_{y\nu}E_v=E_{vy}\widehat V_{y\nu}$，其中 $\widehat V_{y\nu}=E_{vy}^*V_{y\nu}E_v$；输出支撑界使这个等式精确，未截断任何振幅。故

$$
\sum_{y,\nu}\widehat V_{y\nu}^*\widehat V_{y\nu}
=E_v^*\Bigl(\sum_{y,\nu}V_{y\nu}^*V_{y\nu}\Bigr)E_v=I.
\tag{34.9}
$$

把源和控制器合为一个有限 actor，节点维数取 $|F_v|\dim C_v$，参考仍为原 $R$，得到 [RetainedLocalProtocol 的 `Instrument`、`Tree`、`step`](../../../D5/S3/Quantum/Recovery/RetainedLocalProtocol.lean) 的有限矩阵语义。对每个实际结果只求和隐藏指标，节点 CP 映射为 $X\mapsto\sum_\nu\widehat V_{y\nu}X\widehat V_{y\nu}^*$；(34.9) 给出其全部矩阵上的 trace-preserving 字段。逐节点的嵌入等式连同 $I_R$，归纳地保留每个前缀和终端的完整矩阵、轨迹概率及早停记录。这是 [FiniteInstrumentRelationGraph 的 `relation_graph_protocol_correspondence`](../../../D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph.lean) 的有限定义域对应；概率边缘的 trace 恒等式对应 [FiniteKrausInstrumentBornMarginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean)。这里的嵌入证明没有把无限 $H$ 本身当作有限 actor。

最后，在每个完整 Kraus 历史中展开有限源单项。无操作缩短字，故 (34.5) 第一式成立；含非空追加的单项的终长严格大于 $L$，不能贡献 $A_{z\mu}$。其余单项在最小菜单内归约为 $I_L$ 或 $J_L$，在对照菜单内保持每个反转轨道。有限和与相消均不改变这些结论。反之，任意轨道的对角矩阵元来自字投影；对 $w\ne\operatorname{rev}(w)$，算子 $|\operatorname{rev}(w)\rangle\langle\operatorname{rev}(w)|J|w\rangle\langle w|$ 给出非对角矩阵元，证明 (34.6)。$\square$

## 35. 同源返回操作与完整记录的增长代价

**定义 35.1（终长返回、记录距离与受限态）。** 固定 $L$。令

$$
C_{z\mu}=P_{>L}K_{z\mu}P_L,\qquad
\mathsf R=\sum_{z,\mu}A_{z\mu}^*A_{z\mu},\qquad
\mathsf D=\sum_{z,\mu}C_{z\mu}^*C_{z\mu}.
\tag{35.1}
$$

对 $H_L$ 上密度矩阵 $\rho$，记 $\delta_\rho=\operatorname{Tr}(\mathsf D\rho)$ 为最终源字长严格增加的概率。此处返回仅指终长 $L$，不要求还原未知态、ready 控制器或全部物理历史。$p_z^\rho=\sum_\mu\operatorname{Tr}(K_{z\mu}\rho K_{z\mu}^*)$ 是完整可读记录律，

$$
V(p^\rho,p^\sigma)=\frac12\sum_z|p_z^\rho-p_z^\sigma|.
\tag{35.2}
$$

$\rho|_{\mathcal A_L}=\sigma|_{\mathcal A_L}$ 指对每个 $A\in\mathcal A_L$ 有 $\operatorname{Tr}(A\rho)=\operatorname{Tr}(A\sigma)$。在最小菜单中只需两反转奇偶总体权重相同；在对照菜单中等价于每个反转轨道的完整主块相同。

**定理 35.2（分级限制给出的精确返回形式、同源门障碍与记录界）。** 对假设 34.2 的每个协议，

$$
0\le\mathsf D=I_L-\mathsf R\le I_L,\qquad
\mathsf D,\mathsf R\in\mathcal A_L.
\tag{35.3}
$$

若 $\rho|_{\mathcal A_L}=\sigma|_{\mathcal A_L}$，则 $\delta_\rho=\delta_\sigma=:\delta$ 且

$$
V(p^\rho,p^\sigma)\le\delta.
\tag{35.4}
$$

在两输入上的返回概率均至少 $1-\epsilon$ 时，完整记录的等先验最优判别成功率不超过 $(1+\epsilon)/2$。

在最小菜单中，对全部 $H_L$ 输入精确返回的源通道，令 $\Pi_\pm=(I_L\pm J_L)/2$，则只可能有

$$
\Phi(X)=
\begin{pmatrix}
X_{++}&\gamma X_{+-}\\
\overline\gamma X_{-+}&X_{--}
\end{pmatrix},\qquad |\gamma|\le1.
\tag{35.5}
$$

当两扇区非零时，每个这样的 $\gamma$ 可由最小菜单及所授予控制器达到；不存在的扇区略去。各实际结果的效果在每个扇区内为标量。因此 $J_L=I_L$ 时精确返回的源通道为恒等。

即使采用对照菜单，对不同反转轨道的 $a,b\in W$、$|a|=|b|=L$，令 $U_{ab}$ 交换 $|a\rangle,|b\rangle$ 并在 $H_L$ 的其余基上恒等，$\iota_L:H_L\hookrightarrow H$。每个完整源通道 $\Phi$ 满足

$$
\frac12\|\Phi|_{H_L}-\operatorname{Ad}_{\iota_LU_{ab}}\|_\diamond=1.
\tag{35.6}
$$

这也排除任何正概率后选择分支在输入 $|a\rangle$ 上实现该同源目标。

证明。定理 34.3 给出 $K_{z\mu}P_L=A_{z\mu}+C_{z\mu}$，且 $A_{z\mu}^*C_{z'\mu'}=0$，因为输出处在正交终长。由完备性得 (35.3)，包括 $\mathsf D\in\mathcal A_L$；不需实际测量字长。

置

$$
F_z=\sum_\mu A_{z\mu}^*A_{z\mu}\in\mathcal A_L,\qquad
G_z=\sum_\mu C_{z\mu}^*C_{z\mu}\ge0.
$$

则 $p_z^\rho=h_z+g_z$、$p_z^\sigma=h_z+g'_z$，其中 $h_z=\operatorname{Tr}(F_z\rho)=\operatorname{Tr}(F_z\sigma)$，$g_z,g'_z\ge0$，而 $\sum_zg_z=\sum_zg'_z=\delta$。所以

$$
V=\frac12\sum_z|g_z-g'_z|
\le\frac12\sum_z(g_z+g'_z)=\delta.
$$

迹公式是假设 34.2 所引有限仪器的既有 Born 边缘；本处新增限制是来自原生菜单分级的共同 $h_z$ 与共同 $\delta$。未对 $\mu$ 进行额外读出。该结论仅限制记录：源自身仍可保留可完美区分的输入信息。若只条件化于罕见增长成功，条件记录可完美区分，但其无条件权重仍是 $\delta$。

精确返回意味着 $\mathsf D=0$。各 $C_{z\mu}^*C_{z\mu}\ge0$，故每项均零。最小菜单的剩余 Kraus 算子写成 $A_j=\alpha_j\Pi_++\beta_j\Pi_-$，$j=(z,\mu)$。非零扇区上的完备性为 $\sum_j|\alpha_j|^2=\sum_j|\beta_j|^2=1$，于是 (35.5) 中 $\gamma=\sum_j\alpha_j\overline{\beta_j}$，Cauchy–Schwarz 给 $|\gamma|\le1$。这是标准两扇区 Schur 乘子／无噪声块的初等计算，作为源分级应用的中间步骤使用。

为说明其可达性，以 ready qubit 先施 Hadamard、受控 $J$、Hadamard，将反转奇偶相干地写入 qubit；在其一标签施相位，再逆向施同一计算（受控 $J$ 自逆），可得 $\Pi_++e^{-i\theta}\Pi_-$ 并返还 ready qubit。若 $\gamma=re^{i\theta}$，以概率 $(1+r)/2$、$(1-r)/2$ 分别施 $\Pi_++e^{-i\theta}\Pi_-$ 与 $\Pi_+-e^{-i\theta}\Pi_-$ 即得 (35.5)。这是有限控制器的构造，不由算术块操作推出受控反转。

最后从 $|a\rangle$ 出发，所有终长 $L$ 输出都在 $H_{O(a)}$，其余输出长于 $L$，故输出在 $|b\rangle$ 上的概率为零。目标输出恰为 $|b\rangle\langle b|$，两态正交，迹距离为一。以此无参考输入得半 diamond 距离至少一；两个通道的半 diamond 距离至多一，证明 (35.6)。每个细 Kraus 历史已有相同零支撑，故后选择亦无帮助。具体可取 $a=00,b=11$，也可取下一节的 $a=001,b=010$。$\square$

**推论 35.3（跨轨道相位与基输入增长界）。** 若 $a,b$ 属于不同反转轨道，令 $\psi_\pm=(|a\rangle\pm|b\rangle)/\sqrt2$。即使采用对照菜单，两态在 $\mathcal A_L$ 上相同，且

$$
\delta_{\psi_+}=\delta_{\psi_-}
=\frac{\langle a|\mathsf D|a\rangle+\langle b|\mathsf D|b\rangle}{2}.
\tag{35.7}
$$

所以若两个基输入的增长概率各不超过 $\epsilon$，相位对的完整记录距离不超过 $\epsilon$。

证明。$\mathcal A_L$ 的所有算子在两个轨道之间的矩阵元为零，故两态的相反非对角项对该代数及 $\mathsf D$ 都无贡献。应用 (35.4)。这里基数据足够是因为已证明 (34.6) 的完整算子限制；一般设备的几个基概率不建立该限制，亦不给出任意操作的算子范数证书。$\square$

## 36. 原生 001 与 010 的精确移码仪器及线性界取等

**定理 36.1（同模端点上的一次追加相位读出）。** 对定义 34.1 的实际块字取

$$
a=001,\qquad b=010,\qquad
C=\operatorname{span}\{|a\rangle,|b\rangle\}\subset H_3,\qquad
\psi_\pm=\frac{|a\rangle\pm|b\rangle}{\sqrt2}.
\tag{36.1}
$$

两个完整自然端点不同，而包含缝位的完整模五状态相同。其反转轨道分别为 $\{001,100\}$、$\{010\}$。一次右追加 $0$ 给出等距编码 $E=R_0|_C:C\to H_4$，输出码为 $C'=\operatorname{span}\{|0010\rangle,|0100\rangle\}$。最小菜单已能实现完整二结果仪器，其在 $C\otimes R$ 上的实际分支为

$$
\mathcal I_\pm(\tau)
=(EP_\pm^C\otimes I_R)\tau(P_\pm^CE^*\otimes I_R),\qquad
P_\pm^C=|\psi_\pm\rangle\langle\psi_\pm|.
\tag{36.2}
$$

它在移码上精确读出输入的相对正负号。对每个 $0\le\epsilon\le1$，还有同一最小菜单协议在 $C$ 上取等于 (35.4)：最终源恰增加一个块字母的概率为 $\epsilon$，否则源不变，且 $V=\epsilon$。

证明。由 $M^5=\left(\begin{smallmatrix}3&5\\5&8\end{smallmatrix}\right)\equiv3I\pmod5$，有 $P=M^{60}\equiv I\pmod5$。于是任意块字的整个模端点为

$$
v_w\equiv(N_1(w),|w|)\pmod5,\qquad
Q(w)\equiv2N_1(w)+3|w|\pmod5.
\tag{36.3}
$$

$a,b$ 均含一个 $1$ 且长三，故完整模状态均为 $(\text{缝位 }0,(1,3))$，量均为一。自然端点不同由定理 34.3 的单射得出；这不是把模读器换成完整整数读器。它们从相同完整模状态开始的每个共同合法经典续接都有相同输出律。追加 $0$ 后两模端点仍相同，均为 $(1,4)$，量为四。

但是 $\operatorname{rev}(0010)=0100$，故若 $X_C$ 交换 $a,b$，全空间反转投影 $\Pi_\pm^H=(I_H\pm J)/2$ 满足

$$
JR_0|_C=EX_C,\qquad
\Pi_\pm^HR_0|_C=EP_\pm^C.
\tag{36.4}
$$

ready qubit 的 Hadamard—受控 $J$—Hadamard—计算基读出，恰给源 Kraus 算子 $\Pi_+^H,\Pi_-^H$。先追加 $0$ 即得 (36.2)，对有限参考的公式直接由张量恒等成立，不只对两个列出的纯态成立。不执行 $R_0^*$。在 $C'$ 上再次测量 $J$ 奇偶会重复同一符号；继续追加另一个 $0$ 不在这项重复性结论内。反转与控制读口是附加相干服务；相同模端点本身并不提供相位检测。

对于取等，用独立 ready 随机选择控制如下完整三结果仪器：

$$
K_{\mathrm{ret}}=\sqrt{1-\epsilon}\,I_H,\qquad
K_{\mathrm{grow},\pm}=\sqrt\epsilon\,\Pi_\pm^HR_0.
\tag{36.5}
$$

由于 $\Pi_+^H+\Pi_-^H=I_H$ 且 $R_0^*R_0=I_H$，这三项的 $K^*K$ 和恰为 $I_H$。在任何 $H_L$ 输入上，ret 分支保留原态，两个 grow 分支的总概率为 $\epsilon$ 且终长为 $L+1$。对 (36.1) 的相位对，按 $(\mathrm{ret},\mathrm{grow}+ ,\mathrm{grow}-)$ 排列的完整记录律为

$$
p_+=(1-\epsilon,\epsilon,0),\qquad
p_-=(1-\epsilon,0,\epsilon),\qquad V=\epsilon.
\tag{36.6}
$$

两态在对照菜单的零增长代数上已相同，故这也证明 (35.4) 在较强对照假设下的常数不能改进。该实现只用了最小菜单。在 $\epsilon=1$ 时是确定的移码相位测量；在 $\epsilon=0$ 时记录相同而源仍保留正交输入。将全部 Kraus 旗标相干保留的等距扩张保持输入正交；定理没有声称完整系统信息被抹去。$\square$

**定义 36.2（不同的资源坐标）。** (35.4)–(36.6) 的 $\epsilon$ 专指最终源块字长大于输入的概率。在本原生对应下，一个块字母是二十个原窗口。它不是离开某个右后代锥的概率，也不是控制器位数、隐藏环境维数、工作空间、可读记录宽度、熵或总物理成本。右后代锥为 $\{ws:s\in W\}$；反转可在不增长时离开一个这样的锥，故零增长与锥内保持不是同一条件。相反，追加会增长而仍留在该锥。这两个方向说明不能把此线性记录界替换到具有不同锥泄漏合同的平方根界中。

## 37. 同一小码的效果完备与同源门不可达并存

**定理 37.1（对照菜单中的 Z/X/Y 完备性及前向更新限制）。** 在假设 34.2 的对照菜单内，对同一个 $C$，实际有限仪器的效果实线性张成 $\operatorname{Herm}(C)$，而交换 $a,b$ 的同源门仍满足 (35.6)。具体令

$$
Z_C=|a\rangle\langle a|-|b\rangle\langle b|,\qquad
X_C=|a\rangle\langle b|+|b\rangle\langle a|,\qquad
Y_C=-i|a\rangle\langle b|+i|b\rangle\langle a|.
\tag{37.1}
$$

三种仪器分别在 $C$ 上给出 $(I_C\pm Z_C)/2$、$(I_C\pm X_C)/2$、$(I_C\pm Y_C)/2$ 的效果。其 X、Y 仪器输出位于明确的 $C'$，不是对原码上任意通道的合成结论。

证明。对照菜单授予的三结果源字投影仪器

$$
Q_a=|a\rangle\langle a|,\quad Q_b=|b\rangle\langle b|,\quad
Q_\perp=I_H-Q_a-Q_b
$$

以自身为 Kraus 算子，在 $C$ 上给出 Z 两效果，第三结果概率为零。定理 36.1 的仪器给出 X 两效果与实际分支 $EP_\pm^C\rho P_\pm^CE^*$。令全空间对角酉 $D$ 在 $b$ 上为 $-i$，其余字上为一。先施 $D$ 再施该移码仪器，实际 Kraus 算子为

$$
L_\pm=\Pi_\pm^HR_0D,\qquad
L_\pm|_C=EP_\pm^CD|_C,
\qquad (L_\pm|_C)^*(L_\pm|_C)=\frac{I_C\pm Y_C}{2},
\tag{37.2}
$$

因为 $D^*X_CD=Y_C$。其参考分支是 $(L_\pm\otimes I_R)\tau(L_\pm^*\otimes I_R)$，其输出仍在 $C'$；这条明确更新不被替换为同源 Y 的 Lüders 更新。于是 $I_C,X_C,Y_C,Z_C$ 均在效果张成中，四者为 $\operatorname{Herm}(C)$ 的实基，概率律唯一确定该码上的密度矩阵。这是 [V69 定理 5.6 的效果张成判据](AURIC_SHARED_HISTORIES_PROJECTION_TRIANGLES_AND_PROBABILITY_CLOSURE_V69.md#定理-56预测商与层析完备性) 在明确仪器上的应用；不是从一个未指定状态更新的 POVM 推出操作合成。对同一 $a,b$，反转轨道不同，故定理 35.2 排除同源交换，甚至允许增长输出与任意所授予对角操作也无帮助。$\square$

**命题 37.2（观测、更新与同一模型的边界）。** 定理 37.1 的效果完备性只保证完整概率律的可识别性；它不提供单次输入的全部概率、稳定重复制备、同源逆追加或任意源门。对任意已声明重复制备合同，概率估计问题仍依赖该合同，而 (36.2)、(37.2) 的 CP 更新及参考行为不依赖把记录概率当作一次样本。纯算术源也不是由上述操作障碍而被排除的经典模型。

证明。效果实基的配对给出密度矩阵四坐标，是对概率律的单射，不是把单个标签映到四个精确均值的逆函数；[V70 §3.3 与命题 3.5](AURIC_FIXED_READOUT_RELATIONAL_RECURSION_AND_QUADRATIC_ORIGIN_V70.md) 对样本、概率和指定更新作相同区分。任意门合成已被 (35.6) 的同一实际源反例否定。另一方面，$W$ 本身是两块的共同经典状态空间，其确定性转移 $w\mapsto wb$ 及算术坐标 (34.2) 同时存在；非交换的历史更新不否定这个经典模型。附加复 Hilbert、Born 与相干控制结构才使相位输入及其仪器有定义。$\square$

## 38. 同源对应及量子起源的未定桥梁

**定义 38.1（本应用的前提分层）。** 算术层仅含定义 34.1 的合法窗口、整数端点与其模商；复载体层另含不同端点的正交性和复叠加；概率层另含 Born 与完备 Kraus 仪器；操作层另含相干追加、受控反转、独立 ready 控制器及实际完整记录；对照层另含指定更新的对角仪器。这些层按假设 34.2 联合使用。要求从原生算术取得复数域、正交态可制备性、Born 概率、受控 $J$、独立 ready 记录、这些仪器的实际取得和校准，或粒子统计的起源，是额外待定桥梁，不是 (34.1)–(37.2) 已含的结论。

**命题 38.2（有限仪器对应不提供对角源菜单）。** 仓内 [DiagonalKrausInstrumentFactorization 的 `diagonal_instrument_factorization`](../../../D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.lean) 的对角输入因子分解条件，不足以推出 (34.6) 的反转轨道限制。假设 34.2 的对角源操作必须单独声明。

证明。该既有条件是对每个输入列 $i$ 和不同输出行 $o,o'$ 的聚合 Gram 和 $\sum_\mu K_\mu(o,i)\overline{K_\mu(o',i)}=0$，因此描述对角输入的经典权重演化，不要求每个 $K_\mu$ 为对角。任意基置换酉，包括交换 $a,b$，都把对角矩阵送到对角矩阵，因而满足该输入因子分解；此交换却跨越两个反转轨道。这一反例证明该条件不能替代实际源条目的菜单假设。$\square$

**命题 38.3（与经典不可改写记录障碍的非同一性）。** [《Recursive Relational Observation Atomic Generation Acquisition II》§100](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#100-a-native-obstruction-to-exact-width-immutable-history-records) 的源条件不可改写前缀障碍与 (35.4) 使用不同的源纤维、资源坐标及共同实现条件；它不是本处自由双块单射的直接实例。

证明。该节的已声明 LAB 只允许带地址叶编辑 $P_p:\alpha\mapsto\beta$、$S_p:\beta\mapsto\langle\beta,\alpha\rangle$，对同一当前有序源的完整历史纤维要求一个同时适用于每个未来的不可改写二进制补充。其 $U,V,T$ 纤维数为 $35,35,126$，精确位宽为 $6,6,7$。两个六位记录集合必有交叠，一个实际 $U$ 历史的两个未来与一个实际 $V$ 历史的一个未来在同一七位柱中需要三个位置，但只有两个；这是该节定理 100.3 的经典有限反例。

这里 $w\mapsto v_w$ 对完整自然端点单射，故固定自然端点的自由双块历史纤维至多一；模五纤维是另一个明确商，而不是上述 LAB 的完整端点纤维。此处 $\mathsf D$ 是量子源终长事件的效果，那里 $G(t)$ 是给定当前源后的历史补充位宽。没有给出把两种纤维、操作、仪器和资源坐标相互保持的映射，所以既有经典柱计数不能供应相干反转或量子最小追加成本，(35.4) 也不能被当作其位宽界。$\square$

**命题 38.4（条件应用的结论范围）。** 在精确有限菜单中，定理 34.3–37.1 同时给出零增长操作限制、完整记录与终长增长的线性界、原生取等以及同码效果完备与同源门不可达的并存。这些是关于同一实际源和所授予操作的条件结论；它们不推出每个 AURIC 扩展都服从同一菜单，也不推出全部量子基础原则的必要性。

证明。前述各定理的量词都限制在假设 34.2 的全局有限树及明确源生成元内。其自包含的源特定步骤为合法双块到自由字的单射、完整有限支撑对应、源分级对零增长块的限制，以及 $001,010$ 在同一模状态和一次追加后的反转配对。全 Fock 创生、Kraus/Born 边缘、两扇区 Schur 计算、效果张成判据及正交态距离作为既有中间工具按各条引文使用，不构成新的通用分类或文献优先权结论。

原单网格完整表问题 (18.1) 在 $d\ge2$ 的结论由定理 32.1、32.2、33.1 给出：$d=2,3$ 存在只依赖维数的统一常数，而每个固定 $d\ge4$ 都有反例。特别地，定理 33.1 对同一个原层析矩阵给出 $400000(\epsilon+2^{-m})$ 的三维全表界，不再留下三维分支；第 32 节末的未覆盖范围限于该节自身的结论。这些定理仍以完整效果表及其菜单关系为条件，不提供假设 34.2 中实际仪器、复叠加、Born 概率或相干控制的取得。

移除受控 $J$ 或复叠加前提后，(36.2) 的构造不再有同一合同；增加逆追加、重置或跨轨道源门后，(34.5) 的证明也不再适用。因而一组菜单内的反例不能给出撤去某项量子原则后所有模型都失败的全称结论，这正是 [V77 定义 1.1 的反向见证范围](AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)。其定理 10.1 的满锚覆盖不能由几个基概率替代；此处以完整源条目假设和分级证明承担该义务。完整系统保距与局部记录信息之别也与 [V78 定理 9.1 及 §9.1](AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md) 相容；(36.5) 说明记录距离如何带着分支权重变化，并未产生 ready 记录或概率律的来源。故定义 38.1 的取得桥梁仍为待定问题。$\square$

## 追加锚（本行以下为增补区）

## 39. 共同内部参照的有限轨道框架合同

**定义 39.1（同一实载体上的根、框架与全局比较）。** 设 $(V,g)$ 为非零有限维实内积空间，$D=\dim_{\mathbb R}V$。所有伴随、正性与算子范数均相对于同一个 $g$；$\|\cdot\|_{\mathrm{HS}}$ 为 Hilbert–Schmidt 范数。取实线性生成元 $A$、单位根向量 $\Omega_0$ 及带宽常数 $M$，满足

$$
A^*=-A,\qquad \|A\|\le M,\qquad
\|\Omega_0\|=1,\qquad \omega=\|A\Omega_0\|>0.
\tag{39.1}
$$

选定同一实际载体上的有限个正交运输 $U_i$、权重 $\alpha_i>0$，$\sum_i\alpha_i=1$，并给定共同轨道框架的下界 $\mu>0$ 及全局交换子界 $\epsilon_i\ge0$：

$$
x_i=U_i\Omega_0,\qquad
\mathsf F=\sum_i\alpha_i|x_i\rangle\langle x_i|
\succeq\mu I_V,\qquad
\|[A,U_i]\|\le\epsilon_i.
\tag{39.2}
$$

其中 $|x\rangle\langle x|$ 表示实秩一算子 $y\mapsto xg(x,y)$，$[S,T]=ST-TS$。框架条件等价于对每个 $y\in V$ 都有 $\sum_i\alpha_i g(x_i,y)^2\ge\mu\|y\|^2$；它要求这些实际运输后的输入共同覆盖全部方向，并给出覆盖的定量条件数，不是仅列举状态名称或断言轨道张成。定义同根残差与其传播预算

$$
\begin{aligned}
B&=A^2+\omega^2I_V,\qquad r=\|B\Omega_0\|,\\
\Delta&=\left(\frac1\mu\sum_i\alpha_i
                    (r+2M\epsilon_i)^2\right)^{1/2}.
\end{aligned}
\tag{39.3}
$$

这里 $\Omega_0$ 专指根向量。$\mu$ 约束同一组 $x_i$ 的全部实线性组合，$M$ 约束整个生成元，$\epsilon_i$ 约束整个载体上的两条路由 $AU_i$ 与 $U_iA$。单根速度、单根交换子或某个固定时刻的端点比较，均不替代这些不同量词的前件。

**定义 39.2（同根精确供应结果及其稳定化目标）。** [V78 二元失败续稿 §4.4 定理 4.5](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-5) 在 $A^*=-A$、全部运输与 $A$ 精确对易、单位根轨道张成且 $\omega>0$ 时给出

$$
\|(A^2+\omega^2I)\Omega_0\|=0
\quad\Longleftrightarrow\quad A^2=-\omega^2I_V.
\tag{39.4}
$$

该传播使用精确对易与定性张成。下面的应用以 (39.2) 的实际有限框架将非零根残差传播为统一算子界，再构造同一载体上的共同参照与门的比较算子。它没有把定性张成直接当成稳定性前件。

## 40. 从同根残差到复方向、实际参照流与有限门字的稳定比较

**定理 40.1（共同参照的有限框架稳定应用）。** 在定义 39.1 下，首先有

$$
\|A^2+\omega^2I_V\|\le\Delta.
\tag{40.1}
$$

若满足严格谱裕量

$$
\Delta<\omega^2,\qquad
 a=\sqrt{\omega^2-\Delta}>0,\qquad
\eta=\frac{\Delta}{\omega+\sqrt{\omega^2-\Delta}}
     =\omega-\sqrt{\omega^2-\Delta},
\tag{40.2}
$$

则同一实数据定义的

$$
P=(-A^2)^{1/2},\qquad \mathcal J=AP^{-1}
\tag{40.3}
$$

满足

$$
\mathcal J^*=-\mathcal J,\qquad
\mathcal J^2=-I_V,\qquad
\mathcal J^*\mathcal J=I_V,\qquad
\|A-\omega\mathcal J\|\le\eta.
\tag{40.4}
$$

因此 $D$ 为偶数，以下标量作用及内积在 $V$ 上给出对第二变量复线性的复 Hilbert 结构：

$$
(u+iv)x=ux+v\mathcal Jx,\qquad
h(x,y)=g(x,y)+i\,g(\mathcal Jx,y).
\tag{40.5}
$$

对于实际已给定的正交参照流 $R_t=e^{tA}$，令 $R_t^0=e^{\omega t\mathcal J}$、$t_*=\pi/(2\omega)$，则

$$
\begin{aligned}
\|R_t-R_t^0\|&\le\min\{2,|t|\eta\},\qquad t\in\mathbb R,\\
\|R_{t_*}-\mathcal J\|&\le
           \min\{2,\pi\eta/(2\omega)\}.
\end{aligned}
\tag{40.6}
$$

对任意同载体上的实线性算子 $U$，若 $\|[A,U]\|\le\epsilon$，则

$$
\|[\mathcal J,U]\|\le\epsilon/a.
\tag{40.7}
$$

若该 $U$ 还正交且 $b=\epsilon/(2a)<1$，置

$$
\begin{aligned}
U_c&=(U-\mathcal J U\mathcal J)/2,\qquad
U_a=(U+\mathcal J U\mathcal J)/2,\\
U^0&=U_c(U_c^*U_c)^{-1/2},\qquad
\chi(b)=b+1-\sqrt{1-b^2}.
\end{aligned}
\tag{40.8}
$$

则 $U^0$ 对 $g$ 正交、与 $\mathcal J$ 对易，因而对 $h$ 酉，并且

$$
\|U-U^0\|\le\chi(b).
\tag{40.9}
$$

对一条指定的有限门字，每次出现的正交门 $W_j$ 都有其全局界 $\|[A,W_j]\|\le\varepsilon_j$，$b_j=\varepsilon_j/(2a)<1$，则其相应比较门满足

$$
\|W_L\cdots W_1-W_L^0\cdots W_1^0\|
\le\min\left\{2,\sum_{j=1}^L\chi(b_j)\right\}.
\tag{40.10}
$$

所有比较均使用同一 $g,A,\Omega_0,\mathcal J$。式 (40.1) 是充分估计，不宣称必要或最优。

证明。先将根残差沿实际运输传播：

$$
\begin{aligned}
Bx_i&=U_iB\Omega_0+[A^2,U_i]\Omega_0,\\
[A^2,U_i]&=A[A,U_i]+[A,U_i]A,\\
\|Bx_i\|&\le r+2M\epsilon_i.
\end{aligned}
\tag{40.11}
$$

对于这些加权轨道向量，标准有限框架算子不等式给出

$$
\mu\|B\|_{\mathrm{HS}}^2
\le\operatorname{Tr}(B\mathsf F B^*)
=\sum_i\alpha_i\|Bx_i\|^2.
\tag{40.12}
$$

具体地，$B(\mathsf F-\mu I)B^*\succeq0$，取迹即得第一步；第二步逐项取实秩一算子的迹。再用 $\|B\|\le\|B\|_{\mathrm{HS}}$ 即得 (40.1)。框架的分析／合成与正框架算子是成熟工具，参见 O. Christensen, [An Introduction to Frames and Riesz Bases, 2nd ed.](https://doi.org/10.1007/978-3-319-25613-9)，关于 Hilbert 空间框架与框架算子的章节；本处将其用于 (40.11) 的同根路由残差，不另立一般框架定理。

若实际向量残差 $Bx_i$ 也已给定，令 $T:\mathbb R^n\to V$ 的第 $i$ 列为 $\sqrt{\alpha_i}x_i$，$Y=BT$。因为 $TT^*=\mathsf F\succeq\mu I$，$S=T^*\mathsf F^{-1}$ 满足 $TS=I$ 及 $S^*S=\mathsf F^{-1}$，故 $B=YS$ 给出更直接的

$$
\|B\|\le\|Y\|/\sqrt\mu.
\tag{40.13}
$$

式 (39.3) 以 $\|Y\|\le\|Y\|_{\mathrm{HS}}$ 忽略了不同残差向量间的有利关系。同一个论证还说明如何从完整框架上的路由比较取得前件：若 $\rho_{ij}\ge\|[A,U_i]x_j\|$，则

$$
\|[A,U_i]\|\le
\left(\frac1\mu\sum_j\alpha_j\rho_{ij}^2\right)^{1/2}.
\tag{40.14}
$$

这里确实需要每个 $x_j$ 上的联合路由 $AU_ix_j$ 与 $U_iAx_j$，不能只给 $[A,U_i]\Omega_0$。

由于 $-A^2=A^*A$ 为实对称正算子，(40.1) 与严格裕量给出

$$
a^2I\preceq-A^2\preceq(\omega^2+\Delta)I.
\tag{40.15}
$$

有限维实谱演算使 $P$ 正定且与 $A$ 对易；$A$ 可逆。于是直接相乘得到 (40.4) 的三个恒等式。这是实反对称算子的标准极分解：一般极分解与正规算子的极因子对易可参见 N. J. Higham, [Computing the Polar Decomposition—with Applications](https://eprints.maths.manchester.ac.uk/694/1/high86p.pdf), SIAM J. Sci. Stat. Comput. 7 (1986), 1160–1174，定理 1.1、引理 2.1，[DOI](https://doi.org/10.1137/0907079)。这些结果作为本应用的中间工具。

$P$ 的谱在 $[\sqrt{\omega^2-\Delta},\sqrt{\omega^2+\Delta}]$ 内。下端到 $\omega$ 的距离不少于上端到 $\omega$ 的距离，因为

$$
\sqrt{\omega^2-\Delta}+\sqrt{\omega^2+\Delta}\le2\omega.
$$

因此 $A=\mathcal JP$ 和 $\mathcal J$ 正交给 $\|A-\omega\mathcal J\|=\|P-\omega I\|\le\eta$。$\mathcal J^2=-I$ 使 $V$ 成为复向量空间，故 $D$ 偶数；$\mathcal J^*=-\mathcal J$ 给

$$
h(x,\mathcal Jy)=ih(x,y),\quad
h(\mathcal Jx,y)=-ih(x,y),\quad
h(y,x)=\overline{h(x,y)},\quad
h(x,x)=g(x,x).
$$

这正是 [V78 二元失败续稿 §4.2 推论 4.3](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-3) 的实—复构造；成熟一般对应另见 J. C. Baez, [Division Algebras and Quantum Theory](https://arxiv.org/abs/1101.5690)，定理 7。这里精确复方向由实际 $A$ 的极因子给定，而 $A$ 本身只与单频率生成元相差至多 $\eta$。

对 $t\ge0$，在同一实算子空间使用 Duhamel 恒等式：

$$
e^{tA}-e^{\omega t\mathcal J}
=\int_0^t e^{(t-s)A}(A-\omega\mathcal J)
                         e^{\omega s\mathcal J}\,ds.
$$

两侧的指数因子正交，故范数至多 $t\eta$；$t<0$ 对负生成元同理。两正交算子之差至多二。$e^{\pi\mathcal J/2}=\mathcal J$ 给 (40.6)。

为证明运输相容界，记 $E=[A,U]$、$C=\mathcal JU-U\mathcal J$。由 $A=\mathcal JP$、$P\mathcal J=\mathcal JP$ 及 $\mathcal J^2=-I$ 逐项展开可得

$$
PC+CP=E+\mathcal JE\mathcal J.
\tag{40.16}
$$

正定 Sylvester 方程的积分解在此为

$$
C=\int_0^\infty e^{-tP}(E+\mathcal JE\mathcal J)e^{-tP}\,dt.
\tag{40.17}
$$

对被积式求导后积分即验证该式；$P\succeq aI$ 保证无穷端消失。唯一性也可在 $P$ 的实正交特征基上逐项验证：每个矩阵元乘上两个正特征值之和。标准供应是 R. Bhatia–P. Rosenthal, [How and Why to Solve the Operator Equation AX−XB=Y](https://doi.org/10.1112/S0024609396001828), Bull. London Math. Soc. 29 (1997), 1–21；正稳定情形的积分解亦见 [Higham 的 Sylvester 方程说明](https://nhigham.com/2020/09/01/what-is-the-sylvester-equation/)。这里对应其一般形式中的两个系数 $P,-P$，谱由至少 $2a$ 的间隔分开。因为 $\|E+\mathcal JE\mathcal J\|\le2\epsilon$，积分范数至多

$$
\int_0^\infty2\epsilon e^{-2at}\,dt=\epsilon/a,
$$

得到 (40.7)，全过程不预设物理复载体。

最后，(40.8) 的 $U_c$ 与 $\mathcal J$ 对易，$U_a$ 与其反对易，并且

$$
\|U_a\|=\tfrac12\|[\mathcal J,U]\|\le b.
$$

将 $U^*U=I$ 的复线性部分取出；两个交叉项反复线性，得到

$$
U_c^*U_c+U_a^*U_a=I,\qquad
(1-b^2)I\preceq U_c^*U_c\preceq I.
\tag{40.18}
$$

因此 $U_c$ 可逆，其标准正交极因子 $U^0$ 与 $\mathcal J$ 对易，且对 $g$ 正交。由 (40.5) 它对 $h$ 酉。若 $Q=(U_c^*U_c)^{1/2}$，则 $U_c=U^0Q$，$\sqrt{1-b^2}I\preceq Q\preceq I$，所以

$$
\begin{aligned}
\|U-U^0\|&\le\|U_a\|+\|U_c-U^0\|\\
&=\|U_a\|+\|Q-I\|\le b+1-\sqrt{1-b^2}.
\end{aligned}
$$

这给出的是上述谱区间直接导出的算子范数界，不将 Higham 的 Frobenius 范数最优逼近定理改称同一估计。对有限门字逐项相减并用每个前后缀的正交性，得 (40.10)；再用两个正交乘积之差至多二即可。逆元也可一致处理：$[A,W^{-1}]=-W^{-1}[A,W]W^{-1}$，且 $W^{-1}$ 的复线性部分为 $W_c^*$，其极因子为 $(W^0)^*$。$\square$

## 41. 根残差、实际周期与比较门关系的三类边界

**定理 41.1（循环根可隐藏零频率方向）。** 令

$$
V=\mathbb R^3,\qquad
J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
A=J_0\oplus0,
$$

$$
G=SO(2)\times\{+1,-1\},\qquad
\Omega_\tau=(\sqrt{1-\tau^2}e_1,\tau),\quad0<\tau<1.
\tag{41.1}
$$

$G$ 与 $A$ 精确对易，根的 $G$ 轨道张成 $V$，但

$$
\omega^2=1-\tau^2,\qquad
r^2=\tau^2(1-\tau^2)\longrightarrow0.
\tag{41.2}
$$

当 $\tau<1/\sqrt2$ 时，$\|A^2+\omega^2I\|=\omega^2$；不存在正交复结构，任何有效统一上界都不能满足 (40.2)。取第一分量为 $\sqrt{1-\tau^2}e_1$ 或 $\sqrt{1-\tau^2}e_2$、最后分量为 $\pm\tau$ 的四个实际轨道点，等权框架算子为

$$
\mathsf F=\operatorname{diag}\bigl((1-\tau^2)/2,
                  (1-\tau^2)/2,\tau^2\bigr).
\tag{41.3}
$$

证明。四点的和差分别给出两个平面方向和第三轴，故根循环。$B=A^2+\omega^2I$ 在平面上为 $-\tau^2I$，在第三轴上为 $1-\tau^2$，代入根即得 (41.2) 及其算子范数。实奇维上 $\mathcal J^2=-I$ 不可能，因为取实行列式给 $\det(\mathcal J)^2=(-1)^3=-1$。四点的外积中混合项抵消，得到 (41.3)，其最小特征值趋于零。这是 (39.4) 的零残差传播与非零残差稳定传播的区别。$\square$

**定理 41.2（共同复方向不强制实际共同频率或精确周期）。** 在 $\mathbb R^4$ 上取参数 $0<\tau<1$，并令

$$
A=J_0\oplus\sqrt2J_0,\qquad G=SO(2)\times SO(2),\qquad
\Omega_\tau=(\sqrt{1-\tau^2}e_1,\tau e_1).
\tag{41.4}
$$

根循环，全部交换子为零，并且当 $\tau\to0^+$ 时，

$$
\omega^2=1+\tau^2,\qquad
r^2=\tau^2(1-\tau^2)\longrightarrow0,\qquad
\|A^2+\omega^2I\|\longrightarrow1.
\tag{41.5}
$$

它有极复结构 $J_0\oplus J_0$，但流 $e^{tA}$ 没有非零共同周期。即使保持良态框架及 (40.2)，仍可有任意小的 $\Delta>0$ 而没有非零共同周期。

证明。两个非零根分量可由独立平面转动张成两个整块。$B$ 的两块为 $\tau^2I$ 和 $-(1-\tau^2)I$，即得 (41.5)。共同周期 $T\ne0$ 将要求 $T\in2\pi\mathbb Z$ 且 $\sqrt2T\in2\pi\mathbb Z$，与频率比无理矛盾。

为验证严格裕量也不供应精确周期，另取 $q>1$ 无理且 $q\to1$，令 $A_q=J_0\oplus qJ_0$、$\Omega=(e_1,e_1)/\sqrt2$。在同一 $G$ 轨道中取八个点 $(s e_k,t e_k)/\sqrt2$，$k=1,2$，$s,t\in\{+1,-1\}$，等权得到 $\mathsf F=I_4/4$。此时 $M=q$、所有 $\epsilon_i=0$，并且

$$
\omega^2=(1+q^2)/2,\quad r=(q^2-1)/2,\quad
\Delta=q^2-1\longrightarrow0.
\tag{41.6}
$$

只要 $1<q<\sqrt3$ 就有 $\Delta<\omega^2$，但无理频率比仍排除非零共同周期。故 (40.6) 只保证指定时间范围的比较，不能把比较流的周期移给实际流。可见读出自身的周期另由 [V78 圆、周期与内生时钟续稿 §§5–7](AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md) 的可见频率及相应读出合同决定；共同标量相位圆也不等于改变纯态射线的 Bloch 球轨迹。$\square$

**定理 41.3（逐门极修复可破坏原来精确成立的关系词）。** 即使 (39.2) 的参照框架有 $\Delta=0$，并且有限个实际门的交换子误差任意小，定理 40.1 的逐门比较也不保证保留原门之间的全部精确群关系。

证明。在实 Euclidean 四元数空间 $V=\mathbb H$ 上，记 $L_qx=qx$、$R_qx=xq$。取 $A=L_{\mathbf i}$、$\Omega_0=1$，四个框架运输 $R_1,R_{\mathbf i},R_{\mathbf j},R_{\mathbf k}$ 等权。它们与 $A$ 精确对易，$\mathsf F=I_4/4$、$\omega=a=1$、$r=\Delta=0$，极复结构为 $\mathcal J=L_{\mathbf i}$。

令 $K=L_{\mathbf j}$、$N=L_{\mathbf k}$，则 $K^2=N^2=-I$、$KN=\mathcal J$，且 $K,N$ 均与 $\mathcal J$ 反对易。对 $0<\theta<\pi/4$ 置 $c=\cos\theta$、$s=\sin\theta$，取实际正交门

$$
U=cI+sK,\qquad V_1=cI+sN,\qquad W=(UV_1)^{-1}.
\tag{41.7}
$$

其关系 $WUV_1=I$ 精确成立。$U_c=(V_1)_c=cI$，故 $U^0=V_1^0=I$；但

$$
(UV_1)_c=c^2I+s^2\mathcal J,\qquad
W_c=c^2I-s^2\mathcal J,
$$

$$
W^0U^0V_1^0
=\frac{c^2I-s^2\mathcal J}{\sqrt{c^4+s^4}}\ne I.
\tag{41.8}
$$

其严格门裕量也全部成立：$U,V_1$ 的反复线性部分范数均为 $s<1$；$W$ 的为 $\sqrt2sc<1$，相应 $\epsilon=2\|U_a\|$ 等可随 $\theta\to0$ 趋零。这里用 $[\mathcal J,U]=2\mathcal JU_a$ 验证全局界。原来的精确关系词因而只得到 (40.10) 对修复后关系词到 $I$ 的距离界，不能得到距离零。四元数乘法只用于构造一个明确实四维反例，不改变 (40.5) 的标量选择。$\square$

## 42. 有限框架应用的维数与操作取得边界

**定理 42.1（归一化框架的维数界与非全群一致性）。** 在定义 39.1 下，$\mu\le1/D$。有限个轨道向量不能在无限维实 Hilbert 载体上满足 $\mathsf F\succeq\mu I$、$\mu>0$。若仅给定生成元门的交换子界，(40.10) 只控制指定的有限门字；它不提供所有字长上一致的小误差。

证明。全部 $x_i$ 为单位向量，故 $\operatorname{Tr}\mathsf F=\sum_i\alpha_i=1$；取 (39.2) 的迹得 $D\mu\le1$。无限维上有限个 $x_i$ 的张成有非零正交补，$\mathsf F$ 在该补上为零，直接违反正下界。对正交门 $S,T$，$[A,ST]=[A,S]T+S[A,T]$，故其交换子界按门字长度累加；(40.10) 的和同样随实际出现次数累加。具体地，在定理 41.3 中取 $\theta=\pi/n$、$n>4$，则 $\|[A,U]\|=2\sin(\pi/n)\to0$、$U^0=I$，但 $U^n=-I$，故 $\|U^n-(U^0)^n\|=2$。没有额外全群假设时，只有通用上界二，没有从有限生成元误差到所有门字统一趋零的结论。故增加定性张成的历史数目不产生与维数无关的证书，也没有由这些有限界推出无限历史极限。$\square$

**定义 42.2（比较算子与实际菜单）。** 实际可调用的操作菜单是另行指定的算子集合及其允许的组合、持续时间和读出。定理 40.1 的 $\mathcal J,U^0,R_t^0$ 是由 (39.1)–(39.3) 定义的比较结构，不因其存在就成为该菜单的成员。若实际菜单只给若干持续时间，$t_*=\pi/(2\omega)$ 的流值存在并不等于可调用该持续时间。框架输入的取得、共同内积比较、带宽和全局路由界仍各是明确前件。

**定理 42.3（复结构、原门、反转与概率层的非同一性）。** 定理 40.1 不使原实门自动复线性；其前件也没有给出 Born 概率律、CPTP 仪器或原生恢复操作。$\mathcal J$ 不等于第 34–38 节的字反转，定理也不提供共同运输交换子代数中全部复结构的唯一性。

证明。在定理 41.3 中，$0<\theta<\pi/4$ 时 $[\mathcal J,U]\ne0$，尽管该界可任意小，且参照本身已有精确 $\Delta=0$。因此原门不是 (40.5) 的复线性算子；它与酉比较门的距离小不自动把它变成复量子通道。前件仅包含实向量、线性映射和范数，没有概率赋值、效果读出或张量参考下的过程合法性，故这些另有合同的对象不由 (40.1)–(40.10) 指定。这里复结构的存在不充当 Born 或完全正性的证明。

第 34–38 节的字反转 $J_{\mathrm{word}}$ 满足 $J_{\mathrm{word}}^2=I$，本处 $\mathcal J^2=-I$。非零实载体上的可逆识别保持算子平方，不能将二者识别；它们原本也作用于不同的已声明接口。因此本构造不取得受控字反转、相干前缀查询、失败码解码或重试恢复，定义 38.1 的取得桥梁不因此闭合。

最后，$A$ 与 $\omega>0$ 固定后 (40.3) 的极因子已确定，但这不是对全部共同运输复结构的分类。例如 $\mathbb H$ 上的单位四元数左乘与不同的单位纯虚四元数右乘均对易，后者给出多种正交复结构。[V78 二元失败续稿 §4.3 定理 4.4](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-4) 另以不可约性及参考本身属于全部运输的中央参考前件得到唯一化；该额外工作没有由近似相容替代。上述稳定应用沿用框架、实谱演算、Sylvester 方程及正交极分解作为已归属的中间方法，其承重关系是同一实际轨道根残差与有限操作比较间的条件桥梁，不是这些通用方法的独立新分类或文献优先权主张。$\square$

## 追加锚（本行以下为增补区）

## 43. The actual skew-commutant interface for unchanged transports

**定义 43.1（Real carrier, actual generators and diagnostic gap）。** Let $(V,g)$ be a nonzero finite-dimensional real inner-product space, $N=\dim_{\mathbb R}V$. All adjoints and operator norms refer to $g$. Let $U_1,\ldots,U_m$ be actual orthogonal transports on this same carrier, with weights $\beta_s>0$, $\sum_s\beta_s=1$, and let $G$ be the group they generate. Its closure has the same commutant and invariant subspaces: commutation and invariance are closed conditions in finite dimension. Taking that closure is a mathematical description, not an additional operation in a control menu.

Use the real Hilbert space of skew operators

$$
\mathfrak s=\{T\in\operatorname{End}_{\mathbb R}(V):T^*=-T\},\qquad
\langle S,T\rangle_{\mathrm{HS}}=\operatorname{Tr}(S^*T).
\tag{43.1}
$$

Define $C_s(T)=U_sTU_s^*$ and the joint diagnostic interface

$$
\begin{aligned}
\mathscr D(T)&=\bigl(\sqrt{\beta_s}(I-C_s)T\bigr)_{s=1}^m,\\
\mathfrak c&=\ker\mathscr D
=\{T\in\mathfrak s:[T,U_s]=0\text{ for every }s\},\\
\mathscr L&=\mathscr D^*\mathscr D
=\sum_s\beta_s(2I-C_s-C_s^*)\succeq0.
\end{aligned}
\tag{43.2}
$$

Each $C_s$ is a Hilbert–Schmidt isometry of $\mathfrak s$, and $\ker\mathscr L=\mathfrak c$. If $\mathscr L\ne0$, let $\lambda>0$ be a certified lower bound on its spectrum on $\mathfrak c^\perp$; equivalently require

$$
\sum_s\beta_s\|[T,U_s]\|_{\mathrm{HS}}^2
\ge\lambda\|T\|_{\mathrm{HS}}^2
\quad(T\in\mathfrak s\cap\mathfrak c^\perp).
\tag{43.3}
$$

The residual equality follows from $(I-C_s)T=[T,U_s]U_s^*$. For each fixed nonzero finite diagnostic operator the smallest positive eigenvalue exists, but this does not supply a uniform lower bound for a varying family. This gap is a property of the joint constraints on skew matrices, not a lower frequency of a reference on $V$, an input-frame bound, or a physical mixing rate.

Let $A\in\mathfrak s$ be the actual reference generator, and suppose the full Hilbert–Schmidt residual bounds are

$$
\|[A,U_s]\|_{\mathrm{HS}}\le e_s,\qquad
\delta=\left(\frac{\sum_s\beta_s e_s^2}{\lambda}\right)^{1/2}.
\tag{43.4}
$$

Let $\Pi:\mathfrak s\to\mathfrak c$ be orthogonal projection and put $A_0=\Pi A$. When $\mathscr L=0$, use $A_0=A$ and $\delta=0$ directly; there is no division by a nonexistent positive eigenvalue. If $\mathfrak s=\{0\}$, then $A=0$ and neither nonzero-reference criterion below can hold. The projection may equivalently be written $\Pi=I-\mathscr D^+\mathscr D$ with the finite Moore–Penrose inverse. No physical pseudoinverse operation is included in this definition.

**定义 43.2（Supplier correspondence and the additional premise）。** [V78 binary-failure continuation §3.2, Theorem 3.4](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-3-4) bounds squared distance to a joint linear kernel by residual energy divided by its positive spectral gap. Here its variable is the skew operator $A$, its carrier is $\mathfrak s$, and its constraints are $(\sqrt{\beta_s}(I-C_s))_s$. The projected operator then meets the exact commutation premise of [the same supplier's §4.1, Theorem 4.2](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-2) when the actual real transport action is irreducible and the projected skew reference is nonzero. Sections 39–42 instead compare the original reference with a polar structure and nearby repaired gates. The present application keeps every $U_s$ and its product relations unchanged, using the additional actual joint diagnostic gap (43.3).

## 44. Exact common complex structure and quantitative reference comparison

**定理 44.1（Generator-gap application with unchanged transports）。** In Definition 43.1,

$$
\|A-A_0\|\le\|A-A_0\|_{\mathrm{HS}}\le\delta.
\tag{44.1}
$$

There are two sufficient routes to an exact common complex structure on the same actual carrier.

For the general-carrier route, assume a certified lower singular-value bound $a>0$ for $A$ and the strict margin

$$
\|Ax\|\ge a\|x\|\quad(x\in V),\qquad \delta<a.
\tag{44.2}
$$

Then $A_0$ is invertible, and

$$
P_0=(-A_0^2)^{1/2},\qquad J_0=A_0P_0^{-1}
\tag{44.3}
$$

satisfy

$$
J_0^2=-I,\quad J_0^*=-J_0,\quad J_0^*J_0=I,
\qquad [J_0,U]=0\quad(U\in G).
\tag{44.4}
$$

With $J=A(-A^2)^{-1/2}$ the polar structure of the original reference,

$$
\|J-J_0\|\le\frac{2\delta}{2a-\delta}.
\tag{44.5}
$$

For the alternative irreducible-carrier route, assume that the actual $G$ is real irreducible and that a unit root $\Omega_0$ satisfies

$$
\omega=\|A\Omega_0\|>\delta.
\tag{44.6}
$$

This route requires no known lower singular-value bound for $A$. There is $\nu>0$ with

$$
A_0^2=-\nu^2I,\qquad J_0=A_0/\nu,
\tag{44.7}
$$

and (44.4) holds. Moreover,

$$
|\nu-\omega|\le\delta,\qquad
\|A-\nu J_0\|\le\delta,\qquad
\|A-\omega J_0\|\le2\delta.
\tag{44.8}
$$

For the actual reference flow $R_t=e^{tA}$,

$$
\begin{aligned}
\|R_t-e^{\nu tJ_0}\|&\le\min\{2,|t|\delta\},\qquad t\in\mathbb R,\\
\|R_{\pi/(2\nu)}-J_0\|&\le\min\{2,\pi\delta/(2\nu)\}.
\end{aligned}
\tag{44.9}
$$

Under either route, $N$ is even and

$$
(u+iv)x=ux+vJ_0x,\qquad
h_0(x,y)=g(x,y)+i\,g(J_0x,y)
\tag{44.10}
$$

defines a complex inner product, linear in its second variable, for which every original $U\in G$ is unitary. All original products, inverses and exact relations hold for these same operators. Even without either nondegeneracy route, the projection estimate gives the whole-group bound

$$
\|[A,U]\|\le2\delta\qquad(U\in G).
\tag{44.11}
$$

If the preceding root/frame certificate supplies

$$
\|A^2+\omega^2I\|\le\Delta<\omega^2,\qquad
 a=\sqrt{\omega^2-\Delta},\qquad \eta=\omega-a,
\tag{44.12}
$$

and $\delta<a$, then the general route additionally gives

$$
\begin{aligned}
\|A_0-\omega J_0\|&\le\eta+\delta,\\
\|A-\omega J_0\|&\le\eta+2\delta,\\
\|e^{tA}-e^{\omega tJ_0}\|&\le
                 \min\{2,|t|(\eta+2\delta)\}.
\end{aligned}
\tag{44.13}
$$

This last route retains the original root-based frequency calibration without irreducibility. The diagnostic gap, the input-frame/root defect and the reference singular margin have distinct hypotheses and cannot substitute for one another. The general-carrier route permits multiple nonzero frequencies of $A_0$; irreducibility is what gives the single-frequency conclusion in (44.7). These are sufficient criteria, not a classification of every possible model.

Proof. The identity $\mathscr L=\mathscr D^*\mathscr D$ follows because the adjoint of each $C_s$ is its inverse. Its kernel is the common zero-residual space, as each summand in $\|\mathscr D(T)\|^2$ is nonnegative. Write $A=A_0+A_\perp$ in $\mathfrak c\oplus\mathfrak c^\perp$. Applying the supplier's Theorem 3.4 to precisely this interface gives

$$
\lambda\|A_\perp\|_{\mathrm{HS}}^2
\le\langle A,\mathscr LA\rangle_{\mathrm{HS}}
=\sum_s\beta_s\|[A,U_s]\|_{\mathrm{HS}}^2
\le\sum_s\beta_se_s^2.
\tag{44.14}
$$

The operator norm is at most the Hilbert–Schmidt norm, giving (44.1). If $\lambda$ is the least positive eigenvalue, its unit eigenvector attains the Hilbert–Schmidt distance inequality. No optimal operator-norm constant is asserted. When $\mathscr L=0$, the projection is the identity and (44.1) holds with $\delta=0$.

Under (44.2), $\|A_0x\|\ge(a-\delta)\|x\|>0$ for $x\ne0$. Thus $A_0$ is invertible. Its skew adjointness and real spectral calculus give (44.3)–(44.4). Each unchanged $U_s$ commutes with $A_0$, hence with $-A_0^2$, its positive square root and its inverse; this extends to every product and inverse. The polar and real spectral steps are mature tools; see N. J. Higham, [Computing the Polar Decomposition—with Applications](https://eprints.maths.manchester.ac.uk/694/1/high86p.pdf), SIAM J. Sci. Stat. Comput. 7 (1986), 1160–1174, Theorem 1.1 and Lemma 2.1, [DOI](https://doi.org/10.1137/0907079). They are intermediate steps in this actual-commutant application.

For clarity, the particular operator-norm polar comparison (44.5) follows from a self-contained Sylvester calculation. For invertible real maps $B=VP$, $C=WQ$ with orthogonal polar factors, put $E=B-C$ and $X=I-V^*W$. Direct expansion gives

$$
PX+XQ=V^*E-E^*W.
\tag{44.15}
$$

If $P\succeq pI$ and $Q\succeq qI$, $p,q>0$, its unique solution is

$$
X=\int_0^\infty e^{-tP}(V^*E-E^*W)e^{-tQ}\,dt.
\tag{44.16}
$$

Differentiating the integrand verifies the equation, and diagonalizing $P$ and $Q$ on the two sides gives uniqueness since every sum of eigenvalues is positive. Hence $\|X\|\le2\|E\|/(p+q)$. Apply this to $A,A_0$, with $p=a$, $q=a-\delta$, and use $\|J-J_0\|=\|I-J^*J_0\|$ to obtain (44.5). The standard integral method is credited to the Sylvester-equation framework of R. Bhatia–P. Rosenthal, [How and Why to Solve the Operator Equation AX−XB=Y](https://doi.org/10.1112/S0024609396001828), Bull. London Math. Soc. 29 (1997), 1–21; see also [Higham's integral-solution exposition](https://nhigham.com/2020/09/01/what-is-the-sylvester-equation/). This matrix integral is not an infinite-time physical operation, nor is (44.5) identified with Higham's Frobenius-norm approximation theorem.

Under the alternative (44.6), $\|A_0\Omega_0\|\ge\omega-\delta>0$, so $A_0\ne0$. The real self-adjoint operator $A_0^2$ commutes with $G$; all its eigenspaces are invariant. Real irreducibility makes it scalar. Since $-A_0^2=A_0^*A_0\succeq0$ and $A_0\ne0$, it equals $\nu^2I$ for some $\nu>0$. This is the skew-generator step of the supplier's Theorem 4.2, using the standard self-adjoint irreducibility argument, not a new real Schur theorem. Since $\|A_0\Omega_0\|=\nu$, comparison with $\|A\Omega_0\|=\omega$ gives the first bound of (44.8); (44.1) gives the second, and their triangle inequality gives the third. Irreducibility supplies an independent exact structural premise, not a consequence of small generator residuals.

In both routes the usual real complex-structure construction proves (44.10) and the evenness of $N$, exactly as in [the supplier's §4.2, Corollary 4.3](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-3); the mature general correspondence is also [Baez, Division Algebras and Quantum Theory, Theorem 7](https://arxiv.org/abs/1101.5690). In particular $h_0(x,x)=g(x,x)$ and $h_0(x,J_0y)=ih_0(x,y)$. Orthogonality and exact commutation with $J_0$ give $h_0(Ux,Uy)=h_0(x,y)$. No gate is repaired. For any $U\in G$, $[A,U]=[A-A_0,U]$ and $\|U\|=1$ give (44.11). Its lack of a word-length factor comes from the stronger distance-to-common-commutant input, not from adding separate small generator estimates.

Duhamel's identity for the two orthogonal flows gives (44.9), using $A_0=\nu J_0$ and (44.1); differences of orthogonal maps have norm at most two. At $t=\pi/(2\nu)$ the comparison exponential equals $J_0$. This remains an estimate for the actual flow at a specified duration, not an assertion that this duration is callable.

Finally, (44.12) bounds the singular values of $A$ between $a$ and $\sqrt{\omega^2+\Delta}$. The elementary bounds $\|A_0x\|\ge\|Ax\|-\delta\|x\|$ and $\|A_0x\|\le\|Ax\|+\delta\|x\|$ place the singular values of $A_0$ in

$$
[a-\delta,\sqrt{\omega^2+\Delta}+\delta].
$$

The lower-end deviation of the unperturbed interval from $\omega$ is the larger one, as in the proof of Theorem 40.1. Thus $\|P_0-\omega I\|\le\eta+\delta$ and $A_0=J_0P_0$ give the first bound of (44.13); (44.1) gives the second, and Duhamel's identity the third. Actual directional residual data may improve the certified operator bound in (44.1), but this proof uses only the stated $\delta$.

For actual probe certificates, global operator-norm readings $\|[A,U_s]\|\le\epsilon_s$ can supply the Hilbert–Schmidt bounds $e_s=\sqrt N\,\epsilon_s$, hence the valid choice

$$
\delta_{\mathrm{op}}=
\left(\frac{N}{\lambda}\sum_s\beta_s\epsilon_s^2\right)^{1/2}.
\tag{44.17}
$$

Alternatively let actual unit probe vectors $x_j$ and positive weights $\alpha_j$, $\sum_j\alpha_j=1$, on the same carrier satisfy $\mathsf F=\sum_j\alpha_j|x_j\rangle\langle x_j|\succeq\mu I$, $\mu>0$. If $\rho_{sj}\ge\|[A,U_s]x_j\|$, the same trace argument as (40.12) gives

$$
\begin{aligned}
\mu\|[A,U_s]\|_{\mathrm{HS}}^2
&\le\sum_j\alpha_j\rho_{sj}^2,\\
\delta_{\mathrm{frame}}&=
\left(\frac{\sum_{s,j}\beta_s\alpha_j\rho_{sj}^2}
{\lambda\mu}\right)^{1/2}.
\end{aligned}
\tag{44.18}
$$

Thus $\delta_{\mathrm{frame}}$ is another valid input to Theorem 44.1. These are standard finite-frame and Hilbert–Schmidt estimates used inside the transport application, with the dimensional factor retained in (44.17); the frame supplier is [Christensen, An Introduction to Frames and Riesz Bases](https://doi.org/10.1007/978-3-319-25613-9). A root-only commutator test does not give (44.18).

The generator maps, their exact joint kernel and an actual lower bound on its complement remain inputs. A nominal positive gap for rounded matrices does not transfer to the actual interface without control of changes in the kernel: an exact fixed direction can disappear and become a new arbitrarily small positive eigenvalue. The theorem supplies neither a finite-precision zero test nor a native or efficient gap-acquisition protocol. $\square$

## 45. A real QZX instance with exact gap 4/3 and a menu-sensitive echo

**定理 45.1（Exact diagnostic gap, unchanged finite transports and the qualified echo construction）。** On the real Euclidean space $V=\mathbb R^2\oplus\mathbb R^2$, define

$$
\begin{gathered}
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
J_c=\begin{pmatrix}J_2&0\\0&J_2\end{pmatrix},\qquad
Q=(I_4+\sqrt3J_c)/2,\\
Z=\begin{pmatrix}I_2&0\\0&-I_2\end{pmatrix},\qquad
X=\begin{pmatrix}0&I_2\\I_2&0\end{pmatrix}.
\end{gathered}
\tag{45.1}
$$

Take the actual generators $(Q,Z,X)$ with equal weights $1/3$. Their action is real irreducible, their full real commutant is $\mathbb RI_4+\mathbb RJ_c$, their skew commutant is $\mathbb RJ_c$, and the least positive diagnostic eigenvalue is

$$
\lambda_+=4/3.
\tag{45.2}
$$

For $0<\rho<1$, let the actual skew reference and unit root be

$$
A_\rho=\operatorname{diag}(J_2,(1+\rho)J_2),\qquad
\Omega_0=e_1.
\tag{45.3}
$$

Its commutators with $Q,Z$ vanish; its commutator with $X$ has operator norm $\rho$ and Hilbert–Schmidt norm $2\rho$. Consequently (43.4) gives $\delta=\rho<\omega=1$, while the exact projection is

$$
A_0=(1+\rho/2)J_c,\qquad
\|A_\rho-A_0\|=\rho/2,\qquad
\|A_\rho-A_0\|_{\mathrm{HS}}=\rho.
\tag{45.4}
$$

The finite group-word menu generated solely by $Q,Z,X$ contains no $J_c$. If, in addition, arbitrary real durations of the actual reference flow $R_t=e^{tA_\rho}$ and the gate $X$ are callable, the larger menu does implement the exact echo

$$
e^{tA_0}=R_{t/2}X R_{t/2}X\qquad(t\in\mathbb R).
\tag{45.5}
$$

In particular, with $\nu=1+\rho/2$ and $t=\pi/(2\nu)$ this echo equals $J_c$, using two actual reference durations $\pi/(4\nu)$. This positive construction concerns this example and its additional duration contract. If $\rho$ is irrational, the original reference flow nevertheless has no nonzero operator period, while its comparison flow has period $2\pi/\nu$.

Proof. All matrices in (45.1) are real orthogonal, $Q^3=-I_4$ and $Q^6=I_4$. Since $J_c=(2Q-I_4)/\sqrt3$, a real map commutes with $Q$ exactly when it commutes with $J_c$. Commutation also with $Z$ makes it block diagonal, with each two-dimensional block commuting with $J_2$ and hence of the form $a_jI_2+b_jJ_2$. Commutation with $X$ equates the blocks. This proves the two commutant statements. An invariant real subspace would have a commuting orthogonal projection, whose skew coefficient must vanish in this algebra and whose scalar coefficient is zero or one. Thus the real action is irreducible.

Conjugation by $X$ and by $Z$ gives commuting self-adjoint involutions on $\mathfrak s$: $XZ=-ZX$, and the scalar sign disappears under conjugation. Their common fixed space in $\mathfrak s$ is already $\mathbb RJ_c$, because a skew map commuting with $Z$ is block diagonal and commuting with $X$ equates its two skew two-dimensional blocks. On the orthogonal complement, their contribution to $\mathscr L$ has eigenvalues $4/3$ or $8/3$. The $Q$ contribution is positive and annihilates $\mathbb RJ_c$, so $\lambda_+\ge4/3$. The nonzero skew map $J_cZ$ is fixed by conjugation with $Q,Z$ and negated by conjugation with $X$; it attains $4/3$, proving (45.2).

The commutator with $X$ has two off-diagonal blocks $\pm\rho J_2$, giving its stated two norms. Substitution into (43.4) gives $\delta=\sqrt{(4\rho^2/3)/(4/3)}=\rho$. Orthogonal projection of $A_\rho$ onto $\mathbb RJ_c$ averages the two frequencies, and the two diagonal error blocks are $\pm(\rho/2)J_2$. This proves (45.4), a nonzero instance of the irreducible criterion obtained from wholly real matrix data, with every actual transport relation retained.

For the finite-word assertion, $Q$ is central and $XZ=-ZX=Q^3ZX$, so every word in $Q,Z,X$ and their inverses has form

$$
Q^kX^uZ^v,\qquad k\in\mathbb Z,\quad u,v\in\{0,1\}.
\tag{45.6}
$$

If $u$ or $v$ is nonzero its block-index matrix is not scalar, so it cannot equal $J_c$. If both vanish, its common internal rotation angle is $k\pi/3$, which is never $\pi/2$ modulo $2\pi$. Thus the no-command conclusion applies precisely to this finite QZX word menu; it is not a conclusion about every menu containing a callable reference flow.

For that stronger menu, direct block multiplication gives

$$
XA_\rho X=\operatorname{diag}((1+\rho)J_2,J_2),\qquad
[A_\rho,XA_\rho X]=0,\qquad
(A_\rho+XA_\rho X)/2=A_0.
$$

Since $X^2=I$, $XR_{t/2}X=e^{(t/2)XA_\rho X}$. Commutation of the displayed two generators then proves (45.5). The quarter-turn duration follows from $A_0=\nu J_c$. No controlled-$Q$ synthesis or general acquisition theorem is used here.

Finally, a nonzero period $T$ of $e^{tA_\rho}$ would require both $T$ and $(1+\rho)T$ in $2\pi\mathbb Z$, impossible for irrational $\rho$. The comparison generator has the single frequency $\nu$. This is the phase-versus-commensurability distinction of [V78 circles, periods and endogenous clocks, Theorem 5.1 and §5.2](https://github.com/the-omega-institute/trureturing/blob/615d1d58b1cf668e5979245ecb6bdc9ac5ec1525/docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md). Its Theorem 7.1 separately characterizes visible-readout periods. $\square$

## 46. A nondegenerate single-frequency reference with no common complex structure

**定理 46.1（Small individual generator defects do not replace the joint gap）。** On $\mathbb R^4$ let $E_{ij}$ be the coordinate matrix units, $L_{1j}=E_{j1}-E_{1j}$ for $j=2,3,4$, and

$$
U_j(\theta)=e^{\theta L_{1j}},\qquad
0<\theta<\pi,\qquad A=J_2\oplus J_2.
\tag{46.1}
$$

The reference satisfies $A^2=-I_4$, has least singular value one, and for every unit root $\Omega_0$ has $\omega=1$ and zero root frequency residual. Yet

$$
\|[A,U_j(\theta)]\|
\le2\|U_j(\theta)-I\|
=4\sin(\theta/2)\longrightarrow0\quad(\theta\to0^+).
\tag{46.2}
$$

For every such $\theta$, the actual generated action is real irreducible, its full real commutant is $\mathbb RI_4$, and its skew commutant is zero; hence no complex structure commutes with all its transports. For fixed positive weights $\beta_j$ summing to one, its least positive diagnostic eigenvalue obeys

$$
\lambda_+(\theta)
\le\frac{\sum_j\beta_j\|[A,U_j(\theta)]\|_{\mathrm{HS}}^2}{4}
\longrightarrow0.
\tag{46.3}
$$

Every valid $\delta$ from (43.4) is at least two, so neither $\delta<a=1$ nor $\delta<\omega=1$ holds.

Proof. A real map $T$ commuting with $U_j(\theta)$ also commutes with its inverse $U_j(\theta)^*$, and therefore with

$$
L_{1j}=\frac{U_j(\theta)-U_j(\theta)^*}{2\sin\theta},\qquad
-L_{1j}^2=E_{11}+E_{jj}.
\tag{46.4}
$$

The simultaneous eigenspaces of the three diagonal projections on the right are exactly the four coordinate lines, with membership patterns $(1,1,1)$, $(1,0,0)$, $(0,1,0)$, $(0,0,1)$. Thus $T$ is diagonal. Commuting with each $L_{1j}$ equates its first and $j$th diagonal entries, making $T$ scalar. Its skew part is consequently zero and cannot contain a map squaring to $-I$. The same invariant-subspace orthogonal-projection argument proves real irreducibility. Every nonzero root is cyclic because the real span of its group orbit is a nonzero invariant subspace.

The stated reference properties follow from $A^2=-I_4$. Its norm is one, so $[A,U_j]=[A,U_j-I]$ gives the inequality in (46.2); the norm of a plane rotation minus the identity is $2\sin(\theta/2)$. Here $\Pi A=0$ and $\|A\|_{\mathrm{HS}}=2$. The Rayleigh quotient at $A$ gives (46.3), and its numerator tends to zero by $\|T\|_{\mathrm{HS}}\le2\|T\|$ in dimension four. For each fixed $\theta$ the skew kernel is zero, so the positive diagnostic spectrum is nonempty. Equation (44.1) then forces $\delta\ge\|A-\Pi A\|_{\mathrm{HS}}=2$. This gives a concrete obstruction to removing the gap even with an exactly nondegenerate, exactly single-frequency reference and a cyclic root. Real irreducibility does not make small commutators exact. $\square$

## 47. Exact compatibility, operation menus and the remaining interfaces

**定义 47.1（Geometric reconstruction and acquisition are separate contracts）。** The data in Definition 43.1 include an actual finite real carrier, its common inner product, the same actual orthogonal generators, a skew reference, their exact joint kernel, a certified gap on its complement, and either (44.2) or (44.6). Acquiring or calibrating those data is a separate source obligation. A word-history carrier is not identified with $V$ by matching a dimension. A menu of callable operations must additionally specify available maps, controls, durations and readouts. Algebraically defined projection and polar maps are not inserted into that menu by definition; Theorem 45.1 supplies an exact echo only under its explicitly stronger duration contract.

**定理 47.2（Scope of the unchanged-transport conclusion）。** Theorem 44.1 establishes exact complex linearity and unitarity of the original transports under its stated real hypotheses. It does not classify all commuting complex structures, derive a Born probability law or complete instruments, supply ready records or native recovery, or assert an infinite-carrier limit.

Proof. The same original $U_s$ commute with $J_0$, and (44.10) changes the scalar description on the same real space; it does not change the maps or any of their product identities. By contrast, it supplies no probability assignment, effect menu, tensor-reference process contract, or control primitive. Accordingly Born probabilities, CPTP instruments, independent ready records, coherent prefix access, word reversal and failure-code recovery require their own specified interfaces, as in §§34–38 and [the clocks continuation §11.3](https://github.com/the-omega-institute/trureturing/blob/615d1d58b1cf668e5979245ecb6bdc9ac5ec1525/docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md). The operator $J_0^2=-I$ is different from the eraser interface's word reflection with square $I$. Central reference phase also preserves pure-state rays; it is not a trajectory moving a ray on the Bloch sphere.

A fixed projected $A_0$ determines its polar factor, but does not imply uniqueness among all complex structures commuting with $G$. Quaternionic alternatives retain the extra central-reference issue in [V78 binary-failure continuation §4.3, Theorem 4.4](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-4), whose irreducibility and reference-membership hypotheses do separate work. No unbounded word-program approximation or infinite-carrier extension is used in any argument here.

Projection onto a linear kernel, its positive-gap bound, polar decomposition, the Sylvester integral and the self-adjoint irreducibility step remain credited intermediate tools. Their application here relates actual generator defects to exact compatibility with unchanged transports, with the real QZX gap certificate, the menu-sensitive echo and the degenerating-gap obstruction. These applications do not assert novelty of those general tools or literature priority. $\square$

## 追加锚（本行以下为增补区）

## 48. 四维严格秩一桥与十一行列式残差

**引理 48.1（四维 Gaussian 格的秩一抽取阈值）。** 令 $R=\mathbb Z[i]$。若 $H\in\operatorname{Herm}_r(R)$ 为正定，且 $1\le r\le3$，则存在 $0\ne q\in R^r$ 使

$$
q^*H^{-1}q\le1,\qquad 0<qq^*\le H.
\tag{48.1}
$$

当 $r=4$ 时，同一结论在 $\det H\ge12$ 时成立。

**证明。** 令 $D=\det H$。在实化的对偶格 $H^{-1}R^r$ 上使用 Hermitian 范数。其欧氏余体积为 $D^{-1}$，故普通实 Hermite 界给出某个非零 $q\in R^r$ 满足

$$
q^*H^{-1}q\le\gamma_{2r}D^{-1/r}.
\tag{48.2}
$$

置 $a=Dq^*H^{-1}q=q^*\operatorname{adj}(H)q\in\mathbb Z_{>0}$。对于 $r=2,3$，已有式 (33.5) 及其后的整数性计算给出 $a<D+1$，因而 $a\le D$。$r=1$ 时取 $q=1$ 即可。

当 $r=4$ 时，普通实常数 $\gamma _8=2$。Vance，[A Mordell Inequality for Lattices over Maximal Orders](https://arxiv.org/html/0810.2336v5)，§4.2 的 Table 3 在实维数 $8$ 列出 $E_8$ 的 Hermite 不变量 $2$，并在该表说明中明确指出维数不超过 $8$ 的这些格已证明为普通实格最优；因此这里使用的是全部实八维格的界，而非仅对某个 Gaussian 子类的猜测。若 $D\ge16$，则 $2D^{3/4}\le D<D+1$；对 $D=12,13,14,15$ 直接有 $2D^{3/4}<D+1$。由 (48.2)，$a\le2D^{3/4}<D+1$，故仍有 $a\le D$。

最后，对任意 $z\in\mathbb C^r$，$H$-内积的 Cauchy 不等式给出

$$
|q^*z|^2\le(q^*H^{-1}q)(z^*Hz)\le z^*Hz,
$$

即 $0<qq^*\le H$。$\square$

**引理 48.2（严格秩一效果的同网格奇偶完成）。** 在定义 16.1 的 $d=4$ 网格中，令 $e(Y)=p(Y)-\operatorname{Tr}(HY)$。当 $N=2^m\ge2048$ 时，每个秩一效果 $X\in K_{4,m}$ 且 $\|X\|_{\rm op}<1$ 都满足

$$
|e(X)|\le53142\,\epsilon.
\tag{48.3}
$$

**证明。** 记 $\pi=1+i$。沿用定义 16.1 和定理 24.1 的常数

$$
 c_4=\frac1{52},\qquad K_4=102,\qquad
 U_4=(2\cdot128-1)K_4+4(128-1)=26518.
\tag{48.4}
$$

因此 $\|Y\|_{\rm op}\le c_4$ 时 $|e(Y)|\le102\epsilon$，而
$\|Y\|_{\rm op}\le1-16/N$ 时 $|e(Y)|\le26518\epsilon$.

由 §§31–33 使用的饱和子模论证，存在本原 $v\in R^4$ 和整数 $t\ge1$ 使

$$
X=\frac{t\,vv^*}{N},\qquad s=\|v\|^2,\qquad ts<N.
\tag{48.5}
$$

若 $t\ge2$，把 $t=t_1+t_2$ 分成两个正整数且 $t_i\le\lceil t/2\rceil$。两个子效果的范数严格小于 $2/3$, 因为 $\lceil t/2\rceil/t\le2/3$；它们及其和仍在原网格中。由于 $N\ge2048$, 它们满足上侧条件 $\|Y\|\le1-16/N$。式 (16.4) 遂给出

$$
|e(X)|\le2U_4\epsilon+2\epsilon=53038\epsilon.
\tag{48.6}
$$

以下设 $t=1$, 于是 $s<N$。对 $v_j\equiv0\pmod\pi$ 的坐标置 $w_j=0$，对其余坐标取 Gaussian 单位 $w_j\in\{1,-1,i,-i\}$，并记 $r=\|w\|^2$。本原性给出 $1\le r\le4$，且 $r\equiv s\equiv k\pmod2$, 其中 $k=N-s\ge1$；同时 $w\equiv v\pmod\pi$。

若 $r\le k$, 则 $vv^*+ww^*\le(s+r)I_4\le NI_4$。只有两种情形需要改选单位相位：

* $k=1,r=3$. 三个非零坐标记为 $\alpha_j=\overline v_jw_j$. 先选两个单位使 $\operatorname{Re}(\alpha_1\overline{\alpha_2})\le-1$, 再用第三个单位的相反两相之一使 $\operatorname{Re}((\alpha_1+\alpha_2)\overline{\alpha_3})\le0$. 于是
  $|v^*w|^2\le s-2=N-3=k(N-r)$.
* $k=2,r=4$. 对前两个坐标作同样的选择；随后逐次在相反两相中选择，使每次新增项与当前和的实部不正。于是
  $|v^*w|^2\le s-2=N-4\le2(N-4)=k(N-r)$.

在两种例外中，矩阵 $C=(v\;w)$ 的 Gram 矩阵满足

$$
C^*C\le NI_2,\qquad\text{hence}\qquad vv^*+ww^*=CC^*\le NI_4.
\tag{48.7}
$$

令 $u=(v+w)/\pi$, $z=(v-w)/\pi$, 以及

$$
W=\frac{ww^*}{N},\qquad F=\frac{uu^*}{N},\qquad G=\frac{zz^*}{N}.
$$

则这些矩阵和共同和均属原 $K_{4,m}$，并且

$$
X+W=F+G\le I_4.
\tag{48.8}
$$

此外 $\|W\|=r/N\le4/N\le c_4$, 而

$$
\max(\|F\|,\|G\|)\le\frac{(\sqrt{N-1}+2)^2}{2N}\le\frac34\le1-\frac{16}{N}\qquad(N\ge2048).
\tag{48.9}
$$

对 (48.8) 使用四项关系式 (33.4)，再使用 (48.4) 的局部与上侧估计，得到

$$
|e(X)|\le(102+2\cdot26518+4)\epsilon=53142\epsilon.
$$
$\square$

**定理 48.3（严格收缩效果的十一行列式残差分解）。** 令 $N=2^m$，$A\in\operatorname{Herm}_4(R)$ 满足 $A\succeq0$ 且 $A\prec NI_4$。则存在有限个非零 $v_j\in R^4$ 以及一个矩阵 $G$，使

$$
A=\sum_{j=1}^{\ell}v_jv_j^*+G,
\tag{48.10}
$$

并且 $G=0$, 或者 $G\succ0$、$\det G\le11$, 且

$$
\{X\in\operatorname{Herm}_4(R):0\le X\le G\}=\{0,G\}.
\tag{48.11}
$$

**证明。** 对任意半正定积分矩阵 $B$，其积分核是饱和 $R$-子模；取 Gaussian 幺模坐标后

$$
V^*BV=\begin{pmatrix}J&0\\0&0\end{pmatrix},\qquad J\succ0.
\tag{48.12}
$$

若 $\operatorname{rank}B\le3$, 引理 48.1 在正定块 $J$ 上给出一个非零积分秩一子效应，拉回后得到 $0<vv^*\le B$. 对秩四的 $B$, 同样可做此事，只要 $\det B\ge12$。每次减去 $vv^*$ 后仍为积分半正定矩阵，而迹至少减少 $1$, 所以这个过程在有限步后停止于 $0$ 或一个正定矩阵 $G$ 满足 $\det G\le11$ 且不含非零积分秩一子效应。

说明最后的 $G$ 必为区间原子。若存在 $0<X<G$ 的积分 Hermitian 矩阵，置 $Y=G-X$. 若 $X$ 或 $Y$ 奇异且非零，则秩至多三的情形已经给出一个 $vv^*\le X$ 或 $vv^*\le Y$, 与停止条件矛盾。若二者均正定，则 Minkowski 行列式不等式给出

$$
\det(G)^{1/4}\ge\det(X)^{1/4}+\det(Y)^{1/4}\ge2,
$$

因为正定积分矩阵的行列式是正整数；这与 $\det G\le11$ 矛盾。因此 (48.11) 成立。若过程在某一步降为奇异矩阵，秩至多三的抽取会继续到零，故非零余项必为正定。式 (48.10) 遂得证。$\square$

**定理 48.4（原网格严格收缩目标的有界残差归约）。** 设 $N\ge2048$, $E\in K_{4,m}$ 且 $\|E\|_{\rm op}<1$. 令 $A=NE$, 并取定理 48.3 的分解。置

$$
Q_j=\frac{v_jv_j^*}{N},\qquad G_0=\frac GN,\qquad
 e(G_0)=\begin{cases}p(G_0)-\operatorname{Tr}(HG_0),&G\ne0,\\ p(0),&G=0.\end{cases}
$$

则所有 $Q_j,G_0$ 及其任意部分和都属于原 $K_{4,m}$，并存在一个仅依赖于上述常数的显式界

$$
|e(E)-e(G_0)|\le902824\,\epsilon.
\tag{48.13}
$$

**证明。** 由 $0\le G\le A<NI_4$, 每个 $Q_j$ 及 $G_0$ 都是原网格中的效果，且所有部分和仍不超过 $E$. 记 $\operatorname{tr}(Q_j)=\|v_j\|^2/N$. 将迹大于 $1/3$ 的单项列为大项；至多 $11$ 项。其余单项的迹至多 $1/3$, 按原顺序累积成若干组，每个完成组的迹属于 $[1/3,2/3)$, 最后未完成组的迹小于 $1/3$. 因 $\operatorname{Tr}(E)\le4$, 这样的组至多 $12$ 个。记大项数和小组数分别为 $L\le11$ 与 $M\le12$.

每个大项是严格秩一效果：若某个 $Q_j$ 有范数 $1$, 则 $Q_j\le E$ 会迫使 $\|E\|\ge1$, 与假设矛盾。因此引理 48.2 给出其误差至多 $53142\epsilon$. 每个小组 $B_\nu$ 是一个原网格效果，且

$$
\|B_\nu\|\le\operatorname{Tr}(B_\nu)<\frac23\le1-\frac{16}{N},
$$

所以定理 24.1 给出 $|e(B_\nu)|\le26518\epsilon$。由 (16.4) 逐项相加，至多 $L+M\le23$ 次，得

$$
\begin{aligned}
|e(E)-e(G_0)|
&\le 11\cdot53142\,\epsilon+12\cdot26518\,\epsilon
   +2\cdot23\,\epsilon\\
&=902824\,\epsilon.
\end{aligned}
$$
当 $G=0$ 时，首项是 $e(0)=p(0)$，而 $0\le p(0)\le2\epsilon$；这正是上式中允许的零项。$\square$

**推论 48.5（严格收缩范围内四维二次裕量归约的剩余义务）。** 本归约继承定理 48.4 的条件 $N\ge2048$, $E\in K_{4,m}$ 且 $\|E\|_{\rm op}<1$；原下侧分支中范数等于 $1$ 的效果不在此直接归约的适用范围内。引理 48.2 和定理 48.4 只移除原事件中的秩一贡献；它们没有证明原事件。若 $E$ 还满足原显示的二次谱析取

$$
\lambda_{\max}(E)\le1-A N^{-2}\quad\text{或}\quad
\lambda_{\min}(E)\ge A N^{-2},\qquad A>2,
\tag{48.14}
$$

则仍须对定理 48.3 产生的单个正定区间原子 $G_0=G/N$ 建立一个统一的、与 $N,\epsilon,p$ 无关的常数 $C_{\rm atom}$，使

$$
|e(G_0)|\le C_{\rm atom}(\epsilon+N^{-1}).
\tag{48.15}
$$

当 $G=0$ 时 (48.15) 按 $|e(0)|=p(0)\le2\epsilon$ 解释。上侧条件在 $G_0\le E$ 时可传给 $G_0$,但下侧条件一般不能由 $G_0\le E$ 传递；所以 (48.15) 必须覆盖由原下侧分支产生的原子，而不能把定理 24.1 的线性裕量误称为二次裕量结论。因此，式 (48.15) 的统一原子估计与完整的二次裕量结论仍未由本节的部分结果证明。$\square$

本节的新增承重是四维原 Gaussian 网格上的严格秩一同网格完成、以及把任意严格收缩效果归约为至多一个行列式不超过 $11$ 的正定区间原子并给出有界表误差；式 (48.14)–(48.15) 保留原事件的量词和未决边界。Hermite 常数、Minkowski 行列式不等式、Gaussian 饱和子模与既有 §§31–33 的原语只作为证明中的明确中间工具使用，不把它们另列为新结论。

## 追加锚（本行以下为增补区）
