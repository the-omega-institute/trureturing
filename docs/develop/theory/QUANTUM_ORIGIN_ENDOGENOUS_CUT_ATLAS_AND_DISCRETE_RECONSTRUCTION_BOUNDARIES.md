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

## 13. 单一有限 dyadic 效果表的局部关系证书

**定义 13.1（同一网格上的完整二、三结果菜单表）。** Let $d,m\in\mathbb Z$ with $d\ge2$, $m\ge1$, $N=2^m$, $h=N^{-1}$, and
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
\tag{13.1}
$$
Put
$$
B_d=4d^2-3d,\quad c_d=B_d^{-1},\quad
K_d=6d^2+6,\quad T_d=2d+1,\quad M_d=2d.
$$

**定理 13.2（一致局部目标证书）。** Under Definition 13.1, for every $E\in K$ with $\|E\|_{\rm op}\le c_d$,
$$
|p(E)-\operatorname{Tr}(HE)|\le K_d\epsilon.
\tag{13.2}
$$
Moreover,
$$
|\operatorname{Tr}H-1|\le T_d\epsilon,
\qquad \|H\|_{\rm op}\le M_d.
\tag{13.3}
$$
These estimates hold for all $m\ge1$; their constants do not grow with $m$.

**证明。** The menu hypothesis gives $0\le p(0)\le2\epsilon$, $|p(I)-1|\le3\epsilon$, and
$$
|p(A)+p(B)-p(A+B)|\le2\epsilon
\tag{13.4}
$$
whenever $A,B,A+B\in K$.

Indeed, subtract the inequalities for $(I,0)$ and $(I,0,0)$ to bound $p(0)$; the pair inequality then bounds $p(I)$. For (13.4), compare $(A,B,I-A-B)$ with $(A+B,I-A-B)$. These are permitted labelled menus even when entries coincide or vanish.

For use in this proof, suppose $Q\in K$, $L\ge1$ is an integer, and $kQ/L\in K$ for $0\le k\le L$. Then
$$
\left|p(kQ/L)-\frac{k}{L}p(Q)\right|\le4\epsilon
\quad(0\le k\le L).
\tag{13.5}
$$

To obtain this estimate, write $f(k)=p(kQ/L)$ and $\delta=2\epsilon$. Equation (13.4) gives $|f(k)+f(l)-f(k+l)|\le\delta$ for $k+l\le L$. Set $g(k)=f(k)-(k/L)f(L)$ on $0\le k<L$, viewed as the cyclic group $\mathbb Z/L\mathbb Z$. When $k+l<L$, its additive defect is at most $\delta$. When $k+l\ge L$, set $u=k+l-L$ and use
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
\tag{13.6}
$$
If $t=\|E\|_{\rm op}$, then $|E_{ij}|\le t$, whence
$$
\sum_i|a_i|+\sum_{i<j}(2|x_{ij}|+2|y_{ij}|)
\le (4d^2-3d)t\le1.
\tag{13.7}
$$
Split (13.6) into its positive and negative coefficients, obtaining $E=P-Q$, with $P,Q\ge0$. Each summand is a coefficient in $[0,1]$ times a member of $\mathcal B$. By (13.7), all partial sums, $P$, and $Q$ are effects. They belong to the original grid: the coefficients of $D_i$ are multiples of $h$, while those of $R_{ij},J_{ij}$ are multiples of $2h$. Consequently (13.5) applies to each summand, with $L=N$ for $D_i$, and $L=N/2$ for $R_{ij},J_{ij}$.

For a positive sum with $k$ nonzero summands, telescoping (13.4) and using (13.5) gives error at most $(6k+2)\epsilon$ between its table value and the corresponding linear combination of the basis values. This bound also holds for $k=0$, since $p(0)\le2\epsilon$. The total number of summands in $P,Q$ is at most $d^2$. Apply (13.4) to $E+Q=P$, and subtract the two linear combinations. The error is at most $(6d^2+6)\epsilon$, proving (13.2).

Since $I=\sum_iD_i$, (13.4) and the menu bounds above yield
$$
|\operatorname{Tr}H-1|\le2(d-1)\epsilon+3\epsilon=T_d\epsilon.
$$
The diagonal entries of $H$ are $p(D_i)\in[0,1]$. Equation (13.1) implies that both real and imaginary parts of every off-diagonal entry lie in $[-1,1]$. Hence its maximum absolute row sum is at most $1+\sqrt2(d-1)\le2d$, which bounds its operator norm. $\square$

## 14. 同一表格的正性探针与局部密度近似

**定理 14.1（同表格秩一探针与一致负谱界）。** Under Definition 13.1, set
$$
A_d=16K_d/c_d,\qquad D_d=16M_dd/c_d,
\quad a_d=A_d\epsilon+D_dh.
$$

The matrix in (13.1) satisfies
$$
\lambda_{\min}(H)\ge-a_d.
\tag{14.1}
$$
**证明。** First suppose $N\ge8d/c_d$. Let $\psi$ be a unit eigenvector for $\lambda=\lambda_{\min}(H)$, and put $R=\sqrt{c_dN}/2$. Round each real and imaginary component of $R\psi$ to an integer, obtaining $v\in\mathbb Z[i]^d$ with
$$
\|v-R\psi\|\le b:=\sqrt{d/2},\qquad R\ge2b.
$$
In particular $v\ne0$. The actual grid effect
$$
F=vv^*/N=\gamma ww^*,\quad w=v/\|v\|,\quad\gamma=\|v\|^2/N
$$
satisfies $c_d/16\le\gamma\le c_d$; hence (13.2) applies. Since $p(F)\ge0$, it gives
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
Combining the last two inequalities proves (14.1). If $N<8d/c_d$, then $D_dh>2M_d$, and the already proved $\lambda_{\min}(H)\ge-M_d$ proves (14.1) directly. Thus coarse grids are included. $\square$

**推论 14.2（一致局部密度近似）。** Under Definition 13.1, there is a finite constant depending only on $d$, for example
$$
C_d^{\rm loc}=2T_d+K_d+T_d+2dA_d+2dD_d,
$$
such that one matrix $\rho\succeq0$ with $\operatorname{Tr}\rho=1$ obeys
$$
\max_{E\in K:\,\|E\|_{\rm op}\le c_d}
|p(E)-\operatorname{Tr}(\rho E)|
\le C_d^{\rm loc}(\epsilon+h).
\tag{14.2}
$$

**证明。** If $\epsilon\ge1/(2T_d)$, any density matrix works, because both compared numbers lie in $[0,1]$, and $1\le2T_d\epsilon$. Otherwise $s=\operatorname{Tr}H\ge1/2$. Write $H=H_+-H_-$, $t=\operatorname{Tr}H_-\le da_d$, $Z=\operatorname{Tr}H_+=s+t>0$, and $\rho=H_+/Z$. Then
$$
\|H-\rho\|_1=t+|Z-1|\le2da_d+T_d\epsilon.
\tag{14.3}
$$
For every effect, its trace pairing with $H-\rho$ is bounded by this trace norm. Combine (13.2) and (14.3).

The eigenvector coverage and positive-part normalization steps are intermediate mechanisms from [V59](AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md), Theorem 5.2 and Proposition 5.3, and [V64](AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md), Definition 5.1 and Theorem 5.2. In the present derivation, the local relation certificate, the actual same-grid probes, their positive gain and quadratic directional coverage follow from Definition 13.1; the cited conditional mechanisms do not supply that local certificate. These are mathematical statements about the supplied table, with no physical acquisition or priority assertion.

$\square$

## 15. 任意目标关系的未决问题

**定义 15.1（任意目标关系问题及小效果分解条件）。** For the specific $H$ in (13.1), ask whether there is a finite dimension-only constant $L_d$ such that, for every $m\ge1$ and every table in Definition 13.1,
$$
\sup_{E\in K}|p(E)-\operatorname{Tr}(HE)|
\le L_d(\epsilon+h)
\tag{15.1}
$$
with $L_d$ independent of $m$. If (15.1) holds, (14.1)–(14.3) give a single density matrix approximating the table on all of $K$ at rate $C_d(\epsilon+h)$ with a dimension-only constant, treating the large-$\epsilon$ case as above. Theorem 13.2 establishes the corresponding relation only on $\|E\|\le c_d$. If $E=\sum_{j=1}^k E_j$, where $k\ge1$, $E_j\in K$ and $\|E_j\|_{\rm op}\le c_d$, then telescoping (13.4) and Theorem 13.2 gives the conditional bound
$$
|p(E)-\operatorname{Tr}(HE)|\le[kK_d+2(k-1)]\epsilon.
$$
No uniformly bounded such decomposition is asserted. In particular, dividing or rounding a boundary effect need not preserve its original grid or its positive face. The local estimate and this conditional bound neither prove the all-grid approximation assertion nor provide an admissible counterfamily. The arbitrary-target relation remains an open mathematical question.

## 16. 固定四维的互补投影分解障碍

**命题 16.1（任意 dyadic 精度下的小块分解障碍）。** In fixed dimension $d=4$, for every integer $m\ge1$ and $N=2^m$, there are complementary rank-two grid projections $P,Q\in K$ such that every nonzero grid effect below either projection has operator norm exactly one. In particular, neither projection is a sum of grid effects of norm at most $c_4<1$. This is an obstruction to the small-piece decomposition route; it is not a counterexample to all-grid stability.

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

For instance, $N=8$ admits $a=2+i,b=1+i$. The four-square input establishes the construction for arbitrarily fine dyadic grids at fixed dimension. This construction supplies no admissible non-Born table. The question in Definition 15.1 still concerns all labelled menus, including relations involving proper subprojections and their complements. $\square$

## 追加锚（本行以下为增补区）
