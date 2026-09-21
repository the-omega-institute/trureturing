[Index](../../marked_head_profile.md) · [Actual residual classes](341-conditional-future-avoidance-controls-the-current-prefix.md) · [Witness weights](342-original-cut-certificates-preserve-the-old-measure.md)

# CRT 到多值 SAT：保原标签约化与消元运输的边界

有限 AP 覆盖可以精确运输到多值 CNF。成熟 SAT 理论提供可用的 autarky 与奇异消元接口，但等可满足不保证原模数互异、前缀支撑、原费用或条件概率同时保留。以下只给这些接口及可复用的失败判据，不宣称排除新的无界覆盖族。

## 1. 原对象、共同见证与文献接口

令 \(Q=\operatorname{lcm}_i d_i=\prod_p p^{H_p}\)，取独立 CRT 数位
\(X_{p,k}\in\{0,\ldots,p-1\}\)，\(1\le k\le H_p\)。整数模 \(Q\) 与全数位赋值双射。原 AP \(a_i\bmod d_i\) 对应子句

\[
 C_i=\bigvee_{p,\ k\le v_p(d_i)}
 [X_{p,k}\ne\operatorname{digit}_{p,k}(a_i)].
\]

原 AP 恰是该子句的假集；未覆盖点恰是所有子句的共同满足赋值。极小全覆盖对应 minimally unsatisfiable clause-set；仅在自身并集上不可删的非覆盖族不满足其中的 unsatisfiable 前提。全部原模数互异等价于这些**原前缀支撑**互异，单纯“子句互异”弱于这个条件。均匀 CRT 测度下单个原假集的质量为 \(1/d_i\)，不是 SAT 缺陷中的单位子句费用。

已核对 Kullmann 的 [arXiv:1103.3693v1](https://arxiv.org/pdf/1103.3693v1)，*Constraint satisfaction problems in clausal form*（两篇 2011 年文章的合并报告；下列编号属此稿）：§1.3.1–1.3.2（页13–16）的 literal 正是 \(v\ne\varepsilon\)，允许不同有限域；§1.4.1（页19–20）给出 autarky；§1.5.3（页25–26）给出多值 DP；Lemma 1.6.1（页28–29）给出多值奇异消元；Corollary 1.9.9（页40）与 Lemma 1.11.1（页45–46）分别给出加权 Tarsi 与 surplus。这里无需把 Boolean 定理未经核对地移植到奇素数域。

## 2. 全 \(Q\) 缺陷界确实是既有 Simpson 结果

加权变量数为 \(\sum_v(|D_v|-1)\)。原族每个高度以内的数位都实际出现，因此广义 Tarsi 给出

\[
 |\mathcal A|\ge 1+\sum_pH_p(p-1)=1+f(Q)
\]

作为极小全覆盖必要条件。这与 [Simpson, *Acta Arith.* 45 (1985), 145–152](https://doi.org/10.4064/aa-45-2-145-152) **Corollary 2** 同量词：该推论在页151末明确取全族模数的 lcm，页152首取 \(D=1\) 证明。它不是只涉及某条 essential 原模数 \(d_t\) 的另一条下界。任意冗余全覆盖须先取极小子族，并用该子族重算 \(Q\)，不能保留原冗余族的 \(Q\) 套用此界。

更一般，matching-lean surplus 对每个非空数位子集 \(V\) 要求触及它的原标签数至少为 \(1+\sum_{v\in V}(|D_v|-1)\)。取 \(V=\{(p,k):v_p(D)<k\le H_p\}\)，正好恢复 Simpson **Theorem 2**（页149，证明至151）：

\[
 D\mid Q,\ D\ne Q
 \quad\Longrightarrow\quad
 |\{i:d_i\nmid D\}|\ge1+f(Q/D).
\]

任意数位子集补齐为各素数的后缀，不改变触及的原标签并增大右侧需求，故这里没有藏着更强的支撑 cut。[341 的 226 标签诊断例](341-conditional-future-avoidance-controls-the-current-prefix.md#an-irredundant-low-rho-head-with-a-conditionally-redundant-future)的全高度给出 \(1+f(Q)=293>226\)；它已经有实际未覆盖整数，这个既有必要条件也排除其为极小全覆盖。HN 表述实验不以此冒领新族排除。

另一个可用而不同的有限筛选器是 clause-side Hall：给每个数位 \(p-1\) 个容量，若能匹配全部原标签，则选取每个数位未被其匹配标签禁止的值，得到实际未覆盖 CRT 点（Kullmann Lemmas 1.7.1、1.8.1）。其条件为全部标签子集 \(I\) 满足
\(|I|\le\sum_p(p-1)\max_{i\in I}v_p(d_i)\)。筛选失败不等于存在覆盖。

## 3. Autarky 保留原标签，概率另付切片因子

部分赋值 \(\alpha\) 若满足它触及的**每一条**原子句，就删除全部触及子句，得到原标签子集 \(G\)。剩余模数、剩余指数约束、剩余原标签费用均按字面保留。\(G\) 的满足赋值与同一份 \(\alpha\) 合并即满足原 \(F\)，反向则遗忘被删条件，因此二者等可满足。

这不是原 survivor 集相等。在均匀独立 CRT 数位下，\(G\) 不含被赋值坐标，故

\[
 \mu(\operatorname{avoid}F\cap[\alpha])
 =\Bigl(\prod_{v\in\operatorname{dom}\alpha}|D_v|^{-1}\Bigr)
 \mu(\operatorname{avoid}G).
\]

右侧是原未覆盖质量的下界。换成非均匀或相关来源必须使用其实际条件切片律，不能沿用此独立因子。

在正式 226 原标签诊断例中，取 \(X_{13,1}=12\)：21 条 future 子句的禁止 13-余数都在 \(0,\ldots,11\)，而204条 head 与当前 \(1\bmod11^{12}\) 均不使用13。核验后恰删除原索引205–225，保留0–204。在固定 old survivor 上，这给出 Haar 下界 \((1-11^{-12})/13\)，17坐标自由。它是原例上的保标签证书，不是对任意 future 族的统一质量保证。极小全覆盖本身没有非平凡 autarky，不能预设每个假想极小反例都能走这一步。

## 4. 奇异 DP 保真到哪一层

消去域大小为 \(p\) 的数位 \(v\)，每个数值分支选一条 parent，去掉 \(v\) 后合并其它 literal；相冲突的组合不产生子句。所得 CNF 表示 \(\exists v\,F\)。对覆盖集合来说，新假集是**整个 \(v\)-纤维均被覆盖**的底点集合，而非沿该纤维的平均覆盖质量。

若消去最深数位，合法 resolvent 仍有前缀支撑，其模数是 \(\operatorname{lcm}(d_{i_1},\ldots,d_{i_p})/p\)。若只一支出现 \(t\) 次、其它 \(p-1\) 支各出现一次，称为 singular。非退化要求产生恰 \(t\) 条不同新子句，且不与 untouched 子句重复。Lemma 1.6.1 保证：原 \(F\) 极小不可满足，当且仅当此步非退化且新族极小不可满足。**不同新子句仍可有同一支撑、即同一派生模数。** 共享 parent 的派生标签也不自动取得独立原费用。

下面是三个严格限于非覆盖族的失败判据，原模数全部互异且为奇数，每条原 AP 均有逐标签核对的 private integer：

1. `0 mod7, 15 mod21, 15 mod35, 30 mod105, 45 mod63, 25 mod175, 54 mod189, 125 mod875`。消去7数位的 occurrence 为 `(1,2,1,1,1,1,1)`；两个 parent tuple 都得到 `0 mod3375`，共享六条原标签。这是退化 singular，说明“在原并集上不可删”不足以代替极小全覆盖前提。
2. `0 mod21, 15 mod35, 36 mod105, 9 mod63, 108 mod189, 81 mod567, 243 mod1701, 4374 mod5103`。原 AP 甚至两两不交；同样消去7数位却得到 `0 mod3645` 与 `2916 mod3645`。此步非退化，派生模数仍重复，两个 tuple 仍共享六条原标签。原并集质量 `2792/25515`，全覆盖纤维质量 `2/3645`。它否定无附加条件的“非退化即保模数唯一”；未证明这种形态能出现在未知的互异奇模数极小全覆盖中。
3. `0 mod45, 100 mod225, 875 mod1125`。消去低3数位，留下高3数位0与 `0 mod125`，出现支撑空洞。拉回整数为 `{0,875,1000} mod1125`，圆周间距为875、125、125，不能视为单一 AP；直接表示需要三条同模数 AP。

## 5. 存在投影与按见证计数运输概率不同

令 \(k(y)=|\{v:F(y,v)\}|\)。消元只保留 \(k(y)>0\) 这一判据。若在原全部满足赋值上均匀抽样再忘掉 \(v\)，底点质量为 \(k(y)/\sum_z k(z)\)；若直接在消元后满足赋值上均匀抽样，质量为 \(1/|\{z:k(z)>0\}|\)。两者仅在正纤维大小恒定时一致。

上面第二例给出同一实际关系内的成对见证：底点 `1 mod3645` 有7个合法7数位扩张，`3 mod3645` 有6个；二者消元后都合法。全部3,645个底点中，3,643个有扩张，原满足赋值总数22,723。因此原均匀满足律的两个推前质量为 `7/22723`、`6/22723`，消元后均匀律却都为 `1/3643`。等可满足保留了存在性，未保留这份条件概率；若要保概率，必须运输纤维重数或实际条件核。

## 6. 可执行范围

[标准库程序](../../frontier/cover-geometry/sat_prefix_reductions.py)（`--base <report-base> --check`） 以纯 stdout 核验7,395个完整剩余CRT纤维，显式检查每个被消数位的全部扩张，并对19个 private witness 完成137次逐原标签成员关系核对。程序读取正式 `frontier/cover-geometry/hn_majorant_reduction.py`，重算后通过 `certificate_io.read_artifact_bytes` 对齐正式 multipart canonical；不依赖 scratch 证书，不新增重复快照。

这些是标准工具的精确迁移、一个保标签质量接口和运输失败判据；有限诊断不作为新增 Lean 实例准入。未解义务仍是找到对目标候选族有效、同时控制原标签约束与指定来源质量的约化，或对具体消元补齐其费用及概率运输证书。

## 7. 固定有限族在完备化中没有额外的未覆盖见证

固定有限族 \(\mathcal A=\{a_i\bmod m_i:1\le i\le k\}\)，其中 \(m_i>1\) 为两两互异的奇数，令 \(L=\operatorname{lcm}_i m_i\)。在整数的 profinite 完备化 \(\widehat{\mathbb Z}\) 中记

\[
 E_L=\{x\in\mathbb Z/L\mathbb Z:\forall i,\ x\not\equiv a_i\pmod {m_i}\},
 \qquad
 E=\widehat{\mathbb Z}\setminus\bigcup_i\{z:z\equiv a_i\pmod {m_i}\}.
\]

约化映射 \(\pi_L\) 满足 \(E=\pi_L^{-1}(E_L)\)。归一化 Haar 测度给每个模 \(L\) 纤维质量 \(1/L\)，故

\[
 \mu(E)=\frac{|E_L|}{L},\qquad
 E\ne\varnothing
 \ \Longleftrightarrow\ \mu(E)>0
 \ \Longleftrightarrow\ E_L\ne\varnothing
 \ \Longleftrightarrow\ \exists n\in\mathbb Z\ \forall i,\ n\not\equiv a_i\pmod {m_i}.
\]

最后一步只需取一个模 \(L\) 剩余类的整数代表。对 \(L\mid N\)，**同一固定族**在模 \(N\) 的未覆盖集是 \(E_L\) 的完整逆像，每个剩余类恰有 \(N/L\) 个提升，投影满射。因此此有限问题不会出现“完备化有未覆盖点、整数却全部被覆盖”的现象；增加新的禁类时则不能直接援用这个固定族的满射结论。

奇模数约束不读取2进坐标，故在 \(\widehat{\mathbb Z}\cong\prod_p\mathbb Z_p\) 中可写 \(E=\mathbb Z_2\times E_{\mathrm{odd}}\)。还可删去 \(p\nmid L\) 的坐标及高于 \(v_p(L)\) 的数位，精确退回 \(\mathbb Z/L\mathbb Z\)。这些删减合法是因为所有约束都通过该有限商因子化。目标依旧是：对**每个有限族**的两两互异奇模数 \(m_i>1\) 及**每个固定相位元组** \((a_i)_i\)，证明 \(E_L\ne\varnothing\)；这个全称断言仍未解决。允许模数1会引入平凡全覆盖，必须排除。完备性或紧致性均不证明这里尚缺的有限非空前提。

更粗投影则可能丢掉所需关系。例如取 `0 mod3, 1 mod9, 2 mod27`。在模27周期内它们两两不交，分别占9、3、1个点，未覆盖集为

\[
 E_{27}=\{4,5,7,8,11,13,14,16,17,20,22,23,25,26\},
 \qquad |E_{27}|/27=14/27.
\]

若 \(q:\mathbb Z/27\mathbb Z\to\mathbb Z/3\mathbb Z\)，三个禁类的像分别是 \(\{0\},\{1\},\{2\}\)，但 \(q(E_{27})=\{1,2\}\)。所以

\[
 q(E_{27})\ne (\mathbb Z/3\mathbb Z)\setminus\bigcup_i q(C_i).
\]

每条禁类在粗纤维内各有一个见证，不等于这些禁类覆盖了整个粗纤维；存在投影与取补不能交换。这正是第4、5节需要保留共同细点或纤维信息的原因。

## 8. 分离点不等于给出有限正见证

令 \(U=\{0,1\}^{\mathbb N}\)，\(Q_n\) 读取前 \(n\) 位。全部读数联合单射，且 \(U\cong\varprojlim_n\{0,1\}^n\)。取 \(F\subseteq U\) 为仅含有限多个1的序列。每个有限前缀既可接无限个0得到 \(F\) 中的序列，也可接无限个1得到其补集中的序列，故对每个 \(n\)，

\[
 Q_n(F)=Q_n(U\setminus F)=\{0,1\}^n.
\]

因而完整重建空间并不保证每个子集都能在有限层被判定。针对非空目标集的**有限正见证**所需的量词是

\[
 \exists n\ \exists b:\quad
 \varnothing\ne Q_n^{-1}(b)\subseteq F,
 \quad\text{等价于}\quad
 \exists n:\ Q_n(F)\setminus Q_n(U\setminus F)\ne\varnothing.
\]

它在前缀拓扑中等价于 \(F\) 有非空内部：纤维就是基本柱集，而任意非空开集包含一个这样的柱集。仅要求两个像不相等，方向不足；若 \(F\) 是单点，则对 \(n\ge1\)，\(Q_n(F)\) 是单点而 \(Q_n(U\setminus F)=\{0,1\}^n\)，可以给出补集的有限见证，却没有 \(F\) 的有限正见证。

对紧 profinite 空间，在生成其拓扑的有向有限商系统中，每个既开又闭的集合都通过某个有限商因子化。证明如下：在每个点选取一个使成员关系恒定的基本柱邻域，紧致性给出有限子覆盖；再取这些有限商指标的共同细化。细化后的每条纤维落在其中一个邻域内，成员关系遂在纤维上恒定。

第7节的有限族未覆盖集本来就是既开又闭的柱集，已经通过模 \(L\) 的商因子化。因此它的有限可检测性已知；缺口仍是对所有目标族证明它**非空**，而非再证明有限读数可以表达它。

## 9. 无限奇素数族：相容分支可非整数，极限质量可为零

将全部整数枚举为 \(z_1,z_2,\ldots\)，全部奇素数枚举为 \(p_1,p_2,\ldots\)，取无限族

\[
 \mathcal B=\{z_n\bmod p_n:n\ge1\}.
\]

模数两两互异且全为奇数；每个整数都属于以它命名的那一类，故此无限族覆盖 \(\mathbb Z\)。但对每个有限前缀，设 \(L_n=\prod_{i\le n}p_i\)，CRT 给出恰好

\[
 |E_n|=\prod_{i\le n}(p_i-1)>0,
 \qquad
 \frac{|E_n|}{L_n}=\prod_{i\le n}\left(1-\frac1{p_i}\right)>0
\]

个未覆盖剩余类及其密度。每个旧剩余类都有 \(p_{n+1}-1\) 个新提升，所以 \(E_{n+1}\to E_n\) 满射。逐素数选择 \(b_i\not\equiv z_i\pmod {p_i}\) 就给出相容分支；任何整数都不可能实现该分支，否则它会同时避开属于自己的禁类。

这里的逆极限是

\[
 \varprojlim_n\mathbb Z/L_n\mathbb Z\cong\prod_{p\text{ odd}}\mathbb F_p,
\]

**不是** \(\widehat{\mathbb Z}\)：它既没有2进坐标，也没有任何素数的高次数位。将每个 \(b_p\) 任意提升到 \(\mathbb Z_p\)，再任选2进坐标，就得到 \(\widehat{\mathbb Z}\) 中避开全部禁类的点。因此完备化中的未覆盖集 \(E_\infty\) 非空，却与嵌入其中的 \(\mathbb Z\) 不交。

由于这些有限未覆盖柱集递减，概率测度从上连续给出

\[
 \mu(E_\infty)=\lim_{n\to\infty}\prod_{i\le n}\left(1-\frac1{p_i}\right)=0.
\]

末个等号使用素数倒数和发散：删去素数2不改变发散，而 \(\log(1-t)\le-t\) 将乘积上界压至0。所用发散定理已有钉版 Mathlib 声明 `Nat.Primes.not_summable_one_div`（[SumPrimeReciprocals.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/SumPrimeReciprocals.lean#L119)；该文件采用 Erdős 的经典证明）。此处是既有结果的普通应用，不新增 Lean 声明。

这个例子同时满足有限非空与分支相容，却排除了“必有整数实现”和“极限质量必为正”两个结论。只让奇素数支撑增长不能重建全部奇数进坐标，还需要各素数幂高度无界；任何仅含奇模数的系统也不会在全部整数模数中共尾。上述无限族不反驳有限奇互异覆盖问题；对一个固定有限族，第7节的整数代表与正测度等价仍然成立。

## 10. Odd prime-power slices can have no computable surviving thread

This is an ordinary computability construction for an infinite congruence family. It does not provide a finite odd-distinct covering system or prove that none exists. It uses one fixed Haar probability law throughout.

### Construction and exact restrictions

Fix an effective enumeration (phi_e)_(e>=0) of all partial computable functions N -> N, with a uniform finite-step simulation. A3-adic point x is called computable when there is a total algorithm which, on input n>=1, returns its canonical residue x_n in{0,...,3^n-1}. Define its output at input0 to be0, so that this name is a total function on N and occurs in the fixed enumeration.

For each index e, if phi_e(e+1) halts with output a_e, include

    C_e = {x in Z_3 : x = a_e mod3^(e+1)}.

An output outside the canonical residue range is simply reduced modulo3^(e+1). If the computation does not halt, no cylinder with that label is included. There is at most one cylinder of each numerical modulus3^(e+1). All included moduli are odd and greater than1. Each included residue is fixed by one actual halting output; it is never selected again depending on a target point.

The cylinder inventory is computably enumerable by dovetailing. It is not asserted that the height-indexed question "does C_e occur?" is decidable. This distinction is essential.

Let mu be normalized Haar measure on Z_3 and put

    E = Z_3 minus union_(e : phi_e(e+1) halts) C_e.

Countable subadditivity gives

    mu(union C_e) <= sum_(e>=0)3^(-(e+1)) = 1/2,
    mu(E) >= 1/2.

Every cylinder is clopen, so E is closed, nonempty and has positive Haar mass.

### Every computable point is excluded

Suppose x were a computable point of E. Its total residue algorithm is some phi_e in the fixed enumeration. Thus phi_e(e+1) halts and outputs x_(e+1). The corresponding C_e is included and contains x, contradicting x in E.

Consequently E has no computable3-adic point. In particular it contains no embedded ordinary integer, since the residues of a fixed integer modulo3^n are computable, including for negative integers. The associated infinite congruence classes therefore cover every ordinary integer, while their union covers at most half of Z_3.

Every finite subfamily fails to cover: its total cylinder mass is strictly less than1/2, so it has an uncovered residue at its finite LCM, hence an uncovered ordinary integer. This is fully compatible with the finite Erdős7 problem.

There are infinitely many included labels. For example, the enumeration contains total residue algorithms for infinitely many distinct ordinary integers, requiring infinitely many program indices. If a total enumerated sequence of the included classes is desired, output each newly halted index once in dovetail order. Searching for its i-th output terminates for every i. This gives a computable listing with pairwise distinct numerical moduli, without making membership at a prescribed height decidable or ordering the list by height.

### A uniformly decidable finite-resolution tower

For n>=0 take X_n=Z/3^nZ (X_0 a singleton). Let D_n consist of indices e<n whose computations phi_e(e+1) halt within n simulation steps, with their observed outputs a_e. Define

    H_n={r mod3^n : for every e in D_n, r != a_e mod3^(e+1)}.

H_n can be computed exactly by finite simulation and enumeration of3^n residues. Each previously seen computation remains seen, so D_n is contained in D_(n+1). Reduction modulo3^n maps H_(n+1) into H_n. At a fixed stage no private point, residue choice or probability law is reselected.

Each excluded class for e<n contains3^(n-e-1) residues. The union bound therefore gives

    |H_n| >= 3^n - sum_(e=0)^(n-1)3^(n-e-1)
           = (3^n+1)/2.

In particular every level is nonempty. Moreover

    |H_(n+1)| >= (3^(n+1)+1)/2 > 3^n >= |H_n|.

Thus even the number of remaining distinguishable states increases strictly at every step. The ambient arithmetic capacity grows exactly bylog3. These are cardinality/capacity assertions, not a claim of an independent Shannon information increment under every source law.

Lift H_n to the clopen subset K_n={x in Z_3 : x mod3^n in H_n}. Then K_(n+1) is contained in K_n. An included index e is tested at every sufficiently large stage n, so

    intersection_n K_n = E,
    inverse_limit_n H_n is canonically identified with E.

The finite inverse system is uniformly computable and every level is nonempty, but it has no computable compatible thread: such a thread would return all canonical residues of a computable point of E.

### Why compactness gives existence but no effective selector

If a uniformly computable system of explicitly finite nonempty sets has computable SURJECTIVE bonding maps, one can compute a compatible thread. Choose an element of H_0, then enumerate H_(n+1) until finding a preimage of the current element. Surjectivity makes every finite search terminate. No oracle is needed.

Therefore not all bonding maps of the constructed tower can be surjective. Some currently surviving cells have no immediate surviving extension; more generally determining which cells extend forever is not supplied by their decidable finite-stage membership. The positive measure and strict cardinality growth do not repair this selector problem.

There is a sharper comparison using the same numerical moduli. Suppose an algorithm decides, for each height h>=1, whether there is a forbidden class of modulus3^h and returns its final phase when present. Let S_n impose all those final constraints of height at most n. Every r in S_n has three lifts to modulus3^(n+1); earlier constraints hold on all three, and the single possible new class at height n+1 deletes at most one. Thus S_(n+1) -> S_n is surjective, with at least two children per surviving cell. Choosing the least permitted child gives a computable survivor. Our negative construction cannot supply this decidable final-height inventory. The computable order of discovering cylinders does not supply a computable certificate that no further low-height cylinder will appear.

### Consequence for the expression-capacity question

Oddness and distinctness alone do not prevent a noncomputable surviving thread problem in effective infinite prime-resolution systems. One prime,3, already suffices for the construction. It uses a c.e. event stream whose schedule may reveal a low-height constraint arbitrarily late; a computable rule assigning a final residue to every height in advance is a stronger interface not supplied here.

This establishes no reduction of the halting problem to coverage of a supplied finite family: the latter remains decidable by checking one LCM period. It establishes neither formal independence nor a positive or negative answer to Erdős7. Any proposed transfer to that conjecture must preserve its finite quantifier and supply a new argument controlling arbitrary finite architectures.

## 11. The finite-extinction index problem has an exact conditional classification

Specify a uniform effective stream interface: a program may emit pairs(a,m); keep a pair only when m>1 is odd and no previously retained pair has that numerical modulus. Ignore invalid or repeated-modulus events and reduce phases modulo m. Each finite simulation stage yields a computable finite family. Streams may have finitely many or infinitely many retained events.

Let FC be the set of program indices whose retained stream covers all integers at some finite stage. Membership in FC is computably enumerable: simulate stages and check each finite family on its actual LCM. The empty family is not a cover. In fact

    FC is nonempty iff a finite distinct odd covering system exists.

The forward implication takes the finite covering prefix. The reverse implication uses a program outputting that finite family.

There are precisely two possibilities for this specified index problem. If the finite odd-cover conjecture is true (no such cover exists), FC is empty. If a finite cover C exists, FC is Sigma^0_1-complete under many-one reductions: given a machine M and input w, effectively produce a stream program which simulates M(w), emits nothing until it halts, and then emits the fixed list C. Its retained family covers at a finite stage exactly when M(w) halts. This compilation is total computable. The existence of C gives the conditional existence of the reduction; no algorithm for obtaining C from the unresolved conjecture is asserted.

Thus proving HALT-hardness of THIS odd-distinct finite-extinction index problem would already imply the positive answer to Erdős7. It cannot be imported from arbitrary survivor towers without discharging precisely that missing arithmetic premise. In contrast, the no-computable-branch construction above works unconditionally for an infinite family and settles neither side of finite Erdős7.
