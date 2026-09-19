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

[标准库程序](../../frontier/whole-cover/sat_prefix_reductions.py)（`--base <report-base> --check`） 以纯 stdout 核验7,395个完整剩余CRT纤维，显式检查每个被消数位的全部扩张，并对19个 private witness 完成137次逐原标签成员关系核对。程序读取正式 `frontier/whole-cover/hn_majorant_reduction.py`，重算后通过 `certificate_io.read_artifact_bytes` 对齐正式 multipart canonical；不依赖 scratch 证书，不新增重复快照。

这些是标准工具的精确迁移、一个保标签质量接口和运输失败判据；有限诊断不作为新增 Lean 实例准入。未解义务仍是找到对目标候选族有效、同时控制原标签约束与指定来源质量的约化，或对具体消元补齐其费用及概率运输证书。
