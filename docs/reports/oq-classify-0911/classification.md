# observer-quantum-v1 residual-open 分类

已分类 10 / 131。交付完整 ID 字典序的前 10 条；其余 121 条未分类。第 11–20 条虽已成功读出，陈述辖域和库命中复核尚未完成，不计入分类数；下一条为 `151be1c8bb882c891287ed2734b5f1e050a0f18c53498aa256820f7daf936d2c`。

范围：base `875f99765a05f2f6819e7352062fd2ce8c6afa2d`，工作树分支 `lane/theory/oq-probe`。实数目录 `Meta/Digestion/backfill/observer-quantum-v1/residual-open/` 有 131 个 YAML。按完整 atom ID 字典序顺序处理；此顺序仅用于遍历，不是选题排序。每个计入完成数的 atom 必须实际成功执行 `make show-atom ATOM_ID=<完整 ID>` 并读完正文与 coverage。

产地：Codex 主循环直接分类，使用本机 `lean4` skill 的先库后证检索指引；零独立评审席，单点自查。用户已给出的黄金分账 bind 判定作为用户输入保留，不重做其证明；尚未遍历到该 atom。

本席仅交付分类，不修改 Lean、理论源、atom、coverage、冻结状态，不执行 ingest、cover、deposit。通用证明席模板的 Lean 构建、公开定理 proof_shape / 依赖 / escape_witness / admission_basis 和 PR 成功条件不适用于本次报告；以任务专门要求为准。

## 读取工具收据

首次 `make show-atom ATOM_ID=c74925a3c3098b69` 返回 make exit 2：

```text
Unhandled exception: An error occurred trying to start process '/Users/chronoai/trureturing-oq-probe/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint' with working directory '/Users/chronoai/trureturing-oq-probe'. No such file or directory
make: *** [show-atom] Error 1
```

这是 CLI 尚未构建；canonical `make -C tools dotnet` 已 exit 0，0 warnings / 0 errors，工具报告耗时 17.15 s；之后按完整 ID 顺序读取前 20 条，全部 exit 0、`coverage_gids=[]`。最初失败不算已读、已分类。完整 stdout/stderr 保存在 runner attempt 的 `show-atom/001-<ID>.log` 至 `020-<ID>.log`，均保留 RAW、NORMALIZED 与退出码；分类只定案前 10 条。

当前理论源卷首使用「条件性重构」；旧 CAS `c74925a3…` 的卷首仍使用「强制出身」。分类的对象是 `show-atom` 输出的 CAS 正文，不以当前源卷替换旧 atom。

## 分类表

ID 是行身份，后面恰为五项。`proposition` 表示正文含可陈述的数学义务，不表示整段散文均为真或可一次 cover；形式句明确圈定被提取的子句。`pointer` 表示该段承担词典、续报或索引职责，不把引述的每个名词另造为定理。数值核对只是探针，不是 Lean 证明或开放问题进展。

| 顺序 / 完整 atom ID | 1 类别 | 2 形式命题（proposition 时） | 3 精确命中（bind-only 时） | 4 数值可验吗 | 5 停止条件 |
| --- | --- | --- | --- | --- | --- |
| 1 / `01265b7e38d24ab81378ad6d644323995c5a86850074fe1a8ddb3c861c525a35` | `pointer`：§17.3 是测量词典及母账续报，明确否认解决 Zauner / MUB-6。 | — | — | 无独立数值命题；33=7+6+24 不检验未给定义的算术分类，不能拿算术和式作覆盖。 | 若只能从「SIC」「8 类」等名词自行补出母账未展开的命题，当场停手。 |
| 2 / `03fb885c43fa203bbed25b0ff9756a45f6cb4a78bfb816c370c4ec1c1f665f7d` | `bind-only`：承重子句是有限清单逃逸率，后半「王冠」为叙述。 | — | `D5/S0/Diagonal/EscapeCount.lean` → `D5.S0.Diagonal.EscapeCount.escaped_listing_card`，**public**；对任意有限非空 A、Y 与 f:Y→Y，令 m=card A、n=card Y、k=card Fix(f)，均匀清单 g:A→A→Y 的逃逸概率为 (1−k/n^m)^m；由公开计数除以 n^(m²) 薄改写。该文件 `listing_equiv` 为 **private，不算命中**。 | 可：运行下面 E 算法；(n,m,k)=(2,1,2),(2,2,2),(2,3,2) 得 0、1/4、27/64；固定点为 0 时三项皆 1；(3,1,1),(3,2,1) 得 2/3、64/81。 | 若分布不是全部清单上的均匀分布、n=0，或将「清单越大」误解为此概率随 m 递减，停手。 |
| 3 / `04dd29f81fcf1677ef4ad4b86be3fbb863eeb4167724eb18e3e10933df9f981c` | `pointer`：§27.1 归宗与方法说明，列出四类不等式但没有它们的量词、对象及具体恒等式。 | — | — | 不能：没有本段独立定义的输入、散度或待验等式；检验某个 KL 不等式不能验证「全部不许」的族谱叙事。 | 若实施需要自行选择「全部禁令」的集合或以一个散度定理代替四旗舰，停手。 |
| 4 / `059456004ce26fdd82f64331275e58b8c5318b63da997250daa523d6a5cf70f9` | `proposition`：朋友记忆上的相干操作及 CHSH 证书可陈述；FR / PBR / Local Friendliness 不是同一命题。 | 对每个整数 r≥1，在 (ℂ²)⊗(r+2) 上令 ψᵣ=(e₀⊗(r+2)+e₁⊗(r+2))/√2，A₀=Z_F₁，A₁=X_S⊗X_F₁⊗⋯⊗X_Fᵣ，B₀=(Z_B+X_B)/√2，B₁=(Z_B−X_B)/√2（未写因子取 I，X、Z 为 Pauli 矩阵），则 ⟨ψᵣ,(A₀B₀+A₀B₁+A₁B₀−A₁B₁)ψᵣ⟩=2√2 且对所有 1≤j≤r 有 [A₁,Z_Fⱼ]≠0。 | — | 可验该数学子句：Q 算法 r=1,2,3 均得 2.828427124746，四相关为 0.707106781187,0.707106781187,0.707106781187,−0.707106781187；每份记忆的交换子作用在 e₀ 上最大分量绝对值为 2。 | 若用普通 Bell 的 2√2 直接覆盖 Local Friendliness 三前提矛盾、FR 或 PBR，或遗漏残存记录副本，停手。 |
| 5 / `06bd6d9ddb9fa0d591eb72e8d316150ad6e59e0592cf7b0daccc4c076b471026` | `needs-input`：「整体意志」「倾向」「整体选择」没有给出可操作的建模对象；不能从全局索引的存在推出关于意志的命题。 | — | — | 不能复跑原证书 −2.8257：未给 λ* 的样本空间、分布、设置依赖律、观测映射及随机样本；一个邻近 −2√2 的数不证明全部统计等同。 | 未明确全局选择机制、设置独立性和观测等价所量化的实验族之前，停手。 |
| 6 / `08688691d8bb7830970659d82cc3df94425187e73c00feed081c7e99620cc7dc` | `pointer`：旧版主张与不主张的卷首范围说明，未给独立定理的对象、前件及结论。 | — | — | 不能：这是研究范围声明，「强制出身」须回到具体构造的泛性质及前件，不是一个数值等式。 | 若将本段「强制」当作可省略复 C* 框架、张量积或更新生成元前件的依据，停手。 |
| 7 / `0aeb6b17305b0ea10af6e81726ca256b1a737c1a68f3bd78436f0a9d30d17a06` | `proposition`：量子 Fenchel–Young 恒等式有明确数学内容；本段同时夹有不能原样照收的「不裂」等价链。 | 对所有 d≥1、正定复 Hermitian 矩阵 ρ∈M_d(ℂ)（Trρ=1）及 Hermitian H∈M_d(ℂ)，令实数 Z=Re Tr(exp H)>0、G=(1/Z)exp H、S(ρ)=−Re Tr(ρ logρ)、D(ρ∥G)=Re Tr(ρ(logρ−logG))（矩阵 log 用正定谱演算），则 log Z=Re Tr(Hρ)+S(ρ)+D(ρ∥G)，特别 H=0 时 S(ρ)+D(ρ∥I/d)=log d。 | — | 可：G 算法以非对易的二阶矩阵直接从 G 的谱计算 D，a=0,1/2,1 时 D=0.082282878505,0.341738727333,0.794746392727，等式残差绝对值≤4.45×10⁻¹⁶；附带 R 探针给退化配对根基 4 元且交换子非平凡，阻止无条件照收「不裂⇔完美」。 | 若要覆盖本段其余辛化、张量分解或最小化子句，必须先另定其辖域；尤其把「中心扩张不裂」等同于「配对非退化」时停手。 |
| 8 / `0deef6acac3ce522f8d16e6189500f05450970b4f161070e3d90eb8f661635e3` | `pointer`：§39.1 是结算地图；未定义「测地线时钟」或点明所指恒等式。 | — | — | 不能：没有测地线类、长度规范与时钟周期的公式，2π 不能独立复现；三色出生证明也只是索引。 | 若需要自行发明时钟的定义以凑出乘积 2π，或把「本体无洞」当数学完备性，停手。 |
| 9 / `135661d3c97d7ce6dbb5769d4c61e38cbbe6899602df26098f8e092a6dc8a784` | `pointer`：§38.2 总结周期及封存边界，「锥、球、张量律」均为回顾指称，无独立命题。 | — | — | 不能：未给被重构的对象族或所需公理，摘要意象没有独立数值输入。 | 若将「选出复数的张量律」直接改写成没有重构公理的唯一性定理，停手。 |
| 10 / `13f6e0af21c9969253940a6564dea347af2a340de7a7c5f7c2c21988fb79fe8d` | `proposition`：模流与外自同构类是已定义的数学对象；「兑物理时间」不随数学自动成立。 | 对任意作用在复 Hilbert 空间上的 von Neumann 代数 M 及忠实正规态 φ、ψ，令 σ^φ、σ^ψ 为各自标准模自同构群，则存在强连续 u:ℝ→U(M)，使所有 s,t∈ℝ 有 u(s+t)=u(s)σ_s^φ(u(t)) 且 σ_t^ψ=Ad(u(t))∘σ_t^φ，因而二者在 Out(M)=Aut(M)/Inn(M) 中逐时相同；当 M=M_d(ℂ)、d≥1、φ(A)=Tr(ρA)、ρ 正定且 Trρ=1 时，对所有 t∈ℝ、A∈M_d(ℂ)，σ_t^φ(A)=ρ^(it)Aρ^(−it)，其外类恒等。 | — | 无穷维唯一性不能由数值验证；有限维边界可运行 T：ρ=diag(1/3,2/3)，t=0,1,2 时 σ_t(E₀₁) 的系数为 1、0.769238901364−0.638961276314i、0.183456974743−0.983027740411i，演示「外类平凡」不等于流本身平凡。 | 若第三方只将结论放进假设、或把有限维外类恒等写成所有 σ_t 恒等、或据模参数推物理秒，停手。 |

### G、R、T：Gibbs 恒等式、退化配对边界及有限模流（已实跑）

G 用 ρ=diag(0.3,0.7)、H=R diag(a,−a) Rᵀ，其中 R 是角 0.4 的实旋转；G 的两个特征值各自取 log，未用待验恒等式定义 D。本段只用标准 Python 3。

```python
from math import log,exp,cos,sin
from cmath import exp as cexp
p=0.3; c=cos(0.4); s=sin(0.4)
for a in (0.0,0.5,1.0):
    g0=exp(a)/(exp(a)+exp(-a)); g1=exp(-a)/(exp(a)+exp(-a))
    H00=a*(c*c-s*s); H11=-H00
    S=-p*log(p)-(1-p)*log(1-p)
    D=(p*(log(p)-(c*c*log(g0)+s*s*log(g1)))
       +(1-p)*(log(1-p)-(s*s*log(g0)+c*c*log(g1))))
    Hmean=p*H00+(1-p)*H11; logZ=log(exp(a)+exp(-a))
    print('G',a, S, D, logZ, logZ-Hmean-S-D)
    assert abs(logZ-Hmean-S-D)<1e-12
V=[(a,b) for a in range(4) for b in range(4)]
def comm(v,w): return (-1)**((v[0]*w[1]-v[1]*w[0])%2)
rad=[v for v in V if all(comm(v,w)==1 for w in V)]
print('R',rad,comm((1,0),(0,1)))
for t in (0,1,2):
    z=cexp(1j*t*log(0.5))
    print('T',t,format(z.real,'.12f'),format(z.imag,'.12f'))
```

R 输出 `[(0,0),(0,2),(2,0),(2,2)]` 和 `-1`；对应 (ℤ/4)² 上 bicharacter 的交换子。可取中心扩张 (ℤ/2)×(ℤ/4)²，乘法为 (c,a,b)(c′,a′,b′)=(c+c′+ab′,a+a′,b+b′)，各坐标分别模 2、4、4；其交换子非平凡，而配对根基非平凡。这是原文未加限定的等价链的停止信号，不是本席交付的 kernel 反例，也未对账本作 refutes 操作。

### Q：相干记录的 CHSH（标准 Python 3，已实跑）

张量位从低到高是 B、F₁、…、Fᵣ、S；最后的交换子读数来自直接作用在 e₀ 上。

```python
from math import sqrt
for r in (1,2,3):
    d = 2**(r+2)
    psi = [0.0]*d
    psi[0] = psi[-1] = 1/sqrt(2)
    def flip(v,mask): return [v[i^mask] for i in range(d)]
    def z(v,bit): return [(-1 if i & (1<<bit) else 1)*v[i] for i in range(d)]
    def add(v,w,sgn=1): return [a+sgn*b for a,b in zip(v,w)]
    def alice(v,a): return z(v,1) if a==0 else flip(v,d-2)
    def bob(v,b):
        return [x/sqrt(2) for x in add(z(v,0),flip(v,1),1 if b==0 else -1)]
    E = [sum(x*y for x,y in zip(psi,alice(bob(psi,b),a)))
         for a,b in ((0,0),(0,1),(1,0),(1,1))]
    e0 = [1.0]+[0.0]*(d-1)
    comm = [max(abs(x-y) for x,y in
                zip(alice(z(e0,j),1),z(alice(e0,1),j))) for j in range(1,r+1)]
    print(r, format(E[0]+E[1]+E[2]-E[3],'.12f'),
          [round(x,12) for x in E], comm)
```

### E：有限清单逃逸率（标准 Python 3，已实跑）

```python
from itertools import product
from fractions import Fraction
for n,m,f in [(2,1,(0,1)),(2,2,(0,1)),(2,3,(0,1)),
              (2,1,(1,0)),(2,2,(1,0)),(2,3,(1,0)),
              (3,1,(0,0,0)),(3,2,(0,0,0))]:
    k = sum(f[i] == i for i in range(n))
    total, escaped = n**(m*m), 0
    for g in product(range(n), repeat=m*m):
        diag = tuple(f[g[i*m+i]] for i in range(m))
        escaped += all(tuple(g[i*m:(i+1)*m]) != diag for i in range(m))
    expected = (1-Fraction(k,n**m))**m
    print((n,m,k), f'{escaped}/{total}', Fraction(escaped,total), expected)
    assert Fraction(escaped,total) == expected
```

## 检索收据

- 本仓 D5：`rg` 查询 `escape.*rate|list.*escape|chsh|pinching` 先粗筛；随后完整读取 `D5/S0/Diagonal/EscapeCount.lean`、`D5/S0/Asymptotics/FixedPointFreeEscapeProbability.lean`、`D5/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge.lean` 的公开面及上下文。命中一般计数，不能用 private 等价替代。该计数模块冻结状态片存在；不重算其既有声明身份。
- 钉版 mathlib：使用本机已有 mathlib checkout，只读；`git rev-parse HEAD` 为 `db584cd6d46c92f209a44c0f1c829460d327499d`，与本工作树 `lake-manifest.json` 一致。不创建本树 `.lake`。本席没有可调用的 Lean LSP MCP，当前 bind 判断依据是完整声明源码、作用域和既有冻结状态；没有声称做过跨模块编译验证。
- 第 4 条：完整读取 `D5/S3/QuantumBounds/CHSHWitness.lean` 的公开面，`bell_chsh_value` 是两 qubit Bell 态的数值，不能冒充含任意多份朋友记录的全句；其中 `kronecker_self_adjoint` 等 helper 是 private。D5 / pin mathlib 的 `wigner.*friend|friendliness` 查询没有得到本句完整声明；GitHub `gh search code '"Wigner" language:Lean' --limit 10` 返回若干 Wigner 名词候选，不能以名字作为命中。这是有界检索，不是全生态无实现证明。
- 已打开 [Bong 等，A strong no-go theorem on the Wigner's friend paradox](https://arxiv.org/abs/1907.05607) 摘要，HTTP 200，44477 bytes，SHA-256 `7a731b228459022e9e6da3815170a0957941dba865dba4333f1f52f9ec7ac996`；DOI `10.1038/s41567-020-0990-x`。摘要明确说 Bell-type inequality violation **is not in general sufficient** 证明这三个前提的矛盾。只核对摘要，正文 `ASSUMED-UNVERIFIED`；不据该摘要宣称原 atom 的整个 no-go 推理已证明或已反驳。
- 第 7 条：读取母账 `PZG_BEDC.md` 的 27.606–27.607 对偶段，定位到 FY 及「不裂」原义；D5 查询 `fenchel|gibbs|pinching` 后完整读取 `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.lean`，公开 `quantum_relative_entropy_eq_neg_entropy_sub_cross` 与 `von_neumann_entropy_pinching` 给分解及有条件捏合等式，不是本句的 Gibbs 对数谱演算或全部辛化链。未将其 private helper 当命中。pin mathlib 同词查询未定位完整 FY 定理；第三方 GitHub `"Fenchel" language:Lean` 首 10 项只是候选，未逐个打开的均为 `ASSUMED-UNVERIFIED`，不声称生态检索穷尽。
- 第 10 条：D5 / pin mathlib 查询 `tomita|takesaki|modular.*automorphism|connes.*cocycle`。pin `Mathlib/Analysis/InnerProductSpace/StandardSubspace.lean` 开头明确把 Tomita theorem / KMS 列为 TODO；这是该文件的边界，不外推为整个生态不存在实现。
- 第三方 `"modularFlow" language:Lean` 返回两项，已取并读取相应作用域：① [TomitaTakesakiBridge.lean](https://github.com/gvakhrushev/d0_15/blob/e57b8fb69cfd05c244184fe99e45bfb6fed40ba5/09_LEAN_FORMALIZATION/D0/Bridge/TomitaTakesakiBridge.lean)，HTTP 200，1697 bytes，SHA-256 `ade7c029d9a289d0be5b76e1ae90ca3fac06ee5cbe18cc184f492e355ed2d6b7`；公开 `tomita_modular_flow_conditional` 只是投影 `h.cited`，不是模流存在唯一性的证明。② [TomitaMatsubaraAQFTSpineBridge.lean](https://github.com/jagg-ix/catept-main/blob/01f70e0e3cf8a25f07cb4f989e3eeadff235e843/CATEPTMain/Integration/TomitaMatsubaraAQFTSpineBridge.lean)，HTTP 200，11009 bytes，SHA-256 `31c1fe44bad45065a7be7424caaf9cf84fae1b7bb7e779e67eadd39f69c4ebe6`；已读 Honest scope 与 carrier 定义，它明确保持 Tomita–Takesaki 为 hypothesis-level，实数 surrogate 不构成所需命中，传递 import 未核验。

## 未主张

未主张任何数学命题已获 Lean 验证、任何 residual 已闭合、任何开放物理问题已解决；不选择、排序或推荐四个 τ=0 候选。未运行 `make lean`，耗时和 `LEAN_CACHE` 均为不适用；尚未打开的外部页面一律 `ASSUMED-UNVERIFIED`，不作命中依据。

用户列出的六个富矿起点不在本次已分类的前 10 条中，尚未完成其独立复核；尤其没有把 `36a5eee4…` 的黄金分账 bind 判定外推到其余子句。本席结果是部分分类交付，不是 131 条普查完成，也不是 proposition 原 atom 全段已获得覆盖。

## 交付核对

已核对表中恰有 10 条、每条恰为身份加五项、ID 恰为 residual-open 字典序前缀；分类计数为 proposition 3 / bind-only 1 / pointer 5 / needs-input 1。逐条 show-atom 日志均完整且 exit 0。报告三个 Python 代码块从 markdown 原样抽出执行，均 exit 0，输出保存在 attempt 的 `numerical-validation.log`。`make -C tools capacity-audit` 返回 `CAPACITY_AUDIT_RESULT exit=0 reason=clean`。这些检查不构成 Lean 验证。
