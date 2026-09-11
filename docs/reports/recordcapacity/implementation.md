# Record capacity implementation

**交付形状：2（退化形），附带显式结构同构下的锐界。**
主结果是：对任意有限维复矩阵共享群作用 U，有限个非零、两两正交、
和为单位且与 U 等变的幂等元，其条数不超过实际 commutant 的复维数。
自伴记录属于这个更强的代数结论；证明不需要自伴假设。
这是在假设「存在共享对称性且记录等变」之下的界，不是对任意记录结构的界。
物理输入仍在假设位。

还完成了两个相接的结论：
- 给出实际 commutant 到 Π_b M_(m_b)(ℂ) 的代数同构，则条数 ≤ Σ_b m_b。
- 假设实际 commutant 半单，直接调用钉版 mathlib 的 Wedderburn–Artin，
  得到一组非零块大小及同构，**同一组块大小**约束所有有限记录族。
  结构存在与计数使用同一个 e，不是两个无关的存在性陈述。

**与形状 1 的差距**：没有把一个另行指定的表示分解
⊕_i (irrep_i ⊗ ℂ^(m_i)) 转成 commutant 的同构，亦没有证明所得块大小
等于那组指定的表示重数。不能把本次结果报告为完整的一般重数律。
最锐剩余子命题：从互不同构的复不可约表示及其有限重数分解，构造
`commutant U ≃ₐ[ℂ] Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ`。
完成此项后可直接应用本模块 `equivariant_record_card_le_sum`。
半单性不是任意群作用的自动结论，当前保留为显式假设。

commutant 维数是有限线性代数不变量：当群有限或已给有限生成矩阵时，
用方程 X U(g) − U(g) X = 0 求公共核维数即可计算。
当前没有交付一个 Lean 可执行求解器；没有把 `finrank` 宣称为可执行算法。

产地：Codex implementation worker，使用 lean4 skill；单点实施与自查，
本席零独立评审、未开 PR。orchestrator 的亲验与混合评审不由本席代报。

## 检索收据

预登记见 preregistration.md，先于 Lean 实施提交 `b4e41837d1`。
钉版 mathlib 为 `db584cd6d46c92f209a44c0f1c829460d327499d`。

| 检索范围 / 查询 | 实测结果与使用边界 |
| --- | --- |
| D5，commutant / orthogonal idempotent / RecordCapacity | 无现存容量界；WindowRegister 的特定标量交换子结论不是本题 |
| Mathlib，Matrix.isSimpleModule / isSimpleModule + Matrix | 未命中该字面声明；不由建议名字推断存在 |
| RingTheory/SimpleModule/Isotypic | 命中 IsIsotypicOfType.linearEquiv_fun、isotypicComponents、endAlgEquiv |
| RingTheory/SimpleModule/WedderburnArtin | 命中 IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end；终点是简单模 End 环上的矩阵块，非指定复重数 API |
| RingTheory/SimpleModule/IsAlgClosed | 精确命中 IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed；本模块直接应用 |
| RingTheory/Idempotents | 复用 CompleteOrthogonalIdempotents 及映射；文件内未命中条数界 |
| LinearAlgebra/Trace | 直接复用 LinearMap.IsProj.trace、LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero |
| Data/Matrix/Block；Algebra/Algebra/Bilinear | 直接复用 blockDiagonal'RingHom、blockDiagonal'_injective、Algebra.lmul、lmul_injective |
| GitHub，OrthogonalIdempotents + linearIndependent + language:Lean | 3 命中；打开 TauCeti/RingTheory/Idempotents/LinearIndependent.lean，已有精确线性无关定理，未重证/移植它 |
| GitHub，idempotents + card + finrank | 16 命中；打开相关 CharacterTable/IdempotentDecomposition，处理中心幂等元基而非本计数界 |
| GitHub，orthogonal + idempotents + trace | 8 命中；后续 idempotent + sum + finrank + trace 为 27 命中；打开 TauCeti/RepresentationTheory/FDRep，处理表示特征标及缩并，不是容量界 |

第三方核对的 TauCeti 修订为 `04feb87e78a129fb9a95a24fea45da8ab92ca09a`。
查询通过 authenticated gh search/code 实际出网；两个被引用 mathlib 源文件
通过 raw.githubusercontent.com 成功取回。这里只声称给定查询及已读文件范围，
不声称全部命中全文已读或全球检索穷尽。没有新增第三方依赖。
一般表示路线停在「指定重数识别」这一类型层接口；没有重证已存在的结构定理。

## 判形、活路径与用途

`admission_basis: escape-witness`。见证是
`card_le_finrank_of_idempotent_sum` 中的正整数秩求和估计：
非零幂等元的像秩 ≥ 1，求和后用迹预算得到条数界。
这不是定义体的 rfl；没有任何已命中的上游计数界可直接实例化得到本结论。
其证明项直接进入实际 commutant 界和矩阵块界，后者又进入半单结构存在定理。

所有公开定理的直接冻结 D5 依赖均为空（故 GID/statement_id 对均为空）；
本模块只导入 Mathlib。没有借用尚未合入的 RecordSymmetryNoGo。

| 公开定理（模块内后缀） | proof_shape | escape_witness / 方向 |
| --- | --- | --- |
| sum_range_finrank_of_idempotent_sum | bind-only，伴随引理 | 上游投影迹与迹线性；card_le_finrank_of_idempotent_sum → 本引理，履行秩预算义务 |
| card_le_finrank_of_idempotent_sum | content | 正秩有限求和的新估计链，结论自身为见证 |
| algebra_card_le_finrank | content（内联本模块前置后） | algebra_card_le_finrank → card_le_finrank_of_idempotent_sum |
| equivariant_record_card_le_commutant_finrank | content（同上） | 本定理 → algebra_card_le_finrank → 计数见证 |
| matrix_blocks_card_le_sum | content（同上） | 本定理 → card_le_finrank_of_idempotent_sum；忠实块对角作用给出较小载体 |
| equivariant_record_card_le_sum | content（同上） | 本定理 → matrix_blocks_card_le_sum → 计数见证 |
| semisimple_commutant_has_record_capacity | content（同上） | 本定理 → equivariant_record_card_le_sum；上游结构所产同构在活计数路径中使用 |

`utility: none`：每条均为任意有限类型上的一般代数定理，
没有有界枚举、checker、数值归约或有限认证实例。两项定义仅命名实际交换子
及等变元的子类型嵌入，并被公开计数定理使用。

## 五组独立复算

复算用 SymPy 1.14.0 的精确有理数矩阵秩，无浮点容差。
每个不可约块取一张谱互不相交的对角矩阵及循环移位矩阵；按指定重数复制。
约束矩阵为竖向拼接的 Uᵀ ⊗ I − I ⊗ U，公共核维数为 N² − rank。
对角谱在不同块间不相交，单块的循环移位连通所有坐标。
这是一组独立重建的代表，不是对 orchestrator 未提供的原矩阵/脚本逐字重跑。

| mults | dims | N | 约束秩 | commutant 维数 = Σ m² | Σ m |
| --- | --- | ---: | ---: | ---: | ---: |
| [1,1] | [2,3] | 5 | 23 | 2 | 2 |
| [2] | [2] | 4 | 12 | 4 | 2 |
| [2,1] | [2,3] | 7 | 44 | 5 | 3 |
| [3] | [2] | 6 | 27 | 9 | 3 |
| [2,2] | [2,3] | 10 | 92 | 8 | 4 |

五项与用户转述的读数一致。有限读数不作 Lean 证明或用途准入见证。
未复算：orchestrator 原始生成器、原脚本、物理记录的实现、量子互信息、
给定物理系统是否存在共享对称性。上述均未作为本次已验结论。

## 失败与修复

首版 LSP 胶水在 hover 返回时退出，读到初始空诊断，不构成完整检查。
serial-lean 首轮实际判 `partial built=4 failed=1 missing=5`，没有被杀。
改为等 `$/lean/fileProgress` 的 processing 为空再读取最终诊断，定位到
显式参数、命名空间和 Subalgebra 求和强制转换三类接口错误，逐项修正。
第二轮串行构建 `complete built=1 failed=0 missing=1`，exit 0。
未碰两个用户点名的高内存模块；未发生作业被杀或孤儿重叠。

## 落点与验证

D5/S3/Quantum/Matrix 为 7/48；对应 Blueprint 排除 .md 后为 7/48；
Library/Quantum 为 22/48。Quantum 在 Meta/domains.yaml 注册为 S3。
本模块 generality=G，只 import Mathlib，无 G→I 的 D5 边。
验证最终收据在完成门链后补于下文。

已取得的门链收据（冻结前）：
- `serial-lean.sh /Users/chronoai/trureturing-a392714bridge` exit 0：
  `SERIAL_LEAN status=complete built=1 failed=0 missing=1`。
- `make lean-report` exit 0；report SHA-256：
  `2edc38740885e575e3f157c54ce0346675d36d2f50be36ced9379958e7289615`。
- 新模块 11 个报告声明（包含编译器生成声明）公理闭包均只含
  `Classical.choice`、`Quot.sound`、`propext`；`sorryAx=0`、非标准公理=0。
  用户源码为 7 条公开定理、2 项定义；源码 axiom/instance/sorry/native_decide 均为 0。
- `make emit` exit 0，新增一个 Blueprint 投影。
- 指定 `scribe-content-checks.sh` exit 0，第三参数为精确 merge-base
  `5634f82fdcf3f8970ba9501cdcce1de5f2536976`。
  判词：`DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11136
  suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=5006`；
  `^RED` 行为 0；`markdown: judged=1 formula(s)=0 red=0`。

原始日志与公理报告片段在本次 runner attempt 中，文件名分别为
`serial-lean-2.log`、`lean-report.log`、`emit.log`、`scribe-content-checks.log`、
`RecordCapacity-report.json`、`recompute.py`、`recompute.json`。

## 可复算的诊断脚本

```python
import sympy as s, json
from pathlib import Path
out=[]
for mults,dims in [([1,1],[2,3]),([2],[2]),([2,1],[2,3]),([3],[2]),([2,2],[2,3])]:
 diag=[];shift=[];offset=1
 for m,d in zip(mults,dims):
  D=s.diag(*range(offset,offset+d));S=s.zeros(d)
  for j in range(d):S[(j+1)%d,j]=1
  diag.extend([D]*m);shift.extend([S]*m);offset+=d
 generators=[s.diag(*diag),s.diag(*shift)];N=generators[0].rows
 # Column-vectorized commutator: vec(XU-UX)=(U^T tensor I-I tensor U)vec(X).
 constraints=s.Matrix.vstack(*[s.kronecker_product(U.T,s.eye(N))-s.kronecker_product(s.eye(N),U) for U in generators])
 rank=constraints.rank();dim=N*N-rank
 row={'multiplicities':mults,'irrep_dimensions':dims,'carrier_dimension':N,'constraint_rank':rank,'commutant_dimension':dim,'sum_squares':sum(m*m for m in mults),'sum_multiplicities':sum(mults)}
 assert dim==row['sum_squares'];out.append(row)
print(json.dumps(out,indent=2))
Path(__file__).with_name('recompute.json').write_text(json.dumps(out,indent=2)+'\n')
```

## 本席终局

**成（上述形状 2 及显式结构同构下的锐界）。**
`make deposit-uncovered` exit 0；
`LEDGER_ALIGN selectors_considered=4052 changed=0 added=1 unchanged=4051 conflicts=0`；
`PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED
 gid=D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_commutant_finrank
 reason=NO_ATOM`。
冻结事件文件为
`Golden/Frozen/accepted/04b3c32c6e6617522663ebaaf2b76023406607b7c04304985ac3fc6face313bb.json`，
成员状态片为 `Golden/Frozen/state/D5/S3/Quantum/Matrix/RecordCapacity.lean.json`。
这是 deposit-uncovered，无 atom 摄入或覆盖。完整一般重数识别仍未交付。

门链完成后不再扩展代码或重跑门，提交冻结产物并推送本分支。
本席未开 PR，未调用 pr-open，未设置 auto-merge；未声称远端三门或 MERGED。
PR、orchestrator 亲验、独立评审及合并由调用方负责。
