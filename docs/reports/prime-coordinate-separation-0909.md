# S16 坐标分离:纸面核验与来源附记

本报告是 caller 的 `consensus-rnd:sshx` 编排下 Codex CLI I11 的一次实施附记。
数学主输入来自实际 GPT PRO;caller 提供符号、整数、文献和记号核对;
I11 负责本卷追加、有限自查及 canonical ingestion。I11 没有调用子 worker 或新 oracle,
没有读取同轮评审、worker 日志、opaque log_ref 内容、邻近活跃工作树或 caller 会话。
这些来源不是三票独立 review;本报告不是独立评审、Lean 认证或 MERGED 交付。
长期问题仍在理论卷中记录,本报告不另建可变进度登记。

1. **输入身份与本地对照范围。** 仓库为
   https://github.com/the-omega-institute/trureturing,
   工作树 `/Users/auricstudio/trureturing-qgh-separation`,
   分支 `lane/math/quantized-gh-separation-0909`。
   `391f7355698085c6500b46838a093dad05947ffb` 是本轮
   **implementation-input HEAD / ingestion BASE**,不是后续 review-candidate HEAD。
   开始实施时本地 HEAD 与此相等,工作树干净。I11 已完整分段阅读本树
   `CLAUDE.md` 和 `agents/CONTEXT.md`;首次大输出截断后补全阅读,没有把截断当作完整。
   依明确授权,只追加
   [ARITHMETIC_BOUNDARY_QUANTIZATION.md](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md)
   第 27 节和本报告,其余新增文件由指定 ingest 产生。

   原卷前缀 176107 字节、3134 行,SHA256
   `4bbc7e0bbcd387c52a73d362ab78b61d00faf810d45d58df98b426e6fc34a266`。
   I11 在追加前核对此身份,追加后逐字节检查同一前缀身份。
   追加后源为 201529 字节、3627 行,SHA256
   `b7cb35d87d0a7b7e569c49ab57f2b556c454257de8bd65899587d13be1338537`;
   本次追加 25422 字节、493 行,包含 20 个连续编号的实质单元。
   本地去重为本卷第 1-26 节的字面检索及相关第 26 节论证连读:
   26.4 已有实际角点与正定义域,26.10-26.11 已有匹配价格/原始证书与上端点界,
   26.13-26.17 已有固定箱体有限支配。它们在本轮复用,不冒称新发现。
   26.8 的非负距离向量范数单调性,与新增的全实向量函数
   `ell(x)=mean(x)-norm(Pi*x)/sqrt(k*(k-1))` 单调性是不同陈述。
   本地检索没有发现第 27 节的坐标分离 guard 或固定正整数方向 cutoff。
   该对照不是全库声明搜索、穷尽文献搜索或新颖性证明。

2. **primary 的调用事实与不可改写的历史限制。** 唯一数学 primary 为
   task `a9d1269e-64ae-4a9a-b90f-8982ff023ee6`,
   conversation `conv_224b6f5d1adc6409`,观测模型 `GPT-6 Astra`,
   完成时间 `2026-09-09T14:39:45.418+00:00`,conclusion verdict `proved`。
   所供完成元数据记录 envelope SHA256
   `585ba5af088e0446397c1af7eaebb1bd6c6add7979e014fc091fb032af0e53d3`,
   raw-response SHA256
   `be4a315d8f50bd5ebb439ec6265f900d70900d665a19a607ce3198c58fa0a18d`。
   后者是完成记录中的身份,本轮没有获取或重读另一个原始响应/日志载体。
   primary 原先无法获取给定 immutable raw URL 和 GitHub blob URL,
   因而没有检查仓库全文或其内容身份,没有提供 PR/merge 状态;
   当时采用的是请求中完整提供的定义及前置结论。
   caller 后来检查封存源和 S14,以及 I11 此次本地对照,都不将这段历史改成
   “primary 已独立读过仓库”。I11 为 repo-prior-exposed,
   primary 为 external-prior-exposed;不声称 sterile priors 或模型族多样性。

3. **caller 的核验范围与两个记号订正。** 所供
   `caller-separation-symbolic-checks-0909.json` 报告 10 项固定符号/整数检查通过,
   覆盖投影坐标范数、归一化、三元组中心化范数、半径、几何平方差、
   k=3 Bernoulli 余项、27 因子、limb carry、固定窗口容量和既有反射槽计数。
   该记录使用 SymPy 1.14.0,文献提取使用 pypdf 6.18.0。
   这是 caller 的有界支持证据,不是独立 review 票,更不是无限域定理的机器证明。
   I11 的另一次固定检查见第 6 项,使用标准库而不依赖这些包版本。

   原压缩 token `-31[q=3]` 必须展开为 `-3 * indicator(q=3)`,
   其唯一来源是 `27=3^3`。故
   `z_q=(b_i2+1)*indicator(q=p_i2)-(b_i1+4)*indicator(q=p_i1)-3*indicator(q=3)`;
   基中的 3 只出现一次,标签本来为 3 时合并贡献。
   原 `255255+255+255` 必须展开为 `255*255+255+255=65535`。
   这里是每次内积立即进位的数学界,不是已验证的 MPS 操作。

   稳定布局继续为 `box_id=4096*t+256*b0+16*b1+b2`;
   slots 0..6 为相邻对;slots 7..24 使用
   `r=slot-7,j=1+floor(r/3),i=r mod 3`,即 `slot=7+3*(j-1)+i`,
   `i=0,1,2`、`j=1..6`;`row_id=25*box_id+slot`。
   primary 的 `7+6*(i-1)+(j-1)` 使用 `i=1,2,3`,是另一排列,
   本轮明确披露为未采用的呈现。既有 ID 没有重新编号。
   一个未来箱证书可条件覆盖全部 25 个 raw IDs,意思是“若可容许则排除”,
   不等于 25 个 admissible slabs,也不等于 25 次数值评价。

4. **经典文献的核对链。** 来源为 Boyd/Vandenberghe,
   [Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)。
   caller 提供的完整 PDF 为 6881335 字节、714 页,SHA256
   `40d976c83c18cce1900eff8c41bd5ad408c102b813af39d05ff85678ccf8d76e`;
   I11 核对了 PDF 字节身份,并读取供给的相应文字摘录和 source-check receipt。
   I11 没有重新联网取得该书,也没有声称独立核对全书 glyph 或全部论证。

   | 经典材料 | caller 检查的位置 | 本节承担的专门化 |
   | --- | --- | --- |
   | 范数齐次性、三角不等式 | A.1.2,印刷 p.634 / PDF p.648 | 27.4 自足推出投影增量界与精确等号 |
   | 每个范数凸,三角不等式和齐次性证明 | 3.1.5,印刷 pp.72-73 / PDF pp.86-87 | 仅作经典背景,不把范数凸性冒充坐标单调性 |
   | 严格一阶支撑不等式 | 3.1.3,式 (3.3),印刷 p.70 / PDF p.84 | Bernoulli 可由此理解,但 27.6 直接用有限几何和证明 |

   receipt 保留的获取异常是:第一次 45s curl 在 3719168/6881335 字节时超时,
   第二次续传 45s 后又超时,增得 524288 字节,第三次续传完成并 exit 0;
   `pdftotext` 不可用(exit 127),依赖缺失文本的 rg exit 2,随后以 pypdf 继续。
   pypdf 有缺少 fontTools 的 CFF encoding warnings,但所需范数公理、范数凸性证明及
   式 (3.3) 可读并已检查。这些是 caller 供给的历史事实,不是 I11 亲跑的网络命令。
   不把本问题的素数结论归给该书。范数、Bernoulli、唯一分解及抽屉论证在正文闭合;
   专门化分类为 repo-derived paper arguments,无穷尽 novelty、Lean 或 RH 声明。

5. **精确域与不能外推的部分。** 27.2 的较弱分析域为有限正二点网格、
   一个实际角点、`M0<=M1`;原域仍要求不同素数、非负实际指数、严格宽度、
   两个实际角点及 `Q+log(5040)<M0`。平移坐标的幂指数严格正。
   全 `R^k` 单调性自身无需正性。`u>0` 时增量取等当且仅当
   `Pi*x=lambda*Pi*e_i` 且 `lambda>=0`;包含零方差,不可改写成处处严格。
   `L>=ell(c)` 使用一个真正可行角点,无步宽罚项。
   初等阈值等号仍有严格 Bernoulli 步;精确标量阈值等号的严格性来自
   其它有限上端点的负贡献。两者都给依赖箱体的正负裕量。
   k=2 的这两个阈值前提为空,不影响已有二坐标结果。

   三坐标 `1/3` 在有序实几何中尖锐,不代表素数排除常数最优。
   最小坐标标签随其步长移动,未假定它是最小素数。
   整数 guard 的非严格条件足够,但不同素数域无法取等。
   射线 cutoff 和可选非空域界均为精确 floor/ceiling 公式,未计算任何认证数值 cutoff。
   量词仅为每条固定正整数方向、固定非负截距的最终排除;
   不覆盖零方向分量或任意无界序列,也不提供跨射线/跨箱统一负裕量。
   无理对数与抽屉构造给全部指数趋无穷而最小两坐标差趋零的箱体,
   最终逃避这个充分整数 guard,并可取非空原域。
   guard 失败没有建立符号。另行在研的 relative-spread PRO 结论不是本次输入。

6. **可复现的有界固定检查。** 以下 Python 只核对六个固定多项式恒等式和
   四个固定整数/布局事实。多项式是二元有理系数的有限系数字典,
   字母复用不表示在参数上取样;投影恒等式中的 k 是符号。
   唯一迭代集合是这些多项式的有限单项式和 18 个反射槽指标。
   不枚举素数、指数箱体、候选薄层或任何已有固定-xi 区间。
   固定窗口的 `27*19**19` 只是位宽上界操作数,不是候选搜索。
   本轮用 Python 3.9.6 运行这一代码;不引入仓库测试框架或 kernel 改动。

```python
from fractions import Fraction as F
import json

def add(*polys):
    out = {}
    for p in polys:
        for monomial, coefficient in p.items():
            out[monomial] = out.get(monomial, F(0)) + coefficient
    return {m: c for m, c in out.items() if c}

def scale(c, p):
    return add({m: F(c) * v for m, v in p.items()})

def mul(p, q):
    return add(*[{(a[0] + b[0], a[1] + b[1]): u * v}
                 for a, u in p.items() for b, v in q.items()])

one = {(0, 0): F(1)}
x, y = {(1, 0): F(1)}, {(0, 1): F(1)}
checks = []

def check(name, actual, expected):
    assert actual == expected, name
    checks.append(name)

km1 = add(x, scale(-1, one))
check('projection_norm_cross_multiplied',
      add(mul(km1, km1), km1), mul(x, km1))
disc = add(mul(x, x), scale(-1, mul(x, y)), mul(y, y))
mean = scale(F(1, 3), add(x, y))
centered = [scale(-1, mean), add(x, scale(-1, mean)),
            add(y, scale(-1, mean))]
norm2 = add(*(mul(v, v) for v in centered))
check('ordered_triple_norm_squared', norm2, scale(F(2, 3), disc))
check('ordered_triple_radius_squared', scale(F(1, 6), norm2),
      scale(F(1, 9), disc))
check('geometric_squared_difference', add(mul(y, y), scale(-1, disc)),
      mul(x, add(y, scale(-1, x))))
omx = add(one, scale(-1, x))
check('strict_bernoulli_k3_remainder',
      add(mul(mul(omx, omx), omx), scale(-1, one), scale(3, x)),
      mul(mul(x, x), add(scale(3, one), scale(-1, x))))
check('threshold_geometric_sum_k3', mul(omx, add(one, x, mul(x, x))),
      add(one, scale(-1, mul(mul(x, x), x))))
check('prime_factor_27', 3 ** 3, 27)
carry_value = 255 * 255 + 255 + 255
check('corrected_multiply_carry', (carry_value, divmod(carry_value, 256)),
      (65535, (255, 255)))
bits = 5 + (19).bit_length() * (15 + 4)
limbs = (bits + 7) // 8
check('fixed_window_capacity',
      (bits, limbs, 19 ** 16 < 2 ** bits,
       27 * 19 ** 19 < 2 ** bits <= 256 ** limbs), (100, 13, True, True))
decoded = [(1 + r // 3, r % 3) for r in range(18)]
expected = [(j, i) for j in range(1, 7) for i in range(3)]
check('stable_reflected_layout',
      (decoded == expected, len(set(decoded)),
       [7 + 3 * (j - 1) + i for j, i in decoded],
       7 + 3 * (2 - 1) + 0, 7 + 6 * (1 - 1) + (2 - 1)),
      (True, 18, list(range(7, 25)), 10, 8))
print(json.dumps({'status': 'passed', 'check_count': len(checks),
                  'checks': checks, 'candidate_search': False,
                  'kernel_execution': False}, sort_keys=True))
```

   同一代码可从本报告精确取出并运行,不另存 tracked 测试程序:

```sh
python3 - <<'PY'
from pathlib import Path
report = Path('docs/reports/prime-coordinate-separation-0909.md').read_text()
code = report.split('```python\n', 1)[1].split('\n```', 1)[0]
exec(compile(code, 'prime-coordinate-separation-0909:fixed-identities', 'exec'))
PY
```

   该检查只核对固定恒等式,不会机器证明三角等号分类、全域严格性、
   射线量词或抽屉极限论证;这些由正文纸面证明承担,仍需独立评审。

7. **canonical ingestion 与增量保真。** 唯一 ingestion 命令为

```sh
make ingest BASE=391f7355698085c6500b46838a093dad05947ffb SOURCE=arithmetic-boundary-quantization
```

   实际生成目录是 `Meta/Digestion/atoms/sha256` 与 `Meta/Digestion/backfill`。
   不手编/重命名 generated 文件;新 YAML 使用 `fingerprints`、`cas_ref`、
   `coverage_gids` 且没有 body `atom_id`,全部保持 `residual-open`、空 coverage。
   增量检查仅检查新增 CAS 字节哈希、entry 引用、实际 source span 的完整实质覆盖、
   原前缀和 changed-path/whitespace。历史 LF 变体若由 producer 产生则保留原样,
   不重跑历史 atomizer 或历史数学。所有实际命令、退出码、生成数量、跨度证据及
   最终逐文件字节数/SHA256 在 runner 的本轮实施 envelope 里逐项记录。

   实际固定检查 exit 0,十项全部通过。上述 `make ingest` exit 0,
   输出 `residual_open_added=23`、`skipped_existing=165`、`coarse_fallbacks=0`、
   `open_genres=0`、`cas_objects_written=23`、`ledger_changed=true`。
   `git diff --check 391f7355698085c6500b46838a093dad05947ffb` exit 0;
   源/报告的 LF 与行末空白自查也通过。增量 entry/CAS 的逐项保真、
   编号项的实质覆盖和全部最终文件身份由本次实施 envelope 及其核验工件给出。
   这些退出码不作 CI 或形式化 admission 判词。

   增量核验器首次 exit 1:它错误地假设 `receipts` 只能含空
   `unresolved_subitems`,而 canonical writer 为 27.10 正常生成了
   `chain_atoms`。I11 没有修改生成物;核验器改为检查此可选字段的引用、
   子项字节串接与父 CAS 的一致性。23 个新增 CAS 的组成是 20 个编号项主体、
   27.10 的两个子项及 26.30 的一个历史终端 LF 变体。
   单独的第 27 节标题属于非命题结构,不充当证明 atom;
   正文全部证明与假设都在 20 个编号项内,实质覆盖检查针对这些项。
   此核验器修正没有更改数学、源前缀、canonical schema 或 ingestion 命令,
   不构成一次新的 flight 或 oracle 重试。

8. **输入文件身份和有限可信边界。** 以下均为 caller 显式供给的临时输入,
   根目录 `/tmp/qgh-boundaries-0908/`;表中的 hash 来自 I11 对这些供给字节的读取。
   primary envelope 只消费 conclusion,其身份由第 2 项完成元数据给出,不追读 log_ref。

   | 文件 | 字节数 | SHA256 |
   | --- | ---: | --- |
   | pro-separated-prime-coordinates-complete-0909.json | 671 | 138714ca08ccf17fc7376481b3e623e367536205d42886b891515d366f67b0f2 |
   | caller-separation-primary-notation-0909.json | 1303 | 0fb214e20665a9e45e6a7670882e6fef645dbf276f05bd6b31dd89953bd48fab |
   | caller-separation-symbolic-checks-0909.json | 977 | c1c5a12b6bc1afe3fe4b44b977dfe49b6ad984a815dc7190259e528ac94ed2de |
   | caller-separation-literature-book-check-0909.json | 2152 | cbf7101d0fb205e8f380139773c2888af0f5e721d856bd38da40a9a702013b29 |
   | literature-boyd-selected-text-0909.txt | 18573 | 686ce554ad119902b18fb6862efb7da75c109c1cba174e8109077785030fc6d5 |
   | goal-separation-append-0909.json | 34733 | 2b0e134304c7622a9ff4b33c3b8936acf443e136b1e7ab4da65c98176454e472 |
   | separation-append-gate-0909.json | 2254 | 8c1aba65658194e93c2ae896ab1ea1cea0ac58c7fe707590978775efbca1386f |

   gate 内提及的其它 receipt/dispatch 路径不在本轮读取范围,I11 没有沿它们继续发现。
   PDF 的字节/hash 另在第 4 项列明。

9. **本轮状态。** flight `qgh0909-i11-separation-append`,attempt 1,retry budget 1。
   源中所有断言均为参考输入层的 paper arguments,消化状态 residual-open。
   本增量 searched boxes、executed box guards、executed kernels、numerically evaluated slots、
   certified computational exclusions 全为 0,没有 pruning、GPU 执行、prime table 生成、
   CPU 候选枚举或 fixed-xi `m=1..1399999` 重放;旧常量表未变。
   独立数学评审、真实精确过滤实现、普通仓库门及 MERGED 由后续流程承担;
   S16 最终交付依赖 S14 MERGED,本 worker 不声明任何新 merge 状态。
   caller 保有全部 Git/PR 操作权,I11 未 stage、commit、push、merge 或操作 issue/PR。
   本轮有效实施信封只表示一个可审查的源增量,不表示长期目标完成。
