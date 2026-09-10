# S18 / I13：共同高度有限混合的源实现与固定证书

本报告对应 [第 29 节源增量](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md#29-共同高度的有限混合矩判别与所选薄层邻域)，范围仅为 C38 / S18。它把已完成 common-height primary 的纸面结果写成可摄入的连续编号源单元，包含固定形状/固定相对薄层的六分支、带符号矩、恒等与最终符号、驻点次数、上确界端点语义，以及所选 `(2,3,5)` 薄层的邻域和实际格点存在性。一般形状及全部薄层的符号仍未解决；没有 RH、形式化或长期目标完成主张。

## 产地与输入身份

caller contract/runner 为 `consensus-rnd:sshx 1.0.0-beta.42`，本实施只咨询同版 [SKILL.md](/Users/auricstudio/.claude/plugins/cache/consensus-rnd/consensus-rnd/1.0.0-beta.42/skills/sshx/SKILL.md) 及其 `CODEX_WORKER_SPEC.md` 的工件条款，没有咨询另一版本的技能内容。载体为 caller 指派的 Codex CLI I13，flight `qgh0910-i13-common-height`、attempt 1、stage `implementation`，实现 verdict 为 `no-verdict-required`。这是一个实施者的纸面核对和固定 CPU 验证，没有子 agent、其它委派、独立评审票或模型族多样性声明。

已完整读取本树 `CLAUDE.md` 和 `agents/CONTEXT.md`，再开始目标工作；完整所供 GoalArtifact 为输入。实施者为 `repo-prior-exposed`。primary 自报 `external-prior-exposed`，继承未知且不可控的账户/项目记忆；这些记忆不是数学前提。caller 的 ACTUAL GPT PRO 标签按所供事实记录，primary conclusion 没有独立确认具体 serving-model/routing；本实施不推断版本、conversation ID 或新的 PRO 调用。

仓库为 <https://github.com/the-omega-institute/trureturing>，唯一工作目标 `/Users/auricstudio/trureturing-qgh-common-height`，分支 `lane/math/quantized-gh-common-height-0910`。入场 HEAD 等于 immutable BASE `66001d3b87d7063c5dd2a4ea97e51f8f1b876afa`，`git status --porcelain=v1 --untracked-files=all` 输出为空。只做 Git 只读查询，没有暂存、提交、push、PR、merge 或其它生命周期操作。

| 已完成先行输入 | 字节 | SHA256 |
| --- | ---: | --- |
| [primary envelope](/tmp/qgh-boundaries-0908/pro-common-height-envelope-0910.json) | 20084 | `7bba088ffbdf3ae327aa0bbf34c17905e90a7510252a0e3f699ba28a27d6eda7` |
| [caller 固定审计](/tmp/qgh-boundaries-0908/caller-common-height-audit-0910.json) | 3412 | `29f4c31130a881c2f9d6268d3ca3dbf7a061c3c589478916815e3ca2670af71e` |
| [caller 一次性程序](/tmp/qgh-boundaries-0908/caller-common-height-audit-0910.py) | 5522 | `13ccb3d828f117fb43f1b833d7fef15f6d22a5d97ca0d96e2c56a47df3d5db27` |

primary task 为 `fd06c983-162f-4f98-adab-2049d31a9f8d`，其 conclusion verdict 为 `proved`，状态为自足 primary paper mathematics。本实施只消费其 conclusion，`log_ref` 仅是不透明引用，没有打开对应工件。没有读取 worker logs、caller sessions、同轮 reviewer 工件或邻居 worktree；也没有读取 S17 live target。完整旧源直接来自此 immutable-base 工作树，未另读可选 caller snapshot。

caller 审计原记录：`checked_at_utc=2026-09-09T16:36:24.203401+00:00`、SymPy `1.14.0`、21 项成功、host session `81959`、host exit `0`。其 `label_correction` 只把两个检查名称明确为截断次数，原算术和谓词不变。此审计与 primary 是完成在前的数学输入，不是本轮 peer review。两份 caller 文件及 primary envelope 均保持原字节。

primary 当时的 pinned-source 请求失败于 `DisabledError`，未亲读源 bytes/hash、25.7 或第 26 节，将该部分历史前提标为 `ASSUMED-UNVERIFIED`，且没有评定原创性。本次旧源核对不会把该历史事实改成“primary 当时已核验”。当前专门结果统一归为 `repo-derived`；经典出处按下表使用，不把历史“未评定”当作现行有效 provenance 状态，也不作优先权或穷尽新颖性主张。

## 旧源重叠及本次增量

正式写作前的本树只读核对包括 25.7；26.2–26.4、26.10–26.17、26.23–26.25、26.28；27.2–27.5、27.11–27.14；28.1–28.2、28.14–28.19。方法为 `rg` 定位编号后 `sed` 逐段读取，不访问其它工作树。

| 旧源准确内容 | 本层处理 |
| --- | --- |
| 25.7 的共同平移级数、首项极限和唯一分解限制 | 29.1、29.6 引用；不声称首次发现共同平移展开。 |
| 26.2–26.4 的角点/严格 cutoff/正支持；27.2–27.5 的正实网格延伸 | 29.2–29.4 使用同一归一化，把高度交集和相对偏移写明；没有改变原域。 |
| 26.10–26.11、26.23 的精确六贪心混合及并列、饱和 | 29.5 直接以固定容量代入，并引用已有匹配证书。 |
| 26.24–26.25 的质量 3 级数和最大值余项传递 | 29.6 给差值系数绝对值 3 与首项归一化余项；旧常数 6 仍是有效宽界。 |
| 26.13–26.17 的固定箱体全薄层有限归约、达到性和零点等价 | 29.11 区分改变共同高度时仅有上确界，避免错用固定箱体的达到性。 |
| 27.13 只同时接近两坐标、再把第三坐标抬高 | 29.18 引用其无理性机制，以二维齐次抽屉控制三个坐标趋近零形状。 |
| 28.14、28.17 的有界相对跨度但无界共同高度 | 29.7–29.11 处理固定实例，29.12–29.18 处理所选薄层邻域，连续统仍未闭合。 |
| 27.14 的“有限补集”措辞 | 仅在 29.21 追加澄清：剩余集无限，所以已排除集非余有限；27.11 另给无限已排除射线尾。原 27.14 不改，S16 review 不重开。 |

所选形态是一个自足源层、一份证书/来源报告和一次 canonical 摄入。其单元共同依赖同一固定形状、有限测度和所选薄层的证明链；拆开会使本层的符号结论失去其域或误差前提。生成路径数量不代表多层功能或多项研究成果。实质措辞缺陷只有已指定的 27.14 集合对象混淆，已以追加澄清处理；本次核对未发现 primary 定理需撤回的数学缺陷。核对止于完整纸面证明、指定 21 项固定算式及新增源/CAS 引用，不增加搜索器、通用测试框架或 broad preflight。

## 实际文献尽调

查询日为 2026-09-10（Asia/Singapore；请求 UTC 2026-09-09）。三个 Google 限定站点查询为：`site:dlmf.nist.gov logarithm power series 4.6`、`site:mathworld.wolfram.com Vandermonde determinant`、`site:encyclopediaofmath.org Dirichlet theorem simultaneous approximation`。均 HTTP 200，但提取的正文只含跳转/反馈提示，没有可用检索结果；不称搜索结果已核验。随后直接取回下面三份经典材料。

| 实际取回内容 | 使用范围 | HTTP / 字节 / SHA256 |
| --- | --- | --- |
| [NIST DLMF 4.6.E1 TeX](https://dlmf.nist.gov/4.6.E1.tex)，`ln(1+z)=z-z²/2+z³/3-…` | 29.6 的对数级数；收敛域由正支持和几何级数积分自足证明。 | 200 / 69 / `f5bdb547043c7dac361980c2de25ca3762b6fae40f38eba76d53dc600b7e531c` |
| [Eric W. Weisstein, Vandermonde Determinant](https://mathworld.wolfram.com/VandermondeDeterminant.html)，式 (1)–(2) | 不同原子的行列式为差乘积；不引用整数整除的附带部分。 | 200 / 56858 / `5356ad125582dad163cca5313f9dd8464451162bb0ca98afe000b4ab36453c96` |
| [Encyclopedia of Mathematics, Dirichlet theorem](https://encyclopediaofmath.org/wiki/Dirichlet_theorem)，Diophantine approximations 小节 | 同时逼近的经典归属及抽屉方法；本源只用并证明 `Q=N²` 的二维齐次特例。页面所列 Cassels (1957) 书目未直接取得或核页。 | 200 / 23172 / `a1e5bb0191fce5f108ce8373ef721eeeae2d69f76934bf040380b890bed858a6` |

DLMF 完整 `https://dlmf.nist.gov/4.6` 的另一次请求返回 HTTP 403，未取得该页域注释。此失败不被写成成功检索。两份 HTML 正文和公式已实际读取；公式不是本问题专门结果的文献先例。EoM 页面 footer 给出 `oldid=44786`，引用只针对上述小节，不把同页其它 Dirichlet 定理作为本层输入。没有检索后续 `(2,3,5)` / `(2,3,7)` 全薄层、实际 5040 或第三素数射线结果。

三个查询响应各为 92459、92421、92574 字节，SHA256 依次为 `3b71c54018821047ac20926430458f1117c014138b6a28cf555698eeda524242`、`f89782660032e8569d28d7a3178599a48f7be6acaa10f627f336191a45705895`、`b777a827cec05afb5e73f83e6bb9b4ca54b9b4f60b736c5d328eac167045e98f`。请求/响应身份另存本 attempt 的 `literature-retrieval.json`，原取回文档为只读尽调材料，不是 worker log。分数背包的 HKUST 和凹性材料引用既有 26.28 记录，本次未重新取回那些 PDF。

## 21 项固定证明证书与实际结果

下面程序保留 caller 原程序在 `result = {` 之前的全部 21 个数学谓词与原名称，只移除未用的日期/路径导入，把历史报告写入尾部替换为 stdout JSON。没有新候选参数、枚举域、搜索循环或复用 API。有限循环仅展开给定指数级数截断及八原子导数的一个符号式。报告内代码是固定证明证书，不是新增测试框架，也不重跑历史搜索。

本次第一次用系统 `python3` 运行时在 import 阶段失败：`ModuleNotFoundError: No module named 'sympy'`，实际 exit 1，数学检查尚未执行。随后只在 attempt 内新建 `verification-env`，安装 SymPy `1.14.0`、其依赖 mpmath `1.3.0`；PyYAML `6.0.2` 仅用于新增 ledger schema/引用核对，不是数学证书依赖。仓库工具或全局 Python 配置均未改动。

本次成功运行命令是 `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i13-common-height/attempt-1/verification-env/bin/python /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i13-common-height/attempt-1/fixed-certificate.py`，exit 0，stderr 为空。证书 2943 字节，SHA256 `2b9ecd0af2e95322b664b96492aec7b4f62b94b2fbfc1f9b827602700501efcd`。成功结果与 caller 审计的 21 个名称和数量一致，独立审评数量仍为零。

可在仓根用安装了 SymPy 1.14.0 的 Python 复现全部检查：

```sh
python3 - <<'PY'
from pathlib import Path
report = Path('docs/reports/common-height-finite-mixtures-0910.md').read_text()
program = report.split('<!-- fixed-certificate:start -->\n```python\n', 1)[1].split('\n```', 1)[0]
exec(compile(program, '<S18 fixed certificate>', 'exec'))
PY
```

<!-- fixed-certificate:start -->
```python
from fractions import Fraction as F
import json
import math

import sympy as sp

checks = []


def check(name, condition):
    assert condition, name
    checks.append(name)


def exponential_partial(x, degree):
    return sum((x**j / math.factorial(j) for j in range(degree + 1)), F(0))


check("exp(7/10) > 2 through degree four", exponential_partial(F(7, 10), 4) > 2)
check("exp(11/10) > 3 through degree five", exponential_partial(F(11, 10), 5) > 3)
log5_lower = 2 * sum((F(2, 3) ** (2*j+1) / (2*j+1) for j in range(4)), F(0))
check("four-term log5 lower bound", log5_lower == F(8, 5) + F(4, 15309))
check("theta < 7/8 by integer powers", F(5, 2)**8 < 3**7)
check("exp(3/10) > 4/3", exponential_partial(F(3, 10), 3) > F(4, 3))
check("exp(9/10) > 12/5", exponential_partial(F(9, 10), 4) > F(12, 5))
check("strict positive m from two strict exponential bounds", 2*F(3, 4)+F(5, 12) == F(23, 12))
rho2_upper = (F(1, 2)**2 + 2*F(11, 10)**2) / 54
check("rho squared upper constant", rho2_upper == F(89, 1800) < F(7, 30)**2)
check("rho squared lower bound implies eta > 9/10", F(1, 27) > ((F(9, 10)-F(8, 15))/2)**2)
check("lambda lower constant", F(8, 15)-F(7, 30) == F(3, 10))
check("second-moment envelope bound", 2*F(3, 4)**2+F(5, 12)**2 == F(187, 144))
check("second-moment mixture bound", F(9, 8)+F(1, 4)+F(7, 8)*F(1, 9) == F(53, 36))
check("strict second-moment sign", F(187, 144) < F(53, 36))
check("geometric envelope tail from n=3", 2*F(3, 4)**3+F(5, 12)**3 == F(1583, 1728) < F(9, 8))
check("scaled-gap neighborhood margin", F(32, 3)*F(3, 64) == F(1, 2))
check("first-moment neighborhood margin", F(16, 3)*F(3, 64) == F(1, 4))

width, middle = sp.symbols("width middle", nonnegative=True)
v = sp.Matrix([0, middle, width])
projection = v - sp.ones(3, 1)*(middle+width)/3
norm2 = sp.expand(projection.dot(projection))
check("shape-projection identity", sp.simplify(norm2-sp.Rational(2, 3)*(width**2-width*middle+middle**2)) == 0)
check("shape-projection remainder on 0<=middle<=width", sp.simplify(2*width**2/3-norm2-2*middle*(width-middle)/3) == 0)

order, magnitude = sp.symbols("order magnitude", positive=True)
cutoff = (order+1)*magnitude/(3*order+(order+1)*magnitude)
check("leading-term strict-tail cutoff boundary", sp.simplify(3*cutoff/((order+1)*(1-cutoff))-magnitude/order) == 0)

z = sp.symbols("z")
atoms = sp.symbols("a0:8", positive=True)
masses = sp.symbols("s0:8")
numerator = sum(masses[j]*atoms[j]*sp.prod(1-z*atoms[l] for l in range(8) if l != j) for j in range(8))
highest = sp.Poly(numerator, z).coeff_monomial(z**7)
check("eight-atom derivative highest coefficient", sp.simplify(highest+sp.prod(atoms)*sum(masses)) == 0)
check("mass-zero derivative degree at most six", sp.simplify(highest.subs(masses[-1], -sum(masses[:-1]))) == 0)

print(json.dumps({"exact_fixed_checks": len(checks), "checks": checks, "sympy": sp.__version__, "CPU_candidate_search": False, "GPU_dispatches": 0}, ensure_ascii=False, indent=2))
```
<!-- fixed-certificate:end -->

实际成功 stdout（`assert` 失败会立即非零退出，名单只在成功检查后追加）：

```json
{
  "exact_fixed_checks": 21,
  "checks": [
    "exp(7/10) > 2 through degree four",
    "exp(11/10) > 3 through degree five",
    "four-term log5 lower bound",
    "theta < 7/8 by integer powers",
    "exp(3/10) > 4/3",
    "exp(9/10) > 12/5",
    "strict positive m from two strict exponential bounds",
    "rho squared upper constant",
    "rho squared lower bound implies eta > 9/10",
    "lambda lower constant",
    "second-moment envelope bound",
    "second-moment mixture bound",
    "strict second-moment sign",
    "geometric envelope tail from n=3",
    "scaled-gap neighborhood margin",
    "first-moment neighborhood margin",
    "shape-projection identity",
    "shape-projection remainder on 0<=middle<=width",
    "leading-term strict-tail cutoff boundary",
    "eight-atom derivative highest coefficient",
    "mass-zero derivative degree at most six"
  ],
  "sympy": "1.14.0",
  "CPU_candidate_search": false,
  "GPU_dispatches": 0
}
```

算式核验支撑 29.8 的严格尾界阈值、29.10 的最高次项消去、29.14–29.17 的固定常数与扰动估计。它不替代线性优化、解析性、Vandermonde、实际格点存在性及全体量词的纸面证明。caller 原 11 条纸面审计意见照原身份保留如下；其中“source incorporation … outstanding”描述当时历史状态，本次源实现和摄入结果见下文，不把旧句当作当前等待条件。

```json
[
  "Strict 5040 inequality gives an open lower height endpoint when Tbase<=tau, including equality; z=0 is a limit, never an admitted height.",
  "An actual nonnegative relative corner and the quadratic norm bound give lambda>=0. All log-series atoms are in (0,1], z<=1/2, and denominators remain strictly positive.",
  "Six greedy permutations include an optimizer for each height even when the gain-density order changes. Saturation r>=Q and ties are covered.",
  "Moment sides each have mass 3, so the absolute coefficient bound is 3 rather than 6. A finite maximum preserves the common remainder estimate.",
  "After coincident atoms are combined, moments 0..m-1 give the Vandermonde identity criterion. Nonidentity needs m>=2 and first nonzero order<=7.",
  "The positive denominator and mass-zero leading cancellation give at most six stationary roots for each nonidentity mixture. Suprema commute with a finite maximum; identity and excluded endpoints require separate treatment.",
  "For the equal shape with steps log2/log3/log5, gain density decreases with the step, so the same greedy branch maximizes at every height. Its coefficient inequalities cover n=1, n=2 and the entire n>=3 tail.",
  "For the chosen slabs [A+log3,A+log5], capacity stays log5 under shape perturbation. Projection geometry and the log derivative bound give the uniform neighborhood margin without assuming stable optimal order.",
  "Homogeneous simultaneous approximation in two ratios needs no rational independence of reciprocal logarithms. Irrational log2/log3 suffices to force an unbounded sequence of approximating denominators.",
  "The prime-step neighborhood theorem certifies only the chosen slab of each box. It is not an all-slab box exclusion, a general shape-density theorem, or an RH criterion.",
  "No numerical witness or effective common-height cutoff is computed. Source incorporation, independent review and MERGED remain outstanding."
]
```

## canonical 摄入和全部新增引用

实际只执行一次以下 canonical 命令，exit **0**：

```sh
make ingest BASE=66001d3b87d7063c5dd2a4ea97e51f8f1b876afa SOURCE=arithmetic-boundary-quantization
```

实际 stdout：

```text
INGEST residual_open_added=26 skipped_existing=204 coarse_fallbacks=0 open_genres=0 cas_objects_written=26 ledger_changed=true
```

新增 **26 个 CAS 对象、26 个 residual-open entry**，跳过既有 **204** 项，coarse fallback **0**，open genre **0**，`ledger_changed=true`。其中 22 个对象对应 29.1–29.22；另有 1 个历史末单元的 terminal-LF 变体、29.9 的 3 个自动 chain children。第 29 节标题未单独生成对象。全部对象与 entry 均保持 producer 原始字节。

源文件现为 **254298 字节 / 4743 个 LF 行**，raw 与 normalized SHA256 均为 `sha256:c5e1fa97fff5921fe5ba10d84b0268c884caab112fb32beed0c92027ee1aa3f5`。追加部分为 **29442 字节 / 602 行**，SHA256 `sha256:367207ccc071d594e6558b9d2b1eb0dc04a23ed88d57c8454f5be1f60ef481b9`。原 **224856 字节 / 4141 行**前缀与 BASE 取出的完整旧源逐字节相等，SHA256 `sha256:69702718f3602c508146f50cf70ebd78ef81adb09c2b826041d357e4a7dc11c8`。除源文件追加外，BASE 中所有已跟踪路径的差异为空，历史 CAS、entry、报告均保留，暂存区为空。

以下偏移是源文件 UTF-8 字节的零起点半开区间；行号从 1 开始，包含单元后的原有分隔 LF。29.1 的起点之前有本次追加的空行与节标题，29.1 起至 EOF 的 22 个编号单元连续无缝。每个区间的原始字节都严格等于其父 CAS；这不是仅比较去空白后的正文。

| 单元 | 源行 | 字节区间 `[start,end)` | 字节 | 父 CAS ID |
| --- | ---: | --- | ---: | --- |
| 29.1 | 4145–4159 | `[224926,226108)` | 1182 | `395b0f417c00db6a9c60a19286072655b27523112826b54bd3c9559b6933915c` |
| 29.2 | 4160–4202 | `[226108,227988)` | 1880 | `aeccbb39717377790e25a5d2c7399213ea7cab84b5460a247989172955fefd1b` |
| 29.3 | 4203–4239 | `[227988,229210)` | 1222 | `6f4247215865376c8e2e83314645699cf88001d0477d4e94f7b3c3d04bab829b` |
| 29.4 | 4240–4261 | `[229210,230325)` | 1115 | `f7460bb8a83e3ef017916cb688f8cb7a1ec87840ed4c836b0fe9c13b120d098f` |
| 29.5 | 4262–4287 | `[230325,231518)` | 1193 | `59fa104ba824c38f0cde7d9d496d747c60c5d432fbb2fdba769cf34f74d9566c` |
| 29.6 | 4288–4320 | `[231518,232708)` | 1190 | `fba7d227803d58f92e4af84984a4ef445511d546dd8d5e220e4ba3386dfb1885` |
| 29.7 | 4321–4353 | `[232708,234307)` | 1599 | `c7a5394e609aed11faa897724d2b68b37668bceb2a4ea3a6a866dd38747ab0a6` |
| 29.8 | 4354–4374 | `[234307,235094)` | 787 | `dae82370b008ae0c569a75b0ccd4ee6fcf807bb4d39b0b67e9fdb851a3b60730` |
| 29.9 | 4375–4392 | `[235094,236202)` | 1108 | `e96a9787fccfb4ad97898ab83a7bd678ce6fce845a8133b24848544b145aaf98` |
| 29.10 | 4393–4416 | `[236202,237339)` | 1137 | `8a74e79cc49c6034dc2d90ff2f7ec8b3052e974d9e6723d643afb7650acc2c2c` |
| 29.11 | 4417–4445 | `[237339,239082)` | 1743 | `1dff10a3ad7715975d8161f5c2a0994002e2e9a5bd0370d878cb1c968d10dc92` |
| 29.12 | 4446–4468 | `[239082,240017)` | 935 | `7319073f8579c0a2693d161727b3a07370107a9f02710846c123191a34fcf7bf` |
| 29.13 | 4469–4493 | `[240017,241072)` | 1055 | `e862fcbae37c329b77dc1c33a9c51a2afde88868135c4a65ec1a82d82796081a` |
| 29.14 | 4494–4527 | `[241072,242322)` | 1250 | `68cc391b89e6f3e11880cae28e2f8120c9d2a792c309e92f615ef75a93fca4fc` |
| 29.15 | 4528–4557 | `[242322,243401)` | 1079 | `461bf7fb87255758df21524954d01244e805203baecde8d8055e5932228389bb` |
| 29.16 | 4558–4586 | `[243401,244727)` | 1326 | `10416386ddff89ee5f75fccb4bfbc5956fb886184e443673a350451920ee5dcd` |
| 29.17 | 4587–4618 | `[244727,245895)` | 1168 | `d2927fcf5b2acc265d55250706a9a4ad45b763e6b2834a55f6de6ee3b9ff9678` |
| 29.18 | 4619–4651 | `[245895,247642)` | 1747 | `ee8c3d8106de3610430b1aa944066eb471a49a6b601936c5e819b7e043b995a7` |
| 29.19 | 4652–4679 | `[247642,249535)` | 1893 | `7be10a3d1aa8a22e92671ed6ee868e6a1fd2c6cdc71ce9196bd17850b1eb1072` |
| 29.20 | 4680–4702 | `[249535,251274)` | 1739 | `7c7bd22bf86a42311e8914ac394feea0f90037dea6c1427299a01dbb7e0e86b8` |
| 29.21 | 4703–4709 | `[251274,251805)` | 531 | `ca7100e17aef2017dde1132e3726b784505939239d20983896be5d82eedbe664` |
| 29.22 | 4710–4743 | `[251805,254298)` | 2493 | `f04f275b9eb1a3708e7da15d8770c4746c06eb8a25b82467a0514f4fd66fd832` |

下表列出全部 26 个新对象和对应 entry 的准确路径（链接目标），对象 ID 为裸 SHA256；每行 `raw_sha256` 和 `normalized_sha256` 指纹均精确为 `sha256:` 加该 ID。已逐项重新计算原始 SHA256，并按 canonical 的 UTF-8/BOM、CRLF/CR→LF、Unicode NFC 规则计算 normalized SHA256；两者在全部新对象上相等。每个 entry 的 `cas_ref` 与 raw 指纹相等，规范化指纹与对象重算值相等，`coverage_gids=[]`、`unresolved_subitems=[]`。

| 来源 | CAS 路径／ID | CAS 字节 | entry 路径 | entry 字节 | entry 文件 SHA256 |
| --- | --- | ---: | --- | ---: | --- |
| 29.16 | [10416386ddff89ee5f75fccb4bfbc5956fb886184e443673a350451920ee5dcd](../../Meta/Digestion/atoms/sha256/10416386ddff89ee5f75fccb4bfbc5956fb886184e443673a350451920ee5dcd) | 1326 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/10416386ddff89ee5f75fccb4bfbc5956fb886184e443673a350451920ee5dcd.yaml) | 328 | `sha256:b891fe7aa391d7bb971ec8a6ea97bb4e8cf8a966f9502c939fbcb519cee9eab7` |
| 29.11 | [1dff10a3ad7715975d8161f5c2a0994002e2e9a5bd0370d878cb1c968d10dc92](../../Meta/Digestion/atoms/sha256/1dff10a3ad7715975d8161f5c2a0994002e2e9a5bd0370d878cb1c968d10dc92) | 1743 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/1dff10a3ad7715975d8161f5c2a0994002e2e9a5bd0370d878cb1c968d10dc92.yaml) | 328 | `sha256:03dd01af3f576a782fa210aebce7b43d76b6560c875d6822159ef7da96f82bf7` |
| 29.9 自动 child | [293c4fb621bda1f2e36e422b52836517d6d7ffe65f031624ecb791ea6c67cc5b](../../Meta/Digestion/atoms/sha256/293c4fb621bda1f2e36e422b52836517d6d7ffe65f031624ecb791ea6c67cc5b) | 390 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/293c4fb621bda1f2e36e422b52836517d6d7ffe65f031624ecb791ea6c67cc5b.yaml) | 328 | `sha256:c3bc3c00878f40b41a21142ae9030ccf3ed6b5101799740af2794914f43df4eb` |
| 29.1 | [395b0f417c00db6a9c60a19286072655b27523112826b54bd3c9559b6933915c](../../Meta/Digestion/atoms/sha256/395b0f417c00db6a9c60a19286072655b27523112826b54bd3c9559b6933915c) | 1182 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/395b0f417c00db6a9c60a19286072655b27523112826b54bd3c9559b6933915c.yaml) | 328 | `sha256:4aa3fe3c782cfdc91e8d47f7fbc9a1654d474c6b923e32af91a37a84999cb7f4` |
| 29.15 | [461bf7fb87255758df21524954d01244e805203baecde8d8055e5932228389bb](../../Meta/Digestion/atoms/sha256/461bf7fb87255758df21524954d01244e805203baecde8d8055e5932228389bb) | 1079 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/461bf7fb87255758df21524954d01244e805203baecde8d8055e5932228389bb.yaml) | 328 | `sha256:554dceb131b42ecd2d7574aed1464435c2191ef8614a8788f6156ef9b522d05b` |
| 29.5 | [59fa104ba824c38f0cde7d9d496d747c60c5d432fbb2fdba769cf34f74d9566c](../../Meta/Digestion/atoms/sha256/59fa104ba824c38f0cde7d9d496d747c60c5d432fbb2fdba769cf34f74d9566c) | 1193 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/59fa104ba824c38f0cde7d9d496d747c60c5d432fbb2fdba769cf34f74d9566c.yaml) | 328 | `sha256:81afcf54523899ca373156cdc7abfc4e341b3e2549962794e2ac02f93afb2a3a` |
| 28.19 末 LF 变体 | [5b26c0f855afa2cfcc15a3f270a88c0f8aebb6a80b8900f3e15f36832488402a](../../Meta/Digestion/atoms/sha256/5b26c0f855afa2cfcc15a3f270a88c0f8aebb6a80b8900f3e15f36832488402a) | 1956 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/5b26c0f855afa2cfcc15a3f270a88c0f8aebb6a80b8900f3e15f36832488402a.yaml) | 328 | `sha256:0470e272e52edd7d20e21cfec28da68281ea9e63fc8ddc51756f1484438a12e4` |
| 29.14 | [68cc391b89e6f3e11880cae28e2f8120c9d2a792c309e92f615ef75a93fca4fc](../../Meta/Digestion/atoms/sha256/68cc391b89e6f3e11880cae28e2f8120c9d2a792c309e92f615ef75a93fca4fc) | 1250 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/68cc391b89e6f3e11880cae28e2f8120c9d2a792c309e92f615ef75a93fca4fc.yaml) | 328 | `sha256:e7c6fec96bc86a9f988883afb68f731050a91a6cc572ec19e0c89bf6177958f7` |
| 29.3 | [6f4247215865376c8e2e83314645699cf88001d0477d4e94f7b3c3d04bab829b](../../Meta/Digestion/atoms/sha256/6f4247215865376c8e2e83314645699cf88001d0477d4e94f7b3c3d04bab829b) | 1222 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/6f4247215865376c8e2e83314645699cf88001d0477d4e94f7b3c3d04bab829b.yaml) | 328 | `sha256:77e3eabe2af040b03d8281273b04e303551d23d49a50daccb03f955667e70a3a` |
| 29.12 | [7319073f8579c0a2693d161727b3a07370107a9f02710846c123191a34fcf7bf](../../Meta/Digestion/atoms/sha256/7319073f8579c0a2693d161727b3a07370107a9f02710846c123191a34fcf7bf) | 935 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/7319073f8579c0a2693d161727b3a07370107a9f02710846c123191a34fcf7bf.yaml) | 328 | `sha256:54afcc0773a362d64bac9ae6afc28240748bfa78e223819d7c8e2eeff68f0d39` |
| 29.19 | [7be10a3d1aa8a22e92671ed6ee868e6a1fd2c6cdc71ce9196bd17850b1eb1072](../../Meta/Digestion/atoms/sha256/7be10a3d1aa8a22e92671ed6ee868e6a1fd2c6cdc71ce9196bd17850b1eb1072) | 1893 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/7be10a3d1aa8a22e92671ed6ee868e6a1fd2c6cdc71ce9196bd17850b1eb1072.yaml) | 328 | `sha256:b43efaaed3d00415f4b3b8d3cdbab10f704a267801d3b8574106898ca2dc0c6f` |
| 29.20 | [7c7bd22bf86a42311e8914ac394feea0f90037dea6c1427299a01dbb7e0e86b8](../../Meta/Digestion/atoms/sha256/7c7bd22bf86a42311e8914ac394feea0f90037dea6c1427299a01dbb7e0e86b8) | 1739 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/7c7bd22bf86a42311e8914ac394feea0f90037dea6c1427299a01dbb7e0e86b8.yaml) | 328 | `sha256:fe93dd1b943659f7e47eaeed23dbdfe018b426a57f3e0a721934cce6cdec5ea1` |
| 29.10 | [8a74e79cc49c6034dc2d90ff2f7ec8b3052e974d9e6723d643afb7650acc2c2c](../../Meta/Digestion/atoms/sha256/8a74e79cc49c6034dc2d90ff2f7ec8b3052e974d9e6723d643afb7650acc2c2c) | 1137 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/8a74e79cc49c6034dc2d90ff2f7ec8b3052e974d9e6723d643afb7650acc2c2c.yaml) | 328 | `sha256:08de20204a21544feb81d1dc019a4b3e6a18feb79214fa2cbaf1c9e010353fab` |
| 29.9 自动 child | [8ffd714a301a89e760f02d46115a7fc234a415f3997a31e6c32caa28f2f01016](../../Meta/Digestion/atoms/sha256/8ffd714a301a89e760f02d46115a7fc234a415f3997a31e6c32caa28f2f01016) | 75 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/8ffd714a301a89e760f02d46115a7fc234a415f3997a31e6c32caa28f2f01016.yaml) | 328 | `sha256:126881513d71bad4412c9d3016b00c6e3e45016f376c7441a1f17143c0a63ed0` |
| 29.2 | [aeccbb39717377790e25a5d2c7399213ea7cab84b5460a247989172955fefd1b](../../Meta/Digestion/atoms/sha256/aeccbb39717377790e25a5d2c7399213ea7cab84b5460a247989172955fefd1b) | 1880 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/aeccbb39717377790e25a5d2c7399213ea7cab84b5460a247989172955fefd1b.yaml) | 328 | `sha256:898d5cee150699e1d6d7ffa2323994ebf973f75b9ce781e59d56188561406f5f` |
| 29.7 | [c7a5394e609aed11faa897724d2b68b37668bceb2a4ea3a6a866dd38747ab0a6](../../Meta/Digestion/atoms/sha256/c7a5394e609aed11faa897724d2b68b37668bceb2a4ea3a6a866dd38747ab0a6) | 1599 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/c7a5394e609aed11faa897724d2b68b37668bceb2a4ea3a6a866dd38747ab0a6.yaml) | 328 | `sha256:0a3dbc4bb82e0019100c105f42821d75d73d3379bd8d5ae4229c02637fbdbc21` |
| 29.21 | [ca7100e17aef2017dde1132e3726b784505939239d20983896be5d82eedbe664](../../Meta/Digestion/atoms/sha256/ca7100e17aef2017dde1132e3726b784505939239d20983896be5d82eedbe664) | 531 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/ca7100e17aef2017dde1132e3726b784505939239d20983896be5d82eedbe664.yaml) | 328 | `sha256:f909b7de93abf41b01bf2726607193b00b22c3258fb56f12bf54697f3adcd757` |
| 29.17 | [d2927fcf5b2acc265d55250706a9a4ad45b763e6b2834a55f6de6ee3b9ff9678](../../Meta/Digestion/atoms/sha256/d2927fcf5b2acc265d55250706a9a4ad45b763e6b2834a55f6de6ee3b9ff9678) | 1168 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/d2927fcf5b2acc265d55250706a9a4ad45b763e6b2834a55f6de6ee3b9ff9678.yaml) | 328 | `sha256:5ae2bf975447799d6f34938e20f50ea98b4e0de27053111fb50a1673e578ff17` |
| 29.8 | [dae82370b008ae0c569a75b0ccd4ee6fcf807bb4d39b0b67e9fdb851a3b60730](../../Meta/Digestion/atoms/sha256/dae82370b008ae0c569a75b0ccd4ee6fcf807bb4d39b0b67e9fdb851a3b60730) | 787 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/dae82370b008ae0c569a75b0ccd4ee6fcf807bb4d39b0b67e9fdb851a3b60730.yaml) | 328 | `sha256:4c007a3432431c5ffd7d2676702afc5695c9705666f2f8b58c5e03922435edac` |
| 29.13 | [e862fcbae37c329b77dc1c33a9c51a2afde88868135c4a65ec1a82d82796081a](../../Meta/Digestion/atoms/sha256/e862fcbae37c329b77dc1c33a9c51a2afde88868135c4a65ec1a82d82796081a) | 1055 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/e862fcbae37c329b77dc1c33a9c51a2afde88868135c4a65ec1a82d82796081a.yaml) | 328 | `sha256:d9fe13705b56a77f601c72c059821ccbe2a9131811a3961882de0e359cb87771` |
| 29.9 | [e96a9787fccfb4ad97898ab83a7bd678ce6fce845a8133b24848544b145aaf98](../../Meta/Digestion/atoms/sha256/e96a9787fccfb4ad97898ab83a7bd678ce6fce845a8133b24848544b145aaf98) | 1108 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/e96a9787fccfb4ad97898ab83a7bd678ce6fce845a8133b24848544b145aaf98.yaml) | 556 | `sha256:e313d4b0b29427ce75777e17314981e6da35abba2b01901841fe034bdfbb8904` |
| 29.18 | [ee8c3d8106de3610430b1aa944066eb471a49a6b601936c5e819b7e043b995a7](../../Meta/Digestion/atoms/sha256/ee8c3d8106de3610430b1aa944066eb471a49a6b601936c5e819b7e043b995a7) | 1747 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/ee8c3d8106de3610430b1aa944066eb471a49a6b601936c5e819b7e043b995a7.yaml) | 328 | `sha256:5150ba3da067b473386051f95ad3ec809738d0e02b06e1df512d81d78752cfeb` |
| 29.22 | [f04f275b9eb1a3708e7da15d8770c4746c06eb8a25b82467a0514f4fd66fd832](../../Meta/Digestion/atoms/sha256/f04f275b9eb1a3708e7da15d8770c4746c06eb8a25b82467a0514f4fd66fd832) | 2493 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/f04f275b9eb1a3708e7da15d8770c4746c06eb8a25b82467a0514f4fd66fd832.yaml) | 328 | `sha256:b3ba810c1ce32a4ec5a1bbec9b1acbfd35fa6938ca4035e8308318596bbbcb5e` |
| 29.4 | [f7460bb8a83e3ef017916cb688f8cb7a1ec87840ed4c836b0fe9c13b120d098f](../../Meta/Digestion/atoms/sha256/f7460bb8a83e3ef017916cb688f8cb7a1ec87840ed4c836b0fe9c13b120d098f) | 1115 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/f7460bb8a83e3ef017916cb688f8cb7a1ec87840ed4c836b0fe9c13b120d098f.yaml) | 328 | `sha256:120d0f5078c7d75cad9834fd027e4d27b6384e853a178421d6d3553c30858c03` |
| 29.6 | [fba7d227803d58f92e4af84984a4ef445511d546dd8d5e220e4ba3386dfb1885](../../Meta/Digestion/atoms/sha256/fba7d227803d58f92e4af84984a4ef445511d546dd8d5e220e4ba3386dfb1885) | 1190 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/fba7d227803d58f92e4af84984a4ef445511d546dd8d5e220e4ba3386dfb1885.yaml) | 328 | `sha256:d53a088b1a00104c38f53f26d08be13eca131ddf3e8c1c9c9dcac0fa563765df` |
| 29.9 自动 child | [fcf94fbf2bb803f312501aa746a16cbb63f7890f958ebfe14eda6b5d9c429f97](../../Meta/Digestion/atoms/sha256/fcf94fbf2bb803f312501aa746a16cbb63f7890f958ebfe14eda6b5d9c429f97) | 643 | [entry](../../Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/fcf94fbf2bb803f312501aa746a16cbb63f7890f958ebfe14eda6b5d9c429f97.yaml) | 328 | `sha256:d575b8152109d6c804f9c30fd0af930ef9f0212863c7d08d6ffcb0ac79e6dd88` |

历史 28.19 原对象 `6d5c629de009b70b0239c0a0b56d5cd5ffb90cf6f868ca84e94b500a1aa89939` 为 1955 字节，原对象及 entry 保持原样；新对象 `5b26c0f855afa2cfcc15a3f270a88c0f8aebb6a80b8900f3e15f36832488402a` 为 1956 字节，恰为旧对象追加一个 LF。新增章节改变了末单元的截取边界，canonical 因而产生这个变体；没有覆写旧对象，也没有手修新对象。

29.9 父对象 `e96a9787fccfb4ad97898ab83a7bd678ce6fce845a8133b24848544b145aaf98` 的 `receipts.chain_atoms` 按下列顺序保存**裸哈希**，不是 `sha256:` 指纹。三个 child 的 390、75、643 字节按序拼接，严格等于父对象的 1108 字节；子 entry 不含递归 children。

```json
[
  "293c4fb621bda1f2e36e422b52836517d6d7ffe65f031624ecb791ea6c67cc5b",
  "8ffd714a301a89e760f02d46115a7fc234a415f3997a31e6c32caa28f2f01016",
  "fcf94fbf2bb803f312501aa746a16cbb63f7890f958ebfe14eda6b5d9c429f97"
]
```

本次一次性引用校验程序为 attempt 内 `verify-increment.py`，SHA256 `sha256:85e2b61c1d541a41ea8010662067ae4e2c6cc29c36686548fee6dd67ca45164c`；执行命令如下，修正下述校验器前提后实际 exit **0**。完整校验读数 `source-cas-verification.json` 的 SHA256 为 `sha256:8ffaf8f08a9b1f49ad20e6699d002b2238a207ee4c699767bb0f2e006f5cba6a`。程序只核对已给定源增量和 canonical 产物，不是候选生成或仓库新增工具。

```sh
/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i13-common-height/attempt-1/verification-env/bin/python /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i13-common-height/attempt-1/verify-increment.py
```

校验器第一次运行 exit **1**：它额外假定 entry YAML 都以两个 LF 结尾，该假定没有 producer 合约依据。实际测得全部 **26 个 entry 都以一个 LF 结尾**。只删除了外部一次性校验器的这一错误断言，保留所有 schema、指纹、源区间和链引用断言，再运行通过；生成文件修复数为 **0**。失败后保存的 `checker-EOF-observation.json` 记录 26 个 entry 的原始指纹，最终核对仍逐项相等。CAS 的 EOF 也按产出逐项保留：29.22 和前两个 chain child 各有一个末 LF，其余新 CAS 各有两个；没有统一格式化。

临时报告组装和最终封装核验还各有一次 exit **1**：前者把证据中的空列表 `canonical_files_modified_to_repair=[]` 与数值 `0` 作等值断言；后者对已解析为对象的固定结果 `stdout` 再调用 `json.loads`，触发 `TypeError`。两次均在该次文件写入前退出。按实际字段类型纠正后完成组装和核验；两次失败均未修改源、报告或 canonical 文件，也未重跑数学证书。

本层相对 BASE 的最终路径数为 **54**：源文件 1、报告 1、CAS 26、entry 26；没有其它已跟踪改动或未跟踪文件。全部路径及最终字节/hash 清单随同 runner envelope 的 conclusion 交回。

## 未决、偏差与交回边界

数学范围未扩大。原 1–28 节、全部历史 CAS/entry/report、stable slot IDs、工具、Lean 和 frozen 面保留。CPU 候选生成、指数/高度/形状/素数/薄层候选生成、GPU dispatch、daemon 和旧 search replay 均为 0。执行偏差已逐项记账：固定证书的一次缺依赖失败；三个不可用搜索响应及 DLMF 全页 403；一次性引用校验器错误的双 LF 假定导致首次 exit 1、纠正后 exit 0；报告组装和最终封装核验各一次数据类型误用在写入前 exit 1、纠正后通过；canonical producer 实际产生的历史末单元变体和三个 children。所有 canonical 字节保持原样，生成文件手修数为 0。

恒等测度与高阶零矩仍需处理，固定形状结论没有提供形状连续统的有限分类；统一非零首矩缺失时，逐点 cutoff 不能升级为区域统一 cutoff。任意指定形状的素数格点转移仍需独立逼近证明；高阶首矩要求低阶扰动按 29.19 的更强指数速率消失。所选薄层结果没有变成全薄层结果，无界高度上未缩放差趋零，`sup G=0` 不能单独认证有限零点或否定全程严格负号。没有数值 witness、有效 exponent cutoff、rational root-isolation 实现或 RH 结论。

源实现及独立源评审可在本隔离树推进。caller 在本 implementation terminal 后封存、安排 review、普通仓库门及交付；只有最终交付依赖 S17 MERGED。本报告没有要求源实现或独立评审等到 S17 MERGED，也没有读取 S17 实时 review。当前交回可审查内容候选，不声称 S18 已 review/MERGED。完整 changed-file 路径/字节/SHA256 清单与本报告自身最终 hash 位于同次 `result.json` 的 conclusion；报告不嵌入自己的 hash，以免形成自指。
