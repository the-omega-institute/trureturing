# (2,3,5) 整箱全薄层 S19：来源、固定证明证书与摄入核对

产地：caller 提供的 `consensus-rnd:sshx 1.0.0-beta.42` runner 合约，I14，
flight `qgh0910-i14-balanced-all-slabs`，attempt 1。Codex CLI 单一实施者，
没有查阅其它 skill 版本、native subagent、委派或本轮独立 review 票。
原 primary 与 caller 审计是已完成的先行数学输入，不是同轮同行评审。
本实施具有仓库先验；不声称 sterile priors、模型族多样性或独立验证了 serving-model/routing。
实际 GPT PRO 的身份来自 caller 指定的主输入记录。

本层只追加 [理论卷第 30 节](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md#30-三素数-235-的整箱全薄层邻域与无界共同高度)，
本报告与 canonical ingest 输出。工作树为
`/Users/auricstudio/trureturing-qgh-balanced-all-slabs`，分支
`lane/math/quantized-gh-balanced-all-slabs-0910`，immutable base
`a8e208440d8a3f465a7b20c82ededbb27ee95026`。初始 `git status --short --untracked-files=all`
为空，`git rev-parse HEAD` 和当前分支均与上述约定一致；相关命令 exit 0。
已完整分段读取 `CLAUDE.md`（764 行、272879 字节）与 `agents/CONTEXT.md`。
首次全文工具输出被截断，随后补齐所有遗漏，不将截断读取宣称为完整阅读。

结果是 PAPER_ARGUMENT / repo-derived 的参考输入：零形状对每个宽域两角点实薄层有
`exp(T) G < -1/60`；`max xi <= 1/480` 的闭邻域对每个薄层有
`exp(T) G < -1/120`，均覆盖任意有限 `T >= log 2`。
齐次同时逼近使无穷多个实际非负整数指数箱体进入此邻域；原严格 cutoff 域非空恰为
`A > log 2 + log 5040`，等号为空。没有全形状、一般素数、RH、Lean 或优先权主张。
GH 保持用户的字面标签；两个上界之差为负不是 RH 判据或证明。

## 先行输入、边界和核对口径

以下文件只读取指定的数学内容；primary 只消费 `conclusion`，`log_ref` 不透明。
没有读取任何 worker 日志、log_ref 内容、caller 转录、其它 reviewer 工件或邻近/活跃 worktree。
`/tmp/qgh-boundaries-0908/` 下四个输入的实测身份为：

| 文件 | 字节 | LF 数 | SHA256 |
| --- | ---: | ---: | --- |
| pro-balanced-all-slabs-envelope-0910.json | 23507 | 365 | `sha256:5ad15f1f87730e33edd6ef2e9045aa4255a4a85efb1e456312b438da91c5288c` |
| caller-balanced-all-slabs-audit-0910.json | 8204 | 282 | `sha256:b43f792c6cb531a0df491580ba7e34c2024d15aca0d6a9cb63c75167214ca0f8` |
| caller-balanced-all-slabs-audit-0910.py | 7159 | 168 | `sha256:510fa59f83d7aa98ebc2f07640af09f4745725e122152b6a391338d4e817256f` |
| balanced-all-slabs-source-preparation-0910.json | 3987 | 55 | `sha256:f80a7fdc5c1f874edb3f82a8c43b821dd8bc6e5aa09ed70fb1b209d9bef7b3c5` |

准备文件的旧 `predecessor` 在飞行措辞被本次实际封存 S18 base 替代；它没有授权读其活跃
review target 或 result。本次只从指定工作树的 immutable-base 历史源读取 S18。
primary task 是 `8cfd404d-43c8-42f9-a5be-22e0811bc05a`，其原 `verdict` 为 `proved`，
表示该有界 primary 的纸面结论，不是 S19 的 review 或交付 verdict。
primary 自报 pinned-source 请求失败 `DisabledError`，未读取其字节或核验 caller 给的 hash，
且未成功取得外部文献；这些历史限制保持原状。

primary 自报 **34** 项：3 个对数包围、13 个指数正多项式、10 个平方 R 界、8 个大序/裕量组合。
caller 原审计记录 **64** 项全成功、原 host exit **0**，另有完整纸面审计；64 包含那 34 项，
不能相加成 98，也不能把 64 项归给 primary。这里没有重跑未改动的原审计程序。
本报告把所需原输入常数嵌入自足程序，保留 64 项对应核验，并补 5 项
“向外 q 包围确实绑定精确节点公式”的固定连接核验，总计 **69** 项。
这项补充消除了复现者原先需要自行核对的字面常数连接；没有发现已封存数学结论的反例。
新增核验不是新研究检查数，更不是独立审稿。

原 primary 的压缩 token `2^83^7` 原样保留在其输入；新源和证书明确使用
`5^8 < 2^8 * 3^7`。纸面相邻节点 `j=1..7` 对应零起点 raw slots `0..6`，
反射保留 `slot 10`；报告和程序均不更改 25 槽的稳定编号。

## 每个新增单元的来源映射

表中 JSON 路径均相对于上述 primary 的 `conclusion`；caller 的 `paper_audit` 为补充核对。
这些是数学输入位置，不是要追读的日志或 reviewer 地址。

| 新源单元 | 先行数学输入 | 直接复用及本层意义 |
| --- | --- | --- |
| 30.1 | `summary`, `theorem`, `scope_and_remaining_obligations` | 26/27/29 的准确前置与本层全薄层量词 |
| 30.2 | `theorem.definitions`, `transfer_proof.budget_mapping` | 26.3、27.3、29.2 原定义；分开宽域、整数实现、严格 cutoff |
| 30.3 | `proof.positive_support` | 26.4、27.5、29.4 的同一角点机制；补明无需 cutoff |
| 30.4 | `proof.finite_reduction_without_cutoff` | 26.5-26.15；完整宽域饱和、严格凸性、上尾与等号 |
| 30.5 | `proof.relative_corner_order`, `proof.reflected_candidate_check` | 26.21 稳定 IDs；全部 18 guards 恰保留 slot 10 |
| 30.6 | `proof.equal_shape_order` | 29.13 已有平均导数论证，适用于每个容量及正高度 |
| 30.7 | `proof.node_geometry` | 八个规定节点的距离、贪心权重和全部矩恒等式 |
| 30.8 | `proof.all_moment_comparison_lemma` | 经典递增凸序积分比较的自足质量 3 版本 |
| 30.9 | `proof.rational_majorization_certificate` | 全八行有理证书、最大两单位质量、首矩与严格边界 |
| 30.10 | `proof.atom_bound_certificate` | 对数正级数、五组 q/R 包围及十三个指数正多项式 |
| 30.11 | `proof.uniform_height_and_all_slab_conclusion` | 26.24、29.6 的级数；无限矩推出全薄层缩放界 |
| 30.12 | `transfer_proof.budget_mapping` | 减 X 保留闭角点包含，不保证原 cutoff |
| 30.13 | `transfer_proof.projection_bound` | 27.3、29.16 已有 Pi 与范数式，用于全部对应薄层 |
| 30.14 | `transfer_proof.common_mixtures` | 26.23、29.5 六组同权混合；对偶增量在正区间 |
| 30.15 | `transfer_proof.envelope_sharpening` | 包络增量同属正区间，差的 Lipschitz 常数改进为 2 |
| 30.16 | `theorem.whole_box_neighborhood`, `transfer_proof.neighborhood_conclusion` | 闭半径与 T 下边界均保留严格号 |
| 30.17 | `actual_prime_lattice.construction`, `.limits` | 29.18 齐次构造直接复用；本层用于新全薄层半径 |
| 30.18 | `actual_prime_lattice.strict_cutoff_nonemptiness`, `.eventual_nonemptiness` | 26.16 的直接三步长专门化与等号空域 |
| 30.19 | `scope_and_remaining_obligations`, `actual_prime_lattice.limits` | 29.6 的 G→0；形状、格点和 RH 限制 |
| 30.20 | `source_access_and_evidence`, `.visible_inputs`, `.reasoning_discipline`，caller 审计 | 保留历史访问失败和检查数；当前专门结论 repo-derived |
| 30.21 | caller C41/S19、准备文件与本 attempt 的 runner contract | 当前 sealed base、前缀和生成物边界；交付等待 S18 MERGED |

亲读的重叠范围是本树第 26 节（含有限 critical-node theorem、26.23 六排列、
26.24-26.25 矩展开）、27.3-27.5（正交投影及支持）、第 29 节全部
（含有限 common-height mixtures、selected-slab 及齐次逼近）和第 10 节度量定义。
本层没有再把这些前置命题标成新发现。

## 定向文献尽调与实际取回

经典对数级数、分数背包、欧氏凸性、递增凸序/弱大序及抽屉齐次逼近均为
literature-attested 方法。本设置的特定八节点、全薄层裕量和扰动组合经源中证明核对后
记为 repo-derived；未作全球先例穷尽调查或 novelty/priority 声明。
先前源的分数背包/凸性引文保留 26.28 的历史归属，不冒充本次重新取回。

本次通过只读 HTTPS 直接请求以下指定文献页面/正文，发生于
2026-09-09T19:35:28Z 至 19:36:25Z（当地 2026-09-10），没有宽泛搜题或候选搜索。

| 实际 URL | HTTP / 字节 / SHA256 | 实际使用位置与限度 |
| --- | --- | --- |
| https://dlmf.nist.gov/4.6.E1.tex | 200 / 69 / `sha256:f5bdb547043c7dac361980c2de25ca3762b6fae40f38eba76d53dc600b7e531c` | 原公式 `ln(1+z)=z-z²/2+…`；本节自行用几何积分证明收敛域和严格尾界 |
| https://encyclopediaofmath.org/wiki/Majorization | 404 | 没有取得正文，不作为已读引文 |
| https://encyclopediaofmath.org/wiki/Dirichlet_theorem | 200 / 23173 / `sha256:14080d57e0a969e2ae73d9d602b14c7779504700aafaefece2e0fbce901d78e4` | Diophantine approximations 小节的同时逼近/box principle；本节只依赖自证的 Q=N² 特例 |
| https://arxiv.org/abs/1801.00977 | 200 / 41412 / `sha256:c102742bf8919c496ebad19902b2f744b25ae6f0434364a3e57de8bbd3f5af78` | Gushchin、Borzykh，标题、作者、期刊和 DOI 元数据 |
| https://arxiv.org/pdf/1801.00977 | 200 / 514768 / `sha256:f7378b6383d5b686146326a0ad6d7c29c76ad29816a5f47949ec67de61631c39` | §2.3 Theorem 5(ii) 及证明，PDF p.10 / journal p.294；并核对 Theorem 3 的积分分位函数背景 |

Gushchin–Borzykh 的 Theorem 5(ii) 把递增凸序与积分分位函数顺序等价起来，证明中明确用
`E[(X-x)+] <= E[(Y-x)+]` 的全阈值判据。源 30.8 的最大质量积分是同一经典框架，
但把两个检查点如何控制全部 s、正部积分及每个正整数矩完整写出；
质量 3 除以 3 后与概率约定一致，没有把“等总质量”误作“等均值”。
这里没有宣称论文正文出现 (2,3,5)、本比较差 G 或本层常数。

PDF 转文工具 `pdftotext` 不存在（exit 127），随后用已安装 `pypdf` 成功提取文本
（exit 0）；该工具提示缺少可选 fontTools 的 CFF 编码支持。
所用 Theorem 5(ii) 与正部积分文本可读，本次不声称精校全篇排版或全部公式编码。
原 primary 的 DisabledError、原未成功取文和来源身份未独立鉴定均保持原始历史。

## 自足固定证明证书

下列代码只使用 Python 标准库 `fractions.Fraction`、整数和有限已给常数。
它不读取 primary、caller audit、临时路径或其它仓库文件，不接受候选参数，
也不生成指数、高度、形状、素数、矩阶或薄层候选。有限循环只消费上述固定证书。
积分引理和纸面全称证明承担所有 n≥1 的结论；这段程序不会用有限矩抽样替代它。
原 caller 程序未修改；适配只内嵌所需数据、移除外部输入/写回、增加固定连接核验和可复现输出。

从仓根执行以下命令，直接从本报告提取并执行同一程序；无需绝对 `/tmp` 路径或新测试框架：

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess
import sys
report = Path('docs/reports/balanced-prime-235-all-slabs-0910.md').read_text()
marker = '```python\n# S19_FIXED_CERTIFICATE_V1\n'
code = '# S19_FIXED_CERTIFICATE_V1\n' + report.split(marker, 1)[1].split('\n```', 1)[0] + '\n'
result = subprocess.run([sys.executable, '-'], input=code, text=True)
raise SystemExit(result.returncode)
PY
```

```python
# S19_FIXED_CERTIFICATE_V1
"""Self-contained fixed (2,3,5) proof certificate; no candidate inputs."""
from fractions import Fraction as F
from math import factorial
import json
import platform
import sys

if len(sys.argv) != 1:
    raise SystemExit("This fixed certificate accepts no candidate parameters")
checks = []


def check(name, result):
    checks.append({"name": name, "passed": bool(result)})
    if not result:
        raise AssertionError(name)


proof = {'atom_bound_certificate': {'exponential_certificates': {'rule': 'Write P_N(x)=sum from k=0 to N '
                                                                 'of x^k/k!. For x>0, '
                                                                 'exp(x)>P_N(x). Each following '
                                                                 'triple (x,N,target) satisfies '
                                                                 'the exact rational inequality '
                                                                 'P_N(x)>target.',
                                                         'triples': [['19/100', 2, '6/5'],
                                                                     ['2/3', 2, '15/8'],
                                                                     ['3/10', 3, '4/3'],
                                                                     ['19/20', 3, '5/2'],
                                                                     ['29/100', 3, '4/3'],
                                                                     ['7/6', 5, '16/5'],
                                                                     ['12/25', 3, '8/5'],
                                                                     ['13/10', 4, '7/2'],
                                                                     ['3/5', 3, '9/5'],
                                                                     ['3/2', 5, '40/9'],
                                                                     ['23/25', 4, '5/2'],
                                                                     ['31/20', 5, '14/3'],
                                                                     ['3/4', 3, '2']]}},
 'rational_majorization_certificate': {'rows': [{'node': 'j=1',
                                                 'l': '4/5',
                                                 'h': '4/5',
                                                 'w': '5/2',
                                                 'k': '2',
                                                 'w_minus_2l_minus_h': '1/10'},
                                                {'node': 'j=2',
                                                 'l': '5/6',
                                                 'h': '8/15',
                                                 'w': '67/30',
                                                 'k': '9/5',
                                                 'w_minus_2l_minus_h': '1/30'},
                                                {'node': 'j=3',
                                                 'l': '3/4',
                                                 'h': '2/5',
                                                 'w': '23/12',
                                                 'k': '25/16',
                                                 'w_minus_2l_minus_h': '1/60'},
                                                {'node': 'j=4',
                                                 'l': '3/4',
                                                 'h': '5/16',
                                                 'w': '11/6',
                                                 'k': '3/2',
                                                 'w_minus_2l_minus_h': '1/48'},
                                                {'node': 'j=5',
                                                 'l': '5/8',
                                                 'h': '2/7',
                                                 'w': '47/30',
                                                 'k': '23/18',
                                                 'w_minus_2l_minus_h': '13/420'},
                                                {'node': 'j=6',
                                                 'l': '5/9',
                                                 'h': '9/40',
                                                 'w': '289/210',
                                                 'k': '47/42',
                                                 'w_minus_2l_minus_h': '101/2520'},
                                                {'node': 'j=7',
                                                 'l': '2/5',
                                                 'h': '3/14',
                                                 'w': '31/30',
                                                 'k': '5/6',
                                                 'w_minus_2l_minus_h': '2/105'},
                                                {'node': 'slot 10',
                                                 'l': '3/4',
                                                 'h': '1/2',
                                                 'w': '37/18',
                                                 'k': '5/3',
                                                 'w_minus_2l_minus_h': '1/18'}]}}

log_bounds = [(F(693, 1000), F(694, 1000)),
              (F(1098, 1000), F(1099, 1000)),
              (F(1609, 1000), F(1610, 1000))]
for p, (lower, upper) in zip((2, 3, 5), log_bounds):
    y = F(p - 1, p + 1)
    partial = 2 * sum((y ** (2*k+1) / (2*k+1) for k in range(20)), F(0))
    remainder = 2 * y**41 / (41 * (1-y*y))
    check(f'log {p}: strict rational enclosure', lower < partial < partial + remainder < upper)

for x, degree, target in proof['atom_bound_certificate']['exponential_certificates']['triples']:
    x = F(x)
    polynomial = sum((x**k / factorial(k) for k in range(degree+1)), F(0))
    check(f'exp lower polynomial x={x}, degree={degree}', polynomial > F(target))

r_bounds = [(480, 500), (660, 664), (900, 910), (830, 840),
            (902, 904), (635, 638)]
q_scaled_bounds = [([469, 1098, 1098], [473, 1099, 1099]),
                   ([287, 1502, 1609], [290, 1505, 1610]),
                   ([0, 990, 1791], [0, 995, 1793]),
                   ([221, 586, 2119], [224, 589, 2122]),
                   ([625, 0, 1425], [630, 0, 1429])]
for node, (ql, qu), (rl, ru) in zip(range(3, 8), q_scaled_bounds, r_bounds[1:]):
    check(f'j={node}: lower squared R bound', 6*rl*rl < sum(q*q for q in ql))
    check(f'j={node}: upper squared R bound', sum(q*q for q in qu) < 6*ru*ru)

for row in proof['rational_majorization_certificate']['rows']:
    low_atom, high_atom, w, k = map(F, (row['l'], row['h'], row['w'], row['k']))
    margin = w - 2*low_atom - high_atom
    check(row['node'] + ': all-moment majorization and margin',
          0 <= high_atom <= low_atom <= 1 and k >= 2*low_atom
          and margin == F(row['w_minus_2l_minus_h']) and margin >= F(1, 60))
base_certificate_checks = len(checks)
check('primary 34-certificate accounting', base_certificate_checks == 34)

# Independently select distance branches using certified logarithm intervals.
zero, a, b, c = (0,0,0), (1,0,0), (0,1,0), (0,0,1)


def add(v, w):
    return tuple(x+y for x, y in zip(v, w))


def mul(k, v):
    return tuple(k*x for x in v)


def sub(v, w):
    return add(v, mul(-1, w))


def interval(v):
    lower = sum((x*(lo if x >= 0 else hi) for x, (lo, hi) in zip(v, log_bounds)), F(0))
    upper = sum((x*(hi if x >= 0 else lo) for x, (lo, hi) in zip(v, log_bounds)), F(0))
    return lower, upper


def sign(v):
    if v == zero:
        return 0
    lo, hi = interval(v)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    raise AssertionError(('unresolved fixed linear-log comparison', v, lo, hi))


corners = [zero, a, b, c, add(a,b), add(a,c), add(b,c), add(add(a,b),c)]
pairs = list(zip(corners, corners[1:])) + [(a, mul(2,a))]
expected_q = [(zero,zero,zero), (a,a,a), (sub(mul(3,a),c),b,b),
              (sub(mul(2,a),b),sub(mul(2,b),a),c),
              (zero,sub(sub(mul(3,b),a),c),add(a,b)),
              (sub(c,mul(2,a)),sub(mul(2,b),c),sub(mul(2,c),b)),
              (sub(add(b,c),mul(3,a)),zero,sub(sub(mul(2,c),a),b)), (a,a,a)]
for index, ((u,v), expected) in enumerate(zip(pairs, expected_q), 1):
    actual = []
    for step in (a,b,c):
        endpoint = mul(3,step)
        if sign(sub(endpoint,u)) < 0:
            q = sub(u,endpoint)
        elif sign(sub(endpoint,v)) <= 0:
            q = zero
        else:
            other = sub(endpoint,v)
            q = u if sign(sub(u,other)) <= 0 else other
        actual.append(q)
    check(f'node {index}: exact nearest-endpoint branches', tuple(actual) == expected)

products = [1,2,3,5,6,10,15,30]
retained = []
for j in range(1,7):
    p0, p1, p2 = products[j-1:j+2]
    for i, p in enumerate((2,3,5)):
        if p0 > 1 and p0*p0 < p**3 and p1*p0 < p**3 < p2*p0:
            retained.append(7 + 3*(j-1) + i)
check('all 18 fixed reflected eligibility tests retain only slot 10', retained == [10])

check('log-ratio weight bounds from integer powers',
      2**5 > 3**3 and 2**3 < 3**2 and 5**8 < 2**8 * 3**7
      and 3**3 > 5**2 and 2**7 > 5**3)
check('j=1 strict atom cube bound', 125 < 128)
check('j=2 and slot 10 squared R bounds',
      2*F(480,1000)**2 < log_bounds[0][0]**2
      and log_bounds[0][1]**2 < 2*F(500,1000)**2)

offset_lower = [('19/100','2/3'), ('3/10','19/20'), ('29/100','7/6'),
                ('12/25','13/10'), ('3/5','3/2'), ('23/25','31/20'), ('29/100','3/4')]
for node, ((u,v), (rl,ru), (lambda_floor,eta_floor)) in enumerate(
        zip(pairs[1:], r_bounds + [r_bounds[0]], offset_lower), 2):
    v_lower = interval(v)[0]
    check(f'node {node}: lambda and eta strict floors',
          (v_lower-F(ru,1000))/3 > F(lambda_floor)
          and (v_lower+2*F(rl,1000))/3 > F(eta_floor))

# The lower w/k values use the exact log-ratio certificates above.
weight_lowers = [(F(5,2),F(2)),
                 (F(11,6)+F(2,3)*F(3,5), F(3,2)+F(3,10)),
                 (F(5,2)-F(2,3)*F(7,8), F(2)-F(7,16)),
                 (F(11,6),F(3,2)),
                 (F(31,30)+F(4,5)*F(2,3), F(5,6)+F(2,3)*F(2,3)),
                 (F(31,30)+F(4,5)*F(3,7), F(5,6)+F(2,3)*F(3,7)),
                 (F(31,30),F(5,6)),
                 (F(5,2)-F(2,3)*F(2,3),F(2)-F(1,2)*F(2,3))]
for row, (w_lower,k_lower) in zip(proof['rational_majorization_certificate']['rows'], weight_lowers):
    check(row['node'] + ': endpoint first moment / largest-two-mass certificate',
          w_lower == F(row['w']) and k_lower == F(row['k']))

check('radius and uniform strict negative margin', -F(1,60) + 4*F(1,480) == -F(1,120))
check('previous conservative neighborhood radius', 3*F(1,60)/64 == F(1,1280))

# The caller's 64 checks are preserved above. Bind the five outward q boxes
# to the already checked exact linear-log node formulas, using rational intervals.
caller_equivalent_checks = len(checks)
if caller_equivalent_checks != 64:
    raise AssertionError("64-check adaptation accounting")
for node, (ql, qu) in zip(range(3, 8), q_scaled_bounds):
    exact_q = expected_q[node - 1]
    bounds = [interval(q) for q in exact_q]
    check(f"j={node}: outward q bounds linked to exact node formula",
          all(F(lo, 1000) <= lower <= upper <= F(hi, 1000)
              for lo, hi, (lower, upper) in zip(ql, qu, bounds)))
if len(checks) != 69:
    raise AssertionError("69-check fixed certificate accounting")
print(json.dumps({
    "certificate_version": "s19-235-fixed-v1",
    "python_version": platform.python_version(),
    "arithmetic": "Python standard-library fractions.Fraction; exact integers",
    "primary_reported_checks": 34,
    "caller_historical_checks": 64,
    "adapted_caller_equivalent_checks": caller_equivalent_checks,
    "additional_fixed_link_checks": 5,
    "fixed_checks": len(checks), "all_passed": True,
    "retained_reflected_slots": retained,
    "adjacent_paper_nodes": list(range(1, 8)),
    "adjacent_raw_slots": list(range(7)),
    "CPU_candidate_generation": False, "GPU_dispatches": 0,
    "sampled_heights": 0, "sampled_moments": 0,
    "scope": "Fixed proof constants and eight prescribed nodes only; the paper integral argument proves every positive integer moment",
    "checks": checks
}, ensure_ascii=False, sort_keys=True))
```

本次实际执行上列命令（仓根），时间 2026-09-09T19:49:35.614941+00:00；
外层命令和证书子进程均 exit 0，stderr 0 字节。程序版本 `s19-235-fixed-v1`，
Python `3.9.6`，标准库精确有理运算。提取后程序为 12418 字节，
SHA256 `sha256:478bbf361e446eaad6f834c084436ae7aa359f0f83977343be1c6e0c2a837276`。实际结果摘要（完整 69 个具名成功项在 runner 证书结果中）：

```json
{
  "CPU_candidate_generation": false,
  "GPU_dispatches": 0,
  "adapted_caller_equivalent_checks": 64,
  "additional_fixed_link_checks": 5,
  "adjacent_paper_nodes": [
    1,
    2,
    3,
    4,
    5,
    6,
    7
  ],
  "adjacent_raw_slots": [
    0,
    1,
    2,
    3,
    4,
    5,
    6
  ],
  "all_passed": true,
  "arithmetic": "Python standard-library fractions.Fraction; exact integers",
  "caller_historical_checks": 64,
  "certificate_version": "s19-235-fixed-v1",
  "fixed_checks": 69,
  "primary_reported_checks": 34,
  "python_version": "3.9.6",
  "retained_reflected_slots": [
    10
  ],
  "sampled_heights": 0,
  "sampled_moments": 0,
  "scope": "Fixed proof constants and eight prescribed nodes only; the paper integral argument proves every positive integer moment"
}
```

新证书的 69 项成功不改变历史 34 / 64 的来源归属。程序中的上界与正级数是固定证明证书，
不是对 implementation 的镜像测试，也没有建立测试框架。

## Canonical ingest 与逐字节保真

唯一摄入命令：

```sh
make ingest BASE=a8e208440d8a3f465a7b20c82ededbb27ee95026 SOURCE=arithmetic-boundary-quantization
```

实际 make 进程 **exit 0**，SDK `.NET 10.0.400`，只执行一次；原始结果行是：

```text
INGEST residual_open_added=22 skipped_existing=226 coarse_fallbacks=0 open_genres=0 cas_objects_written=22 ledger_changed=true
```

即新增 residual-open 22、跳过已有 226、coarse fallback 0、open genre 0、
新 CAS 22，账目有新增。它们是摄入计数，不是数学检查或搜索计数。

源现为 **286326 字节 / 5391 LF 行**，
`sha256:4856aba958844029d1c7150f610104d3652dcfd25139bdfb53e4346cd905db0a`；
相对 base 只追加 **32028 字节 / 648 LF 行**。完整前缀 **254298 字节 / 4743 LF 行**
逐字节等于 immutable base，前缀 hash 仍为
`sha256:c5e1fa97fff5921fe5ba10d84b0268c884caab112fb32beed0c92027ee1aa3f5`。
历史 31995 个 CAS、31995 个 YAML entry、65 个 report 和 42 个其它 digestion metadata
均保持 base 字节；除本源追加外没有历史 tracked 文件改变，index 为空。

只读核对器 `s19-binding-v2-heading-aware` exit 0：22 个 CAS 的 raw 与 normalized
指纹均逐项重算；本次二者恰好相同，且都等于其 `sha256:<atom_id>` 的 cas_ref。
每个 YAML 均绑定正确 source 和 atom_id，都是 328 字节、末尾恰一个 LF；
每个 CAS 均逐字节等于下表的完整源区间。ordered chain children 全部为空，
自动 chain 数 **0**。没有手改任何 CAS/YAML 或其 EOF。

30.1–30.21 的 21 个连续编号单元精确铺满半开字节区间 **[254371,286326)**，
无遗漏、重叠或局部句子替代。新增前导 LF 位于 **[254298,254299)**；
**[254299,254371)** 是 72 字节的结构标题及其空行：

```text
## 30. 三素数 (2,3,5) 的整箱全薄层邻域与无界共同高度

```

该标题在 canonical generic-v1 中不是独立 claim；没有把它算作编号论证单元。
初版只读核对器曾错误地要求历史末 atom 与首个新编号单元跨越此结构标题也连续，
因此 exit 1；随后修正核对范围并得到上列 exit 0。这是核对器的范围错误，
没有据此修改源或 producer 字节。

第 22 个新增绑定来自旧 29.22 的 canonical terminal-LF 变体：旧 atom
`f04f275b9eb1a3708e7da15d8770c4746c06eb8a25b82467a0514f4fd66fd832`
原字节仍在；新 atom
`512d1aba58b66d4e24ea5d76ce3aa804eaf7b057ef69df0d930ea382aabf2d90`
原文恰等于旧 atom 加一个 LF。这里如实保留两个地址，不据该自动变体修补生产输出。
30.1–30.20 CAS 末尾各两个 LF，30.21 一个 LF，均为生成器实际字节。

以下 atom_id 为裸 hash；每个 raw/normalized fingerprint 和 cas_ref 均使用
`sha256:` 前缀。完整 YAML 文件 hash、EOF 数及路径在 runner envelope 中逐项记录。

| 源单元 | atom_id | 源字节 [start,end) |
| --- | --- | --- |
| 29.22（terminal-LF 变体） | `512d1aba58b66d4e24ea5d76ce3aa804eaf7b057ef69df0d930ea382aabf2d90` | [251805,254299) |
| 30.1 | `4e5e5ab728ff95f50a0959fde254d9d6971f9e405fb815fbcde1750cc87ebc2e` | [254371,255468) |
| 30.2 | `2a85fd23acfab932247e9a16a40fcea2387617bddf75062a481b70efbf487b90` | [255468,257345) |
| 30.3 | `24f15d57c60f27aadae36b7efceae9452402016d72d15953cd8bd5cd6abfbbe8` | [257345,258142) |
| 30.4 | `12abf6c1ec71422f9e2e4cbaf0ac343e7ac64c387b0727fa6b4c9c3b055807dd` | [258142,261125) |
| 30.5 | `d1801ca9343edd8c56b6c9ec98c037397c9e4846a4896806a5eec7bcbb2e9984` | [261125,262528) |
| 30.6 | `efd08fcac03638df546bc1e23dfe24722159cfa9fe964af51af7d6a3d61e8a8e` | [262528,263365) |
| 30.7 | `fbb7454bcd639864dd7ee2f7cb7084b66e54443da1c2132a9ba3752029095b47` | [263365,265061) |
| 30.8 | `85de9bcf507e4587a51685442261aad594a152b001f6e9fb693bd460e014b534` | [265061,266669) |
| 30.9 | `ba19478e5c36a0a432aee475ee610c3c1f005049abcf48429ac091184dc81265` | [266669,268748) |
| 30.10 | `4c3b28bb104c34d2aa90cef2187e93938ca3e9cbc53c501d8813958f5a99ab6d` | [268748,271246) |
| 30.11 | `131c92c36bc569c0c2eb34316da497c6e85390e74a2a852a70aac0ecf32c99d1` | [271246,272301) |
| 30.12 | `8c99b875d8c495a54e4ba055ba07c9d72efc29cc61315ae49a48852f6d7ab471` | [272301,273028) |
| 30.13 | `daf515caf2d702d6b71f0ce60bb688edaeaacb608a4186dddb8109bed61851e2` | [273028,274387) |
| 30.14 | `c956bdba50f15fc3417e937f12b49e3c2e39c028bb787db4fccb31233c5a7f49` | [274387,275511) |
| 30.15 | `07f0567bd56ea68adb7523ec2330723357c1cf9a9e36704f22f95810878a68f7` | [275511,277007) |
| 30.16 | `0d37d9cf790d80246833ea2af7ddf8368dc19df4960a6f29a6838670c5b74140` | [277007,277752) |
| 30.17 | `5877dc4361a0fc02a74a764d446dae8e7415a053aebca1cd9f358acf0eeaa9ca` | [277752,279312) |
| 30.18 | `d83d6cfb23548c6dc74ca6da4cd4e786cab805ea9e90df4da96585b210f8bff4` | [279312,280152) |
| 30.19 | `e2759d04793e560260a6438f54d83891e3e19c5242076457af6aa016a2dd0362` | [280152,281491) |
| 30.20 | `6af3687288e6ecd9421adf7286ea9cbe85d23c1f87e19113e41f22627f15c448` | [281491,284017) |
| 30.21 | `41d300e7a5f0f9881740937ed7ebe63480459a69e0e0ba4c118088e4975a6140` | [284017,286326) |

收尾只读查阅本机同版本 `consensus-rnd:sshx 1.0.0-beta.42` 的
`/Users/auricstudio/.claude/plugins/cache/consensus-rnd/consensus-rnd/1.0.0-beta.42/skills/sshx/SKILL.md`、
同目录 `CODEX_WORKER_SPEC.md` 的工件条款和 `scripts/run-codex-worker.sh` 的 sentinel 检查。
implementation 不要求 verdict；sentinel 接受非符号链接的普通文件，未要求特定完成词。
仅将它们用于本 worker 的原子工件发布；没有启动 runner、其它席位或生命周期操作。
没有查阅其它 skill 版本。

最终报告自身的完整字节数和 SHA256 由 runner result envelope 记录，避免在文件内部
自指其整文件 hash。完整 changed-file manifest 与每个新 CAS/YAML 的源跨度和 ordered chain
也在该结构化结论中逐条列明；报告中的下列清单与之来自同一次最终路径核对。

完整 changed-path set 为 **46** 项：源 1、报告 1、新 CAS 22、新 YAML 22。
下列每行是相对于仓根的完整路径，无省略目录或未列出的变更：

```text
Meta/Digestion/atoms/sha256/07f0567bd56ea68adb7523ec2330723357c1cf9a9e36704f22f95810878a68f7
Meta/Digestion/atoms/sha256/0d37d9cf790d80246833ea2af7ddf8368dc19df4960a6f29a6838670c5b74140
Meta/Digestion/atoms/sha256/12abf6c1ec71422f9e2e4cbaf0ac343e7ac64c387b0727fa6b4c9c3b055807dd
Meta/Digestion/atoms/sha256/131c92c36bc569c0c2eb34316da497c6e85390e74a2a852a70aac0ecf32c99d1
Meta/Digestion/atoms/sha256/24f15d57c60f27aadae36b7efceae9452402016d72d15953cd8bd5cd6abfbbe8
Meta/Digestion/atoms/sha256/2a85fd23acfab932247e9a16a40fcea2387617bddf75062a481b70efbf487b90
Meta/Digestion/atoms/sha256/41d300e7a5f0f9881740937ed7ebe63480459a69e0e0ba4c118088e4975a6140
Meta/Digestion/atoms/sha256/4c3b28bb104c34d2aa90cef2187e93938ca3e9cbc53c501d8813958f5a99ab6d
Meta/Digestion/atoms/sha256/4e5e5ab728ff95f50a0959fde254d9d6971f9e405fb815fbcde1750cc87ebc2e
Meta/Digestion/atoms/sha256/512d1aba58b66d4e24ea5d76ce3aa804eaf7b057ef69df0d930ea382aabf2d90
Meta/Digestion/atoms/sha256/5877dc4361a0fc02a74a764d446dae8e7415a053aebca1cd9f358acf0eeaa9ca
Meta/Digestion/atoms/sha256/6af3687288e6ecd9421adf7286ea9cbe85d23c1f87e19113e41f22627f15c448
Meta/Digestion/atoms/sha256/85de9bcf507e4587a51685442261aad594a152b001f6e9fb693bd460e014b534
Meta/Digestion/atoms/sha256/8c99b875d8c495a54e4ba055ba07c9d72efc29cc61315ae49a48852f6d7ab471
Meta/Digestion/atoms/sha256/ba19478e5c36a0a432aee475ee610c3c1f005049abcf48429ac091184dc81265
Meta/Digestion/atoms/sha256/c956bdba50f15fc3417e937f12b49e3c2e39c028bb787db4fccb31233c5a7f49
Meta/Digestion/atoms/sha256/d1801ca9343edd8c56b6c9ec98c037397c9e4846a4896806a5eec7bcbb2e9984
Meta/Digestion/atoms/sha256/d83d6cfb23548c6dc74ca6da4cd4e786cab805ea9e90df4da96585b210f8bff4
Meta/Digestion/atoms/sha256/daf515caf2d702d6b71f0ce60bb688edaeaacb608a4186dddb8109bed61851e2
Meta/Digestion/atoms/sha256/e2759d04793e560260a6438f54d83891e3e19c5242076457af6aa016a2dd0362
Meta/Digestion/atoms/sha256/efd08fcac03638df546bc1e23dfe24722159cfa9fe964af51af7d6a3d61e8a8e
Meta/Digestion/atoms/sha256/fbb7454bcd639864dd7ee2f7cb7084b66e54443da1c2132a9ba3752029095b47
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/07f0567bd56ea68adb7523ec2330723357c1cf9a9e36704f22f95810878a68f7.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/0d37d9cf790d80246833ea2af7ddf8368dc19df4960a6f29a6838670c5b74140.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/12abf6c1ec71422f9e2e4cbaf0ac343e7ac64c387b0727fa6b4c9c3b055807dd.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/131c92c36bc569c0c2eb34316da497c6e85390e74a2a852a70aac0ecf32c99d1.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/24f15d57c60f27aadae36b7efceae9452402016d72d15953cd8bd5cd6abfbbe8.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/2a85fd23acfab932247e9a16a40fcea2387617bddf75062a481b70efbf487b90.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/41d300e7a5f0f9881740937ed7ebe63480459a69e0e0ba4c118088e4975a6140.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/4c3b28bb104c34d2aa90cef2187e93938ca3e9cbc53c501d8813958f5a99ab6d.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/4e5e5ab728ff95f50a0959fde254d9d6971f9e405fb815fbcde1750cc87ebc2e.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/512d1aba58b66d4e24ea5d76ce3aa804eaf7b057ef69df0d930ea382aabf2d90.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/5877dc4361a0fc02a74a764d446dae8e7415a053aebca1cd9f358acf0eeaa9ca.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/6af3687288e6ecd9421adf7286ea9cbe85d23c1f87e19113e41f22627f15c448.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/85de9bcf507e4587a51685442261aad594a152b001f6e9fb693bd460e014b534.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/8c99b875d8c495a54e4ba055ba07c9d72efc29cc61315ae49a48852f6d7ab471.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/ba19478e5c36a0a432aee475ee610c3c1f005049abcf48429ac091184dc81265.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/c956bdba50f15fc3417e937f12b49e3c2e39c028bb787db4fccb31233c5a7f49.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/d1801ca9343edd8c56b6c9ec98c037397c9e4846a4896806a5eec7bcbb2e9984.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/d83d6cfb23548c6dc74ca6da4cd4e786cab805ea9e90df4da96585b210f8bff4.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/daf515caf2d702d6b71f0ce60bb688edaeaacb608a4186dddb8109bed61851e2.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/e2759d04793e560260a6438f54d83891e3e19c5242076457af6aa016a2dd0362.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/efd08fcac03638df546bc1e23dfe24722159cfa9fe964af51af7d6a3d61e8a8e.yaml
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/fbb7454bcd639864dd7ee2f7cb7084b66e54443da1c2132a9ba3752029095b47.yaml
docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md
docs/reports/balanced-prime-235-all-slabs-0910.md
```

## 推理说明与尚未交付的边界

成熟框架是已有的有限临界节点支配、分数背包、递增凸序和齐次同时逼近。
实质增量是固定八节点的全矩证书及所有薄层共享的严格缩放裕量，和把两个非负增量
放在同一长度区间从而取得常数 2。源、固定报告和 canonical CAS/账目是一个连贯的
内容层：源承载完整假设与证明，报告使有限算术独立可复现，摄入为相同内容赋予地址。
将它们拆开会失去该层的可审查联系；即使生成文件数超过仓库历史 p75，也不能据文件数
把一条源文证明链拆成不完整的地址片段。这里没有混入 judge/tool 变更。

本次明确处理的真实文字问题是原压缩乘法、纸面 j 与 raw slot 的区别、准备时的旧在飞
前提及 34/64 检查数归属；原算术结论未因这些澄清被撤销。五项补充固定连接核验把字面
q 包围连回精确节点公式。没有以完成一层为由扩张成全形状、一般非齐次密度或 RH 结论。
进一步搜题、数值候选生成和后来 (2,3,7)、fixed5040、translated5040、第三素数射线
定理都属于其它研究/来源层，不是完成本次已给证明实现的必要步骤。

caller 拥有 Git 暂存、封存、push、PR、独立评审和普通仓库门；本 worker 未执行这些动作。
S19 源实现可交审，但最终交付仍等待 S18 MERGED，本次未读取其活跃 review 结果或查询
发布状态。不把本层本地固定核验、canonical ingest 成功或候选交回称为独立批准、
MERGED、Lean 吸收或长期研究目标完成。


## I19 / C57 relocation and CI repair (2026-09-10; representation only)

This appendix is original I19 evidence from Codex CLI under the pinned
`consensus-rnd:sshx 1.0.0-beta.42` worker contract, flight
`qgh0910-i19-s19-report-capacity-repair`, attempt 1. Repository priors are exposed;
no independent review verdict is claimed. All text above this heading is the
unchanged historical I14 report, including its input identities and execution receipts.

At repair base `20afad5e9e382df623b632aa16d2db24c2f7c9ab`, PR 6741 CI run
`34422715687`, job `102702004122`, reported exactly:

```text
SL-003 docs/reports: directory contains 49 files (admission limit 48, repository tolerance 96; split per CLAUDE.md 8)
RULE_REJECTED count=1
```

The supplied CI output is 739805 bytes, SHA256
`5c82ca8062eaa30a43f314df1caad2d383a62986d7dce8b822d7f2e86898bd9d`.
The move changes direct regular-file counts from 49 to 48 in `docs/reports`,
and from 0 (absent directory) to 1 in `docs/reports/quantized-gh`.
The 112 report files across all report subdirectories are retained; none unrelated moved.

Historical identities: the original report is exactly the first 38210 bytes / 603 LF
of this file, SHA256 `8bb7197f4931fdc2337ad7d900a514c588520d2ec48cd273cd69065d0e335db4`,
Git blob `4df4e7e3769f10a650ef4f95d6cc5beae923da32` at the base's old root path.
The original source is Git blob `66ad22043eb3ca83586f8b4ec8f1f87710fcbfe0`,
286326 bytes / 5391 LF, SHA256
`4856aba958844029d1c7150f610104d3652dcfd25139bdfb53e4346cd905db0a`.
Both matched the supplied `s19-report-snapshot-0910.md` and
`s19-source-snapshot-0910.md` byte for byte. These immutable blobs and historical
snapshots are references; no second maintained source or report was added.

Current source: 286339 bytes / 5391 LF, SHA256
`59838eb016d5a88043e4f9ca4ffc3c999d85357762d078cf4f05168521ad0d18`. Its only edit is the section 30.20 Markdown destination;
the label and every other byte match the original source after reversing that
single replacement. The first 254298 bytes / 4743 LF remain exactly the S18 prefix,
SHA256 `c5e1fa97fff5921fe5ba10d84b0268c884caab112fb32beed0c92027ee1aa3f5`.
The current [theory source](../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md)
resolves from this location. The report's earlier relative source link and earlier
root-path extraction recipe describe its historical location at the immutable base.
They were preserved verbatim and are superseded as live addresses by this appendix.

Current repository-root extraction/execution recipe (documented, **not executed by I19**):

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess
import sys
report = Path('docs/reports/quantized-gh/balanced-prime-235-all-slabs-0910.md').read_text()
marker = '```python\n# S19_FIXED_CERTIFICATE_V1\n'
code = '# S19_FIXED_CERTIFICATE_V1\n' + report.split(marker, 1)[1].split('\n```', 1)[0] + '\n'
result = subprocess.run([sys.executable, '-'], input=code, text=True)
raise SystemExit(result.returncode)
PY
```

The embedded `S19_FIXED_CERTIFICATE_V1` payload remains 12418 bytes / 247 LF,
SHA256 `478bbf361e446eaad6f834c084436ae7aa359f0f83977343be1c6e0c2a837276`.
Only extraction bytes, syntax and structure were inspected. I19 performed **zero
mathematical program executions**; the historical 69-check receipt above remains
historical evidence, with no new mathematical or review claim.

### I19 canonical run and complete current-unit bindings

After the source reached the current identity above, I19 ran exactly once:

```sh
make ingest BASE=20afad5e9e382df623b632aa16d2db24c2f7c9ab SOURCE=arithmetic-boundary-quantization
```

Actual process exit: **0**; UTC start `2026-09-10T01:08:06.392218+00:00`,
finish `2026-09-10T01:08:35.575145+00:00`. The source hash was identical before
and after the command. The original output (125 bytes, SHA256
`b0bd8cf9cb96b33266b16f202e90ec0ccdd0a31a5e36084d0dd67625658fafac`) was:

```text
INGEST residual_open_added=1 skipped_existing=247 coarse_fallbacks=0 open_genres=0 cas_objects_written=1 ledger_changed=true
```

Producer inputs are the unchanged candidate at the repair base: `tools` Git tree
`8c4a68f7515e119a57fff7a9e23f9ba4e0e4762f`; root `Makefile` SHA256
`b623554844bc4adc4eef9ba7d7176ea7f4ff08180f6be05f0603d8736ebe68a6`;
`tools/scripts/ingest.sh` SHA256
`2377f28ac22d099a0e2cd3264d55fd57dd5322c3565809b5fdcb7b266bd2070c`;
`Meta/Digestion/backfill/arithmetic-boundary-quantization/source.toml` SHA256
`0948618a915f39996a9612c7a2cc1ed2e832c9121a57819ba3db8714c625bade`,
selecting `generic-v1`. The source Git blob identity is now
`a75eb08b8c118c7bb85bec473a3bf04cdf0b354f` (computed identity; still unstaged).

The one new atom is
`09b239a66f1111ac5773805a1bcbe875a4974982ee20f26ea337ef808314e093`,
2539 bytes / 32 LF, with two terminal LF. Its new YAML is 328 bytes / 7 LF,
one terminal LF, SHA256
`6b887fc13f08384d163a9fdb21bbc39b84cec0d252ea732a605f1665b0211909`.
The two exact new paths are:

```text
Meta/Digestion/atoms/sha256/09b239a66f1111ac5773805a1bcbe875a4974982ee20f26ea337ef808314e093
Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/09b239a66f1111ac5773805a1bcbe875a4974982ee20f26ea337ef808314e093.yaml
```

The read-only byte audit checked each entire heading-to-next-heading unit,
including trailing LF, against the actual CAS content and its source-owned YAML.
All **21/21** units cover exactly **[254371,286339)**, **31968 bytes**, with zero
gaps or overlaps. This is full-unit byte coverage, not merely a start-byte match.
The earlier section-title range [254299,254371) is structural text outside these
numbered units. The table below is current I19 evidence; the earlier table remains
historical. Each raw/normalized fingerprint and cas_ref is `sha256:` plus its atom_id;
all ordered chain children are empty. Only 30.20 produced new files.

| Current unit | Full source byte span [start,end) | Current atom_id |
| --- | --- | --- |
| 30.1 | [254371,255468) | `4e5e5ab728ff95f50a0959fde254d9d6971f9e405fb815fbcde1750cc87ebc2e` |
| 30.2 | [255468,257345) | `2a85fd23acfab932247e9a16a40fcea2387617bddf75062a481b70efbf487b90` |
| 30.3 | [257345,258142) | `24f15d57c60f27aadae36b7efceae9452402016d72d15953cd8bd5cd6abfbbe8` |
| 30.4 | [258142,261125) | `12abf6c1ec71422f9e2e4cbaf0ac343e7ac64c387b0727fa6b4c9c3b055807dd` |
| 30.5 | [261125,262528) | `d1801ca9343edd8c56b6c9ec98c037397c9e4846a4896806a5eec7bcbb2e9984` |
| 30.6 | [262528,263365) | `efd08fcac03638df546bc1e23dfe24722159cfa9fe964af51af7d6a3d61e8a8e` |
| 30.7 | [263365,265061) | `fbb7454bcd639864dd7ee2f7cb7084b66e54443da1c2132a9ba3752029095b47` |
| 30.8 | [265061,266669) | `85de9bcf507e4587a51685442261aad594a152b001f6e9fb693bd460e014b534` |
| 30.9 | [266669,268748) | `ba19478e5c36a0a432aee475ee610c3c1f005049abcf48429ac091184dc81265` |
| 30.10 | [268748,271246) | `4c3b28bb104c34d2aa90cef2187e93938ca3e9cbc53c501d8813958f5a99ab6d` |
| 30.11 | [271246,272301) | `131c92c36bc569c0c2eb34316da497c6e85390e74a2a852a70aac0ecf32c99d1` |
| 30.12 | [272301,273028) | `8c99b875d8c495a54e4ba055ba07c9d72efc29cc61315ae49a48852f6d7ab471` |
| 30.13 | [273028,274387) | `daf515caf2d702d6b71f0ce60bb688edaeaacb608a4186dddb8109bed61851e2` |
| 30.14 | [274387,275511) | `c956bdba50f15fc3417e937f12b49e3c2e39c028bb787db4fccb31233c5a7f49` |
| 30.15 | [275511,277007) | `07f0567bd56ea68adb7523ec2330723357c1cf9a9e36704f22f95810878a68f7` |
| 30.16 | [277007,277752) | `0d37d9cf790d80246833ea2af7ddf8368dc19df4960a6f29a6838670c5b74140` |
| 30.17 | [277752,279312) | `5877dc4361a0fc02a74a764d446dae8e7415a053aebca1cd9f358acf0eeaa9ca` |
| 30.18 | [279312,280152) | `d83d6cfb23548c6dc74ca6da4cd4e786cab805ea9e90df4da96585b210f8bff4` |
| 30.19 | [280152,281491) | `e2759d04793e560260a6438f54d83891e3e19c5242076457af6aa016a2dd0362` |
| 30.20 | [281491,284030) | `09b239a66f1111ac5773805a1bcbe875a4974982ee20f26ea337ef808314e093` |
| 30.21 | [284030,286339) | `41d300e7a5f0f9881740937ed7ebe63480459a69e0e0ba4c118088e4975a6140` |

All 32923 pre-repair CAS blobs, 32923 YAML entries, other digestion metadata,
and 112 reports preserve their full historical bytes (this report via its exact
38210-byte prefix at the new location). In particular, the old 30.20 atom
`6af3687288e6ecd9421adf7286ea9cbe85d23c1f87e19113e41f22627f15c448`
and YAML remain untouched. Both historical 29.22 LF variants named above survive.
Current 30.1–30.20 have two terminal LF; 30.21 retains one LF and its original atom,
with only its current offset shifted by 13 bytes. No CAS/YAML was manually edited.

Verification commands and actual exits are recorded in I19's result envelope;
the worker-owned `i19-coverage.json` records all full spans, CAS/YAML identities,
and the original command receipt. Static extraction checks compared the old and
current recipes byte for byte except for the Path literal, parsed syntax without
execution, and confirmed identical certificate payloads and both current links.
The original CI rejection is not replaced by a local CI-success claim. Caller owns
sealing, fresh independent representation-repair review, required CI and PR 6741
MERGED delivery; these remain open. No other target, scientific settlement or
standing-goal completion was claimed. Final report identity belongs in result.json,
not in a self-referential hash inside this report.

I19's final audit wrapper first exited 1 after those byte checks: it wrongly required
exit 0 from `git diff --no-index --check /dev/null` on the new report. Git returned
1 with empty stdout/stderr (different files, no check diagnostics). The wrapper's
expectation was corrected for this command; its actual rerun exit is in result.json.
This audit-wrapper correction changed no source or canonical output and did not rerun ingest.


<a id="i31-inactive-archive"></a>

## I31 — C78 inactive source archive; mathematical dependency remains open

This appendix is inactive historical evidence. Every quoted instruction, command, code block, path, model claim, test, ingestion and delivery record below belongs to the original source revision. It is neither a command nor a current result. The exact original report prefix ends at byte 47922.

The independent migration spans all 30 original sections. Whole-body purity, independent approval, delivery and goal completion remain false. The original 1253-byte Gram subsection [23492,24745), SHA256 848cc4f7d0e77de827c99d9c8e77f55a52fb33daa23c769dda1b8ce960ca27c1, remains contiguous in the active source and explicitly unproved. C88 output has not been supplied or adopted; no new proof, assumption or correction number is introduced. Numerical evidence retains its original status and trust limits; archived certificates have not been rerun.

Permanently reserved outside the active body: 9, 13, 14, 25.17, 26.29, 27.20, 28.19, 29.22, 30.21. No later mathematical item may reuse these numbers.

### Archived original bytes [64,143)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
本卷是 `docs/develop/theory/` 下的**参考输入**,日期为 2026-09-08。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [209,292)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
它们都不因写入本卷或摄取为 atom 而成为 Lean/kernel-frozen 真值。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [353,386)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
长期研究约定与本轮问题⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [678,879)

Disposition: operational leading fragment.

~~~~~~~~~~~~text
目标是持续研究整数索引、严格不等号、等号、零余量与量化规则之间的关系,给出明确的算术与量子模型接口及其剩余义务。本轮只回答一条具体问题: ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [1061,1866)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
研究 lane 为 `lane/math/quantized-gh-boundaries-0908`,工作树为 `/Users/auricstudio/trureturing-qgh-boundaries`,intake base 为 `45e7b20dd95dd8b2d7b8784392c1814193b80515`。本轮保持该 Git 基线,只增加本卷及其 canonical ingestion 输出,不引入新形式根、私有公理或冻结声明。

这是用户指定的长期核心问题研究线。host 目标轮次无上限,每次载体调用及其重试仍有界;同一症状第二次出现时停止原样重试并查根因。连续两周没有边际数学或证据增益时修订方法,不以增加卷数、有限样本数或计算精度冒充成功。继续由现有 host 驱动,不运行无限 daemon。本次有限增量不完成长期目标 S6;评审、PR 三门与 MERGED 落地由 caller 后续承担,未合并工作仍为 open。

~~~~~~~~~~~~

### Archived original bytes [3371,3429)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
上面的整数恒等式由第 6 节程序作精确检查;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [3478,3516)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 小素数为什么让因数较丰?⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [8131,8302)

Disposition: operational fragment in mixed mathematical passage; type / grammar metadata.

~~~~~~~~~~~~text
Li 原文 DOI 仅作书目信息,本轮未取得其全文;不把二手核对写成亲读原文。第 6 节直接从导数定义核对本次使用的 Taylor 系数关系。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [10918,10961)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
;本卷不重做它的反驳或有限证书⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [12281,12300)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
此处代数核对;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [15164,15332)

Disposition: operational leading fragment.

~~~~~~~~~~~~text
第 6 节程序还对 \(m=1,2,10,200,1000000\) 用 `Fraction` 检查原矩阵的顺序主子式为正,舍入行列式为 \(-1/m^2\),二次型为 \(-2/m\),退出码 0。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [15883,15917)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 从 Taylor 系数到 Li 回返⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16573,16585)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
程序认证⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16631,16659)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
`zeta(deflate=True)` 表示 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16759,16783)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
程序中的 `x` 正是 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16795,16796)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16828,16887)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
`ctx.cap=4` 保留到三次幂,已足够计算上面三项;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16940,16980)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 严格包围与舍入的精确失败⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [16982,17056)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
Python-FLINT 0.8.0 的 Arb,256 位精度,给出下列经球比较确认的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [17711,17833)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
程序还只用 \(r_1,r_2\) 的有理上下界验证 \(L_2-(2U_1^2-1)>0\),作为不依赖区间相关性的精确检查。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [18421,21726)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
### 可执行复现

在 `/tmp` 中执行下面完整命令即可复现。依赖固定为 `python-flint==0.8.0`;Python 标准库的 `Fraction` 负责精确有理运算。实施 worker 独立执行同一程序,退出码 0,最后输出 `python-flint=0.8.0 precision=256 cap=4 PASS`。信任边界包括 Python-FLINT 的接口、FLINT/Arb 特殊函数及级数球包围实现、Python 和运行环境;这没有生成 Lean 证明项。

```sh
uv run --with python-flint==0.8.0 python - <<'PY'
from fractions import Fraction as F
from math import floor, prod
import flint
from flint import arb, arb_series, ctx

def toeplitz(x, y):
    return [[F(1), x, y], [x, F(1), x], [y, x, F(1)]]

def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))

def witness(a):
    v = [1, -2, 1]
    return sum(v[i] * a[i][j] * v[j] for i in range(3) for j in range(3))

def q(x, m):
    return F(floor(m * x + F(1, 2)), m)

assert prod(p**a for p, a in zip([2, 3, 5, 7], [4, 2, 1, 1])) == 5040
assert prod(a + 1 for a in [4, 2, 1, 1]) == 60
assert prod(sum(p**j for j in range(a + 1))
            for p, a in zip([2, 3, 5, 7], [4, 2, 1, 1])) == 19344
assert 4181 + 610 + 233 + 13 + 3 == 70 * 3**2 * 2**3 == 5040
assert 2**4 * 3**2 * 5 * 11 == 7920
print("arithmetic: 5040, tau=60, sigma=19344, both encodings, 7920 OK")

for m in [1, 2, 10, 200, 1000000]:
    h, eta, t = F(1, m), F(1, 12 * m), 1 - F(1, 3 * m)
    r1, r2 = (1 - eta) * t, (1 - eta) * (2 * t*t - 1)
    assert 0 < (1-r1)/h == F(5, 12)-h/36 < F(1, 2)
    assert F(1, 2) < (1-r2)/h == F(17, 12)-h/3+h*h/54 < F(3, 2)
    a = toeplitz(r1, r2)
    assert 1-r1*r1 > 0 and det3(a) > 0
    rounded = [[q(x, m) for x in row] for row in a]
    assert rounded == toeplitz(F(1), 1-h)
    assert det3(rounded) == -h*h and witness(rounded) == -2*h
    print("family", m, "PD=True", "det=", det3(rounded), "vTv=", witness(rounded))

ctx.prec, ctx.cap = 256, 4
t = arb_series([0, 1])
s = 1 + t
x = s * (-s * arb.pi().log() / 2).exp() * (s/2).gamma() * (1+t*s.zeta(deflate=True)) / 2
assert x[0].contains(arb(1)/2)
f = (x/x[0]).log()
assert f[1] > 0
r1, r2 = f[2]/f[1], (2*f[2]+3*f[3])/(2*f[1])
gap = r2 - (2*r1*r1-1)
d = 10**18
endpoints = [(999196806720852614, 999196806720852615),
             (996790337371607624, 996790337371607625),
             (1820249309832, 1820249309833)]
for name, value, (lo, hi) in zip(["r1", "r2", "gap"], [r1, r2, gap], endpoints):
    assert arb(lo)/d < value and value < arb(hi)/d
    print(name, str(lo)+"/"+str(d), "< value <", str(hi)+"/"+str(d))
bounds = [(F(lo, d), F(hi, d)) for lo, hi in endpoints]
assert 0 < bounds[0][0] < bounds[0][1] < 1
assert 0 < bounds[1][0] < bounds[1][1] < 1
assert bounds[1][0] - (2*bounds[0][1]**2-1) > 0
assert 1-r1*r1 > 0 and (1-r2)*gap > 0
for (lo, hi), expected in zip(bounds[:2], [F(1), F(199, 200)]):
    assert q(lo, 200) == q(hi, 200) == expected
rounded = toeplitz(F(1), F(199, 200))
assert q(F(1), 200) == 1
assert det3(rounded) == -F(1, 40000)
assert witness(rounded) == -F(1, 100)
print("actual xi: PD=True, Q_200 det=-1/40000, vTv=-1/100")
print("python-flint="+flint.__version__, "precision="+str(ctx.prec), "cap="+str(ctx.cap), "PASS")
PY
```

~~~~~~~~~~~~

### Archived original bytes [21732,21756)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
障碍登记与下一步⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [21758,21783)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本轮增加的证据是:⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [21951,22027)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
以下是本卷的研究义务,不是手写消化状态或新形式工单。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [22055,22085)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
下一次能改变它的结果⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [22961,23112)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
| 形式与发布 | 纸面和数值证据,未冻结、未合并 | caller 的独立评审、canonical PR 三门及 MERGED;形式化另按准入处理 |
~~~~~~~~~~~~

### Archived original bytes [23366,23490)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
本轮不重做相邻 #5908、#6160、#6298 所属的 Robin 有限证书、整数资源优化或物理响应 no-go 工作。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [24752,24773)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
来源核对与产地⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [24779,24812)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本轮实际核对的数学来源⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [24814,25174)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
下列六份外部预印本或论文已在本轮成功下载并核对,两个仓内引用则按钉版的本地文件读取。Li DOI 仅是书目链接,没有取得其全文。HTML 用数学 `alttext` 保留公式,PDF 按页提取核对。本地源字节与 SHA-256 收据保存在实施 attempt 工件中;这些下载和提取工具不承担数学正确性。

~~~~~~~~~~~~

### Archived original bytes [25185,25200)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
已检查文本⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [25990,26006)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,未取得全文⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [26683,26711)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
;未亲读 Robin 1984 原文⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [26879,26901)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本地同一 HEAD 的 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [27228,27249)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本地同一 HEAD 的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [27405,27451)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
以上文献查询支持判据的准确陈述;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [27525,31268)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
### 载体与独立性

本卷由 caller 的 `consensus-rnd:sshx` implementation brief 驱动的 Codex worker 写作,worker 未调用新的 skill 或派出子席。worker 独立读文献、核对纸面代数并运行第 6 节程序,没有读取本轮 thinking 日志或 peer review 工件。这里的“独立复算”指重新执行与核对,也不是实施者给自己签发独立评审批准。先验边界为 Codex `repo-prior-exposed`、oracle `external-prior-exposed`;同轮 peer 输出不作为实施输入,不声称先验无污染。

以下载体事实由 caller 提供,worker 未读取其私人运行日志。六个隔离 thinking 席最终均为 `revise`;caller 经元层收敛保留端点和正规化限制,选择了本卷的小型反驳及实际 ξ 区间证据。**这不表示六席一致批准一个未经修改的旧计划。** 有效 thinking 结果来自 oracle 回退失败后使用的 Codex,不能据此声称模型族多样性。

独立的实际 GPT PRO 咨询已完成,caller 提供的记录为:

| 字段 | 原记录 |
|---|---|
| task | `080f1df1-b4cf-4e0a-b1c4-d76dd21fcb1a` |
| conversation | `conv_b9e496c90a421437` |
| pool | `chrono-chatgpt-pro-pool` |
| dispatch model | `chatgpt-5.5-pro` |
| terminal model | 字面字符串 `6\nPro`,按 JSON 字符串表示为 `"6\\nPro"` |
| ChatGPT URL | <https://chatgpt.com/c/6a9fe809-5830-83ec-8008-2fa7d47d2d92> |

dispatch 与终态字段是两条不同观测,本卷不据此推断未见的精确后端型号。原 pool 的前两次尝试均以 `page.goto Page crashed` 失败,没有研究产出。另一个 PRO follow-up `e512bb9d-21ac-46f4-8209-9941632be445` 在本次 intake 中为 pending,不能引用为已完成回答。PRO 的建议仍是可错参考输入;第 7 节对 \(T^*T\) 的类型修正明确保留。

本卷的 canonical 摄取命令为:

```sh
make ingest BASE=45e7b20dd95dd8b2d7b8784392c1814193b80515 SOURCE=docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md
```

摄取计数、atom 样本和退出码以 worker 结果信封中的实测输出为准,不能把摄取成功写成定理冻结或 PR 已合并。后续评审纠正须明确记下被改判的结论及其证据,已摄取 atom 不手改、不删除。

## 9. 追加勘注: 终态字符串与本次来源

日期 2026-09-08。本次 implementation worker 按 `consensus-rnd:sshx` worker 模式执行,没有派出子席,没有读取 peer 日志,没有提交、推送或操作 PR。以下为参考输入中的纸面论证与数值库证据,不是独立评审批准,也不是 Lean-frozen 定理。长期研究目标保持 active。

**具体勘误,只追加不改旧文:** 第 8 节把 terminal model 当成含字面反斜杠的字符串,这是记录错误。caller 指定的 `pro-map-task-complete.json` 经本次 JSON 解析,其 model 字段的 Unicode codepoints 恰为 `[54,10,80,114,111]`:字符 `6`,一个实际 LF,再接 `Pro`。正确的 JSON 序列化是 `"6\nPro"`,其中只有一个换行转义序列;不是第 8 节所写的含两个反斜杠的序列化。原 JSON SHA256 为 `6274bc727c4a83f7056a8112edee31940604806de34a0c7d4d3413cb32f1c715`。本勘注不据此推断未见的后端型号,不改变第 5-6 节数学。

本次实际源 HEAD 为 `8698bf1a197adb887967cb6722261ea525ea9400`,已经包含 caller 提交的第一卷。`45e7b20dd95dd8b2d7b8784392c1814193b80515` 仅保留为历史 intake 与摄取 BASE。追加前本卷 598 行,源 SHA256 为 `1051e55d93ab1beae2cfc2f4fcee04a6f9c79b1a17792c5ce187286d20b44404`;原文及 62 个已摄入 atom 全部保留。以下使用 [Q]、[Z] 的当前 HEAD 字节,其 SHA256 分别为 `4d38746e7e83ef96bb8c5af3b58f2e6d7a51484f4cbdd673ca4e644fa34bf246`、`2c60183ac740a7426db7f9113b5d769f883382d75bb216e6dfa780c42fca11f7`。

~~~~~~~~~~~~

### Archived original bytes [31322,31353)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 坐标独立不指定度量⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [32401,32448)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 黄金位是编码,不会新增独立方向⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [33048,33095)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### Robin 的函数曲率与已有 KL 恒等式⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [33480,33508)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
(本次源约 2210-2460 行)⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [33866,33894)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
截面几何能组织搜索;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [34024,34062)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 既有 Schur 条件的投影解释⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [34933,34970)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 两个不同的量化输出空间⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [35485,35549)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
(这里只用 Python 任意精度整数形成行列式乘积。)⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [36199,36232)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
输入认证与完整有限前缀⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [36234,36422)

Disposition: operational leading fragment.

~~~~~~~~~~~~text
程序 `tools/scripts/agent/xi_quantization.py` 从第 6 节的 completed xi Taylor 公式自身计算 \(x,y,\beta\),不读取理论散文。Python-FLINT 0.8.0、Arb 256 位、`ctx.cap=4`;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [36729,37010)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
包围方法是对缩放 Arb 球求 `floor().unique_fmpz()`,再用 Arb 比较严格验证两个有理端点。无法认证时提高精度至最多 2048 位,仍失败则停止;不解析小数显示。程序也重新认证第 6 节全部 \(10^{18}\) 粗控制区间,结果一致。

~~~~~~~~~~~~

### Archived original bytes [37183,37207)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
作 Python 整数计算,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [37296,37322)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
或只检查 GPU 负候选⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [37325,37352)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
实际运行请求并完成⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [37368,37516)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,expected、attempted、classified 均为 1399999;unresolved 为 0。每个已完成分辨率还核对 Schur 重建的整系数行列式恒等式。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [37860,37952)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
首负预测在开跑前已登记,此次枚举确认它;末负与计数是本次新测量。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [38193,38262)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
首末奇异的零向量及各类首末记录都在生成报告内。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [38443,40866)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; type / grammar metadata.

~~~~~~~~~~~~text
### 真 MPS 候选与误差账

本次报告来自 Apple M3 Ultra、60 GPU 核、Metal 4、103079215104 字节内存,Python 3.12.13、Torch 2.8.0、NumPy 2.0.2。Torch 导入前设置 `PYTORCH_ENABLE_MPS_FALLBACK=0`,要求 MPS built/available,实际 tensors 位于 `mps:0`。bin 候选为 float32,索引与 \(B\) 符号运算为受支持的 int64;没有在 GPU 上用定宽整数乘行列式。先断言 \(m\le1400000<2^{24}\) 和 \(4(1400001)^2<2^{63}\),再按 65536 行分块分配。复用 `gpu5040.state_store.StateLocks`,在独立外部 state 目录先取 state 锁,再取 per-user GPU/verifier 锁;没有改动或停止既有 gpu5040 工作。

比较 naive `floor(m*t+0.5)` 与 centered-deficit `m-ceil(m*(1-t)-0.5)`。后者的 \(1-t\) 先由高精度有理数形成,再转 float32;仍然只是候选。

| MPS 候选 | 任一 x,y,beta bin 不同的 m 数 | 仅 x,y 任一不同的 m 数 | B 符号/逐项类别不同的 m 数 | Schur 类别不同 |
|---|---:|---:|---:|---:|
| naive | 131641 | 116459 | 50715 | 0 |
| centered | 61386 | 196 | 61 | 0 |

逐坐标 bin 差异为 naive `(x=64006,y=55539,beta=17380)`,centered `(x=55,y=141,beta=61201)`。beta 为负且靠近 -1,所规定的 centered 公式并没有同等改善它。精确不定而 GPU 报非负的数量为 naive 8314、centered 26;精确 PD 而 GPU 报不定分别为 42401、35。报告保留有界 bin/符号样本及完整三类混淆计数。例如 centered 在 \(m=188026\) 将精确 bins \((187875,187422)\) 算成 \((187875,187423)\),把不定报成 PD。因此即使 centered 也不能承担证书。

**历史控制保留:** caller 在派发中给出的旧 MPS smoke 于 \(m=1400000\) 得 naive \((1398876,1395507)\),而精确 bins 是 \((1398876,1395506)\)。这是旧观测,不因新跑而改写。本次当前源码重跑再次得到同一 naive 偏一结果,centered 得精确 bins;两者在这个控制上都报 PD,所以 bin 差异不一定改变类别。控制不计入有限前缀的计数或 digest。

最终主运行 UTC 为 `2026-09-08T12:14:36.796123+00:00` 至 `2026-09-08T12:14:45.828243+00:00`;两端 `torch.mps.synchronize()` 包围的分块总计 0.18041808810085058 秒,含分配/派发,不含 CPU 传输,全部枚举及比较耗时 7.707086249953136 秒。首轮实际 MPS 运行亦完整成功,最终报告是增加符号样本与混淆计数后的新运行,并非挪用旧计时。

### 解析尾界,不是数值外推⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [42104,42171)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
### 复现、状态与未履行义务

结构化全部证据位于 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [42235,44144)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; type / grammar metadata.

~~~~~~~~~~~~text
,包括有理区间、程序及本地 import SHA256、实际 HEAD、依赖/硬件、逐块计时、范围与样本。程序仅在请求范围完整且无 unresolved 时原子发布报告;失败记录留在外部 state 目录,不能覆盖已有完整报告。CPU-only 模式明确写无 MPS 运行,不能向仓内发表 GPU 主报告。可执行入口为:

```sh
make -C tools xi-quantization XI_REPORT=/Users/auricstudio/trureturing-qgh-boundaries/docs/reports/xi-quantization-0908.md
make -C tools xi-quantization XI_MODE=cpu XI_CHUNK=50000 XI_REPORT=/tmp/qgh-xi-quantization-state/cpu-report.md
make -C tools xi-quantization-test
```

Make 配方固定 `uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python ...`,没有修改全局 Python 或 Codex 配置。主报告内记录展开后的精确命令。完整有序数学流的 SHA256 为 `81e77ccc81333be01c37c6fbb3a8168c37386f8293c18131ad45b9f7776e2b60`:对递增的每个完成 \(m\),以 ASCII 写 `m,kx,ky,kbeta,entrywise_class,schur_class` 后接 LF,无头行;类别字面值为 `indefinite`、`singular`、`pd`,控制另记。这个 digest 不含时间、设备、源码版本等运行元数据,不同设备可以复算比较。

完整 CPU-only 运行与主 MPS 运行的数学 digest 相同。另一份不导入分类实现的独立算式复核使用 512 位 Arb 比较、`divmod` 半格判定、缺额变量行列式及全部主子式,也复现同一计数和 digest,并以显式矩阵二次型核对首末负/零见证。这里的独立是算法与复算路径的独立,不是新增评审席或模型族独立性。9 个聚焦行为测试覆盖半格歧义、正负平局、奇异/不定、任意精度乘积、重建、覆盖缺口、序列化及 GPU 非负漏报;既有 ScriptTests 入口实际执行了这些测试。

本增量将“对这一固定三阶块的所有分辨率”从未执行登记变成⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [44397,44401)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
PRO ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [44430,44565)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
caller 仍负责独立评审、PR 三门与发布;本次 worker 不把任何本地验证称为 MERGED 或 standing-goal satisfaction。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [44567,50141)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
## 13. 实施收尾的追加记录

第 12 节已摄入的运行事实继续保留。随后修正报告发布失败的状态记录:即使数学覆盖已完成,发布异常也明确记为 `publication_failed` 并返回非零,保留已完成覆盖与已有报告,不把发布失败说成完整运行。新增的存储失败注入测试使聚焦行为测试总数成为 10;这不改变任何 bin、分类或数学 digest。

因此当前主报告采用终版程序的另一次完整 MPS 运行,UTC 为 `2026-09-08T12:26:31.783258+00:00` 至 `2026-09-08T12:26:40.339952+00:00`,同步 MPS 分块总计 0.162419916363433 秒,枚举/比较 7.136823707958683 秒。全部精确计数、混淆计数和 digest 与第 12 节所记运行相同。终版程序 SHA256 为 `52b0b82da67a608464b3acc189b1449e731e8c6ad4e9cef168978ca22a57908c`;本地 import `gpu5040/state_store.py` 为 `a1eda747e24ea792caac30da136e85ba0beac6dc6f08d53880624b8ac6b1f03a`,Make 入口为 `624482b96b758254c78d31c8dacfa330fd8a775d6beef6412248a17e9aed1cb9`。终版 CPU-only 完整运行也给出同一 digest,且明确没有 MPS 执行。此前的运行来源和计时只作为历史,没有拿来替代终版源码的实跑。

## 14. 评审勘误:发布边界与回归核验

本节是 `consensus-rnd:sshx` 实施修复的 repo-derived 工程证据,不追加数学定理。第 12 节“失败记录不能覆盖已有完整报告”和第 13 节“发布异常保留已有报告”的全称保证不成立,在此明确收窄:共享 `state_store.atomic_write` 先 `os.replace`,后同步目录;只有 replacement 之前的失败保留旧目标字节。quality 席在独立字节相同的夹具中注入 replacement 之后的目录同步错误,观察到非零退出、外部 `publication_failed`,同时目标已是新报告。此时新字节可以可见,掉电后的持久性不确定,没有回滚保证。该反例不表明第 13 节的历史实际 MPS 运行发生过 I/O 失败;其来源、计时和已有 atom 均继续保留。

修复后的报告 schema 为 2。`mathematical_status=complete` 只表示数学认证完成;写入 Markdown 的 `status=publication_unconfirmed` 是发布前快照,成功发布也不改写为自证成功。外部 runtime/stdout 的 `status=complete` 表示报告 writer 已返回,进程退出 0 还要求 runtime 写入返回。报告发布异常仍记 `publication_failed` 和异常类型/消息,保留覆盖、计数与完整数学 digest 并返回非零。若 runtime 记录本身也写失败,stdout 另带 `runtime_record_error` 并返回非零;此前可见的 runtime 同样不能自证自己的最终目录同步。此契约明确区分数学完成、可见字节和 I/O 结果,没有另造事务服务或改写共享 writer。

聚焦 Python 套件现为 11 项。实际共享 writer 的测试覆盖成功、replacement 前失败、replacement 后目录同步失败,以及失败/成功结果记录的目录同步失败;成功和失败两侧都核对三行合成覆盖及独立 CSV digest。尾界测试独立钉住 `error_at_M=7000001/3920000000000` 与 `gap_minus_error=211525460221/6125000000000000000`,并拒绝 `gap-error` 不严格为正、x/y/beta 严格端点达到等号或越界,及独立端点 PD 前提失败。预登记把尾界系数 5 改为 1,实得仅 `test_tail_rational_bound_and_strict_hypotheses` 失败,Python 退出 1 / Make 退出 2,无编译或导入错误;恢复后 11 项全绿。Make 的两个 `.PHONY` 和两条 help 配方合为各一条,已有 `ToolsTargets` 增列两个真实命令,保留并扩充严格 dispatch 断言。实际 `ToolsMakefileIsAThinCompleteDispatchTable` 先复现 `Assert.Single` 的两项失败;修复后该测试、根 Make 薄表、ScriptTests 入口及原有必需 check-fast filters 共 19 项通过,构建零警告、零错误;canonical selftest 通过。这些是本 worker 的执行证据,不冒充独立复审或 PR 准入。

修复终版只重跑一次实际 MPS 完整前缀,复用同一 per-user GPU/verifier 锁并使用独立外部 state;没有另做完整 CPU-only 扫描。UTC 为 `2026-09-08T13:39:56.700277+00:00` 至 `2026-09-08T13:40:04.933080+00:00`,同步 MPS 总计 0.1530874171294272 秒,枚举/比较 6.9315066249109805 秒;命令退出 0,外部 runtime 为 `complete`,无 publication/recording error。重现命令为:

```sh
make -C tools xi-quantization XI_MODE=mps XI_FIRST=1 XI_LAST=1399999 XI_CHUNK=65536 XI_PRECISION=256 XI_DIGITS=40 XI_STATE=/tmp/qgh-xi-quantization-i3-publication-contract XI_REPORT=/Users/auricstudio/trureturing-qgh-boundaries/docs/reports/xi-quantization-0908.md
```

相对 `309ff1c32e2ba45af38856c33059dbc5bbd13b55` 的报告,全部数学输入、尾界、1399999 项覆盖、精确计数、首末见证、控制和 GPU 混淆/差异记录均相同,有序 CSV digest 仍为 `81e77ccc81333be01c37c6fbb3a8168c37386f8293c18131ad45b9f7776e2b60`。变化仅为发布契约/schema、真实新运行的时刻/计时、运行路径和代码来源。报告的 `source_head` 是带未提交修复的该 HEAD,实际运行字节由 manifest 绑定:producer SHA256 `6bd7295216e998874ff2b9f47e7145f4224f0a7547e630d0157a295d10089a1d`,Make SHA256 `360891306af6257eaf4b4def814a9cd0ab73e77b452124277e8fe3ff107a63d4`,共享 writer 仍为第 13 节的 SHA256。新 Markdown 报告 SHA256 为 `cf8220d31dd7f878e0381b50527198868669ad9e485bdead5618597662817806`;旧报告留在上述提交,未把旧计时配给新代码。caller 继续负责 judge/content 分区、复制工程修复、独立复审和 PR 三门;此有界修复不宣称 MERGED、RH 进展或长期研究目标完成。

~~~~~~~~~~~~

### Archived original bytes [50259,50386)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本节落实第 10 节的距离问题,使用已完成实际 GPT PRO 的论证并由实施者逐步核对;产地见第 17 节。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [50588,50634)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 固定素数标签、预算与加权度量⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [52375,52408)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 强化的二次 Jensen 缺口⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [54104,54146)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### Hermite 上包络及全部等号情形⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [57048,57067)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,无新搜索实现⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [58619,58653)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 固定坐标的常数不能丢⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [59809,59842)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
单个边界整数的有界复算⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [59844,59860)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本次只核验 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [60027,60093)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
保存 Python-FLINT 0.8.0 / Arb 256 位的完整可执行计算与⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [60136,60190)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
球比较及包围端点的精确有理比较均认证⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [60659,60708)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 固定支撑损失不等于任意全局损失⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [62760,62797)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 离散对偶比较与来源边界⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [63228,63582)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
caller 提供的两次后续任务 `949095a4-d3a7-4179-b842-f255db211159`、`db06ed96-26f3-47ff-90eb-db97ec4de9d6` 只有载体失败记录(`prompt_delivery_uncertain`;`page.goto Page crashed`),没有数学答案。它们既不证明也不否定优势。本增量未执行所提 GPU 窗口,不把预测当作结果,也不让新搜索依赖缺失结论。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [63584,64220)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; operational leading fragment.

~~~~~~~~~~~~text
主要研究输入是 caller 提供的实际 GPT PRO task `14803801-6a68-4b5a-8a76-f6615d838e88` 的 structured conclusion,完成时间 `2026-09-08T13:17:09.406+00:00`,返回 model `chatgpt-5.5-pro`;该输入没有单独提供 conversation id,不补造。实施 worker 没有打开 oracle transcript 或 opaque log_ref,没有新 oracle 调用。caller 的单点 256 位 Arb 读数是支持证据;本 worker 独立重算同一 5040 输入,结果一致。这里独立指证明核对和计算路径,不表示独立评审或模型族多样性;Codex 为 `repo-prior-exposed`。

文献尽调范围明确如下:实施者于 2026-09-08 读取 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [64406,64436)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
的摘要页及作者元数据⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [64529,64545)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
PRO 自报亲读⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [64660,64750)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本 worker 未独立取得这些正文或核对 DOI,不把转述写成亲验。PRO 另报 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [64822,64889)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
正文获取失败,其一般结果是否覆盖本特例未核实。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [64998,65741)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
本次是 `consensus-rnd:sshx` 的委派 implementation,无新增子席或独立评审判词。C17 允许的 continuation 工作树为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-variance-0908`,封存起点 `0b8b5592d56d601d92db36b5f7ef331ef3ed33f1`;原 803 行前缀逐字节保留。源与报告之外仅由以下 canonical 命令生成新 atom/账目,计数由实施结果信封报告:

```sh
make ingest BASE=0b8b5592d56d601d92db36b5f7ef331ef3ed33f1 SOURCE=arithmetic-boundary-quantization
```

本轮不新建形式根或修改冻结 Lean,不重做既有有限扫描。独立复审、PR 三门和 MERGED 发布由 caller 负责,尚未交付的环节保持 open;有限追加不完成持续研究目标。

~~~~~~~~~~~~

### Archived original bytes [65880,65937)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本次追加日期为 2026-09-09,保留此前 1050 行。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [69965,69999)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
不新建第二个整数优化器,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [70072,70091)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
实施时读取的 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [70280,70320)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
网页仅为经典归属的有限核对,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [79613,79848)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
保存自含程序、完整输入、8 状态/2 可行的清单和执行身份。其 Python-FLINT 0.8.0 / Arb 256 位计算保持原给定包围,以精确有理端点和严格球比较认证下表,不是读取打印近似值作证明。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [80406,80439)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,也不提供新 GPU 搜索方向⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [80444,81751)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
**本次产地及保留义务。** 主输入是 caller 提供的实际 browser-PRO task `84963abe-485a-4093-901b-03acf69dc52e`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,实际返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T15:45:56.133+00:00`。这不同于第 17 节返回 `chatgpt-5.5-pro` 的任务;此前两个失败任务保持失败,不复活。实施者在 caller 已应用的 `consensus-rnd:sshx` 下核对纸面证明和这个固定网格,为 `repo-prior-exposed`,无 sterile-prior、模型族多样性或独立评审批准声明。未打开 opaque primary log_ref 或 oracle transcript;结构化主结论是输入,不是批准票。

本次使用已隔离且清洁复用的 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-dual-0909`,起点 `fa198bc9a4e5da392e3f2a6f826f73f2ea672c3c`。源与报告之外,仅由 `make ingest BASE=fa198bc9a4e5da392e3f2a6f826f73f2ea672c3c SOURCE=arithmetic-boundary-quantization` 生成 atoms/消化条目,全部历史保留。没有 CPU 候选生成、GPU 工作、xi/5040 实验重跑、工具改动、Lean 重建或冻结;无无限覆盖、新颖性或 RH 进展声明。独立复审、git/PR 三门及 MERGED 落地仍由 caller 承担,未合并即 open;本次追加不完成持续目标。

~~~~~~~~~~~~

### Archived original bytes [81888,81974)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本次于 2026-09-09 追加,完整保留 I5 的 1297 行及其中历史 OPEN 陈述。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [90747,90768)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
与本次来源边界⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [92542,93590)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; operational leading fragment.

~~~~~~~~~~~~text
**本次来源与核验限度。** 主输入是 caller 提供的已完成 browser-PRO structured conclusion:task `6f6085dc-6f5a-473f-a229-072469c98c75`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,实际返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T16:20:22.227+00:00`,opaque primary log_ref `qgh0909:k2-dominance:14c8e7b2`。这些是该次调用的来源记录,不是新的模型调用或独立批准票;该 opaque 引用及原始对话均未打开。主输入自报 `external-prior-exposed; sterile-context-unverified`。实施者是 caller 已应用的 `consensus-rnd:sshx` 下的委派 Codex implementation,为 `repo-prior-exposed`,没有新面板、子席、独立模型或 sterile-prior 声明。I5 的源和报告作为实施输入读取,不充作独立评审证据;caller 已有核对也只作支持。

本次纸面审核展开了实际角点计数、内点正性、上端权重、质量为 2 的矩匹配、Hermite 余项符号及等号的双向证明,并将整数情形统一记为 \(m^*,V^*\)。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [93631,93650)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
实施时还读取 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [93727,93837)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
的摘要接口,仅核对以函数值和导数值插值的经典方法归属,没有从摘要取得本定理。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [94022,94741)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; operational leading fragment.

~~~~~~~~~~~~text
工作树仍为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-dual-0909`。本次唯一摄入基线是已终态提交的 I5 `ba80db594e632ae67aad496a3d68bab506769478`;其完整前缀为 1297 行、81750 字节、SHA256 `c112c2a0f0aa190845d05e80b67ad36e784aa894730c3b4d0e5ec017277713d0`。除追加本卷,新 atom 与消化条目只通过以下 canonical 命令生成,所有历史 atoms/条目保留:

```sh
make ingest BASE=ba80db594e632ae67aad496a3d68bab506769478 SOURCE=arithmetic-boundary-quantization
```

本次无 CPU/GPU 候选搜索,不重跑 xi、5040 或人工网格实验,不修改既有报告、数值证据、工具、测试套件、其它理论、形式根或冻结状态。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [94783,94847)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
未将另行进行的 primary follow-up 结论纳入本增量。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [95227,95258)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,也不完成长期研究目标⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [95261,95443)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
I5/I6 组合源的独立复审、CI 三门和 PR MERGED 落地仍由 caller 承担;本次实施不声明这些义务已履行,也不为已解决的二素数比较安排 GPU 搜索。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [95539,95591)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本节是 2026-09-09 的 S12 后续结算,状态为 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [107088,107132)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
被拒绝的 caller 矩公式及正确方向⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [107138,107183)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本任务早先 caller prompt 提出的行矩⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [107237,107329)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,已在任何源实施之前被主数学论证拒绝;它不是本卷已合入定理的撤回⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [110196,110236)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
### 素数平移、尚余区域与来源⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [113101,113217)

Disposition: type / grammar metadata; operational trailing fragment.

~~~~~~~~~~~~text
该人工实数例仍非素数格反例;这里没有重跑其八状态枚举或数值报告,没有新数值实例。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [113490,113538)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
主数学来源、摄入边界与交付义务。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [113540,114057)

Disposition: grammar: archive space before removed operational suffix; operational provenance.

~~~~~~~~~~~~text
 主输入是 caller 提供的完成 structured conclusion:task `e96a5b22-8c16-4bd0-95ce-a06f1cf2413a`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,观测返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T16:42:56.754+00:00`,opaque primary log_ref `qgh0909:lower-corner-all-k:73b2c9e4`。这是同一主数学对话的来源输入,不是独立评审、实施批准或投票。没有打开该 log_ref、原始对话、先前 worker 日志或同轮 peer 输出,没有新 PRO 调用。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [114059,114293)

Disposition: operational leading fragment.

~~~~~~~~~~~~text
本次是 caller 已应用 `consensus-rnd:sshx` 下的 I7 implementation 同载体重试,实施者为 Codex、`repo-prior-exposed`,纸面逐式核对是实施支持证据,不冒称独立复审、上下文无先验或模型多样性。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [114371,114393)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本次写作还读取 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [114563,114641)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
的摘要接口,只核对经典方法归属,未从摘要取得本条件定理,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [114685,116153)

Disposition: operational provenance / implementation / execution / delivery, inactive archive; operational leading fragment.

~~~~~~~~~~~~text
工作树为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-lower-corner-0909`,封存 HEAD 与唯一摄入 BASE 均为 `6fe2f015c1191dca86563a2e1292227af48ce9e0`。追加前实际核对 PR 6488 为 MERGED,merge commit `e03d7817c7d77eb896d5ef5522ab59eb19f297d7`。完整历史前缀为 1547 行、95444 字节、SHA256 `4ac0311a51f086e4ad587f30a73067fca0ebcac222a9499b3ed55af58a9dfaee`,逐字节保留。源之外的新 CAS blob 与 residual-open 条目仅由以下 canonical 命令产生:

```sh
make ingest BASE=6fe2f015c1191dca86563a2e1292227af48ce9e0 SOURCE=arithmetic-boundary-quantization
```

所有历史 CAS/条目及既有报告保留。此前 Q1/T1 advisory 关于约 18 行旧散文未被旧 CAS 切片保留的追溯边界仍在;本增量不修历史源或 producer。本节使用编号项与普通标题,但摄入退出成功本身不证明散文全覆盖:本次实际 emitted claims 的新散文覆盖范围与任何遗漏,由本次实施结果信封逐项报告,不对旧切片作穷尽摄入声明。canonical CAS 的空白/文件末尾格式归 generator 所有,与源 diff 的 whitespace 核验分开报告。

没有 CPU/GPU 候选生成,不重跑 xi、5040 或人工网格,不改工具、测试、其它理论、形式根或冻结状态,不重建 Lean。独立质量复审、CI 三门和 PR MERGED 落地仍由 caller 承担;本实施不宣布这些义务完成。有限的 S12 纸面追加不完成持续研究目标,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [116317,116363)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本节是 2026-09-09 的 S13 追加,状态为 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [116530,116551)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
独立数学批准、⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [119183,119241)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
本例为已给的单个人工见证,没有候选搜索。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [120743,120837)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
给定的 Python-FLINT 0.8.0 / Arb 256 位程序,以精确有理输入和严格球比较认证⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [120963,121101)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
 完整保留所供 2512 字节程序、1840 字节 JSON 证书、全部八项分类及其摘要、原始程序身份和可复现命令。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [121175,121438)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
该报告还分列 primary 的 \(2^{-384}\) 有理包围及其自报算法身份,不把两份支持计算当成两张独立评审票。本次实施只执行这一既给程序一次并核对输出;没有生成新网格、枚举素数或重跑第 21 节旧报告。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [126377,126403)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
及 caller 核对的来源⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [126753,126785)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
Caller 独立下载并核对了 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [126876,126877)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [126918,127200)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
PDF SHA256 为 `d3b6011255c49e52b002e08faebb7d252ca1027e545b72fa097176e6285443a2`。这是 caller-checked 书目、区间方向及实数全称量词的 provenance,不声称这就是先前 primary invocation 所访问的 author-uploaded URL。本增量没有复核完整筛法证明,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [128681,128706)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
,没有执行素数采样⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [131675,131694)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
caller 曾丢弃的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [135050,135094)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
已由后续实际 PRO 更正的抵消引理⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [135792,135923)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
这一公式采用 recovered primary payload 的 `K_correction`,更正先前纯文本歧义;恢复载体不构成独立评审票。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [139135,141822)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
**25.17 主来源、支持证据与恢复身份。** 本次只消费 caller 所供完成输入的 conclusion 及完成元数据,未追随任何 `log_ref`,未打开 worker 日志或另一 S12 worktree。两次主数学任务均来自 `company-chatgpt-pro` browser Work,pool ID `61e1f52e-a625-4e08-b426-43e25bbab449`,完成记录观测模型均为 `GPT-6 Astra`,不是按产品名猜测模型:

- 仿射障碍 task `c9caf71c-5b42-4d07-8de0-98540288eb7e`,conversation `conv_515ce9ddd365db68`,完成 `2026-09-08T17:49:38.119+00:00`。Envelope `pro-prime-bridge-retry-envelope-0909.json` SHA256 `1c8f5ae65d521ad567538a39a9623fcbbcdd6816f814307492682adada7cb515`;完成记录 `pro-prime-bridge-retry-complete-0909.json` SHA256 `862db73918aef78c101bd35ded76006783fa378d8cb53f483f5fad206ce554d9`。
- 变形素数族 task `69b53236-d65f-4a22-92d4-fae3fd47b58f`,同 conversation 的 follow-up,完成 `2026-09-08T18:14:16.718+00:00`。Envelope `pro-short-interval-primes-envelope-0909.json` SHA256 `5ee071939adcc75ee407f20cc254b4c4002941e9aeb032169bf5a3990097f9f3`;完成记录 `pro-short-interval-primes-complete-0909.json` SHA256 `1e0da2ce725a0ae90f6f507d9b70eea21a0bb1691ed66094246f1f462f41dbf7`。
- 两完成记录的 response 分别与给定 envelope 解析为相同对象。它们是 primary research 输入,不是相互独立的 review。原任务自报仿射论证核对一网格八角点、14 条固定有理不等式;短区间任务自报五项符号恒等式,零素数样本,这些自报与本次实际执行分列。
- `caller-short-interval-audit-0909.json` SHA256 `8fe87b0f14e0997aec9a8f52b2c07060cd277e9f0403ab7f7ea1744d14d22c02` 记录 caller 用 SymPy 1.14.0 核对 11 条精确恒等式、exit 0、零素数样本,是支持证据而非独立批准。其旧 notation-gap 字段由下项后续 correction 解决。
- `pro-prime-gpu-batch-recovered-input-0909.json` SHA256 `4bdcc8bae0a09e9303d968038f5f256055db717101270f3791755fcbfaff6252` 的 `K_correction` 是本节唯一采用的后续数学更正。`caller-prime-payload-recovery-0909.json` SHA256 `dc315e7fa8ff3d7a0e38754f09b10c3fffeb1bf10d46a1f536404f8d8a528f4f` 记录原 reply 需六处 JSON 反斜杠插入、caller 核对忠实身份及全部原 conclusion 字段保留;该恢复不是替代主数学或独立 review,不为其另造 invocation/model 身份。
- `caller-bhp-source-check-0909.json` SHA256 `9ce134f11bd5d7fae613893f0b8706bf07e68cbd019c828efe80563e9d392ba1` 是 25.8 所用来源核对。以上 basename 均指 caller 的 `/tmp/qgh-boundaries-0908/` 完成输入;其所含路径只是 provenance,不作为追读日志的指令。整数比程序及证书则已完整保存于本节链接的持久报告。

~~~~~~~~~~~~

### Archived original bytes [141830,141860)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
摄入范围与交付边界。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [141863,142085)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
实施是 caller 已编排 `consensus-rnd:sshx` 的 I8 implementation,由 Codex 逐式审计和追加,`repo-prior-exposed`;无子 worker、无同轮独立评审票,不声称 sterile priors 或已证明模型族多样性。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [142238,142318)

Disposition: mixed passage: preserve listed exact mathematical / citation fragments.

~~~~~~~~~~~~text
独立数学复审、普通 CI 三门及 MERGED 仍是 caller 的后续义务。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [142320,144030)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
本树 `/Users/auricstudio/trureturing-qgh-prime-obstructions`,分支 `lane/math/quantized-gh-prime-obstructions-0909`,封存 HEAD 和唯一摄入 BASE 均为 `c6bf5faaf36deb301317ef393195be039e410656`。追加前完整源为 1932 行、116207 字节、SHA256 `47c5027509e1641f3cbedff7dd2c8b5fe4c660c78931e06dbcc1f8d2c74ac8d6`,逐字节保留。唯一 CAS/条目写者为

```sh
make ingest BASE=c6bf5faaf36deb301317ef393195be039e410656 SOURCE=arithmetic-boundary-quantization
```

本次实际新增 blob/entry、编号证明覆盖及格式例外在 implementation envelope 中报告;成功 exit 本身不证明散文覆盖。新命题只进入 residual-open,不代表 Lean 吸收或数学冻结。历史 Q1/T1 关于 18 行旧散文位于旧 CAS 之外的 advisory 继续披露,本次不修历史。canonical generator 所有的 LF/空白 EOF 变体与源 diff 的 whitespace 检查分列。

只增加本节、一个既有 `docs/reports/**` 约定下的给定见证报告及 canonical 摄入结果,保留全部历史 CAS/entry/report。不采用恢复 GPU 设计的 manifest 或歧义尾项,不修它们、不实现 kernel、不把设计计数称为执行计数;另一个仍在运行的全实数薄层有限归约 PRO 任务不在本节输入中。没有 CPU/GPU 候选生成、素数枚举、固定 xi 重放、Lean 重建、harness 或 workflow 改动,没有 commit/push/PR 操作。按 caller 最新交付上下文,S12 PR #6640 有三份 approve 但仍 OPEN,其外部 harness 修复 #6644 已 MERGED;这些是 caller 所供状态,不是本 worker 新取的 GitHub 读数。C22 只允许此隔离树提前实施,S12 MERGED 仍是 S13 delivery 依赖。有限的纸面追加不完成长期研究目标。

~~~~~~~~~~~~

### Archived original bytes [144115,144157)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
本节为 2026-09-09 的 S14 参考输入,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [144199,144353)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
两次已完成的实际 GPT PRO 主推导依次给出有限归约及其活跃切换点精化;它们是顺序 primary 输入,不是独立 review 共识。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [144484,144530)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
第 1-25 节的源字节和既有结算保留;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [153883,153901)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
第一主推导的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [154669,154684)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
第一主推导⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [162332,162359)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
常量角点次序证书。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [162362,162382)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
PRO 选定的前瞻 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [162514,162547)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
此处为槽布局将坐标改标⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [163254,163475)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
是给定输入的原样 6741 字节,SHA256
9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672。
它保存每个 triple、八个 mask 和严格递增的整数乘积,是常量输入证书而非搜索结果;
~~~~~~~~~~~~

### Archived original bytes [163558,163610)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
给出逐行可复现的标准库 Python 检查。

~~~~~~~~~~~~

### Archived original bytes [163618,163654)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
前瞻箱体、槽和稳定行号。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [164411,164478)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
批次、压缩和调度必须保留此含箱体身份的行号。
~~~~~~~~~~~~

### Archived original bytes [164759,164900)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次常量检查只遍历 56 个输入行,没有生成上述 229376 个指数箱体,
也没有执行这些 row_id 的解析差值计算。
~~~~~~~~~~~~

### Archived original bytes [164909,164953)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
guards 的整数位宽与 carry 设计界。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [165313,165325)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
前瞻表示⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [165354,165389)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
每 limb 放在 32 位整数 lane,
~~~~~~~~~~~~

### Archived original bytes [165746,165971)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
这是整数表示的数学设计界,不是已验证的 MPS 指令、存储或 carry 行为。
常量证书检查可精确核对 \(19^{102}\) 的 bit_length 为 434,
该更小实测位数不改变预留 64 limbs 的设计。
~~~~~~~~~~~~

### Archived original bytes [169931,169961)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
截断之外的数值义务。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [170013,170482)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
未来实际 MPS 程序还须给出向外误差包围,或由 CPU 对已完成 GPU 输出作严格验证,
涵盖输入 \(\log p_i\)、角点和反射预算、\(a,\mu,\ell\);
距离中的 min/max、减法、平方和、平方根及 \(L,H\);
混合 fraction、0/1 clipping、六排列最大值;
乘除、消去、求和次序、reduction、融合运算和实际 roundoff;
下溢、subnormal 或 flush-to-zero 丢项;以及实际 log、exp、log1p 和平方根的误差。
~~~~~~~~~~~~

### Archived original bytes [170632,171282)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
直接算 \(e^{\ell-nz}\) 可避免先形成大 \(e^\ell\) 因子,仍须包围下溢与抵消。

每个原始 row_id 将来都须保留 active/inactive 及精确 guard 证据,
每个 active 行须有认证分类或 unresolved,完整结论还须验证 GPU 非候选和所有必要排除,
保留 GPU/CPU 分歧及完整分类摘要。CPU 可以认证已完成的 GPU 结果,
不能变成持续指数箱体候选生成器或 GPU 计算的 fallback kernel。
同一批次的域、输入/程序身份、范围、计数、未决项和复现命令必须随程序持久化;
运行 checkpoint 留在仓外。这里没有实现或执行这些数值步骤。

~~~~~~~~~~~~

### Archived original bytes [171290,171326)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
经典材料归属及核对范围。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [172326,172355)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
caller 核对位置分别为 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [172446,172501)

Disposition: operational trailing fragment.

~~~~~~~~~~~~text
I9 读取的是获准的核对 receipt 及文字摘录,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [172502,174146)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
没有把 primary 无法访问仓库 URL 改写成已独立读 GitHub。

**26.29 当前调用的不可变来源事实。** 第一 primary task 为
ce312694-86a6-4a1b-8318-90c77dc28f75,conversation conv_264064eff69b5335,
实际完成模型 GPT-6 Astra,完成于 2026-09-09T13:25:33.673+00:00;
其 pro-real-slab-reduction-envelope-0909.json 的 SHA256 为
5f551e3062515163f220d7fce433908598f5147c5060d92e56ba1292e03ec77a。
第二 primary task 为 3609e6b0-ab4d-4891-9b0f-55c613d43942,
conversation conv_4c0b62a5e14b0f64,实际完成模型 GPT-6 Astra,
完成于 2026-09-09T13:47:33.577+00:00;
其 pro-real-slab-sharpening-envelope-0909.json 的 SHA256 为
8105875c946f2c693c8db6a6b1f789756aab75fbd4cd297293431f08f25dcc92。
两份完成记录分别绑定这些 envelope 身份;两次调用都未成功获取钉版仓库 URL,
使用完整的供给定义,caller 已将定义与交付源核对。
这两份顺序主输入不构成两票独立批准,也不证明模型族多样性或 sterile priors。

本实施为 caller 的 consensus-rnd:sshx 编排下的 Codex CLI I9,
repo-prior-exposed;未产生子 agent、额外 oracle 或独立 review 票。
只消费给定 conclusion、完成元数据及列明的 caller 数学/文献/常量/gate 输入,
不追读 log_ref、不消费 peer review 工件。
上述输入位于 caller 的 /tmp/qgh-boundaries-0908/;其完整字节身份见设计报告和实施信封。
较早恢复但 hash 不匹配的 GPU manifest 是历史,不属于本节输入。
本节用明确乘法核对 \(7+6\cdot3=25\)、
\(6\cdot2^{-23}/25=3/104857600\)、\(255\cdot19+18=4863\),
没有采用 primary 中压缩的乘法串。

~~~~~~~~~~~~

### Archived original bytes [174154,174193)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
摄入、派发事实和剩余义务。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [174195,174214)

Disposition: grammar: archive space before removed operational suffix; operational provenance.

~~~~~~~~~~~~text
 本次指定树为⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [174215,175606)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
/Users/auricstudio/trureturing-qgh-variance,分支
lane/math/quantized-gh-real-slabs-0909,封存输入和 canonical ingest BASE 为
0ba660de65b4224b8734908f7d0dd178115fa377。
追加前源为 2410 行、144029 字节,SHA256
b9898b7df94a1d46bb2898a738b27f927b6136ea1eb7db240fafc428f84bbe36,
Git blob 41c4487989f5739f80e4098cd91a8b229f870891;完整前缀逐字节保留。
新增源段、常量输入文件和设计报告之外,只由下列 canonical 命令产生 CAS/消化条目:

~~~sh
make ingest BASE=0ba660de65b4224b8734908f7d0dd178115fa377 SOURCE=arithmetic-boundary-quantization
~~~

新条目属于参考输入的 residual-open,不表示 Lean 吸收或冻结。
本节每个实质内容单元均编号;新增 CAS/entry 身份、源覆盖和实际命令退出码
由本次 implementation envelope 给出。旧 18 行散文覆盖 advisory 及 generator 所有的
LF/EOF 变体均是历史,本次不重写、不手工规范化。
caller gate 所给派发事实为 S12 PR #6640 已 MERGED,
S13 的 sealed prefix 在派发时独立评审 pending;这里保留它的全部源字节,
不读取或改动其活跃评审工作树。这是此调用的 provenance,不改写第 25 节当时的状态记录。

本次执行的有界输入核验只有 56 个常量行及计数/位宽/carry/尾常数,
指数箱体执行数为 0、解析测试行执行数为 0,没有候选实验或 exponent sweep。
~~~~~~~~~~~~

### Archived original bytes [175687,176108)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
下一数值义务是按另行登记的 MPS 窗口实现并认证所有必要分类,
本节不声称已有 GPU kernel、GPU 搜索、持续 CPU 候选生成、一般域符号结论、
新 formal root、axiom 或 Lean freeze。
S14 的独立数学评审、普通仓库门与 MERGED 尚属 caller 后续义务,
最终交付依赖 S13 MERGED;Git/PR 动作不属于 I9。
这次有限源追加不完成持续研究目标。

~~~~~~~~~~~~

### Archived original bytes [176184,176223)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本次命题、来源和追加边界。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [176226,176496)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本节为 2026-09-09 的 S16 参考输入,
分类为 PAPER_ARGUMENT / repo-derived,承接已完成的实际 GPT PRO primary
task a9d1269e-64ae-4a9a-b90f-8982ff023ee6,conversation conv_224b6f5d1adc6409,
观测模型 GPT-6 Astra,完成于 2026-09-09T14:39:45.418+00:00。
~~~~~~~~~~~~

### Archived original bytes [176994,177500)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
本次 implementation-input HEAD / ingestion BASE 是
391f7355698085c6500b46838a093dad05947ffb,不是尚待 caller 形成的 review-candidate HEAD。
第 1-26 节的完整 176107 字节 / 3134 行前缀保持不变,SHA256 为
4bbc7e0bbcd387c52a73d362ab78b61d00faf810d45d58df98b426e6fc34a266。
既有 atoms、entries、报告和常量表均保留。独立评审、仓库门与 MERGED 尚未由本节取得;
最终 S16 交付还依赖 S14 MERGED。本节不含另行在研的 relative-spread PRO 问题。

~~~~~~~~~~~~

### Archived original bytes [192948,193045)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
这是抽屉原理的纸面构造,没有生成、搜索或数值评价其中任何一列箱体。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [193654,193688)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
,更没有完成长期研究目标⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [193692,193765)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
另行在研的相对展宽问题没有进入本节的证明或结论。
~~~~~~~~~~~~

### Archived original bytes [193774,193825)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
前瞻整箱过滤与第一处压缩记号订正。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [193827,193870)

Disposition: grammar: archive space before removed operational suffix; operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
 以下仅是未来设计的数学依据。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [193871,193898)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
对每箱可先精确构造⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [194099,194229)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
若比较失败或未决,箱体留给既有 eligibility
和符号程序,不得从浮点对数的近似次序直接宣布排除。
~~~~~~~~~~~~

### Archived original bytes [194435,194456)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
primary 的压缩串 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [194974,195025)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
前瞻有限容量与第二处压缩记号订正。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [195031,195046)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
另行预登记⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [195577,195592)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
未来逐内积⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [195770,195798)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
primary 的 `255255+255+255`⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [196121,196416)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
比较可从最高 limb 向下进行;完整幂构造、中间乘积、指数计数器、索引和进位传播
仍须在真实实现中证明不越界。溢出、次序未认证或精确比较不可用只能返回 unresolved,
不能排除箱体。这里没有认证任何 MPS 指令或 kernel。
~~~~~~~~~~~~

### Archived original bytes [196425,196482)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
保留第 26 节的稳定 25 槽,不采纳另一排列。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [197099,197117)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
primary 另写的 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [197211,197229)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次只披露为⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [197451,197499)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
条件覆盖的记账语义与本轮零执行。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [197502,197508)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
未来⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [197834,197964)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
证书应绑定素数/指数三元组、带标签的精确坐标次序、guard 比较、定理身份与版本及 raw-ID 范围。
~~~~~~~~~~~~

### Archived original bytes [198053,198059)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
未来⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [198275,198352)

Disposition: type / grammar metadata; operational sentence or fragment.

~~~~~~~~~~~~text
第一类;输入/程序身份和独立精确算术认证仍是实施义务。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [198354,198678)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
本源增量的 searched boxes、executed box guards、executed kernels、numerically evaluated slots、
certified computational exclusions 均为 0,没有实施 pruning,没有修改任何 kernel。
固定代数和整数恒等式的 CPU 验算只支撑正文记号,不是候选生成、指数箱搜索或旧结果重放。

~~~~~~~~~~~~

### Archived original bytes [198686,198722)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
经典材料与历史访问限制。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [199343,199961)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
caller 已检查这些书页,所供 PDF 为 6881335 字节,SHA256
40d976c83c18cce1900eff8c41bd5ad408c102b813af39d05ff85678ccf8d76e。
I11 读取所供核对材料、对应文字摘录,并核对 PDF 身份。
primary 当时无法读取所给 immutable raw URL 和 GitHub blob URL,因此没有独立检查仓库全文或其身份;
它使用请求提供的定义。这一历史限制不因 caller 后来的源核对或 I11 的本地前缀核对而抹去。
primary、caller 的有界数学核验与 I11 实施自查是不同职责,不组成三票独立 review。
本轮 provenance 和可复现的固定恒等式验算见
~~~~~~~~~~~~

### Archived original bytes [200053,201530)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text

**27.20 本次 canonical 摄入及状态。** 本实施为 caller 的 consensus-rnd:sshx 编排下
Codex CLI I11,flight qgh0909-i11-separation-append,attempt 1,retry budget 1;
工作树为 /Users/auricstudio/trureturing-qgh-separation,分支
lane/math/quantized-gh-separation-0909。实施者 repo-prior-exposed,
primary external-prior-exposed;不声称 sterile priors 或模型族多样性。
本轮没有子 worker、新 oracle、同轮 review 输入、worker 日志或 opaque log_ref 内容读取,
没有邻近活跃工作树或 caller 会话发现。仅依指定参考源与显式供给材料执行本增量。
源文和一个新报告之外的新增 CAS/entry 仅由
~~~sh
make ingest BASE=391f7355698085c6500b46838a093dad05947ffb SOURCE=arithmetic-boundary-quantization
~~~
产生,不手编或重命名 generated 文件。实际路径为 Meta/Digestion/atoms/sha256
与 Meta/Digestion/backfill;schema 使用 fingerprints/cas_ref/coverage_gids,没有 body atom_id。
新条目保持 residual-open,不表示证明已被 Lean 吸收。generator 若产生历史 LF 变体则原样保留,
不重放历史 atom、不作全仓 harness/Lean 构建。每个新实质单元在本节中编号,
新 canonical 源跨度覆盖、文件身份和命令退出码由本次 implementation envelope 记录。
Git 暂存、提交、push、PR、merge 和后续独立评审均归 caller;本节没有代行这些动作,
也没有把有效实施信封当作独立评审或长期目标完成。

~~~~~~~~~~~~

### Archived original bytes [201612,201642)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本层命题与证据身份。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [201645,201860)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本节是 C33 / S17 的 PAPER_ARGUMENT / repo-derived
参考输入,主数学输入为实际 GPT PRO task aaaf57ba-7b72-4143-b830-b4b58fe7fc2c,
conversation conv_576df749336210e9,该调用观测模型 GPT-6 Astra。
~~~~~~~~~~~~

### Archived original bytes [202407,203008)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
本节只用已完成的 relative-spread primary、其 caller 固定核验和本树封存的先行源文。
后续 common-height 与 balanced-all-slab primaries 不是本层输入。
第 1-27 节的 201529 字节 / 3627 行前缀原样保留,SHA256 为
b7cb35d87d0a7b7e569c49ab57f2b556c454257de8bd65899587d13be1338537;
implementation BASE 为 feb497ec31f68e09ccc547a08810c398e66f3ee6。
原始 primary payload 的 SHA256 为
7d0bddfc1fcf761290f7bf777663f52f07af927eb2832001a67ff509bdeb4f11。
其两处转义的非负整数记号在本节排作通常的 \(\mathbb Z_{\ge0}\),原始 payload 不改。

~~~~~~~~~~~~

### Archived original bytes [204624,204655)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
保留 primary 的常数,其中⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [204665,204686)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
原 payload 所记的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [206168,206187)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
这与 primary 从 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [213634,213669)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
,也不需要运行其 25 槽设计⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [216677,216788)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
primary 已纠正 caller 早先把被排除符号写成 \(G<0\) 的措辞;
这里不沿用那个反向表述。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [221018,221049)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
,本轮没有执行指数枚举⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [221482,221489)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
控制;⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [221490,221577)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
后续独立研究即使完成,也须作为另层输入,不能被本节提前引用。
~~~~~~~~~~~~

### Archived original bytes [221586,221625)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
经典归属与已完成固定核验。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [221628,221652)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
primary 已读并引用 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [221896,221959)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
第 27.19 节已保存 caller 的书页与 PDF 身份核对。
~~~~~~~~~~~~

### Archived original bytes [222229,222808)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
caller 的既有审计为 caller-relative-prime-spread-audit-0909.json,
SHA256 493e5f8d2432469936611f95c5d34a42ea5463bb1b29188e827b135ac14b4c47:
SymPy 1.14.0,11 项固定符号恒等式已通过,所供 host session 11977 退出 0。
这些既有核验按其原身份保留,不作为本轮重新运行的 11 个结果,
更不作为独立评审或历史数值搜索的重放许可。
本轮 CPU 仅做源文/身份/生成覆盖验证及普通编排;搜索计数和 GPU dispatch 均为 0。
完整输入限制、11 项名称、核验出处和剩余交付义务见唯一新增报告
~~~~~~~~~~~~

### Archived original bytes [222900,224857)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text

**28.19 实施、canonical 摄入与尚待交付。** 本层为 caller 的 consensus-rnd:sshx
编排下 Codex CLI I12 实施,flight qgh0910-i12-relative-spread,attempt 1,
工作树 /Users/auricstudio/trureturing-qgh-variance,分支
lane/math/quantized-gh-relative-spread-0910。
实施者继承 repo-prior-exposed 的 CLAUDE.md / agents/CONTEXT.md 及完整所供 GoalArtifact;
primary 自报 external-prior-exposed,账户/项目先验未知且不可控。
不声称先验无污染或模型族多样性。primary 当时读取 pinned 仓库 URL 遇到 DisabledError,
故其仓库全文忠实性未获独立检查;此历史访问限制不会被本次本地核对抹去。

本层源文之外只加一份纸面核验/provenance 报告。全部新增 CAS 与条目仅由
~~~sh
make ingest BASE=feb497ec31f68e09ccc547a08810c398e66f3ee6 SOURCE=arithmetic-boundary-quantization
~~~
产生;旧 CAS/entry/report 保留,生成字节及生成器拥有的 EOF 空行不手修。
源文是 paper reference input,CAS 是该输入的 canonical 摄入物,
覆盖源跨度不表示其命题已由 Lean 吸收。条目的 receipts.chain_atoms 及嵌套子项
按实际 schema 读取,不用删字段来迎合临时检查。
本轮没有工具、Lean、source registry、策略或 GPU kernel 改动,
没有候选生成、旧 fixed-xi 重放、子 worker、peer review 或 worker log_ref 内容读取。
canonical 工具的实际退出码、生成身份及每个新编号单元的跨度覆盖由实施信封记录;
工具若失败须显式交回,不能手工制造通过。

源实现候选仍需 caller 在实施 terminal 后封存,再安排独立源文评审、普通仓库门和 PR。
最终 S17 MERGED 依赖 S16 MERGED;本实施不判定前驱实时 review 状态。
Git 暂存、提交、push、PR 和 merge 都归 caller,不由 I12 执行。
本节交回候选不等于独立评审、正式交付、长期研究目标完成或允许立即用作已准入剪枝规则。

~~~~~~~~~~~~

### Archived original bytes [224933,224963)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本层范围与已有前置。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [224966,225125)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本节为 C38 / S18 的 PAPER_ARGUMENT / repo-derived
参考输入,主数学输入是已完成的 common-height primary
fd06c983-162f-4f98-adab-2049d31a9f8d。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [247454,247520)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
没有执行该构造、产生指数候选、计算数值见证或⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [247539,247543)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
。
~~~~~~~~~~~~

### Archived original bytes [249349,249408)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本节不运行它,不修改稳定行号或实现剪枝。
~~~~~~~~~~~~

### Archived original bytes [249488,249493)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
OPEN,⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [249494,249534)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本结果不完成长期研究目标。
~~~~~~~~~~~~

### Archived original bytes [249543,249600)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
经典出处、重叠核对与 primary 的历史限制。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [249821,249843)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本次另实际取回 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [250345,250544)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
三个限定站点的 Google 查询仅返回跳转页,DLMF 的完整 4.6 页面请求为 HTTP 403;
成功取回的公式与两个条目、实际查询和内容身份均记录于本层唯一报告。
~~~~~~~~~~~~

### Archived original bytes [250618,251274)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
primary 自报请求 pinned source 时遇 DisabledError,未独立看到其字节、SHA256、25.7 或
26 节全文,把先行源前提标为 ASSUMED-UNVERIFIED;它对原创性未作评定。
这些是该次 primary 的历史访问/新颖性限制,不会因本次读取本树旧源而变成
“primary 当时已经核查”。本次亲读 25.7、26.2-26.4、26.10-26.17、26.23-26.25、
27.2-27.5 的相关条款、27.11-27.14、28.14-28.19 等先行文本,区分准确重叠与新增组合。
本节专门推导的当前归属为 repo-derived,不以历史的“未评定”充当现行 provenance 状态,
不声称穷尽文献检索或文献中无先例。

~~~~~~~~~~~~

### Archived original bytes [251705,251804)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
这里仅追加源文澄清,不修改 27.14,不新增定理,也不重开已结算的 S16 review。
~~~~~~~~~~~~

### Archived original bytes [251805,254299)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
**29.22 本层产地、固定核验与 canonical 摄入。** 本实施为 caller 的
consensus-rnd:sshx 1.0.0-beta.42 编排下 I13,flight qgh0910-i13-common-height,
attempt 1,工作树 /Users/auricstudio/trureturing-qgh-common-height,
分支 lane/math/quantized-gh-common-height-0910,immutable BASE
66001d3b87d7063c5dd2a4ea97e51f8f1b876afa。
实施者为 Codex CLI,继承完整所供 GoalArtifact 及 repo-prior-exposed 的仓库规范;
没有子 worker 或同轮独立 review 票。primary 自报 external-prior-exposed,
账户/项目上下文未知且不可控,其具体 serving-model/routing 未独立确认;
本层不从 ACTUAL GPT PRO 的 caller 标签推断模型版本或模型族多样性。

主 envelope 为 pro-common-height-envelope-0910.json,SHA256
7bba088ffbdf3ae327aa0bbf34c17905e90a7510252a0e3f699ba28a27d6eda7,
只消费 conclusion,所有 log_ref 保持不透明。
caller-common-height-audit-0910.json 是已完成先行审计,
记载 21 项成功固定精确核验、完整纸面审计及原 host exit 0,不是本轮 peer review。
本层仅将同一 21 项算式适配成报告内自足固定证明证书并运行,
原审计和原一次性程序字节不变;程序、实际结果和输入身份见
[common-height-finite-mixtures-0910.md](../../reports/common-height-finite-mixtures-0910.md)。
该证书不接受候选参数,不是可复用搜索器。CPU 仅用于固定核验、源和引用一致性;
没有指数、高度、形状、素数或薄层候选生成,没有 GPU、daemon 或旧搜索重放。

本节前的完整 224856 字节 / 4141 行源前缀保持不变,SHA256
69702718f3602c508146f50cf70ebd78ef81adb09c2b826041d357e4a7dc11c8。
所有历史 CAS、entry 和报告保留。源追加后唯一摄入门为
~~~sh
make ingest BASE=66001d3b87d7063c5dd2a4ea97e51f8f1b876afa SOURCE=arithmetic-boundary-quantization
~~~
全部新增 CAS/entry 仅由该命令生成,包括可能出现的历史末单元 terminal-LF 变体和
自动 chain children;生成字节及其 EOF 空行不手修。摄入只提供源文内容地址,
不表示数学被 Lean 吸收。本层源实现和独立源评审可在隔离树中推进,
由 caller 在本次 implementation terminal 后封存、安排评审与普通仓库门;
最终交付依赖 S17 MERGED。Git 暂存、提交、push、PR、merge 均由 caller 所有,
本实施不执行,也不读取另一在飞 target 或同轮 reviewer 工件。
交回本层候选不等于已独立批准、已正式交付或长期目标完成。

~~~~~~~~~~~~

### Archived original bytes [254378,254417)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
本层结果、状态与准确重叠。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [254420,254618)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本节是 C41 / S19 的 PAPER_ARGUMENT / repo-derived
参考输入,只追加已完成的 balanced-all-slabs primary
8cfd404d-43c8-42f9-a5be-22e0811bc05a 及 caller 固定核验所支持的结果。
~~~~~~~~~~~~

### Archived original bytes [264573,264627)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
报告给出不调用浮点对数的可执行核对。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [268476,268573)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
primary 中的压缩乘法串在本节明确解释为 `2^8 * 3^7`,原始 primary 字节不改。
~~~~~~~~~~~~

### Archived original bytes [269198,269210)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
报告中的⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [271087,271245)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
所有算式均在单一报告内给出自足可执行的固定有理核验,不用浮点 exp/log/sqrt,
没有生成高度、矩阶、素数或薄层候选。
~~~~~~~~~~~~

### Archived original bytes [279060,279121)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
这是齐次存在性证明,没有执行指数构造或给出⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [279146,279150)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
。
~~~~~~~~~~~~

### Archived original bytes [280160,280202)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
缩放、形状和研究目标的边界。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [281444,281490)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次源实现不完成持续研究目标。
~~~~~~~~~~~~

### Archived original bytes [281499,281564)

Disposition: type / grammar metadata.

~~~~~~~~~~~~text
当前文献归属、primary 访问限制及固定核验产地。⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [281819,281917)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次亲读本树第 26 节、27.3-27.5、29.1-29.22 和第 10 节度量定义作重叠检查。
~~~~~~~~~~~~

### Archived original bytes [281969,281988)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次实际取得 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [282479,282495)

Disposition: operational fragment in mixed mathematical passage.

~~~~~~~~~~~~text
另实际取回 ⟦end of exact byte span⟧
~~~~~~~~~~~~

### Archived original bytes [282858,282962)

Disposition: operational sentence or fragment.

~~~~~~~~~~~~text
本次另试的 EoM Majorization 页面返回 HTTP 404;检索不构成文献穷尽或优先权判定。
~~~~~~~~~~~~

### Archived original bytes [282963,283922)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text
primary 原始 envelope 的 SHA256 为
5ad15f1f87730e33edd6ef2e9045aa4255a4a85efb1e456312b438da91c5288c。
只消费其中 conclusion,log_ref 保持不透明。它自报 pinned source 获取遇 DisabledError,
未读源字节或独立核对其 SHA256,且没有成功取回外部文献;
本次源/文献读取不改变那些历史事实。原压缩串 `2^83^7` 留在原始输入,
本节只按其数学意图显式写为 `2^8 * 3^7`。
primary 自报 34 项固定有理检查;caller 的原审计另记录总计 64 项成功检查、
host exit 0 及纸面核验,包含那 34 项及额外的分支、eligibility、权重和半径核对。
它们是已完成的先行数学输入,不是本轮同轮 peer review,也不能合称为 primary 跑了 64 项。
本实施把固定算式改成报告内不依赖绝对临时路径的自足证书并实际执行,
原 caller 审计和程序不改。全部输入身份、逐单元映射、当前调用结果及检索收据见
~~~~~~~~~~~~

### Archived original bytes [284029,286339)

Disposition: operational provenance / implementation / execution / delivery, inactive archive.

~~~~~~~~~~~~text

**30.21 单一源/报告/摄入层与交付义务。** 本实施是 caller 提供的
consensus-rnd:sshx 1.0.0-beta.42 runner 合约下的 I14,flight
qgh0910-i14-balanced-all-slabs,attempt 1,实施者为 Codex CLI。
未查阅另一版本的 skill,没有 native subagent、委派、额外 oracle 或本轮独立评审票;
只继承已供 GoalArtifact 与仓库先验,不声称无先验或模型族多样性。
primary 的具体 serving-model/routing 未在本实施独立鉴定,实际 GPT PRO 身份是 caller 的来源记录。
工作树为 /Users/auricstudio/trureturing-qgh-balanced-all-slabs,
分支 lane/math/quantized-gh-balanced-all-slabs-0910,immutable BASE 为
a8e208440d8a3f465a7b20c82ededbb27ee95026。
准备文件旧的 predecessor-in-flight 行只属准备时状态,当前以这个实际封存 S18 base 为准;
没有读取 S18 活跃评审 target、result、任何 worker 日志、log_ref 内容或 caller 转录。

第 1-29 节完整前缀保持 254298 字节、4743 个 LF,SHA256
c5e1fa97fff5921fe5ba10d84b0268c884caab112fb32beed0c92027ee1aa3f5,
每个历史 CAS、entry 和报告均保留。只允许本节、一个报告及下列 canonical 摄入输出:
~~~sh
make ingest BASE=a8e208440d8a3f465a7b20c82ededbb27ee95026 SOURCE=arithmetic-boundary-quantization
~~~
每个新 CAS/YAML、raw/normalized 指纹、源的完整连续跨度和有序 chain children
在实施结论中逐项给出;指纹/cas_ref 带 `sha256:`,子 atom_id 为裸 hash。
生成器拥有的 EOF、历史末单元 terminal-LF 变体和自动 child 均原样保留,
不手修 producer 字节。摄入是参考输入的内容寻址,不是 Lean 吸收或冻结。
CPU 仅运行固定证明证书和必要编排,没有指数、高度、形状、素数或薄层候选生成,
没有 GPU、daemon、旧搜索重放、工具/Lean/frozen 改动或广泛 build/preflight。
源、报告与摄入组成同一可审查的内容层;不能在未保真源语义时单独交付派生地址,
也没有理由把后来定理或新搜索绑入这一层。
caller 在本次 implementation terminal 后负责封存、独立评审和普通仓库门,
最终 S19 交付仍等待 S18 MERGED;本实施不执行暂存、commit、push、PR、merge 或生命周期动作。
候选交回不是独立批准、正式交付或长期研究目标完成。
~~~~~~~~~~~~

## I31 / C89 independent-body migration evidence (2026-09-10)

This is a partial representation of the unchanged C78 goal across all 30 original sections. The exact Gram target remains pending. Whole-body purity, accepted whole-book result, independent approval, delivery/MERGED and continuous-goal completion are all false. No fresh mathematical proof or correction number is adopted. The inactive archive above is historical evidence; its instructions, commands and paths are not live navigation or authority.

### Exact original/current recovery and reservations

Pinned BASE/HEAD: `a8fc797b76637136f9b95392c105d5101b09330e`; branch `lane/math/quantized-gh-pure-s19-0910`. The source changes from 286339 bytes / 5391 LF / SHA256 `59838eb016d5a88043e4f9ca4ffc3c999d85357762d078cf4f05168521ad0d18` to 238272 bytes / 4983 LF / SHA256 `9393b391e41432651264bde9a4e4dfdcb9a9f0eeaa880ab0c4afe502e6967dce`, with one terminal LF in each.

The entire original report is current bytes [0,47922): 47922 bytes / 764 LF / SHA256 `a073280a2a3c4382c89d284e9970e5335a33db78b87e49679f413592caa808ce`. It is preserved byte-exact. Final complete report and mapping identities are recorded in the mapping and runner conclusion respectively, avoiding circular self-hashes.

The protected original source [23492,24745), lines 531–552, remains current source [18988,20241), lines 474–495: 1253 bytes / 22 LF / SHA256 `848cc4f7d0e77de827c99d9c8e77f55a52fb33daa23c769dda1b8ce960ca27c1`. It occurs once, contiguously and byte-exact. Its original full-half-axis distance, weighted synthesis/operator and finite/global PSD/RH targets remain unproved targets, neither proved theorems nor assumptions. Actual PRO C88 output has not been supplied or adopted. Caller must later integrate the full actual proof at fresh addresses, then canonically integrate and review the composed body. No additional mathematical typing dependency was identified; all broader original open questions and conditional limitations remain.

The mapping [theory-body-migration-s19-0910.json](theory-body-migration-s19-0910.json) provides 786 disjoint exhaustive original-source recovery spans, 228 exact archive spans, 291 source type/grammar/citation metadata additions, all 176 original chapter/numbered addresses, all 67 headings and all 213 structural/unnumbered regions. It records whole-span identities and every original/current address, 73 original Markdown citation or short-bibliography occurrences and their rebindings, complete current units, report-prefix recovery and added archive/evidence scaffolding. Concatenating mapped current slices in original-byte order reconstructs every original byte. Byte recovery alone is not mathematical fidelity.

Permanently reserved outside the active body: `9`, `13`, `14`, `25.17`, `26.29`, `27.20`, `28.19`, `29.22`, `30.21`. These original numbers are not reused. Mixed entries retain all mathematical parts at their original numbers. There is one active mathematical body; the report is an inactive historical archive.

### Analytical fidelity inspection through all 30 sections

Full source read, explicit semantic classification of moved fragments, inspection of changed contexts, all displayed formulas checked byte-exact, and independent byte-recovery verification within this implementation. These are implementation self-checks, not an independent review or new mathematical proof.

- Original section 1: GH ambiguity and the working RH interpretation are unchanged; the rounding question remains the negated universal target answered by section 5. Only lane/host/roadmap instructions move.

- Original section 2: The labeled factorization 5040=2^4*3^2*5*7, Zeckendorf reversibility, divisor identities, Robin domain and Nicolas normalization remain with the original proofs and citations.

- Original section 3: All literature-attested criteria retain exact domains, strictness, equality and zero conventions: Robin/Lagarias, Nicolas k>=1, Li and lambda_0, full-half-axis Nyman-Beurling distance and Baez-Duarte coefficients. Retrieval history moves; bibliography remains attached.

- Original section 4: The floor/ceiling equivalences, zero-bin versus true equality distinctions, strict/closed interval decision cases and unresolved equality limits remain exact.

- Original section 5: The all-integer-m five-dimensional unitary counterexample, complete algebra, tie/domain/scale cases and hidden-state obstruction remain. Fixed sampled checks move as historical evidence, without replacing the universal proof.

- Original section 6: Taylor/Li identities, b_1 positivity, completed-xi constant term 1/2, deflated-zeta notation, all strict rational bounds, Sylvester inference and Q_200 negative witness remain. The original executable and library/runtime trust boundary are archived and cited; numerical evidence is not promoted to an analytical or kernel proof.

- Original section 7: All open Schur/history, arithmetic-bridge and global-Li obligations remain mathematical targets. The exact 1253-byte Gram subsection remains unproved and contiguous. Its operator, distance, finite threshold and RH target are neither erased nor adopted. C88 is the outstanding dependent proof; its output is unavailable.

- Original section 8: All L/N/S/B1/B2/R/Q/Z mathematical bibliography labels, titles, URLs, mathematical locators and use limits remain attached to their original uses. Model, browser, ingest and review provenance moves to the inactive archive.

- Original section 9: The entire model-terminal-string and implementation record is archived verbatim; number 9 is permanently reserved outside the body.

- Original section 10: The chosen Euclidean metric, projection/Pythagoras, labeled exponent uniqueness, lattice-versus-slab distinction and existing KL-loss formula remain; coordinate encoding supplies no new orthogonality or sign theorem.

- Original section 11: The complete three-observation Schur geometry, entrywise PSD/PD conditions, exact determinant and negative vector, and universal Schur rounding proof remain, including the m^3 denominator distinction.

- Original section 12: Original strict d=10^40 input bounds, finite [1,1399999] classifications and exact first/last witnesses remain as historical numerical evidence. The analytic m>=1400000 tail, all-resolution conclusion and higher-order/open limitations remain. Hardware, programs, runtime counts and verification records move with a retained mathematical certificate citation.

- Original section 13: The entire operational publication/implementation record is archived verbatim; number 13 is permanently reserved. Its historical numbers and failures remain recoverable.

- Original section 14: The entire engineering review/correction/test/publication history is archived verbatim, including all mathematical test literals and measured failures. Number 14 is permanently reserved; no test or old experiment is replayed.

- Original section 15: All labeled-prime definitions, strengthened Jensen estimate, Hermite envelope proof and every equality/domain case remain with original paper status and classical attribution.

- Original section 16: Finite nonempty exponent sets, closed/strict budget distinctions, variance normalization, positive support and empty-domain alternatives remain; fixed coordinates and h=0,1 cases retain every constant and quantifier.

- Original section 17: The single 5040 interval example retains its exact numbers and numerical status, exclusion from n>5040, distinction between support/global KL loss and still-open general dual comparison. Literature coverage limitations remain; failed carrier facts move.

- Original section 18: The two-point fractional-knapsack definitions, complete matching primal/price proof, ties, saturation and separation from integer optimization remain with attached classical references.

- Original section 19: All three sufficient dominance conditions and proofs remain unchanged in their mathematical content and scope; no sufficient condition becomes necessary.

- Original section 20: The exact remaining fractional-coordinate inequality and its unresolved genuine-prime quantifier remain; no general-prime conclusion is inferred.

- Original section 21: The complete artificial eight-corner table, two feasible points, LP argument and strict Arb bounds remain. It is still an artificial real-grid example, not a prime-lattice or Robin counterexample; its original certificate remains attached.

- Original section 22: The full positive-real k=2 theorem and proof retain arbitrary optimal basic-solution choice, actual-corner counting, inner-support positivity, moment/Hermite comparison, endpoint/equality cases and all domains.

- Original section 23: The different-prime strict corollary retains its complete proof and two-point domain; k>=3 and the broader finite-set comparison remain open. Classical citations stay attached.

- Original section 24: All-dimensional dominance remains conditional on existence of an optimal genuinely fractional solution whose actual lower corner is feasible. Both concentrated-distance proofs, complete equality/positivity cases and the already-rejected wrong moment formula with its correct replacement survive. No fresh correction numbering is adopted; 24.16 retains its mathematical citations/open statement.

- Original section 25: The fixed artificial integer-ratio witness, exact eight-corner table, strict numerical sign, affine-neighborhood obstruction, BHP short-interval theorem with its real quantifier, actual-prime asymptotic construction and complete cancellation correction retain all conditions and proof steps. The old nearest-endpoint and multiplication corrections remain explicit. 25.17 is reserved; 25.18 retains only classical attribution.

- Original section 26: The full all-real-slab finite reduction retains positive support, strict Jensen, saturation equalities, ties, empty domains, maximum attainment, zero existence, upper-tail behavior, exact integer guards and all endpoint cases. Mathematical 56-triple/25-slot/bit-capacity encodings and their proofs remain, as do six mixtures, absolute convergence and the 24-term tail/rounding limitations. Operational schedules and provenance move; 26.29 is reserved; general-prime openness remains.

- Original section 27: The Euclidean monotonicity/equality proof, scalar thresholds and strict threshold equality, k=2 empty premise, ordered-prime guard, positive-integer ray cutoff and escaping unbounded sequence remain. Exact integer representation and stable slot distinctions remain mathematical definitions/proofs. No guard failure supplies a sign or implemented pruning; 27.20 is reserved.

- Original section 28: All remote-coordinate estimates, positive support, exact norm remainder, both resource cases, closed threshold strictness, finite and upper tails, bounded relative spread and nonzero nonnegative ray cutoff remain, including empty strict-5040 domains and unresolved common height. 28.19 is reserved.

- Original section 29: All six fixed mixtures, signed moments, merged-atom Vandermonde identity, first-seven-moment criterion, strict eventual cutoff, degree-six numerator/at-most-36 stationary heights, and exact supremum/attainment distinctions remain. The selected 2,3,5 slab alone has its original neighborhood theorem and homogeneous-lattice existence proof. General-shape/high-order transfer obligations and the already-adopted 27.14 set clarification remain; 29.22 is reserved.

- Original section 30: The entire 2,3,5 all-slab argument remains: wider versus strict original domain, every guard and eight-node table, all-integer-moment comparison, full fixed rational proof steps, uniform scaled margin, common-budget/projection transfer, closed radius 1/480, strict margin 1/120, actual-lattice subsequence and exact strict-5040 nonemptiness. No arbitrary shape/prime/RH claim is added; 30.21 is reserved.


All 532 original displayed formulas, including mathematical arrays, tables and proof chains, are byte-exact contiguous spans of the current source. Mathematical words, domains, quantifiers, constants, strict/equality/endpoints, proof steps and evidence status were inspected across the complete original source, not only by keyword or reconstruction. Labels express existing mathematical types; original numerical evidence stays numerical. Numerical-library execution details move with their original evidence limitations and attached certificate references. The completed-xi constant `1/2` retains an explicit `xi(1+t)` binding after code-variable prose moves.

### Single canonical ingestion and full-unit evidence

Exactly one new source-revision invocation ran after final source editing (I27 had no ingest):

```text
make ingest BASE=a8fc797b76637136f9b95392c105d5101b09330e SOURCE=arithmetic-boundary-quantization
```

Start UTC `2026-09-10T12:35:37.716663+00:00`; end UTC `2026-09-10T12:35:57.030154+00:00`; actual exit **0**. Full stdout:

```text
INGEST residual_open_added=245 skipped_existing=41 coarse_fallbacks=0 open_genres=0 cas_objects_written=245 ledger_changed=true
```

Full stderr: empty (0 bytes). No second ingest and no manual producer or canonical edits.

Actual added output is 245 CAS/YAML pairs (490 files). All 199 complete current source units partition the entire 238272-byte source, including tables, following prose, separators and actual chains: 190 units are new and 9 reuse existing pairs. All new CAS contents are exact current spans, and every raw/normalized fingerprint and cas_ref matches its entire CAS. The 36 new parent YAMLs with actual `receipts.chain_atoms` concatenate to the whole parent. Nested headings stay in their claim; a peer heading ends it. The mapping separately records the actual claim unit and the possibly larger interval to the next numbered entry; chapters compose complete units. No inherited seven-line schema or guessed children field is assumed.

The 329 source-owned historical pairs listed in the allowed I27 view were checked against their exact current bytes and bounded BASE objects, including 22 historical chain parents and every listed terminal-LF variant. Global tracked Git delta has no historical CAS/YAML modification. This is a bounded source-pair comparison plus current delta, not a replay of the historical 64376-object inventory. Index and HEAD remain unchanged.

The complete changed set is the source and report modifications, the named new mapping, and the 490 producer files enumerated below: 493 paths. Final per-path status, bytes/LF/terminal-LF/SHA256 identities are in the runner conclusion/evidence. The mapping also preserves the earlier canonical-audit snapshot explicitly as a pre-finalization snapshot.

For each row, the full CAS path is `Meta/Digestion/atoms/sha256/` + atom ID; the full YAML path is `Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/` + atom ID + `.yaml`. IDs are exact CAS SHA256s. Source intervals are byte offsets [start,end); C denotes the actual number of ordered chain atoms, not a guessed schema. Full parsed YAML and ordered member identities are in the mapping.

| Atom ID / CAS SHA256 | CAS bytes / LF / terminal LF | YAML SHA256 | YAML bytes / LF | Current source intervals | C |
|---|---|---|---|---|---|

| `02eece2071f9332b4f8e747911a68c3f6ee23fe669f6d192e8b3b78d950d8d95` | 50 / 2 / 2 | `ab7016888e73596674b87b205b4d3ac20bb6d84f575db771a22633d7f4f7a6b2` | 328 / 7 | [9069,9119) | 0 |

| `078ad895fc85e84e99df79202d05e55c51a40bfe92a12047cb2228e871fd99b7` | 1474 / 32 / 2 | `f227defae060e3a590da696d080ce87839a0f392683f712d56bcc9cb4e740960` | 328 / 7 | [97968,99442) | 0 |

| `080da3972513ef560c0a1ee6df3e5e1e1f2962f934d7d1ea08da6606e9bbb297` | 462 / 6 / 2 | `81b9de6421b168e5661d3937e726631e30f325444a6cb1a373ebd7ed0a103bae` | 328 / 7 | [209184,209646) | 0 |

| `09269a3e3de7ccaded99d8451eba6c9f1d9d595587b8ee8956a0e2f6b577e126` | 2012 / 52 / 2 | `a1f10031b0417c2b50b9cfb60d7448883f15a0dbec4bdb6eb404822cbb964d9a` | 328 / 7 | [222135,224147) | 0 |

| `0a169a4a8d6b44d6234405400b6be9fe79c6950251e95a762310d5e316a4aecb` | 1377 / 27 / 2 | `5cf986b4b049983156c2dc9dbc5a2e91a7fa32c31f32ae24eff17b7055e4384a` | 485 / 10 | [151414,152791) | 2 |

| `0c4d770f00fc19ec7a548f4997671fefd4fb685b0251496e85b7453f6b5b4c52` | 835 / 17 / 2 | `c9e9fe1aabfb6b7bc6d1c26f79d89b4060586c74031dc20f69278fe63f6401e2` | 328 / 7 | [123567,124402) | 0 |

| `108f84ef6f9d7e2f6926d68048236e1e22938acfac865fb13e67304cf1fc638f` | 1112 / 24 / 2 | `55cdac74c1b67025a8ed3b2f40cda43cd7d4c65aa95edfc31fecf36e8969a7c2` | 328 / 7 | [85696,86808) | 0 |

| `121fe7e92a5e113fac6ca3f6521c1d8a26c761baede301f93fda3c890ec7b08d` | 884 / 24 / 2 | `a4d8250a493c28049f30bb85ef89d54b8d5b5caceaea46e5cf89ac6a4b7e7010` | 328 / 7 | [124402,125286) | 0 |

| `12a7456bcdfae7970230281864ecada698bdddc0979a8557aacd5b8aba51d82a` | 1141 / 17 / 2 | `26fe1079098d2d8684c53a1d008e22c534305e938e912df039a05927f6019bb6` | 485 / 10 | [4183,5324) | 2 |

| `139e7e00c6277ecdadd74711f90115062b5a6cc59f730386d95ff489206f64cf` | 697 / 8 / 2 | `f08ad46194a3b30b078eaf758966b3fff075022256278eaaab223d29d949bc1d` | 556 / 11 | [14333,15030) | 3 |

| `15255179943fc1b00df9c13c2a1eaa6b0e687d511aaf8e357a00db63707bdd15` | 1015 / 21 / 2 | `88cfc8f882fe9ee1e2cff09cc728a03b10df22fcf633dd900dcb44f2558db2ad` | 328 / 7 | [158170,159185) | 0 |

| `15b706e8b8baf25929119e0e671acb1ccb97664afa08793ef81ef53820275a8d` | 942 / 26 / 2 | `629778d6d72125dba383943034db615657430b117bbd275763e3fa2197c24402` | 328 / 7 | [104275,105217) | 0 |

| `168e8a474e78bafc7fd72cd938ac995adcad5f0f8a3342c25dfdcfa6f3a95e7d` | 5799 / 104 / 2 | `f3314992fff47b42211d098fb71013276d09534c5df5b184c301596f506f68ad` | 1124 / 19 | [49712,55511) | 11 |

| `190b220b0b6d62e63496a308876126eb2d4431dfa1bbc39705565a5c40d87da4` | 1406 / 33 / 2 | `238b04ae9b94ec4a8ac18461935d834f6ad8140925fbc6759d4142e0e6fe06a5` | 328 / 7 | [107855,109261) | 0 |

| `19c4504697febcf9a3dc6f9d586de96b5533460f877f90b9689b5f7757d8234a` | 1223 / 26 / 2 | `1be5eaeb5783bc304679db80df3e9c78834933ae2868c1678c03d0e49824bc2e` | 328 / 7 | [188679,189902) | 0 |

| `1a2703254e6926fe6f8da434fe675fe56e2aaf7b24941cbeafd51e0dbfe83760` | 1061 / 31 / 2 | `9ff35d61a86b6f1daea3888d6c3b68c7365984619f50e7b6f4d0bb6144fed8b9` | 328 / 7 | [121539,122600) | 0 |

| `1a5fe71020bfbd4112873a2535c5829ddf36cf2b3fe51f90cc6e65954626fe23` | 2358 / 66 / 2 | `f8a062444ae509c511a2a4b164d536f06980c97ab3595d0725c59441b76f9f1b` | 328 / 7 | [224147,226505) | 0 |

| `1e2ef58bcb3182066413489533f165cb55464521e458a345dac9df38671cfe3e` | 941 / 29 / 2 | `c2bee6e0f93bebe56bdaf76630759b91e639f306fc4f4c69578daacad20b09f1` | 328 / 7 | [84755,85696) | 0 |

| `1f70580349b16ea3fb2ff5ded0c95550dccd5ddcb1d1fe69ec73d4d261a397a1` | 927 / 18 / 2 | `c5374ac60d911ac9064b81939245ca6f24f1333bc214c86e043ba44ca02386a5` | 328 / 7 | [25562,26489) | 0 |

| `2140c881a73102917a7d98789fc34938214f9e3f032bfa9333b0a17909596e00` | 1796 / 38 / 2 | `bf893cc40855afa7e41bf3ac75763f59a2e52dbed5c52a028c5ca6537a6c1bbb` | 328 / 7 | [31549,33345) | 0 |

| `2144b1c3e305ad48a2effa3ebc5f292741c5835b293b318946fa3cf3a7563d4b` | 3214 / 63 / 2 | `665e4eb1f5d5c19fa87e8c0adc7766726e6cd59b4bf0b0eda936f280ca7024c9` | 627 / 12 | [56809,60023) | 4 |

| `2150768d0d1eaac4230a93b181ac0fca48a4c5124d10b92a448f54995b36626d` | 2056 / 29 / 2 | `252149ca7bfe66978a32b483486803dce7058e15f0e66f5a0150925d1574d614` | 328 / 7 | [57967,60023) | 0 |

| `215955f248c978f22d82bb721b7e777b4e5caebd9853c9dc75d7bc92c2163ca5` | 57 / 2 / 2 | `17cf7de718ad467bc11559925e2113c742f9b4d6aa0ecbba265b6a3876fdd245` | 328 / 7 | [767,824) | 0 |

| `2277a0690523b9ef10c8e4e29c0ec29db992c9792ccde9ac3d280031df8842fc` | 987 / 19 / 2 | `0bee510cc0905e1e7499ced1c467598a22ee26f786afdb040527cd70e8560f98` | 328 / 7 | [180259,181246) | 0 |

| `228ed2150eecc4cb74b77a92282e3437c91e838c54f60bbe64244816f1d44cc7` | 1615 / 39 / 2 | `d55ecc37884fd89b9d49de35df14d0b16ed55c496d43ca24a975cb7760e38cdd` | 328 / 7 | [163653,165268) | 0 |

| `22aa76eccac61cdbcea9627b69e84ac118320c199f81e21c744fc504de058a4d` | 1158 / 13 / 1 | `06de7e85e38f4d504518005b8e3203f46d24304ffae3b41457f06bb394fbd06b` | 328 / 7 | [139577,140735) | 0 |

| `23568c1278678820cb38a2d8632719e8b407a79af63e176bdea07d11b4efd65d` | 885 / 23 / 2 | `fb3b614353a2122b15c1c8fd3ef1fe5db807975cbb6e0b0fc87d556ff04311ba` | 328 / 7 | [168848,169733) | 0 |

| `24a4a0501b6d4473bc9c1b4d6bd527dd106e15813eea226cab2a49ec090015d5` | 3247 / 80 / 2 | `28c439a6cea8c8c1dd513f6141946c2e5118192f046788c2327e61d9b64deed4` | 769 / 14 | [11086,14333) | 6 |

| `2551c0986ef0c70fec4af806603e8175baf398f13cb605c98fa40ac5e2069bff` | 1629 / 33 / 2 | `3725cdbd73895bf3f56906dacf32047cc742c3af6f98d14e6707a412cec0dcc0` | 328 / 7 | [191122,192751) | 0 |

| `2b1f8b2853aa9149d8909ea7ed749dec06716b90eb2b834e9e1bee983cc638e7` | 182 / 2 / 2 | `97bed3d6e3432c24072dea406b08a10f27cd2cdfeb3173ad42e862d23e057685` | 328 / 7 | [585,767) | 0 |

| `2b571dd7954d9dbf4660633265e372370d42257b0b918d01b70fc89ee2141693` | 62 / 2 / 2 | `f7d255b4bf0a603fe235fa403940a3dddb87227ab7616adc78562e39588c4161` | 328 / 7 | [35092,35154) | 0 |

| `2bc2d3375d7a3402c4801dab7aae52eabe5cb094784a94c7fd749cea635144ac` | 1296 / 42 / 2 | `1b0e6065ab5dc1093c505681345dd97ac241dd009da50f61ff0b6e3c19420199` | 328 / 7 | [101860,103156) | 0 |

| `2e291aae7a929a7418e1952756fe0429a2a6bcc7c93d3f6addfdc5fedf1abc1c` | 1773 / 29 / 2 | `0f1b3ca2d196a7d669694473b2ac7611e73d437d5532b80af1e03b20d7799f16` | 328 / 7 | [195873,197646) | 0 |

| `2f441300fc6afc73470b75ed5d7199ef9d598b8c57558f5c1c3bae5b570b2303` | 664 / 7 / 2 | `eb7d14a650e1fa5d56ac9250c776f1f685e5aed9f12424e947134b198bfb4d62` | 328 / 7 | [162989,163653) | 0 |

| `2fc4306d5dd4d50ceccef52c1201ea1f2e5ea7f56bab8bc57e9c241b4cd0dae7` | 1003 / 26 / 2 | `18865209b16d8c28bfbb484a4bdbd1a6159eb7a3efb6ad5f7d421cc7c4c65147` | 328 / 7 | [136197,137200) | 0 |

| `2fd666b069c9cb70caa823a99332a676c0f16f40580ad121d6c5b5902cc7712d` | 1024 / 19 / 2 | `721b5fc275f3b7a92fb571819138a46b98bfe961b8209b4c172e98efe942de1a` | 328 / 7 | [177627,178651) | 0 |

| `3459206e69ab5fb27b11a04cbf1def2003943b743ab909d5c6b0e2d6b5e953b4` | 44 / 2 / 2 | `9749057c10095ccf31a508f51229937fc1c50b54ccca844972ed2065e80c13ff` | 328 / 7 | [17369,17413) | 0 |

| `361599c01c984a71fba24506b0d2c214d04ec3817e21b723688e727b524e5f54` | 51 / 2 / 2 | `200099bf0aed085b27c861b4e42796412b52f52cc358fd5c622ef1b09c0984df` | 328 / 7 | [55511,55562) | 0 |

| `362871001990fc34261a5096e161d805721c17a90620e4c68aecc22f414bad52` | 934 / 27 / 2 | `068bde5b9a95edd5b80cea5b09b2abde7b2c3f0fdf0f4249d53fb8b4f108f843` | 328 / 7 | [116402,117336) | 0 |

| `36ce66a874175df45a80e4180b2e0627359375c550d4636fc793200db2587a34` | 420 / 6 / 1 | `2420cb382539272792e62f0e082481df0ba2782317d5f39931720a526ce12683` | 328 / 7 | [193568,193988) | 0 |

| `39c2991600dc7bcfc74f6dbdb540055048b4b633dfc7605d3f3ab76da9bd3c64` | 1117 / 33 / 2 | `3329063eb8e80fd123cdfc50a5c129b698d74f27256668a8435ec47afdbe7f39` | 328 / 7 | [92565,93682) | 0 |

| `39ed76a8f0abce131ef150d2615e45a2d4be44e110bdc4d7a56a77dcdc3ab0f8` | 1318 / 47 / 2 | `973e5f530bceb577809d90b87468c279a2504ea20bff63ae4da96bec60c342e1` | 328 / 7 | [16051,17369) | 0 |

| `3a2cc7373cd8a766c432edcdac16977105d48d9c19b0239c696cb8b15fa7ba57` | 1658 / 35 / 2 | `63a9b515e0dbc39ec728968978cd49b4732c98d30cff2519ae352bed4a5fb523` | 328 / 7 | [27783,29441) | 0 |

| `3a33f608ef07e3dc8d7e7a339bc939eed204d1c036ca3792fe24e1e74463f0ae` | 51 / 2 / 2 | `3857cbd1f7db2d5b0cac642cadd561641f1bde8772bd4956ed5c696422b52248` | 328 / 7 | [86808,86859) | 0 |

| `3dbd9ceec2ae3316370314092fbcb624f91050e66ae0e20509f9dfaca81c86e3` | 1850 / 26 / 2 | `41b74fa83d2f36333335de8ac2d366f7cfd27fe8a655a3fa917b8ab3936be973` | 328 / 7 | [206359,208209) | 0 |

| `3f083007aef982459e36850cddcbb1571a2344af1fed50bf44ac3277f780b770` | 1144 / 23 / 2 | `68a191d5c079d9880d767db114d358bbb53c745a99c42590cf0b75286d6a7ee8` | 328 / 7 | [159185,160329) | 0 |

| `3f6acd1057cb0964056f6995d801ef8611466f254271580d69ffc6bc50ada599` | 860 / 19 / 2 | `e55e25974159b595f079fd4a47b753b5dc4c69f67a3b5ee570da60f25ecaebab` | 328 / 7 | [95704,96564) | 0 |

| `3f8a34b05d85c54d5c564e8b3d5778f4b7c6833c911ac6e31bb91004705a612d` | 2022 / 48 / 2 | `d124a81edca0445ed486a02111a46be93f7284237883f30f8e3555b37f0c1bec` | 328 / 7 | [93682,95704) | 0 |

| `402414011b95ec738e1f7bdeaaefa294bb08c15da0671c0d7b348bfb1fc15781` | 824 / 26 / 2 | `c0a7e548112be30e1933171f5cc7635afc1626fdf562d675df27bce1306afb85` | 328 / 7 | [165268,166092) | 0 |

| `430272005bd87ea86a0ac8f04ded7b31d7b30065410aa2cac998172163a1eac0` | 732 / 17 / 2 | `f82f667163aeb334fe09ff093e26252c521ed4226b717a01f17a3059d068eb63` | 328 / 7 | [126385,127117) | 0 |

| `441aaaad58ccdb96acf28d0ea83f67049178a3b6d35aa2dc773228f968e11c7e` | 1145 / 22 / 2 | `e086a2a656c174038df97bb798a3d5e9c99c0b80460442b3879cd09857719bee` | 328 / 7 | [187534,188679) | 0 |

| `44daa121c7cf5b47a3f639c42d1cdb5f1e70fae463c177ea0dc248c7e3848ff3` | 130 / 4 / 2 | `4acfe5a2d5a8f02b5deea860e0025a30becc88b264e9024a6021bea9a331f510` | 485 / 10 | [25432,25562) | 2 |

| `44de17b0bc3ee6e429099c87da8a13ac76b7f45f5b26209f311a821b086deb86` | 136 / 2 / 2 | `fca0ad29793050c47448ca92a7843cb27f0d2b5906e38cc8eca93b4b2beaf500` | 328 / 7 | [18852,18988) | 0 |

| `4707c9b2be597de7db9f05fe8a7fbdcac5f9cea22563f278e7d18a927f1a2fc7` | 1021 / 40 / 2 | `73ff66c7626a3f91432a3f9d96a21d33b50103a8e98d6c4d40f44d1b04155213` | 328 / 7 | [15030,16051) | 0 |

| `472f3b7460d2e43304aa24cb7b9cae3165914081a1c131528e7b3a672a1597d3` | 60 / 2 / 2 | `baa28355dca009415893bbf80b4824fe170b4c222e4c03b87b9cce2b2bd08922` | 328 / 7 | [82758,82818) | 0 |

| `4773fb3a1dc30aa8250574218d7e231b3ddcac23b38d7b6fce1fbe6757501140` | 3013 / 54 / 2 | `478e03ac128ec48cb9c5a6df60902a4f4d50181cf596a022921d87b5870d3851` | 328 / 7 | [213512,216525) | 0 |

| `47aa7d67efc061585de15f04a60a0f93914b4cf87dc165105118124ae2825cb0` | 60 / 2 / 2 | `c7484f8c4dbf886e07f5f44ec5ebb0139b88ff28182db972d9b360b4f9cbfdce` | 328 / 7 | [68968,69028) | 0 |

| `4936512302a78e682c3bba9045561b126f57409095fc34d8ffc77d1d68630b09` | 831 / 21 / 2 | `b3ed1d3b0036dba9b0f4906a772e55a734b97bf85c8350a6bff35ea6f105034f` | 328 / 7 | [118119,118950) | 0 |

| `4aa7dd18704f49a2948b6775cd1afe0b8a431ff8e8880434ea2721d6ab41335e` | 1023 / 30 / 2 | `33455f678549da46f79c2356c865a6b4fd5447ecc6102cb2c522c216e32ffde4` | 328 / 7 | [56944,57967) | 0 |

| `4aecaa3e39890ee434fc09d7a6e648e414c7333d80e9ae94eb849f7d9f64d467` | 1519 / 33 / 2 | `b49d786dfbb71bfc3cc05850158992a491b150bb230b6ba221d05c37618d9aa8` | 328 / 7 | [86907,88426) | 0 |

| `4c9e8087ed3826b95da48c3ac722ee15ed8111774e749e7bdfa4de8fe127cce0` | 144 / 2 / 2 | `8a600e9205f920a0c53f264c3867197c7589e5e48970b10e987de3904f063f7a` | 328 / 7 | [11252,11396) | 0 |

| `4d9ccec64e27fef01b8d2a11375cf29448040c205088bdafc15cc90ce524d866` | 1973 / 20 / 2 | `3a2f7a07376a4f92d886992abfba9dea29fb865a6f63a3329f49189e27243196` | 328 / 7 | [75018,76991) | 0 |

| `4e198a7b042378506201ae6a26cf78e56c80b0aeca685b9bdc628b074c718f82` | 53 / 2 / 2 | `4873824ec220f7210b7d1e160fb67e998f08fe6df804a4a49801aa8b8352cb13` | 328 / 7 | [33345,33398) | 0 |

| `4f3e1a6dab466fca335953afbeb7b47a204713cce5ec81a9a91de66f1136202a` | 982 / 22 / 2 | `809f2712ea507e47ae2b17ff9ec94c2900891a709d5973fe14fb53b8e14bf810` | 328 / 7 | [135215,136197) | 0 |

| `4fd235927c9217d29d4765fdc70c98df9289795296b7e5fc7479c7d5e4affb9f` | 398 / 6 / 2 | `0d085d29d56c9239ab986904aa136d123966ae11385a9bc6fe7395f6abd6d887` | 556 / 11 | [31151,31549) | 3 |

| `50490ced6d2ed020880e86fc48b5b47515b9b4efcfb3031552b7407b1bf0edca` | 185 / 4 / 2 | `06606d2da72e69749084ff5b269c8affb85fdd721122e5fa41279276f2aeb628` | 328 / 7 | [0,185) | 0 |

| `5124472be02c76ac2f0d5bec3cc0d653fc17252154f1f6cf2366b1d74ff43c26` | 41 / 2 / 2 | `89c7c82f235b3abd5b913057a27632f1c26a910a70bd9dfe43ee08416ff1f09d` | 328 / 7 | [78356,78397) | 0 |

| `51f7af1f217392364d2fe21fcc677cc8ebd3fea7b34f0d3f276021a5363c110c` | 108 / 4 / 2 | `af909caa02534b82f484bd91d30bcc3f57e3b599e23f5a9cfad48cfa7a74df13` | 485 / 10 | [82758,82866) | 2 |

| `5210844d9c032e7c6d6983ddedf9adae7a79a845f497fb9430c1ff234a935e67` | 1526 / 30 / 2 | `4461a360b1e35259c734c2ff8cc922b1ad0af49de1e7e999172f2f2d30b32589` | 328 / 7 | [230890,232416) | 0 |

| `52c920bbc6d09fea07d750297bb85b03ce0e8a0600718d183e26a83aa8ecbd0c` | 466 / 2 / 2 | `2a51edba6f895e8b6a592a6f9a6dd116214e567367da52005fc0daa7fb6d4841` | 328 / 7 | [113646,114112) | 0 |

| `53d4a5aaff0ccb369fed986c326373c0853bda29bfcfe43de979b635ce89aae3` | 1710 / 25 / 2 | `066d22140f29acd2cea0ee1585a22df9202c6229885ff32861ed15cc19b8b1be` | 328 / 7 | [29441,31151) | 0 |

| `557465cae39cc4ca6e670ceb714ee9e8e4177d8e17b8ebacb711367e00be5ace` | 52 / 2 / 2 | `0c5d8517b606241e7034e5ec4910ca74626a99cd3f39c5702b8d5fec6edcc692` | 328 / 7 | [25432,25484) | 0 |

| `56040bfd48608c107c8d23293442db6d6f7e3e007dd0cde47ebd43902b874684` | 147 / 4 / 2 | `295fb0cc294c55e87d0173d8dda706fd8c8b6fd10d37df6b528c9208fd41443c` | 485 / 10 | [140917,141064) | 2 |

| `583418ce7b86072c958442f0a4179a473429229c0358b624e3e778bb1b53bec6` | 4557 / 66 / 2 | `568bc4811fb079075d328bbb3129e58616d5c6bf926b35d5efe83560d99b42ee` | 769 / 14 | [45155,49712) | 6 |

| `5835e7dc0110ed3fe10e56b6c92a52ea040735bfcc86a999e76c694adac8c9ad` | 1218 / 24 / 2 | `ce46ff5840ffe881fb3c6698cf589e16adff0d89a6c45134fcdc9ddcffe72dc7` | 328 / 7 | [174792,176010) | 0 |

| `5a174f44b43d66cf88d8cfb56c4f6a62465dbbe4bd4dca7d8c8c070c023d8ab5` | 1365 / 12 / 2 | `7fb336b1a30a2288fa7d1eade9c196dc8c87ab80619201dbbed554834d31d7e7` | 328 / 7 | [76991,78356) | 0 |

| `5a3521bb018111bfeea91ca41d1d99f748a65c449f36c584cb6b6f503e594acc` | 881 / 22 / 2 | `15e247eb08dcbc0c1b2b92edf24dd22ba3dc379b19c3f967314319f7eb6b10d6` | 328 / 7 | [82866,83747) | 0 |

| `5a7e708ec94f8bd857acdb691c5e654ddd96067c37c11076a306c5cfd708673c` | 967 / 11 / 2 | `2fdef0bc3ecd3075dfdcfc9c2732eb8c11228513c93d41929b78cb068dab0890` | 328 / 7 | [209796,210763) | 0 |

| `5b3f571f0307b02dac5e9f4914fe98b6856621afc3d0fc82c90b0e15db315c61` | 600 / 6 / 2 | `06caf5f7bebe9a800ec16c77d634340bbda6324463edd8263534507b463487e3` | 328 / 7 | [141064,141664) | 0 |

| `5b5fe3f534552106c3425c4ab054450cbcddf5480b9ff9ee36008f843eccf1f4` | 665 / 14 / 2 | `ac26e6d8097710df47f1eba313ba09c21c35f5c97c1152e097bff437f42fe57b` | 328 / 7 | [23881,24546) | 0 |

| `5ba0ef3ddd029cfc3a65e86dabc7d2588fa84f0c980aecd82b526172908d6aea` | 99 / 4 / 2 | `cb7fcca75241ea56abb2f0b2acc6aaa0492f08e96f1406e9198fe7aaa451691c` | 485 / 10 | [86808,86907) | 2 |

| `5be7ce10257a59ca44cf66414b412365c9804f578c2be4e4fede02624f49a7dd` | 1096 / 14 / 2 | `01d28031b95a124fbbb9f52fb307a1fa6371dc080da130b75ad9cf5067523fc5` | 328 / 7 | [44059,45155) | 0 |

| `5ef42bd7a739c964cfcfcc818c7b019b911caf61ee93c9f79774e048de9c64ca` | 1291 / 13 / 2 | `b147014effcf5efa2fad465160652dbb917c47862dc1147df00bc2626afc5896` | 328 / 7 | [99442,100733) | 0 |

| `5fd570c2d406ab4d8ddbdb7509186b1bc5b3b56b2f9a610a92d5e528e5f0c1b3` | 260 / 2 / 2 | `d530ac6cb7226064c23e245f528b2df222070e8c4728040dd1b7ed76f53906ea` | 328 / 7 | [31289,31549) | 0 |

| `610c2dfbb4c101e59a5eace80821b4d696a8d4421f45b2e745e50c65e7d138a0` | 1373 / 34 / 2 | `d61c927315194076d264492618878bf1b841bf08d998d2e40006385af3bce0cc` | 328 / 7 | [143010,144383) | 0 |

| `6161a73ecc868c1a5010a0a3a7536784203dd613eb25d0d0391eff1f3a94325e` | 1167 / 25 / 2 | `e54316a604bdc218416124d6ecf7803d260869ca2c1b8c43a24e671d1df4240f` | 328 / 7 | [78445,79612) | 0 |

| `625a42d0c2c5251efd57bca51e3af63654a659bebd4629a19fbc546b59d1296a` | 1188 / 18 / 2 | `86e09e6e87f28f3d3e8ee2859f577ac84345d3f658490dbf5ce5d2b250710fe0` | 485 / 10 | [181246,182434) | 2 |

| `62cac1a9ae1e70284c6f5239c8e406e0420510bc79ecf769e162ba56f8c132b5` | 1138 / 18 / 2 | `d95d93e7dc1cda011adbabebf8b96e99be57159fad3cb084bcae964380a1a2a5` | 556 / 11 | [193568,194706) | 3 |

| `6478e2b95df1e6ff654dd18e03c448730f57a99eded3516a2075f959318d5d60` | 598 / 9 / 2 | `f0a07837cd9530fdc4344601033cce646c58e2e8d3981a2952b01a4094ae0746` | 328 / 7 | [74420,75018) | 0 |

| `65579100c3cc079a6ab66ae21970e88b042b86cba4ad252832c05e3778e02237` | 1672 / 51 / 2 | `b705cde48241915fb92393fb1e5e1a80a1f309d2bcf33dc5c423ed6a386d1338` | 328 / 7 | [218825,220497) | 0 |

| `68ef71fe354ed7b25522bea70d3c1a509a9b55d2ed33ee8e99cd7d6618d56ad7` | 1085 / 25 / 2 | `771f1a0c06924992ca619c8a9477bd4f5a0a53d66520e78955f3181de74fd676` | 328 / 7 | [198611,199696) | 0 |

| `6932fb2dc043d3710539f98864728f304c948a11c941d236ba0b06287f336461` | 1735 / 16 / 2 | `3f04fd0d7081896938eb8bae11e203b04c2af139ac9779cccc693e31665f101b` | 328 / 7 | [88426,90161) | 0 |

| `698a2dee9e055d42d2482547ed44e7183b395217a530c1a882eaba4f4f2ad263` | 595 / 9 / 1 | `dba48324f0d65a746f863a78881a60703775212b4312a6625c798d1875113d97` | 328 / 7 | [181246,181841) | 0 |

| `6a71711c4cd3e6959053720af28fee6ff3104efa86ff40d414f1609893da1911` | 725 / 10 / 2 | `739fdfa029d14957bc646725b4c0116253b453cfe5d97081c21998af480be83c` | 328 / 7 | [161331,162056) | 0 |

| `6bca950a7e5394471238f845120d89c38d21b7d0983b7baf08d0de15a06ca42a` | 1734 / 28 / 2 | `13338e9660ab3b5220e1292ec6581c2784b9ff230a7603513691c6dced0f9900` | 556 / 11 | [37950,39684) | 3 |

| `6d4aa4daa1a4df89fc85dc2ccd41cd47435ed1c8a1e9a9b8f70ee8b4af454826` | 411 / 2 / 2 | `efb2ee206fdc8d7beb713ffdf8eb05996152451cbb2ab8da233a3053811ddabc` | 328 / 7 | [60167,60578) | 0 |

| `71c6b85ce78068adc0e8d090d8a8aeb462dd830054ba92229a07e00f01aebe99` | 1114 / 28 / 2 | `c8ddc5706a2b75363232940f0f8c397751b3d451fae83fd3827e204063e701bb` | 328 / 7 | [114112,115226) | 0 |

| `7238ad80c903f2a341d74ba23a30260b23bc04e839056d3f826284b876b085d5` | 1821 / 26 / 2 | `11223b3b570c5540a6212d86c99664dcf2fd8a58081cc6be6ae16ac61faa370b` | 328 / 7 | [90744,92565) | 0 |

| `751ffea971df0a29aa3dceee9994200341e7b86a0bed2f9ee23ed609b20f204d` | 1591 / 39 / 2 | `ea400a14f056255cd199a58c1f6dff082223503944398bc26982a2b9289abf02` | 328 / 7 | [166092,167683) | 0 |

| `7534800063c37df7c82e66107e3288768547351c5c8c828aafb97bcd7fbbc7a2` | 1301 / 27 / 2 | `d78bbe9ab1c5888464dc044e695972fd052ed81ee1ab876de54e6da7436dac15` | 328 / 7 | [105217,106518) | 0 |

| `755595969145006216506ac3bbb51b8ed1578cbbf6d00e3421e9b4e7184c7ce6` | 1099 / 22 / 2 | `607cc3fb4b76bcfb218d54be9e357a9683a1f9627baf0d08505c72a1460575fe` | 328 / 7 | [125286,126385) | 0 |

| `76e8bda974442b7602d00e27cf72da32b88c32d3182d80e292b3e351f8a3b6c0` | 72 / 2 / 2 | `9e23b765acb1c8e2bb416c042030e244868081cac2ad3d73656a759f47ad601e` | 328 / 7 | [209646,209718) | 0 |

| `79697337fea946408ad03a7ad800141090744fe835f0d35dd256ab4bad503bb5` | 1720 / 33 / 2 | `06eb36a1e818aec3f6aac020f140df00dcd81bd80fcb5ea66e33187f686bfbb9` | 328 / 7 | [204639,206359) | 0 |

| `7992cc777c11674132e03e386e5bd22e95c9b3ff52c5ac39d638ee894f092489` | 32 / 2 / 2 | `a6d4df6a096dd2cd8af5709ca86481ae218768b29f92a1228f8d8b524e9d6733` | 328 / 7 | [185,217) | 0 |

| `7ac48248522e83f0d483dcf7b21ba22fc938e60a57afa53bff7b2fb6fd496e3a` | 1337 / 47 / 2 | `04e030f93a6500f2b19403d23d54f021d3334e8a21a24f3a6b267ff03b731ffe` | 328 / 7 | [106518,107855) | 0 |

| `7c0f1550fc676e468485fcacc762d03b274edd459f1024aafd0f7a14b72fc7de` | 1617 / 41 / 2 | `803140c33c84d7d5606395cff15784cb2881fba73ada5022db2b728056c812f5` | 485 / 10 | [176010,177627) | 2 |

| `7caeab1342641a08d027850acee1fdeaccb28c99dca3633b3be55898f656085c` | 1103 / 18 / 2 | `4df510f3c1d98f70886a137b3ff42653f45aa0b800a248056a28dc09b64b7491` | 328 / 7 | [154726,155829) | 0 |

| `7e2f7a19cc9d22d1ce72ec770a9dd9007dea9a6cb3845234507d95f0efe0d612` | 1097 / 13 / 2 | `f45b7b8aca8e2f2eec2520b838d4cc71ca716426a5f7755b16e99df4dfcbb7f8` | 328 / 7 | [22784,23881) | 0 |

| `817821ae1943bf208ded60a3d9019d537d3874c5bf1fae46e6b322d7bbe88e14` | 1684 / 35 / 2 | `c6d6df2b25a9afb2005608cb61b64772604e1f5fae24a329cfbdfcf8c534871e` | 328 / 7 | [155829,157513) | 0 |

| `8198904318811f55bd642fb43e59a4987b5ff4276634166495663e147211ceb1` | 1356 / 29 / 2 | `645caa46db1711ed41ee926d11777d49305e207f3a171c285d8b36db87b5ddac` | 328 / 7 | [202085,203441) | 0 |

| `82a1edcba51fbbacd9603b1a54dc3e2ad454b5ee15f70f68960278b62fa2ebd4` | 1164 / 21 / 2 | `48793b2da596f6e806fc9961b1664c1c1966cefa96b512ae1614475d37a1bef0` | 328 / 7 | [26489,27653) | 0 |

| `8458b76fb63c34d4056b60000042f08e1d1b1bfb690e72a97853cf5b1113f549` | 1389 / 28 / 2 | `b53d9605cad7399f856fd82c43099e10e8b053c4ef538753057b2e707abdc281` | 328 / 7 | [228347,229736) | 0 |

| `87602c96aa850db8d95d32436bf338ae962bb4e00f043a6f24f7a9237f7df373` | 297 / 4 / 2 | `eab0692e52c19dac54c670180faa47a609bee412144ed853f72c932efc4212df` | 328 / 7 | [14393,14690) | 0 |

| `89683ac2bda35da807eb9c7931312dd6c954821797e95cd2629ab4519f45ecb2` | 78 / 2 / 2 | `71ac4389c3f672c9efd0bb45ab47af17d362ad28fb17605e522d4385b595e28b` | 328 / 7 | [217,295), [824,902), [4227,4305), [9119,9197), [11174,11252), [14393,14471), [22706,22784), [25484,25562), [27705,27783), [31211,31289), [38007,38085), [40888,40966), [45222,45300), [49763,49841), [55562,55640), [56866,56944), [60089,60167), [69028,69106), [71722,71800), [90666,90744), [113568,113646), [140986,141064), [162911,162989), [183179,183257), [209718,209796) | 0 |

| `8ba62419807b0817a27486ad126a1a327f300a21eb2ec880c97a4165fa555ec1` | 1439 / 16 / 2 | `c4587988704f4d2190d00e503e6d504cb51d74f6871d5372022f95594679b9f1` | 328 / 7 | [17413,18852) | 0 |

| `8baae850e99a63be3ec6409789d604839389a1d5eea38e6ac057598b0b74f6d2` | 1252 / 37 / 2 | `ec65e95087937ff718495ff3b6001599e9842285d79fab527cbb7bf544e23078` | 328 / 7 | [186282,187534) | 0 |

| `8babb41814eabef8e8f006181969649674233972935f611d13d159fdf579abb6` | 873 / 17 / 2 | `417e6b7ee2fecc10470a5d9106a9cf6ce00a31c50607097519e83267622158d5` | 328 / 7 | [150541,151414) | 0 |

| `8d3103609cf6632a942adb1c30a40fda6481603b2162a1cee0e3fed32fa35f5b` | 793 / 22 / 2 | `824d3b6a99977930c00e4a39ddcc8cb14de982ccdb15605f54439b48d2a0e495` | 328 / 7 | [120746,121539) | 0 |

| `8d9fb739549e45f8fe15c9bf830f94453c74f86e6651fee7abe39d3b58dc91db` | 1103 / 21 / 2 | `a8e932d9a7647655d0a5d98f3488c415167247a0098cbdd276a5b8a15ec44f9f` | 328 / 7 | [73317,74420) | 0 |

| `8f0c951a19753f9f16c17f04acf088b727319e1a2d7e800de506bac38cde07dd` | 78 / 2 / 2 | `06f8698e3bd1c983aac5ef344ca1988004b3a3ef8e2d3f94bd6bba220a85dd15` | 328 / 7 | [20302,20380) | 0 |

| `8f4031dd07e69c10d01dac15007e0bbdad540a8188e3dfe565212d0a81e3f6ad` | 1176 / 39 / 2 | `c1a341217b269496300204ea38a110ab4fb66b017b2b92fdfc445d37bfd77528` | 328 / 7 | [115226,116402) | 0 |

| `8f9463792a5258d9a6856c95402bf1f1f579669f10fad38395391e80a7c32a14` | 1404 / 17 / 2 | `7965740958f8ceb5e1f654faf0bd49c256e1f8b3b4c316c2c46a13bf55291645` | 328 / 7 | [96564,97968) | 0 |

| `8fa139a1437c4b688c61c7a2c1003775ee094da61cc136a77e8533cdf64f7ebc` | 147 / 4 / 2 | `3b21c8ed014656340c5bf306c69eb51a7f0f67f7bc31c7b827f04e646b911992` | 485 / 10 | [183110,183257) | 2 |

| `8ff5173a9b3428694044aeb57db0a4ea8325dd52ce21a3c5583a35acfdad77be` | 827 / 18 / 2 | `4311f34548ca9f3fc9e8bc496f31645c64824a78e1370320435950cc0efdc1b9` | 328 / 7 | [212685,213512) | 0 |

| `8ffa6df089fdd8e22d15682775ba711442cb122ac531f80acfdc90e22b7a53b6` | 1346 / 28 / 2 | `50a2b61bf06a53745fbfeecceb5e168405015a02562ddac8966955b222eae3ee` | 328 / 7 | [141664,143010) | 0 |

| `9059492ed5256d8d58e04fb0407419ddaa461026802d00f9e6174c7e1e4c7809` | 1507 / 34 / 2 | `0df7332c5d9376262719a0ce163f99891b57b0a2aa342a9d676b050ca9c782f4` | 328 / 7 | [127117,128624) | 0 |

| `905e9b2cb869e1635c086353430b2e2601a9e87ffeb370dff10a35e889fdd034` | 676 / 10 / 2 | `51d65d175f3835312dcd0f44d19f457a92a2a60460d4a913e52d477da9611dbc` | 328 / 7 | [182434,183110) | 0 |

| `90781318d8f9b56afc106e49cf1070f5e3340c26d67dc61c678a726422c9564c` | 1935 / 42 / 2 | `81ec360fb2ef847cf9ac0a172cba5c8cdd72f21e025f28c326c6b1799e58e675` | 328 / 7 | [152791,154726) | 0 |

| `91438118907d4c2d2a8fff9d7cfabeeed71f2345526656e2388e08386f19a828` | 1538 / 28 / 2 | `96b89030a4ddbee6ab1194b83bd7d7a762d6da18564d0d211241b19e39856d85` | 328 / 7 | [233191,234729) | 0 |

| `916118201a62fe7ab14e8cd3713e3449a6854ba8ec2c740ab4da583f8fc5c414` | 291 / 3 / 1 | `f72e68a1808adb226204f82151c9aebf1209119f7098446d58069410be67d700` | 328 / 7 | [139286,139577) | 0 |

| `916c8b57b491260156ba39e858fb7ddd2f821328018727c0cca7825730ad1178` | 1122 / 32 / 2 | `61ab74a0fd10c1690f09dee285164d21e5a40f11c364c2e0913964717b714c64` | 328 / 7 | [133266,134388) | 0 |

| `9299db7f59a34f958e1f474cef2b10e866ccfd664b3a09019947ad559794d1ea` | 1002 / 19 / 2 | `9dc453e544028f1bc6972ad8ab39b9d2886687ea48b1a09c48c0196af43d652a` | 328 / 7 | [160329,161331) | 0 |

| `93c7fc7eba04c82de3d54e11d50ce98fd6ee03bc10105ac0160480bcafde2191` | 138 / 4 / 2 | `7ddb5dad901847b010a64d03ff3c841bcd5e05277d6319c7ed73b7066d67a9d3` | 485 / 10 | [20242,20380) | 2 |

| `93ca504e3059996775c59bc5d3c688beb53af70894922c205cecb6b24572f089` | 48 / 2 / 2 | `5bd8e00683a8faf362a0ef6ea75755e142c8dd473d9db61ec42d5d1b8b5befde` | 328 / 7 | [78397,78445), [82818,82866), [86859,86907) | 0 |

| `956bb9b9c99b556d3c83d2a64fd2cf12c0e137ce26dd7bbb8a04f9fcb0d67ab7` | 1747 / 29 / 2 | `d66d11e6fc0085c9ae5e5521a2d069c03e1e8c3cd4d09bdd065a49672ea07cff` | 556 / 11 | [33345,35092) | 3 |

| `95e989a97c01b16bf28e71e2a506db4d6f357c364fb7643275221f6fb112574c` | 2119 / 39 / 2 | `c6f2b2b1fa4ab1f1c479ebbf67c8120453788f3514e409a2558f9e31415eb046` | 328 / 7 | [41940,44059) | 0 |

| `97ca0b147af7dc87d9aa578a132805d492851c893a9245da4243652b3e067673` | 2193 / 40 / 2 | `67c0655f756f6412eb94f0866c46419f84642453570eef10bfb90a448397c5d9` | 328 / 7 | [69472,71665) | 0 |

| `97e1697dc4fd5bff1732a72fe53c3a8182cd82623b3013323b6d72a9fb5cf123` | 1014 / 25 / 2 | `663867321ae2012ff447c98e4938b96654bdc2bedad7c4c42808c0296a6917a1` | 328 / 7 | [171082,172096) | 0 |

| `9984f0f9827ab76ed71cdb5bbd7dae9816361369065738a18d087daf60c2178e` | 1433 / 32 / 2 | `77336c6cb5ebd24aef4079b2752acded1c649729ae5cbbbe669e70e521253a0f` | 328 / 7 | [216525,217958) | 0 |

| `9abccc5a4f112e3ae41e4aa9cd89cbd50c134ceadad86a2d08873908e47b774f` | 711 / 19 / 2 | `edce682415f6e150dc882e7dc7881bd159ebf36ad096cc96bb07bbc0df9df1e6` | 328 / 7 | [1700,2411) | 0 |

| `9b475f3d3099cdc077ced2418097284560c2e1a5baaa90fe243353f5681321e5` | 1047 / 30 / 2 | `0dfe72769cc80a23a497b93fc9169315bacf634d989cfd7bf85c626e7e6cf02b` | 328 / 7 | [130315,131362) | 0 |

| `9b910b826bbec6a05b01e271ad4bc8eeca17176a9b8230890a436ea83eed8c0b` | 368 / 4 / 2 | `db263e39cb875986c725cf4aef1928e74837abe1a08d69edeb8e46503fc9e0cb` | 328 / 7 | [217,585) | 0 |

| `9c65f897c84155877e67d0c93b9ece034e7176de23914e138a08649f2380198e` | 1335 / 18 / 1 | `875d150854b5c7b83653eab155e77e4d9562e0141da5aae56aadd71b254dff85` | 328 / 7 | [236937,238272) | 0 |

| `a03a13ed3c2f986ecaa41ac797d7f9aadca9f9b32bd0974de0f59970a90888e5` | 1280 / 34 / 2 | `ef217eaadc7d916eb4a9dfe7d5dd1fe7c95851e57bb1bacb7fe36e7b435095ff` | 328 / 7 | [199696,200976) | 0 |

| `a262370c499d58ea95a3f57d287ad15580a910395247df1d72f0c162c4e86949` | 1167 / 24 / 2 | `5cc5883c466473c60899319fbcbcda0b506c72ce2e0ac9b7e8ece82e4e87e1dd` | 328 / 7 | [194706,195873) | 0 |

| `a3369404072987cf98ce4c193dedd412106b179aecd60f9d9b5a908216f362dc` | 775 / 16 / 2 | `c7bbb1249ee5bc99d729721e46093b9dd26592d14b01e0bcea2e30b1487ebb60` | 328 / 7 | [232416,233191) | 0 |

| `a349ecb51389284af0d9942ced062e604529f1c2029630cc433a35e670228dcf` | 867 / 17 / 2 | `aa4dbbedddca9a9e863ad942ba6136e5bad43b5f2490b47439694b432228294b` | 328 / 7 | [217958,218825) | 0 |

| `a41dbe54185bc4fbabb4ec8f9761d68c6e630cf046a448ff1d5ead648f1ba49a` | 1772 / 44 / 2 | `e9567f2123fdf44010e369c2c16372e8663af504042a38286f15ede4198d8607` | 328 / 7 | [2411,4183) | 0 |

| `a50df88fd4cd16cebca7776e2faaeb70b3fa7d28bddfe6069a5fb3bfa5dbe048` | 987 / 24 / 2 | `4a2f5cd0950731ce229d36cb62ed715c44e9d46c194eba33cbc8421057a3747e` | 328 / 7 | [81771,82758) | 0 |

| `a56ab8aae5f5dddaeb8b7cc761548edc9835e290d7cad7a218d997ce20aed0c0` | 343 / 6 / 1 | `fd0312e2296249865ea93279e66c6e15fd9fd2c95641839f2edc7b42ec5289fe` | 328 / 7 | [151414,151757) | 0 |

| `a602a57e20b28b62720c4a3dcf0f9a82dd239a6a041a3ef09fdcd6c5d3692e5d` | 1159 / 30 / 2 | `a4b54551902417aca163b3bfe252bd11eeaae86ee84fe7c1083d43f6dd6d796d` | 328 / 7 | [137200,138359) | 0 |

| `a89b110a2863cab342ce155db2aa964f03b52af5281a3a633ec385003735396d` | 780 / 11 / 2 | `19441451f7228dd4431a2ee3a6c0e5535a99da298b63655b28db0efb82c20b23` | 328 / 7 | [162056,162836) | 0 |

| `a92a190019d9873a9acfea086acdf962b127b3677567036bb35d59294820bc66` | 1925 / 43 / 2 | `f91ebc100e3692c8d859be72428b00468b4b900823192322eaa405f88fecb6ab` | 328 / 7 | [184357,186282) | 0 |

| `ab66578c6774443c16b9a64bcb532e061d3f8edb0d9ced22a4ecda9bfd0b73a4` | 52 / 2 / 2 | `1f0c0ffc4b672a3e0c9f4f047f9201d72eaff993829f2bb53c3eb6bef18745f7` | 328 / 7 | [27653,27705) | 0 |

| `acea51c7777ee3b349436fc86bda7e92192deb63e950d0101c7ad43d1121e04b` | 1097 / 15 / 2 | `a7ae56c045264f413a58f329916e351ddd2dd5aa5d5cb544388fdcfbc8b91cb0` | 328 / 7 | [4227,5324) | 0 |

| `acfd341feae542551cf081f197c3f968a280b06e8b82fe0678f0712c5e3e648d` | 2858 / 52 / 2 | `452696eb5541b67a731a30d0f32b51fbada64d42cfe6ff0ba7ed710f4d89bcac` | 556 / 11 | [35092,37950) | 3 |

| `ad2e56ad06f124fdbd874e6b482e44450c571a4d21e54e032fe721ab26bfc542` | 1282 / 25 / 2 | `3a472ac3fd7d26ff59b9d42e54a899511057334bd549e58eeb7ee538891aa081` | 328 / 7 | [145862,147144) | 0 |

| `ae47667b577f1569d1b701e0b0b28b57f2ebbbb5cd97167724c284af21602a65` | 1109 / 30 / 2 | `bd2e7584b9d851725ed46a572d7e1d3eb6b7cfd0c05c52ffbe28075d85acff79` | 328 / 7 | [200976,202085) | 0 |

| `ae54ae2a8dd4aa2b9f6106f92b0e93cdcbae96d25ae5dc5aa1b6e80667962a05` | 2272 / 17 / 2 | `b9dc08edfa6ae3affa8d2a5d4706aaa8e8d1c4d3f9d1b1ee9cd709c106bc3e1d` | 328 / 7 | [20380,22652) | 0 |

| `ae95f3cb9287e7d4b616b7012e53bf3111f16ba228a03264a25d3af875667e40` | 224 / 2 / 2 | `6edf770bc1a0e37029f96d81ed8b02b87446ea69ee2a2325c553d8a28eb8dab0` | 328 / 7 | [113287,113511) | 0 |

| `aef035d0bb5167d8ed2c286415e8ed9f86a508695158c1d25c2eef6be7f95d22` | 1039 / 37 / 2 | `e022e63b14f7e5398001bdb409687210c8454ffd5626ad6136d6a1f6e1428097` | 328 / 7 | [118950,119989) | 0 |

| `aef6c3da566cbbc5b6b97389e777639df28d5bede6d7aa0e4385cef8159321ac` | 967 / 19 / 2 | `d2a7ba8931fbc34e643c23d6cc471f9f8d9c00e56f08a81728205ea1b48490ea` | 328 / 7 | [122600,123567) | 0 |

| `b1da687a77cb422b86b7735222b2ebcf647b0d9da59401394ab74dea789ba107` | 132 / 4 / 2 | `52a45f3cb29d0226a763d9ca47ac82c81f7e007c141ba54e558956d53909ce51` | 485 / 10 | [40834,40966) | 2 |

| `b2e35b15f6dc69614672d6d24a1ed3dfd31280aaa62fa997442704a29c2660ba` | 1198 / 32 / 2 | `08b2420edb8c2cf6d8bd49680034d0bfe6329abb1d9b1c6df437daf5e5881880` | 328 / 7 | [203441,204639) | 0 |

| `b421ffaf3f4198aff5cf74a714896fed0e08335d19457d06a2b189feec9faf55` | 57 / 2 / 2 | `5f76fcab7a8ac017bae165b1db75807521b00f55486a78e1d87ac6efd71f3908` | 328 / 7 | [71665,71722) | 0 |

| `b481e6ed6b9b3f64d1b875f0e20d6ef1a7c11184b73f57708de40b43012a1bb1` | 135 / 4 / 2 | `0a4a9fd868568e72750c5d3082ffb75348cc4b0baaebe650589c776f94266354` | 485 / 10 | [113511,113646) | 2 |

| `b70283dad0783835da72d7eda72bfe0a69f0cbe91308ebd44b89e14eeb114462` | 150 / 4 / 2 | `b66d4024eee49a1308399839a7ee3889e1a6d87f1c0ba22e973c133e904f19f8` | 485 / 10 | [209646,209796) | 2 |

| `b939a4aed307d95114c7c1374d7d3c3bc8f6506d45ca6d546ee757cdd7b9e244` | 1339 / 28 / 2 | `288301bde98f1809f7a8b55a46ac544da6f7c75edeff39507d707096f20a0a12` | 328 / 7 | [45300,46639) | 0 |

| `b9a25c9222c3ee6142ea7188f654e374c853e7d40524da8d3951be405599a497` | 1154 / 26 / 2 | `e4ddc31e94f5a405fe093139cca8a5fbeeea4aa5b59f89923fde2ae533202630` | 328 / 7 | [229736,230890) | 0 |

| `ba09e7b8badbecd1f0036345091ffff910e264017b89d06538a5049643e4e52a` | 77 / 3 / 2 | `fcef0083b4273fa7a3fa31c069988bcaf2018b4b622b89ae86a7550f9a321b8a` | 328 / 7 | [177550,177627) | 0 |

| `ba1a46110be05490ba9b922631c7a80de8a0fbe2700b9b87d226a41f66447810` | 1349 / 43 / 2 | `1caa5b6e96ba0e9cf7838b2a5ca9c92462ea2f2226680881c5ec2332ee35258f` | 328 / 7 | [169733,171082) | 0 |

| `bb9cb917b899f69525f976e72623f465b5df3ccfff956d520c8bda50da6cd742` | 563 / 2 / 2 | `415de96fa8566e6f9494a81c945a179ea12fc9810bd7c9adfa09d28cdb51774d` | 328 / 7 | [49149,49712) | 0 |

| `bc27a21c50f8ffc0dd3c85fdf165f5b5525c740bd981efa0d9d3e58156e6b83e` | 57 / 2 / 2 | `bc95231d5c39578cb274a3ef451cb514ddaa00180c38ac56db9ff3e2efbb920e` | 328 / 7 | [90609,90666) | 0 |

| `bc29aa4c691a1134057260f7befd5588e2420c6e342f8f771f0d7d76ad8172bb` | 1165 / 29 / 2 | `54eb3aa8226b3368f35ac21e2f7d905a5b076cca7ea6b831f2e9400eaaad9437` | 328 / 7 | [167683,168848) | 0 |

| `bc578fae7f93316cf5f0c988cad90865629d9b2aa5318c5784900a3e5033086e` | 1517 / 40 / 2 | `694255bf08db61fb6a4fc2617265d1df22f7b727d1ed80aab970458ef719aafa` | 328 / 7 | [71800,73317) | 0 |

| `bcf626473ee6a740174e0ba59bec7045fbeefb506b8e0e54d1b18e6ea0ad74c5` | 44 / 2 / 2 | `836c2ae0fc254a7f658a5852d3fb1ebad06709218acabe41614cdff6d3c82272` | 328 / 7 | [4183,4227) | 0 |

| `be4bc199a00227b016db43effbd6ef73dd9ddc838fec51b0771bc31a7433bce5` | 1220 / 33 / 2 | `4ef1caffc60982e95ed9187e555a740928bed4e4af9f5832db20408962474256` | 328 / 7 | [189902,191122) | 0 |

| `c0f02a1d0dc24a51fbd7ee626dd60b030f96d8bb74b96584072a7f54fc1d2a3f` | 57 / 2 / 2 | `c91da2e07f19bb691977a9b68f3c99aa0198219b2d25445c1cdb77fd1c9af11e` | 328 / 7 | [113511,113568) | 0 |

| `c1fe382a299fd0e99f6370f433646b9fdaf11bd637fa95b221a492b1216ca9e8` | 1608 / 35 / 2 | `bdce33bb47da1adb58b1964074a6a53e8babc407134e1fd7dc55ab8b7ddcaf04` | 328 / 7 | [178651,180259) | 0 |

| `c31591d079ad3cfc60bd5e6a1741d70d309c2d3c62cd71ea13fe566367801c3c` | 1127 / 18 / 2 | `85905f97cd5fbbee2903a2e8eb3ca066ced3d42c54d931e14604b7547fe35ae5` | 328 / 7 | [100733,101860) | 0 |

| `c3c6811051388c97e3b5d0ffbd2d803c311f5382bd6e770ba2a8339277c29f0c` | 582 / 8 / 2 | `7367b6ca63346062692e71b2ff3b2a4eebc6d4281b61935e6d8cd66817139336` | 556 / 11 | [185,767) | 3 |

| `c3e5dfb3dc6381eb436d50acfa8bab871bdff05abd9a4b05a11b3f1a68163c04` | 870 / 15 / 2 | `7a4b0cb5afca7f7baa9e33c98219d19bef6798518da2ca2d9450f6ad3a806a3d` | 328 / 7 | [234729,235599) | 0 |

| `c51ce3eea6abf5349f9931318c34ad91907b754a20ab218821b55a3c976ce255` | 580 / 20 / 2 | `c53180981db859e5f8eb1f9611a0915a1fb2da8945656ae1ef157de21b23cfc8` | 328 / 7 | [55562,56142) | 0 |

| `c5754c48391212f03bd807b894d7606b63e61cf4cf914b62e44ca7ceb275a732` | 1120 / 27 / 2 | `aa0894a5a548799f465ad550cffaf23b44db457da2d803f1e37f8c26fb529ddb` | 328 / 7 | [148433,149553) | 0 |

| `c59e97b9e869558730b365cd247a18d16e9333ceb1ccb0e0bab4eab2f93b32d1` | 1967 / 37 / 2 | `99f6769a139a1238416969fe7ba2df902fe4918e6d06655f36cb079752bac948` | 328 / 7 | [9119,11086) | 0 |

| `c6b278266ca4dd96d3063d5a081c755a017df013cfa6deef96a49b6422571fad` | 815 / 6 / 2 | `23d86f949a9b8d1cd51202d1bdb289e9d9950c6ecbfb6cb8a5183b5451ac6939` | 328 / 7 | [13518,14333) | 0 |

| `c7732e230a340afba65874b6960bbbe92e1d58705506f1983c7466c9a4c59da6` | 135 / 4 / 2 | `d1af39144dab160f17e85d89d6d319465ad27392640a5cfbc5844b83c7daa6ce` | 485 / 10 | [90609,90744) | 2 |

| `c7b9842b6c357520542632d03a4b130ab680dc8d3c5d24922b0fd0a743602af9` | 1008 / 31 / 2 | `3775a6cec23df3e3e17cf482b2aabc5ddf510cc23d160d417c6c08dc9c391ad8` | 328 / 7 | [83747,84755) | 0 |

| `c853f87559e9cc166924b77f0c7e72dca2b3c33bf534693c1e219ea20d6302e6` | 135 / 4 / 2 | `01fc9cf5b8bb797260541f85bfbe6a6b23a1372ef70593e4e31690859f440448` | 485 / 10 | [71665,71800) | 2 |

| `cabf52cb765e921ab400a79ebe98b7299cb37c357de0079ac275d30ce602a821` | 1150 / 20 / 2 | `006d1b46ecad8139e279408cc263ffc37cbf8ca0a1918d1af4e4f61400fb5d34` | 328 / 7 | [39684,40834) | 0 |

| `cb5e52d3d24982a9c21c2c0e95c360492aeb4992b269398abd243d430c3bb622` | 891 / 15 / 2 | `dea7bad28f9458a4d0646bdb1b086c2375ce62771b2d65cfa6ba400dfa0ed9c3` | 328 / 7 | [131362,132253) | 0 |

| `cbfac4ce166538a5167a451addbe16014e68dcc7a7eaeb59f037867e9d31380f` | 757 / 15 / 2 | `50edc533f984c6ef1f9a0d6776f0a0ca8912b18794cf3b58488ff801d3fe6328` | 328 / 7 | [119989,120746) | 0 |

| `cc890a7fec7ac6ab8fc5716db3f72c14d3c6cbe5840d9bac85b688b9a0a796e1` | 975 / 15 / 2 | `eb50b51c83cd2bf9aa7abe9d90e0edd49947988a961849f30aeeb4ffee631597` | 328 / 7 | [208209,209184) | 0 |

| `cd2f82b2ff48a9b546404341eec13a5d7e8daf6bb4b311461719972eae0804a2` | 741 / 13 / 2 | `7f7ea28a01c671032df8519c0bad583a99945d109a1ebfa1a6f60aa94a0d8d5d` | 328 / 7 | [174051,174792) | 0 |

| `cee49505374dc61a13efb5e665f737df2f9dfc355c32f1ced2927e448adda59d` | 1317 / 40 / 2 | `3b8e2251078fbc8b7e3397c5f45adeff665bfe97239a0e403d42ebfa69e1cc21` | 328 / 7 | [80454,81771) | 0 |

| `cf3a11d3e91869750f8ccd3e899d1ff2cc925ae248d17d0c58f079fe54bd5bb4` | 1638 / 33 / 2 | `f303b28bf787323065a057c1d1f11b1213e13ca56caf4aad4d512fc61956c874` | 328 / 7 | [220497,222135) | 0 |

| `cfb8b50edcb68bec749eb05bd46a4042fa67c59da06cb599fa1dcab278ea2091` | 1479 / 39 / 2 | `145d2b4b2c01f2f18ae584e34c10c8d0d3ba3ad85a4e371584e476970a4612af` | 328 / 7 | [144383,145862) | 0 |

| `d1f10a6c6dde3a4bc0074874c140c25a60eac63c2b14a6a5812e67f3d3504daa` | 842 / 17 / 2 | `fb43708fdde8bca65412c1f7ea8ca5455e544a6a1f164388b81ed1ea704c8d6e` | 328 / 7 | [79612,80454) | 0 |

| `d23a0631c6af3835e1c4a305b80dce347c3009fbcf80af75618a513d685de25a` | 827 / 18 / 2 | `9baf7a0efc7dfcc23b6bd5203b45a4d42ec26fca9974cecba47b597867e3853b` | 328 / 7 | [134388,135215) | 0 |

| `d2582d5a3e32082fa5faa650a29031c1307a2803ca83a948b42a2abcf5aea26c` | 51 / 2 / 2 | `e730e5cd8a9064f68edbf9b9503864fc260593c38afa7a9467f34cddd785db45` | 328 / 7 | [49712,49763) | 0 |

| `d308e0151342a0704362c61f969a1247ba1ed2a1df70e64489232f39222840c0` | 485 / 15 / 2 | `ca6442342b3c66e7683c092302fabe20aa5007edc13f7cce11cba2eee5a99750` | 328 / 7 | [49763,50248) | 0 |

| `d3b34448ebbca85f423abd5d2293b17c7a1921cd9224d4db0c634f4cf32e19ad` | 1085 / 26 / 2 | `5acd923ba5cf301d339854c8dbcc742528488b01a65269671f8cc616f1c61067` | 328 / 7 | [226505,227590) | 0 |

| `d59946061428632bf4c15fc56bb6590d4094a80cf98ea54c1d11766fff1ec90b` | 757 / 12 / 2 | `5240824f1e65d3655fe61ff7ac8c8879eb7e8f219ba6b04427e27e090f959eaf` | 328 / 7 | [227590,228347) | 0 |

| `d60182242a88bc060ba428367b5decb696d8b122e9d546fcd4bc0d402c6b93cb` | 1619 / 20 / 2 | `ba215af660a93107c9c9b038060c2062551563020f22c976ec29ed87fca410d6` | 556 / 11 | [17369,18988) | 3 |

| `d70eb8957edeab1bf1f289bfcce08049c7e490778498b752d4dd04aca93c17b2` | 1338 / 18 / 2 | `4d66411f710e47291008230ce084f8e6937b0f4884bd25ee5f659e7e8d1a3ecb` | 328 / 7 | [235599,236937) | 0 |

| `d70f881870785952ae446d3396717145363498d179c7fac87c96cbce1e6d450c` | 69 / 2 / 2 | `b6be9026bd55a38bca9ce2ffa605137d1006eca34af828e955e1ac045f232be3` | 328 / 7 | [140917,140986) | 0 |

| `d9913ee1ddadce68926cf89b9a874d3412dcac9a3d5bf944fdde8063da293d74` | 721 / 26 / 2 | `ecc65786dbb346fd04840f49d5b80618e66b6205a4d20fd48fd718cbb9b186cc` | 328 / 7 | [824,1545) | 0 |

| `d9d63546e04ba716f017cf7dde21a48ed4dcaf6244ff6d04edce2a05dedce1e1` | 1599 / 24 / 2 | `e309e0d0369f8d188abd91acb9410a46179c6e6013939a6a9e6f706d6454257d` | 328 / 7 | [38085,39684) | 0 |

| `dbe16e30c071470f84b9cc3d6fc9f05a8ebb4dcbb51cac5ba92f253395dac706` | 1298 / 24 / 2 | `d5b41e96c8f5cb2faeee7cc2d5b5d03895a0f565a41accfceaa2bcfb01330df0` | 556 / 11 | [55511,56809) | 3 |

| `dc5cb97f6730ab70e3afb0cb68c7034fdb9bcf2a13dca96c67a985b67be1bf13` | 60 / 2 / 2 | `675b23d21a79ceb3800c597571650d4c14a97f5e29f8edaed8905fe67f3b9b63` | 328 / 7 | [20242,20302) | 0 |

| `ddc48da282f1799de3e639180a051af774e97c12813429a97cb52955f5dff717` | 927 / 24 / 2 | `501f3c0019bc7c700b72f6d224f67f240e9358244a6153e1e54a16e3239dba29` | 328 / 7 | [138359,139286) | 0 |

| `de7e4b8a4836463e2752b92ffb4e62c40d6a929920a8ade8c1c5fa99c66de9a6` | 130 / 4 / 2 | `3c37a57eb039b36c2c88e95240db34ad40f7727d1f9e9a82c837eea8d76afff1` | 485 / 10 | [27653,27783) | 2 |

| `df2e3df3c984fa4602df97709cb8694f8c1d715e6d0085cd17e28cb96a2439dc` | 54 / 2 / 2 | `3f939cc7c81f22e033c1fedb32b602fb8a6727441c3f9281f1451cfcc16a1990` | 328 / 7 | [40834,40888) | 0 |

| `e25e894eab9ef67a1b58aedc8a35d6b6546144b1a329f7dd6e9b35879bf84f28` | 1691 / 30 / 2 | `7a3d4f774592b5347dca898eacd16230a11d7e9c2aa42f7d3834845d3eebf8b6` | 328 / 7 | [128624,130315) | 0 |

| `e27c210f0a81f478bb843f29d08e682d3dc0aa5ba72311b32715ab399418c564` | 1289 / 31 / 2 | `ac2f9d44a8ed05a8242a60618f31ec6687dd2a495149dd9dd221e2483f8d17c2` | 328 / 7 | [147144,148433) | 0 |

| `e480feaca7a078d31df4f7950cc52f31ad033f6f97860c8a0736defeb896b2e5` | 1013 / 20 / 2 | `1dd1d84746f2abede75747b9afe5c2ce1976a2a37a46b66cc99a225b99874819` | 328 / 7 | [132253,133266) | 0 |

| `e745c85b96f2c8779a7fc1a21929777d842b8d3bb9a5275eb830a259b00d7809` | 1540 / 38 / 1 | `5c4bb38b65458deb31d30fe29bdf95d4a8c47568d20330f27ed6a587d1688843` | 328 / 7 | [176010,177550) | 0 |

| `e7da2f86ca00d50903f357df9f4cccbff5ace39e6bf76e31c4e2aa4e9a43ace6` | 1100 / 13 / 2 | `73f2ca2ec5c49f4e4affc62ae0f1e6a2a0743556cace03fae0197d5440d8f958` | 328 / 7 | [183257,184357) | 0 |

| `e8ab8fa05569b7b2122e4698c69dd80daa091a95618bddc1d5ad8284def98fe9` | 1990 / 35 / 2 | `3f5ce218e09a6ab555da5fe87fc54fade2f64a2b76a2b05cb018fedc92019a4d` | 328 / 7 | [109261,111251) | 0 |

| `e9653086318238988a2627362c9a4ea8e66781f18529c4d26f231284b5dab1a7` | 132 / 4 / 2 | `e58ceb878599d4e45dd5eb0e1582a866bbd614d1accb7c3bbfc4e0d8e1dc9160` | 485 / 10 | [22652,22784) | 2 |

| `e97468478160606685c27683e3cf5eb8fc135a60507d28a9d8c5dd7bf10126a7` | 89 / 4 / 2 | `768ec1dcd31a447845ef859103cab5a4e0dbdc408cb68068c9448c3f3757224c` | 485 / 10 | [78356,78445) | 2 |

| `e9d59795afa3818682e3382c316172604062f9a82a110c1e268282e071181391` | 1922 / 44 / 2 | `976097feab2e852b14a4df417cf7e8d253da71eb1d63402adee6a1de6bdec718` | 328 / 7 | [210763,212685) | 0 |

| `ea11c7f44d754908aeacde909437e3b3e0bee73523fd87fa2793d7251ffa2042` | 1644 / 53 / 2 | `1a569ad43c7d87f794e9afa24ad303ae3de99fe27cfa1ac20108ea980632c47a` | 627 / 12 | [767,2411) | 4 |

| `ec8fc11c3c10e16412476b5cc8ab7d64568ad9d85fc18db0eeed2133bf1306c5` | 2017 / 39 / 2 | `59f15f602c5ad9c4cc358fb10da6c659c7449e5596c3e8ecab86f8284afbf3d1` | 485 / 10 | [9069,11086) | 2 |

| `eecc9faf881e0b13412955c064d7efeae56e3f8d4802aee6aba9219bd9fc21ed` | 182 / 2 / 1 | `48ba06b5fa2e4c1fe279f9e26326f13b1dd174f98e3bdb7ea52439a0dccfa4dd` | 328 / 7 | [140735,140917) | 0 |

| `eef6d5b4b6f8c83fc6373671d8669180d0af8f5ca1257c1d8a0921a5da251d3d` | 988 / 19 / 2 | `86deea97eca4c403a2494f5ff9bec230978fbe3c4f95e0a52bc828a8efcf3dfe` | 328 / 7 | [149553,150541) | 0 |

| `efea62d5ed260e534ed484696fb347010b827f5e0cf9fb32d75579ac12707808` | 54 / 2 / 2 | `455215b8c47ca1d04599d796dbf19ec43a43a0d48edc273fca8f2af3b7193e15` | 328 / 7 | [22652,22706) | 0 |

| `f00044b46ba4ef1706b1ce80b6a0e978c4153b7408ec2ad8837de98a370512f9` | 69 / 2 / 2 | `053410ead180f22dd5792fcd041177c9f96ed2b89df77c905d33e884e70ae456` | 328 / 7 | [183110,183179) | 0 |

| `f153cd2ebe554bbc97bd5b4f69b5ef137a9c16967da98f9fd80c149706449b67` | 657 / 11 / 2 | `86528de192ab8f70d6d73e8e7a8d3d43c17ccdcfc487ebaa9ea2beb0b49c2b58` | 328 / 7 | [157513,158170) | 0 |

| `f1914051a2305a19e562b367300ce86ebc9a03f9b769e9e96fcf6554484b7fe6` | 704 / 26 / 2 | `b87408e55cf30f7527a613cc8a2f8987e679969bb9239420a0c5865a3717153b` | 328 / 7 | [6602,7306) | 0 |

| `f1f77207ae9594b018e67726e649e13202b3e507982c9b1449eb6860ba30ac4b` | 817 / 21 / 2 | `dca6d64b221c00d4b1b27caa1ee55b513966e42ac50ee276899a2635db0a8a86` | 328 / 7 | [192751,193568) | 0 |

| `f2638303e2ec5c8083edbac9c9a62444bf158d81140924505a70155e6966d769` | 886 / 18 / 2 | `a82b1252dabead861510a735ff26cc6cd70a2ac351908a10cd8d1da636a22bb3` | 328 / 7 | [24546,25432) | 0 |

| `f36bce745e8a468af61fba836ca00ed48a0821de4eedc1ed663a955dcad3c5d2` | 783 / 21 / 2 | `3e8378623aa318a252820086abd6a1040dc11bbe576bf0bbeed0b56c5a1e5275` | 328 / 7 | [117336,118119) | 0 |

| `f541cd49120d9464fa7c888b2aacecdca5fa636edf6ceaa77bb70c855b5fabac` | 593 / 9 / 2 | `a617473f6d8e49146f2d0a29fbb0d784f4b2198e4e0aa38eefb16f8a8c0064b2` | 328 / 7 | [181841,182434) | 0 |

| `f54a243857d9b8bf637d7c02a95e17fc02b217741781c3e595342a18b2004e4e` | 965 / 23 / 2 | `b2bb7506a72e709adf60961837b7fbb47f10fdebe725414e650c62ee99398aff` | 328 / 7 | [197646,198611) | 0 |

| `f6008de45128e5b1c775932a328e64e5ba080dd2f05c90a5c3ca8df8afb07d7f` | 153 / 4 / 2 | `4cdd08a0b0eb6a55f41aceabe2e9017380a5ee1fae1b1c13ee60318d594a3263` | 485 / 10 | [162836,162989) | 2 |

| `f755864fff62e1e2cf5be7e960dc1e8d3d94f16190e114aeee05501bb519d85c` | 2697 / 50 / 2 | `a7d71462efa8e0dd3867d418bc2da706337318daba0a65b60ee860a0abacbe6c` | 627 / 12 | [68968,71665) | 4 |

| `f7d5a3098ec464365e29b2d5496308075b468713aa09d069ab8695476b8bc5c6` | 1646 / 45 / 2 | `5c8e589b931e740a094c18bc86c29c27efa6ac16b42e7fa1b814bfb779e99f4a` | 627 / 12 | [60023,61669) | 4 |

| `f997dd3619c188b83af714ffd2b7d80e70039afd2d0e80180009b714318a4cee` | 2036 / 13 / 2 | `cb05f7e31586a98ff8a799cab044db1ac6a941dd1f647e43119ae4c7d5edab66` | 328 / 7 | [111251,113287) | 0 |

| `fa626ce4ddc2af256f0c8772d5e924b8ef474971ef8e94372ac8232bc8f1ac4b` | 1119 / 28 / 2 | `d4efa731c96f330494cc0ee0b3f4dd495e2653a749b33dfd0b97c64f42c94e3d` | 328 / 7 | [103156,104275) | 0 |

| `fae5d7f24ecdbec2a17ec2d9ceb7d2e072324bd7f7f5009c50ba326df72d7c9b` | 75 / 2 / 2 | `23f595ade7092d03d2827519019574bf55260aedb7edb88e5c9f3f1e71568a44` | 328 / 7 | [162836,162911) | 0 |

| `fbac8ff148667978d6bca1785d879bae872db416cf7fad45ff6ee0258d9decba` | 974 / 15 / 2 | `2cba09d9cef67d736dafc419d8dc8bc2a379bcb22c950f43047c6baa46daa1bb` | 328 / 7 | [40966,41940) | 0 |

| `fc378f50e6baa94971242101e973f5951df9d314cc99dd90abb246f11cccbaf8` | 895 / 23 / 2 | `66cff34351fa43b9a17ba8f3a5d464cbb3227a16ff4659f2d8208db78cdd0e53` | 328 / 7 | [172096,172991) | 0 |

| `fe749c39ff4004dc12b2c8354949d9d623d5c1b2414610cd2baa148907c85b73` | 1060 / 30 / 2 | `c8d6ae95eefa8a32a5adc66c5acd6d1e45135059025666a2ef878afbc6a7bf8f` | 328 / 7 | [172991,174051) | 0 |

| `ffd7688639d99a67f93d3a870cc363723e5298ea15bb0cb61ef7c01f897891e0` | 448 / 6 / 2 | `0327e76dd45a72660e8eac21e7caba129fdff85f44ae94bf91f309b6ddf565dd` | 328 / 7 | [90161,90609) | 0 |


### Observed failures, exits and process limitations

The following are implementation/representation-tool failures, not failed mathematical theorems. Captured child exits take precedence over wrapper success; an unknown original exit stays unknown.

- Scratch migrate.py selectors; exit(s) [1, 1]: Ambiguous global selectors for 另实际取回 and 另实际取回 NIST DLMF. Bound selector to original source line 5343 before applying the final representation.

- Read-only rg search; exit(s) 1: zsh could not expand Meta/Digestion/sources*. Used a corrected scoped search; no repository mutation.

- Scratch migrate.py parse; exit(s) 1: Python interpreted a literal backslash-xi as a malformed hex escape. Used a raw string before applying the final representation.

- Initial prepare verification wrapper; exit(s) null: Wrapper printed output without retaining the running session handle; no reliable final exit captured. Scoped pgrep -fl verify_representation.py exited 1 with no process; later captured verification results are separate runs, not a reconstructed original exit.

- Captured prepare-check; exit(s) 1: Five apparent coverage gaps: two draft metadata-ordering issues and three heading-only structural units. Fixed before ingest. prepare-check-r2 and prepare-check-r3 both exited 0.

- Initial git diff --check; exit(s) 2: Three source trailing spaces after suffix archival; archived exact fragments ending in spaces; report blank EOF. Source spaces became mapped archive spans; exact archive fragments received external end markers. Final evidence append changes the report EOF without altering archived bytes. Final diff-check outcome is recorded separately.

- First canonical-audit; exit(s) 1: Audit incorrectly required the interval after 24.5 through a peer heading to be a single CAS. Corrected audit grammar, keeping nested versus peer boundaries and separate composed intervals. canonical-audit-r2 exited 0. No source change or repeated ingest.

- Finalization read-only mapping inspection; exit(s) 1: Inspection assumed permanent_reservations members were objects; actual members are strings. AttributeError: str object has no attribute items. Corrected the read-only inspection to inspect actual value types; next invocation exited 0. No source/report/map mutation from the failed inspection.

- Bounded-output presentation; exit(s) 0: Some prerequisite and finalization tool presentations were truncated, including an accidentally expanded nested canonical mapping. Required prerequisite text and needed mapping fields recovered in bounded projections. No opaque logs were read; the full mapping was programmatically parsed.


Captured structural-verification receipts: `prepare-check` 1; `prepare-check-r2` 0; `prepare-check-r3` 0; `post-representation` 0; first `canonical-audit` 1; `canonical-audit-r2` 0; initial `source-diff-check` 2; final source-only diff-check 0. The successful post/final checks do not erase earlier failures. The final full diff-check and final report/map recovery checks are recorded in the runner evidence after this append.

The user-visible cumulative GoalArtifact contained a literal truncation region. The complete assigned brief was recovered after editing and the single ingest. Full prerequisite-before-actions compliance therefore cannot be claimed for that cumulative text. Direct I31 instructions and supplied authoritative clauses governed all edits. No historical navigation/command in recovered text was executed.

Assigned full brief: 252365 bytes, SHA256 `c27f19609015a92077cf017e2904556dda9e787b099be878ec26da7b26245799`. Complete local CLAUDE, agents/CONTEXT and pinned beta.42 SKILL/CODEX_WORKER_SPEC were read in bounded chunks before editing; current caller-authoritative clauses govern the old snapshot. This does not repair the chronology limitation for the cumulative GoalArtifact.

Caller-authoritative C89 corrects the prior deployment claim: C82 attempt 1 already used macstudio3-trureturing, pool_id 10ad7e89-dd40-4278-a77c-42542b53fd59. C88 changes to a single-file attachment with a 2607-byte composer prompt and omits the old mode:work tag on that previously used deployment. Neither original C82 failure/budget nor live C88 task/attachment bytes are changed. C88 has caller retry_budget 0; no access/model identity/proof is inferred from waiting_response.

CPU operations were fixed representation/byte/JSON/YAML/Git verification and necessary canonical orchestration. No new mathematical program, certificate, test, old ingest, fixed-xi or pilot replay, candidate generation, symbolic/numeric search, GPU dispatch, runtime campaign, daemon, Lean operation, dependency installation, or separate broad build/preflight/cache operation was launched.

The authorized make ingest invokes dotnet run --configuration Release. Its intrinsic build/restore/startup, producer-owned per-worktree lock and atomic YAML behavior belong to that invocation. No process-tree or host-wide side-effect tracing was performed; absence of ignored caches or unrelated host activity is not asserted. No host cleanup was attempted.

Used already-installed PyYAML to parse actual schemas, including receipts.chain_atoms; no package installation.

Only assigned worktree, its pinned Git objects, three expressly supplied I27 fidelity views, prerequisite skill/spec, and own attempt input/artifacts were used. No neighboring physical target, peer implementation/process evidence, worker log, log_ref contents, last-message, caller transcript, broad task registry or unlisted temporary input was consumed.

No stage, commit, push, branch mutation, rebase, merge, PR action or make pr. Caller owns lifecycle; final tree remains unstaged on pinned HEAD. No source edits after the single canonical ingest; report/map finalization is append/metadata only.

No automatic approval rejection was observed. Final implementation evidence remains fallible self-inspection. The exact Gram proof dependency, caller seal/audit, complete composed independent review, ordinary gates, faithful downstream integration and ordered S19-through-S25 MERGED remain outstanding. This partial migration is progress toward the unchanged full goal and is not an accepted whole-book result.


## S19 complete proof adoption (C94 / I33)

The active mathematical source now contains complete proofs at 30.22–30.51. This is source preparation, with the general complex singular cases, infinite endpoint/nonattainment distinction and all finite rational-certificate quantifiers preserved. The original envelopes remain immutable caller inputs; this report does not reproduce them.

The mathematical authorship is the recovered actual-PRO C88 proof, corrected by all five C90 items and incorporated unchanged by valid C92, together with recovered C93. C88 original task 7da5f586-e75f-4b16-9971-e8cb8ed73725 and C93 original task 604cbba9-113f-4371-b804-0977c4534969 remain failed carriers without a mathematical rejection. Their recoveries are 6700a985-d020-4e3e-afce-31675e057216 (conv_45d699acc8264d78) and 16e953cc-6dc4-4cef-9205-0acf6b9177bf (conv_1aded136c3f591e2). C90 task 474db6d9-2b27-4cf5-86fe-152eda16d7f8 completed the mathematics but its caller-origin null-log_ref defect leaves that formal flight abstained; C92 task 9661f1d7-961b-4764-afa0-d994993266eb repaired packaging, without changing its proofs or budgets. C88's deployment correction and I31's late cumulative intake remain recorded in the immutable report prefix.

The supplied visible envelopes are the exact available primary inputs; unavailable original author serialization is not reconstructed. Actual-PRO attribution rests on supplied task evidence, with hidden serving identity ASSUMED-UNVERIFIED and no model-diversity claim. The Baez-Duarte Theorem 1.1 normalization uses the supplied primary and caller original-paper check; this implementation made no fresh literature retrieval. The full cumulative brief/GoalArtifact, current authority snapshot, local instructions, pinned beta.42 skill/spec and every supplied envelope/supporting input were read before target mutation; the attempt intake receipt records the distinction between initial byte reads and completed semantic intake.

The new adoption map is the single authoritative inventory of exact input identities, proof-to-primary correspondence, source addresses, changed bytes, canonical pairs/chains and recovery bindings. The older I31 map is an immutable earlier snapshot. Existing mathematical hypotheses, proofs, tables, numerical-evidence qualifications and open questions remain active; the source changes below close the old Gram obligations and remove process wording while retaining its mathematical scope. Mathematical software, performance guarantees, formalization, RH resolution, global certificate-success bounds, independent review, downstream integration and ordered delivery are not established by this implementation.

### Inactive byte-exact source fragments

These archived fragments are historical, not active hypotheses or pending obligations. Delimiter lines are external to each preserved span; the map records exact boundaries, including the protected 1253-byte Gram subspan.

I33 archive 01.

````text
证明的有限核对说明：这些是精确抽查;全称命题由上面的构造和不等式证明承担。它本身没有证明实际 ξ 序列在每种分辨率上都失败。
````

I33 archive 02.

````text
**未证数学目标（原文整体保留）。** 下列距离算子目标仍待完整证明；不作为已证定理或假设使用。

### PRO 提供的下一篇纸面目标: 距离的算子实现

以下留作后续附录目标,本轮不宣称已完成新的谱判据。使用第 3 节的 \(\mathcal H,\chi,f_k,D_N\),在 \(\ell^2(\mathbb N_0)\) 的标准基上设

\[
h_0=\chi,\quad h_k=f_k/k\ (k\ge1),\qquad T e_k=h_k.
\]

因为 \(\|f_k\|_{\mathcal H}^2=\|f_1\|_{\mathcal H}^2/k\),且 \(f_1\) 在 \((0,1]\) 有界、在 \((1,\infty)\) 等于 \(1/x\),候选合成算子 \(T:\ell^2\to\mathcal H\) 的 Hilbert-Schmidt 范数平方为

\[
1+\|f_1\|_{\mathcal H}^2\sum_{k\ge1}k^{-3}<\infty.
\]

正确的正迹类对象是 **\(A=T^*T\)**,作用在 \(\ell^2\);不能写成类型不匹配的 `A=TT`。若 \(P_N\) 投影到 \(e_0,\ldots,e_N\),令 \(A_N=P_NAP_N\) 视为有限矩阵,待系统写明的目标是

\[
D_N=\sup\{\delta\ge0:A_N-\delta e_0e_0^*\succeq0\},
\qquad \mathrm{RH}\iff\inf_{N\ge1}D_N=0.
\]

目标必须使用全半轴范数,并处理有限 Gram 块奇异时的距离与减秩阈值;不能依赖未经证明的可逆性。缩放 \(f_k\mapsto f_k/k\) 不改变任何有限线性张成空间。即使上述实现全部写成证明,\(A\succeq0\) 本来就由 \(T^*T\) 自动成立,RH 内容仍在距离阈值趋零的全局条件,不会因“已有正算子”自动解决。


````

I33 archive 03.

````text
第 7 节其它算术桥、物理检测与 距离算子义务仍 open。
````

I33 archive 04.

````text
和所有历史记录保持有效
````

I33 archive 05.

````text
本地对照范围是本卷第 1-26 节,没有作全库或文献的穷尽新颖性断言。
````

I33 archive 06.

````text
后来的整箱全薄层邻域、实际 5040 箱体和第三素数射线问题均不进入本层。
````

I33 archive 07.

````text
后来的 \((2,3,7)\)、实际 fixed5040、translated5040 和第三素数射线结果不属于本层。
````

I33 archive 08.

````text
本节专门的八节点、裕量、扰动组合及格点应用当前标为 repo-derived,
没有以历史的未评定原始措辞作为现行 provenance 标签。
````

### Adoption evidence and scope

The single authorized ingest exited 0: residual_open_added=40, skipped_existing=197, coarse_fallbacks=0, open_genres=0, cas_objects_written=40. The source was frozen before that invocation. Structural verification binds all 228 current whole units and their ordered chains; each newly emitted pair is accounted for. Exact current and pre-I31 source recovery, the protected Gram archive, the original report prefix and bounded historical bindings are independently described in the map. Producer-owned CAS/YAML/LF bytes were not repaired or normalized.

CPU activity was structural text/JSON/YAML/Git verification and intrinsic ingest orchestration only. No mathematical program, test, search or historical replay was executed. The map retains the pre-write scratch failures and corrected exits; they are representation failures, not rejected mathematics. No source edit followed ingest. All changes remain unstaged on the assigned BASE; implementation supplies no independent-review verdict or approval and does not complete the continuing goal or downstream delivery.

Authoritative adoption map: [theory-proof-adoption-s19-0910.json](theory-proof-adoption-s19-0910.json), SHA256 `9abba55e13c08d0f784a6c958416c5cfb4245872ad087ccba2f385469f23a8ec`. The result envelope binds the full final source, report and map identities.
