# 固定素数实薄层:常量输入证书与前瞻有限设计

本报告配套 [源卷第 26 节](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md),产地为 caller 的 consensus-rnd:sshx 编排下 Codex CLI I9 source implementation。数学来自两份已完成的实际 GPT PRO 顺序 primary,不是独立评审共识。I9 只读取获准 conclusion、完成元数据和 caller 核验材料,未追读 log_ref 或 peer 工件,未派子 agent/oracle。状态为 PAPER_ARGUMENT / repo-derived 及有界常量核验,不作新颖性、Lean 冻结或一般素数域符号声明。

输入 [prime-slab-corner-order-0909.json](prime-slab-corner-order-0909.json) 原样复制自 caller 的 prime-corner-order-input-0909.json,恰为 6741 字节,SHA256 为 9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672。它是常量输入,没有搜索输出。核验范围为 56 个递增三元组、每行八个 mask/整数乘积和下列设计常数;指数箱体生成/执行数为 0,解析测试行执行数为 0,CPU/GPU 候选实验为 0。

对递增素数三元组 \(p_0<p_1<p_2\),唯一未定子集比较为 \(p_2\) 与 \(p_0p_1\)。bit \(i\) 选择坐标 \(i\),bit 0 最低;次序分别为 [0,1,2,4,3,5,6,7] 或 [0,1,2,3,4,5,6,7]。每个指数箱体的角点乘积是常量子集乘积乘同一个正整数 \(B=\prod_i p_i^{b_i}\),故核验这 56 行不需要生成指数箱体。

前瞻域为素数 [2,3,5,7,11,13,17,19] 的 56 个字典序递增三元组,独立指数 \(b_i=0,\ldots,15\)。令
\(\mathrm{box\_id}=4096t+256b_0+16b_1+b_2\),共有 229376 个箱体。每箱 25 槽:\(0\ldots6\) 对应相邻 \(s=\mathrm{slot}+1\);\(7\ldots24\) 令 \(r=\mathrm{slot}-7\),对应反射 \(j=1+\lfloor r/3\rfloor,\ i=r\bmod3\)。稳定行号为 \(\mathrm{row\_id}=25\,\mathrm{box\_id}+\mathrm{slot}\),范围 0..5734399。

| 设计量 | 精确值 | 含义 |
| --- | ---: | --- |
| 相邻 RAW slots | 1605632 | \(229376\cdot7\) |
| 反射 RAW slots | 4128768 | \(229376\cdot(6\cdot3)\) |
| 全部 RAW slots | 5734400 | guards 前总数,不是幸存或执行数 |
| 每箱上界 | 25 | \(7+6\cdot3\),不保证每箱全部通过 |
| 最大操作数界 | \(19^{102}<2^{510}\) | 其精确 bit_length 为 434 |
| limbs | 64 | base 256,共 512 位的前瞻表示 |
| 最大 limb 乘加 | 4863 | \(255\cdot19+18\),新 carry 至多 18 |
| 24 项缩放尾界 | \(3/104857600\) | \(6\cdot2^{-23}/25\),只含截断误差 |

相邻对的 \(e^{T_0},e^{T_1}\) 为 \(R_{s-1},R_s\),guard 为 \(R_{s-1}>5040\)。反射对令 \(X=PR_{j-1}\)、\(E_i=p_i^{3(2b_i+3)}\),则 \(e^{T_1}=E_i/(P^2R_{j-1})\)。全部 guards 是
\[
R_{j-1}>5040,\quad p_i^{3(b_i+1)}<X,\quad X^2<E_i,\quad
P^2R_{j-1}R_j<E_i<P^2R_{j-1}R_{j+1}.
\]
其它素数的指数为 \(-(b_l+e_l^{(j-1)}+2)<0\),所以反射上端点恒非整数。同一固定箱体内的不同幸存预算对不重复,由唯一分解证明;row_id 始终保留箱体身份。整数 guards 不决定解析差值 \(G\) 的符号。

位宽证明为 \(R_s\) 每个素数指数至多 16,\(PR_s\) 至多 17,\(P^2R_sR_l\) 及 \(X^2\) 至多 34,共至多 102 个不超过 19 的素因子;\(E_i\) 指数至多 99。重复小素数乘法满足输入 carry \(\le p-1\Rightarrow\) 输出 carry \(\le p-1\),所以每次 limb 乘加至多 4863。这是设计界,没有测试或断言实际 MPS 整数操作正确。

I9 从仓根实际运行以下自含检查,退出码为 0,全部断言通过。它只依赖 Python 3 标准库,只计算 448 个常量子集乘积、25 个槽的指标映射和固定整数/Fraction 常数,没有指数循环、浮点 \(G\) 求值或候选生成。

~~~python
from pathlib import Path
from itertools import combinations
from math import comb, prod, isqrt
from fractions import Fraction
import hashlib
import json

path = Path("docs/reports/prime-slab-corner-order-0909.json")
raw = path.read_bytes()
sha = hashlib.sha256(raw).hexdigest()
assert len(raw) == 6741
assert sha == "9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672"
data = json.loads(raw)
primes = [2, 3, 5, 7, 11, 13, 17, 19]
assert data["schema_version"] == 1
assert data["kind"] == "constant-prime-corner-order-input"
assert data["primes"] == primes
assert data["search_executed"] is False
assert data["exponent_boxes_generated"] == 0
assert data["triple_order"] == "lexicographic increasing prime-list index triples"
assert data["mask_convention"] == (
    "bit i selects prime at coordinate i; bit 0 is the least significant bit"
)
assert all(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))
           for p in primes)
triples = list(combinations(primes, 3))
assert len(data["rows"]) == len(triples) == comb(8, 3) == 56
for index, (row, triple) in enumerate(zip(data["rows"], triples)):
    assert row["triple_index"] == index
    assert row["primes"] == list(triple)
    products = [prod(triple[i] for i in range(3) if mask & (1 << i))
                for mask in range(8)]
    masks = sorted(range(8), key=products.__getitem__)
    p0, p1, p2 = triple
    assert p2 != p0 * p1
    expected = ([0, 1, 2, 4, 3, 5, 6, 7] if p2 < p0 * p1
                else [0, 1, 2, 3, 4, 5, 6, 7])
    assert row["sorted_masks"] == masks == expected
    assert sorted(masks) == list(range(8))
    ordered = [products[m] for m in masks]
    assert row["subset_products"] == ordered
    assert all(a < b for a, b in zip(ordered, ordered[1:]))

assert [slot + 1 for slot in range(7)] == list(range(1, 8))
reflected = [(1 + (slot - 7) // 3, (slot - 7) % 3)
             for slot in range(7, 25)]
assert reflected == [(j, i) for j in range(1, 7) for i in range(3)]
boxes = comb(8, 3) * 16**3
slots = 7 + 6 * 3
assert boxes == 229376 and slots == 25
assert 4096 * 55 + 256 * 15 + 16 * 15 + 15 == boxes - 1
assert (boxes * 7, boxes * 18, boxes * slots) == (
    1605632, 4128768, 5734400
)
assert 25 * (boxes - 1) + 24 == 5734399
assert 3 * 34 == 102 and 3 * (2 * 15 + 3) == 99
assert 19**102 < 2**510 < 256**64 == 2**512
assert (19**102).bit_length() == 434
carry_max = 255 * 19 + 18
assert carry_max == 4863 and carry_max // 256 == 18
tail = Fraction(6, 25 * 2**23)
assert tail == Fraction(3, 104857600)
print(json.dumps({
    "certificate_bytes": len(raw), "certificate_sha256": sha,
    "constant_rows_checked": 56, "subset_products_checked": 448,
    "prospective_boxes": boxes, "raw_slots": boxes * slots,
    "guard_bound_bit_length": 434, "limbs": 64,
    "carry_max": carry_max, "tail_exact": str(tail),
    "exponent_boxes_generated": 0, "analytic_rows_executed": 0
}, sort_keys=True))
~~~

级数依据是 \(f(x)=-\sum_{n\ge1}e^{-nx}/n\) 的绝对收敛。六个可行排列混合的最大值精确等于 \(D\);每个混合删掉零质量后质量总和为 3。共同认证下界 \(\ell\ge\log2\) 可取 \(c_{\min}\) 或 \(\log2\)。令 \(Z=e^\ell G\)、\(S\) 为六个排列的缩放 24 项和的最大值,则
\[
|Z-S|\le\tau(\ell)=\frac{6e^{-24\ell}}{25(1-e^{-\ell})}
\le\frac{6\cdot2^{-23}}{25}=\frac3{104857600}.
\]
统一误差界在取最大值后保持。整数最优解及零质量删去不改变此结论。若严谨计算给出 \(S\in[S_-,S_+]\),用 \([S_--\tau_+,S_++\tau_+]\) 包围 \(Z\):上界 \(<0\) 证负、下界 \(>0\) 证正;仅接触零支持相应弱符号,不证明等号;横跨零为 unresolved。

这个尾界不覆盖浮点输入、距离分支、fractions、clipping、求和/最大值、MPS roundoff、融合操作、下溢或超越函数误差。未来须向外包围它们或由 CPU 严格认证已完成 GPU 结果,包括 GPU 非候选、每个必要排除和全部 row_id 覆盖;保留 unresolved 与 GPU/CPU 分歧。CPU 不承担持续候选生成或替代 GPU kernel。输入/程序身份、已搜范围、计数、完整分类摘要及复现命令须随未来程序保存,运行状态在仓外。

两份 primary 的实际调用事实如下;它们均无法取回钉版仓库 URL,使用完整供给定义,caller 已与交付源核对。不能声称 oracle 独立读取 GitHub。

| primary | task | conversation | 实际模型 | 完成时间 UTC |
| --- | --- | --- | --- | --- |
| 全实薄层归约 | ce312694-86a6-4a1b-8318-90c77dc28f75 | conv_264064eff69b5335 | GPT-6 Astra | 2026-09-09T13:25:33.673+00:00 |
| 活跃切换精化/尾界 | 3609e6b0-ab4d-4891-9b0f-55c613d43942 | conv_4c0b62a5e14b0f64 | GPT-6 Astra | 2026-09-09T13:47:33.577+00:00 |

以下 basename 均指 caller 获准输入目录 /tmp/qgh-boundaries-0908/,是本次读取的 provenance,不指示追读其它路径或日志。

| 输入文件 | 字节 | SHA256 |
| --- | ---: | --- |
| pro-real-slab-reduction-envelope-0909.json | 14814 | 5f551e3062515163f220d7fce433908598f5147c5060d92e56ba1292e03ec77a |
| pro-real-slab-reduction-complete-0909.json | 663 | 7d061bd1070a2fb625dee1a13a7ba1006909567564ceebed3e790806b9563f09 |
| pro-real-slab-sharpening-envelope-0909.json | 22893 | 8105875c946f2c693c8db6a6b1f789756aab75fbd4cd297293431f08f25dcc92 |
| pro-real-slab-sharpening-complete-0909.json | 664 | b4ec5cf2e71225690eff373912f6939c673fa7379ac745c4465c921b92a64bb1 |
| caller-real-slab-audit-0909.json | 2298 | 0b7851234a3683fe3ef857d70ca3e8e0df3e8185562f156959e1e93529313297 |
| caller-real-slab-literature-check-0909.json | 2268 | 9745f0ae762136f78d5beac78b92fc72229c148cda5bfa7a765cfcd87a281b05 |
| caller-real-slab-literature-extract-0909.json | 21926 | 53dbbc6448caf8282b7efcce9af141b31a77bc6795691b530325ea8e41278071 |
| caller-sharp-slab-constants-audit-0909.json | 1454 | ba74628469628d717f07b13c1c4806e16e9ffaadc7a777f6120c6e6db8c0dec2 |
| prime-corner-order-input-0909.json | 6741 | 9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672 |
| real-slab-append-gate-0909.json | 2597 | 968f10bca68394fe86a9b05cd5f94584ea08b57967469fbcf1ad0792bf727a1e |

经典归属的 caller 核对为 [HKUST Lecture 14](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf) slides 4-7 的分数背包;[Boyd/Vandenberghe Convex functions](https://web.stanford.edu/class/ee364a/lectures/functions.pdf) slides 3.4/3.14/3.24/3.25 的范数、Jensen、单调复合;[Doikov Convex Functions](https://doikov.com/teaching/orie6365-s26/notes/lecture05_convex.pdf) §5.1.3 Theorem 5.1.4,陈述 PDF p.2 / 证明 p.3 的端点最大化。三份 PDF 的 caller receipt SHA256 依次为 02a501415b8472ca147d17d6e5369d7889f7b2aeba7b9ba37082e7dbebdefa7d、c172569e16a24039ac7dd0ae9d1ee743e31eb6a9369eac38206b758cbe76903b、aed2706ef6ca94ed020d359de05be9a18784e3fc0ceb4fefef31c23c34a37f8b。本次使用 receipt 与摘录,这不是穷尽文献调查;专门化证明完整写在源卷。

派发 gate 所给事实为 S12 PR #6640 MERGED,S13 sealed HEAD 0ba660de65b4224b8734908f7d0dd178115fa377 的独立评审在派发时 pending。S14 仅在指定的 real-slabs 分支追加,保留完整 2410 行 / 144029 字节源前缀,SHA256 b9898b7df94a1d46bb2898a738b27f927b6136ea1eb7db240fafc428f84bbe36。旧 hash 不匹配的恢复 GPU manifest 不是本次输入。没有旧 witness/fixed-xi 重放、GPU 搜索、Lean 修改或冻结。无界全素数/全指数 \(k\ge3\) 比较及 RH 保持 OPEN。源摄入后仍须 caller 组织独立评审与普通门,最终 S14 MERGED 依赖 S13 MERGED;本报告不完成 standing goal。
