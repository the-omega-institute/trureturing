# SFT 第 29–35 节的有限核验与来源

本目录随 PR #8336 的原理论卷增补一起提交。唯一理论正文仍为 `../../RECURSIVE_RELATIONAL_OBSERVATION_SFT.md` 的第 29–35 节，没有另立重复理论卷。

## 写回基线

2026-09-25 写回从 head `c76b364d82bce381b548497ace59e7c3ed5b8080` 出发，原理论正文 blob 为 `924816d195659553e6982bdad883d3b05eff1316`。保留该基线第 1–28 节，只在末尾追加既有交付的第 29–35 节及写回补记。新正文 blob 为 `f388dbed71cf36a1fb94ac76e517ce9183ce0a2e`。预提交比较显示正文新增 534 行、删除 0 行。

初稿在第 29、35 节记载的旧 head、只读接入和未提交状态属于初稿形成时的历史记录；第 35 节的写回补记记录本次发布基线。本目录的文献清单保留初稿查阅时间和当时的远端 Library 写入标志，这些历史字段不描述本次 Git 提交是否成功。实际提交由 Git 历史确认。

## 复现

使用 Python 3.10 或更新版本，只依赖标准库。不要使用 `python -O`，因为有限检查采用 `assert`。

```sh
cd docs/develop/theory/support/rro_sft_29_35
python3 verify_partition_closure.py --output verification.json
python3 verify_fixed_c2_closure.py
```

第二个脚本直接导入同目录的第一个脚本，并在同目录重写 `fixed_c2_verification.json`。两个脚本均不联网、不调用 Lean、不修改远端，也不修改 CI。

## 实际重跑

2026-09-25 在本次写回会话中再次执行两个脚本，结果与原交付 JSON 一致。上传的两个 Python 源的 Git blob 与本地执行文件逐字节匹配，结果 JSON 记录相应 SHA256。

`verify_partition_closure.py` 返回 `ALL_PARTITION_AND_PATH_CLOSURE_CHECKS_PASSED`：穷尽 n≤12 的 12647 个有序分拆对及独立 BFS 距离检查，验证 33794 个构造路径步骤、3098 对相邻块因子；另检查正文规定的有限群代数案例和种子确定的路径样本。长链路径样本部分不是穷尽。

`verify_fixed_c2_closure.py` 返回 `FIXED_C2_TWO_STEP_CLOSURE_CHECKS_PASSED`：原样 2→3→2 因子链，两侧兼容输入各 1024 个，双向五边窗口恢复各 131072 次。一步不可能性的全称结论由正文整除证明承担，不由有限奇偶枚举承担。

## 证明地位

本批发布的是书面数学证明、有限 Python 核验和来源记录。没有新增 Lean 或 Scribe 源，没有运行或改动 CI、消化和冻结流程，没有独立第二模型审稿。已有 PR 的机器验证结果不得外推为第 29–35 节已经形式化。

`literature_ledger.json` 保留精确查阅范围。基本 AB/BA 块结构和二分图编码属于既有文献接口；正文自行证明的组合结果不宣称全球首创。
