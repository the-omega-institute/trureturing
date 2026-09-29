# SFT 第 29–35 节的有限核验与来源

本目录提供 `../../RECURSIVE_RELATIONAL_OBSERVATION_SFT.md` 第 29–35 节的有限核验程序、结果与来源。

## 复现

使用 Python 3.10 或更新版本，只依赖标准库。不要使用 `python -O`，因为有限检查采用 `assert`。

```sh
cd docs/develop/theory/support/rro_sft_29_35
python3 verify_partition_closure.py --output verification.json
python3 verify_fixed_c2_closure.py
```

第二个脚本导入同目录的第一个脚本，并生成 `fixed_c2_verification.json`。

## 核验结果

`verify_partition_closure.py` 返回 `ALL_PARTITION_AND_PATH_CLOSURE_CHECKS_PASSED`：穷尽 n≤12 的 12647 个有序分拆对及独立 BFS 距离检查，验证 33794 个构造路径步骤、3098 对相邻块因子；另检查正文规定的有限群代数案例和种子确定的路径样本。长链路径样本部分不是穷尽。

`verify_fixed_c2_closure.py` 返回 `FIXED_C2_TWO_STEP_CLOSURE_CHECKS_PASSED`：原样 2→3→2 因子链，两侧兼容输入各 1024 个，双向五边窗口恢复各 131072 次。一步不可能性的全称结论由正文整除证明承担，不由有限奇偶枚举承担。

## 证明地位

有限 Python 核验不构成全称证明或 Lean 证书。第 29–35 节的全称论断以理论正文的书面推导为限。

`literature_ledger.json` 保留精确查阅范围。基本 AB/BA 块结构和二分图编码属于既有文献接口；正文自行证明的组合结果不宣称全球首创。
