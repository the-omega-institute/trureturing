# A392714 层 3 后半：Φ(n) 尾词归约实施报告

## 预登记与文献核验

档位为第二档研究线第 3 层，`admission_basis: escape-witness`；拟议见证是 Φ(n) 到编码词的保号对应本身。该对应不是层 2 或层 3 前半的实例化结果。联网核验了 `https://arxiv.org/html/2605.11137v1`：Remark 4 将奇偶差明确写作 conjecture；正文给出前缀量 `T_k` 与固定首项，但没有无权符号和证明。本轮没有把猜想写成 Lean 假设。

## 本轮已证

新增 `D5/S1/Words/Compositions/PhiTailEncoding.lean`，定义了零基 `suffixBudget`、`admissible`、`phi`，以及 Φ(n) 合格排列的倒序尾词 `tailWord`。对 `1 ≤ n` 已核验：

- `tailWord_length`：尾词长度为 `2*n-1`；
- `tailWord_entry_bounds`：若排列固定零点，则每个尾词字母严格落在 `-(n:ℤ) < w < n`；
- `mem_phi_tailWord_bounds`：Φ(n) 成员自动满足上述界。

第二条使用排列单射性和固定零点排除值 `0`，因此实际字母范围收紧为 `-(n-1), …, n-1`。这些定理把 Φ 的尾部数据接到了前半使用的整数词域，但没有声称词的前缀非负性。

## 未闭合缺口

仍缺三条独立桥：

1. `admissible p` 与 `Good 0 (tailWord n p)` 的一般等价（需处理后缀求和、倒序和边界 `k=2n` 排除）；
2. 固定位置块交换的未配对词分类，及其与 `alternating (ofFn a,b)` 的满射性；
3. 尾词排列的 `Equiv.Perm.sign` 与编码权重 `signInt a * signInt b` 的保号等式。

因此不能由 `encoded_product_sign_sum` 推出 `Target`，也没有加入任何待证假设、`sorry` 或私有公理。按三态结算，本轮为 **blocked（部分已证）**，最锐剩余子命题是第 1 条的 `admissible ↔ Good`。

## 门链收据

本轮新增单元通过：

`bash tools/scripts/agent/serial-lean.sh /Users/chronoai/trureturing-a392714bridge`

输出：`SERIAL_LEAN status=complete built=6 failed=0 missing=6`。

随后按要求运行 `make lean-report`、`make emit`、`make deposit-uncovered GID=D5/S1/Words/Compositions/PhiTailEncoding`；具体退出码与 axiom 闭包以终端日志为准。未使用 `native_decide`，未修改冻结模块。

最终收据：`make lean-report` 退出 0（delta changed=1, added=0, recheck=1）；
`make emit` 退出 0，`emitted: 0 changed blueprint(s)`；
scribe-content-checks 的判词为
`DESCRIBE_STATUS ... status=classified ... red=0`，markdown 为 `judged=1 formula(s)=3 red=0`。
`make deposit-uncovered` 以
`PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED ... reason=NO_ATOM` 结束，模块已冻结且无覆盖 atom。
