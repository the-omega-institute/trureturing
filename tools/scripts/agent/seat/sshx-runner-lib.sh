#!/usr/bin/env bash
# 共用:解析本机已安装的 sshx codex runner。**只供 source,不供执行。**
#
# 立库依据(第 4.2 条 唯一真源):这段解析此前只存在于 seat/dispatch.sh,而
# openproblem/op-resume-seat.sh 走的是另一条路 —— 把版本**钉死**在
# `.../consensus-rnd/1.0.0-beta.42/skills/sshx/scripts/run-codex-worker.sh`。
# dispatch.sh 的头注已经记过这个缺陷是什么样子:钉死的路径**不会有任何症状**,
# 老路径还在,脚本照常退出 0,于是每一席都跑在钉死的那一版上,直到那一版被清掉才炸。
# 2026-09-12 本机实测装了五个版本(beta.31/.32/.36/.37/.42),beta.42 恰好在,
# 所以 op-resume-seat.sh 此刻**没有**坏 —— 它是同一类的潜伏缺陷,不是当下的故障。
# 把解析放进一个库,而不是把它抄第二份,是因为抄第二份正是第 4.2 条禁的第二真源。
#
# 契约:resolve_runner <plugin-root> -> 打印 runner 绝对路径,退出 0;
#       找不到即 return 1,**绝不回退到任何猜测路径**(第 2.1 条 fail-closed)。
# 版本序必须用 `sort -V`:纯字典序会把 beta.9 排在 beta.42 之后。

SSHX_PLUGIN_ROOT_DEFAULT="${SSHX_PLUGIN_ROOT:-$HOME/.claude/plugins/cache/consensus-rnd/consensus-rnd}"

resolve_runner() {
  local root="$1" newest
  newest=$(ls -d "$root"/*/ 2>/dev/null | sed 's|.*/\([^/]*\)/$|\1|' | sort -V | tail -1)
  [ -n "$newest" ] || return 1
  local candidate="$root/$newest/skills/sshx/scripts/run-codex-worker.sh"
  [ -f "$candidate" ] || return 1
  printf '%s\n' "$candidate"
}
