#!/usr/bin/env bash
# 把当前 .lake/build 发布为一个不可变的、内容寻址的 GitHub Release 资产。
#
# 命名空间与 spec A14 的 `E<n>` 发布 tag 严格分开：这些 tag 是构建缓存，不是版本发布。
# tag 绑定 (toolchain, os, arch, config_sha256, sources_sha256) 五元组；同一元组只发一次。
#
# 这个归档**不是权威**：它是一个加速器，不构成独立的 admission 证据。消费侧 (`fetch`)
# 对**依赖层身份** (`toolchain`/`config_sha256`)、归档完整性与摘要一律 fail-closed;
# 唯独 `sources_sha256` 允许回退到同 config 的最近一份,差量交给 `lake build` 补——
# 那是加速器该有的形状,不是把关。
#
# 【勘误：这里曾写「永远不进 admission 信任链」，那句话是假的】
#
#   三席独立评审（#2729）一致判定它按字面不成立。归档发布的 .olean 会被 consumer 侧的
#   Lake 当作构建输入复用，canonical Lean 报告又从那个 olean 环境读声明 —— 发布者
#   **确实位于 admission 下方**。两条本以为能兜底的机制都兜不住：
#
#   ① Lake 的增量判定兜不住。`Build/Common.lean:213-223` 只在 depTrace.hash 等于
#      saved depHash 且输出存在时判 up-to-date；`Build/Module.lean:742-755` **只检查
#      输出文件是否存在，不比对内容**。故可以留一个与当前 depHash 自洽的 trace，
#      或在 trace 生成后改 olean 字节，Lake 会直接采用已存在的输出。
#   ② kernel 复核补不上 source binding。`Inspector.lean:284-292` 以 trustLevel := 0
#      调 importModules，但 pinned `Environment.lean:2242-2350` 的 import 路径直接把
#      反序列化的 ModuleData.constants 放进 Kernel.Environment，未调 replay；而且
#      **无论 trust-0 如何**，一个 kernel-valid 但来自不同源码的 olean 照样通过类型
#      检查。`inspect.sh:116-131` 又把磁盘上的 source_sha256 当独立 CLI 参数写进报告，
#      没有证明该 hash 是那份 olean 的原像。
#
#   可成立的替代不变量是：**归档不构成独立 admission 证据，且它不引入比现有 dev
#   cache / report producer 更宽的 writer 集合。** 后半句是有条件的，不是天然成立：
#   `workflow_dispatch` 曾是那条更宽的 writer 路径（`gh workflow run --ref` 取的是
#   该分支上的 workflow 版本，故 job 内检查 ref 不构成机器边界），已于 PR #2818 移除，
#   并由 `ContentsWriteWorkflowClosureTests` 钉住。
#
#   仍未落地的部分（#2729 判决第 2、3 条与 B 步）：checkout 未钉不可变 github.sha；
#   release tag 仍用可移动的 target_commitish=dev；manifest 未记 producer_commit_sha /
#   workflow_run_id；consumer 侧没有 provenance 核验。**在这些落地之前，ensure 不得
#   自动 fetch 本归档** —— 当前也确实没有，手工 target 只作诊断。
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
REPO="${STRATALINT_CACHE_REPO:-the-omega-institute/trureturing}"
VERB="${1:-}"

die() { printf 'lean-cache-publish: %s\n' "$1" >&2; exit 1; }

usage() {
  cat >&2 <<'USAGE'
usage: lean-cache-publish.sh <address|publish|fetch> [--repository DIR]

  address   打印当前工作树对应的缓存 tag 与其五元组，不做任何网络访问
  publish   若该 tag 尚不存在，打包 .lake/build 并发布为该 tag 的资产
  fetch     取回与当前工作树完全匹配的归档并解包；任何不匹配即 fail-closed
USAGE
  exit 2
}

repository="$ROOT"
shift || true
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) repository="${2:?--repository needs a value}"; shift 2 ;;
    *) usage ;;
  esac
done

[[ -n "$VERB" ]] || usage

# ── 身份 ──────────────────────────────────────────────────────────────────────
# 两个哈希来自本仓既有的唯一真源，不另算一套。
helper="$repository/tools/scripts/report/lean-report-input.sh"
[[ -x "$helper" ]] || die "input helper is absent: $helper"
read -r _address _producer sources_sha256 config_sha256 \
  < <("$helper" address --repository "$repository")
[[ "$sources_sha256" =~ ^[0-9a-f]{64}$ ]] || die "sources address is malformed"
[[ "$config_sha256" =~ ^[0-9a-f]{64}$ ]] || die "config address is malformed"

toolchain="$(tr -d '[:space:]' < "$repository/lean-toolchain")"
[[ -n "$toolchain" ]] || die "lean-toolchain is empty"
# olean 的兼容性跟 Lean 版本走而不跟平台走（mathlib 的 cache key 掺 lean-toolchain 而不掺
# platform），但整包 buildDir 的可移植性是另一回事，只由 #2542 步骤 B 的实测支持：
# Linux ARM64 产、macOS ARM64 消费，Built=0 而对照组 Built=2。
# 那次实测覆盖的是同架构跨 OS，所以 arch 仍然进 tag —— 未测的组合不得静默复用。
os="$(uname -s | tr '[:upper:]' '[:lower:]')"
arch="$(uname -m)"
slug="${toolchain//[^A-Za-z0-9]/-}"
# tag 里不含平台维度。两条独立读数支持这一点：
# ① mathlib 的缓存键（Cache/Hashing.lean:149）是 rootHash::pathHash::内容哈希::import 哈希，
#    其下载 URL（Cache/Requests.lean:293）是 "{URL}/f/{repo}/{fileName}" —— 全无平台/架构；
#    最大的 Lean 项目对所有平台发同一份 olean 缓存。
# ② 本仓 .lake/build 实测不含任何平台相关二进制：*.o/*.so/*.dylib/*.a/*.dll 计数皆为 0，
#    只有 olean/ilean/c/trace/hash/json，且 olean 的 file(1) 类型是 "data" 而非 Mach-O/ELF。
# slug（toolchain）必须保留：不同 Lean 版本的 olean 确实不兼容。
# 加上平台维度的后果是把主检出（darwin-arm64）挡在 CI 产物（linux-aarch64）之外，
# 而 owner 的目标恰恰是「主 checkout 不用从 0 开始 build 热缓存」。
tag="lean-cache-v1-${slug}-${config_sha256:0:16}-${sources_sha256:0:16}"
asset="lean-build.tgz"

emit_address() {
  printf 'tag=%s\n' "$tag"
  printf 'toolchain=%s\n' "$toolchain"
  printf 'os=%s\n' "$os"
  printf 'arch=%s\n' "$arch"
  printf 'config_sha256=%s\n' "$config_sha256"
  printf 'sources_sha256=%s\n' "$sources_sha256"
  printf 'asset=%s\n' "$asset"
}

case "$VERB" in
  address)
    emit_address
    ;;

  publish)
    [[ -d "$repository/.lake/build" ]] || die "nothing to publish: $repository/.lake/build is absent"
    if gh release view "$tag" --repo "$REPO" >/dev/null 2>&1; then
      printf 'LEAN_CACHE_PUBLISH {"status":"exists","tag":"%s"}\n' "$tag"
      exit 0
    fi
    staged="$(mktemp -d)"
    trap 'rm -rf "$staged"' EXIT
    ( cd "$repository" && lake pack "$staged/$asset" >/dev/null )
    bytes="$(wc -c < "$staged/$asset" | tr -d ' ')"
    digest="$(shasum -a 256 "$staged/$asset" | cut -d' ' -f1)"
    emit_address > "$staged/manifest.txt"
    {
      printf 'archive_sha256=%s\n' "$digest"
      printf 'archive_bytes=%s\n' "$bytes"
    } >> "$staged/manifest.txt"
    gh release create "$tag" --repo "$REPO" \
      --title "Lean build cache ${config_sha256:0:8}/${sources_sha256:0:8} (${os}-${arch})" \
      --notes "Immutable Lean build cache. Not authoritative: an accelerator only, never admission evidence. Produced from ${toolchain} on ${os}-${arch}." \
      "$staged/$asset" "$staged/manifest.txt" >/dev/null
    printf 'LEAN_CACHE_PUBLISH {"status":"published","tag":"%s","bytes":%s,"sha256":"%s"}\n' \
      "$tag" "$bytes" "$digest"
    ;;

  fetch)
    staged="$(mktemp -d)"
    trap 'rm -rf "$staged"' EXIT
    # 精确地址优先；取不到就按 config 前缀回退到最近一份。
    # 为什么必须回退:dev 约 16 提交/小时,而发布一轮 6.5 分钟起——`sources_sha256`
    # **结构性地**追不上。实测:新建 worktree 到 fetch 之间 dev 就前进了,
    # 本机要 …-02ab04b1 而当时最新的 release 是 …-6b2da53f,精确匹配当场 miss。
    # 回退是安全的:`toolchain` 与 `config_sha256` 仍严格相等(依赖层不容将就),
    # 只放宽 `sources_sha256`,差量由 `lake build` 补齐——lake 按 depHash 判 stale,
    # 旧基底里过期的模块会被重编译。这正是 mathlib `lake exe cache get` 的模型。
    resolved="$tag"
    mode="exact"
    if ! gh release download "$tag" --repo "$REPO" --dir "$staged" --pattern "$asset" --pattern 'manifest.txt' >/dev/null 2>&1; then
      prefix="lean-cache-v1-${slug}-${config_sha256:0:16}-"
      resolved="$(gh release list --repo "$REPO" --limit 100 --json tagName --jq '.[].tagName' 2>/dev/null \
                    | grep "^${prefix}" | head -1)"
      [[ -n "$resolved" ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"no release for this address nor its config prefix"}\n' "$tag"; exit 1; }
      mode="prefix"
      gh release download "$resolved" --repo "$REPO" --dir "$staged" --pattern "$asset" --pattern 'manifest.txt' >/dev/null 2>&1 \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"prefix candidate %s could not be downloaded"}\n' "$tag" "$resolved"; exit 1; }
    fi
    [[ -f "$staged/$asset" && -f "$staged/manifest.txt" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"release is missing the archive or its manifest"}\n' "$tag"; exit 1; }
    # 声明的摘要必须与取到的字节相符；不符即丢弃，绝不静默使用。
    declared="$(sed -n 's/^archive_sha256=//p' "$staged/manifest.txt")"
    actual="$(shasum -a 256 "$staged/$asset" | cut -d' ' -f1)"
    [[ -n "$declared" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"manifest declares no digest"}\n' "$tag"; exit 1; }
    [[ "$declared" == "$actual" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"digest mismatch"}\n' "$tag"; exit 1; }
    # 严格相等的只有依赖层身份。`os`/`arch` 不承重(olean 无平台相关二进制,
    # mathlib 亦对所有平台发同一份);`sources_sha256` 在前缀回退下必然不同,
    # 那正是回退的用途,由 lake 补差量兜底。
    for field in toolchain config_sha256; do
      want="$(emit_address | sed -n "s/^${field}=//p")"
      got="$(sed -n "s/^${field}=//p" "$staged/manifest.txt")"
      [[ "$want" == "$got" ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"%s mismatch"}\n' "$tag" "$field"; exit 1; }
    done
    ( cd "$repository" && lake unpack "$staged/$asset" >/dev/null )
    got_sources="$(sed -n 's/^sources_sha256=//p' "$staged/manifest.txt")"
    printf 'LEAN_CACHE_FETCH {"status":"unpacked","mode":"%s","tag":"%s","resolved":"%s","fetched_sources_sha256":"%s","sha256":"%s"}\n' \
      "$mode" "$tag" "$resolved" "$got_sources" "$actual"
    ;;

  *) usage ;;
esac
