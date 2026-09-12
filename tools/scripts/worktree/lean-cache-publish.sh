#!/usr/bin/env bash
# 把当前 .lake/build 发布为内容寻址的 GitHub Release 资产,大归档分片上传。
#
# 命名空间与 spec A14 的 `E<n>` 发布 tag 严格分开：这些 tag 是构建缓存，不是版本发布。
# tag 绑定 (toolchain, config_sha256, sources_sha256) 三元组；同一元组只发一次。
# tag = <TAG_PREFIX>-<toolchain-slug>-<config16>-<sources16>.
#
# 这个归档**不是权威**：它是一个加速器，不构成独立的 admission 证据。消费侧 (`fetch`)
# 对 toolchain、归档完整性与摘要一律 fail-closed;默认只允许 sources 回退到同 config
# 的最近一份。fetch --allow-seed 另允许同工具链的 project 种子,差量交给 lake build。
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
#   该分支上的 workflow 版本，故 job 内检查 ref 不构成机器边界），已于 PR #2818 移除。
#   〔2026-08-29：原先钉住此形状的 `ContentsWriteWorkflowClosureTests` 已随 workflow 测试
#   禁令（CLAUDE.md 器律⑦′）整体删除。**此形状此后没有机器钉子** —— 把 workflow_dispatch
#   加回去不会有测试变红，只能由评审与真跑发现。〕
#
#   已落地（#2729 判决第 2、3 条）：release tag 用 --target producer_commit_sha；
#   manifest 记 producer_commit_sha 与 workflow_run_id；缺这两个值时 publish 直接拒绝；
#   workflow 侧显式写出 checkout 取的事件 SHA。
#
#   仍未落地（B 步）：**consumer 侧没有任何 provenance 核验** —— 上面这些字段现在
#   写得出来，但没有人去核它们。**在 consumer 核验落地之前，ensure 不得自动 fetch
#   本归档** —— 当前也确实没有，手工 target 只作诊断。
set -euo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
REPO="${STRATALINT_CACHE_REPO:-the-omega-institute/trureturing}"
TAG_PREFIX="lean-cache-v1"
# Issue #6194: publisher run 34119746844 failed at `gh release upload` with
# "HTTP 422: Validation Failed ... size must be less than 2147483648".
# The 2 GiB per-asset limit is exclusive. The six preceding successful archive
# sizes were 1,948,811,751; 2,010,523,084; 2,062,929,966; 2,066,721,511;
# 2,097,463,138; 2,114,121,660 bytes. That run's archive crossed the limit.
# Use 1.5 GiB chunks for headroom. Two-digit suffixes allow 100 parts x 1.5 GiB
# (150 GiB total); split fails closed on exhaustion before release creation.
CHUNK_BYTES=1610612736
VERB="${1:-}"

die() { printf 'lean-cache-publish: %s\n' "$1" >&2; exit 1; }

# 【2026-08-30】此前两处直接写 `shasum -a 256`。`shasum` 是 macOS/Perl 自带,
# **Linux 上通常没有** —— CI runner 是 ubuntu-24.04-arm,于是取回器以
# `exit 127`(command not found)静默失败,`LeanArchiveFetch` 只能记
# `archive fetcher emitted no receipt (exit 127)`,回落全量编译 37 分钟并撞
# 45 分钟 job 预算(实测 job 99264190096)。本机是 macOS,故本地一直复现不出。
# 探测顺序与本仓 report 侧的输入哈希 helper 一致(同一真源,不另发明)。
sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    die "no sha256 implementation is available (tried sha256sum, shasum, openssl)"
  fi
}

usage() {
  cat >&2 <<'USAGE'
usage: lean-cache-publish.sh <address|publish|fetch> [--repository DIR] [--allow-seed]

  address   打印当前工作树对应的缓存 tag 与其三元组，不做任何网络访问
  publish   若该 tag 尚不存在，打包 .lake/build 并发布为该 tag 的资产
  fetch     精确地址优先,其次同 config 前缀;校验失败即 fail-closed
  --allow-seed  仅供 fetch:两级均无层时,允许同工具链最近的 project 层作种子
USAGE
  exit 2
}

repository="$ROOT"
allow_seed=0
writer_owned=0
shift || true
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) repository="${2:?--repository needs a value}"; shift 2 ;;
    --allow-seed) [[ "$VERB" == fetch ]] || usage; allow_seed=1; shift ;;
    --writer-owned) [[ "$VERB" == fetch ]] || usage; writer_owned=1; shift ;;
    *) usage ;;
  esac
done

[[ -n "$VERB" ]] || usage

# ── 发布者身份 ────────────────────────────────────────────────────────────────
# 自 PR #2818 起本归档的触发集合只有 `schedule`，即唯一合法发布者是 dev 上的定时
# CI producer。consumer 侧的 provenance 核验要靠这两个值把资产绑回那次运行，故它们
# 缺失或形状不对时**拒绝发布**：发不出资产，好过发一个事后无法归属的资产。
# 这一段刻意早于 address 计算 —— 身份不成立就不必再算别的。
if [[ "$VERB" == "publish" ]]; then
  # Release snapshots are writable only from the scheduled dev producer. PR
  # and local invocations remain read-only so an untrusted candidate cannot
  # populate the shared release namespace.
  if [[ "${GITHUB_EVENT_NAME:-}" != "schedule" || "${GITHUB_REF:-}" != "refs/heads/dev" ]]; then
    printf 'LEAN_CACHE_PUBLISH {"status":"skipped","reason":"Release publication requires the scheduled dev producer"}\n'
    exit 0
  fi
  producer_commit_sha="${GITHUB_SHA:-}"
  workflow_run_id="${GITHUB_RUN_ID:-}"
  [[ "$producer_commit_sha" =~ ^[0-9a-f]{40}$ ]] \
    || die "publish needs GITHUB_SHA as a 40-hex producer commit; refusing to publish an unattributable archive"
  [[ "$workflow_run_id" =~ ^[0-9]+$ ]] \
    || die "publish needs GITHUB_RUN_ID; refusing to publish an unattributable archive"
fi

# ── 身份 ──────────────────────────────────────────────────────────────────────
# 两个哈希来自本仓既有的唯一真源，不另算一套。
helper="${repository}/tools/scripts/worktree/lean-cache-input.sh"
[[ -x "$helper" ]] || die "input helper is absent: $helper"
input_address="$("$helper" address --repository "$repository")" \
  || die "Lean input address is unavailable"
[[ "$input_address" =~ ^[0-9a-f]{64}\ [0-9a-f]{64}$ ]] || die "Lean input address is malformed"
read -r sources_sha256 config_sha256 <<< "$input_address"
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
tag="${TAG_PREFIX}-${slug}-${config_sha256:0:16}-${sources_sha256:0:16}"
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
    digest="$(sha256_of "$staged/$asset")"
    archives=("$staged/$asset")
    if (( bytes > CHUNK_BYTES )); then
      split -b "$CHUNK_BYTES" -d -a 2 "$staged/$asset" "$staged/$asset.part-"
      archives=("$staged/$asset.part-"*)
    fi
    emit_address > "$staged/manifest.txt"
    {
      printf 'archive_sha256=%s\n' "$digest"
      printf 'archive_bytes=%s\n' "$bytes"
      printf 'parts=%s\n' "${#archives[@]}"
      if (( ${#archives[@]} > 1 )); then
        for i in "${!archives[@]}"; do
          part_digest="$(sha256_of "${archives[$i]}")"
          printf 'part_sha256_%s=%s\n' "$i" "$part_digest"
        done
      fi
      printf 'producer_commit_sha=%s\n' "$producer_commit_sha"
      printf 'workflow_run_id=%s\n' "$workflow_run_id"
    } >> "$staged/manifest.txt"
    # `--target` 把 tag 建在产出它的那个 commit 上。
    #
    # 【这里曾写「缺省 target_commitish 会跟着默认分支走，tag 指向的东西事后还会变」，
    #   那句话是假的】gh 的 --target 是「Target branch or full commit SHA (default
    #   [main branch])」，作用于 **automatic tag creation**：已建成的 tag **不会**因
    #   默认分支之后前进而自动移动。
    #
    #   注意别把这条说过头：tag 本身并非无条件不可变。`gh release create --help` 写
    #   「When release immutability is **enabled** for a repository, Git tags associated
    #   with a release cannot be modified or deleted」—— 那是个仓库开关，而本仓实测
    #   release 的 `immutable=false`（#2729 cost 席读数）。此处需要的只是「不会自动
    #   移动」这条窄命题，它够用，且经核验。
    #
    #   真正的不变量在**创建时刻**：不带 --target 时，tag 建在 gh 执行那一刻默认分支的
    #   tip 上，而那**未必是被打包的那棵树**（dev 每小时前进约 16 个提交，打包与发布之间
    #   隔着一次 lake pack）。于是 manifest 里记的 producer_commit_sha 会与 tag 实际指向的
    #   commit 不是同一个，consumer 拿哪一个都对不上。--target 消除的是这个错配，
    #   不是一个并不存在的事后漂移。
    if ! gh release create "$tag" --repo "$REPO" \
      --target "$producer_commit_sha" \
      --title "Lean build cache ${config_sha256:0:8}/${sources_sha256:0:8} (${os}-${arch})" \
      --notes "Lean build cache produced from ${toolchain} on ${os}-${arch} at ${producer_commit_sha} by run ${workflow_run_id}. An accelerator, not independent admission evidence." \
      "${archives[@]}" "$staged/manifest.txt" >/dev/null; then
      printf 'LEAN_CACHE_PUBLISH {"status":"failed","tag":"%s","reason":"release creation or asset upload failed"}\n' "$tag"
      exit 0
    fi
    # 剪枝：稳态只留一份。fetch 的前缀回落是 `grep "^${prefix}" | head -1`，只取最新的
    # 一份，故同 config 的旧份边际收益为零；而 GitHub Releases **没有** Actions Cache 那样
    # 的 LRU 兜底，不剪就是无上界累积（案号 #2896：实测 9 份 13.1 GiB、5.8 GiB/日）。
    #
    # 顺序不可换：先确认**新份真的在**，再删旧份。反序时若 create 半成功，会同时失去新旧
    # 两份，把一次浪费变成一次断供。
    #
    # 失败一律 fail-open 为「不删」：列举失败、view 失败、任一 delete 失败，都只记进收据，
    # 不阻断发布。剪枝是清理，不是发布的正确性条件——为清理失败而判发布失败，是把
    # 一个可自愈的存量问题升级成供给中断。
    # 同一 config 前缀下保留的 release 份数(含刚发布的这份)。
    RETAIN=5
    pruned=0
    prune_error=""
    if gh release view "$tag" --repo "$REPO" --json tagName --jq .tagName >/dev/null 2>&1; then
      prefix="${TAG_PREFIX}-${slug}-${config_sha256:0:16}-"
      # 保留窗口:同 config 前缀下最近 RETAIN 份(含刚发的这份)不剪。
      # 只留一份时,任何仍在飞、其 sources 尚未换代的消费者会在 prefix 回退上落空;
      # 保留几份让它们仍能取回一份可用的近邻,代价是有界的存量而非无界累积。
      # 列举按创建时间倒序,故跳过前 RETAIN 个即为保留最新的那几份。
      if superseded="$(gh release list --repo "$REPO" --limit 100 --json tagName,createdAt \
                         --jq 'sort_by(.createdAt) | reverse | .[].tagName' 2>/dev/null)"; then
        kept=0
        while IFS= read -r old_tag; do
          [[ -n "$old_tag" ]] || continue
          [[ "$old_tag" == "$prefix"* ]] || continue
          [[ "$old_tag" != "$tag" ]] || continue
          if (( kept < RETAIN - 1 )); then
            kept=$((kept + 1))
            continue
          fi
          if gh release delete "$old_tag" --repo "$REPO" --yes --cleanup-tag >/dev/null 2>&1; then
            pruned=$((pruned + 1))
          else
            prune_error="delete failed for ${old_tag}"
            break
          fi
        done <<< "$superseded"
      else
        prune_error="could not list releases"
      fi
    else
      prune_error="new release is not readable back; pruned nothing"
    fi
    printf 'LEAN_CACHE_PUBLISH {"status":"published","tag":"%s","bytes":%s,"sha256":"%s","pruned":%s,"prune_error":%s}\n' \
      "$tag" "$bytes" "$digest" "$pruned" \
      "$(if [[ -n "$prune_error" ]]; then printf '"%s"' "$prune_error"; else printf 'null'; fi)"
    ;;

  fetch)
    if [[ "${STRATALINT_ACTIONS_CACHE_SEEDED:-}" == "1" || "${STRATALINT_ACTIONS_CACHE_SEEDED:-}" == "true" ]]; then
      printf 'LEAN_CACHE_FETCH {"status":"skipped","reason":"Actions supplied an applicable seed"}\n'
      exit 0
    fi
    staged="$(mktemp -d)"
    trap 'rm -rf "$staged"' EXIT
    # 精确地址优先；取不到就按 config 前缀回退到最近一份。
    # 为什么必须回退:dev 约 16 提交/小时,而发布一轮 6.5 分钟起——`sources_sha256`
    # **结构性地**追不上。实测:新建 worktree 到 fetch 之间 dev 就前进了,
    # 本机要 …-02ab04b1 而当时最新的 release 是 …-6b2da53f,精确匹配当场 miss。
    # 回退是安全的:`toolchain` 与 `config_sha256` 仍严格相等(依赖层不容将就),
    # 只放宽 `sources_sha256`,差量由 `lake build` 补齐——lake 按 depHash 判 stale,
    # 旧基底里过期的模块会被重编译。这正是 mathlib `lake exe cache get` 的模型。
    # Each attempt has its own staging directory and exit status. A corrupt release
    # must not prevent trying the next exact/config-prefix/same-toolchain candidate.
    try_fetch() (
    resolved="$1"
    mode="$2"
    candidate_dir="$(mktemp -d "$staged/candidate.XXXXXX")" || exit 1
    staged="$candidate_dir"
    trap 'rm -rf "$staged"' EXIT
    seed_config=""
    if [[ "$mode" == seed ]]; then
      seed_config="${resolved#"${TAG_PREFIX}-${slug}-"}"
      seed_config="${seed_config%%-*}"
      [[ "$seed_config" =~ ^[0-9a-f]{16}$ ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"seed tag has a malformed config address"}\n' "$resolved"; exit 1; }
    fi
    gh release download "$resolved" --repo "$REPO" --dir "$staged" --pattern 'manifest.txt' >/dev/null 2>&1 \
      && [[ -f "$staged/manifest.txt" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"release is missing the archive or its manifest"}\n' "$resolved"; exit 1; }
    parts="$(sed -n 's/^parts=//p' "$staged/manifest.txt")"
    # Releases predating chunking have no parts field. All new writes declare it.
    if [[ -z "$parts" ]] && ! grep -q '^parts=' "$staged/manifest.txt"; then parts=1; fi
    [[ "$parts" =~ ^([1-9][0-9]?|100)$ ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"invalid parts count"}\n' "$resolved"; exit 1; }
    archive_assets=()
    archive_digests=()
    if (( parts > 1 )); then
      gh release download "$resolved" --repo "$REPO" --dir "$staged" --pattern "$asset.part-*" >/dev/null 2>&1 \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"parts could not be downloaded"}\n' "$resolved"; exit 1; }
      for ((i=0; i<parts; i++)); do
        printf -v part '%s.part-%02d' "$asset" "$i"
        [[ -f "$staged/$part" ]] \
          || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"missing part %s"}\n' "$resolved" "$part"; exit 1; }
        part_declared="$(sed -n "s/^part_sha256_${i}=//p" "$staged/manifest.txt")"
        part_actual="$(sha256_of "$staged/$part")" \
          || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"could not hash part %s"}\n' "$resolved" "$part"; exit 1; }
        [[ "$part_declared" == "$part_actual" ]] \
          || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"part checksum mismatch for %s"}\n' "$resolved" "$part"; exit 1; }
        archive_assets+=("$part")
        archive_digests+=("$part_actual")
        cat "$staged/$part" >> "$staged/$asset" \
          || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"could not assemble archive"}\n' "$resolved"; exit 1; }
      done
    else
      gh release download "$resolved" --repo "$REPO" --dir "$staged" --pattern "$asset" >/dev/null 2>&1 \
        && [[ -f "$staged/$asset" ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"single archive could not be downloaded"}\n' "$resolved"; exit 1; }
      archive_assets=("$asset")
    fi
    # 声明的摘要必须与取到的字节相符；不符即丢弃，绝不静默使用。
    declared="$(sed -n 's/^archive_sha256=//p' "$staged/manifest.txt")"
    actual="$(sha256_of "$staged/$asset")" \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"could not hash archive"}\n' "$resolved"; exit 1; }
    [[ -n "$declared" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"manifest declares no digest"}\n' "$resolved"; exit 1; }
    [[ "$declared" == "$actual" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"digest mismatch"}\n' "$resolved"; exit 1; }
    if (( parts == 1 )); then archive_digests=("$actual"); fi
    # Seed safety (#5994): mathlib is restored separately, keyed by the candidate's
    # manifest and toolchain; lakefile changes affect only the project cache key.
    # This archive supplies only the project layer. For an honestly produced cache,
    # each module's content-addressed .trace depHash makes lake build rebuild what
    # config/source changes invalidate, so stale oleans are not reused as current.
    # This is build invalidation, not output authentication; the trust limit above
    # still applies. Exact/prefix keep full config equality; seed binds its own tag.
    for field in toolchain config_sha256; do
      want="$(emit_address | sed -n "s/^${field}=//p")"
      got="$(sed -n "s/^${field}=//p" "$staged/manifest.txt")"
      if [[ "$mode" == seed && "$field" == config_sha256 ]]; then
        [[ "$got" =~ ^[0-9a-f]{64}$ && "${got:0:16}" == "$seed_config" ]] \
          || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"seed config does not match its release tag"}\n' "$tag"; exit 1; }
        continue
      fi
      [[ "$want" == "$got" ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"%s mismatch"}\n' "$tag" "$field"; exit 1; }
    done
    # ── 产地核验 ────────────────────────────────────────────────────────────
    # 这段是 #2729 判决的 B 步前半。摘要与依赖层身份只证明「字节没坏、层对得上」，
    # 不证明**是谁产的**：manifest 与 payload 同处一个发布面，有写权者可一起替换而
    # 保持自洽（`cost` 席实测 release `immutable=false`）。
    #
    # 归档的 .olean 会被 Lake 当构建输入复用、canonical 报告从那个环境读声明，故
    # 发布者位于 admission 下方。三席一致：**任一 provenance 检查不过即判 miss，
    # 不消费其 olean**。
    # 【2026-08-30 τ=0 裁决:去掉产地的【身份】校验,只留【内容】校验】
#
# owner 原话:「我觉得不需要验证, 直接删了就行, 只要是 cache 匹配就可以.
#              这样本地都可以 release cache, 只要你有权限传到 github release 即可.」
#
# 删掉的四项(全是身份类):
#   release author == github-actions[bot]
#   每个 asset 的 uploader == github-actions[bot]
#   发布器 workflow id 归属(按路径解析 lean-cache-publish.yml 的 id 并比对)
#   run 的 event=schedule / head_branch=dev / head_sha / conclusion=success
#
# 保留的(全是内容与结构类):
#   producer_commit_sha 与 workflow_run_id 的**形状**
#   release target_commitish == 声明的 producer commit
#   asset 恰好为 manifest.txt 与它声明的单归档或全部分片
#   GitHub 自己记录的 asset digest == 实际下载字节的 sha256(独立第二侧)
#   以及取回后按 sources_sha256 的内容比对
#
# 【orchestrator 提过的顾虑,如实留档,不是反对】
# 内容寻址绑的是**输入**(toolchain + lake-manifest + lakefile + sources);
# 没有任何一侧验证 archive 里的 `.olean` 是**那些输入的正确构建输出** ——
# 重建它就等于放弃缓存。故在删掉身份校验后,
# 「这堆 olean 是不是 lake build 的真实产物」不再有任何机器保证。
# 而 consumer 复用的 olean 会进 Lean 报告、报告喂 admission,
# 即发布者位于 admission 下方(该结论由 #2729 三席评审确立)。
#
# 【同时暴露的一处既存空洞,一并记】
# `workflow_run_id` 只被验形状(纯数字),从不被验指向真实 run —— 本次发布
# 即以时间戳填入并通过。故它在删改前就已是形同虚设的溯源字段。
#
# owner 已知悉上述并作此裁决。改这段回去同样是 τ=0 动作。

fail_provenance() {
      printf 'LEAN_CACHE_FETCH {"status":"rejected","tag":"%s","resolved":"%s","stage":"provenance","reason":"%s"}\n' \
        "$tag" "$resolved" "$1"
      exit 1
    }
    producer_commit_sha="$(sed -n 's/^producer_commit_sha=//p' "$staged/manifest.txt")"
    archive_run_id="$(sed -n 's/^workflow_run_id=//p' "$staged/manifest.txt")"
    [[ "$producer_commit_sha" =~ ^[0-9a-f]{40}$ ]] \
      || fail_provenance "manifest carries no producer commit; archives published before #2833 are not attributable and are refused"
    [[ "$archive_run_id" =~ ^[0-9]+$ ]] \
      || fail_provenance "manifest carries no workflow run id"

    # 一次 REST 调用拿齐 target_commitish 与资产清单。走 api 而非
    # `gh release view --json`，因为后者的 asset 字段缺少这里要比的信息。
    command -v jq >/dev/null 2>&1 \
      || fail_provenance "jq is required to read release provenance and is absent"
    release_json="$(gh api "repos/${REPO}/releases/tags/${resolved}" 2>/dev/null)" \
      || fail_provenance "release metadata is unreadable"
    release_target="$(printf '%s' "$release_json" | jq -r '.target_commitish // ""')" \
      || fail_provenance "release metadata is malformed"
    [[ "$release_target" == "$producer_commit_sha" ]] \
      || fail_provenance "release target ${release_target:-<absent>} does not match the declared producer commit"

    # 资产必须恰好是声明的归档或分片与 manifest。多一份说明 release 被追加过，
    # 而逐份比对摘要并不排除「另外还多了一份」这种情形。
    for expected in "${archive_assets[@]}" manifest.txt; do
      count="$(printf '%s' "$release_json" | jq --arg n "$expected" '[.assets[]? | select(.name == $n)] | length')" \
        || fail_provenance "release asset inventory is malformed"
      [[ "$count" == "1" ]] \
        || fail_provenance "release carries ${count:-<absent>} assets named ${expected}, expected exactly 1"
    done
    total_assets="$(printf '%s' "$release_json" | jq '[.assets[]?] | length')" \
      || fail_provenance "release asset inventory is malformed"
    [[ "$total_assets" == "$((parts + 1))" ]] \
      || fail_provenance "release carries ${total_assets:-<absent>} assets, expected exactly $((parts + 1))"
    # 进程替换里的失败不会被 `set -e` 捕获，故先把结果取进变量并查状态：解析失败

    # 把**手里的字节**绑到**被验产地的那个资产**上。此前只比 manifest 声明的摘要，而
    # manifest 与 payload 同处一个发布面；GitHub 自己记的 asset digest 是独立的第二侧。
    for i in "${!archive_assets[@]}"; do
      expected="${archive_assets[$i]}"
      github_digest="$(printf '%s' "$release_json" \
        | jq -r --arg n "$expected" '.assets[]? | select(.name == $n) | .digest // ""')" \
        || fail_provenance "release asset digest is malformed"
      [[ "$github_digest" == "sha256:${archive_digests[$i]}" ]] \
        || fail_provenance "archive bytes do not match the digest GitHub recorded for ${expected} (${github_digest:-<absent>})"
    done

    # `head_branch=dev` + `event=schedule` + 该 run 成功，合起来说明该 commit 当时
    # 就是默认分支的 tip。**残余**：dev 若被 force-push，历史上的 tip 可能已不在
    # 当前历史里。此处不另做祖先查询——那要么依赖本机 fetch 状态（会随上次 fetch
    # 何时发生而变），要么再加一次 API 往返。记为已知残余，不冒充已排除。

    # 解包只有这一个入口，且它在**产地核验之后**。做成具名函数不是修辞：
    # `VerifiedConsumptionHasASingleEntryPoint` 钉住脚本里 `lake unpack` 恰好出现一次
    # 且落在此函数体内，故将来任何新分支想解包都必须走这里，不能各写各的。
    consume_verified_archive() {
      ( cd "$repository" && lake unpack "$staged/$asset" >/dev/null )
    }
    consume_verified_archive \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"archive could not be unpacked"}\n' "$resolved"; exit 1; }
    got_sources="$(sed -n 's/^sources_sha256=//p' "$staged/manifest.txt")"
    seed_fields=""
    if [[ "$mode" == seed ]]; then
      seed_fields=",\"seed_config\":\"${seed_config}\",\"candidate_config\":\"${config_sha256}\""
    fi
    printf 'LEAN_CACHE_FETCH {"status":"unpacked","mode":"%s","tag":"%s","resolved":"%s","fetched_sources_sha256":"%s","sha256":"%s","producer_commit_sha":"%s","workflow_run_id":"%s"%s}\n' \
      "$mode" "$tag" "$resolved" "$got_sources" "$actual" "$producer_commit_sha" "$archive_run_id" "$seed_fields"
    )

    if try_fetch "$tag" exact; then exit 0; fi
    releases="$(gh release list --repo "$REPO" --limit 100 --json tagName,createdAt \
      --jq 'sort_by(.createdAt) | reverse | .[].tagName' 2>/dev/null)" \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"could not list releases"}\n' "$tag"; exit 1; }
    prefix="${TAG_PREFIX}-${slug}-${config_sha256:0:16}-"
    # Newest first within each tier; exhaust the config tier before allowing seeds.
    for mode in prefix seed; do
      [[ "$mode" != seed || "$allow_seed" == 1 ]] || continue
      while IFS= read -r release_tag; do
        [[ "$release_tag" != "$tag" ]] || continue
        if [[ "$mode" == prefix ]]; then
          [[ "$release_tag" == "$prefix"* ]] || continue
        else
          [[ "$release_tag" == "${TAG_PREFIX}-${slug}-"* && "$release_tag" != "$prefix"* ]] || continue
        fi
        if try_fetch "$release_tag" "$mode"; then exit 0; fi
      done <<< "$releases"
    done
    # Keep the last candidate's receipt as the terminal, specific failure reason.
    # If no release existed at all, there is no candidate receipt to preserve;
    # still emit the structured miss contract so callers can distinguish an
    # ordinary cache miss from a malformed fetcher invocation.
    printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"no release for this address nor its config prefix or an allowed same-toolchain seed passed validation"}\n' "$tag"
    printf 'lean-cache-publish: no release for this address nor its config prefix or an allowed same-toolchain seed passed validation\n' >&2
    exit 1
    ;;

  *) usage ;;
esac
