#!/usr/bin/env bash
# 把当前 .lake/build 发布为一个不可变的、内容寻址的 GitHub Release 资产。
#
# 命名空间与 spec A14 的 `E<n>` 发布 tag 严格分开：这些 tag 是构建缓存，不是版本发布。
# tag 绑定 (toolchain, os, arch, config_sha256, sources_sha256) 五元组；同一元组只发一次。
#
# 这个归档**不是权威**：它是一个加速器，永远不进 admission 信任链，
# 它的存在也永远不能让任何判词从红变绿。消费侧 (`fetch`) 对任何不匹配一律 fail-closed。
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
tag="lean-cache-v1-${slug}-${os}-${arch}-${config_sha256:0:16}-${sources_sha256:0:16}"
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
    gh release download "$tag" --repo "$REPO" --dir "$staged" --pattern "$asset" --pattern 'manifest.txt' >/dev/null 2>&1 \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"no release for this exact address"}\n' "$tag"; exit 1; }
    [[ -f "$staged/$asset" && -f "$staged/manifest.txt" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"release is missing the archive or its manifest"}\n' "$tag"; exit 1; }
    # 声明的摘要必须与取到的字节相符；不符即丢弃，绝不静默使用。
    declared="$(sed -n 's/^archive_sha256=//p' "$staged/manifest.txt")"
    actual="$(shasum -a 256 "$staged/$asset" | cut -d' ' -f1)"
    [[ -n "$declared" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"manifest declares no digest"}\n' "$tag"; exit 1; }
    [[ "$declared" == "$actual" ]] \
      || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"digest mismatch"}\n' "$tag"; exit 1; }
    # manifest 的五元组必须逐字段等于本地重算的那一份。
    for field in toolchain os arch config_sha256 sources_sha256; do
      want="$(emit_address | sed -n "s/^${field}=//p")"
      got="$(sed -n "s/^${field}=//p" "$staged/manifest.txt")"
      [[ "$want" == "$got" ]] \
        || { printf 'LEAN_CACHE_FETCH {"status":"miss","tag":"%s","reason":"%s mismatch"}\n' "$tag" "$field"; exit 1; }
    done
    ( cd "$repository" && lake unpack "$staged/$asset" >/dev/null )
    printf 'LEAN_CACHE_FETCH {"status":"unpacked","tag":"%s","sha256":"%s"}\n' "$tag" "$actual"
    ;;

  *) usage ;;
esac
