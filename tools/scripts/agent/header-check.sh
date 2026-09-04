#!/usr/bin/env bash
# header-check.sh <lean-file>... — deposit **之前**必跑。
#
# 立条依据 issue #3518(2026-08-27 实测):F-plane 头部若因 `digest:` 折行而成为 **7 行**,
# `make deposit` **退出 0 并把模块 Freeze 掉**,缺陷只由 SL-012 在 preflight/CI 阶段报出。
# 而 Freeze 是 append-only、不可逆的 —— 事后只能靠新增勘误,改不了已冻的那条。
# 故这道检查必须在 deposit 之前跑,不能等 preflight。
#
# 2026-08-28 扩条(OB3 / PR #3654 血案):同一道门必须一并查 **SL-003 容量**。
# 我的 deposit 模板当时查了头部形状与目录文件数,**唯独不查行数**;
# 而实施 brief 里我自己写下了「455 → 855 行」这个数,却没拿它当判据。
# 结果:`make deposit` 退出 0、**不可逆冻结**,随后 CI 才由
# CapacityPolicyTests.RepositoryHasNoOversizeArtifactOrOverfullDirectory 判红(855 > 800)。
# 教训与 #3518 同形:凡「deposit 会照做、只有事后 CI 报」的检查,一律前移到这道门。
#
# 合规形状(恰 6 行,第 6 行以 ` -/` 收尾):
#   /- GID: <path>
#      generality: <G|F|E>
#      mirror-B: <path|none(...)>
#      mirror-E: <path|none(...)>
#      anchors: [...]
#      digest: <一行写完，不得折行> -/
#
# 退出码:0 = 全部合规;1 = 有不合规文件(逐条打印)
__closure_gen() {  # <repo> <file> —— BFS 走 D5 import 传递闭包,打印 generality 为 I/E 的成员
  local repo="$1" start="$2"
  /usr/bin/python3 - "$repo" "$start" <<'PYEOF'
import sys,os,re,collections
repo,start=sys.argv[1],sys.argv[2]
def gen(p):
    try:
        with open(p,encoding='utf-8') as fh:
            for i,l in enumerate(fh):
                if i==1:
                    m=re.search(r'generality:\s*([A-Za-z]+)',l); return m.group(1) if m else None
                if i>1: break
    except OSError: pass
    return None
def imports(p):
    out=[]
    try:
        with open(p,encoding='utf-8') as fh:
            for l in fh:
                m=re.match(r'^import\s+(D5\.[A-Za-z0-9_.]+)',l)
                if m: out.append(os.path.join(repo,m.group(1).replace('.','/')+'.lean'))
                elif l.startswith(('theorem','def','namespace','lemma','structure')): break
    except OSError: pass
    return out
seen=set(); q=collections.deque(imports(start)); bad=[]
while q:
    t=q.popleft()
    if t in seen or not os.path.exists(t): continue
    seen.add(t); g=gen(t)
    if g in ('I','E'):
        bad.append(f"      {os.path.relpath(t,repo)} (generality: {g})")
    q.extend(imports(t))
print("\n".join(bad))
PYEOF
}
__main() {
  local bad=0 f
  [ $# -gt 0 ] || { echo "usage: header-check.sh <lean-file>..." >&2; return 2; }
  for f in "$@"; do
    if [ ! -f "$f" ]; then echo "  ✗ $f  <- 文件不存在"; bad=1; continue; fi
    local first; first=$(head -1 "$f")
    case "$first" in
      "/- GID: "*) ;;
      *) echo "  ✗ $f  <- 首行不是 '/- GID: …'，实为: ${first:0:60}"; bad=1; continue;;
    esac
    # 头部块结束行号(第一个含 ' -/' 的行)
    local endline; endline=$(grep -n -- ' -/' "$f" | head -1 | cut -d: -f1)
    if [ -z "$endline" ]; then echo "  ✗ $f  <- 头部块没有 ' -/' 收尾"; bad=1; continue; fi
    if [ "$endline" -ne 6 ]; then
      echo "  ✗ $f  <- 头部 $endline 行（应为 6）；#3518：deposit 会照冻不误，只有 SL-012 报"
      sed -n "1,${endline}p" "$f" | sed 's/^/      | /'
      bad=1; continue
    fi
    local keys ok=1 k
    for k in generality mirror-B mirror-E anchors digest; do
      grep -q "^   $k:" "$f" || { echo "  ✗ $f  <- 头部缺键 '$k:'"; ok=0; }
    done
    [ "$ok" = 1 ] || { bad=1; continue; }
    # ---- SL-003 容量(2026-08-28 扩条):行数硬线 800、目录文件数准入 12 ----
    # 2026-08-28 二次勘正:此处原为 `wc -l` + `>= 800`,**两个方向都错**。
    #   ① 真判据是 `lineCount > ArtifactHardLineLimit`(`CapacityPolicy.cs:50`),
    #      即 **800 行合法、801 才红**;`>=` 会误拦合法文件(与我在目录上限犯的 off-by-one 同形)。
    #   ② 真算法是 `text.Split('\n').Length - (text.EndsWith('\n') ? 1 : 0)`
    #      (`RepositoryRules.Structure.cs:112-113`)。对**末尾无换行**的文件,
    #      它比 `wc -l` **多数一行** —— 那个方向是**放行真红**,比误拦危险得多。
    local lines; lines=$(/usr/bin/python3 -c "
import sys;t=open(sys.argv[1],encoding='utf-8',errors='replace').read()
print(len(t.split(chr(10)))-(1 if t.endswith(chr(10)) else 0))" "$f")
    if [ "$lines" -gt 800 ]; then
      echo "  ✗ $f  <- $lines 行，超 SL-003 硬线 800(判据 >800;按 C# CountArtifactLines 口径)；deposit 会照冻不误，只有 CI 的 CapacityPolicyTests 报"
      bad=1; continue
    fi
    local dir dn; dir=$(dirname "$f")
    # 2026-08-28:**拒绝仓外路径**。我把分支上的文件 `git show > /tmp/u2.lean` 再喂进来,
    #   于是目录判据数的是 `/tmp/*.lean`(当时 4 个),**看起来是个合理的数,实际毫无意义**。
    #   坏原材料的正解是让产生处 fail-closed,不是让读者记得警惕(器律④)。
    # **判据是「这个目录在不在某个 git 工作树里」,不是匹配路径字面。**
    #   初版我写成 `case "$dir" in */trureturing*|.|./*)`,只测了拒绝侧,
    #   结果把合法的**仓内相对路径**(`D5/S3/…/X.lean` → dirname 无 `trureturing` 字样)也拒了。
    #   放行侧天然盲 —— 两侧都要有具名读数。
    if ! (cd "$dir" 2>/dev/null && git rev-parse --show-toplevel >/dev/null 2>&1); then
      echo "  ✗ $f  <- 该路径不在任何 git 工作树里($dir),目录容量判据无意义。"
      echo "      → 正解:在检出该分支的 worktree 里跑,别 \`git show > /tmp/x.lean\` 再喂进来。"
      bad=1; continue
    fi
    dn=$(ls -1 "$dir"/*.lean 2>/dev/null | wc -l | tr -d ' ')
    # SL-003 真规则(2026-08-28 查 RepositoryRules.Structure.cs:73,236 实证):
    #   `DirectoryFileLimit = 12`,违规判据是 **Count > 12**;准入通过条件是 `projectedOccupancy <= 12`。
    #   **12 个文件是合法的,13 个才红。** 我此前按记忆写成 `>= 12`,多拦一格 ——
    #   典型的「据记忆写判据而不读真规则」,与今晚反复抓的形状同源。
    if [ "$dn" -gt 12 ]; then
      echo "  ✗ $f  <- 目录 $dir 有 $dn 个 .lean，超 SL-003 上限 12(>12 才违规)"
      bad=1; continue
    fi
    # ---- SL-010 地层(2026-08-28;13:05 按源码勘正)----
    # **真规则**(`RepositoryRules.Structure.cs:352-386` 实证,不是我的印象):
    #   ① generality 只有 **G / I / E** 三值(`Routing.cs:84`:`is not ("G" or "I" or "E")` 即报错)——**没有 F**;
    #   ② **只有 `Generality == "G"` 的工件被检查**,其余直接 `continue`;
    #   ③ 判据是 G 的 **ImportClosure(传递闭包)** 里出现 `I` 或 `E`,**不是只看直接 import**;
    #   ④ 另有 `IsLeanClosureFactAffected` 门,本器**无法建模**。
    # 故本检查是**早反馈近似**:可能对真规则不会红的情形报红(缺 ④ 那道门),
    # 但不会漏掉「G 传递依赖 I/E」这一类。**初版我用 rank 序 + 只看直接 import,
    # 两个方向都错:误报 `E import I`,又漏传递依赖。** 那是「据记忆写判据」的又一例。
    local mygen; mygen=$(sed -n '2p' "$f" | grep -oE 'generality: [A-Za-z]+' | awk '{print $2}')
    local repo; repo=$(cd "$(dirname "$f")" && git rev-parse --show-toplevel 2>/dev/null)
    if [ "$mygen" = "G" ] && [ -n "$repo" ]; then
      local viol; viol=$(__closure_gen "$repo" "$f")
      if [ -n "$viol" ]; then
        echo "  ✗ $f  <- SL-010 地层违规:G 工件的 import 闭包里有 I/E 事实:"
        printf "%b\n" "$viol"
        echo "      (deposit 会照冻不误,只有 CI 的 dev baseline admission 以 SL-010 报)"
        bad=1; continue
      fi
    fi
    echo "  ✓ $f  ($lines 行 / 目录 $dn 文件 / generality: ${mygen:-?} 地层合规)"
  done
  [ "$bad" = 0 ] && echo "header-check: 全部合规" || echo "header-check: 有不合规项，**不要 deposit**"
  return $bad
}
__main "$@"
