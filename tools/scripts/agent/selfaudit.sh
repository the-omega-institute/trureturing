#!/bin/bash
# 器律⑥/⑥‴ 转录自审:三种违规形
#   (i)  尾随& 无 wait          (ii) 已知长任务前台跑
#   (iii) 叠第二条等待通道 —— 宿主后台作业完成必定通知,再等一遍即多一条通道
#
# 保证边界(反例集合两维,写不出就不能用「保证」二字):
#   ① 绕过检查:非 sleep 的延时(read -t、python time.sleep、无 sleep 的忙等 until)、
#      任务路径经变量间接(f=$T; cat "$f")、非 Bash 载体、宿主换输出目录布局。
#   ② 检查本身被跳过:**本器不在任何门上**——CI 看不到会话转录,故它结构上只能是
#      自审器,由「每次反思跑一遍」这条纪律驱动;不跑即等于不存在。
#      转录解析失败已 fail-closed(exit 2),不再把崩溃读成「0 命中」。
# 用法: selfaudit.sh [transcript.jsonl] [N_recent]   缺省=最新会话/全量
#       selfaudit.sh --selftest                      跑匹配器的阳性/阴性对照
set -u
if [ "${1:-}" = "--selftest" ]; then T=--selftest; N=0; else
  # 转录住在**主检出**的项目目录下。从 worktree 里跑时 --show-toplevel 给的是 worktree
  # 路径,推出的目录不存在(2026-09-05 实测),故用 --git-common-dir 定位主检出。
  if [ -z "${CLAUDE_PROJECT_DIR:-}" ]; then
    common="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" || common=""
    root="${common%/.git}"
    [ -n "$root" ] && CLAUDE_PROJECT_DIR="$HOME/.claude/projects/$(printf '%s' "$root" | sed 's|/|-|g')"
  fi
  T="$(ls -t "${CLAUDE_PROJECT_DIR:-/nonexistent}"/*.jsonl 2>/dev/null | head -1)"
  # fail-closed:找不到转录就红,不得让一次崩溃被读成「0 命中」。
  if [ -z "$T" ]; then
    echo "SELFAUDIT_TRANSCRIPT_NOT_FOUND dir=${CLAUDE_PROJECT_DIR:-<未解析>}" >&2
    exit 2
  fi
  N="${2:-0}"
fi
python3 - "$T" "$N" <<'PY'
import json,re,sys
path,n=sys.argv[1],int(sys.argv[2])

# ---- 唯一真源:三种违规形的判据 ------------------------------------------
LONG=r'(^|;|&&|\|\s*)\s*(bash [^\n]*(land\.sh|run-codex-worker\.sh)'\
     r'|make (lean|preflight|gate|ingest|cover|deposit|emit|test)\b'\
     r'|nyxid oracle ask|dotnet test)'

def normalize(cmd):
    """剥 heredoc 体与引号字面量,只留命令位置的字节。
    引号字面量必须剥:grep 模式串里的 `\\|make lean`、echo 文本、python -c 体
    都会被误判为命令位置(2026-08-29 实测 5 条报告中 4 条为此类假阳)。"""
    b=re.sub(r"<<'?([A-Z]+)'?.*?\n\1(\n|$)",'',cmd,flags=re.S)
    return re.sub(r"'[^']*'|\"(?:[^\"\\]|\\.)*\"",' ',b)

# 器律⑥‴:宿主的后台作业**完成时必定通知**,故任何针对「宿主任务输出路径」的
# 等待都是第二条通道。分界必须精确,否则把「消费产物」误判为「等待」:
#   放行 收到通知后单次 cat 该文件(无 sleep)
#   放行 只有 sleep 而不碰任务路径(可能是器律⑥′ 允许的外部轮询)
#   放行 创建该后台作业的那次调用(出现路径但无 sleep)
TASKPATH=r'/tasks/[A-Za-z0-9_]+\.output'
SLEEP   =r'(^|;|&&|\|\||\bdo\b|\bthen\b)\s*sleep\s'

def judge(cmd,bg):
    """→ (违规i, 违规ii, 违规iii)。所有消费者共用此函数,自测亦然。"""
    b=normalize(cmd)
    viol_i   = any(re.search(r'&\s*$',ln) for ln in b.split('\n')) and 'wait' not in b
    viol_ii  = (not bg) and bool(re.search(LONG,b))
    viol_iii = bool(re.search(SLEEP,b)) and bool(re.search(TASKPATH,b))
    return viol_i, viol_ii, viol_iii
# -------------------------------------------------------------------------

if path=='--selftest':
    # 阳性对照与阴性对照钉在一处:收紧匹配器与「降级检测」在此可分辨(第20条红线)。
    CASES=[
      ("真ii 前台长任务",      "make lean-report > x.log",             False, (False,True,False)),
      ("真ii 前台 dotnet test","cd t && dotnet test proj.csproj",      False, (False,True,False)),
      ("真i  尾随&无wait",     "bash seat.sh dispatch a b > x.log &",   False, (True,False,False)),
      ("合法 &+wait",          "for x in 1 2; do run $x & done; wait",  False, (False,False,False)),
      ("负 后台长任务",        "make lean-report > x.log",             True,  (False,False,False)),
      ("负 引号内(grep模式)",  "grep -n 'x\\|make lean' ci.yml",        False, (False,False,False)),
      ("负 引号内(命令位置)",  'echo "step 1; make lean; step 2"',      False, (False,False,False)),
      ("负 引号内(py -c体)",   'python3 -c "x=1; make test"',           False, (False,False,False)),
      # ---- (iii) 叠第二条等待通道:阳性 ----
      ("真iii sleep 后读任务输出", "sleep 90; cat /tmp/p/tasks/babc.output",              False, (False,False,True)),
      ("真iii until 轮询任务输出", "until [ -s /tmp/p/tasks/bq.output ]; do sleep 5; done", False, (False,False,True)),
      # ---- (iii) 阴性对照:三条分界各钉一条,收紧过头会在此变红 ----
      ("负iii 通知后单次读",      "cat /tmp/p/tasks/babc.output",                        False, (False,False,False)),
      ("负iii 只sleep不碰任务",   "sleep 300; gh pr view 123",                           False, (False,False,False)),
      ("负iii 创建后台作业",      "make lean-report > /tmp/p/tasks/b.output",            True,  (False,False,False)),
    ]
    bad=0
    for name,cmd,bg,exp in CASES:
        got=judge(cmd,bg); ok=(got==exp); bad+=0 if ok else 1
        print(f"  {'ok  ' if ok else 'FAIL'} {name:22s} exp={exp} got={got}")
    print(f"SELFTEST_{'PASS' if not bad else 'FAIL'} cases={len(CASES)} failed={bad}")
    sys.exit(1 if bad else 0)

cmds=[]; taskouts=[]
for line in open(path):
    try: d=json.loads(line)
    except: continue
    for c in ((d.get('message') or {}).get('content') or []):
        if not (isinstance(c,dict) and c.get('type')=='tool_use'): continue
        if c.get('name')=='Bash':
            cmds.append((c['input'].get('command',''), c['input'].get('run_in_background',False)))
        elif c.get('name')=='TaskOutput':
            taskouts.append(c.get('input') or {})
if n: cmds=cmds[-n:]; taskouts=taskouts[-n:]

amp=fg=legal=stack=0
for i,(cmd,bg) in enumerate(cmds):
    if 'selfaudit' in cmd: continue      # 器不审自己的调用与源码
    vi,vii,viii=judge(cmd,bg)
    if vi: amp+=1;  print(f"[i   #{i}] {cmd[:140]}", file=sys.stderr)
    elif any(re.search(r'&\s*$',ln) for ln in normalize(cmd).split('\n')): legal+=1
    if vii: fg+=1;  print(f"[ii  #{i}] {cmd[:140]}", file=sys.stderr)
    if viii: stack+=1; print(f"[iii #{i}] {cmd[:140]}", file=sys.stderr)
# (iii-a) 宿主的阻塞式任务读取:与 sleep 轮询同罪,载体不同故单独计。
for i,inp in enumerate(taskouts):
    if inp.get('block') is True:
        stack+=1
        print(f"[iii-a #{i}] TaskOutput block=true", file=sys.stderr)
print(f"bash_calls={len(cmds)} viol_i_amp_no_wait={amp} legal_amp_with_wait={legal} "
      f"viol_ii_foreground_long={fg} viol_iii_extra_wait_channel={stack}")
PY
