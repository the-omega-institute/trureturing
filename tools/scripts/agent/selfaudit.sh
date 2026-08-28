#!/bin/bash
# 器律⑥ 转录自审:两种违规形 (i) 尾随& 无wait (ii) 已知长任务前台跑
# 用法: selfaudit.sh [transcript.jsonl] [N_recent]   缺省=最新会话/全量
#       selfaudit.sh --selftest                      跑匹配器的阳性/阴性对照
set -u
if [ "${1:-}" = "--selftest" ]; then T=--selftest; N=0; else
  T="${1:-$(ls -t ~/.claude/projects/-Users-auricstudio-trureturing/*.jsonl | head -1)}"
  N="${2:-0}"
fi
python3 - "$T" "$N" <<'PY'
import json,re,sys
path,n=sys.argv[1],int(sys.argv[2])

# ---- 唯一真源:两种违规形的判据 ------------------------------------------
LONG=r'(^|;|&&|\|\s*)\s*(bash [^\n]*(land\.sh|run-codex-worker\.sh)'\
     r'|make (lean|preflight|gate|ingest|cover|deposit|emit|test)\b'\
     r'|nyxid oracle ask|dotnet test)'

def normalize(cmd):
    """剥 heredoc 体与引号字面量,只留命令位置的字节。
    引号字面量必须剥:grep 模式串里的 `\\|make lean`、echo 文本、python -c 体
    都会被误判为命令位置(2026-08-29 实测 5 条报告中 4 条为此类假阳)。"""
    b=re.sub(r"<<'?([A-Z]+)'?.*?\n\1(\n|$)",'',cmd,flags=re.S)
    return re.sub(r"'[^']*'|\"(?:[^\"\\]|\\.)*\"",' ',b)

def judge(cmd,bg):
    """→ (违规i, 违规ii)。所有消费者共用此函数,自测亦然。"""
    b=normalize(cmd)
    viol_i  = any(re.search(r'&\s*$',ln) for ln in b.split('\n')) and 'wait' not in b
    viol_ii = (not bg) and bool(re.search(LONG,b))
    return viol_i, viol_ii
# -------------------------------------------------------------------------

if path=='--selftest':
    # 阳性对照与阴性对照钉在一处:收紧匹配器与「降级检测」在此可分辨(第20条红线)。
    CASES=[
      ("真ii 前台长任务",      "make lean-report > x.log",             False, (False,True)),
      ("真ii 前台 dotnet test","cd t && dotnet test proj.csproj",      False, (False,True)),
      ("真i  尾随&无wait",     "bash seat.sh dispatch a b > x.log &",   False, (True,False)),
      ("合法 &+wait",          "for x in 1 2; do run $x & done; wait",  False, (False,False)),
      ("负 后台长任务",        "make lean-report > x.log",             True,  (False,False)),
      ("负 引号内(grep模式)",  "grep -n 'x\\|make lean' ci.yml",        False, (False,False)),
      ("负 引号内(命令位置)",  'echo "step 1; make lean; step 2"',      False, (False,False)),
      ("负 引号内(py -c体)",   'python3 -c "x=1; make test"',           False, (False,False)),
    ]
    bad=0
    for name,cmd,bg,exp in CASES:
        got=judge(cmd,bg); ok=(got==exp); bad+=0 if ok else 1
        print(f"  {'ok  ' if ok else 'FAIL'} {name:22s} exp={exp} got={got}")
    print(f"SELFTEST_{'PASS' if not bad else 'FAIL'} cases={len(CASES)} failed={bad}")
    sys.exit(1 if bad else 0)

cmds=[]
for line in open(path):
    try: d=json.loads(line)
    except: continue
    for c in ((d.get('message') or {}).get('content') or []):
        if isinstance(c,dict) and c.get('type')=='tool_use' and c.get('name')=='Bash':
            cmds.append((c['input'].get('command',''), c['input'].get('run_in_background',False)))
if n: cmds=cmds[-n:]

amp=fg=legal=0
for i,(cmd,bg) in enumerate(cmds):
    if 'selfaudit' in cmd: continue      # 器不审自己的调用与源码
    vi,vii=judge(cmd,bg)
    if vi: amp+=1;  print(f"[i  #{i}] {cmd[:140]}", file=sys.stderr)
    elif any(re.search(r'&\s*$',ln) for ln in normalize(cmd).split('\n')): legal+=1
    if vii: fg+=1;  print(f"[ii #{i}] {cmd[:140]}", file=sys.stderr)
print(f"bash_calls={len(cmds)} viol_i_amp_no_wait={amp} legal_amp_with_wait={legal} viol_ii_foreground_long={fg}")
PY
