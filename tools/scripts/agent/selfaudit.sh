#!/bin/bash
# 器律⑥ 转录自审:两种违规形 (i) 尾随& 无wait (ii) 已知长任务前台跑
# 用法: selfaudit.sh [transcript.jsonl] [N_recent]  缺省=最新会话/全量
set -u
T="${1:-$(ls -t ~/.claude/projects/-Users-auric-trureturing/*.jsonl | head -1)}"
N="${2:-0}"
python3 - "$T" "$N" <<'PY'
import json,re,sys
path,n=sys.argv[1],int(sys.argv[2])
cmds=[]
for line in open(path):
    try: d=json.loads(line)
    except: continue
    for c in ((d.get('message') or {}).get('content') or []):
        if isinstance(c,dict) and c.get('type')=='tool_use' and c.get('name')=='Bash':
            cmds.append((c['input'].get('command',''), c['input'].get('run_in_background',False)))
if n: cmds=cmds[-n:]
LONG=('seat.sh dispatch','run-codex-worker.sh','make lean','make preflight','make gate','make worktree','make pr-open','make cover','make deposit','make emit','make ingest','make test','dotnet test','land.sh','nyxid oracle ask')
amp=fg=legal=0
for cmd,bg in cmds:
    body=re.sub(r"<<'?([A-Z]+)'?.*?\n\1(\n|$)",'',cmd,flags=re.S)  # strip heredoc bodies (tolerate no trailing newline)
    if 'selfaudit' in body: continue  # the auditor's own invocations/source are not audit targets
    has_wait='wait' in body
    for ln in body.split('\n'):
        if re.search(r'&\s*$',ln):
            (legal,amp)[0 if has_wait else 1]  # count below
            if has_wait: legal+=1
            else: amp+=1
    if not bg and any(k in body for k in LONG):
        if re.search(r'(^|;|&&|\|\s*)\s*(bash [^\n]*(land\.sh|run-codex-worker\.sh)|make (lean|preflight|gate|ingest|cover|deposit|emit|test)\b|nyxid oracle ask|dotnet test)',body): fg+=1
print(f"bash_calls={len(cmds)} viol_i_amp_no_wait={amp} legal_amp_with_wait={legal} viol_ii_foreground_long={fg}")
PY
