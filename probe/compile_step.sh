#!/bin/bash
# Compile one completed probe increment, retain measurements, commit only probe, push.
set -eu
export PATH="$HOME/.dotnet:$HOME/.elan/bin:$HOME/.cargo/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
step=$1
note=$2
probe_log_dir=/var/folders/rm/8w0nylc12d909d_tl053wqkw0000gn/T/consensus-rnd/sshx/s6c2e-probe-syy-cycles-probe/attempt-1/scratch
probe_log="$probe_log_dir/$step.log"
if /usr/bin/time -l lake env lean probe/SyyProbe.lean > "$probe_log" 2>&1; then
  python3 - "$note" "$probe_log" <<'PY'
import sys,re,json,pathlib
note,log=sys.argv[1:]
text=pathlib.Path(log).read_text()
with open('probe/REPORT.md','a') as f:
    f.write('\n'+note+'\n')
wall=float(re.search(r'([0-9.]+) real',text).group(1))
rss=int(re.search(r'(\d+)  maximum resident set size',text).group(1))
pathlib.Path('probe/lean_measurement.json').write_text(json.dumps(dict(command='/usr/bin/time -l lake env lean probe/SyyProbe.lean',exit=0,wall_s=wall,peak_rss_bytes=rss,peak_rss_gb=rss/10**9,log=log),indent=2)+'\n')
print(text)
PY
  git add probe
  git commit -m "probe(syy-cycles): $step"
  git push -u origin lane/math/op-syy-cycles-probe
else
  probe_exit=$?
  cat "$probe_log"
  exit "$probe_exit"
fi
