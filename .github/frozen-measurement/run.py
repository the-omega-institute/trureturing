from pathlib import Path
import json, os, subprocess, sys, tarfile
root=Path.cwd()
conf=Path(__file__).resolve().parent
rows=json.loads((conf/'shards.json').read_text())
row=rows[int(os.environ['SHARD'])]
parts=row['paths']
artifacts=Path(os.environ['RUNNER_TEMP'])/'results'
artifacts.mkdir(exist_ok=True)
if sys.argv[1]=='targets':
    output=Path(os.environ['RUNNER_TEMP'])/'targets'
    output.write_text(''.join(p.removesuffix('.lean').replace('/','.')+'\n' for p in parts))
    sys.exit()
producer=root/'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'
cli=root/'tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll'
os.environ['STRATALINT_LEAN_PRODUCER_DLL']=str(producer)
assert cli.is_file() and producer.is_file()
prefix='Golden/Frozen/state/'
for offset in range(0,len(parts),16):
    batch=parts[offset:offset+16]
    targets=' '.join(p.removesuffix('.lean').replace('/','.') for p in batch)
    report=Path(os.environ['RUNNER_TEMP'])/'scope.json'
    for command in (['python3','-B','tools/lean-inspector/build_inputs.py','prepare','--targets',targets],
                    ['bash','tools/scripts/report/lean-report-scoped.sh','--targets',targets,'--output',str(report)],
                    ['dotnet',str(cli),'ledger-align','--refresh-annotations','--candidate-lean-report',str(report),*[s for p in batch for s in ('--selector',p)]]):
        subprocess.run(command,check=True)
    states=[prefix+p+'.json' for p in batch]
    changed=subprocess.check_output(['git','diff','--name-only','--',*states],text=True).splitlines()
    assert set(changed)<=set(states)
    with tarfile.open(artifacts/f'{offset}.tar.gz','w:gz') as tar:
        for path in changed:tar.add(path,arcname=path,recursive=False)
    (artifacts/f'{offset}.json').write_text(json.dumps({'paths':batch,'changed':changed,'worker':row['worker']}))
