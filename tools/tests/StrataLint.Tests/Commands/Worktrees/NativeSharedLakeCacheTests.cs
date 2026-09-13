using System.Text;
using StrataLint.Cli;
using Xunit.Abstractions;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class NativeSharedLakeCacheTests(ITestOutputHelper output)
{
    [Fact]
    public void OfficialRestorationSupportsConsumersMissesAndIndependentWorktrees()
        => RunNative(NativeProgram);

    [Fact]
    public void CanonicalCiArchivesAndVerifiedFetchPreserveNativeArtifacts()
        => RunNative(NativeArchiveProgram);

    [Fact]
    public void OfficialPackageRestorationAndWriterLifetimesRemainIndependent()
        => RunNative(NativeOwnershipProgram);

    private void RunNative(string program)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        Assert.True(LeanLakeExecutable.TryResolve(out var lake, out var reason), reason);
        var script = Path.Combine(temporary.Path, "native.py");
        File.WriteAllText(script, program);
        var result = TestProcessRunner.Run("python3", [script, typeof(Program).Assembly.Location,
            lake, TestRepositoryLayout.FindRoot()], temporary.Path,
            TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        var diagnostic = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        output.WriteLine(diagnostic);
        Assert.True(result.ExitCode == 0, diagnostic);
    }

    private const string NativePrelude = """
import os, sys, subprocess, pathlib, json, hashlib, shutil, tarfile, time, concurrent.futures
P = pathlib.Path(__file__).resolve().parent
assembly, lake, repository = sys.argv[1:]
CLI = [shutil.which('dotnet'), assembly, 'worktree']
# Fixtures select their mode explicitly, even when this suite itself runs in Actions.
ENV = dict(os.environ, LAKE_BIN=lake, ELAN_TOOLCHAIN='leanprover/lean4:v4.33.0', GITHUB_ACTIONS='false',
           XDG_CACHE_HOME=str(P/'xdg-cache'))
cache = P / 'xdg-cache/lake'
records = []
def run(args, cwd, expected=0, env=None):
    started = time.monotonic()
    result = subprocess.run(list(map(str,args)), cwd=cwd, env=env or ENV, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90)
    records.append(dict(argv=list(map(str,args)), exit=result.returncode, seconds=round(time.monotonic()-started,4)))
    assert result.returncode == expected, (args,result.returncode,result.stdout,result.stderr)
    return result
def command(root, *args, expected=0, ci=False, store=cache):
    env=dict(ENV,GITHUB_ACTIONS='true' if ci else 'false',GITHUB_EVENT_NAME='pull_request_target')
    return run(CLI + ['with-cache','--path',root,'--','env','LAKE_CACHE_DIR='+str(store),*args], root, expected, env)
def fresh(name, value=42):
    root = P / name
    root.mkdir()
    (root/'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
    (root/'lake-manifest.json').write_text('{"version":"1.2.0","packages":[]}\n')
    # The production root deliberately leaves the Lake file default unset;
    # LeanProcessPolicy supplies the official cache environment at the runner
    # boundary. This keeps the probe honest about the canonical root policy.
    (root/'lakefile.toml').write_text('name="fixture"\ndefaultTargets=["Fixture"]\n[[lean_lib]]\nname="Fixture"\n')
    (root/'Fixture.lean').write_text(f'module\npublic abbrev answer : Nat := {value}\npublic theorem answer_ok : answer = {value} := rfl\n')
    with (root/'lakefile.toml').open('a') as f:
        f.write('\n[[lean_lib]]\nname="Claim"\n')
    claim=root/'Claim.lean'
    claim.write_text('def claim : Prop := 1 = 0\n')
    with (root/'Fixture.lean').open('a') as f:
        f.write('public theorem refutation : ¬ (1 = 0) := by decide\n')
    (root/'utility.json').write_text(json.dumps([dict(modulePath='Fixture.lean',claimGid='fixture/claim',
        claimModule='Claim',claimSelector='claim',claimSourcePath='Claim.lean',
        claimSourceSha256='sha256:'+hashlib.sha256(claim.read_bytes()).hexdigest(),
        resultGid='fixture/refutation',resultModule='Fixture',resultSelector='refutation')]))
    run(['git','init','-q'],root)
    inspector=root/'tools/lean-inspector/Inspector.lean'
    inspector.parent.mkdir(parents=True)
    shutil.copyfile(pathlib.Path(repository)/'tools/lean-inspector/Inspector.lean',inspector)
    return root
def install_runner(root):
    scripts=root/'tools/scripts/worktree';scripts.mkdir(parents=True,exist_ok=True)
    runner=scripts/'lean-cache-run.sh'
    shutil.copyfile(pathlib.Path(repository)/'tools/scripts/worktree/lean-cache-run.sh',runner)
    runner.chmod(0o755)
    from xml.sax.saxutils import escape
    project=root/'tools/StrataLint.Cli/StrataLint.Cli.csproj';project.parent.mkdir(parents=True)
    project.write_text('<Project><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework>'+
        '<RunCommand>'+escape(CLI[0])+'</RunCommand>'+
        '<RunArguments>'+escape('"'+assembly+'"')+'</RunArguments></PropertyGroup>'+
        '<Target Name="Restore"/><Target Name="Build"/><Target Name="ComputeRunArguments"/></Project>')
    return runner
def artifact(root):
    local = root / json.loads(command(root,lake,'query','-J','+Fixture:olean').stdout)
    assert local.is_relative_to(root), 'full restoration must return module-shaped paths'
    # Simultaneous cold writers can retain distinct output inodes for equal bytes.
    return next(path for path in cache.rglob('*.olean') if path.read_bytes()==local.read_bytes())
def inode(path):
    st=path.stat()
    return dict(device=st.st_dev,inode=st.st_ino,links=st.st_nlink,bytes=st.st_size,allocated=st.st_blocks*512)
def storage(*roots):
    paths=[p for root in roots for p in root.rglob('*') if p.is_file()]
    unique={(p.stat().st_dev,p.stat().st_ino):p.stat() for p in paths}
    return dict(files=len(paths),logical_bytes=sum(p.stat().st_size for p in paths),
        unique_inodes=len(unique),inode_allocated_bytes=sum(st.st_blocks*512 for st in unique.values()),
        filesystem_available_bytes=shutil.disk_usage(P).free)
def inspect(root, output, **mode):
    source=root/'Fixture.lean'
    args=['--output',str(root/output),'--material-spool',str(root/(output+'.materials')),
          '--utility-input',str(root/'utility.json'),
          'Fixture','Fixture.lean','sha256:'+hashlib.sha256(source.read_bytes()).hexdigest()]
    command(root,lake,'build','+Claim',**mode)
    command(root,lake,'env','lean','--run','tools/lean-inspector/Inspector.lean',*args,**mode)
    return json.loads((root/output).read_text())
""";

    private const string NativeArchiveProgram = NativePrelude + "\n" + """
writer=fresh('writer')
lake_version=command(writer,lake,'--version').stdout.strip()
assert '(Lean version 4.33.0)' in lake_version
assert 'Built Fixture' in command(writer,lake,'build','-v').stdout
cached=artifact(writer)
assert os.path.samefile(writer/'.lake/build/lib/lean/Fixture.olean',cached)
reader=fresh('reader')
hit=command(reader,lake,'build','-v')
assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
assert artifact(reader)==cached and os.path.samefile(reader/'.lake/build/lib/lean/Fixture.olean',cached)
report=inspect(reader,'local.json')
ci_root=fresh('ci-reader')
ci_hit=command(ci_root,lake,'build','-v',ci=True)
assert 'Built Fixture' not in ci_hit.stdout and 'Reused Fixture' in ci_hit.stdout
assert os.path.samefile(reader/'.lake/build/lib/lean/Fixture.olean',cached)
# setup.json is a compiler invocation input, not a published Lake artifact.
root_outputs=[p.relative_to(writer/'.lake/build') for p in (writer/'.lake/build').rglob('Fixture.*')
              if p.is_file() and not p.name.endswith('.setup.json')]
assert root_outputs
for relative in root_outputs:
    restored_bytes=(ci_root/'.lake/build'/relative).read_bytes()
    built_bytes=(writer/'.lake/build'/relative).read_bytes()
    if relative.suffix=='.trace':
        # Lake writes synthetic fetch metadata instead of copying a build log.
        restored_trace,built_trace=json.loads(restored_bytes),json.loads(built_bytes)
        assert restored_trace['depHash']==built_trace['depHash']
        assert restored_trace['outputs']==built_trace['outputs']
    else:
        assert restored_bytes==built_bytes, relative
assert os.path.samefile(ci_root/'.lake/build/lib/lean/Fixture.olean',cached)
assert inspect(ci_root,'restored.json',ci=True)==report, 'full report differs between local and CI restored artifacts'
# Actions saves the build directory directly. Model that data boundary, without
# reading or testing workflow text, and give its next reader an empty store.
ci_archive=P/'actions-build.tgz'
run(['tar','-czf',ci_archive,'-C',ci_root,'.lake/build'],ci_root)
ci_reader=fresh('actions-reader')
empty_store=P/'empty-official-cache';empty_store.mkdir()
assert not list(empty_store.iterdir())
run(['tar','-xzf',ci_archive,'-C',ci_reader],ci_reader)
replayed=command(ci_reader,lake,'build','-v',ci=True,store=empty_store)
assert 'Built Fixture' not in replayed.stdout, replayed.stdout
assert 'Replayed Fixture' in replayed.stdout or 'Reused Fixture' in replayed.stdout, replayed.stdout
assert (ci_reader/'.lake/build/lib/lean/Fixture.olean').read_bytes()==cached.read_bytes()
assert inspect(ci_reader,'archive.json',ci=True,store=empty_store)==report
changed=fresh('changed',43)
assert 'Built Fixture' in command(changed,lake,'build','-v').stdout
new=artifact(changed)
assert new!=cached
# Fetch must enter the real selected-repository shell runner and candidate CLI.
# The fixture project supplies dotnet-run metadata for the already-built candidate
# assembly; no replacement runner, writer guard, dotnet executable or Lake is used.
target=fresh('fetch-reader')
runner=install_runner(target)
command(target,lake,'build',ci=True)
overlap=target/'.lake/build/lib/lean/Fixture.olean'
assert os.path.samefile(overlap,cached), 'fetch target must overlap the older shared generation'
old_bytes=cached.read_bytes();old_hash=hashlib.sha256(old_bytes).hexdigest()
# The archive contains actual, different compiled bytes at the overlapping path.
payload=P/'release';payload.mkdir()
fetch_archive=payload/'lean-build.tgz'
(target/'Fixture.lean').write_bytes((changed/'Fixture.lean').read_bytes())
# Only release transport and input-address values are fixture data.
source_address='3'*64;config_address='4'*64;producer='a'*40
helper=target/'tools/scripts/worktree/lean-cache-input.sh'
helper.write_text('#!/bin/sh\nprintf "%s %s\\n" '+source_address+' '+config_address+'\n');helper.chmod(0o755)
bin_dir=P/'fetch-bin';bin_dir.mkdir()
gh=bin_dir/'gh'
gh.write_text('#!'+sys.executable+'\n'+
    'import sys,pathlib,shutil\na=sys.argv[1:];p=pathlib.Path('+repr(str(payload))+')\n'+
    'if a[:2]==["release","download"]:\n'+
    ' n=a[a.index("--pattern")+1];d=a[a.index("--dir")+1]\n'+
    ' assert n in ["manifest.txt","lean-build.tgz"];shutil.copyfile(p/n,pathlib.Path(d)/n)\n'+
    'elif a[:2]==["release","create"]:\n'+
    ' for arg in a[2:]:\n'+
    '  f=pathlib.Path(arg)\n'+
    '  if f.is_file() and f.name in ["lean-build.tgz","manifest.txt"]: shutil.copyfile(f,p/f.name)\n'+
    'elif a[:1]==["api"]: print((p/"release.json").read_text())\n'+
    'elif a[:2]==["release","list"]: pass\n'+
    'else: sys.exit(1)\n');gh.chmod(0o755)
# Only the selected absolute Lake is available; PATH still supplies real tools.
for tool in ['dotnet','jq']:
    (bin_dir/tool).symlink_to(shutil.which(tool))
fetch_env=dict(ENV,PATH=str(bin_dir)+':/usr/bin:/bin:/usr/sbin:/sbin')
assert shutil.which('lake',path=fetch_env['PATH']) is None
# Use a tree with old hardlinked output and new source: export must build first.
exporter=fresh('exporter')
install_runner(exporter)
command(exporter,lake,'build')
(exporter/'Fixture.lean').write_bytes((changed/'Fixture.lean').read_bytes())
shutil.copy2(helper,exporter/'tools/scripts/worktree/lean-cache-input.sh')
published=run(['bash',pathlib.Path(repository)/'tools/scripts/worktree/lean-cache-publish.sh',
    'publish','--repository',exporter],P,env=dict(fetch_env,GITHUB_SHA=producer,GITHUB_RUN_ID='7777'))
with tarfile.open(fetch_archive) as pack:
    member=next(m for m in pack.getmembers() if m.name.endswith('/Fixture.olean'))
    assert pack.extractfile(member).read()==new.read_bytes()!=old_bytes
assert cached.read_bytes()==old_bytes, 'export rebuild changed old hardlinked generation'
digest=hashlib.sha256(fetch_archive.read_bytes()).hexdigest()
assert 'archive_sha256='+digest in (payload/'manifest.txt').read_text()
(payload/'release.json').write_text(json.dumps(dict(target_commitish=producer,assets=[
    dict(name='lean-build.tgz',digest='sha256:'+digest),dict(name='manifest.txt')])))
def fetch(expected):
    return run(['bash',pathlib.Path(repository)/'tools/scripts/worktree/lean-cache-publish.sh',
        'fetch','--repository',target],P,expected,fetch_env)
def tree_hashes(root):
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}
ready=target/'fetch-writer-ready';release=target/'fetch-writer-release'
hold='import pathlib,time;pathlib.Path("fetch-writer-ready").touch();'+\
    'exec("while not pathlib.Path(\\"fetch-writer-release\\").exists(): time.sleep(.05)")'
holder=subprocess.Popen([str(runner),'env','LAKE_CACHE_DIR='+str(cache),lake,'env',sys.executable,'-c',hold],
    cwd=target,env=ENV,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
try:
    deadline=time.monotonic()+30
    while not ready.exists():
        assert holder.poll() is None and time.monotonic()<deadline
        time.sleep(.05)
    before=tree_hashes(target/'.lake/build')
    blocked=fetch(1)
    assert 'busy' in blocked.stderr, (blocked.stdout,blocked.stderr)
    assert 'archive could not be unpacked' in blocked.stdout
    assert tree_hashes(target/'.lake/build')==before, 'busy fetch mutated extraction destination'
    assert os.path.samefile(overlap,cached) and cached.read_bytes()==old_bytes
finally:
    release.touch()
    holder_out,holder_err=holder.communicate(timeout=30)
    assert holder.returncode==0, (holder_out,holder_err)
accepted=fetch(0)
assert '"status":"unpacked"' in accepted.stdout
assert overlap.read_bytes()==new.read_bytes()!=old_bytes, 'real unpack did not replace the overlapping output'
assert not os.path.samefile(overlap,cached)
assert cached.read_bytes()==old_bytes and hashlib.sha256(cached.read_bytes()).hexdigest()==old_hash
after_fetch=command(target,lake,'build','-v')
assert 'Built Fixture' not in after_fetch.stdout, after_fetch.stdout
old_reader=fresh('old-generation-reader')
old_hit=command(old_reader,lake,'build','-v')
assert 'Built Fixture' not in old_hit.stdout and 'Reused Fixture' in old_hit.stdout
assert artifact(old_reader)==cached and cached.read_bytes()==old_bytes
print(json.dumps(dict(commands=records,lake_version=lake_version,local_and_ci_hardlinks=True,
    ci_root_outputs=len(root_outputs),ci_restored_without_build=True,
    actions_archive_empty_store_no_rebuild=True,actions_archive_report_equivalence=True,
    native_fetch_busy_exit=blocked.returncode,native_fetch_success_exit=accepted.returncode,
    busy_fetch_destination_unchanged=True,native_unpack_replaced_hardlink=True,
    previous_generation_sha256=old_hash,previous_generation_reused=True,
    restricted_path_without_lake=True,absolute_lake_selection=True,native_export_exit=published.returncode,old_inode=inode(cached),new_inode=inode(new))))
""";

    private const string NativeProgram = NativePrelude + "\n" + """
writer=fresh('writer')
snapshots={'before':storage(cache,writer)}
lake_version=command(writer,lake,'--version').stdout.strip()
assert '(Lean version 4.33.0)' in lake_version
assert 'Built Fixture' in command(writer,lake,'build','-v').stdout
cached=artifact(writer)
assert cached.is_relative_to(cache)
local=writer/'.lake/build/lib/lean/Fixture.olean'
assert os.path.samefile(local,cached), 'same-device native publication did not hardlink'
snapshots['writer']=storage(cache,writer)
reader=fresh('reader')
hit=command(reader,lake,'build','-v')
assert 'Built Fixture' not in hit.stdout and 'Reused Fixture' in hit.stdout
assert os.path.samefile(reader/'.lake/build/lib/lean/Fixture.olean',cached)
assert artifact(reader)==cached
snapshots['same_source_reader']=storage(cache,writer,reader)
changed=fresh('changed',43)
miss=command(changed,lake,'build','-v')
assert 'Built Fixture' in miss.stdout
new=artifact(changed)
snapshots['changed_source']=storage(cache,writer,reader,changed)
assert new!=cached
sys.path.insert(0,str(pathlib.Path(repository)/'tools/lean-inspector/Census'))
from streaming import enumerate_oleans
native_env=dict(ENV,LAKE_CACHE_DIR=str(cache),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LAKE_NO_CACHE='true')
manifest,inputs=enumerate_oleans(reader,{'Fixture':'Fixture.lean'})
parts=manifest[0][1]
assert len(parts)==3 and all(pathlib.Path(p).is_relative_to(reader) for p in parts)
# Local setup input is generated for compilation; a cache hit restores outputs
# and synthetic trace metadata without requiring another compiler invocation.
assert (writer/'.lake/build/ir/Fixture.setup.json').exists()
assert not (reader/'.lake/build/ir/Fixture.setup.json').exists()
assert not os.path.samefile(writer/'.lake/build/lib/lean/Fixture.trace',reader/'.lake/build/lib/lean/Fixture.trace')
driver=reader/'Static.lean'
driver.write_text('import Fixture\n#eval IO.println s!"compile:{answer}"\n'+
    'def main (args : List String) : IO Unit := IO.println s!"{answer}:{args.head!}"\n')
static=command(reader,lake,'env','lean','-R',str(reader),'--run',driver,'argument')
assert static.stdout.splitlines()==['compile:42','42:argument'], 'source runner changed Lean arguments'
benchmark=command(reader,lake,'env',sys.executable,'-c',
    'import sys; sys.path.insert(0,sys.argv[1]); from Certificate.certificate_benchmark import run_driver; run_driver(sys.argv[2])',
    str(pathlib.Path(repository)/'tools/lean-inspector/Census'),str(driver))
assert benchmark.stdout.strip()=='compile:42', 'benchmark runner lost restored imports'
# Analysis exports must run again even when all their artifacts are cached.
analysis=reader/'tools/lean-inspector/LeanInformationAuditAnalysis'
analysis.mkdir(parents=True)
analysis_script=analysis/'run-analysis-fixtures.sh'
shutil.copyfile(pathlib.Path(repository)/'tools/lean-inspector/LeanInformationAuditAnalysis/run-analysis-fixtures.sh',analysis_script)
install_runner(reader)
with (reader/'lakefile.toml').open('a') as f:
    f.write('\n[[lean_lib]]\nname="LeanInformationAuditAnalysis"\nsrcDir="tools/lean-inspector"\nglobs=["LeanInformationAuditAnalysis.+"]\n')
exports={'CausalProjection':['causal-analysis.json','causal-analysis.txt'],
    'FrozenRootAnalysis':['frozen-seal.json','frozen-analysis.json','frozen-analysis.txt'],
    'BoundedClosure':['bounded-analysis.json','bounded-analysis.txt']}
for module,names in exports.items():
    (analysis/(module+'.lean')).write_text('import Lean\nimport Fixture\nopen Lean Elab Command\n'+
        'run_cmd liftIO do\n  let folder ← IO.getEnv "IE_PROJECTION_OUTPUT_DIR"\n'+
        '  for name in #['+', '.join(json.dumps(n) for n in names)+'] do\n'+
        '    IO.FS.writeFile ((folder.get! : System.FilePath) / name) (toString answer)\n')
seed=reader/'analysis-seed';seed.mkdir()
command(reader,'env','IE_PROJECTION_OUTPUT_DIR='+str(seed),lake,'build','LeanInformationAuditAnalysis')
# Exercise the supported absolute selection through the actual script and runner,
# with real auxiliary tools but no Lake discoverable on PATH.
analysis_bin=P/'analysis-bin';analysis_bin.mkdir()
(analysis_bin/'dotnet').symlink_to(CLI[0])
analysis_env=dict(native_env,PATH=str(analysis_bin)+':/usr/bin:/bin:/usr/sbin:/sbin')
assert pathlib.Path(lake).is_absolute()
assert shutil.which('lake',path=analysis_env['PATH']) is None
cached_analysis=command(reader,lake,'build','-v','LeanInformationAuditAnalysis')
assert 'Built LeanInformationAuditAnalysis.' not in cached_analysis.stdout
for name in ['analysis-first','analysis-second']:
    destination=reader/name
    result=run(['bash',analysis_script,destination],reader,env=analysis_env)
    assert 'ANALYSIS_FIXTURES_EXIT=0' in result.stdout
    assert len(list(destination.iterdir()))==7
    assert all(p.read_text()=='42' for p in destination.iterdir())
# Exercise the actual Census native builder within its inspector library scope.
with (reader/'lakefile.toml').open('a') as f:
    f.write('\n[[lean_lib]]\nname="NativeSupport"\nsrcDir="tools/lean-inspector"\n')
support=reader/'tools/lean-inspector/NativeSupport.lean'
support.write_text('def native_answer : Nat := 42\n')
command(reader,lake,'build','NativeSupport')
program=reader/'tools/lean-inspector/Census/value.lean'
program.parent.mkdir(parents=True)
program.write_text('import NativeSupport\ndef main : IO Unit := IO.println native_answer\n')
build_native='import sys; sys.path.insert(0,sys.argv[1]); from native import build; print(build(sys.argv[2],"value.lean"))'
native=command(reader,lake,'env',sys.executable,'-c',build_native,
    str(pathlib.Path(repository)/'tools/lean-inspector/Census'),str(reader))
binary=pathlib.Path(native.stdout.strip().splitlines()[-1])
assert run([binary],reader).stdout.strip()=='42', 'native consumer lost restored C dependency'
report=inspect(reader,'local.json')
assert report['modules'][0]['utility_refutation']['is_closed_negation'], 'utility claim import lost'
assert inspect(reader,'ci.json',ci=True)==report, 'full report differs between local and CI'
archive=P/'build.tgz'
command(reader,lake,'pack',archive)
with tarfile.open(archive) as pack:
    assert any(n.endswith('/Fixture.olean') for n in pack.getnames())
restored=fresh('archive-reader')
command(restored,lake,'unpack',archive)
assert (restored/'.lake/build/lib/lean/Fixture.olean').is_file()
reuse=fresh('changed-reader',43)
assert 'Built Fixture' not in command(reuse,lake,'build','-v').stdout
assert artifact(reuse)==new
assert artifact(writer)==cached, 'new generation lost old-source reuse'
from mutations import compiled_digests
original_digests=compiled_digests(reuse,'Fixture')
# Failed actual source compilation cannot masquerade as a hit.
try:
    (reuse/'Fixture.lean').write_text('def answer : Nat := "invalid"\n')
    invalid=command(reuse,lake,'build',expected=1)
    assert 'type mismatch' in invalid.stdout.lower(), invalid.stdout
finally:
    (reuse/'Fixture.lean').write_bytes((changed/'Fixture.lean').read_bytes())
command(reuse,lake,'build')
assert compiled_digests(reuse,'Fixture')==original_digests
print(json.dumps(dict(commands=records,shared_olean_parts=len(parts),
    root_local_olean_on_hit=True,hardlink_identity=True,report_equivalence=True,
    actual_miss_and_cross_tree_reuse=True,utility_import=True,
    static_runners=True,analysis_repeated_exports=7,analysis_absolute_lake_without_path=True,
    analysis_cached_without_build=True,mutation_restored_bytes=True,
    storage=snapshots,writer_inode=inode(local),reader_inode=inode(reader/'.lake/build/lib/lean/Fixture.olean'),
    cache_inode=inode(cached),setup_only_for_compilation=True,independent_trace_inodes=True)))
""";

    private const string NativeOwnershipProgram = NativePrelude + "\n" + """
native_env=dict(ENV,LAKE_CACHE_DIR=str(cache),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LAKE_NO_CACHE='true')
# Distinct checkout writers use the same official store concurrently.
parallel=[fresh('parallel-a',44),fresh('parallel-b',44)]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    list(pool.map(lambda root: command(root,lake,'build'),parallel))
assert artifact(parallel[0])==artifact(parallel[1])
# The finite-closure check must ignore an unrelated M3 import, then reject
# the same dependency when SealCommand itself imports it.
audit=fresh('import-cost')
with (audit/'lakefile.toml').open('a') as f:
    f.write('\n[[lean_lib]]\nname="LeanInformationAudit"\n[[lean_lib]]\nname="D5"\n')
def write_module(module,text):
    path=audit/pathlib.Path(*module.split('.')).with_suffix('.lean')
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    return path
forbidden='D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog'
write_module(forbidden,'def structuralFixture : Nat := 0\n')
seal=write_module('LeanInformationAudit.SealCommand','import Lean\n')
write_module('LeanInformationAudit.Tests.Seal.M3','import '+forbidden+'\n')
check=write_module('LeanInformationAudit.Tests.Seal.ImportCost',
    (pathlib.Path(repository)/'tools/lean-inspector/LeanInformationAudit/Tests/Seal/ImportCost.lean').read_text())
command(audit,lake,'build','+LeanInformationAudit.Tests.Seal.ImportCost')
original_seal=seal.read_bytes()
try:
    seal.write_text('import Lean\nimport '+forbidden+'\n')
    red=command(audit,lake,'build','+LeanInformationAudit.Tests.Seal.ImportCost',expected=1)
    assert 'structural dependency in finite seal closure' in red.stdout+red.stderr
finally:
    seal.write_bytes(original_seal)
command(audit,lake,'build','+LeanInformationAudit.Tests.Seal.ImportCost')
# Preserve the package's explicit official restoration setting. Both root and
# dependency cache hits restore module paths with shared artifact inodes.
def package_tree(name):
    root=fresh(name)
    dep=root/'dep';dep.mkdir()
    (dep/'lakefile.toml').write_text('name="dep"\nrestoreAllArtifacts=true\n[[lean_lib]]\nname="Dep"\n')
    (dep/'Dep.lean').write_text('module\npublic theorem dependency : True := True.intro\n')
    with (root/'lakefile.toml').open('a') as f:
        f.write('\n[[require]]\nname="dep"\npath="dep"\n')
    source=root/'Fixture.lean'
    source.write_text(source.read_text().replace('module\n','module\npublic import Dep\n',1))
    run([lake,'update'],root,env=native_env)
    return root
pa,pb=package_tree('package-writer'),package_tree('package-reader')
command(pa,lake,'build')
command(pb,lake,'build')
assert os.path.samefile(pa/'.lake/build/lib/lean/Fixture.olean',pb/'.lake/build/lib/lean/Fixture.olean')
da=pa/'dep/.lake/build/lib/lean/Dep.olean';db=pb/'dep/.lake/build/lib/lean/Dep.olean'
assert os.path.samefile(da,db), 'explicit dependency restoration did not share its inode'
# Preserve worktree-local ownership after the CLI dies with a live descendant.
locked=fresh('lifetime');marker=locked/'ready';release=locked/'release'
subgroup='import pathlib,os,time,json\nos.setpgid(0,0)\np=pathlib.Path("ready"); t=p.with_suffix(".tmp")\n'+\
    't.write_text(json.dumps(dict(pid=os.getpid(),leader=os.getppid(),session=os.getsid(0)))); t.replace(p)\n'+\
    'while not pathlib.Path("release").exists(): time.sleep(.05)\n'
hold='import subprocess,sys; sys.exit(subprocess.call([sys.executable,"-c",'+repr(subgroup)+']))'
lifetime_log=locked/'writer.log'
with lifetime_log.open('w') as log:
    child=subprocess.Popen(list(map(str,CLI+['with-cache','--path',locked,'--',sys.executable,'-c',hold])),
        cwd=locked,env=ENV,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
writer_pid=None
try:
    deadline=time.monotonic()+15
    while not marker.exists():
        assert child.poll() is None and time.monotonic()<deadline, lifetime_log.read_text()
        time.sleep(.05)
    identity=json.loads(marker.read_text());writer_pid=identity['pid']
    assert identity['session']==identity['leader'] and os.getpgid(writer_pid)==writer_pid
    child.kill();child.wait()
    os.kill(identity['leader'],9)
    os.kill(writer_pid,0)  # The descendant must still exist at the negative check.
    busy=run(CLI+['ensure-cache','--path',locked],locked,expected=2)
    assert 'busy' in busy.stderr
    release.touch()
    deadline=time.monotonic()+15
    while True:
        recovered=subprocess.run(list(map(str,CLI+['ensure-cache','--path',locked])),cwd=locked,env=ENV,
                                 text=True,capture_output=True,timeout=20)
        if recovered.returncode==0: break
        assert 'busy' in recovered.stderr and time.monotonic()<deadline, recovered.stderr
        time.sleep(.1)
finally:
    release.touch()
    if child.poll() is None: child.kill();child.wait()
    if writer_pid is not None:
        try: os.kill(writer_pid,9)
        except ProcessLookupError: pass
print(json.dumps(dict(commands=records,dependency_restore_hardlinks=True,
    concurrent_writers=True,subgroup_descendant_lock_recovery=True,
    concurrent_writer_inodes=[inode(root/'.lake/build/lib/lean/Fixture.olean') for root in parallel],finite_closure_negative=True)))
""";

}
